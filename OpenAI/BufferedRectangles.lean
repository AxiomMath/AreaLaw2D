/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/BufferedRectangles.lean` (Apache 2.0). Namespace `TNLean.PEPS.AreaLaw`
renamed to `OpenAI`; the rectangle layer is restated over the repository's encoding (see the
implementation notes), and only the declarations `OpenAI.Rectangles` and
`OpenAI.SupportCounting` lack are ported.
-/
import OpenAI.SupportCounting
import OpenAI.GraphInteractionBudget
import OpenAI.GraphLatticeDiamond

/-!
# Safe integer rectangles: the diamond count of split supports

For a cut `A` of a finite domain `Λ ⊆ ℤ²`, a rectangle `Q` is safe when its sup-norm distance to
the endpoints of the crossing edges exceeds `D₀ · size Q`. Inside a safe rectangle with
`R < D₀`, an admissible support meeting `A` lies in `A`, so a support split by a contour
`A ∩ T^{+d}` with `T^{+d} ⊆ Q` meets `T^{+d}` and leaves it. Its sites then lie within ambient
distance `R` of the boundary layer `T^{+d} \ T^{+(d-R)}`, which for a rectangle `T` has at most
`4 R (size T + 2 d)` sites. Every admissible support of range `R` containing a site `a` lies in
the `ℓ¹` diamond of radius `R` about `a`, of `v_R = 1 + 2 R (R + 1)` sites, so at most
`μ_R = 2 ^ (v_R - 1)` supports contain `a`. Hence at most `8 (R + 1) μ_R (size T + d)` supports
are split by the contour.

## Main statements

* `latticeL1Distance_le_one_of_adj`: nearest-neighbour edges have ambient displacement one.
* `exists_of_splits_rectRegion`: a support split by a contour near a safe rectangle.
* `card_admissibleSupport_containing_le`: at most `μ_R` admissible supports contain a site.
* `card_crossingTerms_rectRegion_le`: the crossing count `≤ 8 (R + 1) μ_R (size T + d)`.

## Implementation notes

TNLean's structure `IntRect` is the predicate `IsIntRect` on `Finset (ℤ × ℤ)`, its `size` is
`boxSize`, its `Q.dilate d` is `ambientDilation Q d`, its physical region `rectRegion A Q` is
`A ∩ Q`, and its sites `Site Λ` are points of `ℤ × ℤ`. The sup-norm distance `supDist` is
Mathlib's `dist` on `ℤ × ℤ`, and the safety condition `IsSafe` takes a real `D₀`, as in
`OpenAI.Rectangles`. TNLean's admissible supports `AdmissibleSupport Λ R` are the subtype of
`supports Λ R`, and a support split by a region `B` is a member of `crossingTerms` for `B`.

The remaining declarations of the source are already in `OpenAI.Rectangles`:
`IntRect.toFinset_dilate` is `ambientDilation_Icc`, `IntRect.dilate_dilate` is
`ambientDilation_ambientDilation`, `IntRect.toFinset_dilate_mono` is `ambientDilation_mono`,
`IntRect.mem_dilate_of_supDist_le` is `mem_ambientDilation_add`, `IntRect.one_le_size` is
`IsIntRect.one_le_boxSize`, `supDist_le_of_walk` is `dist_le_length_of_walk`,
`subset_of_isSafe` and `not_splits_two_contours` keep their names, and `card_dilate_sdiff_le`
is `IsIntRect.card_ambientDilation_sdiff_le`. The crossing count assumes `R ≤ d` rather than
the source's `R + 1 ≤ d`, using the layer of width `R`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  the definitions before Lemma 3.2 and the proof of Lemma 3.2 (`lem:initial-buffer`),
  `02-initial.tex`, lines 220–239 and 263–293, `eq:initial-contour-budget`.
-/

namespace OpenAI

open SimpleGraph

/-! ### Ambient distances -/

/-- Nearest-neighbour edges of an induced domain have ambient displacement one. -/
theorem latticeL1Distance_le_one_of_adj {Λ : Finset (ℤ × ℤ)} {x y : (Λ : Set (ℤ × ℤ))}
    (h : ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).Adj x y) :
    latticeL1Distance x.1 y.1 ≤ 1 := by
  rw [induce_adj, squareLattice_adj_iff] at h
  unfold latticeL1Distance
  rcases h with ⟨h₁, h₂ | h₂⟩ | ⟨h₁, h₂ | h₂⟩ <;> omega

/-- The sup-norm distance is bounded by the lattice path distance. -/
theorem dist_le_latticeL1Distance (a b : ℤ × ℤ) : dist a b ≤ latticeL1Distance a b := by
  rw [dist_eq_max_abs, latticeL1Distance]
  have h : max |a.1 - b.1| |a.2 - b.2| ≤ ((a.1 - b.1).natAbs + (a.2 - b.2).natAbs : ℕ) := by
    push_cast [Int.natCast_natAbs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  rw [← Int.cast_natCast (R := ℝ)]
  exact Int.cast_le.2 h

/-! ### Rectangle sides -/

/-- The number of horizontal sites of a rectangle is bounded by its size. -/
theorem width_le_boxSize_Icc {a b : ℤ × ℤ} (h : a ≤ b) :
    b.1 + 1 - a.1 ≤ boxSize (Finset.Icc a b) := by
  rw [boxSize_Icc h]
  have := h.1
  omega

/-- The number of vertical sites of a rectangle is bounded by its size. -/
theorem height_le_boxSize_Icc {a b : ℤ × ℤ} (h : a ≤ b) :
    b.2 + 1 - a.2 ≤ boxSize (Finset.Icc a b) := by
  rw [boxSize_Icc h]
  have := h.2
  omega

/-! ### Supports split by a contour -/

variable {D₀ : ℝ} {Λ A Q T X : Finset (ℤ × ℤ)} {R : ℕ}

/-- **A support split by a contour lies across the rectangle boundary.** If `T^{+d} ⊆ Q` with
`Q` safe and `R < D₀`, and an admissible support is split by `A ∩ T^{+d}`, then it lies in `A`,
has a site in `T^{+d}`, and has a site outside `T^{+d}`. -/
theorem exists_of_splits_rectRegion (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀) {d : ℕ}
    (hQ : ambientDilation T d ⊆ Q) (hX : X ∈ supports Λ R)
    (hsplit : (X ∩ (A ∩ ambientDilation T d)).Nonempty ∧
      (X \ (A ∩ ambientDilation T d)).Nonempty) :
    X ⊆ A ∧ (∃ v ∈ X, v ∈ ambientDilation T d) ∧ ∃ w ∈ X, w ∉ ambientDilation T d := by
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hsplit
  rw [Finset.mem_inter, Finset.mem_inter] at hv
  rw [Finset.mem_sdiff, Finset.mem_inter] at hw
  have hXA := subset_of_isSafe hs hR hX hv.1 hv.2.1 (hQ hv.2.2)
  exact ⟨hXA, ⟨v, hv.1, hv.2.2⟩, ⟨w, hw.1, fun h ↦ hw.2 ⟨hXA hw.1, h⟩⟩⟩

/-! ### Counting the supports split by one contour -/

/-- An admissible support of range `R` containing `a` lies in the `ℓ¹` diamond of radius `R`
about `a`. -/
theorem subset_latticeDiamond_of_mem_supports (hX : X ∈ supports Λ R) {a : ℤ × ℤ}
    (ha : a ∈ X) : X ⊆ latticeDiamond a R := by
  intro x hx
  obtain ⟨hXΛ, -, hw⟩ := mem_supports_iff_walk.1 hX
  obtain ⟨p, hp⟩ := hw a ha x hx
  exact mem_latticeDiamond.2 ((latticeL1Distance_le_walk_length Subtype.val
    (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h) p).trans hp)

/-- At most `μ_R = 2^{v_R - 1}` admissible supports of range `R` contain a given site, with
`v_R = 1 + 2 R (R + 1)` [OAI265, §2.2, the multiplicity bound after `eq:ball-count`]. -/
theorem card_admissibleSupport_containing_le (v : ℤ × ℤ) :
    (Finset.univ.filter fun X : supports Λ R ↦ v ∈ X.1).card ≤
      2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
  classical
  have hval : (Finset.univ.filter fun X : supports Λ R ↦ v ∈ X.1).card =
      ((Finset.univ.filter fun X : supports Λ R ↦ v ∈ X.1).map
        (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
  rw [hval, ← card_latticeDiamond v R]
  refine card_supportFamily_le_pow _ _ v (mem_latticeDiamond.2 (by simp)) fun X hX ↦ ?_
  obtain ⟨Y, hY, rfl⟩ := Finset.mem_map.1 hX
  have hvY := (Finset.mem_filter.1 hY).2
  exact ⟨hvY, subset_latticeDiamond_of_mem_supports Y.2 hvY⟩

/-- **The crossing count of one contour** [OAI265, §3.2, `eq:initial-contour-budget`]. Let `T`
be an integer rectangle with `T^{+d}` inside a safe set `Q`, `R < D₀` and `R ≤ d`. At most
`8 (R + 1) μ_R (size T + d)` admissible supports are split by `A ∩ T^{+d}`, where
`μ_R = 2^{v_R - 1}` bounds the number of admissible supports containing a site and
`v_R = 1 + 2 R (R + 1)`. Missing sites of the domain only decrease the count. -/
theorem card_crossingTerms_rectRegion_le (hT : IsIntRect T) (hs : IsSafe D₀ Λ A Q)
    (hR : (R : ℝ) < D₀) {d : ℕ} (hd : R ≤ d) (hQ : ambientDilation T d ⊆ Q) :
    (crossingTerms (fun X : supports Λ R ↦ (X : Finset (ℤ × ℤ)))
        (A ∩ ambientDilation T d)).card ≤
      8 * (R + 1) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) * (boxSize T + d) := by
  classical
  set layer := ambientDilation T d \ ambientDilation T (d - R)
  set μ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  have hcover : crossingTerms (fun X : supports Λ R ↦ (X : Finset (ℤ × ℤ)))
      (A ∩ ambientDilation T d) ⊆
        layer.biUnion fun v ↦ Finset.univ.filter fun X : supports Λ R ↦ v ∈ X.1 := by
    intro X hX
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := mem_crossingTerms.1 hX
    rw [Finset.mem_inter] at hv
    rw [Finset.mem_sdiff] at hw
    exact Finset.mem_biUnion.2 ⟨v, mem_sdiff_ambientDilation_of_isSafe hs hR (by omega) hQ X.2
      hv.1 hv.2 hw.1 hw.2, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv.1⟩⟩
  have hlayer := hT.card_ambientDilation_sdiff_le hd
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ layer.card * μ :=
        Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦ card_admissibleSupport_containing_le v
    _ ≤ 4 * R * (boxSize T + 2 * d) * μ := Nat.mul_le_mul_right _ hlayer
    _ ≤ 4 * (R + 1) * (2 * (boxSize T + d)) * μ := by
        gcongr
        · omega
        · omega
    _ = 8 * (R + 1) * μ * (boxSize T + d) := by ring

end OpenAI
