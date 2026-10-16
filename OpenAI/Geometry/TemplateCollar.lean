/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Adapted from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/CollarInformation.lean` (`Template.collar_cut_card_le`). Apache 2.0.
-/
import OpenAI.Rectangles
import OpenAI.Geometry.TemplatePieceStrips

/-!
# Cuts and sizes of a template collar

For a template `T` separated from the cut `A` with `L ≤ s₀`, the cuts of `X = A ∩ T`,
`S₀ = A ∩ T_L` and `S₀ \ X` have `O(n)` edges and `|S₀| = O(n²)` [OAI265, Lemma 9.4 and the
last sentence of Proposition 9.6].  These are the size and boundary assertions of
Proposition 9.6.

Every site of `T_L` is at sup-distance at most `s₀` from `T`, hence off the crossing-edge
endpoints, so a crossing edge of `A ∩ T_L` leaves `T_L` itself.  The lattice points of a template
piece are octagonally convex, so the rows and columns of each dilated piece are integer
intervals and each dilated piece has at most `s₀ + 2L + 1` outgoing edges in each of the four
lattice directions.  Summing over the `N₀` pieces gives at most `12 N₀ (s₀ + 1) ≤ n / 2`
outgoing edges of `T_L`.  The size bound comes from `diam_∞ T ≤ n`.

## Main definitions

* `OpenAI.IsOctagonallyConvex`: closure under betweenness for `x`, `y`, `x + y`, `x - y`.

## Main statements

* `OpenAI.IsOctagonallyConvex.mk_mem_ambientDilation_of_snd_eq`,
  `OpenAI.IsOctagonallyConvex.mk_mem_ambientDilation_of_fst_eq`: rows and columns of a dilation.
* `OpenAI.IsTemplate.two_mul_sum_card_filter_le`: the outgoing edges of `T_L`.
* `OpenAI.IsTemplate.exists_pieces`: a template as a union of octagonally convex pieces.
* `OpenAI.IsTemplate.collar_cut_card_le`: the cut and size assertions of Proposition 9.6.

## Implementation notes

TNLean bounds `|S₀|` through the layer counts `|T_{d} \ T_{d-1}| ≤ n`; here the size bound
`|T_L| ≤ (2 (n + L) + 1)²` suffices, since `2 L + 1 ≤ n`.
-/

namespace OpenAI

open SimpleGraph

/-- A set of lattice sites is *octagonally convex* if it contains every site at which each of the
four forms `x`, `y`, `x + y` and `x - y` lies between its values at two sites of the set.  The
lattice points of a convex polygon with sides of slope `0`, `∞`, `1` or `-1` form such a set. -/
def IsOctagonallyConvex (Q : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ Q, ∀ r ∈ Q, ∀ q : ℤ × ℤ,
    min p.1 r.1 ≤ q.1 → q.1 ≤ max p.1 r.1 → min p.2 r.2 ≤ q.2 → q.2 ≤ max p.2 r.2 →
    min (p.1 + p.2) (r.1 + r.2) ≤ q.1 + q.2 → q.1 + q.2 ≤ max (p.1 + p.2) (r.1 + r.2) →
    min (p.1 - p.2) (r.1 - r.2) ≤ q.1 - q.2 → q.1 - q.2 ≤ max (p.1 - p.2) (r.1 - r.2) → q ∈ Q

/-- An octagonally convex set meets every vertical line between two of its sites, at a height
between theirs. -/
theorem IsOctagonallyConvex.exists_fst_eq {Q : Set (ℤ × ℤ)} (hQ : IsOctagonallyConvex Q)
    {p r : ℤ × ℤ} (hp : p ∈ Q) (hr : r ∈ Q) {t : ℤ} (h₁ : p.1 ≤ t) (h₂ : t ≤ r.1) :
    ∃ q ∈ Q, q.1 = t ∧ min p.2 r.2 ≤ q.2 ∧ q.2 ≤ max p.2 r.2 := by
  let y := max (min p.2 r.2) (max (t - max (p.1 - p.2) (r.1 - r.2))
    (min (p.1 + p.2) (r.1 + r.2) - t))
  have hy₁ : min p.2 r.2 ≤ y := le_max_left _ _
  have hy₂ : y ≤ max p.2 r.2 := by
    simp only [y, max_le_iff]
    refine ⟨by omega, by omega, by omega⟩
  have hy₃ : y ≤ t - min (p.1 - p.2) (r.1 - r.2) := by
    simp only [y, max_le_iff]
    refine ⟨by omega, by omega, by omega⟩
  have hy₄ : y ≤ max (p.1 + p.2) (r.1 + r.2) - t := by
    simp only [y, max_le_iff]
    refine ⟨by omega, by omega, by omega⟩
  have hy₅ : t - max (p.1 - p.2) (r.1 - r.2) ≤ y := le_max_of_le_right (le_max_left _ _)
  have hy₆ : min (p.1 + p.2) (r.1 + r.2) - t ≤ y := le_max_of_le_right (le_max_right _ _)
  refine ⟨(t, y), hQ p hp r hr _ (by simp; omega) (by simp; omega) hy₁ hy₂ (by simp; omega)
    (by simp; omega) (by simp; omega) (by simp; omega), rfl, hy₁, hy₂⟩

/-- Octagonal convexity is invariant under exchanging the coordinates. -/
theorem IsOctagonallyConvex.preimage_swap {Q : Set (ℤ × ℤ)} (hQ : IsOctagonallyConvex Q) :
    IsOctagonallyConvex (Prod.swap ⁻¹' Q) := by
  intro p hp r hr q h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  exact hQ _ hp _ hr q.swap h₃ h₄ h₁ h₂ (by simp; omega) (by simp; omega) (by simp; omega)
    (by simp; omega)

variable {Q : Finset (ℤ × ℤ)} {L : ℕ}

/-- The rows of the dilation of an octagonally convex set are integer intervals. -/
theorem IsOctagonallyConvex.mk_mem_ambientDilation_of_snd_eq
    (hQ : IsOctagonallyConvex (Q : Set (ℤ × ℤ))) {x x' : ℤ × ℤ}
    (hx : x ∈ ambientDilation Q L) (hx' : x' ∈ ambientDilation Q L)
    (h : x.2 = x'.2) {t : ℤ} (h₁ : x.1 ≤ t) (h₂ : t ≤ x'.1) :
    (t, x.2) ∈ ambientDilation Q L := by
  obtain ⟨p, hp, hp₁, hp₂⟩ := mem_ambientDilation.1 hx
  obtain ⟨r, hr, hr₁, hr₂⟩ := mem_ambientDilation.1 hx'
  rw [abs_le] at hp₁ hp₂ hr₁ hr₂
  refine mem_ambientDilation.2 ?_
  by_cases hpt : t - L ≤ p.1
  · exact ⟨p, hp, by rw [abs_le]; omega, by rw [abs_le]; omega⟩
  · obtain ⟨q, hq, hq₁, hq₂, hq₃⟩ := hQ.exists_fst_eq hp hr (t := t - L) (by omega) (by omega)
    exact ⟨q, hq, by rw [abs_le]; omega, by rw [abs_le]; omega⟩

/-- Dilation commutes with exchanging the coordinates. -/
theorem mem_ambientDilation_image_swap {x : ℤ × ℤ} :
    x ∈ ambientDilation (Q.image Prod.swap) L ↔ x.swap ∈ ambientDilation Q L := by
  simp only [mem_ambientDilation, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, h₁, h₂⟩
    exact ⟨q, hq, h₂, h₁⟩
  · rintro ⟨q, hq, h₁, h₂⟩
    exact ⟨q.swap, ⟨q, hq, rfl⟩, h₂, h₁⟩

/-- The columns of the dilation of an octagonally convex set are integer intervals. -/
theorem IsOctagonallyConvex.mk_mem_ambientDilation_of_fst_eq
    (hQ : IsOctagonallyConvex (Q : Set (ℤ × ℤ))) {x x' : ℤ × ℤ}
    (hx : x ∈ ambientDilation Q L) (hx' : x' ∈ ambientDilation Q L)
    (h : x.1 = x'.1) {t : ℤ} (h₁ : x.2 ≤ t) (h₂ : t ≤ x'.2) :
    (x.1, t) ∈ ambientDilation Q L := by
  have hQ' : IsOctagonallyConvex ((Q.image Prod.swap : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    have : ((Q.image Prod.swap : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = Prod.swap ⁻¹' Q := by
      ext z
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_preimage]
      exact ⟨fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw,
        fun hz => ⟨z.swap, hz, Prod.swap_swap z⟩⟩
    rw [this]
    exact hQ.preimage_swap
  have := hQ'.mk_mem_ambientDilation_of_snd_eq (x := x.swap) (x' := x'.swap)
    (mem_ambientDilation_image_swap.2 (by simpa using hx))
    (mem_ambientDilation_image_swap.2 (by simpa using hx')) h h₁ h₂
  simpa using mem_ambientDilation_image_swap.1 this

/-- A finite set of integers no two of which differ by more than `d` has at most `d + 1`
elements. -/
theorem card_le_of_forall_sub_le {s : Finset ℤ} {d : ℕ} (h : ∀ a ∈ s, ∀ b ∈ s, a - b ≤ d) :
    s.card ≤ d + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hsub : s ⊆ Finset.Icc (s.min' hs) (s.min' hs + d) := fun a ha =>
      Finset.mem_Icc.2 ⟨s.min'_le a ha, by have := h a ha _ (s.min'_mem hs); omega⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Int.card_Icc]
    omega

/-- The four unit steps of the square lattice. -/
def latticeSteps : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

theorem card_latticeSteps : latticeSteps.card = 4 := by decide

/-- Adjacent sites of the square lattice differ by a unit step. -/
theorem sub_mem_latticeSteps_of_adj {x y : ℤ × ℤ} (h : (hasse ℤ □ hasse ℤ).Adj x y) :
    y - x ∈ latticeSteps := by
  rw [squareLattice_adj_iff] at h
  simp only [latticeSteps, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_sub,
    Prod.snd_sub]
  omega

private theorem injOn_snd_filter {D : Finset (ℤ × ℤ)}
    (hrow : ∀ x ∈ D, ∀ x' ∈ D, x.2 = x'.2 → ∀ t, x.1 ≤ t → t ≤ x'.1 → (t, x.2) ∈ D)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Set.InjOn Prod.snd (D.filter fun x => x + (σ, 0) ∉ D : Set (ℤ × ℤ)) := by
  have key : ∀ a ∈ D, ∀ b ∈ D, a.2 = b.2 → a.1 < b.1 → a + (σ, 0) ∉ D → b + (σ, 0) ∉ D →
      False := by
    intro a ha b hb h2 hlt hna hnb
    rcases hσ with rfl | rfl
    · refine hna ?_
      convert hrow a ha b hb h2 (a.1 + 1) (by omega) (by omega) using 1
      exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add, add_zero])
    · refine hnb ?_
      convert hrow a ha b hb h2 (b.1 - 1) (by omega) (by omega) using 1
      exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add]; omega)
  intro x hx x' hx' h
  simp only [Finset.mem_coe, Finset.mem_filter] at hx hx'
  rcases lt_trichotomy x.1 x'.1 with hl | hl | hl
  · exact (key x hx.1 x' hx'.1 h hl hx.2 hx'.2).elim
  · exact Prod.ext hl h
  · exact (key x' hx'.1 x hx.1 h.symm hl hx'.2 hx.2).elim

private theorem injOn_fst_filter {D : Finset (ℤ × ℤ)}
    (hcol : ∀ x ∈ D, ∀ x' ∈ D, x.1 = x'.1 → ∀ t, x.2 ≤ t → t ≤ x'.2 → (x.1, t) ∈ D)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Set.InjOn Prod.fst (D.filter fun x => x + (0, σ) ∉ D : Set (ℤ × ℤ)) := by
  have key : ∀ a ∈ D, ∀ b ∈ D, a.1 = b.1 → a.2 < b.2 → a + (0, σ) ∉ D → b + (0, σ) ∉ D →
      False := by
    intro a ha b hb h1 hlt hna hnb
    rcases hσ with rfl | rfl
    · refine hna ?_
      convert hcol a ha b hb h1 (a.2 + 1) (by omega) (by omega) using 1
      exact Prod.ext (by simp only [Prod.fst_add, add_zero]) (by simp only [Prod.snd_add])
    · refine hnb ?_
      convert hcol a ha b hb h1 (b.2 - 1) (by omega) (by omega) using 1
      exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add]; omega)
  intro x hx x' hx' h
  simp only [Finset.mem_coe, Finset.mem_filter] at hx hx'
  rcases lt_trichotomy x.2 x'.2 with hl | hl | hl
  · exact (key x hx.1 x' hx'.1 h hl hx.2 hx'.2).elim
  · exact Prod.ext h hl
  · exact (key x' hx'.1 x hx.1 h.symm hl hx'.2 hx.2).elim

/-- A finite set of sites whose rows and columns are integer intervals, and whose coordinates
each vary by at most `d`, has at most `d + 1` sites leaving it in any one lattice direction. -/
theorem card_filter_add_notMem_le {D : Finset (ℤ × ℤ)}
    (hrow : ∀ x ∈ D, ∀ x' ∈ D, x.2 = x'.2 → ∀ t, x.1 ≤ t → t ≤ x'.1 → (t, x.2) ∈ D)
    (hcol : ∀ x ∈ D, ∀ x' ∈ D, x.1 = x'.1 → ∀ t, x.2 ≤ t → t ≤ x'.2 → (x.1, t) ∈ D)
    {d : ℕ} (hd : ∀ x ∈ D, ∀ x' ∈ D, x.1 - x'.1 ≤ d ∧ x.2 - x'.2 ≤ d)
    {e : ℤ × ℤ} (he : e ∈ latticeSteps) : (D.filter fun x => x + e ∉ D).card ≤ d + 1 := by
  have hsnd {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
      (D.filter fun x => x + (σ, 0) ∉ D).card ≤ d + 1 := by
    rw [← Finset.card_image_of_injOn (injOn_snd_filter hrow hσ)]
    refine card_le_of_forall_sub_le fun a ha b hb => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    exact (hd x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1).2
  have hfst {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
      (D.filter fun x => x + (0, σ) ∉ D).card ≤ d + 1 := by
    rw [← Finset.card_image_of_injOn (injOn_fst_filter hcol hσ)]
    refine card_le_of_forall_sub_le fun a ha b hb => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    exact (hd x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1).1
  simp only [latticeSteps, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hsnd (Or.inl rfl)
  · exact hsnd (Or.inr rfl)
  · exact hfst (Or.inl rfl)
  · exact hfst (Or.inr rfl)

/-- If no site of `S` is an endpoint of a crossing edge of `A`, every crossing edge of `A ∩ S`
leaves `S` itself, in one of the four lattice directions. -/
theorem card_edgeBoundary_inter_le {Λ A S : Finset (ℤ × ℤ)}
    (hS : ∀ x ∈ S, x ∉ cutEndpoints Λ A) :
    (edgeBoundary Λ (A ∩ S)).card ≤
      ∑ e ∈ latticeSteps, (S.filter fun x => x + e ∉ S).card := by
  classical
  have hsub : edgeBoundary Λ (A ∩ S) ⊆ latticeSteps.biUnion fun e =>
      (S.filter fun x => x + e ∉ S).image fun x => (x, x + e) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hadj⟩ := mem_edgeBoundary.1 hxy
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_sdiff, Finset.mem_inter] at hy
    have hyA : y ∈ A := by
      by_contra hyA
      exact hS x hx.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst
        (mem_edgeBoundary.2 ⟨hx.1, Finset.mem_sdiff.2 ⟨hy.1, hyA⟩, hadj⟩)))
    have hyS : y ∉ S := fun hyS => hy.2 ⟨hyA, hyS⟩
    refine Finset.mem_biUnion.2 ⟨y - x, sub_mem_latticeSteps_of_adj hadj, ?_⟩
    refine Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx.2, ?_⟩, ?_⟩
    · rwa [add_sub_cancel]
    · rw [add_sub_cancel]
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun e _ => Finset.card_image_le))

/-- If no site of `S` is an endpoint of a crossing edge of `A`, every crossing edge of
`(A ∩ S) \ (A ∩ S')` leaves `S` or enters `S'`. -/
theorem card_edgeBoundary_inter_sdiff_le {Λ A S S' : Finset (ℤ × ℤ)}
    (hS : ∀ x ∈ S, x ∉ cutEndpoints Λ A) :
    (edgeBoundary Λ ((A ∩ S) \ (A ∩ S'))).card ≤
      ∑ e ∈ latticeSteps, (S.filter fun x => x + e ∉ S).card +
        ∑ e ∈ latticeSteps, (S'.filter fun x => x + e ∉ S').card := by
  classical
  have hsub : edgeBoundary Λ ((A ∩ S) \ (A ∩ S')) ⊆
      (latticeSteps.biUnion fun e =>
        (S.filter fun x => x + e ∉ S).image fun x => (x, x + e)) ∪
      (latticeSteps.biUnion fun e =>
        (S'.filter fun x => x + e ∉ S').image fun x => (x + e, x)) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hadj⟩ := mem_edgeBoundary.1 hxy
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hx hy
    have hyA : y ∈ A := by
      by_contra hyA
      exact hS x hx.1.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst
        (mem_edgeBoundary.2 ⟨hx.1.1, Finset.mem_sdiff.2 ⟨hy.1, hyA⟩, hadj⟩)))
    by_cases hyS : y ∈ S
    · have hyS' : y ∈ S' := by
        by_contra hyS'
        exact hy.2 ⟨hyA, hyS⟩ (fun _ => hyS')
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x - y,
        sub_mem_latticeSteps_of_adj hadj.symm, Finset.mem_image.2 ⟨y,
          Finset.mem_filter.2 ⟨hyS', ?_⟩, ?_⟩⟩)
      · rw [add_sub_cancel]
        exact fun hxS' => hx.2 hx.1.1 hxS'
      · rw [add_sub_cancel]
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨y - x,
        sub_mem_latticeSteps_of_adj hadj, Finset.mem_image.2 ⟨x,
          Finset.mem_filter.2 ⟨hx.1.2, ?_⟩, ?_⟩⟩)
      · rwa [add_sub_cancel]
      · rw [add_sub_cancel]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (add_le_add ?_ ?_)) <;>
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => Finset.card_image_le)

section Template

variable {Ctpl D₀ : ℝ} {n s₀ : ℕ} {T : Finset (ℤ × ℤ)}

/-- The lattice points of a set in the plane at sup-distance at most `d` apart differ by at most
`d` in each coordinate. -/
private theorem sub_le_of_ediam_le {P : Set (ℝ × ℝ)} {d : ℕ} (hP : Metric.ediam P ≤ d)
    {p r : ℤ × ℤ} (hp : ((p.1 : ℝ), (p.2 : ℝ)) ∈ P) (hr : ((r.1 : ℝ), (r.2 : ℝ)) ∈ P) :
    p.1 - r.1 ≤ d ∧ p.2 - r.2 ≤ d := by
  have h := (Metric.edist_le_ediam_of_mem hp hr).trans hP
  rw [edist_dist, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _),
    Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at h
  have h₁ : ((p.1 - r.1 : ℤ) : ℝ) ≤ ((d : ℤ) : ℝ) := by push_cast; exact (abs_le.1 h.1).2
  have h₂ : ((p.2 - r.2 : ℤ) : ℝ) ≤ ((d : ℤ) : ℝ) := by push_cast; exact (abs_le.1 h.2).2
  exact ⟨Int.cast_le.1 h₁, Int.cast_le.1 h₂⟩

private theorem cast_mem_Icc_of_min_le {lo hi : ℝ} {a b c : ℤ} (ha : lo ≤ a ∧ (a : ℝ) ≤ hi)
    (hb : lo ≤ b ∧ (b : ℝ) ≤ hi) (h₁ : min a b ≤ c) (h₂ : c ≤ max a b) :
    lo ≤ c ∧ (c : ℝ) ≤ hi := by
  rcases le_total a b with h | h
  · rw [min_eq_left h] at h₁
    rw [max_eq_right h] at h₂
    exact ⟨ha.1.trans (Int.cast_le.2 h₁), (Int.cast_le.2 h₂).trans hb.2⟩
  · rw [min_eq_right h] at h₁
    rw [max_eq_left h] at h₂
    exact ⟨hb.1.trans (Int.cast_le.2 h₁), (Int.cast_le.2 h₂).trans ha.2⟩

/-- The lattice points of a template piece form an octagonally convex set. -/
theorem IsTemplatePiece.isOctagonallyConvex {P : Set (ℝ × ℝ)} (hP : IsTemplatePiece P) :
    IsOctagonallyConvex {z : ℤ × ℤ | ((z.1 : ℝ), (z.2 : ℝ)) ∈ P} := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, hb⟩ := hP.exists_four_strip_bounds
  intro p hp r hr q h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  simp only [Set.mem_ofPred_eq, hb] at hp hr ⊢
  refine ⟨cast_mem_Icc_of_min_le hp.1 hr.1 h₁ h₂, cast_mem_Icc_of_min_le hp.2.1 hr.2.1 h₃ h₄,
    ?_, ?_⟩
  · have := cast_mem_Icc_of_min_le (a := p.1 + p.2) (b := r.1 + r.2) (by push_cast; exact hp.2.2.1)
      (by push_cast; exact hr.2.2.1) h₅ h₆
    push_cast at this
    exact this
  · have := cast_mem_Icc_of_min_le (a := p.1 - p.2) (b := r.1 - r.2) (by push_cast; exact hp.2.2.2)
      (by push_cast; exact hr.2.2.2) h₇ h₈
    push_cast at this
    exact this

/-- In a template with constant `C_tpl ≥ 24` and `L ≤ s₀`, the dilation `T_L` has at most `n / 2`
outgoing lattice edges: each of the `N₀` dilated pieces has rows and columns that are integer
intervals, hence at most `s₀ + 2L + 1` outgoing edges in each of the four directions. -/
theorem IsTemplate.two_mul_sum_card_filter_le (hT : IsTemplate Ctpl n s₀ T) (hC : 24 ≤ Ctpl)
    {L : ℕ} (hL : L ≤ s₀) :
    2 * ∑ e ∈ latticeSteps,
      ((ambientDilation T L).filter fun x => x + e ∉ ambientDilation T L).card ≤ n := by
  classical
  obtain ⟨-, -, -, N₀, P, -, hP, hTP, hscale, -⟩ := hT
  have hmemT : ∀ z : ℤ × ℤ, z ∈ T ↔ ∃ i, ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i := fun z => by
    simpa using Set.ext_iff.1 hTP z
  let Q : Fin N₀ → Finset (ℤ × ℤ) := fun i => T.filter fun z => ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i
  have hconv (i : Fin N₀) : IsOctagonallyConvex (Q i : Set (ℤ × ℤ)) := by
    have hQ : (Q i : Set (ℤ × ℤ)) = {z : ℤ × ℤ | ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i} := by
      ext z
      simp only [Q, Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨And.right, fun h => ⟨(hmemT z).2 ⟨i, h⟩, h⟩⟩
    rw [hQ]
    exact (hP i).1.isOctagonallyConvex
  have hdiam (i : Fin N₀) : ∀ x ∈ ambientDilation (Q i) L, ∀ x' ∈ ambientDilation (Q i) L,
      x.1 - x'.1 ≤ ((s₀ + 2 * L : ℕ) : ℤ) ∧ x.2 - x'.2 ≤ ((s₀ + 2 * L : ℕ) : ℤ) := by
    intro x hx x' hx'
    obtain ⟨p, hp, hp₁, hp₂⟩ := mem_ambientDilation.1 hx
    obtain ⟨r, hr, hr₁, hr₂⟩ := mem_ambientDilation.1 hx'
    have h := sub_le_of_ediam_le (hP i).2 (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hr).2
    rw [abs_le] at hp₁ hp₂ hr₁ hr₂
    push_cast
    omega
  have hdir (e : ℤ × ℤ) (he : e ∈ latticeSteps) :
      ((ambientDilation T L).filter fun x => x + e ∉ ambientDilation T L).card ≤
        N₀ * (s₀ + 2 * L + 1) := by
    have hsub : ((ambientDilation T L).filter fun x => x + e ∉ ambientDilation T L) ⊆
        Finset.univ.biUnion fun i =>
          (ambientDilation (Q i) L).filter fun x => x + e ∉ ambientDilation (Q i) L := by
      intro x hx
      obtain ⟨hx, hxe⟩ := Finset.mem_filter.1 hx
      obtain ⟨t, ht, ht₁, ht₂⟩ := mem_ambientDilation.1 hx
      obtain ⟨i, hi⟩ := (hmemT t).1 ht
      refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2
        ⟨mem_ambientDilation.2 ⟨t, Finset.mem_filter.2 ⟨ht, hi⟩, ht₁, ht₂⟩, fun h => hxe ?_⟩⟩
      exact ambientDilation_mono_left (Finset.filter_subset _ _) L h
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin N₀, (s₀ + 2 * L + 1) := Finset.sum_le_sum fun i _ =>
          card_filter_add_notMem_le
            (fun _ hx _ hx' h _ h₁ h₂ =>
              (hconv i).mk_mem_ambientDilation_of_snd_eq hx hx' h h₁ h₂)
            (fun _ hx _ hx' h _ h₁ h₂ =>
              (hconv i).mk_mem_ambientDilation_of_fst_eq hx hx' h h₁ h₂)
            (hdiam i) he
      _ = N₀ * (s₀ + 2 * L + 1) := by simp
  have hsum := Finset.sum_le_card_nsmul _ _ _ hdir
  rw [card_latticeSteps, smul_eq_mul] at hsum
  have hscale' : 24 * N₀ * (s₀ + 1) ≤ n := by
    have : (24 : ℝ) * N₀ * (s₀ + 1) ≤ n :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))
        (by positivity)).trans hscale
    exact_mod_cast this
  have h3 : s₀ + 2 * L + 1 ≤ 3 * (s₀ + 1) := by omega
  calc 2 * _ ≤ 2 * (4 * (N₀ * (s₀ + 2 * L + 1))) := Nat.mul_le_mul_left _ hsum
    _ ≤ 2 * (4 * (N₀ * (3 * (s₀ + 1)))) := by gcongr
    _ = 24 * N₀ * (s₀ + 1) := by ring
    _ ≤ n := hscale'

/-- A dilation `T_L` with `L ≤ s₀` of a template separated from the cut contains no endpoint of
a crossing edge. -/
theorem notMem_cutEndpoints_of_isSeparatedFromCut {Λ A : Finset (ℤ × ℤ)}
    (hsep : IsSeparatedFromCut D₀ s₀ Λ A T) (hD : 1 ≤ D₀) {L : ℕ} (hL : L ≤ s₀) :
    ∀ x ∈ ambientDilation T L, x ∉ cutEndpoints Λ A := by
  intro x hx hxZ
  obtain ⟨t, ht, h₁, h₂⟩ := mem_ambientDilation.1 hx
  have h := (lt_ambientEDist_iff ENNReal.ofReal_lt_top).1 hsep t ht x hxZ
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff'] at h
  have hd : dist t x ≤ L := dist_le_natCast_iff.2 ⟨by rwa [abs_sub_comm], by rwa [abs_sub_comm]⟩
  have hL' : (L : ℝ) ≤ s₀ := by exact_mod_cast hL
  have hs : (0 : ℝ) ≤ s₀ := Nat.cast_nonneg _
  nlinarith [h.1]

/-- A template of diameter at most `n` has at most `(2 (n + L) + 1)²` sites in its dilation
`T_L`. -/
theorem IsTemplate.card_ambientDilation_le_sq (hT : IsTemplate Ctpl n s₀ T) (L : ℕ) :
    (ambientDilation T L).card ≤ (2 * (n + L) + 1) ^ 2 := by
  obtain ⟨-, -, ⟨t₀, ht₀⟩, -, -, -, -, -, -, hdiam⟩ := hT
  set m : ℤ := ((n + L : ℕ) : ℤ)
  have hsub : ambientDilation T L ⊆ Finset.Icc (t₀ - (m, m)) (t₀ + (m, m)) := by
    intro x hx
    obtain ⟨t, ht, h₁, h₂⟩ := mem_ambientDilation.1 hx
    have h := (Metric.edist_le_ediam_of_mem (Finset.mem_coe.2 ht) (Finset.mem_coe.2 ht₀)).trans
      hdiam
    rw [edist_dist, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _),
      dist_le_natCast_iff, abs_le, abs_le] at h
    rw [abs_le] at h₁ h₂
    simp only [Finset.mem_Icc, Prod.le_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add,
      Prod.snd_add, m]
    push_cast
    omega
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [card_Icc_eq_mul]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, m]
  have : t₀.1 + ((n + L : ℕ) : ℤ) + 1 - (t₀.1 - ((n + L : ℕ) : ℤ)) =
      ((2 * (n + L) + 1 : ℕ) : ℤ) := by push_cast; ring
  have h' : t₀.2 + ((n + L : ℕ) : ℤ) + 1 - (t₀.2 - ((n + L : ℕ) : ℤ)) =
      ((2 * (n + L) + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, h', Int.toNat_natCast, sq]

/-- A template with constant `C_tpl ≥ 24` has `24 (s₀ + 1) ≤ n`. -/
theorem IsTemplate.twentyFour_mul_add_one_le (hT : IsTemplate Ctpl n s₀ T) (hC : 24 ≤ Ctpl) :
    24 * (s₀ + 1) ≤ n := by
  obtain ⟨-, -, -, N₀, P, hN₀, -, -, hscale, -⟩ := hT
  have : (24 : ℝ) * 1 * (s₀ + 1) ≤ n :=
    (mul_le_mul_of_nonneg_right (mul_le_mul hC (by exact_mod_cast hN₀) zero_le_one
      (by linarith)) (by positivity)).trans hscale
  have : (24 : ℝ) * (s₀ + 1) ≤ n := by linarith
  exact_mod_cast this

end Template

/-- **The cut and size assertions of Proposition 9.6** [OAI265, §9.5, from Lemma 9.4].  For a
template `T` with parameters `(n, s₀)` and template constant `C_tpl ≥ 24`, separated from the
cut `A` at a clearance constant `D₀ ≥ 1`, and any `L ≤ s₀`, the cuts of `A ∩ T` and
`A ∩ T_L` have at most `4n` edges, the cut of `(A ∩ T_L) \ (A ∩ T)` at most `8n`, and
`|A ∩ T_L| ≤ 10 n²`. -/
theorem IsTemplate.collar_cut_card_le {Ctpl D₀ : ℝ} {n s₀ : ℕ} {T : Finset (ℤ × ℤ)}
    (hT : IsTemplate Ctpl n s₀ T) (hC : 24 ≤ Ctpl) {Λ A : Finset (ℤ × ℤ)}
    (hsep : IsSeparatedFromCut D₀ s₀ Λ A T) (hD : 1 ≤ D₀) {L : ℕ} (hL : L ≤ s₀) :
    (edgeBoundary Λ (A ∩ T)).card ≤ 4 * n ∧
    (edgeBoundary Λ (A ∩ ambientDilation T L)).card ≤ 4 * n ∧
    (edgeBoundary Λ ((A ∩ ambientDilation T L) \ (A ∩ T))).card ≤ 8 * n ∧
    (A ∩ ambientDilation T L).card ≤ 10 * n ^ 2 := by
  have hZ := notMem_cutEndpoints_of_isSeparatedFromCut hsep hD hL
  have hZ₀ := notMem_cutEndpoints_of_isSeparatedFromCut hsep hD (Nat.zero_le s₀)
  rw [ambientDilation_zero] at hZ₀
  have hB := hT.two_mul_sum_card_filter_le hC hL
  have hB₀ := hT.two_mul_sum_card_filter_le hC (Nat.zero_le s₀)
  rw [ambientDilation_zero] at hB₀
  have h₁ := card_edgeBoundary_inter_le (Λ := Λ) (A := A) hZ₀
  have h₂ := card_edgeBoundary_inter_le (Λ := Λ) (A := A) hZ
  have h₃ := card_edgeBoundary_inter_sdiff_le (Λ := Λ) (A := A) (S' := T) hZ
  have hn := hT.twentyFour_mul_add_one_le hC
  have hcard := hT.card_ambientDilation_le_sq L
  refine ⟨by omega, by omega, by omega, ?_⟩
  refine (Finset.card_le_card Finset.inter_subset_right).trans (hcard.trans ?_)
  have : 2 * L + 1 ≤ n := by omega
  nlinarith

section Pieces

variable {Ctpl : ℝ} {n s₀ : ℕ} {T : Finset (ℤ × ℤ)}

/-- A template is the union of `N₀` octagonally convex sets of sites, the lattice points of its
pieces, whose coordinates each vary by at most `s₀`, with `C_tpl N₀ (s₀ + 1) ≤ n`. -/
theorem IsTemplate.exists_pieces (hT : IsTemplate Ctpl n s₀ T) :
    ∃ (N₀ : ℕ) (Q : Fin N₀ → Finset (ℤ × ℤ)), T = Finset.univ.biUnion Q ∧
      (∀ i, IsOctagonallyConvex (Q i : Set (ℤ × ℤ))) ∧
      (∀ i, ∀ x ∈ Q i, ∀ x' ∈ Q i, x.1 - x'.1 ≤ s₀ ∧ x.2 - x'.2 ≤ s₀) ∧
      Ctpl * N₀ * (s₀ + 1) ≤ n := by
  classical
  obtain ⟨-, -, -, N₀, P, -, hP, hTP, hscale, -⟩ := hT
  have hmemT : ∀ z : ℤ × ℤ, z ∈ T ↔ ∃ i, ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i := fun z => by
    simpa using Set.ext_iff.1 hTP z
  refine ⟨N₀, fun i => T.filter fun z => ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i, ?_, fun i => ?_,
    fun i x hx x' hx' => ?_, hscale⟩
  · ext z
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun h => ((hmemT z).1 h).imp fun i hi => ⟨h, hi⟩, fun ⟨_, h, _⟩ => h⟩
  · have hQ : ((T.filter fun z => ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i : Finset (ℤ × ℤ)) :
        Set (ℤ × ℤ)) = {z : ℤ × ℤ | ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i} := by
      ext z
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨And.right, fun h => ⟨(hmemT z).2 ⟨i, h⟩, h⟩⟩
    rw [hQ]
    exact (hP i).1.isOctagonallyConvex
  · exact sub_le_of_ediam_le (hP i).2 (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hx').2

end Pieces

end OpenAI
