/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/ScanHistories.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's
domain encoding: TNLean's `Site Λ` and `domainGraph Λ` are `↥(Λ : Set (ℤ × ℤ))` and
`(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`, and `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, as in
`OpenAI.Scan.SupportLocalization`. TNLean's unordered induced-graph edge boundary
`edgeBoundary Λ X` of `X : Finset (Site Λ)` is this project's ordered
`OpenAI.edgeBoundary Λ (X.map (Function.Embedding.subtype _))`, which has the same
cardinality (`OpenAI.card_image_mk_edgeBoundary`); this changes the statement of the field
`CollarScan.HistoryProperties.cut_bounds` and its pre-charge companion. The cut-edge bounds
`state_cut_bounds_domainGraph` and `oldChargeState_cut_bounds_domainGraph` of
`TNLean/PEPS/AreaLaw/Scan/StatusCutBounds.lean`, with the prefix bounds of
`TNLean/PEPS/AreaLaw/Scan/PrefixBoundary.lean` and the edge-boundary calculus of
`TNLean/PEPS/AreaLaw/EdgeBoundaryCalculus.lean` they use, are not in `OpenAI.Scan.StatusCutBounds`;
they are restated and reproved here over `OpenAI.edgeBoundary`, keeping the TNLean names.
-/
import OpenAI.Scan.BadOldHistoryDecay
import OpenAI.Scan.DesignatedDilution
import OpenAI.Scan.PhysicalBandCommutation
import OpenAI.Scan.SplitCounting
import OpenAI.Scan.StatusCutBounds
import OpenAI.Scan.AssignedLead
import OpenAI.Scan.TerminalSplits
import OpenAI.Corollary
import OpenAI.Geometry.TemplateCollar

/-!
# Geometry and probabilities of the collar scan

This module states Lemma 9.1 (`scanner:histories`) of the area-law manuscript
for the actual finite collar scan. The structure `CollarScan.HistoryProperties`
lists the four assertions for one scanner, with explicit constants. The theorem
`eventually_historyProperties` proves them at the source scales
`L = ⌊n^(1-ℓ)⌋`, `m = ⌊n^μ⌋`, `K = ⌊L/(8m)⌋`, `D = ⌈n^κ⌉`, `r₀ = ⌈C_r log² n⌉`
and `M = ⌈C₁ n D⌉`, under the test geometry `scanner:test-geometry`, for all
sufficiently large `n`.

The threshold on `n` depends only on the exponents, the radius coefficient, the
padding constant, the target-size constant, the anchor multiplicity and the
inverse power. It is chosen before the finite domain, the cut, the target, the
interaction labels and the scanner.

The constants are explicit: prefix comparisons differ by at most `3nD` sites,
status cuts have at most `40nD` edges, at most `10bKnD` labelled terms split,
the split probability is at most `10D/m`, and a split term is sampled with
probability at least `c/(nD)` for `c = 1/(2(C₁+1))`. Here `b` bounds the number
of labels with a fixed anchor; the source's padding constant `C₁` is taken large
enough for every candidate list by requiring `3b ≤ C₁`.

All probabilities are classical path probabilities of the finite history tree.
No transported replica state enters these statements.

## Implementation notes

The cut-edge counts of item 2 are those of the ordered edge boundary `OpenAI.edgeBoundary` of
the image of a region in `ℤ²`, which counts each crossing edge once. The bounds on full and
positive-depth prefixes, and the boundary calculus behind them, are proved first.

The proofs are independently written from the manuscript; no Lean declaration
or proof is copied or adapted from OpenAI's implementation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 9.1, `08-scanner.tex`, lines 195–221 (statement) and 223–347 (proof),
at `openai/math@adc7f124`.
-/

open scoped symmDiff

/-! ## Edge-boundary calculus on the ordered edge boundary -/

namespace OpenAI

open SimpleGraph

/-- Changing a region by a symmetric difference `D` changes its edge boundary by at most
four edges per site of `D`. -/
theorem card_edgeBoundary_le_add_four_mul_symmDiff (Λ X Y : Finset (ℤ × ℤ)) :
    (edgeBoundary Λ X).card ≤ (edgeBoundary Λ Y).card + 4 * (X ∆ Y).card := by
  classical
  set E := (edgeBoundary Λ X).filter fun p ↦ p.1 ∈ X ∆ Y ∨ p.2 ∈ X ∆ Y
  have hsub : edgeBoundary Λ X ⊆ edgeBoundary Λ Y ∪ E := by
    intro p hp
    by_cases hpY : p ∈ edgeBoundary Λ Y
    · exact Finset.mem_union_left _ hpY
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, ?_⟩)
    obtain ⟨hx, hy, hadj⟩ := mem_edgeBoundary.mp hp
    rw [Finset.mem_sdiff] at hy
    by_cases hxY : p.1 ∈ Y
    · right
      have hyY : p.2 ∈ Y := by
        by_contra hyY
        exact hpY (mem_edgeBoundary.mpr ⟨hxY, Finset.mem_sdiff.mpr ⟨hy.1, hyY⟩, hadj⟩)
      exact Finset.mem_symmDiff.mpr (Or.inr ⟨hyY, hy.2⟩)
    · exact Or.inl (Finset.mem_symmDiff.mpr (Or.inl ⟨hx, hxY⟩))
  let f : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) := fun p ↦ if p.1 ∈ X ∆ Y then p else p.swap
  have hinj : Set.InjOn f E := by
    intro p hp p' hp' hpp
    rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    have hpX := (mem_edgeBoundary.mp hp.1).1
    have hpX' := (Finset.mem_sdiff.mp (mem_edgeBoundary.mp hp.1).2.1).2
    have hqX := (mem_edgeBoundary.mp hp'.1).1
    have hqX' := (Finset.mem_sdiff.mp (mem_edgeBoundary.mp hp'.1).2.1).2
    simp only [f] at hpp
    split_ifs at hpp with h1 h2 h2
    · exact hpp
    · exact absurd (congrArg Prod.fst hpp ▸ hpX) (by simpa using hqX')
    · exact absurd (congrArg Prod.fst hpp ▸ hqX) (by simpa using hpX')
    · exact Prod.swap_injective hpp
  have hadj : ∀ p ∈ E.image f, (hasse ℤ □ hasse ℤ).Adj p.1 p.2 := by
    intro p hp
    obtain ⟨p, hpE, rfl⟩ := Finset.mem_image.mp hp
    have h := (mem_edgeBoundary.mp (Finset.mem_filter.mp hpE).1).2.2
    simp only [f]
    split_ifs
    · exact h
    · exact h.symm
  have hfst : (E.image f).image Prod.fst ⊆ X ∆ Y := by
    intro z hz
    obtain ⟨_, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hpE, rfl⟩ := Finset.mem_image.mp hp
    have h := (Finset.mem_filter.mp hpE).2
    simp only [f]
    split_ifs with h1
    · exact h1
    · exact h.resolve_left h1
  have hE : E.card ≤ 4 * (X ∆ Y).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (card_le_four_mul_card_image_fst hadj).trans
      (Nat.mul_le_mul_left 4 (Finset.card_le_card hfst))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hE _))

/-- Removing a region `Y` from `X ⊆ Λ` adds at most the edges of `∂Y`. -/
theorem card_edgeBoundary_sdiff_le {Λ X : Finset (ℤ × ℤ)} (hX : X ⊆ Λ) (Y : Finset (ℤ × ℤ)) :
    (edgeBoundary Λ (X \ Y)).card ≤ (edgeBoundary Λ X).card + (edgeBoundary Λ Y).card := by
  classical
  have hsub : edgeBoundary Λ (X \ Y) ⊆
      edgeBoundary Λ X ∪ (edgeBoundary Λ Y).image Prod.swap := by
    intro p hp
    obtain ⟨hx, hy, hadj⟩ := mem_edgeBoundary.mp hp
    rw [Finset.mem_sdiff] at hx hy
    by_cases hyX : p.2 ∈ X
    · have hyY : p.2 ∈ Y := by
        by_contra hyY
        exact hy.2 (Finset.mem_sdiff.mpr ⟨hyX, hyY⟩)
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.swap, ?_, p.swap_swap⟩)
      exact mem_edgeBoundary.mpr ⟨hyY, Finset.mem_sdiff.mpr ⟨hX hx.1, hx.2⟩, hadj.symm⟩
    · exact Finset.mem_union_left _ (mem_edgeBoundary.mpr ⟨hx.1,
        Finset.mem_sdiff.mpr ⟨hy.1, hyX⟩, hadj⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_image_le _))

/-- The complement of `X ⊆ Λ` in `Λ` has the same edge boundary as `X`, with each edge
reversed. -/
theorem card_edgeBoundary_sdiff_left {Λ X : Finset (ℤ × ℤ)} (hX : X ⊆ Λ) :
    (edgeBoundary Λ (Λ \ X)).card = (edgeBoundary Λ X).card := by
  classical
  have h : edgeBoundary Λ (Λ \ X) = (edgeBoundary Λ X).image Prod.swap := by
    ext p
    rw [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨hx, hy, hadj⟩ := mem_edgeBoundary.mp hp
      rw [Finset.sdiff_sdiff_eq_self hX] at hy
      exact ⟨p.swap, mem_edgeBoundary.mpr ⟨hy, hx, hadj.symm⟩, p.swap_swap⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hx, hy, hadj⟩ := mem_edgeBoundary.mp hq
      refine mem_edgeBoundary.mpr ⟨hy, ?_, hadj.symm⟩
      rwa [Finset.sdiff_sdiff_eq_self hX]
  rw [h, Finset.card_image_of_injective _ Prod.swap_injective]

end OpenAI

/-! ## Edge boundaries of deterministic depth prefixes -/

namespace OpenAI.Scan

open SimpleGraph

/-- A lattice step moves a site of `T_r` into `T_{r+1}`. -/
theorem add_mem_ambientDilation_succ {T : Finset (ℤ × ℤ)} {r : ℕ} {x e : ℤ × ℤ}
    (hx : x ∈ ambientDilation T r) (he : e ∈ latticeSteps) :
    x + e ∈ ambientDilation T (r + 1) := by
  obtain ⟨t, ht, h1, h2⟩ := mem_ambientDilation.mp hx
  refine mem_ambientDilation.mpr ⟨t, ht, ?_⟩
  simp only [latticeSteps, Finset.mem_insert, Finset.mem_singleton] at he
  rw [abs_le] at h1 h2
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [Prod.fst_add, Prod.snd_add, abs_le] <;> push_cast <;> omega

/-- Sites of `T_j` leaving it in one lattice direction lie in the last layer
`T_j \ T_{j-1}` when `j ≥ 1`, and inject into the first layer `T_1 \ T` when `j = 0`. -/
private theorem card_filter_add_notMem_ambientDilation_le (T : Finset (ℤ × ℤ)) {n L : ℕ}
    (hL : 1 ≤ L) (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    {j : ℕ} (hj : j ≤ L) {e : ℤ × ℤ} (he : e ∈ latticeSteps) :
    ((ambientDilation T j).filter fun x ↦ x + e ∉ ambientDilation T j).card ≤ n := by
  classical
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hfirst := hrow 1 le_rfl hL
    simp only [Nat.sub_self, ambientDilation_zero] at hfirst
    refine le_trans ?_ hfirst
    refine Finset.card_le_card_of_injOn (· + e) (fun x hx ↦ ?_)
      (fun x _ y _ h ↦ add_right_cancel h)
    rw [Finset.mem_coe, Finset.mem_filter, ambientDilation_zero] at hx
    rw [Finset.mem_coe, Finset.mem_sdiff]
    have h1 := add_mem_ambientDilation_succ (T := T) (r := 0) (x := x)
      (by rw [ambientDilation_zero]; exact hx.1) he
    exact ⟨h1, hx.2⟩
  · refine le_trans (Finset.card_le_card fun x hx ↦ ?_) (hrow j hj0 hj)
    rw [Finset.mem_filter] at hx
    refine Finset.mem_sdiff.mpr ⟨hx.1, fun hx' ↦ hx.2 ?_⟩
    have := add_mem_ambientDilation_succ hx' he
    rwa [Nat.sub_add_cancel hj0] at this

/-- The scanner clearance excludes actual cut endpoints from every permitted dilation.
Source: `08-scanner.tex`, lines 43–48 and 254–255. -/
theorem disjoint_ambientDilation_boundaryEndpoints_of_clearance
    (Λ T A : Finset (ℤ × ℤ)) (L r₀ : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {j : ℕ} (hj : j ≤ L) :
    Disjoint (ambientDilation T j) (cutEndpoints Λ A) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzcut
  obtain ⟨t, ht, h1, h2⟩ := mem_ambientDilation.mp hz
  have hfar := hclear t ht z hzcut
  simp only [ambientSupDistance, lt_max_iff] at hfar
  rw [abs_sub_comm t.1, abs_sub_comm t.2] at hfar
  push_cast at hfar
  omega

/-- The image in `ℤ²` of a set of sites of `Λ` lies in `Λ`. -/
theorem map_subtype_subset (Λ : Finset (ℤ × ℤ)) (X : Finset (↥(Λ : Set (ℤ × ℤ)))) :
    X.map (Function.Embedding.subtype _) ⊆ Λ := by
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
  exact x.2

/-- The image in `ℤ²` of the complement of a set of sites of `Λ` is its complement in `Λ`. -/
theorem map_subtype_compl (Λ : Finset (ℤ × ℤ)) (X : Finset (↥(Λ : Set (ℤ × ℤ)))) :
    Xᶜ.map (Function.Embedding.subtype _) = Λ \ X.map (Function.Embedding.subtype _) := by
  ext z
  simp only [Finset.mem_map, Finset.mem_compl, Function.Embedding.coe_subtype,
    Finset.mem_sdiff, not_exists, not_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun y hy hyx ↦ hx (Subtype.ext hyx ▸ hy)⟩
  · rintro ⟨hz, hzX⟩
    exact ⟨⟨z, hz⟩, fun h ↦ hzX _ h rfl, rfl⟩

/-- Full physical depth prefixes have at most `4n` edges. The source hypotheses
are ambient row counts and clearance at actual cut endpoints; no boundary
estimate is an input. Negative fronts give the empty prefix, and the zero front
uses the first positive row. Source: Lemma 9.1(2), lines 251–255. -/
theorem card_edgeBoundary_depthPrefix_le (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset (↥(Λ : Set (ℤ × ℤ)))) {n L r₀ : ℕ} (hL : 1 ≤ L)
    (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {j : ℤ} (hj : j ≤ L) :
    (edgeBoundary Λ ((depthPrefix A (fun x ↦ ambientDepth T hT x.val) j).map
      (Function.Embedding.subtype _))).card ≤ 4 * n := by
  classical
  by_cases hj0 : 0 ≤ j
  · lift j to ℕ using hj0
    have hjL : j ≤ L := by exact_mod_cast hj
    have heq : (depthPrefix A (fun x ↦ ambientDepth T hT x.val) j).map
        (Function.Embedding.subtype _) =
        A.map (Function.Embedding.subtype _) ∩ ambientDilation T j := by
      ext z
      simp only [depthPrefix, Finset.mem_map, Finset.mem_filter, Finset.mem_inter,
        Function.Embedding.coe_subtype, ambientDepth_le_iff_mem_dilation]
      constructor
      · rintro ⟨x, ⟨hx, hxj⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxj⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxj⟩
        exact ⟨x, ⟨hx, hxj⟩, rfl⟩
    rw [heq]
    have hdisj := disjoint_ambientDilation_boundaryEndpoints_of_clearance Λ T _ L r₀ hclear hjL
    refine (card_edgeBoundary_inter_le fun x hx ↦ Finset.disjoint_left.mp hdisj hx).trans ?_
    have hcard : latticeSteps.card = 4 := by decide
    calc
      _ ≤ latticeSteps.card • n := Finset.sum_le_card_nsmul _ _ _ fun e he ↦
          card_filter_add_notMem_ambientDilation_le T hL hrow hjL he
      _ = 4 * n := by rw [hcard, smul_eq_mul]
  · have heq : depthPrefix A (fun x ↦ ambientDepth T hT x.val) j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hd : ambientDepth T hT x.val ≤ j := (Finset.mem_filter.mp hx).2
      have hn := ambientDepth_nonneg T hT x.val
      omega
    rw [heq, Finset.map_empty]
    simp [edgeBoundary]

/-- Positive-depth prefixes remove the zero-depth prefix from the full prefix. -/
theorem positiveDepthPrefix_eq_sdiff {V : Type*} [DecidableEq V]
    (A : Finset V) (depth : V → ℤ) (j : ℤ) :
    positiveDepthPrefix A depth j = depthPrefix A depth j \ depthPrefix A depth 0 := by
  ext x
  simp only [positiveDepthPrefix, depthPrefix, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hx : x ∈ A <;> simp [hx, not_le, and_comm]

/-- Positive-depth physical prefixes have at most `8n` edges, including the
zero and negative fronts. The two contributions are the last included row
and the first positive row. Source: Lemma 9.1(2), lines 251–255. -/
theorem card_edgeBoundary_positiveDepthPrefix_le (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset (↥(Λ : Set (ℤ × ℤ)))) {n L r₀ : ℕ} (hL : 1 ≤ L)
    (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {j : ℤ} (hj : j ≤ L) :
    (edgeBoundary Λ ((positiveDepthPrefix A (fun x ↦ ambientDepth T hT x.val) j).map
      (Function.Embedding.subtype _))).card ≤ 8 * n := by
  classical
  rw [positiveDepthPrefix_eq_sdiff, Finset.map_sdiff]
  have hjbound := card_edgeBoundary_depthPrefix_le Λ T hT A hL hrow hclear hj
  have hzero := card_edgeBoundary_depthPrefix_le Λ T hT A hL hrow hclear
    (j := 0) (by omega)
  have hdiff := card_edgeBoundary_sdiff_le
    (map_subtype_subset Λ (depthPrefix A (fun x ↦ ambientDepth T hT x.val) j))
    ((depthPrefix A (fun x ↦ ambientDepth T hT x.val) 0).map (Function.Embedding.subtype _))
  omega

end OpenAI.Scan

/-! ## Physical cut-edge bounds for actual scan statuses -/

namespace OpenAI.Scan

open SimpleGraph

private theorem physical_status_cut_bounds {Λ T : Finset (ℤ × ℤ)}
    (hT : T.Nonempty) (A : Finset (↥(Λ : Set (ℤ × ℤ)))) (depth : ↥(Λ : Set (ℤ × ℤ)) → ℤ)
    (hdepth : depth = fun x ↦ ambientDepth T hT x.val)
    (σ : PhysicalPartition (↥(Λ : Set (ℤ × ℤ)))) {n D L r₀ : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (jN jF : ℤ) (hjN : jN ≤ L) (hjF : jF ≤ L)
    (hpos : ∀ x, σ x = none → 0 < depth x)
    (hP : ((receiving σ false) ∆ depthPrefix A depth jN).card ≤ 3 * n * D)
    (hPY : ((receiving σ false ∪ middle σ) ∆ depthPrefix A depth jF).card ≤ 3 * n * D)
    (hU : ((positiveNear depth σ) ∆ positiveDepthPrefix A depth jN).card ≤ 3 * n * D)
    (hUY : ((positiveNearMiddle depth σ) ∆ positiveDepthPrefix A depth jF).card ≤
      3 * n * D) :
    (edgeBoundary Λ ((positiveNear depth σ).map
      (Function.Embedding.subtype _))).card ≤
      20 * n * D ∧
    (edgeBoundary Λ ((positiveNearMiddle depth σ).map
      (Function.Embedding.subtype _))).card ≤
      20 * n * D ∧
    (edgeBoundary Λ ((middle σ).map (Function.Embedding.subtype _))).card ≤ 40 * n * D ∧
    (edgeBoundary Λ ((receiving σ false).map
      (Function.Embedding.subtype _))).card ≤
      16 * n * D ∧
    (edgeBoundary Λ ((receiving σ true).map
      (Function.Embedding.subtype _))).card ≤
      16 * n * D := by
  classical
  have hsymm (X Y : Finset (↥(Λ : Set (ℤ × ℤ)))) :
      (edgeBoundary Λ (X.map (Function.Embedding.subtype _))).card ≤
        (edgeBoundary Λ (Y.map (Function.Embedding.subtype _))).card + 4 * (X ∆ Y).card := by
    have h := card_edgeBoundary_le_add_four_mul_symmDiff Λ
      (X.map (Function.Embedding.subtype _)) (Y.map (Function.Embedding.subtype _))
    have hmap : (X ∆ Y).map (Function.Embedding.subtype _) =
        X.map (Function.Embedding.subtype _) ∆ Y.map (Function.Embedding.subtype _) := by
      simp only [symmDiff_def, Finset.sup_eq_union, Finset.map_union, Finset.map_sdiff]
    rwa [← hmap, Finset.card_map] at h
  have hbase (j : ℤ) (hj : j ≤ L) :
      (edgeBoundary Λ ((depthPrefix A depth j).map (Function.Embedding.subtype _))).card ≤
        4 * n := by
    subst hdepth
    exact card_edgeBoundary_depthPrefix_le Λ T hT A hL hrows hclear hj
  have hpositive (j : ℤ) (hj : j ≤ L) :
      (edgeBoundary Λ ((positiveDepthPrefix A depth j).map
        (Function.Embedding.subtype _))).card ≤ 8 * n := by
    subst hdepth
    exact card_edgeBoundary_positiveDepthPrefix_le Λ T hT A hL hrows hclear hj
  have hnD : n ≤ n * D := by simpa using Nat.mul_le_mul_left n hD
  have hU' : (edgeBoundary Λ ((positiveNear depth σ).map
      (Function.Embedding.subtype _))).card ≤ 20 * n * D := by
    have := hsymm (positiveNear depth σ) (positiveDepthPrefix A depth jN)
    have := hpositive jN hjN
    nlinarith
  have hUY' : (edgeBoundary Λ ((positiveNearMiddle depth σ).map
      (Function.Embedding.subtype _))).card ≤ 20 * n * D := by
    have := hsymm (positiveNearMiddle depth σ) (positiveDepthPrefix A depth jF)
    have := hpositive jF hjF
    nlinarith
  refine ⟨hU', hUY', ?_, ?_, ?_⟩
  · rw [middle_eq_positiveNearMiddle_sdiff_positiveNear depth σ hpos, Finset.map_sdiff]
    have := card_edgeBoundary_sdiff_le (map_subtype_subset Λ (positiveNearMiddle depth σ))
      ((positiveNear depth σ).map (Function.Embedding.subtype _))
    nlinarith
  · have := hsymm (receiving σ false) (depthPrefix A depth jN)
    have := hbase jN hjN
    nlinarith
  · rw [receiving_far_eq_compl, map_subtype_compl,
      card_edgeBoundary_sdiff_left (map_subtype_subset Λ _)]
    have := hsymm (receiving σ false ∪ middle σ) (depthPrefix A depth jF)
    have := hbase jF hjF
    nlinarith

namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- Every completed physical status has at most `40nD` cut edges in
each of U, UY, Y, P₀, V, with sharper constants for all but Y. No prefix,
edge-count, or good-history certificate is assumed. -/
theorem state_cut_bounds_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K)
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    (edgeBoundary Λ ((positiveNear S.depth (S.state h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((positiveNearMiddle S.depth (S.state h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((middle (S.state h g)).map
      (Function.Embedding.subtype _))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.state h g) false).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.state h g) true).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D := by
  have hb := S.prefix_uncertainty_rows h.1 g hn hk hr hDpos hD hL
  have ha := state_prefix_approximation_domainGraph hT S hgraph hdepth
    h g hn hk hr hDpos hD hL hrows
  have hLpos : 1 ≤ L := (Nat.mul_pos (Nat.mul_pos (by decide) g.pos) (by omega)).trans_le hL
  exact physical_status_cut_bounds hT S.A S.depth hdepth (S.state h g) hLpos hDpos
    hrows hclear (S.front g (h.1 g) k false - 1) (-S.front g (h.1 g) k true)
    (by
      have := hb.1.2
      have : (0 : ℤ) ≤ (S.D + S.r₀ : ℕ) := by positivity
      omega)
    hb.2.2 (fun x hx ↦ by have := Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hx); omega)
    ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2

/-- Every pre-charge physical status has at most `40nD` cut edges in
each of U, UY, Y, P₀, V, with sharper constants for all but Y. No prefix,
edge-count, or good-history certificate is assumed. -/
theorem oldChargeState_cut_bounds_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K)
    (hn : 0 < S.n) (hk : (k + 1) ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    (edgeBoundary Λ ((positiveNear S.depth (S.oldChargeState h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((positiveNearMiddle S.depth (S.oldChargeState h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((middle (S.oldChargeState h g)).map
      (Function.Embedding.subtype _))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.oldChargeState h g) false).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.oldChargeState h g) true).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D := by
  have hb := S.prefix_uncertainty_rows h.1 g hn hk hr hDpos hD hL
  have ha := oldChargeState_prefix_approximation_domainGraph hT S hgraph hdepth
    h g hn hk hr hDpos hD hL hrows
  have hLpos : 1 ≤ L := (Nat.mul_pos (Nat.mul_pos (by decide) g.pos) (by omega)).trans_le hL
  exact physical_status_cut_bounds hT S.A S.depth hdepth (S.oldChargeState h g) hLpos hDpos
    hrows hclear (S.front g (h.1 g) (k + 1) false - 1) (-S.front g (h.1 g) (k + 1) true)
    (by
      have := hb.1.2
      have : (0 : ℤ) ≤ (S.D + S.r₀ : ℕ) := by positivity
      omega)
    hb.2.2 (fun x hx ↦ by
      have := Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hx)
      omega)
    ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2

end CollarScan

end OpenAI.Scan


open Filter SimpleGraph TensorPower TensorPower.ReplicaTransport
open scoped BigOperators symmDiff

namespace OpenAI.Scan

universe u

namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

open Classical in
/-- The four assertions of Lemma 9.1 (`scanner:histories`, `08-scanner.tex`,
lines 195–221) for one actual collar scan with collar depth `L`, anchor
multiplicity `μ`, and inverse power `p` in the bad-history estimate. Completed
statuses after `k ≤ nm` fill–charge pairs and pre-charge statuses with
`k + 1 ≤ nm` are both covered. -/
structure HistoryProperties {Λ : Finset (ℤ × ℤ)} (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (L μ : ℕ) (p : ℝ) : Prop where
  /-- Item 1: a splitting designated support of a completed status is its graph
  `r₀`-ball, and this ball lies in `A`. -/
  support_eq_ball : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (i : I), S.designatedSplitIncidence (S.state h g) L i side →
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i ∧
        S.ball i ⊆ S.A
  /-- Item 1 for pre-charge statuses. -/
  old_support_eq_ball : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (i : I), S.designatedSplitIncidence (S.oldChargeState h g) L i side →
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i ∧
        S.ball i ⊆ S.A
  /-- Item 1: a support splits at most one band, on one side. -/
  split_unique : ∀ {k : ℕ} (h : History S.K S.m S.M k), k ≤ S.n * S.m →
    ∀ (g g' : Fin S.K) (side side' : Bool) (i : I),
      S.designatedSplitIncidence (S.state h g) L i side →
      S.designatedSplitIncidence (S.state h g') L i side' → g = g' ∧ side = side'
  /-- Item 1 for pre-charge statuses. -/
  old_split_unique : ∀ {k : ℕ} (h : History S.K S.m S.M k), k + 1 ≤ S.n * S.m →
    ∀ (g g' : Fin S.K) (side side' : Bool) (i : I),
      S.designatedSplitIncidence (S.oldChargeState h g) L i side →
      S.designatedSplitIncidence (S.oldChargeState h g') L i side' → g = g' ∧ side = side'
  /-- Item 1: in its band, a splitting support meets `Y` and exactly one side, and it
  lies in one part of every other band. -/
  terminal_split : ∀ {k : ℕ} (h : History S.K S.m S.M k), k ≤ S.n * S.m →
    ∀ (g : Fin S.K) (side : Bool) (i : I),
      S.designatedSplitIncidence (S.state h g) L i side →
      IsTerminalSplit (S.state h)
        (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side
  /-- Item 1 for pre-charge statuses. -/
  old_terminal_split : ∀ {k : ℕ} (h : History S.K S.m S.M k), k + 1 ≤ S.n * S.m →
    ∀ (g : Fin S.K) (side : Bool) (i : I),
      S.designatedSplitIncidence (S.oldChargeState h g) L i side →
      IsTerminalSplit (S.oldChargeState h)
        (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side
  /-- Item 1: the metrics of all statuses of distinct bands commute on the symmetric
  replica space, for arbitrary histories, times and completed or pre-charge
  statuses. -/
  band_commute : ∀ {k k' : ℕ} (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K), g < g' → ∀ (preCharge preCharge' : Bool)
    (q : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool → ℕ) [∀ v, NeZero (q v)] {t : ℝ}, 0 ≤ t → ∀ replicas : ℕ,
      Commute (symBandMetric q t replicas (S.quantumHistoryPartition h g preCharge))
        (symBandMetric q t replicas (S.quantumHistoryPartition h' g' preCharge'))
  /-- Item 2: every assigned site of `A` has oriented depth at most `j + D + r₀` on
  its side. -/
  assigned_lead : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (x : ↥(Λ : Set (ℤ × ℤ))), x ∈ S.A → S.state h g x = some side →
      orientedDepth S.depth side x ≤ S.front g (h.1 g) k side + S.D + S.r₀
  /-- Item 2 for pre-charge statuses. -/
  old_assigned_lead : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (x : ↥(Λ : Set (ℤ × ℤ))), x ∈ S.A → S.oldChargeState h g x = some side →
      orientedDepth S.depth side x ≤ S.front g (h.1 g) (k + 1) side + S.D + S.r₀
  /-- Item 2: `U` contains, and `UY` is contained in, a deterministic positive-depth
  prefix, and each differs from it by at most `3nD` sites. -/
  prefix_comparison : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K),
    k ≤ S.n * S.m →
    positiveDepthPrefix S.A S.depth (S.front g (h.1 g) k false - 1) ⊆
        positiveNear S.depth (S.state h g) ∧
      positiveNearMiddle S.depth (S.state h g) ⊆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) k true) ∧
      ((positiveNear S.depth (S.state h g)) ∆
        positiveDepthPrefix S.A S.depth (S.front g (h.1 g) k false - 1)).card ≤
          3 * S.n * S.D ∧
      ((positiveNearMiddle S.depth (S.state h g)) ∆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) k true)).card ≤
          3 * S.n * S.D
  /-- Item 2 for pre-charge statuses. -/
  old_prefix_comparison : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K),
    k + 1 ≤ S.n * S.m →
    positiveDepthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false - 1) ⊆
        positiveNear S.depth (S.oldChargeState h g) ∧
      positiveNearMiddle S.depth (S.oldChargeState h g) ⊆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true) ∧
      ((positiveNear S.depth (S.oldChargeState h g)) ∆
        positiveDepthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false - 1)).card ≤
          3 * S.n * S.D ∧
      ((positiveNearMiddle S.depth (S.oldChargeState h g)) ∆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true)).card ≤
          3 * S.n * S.D
  /-- Item 2: the cuts of `U`, `UY`, `Y`, `P₀` and `V` have at most `40nD` edges. -/
  cut_bounds : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K), k ≤ S.n * S.m →
    (edgeBoundary Λ ((positiveNear S.depth (S.state h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((positiveNearMiddle S.depth (S.state h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((middle (S.state h g)).map
      (Function.Embedding.subtype _))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.state h g) false).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.state h g) true).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D
  /-- Item 2 for pre-charge statuses. -/
  old_cut_bounds : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K),
    k + 1 ≤ S.n * S.m →
    (edgeBoundary Λ ((positiveNear S.depth (S.oldChargeState h g)).map
      (Function.Embedding.subtype _))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ ((positiveNearMiddle S.depth (S.oldChargeState h g)).map
      (Function.Embedding.subtype _))).card ≤
      20 * S.n * S.D ∧
    (edgeBoundary Λ ((middle (S.oldChargeState h g)).map
      (Function.Embedding.subtype _))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.oldChargeState h g) false).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ ((receiving (S.oldChargeState h g) true).map
      (Function.Embedding.subtype _))).card ≤ 16 * S.n * S.D
  /-- Item 2: at most `10μKnD` labelled terms split, counted over bands and sides. -/
  split_count : ∀ {k : ℕ} (h : History S.K S.m S.M k), k ≤ S.n * S.m →
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦ S.designatedSplitIncidence (S.state h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ
  /-- Item 2 for pre-charge statuses. -/
  old_split_count : ∀ {k : ℕ} (h : History S.K S.m S.M k), k + 1 ≤ S.n * S.m →
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦
        S.designatedSplitIncidence (S.oldChargeState h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ
  /-- Item 3 at a charge round: for every label and every common parameter, the
  terminal-leaf probability of a split is at most `10D/m`. -/
  charge_dilution : ∀ (k : ℕ) (i : I) {q : ℝ}, 0 ≤ q → q ≤ 1 →
    (1 - q) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) +
    q * (∑ h : History S.K S.m S.M (k + 1),
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m
  /-- Item 3 at a fill round. -/
  fill_dilution : ∀ (k : ℕ) (i : I) {q : ℝ}, 0 ≤ q → q ≤ 1 →
    (1 - q) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) +
    q * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m
  /-- Item 4: the probability that a full history fails goodness at some time is at
  most `n^(-p)`. -/
  bad_history : (∑ h : History S.K S.m S.M (S.n * S.m),
    if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (S.n : ℝ) ^ (-p)
  /-- Item 4: at a charge round on a good old history, each split term is sampled on
  its splitting side, by a unique slot, with probability at least
  `1/(2(C₁+1)nD)`, and the sampled move is exactly the old `Y`-part of its designated support. -/
  good_sampling : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (i : I), k + 1 ≤ S.n * S.m → S.IsGoodOldHistory h →
    S.designatedSplitIncidence (S.oldChargeState h g) L i side →
    ∃! slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (side, slot) = some i ∧
      (∀ c : ChargeChoices S.K S.M, c g = (side, slot) →
        middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g) =
          designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
            middle (S.oldChargeState h g)) ∧
      (∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0) =
        1 / (2 * (S.M : ℝ)) ∧
      0 < 1 / (2 * (S.C₁ + 1)) ∧
      (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D) ≤
        ∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0

omit [Fintype I] [LinearOrder I] in
/-- A splitting graph ball lies in `A`, once its middle witness lies in the
compact collar. -/
private theorem ball_subset_of_middle {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (σ : PhysicalPartition (↥(Λ : Set (ℤ × ℤ)))) (hsub : middle σ ⊆ S.truncationSet L) (i : I)
    (hsplit : (S.ball i ∩ middle σ).Nonempty) : S.ball i ⊆ S.A := by
  obtain ⟨y, hy⟩ := hsplit
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyA, hydepth⟩ := Finset.mem_filter.mp (hsub hym)
  have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
    ⟨y, hyA, by simpa only [hdepth] using hydepth,
      by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
  simpa only [ball, hgraph] using hb

/-- The middle of a completed status lies in the compact collar. -/
private theorem middle_state_subset_truncationSet {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {k L : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (hL : 8 * S.K * S.m ≤ L) : middle (S.state h g) ⊆ S.truncationSet L := by
  intro x hx
  have hn := (Finset.mem_filter.mp hx).2
  have hA := (initial_middle_depth S.A S.depth _ _
    (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hn).1 false).1
  exact Finset.mem_filter.mpr ⟨hA, (Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hn)).2⟩

open Classical in
/-- Lemma 9.1 for one scanner, from the finite scale inequalities that the source
scales satisfy for large `n` and from the bad-history bound `hbad`, which is the
first assertion of item 4 (`08-scanner.tex`, lines 195–347). -/
theorem historyProperties_of_scales {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L μ : ℕ} {p : ℝ}
    (hn : 2 ≤ S.n) (hr : 2 * S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hC : 3 * (μ : ℝ) ≤ S.C₁) (hCpos : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hbad : (∑ h : History S.K S.m S.M (S.n * S.m),
      if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (S.n : ℝ) ^ (-p)) :
    S.HistoryProperties L μ p := by
  have hn0 : 0 < S.n := by omega
  have hr0 : S.r₀ ≤ S.D := by omega
  have hD : 4 * S.D ≤ S.m := by omega
  have hm : 2 ≤ S.m := by omega
  have hm0 : 0 < S.m := by omega
  have hball_depth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀ :=
    fun i x hx ↦ abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth i x hx
  refine
    { support_eq_ball := ?_
      old_support_eq_ball := ?_
      split_unique := fun h hk g g' side side' i hs hs' ↦
        state_designatedSplitIncidence_unique_domainGraph hT S hgraph hdepth h hn0 hk hr0
          hDpos hD hL hrows hclear g g' side side' i hs hs'
      old_split_unique := fun h hk g g' side side' i hs hs' ↦
        old_designatedSplitIncidence_unique_domainGraph hT S hgraph hdepth h hn0 hk hr0
          hDpos hD hL hrows hclear g g' side side' i hs hs'
      terminal_split := fun h hk g side i hs ↦
        state_designatedSplitIncidence_isTerminalSplit_domainGraph hT S hgraph hdepth h hn0
          hk hr0 hDpos hD hL hrows hclear g side i hs
      old_terminal_split := fun h hk g side i hs ↦
        old_designatedSplitIncidence_isTerminalSplit_domainGraph hT S hgraph hdepth h hn0
          hk hr0 hDpos hD hL hrows hclear g side i hs
      band_commute := fun h h' g g' hg preCharge preCharge' q _ _ ht replicas ↦
        S.commute_quantumHistoryPartition h h' g g' hg preCharge preCharge' q ht replicas
      assigned_lead := fun h g side x hxA hx ↦
        S.bandState_assigned_lead g (h.1 g) _ (fun t ↦ h.2 t g) hball_depth side x hxA hx
      old_assigned_lead := fun h g side x hxA hx ↦
        S.oldChargeState_assigned_lead h g hball_depth side x hxA hx
      prefix_comparison := fun h g hk ↦ by
        obtain ⟨h1, h2, -, -, h5, h6⟩ := state_prefix_approximation_domainGraph hT S hgraph
          hdepth h g hn0 hk hr0 hDpos hD hL hrows
        exact ⟨h1, h2, h5, h6⟩
      old_prefix_comparison := fun h g hk ↦ by
        obtain ⟨h1, h2, -, -, h5, h6⟩ := oldChargeState_prefix_approximation_domainGraph hT S
          hgraph hdepth h g hn0 hk hr0 hDpos hD hL hrows
        exact ⟨h1, h2, h5, h6⟩
      cut_bounds := fun h g hk ↦
        state_cut_bounds_domainGraph hT S hgraph hdepth h g hn0 hk hr0 hDpos hD hL hrows
          hclear
      old_cut_bounds := fun h g hk ↦
        oldChargeState_cut_bounds_domainGraph hT S hgraph hdepth h g hn0 hk hr0 hDpos hD hL
          hrows hclear
      split_count := fun h hk ↦
        sum_card_state_designatedSplitIncidence_le_domainGraph hT S hgraph hdepth h hn hm hk
          hr0 hDpos hmargin hL hrows hmult hclear
      old_split_count := fun h hk ↦
        sum_card_old_designatedSplitIncidence_le_domainGraph hT S hgraph hdepth h hn hm hk
          hr0 hDpos hmargin hL hrows hmult hclear
      charge_dilution := fun k i _ hq0 hq1 ↦
        designated_split_mixture_dilution_domainGraph (k := k) hT S hgraph hdepth i hn0 hm0
          hr0 hD hDpos hCpos hL hrows hclear hq0 hq1
      fill_dilution := fun k i _ hq0 hq1 ↦
        fill_split_mixture_dilution_domainGraph (k := k) hT S hgraph hdepth i hn0 hm0 hr0 hD
          hDpos hCpos hL hrows hclear hq0 hq1
      bad_history := hbad
      good_sampling := fun h g side i hk hgood hs ↦
        S.good_designated_split_sampling_domainGraph hT hgraph hdepth h g side i hn hm hk hr
          hD hDpos hL hC hrows hmult hclear hgood hs }
  · intro k h g side i hs
    have heq := S.designatedSupport_eq_ball_of_state_split h g side i hL hs
    refine ⟨heq, ball_subset_of_middle hT S hgraph hdepth hclear _
      (middle_state_subset_truncationSet S h g hL) i ?_⟩
    simpa only [heq] using hs.2
  · intro k h g side i hs
    have heq := S.designatedSupport_eq_ball_of_split h g side i hL hs
    refine ⟨heq, ball_subset_of_middle hT S hgraph hdepth hclear _
      (S.middle_subset_truncationSet h g hL) i ?_⟩
    simpa only [heq] using hs.2

end CollarScan

open Classical in
/-- **Lemma 9.1** (`scanner:histories`, `08-scanner.tex`, lines 195–221): under
the source scales `scanner:scales` and the test geometry `scanner:test-geometry`,
the actual collar scan has the four properties of `CollarScan.HistoryProperties`
for all sufficiently large `n`.

The exponents satisfy `0 < ℓ`, `0 < κ < μ < 1 - ℓ`; the radius is
`r₀ = ⌈C_r log² n⌉` with `C_r > 0`; the target satisfies `|T| ≤ C_T n²`, its
ambient layers `T_d \ T_{d-1}` have at most `n` sites for `1 ≤ d ≤ L`, and its
sup-norm distance to the endpoints of the cut edges exceeds `2L + 10r₀`. The
padding constant `C₁ > 0` with `3b ≤ C₁` is the source's uniform constant large
enough for every labelled candidate list, where `b` bounds the anchor
multiplicity. The threshold depends only on these fixed constants and on the
inverse power `p`. -/
theorem eventually_historyProperties {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell)
    (hkappa : 0 < kappa) (hkappamu : kappa < mu) (hmu : mu < 1 - ell) (hCr : 0 < Cr)
    (hC1 : 0 < C1) (hCt : 0 ≤ Ct) (b : ℕ) (hb : 3 * (b : ℝ) ≤ C1) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
      S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
        ((2 * ⌊(n : ℝ) ^ (1 - ell)⌋₊ + 10 * S.r₀ : ℕ) : ℤ) <
          ambientSupDistance t z) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ b) →
      S.HistoryProperties ⌊(n : ℝ) ^ (1 - ell)⌋₊ b p := by
  filter_upwards [eventually_bad_history_probability_le.{u} hell hkappa hkappamu hmu hCr
      hC1 hCt b p,
    eventually_split_counting_scale_separation (ell := ell) hCr.le hkappa hkappamu,
    eventually_const_mul_roundedLogRadius_le_rpow hCr.le hkappa 2]
    with n hbad hscale hr2
  intro I _ _ Λ T hT S hSn hm hK hD hR hC ht hgraph hdepth hrows hclear hmult
  dsimp only at hscale
  obtain ⟨hn, -, hDpos, hmargin, -⟩ := hscale
  have hM : S.M = ⌈C1 * n * S.D⌉₊ := by
    simp only [CollarScan.M, chargeSlotCount, hC, hSn]
  have hbad' := hbad I Λ T hT S hSn hm hK hD hR hM ht hgraph hdepth hclear hrows hmult
  subst hSn
  have hr : 2 * S.r₀ ≤ S.D := by
    have hceil : (S.n : ℝ) ^ kappa ≤ (⌈(S.n : ℝ) ^ kappa⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (2 * S.r₀ : ℝ) ≤ S.D := by
      rw [hR, hD]
      linarith
    exact_mod_cast h2
  have hKL : 8 * S.K * S.m ≤ ⌊(S.n : ℝ) ^ (1 - ell)⌋₊ := by
    rw [hK]
    exact eight_mul_bandCount_mul_le _ _
  exact S.historyProperties_of_scales hT hgraph hdepth hn hr (by rw [hD]; exact hDpos)
    (by rw [hD, hR, hm]; exact hmargin) hKL (by rw [hC]; exact hb) (by rw [hC]; exact hC1)
    hrows hmult hclear hbad'

end OpenAI.Scan
