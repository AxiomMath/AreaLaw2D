/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/TailParameter.lean` (Apache 2.0).  Namespace `TNLean.PEPS.AreaLaw`
renamed to `OpenAI`.  Adapted to the encoding of `OpenAI.Scan.MarginalTailsBridge`: a cut
`A : Finset (Site Λ)` is a finite set `A` of `ℤ × ℤ` (no inclusion in `Λ` is needed for the
counts; the regional statement takes `A ⊆ Λ`), TNLean's `AdmissibleSupport Λ R` is the subtype
of `supports Λ R`, its unordered `edgeBoundary` is the ordered `OpenAI.edgeBoundary` (of equal
cardinality), its `cutLogBudget Λ q R` is `OpenAI.latticeCutLogBudget Λ q R`, the bundled
`LocalHamiltonian` is an interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`, and
`IsGappedGroundState` is the normalization `star Ω ⬝ᵥ Ω = 1`, the eigenvector equation and
`OpenAI.HasGlobalGap`.  The regional state and entropy are those of `OpenAI.pureState`
(`MState.restrict`, `regionEntropy`), as in `OpenAI.Scan.MarginalTailsBridge`, over any `RCLike`
field.  TNLean's `cutLogBudget_le_card` (`InitialBuffer.lean`) has the exponent
`v_R = 1 + 2R(R + 1)`; the existing `OpenAI.cutLogBudget_le_card` has the coarser `(2R + 1)²`,
so the `v_R` form is added here as `cutLogBudget_le_card_diamond`, with the support count
`card_le_diamond_of_mem_supports` (TNLean `card_support_le_diamond` on the lattice).  The
ball of the edge count is the ambient diamond `latticeDiamond` rather than the graph ball.
-/
import OpenAI.BufferedRectangles
import OpenAI.Scan.MarginalTailsBridge

/-!
# The marginal-tail parameter of a general cut

For a finite-range Hamiltonian on a finite induced square-lattice domain, the parameter
`ℬ_A` of Lemma 3.1 of [OAI265] is at most a constant times `1 + |∂_Λ A|`, for every cut `A`.
An admissible support that meets both sides of the cut contains two sites joined by a walk of
length at most `R`, which crosses an edge of the cut; so the support has a site within distance
`R` of the endpoint of that edge inside `A`.  Each edge therefore accounts for at most
`v_R μ_R` crossing supports, with `v_R = 1 + 2R(R + 1)` the diamond count and
`μ_R = 2^{v_R - 1}` the number of admissible supports through a site.

Inserting this bound into the tail estimate of Lemma 3.1 gives the typical-spectrum statement at
the width `C_M √(1 + |∂_Λ A|) log (n + 2)`.

## Main statements

* `OpenAI.card_crossingTerms_le_edgeBoundary`: at most `|∂_Λ A| v_R μ_R` admissible supports
  cross a cut `A`.
* `OpenAI.cutLogBudget_le_edgeBoundary`: `ℬ_A ≤ C (1 + |∂_Λ A|)`,
  `eq:initial-local-tail-parameter`, with `C = tailParameterConstant q R`.
* `OpenAI.concentrationWidth_le`: the concentration width is at most
  `C_M √(1 + |∂_Λ A|) log (n + 2)`, with `C_M = typicalWidthConstant q R J Δ M`.
* `OpenAI.IsAdmissible.one_sub_rpow_le_typicalMass_edgeBoundary`: the typical marginal
  spectrum at that width.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `02-initial.tex`, lines 202–212, `eq:initial-local-tail-parameter`
  and the concentration statement after it; the counts are those of
  `01-preliminaries.tex`, lines 81–102.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix

namespace OpenAI

open Arealaw SimpleGraph
open scoped ComplexOrder

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-! ### Counting the supports that cross a cut -/

/-- An admissible support of range `R` has at most `v_R = 1 + 2R(R + 1)` sites. -/
theorem card_le_diamond_of_mem_supports {X : Finset (ℤ × ℤ)} (hX : X ∈ supports Λ R) :
    X.card ≤ 1 + 2 * R * (R + 1) := by
  obtain ⟨a, ha⟩ := (mem_supports_iff_walk.1 hX).2.1
  exact (Finset.card_le_card (subset_latticeDiamond_of_mem_supports hX ha)).trans
    (card_latticeDiamond a R).le

/-- **Crossing supports of a general cut.** At most `|∂_Λ A| v_R μ_R` admissible supports
of range `R` meet both a region `A` and its complement, where `v_R = 1 + 2R(R + 1)` and
`μ_R = 2^{v_R - 1}`. Source: `02-initial.tex`, lines 202–206, with the counts of
`01-preliminaries.tex`, lines 81–102. -/
theorem card_crossingTerms_le_edgeBoundary (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (A : Finset (ℤ × ℤ)) :
    (crossingTerms (fun X : supports Λ R ↦ X.1) A).card ≤
      (edgeBoundary Λ A).card *
        ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1)) := by
  classical
  -- the supports with a site within distance `R` of the endpoint of `e` inside `A`
  set near : (ℤ × ℤ) × (ℤ × ℤ) → Finset (supports Λ R) := fun e ↦
    (latticeDiamond e.1 R).biUnion fun v ↦ Finset.univ.filter fun X : supports Λ R ↦ v ∈ X.1
  have hcover : crossingTerms (fun X : supports Λ R ↦ X.1) A ⊆
      (edgeBoundary Λ A).biUnion near := by
    intro X hX
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := mem_crossingTerms.1 hX
    rw [Finset.mem_inter] at hv
    rw [Finset.mem_sdiff] at hw
    obtain ⟨hXΛ, -, hwalk⟩ := mem_supports_iff_walk.1 X.2
    obtain ⟨p, hp⟩ := hwalk v hv.1 w hw.1
    obtain ⟨u, u', he, p', hp'⟩ := exists_edgeBoundary_of_walk p hv.2 hw.2
    have hdist : latticeL1Distance (u : ℤ × ℤ) v ≤ R :=
      (latticeL1Distance_le_walk_length Subtype.val
        (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h) p'.reverse).trans
        ((Walk.length_reverse p').le.trans (hp'.trans hp))
    exact Finset.mem_biUnion.2 ⟨_, he, Finset.mem_biUnion.2 ⟨v, mem_latticeDiamond.2 hdist,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hv.1⟩⟩⟩
  have hcard : ∀ e ∈ edgeBoundary Λ A,
      (near e).card ≤ (1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
    intro e _
    calc (near e).card ≤ (latticeDiamond e.1 R).card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
          Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦ card_admissibleSupport_containing_le v
      _ = _ := by rw [card_latticeDiamond]
  exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul _ _ _ hcard)

/-! ### The tail parameter -/

/-- The cut parameter of Lemma 3.1 grows at most linearly with the number of crossing
supports: `ℬ ≤ 1 + |𝒞| log² (e q^{v_R})`, with `v_R = 1 + 2R(R + 1)`. -/
theorem cutLogBudget_le_card_diamond (hq : 1 ≤ q) (Cr : Finset (supports Λ R)) :
    cutLogBudget Cr (fun X ↦ Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ)))) ≤
      1 + Cr.card * Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 := by
  have hbound : ∀ X ∈ Cr,
      Real.log (Real.exp 1 * (Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) : ℝ)) ^ 2 ≤
        Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 := by
    intro X _
    have h1 : (1 : ℝ) ≤ Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) := by
      have : 1 ≤ Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) := by
        simp only [card_reg (loc := Qudits q), Fintype.card_fin, Finset.prod_const]
        exact Nat.one_le_pow _ _ hq
      exact_mod_cast this
    have h2 : (Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) : ℝ) ≤
        (q : ℝ) ^ (1 + 2 * R * (R + 1)) := by
      have : Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) ≤ q ^ (1 + 2 * R * (R + 1)) := by
        simp only [card_reg (loc := Qudits q), Fintype.card_fin, Finset.prod_const]
        exact Nat.pow_le_pow_right hq (card_le_diamond_of_mem_supports X.2)
      exact_mod_cast this
    have he : 1 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hl : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ)))) :=
      Real.log_nonneg (by nlinarith)
    have := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le)
    exact pow_le_pow_left₀ hl this 2
  have hsum := Finset.sum_le_card_nsmul Cr _ _ hbound
  rw [nsmul_eq_mul] at hsum
  rw [cutLogBudget]
  linarith

/-- The constant `C = v_R μ_R log² (e q^{v_R})` of `eq:initial-local-tail-parameter`, with
`v_R = 1 + 2R(R + 1)` and `μ_R = 2^{v_R - 1}`. It depends only on the local dimension and
the range. Source: `02-initial.tex`, lines 202–206. -/
noncomputable def tailParameterConstant (q R : ℕ) : ℝ :=
  ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) *
    Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2

/-- The constant of `eq:initial-local-tail-parameter` is at least one for `q ≥ 1`. -/
theorem one_le_tailParameterConstant (hq : 1 ≤ q) (R : ℕ) : 1 ≤ tailParameterConstant q R := by
  have hq' : (1 : ℝ) ≤ (q : ℝ) ^ (1 + 2 * R * (R + 1)) := one_le_pow₀ (by exact_mod_cast hq)
  have hlog : 1 ≤ Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_pos 1]
  have hcount : (1 : ℝ) ≤ ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold tailParameterConstant
  nlinarith [one_le_pow₀ (n := 2) hlog]

/-- **The tail parameter of a general cut.** For local dimension `q ≥ 1`, the parameter of
Lemma 3.1 satisfies `ℬ_A ≤ C (1 + |∂_Λ A|)` for every cut `A` of a finite induced domain,
with `C = tailParameterConstant q R`.
Source: `02-initial.tex`, lines 202–206, `eq:initial-local-tail-parameter`. -/
theorem cutLogBudget_le_edgeBoundary (hq : 1 ≤ q) (R : ℕ) (A : Finset (ℤ × ℤ)) :
    latticeCutLogBudget Λ q R A ≤
      tailParameterConstant q R * (1 + (edgeBoundary Λ A).card) := by
  have hC := one_le_tailParameterConstant hq R
  have hcard : ((crossingTerms (fun X : supports Λ R ↦ X.1) A).card : ℝ) ≤
      (edgeBoundary Λ A).card *
        ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) := by
    exact_mod_cast card_crossingTerms_le_edgeBoundary Λ R A
  have hb : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  calc latticeCutLogBudget Λ q R A
      ≤ 1 + (crossingTerms (fun X : supports Λ R ↦ X.1) A).card *
          Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 :=
        cutLogBudget_le_card_diamond hq _
    _ ≤ 1 + (edgeBoundary Λ A).card * tailParameterConstant q R := by
        rw [tailParameterConstant, ← mul_assoc]
        gcongr
    _ ≤ _ := by nlinarith

/-! ### The typical spectrum at the boundary width -/

/-- The constant `C_M = 32 √((1 + J/Δ) C) (M + (e/2 + log 2)/log 2)` of the concentration
statement after Lemma 3.1, with `C = tailParameterConstant q R`. It depends only on
`q, R, J, Δ` and `M`. Source: `02-initial.tex`, lines 207–212. -/
noncomputable def typicalWidthConstant (q R : ℕ) (J Δ M : ℝ) : ℝ :=
  32 * Real.sqrt ((1 + J / Δ) * tailParameterConstant q R) *
    (M + (Real.exp 1 / 2 + Real.log 2) / Real.log 2)

/-- The concentration width of a cut is at most `C_M √(1 + |∂_Λ A|) log (n + 2)`.
Source: `02-initial.tex`, lines 207–212. -/
theorem concentrationWidth_le (hq : 1 ≤ q) (R : ℕ) (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ)
    (A : Finset (ℤ × ℤ)) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    concentrationWidth Λ q R J Δ A n M ≤
      typicalWidthConstant q R J Δ M * Real.sqrt (1 + (edgeBoundary Λ A).card) *
        Real.log (n + 2) := by
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log two_pos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hc : 0 < Real.exp 1 / 2 + Real.log 2 := by positivity
  have hsqrt : Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A) ≤
      Real.sqrt ((1 + J / Δ) * tailParameterConstant q R) *
        Real.sqrt (1 + (edgeBoundary Λ A).card) := by
    rw [← Real.sqrt_mul (by have := one_le_tailParameterConstant hq R; positivity), mul_assoc]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (cutLogBudget_le_edgeBoundary hq R A)
      (by positivity))
  have hfactor : M * Real.log ((n : ℝ) + 2) + Real.exp 1 / 2 + Real.log 2 ≤
      (M + (Real.exp 1 / 2 + Real.log 2) / Real.log 2) * Real.log ((n : ℝ) + 2) := by
    have : Real.exp 1 / 2 + Real.log 2 ≤
        (Real.exp 1 / 2 + Real.log 2) / Real.log 2 * Real.log ((n : ℝ) + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hL hc.le
    linarith
  have hfactor_nonneg : 0 ≤ M * Real.log ((n : ℝ) + 2) + Real.exp 1 / 2 + Real.log 2 := by
    have := mul_nonneg hM (hlog2.le.trans hL)
    linarith
  calc concentrationWidth Λ q R J Δ A n M
      = 32 * Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A) *
          (M * Real.log ((n : ℝ) + 2) + Real.exp 1 / 2 + Real.log 2) := rfl
    _ ≤ 32 * (Real.sqrt ((1 + J / Δ) * tailParameterConstant q R) *
          Real.sqrt (1 + (edgeBoundary Λ A).card)) *
          ((M + (Real.exp 1 / 2 + Real.log 2) / Real.log 2) * Real.log ((n : ℝ) + 2)) := by
        gcongr
    _ = _ := by
        unfold typicalWidthConstant
        ring

/-- The typical mass grows with the width of the window. -/
theorem typicalMass_le_typicalMass_of_le {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (S : ℝ) {w w' : ℝ} (h : w ≤ w') :
    Entropy.typicalMass p S w ≤ Entropy.typicalMass p S w' :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ by
    rw [Entropy.mem_typicalSet] at hi ⊢
    exact ⟨hi.1, hi.2.trans h⟩) fun i _ _ ↦ hp i

section Lattice

variable {𝕜 : Type*} [RCLike 𝕜]
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}

/-- **Typical marginal spectrum at the boundary width.** For a gapped ground vector of a
finite-range Hamiltonian with local dimension `q ≥ 1`, every cut `A`, every `n` and every
`M ≥ 0`, the positive eigenvalues of the regional state whose surprisal lies within
`C_M √(1 + |∂_Λ A|) log (n + 2)` of `S_Ω(A)` carry mass at least `1 - (n + 2)^{-M}`, with
`C_M = typicalWidthConstant q R J Δ M`. The manuscript states `n ≥ 1` and `M > 0`.
Source: `02-initial.tex`, lines 207–212. -/
theorem IsAdmissible.one_sub_rpow_le_typicalMass_edgeBoundary (hΦ : IsAdmissible Λ R J Φ)
    (hq : 1 ≤ q) (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hΔ : 0 < Δ) (heig : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω)
    (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ) {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    1 - ((n : ℝ) + 2) ^ (-M) ≤
      Entropy.typicalMass ((pureState Ω hΩ).restrict hA).psd.isHermitian.eigenvalues
        ((pureState Ω hΩ).regionEntropy hA)
        (typicalWidthConstant q R J Δ M * Real.sqrt (1 + (edgeBoundary Λ A).card) *
          Real.log (n + 2)) :=
  (hΦ.one_sub_rpow_le_typicalMass_reducedState hJ hΩ hΔ heig hgap hA n M).trans
    (typicalMass_le_typicalMass_of_le ((pureState Ω hΩ).restrict hA).psd.eigenvalues_nonneg _
      (concentrationWidth_le hq R hJ hΔ A n hM))

end Lattice

end OpenAI
