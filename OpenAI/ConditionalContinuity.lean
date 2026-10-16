import OpenAI.ConditionalEntropy
import OpenAI.Statements

/-!
# Continuity of the conditional entropy

Lemma 2.1 of [OAI265, §2.1, eq. (2.1)], the Alicki–Fannes–Winter bound: for states `ρ`, `τ`
on `D ⊗ E` at trace distance `δ = ½ ‖ρ - τ‖₁`, with `d_D = dim D` and `h` the binary entropy,
`|S(D|E)_ρ - S(D|E)_τ| ≤ 2 δ log d_D + (1 + δ) h(δ / (1 + δ)) ≤ 4 √δ log (e d_D)`.
Neither bound involves the dimension of `E`.

Write `ρ - τ = P - N` with `P`, `N` the positive and negative parts, so that
`tr P = tr N = δ`.  The matrix `ρ + N = τ + P` has trace `1 + δ`.  Superadditivity of the
conditional entropy and its upper bound, applied to both decompositions, give
`S(D|E)_ρ - S(D|E)_τ ≤ S(D|E)_P - S(D|E)_N + η(δ) - η(1 + δ)` with `η(x) = -x log x`,
and the dimension bound `|S(D|E)_X| ≤ tr X · log d_D` finishes.  The scalar identity
`(1 + δ) h(δ / (1 + δ)) = η(δ) - η(1 + δ)` matches the paper's form, and
`η(δ) - η(1 + δ) ≤ 4 √δ` gives the second bound.

## Main statements

* `Arealaw.exists_posSemidef_sub_eq`: the Jordan decomposition of a Hermitian matrix, with
  the traces of its parts.
* `Arealaw.abs_vonNeumann_sub_traceLeft_sub_le`,
  `Arealaw.abs_vonNeumann_sub_traceLeft_sub_le_sqrt`: the bipartite bounds.
* `OpenAI.conditional_continuity`: Lemma 2.1 on regions.

## Implementation notes

The paper's absolute constant `C` is `4`.  No division by `δ` occurs, so `δ = 0` is not a
separate case.

The proof is ported from QICLean, `QICLean/Entropy/ControlledContinuity.lean` at commit
`32a5a1a8` (Apache 2.0): `one_add_mul_binEntropy_div_one_add`,
`log_one_add_le_two_mul_sqrt`, `negMulLog_sub_negMulLog_one_add_le`,
`winterModulus_le_sqrt` and `abs_conditionalEntropy_sub_le`.  QICLean adapted them from
`openai/math` at commit `adc7f1241b42`, file
`lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean`, declarations
`conditional_continuity`, `log_one_add_le_two_sqrt` and `mixing_modulus_le`.  The changes:
the matrix statements are about `Arealaw.vonNeumann` and Physlib's `traceLeft` over a general
`RCLike` field, for `Arealaw.MState`s with the trace distance `Arealaw.SubState.D₁`; the
Jordan parts are Physlib's `HermitianMat.posPart` and `HermitianMat.negPart`; and the region
form is new.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §2.1, Lemma 2.1, eq. (2.1).
* R. Alicki, M. Fannes, *Continuity of quantum conditional information*, J. Phys. A 37 (2004),
  L55–L57.
* A. Winter, *Tight uniform continuity bounds for quantum entropies*, Commun. Math. Phys. 347
  (2016), Lemma 2.
-/

namespace Arealaw

open Matrix Real
open scoped HermitianMat ComplexOrder

/-! ## The scalar modulus -/

/-- The Winter modulus in the paper's form is `η(δ) - η(1 + δ)`:
`(1 + δ) h(δ / (1 + δ)) = -δ log δ + (1 + δ) log (1 + δ)`. -/
theorem one_add_mul_binEntropy_div_one_add {δ : ℝ} (hδ : 0 ≤ δ) :
    (1 + δ) * binEntropy (δ / (1 + δ)) = negMulLog δ - negMulLog (1 + δ) := by
  have hp : 0 < 1 + δ := by linarith
  have h1 : 1 - δ / (1 + δ) = (1 + δ)⁻¹ := by field_simp; ring
  rw [binEntropy, h1, inv_inv, div_eq_mul_inv, mul_inv, inv_inv]
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  rw [Real.log_mul (inv_ne_zero hδ.ne') hp.ne', Real.log_inv]
  simp only [negMulLog]
  field_simp
  ring

/-- `log (1 + x) ≤ 2 √x` for `x ≥ 0`. -/
theorem log_one_add_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : log (1 + x) ≤ 2 * √x := by
  have hp : 0 < 1 + x := by linarith
  have hl := log_le_sub_one_of_pos (sqrt_pos.mpr hp)
  rw [log_sqrt hp.le] at hl
  have hs : √(1 + x) ≤ 1 + √x := by
    have h1 := sq_sqrt hp.le
    have h2 := sq_sqrt hx
    nlinarith [sqrt_nonneg (1 + x), sqrt_nonneg x]
  linarith

/-- The mixing modulus is at most `4 √x`: `η(x) - η(1 + x) ≤ 4 √x` for `x ≥ 0`. -/
theorem negMulLog_sub_negMulLog_one_add_le {x : ℝ} (hx : 0 ≤ x) :
    negMulLog x - negMulLog (1 + x) ≤ 4 * √x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hp : 0 < 1 + x := by linarith
  have hid : negMulLog x - negMulLog (1 + x) = log (1 + x) + x * log (1 + 1 / x) := by
    rw [show 1 + 1 / x = (1 + x) / x by field_simp; ring, log_div hp.ne' hx.ne']
    simp only [negMulLog]
    ring
  rw [hid]
  have hb := log_one_add_le_two_mul_sqrt hx.le
  have hc := mul_le_mul_of_nonneg_left
    (log_one_add_le_two_mul_sqrt (show 0 ≤ 1 / x by positivity)) hx.le
  have hroot : x * (2 * √(1 / x)) = 2 * √x := by
    rw [one_div, sqrt_inv]
    have hs := sq_sqrt hx.le
    have hn := (sqrt_pos.mpr hx).ne'
    field_simp
    nlinarith
  rw [hroot] at hc
  linarith

/-- **The square-root modulus**: `2 δ log d + (1 + δ) h(δ / (1 + δ)) ≤ 4 √δ log (e d)` for
`0 ≤ δ ≤ 1` and `d ≥ 1`.  Both side conditions are needed: at `δ = 9` the coefficients of
`log d` are `18 > 12`, and for fixed `δ ∈ (0, 1]` they are `2 δ < 4 √δ`, so the inequality fails
as `d → ∞` in the first case and as `d → 0⁺` in the second. -/
theorem winterModulus_le_sqrt {δ d : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) :
    2 * δ * log d + (1 + δ) * binEntropy (δ / (1 + δ)) ≤ 4 * √δ * log (exp 1 * d) := by
  rw [one_add_mul_binEntropy_div_one_add hδ0, log_mul (exp_pos 1).ne' (by linarith), log_exp]
  have hm := negMulLog_sub_negMulLog_one_add_le hδ0
  have hlog : 0 ≤ log d := log_nonneg hd
  have hsq : δ ≤ √δ := by
    have h1 : √δ ≤ 1 := by simpa using sqrt_le_sqrt hδ1
    calc δ = √δ * √δ := (mul_self_sqrt hδ0).symm
      _ ≤ √δ * 1 := mul_le_mul_of_nonneg_left h1 (sqrt_nonneg _)
      _ = √δ := mul_one _
  nlinarith [sqrt_nonneg δ]

/-! ## The Jordan decomposition -/

section Jordan

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- **The Jordan decomposition with its traces**: a Hermitian `A` is `P - N` with `P`, `N`
positive semidefinite, `tr P = (‖A‖₁ + tr A) / 2` and `tr N = (‖A‖₁ - tr A) / 2`. -/
theorem exists_posSemidef_sub_eq {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    ∃ P N : Matrix ι ι 𝕜, P.PosSemidef ∧ N.PosSemidef ∧ P - N = A ∧
      RCLike.re P.trace = (A.traceNorm + RCLike.re A.trace) / 2 ∧
      RCLike.re N.trace = (A.traceNorm - RCLike.re A.trace) / 2 := by
  classical
  set A' : HermitianMat ι 𝕜 := ⟨A, hA⟩
  have hsub : (A'⁺).mat - (A'⁻).mat = A := congrArg HermitianMat.mat A'.posPart_add_negPart
  have htr : RCLike.re (A'⁺).mat.trace = (A.traceNorm + RCLike.re A.trace) / 2 := by
    obtain ⟨e, he⟩ := A'.cfc_eigenvalues fun x => x ⊔ 0
    have habs : A.traceNorm = ∑ i, |A'.H.eigenvalues i| :=
      Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues A'.H
    have hpos : (A'⁺).trace = ∑ i, max (A'.H.eigenvalues i) 0 := by
      rw [HermitianMat.posPart_eq_cfc_max, ← HermitianMat.sum_eigenvalues_eq_trace, he]
      exact e.sum_comp fun i => max (A'.H.eigenvalues i) 0
    have htrA : RCLike.re A.trace = ∑ i, A'.H.eigenvalues i := by
      have h := HermitianMat.sum_eigenvalues_eq_trace A'
      rw [HermitianMat.trace_eq_re_trace] at h
      exact h.symm
    rw [← HermitianMat.trace_eq_re_trace, hpos, habs, htrA, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (A'.H.eigenvalues i) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  refine ⟨_, _, HermitianMat.zero_le_iff.1 A'.posPart_nonneg,
    HermitianMat.zero_le_iff.1 A'.negPart_nonneg, hsub, htr, ?_⟩
  have h := congrArg (fun X => RCLike.re X.trace) hsub
  simp only [trace_sub, map_sub] at h
  linarith

end Jordan

/-! ## The bipartite bound -/

section Bipartite

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

/-- **Alicki–Fannes–Winter, sharp form** [OAI265, §2.1, eq. (2.1)]: for states `ρ`, `τ` on
`D ⊗ E` at trace distance `δ`, `|S(D|E)_ρ - S(D|E)_τ| ≤ 2 δ log d_D + (1 + δ) h(δ / (1 + δ))`,
with `S(D|E)_ρ = S(ρ) - S(tr_D ρ)`. -/
theorem abs_vonNeumann_sub_traceLeft_sub_le (ρ τ : MState (m × n) 𝕜) :
    |(vonNeumann ρ.psd.isHermitian - vonNeumann ρ.psd.isHermitian.traceLeft) -
        (vonNeumann τ.psd.isHermitian - vonNeumann τ.psd.isHermitian.traceLeft)| ≤
      2 * ρ.toSubState.D₁ τ.toSubState * Real.log (Fintype.card m) +
        (1 + ρ.toSubState.D₁ τ.toSubState) *
          binEntropy (ρ.toSubState.D₁ τ.toSubState / (1 + ρ.toSubState.D₁ τ.toSubState)) := by
  set δ := ρ.toSubState.D₁ τ.toSubState with hδ
  rw [one_add_mul_binEntropy_div_one_add (SubState.D₁_nonneg _ _)]
  obtain ⟨P, N, hP, hN, hPN, hPtr, hNtr⟩ :=
    exists_posSemidef_sub_eq (ρ.psd.isHermitian.sub τ.psd.isHermitian)
  have h0 : RCLike.re (ρ.M - τ.M).trace = 0 := by
    rw [trace_sub, map_sub, ρ.tr_eq_one, τ.tr_eq_one, sub_self]
  rw [h0, add_zero, ← MState.D₁_eq_traceNorm_div_two, ← hδ] at hPtr
  rw [h0, sub_zero, ← MState.D₁_eq_traceNorm_div_two, ← hδ] at hNtr
  have heq : ρ.M + N = τ.M + P := by
    rw [add_comm τ.M P]
    exact (sub_eq_sub_iff_add_eq_add.1 hPN).symm
  have hρN : RCLike.re (ρ.M + N).trace = 1 + δ := by
    rw [trace_add, map_add, ρ.tr_eq_one, hNtr]
  have hτP : RCLike.re (τ.M + P).trace = 1 + δ := by rw [← heq, hρN]
  have hpa := abs_vonNeumann_sub_traceLeft_le hP
  have hna := abs_vonNeumann_sub_traceLeft_le hN
  rw [hPtr] at hpa
  rw [hNtr] at hna
  have h₁ := vonNeumann_sub_traceLeft_add_le ρ.psd hN
  have h₂ := vonNeumann_sub_traceLeft_add_le_add τ.psd hP
  have h₃ := vonNeumann_sub_traceLeft_add_le τ.psd hP
  have h₄ := vonNeumann_sub_traceLeft_add_le_add ρ.psd hN
  rw [τ.tr_eq_one, hPtr, hτP, negMulLog_one, zero_add] at h₂
  rw [ρ.tr_eq_one, hNtr, hρN, negMulLog_one, zero_add] at h₄
  have hc : vonNeumann (ρ.psd.add hN).isHermitian -
        vonNeumann (ρ.psd.add hN).isHermitian.traceLeft =
      vonNeumann (τ.psd.add hP).isHermitian - vonNeumann (τ.psd.add hP).isHermitian.traceLeft := by
    rw [vonNeumann_congr _ (τ.psd.add hP).isHermitian heq,
      vonNeumann_congr _ (τ.psd.add hP).isHermitian.traceLeft (congrArg traceLeft heq)]
  rw [abs_le] at hpa hna ⊢
  constructor <;> linarith [hpa.1, hpa.2, hna.1, hna.2]

/-- **Alicki–Fannes–Winter, square-root form** [OAI265, §2.1, eq. (2.1)], with `C = 4`: for
states `ρ`, `τ` on `D ⊗ E` at trace distance `δ`, `|S(D|E)_ρ - S(D|E)_τ| ≤ 4 √δ log (e d_D)`. -/
theorem abs_vonNeumann_sub_traceLeft_sub_le_sqrt (ρ τ : MState (m × n) 𝕜) :
    |(vonNeumann ρ.psd.isHermitian - vonNeumann ρ.psd.isHermitian.traceLeft) -
        (vonNeumann τ.psd.isHermitian - vonNeumann τ.psd.isHermitian.traceLeft)| ≤
      4 * √(ρ.toSubState.D₁ τ.toSubState) * Real.log (Real.exp 1 * Fintype.card m) := by
  refine (abs_vonNeumann_sub_traceLeft_sub_le ρ τ).trans
    (winterModulus_le_sqrt (SubState.D₁_nonneg _ _) (SubState.D₁_le_one _ _) ?_)
  have : Nonempty (m × n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := ρ.tr_eq_one
    simp [Matrix.trace] at this
  have : Nonempty m := ⟨(Classical.arbitrary (m × n)).1⟩
  exact_mod_cast Fintype.card_pos

end Bipartite

/-! ## Regions -/

section Region

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U X Y : Finset σ}

/-- On disjoint regions the conditional entropy `S(X ∪ Y) - S(Y)` is the bipartite
`S(ρ) - S(tr_X ρ)` of the marginal on `X ∪ Y`, read on `X ⊗ Y` through `unionEquiv`. -/
theorem SubState.regionEntropy_union_sub_regionEntropy (ρ : SubState (Reg loc U) 𝕜)
    (hX : X ⊆ U) (hY : Y ⊆ U) (hd : Disjoint X Y) :
    ρ.regionEntropy (Finset.union_subset hX hY) - ρ.regionEntropy hY =
      vonNeumann ((ρ.restrict (Finset.union_subset hX hY)).submatrix
          (unionEquiv hd).symm).psd.isHermitian -
        vonNeumann ((ρ.restrict (Finset.union_subset hX hY)).submatrix
          (unionEquiv hd).symm).psd.isHermitian.traceLeft := by
  have e₁ : ρ.regionEntropy (Finset.union_subset hX hY) =
      vonNeumann ((ρ.restrict (Finset.union_subset hX hY)).submatrix
        (unionEquiv hd).symm).psd.isHermitian :=
    (entropy_submatrix _ _).symm
  have e₂ : ρ.regionEntropy hY =
      vonNeumann ((ρ.restrict (Finset.union_subset hX hY)).submatrix
        (unionEquiv hd).symm).psd.isHermitian.traceLeft := by
    refine vonNeumann_congr _ _ ?_
    change ptrace hY ρ.M = traceLeft ((ptrace (Finset.union_subset hX hY) ρ.M).submatrix
      (unionEquiv hd).symm (unionEquiv hd).symm)
    rw [← ptrace_eq_traceLeft hd, ptrace_ptrace]
  rw [e₁, e₂]

end Region

end Arealaw

namespace OpenAI

open Arealaw

/-- **Lemma 2.1** [OAI265, §2.1, eq. (2.1)]. -/
theorem conditional_continuity {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ]
    {loc : σ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] :
    ConditionalContinuity σ loc 𝕜 := by
  intro U X Y hX hY hd ρ τ
  have hD : ((ρ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm).toSubState.D₁
      ((τ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm).toSubState =
      (ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
        (τ.toSubState.restrict (Finset.union_subset hX hY)) := by
    simp
  have h₁ := abs_vonNeumann_sub_traceLeft_sub_le
    ((ρ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm)
    ((τ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm)
  have h₂ := abs_vonNeumann_sub_traceLeft_sub_le_sqrt
    ((ρ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm)
    ((τ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm)
  rw [hD] at h₁ h₂
  rw [ρ.toSubState.regionEntropy_union_sub_regionEntropy hX hY hd,
    τ.toSubState.regionEntropy_union_sub_regionEntropy hX hY hd]
  exact ⟨h₁, h₂⟩

end OpenAI
