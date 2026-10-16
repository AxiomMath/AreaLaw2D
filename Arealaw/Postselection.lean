import Arealaw.Cor
import Arealaw.PurifiedDist

/-!
# Postselection lowers correlations to a trace distance

BH12 Lemma 9: if measuring an effect `M` on `A` succeeds with probability `p` and moves the state
of `C` from `ρ_C` to `ρ'_C`, then `Cor(A : C) ≥ p D₁(ρ'_C, ρ_C) ≥ p/2 D(ρ'_C, ρ_C)²`.  The
correlation functional sees the move by testing `M ⊗ N`, with `N` the effect attaining `D₁`.
-/

namespace Arealaw

open scoped Kronecker ComplexOrder MatrixOrder
open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]

open scoped Classical in
/-- Testing `X` against `M ⊗ N` is testing the `√M`-postselected reduction of `X` against `N`:
`tr((M ⊗ N) X) = tr(N tr_A((√M ⊗ 1) X (√M ⊗ 1)))`.  Positivity of `M` makes `√M √M = M`;
for `M = -1` the left side is `-tr((1 ⊗ N) X)` and the right side is `0`. -/
theorem trace_kronecker_mul_eq {M : Matrix α α 𝕜} (hM : 0 ≤ M) (N : Matrix γ γ 𝕜)
    (X : Matrix (α × γ) (α × γ) 𝕜) :
    ((M ⊗ₖ N) * X).trace = (N * ((CFC.sqrt M ⊗ₖ 1) * X * (CFC.sqrt M ⊗ₖ 1)).traceLeft).trace := by
  have hMN : (CFC.sqrt M ⊗ₖ 1) * (1 ⊗ₖ N) * (CFC.sqrt M ⊗ₖ 1) = M ⊗ₖ N := by
    simp [← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self M hM]
  rw [trace_mul_comm N, ← trace_mul_one_kron_right, ← hMN, trace_mul_cycle, trace_mul_cycle]
  simp only [Matrix.mul_assoc]

open scoped Classical in
/-- Testing the correlation matrix `ρ_AC - ρ_A ⊗ ρ_C` against `M ⊗ N` gives `p` times the shift
of `ρ_C` under postselection on `M`: `tr((M ⊗ N)(ρ_AC - ρ_A ⊗ ρ_C)) = p tr(N(ρ'_C - ρ_C))`, where
`p = tr(M ρ_A)` and `p ρ'_C = tr_A((√M ⊗ 1) ρ (√M ⊗ 1))`. -/
theorem trace_kronecker_mul_sub_eq {ρ : Matrix (α × γ) (α × γ) 𝕜} (hρ : ρ.PosSemidef)
    {M : Matrix α α 𝕜} (hM : 0 ≤ M) {p : ℝ} (hp : RCLike.re (M * ρ.traceRight).trace = p)
    {C' : Matrix γ γ 𝕜} (hC' : (p : 𝕜) • C' = ((CFC.sqrt M ⊗ₖ 1) * ρ * (CFC.sqrt M ⊗ₖ 1)).traceLeft)
    (N : Matrix γ γ 𝕜) :
    ((M ⊗ₖ N) * (ρ - ρ.traceRight ⊗ₖ ρ.traceLeft)).trace = p * (N * (C' - ρ.traceLeft)).trace := by
  -- `hp` fixes only the real part; positivity makes the trace real.
  have hMA : (M * ρ.traceRight).trace = p := by
    rw [← hp, RCLike.conj_eq_iff_re.mp (hM.posSemidef.trace_mul_nonneg hρ.traceRight).isSelfAdjoint]
  rw [Matrix.mul_sub, trace_sub, trace_kronecker_mul_eq hM, ← hC', Matrix.mul_smul, trace_smul,
    ← mul_kronecker_mul, trace_kronecker, hMA, Matrix.mul_sub, trace_sub, mul_sub, smul_eq_mul]

variable [DecidableEq α]

/-- Postselection bounds correlations from below by trace distance:
`Cor(A : C) ≥ p D₁(ρ'_C, ρ_C)` where `p = tr(M ρ_A)` and `p ρ'_C = tr_A((√M ⊗ 1) ρ (√M ⊗ 1))`.
`M ≤ 1` makes `M` admissible in `Cor`. -/
theorem mul_D₁_le_Cor {ρ : Matrix (α × γ) (α × γ) 𝕜} (hρ : ρ.PosSemidef) {M : Matrix α α 𝕜}
    (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) {p : ℝ} (hp : RCLike.re (M * ρ.traceRight).trace = p)
    {ρC ρC' : SubState γ 𝕜} (hρC : ρC.M = ρ.traceLeft)
    (hρC' : (p : 𝕜) • ρC'.M = ((CFC.sqrt M ⊗ₖ 1) * ρ * (CFC.sqrt M ⊗ₖ 1)).traceLeft) :
    p * ρC'.D₁ ρC ≤ Cor (ρ - ρ.traceRight ⊗ₖ ρ.traceLeft) := by
  have hp₀ : 0 ≤ p := hp ▸ re_trace_mul_nonneg hM₀.posSemidef hρ.traceRight
  obtain ⟨N, hN₀, hN₁, hN⟩ := (ρC'.isGreatest_D₁ ρC).1
  refine le_trans ?_ (norm_trace_le_Cor _ (l2_opNorm_le_one_of_nonneg_of_le_one hM₀ hM₁)
    (l2_opNorm_le_one_of_nonneg_of_le_one hN₀ hN₁))
  rw [trace_kronecker_mul_sub_eq hρ hM₀ hp hρC' N, ← hρC, norm_mul, RCLike.norm_of_nonneg hp₀, hN]
  exact mul_le_mul_of_nonneg_left (RCLike.abs_re_le_norm _) hp₀

/-- **BH12 Lemma 9**: postselecting on an effect `M` of `A` that succeeds with probability `p`
and moves `ρ_C` to `ρ'_C` witnesses `Cor(A : C) ≥ p/2 D(ρ'_C, ρ_C)²`.  The paper assumes
`p > 0`, where `ρ'_C` is determined; the bound holds without it. -/
theorem lemma9 (ρ : MState (α × γ) 𝕜) {M : Matrix α α 𝕜} (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) {p : ℝ}
    (hp : RCLike.re (M * ρ.M.traceRight).trace = p) (ρC ρC' : MState γ 𝕜)
    (hρC : ρC.M = ρ.M.traceLeft)
    (hρC' : (p : 𝕜) • ρC'.M = ((CFC.sqrt M ⊗ₖ 1) * ρ.M * (CFC.sqrt M ⊗ₖ 1)).traceLeft) :
    p / 2 * ρC'.toSubState.D ρC.toSubState ^ 2 ≤ Cor (ρ.M - ρ.M.traceRight ⊗ₖ ρ.M.traceLeft) := by
  refine le_trans ?_ (mul_D₁_le_Cor ρ.psd hM₀ hM₁ hp hρC hρC')
  nlinarith [ρC'.toSubState.D_sq_le_two_mul_D₁ ρC.toSubState,
    re_trace_mul_nonneg hM₀.posSemidef ρ.psd.traceRight]

end Arealaw
