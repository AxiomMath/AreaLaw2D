/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit 5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/PureStateTraceDistance.lean`. Apache 2.0.
-/
import Arealaw.TraceDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Trace distance of two pure states

The QICLean proof is stated here using this project's native trace norm, so its left-hand side
is exactly the normalized-state distance `Arealaw.MState.D₁`.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Classical

variable {m : Type*} [Fintype m]

open scoped Classical in
/-- If `X` is Hermitian and `X³ = c X` with `c > 0`, then
`|X| = c⁻¹ᐟ² X²`. -/
theorem abs_eq_inv_sqrt_smul_mul_self {X : Matrix m m ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) (h3 : X * X * X = (c : ℂ) • X) :
    CFC.abs X = (Real.sqrt c)⁻¹ • (X * X) := by
  have hXX : 0 ≤ X * X := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [hX.eq] using Matrix.posSemidef_conjTranspose_mul_self X
  have habs : CFC.abs X = CFC.sqrt (X * X) := by
    rw [CFC.abs, Matrix.star_eq_conjTranspose, hX.eq]
  rw [habs]
  refine CFC.sqrt_unique ?_ (smul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c)) hXX)
  have h4 : X * X * (X * X) = (c : ℂ) • (X * X) := by
    rw [← Matrix.mul_assoc, h3, Matrix.smul_mul]
  have hr : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  rw [smul_mul_smul_comm, h4, ← Complex.coe_smul, smul_smul,
    ← Complex.ofReal_mul, hr, Complex.ofReal_one, one_smul]

end Classical

omit [DecidableEq n] in
/-- `(P - Q)³ = (1 - s) (P - Q)` for the two rank-one idempotents. -/
theorem sub_mul_sub_mul_sub_of_idempotent {P Q : Matrix n n ℂ} {s : ℂ}
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQP : P * Q * P = s • P)
    (hQPQ : Q * P * Q = s • Q) :
    (P - Q) * (P - Q) * (P - Q) = (1 - s) • (P - Q) := by
  have hexp : (P - Q) * (P - Q) * (P - Q) =
      P * P * P - P * P * Q - P * Q * P + P * Q * Q - Q * P * P +
        Q * P * Q + Q * Q * P - Q * Q * Q := by
    noncomm_ring
  rw [hexp, hPQP, hQPQ, hP, hQ, Matrix.mul_assoc P Q Q,
    Matrix.mul_assoc Q P P, hP, hQ]
  simp only [sub_smul, one_smul, smul_sub]
  abel

omit [DecidableEq n] in
/-- The trace distance of two pure states is
`√(1 - |⟨ψ,φ⟩|²)`, expressed as half the trace norm. -/
theorem traceNorm_div_two_vecMulVec_eq {ψ φ : EuclideanSpace ℂ n}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) -
        vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))).traceNorm / 2 =
      Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) := by
  classical
  set u := WithLp.ofLp ψ
  set v := WithLp.ofLp φ
  set P := vecMulVec u (star u)
  set Q := vecMulVec v (star v)
  set a : ℂ := star u ⬝ᵥ v with ha
  have hunit : ∀ x : EuclideanSpace ℂ n, ‖x‖ = 1 →
      star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x = 1 := by
    intro x hx
    have h : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hx]
      simp
    rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  have huu := hunit ψ hψ
  have hvv := hunit φ hφ
  have hainner : ⟪ψ, φ⟫_ℂ = a := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hvu : star v ⬝ᵥ u = star a := by
    rw [ha, ← Matrix.star_dotProduct_star, star_star, dotProduct_comm]
  have hvmv : ∀ (x y z w : n → ℂ),
      vecMulVec x y * vecMulVec z w = (y ⬝ᵥ z) • vecMulVec x w := by
    intro x y z w
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp [vecMulVec_apply, mul_left_comm]
  have hP : P * P = P := by rw [hvmv, huu, one_smul]
  have hQ : Q * Q = Q := by rw [hvmv, hvv, one_smul]
  set s : ℂ := a * star a with hs
  have hPQP : P * Q * P = s • P := by
    rw [hvmv, smul_mul, hvmv, hvu, smul_smul, ← ha]
  have hQPQ : Q * P * Q = s • Q := by
    rw [hvmv, smul_mul, hvmv, ← ha, hvu, smul_smul, mul_comm]
  have hsre : s = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set X := P - Q with hX
  change X.traceNorm / 2 = _
  have hXh : X.IsHermitian := by
    have hPh : P.IsHermitian := by
      rw [IsHermitian, conjTranspose_vecMulVec, star_star]
    have hQh : Q.IsHermitian := by
      rw [IsHermitian, conjTranspose_vecMulVec, star_star]
    exact hPh.sub hQh
  have h3 := sub_mul_sub_mul_sub_of_idempotent hP hQ hPQP hQPQ
  have htr : (X * X).trace = 2 * (1 - s) := by
    have hXX : X * X = P * P - P * Q - Q * P + Q * Q := by
      rw [hX]
      noncomm_ring
    rw [hXX, hP, hQ, trace_add, trace_sub, trace_sub, hvmv, hvmv,
      trace_smul, trace_smul, trace_vecMulVec, trace_vecMulVec,
      trace_vecMulVec, trace_vecMulVec]
    rw [dotProduct_comm u (star u), huu, dotProduct_comm v (star v), hvv,
      dotProduct_comm u (star v), hvu, dotProduct_comm v (star u), ← ha, hs]
    simp only [smul_eq_mul]
    ring
  have hle : ‖a‖ ^ 2 ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) ψ φ
    rw [hψ, hφ, hainner, one_mul] at h
    nlinarith [norm_nonneg a]
  rw [hainner]
  set c : ℝ := 1 - ‖a‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by linarith
  have htn : X.traceNorm = (CFC.abs X).trace.re := by
    rw [Matrix.traceNorm, CFC.abs, Matrix.star_eq_conjTranspose, hXh.eq]
    rfl
  rcases hc0.lt_or_eq with hcpos | hczero
  · have h3' : X * X * X = (c : ℂ) • X := by
      rw [h3, hsre, hc]
      push_cast
      rfl
    rw [htn, abs_eq_inv_sqrt_smul_mul_self hXh hcpos h3', trace_smul,
      htr, hsre]
    have hcoe : (2 : ℂ) * (1 - ((‖a‖ ^ 2 : ℝ) : ℂ)) = ((2 * c : ℝ) : ℂ) := by
      rw [hc]
      push_cast
      ring
    rw [hcoe, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hcpos.le
    have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
    field_simp
    linarith
  · have hs1 : (1 : ℂ) - s = 0 := by
      have h1 : ‖a‖ ^ 2 = 1 := by linarith
      rw [hsre, h1]
      simp
    have hX0 : X = 0 := by
      have htr0 : (Xᴴ * X).trace = 0 := by
        rw [hXh.eq, htr, hs1, mul_zero]
      exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr0
    rw [htn, hX0, CFC.abs_zero, ← hczero, Real.sqrt_zero]
    simp

end Matrix
