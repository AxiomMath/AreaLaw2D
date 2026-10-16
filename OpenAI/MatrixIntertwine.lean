/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI

Ported and specialized from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Entropy/ConditionalMovement/LogCompression.lean`,
`QICLean/Analysis/OperatorMean/RealPowerIntertwine.lean`,
`QICLean/Algebra/MatrixAux.lean`, and
`QICLean/Analysis/CoisometricCompression.lean`.
-/
import OpenAI.MatrixPowers
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Rectangular matrix intertwining

Minimal finite-dimensional identities used to transport filtered vectors and
transport states along rectangular intertwiners.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Continuous functional calculus respects a rectangular intertwiner of
Hermitian matrices. -/
theorem cfc_intertwine {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (V : Matrix m n ℂ)
    (hV : A * V = V * B) (f : ℝ → ℝ) : cfc f A * V = V * cfc f B := by
  let U := hA.eigenvectorUnitary
  let W := hB.eigenvectorUnitary
  let K := star (U : Matrix m m ℂ) * V * (W : Matrix n n ℂ)
  let d := diagonal (fun i => (hA.eigenvalues i : ℂ))
  let e := diagonal (fun i => (hB.eigenvalues i : ℂ))
  have hAu : A = (U : Matrix m m ℂ) * d * star (U : Matrix m m ℂ) :=
    hA.spectral_theorem
  have hBw : B = (W : Matrix n n ℂ) * e * star (W : Matrix n n ℂ) :=
    hB.spectral_theorem
  have huu : star (U : Matrix m m ℂ) * (U : Matrix m m ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hww : star (W : Matrix n n ℂ) * (W : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self W
  have huU : (U : Matrix m m ℂ) * star (U : Matrix m m ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hwW : (W : Matrix n n ℂ) * star (W : Matrix n n ℂ) = 1 :=
    Unitary.coe_mul_star_self W
  have hdK : d * K = K * e := by
    have h := congrArg
      (fun T : Matrix m n ℂ => star (U : Matrix m m ℂ) * T * (W : Matrix n n ℂ)) hV
    rw [hAu, hBw] at h
    simpa only [K, Matrix.mul_assoc,
        ← Matrix.mul_assoc (star (U : Matrix m m ℂ)) (U : Matrix m m ℂ), huu,
      Matrix.one_mul, ← Matrix.mul_assoc (star (W : Matrix n n ℂ)) (W : Matrix n n ℂ), hww,
          Matrix.mul_one] using h
  have hdiag : diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * K =
      K * diagonal (fun i => (f (hB.eigenvalues i) : ℂ)) := by
    ext i j
    have h := congrArg (fun T : Matrix m n ℂ => T i j) hdK
    simp only [d, e, Matrix.diagonal_mul, Matrix.mul_diagonal] at h ⊢
    by_cases heq : hA.eigenvalues i = hB.eigenvalues j
    · rw [heq, mul_comm]
    · have hz : K i j = 0 := by
        apply (mul_eq_zero.mp
          (show ((hA.eigenvalues i : ℂ) - (hB.eigenvalues j : ℂ)) * K i j = 0 by
            linear_combination h)).resolve_left
        simpa only [sub_eq_zero, Complex.ofReal_inj] using heq
      simp only [hz, mul_zero, zero_mul]
  have hk : (U : Matrix m m ℂ) * K * star (W : Matrix n n ℂ) = V := by
    simp only [K, ← Matrix.mul_assoc, huU, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hwW, Matrix.mul_one]
  rw [hA.cfc_eq, hB.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]
  change (U : Matrix m m ℂ) * diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
    star (U : Matrix m m ℂ) * V = V * ((W : Matrix n n ℂ) *
    diagonal (fun i => (f (hB.eigenvalues i) : ℂ)) * star (W : Matrix n n ℂ))
  rw [← hk]
  simp only [Matrix.mul_assoc,
    ← Matrix.mul_assoc (star (U : Matrix m m ℂ)) (U : Matrix m m ℂ), huu,
    Matrix.one_mul, ← Matrix.mul_assoc (star (W : Matrix n n ℂ)) (W : Matrix n n ℂ), hww]
  simpa only [Matrix.mul_assoc] using congrArg
    (fun T : Matrix m n ℂ => (U : Matrix m m ℂ) * T * star (W : Matrix n n ℂ)) hdiag

/-- Every real power respects a rectangular intertwiner of positive
semidefinite matrices. -/
theorem PosSemidef.rpow_intertwine
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (V : Matrix m n ℂ)
    (hV : A * V = V * B) (s : ℝ) : A ^ s * V = V * B ^ s := by
  simpa only [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg] using
    cfc_intertwine hA.isHermitian hB.isHermitian V hV (fun x : ℝ => x ^ s)

omit [DecidableEq m] [DecidableEq n] in
/-- A matrix factor moves across the complex dot product as its conjugate
transpose. -/
theorem star_dotProduct_mulVec (A : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
/-- The real part of the standard self-pairing is the squared Euclidean norm. -/
theorem re_star_dotProduct_self_eq_norm_sq (v : n → ℂ) :
    RCLike.re (star v ⬝ᵥ v) = ‖(EuclideanSpace.equiv n ℂ).symm v‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
    PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp, dotProduct_comm]

/-- Matrix exponential respects a rectangular intertwiner. -/
theorem mul_exp_eq_exp_mul_of_mul_eq
    (V : Matrix m n ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (h : V * A = B * V) :
    V * NormedSpace.exp A = NormedSpace.exp B * V := by
  have hpow : ∀ k : ℕ, V * A ^ k = B ^ k * V := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      calc
        V * (A ^ k * A) = (V * A ^ k) * A := by rw [Matrix.mul_assoc]
        _ = (B ^ k * V) * A := by rw [ih]
        _ = B ^ k * (B * V) := by rw [Matrix.mul_assoc, h]
        _ = (B ^ k * B) * V := by rw [Matrix.mul_assoc]
  have hleft :
      HasSum (fun k : ℕ => V * (((k.factorial : ℂ)⁻¹) • A ^ k))
        (V * NormedSpace.exp A) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).map
      (mulLeftLinearMap n ℂ V)
      (mulLeftLinearMap n ℂ V).continuous_of_finiteDimensional
  have hright :
      HasSum (fun k : ℕ => (((k.factorial : ℂ)⁻¹) • B ^ k) * V)
        (NormedSpace.exp B * V) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).map
      (mulRightLinearMap m ℂ V)
      (mulRightLinearMap m ℂ V).continuous_of_finiteDimensional
  have hseries :
      (fun k : ℕ => V * (((k.factorial : ℂ)⁻¹) • A ^ k)) =
        fun k : ℕ => (((k.factorial : ℂ)⁻¹) • B ^ k) * V := by
    funext k
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun X => ((k.factorial : ℂ)⁻¹) • X) (hpow k)
  have hleft' :
      HasSum (fun k : ℕ => (((k.factorial : ℂ)⁻¹) • B ^ k) * V)
        (V * NormedSpace.exp A) := by
    rw [← hseries]
    exact hleft
  exact hleft'.unique hright

end Matrix
