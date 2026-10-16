/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewSetup.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.CfcComplex
import QuantumInfo.ForMathlib.Matrix

/-!
# The scalar function of the conditional skew estimate

This first layer defines the three marginals, their tensor lifts, and the entire-function
expression used in Lemma 5.3.  It uses Physlib's `traceLeft` and `traceRight` directly.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- The scalar power function that vanishes at zero. -/
def suppPowFun (z : ℂ) (t : ℝ) : ℂ := if t = 0 then 0 else ((t : ℝ) : ℂ) ^ z

/-- The marginal on `P₀ × P₁`. -/
def margP (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (P₀ × P₁) (P₀ × P₁) ℂ :=
  Matrix.traceRight (vecMulVec θ (star θ))

/-- The marginal on `(X × U) × F`. -/
def margW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    Matrix ((X × U) × F) ((X × U) × F) ℂ :=
  Matrix.traceLeft (vecMulVec θ (star θ))

/-- The marginal on `X × U`. -/
def margY (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (X × U) (X × U) ℂ :=
  Matrix.traceRight (margW θ)

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_margP (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    (margP θ).PosSemidef := by
  classical
  exact (posSemidef_vecMulVec_self_star θ).traceRight

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_margW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    (margW θ).PosSemidef := by
  classical
  exact (posSemidef_vecMulVec_self_star θ).traceLeft

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_margY (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    (margY θ).PosSemidef := by
  classical
  exact (posSemidef_margW θ).traceRight

/-- Lift an operator on `P₀ × P₁`. -/
def liftP (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  A ⊗ₖ (1 : Matrix ((X × U) × F) ((X × U) × F) ℂ)

/-- Lift an operator on `X × U`. -/
def liftY (B : Matrix (X × U) (X × U) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix F F ℂ))

/-- Regroup `(P₀ P₁)((X U)F)` as `(P₀ X)(P₁(U F))`. -/
def regroup (q : (P₀ × P₁) × ((X × U) × F)) : (P₀ × X) × (P₁ × (U × F)) :=
  ((q.1.1, q.2.1.1), (q.1.2, (q.2.1.2, q.2.2)))

/-- Lift an operator on `P₀ × X`. -/
def liftH (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (h ⊗ₖ (1 : Matrix (P₁ × (U × F)) (P₁ × (U × F)) ℂ)).submatrix regroup regroup

/-- The scalar function in the conditional skew estimate. -/
def skewFun (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    (h : Matrix (P₀ × X) (P₀ × X) ℂ) (z : ℂ) : ℂ :=
  star θ ⬝ᵥ ((liftP (cfcC (margP θ) (suppPowFun z)) *
    liftY (cfcC (margY θ) (suppPowFun (-z))) * liftH h *
    liftP (cfcC (margP θ) (suppPowFun (-z))) *
    liftY (cfcC (margY θ) (suppPowFun z))) *ᵥ θ)

omit [DecidableEq P₀] [DecidableEq P₁] in
theorem liftP_mul (A B : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    liftP (X := X) (U := U) (F := F) A * liftP B = liftP (A * B) := by
  rw [liftP, liftP, liftP, ← mul_kronecker_mul, Matrix.one_mul]

omit [DecidableEq X] [DecidableEq U] in
theorem liftY_mul (A B : Matrix (X × U) (X × U) ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) A * liftY B = liftY (A * B) := by
  rw [liftY, liftY, liftY, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.one_mul]

theorem liftP_liftY_comm (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ)
    (B : Matrix (X × U) (X × U) ℂ) :
    liftP (F := F) A * liftY B = liftY B * liftP A := by
  rw [liftP, liftY, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁] [Fintype X]
  [Fintype U] [Fintype F] in
theorem conjTranspose_liftP (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    (liftP (X := X) (U := U) (F := F) A)ᴴ = liftP Aᴴ := by
  rw [liftP, liftP, conjTranspose_kronecker, conjTranspose_one]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] in
theorem conjTranspose_liftY (B : Matrix (X × U) (X × U) ℂ) :
    (liftY (P₀ := P₀) (P₁ := P₁) (F := F) B)ᴴ = liftY Bᴴ := by
  rw [liftY, liftY, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_one]

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [Fintype X] [DecidableEq X]
  [Fintype U] [Fintype F] in
theorem conjTranspose_liftH (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    (liftH (U := U) (F := F) (P₁ := P₁) h)ᴴ = liftH hᴴ := by
  rw [liftH, liftH, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [Fintype F] in
theorem liftP_one :
    liftP (X := X) (U := U) (F := F) (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) = 1 := by
  rw [liftP, one_kronecker_one]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [Fintype F] in
theorem liftY_one :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (1 : Matrix (X × U) (X × U) ℂ) = 1 := by
  rw [liftY, one_kronecker_one, one_kronecker_one]

end Entropy.ConditionalSkew

end
