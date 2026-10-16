/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewPhase.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
lift and Schmidt-mirroring portion.
-/
import OpenAI.ConditionalSkewEta

/-! # Lifted phase geometry for the conditional skew estimate -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open Matrix Entropy.MarginalPhase

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- The marginal `ρ_W` reassociated to `X × (U × F)`. -/
def rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  (margW θ).submatrix assocE.symm assocE.symm

/-- An operator on `X × (U × F)`, tensored with the identity on `P`. -/
def liftR (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ M.submatrix assocE assocE

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem liftR_mul (A B : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) A * liftR B = liftR (A * B) := by
  rw [liftR, liftR, liftR, ← mul_kronecker_mul, Matrix.one_mul, submatrix_mul_equiv]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem liftR_sub (A B : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) (A - B) = liftR A - liftR B := by
  ext i j
  simp [liftR, mul_sub]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [Fintype F] in
theorem liftR_one :
    liftR (P₀ := P₀) (P₁ := P₁) (1 : Matrix (X × (U × F)) (X × (U × F)) ℂ) = 1 := by
  rw [liftR, submatrix_one_equiv, one_kronecker_one]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem conjTranspose_liftR (A : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (liftR (P₀ := P₀) (P₁ := P₁) A)ᴴ = liftR Aᴴ := by
  rw [liftR, liftR, conjTranspose_kronecker, conjTranspose_one, conjTranspose_submatrix]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] in
theorem liftR_embedF (B : Matrix (X × U) (X × U) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) (embedF (F := F) B) = liftY B := by
  rw [liftR, embedF, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, liftY]

theorem liftR_cfcC_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (g : ℝ → ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) (cfcC (rhoW θ) g) =
      (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ cfcC (margW θ) g := by
  rw [liftR, rhoW, cfcC_submatrix_equiv (posSemidef_margW θ).1, submatrix_submatrix,
    Equiv.symm_comp_self, submatrix_id_id]

theorem liftP_liftR_comm (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ)
    (B : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    liftP A * liftR B = liftR B * liftP A := by
  rw [liftP, liftR, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/-- Schmidt mirroring across `P` and `W`: `g(ρ_P) θ = g(ρ_W) θ`. -/
theorem liftP_cfcC_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (g : ℝ → ℂ) :
    liftP (cfcC (margP θ) g) *ᵥ θ = liftR (cfcC (rhoW θ) g) *ᵥ θ := by
  rw [liftP, liftR_cfcC_rhoW]
  exact cfcC_kronecker_one_mulVec θ g

omit [DecidableEq P₀] [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [DecidableEq F] in
theorem marginalXU_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    marginalXU (rhoW θ) = margY θ := by
  rw [marginalXU, rhoW, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  rfl

theorem liftP_ker_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftP (cfcC (margP θ) kerFun) *ᵥ θ = 0 := by
  have hA := (posSemidef_margP θ).1
  exact liftP_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
    (by rw [mul_cfcC_ker hA, trace_zero])

theorem liftY_ker_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (cfcC (margY θ) kerFun) *ᵥ θ = 0 := by
  have hA := (posSemidef_margY θ).1
  exact liftY_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
    (by rw [mul_cfcC_ker hA, trace_zero])

/-- The imaginary-axis vector `ρ_P^{[-iu]} ρ_Y^{[iu]} θ` equals
`ρ̂_Y^{iu} ρ̂_{YF}^{-iu} θ`. -/
theorem imag_vector_eq (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    liftP (cfcC (margP θ) (suppPowFun (-((u : ℂ) * Complex.I)))) *ᵥ
        (liftY (cfcC (margY θ) (suppPowFun ((u : ℂ) * Complex.I))) *ᵥ θ) =
      liftR (embedF (cfcC (margY θ) (hatFun u)) *
        cfcC (rhoW θ) (hatFun (-u))) *ᵥ θ := by
  have hP := (posSemidef_margP θ).1
  have hY := (posSemidef_margY θ).1
  have hneg : -((u : ℂ) * Complex.I) = ((-u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  set a := cfcC (margP θ) (hatFun (-u))
  have hker : liftY (P₀ := P₀) (P₁ := P₁) (F := F)
      (cfcC (margY θ) kerFun) *ᵥ (liftP a *ᵥ θ) = 0 := by
    rw [mulVec_mulVec, ← liftP_liftY_comm, ← mulVec_mulVec, liftY_ker_mulVec,
      mulVec_zero]
  rw [hneg, cfcC_suppPow_imag hP, cfcC_suppPow_imag hY, mulVec_mulVec,
    liftP_liftY_comm, ← mulVec_mulVec, liftP_sub, sub_mulVec, liftP_ker_mulVec, sub_zero,
    liftY_sub, sub_mulVec, hker, sub_zero, liftP_cfcC_mulVec, ← liftR_embedF,
    mulVec_mulVec, liftR_mul]

end Entropy.ConditionalSkew
