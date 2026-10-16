/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseSetup.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import QuantumInfo.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Marginals on three systems for the marginal-phase comparison

This port uses Physlib's canonical `Matrix.traceLeft` and `Matrix.traceRight` in place of
QICLean's duplicate partial-trace names.
-/

open scoped Matrix Kronecker

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- Reassociate `(X × U) × F` as `X × (U × F)`. -/
abbrev assocE : (X × U) × F ≃ X × (U × F) := Equiv.prodAssoc X U F

/-- The marginal `ρ_{XU} = tr_F ρ`. -/
def marginalXU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix (X × U) (X × U) ℂ :=
  Matrix.traceRight (ρ.submatrix assocE assocE)

/-- The marginal `ρ_U = tr_X ρ_{XU}`. -/
def marginalU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) : Matrix U U ℂ :=
  Matrix.traceLeft (marginalXU ρ)

/-- The marginal `ρ_{UF} = tr_X ρ`. -/
def marginalUF (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix (U × F) (U × F) ℂ :=
  Matrix.traceLeft ρ

/-- The reference operator `σ_f = I_X / dim(X) ⊗ ρ_{UF}`. -/
def sigmaF (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  ((Fintype.card X : ℂ)⁻¹ • (1 : Matrix X X ℂ)) ⊗ₖ marginalUF ρ

/-- The reference operator `σ_s = I_X / dim(X) ⊗ ρ_U`. -/
def sigmaS (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix (X × U) (X × U) ℂ :=
  ((Fintype.card X : ℂ)⁻¹ • (1 : Matrix X X ℂ)) ⊗ₖ marginalU ρ

/-- Embed an operator on `X × U` by tensoring it with the identity on `F`. -/
def embedF (W : Matrix (X × U) (X × U) ℂ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  (W ⊗ₖ (1 : Matrix F F ℂ)).submatrix assocE.symm assocE.symm

omit [DecidableEq X] [DecidableEq U] in
theorem embedF_mul (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) A * embedF B = embedF (A * B) := by
  rw [embedF, embedF, embedF, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

omit [Fintype X] [Fintype U] [Fintype F] in
theorem embedF_one : embedF (F := F) (1 : Matrix (X × U) (X × U) ℂ) = 1 := by
  rw [embedF, one_kronecker_one, submatrix_one_equiv]

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] in
theorem conjTranspose_embedF (W : Matrix (X × U) (X × U) ℂ) :
    (embedF (F := F) W)ᴴ = embedF Wᴴ := by
  rw [embedF, embedF, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one]

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] in
theorem embedF_sub (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (A - B) = embedF A - embedF B := by
  ext i j
  simp [embedF, sub_mul]

omit [DecidableEq X] [DecidableEq U] in
/-- `tr (M (W ⊗ I_F)) = tr (tr_F(M) W)`. -/
theorem trace_mul_embedF (M : Matrix (X × (U × F)) (X × (U × F)) ℂ)
    (W : Matrix (X × U) (X × U) ℂ) :
    (M * embedF W).trace = (Matrix.traceRight (M.submatrix assocE assocE) * W).trace := by
  rw [← trace_mul_kron_one_right, embedF, ← Matrix.trace_submatrix _ assocE,
    ← submatrix_mul_equiv (e₂ := assocE)]
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]

omit [DecidableEq X] [Fintype U] [DecidableEq U] [DecidableEq F] in
theorem marginalU_eq (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    marginalU ρ = Matrix.traceRight (marginalUF ρ) := by
  ext u u'
  simp only [marginalU, marginalXU, marginalUF, Matrix.traceLeft, Matrix.traceRight,
    Matrix.of_apply, submatrix_apply, Equiv.prodAssoc_apply]
  exact Finset.sum_comm

omit [Fintype U] [DecidableEq U] [DecidableEq F] in
theorem traceRight_sigmaF (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix.traceRight ((sigmaF ρ).submatrix assocE assocE) = sigmaS ρ := by
  ext ⟨x, u⟩ ⟨x', u'⟩
  simp only [sigmaF, sigmaS, Matrix.traceRight, Matrix.of_apply, submatrix_apply,
    Equiv.prodAssoc_apply, kroneckerMap_apply, marginalU_eq, Finset.mul_sum]

end Entropy.MarginalPhase

end
