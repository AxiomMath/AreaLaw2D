/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/CfcConjugation.lean`.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import QuantumInfo.ForMathlib.Isometry

/-! # Unitary covariance of the matrix functional calculus -/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

section Reindex

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Reindexing rows and columns by an equivalence, as a star-algebra homomorphism. -/
noncomputable def reindexStarAlgHom (e : m ≃ n) :
    Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun M := M.submatrix e.symm e.symm
  map_one' := by simp [Matrix.submatrix_one_equiv]
  map_mul' A B := by rw [← Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.submatrix_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      show (r • (1 : Matrix m m ℂ)).submatrix e.symm e.symm =
          r • ((1 : Matrix m m ℂ).submatrix e.symm e.symm) from rfl,
      Matrix.submatrix_one_equiv]
  map_star' A := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, Matrix.conjTranspose_submatrix]

@[simp] theorem reindexStarAlgHom_apply (e : m ≃ n) (M : Matrix m m ℂ) :
    reindexStarAlgHom e M = M.submatrix e.symm e.symm := rfl

/-- Functional calculus commutes with reindexing a Hermitian matrix. -/
theorem cfc_submatrix_equiv {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (e : m ≃ n) :
    cfc f (A.submatrix e.symm e.symm) = (cfc f A).submatrix e.symm e.symm := by
  have hcont : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (reindexStarAlgHom (m := m) (n := n) e) :=
    LinearMap.continuous_of_finiteDimensional
      ((reindexStarAlgHom (m := m) (n := n) e : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ))
  have hsa : IsSelfAdjoint A := hA
  have hsa' : IsSelfAdjoint (reindexStarAlgHom e A) := by
    change (A.submatrix e.symm e.symm).IsHermitian
    exact hA.submatrix e.symm
  simpa only [reindexStarAlgHom_apply] using
    (StarAlgHomClass.map_cfc (reindexStarAlgHom (m := m) (n := n) e) f A
      hcont hcontφ hsa hsa').symm

end Reindex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real powers commute with unitary conjugation of a positive-semidefinite matrix. -/
theorem rpow_conj_unitary {A : Matrix n n ℂ} (hA : A.PosSemidef) (s : ℝ)
    (U : unitary (Matrix n n ℂ)) :
    ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)) ^ s =
      (U : Matrix n n ℂ) * A ^ s * star (U : Matrix n n ℂ) := by
  have hconj : ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same (star (U : Matrix n n ℂ))
    rwa [star_eq_conjTranspose, conjTranspose_conjTranspose] at h
  rw [CFC.rpow_eq_cfc_real hconj.nonneg, CFC.rpow_eq_cfc_real hA.nonneg]
  have hUinv : (↑(U⁻¹) : Matrix n n ℂ) = star (U : Matrix n n ℂ) := by
    rw [← Unitary.star_eq_inv U, Unitary.coe_star]
  rw [← hUinv]
  exact Matrix.cfc_conj_unitary (A := A) (fun x : ℝ => x ^ s) U

end Matrix
