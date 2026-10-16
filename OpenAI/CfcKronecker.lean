/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu

Ported from `LionSR/QICLean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0), files
`QICLean/Algebra/MatrixKroneckerEmbed.lean` and
`QICLean/Analysis/CfcKronecker.lean`.
-/
import OpenAI.CfcConjugation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Continuous functional calculus through tensor embeddings

The maps `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ B` are continuous star-algebra homomorphisms, so
the real continuous functional calculus commutes with both embeddings.
-/

open scoped Matrix Kronecker

noncomputable section

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Tensor a matrix with the identity on the right. -/
noncomputable def leftKroneckerEmbed :
    Matrix m m ℂ →⋆ₐ[ℂ] Matrix (m × n) (m × n) ℂ := by
  exact
    { toFun := fun A => A ⊗ₖ (1 : Matrix n n ℂ)
      map_one' := one_kronecker_one
      map_mul' := fun A B => by rw [← mul_kronecker_mul, mul_one]
      map_zero' := zero_kronecker _
      map_add' := fun A B => add_kronecker A B _
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          smul_kronecker, one_kronecker_one]
      map_star' := fun A => by
        rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_kronecker,
          conjTranspose_one] }

@[simp] theorem leftKroneckerEmbed_apply (A : Matrix m m ℂ) :
    leftKroneckerEmbed (n := n) A = A ⊗ₖ (1 : Matrix n n ℂ) := by
  rfl

/-- Tensor a matrix with the identity on the left. -/
noncomputable def rightKroneckerEmbed :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (m × n) (m × n) ℂ := by
  exact
    { toFun := fun B => (1 : Matrix m m ℂ) ⊗ₖ B
      map_one' := one_kronecker_one
      map_mul' := fun A B => by rw [← mul_kronecker_mul, mul_one]
      map_zero' := kronecker_zero _
      map_add' := fun A B => kronecker_add _ A B
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          kronecker_smul, one_kronecker_one]
      map_star' := fun B => by
        rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_kronecker,
          conjTranspose_one] }

@[simp] theorem rightKroneckerEmbed_apply (B : Matrix n n ℂ) :
    rightKroneckerEmbed (m := m) B = (1 : Matrix m m ℂ) ⊗ₖ B := by
  rfl

theorem cfc_kronecker_one {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (A ⊗ₖ (1 : Matrix n n ℂ)) = cfc f A ⊗ₖ (1 : Matrix n n ℂ) := by
  have hcont : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (leftKroneckerEmbed (m := m) (n := n)) :=
    LinearMap.continuous_of_finiteDimensional
      ((leftKroneckerEmbed (m := m) (n := n) :
        Matrix m m ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ))
  have hsa : IsSelfAdjoint A := hA
  have hsa' : IsSelfAdjoint (leftKroneckerEmbed (n := n) A) := by
    rw [leftKroneckerEmbed_apply, IsSelfAdjoint, star_eq_conjTranspose,
      conjTranspose_kronecker, hA.eq, conjTranspose_one]
  simpa [leftKroneckerEmbed_apply] using
    (StarAlgHomClass.map_cfc (leftKroneckerEmbed (m := m) (n := n)) f A
      hcont hcontφ hsa hsa').symm

theorem cfc_one_kronecker {B : Matrix n n ℂ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f ((1 : Matrix m m ℂ) ⊗ₖ B) = (1 : Matrix m m ℂ) ⊗ₖ cfc f B := by
  have hcont : ContinuousOn f (spectrum ℝ B) := B.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (rightKroneckerEmbed (m := m) (n := n)) :=
    LinearMap.continuous_of_finiteDimensional
      ((rightKroneckerEmbed (m := m) (n := n) :
        Matrix n n ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ))
  have hsa : IsSelfAdjoint B := hB
  have hsa' : IsSelfAdjoint (rightKroneckerEmbed (m := m) B) := by
    rw [rightKroneckerEmbed_apply, IsSelfAdjoint, star_eq_conjTranspose,
      conjTranspose_kronecker, hB.eq, conjTranspose_one]
  simpa [rightKroneckerEmbed_apply] using
    (StarAlgHomClass.map_cfc (rightKroneckerEmbed (m := m) (n := n)) f B
      hcont hcontφ hsa hsa').symm

end Matrix

end
