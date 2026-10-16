/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Analysis/CfcConjugation.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.CfcConjugation

/-! # Transpose covariance of the matrix continuous functional calculus -/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n : Type*}

lemma IsHermitian.transpose_eq_map_conj {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Aᵀ = A.map (starRingEnd ℂ) := by
  have h : Aᵀ = (Aᴴ).map star := by
    rw [Matrix.conjTranspose, Matrix.map_map]
    simp [Function.comp_def]
  rw [h, hA.eq]
  rfl

variable [Fintype n] [DecidableEq n]

/-- Entrywise complex conjugation as a real star-algebra homomorphism. -/
noncomputable def conjugateStarAlgHom : Matrix n n ℂ →⋆ₐ[ℝ] Matrix n n ℂ := by
  exact
    { (RCLike.conjAe (K := ℂ)).mapMatrix.toAlgHom with
      map_star' := fun M => by
        change ((star M).map (RCLike.conjAe (K := ℂ))) =
          star (M.map (RCLike.conjAe (K := ℂ)))
        ext i j
        simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
          Matrix.map_apply, RCLike.conjAe_coe] }

@[simp] theorem conjugateStarAlgHom_apply (M : Matrix n n ℂ) :
    conjugateStarAlgHom M = M.map (starRingEnd ℂ) := by
  rfl

theorem cfc_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A)ᵀ = cfc f Aᵀ := by
  have hcont : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (conjugateStarAlgHom (n := n)) :=
    conjugateStarAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hsa : IsSelfAdjoint A := hA
  have hcfc : (cfc f A).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate f A)
  rw [hcfc.transpose_eq_map_conj, hA.transpose_eq_map_conj,
    ← conjugateStarAlgHom_apply, ← conjugateStarAlgHom_apply]
  exact StarAlgHomClass.map_cfc conjugateStarAlgHom f A hcont hcontφ hsa
    (hsa.map conjugateStarAlgHom)

end Matrix

end
