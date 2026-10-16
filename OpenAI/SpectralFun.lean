/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0), files
`QICLean/Analysis/ResolventDefect.lean`,
`QICLean/Analysis/SpectralKronecker.lean`, and
`QICLean/Analysis/SpectralFunUnique.lean`.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Complex spectral functions of finite Hermitian matrices

This is the common eigenbasis calculus needed by the support-power and conditional-skew layers.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply an arbitrary complex scalar function in the orthonormal basis `U`. -/
def spectralFun (U : unitary (Matrix n n ℂ)) (f : n → ℂ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * diagonal f * star (U : Matrix n n ℂ)

theorem spectralFun_mul (U : unitary (Matrix n n ℂ)) (f g : n → ℂ) :
    spectralFun U f * spectralFun U g = spectralFun U (f * g) := by
  simp only [spectralFun]
  rw [show (U : Matrix n n ℂ) * diagonal f * star (U : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * diagonal g * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * diagonal f * (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
        diagonal g * star (U : Matrix n n ℂ) by simp only [Matrix.mul_assoc],
    Unitary.star_mul_self_of_mem U.2, Matrix.mul_one, Matrix.mul_assoc (U : Matrix n n ℂ),
    diagonal_mul_diagonal]
  rfl

theorem spectralFun_add (U : unitary (Matrix n n ℂ)) (f g : n → ℂ) :
    spectralFun U (f + g) = spectralFun U f + spectralFun U g := by
  rw [spectralFun, spectralFun, spectralFun,
    show diagonal (f + g) = diagonal f + diagonal g from (diagonal_add f g).symm,
    Matrix.mul_add, Matrix.add_mul]

theorem spectralFun_const (U : unitary (Matrix n n ℂ)) (c : ℂ) :
    spectralFun U (fun _ => c) = c • 1 := by
  simp only [spectralFun]
  rw [show diagonal (fun _ : n => c) = c • (1 : Matrix n n ℂ) by
      ext i j
      by_cases h : i = j <;> simp [h, diagonal],
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Unitary.mul_star_self_of_mem U.2]

theorem spectralFun_one (U : unitary (Matrix n n ℂ)) :
    spectralFun U (fun _ => 1) = 1 := by
  rw [spectralFun_const, one_smul]

theorem conjTranspose_spectralFun (U : unitary (Matrix n n ℂ)) (f : n → ℂ) :
    (spectralFun U f)ᴴ = spectralFun U (star f) := by
  simp only [spectralFun, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose, Matrix.mul_assoc]

theorem spectralFun_smul (U : unitary (Matrix n n ℂ)) (c : ℂ) (f : n → ℂ) :
    spectralFun U (c • f) = c • spectralFun U f := by
  simp only [spectralFun, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem spectralFun_apply (U : unitary (Matrix n n ℂ)) (f : n → ℂ) (i j : n) :
    spectralFun U f i j = ∑ k, (U : Matrix n n ℂ) i k * f k * star (U : Matrix n n ℂ) k j := by
  simp [spectralFun, mul_apply, diagonal, mul_assoc]

/-- The spectral theorem in `spectralFun` form. -/
theorem IsHermitian.spectralFun_eigenvectorUnitary {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    spectralFun hA.eigenvectorUnitary (fun k => (hA.eigenvalues k : ℂ)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

theorem IsHermitian.cfc_eq_spectralFun {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f A = spectralFun hA.eigenvectorUnitary
      (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) := by
  rw [hA.cfc_eq]
  rfl

theorem IsHermitian.spectralFun_eq_cfc_re_add_im {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (g : ℝ → ℂ) :
    spectralFun hA.eigenvectorUnitary (fun k => g (hA.eigenvalues k)) =
      cfc (fun t => (g t).re) A + Complex.I • cfc (fun t => (g t).im) A := by
  rw [hA.cfc_eq_spectralFun, hA.cfc_eq_spectralFun, ← spectralFun_smul, ← spectralFun_add]
  congr 1
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-- A complex spectral function of `cfc h A` is the composite spectral function of `A`. -/
theorem IsHermitian.spectralFun_cfc_comp {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (h : ℝ → ℝ)
    (hB : (cfc h A).IsHermitian) (g : ℝ → ℂ) :
    spectralFun hB.eigenvectorUnitary
        (fun k => g (hB.eigenvalues k)) =
      spectralFun hA.eigenvectorUnitary
        (fun k => g (h (hA.eigenvalues k))) := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) :=
    fun f => (finite_real_spectrum (A := A)).continuousOn f
  have hfin' : ∀ f : ℝ → ℝ, ContinuousOn f (h '' spectrum ℝ A) :=
    fun f => ((finite_real_spectrum (A := A)).image h).continuousOn f
  rw [hB.spectralFun_eq_cfc_re_add_im,
    ← cfc_comp (fun t => (g t).re) h A hA.isSelfAdjoint
      (hfin' _) (hfin _),
    ← cfc_comp (fun t => (g t).im) h A hA.isSelfAdjoint
      (hfin' _) (hfin _)]
  exact (hA.spectralFun_eq_cfc_re_add_im (g ∘ h)).symm

/-- The affine function `t ↦ a t + b` of a Hermitian matrix. -/
theorem IsHermitian.cfc_affine {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (a b : ℝ) :
    cfc (fun t : ℝ => a * t + b) A =
      a • A + b • (1 : Matrix n n ℂ) := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) :=
    fun f => (finite_real_spectrum (A := A)).continuousOn f
  rw [cfc_add (a := A) (fun t : ℝ => a * t) (fun _ => b)
      (hfin _) (hfin _),
    cfc_const_mul a (fun t : ℝ => t) A (hfin _),
    cfc_id' ℝ A hA.isSelfAdjoint,
    cfc_const b A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

end Matrix

end
