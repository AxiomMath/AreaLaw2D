/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI

Ported and specialized from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/ProjectionCfcUpperBound.lean` and
`QICLean/Analysis/ProjectionQuadraticBound.lean`.
-/
import OpenAI.MatrixIntertwine
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Scalar floors for positive matrices

The two finite-dimensional order consequences needed by the filtered metric
floor estimate, specialized away from the source's general projection-compression API.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

/-- Matrix order implies order of real quadratic forms. -/
theorem re_dotProduct_mulVec_le_of_le
    {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hAB : A ≤ B) (v : n → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).re ≤ (star v ⬝ᵥ (B *ᵥ v)).re := by
  have h := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg v)).1
  simpa only [sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using h

/-- A positive scalar lower bound controls every nonpositive real power. -/
theorem PosDef.rpow_le_smul_one_of_scalar_floor
    {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosDef)
    {b s : ℝ} (hb : 0 < b) (hs : s ≤ 0) (hfloor : b • (1 : Matrix n n ℂ) ≤ M) :
    M ^ s ≤ b ^ s • (1 : Matrix n n ℂ) := by
  classical
  have hspectrum : ∀ x ∈ spectrum ℝ M, b ≤ x :=
    (algebraMap_le_iff_le_spectrum hM.isHermitian.isSelfAdjoint).mp
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor)
  have hcfc : cfc (fun x : ℝ => x ^ s) M ≤ b ^ s • (1 : Matrix n n ℂ) := by
    have h := (cfc_le_algebraMap_iff (fun x : ℝ => x ^ s) (b ^ s) M
      (hf := Matrix.finite_real_spectrum.continuousOn _) (ha := hM.isHermitian.isSelfAdjoint)).mpr
        (fun x hx => Real.rpow_le_rpow_of_nonpos hb (hspectrum x hx) hs)
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  simpa only [CFC.rpow_eq_cfc_real hM.posSemidef.nonneg] using hcfc

end Matrix
