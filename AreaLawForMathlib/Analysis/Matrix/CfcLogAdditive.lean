/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu

Ported from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/CfcLogAdditive.lean`.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Logarithm of a product of commuting positive definite matrices

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean`.

For commuting positive definite matrices, the continuous-functional-calculus logarithm
is additive over products.  This is the logarithmic input to the Section 7 operator means.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix.PosDef

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a positive-definite matrix, the logarithm of a real power is the exponent times
the logarithm. -/
theorem cfc_log_rpow {A : Matrix n n ℂ} (hA : A.PosDef) (s : ℝ) :
    CFC.log (A ^ s) = s • CFC.log A := by
  rw [CFC.log, CFC.log]
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  rw [← cfc_comp' Real.log (fun x : ℝ => x ^ s) A
    ((A.finite_real_spectrum.image (fun x : ℝ => x ^ s)).continuousOn Real.log)
    (A.finite_real_spectrum.continuousOn (fun x : ℝ => x ^ s))]
  rw [← cfc_smul s Real.log A (A.finite_real_spectrum.continuousOn Real.log)]
  apply cfc_congr
  intro x hx
  have hxpos : 0 < x := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hA.eigenvalues_pos i
  change Real.log (x ^ s) = s * Real.log x
  rw [Real.log_rpow hxpos]

/-- The logarithm of a product of commuting positive definite matrices is the sum of their
logarithms. -/
theorem cfc_log_mul {X Y : Matrix n n ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    (hXY : Commute X Y) :
    CFC.log (X * Y) = CFC.log X + CFC.log Y := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hlog : Commute (CFC.log X) (CFC.log Y) :=
    Commute.cfc_real (Commute.cfc_real hXY.symm Real.log).symm Real.log
  have hsa : IsSelfAdjoint (CFC.log X + CFC.log Y) :=
    IsSelfAdjoint.add IsSelfAdjoint.log IsSelfAdjoint.log
  have key : X * Y = NormedSpace.exp (CFC.log X + CFC.log Y) := by
    rw [NormedSpace.exp_add_of_commute hlog, CFC.exp_log X hX.isStrictlyPositive,
      CFC.exp_log Y hY.isStrictlyPositive]
  rw [key, CFC.log_exp _ hsa]

end Matrix.PosDef
