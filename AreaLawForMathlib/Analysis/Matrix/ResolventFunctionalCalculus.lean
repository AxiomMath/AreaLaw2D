/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and restricted to the power-derivative dependency from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/ResolventFunctionalCalculus.lean`.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Resolvent form of the real-power integrand

Extends
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean`.

This file contains the single functional-calculus identity needed by the Section 7
Fréchet derivative of a positive matrix power.
-/

open Filter MeasureTheory Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

private instance {n : Type*} [Fintype n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint := by
  let := Classical.decEq n
  exact ContinuousFunctionalCalculus.toNonUnital

/-- Resolvent form of the Löwner real-power integrand. -/
theorem cfc_rpowIntegrand₀₁_eq_resolvent
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {p t : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    cfc (Real.rpowIntegrand₀₁ p t) A =
      t ^ (p - 1) • (1 : Matrix n n ℂ) -
        t ^ p • (t • (1 : Matrix n n ℂ) + A)⁻¹ := by
  have hA_nonneg : (0 : Matrix n n ℂ) ≤ A :=
    Matrix.nonneg_iff_posSemidef.mpr hA
  rw [Real.rpowIntegrand₀₁_eq_sub (ne_of_lt hp.2) ht]
  have hg : ContinuousOn (fun z : ℝ => (t + z)⁻¹) (spectrum ℝ A) := by
    apply (continuous_const.add continuous_id).continuousOn.inv₀
    intro z hz
    have hz_nonneg := spectrum_nonneg_of_nonneg hA_nonneg hz
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht hz_nonneg)
  have hspectrum : ∀ r ∈ spectrum ℝ A, t + r ≠ 0 := by
    intro r hr
    have hr_nonneg := spectrum_nonneg_of_nonneg hA_nonneg hr
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht hr_nonneg)
  have hself : IsSelfAdjoint A := hA.isHermitian
  have hg_mul : ContinuousOn (fun z : ℝ => t ^ p * (t + z)⁻¹) (spectrum ℝ A) :=
    continuousOn_const.mul hg
  have hadd : ContinuousOn (fun z : ℝ => t + z) (spectrum ℝ A) :=
    (continuous_const.add continuous_id).continuousOn
  have hcfc := cfc_sub (fun _ : ℝ => t ^ (p - 1))
    (fun z : ℝ => t ^ p * (t + z)⁻¹) A continuousOn_const hg_mul
  have hcfc_add :
      cfc (fun z : ℝ => t + z) A = algebraMap ℝ (Matrix n n ℂ) t + A := by
    simpa only [id_eq, cfc_id' ℝ A hself] using
      cfc_const_add t (fun z : ℝ => z) A continuous_id.continuousOn hself
  rw [hcfc, cfc_const _ _ hself, cfc_const_mul _ _ _ hg,
    cfc_inv _ _ hspectrum hadd hself, hcfc_add]
  simp only [Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse]

end Matrix
