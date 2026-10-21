/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/Transport/Commutant.lean` (the tree-free part).
-/
import AreaLawForMathlib.Analysis.Matrix.FilteredNorm
import AreaLawForMathlib.LinearAlgebra.Matrix.TracePairing

/-!
# Derivative maps over the commutant

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`.

A matrix `Z` commuting with `C` makes the derivative of `C ↦ C^p` a right module map over `Z`,
and likewise the partial derivatives of the weighted geometric mean when `Z` commutes with both
arguments. Dually the trace adjoint of a right module map over `Z` is a left module map.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Set

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix commuting with `a` commutes with its ring inverse. -/
theorem commute_ringInverse_right {Z a : Matrix n n ℂ} (h : Commute Z a) :
    Commute Z (Ring.inverse a) := by
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right Z

omit [DecidableEq n] in
theorem sandwich_mul_right {V X Z : Matrix n n ℂ} (h : Commute Z V) :
    V * (X * Z) * V = V * X * V * Z := by
  rw [show V * (X * Z) * V = V * X * (Z * V) by simp only [Matrix.mul_assoc], h.eq]
  simp only [Matrix.mul_assoc]

/-- The derivative of a real power is a right module map over the commutant. -/
theorem rpowDeriv_mul_right {C Z : Matrix n n ℂ} (hC : C.PosDef) (hZ : Commute Z C) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix n n ℂ) :
    rpowDeriv p C (X * Z) = rpowDeriv p C X * Z := by
  unfold rpowDeriv
  split_ifs with h0 h1
  · simp
  · rfl
  · have hp' : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm h0), lt_of_le_of_ne hp.2 h1⟩
    rw [rpowFDeriv_apply hC hp', rpowFDeriv_apply hC hp', smul_mul_assoc]
    congr 1
    have hint := (integrableOn_rpowFDerivIntegrand hC hp').apply_continuousLinearMap X
    have hR : ∀ t : ℝ, Commute Z (Ring.inverse (t • (1 : Matrix n n ℂ) + C)) := fun t =>
      commute_ringInverse_right (((Commute.one_right Z).smul_right t).add_right hZ)
    have hpt : ∀ t : ℝ, t ^ p • (Ring.inverse (t • (1 : Matrix n n ℂ) + C) * (X * Z) *
        Ring.inverse (t • (1 : Matrix n n ℂ) + C)) =
        (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip Z (rpowFDerivIntegrand p C t X) := by
      intro t
      rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
        rpowFDerivIntegrand_apply, sandwich_mul_right (hR t), smul_mul_assoc]
    simp_rw [hpt]
    rw [ContinuousLinearMap.integral_comp_comm _ hint]
    rfl

/-- The partial derivative of the mean in its second argument is a right module map over the
commutant of both arguments. -/
theorem geomMeanDerivRight_mul_right {A B Z : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hZA : Commute Z A) (hZB : Commute Z B) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (X : Matrix n n ℂ) :
    geomMeanDerivRight p A B (X * Z) = geomMeanDerivRight p A B X * Z := by
  have h1 : Commute Z (A ^ (1 / 2 : ℝ)) := (PosDef.commute_rpow_left hA hZA.symm _).symm
  have h2 : Commute Z (A ^ (-(1 / 2) : ℝ)) := (PosDef.commute_rpow_left hA hZA.symm _).symm
  have hC : Commute Z (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) :=
    (h2.mul_right hZB).mul_right h2
  simp only [geomMeanDerivRight, ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [sandwich_mul_right h2, rpowDeriv_mul_right (hA.whiten hB) hC hp, sandwich_mul_right h1]

/-- The partial derivative of the mean in its first argument is a right module map over the
commutant of both arguments. -/
theorem geomMeanDerivLeft_mul_right {A B Z : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hZA : Commute Z A) (hZB : Commute Z B) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (X : Matrix n n ℂ) :
    geomMeanDerivLeft p A B (X * Z) = geomMeanDerivLeft p A B X * Z :=
  geomMeanDerivRight_mul_right hB hA hZB hZA ⟨by linarith [hp.2], by linarith [hp.1]⟩ X

omit [DecidableEq n] in
/-- The trace adjoint of a right module map over `Z` is a left module map over `Z`. -/
theorem traceAdjointMap_mul_left {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {Z : Matrix n n ℂ}
    (h : ∀ X, Φ (X * Z) = Φ X * Z) (Y : Matrix n n ℂ) :
    traceAdjointMap Φ (Z * Y) = Z * traceAdjointMap Φ Y := by
  refine ext_iff_trace_mul_right.mpr fun X => ?_
  have h2 : (Z * traceAdjointMap Φ Y * X).trace = (traceAdjointMap Φ Y * (X * Z)).trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [h2, trace_traceAdjointMap_mul, trace_traceAdjointMap_mul, h, ← Matrix.mul_assoc,
    trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]

namespace Transport

/-- A matrix commuting with `M` commutes with `M^{-iu}`. -/
theorem commute_imagPow {M Z : Matrix n n ℂ} (h : Commute Z M) (u : ℝ) :
    Commute Z (imagPow M u) := by
  have hlog : Commute Z (CFC.log M) := (Commute.cfc_real h.symm _).symm
  exact (((hlog.smul_right Complex.I).smul_right (-u))).exp_right

/-- A matrix commuting with `M` and fixing `pre` fixes the filtered vector. -/
theorem mulVec_filteredVector {M Z : Matrix n n ℂ} (hM : M.PosDef) (h : Commute Z M)
    {pre : n → ℂ} (hpre : Z *ᵥ pre = pre) : Z *ᵥ filteredVector M pre = filteredVector M pre := by
  have hc : Commute Z (M ^ (-(1 / 4) : ℝ)) := (PosDef.commute_rpow_left hM h.symm _).symm
  rw [filteredVector, mulVec_smul, filteredRaw, mulVec_mulVec, hc.eq, ← mulVec_mulVec, hpre]

end Transport

end Matrix
