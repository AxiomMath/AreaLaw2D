/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Analysis/ResolventPhaseBound.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
continuity, integrability, and tail-bound portion.
-/
import OpenAI.ResolventPhaseGap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The square-root rate of a resolvent defect -/

open MeasureTheory Set Filter Topology
open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

/-- The phase rate `𝓡_η`. -/
def phaseRate (D η : ℝ) : ℝ :=
  if 0 < η then
    √(min 1 η) + √(η * Real.log (Real.exp 1 * D / min 1 η))
  else 0

theorem sqrt_mul_le_add {X Y t : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (ht : 0 < t) : √(X * Y) ≤ (t * X + Y / t) / 2 := by
  have h := two_mul_le_add_sq (√(t * X)) (√(Y / t))
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), mul_assoc,
    ← Real.sqrt_mul (by positivity),
    show t * X * (Y / t) = X * Y by field_simp] at h
  linarith

theorem sqrt_mul_rpow_neg {c v q : ℝ} (hc : 0 ≤ c) (hv : 0 < v) :
    √(c * v ^ (-q)) = √c * v ^ (-q / 2) := by
  rw [Real.sqrt_mul hc, Real.sqrt_eq_rpow (v ^ (-q)), ← Real.rpow_mul hv.le]
  ring_nf

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

namespace ResolventCompression

variable (R : ResolventCompression n m)

def sqrtRatio (v : ℝ) : ℝ := √(R.defect v / v)

theorem defect_continuousOn : ContinuousOn R.defect (Ici 0) := by
  have hfun : R.defect = fun v =>
      ∑ k, (R.lam k + v)⁻¹ * R.weightA k -
        ∑ j, (R.mu j + v)⁻¹ * R.weightB j :=
    funext R.defect_eq_sum
  rw [hfun]
  refine ContinuousOn.sub
    (continuousOn_finsetSum _ fun k _ => ?_)
    (continuousOn_finsetSum _ fun j _ => ?_)
  · refine ContinuousOn.mul
      (ContinuousOn.inv₀ (by fun_prop) fun v hv => ?_) continuousOn_const
    have : (0 : ℝ) ≤ v := hv
    linarith [R.lam_pos k]
  · refine ContinuousOn.mul
      (ContinuousOn.inv₀ (by fun_prop) fun v hv => ?_) continuousOn_const
    have : (0 : ℝ) ≤ v := hv
    linarith [R.mu_pos j]

theorem sqrtRatio_continuousOn : ContinuousOn R.sqrtRatio (Ioi 0) := by
  refine ContinuousOn.sqrt
    (ContinuousOn.div (R.defect_continuousOn.mono Ioi_subset_Ici_self)
      continuousOn_id fun v hv => ?_)
  exact ne_of_gt hv

theorem sqrtRatio_le_left {v : ℝ} (hv : 0 < v) :
    R.sqrtRatio v ≤ √R.invQuadA * v ^ (-(1 : ℝ) / 2) := by
  rw [sqrtRatio, ← sqrt_mul_rpow_neg R.invQuadA_nonneg hv,
    Real.rpow_neg_one]
  refine Real.sqrt_le_sqrt ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (R.defect_le_invQuadA hv.le)
    (inv_nonneg.2 hv.le)

theorem sqrtRatio_le_right {v : ℝ} (hv : 0 < v) :
    R.sqrtRatio v ≤ √R.quadB * v ^ (-(3 : ℝ) / 2) := by
  rw [sqrtRatio, ← sqrt_mul_rpow_neg R.quadB_nonneg hv]
  refine Real.sqrt_le_sqrt ?_
  have h := R.defect_le_quadB_div_sq hv
  rw [show v ^ (-(3 : ℝ)) = (v ^ 2 * v)⁻¹ by
    rw [Real.rpow_neg hv.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring]
  rw [mul_inv, ← mul_assoc, ← div_eq_mul_inv, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right h hv.le

theorem integrableOn_sqrtRatio : IntegrableOn R.sqrtRatio (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hr : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) / 2)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    refine (hr.const_mul √R.invQuadA).mono' ?_ ?_
    · exact (R.sqrtRatio_continuousOn.mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun v hv => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by unfold sqrtRatio; positivity)]
      exact R.sqrtRatio_le_left hv.1
  · have hr : IntegrableOn (fun v : ℝ => v ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine (hr.const_mul √R.quadB).mono' ?_ ?_
    · exact (R.sqrtRatio_continuousOn.mono
        (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun v hv => ?_)
      have hv' : (0 : ℝ) < v := lt_trans one_pos hv
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by unfold sqrtRatio; positivity)]
      exact R.sqrtRatio_le_right hv'

theorem logGap_nonneg : 0 ≤ R.logGap := by
  rw [← R.integrableOn_defect_and_integral.2]
  exact setIntegral_nonneg measurableSet_Ioi fun v hv =>
    R.defect_nonneg (le_of_lt hv)

end ResolventCompression

end Matrix

end
