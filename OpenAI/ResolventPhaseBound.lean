/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Analysis/ResolventPhaseBound.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
split-integral and phase-gap portion.
-/
import OpenAI.ResolventPhaseRate

/-! # A phase gap is controlled by its logarithmic compression gap -/

open MeasureTheory Set Filter Topology
open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

namespace ResolventCompression

variable (R : ResolventCompression n m)

/-- The split integral estimate for `sqrt(h(v)/v)`. -/
theorem integral_sqrtRatio_le {D : ℝ} (hD : 1 ≤ D)
    (hK : R.invQuadA ≤ D ^ 2) (hM : R.quadB ≤ 1)
    (hη : 0 < R.logGap) :
    ∫ v in Ioi (0 : ℝ), R.sqrtRatio v ≤
      4 * √(min 1 R.logGap) +
        √(2 * R.logGap * Real.log (Real.exp 1 * D / min 1 R.logGap)) := by
  set η := R.logGap
  set y := min 1 η
  have hy0 : 0 < y := lt_min one_pos hη
  have hy1 : y ≤ 1 := min_le_left _ _
  have hyη : y ≤ η := min_le_right _ _
  have hD0 : 0 < D := by linarith
  set a := y / D ^ 2
  set b := 1 / y
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hab : a ≤ b := by
    rw [div_le_div_iff₀ (by positivity) hy0]
    nlinarith [mul_le_mul hy1 hy1 hy0.le zero_le_one]
  have hint := R.integrableOn_sqrtRatio
  have h1 : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a :=
    (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have h2 : Ioi a = Ioc a b ∪ Ioi b :=
    (Ioc_union_Ioi_eq_Ioi hab).symm
  have hsplit : ∫ v in Ioi (0 : ℝ), R.sqrtRatio v =
      (∫ v in Ioc 0 a, R.sqrtRatio v) +
        (∫ v in Ioc a b, R.sqrtRatio v) +
          ∫ v in Ioi b, R.sqrtRatio v := by
    rw [h1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (h1 ▸ subset_union_left))
      (hint.mono_set (h1 ▸ subset_union_right)), h2,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (by
        rw [h1, h2]
        intro v hv
        exact Or.inr (Or.inl hv)))
      (hint.mono_set (by
        rw [h1, h2]
        intro v hv
        exact Or.inr (Or.inr hv))), add_assoc]
  have hleft : ∫ v in Ioc 0 a, R.sqrtRatio v ≤ 2 * √y := by
    have hr : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) / 2)) (Ioc 0 a) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    calc
      ∫ v in Ioc 0 a, R.sqrtRatio v
          ≤ ∫ v in Ioc 0 a, √R.invQuadA * v ^ (-(1 : ℝ) / 2) :=
        setIntegral_mono_on
          (hint.mono_set (h1 ▸ subset_union_left)) (hr.const_mul _)
          measurableSet_Ioc fun v hv => R.sqrtRatio_le_left hv.1
      _ = √R.invQuadA * (2 * a ^ ((1 : ℝ) / 2)) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le ha.le,
          integral_rpow (Or.inl (by norm_num)),
          Real.zero_rpow (by norm_num), sub_zero]
        congr 1
        rw [show -(1 : ℝ) / 2 + 1 = 1 / 2 by norm_num]
        ring
      _ ≤ D * (2 * (√y / D)) := by
        refine mul_le_mul ?_ ?_ (by positivity) hD0.le
        · calc
            √R.invQuadA ≤ √(D ^ 2) := Real.sqrt_le_sqrt hK
            _ = D := Real.sqrt_sq hD0.le
        · rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity),
            Real.sqrt_sq hD0.le]
      _ = 2 * √y := by field_simp
  have hright : ∫ v in Ioi b, R.sqrtRatio v ≤ 2 * √y := by
    have hr : IntegrableOn (fun v : ℝ => v ^ (-(3 : ℝ) / 2)) (Ioi b) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hb
    calc
      ∫ v in Ioi b, R.sqrtRatio v
          ≤ ∫ v in Ioi b, √R.quadB * v ^ (-(3 : ℝ) / 2) :=
        setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hb.le))
          (hr.const_mul _) measurableSet_Ioi fun v hv =>
            R.sqrtRatio_le_right (lt_trans hb hv)
      _ = √R.quadB * (2 * b ^ (-(1 : ℝ) / 2)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hb]
        norm_num
        left
        ring
      _ ≤ 1 * (2 * √y) := by
        refine mul_le_mul ?_ ?_ (by positivity) zero_le_one
        · calc
            √R.quadB ≤ √1 := Real.sqrt_le_sqrt hM
            _ = 1 := Real.sqrt_one
        · rw [show b = y⁻¹ by simp [b], Real.inv_rpow hy0.le,
            ← Real.rpow_neg hy0.le, Real.sqrt_eq_rpow]
          norm_num
      _ = 2 * √y := one_mul _
  set L := 2 * Real.log (Real.exp 1 * D / y)
  have hL : 0 < L := by
    have h : 1 < Real.exp 1 * D / y := by
      rw [lt_div_iff₀ hy0]
      nlinarith [Real.add_one_lt_exp (one_ne_zero), hy1]
    have h' := Real.log_pos h
    positivity
  have hlogab : Real.log (b / a) ≤ L := by
    have hba : b / a = (D / y) ^ 2 := by
      simp only [a, b]
      field_simp
    rw [hba, Real.log_pow]
    push_cast
    have h : Real.log (D / y) ≤
        Real.log (Real.exp 1 * D / y) :=
      Real.log_le_log (by positivity) (by
        rw [mul_div_assoc]
        nlinarith [Real.add_one_le_exp (1 : ℝ),
          (by positivity : 0 < D / y)])
    linarith
  have hmid : ∫ v in Ioc a b, R.sqrtRatio v ≤ √(η * L) := by
    set t := √(L / η)
    have ht : 0 < t := Real.sqrt_pos.2 (div_pos hL hη)
    have hhint : IntegrableOn R.defect (Ioc a b) :=
      R.integrableOn_defect_and_integral.1.mono_set
        (fun v hv => lt_trans ha hv.1)
    have hinv : IntegrableOn (fun v : ℝ => v⁻¹) (Ioc a b) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1
        (intervalIntegral.intervalIntegrable_inv (fun v hv => by
          rw [uIcc_of_le hab] at hv
          exact (lt_of_lt_of_le ha hv.1).ne') continuousOn_id)
    calc
      ∫ v in Ioc a b, R.sqrtRatio v
          ≤ ∫ v in Ioc a b, (t * R.defect v + v⁻¹ / t) / 2 := by
        refine setIntegral_mono_on
          (hint.mono_set (fun v hv => lt_trans ha hv.1))
          (((hhint.const_mul t).add (hinv.div_const t)).div_const 2)
          measurableSet_Ioc fun v hv => ?_
        have hv0 : 0 < v := lt_trans ha hv.1
        rw [sqrtRatio, div_eq_mul_inv]
        exact sqrt_mul_le_add (R.defect_nonneg hv0.le)
          (inv_nonneg.2 hv0.le) ht
      _ = (t * ∫ v in Ioc a b, R.defect v) / 2 +
          (∫ v in Ioc a b, v⁻¹) / t / 2 := by
        rw [integral_div,
          integral_add (hhint.const_mul t) (hinv.div_const t),
          integral_const_mul, integral_div]
        ring
      _ ≤ (t * η) / 2 + L / t / 2 := by
        gcongr
        · rw [show η = ∫ v in Ioi (0 : ℝ), R.defect v from
            R.integrableOn_defect_and_integral.2.symm]
          exact setIntegral_mono_set R.integrableOn_defect_and_integral.1
            ((ae_restrict_iff' measurableSet_Ioi).2
              (Eventually.of_forall fun v hv =>
                R.defect_nonneg (le_of_lt hv)))
            (Eventually.of_forall fun v hv => lt_trans ha hv.1)
        · rw [← intervalIntegral.integral_of_le hab,
            integral_inv_of_pos ha hb]
          exact hlogab
      _ = √(η * L) := by
        have hη' : η ≠ 0 := hη.ne'
        have htt : t * t = L / η :=
          Real.mul_self_sqrt (div_nonneg hL.le hη.le)
        have hsq : √(η * L) = t * η := by
          rw [show η * L = (t * η) ^ 2 by
            rw [mul_pow, sq, htt]
            field_simp]
          exact Real.sqrt_sq (by positivity)
        rw [hsq]
        field_simp
        have h3 : t ^ 2 * η = L := by
          rw [sq, htt]
          field_simp
        linarith
  rw [hsplit]
  have h : √(η * L) =
      √(2 * η * Real.log (Real.exp 1 * D / y)) := by
    congr 1
    simp only [L]
    ring
  linarith

theorem integral_sqrtRatio_eq_zero (hη : R.logGap = 0) :
    ∫ v in Ioi (0 : ℝ), R.sqrtRatio v = 0 := by
  have h0 : ∫ v in Ioi (0 : ℝ), R.defect v = 0 := by
    rw [R.integrableOn_defect_and_integral.2, hη]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] R.defect :=
    (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun v hv => R.defect_nonneg (le_of_lt hv))
  have hae :=
    (integral_eq_zero_iff_of_nonneg_ae hnn
      R.integrableOn_defect_and_integral.1).1 h0
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_, integral_zero]
  filter_upwards [hae] with v hv
  simp [sqrtRatio, hv]

theorem integral_sqrtRatio_le_phaseRate {D : ℝ} (hD : 1 ≤ D)
    (hK : R.invQuadA ≤ D ^ 2) (hM : R.quadB ≤ 1) :
    ∫ v in Ioi (0 : ℝ), R.sqrtRatio v ≤ 4 * phaseRate D R.logGap := by
  rcases R.logGap_nonneg.lt_or_eq with hη | hη
  · refine (R.integral_sqrtRatio_le hD hK hM hη).trans ?_
    simp only [phaseRate, hη, ↓reduceIte]
    rw [mul_add]
    have hy0 : 0 < min 1 R.logGap := lt_min one_pos hη
    have hlog : 0 ≤ R.logGap *
        Real.log (Real.exp 1 * D / min 1 R.logGap) := by
      refine mul_nonneg hη.le (Real.log_nonneg ?_)
      rw [le_div_iff₀ hy0, one_mul]
      calc
        min 1 R.logGap ≤ 1 := min_le_left _ _
        _ ≤ Real.exp 1 * 1 := by
          nlinarith [Real.add_one_le_exp (1 : ℝ)]
        _ ≤ Real.exp 1 * D := by gcongr
    have h : √(2 * R.logGap *
        Real.log (Real.exp 1 * D / min 1 R.logGap)) ≤
        4 * √(R.logGap *
          Real.log (Real.exp 1 * D / min 1 R.logGap)) := by
      rw [mul_assoc, Real.sqrt_mul (by norm_num)]
      gcongr
      calc
        √2 ≤ √16 := Real.sqrt_le_sqrt (by norm_num)
        _ = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    linarith
  · rw [R.integral_sqrtRatio_eq_zero hη.symm, ← hη]
    simp [phaseRate]

theorem norm_toLp_discrepancy_le {v : ℝ} (hv : 0 < v) :
    ‖(WithLp.toLp 2 (R.discrepancy v) : EuclideanSpace ℂ n)‖ ≤
      R.sqrtRatio v := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), sqrtRatio]
  refine Real.sqrt_le_sqrt ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
    le_div_iff₀ hv, mul_comm]
  exact R.mul_norm_discrepancy_sq_le hv.le

theorem phaseGap_zero : R.phaseGap 0 = 0 := by
  simp only [phaseGap, Complex.cpow_zero, spectralFun_one, one_mulVec,
    a0, sub_self]

/-- The phase gap is bounded by the integral of the square-root defect rate. -/
theorem norm_phaseGap_le_integral (u : ℝ) :
    ‖(WithLp.toLp 2 (R.phaseGap (-(u * Complex.I))) : EuclideanSpace ℂ n)‖ ≤
      |Real.sinh (Real.pi * u)| / Real.pi *
        ∫ v in Ioi (0 : ℝ), R.sqrtRatio v := by
  have hS : 0 ≤ ∫ v in Ioi (0 : ℝ), R.sqrtRatio v :=
    setIntegral_nonneg measurableSet_Ioi fun v _ => Real.sqrt_nonneg _
  rcases eq_or_ne u 0 with rfl | hu
  · simp only [Complex.ofReal_zero, zero_mul, neg_zero, R.phaseGap_zero]
    simp only [WithLp.toLp_zero, norm_zero]
    positivity
  set p := R.phaseGap (-(u * Complex.I))
  set P : EuclideanSpace ℂ n := WithLp.toLp 2 p
  have hrep := R.dotProduct_phaseGap_eq_integral p hu
  have hself : star p ⬝ᵥ p = ((‖P‖ : ℝ) : ℂ) ^ 2 := by
    have h1 : star p ⬝ᵥ p = inner ℂ P P := by
      rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [h1, inner_self_eq_norm_sq_to_K]
    rfl
  have hsin :
      ‖-(Complex.sin (Real.pi * (-(u * Complex.I))) / Real.pi)‖ =
        |Real.sinh (Real.pi * u)| / Real.pi := by
    rw [norm_neg, norm_div,
      show (Real.pi : ℂ) * (-(u * Complex.I)) =
        -(((Real.pi * u : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.sin_neg, norm_neg, Complex.sin_mul_I, norm_mul,
      Complex.norm_I, mul_one, ← Complex.ofReal_sinh, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hint := R.integrableOn_sqrtRatio
  have hbound :
      ‖∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (-(u * Complex.I)) *
            (star p ⬝ᵥ R.discrepancy v)‖ ≤
        ∫ v in Ioi (0 : ℝ), ‖P‖ * R.sqrtRatio v := by
    refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv']
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, neg_zero, Real.rpow_zero, one_mul]
    calc
      ‖star p ⬝ᵥ R.discrepancy v‖ =
          ‖inner ℂ P
            (WithLp.toLp 2 (R.discrepancy v) : EuclideanSpace ℂ n)‖ := by
        rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      _ ≤ ‖P‖ *
          ‖(WithLp.toLp 2 (R.discrepancy v) : EuclideanSpace ℂ n)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖P‖ * R.sqrtRatio v := by
        gcongr
        exact R.norm_toLp_discrepancy_le hv'
  have hmain : ‖P‖ ^ 2 ≤
      |Real.sinh (Real.pi * u)| / Real.pi *
        (‖P‖ * ∫ v in Ioi (0 : ℝ), R.sqrtRatio v) := by
    have h := congrArg norm hrep
    rw [hself, norm_mul, hsin, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    rw [h, ← integral_const_mul]
    gcongr
  rcases (norm_nonneg P).lt_or_eq with hP | hP
  · have h : ‖P‖ * ‖P‖ ≤
        ‖P‖ * (|Real.sinh (Real.pi * u)| / Real.pi *
          ∫ v in Ioi (0 : ℝ), R.sqrtRatio v) := by
      nlinarith
    exact le_of_mul_le_mul_left h hP
  · rw [← hP]
    have h : 0 ≤ |Real.sinh (Real.pi * u)| / Real.pi := by positivity
    positivity

/-- The explicit phase-gap bound controlled by the logarithmic gap. -/
theorem norm_phaseGap_le_phaseRate {D : ℝ} (hD : 1 ≤ D)
    (hK : R.invQuadA ≤ D ^ 2) (hM : R.quadB ≤ 1) (u : ℝ) :
    ‖(WithLp.toLp 2 (R.phaseGap (-(u * Complex.I))) : EuclideanSpace ℂ n)‖ ≤
      2 * |Real.sinh (Real.pi * u)| * phaseRate D R.logGap := by
  have hR : 0 ≤ phaseRate D R.logGap := by
    unfold phaseRate
    split_ifs <;> positivity
  refine (R.norm_phaseGap_le_integral u).trans ?_
  have hS := R.integral_sqrtRatio_le_phaseRate hD hK hM
  have hπ : 4 / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.two_le_pi]
  calc
    |Real.sinh (Real.pi * u)| / Real.pi *
          ∫ v in Ioi (0 : ℝ), R.sqrtRatio v
        ≤ |Real.sinh (Real.pi * u)| / Real.pi *
          (4 * phaseRate D R.logGap) := by gcongr
    _ = |Real.sinh (Real.pi * u)| * (4 / Real.pi) *
        phaseRate D R.logGap := by ring
    _ ≤ |Real.sinh (Real.pi * u)| * 2 * phaseRate D R.logGap := by
      gcongr
    _ = 2 * |Real.sinh (Real.pi * u)| * phaseRate D R.logGap := by
      ring

end ResolventCompression

end Matrix

end
