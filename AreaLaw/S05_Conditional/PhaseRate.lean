import AreaLaw.S05_Conditional.Defs

/-!
# §5.2 The scalar part of Lemma 5.2: the rate `∫ √(h/v) ≲ 𝓡_η`

Digest `digest/05-conditional.md` (D5.12.7, D5.12.8), paper `paper/sections/04-conditional.tex`
lines 310–479. A measurable `h ≥ 0` on `(0, ∞)` with `h(v) ≤ min(d², v⁻²)` and `∫ h = η`
(the resolvent defect of D5.13–D5.14) has `∫₀^∞ √(h(v)/v) dv ≤ 4 𝓡_η`, and the weighted
integrals `∫ v^s √(h/v)` (`-1/4 ≤ s < 0`) converge to it as `s ↑ 0`. No matrices.
-/

namespace AreaLaw

open MeasureTheory Set Filter Topology Real

namespace Conditional

variable {d : ℕ} {h : ℝ → ℝ} {v : ℝ}

/-- Near `0`: `h ≤ d²` gives `√(h/v) ≤ d v^{-1/2}`. -/
theorem sqrt_div_le_left (hv : 0 < v) (hh : h v ≤ (d : ℝ) ^ 2) :
    √(h v / v) ≤ d * v ^ (-(1 / 2 : ℝ)) := by
  calc √(h v / v) ≤ √((d : ℝ) ^ 2 / v) := sqrt_le_sqrt (by gcongr)
    _ = d * v ^ (-(1 / 2 : ℝ)) := by
      rw [sqrt_div' _ hv.le, sqrt_sq (Nat.cast_nonneg d), rpow_neg hv.le, ← sqrt_eq_rpow,
        div_eq_mul_inv]

/-- Near `∞`: `h ≤ v⁻²` gives `√(h/v) ≤ v^{-3/2}`. -/
theorem sqrt_div_le_right (hv : 0 < v) (hh : h v ≤ (v ^ 2)⁻¹) :
    √(h v / v) ≤ v ^ (-(3 / 2 : ℝ)) := by
  calc √(h v / v) ≤ √((v ^ 2)⁻¹ / v) := sqrt_le_sqrt (by gcongr)
    _ = v ^ (-(3 / 2 : ℝ)) := by
      rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_neg hv.le, div_eq_mul_inv, ← rpow_neg_one,
        ← rpow_add hv, ← rpow_mul hv.le]
      norm_num

variable (hint : IntegrableOn h (Ioi 0))
  (hh : ∀ v > 0, h v ≤ min ((d : ℝ) ^ 2) (v ^ 2)⁻¹)
include hint hh

/-- `v^s √(h/v)` is integrable on `(0,∞)` for `-1/2 < s < 1/2`: it is at most `d v^{s-1/2}` on
`(0,1]` and `v^{s-3/2}` on `(1,∞)`. -/
theorem integrableOn_rpow_mul_sqrt_div {s : ℝ} (hs1 : -(1 / 2) < s) (hs2 : s < 1 / 2) :
    IntegrableOn (fun v => v ^ s * √(h v / v)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun v => v ^ s * √(h v / v)) (volume.restrict (Ioi 0)) :=
    ((measurable_id.pow_const s).aemeasurable.mul
      (hint.aemeasurable.div measurable_id.aemeasurable).sqrt).aestronglyMeasurable
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hr : IntegrableOn (fun v : ℝ => d * v ^ (s - 1 / 2)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    refine hr.mono' (hm.mono_set Ioc_subset_Ioi_self) ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun v hv => ?_))
    rw [norm_of_nonneg (by have := hv.1; positivity), sub_eq_add_neg, rpow_add hv.1,
      mul_left_comm]
    exact mul_le_mul_of_nonneg_left (sqrt_div_le_left hv.1 ((hh v hv.1).trans (min_le_left _ _)))
      (by have := hv.1; positivity)
  · have hr : IntegrableOn (fun v : ℝ => v ^ (s - 3 / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine hr.mono' (hm.mono_set (Ioi_subset_Ioi zero_le_one))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 1 < v) => ?_))
    have hv0 : 0 < v := one_pos.trans hv
    rw [norm_of_nonneg (by positivity), sub_eq_add_neg, rpow_add hv0]
    exact mul_le_mul_of_nonneg_left (sqrt_div_le_right hv0 ((hh v hv0).trans (min_le_right _ _)))
      (by positivity)

/-- `√(h/v)` is integrable on `(0,∞)`. -/
theorem integrableOn_sqrt_div : IntegrableOn (fun v => √(h v / v)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_sqrt_div hint hh (s := 0) (by norm_num) (by norm_num)

end Conditional

open Conditional

/-- D5.12.7 (scalar part). For `-1/4 ≤ s < 0` the integral `∫₀^∞ v^s √(h/v) dv` is finite (the
integrand is majorised by `d v^{-3/4}` on `(0,1]` and `v^{-3/2}` on `[1,∞)`), and it tends to
`∫₀^∞ √(h/v) dv` as `s ↑ 0` by dominated convergence. -/
theorem step_5_12_7 {d : ℕ} {h : ℝ → ℝ} (hint : IntegrableOn h (Ioi 0))
    (hh : ∀ v > 0, h v ≤ min ((d : ℝ) ^ 2) (v ^ 2)⁻¹) :
    (∀ s ∈ Ico (-(1 / 4) : ℝ) 0, IntegrableOn (fun v => v ^ s * √(h v / v)) (Ioi 0)) ∧
      Tendsto (fun s : ℝ => ∫ v in Ioi 0, v ^ s * √(h v / v)) (𝓝[<] 0)
        (𝓝 (∫ v in Ioi 0, √(h v / v))) := by
  refine ⟨fun s hs => integrableOn_rpow_mul_sqrt_div hint hh (by linarith [hs.1])
    (by linarith [hs.2]), ?_⟩
  have hI := integrableOn_sqrt_div hint hh
  have hJ := integrableOn_rpow_mul_sqrt_div hint hh (s := -(1 / 4)) (by norm_num) (by norm_num)
  have hev : ∀ᶠ s in 𝓝[<] (0 : ℝ), s ∈ Ioo (-(1 / 4) : ℝ) 0 :=
    Ioo_mem_nhdsLT (by norm_num)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => √(h v / v) + v ^ (-(1 / 4) : ℝ) * √(h v / v)) ?_ ?_ (hI.add hJ) ?_
  · filter_upwards [hev] with s hs
    exact (integrableOn_rpow_mul_sqrt_div hint hh (by linarith [hs.1])
      (by linarith [hs.2])).aestronglyMeasurable
  · filter_upwards [hev] with s hs
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) => ?_)
    rw [norm_of_nonneg (by positivity)]
    have hle : v ^ s ≤ 1 + v ^ (-(1 / 4) : ℝ) := by
      rcases le_total v 1 with h1 | h1
      · linarith [rpow_le_rpow_of_exponent_ge hv h1 hs.1.le, rpow_pos_of_pos hv (-(1 / 4) : ℝ)]
      · linarith [rpow_le_one_of_one_le_of_nonpos h1 hs.2.le, rpow_pos_of_pos hv (-(1 / 4) : ℝ)]
    nlinarith [sqrt_nonneg (h v / v)]
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) => ?_)
    simpa using ((continuousAt_const_rpow hv.ne' (b := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio 0))).mul_const (√(h v / v))

/-- D5.12.8. Let `1 ≤ d`, `h ≥ 0` integrable on `(0,∞)` with `h(v) ≤ min(d², v⁻²)` and
`∫₀^∞ h = η`. Then `√(h/v)` is integrable and `∫₀^∞ √(h(v)/v) dv ≤ 4 𝓡_η`. For `η > 0`, with
`y = min(1, η)`, split at `y/d² ≤ 1/y`: the two ends give `2√y` each, the middle
`√(2η log(d²/y²)/2) ≤ √(2 η log(e d / y))` by Cauchy–Schwarz (in the form
`√(h v⁻¹) ≤ (t h + v⁻¹/t)/2`, optimised in `t`). For `η = 0`, `h = 0` a.e. -/
theorem step_5_12_8 {d : ℕ} (hd : 1 ≤ d) {η : ℝ} {h : ℝ → ℝ} (hint : IntegrableOn h (Ioi 0))
    (hh0 : ∀ v > 0, 0 ≤ h v) (hh : ∀ v > 0, h v ≤ min ((d : ℝ) ^ 2) (v ^ 2)⁻¹)
    (hη : ∫ v in Ioi 0, h v = η) :
    IntegrableOn (fun v => √(h v / v)) (Ioi 0) ∧ ∫ v in Ioi 0, √(h v / v) ≤ 4 * 𝓡 d η := by
  have hI := integrableOn_sqrt_div hint hh
  refine ⟨hI, ?_⟩
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] h :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hh0)
  rcases (hη ▸ setIntegral_nonneg measurableSet_Ioi hh0 : 0 ≤ η).lt_or_eq with hηp | rfl
  swap
  · -- D5.12.9: `η = 0` forces `h = 0` a.e.
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hη
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by filter_upwards [hae] with v hv; simp [hv]),
      integral_zero, 𝓡, if_neg (lt_irrefl 0), mul_zero]
  set y := min 1 η
  have hy0 : 0 < y := lt_min one_pos hηp
  have hy1 : y ≤ 1 := min_le_left _ _
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set a := y / (d : ℝ) ^ 2
  set b := 1 / y
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hab : a ≤ b := by
    rw [div_le_div_iff₀ (by positivity) hy0]
    nlinarith [mul_le_mul hy1 hy1 hy0.le zero_le_one]
  have h1 : Ioi (0 : ℝ) = Ioc 0 a ∪ (Ioc a b ∪ Ioi b) := by
    rw [Ioc_union_Ioi_eq_Ioi hab, Ioc_union_Ioi_eq_Ioi ha.le]
  have hsplit : ∫ v in Ioi 0, √(h v / v) = (∫ v in Ioc 0 a, √(h v / v)) +
      ((∫ v in Ioc a b, √(h v / v)) + ∫ v in Ioi b, √(h v / v)) := by
    rw [h1] at hI ⊢
    rw [setIntegral_union (t := Ioc a b ∪ Ioi b)
        (by rw [Ioc_union_Ioi_eq_Ioi hab]; exact Ioc_disjoint_Ioi_same)
        (measurableSet_Ioc.union measurableSet_Ioi) (hI.mono_set subset_union_left)
        (hI.mono_set subset_union_right),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hI.mono_set (subset_union_left.trans subset_union_right))
        (hI.mono_set (subset_union_right.trans subset_union_right))]
  rw [h1] at hI
  -- D5.12.8, `(0, y/d²]`: `√(h/v) ≤ d v^{-1/2}`.
  have hleft : ∫ v in Ioc 0 a, √(h v / v) ≤ 2 * √y := by
    have hr : IntegrableOn (fun v : ℝ => d * v ^ (-(1 / 2 : ℝ))) (Ioc 0 a) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul _
    calc ∫ v in Ioc 0 a, √(h v / v) ≤ ∫ v in Ioc 0 a, d * v ^ (-(1 / 2 : ℝ)) :=
          setIntegral_mono_on (hI.mono_set subset_union_left) hr measurableSet_Ioc
            fun v hv => sqrt_div_le_left hv.1 ((hh v hv.1).trans (min_le_left _ _))
      _ = d * (2 * √a) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le ha.le,
          integral_rpow (Or.inl (by norm_num)), zero_rpow (by norm_num), sqrt_eq_rpow]
        norm_num
        exact Or.inl (by ring)
      _ = 2 * √y := by
        rw [sqrt_div' _ (by positivity), sqrt_sq (by positivity)]
        field_simp
  -- D5.12.8, `[1/y, ∞)`: `√(h/v) ≤ v^{-3/2}`.
  have hright : ∫ v in Ioi b, √(h v / v) ≤ 2 * √y := by
    calc ∫ v in Ioi b, √(h v / v) ≤ ∫ v in Ioi b, v ^ (-(3 / 2 : ℝ)) :=
          setIntegral_mono_on (hI.mono_set (subset_union_right.trans subset_union_right))
            (integrableOn_Ioi_rpow_of_lt (by norm_num) hb) measurableSet_Ioi fun v hv =>
            sqrt_div_le_right (hb.trans hv) ((hh v (hb.trans hv)).trans (min_le_right _ _))
      _ = 2 * √y := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) hb, show b = y⁻¹ from one_div y,
          inv_rpow hy0.le, ← rpow_neg hy0.le, sqrt_eq_rpow]
        norm_num
        ring
  -- D5.12.8, `[y/d², 1/y]`: Cauchy–Schwarz against `∫ h ≤ η` and `∫ dv/v = log(b/a)`.
  set L := 2 * log (exp 1 * d / y)
  have hlog1 : 1 ≤ exp 1 * d / y := by
    rw [le_div_iff₀ hy0, one_mul]
    nlinarith [add_one_le_exp (1 : ℝ)]
  have hL : 0 < L := by
    have : 1 < exp 1 * d / y := by
      rw [lt_div_iff₀ hy0]; nlinarith [add_one_lt_exp (one_ne_zero (α := ℝ))]
    have := log_pos this
    positivity
  have hmid : ∫ v in Ioc a b, √(h v / v) ≤ √(η * L) := by
    set t := √(L / η)
    have ht : 0 < t := sqrt_pos.2 (div_pos hL hηp)
    have hhint : IntegrableOn h (Ioc a b) := hint.mono_set fun v hv => ha.trans hv.1
    have hinv : IntegrableOn (fun v : ℝ => v⁻¹) (Ioc a b) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1
        (intervalIntegral.intervalIntegrable_inv (fun v hv => by
          rw [uIcc_of_le hab] at hv; exact (ha.trans_le hv.1).ne') continuousOn_id)
    calc ∫ v in Ioc a b, √(h v / v) ≤ ∫ v in Ioc a b, (t * h v + v⁻¹ / t) / 2 := by
          refine setIntegral_mono_on (hI.mono_set (subset_union_left.trans subset_union_right))
            (((hhint.const_mul t).add (hinv.div_const t)).div_const 2) measurableSet_Ioc
            fun v hv => ?_
          have hv0 : 0 < v := ha.trans hv.1
          have h2 := two_mul_le_add_sq (√(t * h v)) (√(v⁻¹ / t))
          rw [sq_sqrt (mul_nonneg ht.le (hh0 v hv0)), sq_sqrt (by positivity), mul_assoc,
            ← sqrt_mul (mul_nonneg ht.le (hh0 v hv0)),
            show t * h v * (v⁻¹ / t) = h v / v by field_simp] at h2
          linarith
      _ = (t * ∫ v in Ioc a b, h v) / 2 + (∫ v in Ioc a b, v⁻¹) / t / 2 := by
          rw [integral_div, integral_add (hhint.const_mul t) (hinv.div_const t),
            integral_const_mul, integral_div]
          ring
      _ ≤ (t * η) / 2 + L / t / 2 := by
          gcongr
          · exact hη ▸ setIntegral_mono_set hint hnn
              (Eventually.of_forall fun v hv => ha.trans hv.1)
          · rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb,
              show b / a = ((d : ℝ) / y) ^ 2 by simp only [a, b]; field_simp, log_pow]
            have : log (d / y) ≤ log (exp 1 * d / y) := log_le_log (by positivity) (by
              rw [mul_div_assoc]; nlinarith [add_one_le_exp (1 : ℝ), (by positivity : 0 < d / y)])
            push_cast
            linarith
      _ = √(η * L) := by
          have htt : t ^ 2 = L / η := sq_sqrt (div_nonneg hL.le hηp.le)
          rw [show η * L = (t * η) ^ 2 by rw [mul_pow, htt]; field_simp,
            sqrt_sq (by positivity)]
          field_simp
          rw [htt]
          field_simp
          ring
  have hR : 𝓡 d η = √y + √(η * log (exp 1 * d / y)) := by rw [𝓡, if_pos hηp]
  have hsq : √(η * L) ≤ 4 * √(η * log (exp 1 * d / y)) := by
    rw [show η * L = 2 * (η * log (exp 1 * d / y)) by ring, sqrt_mul zero_le_two]
    gcongr
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  rw [hsplit, hR]
  linarith

end AreaLaw
