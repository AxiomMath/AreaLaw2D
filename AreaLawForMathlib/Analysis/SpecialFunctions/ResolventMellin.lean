import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Mellin transform of a resolvent

Extends `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`, where the Beta integral and the
reflection formula `Complex.Gamma_mul_Gamma_one_sub` are proved.

For `x > 0` and `-1 < re z < 0`,
`∫ v in Ioi 0, v ^ z / (x + v) = -(π / sin (π z)) * x ^ z`.
The substitution `v = x t / (1 - t)` turns the integral into `x ^ z B(z + 1, -z)`, and
`B(z + 1, -z) = Γ(z + 1) Γ(-z) = -π / sin (π z)`. Summing over finitely many `x`, the same
identity represents `∑ c_k x_k ^ z` as a resolvent integral (the spectral form for a positive
definite matrix with eigenvalues `x_k`).

## Main results

* `Complex.integral_Ioi_cpow_div_add`: the resolvent Mellin integral.
* `Complex.integrableOn_Ioi_cpow_div_add`: its integrand is integrable on `Ioi 0`.
* `Complex.sum_mul_cpow_eq_integral`: the finite-sum (spectral) form.
-/

open MeasureTheory Set
open scoped Real

namespace Complex

/-- `sin (π z) ≠ 0` in the open strip `-1 < re z < 0`. -/
theorem sin_pi_mul_ne_zero_of_re_mem {z : ℂ} (h1 : -1 < z.re) (h0 : z.re < 0) :
    sin (π * z) ≠ 0 := by
  rw [Ne, sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  obtain rfl : z = k := mul_left_cancel₀ (ofReal_ne_zero.2 Real.pi_ne_zero) (by rw [hk]; ring)
  simp only [intCast_re] at h1 h0
  have : -1 < k := by exact_mod_cast h1
  have : k < 0 := by exact_mod_cast h0
  omega

/-- The image of `(0,1)` under `t ↦ x t / (1 - t)` is `(0,∞)`. -/
theorem image_Ioo_mul_div_one_sub {x : ℝ} (hx : 0 < x) :
    (fun t : ℝ => x * t / (1 - t)) '' Ioo 0 1 = Ioi 0 := by
  ext v
  simp only [mem_image, mem_Ioo, mem_Ioi]
  refine ⟨fun ⟨t, ⟨ht0, ht1⟩, h⟩ => h ▸ div_pos (mul_pos hx ht0) (by linarith), fun hv => ?_⟩
  refine ⟨v / (x + v), ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith)⟩, ?_⟩
  have : x + v ≠ 0 := by positivity
  field_simp
  rw [add_sub_cancel_right, div_self hx.ne']

/-- **Resolvent Mellin integral.** For `x > 0` and `-1 < re z < 0`,
`∫₀^∞ v ^ z / (x + v) dv = -(π / sin (π z)) x ^ z`. -/
theorem integral_Ioi_cpow_div_add {x : ℝ} (hx : 0 < x) {z : ℂ} (h1 : -1 < z.re)
    (h0 : z.re < 0) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ z / (x + v) = -(π / sin (π * z)) * (x : ℂ) ^ z := by
  set f : ℝ → ℝ := fun t => x * t / (1 - t)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (x / (1 - t) ^ 2) (Ioo 0 1) t := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2]
    refine ((((hasDerivAt_id t).const_mul x).div ((hasDerivAt_id t).const_sub 1) h1t).congr_deriv
      ?_).hasDerivWithinAt
    simp only [id]
    field_simp
    ring
  have hinj : InjOn f (Ioo 0 1) := by
    intro s hs t ht hst
    have : 1 - s ≠ 0 := by linarith [hs.2]
    have : 1 - t ≠ 0 := by linarith [ht.2]
    simp only [f] at hst
    field_simp at hst
    nlinarith
  rw [← image_Ioo_mul_div_one_sub hx, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj]
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, |x / (1 - t) ^ 2| • ((f t : ℂ) ^ z / (x + f t)) =
      (x : ℂ) ^ z * ((t : ℂ) ^ (z + 1 - 1) * (1 - (t : ℂ)) ^ (-z - 1)) := by
    intro t ⟨ht0, ht1⟩
    have h1t : 0 < 1 - t := by linarith
    have h1tC : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1t.ne'
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hcpow : (f t : ℂ) ^ z = (x : ℂ) ^ z * (t : ℂ) ^ z * ((1 - t : ℝ) : ℂ) ^ (-z) := by
      rw [show f t = x * t * (1 - t)⁻¹ by simp only [f]; ring, ofReal_mul,
        mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_mul,
        mul_cpow_ofReal_nonneg hx.le ht0.le, ofReal_inv,
        inv_cpow _ _ (by rw [arg_ofReal_of_nonneg h1t.le]; exact Real.pi_pos.ne), ← cpow_neg]
    have hden : (x : ℂ) + f t = x * ((1 - t : ℝ) : ℂ)⁻¹ := by
      simp only [f]
      push_cast at h1tC ⊢
      field_simp
      ring
    rw [abs_of_pos (by positivity), real_smul, hcpow, hden, add_sub_cancel_right,
      show 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring, cpow_sub _ _ h1tC, cpow_one]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hint, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hgamma := Gamma_mul_Gamma_eq_betaIntegral (s := z + 1) (t := -z) (by simp; linarith)
    (by simp; linarith)
  rw [show z + 1 + -z = 1 by ring, Gamma_one, one_mul] at hgamma
  have hrefl := Gamma_mul_Gamma_one_sub (-z)
  rw [show 1 - -z = z + 1 by ring, mul_comm, hgamma, mul_neg, sin_neg] at hrefl
  rw [← betaIntegral, hrefl]
  ring

/-- The resolvent Mellin integrand is integrable on `Ioi 0` in the open strip. -/
theorem integrableOn_Ioi_cpow_div_add {x : ℝ} (hx : 0 < x) {z : ℂ} (h1 : -1 < z.re)
    (h0 : z.re < 0) : IntegrableOn (fun v : ℝ => (v : ℂ) ^ z / (x + v)) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_Ioi_cpow_div_add hx h1 h0]
  exact mul_ne_zero (neg_ne_zero.2 (div_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
    (sin_pi_mul_ne_zero_of_re_mem h1 h0)))
    (by rw [Ne, cpow_eq_zero_iff]; exact fun h => (ofReal_ne_zero.2 hx.ne') h.1)

/-- **Spectral form.** For finitely many `x k > 0`, coefficients `c k` and `-1 < re z < 0`,
`∑ c_k x_k ^ z = -(sin (π z) / π) ∫₀^∞ v ^ z ∑ c_k / (x_k + v) dv`. Applied to the eigenvalues
of a positive definite matrix this is `A ^ z = -(sin π z / π) ∫₀^∞ v ^ z (A + v)⁻¹ dv`. -/
theorem sum_mul_cpow_eq_integral {ι : Type*} (s : Finset ι) {x : ι → ℝ}
    (hx : ∀ k ∈ s, 0 < x k) (c : ι → ℂ) {z : ℂ} (h1 : -1 < z.re) (h0 : z.re < 0) :
    ∑ k ∈ s, c k * (x k : ℂ) ^ z =
      -(sin (π * z) / π) * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ z * ∑ k ∈ s, c k / (x k + v) := by
  have hsin := sin_pi_mul_ne_zero_of_re_mem h1 h0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp_rw [Finset.mul_sum, mul_div_left_comm _ (c _)]
  rw [integral_finsetSum _ fun k hk => (integrableOn_Ioi_cpow_div_add (hx k hk) h1 h0).const_mul
    _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, integral_Ioi_cpow_div_add (hx k hk) h1 h0]
  field_simp

end Complex
