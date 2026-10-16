import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Subtracting the sharp comparisons

The scalar step of the proof of Proposition 9.6 [OAI265, lines 879–895]: the sharp lower
comparison of Proposition 8.1 bounds `-log N² / k` from below by `(a/2)` times a sum over the
`K` bands, the sharp upper comparison bounds the same quantity from above, and dividing their
difference by `2 s W = a K / 2` bounds `2 S' + ⟨g_pre - g_post⟩` by the band average of the
error terms.  The band averages enter as the weighted sums `f g = ∑_j w_j g_pre(j, g)` and
`p g = ∑_j w_j g_post(j, g)`.
-/

open scoped BigOperators

namespace OpenAI.Scan

/-- **The subtracted sharp comparison** at one replica count [OAI265, eqs. (8.10), (8.11)
and (9.19)]: if `F` lies between the sharp lower bound, with entropy-gap averages `f`, and the
sharp upper bound, with averages `p`, then `2 S' + K⁻¹ ∑_g (f g - p g)` is at most
`τ K⁻¹ ∑_g f g + 2 τ log d + (3 + 1/a) h + 37 K_mom a + E_def M / τ + r +
2 (aK)⁻¹ (2 log d - log z + r') - (log z) / a`. -/
theorem two_mul_add_inv_mul_sum_sub_le_of_sharp_comparisons {K : ℕ} (hK : 0 < K)
    {a τ Sent logd logz h Kmom Edef M rem rem' F : ℝ} (ha : 0 < a) (f p : Fin K → ℝ)
    (hlow : (a / 2) * (∑ g, (2 * Sent + (1 - τ) * f g - τ * (2 * logd) - (3 + 1 / a) * h -
        25 * Kmom * a - Edef / τ * M - rem)) ≤ F)
    (hup : F ≤ 2 * logd - logz + (a / 2) * (∑ g, p g) + 6 * (K : ℝ) * Kmom * a ^ 2 -
        (K : ℝ) / 2 * logz + rem') :
    2 * Sent + (K : ℝ)⁻¹ * ∑ g, (f g - p g) ≤
      τ * ((K : ℝ)⁻¹ * ∑ g, f g) + 2 * τ * logd + (3 + 1 / a) * h + 37 * Kmom * a +
        Edef / τ * M + rem + 2 / (a * K) * (2 * logd - logz + rem') - logz / a := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum : ∑ g, (2 * Sent + (1 - τ) * f g - τ * (2 * logd) - (3 + 1 / a) * h -
      25 * Kmom * a - Edef / τ * M - rem) =
      (K : ℝ) * (2 * Sent - τ * (2 * logd) - (3 + 1 / a) * h - 25 * Kmom * a -
        Edef / τ * M - rem) + (1 - τ) * ∑ g, f g := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hsum] at hlow
  rw [Finset.sum_sub_distrib]
  have hkey :
      (τ * ((K : ℝ)⁻¹ * ∑ g, f g) + 2 * τ * logd + (3 + 1 / a) * h + 37 * Kmom * a +
        Edef / τ * M + rem + 2 / (a * K) * (2 * logd - logz + rem') - logz / a) -
      (2 * Sent + (K : ℝ)⁻¹ * ((∑ g, f g) - ∑ g, p g)) =
      2 / (a * K) *
        ((2 * logd - logz + (a / 2) * (∑ g, p g) + 6 * (K : ℝ) * Kmom * a ^ 2 -
          (K : ℝ) / 2 * logz + rem') -
        (a / 2) * ((K : ℝ) * (2 * Sent - τ * (2 * logd) - (3 + 1 / a) * h -
          25 * Kmom * a - Edef / τ * M - rem) + (1 - τ) * ∑ g, f g)) := by
    field_simp
    ring
  have hnn : 0 ≤ 2 / (a * K) *
        ((2 * logd - logz + (a / 2) * (∑ g, p g) + 6 * (K : ℝ) * Kmom * a ^ 2 -
          (K : ℝ) / 2 * logz + rem') -
        (a / 2) * ((K : ℝ) * (2 * Sent - τ * (2 * logd) - (3 + 1 / a) * h -
          25 * Kmom * a - Edef / τ * M - rem) + (1 - τ) * ∑ g, f g)) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

end OpenAI.Scan
