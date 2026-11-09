import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field

/-!
# Hölder's inequality with three exponents `3, 3, 3`

Extends `Mathlib/Analysis/MeanInequalities.lean`: for nonnegative weights `w` and nonnegative
`X, Y, Z`, `∑ w X Y Z ≤ (∑ w X³)^{1/3} (∑ w Y³)^{1/3} (∑ w Z³)^{1/3}`, from the three-term
AM–GM inequality `x y z ≤ (x³ + y³ + z³)/3` after normalizing each factor.
-/

namespace Real

/-- `x y z ≤ (x³ + y³ + z³)/3` for `x, y, z ≥ 0`. -/
theorem mul_mul_le_add_pow_three_div {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ (x ^ 3 + y ^ 3 + z ^ 3) / 3 := by
  nlinarith [mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
    (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z))) (sq_nonneg (z - x)))]

theorem rpow_one_third_pow_three {A : ℝ} (hA : 0 ≤ A) : (A ^ (1 / 3 : ℝ)) ^ 3 = A := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
  norm_num

/-- **Hölder's inequality** with exponents `3, 3, 3` for weighted finite sums. -/
theorem sum_mul_mul_le_rpow_one_third {ι : Type*} (s : Finset ι) {w X Y Z : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hX : ∀ i ∈ s, 0 ≤ X i) (hY : ∀ i ∈ s, 0 ≤ Y i)
    (hZ : ∀ i ∈ s, 0 ≤ Z i) (hA : 0 < ∑ i ∈ s, w i * X i ^ 3) (hB : 0 < ∑ i ∈ s, w i * Y i ^ 3)
    (hC : 0 < ∑ i ∈ s, w i * Z i ^ 3) :
    ∑ i ∈ s, w i * (X i * Y i * Z i) ≤
      (∑ i ∈ s, w i * X i ^ 3) ^ (1 / 3 : ℝ) * (∑ i ∈ s, w i * Y i ^ 3) ^ (1 / 3 : ℝ) *
        (∑ i ∈ s, w i * Z i ^ 3) ^ (1 / 3 : ℝ) := by
  set A := ∑ i ∈ s, w i * X i ^ 3
  set B := ∑ i ∈ s, w i * Y i ^ 3
  set C := ∑ i ∈ s, w i * Z i ^ 3
  set a := A ^ (1 / 3 : ℝ)
  set b := B ^ (1 / 3 : ℝ)
  set c := C ^ (1 / 3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hA _
  have hb : 0 < b := Real.rpow_pos_of_pos hB _
  have hc : 0 < c := Real.rpow_pos_of_pos hC _
  have ha3 : a ^ 3 = A := rpow_one_third_pow_three hA.le
  have hb3 : b ^ 3 = B := rpow_one_third_pow_three hB.le
  have hc3 : c ^ 3 = C := rpow_one_third_pow_three hC.le
  have hterm : ∀ i ∈ s, w i * (X i * Y i * Z i) ≤
      a * b * c / 3 * (w i * X i ^ 3 / A + w i * Y i ^ 3 / B + w i * Z i ^ 3 / C) := by
    intro i hi
    have h := mul_mul_le_add_pow_three_div (div_nonneg (hX i hi) ha.le)
      (div_nonneg (hY i hi) hb.le) (div_nonneg (hZ i hi) hc.le)
    rw [div_pow, div_pow, div_pow, ha3, hb3, hc3] at h
    have e : X i * Y i * Z i = a * b * c * (X i / a * (Y i / b) * (Z i / c)) := by
      field_simp
    rw [e]
    calc w i * (a * b * c * (X i / a * (Y i / b) * (Z i / c))) ≤
          w i * (a * b * c * ((X i ^ 3 / A + Y i ^ 3 / B + Z i ^ 3 / C) / 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (hw i hi)
      _ = _ := by ring
  calc ∑ i ∈ s, w i * (X i * Y i * Z i) ≤ ∑ i ∈ s,
        a * b * c / 3 * (w i * X i ^ 3 / A + w i * Y i ^ 3 / B + w i * Z i ^ 3 / C) :=
        Finset.sum_le_sum hterm
    _ = a * b * c / 3 * (A / A + B / B + C / C) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
          ← Finset.sum_div, ← Finset.sum_div]
    _ = a * b * c := by
        rw [div_self hA.ne', div_self hB.ne', div_self hC.ne']
        ring

end Real
