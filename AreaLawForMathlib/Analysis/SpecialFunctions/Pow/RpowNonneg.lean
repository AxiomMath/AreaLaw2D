import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Nonnegativity of small real powers of arbitrary reals

For `x < 0`, Mathlib's `x ^ y = e^{y log |x|} cos(yπ)`, which is nonnegative for `|y| ≤ 1/2`.
-/

namespace Real

/-- For `0 ≤ y ≤ 1/2`, `0 ≤ x ^ y` for every real `x`. -/
theorem rpow_nonneg_of_le_half (x : ℝ) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) : 0 ≤ x ^ y := by
  rcases le_or_gt 0 x with hx | hx
  · exact Real.rpow_nonneg hx _
  · rw [Real.rpow_def_of_neg hx]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩) <;>
      nlinarith [Real.pi_pos]

end Real
