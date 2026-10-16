/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewPhase.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
phase-rate estimate portion.
-/
import OpenAI.ConditionalSkewPhaseComparison

/-! # Scalar phase-rate estimate for the conditional skew bound -/

noncomputable section

namespace Entropy.ConditionalSkew

theorem neg_mul_log_le_two_sqrt {η : ℝ} (hη : 0 < η) :
    -(η * Real.log η) ≤ 2 * √η := by
  have hs : 0 < √η := Real.sqrt_pos.2 hη
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at h1
  have h2 : Real.log η = 2 * Real.log √η := by
    rw [Real.log_sqrt hη.le]
    ring
  have h4 : -Real.log √η ≤ (√η)⁻¹ := by linarith
  rw [h2]
  calc
    -(η * (2 * Real.log √η)) = 2 * η * (-Real.log √η) := by ring
    _ ≤ 2 * η * (√η)⁻¹ := by gcongr
    _ = 2 * √η := by rw [mul_assoc, ← div_eq_mul_inv, Real.div_sqrt]

theorem one_le_log_exp_mul {D : ℝ} (hD : 1 ≤ D) :
    1 ≤ Real.log (Real.exp 1 * D) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hD]

/-- For `1 ≤ D`, `log (eD) ≤ ℓ`, and `η ≤ 2ℓ`, the marginal phase rate is at most
`3ℓ (min 1 η)^(1/4)`. -/
theorem phaseRate_le {D ℓ η : ℝ} (hD : 1 ≤ D)
    (hDℓ : Real.log (Real.exp 1 * D) ≤ ℓ) (hη : η ≤ 2 * ℓ) :
    Matrix.phaseRate D η ≤ 3 * ℓ * √√(min 1 η) := by
  have hL := one_le_log_exp_mul hD
  have hℓ : 1 ≤ ℓ := hL.trans hDℓ
  have heD : 0 < Real.exp 1 * D := by positivity
  unfold Matrix.phaseRate
  split_ifs with h0
  · by_cases h1 : η ≤ 1
    · rw [min_eq_right h1]
      have hsη : √η ≤ 1 := Real.sqrt_le_one.mpr h1
      have hηs : η ≤ √η := by
        calc
          η = √η * √η := (Real.mul_self_sqrt h0.le).symm
          _ ≤ 1 * √η := by gcongr
          _ = √η := one_mul _
      have hss : √η ≤ √√η := by
        have h4 : √√η ≤ 1 := Real.sqrt_le_one.mpr hsη
        calc
          √η = √√η * √√η :=
            (Real.mul_self_sqrt (Real.sqrt_nonneg η)).symm
          _ ≤ 1 * √√η := by gcongr
          _ = √√η := one_mul _
      have hlog : η * Real.log (Real.exp 1 * D / η) ≤ 3 * ℓ * √η := by
        rw [Real.log_div heD.ne' h0.ne', mul_sub]
        have := neg_mul_log_le_two_sqrt h0
        have : η * Real.log (Real.exp 1 * D) ≤ ℓ * √η := by
          calc
            η * Real.log (Real.exp 1 * D) ≤ √η * ℓ :=
              mul_le_mul hηs hDℓ (by linarith) (Real.sqrt_nonneg _)
            _ = ℓ * √η := mul_comm _ _
        nlinarith [Real.sqrt_nonneg η]
      have h3 : √(η * Real.log (Real.exp 1 * D / η)) ≤
          2 * ℓ * √√η := by
        calc
          √(η * Real.log (Real.exp 1 * D / η)) ≤ √(3 * ℓ * √η) :=
            Real.sqrt_le_sqrt hlog
          _ = √(3 * ℓ) * √√η := Real.sqrt_mul (by linarith) _
          _ ≤ 2 * ℓ * √√η := by
            gcongr
            rw [Real.sqrt_le_left (by linarith)]
            nlinarith
      nlinarith [Real.sqrt_nonneg √η]
    · push Not at h1
      rw [min_eq_left h1.le, div_one, Real.sqrt_one, Real.sqrt_one, mul_one]
      have h3 : √(η * Real.log (Real.exp 1 * D)) ≤ 3 / 2 * ℓ := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      linarith
  · positivity

theorem phaseRate_nonneg (D η : ℝ) : 0 ≤ Matrix.phaseRate D η := by
  unfold Matrix.phaseRate
  split_ifs <;> positivity

theorem sqrt_sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    √√√x = x ^ (1 / 8 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx, ← Real.rpow_mul hx]
  norm_num

end Entropy.ConditionalSkew
