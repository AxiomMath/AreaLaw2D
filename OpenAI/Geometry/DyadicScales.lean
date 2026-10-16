/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Geometry.Exponents
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic.Linarith

/-!
# Arithmetic of the fine-cell and belt scales

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/DyadicScales.lean` (Apache 2.0).  These are the
arithmetic ingredients of [OAI265, §11, `geometry:belt-count`].
-/

noncomputable section

namespace OpenAI.Geometry

/-- Exponent of the fine-cell side length at layer scale `k`. -/
def fineScaleIndex (k : ℕ) : ℕ := Nat.floor ((Exponents.zeta : ℝ) * (k : ℝ))

/-- Exponent of the belt-pitch side length at layer scale `k`. -/
def pitchScaleIndex (k : ℕ) : ℕ :=
  Nat.floor ((1 + (Exponents.geometryDelta : ℝ)) * (k : ℝ))

/-- The fine-cell exponent does not exceed the layer-cell exponent. -/
theorem fineScaleIndex_le (k : ℕ) : fineScaleIndex k ≤ k := by
  apply Nat.floor_le_of_le
  have hz : (Exponents.zeta : ℝ) ≤ 1 := by
    exact_mod_cast Exponents.geometry_gaps.2.1.le
  simpa using mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg k)

/-- The layer-cell exponent does not exceed the belt-pitch exponent. -/
theorem le_pitchScaleIndex (k : ℕ) : k ≤ pitchScaleIndex k := by
  apply Nat.le_floor
  have hδ : 0 ≤ (Exponents.geometryDelta : ℝ) := by
    norm_num [Exponents.geometryDelta]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Every fine-cell side length divides its layer-cell side length. -/
theorem fineScale_dvd_layerScale (k : ℕ) : 2 ^ fineScaleIndex k ∣ (2 : ℕ) ^ k :=
  pow_dvd_pow 2 (fineScaleIndex_le k)

/-- Every layer-cell side length divides its belt pitch. -/
theorem layerScale_dvd_pitchScale (k : ℕ) : (2 : ℕ) ^ k ∣ 2 ^ pitchScaleIndex k :=
  pow_dvd_pow 2 (le_pitchScaleIndex k)

/-- The rounded scale exponents give the sparse-belt decay exponent, with an
additive rounding loss of two. -/
theorem layerScale_exponent_le (k : ℕ) :
    2 * (k : ℝ) - (pitchScaleIndex k : ℝ) - (fineScaleIndex k : ℝ) ≤
      2 - (Exponents.geometryDelta : ℝ) * (k : ℝ) / 2 := by
  have hf := Nat.lt_floor_add_one ((Exponents.zeta : ℝ) * (k : ℝ))
  have hp := Nat.lt_floor_add_one ((1 + (Exponents.geometryDelta : ℝ)) * (k : ℝ))
  have hz : (Exponents.zeta : ℝ) = 1 - (Exponents.geometryDelta : ℝ) / 2 := by
    simp [Exponents.zeta]
  change (Exponents.zeta : ℝ) * (k : ℝ) < (fineScaleIndex k : ℝ) + 1 at hf
  change (1 + (Exponents.geometryDelta : ℝ)) * (k : ℝ) <
    (pitchScaleIndex k : ℝ) + 1 at hp
  rw [hz] at hf
  nlinarith

end OpenAI.Geometry
