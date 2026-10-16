/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Geometry.DyadicScales
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-!
# Uniform separation of the three dyadic scales

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/ScaleSeparation.lean` (Apache 2.0), proving the
scale-separation passage in [OAI265, §11].
-/

noncomputable section

namespace OpenAI.Geometry

/-- Above an explicit threshold, both rounded indices differ from the layer
index by any prescribed natural gap. -/
theorem dyadicScale_index_gaps (d k : ℕ) (hk : 10000000 * d ≤ k) :
    fineScaleIndex k + d ≤ k ∧ k + d ≤ pitchScaleIndex k := by
  have hd : d ≤ k := by omega
  have hk' : (10000000 : ℝ) * (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hf : fineScaleIndex k ≤ k - d := by
    unfold fineScaleIndex
    apply Nat.floor_le_of_le
    rw [Nat.cast_sub hd]
    norm_num [Exponents.zeta, Exponents.geometryDelta]
    linarith
  refine ⟨by omega, ?_⟩
  unfold pitchScaleIndex
  apply Nat.le_floor
  norm_num [Exponents.geometryDelta, Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) d]

/-- Any prescribed dyadic factor separates the fine, layer, and pitch sides
above the explicit index threshold. -/
theorem dyadicScale_side_ratios (d k : ℕ) (hk : 10000000 * d ≤ k) :
    (2 : ℕ) ^ d * 2 ^ fineScaleIndex k ≤ 2 ^ k ∧
      (2 : ℕ) ^ d * 2 ^ k ≤ 2 ^ pitchScaleIndex k := by
  obtain ⟨hf, hp⟩ := dyadicScale_index_gaps d k hk
  constructor
  · rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Every fixed real factor separates the fine, layer, and pitch sides above
one threshold independent of the domain and cut. -/
theorem exists_dyadicScale_side_ratios (M : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      M * (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ k ∧
        M * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ pitchScaleIndex k := by
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
  refine ⟨10000000 * d, ?_⟩
  intro k hk
  have h := dyadicScale_side_ratios d k hk
  have h' : (2 : ℝ) ^ d * (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ d * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ pitchScaleIndex k := by
    exact_mod_cast h
  constructor
  · exact (mul_le_mul_of_nonneg_right hd.le (pow_nonneg (by norm_num) _)).trans h'.1
  · exact (mul_le_mul_of_nonneg_right hd.le (pow_nonneg (by norm_num) _)).trans h'.2

end OpenAI.Geometry
