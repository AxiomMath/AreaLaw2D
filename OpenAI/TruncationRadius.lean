/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/TruncationRadius.lean`. Apache 2.0.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The base truncation radius

The scalar radius choice used in Proposition 4.5 of OAI265.
-/

namespace OpenAI

/-- `K / 2 ≤ 2^K` for `K ≥ 0`. -/
theorem half_le_two_rpow {K : ℝ} (hK : 0 ≤ K) : K / 2 ≤ (2 : ℝ) ^ K := by
  rw [Real.rpow_def_of_pos two_pos]
  have h1 := Real.add_one_le_exp (Real.log 2 * K)
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  nlinarith

/-- Choice of a logarithmic-squared base radius for Proposition 4.5. -/
theorem exists_truncationConstant {B C₀ c g : ℝ} (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hc : 0 < c) (hg : 0 < g) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℝ, 2 ≤ n → ∀ s : ℝ, 0 ≤ s → s ≤ C₀ * n ^ 2 →
      B * s * Real.exp (-(c / 2 * ((⌈C₁ * Real.log n ^ 2⌉₊ : ℕ) : ℝ) ^ (1 / 2 : ℝ))) ≤
        min (n ^ (-1000 : ℝ)) (g / 4) := by
  set m := min 1 (g / 4)
  have hm : 0 < m := lt_min one_pos (by positivity)
  set K := 2 * (B * C₀) / m
  have hK : 0 ≤ K := by positivity
  set β := 1002 + K
  set C₁ := (β / (c / 2)) ^ 2
  have hβ : 0 < β := by positivity
  refine ⟨C₁, by positivity, fun n hn s hs hsn => ?_⟩
  have hn0 : 0 < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  set r₀ : ℕ := ⌈C₁ * Real.log n ^ 2⌉₊
  have hr : β / (c / 2) * Real.log n ≤ (r₀ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le ?_
    calc
      ((β / (c / 2) * Real.log n) ^ 2 : ℝ) = C₁ * Real.log n ^ 2 := by
        simp only [C₁]
        ring
      _ ≤ (r₀ : ℝ) := Nat.le_ceil _
  have hexp : Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤ n ^ (-β) := by
    rw [Real.rpow_def_of_pos hn0]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ c / 2)
    have heq : c / 2 * (β / (c / 2) * Real.log n) = β * Real.log n := by
      field_simp
    nlinarith
  have hbound : B * s * Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤
      B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := by
    have hsplit : n ^ (2 : ℝ) * n ^ (-β) = n ^ (-K) * n ^ (-1000 : ℝ) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      simp only [β]
      ring
    calc
      B * s * Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤
          B * (C₀ * n ^ 2) * n ^ (-β) := by gcongr
      _ = B * C₀ * (n ^ (2 : ℝ) * n ^ (-β)) := by rw [Real.rpow_two]; ring
      _ = B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := by rw [hsplit]; ring
  have hnK : n ^ (-K) ≤ (2 : ℝ) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos two_pos hn (by linarith)
  have h2K : B * C₀ * (2 : ℝ) ^ (-K) ≤ m := by
    have h1 : B * C₀ = m * (K / 2) := by
      simp only [K]
      field_simp
    have h2 : B * C₀ ≤ m * (2 : ℝ) ^ K := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left (half_le_two_rpow hK) hm.le
    rw [Real.rpow_neg two_pos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have hBnK : B * C₀ * n ^ (-K) ≤ m :=
    (mul_le_mul_of_nonneg_left hnK (by positivity)).trans h2K
  have hn1000 : n ^ (-1000 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hpos : 0 ≤ n ^ (-1000 : ℝ) := Real.rpow_nonneg hn0.le _
  refine le_min ?_ ?_
  · calc
      _ ≤ B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := hbound
      _ ≤ 1 * n ^ (-1000 : ℝ) := by
        gcongr
        exact hBnK.trans (min_le_left _ _)
      _ = n ^ (-1000 : ℝ) := one_mul _
  · calc
      _ ≤ B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := hbound
      _ ≤ (g / 4) * 1 := by
        gcongr
        exact hBnK.trans (min_le_right _ _)
      _ = g / 4 := mul_one _

end OpenAI
