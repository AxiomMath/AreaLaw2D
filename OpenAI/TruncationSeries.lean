/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/TruncationSeries.lean`. Apache 2.0.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The volume-free truncation series

Scalar summability estimates used in the proof of Proposition 4.5 of OAI265.
-/

open scoped Nat

namespace OpenAI

/-- Stretched exponentials beat polynomials. -/
theorem exists_one_add_pow_mul_exp_neg_rpow_le {b α : ℝ} (hb : 0 < b) (hα : 0 < α)
    (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 ≤ u →
      (u + 1) ^ k * Real.exp (-(b * u ^ α)) ≤ M := by
  set m : ℕ := ⌈(k : ℝ) / α⌉₊
  have hm : (k : ℝ) ≤ α * m := by
    have := Nat.le_ceil ((k : ℝ) / α)
    rw [div_le_iff₀ hα] at this
    linarith
  refine ⟨2 ^ k * max 1 (m ! / b ^ m), by positivity, fun u hu => ?_⟩
  have he : 0 < Real.exp (-(b * u ^ α)) := Real.exp_pos _
  rcases le_total u 1 with h1 | h1
  · have : (u + 1) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have he1 : Real.exp (-(b * u ^ α)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := Real.rpow_nonneg hu α; nlinarith)
    calc
      (u + 1) ^ k * Real.exp (-(b * u ^ α)) ≤ 2 ^ k * 1 :=
        mul_le_mul this he1 he.le (by positivity)
      _ ≤ 2 ^ k * max 1 (m ! / b ^ m) := by gcongr; exact le_max_left _ _
  · have hu0 : 0 < u := by linarith
    have hy : 0 ≤ b * u ^ α := by positivity
    have hfac := Real.pow_div_factorial_le_exp _ hy m
    have hpow : (b * u ^ α) ^ m = b ^ m * u ^ (α * m) := by
      rw [mul_pow, ← Real.rpow_natCast (u ^ α), ← Real.rpow_mul hu]
    have huk : (u + 1) ^ k ≤ 2 ^ k * u ^ (α * m) := by
      calc
        (u + 1) ^ k ≤ (2 * u) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
        _ = 2 ^ k * u ^ (k : ℝ) := by rw [mul_pow, Real.rpow_natCast]
        _ ≤ 2 ^ k * u ^ (α * m) := by gcongr
    have hupos : 0 < u ^ (α * m) := Real.rpow_pos_of_pos hu0 _
    have hbm : 0 < b ^ m := pow_pos hb m
    have hexp : Real.exp (-(b * u ^ α)) ≤ m ! / (b ^ m * u ^ (α * m)) := by
      rw [Real.exp_neg, le_div_iff₀ (by positivity), ← hpow,
        inv_mul_le_iff₀ (Real.exp_pos _)]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < m !)] at hfac
      linarith
    calc
      (u + 1) ^ k * Real.exp (-(b * u ^ α)) ≤
          2 ^ k * u ^ (α * m) * (m ! / (b ^ m * u ^ (α * m))) :=
        mul_le_mul huk hexp he.le (by positivity)
      _ = 2 ^ k * (m ! / b ^ m) := by field_simp
      _ ≤ 2 ^ k * max 1 (m ! / b ^ m) := by gcongr; exact le_max_right _ _

/-- The volume-free shell-series estimate in the proof of Proposition 4.5. -/
theorem exists_sum_shell_le {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r₀ N : ℕ,
      ∑ d ∈ Finset.range N, ((d : ℝ) + 1) ^ 2 *
          Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) ≤
        A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by
  obtain ⟨M, hM, hMb⟩ := exists_one_add_pow_mul_exp_neg_rpow_le (half_pos hc) hα 4
  have hsum : Summable fun d : ℕ => 1 / ((d : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  set S := ∑' d : ℕ, 1 / ((d : ℝ) + 1) ^ 2
  have hS : 0 ≤ S :=
    tsum_nonneg fun d : ℕ => (by positivity : (0 : ℝ) ≤ 1 / ((d : ℝ) + 1) ^ 2)
  refine ⟨16 * M * S, by positivity, fun r₀ N => ?_⟩
  have hterm : ∀ d : ℕ,
      ((d : ℝ) + 1) ^ 2 * Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) ≤
        Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (16 * M * (1 / ((d : ℝ) + 1) ^ 2)) := by
    intro d
    set u : ℕ := d / 2
    have hmax : ((r₀ : ℝ) ^ α + (u : ℝ) ^ α) / 2 ≤
        ((max r₀ u : ℕ) : ℝ) ^ α := by
      have h1 : (r₀ : ℝ) ^ α ≤ ((max r₀ u : ℕ) : ℝ) ^ α :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast le_max_left _ _) hα.le
      have h2 : (u : ℝ) ^ α ≤ ((max r₀ u : ℕ) : ℝ) ^ α :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast le_max_right _ _) hα.le
      linarith
    have hexp : Real.exp (-(c * ((max r₀ u : ℕ) : ℝ) ^ α)) ≤
        Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          Real.exp (-(c / 2 * (u : ℝ) ^ α)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hdu : (d : ℝ) + 1 ≤ 2 * ((u : ℝ) + 1) := by
      have : d ≤ 2 * u + 1 := by omega
      have : (d : ℝ) ≤ 2 * u + 1 := by exact_mod_cast this
      linarith
    have hd0 : 0 < (d : ℝ) + 1 := by positivity
    have hpoly : ((d : ℝ) + 1) ^ 4 * Real.exp (-(c / 2 * (u : ℝ) ^ α)) ≤ 16 * M := by
      have h4 : ((d : ℝ) + 1) ^ 4 ≤ 16 * ((u : ℝ) + 1) ^ 4 := by
        calc
          ((d : ℝ) + 1) ^ 4 ≤ (2 * ((u : ℝ) + 1)) ^ 4 :=
            pow_le_pow_left₀ hd0.le hdu 4
          _ = 16 * ((u : ℝ) + 1) ^ 4 := by ring
      calc
        ((d : ℝ) + 1) ^ 4 * Real.exp (-(c / 2 * (u : ℝ) ^ α)) ≤
            16 * ((u : ℝ) + 1) ^ 4 * Real.exp (-(c / 2 * (u : ℝ) ^ α)) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ ≤ 16 * M := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hMb u (by positivity)) (by norm_num)
    have hE := Real.exp_pos (-(c / 2 * (r₀ : ℝ) ^ α))
    calc
      ((d : ℝ) + 1) ^ 2 * Real.exp (-(c * ((max r₀ u : ℕ) : ℝ) ^ α)) ≤
          ((d : ℝ) + 1) ^ 2 * (Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
            Real.exp (-(c / 2 * (u : ℝ) ^ α))) := by gcongr
      _ = Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (((d : ℝ) + 1) ^ 4 * Real.exp (-(c / 2 * (u : ℝ) ^ α)) /
            ((d : ℝ) + 1) ^ 2) := by field_simp
      _ ≤ Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (16 * M / ((d : ℝ) + 1) ^ 2) := by gcongr
      _ = Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (16 * M * (1 / ((d : ℝ) + 1) ^ 2)) := by ring
  calc
    ∑ d ∈ Finset.range N, ((d : ℝ) + 1) ^ 2 *
        Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) ≤
        ∑ d ∈ Finset.range N, Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (16 * M * (1 / ((d : ℝ) + 1) ^ 2)) :=
      Finset.sum_le_sum fun d _ => hterm d
    _ = Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) * (16 * M) *
        ∑ d ∈ Finset.range N, 1 / ((d : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) * (16 * M) * S := by
      gcongr
      exact hsum.sum_le_tsum _ fun d _ => by positivity
    _ = 16 * M * S * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by ring

end OpenAI
