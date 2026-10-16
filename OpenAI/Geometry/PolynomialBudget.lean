/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Polynomially weighted dyadic decay

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/PolynomialBudget.lean` (Apache 2.0), for
[OAI265, §11, `geometry:total-repairs`].  These are scalar series estimates;
they do not assert the still-open repair construction or count.
-/

open Filter Topology

namespace OpenAI.Geometry

/-- Every fixed real power of the layer index is eventually absorbed into
half of the fixed geometric decay exponent. -/
theorem exists_polynomial_dyadic_absorption (p : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ((k : ℝ) + 1) ^ p *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) ≤
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 4) := by
  let a : ℝ := (Exponents.geometryDelta : ℝ) * Real.log 2 / 4
  have ha : 0 < a := by
    have hδ : 0 < (Exponents.geometryDelta : ℝ) := by
      norm_num [Exponents.geometryDelta]
    exact div_pos (mul_pos hδ (Real.log_pos (by norm_num))) (by norm_num)
  have hshift : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun k : ℕ => ((k : ℝ) + 1) ^ p * Real.exp (-a * (k : ℝ)))
      atTop (𝓝 0) := by
    convert ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha).comp
      hshift).mul_const (Real.exp a) using 1
    · funext k
      simp only [Function.comp_apply]
      rw [mul_assoc, ← Real.exp_add,
        show -a * ((k : ℝ) + 1) + a = -a * (k : ℝ) by ring]
    · simp
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨K, fun k hk => ?_⟩
  have h := mul_le_mul_of_nonneg_right (hK k hk).le
    (Real.exp_nonneg (-a * (k : ℝ)))
  rw [Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num),
    Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num)]
  have hleft :
      Real.exp (Real.log 2 * (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) =
        Real.exp (-a * (k : ℝ)) * Real.exp (-a * (k : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  have hright :
      Real.exp (Real.log 2 * (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 4)) =
        Real.exp (-a * (k : ℝ)) := by
    congr 1
    dsimp [a]
    ring
  rw [hleft, hright]
  simpa only [mul_assoc, one_mul] using h

/-- The polynomially weighted sparse-belt decay is summable over natural
scales. -/
theorem summable_polynomial_dyadic_decay (p : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ p *
      (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) := by
  let q : ℝ := (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) / 4)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    norm_num [Exponents.geometryDelta]
  apply (summable_geometric_of_norm_lt_one hq).of_norm_bounded_eventually_nat
  obtain ⟨K, hK⟩ := exists_polynomial_dyadic_absorption p
  filter_upwards [Filter.eventually_ge_atTop K] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _))]
  have heq : q ^ k =
      (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [heq]
  exact hK k hk

/-- Every finite collection of scales has one strictly positive numerical
budget, depending only on the exponent and fixed geometry constants. -/
theorem exists_uniform_polynomial_dyadic_sum_bound (p : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ F : Finset ℕ,
      ∑ k ∈ F, ((k : ℝ) + 1) ^ p *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) ≤ B := by
  let w : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ p *
    (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)
  have hw : ∀ k, 0 ≤ w k := fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨1 + ∑' k, w k, ?_, fun F => ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg hw)
  · have hsum := (summable_polynomial_dyadic_decay p).sum_le_tsum F (fun k _ => hw k)
    exact hsum.trans (by linarith)

end OpenAI.Geometry
