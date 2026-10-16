/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewStrip.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.ConditionalSkewStripCore

/-! # The strip bound for the conditional skew function -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

variable (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)

theorem norm_skew_term_le (hθ : star θ ⬝ᵥ θ = 1)
    {c : Matrix (P₀ × P₁) (P₀ × P₁) ℂ}
    (hc₁ : c * cᴴ ≤ 1) (hc₂ : cᴴ * c ≤ 1)
    {d : Matrix (X × U) (X × U) ℂ} (hd₁ : d * dᴴ ≤ 1) (hd₂ : dᴴ * d ≤ 1)
    {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1 / 2) :
    ‖star θ ⬝ᵥ ((liftP (cfcC (margP θ) (suppPowFun z) * c *
      cfcC (margP θ) (suppPowFun (-z))) *
      liftY (cfcC (margY θ) (suppPowFun (-z)) * d *
        cfcC (margY θ) (suppPowFun z))) *ᵥ θ)‖ ≤ 1 := by
  have hP := posSemidef_margP θ
  have hY := posSemidef_margY θ
  have htrP : (margP θ).trace.re ≤ 1 := by rw [trace_margP, hθ, Complex.one_re]
  have htrY : (margY θ).trace.re ≤ 1 := by rw [trace_margY, hθ, Complex.one_re]
  rw [liftP_liftY_comm, ← mulVec_mulVec, star_dotProduct_mulVec_eq,
    conjTranspose_liftY]
  refine (norm_star_dotProduct_le _ _).trans ?_
  rw [← one_mul (1 : ℝ)]
  refine mul_le_mul (norm_toLp_le_one_of_re_le ?_) (norm_toLp_le_one_of_re_le ?_)
    (norm_nonneg _) zero_le_one
  · have hB : (cfcC (margY θ) (suppPowFun (-z)) * d *
        cfcC (margY θ) (suppPowFun z))ᴴ =
        cfcC (margY θ) (suppPowFun (starRingEnd ℂ z)) * dᴴ *
          cfcC (margY θ) (suppPowFun (-(starRingEnd ℂ z))) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_suppPow hY,
        conjTranspose_suppPow hY, map_neg, Matrix.mul_assoc]
    rw [normSq_liftY_mulVec, hB]
    have hd₁' : dᴴ * dᴴᴴ ≤ 1 := by rwa [conjTranspose_conjTranspose]
    have hd₂' : dᴴᴴ * dᴴ ≤ 1 := by rwa [conjTranspose_conjTranspose]
    have hle := re_trace_sandwich_mul_le hY htrY hd₁' hd₂'
      (z := starRingEnd ℂ z) (by simpa using hz₀) (by simpa using hz₁)
    simpa [Matrix.mul_assoc] using hle
  · rw [normSq_liftP_mulVec]
    exact re_trace_sandwich_mul_le hP htrP hc₁ hc₂ hz₀ hz₁

theorem unitP_contraction (a b : P₀) :
    unitP (P₁ := P₁) a b * (unitP a b)ᴴ ≤ 1 ∧
      (unitP (P₁ := P₁) a b)ᴴ * unitP a b ≤ 1 := by
  simp only [unitP, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul]
  refine ⟨kronecker_one_le_one (single_mul_conjTranspose_le_one a b), ?_⟩
  have h := single_mul_conjTranspose_le_one (n := P₀) b a
  rw [conjTranspose_single, star_one] at h ⊢
  exact kronecker_one_le_one h

theorem unitY_contraction (x x' : X) :
    unitY (U := U) x x' * (unitY x x')ᴴ ≤ 1 ∧
      (unitY (U := U) x x')ᴴ * unitY x x' ≤ 1 := by
  simp only [unitY, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul]
  refine ⟨kronecker_one_le_one (single_mul_conjTranspose_le_one x x'), ?_⟩
  have h := single_mul_conjTranspose_le_one (n := X) x' x
  rw [conjTranspose_single, star_one] at h ⊢
  exact kronecker_one_le_one h

theorem skewFun_eq_sum (h : Matrix (P₀ × X) (P₀ × X) ℂ) (z : ℂ) :
    skewFun θ h z = ∑ i, ∑ j, h i j * (star θ ⬝ᵥ
      ((liftP (cfcC (margP θ) (suppPowFun z) * unitP i.1 j.1 *
          cfcC (margP θ) (suppPowFun (-z))) *
        liftY (cfcC (margY θ) (suppPowFun (-z)) * unitY i.2 j.2 *
          cfcC (margY θ) (suppPowFun z))) *ᵥ θ)) := by
  rw [skewFun, liftH_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, sum_mulVec,
    smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul, lift_mul_rearrange]

theorem norm_skewFun_le_of_strip (hθ : star θ ⬝ᵥ θ = 1)
    {h : Matrix (P₀ × X) (P₀ × X) ℂ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖skewFun θ h z‖ ≤ (Fintype.card (P₀ × X) : ℝ) ^ 2 := by
  have hpos : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / 2 →
      ‖skewFun θ h w‖ ≤ (Fintype.card (P₀ × X) : ℝ) ^ 2 := by
    intro w hw0 hw1
    rw [skewFun_eq_sum]
    calc
      ‖∑ i, ∑ j, h i j * _‖ ≤ ∑ i : P₀ × X, ∑ j : P₀ × X, (1 : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, ← one_mul (1 : ℝ)]
        exact mul_le_mul (norm_apply_le_one_of_nonneg_le_one hh0 hh1 i j)
          (norm_skew_term_le θ hθ (unitP_contraction i.1 j.1).1
            (unitP_contraction i.1 j.1).2 (unitY_contraction i.2 j.2).1
            (unitY_contraction i.2 j.2).2 hw0 hw1)
          (norm_nonneg _) zero_le_one
      _ = (Fintype.card (P₀ × X) : ℝ) ^ 2 := by simp [sq]
  rcases le_total 0 z.re with h0 | h0
  · exact hpos z h0 ((le_abs_self _).trans hz)
  · have hH : h.IsHermitian := (nonneg_iff_posSemidef.1 hh0).1
    have h1 := skewFun_neg_conj θ h hH (-(starRingEnd ℂ z))
    rw [map_neg, Complex.conj_conj, neg_neg] at h1
    rw [h1, Complex.norm_conj]
    exact hpos _ (by simp; linarith) (by simp; linarith [neg_abs_le z.re])

end Entropy.ConditionalSkew

end
