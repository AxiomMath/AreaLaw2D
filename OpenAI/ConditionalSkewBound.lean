/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewPhase.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
final conditional-skew estimate portion.
-/
import OpenAI.ConditionalSkewRate
import OpenAI.SkewFromPhases

/-! # The conditional skew estimate -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open Matrix Entropy.MarginalPhase

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U]
  [DecidableEq F] in
theorem trace_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    (rhoW θ).trace = star θ ⬝ᵥ θ := by
  rw [← traceRight_thetaR, traceRight_trace, trace_vecMulVec, dotProduct_comm]
  change (star θ ∘ reindexE.symm) ⬝ᵥ (θ ∘ reindexE.symm) = _
  rw [dotProduct_comp_equiv_symm]
  congr 1

/-- The universal constant in the conditional skew estimate. -/
def skewConst : ℝ :=
  18 * Real.pi ^ 2 + 6144 * Real.exp (Real.pi ^ 2 + 1)

set_option maxHeartbeats 800000 in
-- The final estimate combines several nonlinear rate inequalities in one kernel proof.
/-- Conditional skew estimate, Lemma 5.3 of the area-law manuscript. -/
theorem conditionalSkew_le
    {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1)
    {h : Matrix (P₀ × X) (P₀ × X) ℂ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * Fintype.card (P₀ × X)) ≤ 1 / 8) :
    ‖skewFun θ h ((a / 2 : ℝ) : ℂ)‖ -
        (skewFun θ h ((a / 2 : ℝ) : ℂ)).re ≤
      skewConst * a ^ 2 *
        Real.log (Real.exp 1 * Fintype.card (P₀ × X)) ^ 4 *
          skewEta θ ^ (1 / 8 : ℝ) := by
  have hne : Nonempty ((P₀ × P₁) × ((X × U) × F)) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp [dotProduct] at hθ
  obtain ⟨⟨⟨p0, _⟩, ⟨⟨x0, _⟩, _⟩⟩⟩ := hne
  set d : ℝ := (Fintype.card (P₀ × X) : ℝ) with hd
  set ℓ := Real.log (Real.exp 1 * d) with hℓdef
  set η := skewEta θ with hηdef
  set R := Matrix.phaseRate (Fintype.card X) η with hRdef
  have hP0 : (1 : ℝ) ≤ Fintype.card P₀ := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨p0⟩
  have hX1 : (1 : ℝ) ≤ Fintype.card X := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x0⟩
  have hXd : (Fintype.card X : ℝ) ≤ d := by
    rw [hd, Fintype.card_prod, Nat.cast_mul]
    nlinarith
  have hd1 : 1 ≤ d := hX1.trans hXd
  have hℓ1 : 1 ≤ ℓ := one_le_log_exp_mul hd1
  have hlogX : Real.log (Real.exp 1 * Fintype.card X) ≤ ℓ :=
    Real.log_le_log (by positivity) (by gcongr)
  have hlogd : Real.log d ≤ ℓ := by
    rw [hℓdef, Real.log_mul (Real.exp_pos 1).ne' (by linarith),
      Real.log_exp]
    linarith
  have hη0 : 0 ≤ η := condMutualInfo_nonneg _
  have hη2 : η ≤ 2 * ℓ := by
    have hbound := condMutualInfo_le_two_log (posSemidef_rhoW θ)
      (by rw [trace_rhoW, hθ])
    have h2 : Real.log (Fintype.card X) ≤ Real.log d :=
      Real.log_le_log (by linarith) hXd
    change η ≤ _ at hbound
    linarith
  have hR := phaseRate_le hX1 hlogX hη2
  have hR0 : 0 ≤ R := phaseRate_nonneg _ _
  have hf0 := skewFun_zero_nonneg θ h hh0
  rw [Complex.nonneg_iff] at hf0
  have hherm : h.IsHermitian := (nonneg_iff_posSemidef.1 hh0).1
  have main := OpenAI.norm_sub_re_le_of_phase_bounds (f := skewFun θ h)
    (differentiable_skewFun θ h) (m := d ^ 2) (ℓ := ℓ) (R := R)
    (p := (skewFun θ h 0).re) (one_le_pow₀ hd1) hℓ1
    (by rw [Real.log_pow]; push_cast; linarith) hR0 hf0.1
    (Complex.ext rfl (by simpa using hf0.2.symm))
    (skewFun_neg_conj θ h hherm)
    (norm_skewFun_imag_le θ h hθ hh0 hh1)
    (fun z hz => norm_skewFun_le_of_strip θ hθ hh0 hh1
      (hz.trans (by norm_num)))
    (norm_skewFun_imag_sub_le hθ hh0 hh1) (t := a / 2)
    (by
      rw [abs_of_pos (by positivity), le_div_iff₀ (by positivity)]
      nlinarith)
  refine main.trans ?_
  set μ := min 1 η with hμ
  have hμ0 : 0 ≤ μ := le_min zero_le_one hη0
  have hμ1 : μ ≤ 1 := min_le_left _ _
  set q := √√μ
  set r := √q
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q ≤ 1 := Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hμ1)
  have hqr : q ≤ r := by
    have h4 : r ≤ 1 := Real.sqrt_le_one.mpr hq1
    calc
      q = r * r := (Real.mul_self_sqrt hq0).symm
      _ ≤ 1 * r := by gcongr
      _ = r := one_mul _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrη : r ≤ η ^ (1 / 8 : ℝ) := by
    rw [show r = √√√μ from rfl, sqrt_sqrt_sqrt_eq_rpow hμ0]
    exact Real.rpow_le_rpow hμ0 (min_le_right _ _) (by norm_num)
  have hR2 : R ^ 2 ≤ 9 * ℓ ^ 2 * r := by
    have hsqR : R ^ 2 ≤ (3 * ℓ * q) ^ 2 :=
      pow_le_pow_left₀ hR0 hR 2
    have hq2 : q ^ 2 ≤ r := by nlinarith
    nlinarith
  have hsq : √(min 1 R) ≤ 2 * ℓ * r := by
    calc
      √(min 1 R) ≤ √(3 * ℓ * q) :=
        Real.sqrt_le_sqrt ((min_le_right _ _).trans hR)
      _ = √(3 * ℓ) * r := Real.sqrt_mul (by linarith) _
      _ ≤ 2 * ℓ * r := by
        gcongr
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
  have hE : 0 ≤ Real.exp (Real.pi ^ 2 + 1) := (Real.exp_pos _).le
  have hℓ2 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hℓ3 : ℓ ^ 3 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hη8 : 0 ≤ η ^ (1 / 8 : ℝ) := Real.rpow_nonneg hη0 _
  have hπ : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  have hA : 8 * Real.pi ^ 2 * R ^ 2 ≤
      72 * Real.pi ^ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hR2
      (by positivity : (0 : ℝ) ≤ 8 * Real.pi ^ 2)
    have h9 : 9 * ℓ ^ 2 * r ≤
        9 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
      gcongr
    nlinarith
  have hB : 12288 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 2 *
      √(min 1 R) ≤
      24576 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 4 *
        η ^ (1 / 8 : ℝ) := by
    have h1 : ℓ ^ 2 * √(min 1 R) ≤
        2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
      calc
        ℓ ^ 2 * √(min 1 R) ≤ ℓ ^ 2 * (2 * ℓ * r) := by gcongr
        _ = 2 * ℓ ^ 3 * r := by ring
        _ ≤ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by gcongr
    calc
      12288 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 2 * √(min 1 R) =
          12288 * Real.exp (Real.pi ^ 2 + 1) *
            (ℓ ^ 2 * √(min 1 R)) := by ring
      _ ≤ 12288 * Real.exp (Real.pi ^ 2 + 1) *
          (2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  calc
    (a / 2) ^ 2 *
        (8 * Real.pi ^ 2 * R ^ 2 +
          12288 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 2 *
            √(min 1 R)) ≤
      (a / 2) ^ 2 *
        (72 * Real.pi ^ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) +
          24576 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 4 *
            η ^ (1 / 8 : ℝ)) := by gcongr
    _ = skewConst * a ^ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
      rw [skewConst]
      ring

end Entropy.ConditionalSkew
