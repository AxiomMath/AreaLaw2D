/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewSetup.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.ConditionalSkewSupport

/-! # Values and analyticity of the conditional skew function -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem star_mulVec_dotProduct {n m : Type*} [Fintype n] [Fintype m]
    (W : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star (W *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Wᴴ *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec]

theorem star_dotProduct_mulVec_eq {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (x y : n → ℂ) : star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

variable (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (h : Matrix (P₀ × X) (P₀ × X) ℂ)

theorem skewFun_zero : skewFun θ h 0 = star θ ⬝ᵥ (liftH h *ᵥ θ) := by
  have hP := posSemidef_margP θ
  have hY := posSemidef_margY θ
  rw [skewFun, neg_zero, ← mulVec_mulVec, liftY_supp_zero_mulVec, ← mulVec_mulVec,
    liftP_supp_zero_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, star_dotProduct_mulVec_eq,
    conjTranspose_liftP, conjTranspose_suppPow hP, map_zero, liftP_supp_zero_mulVec,
    star_dotProduct_mulVec_eq, conjTranspose_liftY, conjTranspose_suppPow hY, map_zero,
    liftY_supp_zero_mulVec]

theorem conj_ofReal_mul_I (y : ℝ) :
    starRingEnd ℂ ((y : ℂ) * Complex.I) = -((y : ℂ) * Complex.I) := by
  simp [Complex.conj_ofReal]

theorem skewFun_imag (y : ℝ) :
    skewFun θ h ((y : ℂ) * Complex.I) =
      star (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
          (liftY (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)) ⬝ᵥ
        (liftH h *ᵥ (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
          (liftY (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ))) := by
  have hP := posSemidef_margP θ
  have hY := posSemidef_margY θ
  rw [skewFun, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    star_dotProduct_mulVec_eq, star_dotProduct_mulVec_eq, conjTranspose_liftP,
    conjTranspose_suppPow hP, conj_ofReal_mul_I, conjTranspose_liftY,
    conjTranspose_suppPow hY, map_neg, conj_ofReal_mul_I, neg_neg, mulVec_mulVec,
    ← liftP_liftY_comm, ← mulVec_mulVec]

theorem dotProduct_star_imag_vector (y : ℝ) :
    star (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
        (liftY (P₀ := P₀) (P₁ := P₁) (F := F)
          (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)) ⬝ᵥ
      (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
        (liftY (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)) =
      star θ ⬝ᵥ θ := by
  have hP := posSemidef_margP θ
  have hY := posSemidef_margY θ
  rw [star_mulVec_dotProduct, conjTranspose_liftP, conjTranspose_suppPow hP, map_neg,
    conj_ofReal_mul_I, neg_neg, mulVec_mulVec, liftP_mul, suppPow_mul hP.1, add_neg_cancel,
    mulVec_mulVec, liftP_liftY_comm, ← mulVec_mulVec, liftP_supp_zero_mulVec,
    star_mulVec_dotProduct, conjTranspose_liftY, conjTranspose_suppPow hY,
    conj_ofReal_mul_I, mulVec_mulVec, liftY_mul, suppPow_mul hY.1, neg_add_cancel,
    liftY_supp_zero_mulVec]

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁] [Fintype X]
  [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem regroup_injective :
    Function.Injective (regroup (P₀ := P₀) (P₁ := P₁) (X := X) (U := U) (F := F)) := by
  rintro ⟨⟨a, b⟩, ⟨⟨c, d⟩, e⟩⟩ ⟨⟨a', b'⟩, ⟨⟨c', d'⟩, e'⟩⟩ h
  simp only [regroup, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  rfl

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [Fintype F] in
theorem liftH_one : liftH (P₁ := P₁) (U := U) (F := F)
    (1 : Matrix (P₀ × X) (P₀ × X) ℂ) = 1 := by
  rw [liftH, one_kronecker_one, submatrix_one _ regroup_injective]

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [Fintype X] [DecidableEq X]
  [Fintype U] [Fintype F] in
theorem liftH_sub (h₁ h₂ : Matrix (P₀ × X) (P₀ × X) ℂ) :
    liftH (P₁ := P₁) (U := U) (F := F) (h₁ - h₂) = liftH h₁ - liftH h₂ := by
  ext i j
  simp [liftH, sub_mul]

omit [DecidableEq P₀] [DecidableEq X] in
theorem posSemidef_liftH {h : Matrix (P₀ × X) (P₀ × X) ℂ} (hh : h.PosSemidef) :
    (liftH (P₁ := P₁) (U := U) (F := F) h).PosSemidef := by
  exact (hh.kronecker PosSemidef.one).submatrix _

theorem norm_le_one_of_nonneg_le_one {a : ℂ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : ‖a‖ ≤ 1 := by
  rw [Complex.nonneg_iff] at h0
  rw [Complex.le_def] at h1
  have him : a.im = 0 := h0.2.symm
  rw [Complex.norm_eq_sqrt_sq_add_sq, him]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [Real.sqrt_sq h0.1]
  simpa using h1.1

theorem norm_skewFun_imag_le (hθ : star θ ⬝ᵥ θ = 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (y : ℝ) : ‖skewFun θ h ((y : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [skewFun_imag]
  set v := liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
    (liftY (P₀ := P₀) (P₁ := P₁) (F := F)
      (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)
  have hv : star v ⬝ᵥ v = 1 := by rw [dotProduct_star_imag_vector, hθ]
  have hH0 := posSemidef_liftH (P₁ := P₁) (U := U) (F := F)
    (nonneg_iff_posSemidef.1 hh0)
  have hH1 : (1 - liftH (P₁ := P₁) (U := U) (F := F) h).PosSemidef := by
    rw [← liftH_one, ← liftH_sub]
    exact posSemidef_liftH (le_iff.1 hh1)
  refine norm_le_one_of_nonneg_le_one (hH0.dotProduct_mulVec_nonneg v) ?_
  have ht := hH1.dotProduct_mulVec_nonneg v
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hv, sub_nonneg] at ht
  exact ht

theorem skewFun_zero_nonneg (hh0 : 0 ≤ h) : 0 ≤ skewFun θ h 0 := by
  rw [skewFun_zero]
  exact (posSemidef_liftH (nonneg_iff_posSemidef.1 hh0)).dotProduct_mulVec_nonneg θ

theorem skew_matrix_conjTranspose {A₁ A₂ : Matrix (P₀ × P₁) (P₀ × P₁) ℂ}
    {B₁ B₂ : Matrix (X × U) (X × U) ℂ}
    {H : Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ}
    (hH : Hᴴ = H) :
    (liftP A₁ * liftY B₁ * H * liftP A₂ * liftY B₂)ᴴ =
      liftP A₂ᴴ * liftY B₂ᴴ * H * liftP A₁ᴴ * liftY B₁ᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hH,
    conjTranspose_liftP, conjTranspose_liftP, conjTranspose_liftY, conjTranspose_liftY]
  rw [← liftP_liftY_comm A₁ᴴ, ← Matrix.mul_assoc (liftY B₂ᴴ),
    ← liftP_liftY_comm A₂ᴴ]
  simp only [Matrix.mul_assoc]

theorem skewFun_neg_conj (hh : h.IsHermitian) (z : ℂ) :
    skewFun θ h (-(starRingEnd ℂ z)) = starRingEnd ℂ (skewFun θ h z) := by
  have hP := posSemidef_margP θ
  have hY := posSemidef_margY θ
  have hH : (liftH (P₁ := P₁) (U := U) (F := F) h)ᴴ = liftH h := by
    rw [conjTranspose_liftH, hh.eq]
  have key : ∀ M : Matrix ((P₀ × P₁) × ((X × U) × F))
      ((P₀ × P₁) × ((X × U) × F)) ℂ,
      starRingEnd ℂ (star θ ⬝ᵥ (M *ᵥ θ)) = star θ ⬝ᵥ (Mᴴ *ᵥ θ) := by
    intro M
    rw [← Complex.star_def, star_dotProduct, star_star, star_mulVec_dotProduct]
  rw [skewFun, skewFun, key, skew_matrix_conjTranspose hH, conjTranspose_suppPow hP,
    conjTranspose_suppPow hP, conjTranspose_suppPow hY, conjTranspose_suppPow hY,
    map_neg, neg_neg]

theorem differentiable_suppPow_apply {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℂ) (i j : n) :
    Differentiable ℂ (fun z => cfcC A (suppPowFun (c * z)) i j) := by
  have hp := differentiable_supportCPow_apply hA i j
  simp only [supportCPow_eq_cfcC] at hp
  exact hp.comp (differentiable_id.const_mul c)

theorem differentiable_skewFun : Differentiable ℂ (skewFun θ h) := by
  have hP := (posSemidef_margP θ).1
  have hY := (posSemidef_margY θ).1
  have hA : ∀ c : ℂ, ∀ i j, Differentiable ℂ (fun z =>
      liftP (X := X) (U := U) (F := F)
        (cfcC (margP θ) (suppPowFun (c * z))) i j) := by
    intro c i j
    simp only [liftP, kroneckerMap_apply]
    exact (differentiable_suppPow_apply hP c _ _).mul (differentiable_const _)
  have hB : ∀ c : ℂ, ∀ i j, Differentiable ℂ (fun z =>
      liftY (P₀ := P₀) (P₁ := P₁) (F := F)
        (cfcC (margY θ) (suppPowFun (c * z))) i j) := by
    intro c i j
    simp only [liftY, kroneckerMap_apply]
    exact (differentiable_const _).mul ((differentiable_suppPow_apply hY c _ _).mul
      (differentiable_const _))
  have hM : ∀ i j, Differentiable ℂ (fun z =>
      ((liftP (cfcC (margP θ) (suppPowFun (1 * z))) *
        liftY (cfcC (margY θ) (suppPowFun (-1 * z))) * liftH h *
        liftP (cfcC (margP θ) (suppPowFun (-1 * z))) *
        liftY (cfcC (margY θ) (suppPowFun (1 * z))) :
          Matrix ((P₀ × P₁) × ((X × U) × F))
            ((P₀ × P₁) × ((X × U) × F)) ℂ) i j)) := by
    intro i j
    refine differentiable_mul_apply (fun i j => ?_) (hB 1) i j
    refine differentiable_mul_apply (fun i j => ?_) (hA (-1)) i j
    refine differentiable_mul_apply
      (N := fun _ : ℂ => liftH (P₁ := P₁) (U := U) (F := F) h)
      (fun i j => ?_) (fun i j => differentiable_const _) i j
    exact differentiable_mul_apply (hA 1) (hB (-1)) i j
  have heq : skewFun θ h = fun z => star θ ⬝ᵥ
      ((liftP (cfcC (margP θ) (suppPowFun (1 * z))) *
        liftY (cfcC (margY θ) (suppPowFun (-1 * z))) * liftH h *
        liftP (cfcC (margP θ) (suppPowFun (-1 * z))) *
        liftY (cfcC (margY θ) (suppPowFun (1 * z)))) *ᵥ θ) := by
    funext z
    simp [skewFun]
  rw [heq]
  simp only [dotProduct, mulVec]
  exact Differentiable.fun_sum fun i _ => (differentiable_const _).mul
    (Differentiable.fun_sum fun j _ => (hM i j).mul (differentiable_const _))

end Entropy.ConditionalSkew

end
