/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewSetup.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.ConditionalSkewSetup

/-! # Kernel support for the conditional skew function -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

theorem suppPowFun_zero_add_ker (t : ℝ) :
    suppPowFun 0 t + (if t = 0 then 1 else 0) = 1 := by
  unfold suppPowFun
  split_ifs <;> simp

theorem ker_mul_id (t : ℝ) : (if t = 0 then (1 : ℂ) else 0) * (t : ℂ) = 0 := by
  split_ifs with h <;> simp [h]

theorem dotProduct_mulVec_eq_trace' {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (M *ᵥ v) = (M * vecMulVec v (star v)).trace := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

omit [DecidableEq P₀] [DecidableEq P₁] in
theorem liftP_mulVec_eq_zero (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    {K : Matrix (P₀ × P₁) (P₀ × P₁) ℂ} (hK : Kᴴ = K) (hKK : K * K = K)
    (htr : (margP θ * K).trace = 0) : liftP K *ᵥ θ = 0 := by
  rw [← dotProduct_star_self_eq_zero, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    conjTranspose_liftP, hK, liftP_mul, hKK, dotProduct_mulVec_eq_trace', trace_mul_comm,
    liftP, trace_mul_kron_one_right]
  exact htr

omit [DecidableEq X] [DecidableEq U] in
theorem liftY_mulVec_eq_zero (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    {K : Matrix (X × U) (X × U) ℂ} (hK : Kᴴ = K) (hKK : K * K = K)
    (htr : (margY θ * K).trace = 0) : liftY (P₀ := P₀) (P₁ := P₁) (F := F) K *ᵥ θ = 0 := by
  rw [← dotProduct_star_self_eq_zero, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    conjTranspose_liftY, hK, liftY_mul, hKK, dotProduct_mulVec_eq_trace', trace_mul_comm,
    liftY, trace_mul_one_kron_right, trace_mul_kron_one_right]
  exact htr

/-- The indicator of the scalar kernel. -/
def kerFun (t : ℝ) : ℂ := if t = 0 then 1 else 0

theorem cfcC_ker_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (cfcC A kerFun)ᴴ = cfcC A kerFun := by
  rw [conjTranspose_cfcC hA]
  congr 1
  funext t
  unfold kerFun
  split_ifs <;> simp

theorem cfcC_ker_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : cfcC A kerFun * cfcC A kerFun = cfcC A kerFun := by
  rw [cfcC_mul hA]
  congr 1
  funext t
  unfold kerFun
  split_ifs <;> simp

theorem mul_cfcC_ker {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : A * cfcC A kerFun = 0 := by
  calc
    A * cfcC A kerFun = cfcC A (fun t => (t : ℂ)) * cfcC A kerFun := by rw [cfcC_id hA]
    _ = 0 := by
      rw [cfcC_mul hA, cfcC_eq_spectralFun hA, ← zero_smul ℂ (1 : Matrix n n ℂ),
        ← spectralFun_const hA.eigenvectorUnitary 0]
      congr 1
      funext k
      unfold kerFun
      split_ifs with h <;> simp [h]

theorem cfcC_supp_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfcC A (suppPowFun 0) = 1 - cfcC A kerFun := by
  rw [eq_sub_iff_add_eq, cfcC_add hA, ← cfcC_one hA]
  congr 1
  funext t
  unfold suppPowFun kerFun
  split_ifs <;> simp

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁] [Fintype X]
  [Fintype U] [Fintype F] in
theorem liftP_sub (A B : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    liftP (X := X) (U := U) (F := F) (A - B) = liftP A - liftP B := by
  ext i j
  simp [liftP, sub_mul]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] in
theorem liftY_sub (A B : Matrix (X × U) (X × U) ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (A - B) = liftY A - liftY B := by
  ext i j
  simp [liftY, sub_mul, mul_sub]

theorem liftP_supp_zero_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftP (cfcC (margP θ) (suppPowFun 0)) *ᵥ θ = θ := by
  have hA := (posSemidef_margP θ).1
  rw [cfcC_supp_zero hA, liftP_sub, liftP_one, sub_mulVec, one_mulVec,
    liftP_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
      (by rw [mul_cfcC_ker hA, trace_zero]), sub_zero]

theorem liftY_supp_zero_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (cfcC (margY θ) (suppPowFun 0)) *ᵥ θ = θ := by
  have hA := (posSemidef_margY θ).1
  rw [cfcC_supp_zero hA, liftY_sub, liftY_one, sub_mulVec, one_mulVec,
    liftY_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
      (by rw [mul_cfcC_ker hA, trace_zero]), sub_zero]

theorem suppPow_mul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (z w : ℂ) :
    cfcC A (suppPowFun z) * cfcC A (suppPowFun w) = cfcC A (suppPowFun (z + w)) := by
  rw [cfcC_mul hA]
  congr 1
  funext t
  unfold suppPowFun
  split_ifs with h
  · simp
  · rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 h)]

theorem conjTranspose_suppPow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (z : ℂ) :
    (cfcC A (suppPowFun z))ᴴ = cfcC A (suppPowFun (starRingEnd ℂ z)) := by
  rw [conjTranspose_cfcC hA.1]
  refine cfcC_congr_of_nonneg hA fun t ht => ?_
  unfold suppPowFun
  split_ifs with h
  · simp
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos.le]
      exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

end Entropy.ConditionalSkew

end
