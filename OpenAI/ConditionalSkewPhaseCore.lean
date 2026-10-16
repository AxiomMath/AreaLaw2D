/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewPhase.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
generic phase-calculus portion.
-/
import OpenAI.ConditionalSkewStrip
import OpenAI.MarginalPhaseSingular

/-! # Generic phase calculus for the conditional skew estimate -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix Entropy.MarginalPhase

/-- The kernel-completed phase function. -/
def hatFun (u : ℝ) (t : ℝ) : ℂ :=
  if t = 0 then 1 else ((t : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)

variable {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem hatPhase_eq_cfcC {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (u : ℝ) : hatPhase hM u = cfcC M (hatFun u) := by
  rw [cfcC_eq_spectralFun hM]
  rfl

theorem hatFun_neg_mul (u t : ℝ) :
    hatFun (-u) t * hatFun u t = 1 := by
  unfold hatFun
  split_ifs with h
  · simp
  · rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 h)]
    push_cast
    ring_nf
    simp

theorem cfcC_hat_neg_mul {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (u : ℝ) :
    cfcC M (hatFun (-u)) * cfcC M (hatFun u) = 1 := by
  rw [cfcC_mul hM]
  simp_rw [hatFun_neg_mul]
  exact cfcC_one hM

theorem cfcC_hat_mul_neg {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (u : ℝ) :
    cfcC M (hatFun u) * cfcC M (hatFun (-u)) = 1 := by
  simpa using cfcC_hat_neg_mul hM (-u)

theorem cfcC_suppPow_imag {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (u : ℝ) :
    cfcC M (suppPowFun ((u : ℂ) * Complex.I)) =
      cfcC M (hatFun u) - cfcC M kerFun := by
  rw [eq_sub_iff_add_eq, cfcC_add hM]
  congr 1
  funext t
  unfold suppPowFun hatFun kerFun
  split_ifs <;> simp

theorem conjTranspose_cfcC_hat {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (u : ℝ) :
    (cfcC M (hatFun u))ᴴ = cfcC M (hatFun (-u)) := by
  rw [conjTranspose_cfcC hM.1]
  refine cfcC_congr_of_nonneg hM fun t ht => ?_
  unfold hatFun
  split_ifs with h
  · simp
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos.le]
      exact Real.pi_ne_zero.symm
    have hc := Complex.cpow_conj (t : ℂ)
      ((u : ℂ) * Complex.I) harg
    rw [Complex.conj_ofReal] at hc
    rw [← hc]
    congr 1
    simp [Complex.conj_ofReal]

/-- Coefficient matrix of a vector on `n × m`. -/
def coeffMat (θ : n × m → ℂ) : Matrix n m ℂ :=
  Matrix.of fun a b => θ (a, b)

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem traceRight_vecMulVec (θ : n × m → ℂ) :
    Matrix.traceRight (vecMulVec θ (star θ)) =
      coeffMat θ * (coeffMat θ)ᴴ := by
  ext i j
  simp [Matrix.traceRight, coeffMat, vecMulVec, mul_apply]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem traceLeft_vecMulVec (θ : n × m → ℂ) :
    Matrix.traceLeft (vecMulVec θ (star θ)) =
      ((coeffMat θ)ᴴ * coeffMat θ)ᵀ := by
  ext i j
  simp [Matrix.traceLeft, coeffMat, vecMulVec, mul_apply, mul_comm]

omit [DecidableEq n] in
theorem kronecker_one_mulVec_apply (M : Matrix n n ℂ)
    (θ : n × m → ℂ) (a : n) (b : m) :
    ((M ⊗ₖ (1 : Matrix m m ℂ)) *ᵥ θ) (a, b) =
      (M * coeffMat θ) a b := by
  simp [mulVec, dotProduct, one_apply, Fintype.sum_prod_type,
    mul_apply, coeffMat]

omit [DecidableEq m] in
theorem one_kronecker_mulVec_apply (N : Matrix m m ℂ)
    (θ : n × m → ℂ) (a : n) (b : m) :
    (((1 : Matrix n n ℂ) ⊗ₖ N) *ᵥ θ) (a, b) =
      (coeffMat θ * Nᵀ) a b := by
  simp [mulVec, dotProduct, one_apply, Fintype.sum_prod_type,
    mul_apply, coeffMat, mul_comm]

/-- Schmidt mirroring for a function of the two marginals of a pure vector. -/
theorem cfcC_kronecker_one_mulVec (θ : n × m → ℂ) (g : ℝ → ℂ) :
    (cfcC (Matrix.traceRight (vecMulVec θ (star θ))) g ⊗ₖ
        (1 : Matrix m m ℂ)) *ᵥ θ =
      ((1 : Matrix n n ℂ) ⊗ₖ
        cfcC (Matrix.traceLeft (vecMulVec θ (star θ))) g) *ᵥ θ := by
  set C := coeffMat θ
  have hA : (C * Cᴴ).IsHermitian :=
    isHermitian_mul_conjTranspose_self C
  have hB : (Cᴴ * C).IsHermitian :=
    isHermitian_conjTranspose_mul_self C
  have key : cfcC (C * Cᴴ) g * C =
      C * cfcC (Cᴴ * C) g :=
    cfcC_mul_intertwine hA hB C
      (by rw [Matrix.mul_assoc]) g
  have htr : (cfcC ((Cᴴ * C)ᵀ) g)ᵀ =
      cfcC (Cᴴ * C) g := by
    rw [cfcC_transpose hB.transpose, transpose_transpose]
  funext ⟨a, b⟩
  rw [kronecker_one_mulVec_apply, one_kronecker_mulVec_apply,
    traceRight_vecMulVec, traceLeft_vecMulVec, htr, key]

omit [DecidableEq n] in
theorem norm_toLp_comp_equiv_symm {l : Type*} [Fintype l]
    (e : n ≃ l) (v : n → ℂ) :
    ‖(WithLp.toLp 2 (v ∘ e.symm) : EuclideanSpace ℂ l)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re']
  congr 1
  change (star v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = star v ⬝ᵥ v
  rw [dotProduct_comp_equiv_symm]
  congr 1
  funext i
  simp

theorem norm_toLp_mulVec_of_unitary {R : Matrix n n ℂ}
    (hR : Rᴴ * R = 1) (v : n → ℂ) :
    ‖(WithLp.toLp 2 (R *ᵥ v) : EuclideanSpace ℂ n)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re',
    star_mulVec_dotProduct, mulVec_mulVec, hR, one_mulVec]

theorem dotProduct_mulVec_conj_unitary {R H : Matrix n n ℂ}
    (hR : Rᴴ * R = 1) (hc : R * H = H * R) (v : n → ℂ) :
    star (R *ᵥ v) ⬝ᵥ (H *ᵥ (R *ᵥ v)) =
      star v ⬝ᵥ (H *ᵥ v) := by
  rw [star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hR, Matrix.one_mul]

/-- Quadratic-form perturbation under a positive contraction. -/
theorem norm_quadForm_sub_le {H : Matrix n n ℂ}
    (h0 : 0 ≤ H) (h1 : H ≤ 1) (w w₀ : n → ℂ) :
    ‖star w ⬝ᵥ (H *ᵥ w) - star w₀ ⬝ᵥ (H *ᵥ w₀)‖ ≤
      2 * √((star w₀ ⬝ᵥ (H *ᵥ w₀)).re) *
          ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ n)‖ +
        ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ n)‖ ^ 2 := by
  set B := CFC.sqrt H
  have hB : Bᴴ = B := (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq
  have hHB : H = Bᴴ * B := by
    rw [hB]
    exact (CFC.sqrt_mul_sqrt_self H h0).symm
  have hform : ∀ x y : n → ℂ,
      star x ⬝ᵥ (H *ᵥ y) =
        star (B *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
    intro x y
    rw [hHB, ← mulVec_mulVec, ← star_mulVec_dotProduct]
  have hBsq : ∀ x : n → ℂ,
      ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ n)‖ =
        √((star x ⬝ᵥ (H *ᵥ x)).re) := by
    intro x
    rw [hform, ← norm_toLp_sq_eq_re',
      Real.sqrt_sq (norm_nonneg _)]
  have hBle : ∀ x : n → ℂ,
      ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ n)‖ ≤
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
    intro x
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re', ← hform]
    have ht := (le_iff.1 h1).dotProduct_mulVec_nonneg x
    rw [sub_mulVec, one_mulVec, dotProduct_sub, sub_nonneg,
      Complex.le_def] at ht
    exact ht.1
  set e := w - w₀
  have hw : w = w₀ + e := by simp [e]
  have hexp : star w ⬝ᵥ (H *ᵥ w) -
      star w₀ ⬝ᵥ (H *ᵥ w₀) =
      star (B *ᵥ e) ⬝ᵥ (B *ᵥ w₀) +
        star (B *ᵥ w₀) ⬝ᵥ (B *ᵥ e) +
        star (B *ᵥ e) ⬝ᵥ (B *ᵥ e) := by
    rw [hform, hform, hw, mulVec_add, star_add, add_dotProduct,
      dotProduct_add, dotProduct_add]
    ring
  set a := ‖(WithLp.toLp 2 (B *ᵥ w₀) : EuclideanSpace ℂ n)‖
  set E := ‖(WithLp.toLp 2 e : EuclideanSpace ℂ n)‖
  have hBe := hBle e
  rw [hexp, ← hBsq w₀]
  calc
    _ ≤ ‖star (B *ᵥ e) ⬝ᵥ (B *ᵥ w₀)‖ +
          ‖star (B *ᵥ w₀) ⬝ᵥ (B *ᵥ e)‖ +
          ‖star (B *ᵥ e) ⬝ᵥ (B *ᵥ e)‖ := norm_add₃_le
    _ ≤ E * a + a * E + E * E := by
      gcongr
      · exact (norm_star_dotProduct_le _ _).trans
          (mul_le_mul_of_nonneg_right hBe (norm_nonneg _))
      · exact (norm_star_dotProduct_le _ _).trans
          (mul_le_mul_of_nonneg_left hBe (norm_nonneg _))
      · exact (norm_star_dotProduct_le _ _).trans
          (mul_le_mul hBe hBe (norm_nonneg _) (norm_nonneg _))
    _ = 2 * a * E + E ^ 2 := by ring

end Entropy.ConditionalSkew

end
