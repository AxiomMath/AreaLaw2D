/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewPhase.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
imaginary-axis comparison portion.
-/
import OpenAI.ConditionalSkewGeometry

/-! # Marginal-phase comparison for the conditional skew function -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open Matrix Entropy.MarginalPhase

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁]
  [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

omit [Fintype X] [Fintype U] [DecidableEq U] [Fintype F] in
theorem embedF_one_kronecker (A : Matrix U U ℂ) :
    embedF (F := F) ((1 : Matrix X X ℂ) ⊗ₖ A) =
      (1 : Matrix X X ℂ) ⊗ₖ (A ⊗ₖ (1 : Matrix F F ℂ)) := by
  ext ⟨x, u, f⟩ ⟨x', u', f'⟩
  simp [embedF, mul_assoc]

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁] [Fintype X]
  [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem regroup_bijective :
    Function.Bijective (regroup (P₀ := P₀) (P₁ := P₁) (X := X) (U := U) (F := F)) :=
  ⟨regroup_injective,
    fun ⟨⟨a, c⟩, ⟨b, ⟨d, e⟩⟩⟩ => ⟨⟨⟨a, b⟩, ⟨⟨c, d⟩, e⟩⟩, rfl⟩⟩

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F] in
theorem liftR_one_kronecker_eq (K : Matrix (U × F) (U × F) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) ((1 : Matrix X X ℂ) ⊗ₖ K) =
      ((1 : Matrix (P₀ × X) (P₀ × X) ℂ) ⊗ₖ
        ((1 : Matrix P₁ P₁ ℂ) ⊗ₖ K)).submatrix regroup regroup := by
  ext ⟨⟨a, b⟩, ⟨⟨c, d⟩, e⟩⟩ ⟨⟨a', b'⟩, ⟨⟨c', d'⟩, e'⟩⟩
  simp only [liftR, regroup, kronecker_apply, submatrix_apply, Equiv.prodAssoc_apply,
    one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem liftR_one_kronecker_comm_liftH (K : Matrix (U × F) (U × F) ℂ)
    (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) ((1 : Matrix X X ℂ) ⊗ₖ K) * liftH h =
      liftH h * liftR ((1 : Matrix X X ℂ) ⊗ₖ K) := by
  rw [liftR_one_kronecker_eq, liftH, ← submatrix_mul _ _ _ _ _ regroup_bijective,
    ← submatrix_mul _ _ _ _ _ regroup_bijective, ← mul_kronecker_mul,
    ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] in
theorem posSemidef_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    (rhoW θ).PosSemidef :=
  (posSemidef_margW θ).submatrix _

/-- The unitary `ρ̂_U^{iu} ρ̂_{UF}^{-iu}` on `U × F`. -/
def zetaUF (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    Matrix (U × F) (U × F) ℂ :=
  (cfcC (marginalU (rhoW θ)) (hatFun u) ⊗ₖ (1 : Matrix F F ℂ)) *
    cfcC (marginalUF (rhoW θ)) (hatFun (-u))

/-- The marginal phase-difference operator on `X × (U × F)`. -/
def phaseDiffW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  embedF (((1 : Matrix X X ℂ) ⊗ₖ
      cfcC (marginalU (rhoW θ)) (hatFun (-u))) *
      cfcC (margY θ) (hatFun u)) -
    ((1 : Matrix X X ℂ) ⊗ₖ
      cfcC (marginalUF (rhoW θ)) (hatFun (-u))) *
      cfcC (rhoW θ) (hatFun u)

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] in
theorem zetaUF_unitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    (zetaUF θ u)ᴴ * zetaUF θ u = 1 := by
  have hU := posSemidef_marginalU (posSemidef_rhoW θ)
  have hUF := posSemidef_marginalUF (posSemidef_rhoW θ)
  rw [zetaUF, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_cfcC_hat hU, conjTranspose_cfcC_hat hUF, neg_neg,
    Matrix.mul_assoc, ← Matrix.mul_assoc (_ ⊗ₖ _), ← mul_kronecker_mul,
    cfcC_hat_neg_mul hU.1, Matrix.one_mul, one_kronecker_one, Matrix.one_mul,
    cfcC_hat_mul_neg hUF.1]

theorem liftR_zetaUF_unitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    (liftR (P₀ := P₀) (P₁ := P₁)
      ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u))ᴴ *
      liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) = 1 := by
  rw [conjTranspose_liftR, liftR_mul, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul, zetaUF_unitary, one_kronecker_one,
    liftR_one]

/-- The comparison vector gives the same quadratic form as the original vector. -/
theorem comparison_vector_quadForm
    (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    (h : Matrix (P₀ × X) (P₀ × X) ℂ) (u : ℝ) :
    star (liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ) ⬝ᵥ
        (liftH h *ᵥ (liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ)) =
      star θ ⬝ᵥ (liftH h *ᵥ θ) :=
  dotProduct_mulVec_conj_unitary (liftR_zetaUF_unitary θ u)
    (liftR_one_kronecker_comm_liftH _ h) θ

/-- The unitary relating the vector difference to the marginal phase difference. -/
def relUnitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  liftP (cfcC (margP θ) (hatFun (-u))) *
    liftR (embedF ((1 : Matrix X X ℂ) ⊗ₖ
      cfcC (marginalU (rhoW θ)) (hatFun u)))

theorem relUnitary_unitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    (relUnitary θ u)ᴴ * relUnitary θ u = 1 := by
  have hP := posSemidef_margP θ
  have hU := posSemidef_marginalU (posSemidef_rhoW θ)
  rw [relUnitary, conjTranspose_mul, conjTranspose_liftP, conjTranspose_liftR,
    conjTranspose_embedF, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_cfcC_hat hP, conjTranspose_cfcC_hat hU, neg_neg,
    Matrix.mul_assoc, ← Matrix.mul_assoc (liftP _), liftP_mul,
    cfcC_hat_mul_neg hP.1, liftP_one, Matrix.one_mul, liftR_mul, embedF_mul,
    ← mul_kronecker_mul, Matrix.one_mul, cfcC_hat_neg_mul hU.1,
    one_kronecker_one, embedF_one, liftR_one]

/-- The vector difference is a unitary image of the marginal phase difference. -/
theorem imag_vector_sub_eq (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    liftR (embedF (cfcC (margY θ) (hatFun u)) *
        cfcC (rhoW θ) (hatFun (-u))) *ᵥ θ -
        liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ =
      relUnitary θ u *ᵥ (liftR (phaseDiffW θ u) *ᵥ θ) := by
  have hP := (posSemidef_margP θ).1
  have hU := (posSemidef_marginalU (posSemidef_rhoW θ)).1
  have hb : embedF (F := F) ((1 : Matrix X X ℂ) ⊗ₖ
      cfcC (marginalU (rhoW θ)) (hatFun u)) * phaseDiffW θ u =
      embedF (cfcC (margY θ) (hatFun u)) -
        ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *
          cfcC (rhoW θ) (hatFun u) := by
    rw [phaseDiffW, Matrix.mul_sub, embedF_mul, ← Matrix.mul_assoc,
      ← mul_kronecker_mul, Matrix.one_mul, cfcC_hat_mul_neg hU,
      one_kronecker_one, Matrix.one_mul, ← Matrix.mul_assoc,
      embedF_one_kronecker, ← mul_kronecker_mul, Matrix.one_mul, zetaUF]
  have h1 : ∀ E : Matrix (X × (U × F)) (X × (U × F)) ℂ,
      liftP (cfcC (margP θ) (hatFun (-u))) *ᵥ (liftR E *ᵥ θ) =
        liftR (E * cfcC (rhoW θ) (hatFun (-u))) *ᵥ θ := by
    intro E
    rw [mulVec_mulVec, liftP_liftR_comm, ← mulVec_mulVec, liftP_cfcC_mulVec,
      mulVec_mulVec, liftR_mul]
  have h2 : liftP (cfcC (margP θ) (hatFun (-u))) *ᵥ
      (liftR (((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *
        cfcC (rhoW θ) (hatFun u)) *ᵥ θ) =
      liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ := by
    rw [← liftR_mul, ← mulVec_mulVec, ← liftP_cfcC_mulVec, mulVec_mulVec,
      liftP_liftR_comm, ← mulVec_mulVec, mulVec_mulVec (v := θ), liftP_mul,
      cfcC_hat_neg_mul hP, liftP_one, one_mulVec]
  rw [relUnitary, ← mulVec_mulVec, mulVec_mulVec (M := liftR _), liftR_mul, hb,
    liftR_sub, sub_mulVec, mulVec_sub, h1, h2]

/-- The reindexing `P × W ≃ (X × (U × F)) × P`. -/
def reindexE : (P₀ × P₁) × ((X × U) × F) ≃ (X × (U × F)) × (P₀ × P₁) :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr assocE (Equiv.refl _))

/-- The vector `θ` reindexed for the marginal-phase comparison. -/
def thetaR (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    EuclideanSpace ℂ ((X × (U × F)) × (P₀ × P₁)) :=
  WithLp.toLp 2 (θ ∘ reindexE.symm)

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem kronecker_one_eq_submatrix_liftR
    (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    M ⊗ₖ (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) =
      (liftR M).submatrix reindexE.symm reindexE.symm := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [liftR, reindexE, mul_comm]

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem kronecker_one_mulVec_thetaR
    (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (M ⊗ₖ (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ)) *ᵥ (thetaR θ).ofLp =
      (liftR M *ᵥ θ) ∘ reindexE.symm := by
  rw [kronecker_one_eq_submatrix_liftR, submatrix_mulVec_equiv]
  congr 2

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U]
  [DecidableEq F] in
theorem norm_thetaR {θ : (P₀ × P₁) × ((X × U) × F) → ℂ}
    (hθ : star θ ⬝ᵥ θ = 1) : ‖thetaR θ‖ = 1 := by
  rw [thetaR, norm_toLp_comp_equiv_symm]
  have h := norm_toLp_sq_eq_re' θ
  rw [hθ, Complex.one_re] at h
  nlinarith [norm_nonneg
    (WithLp.toLp 2 θ : EuclideanSpace ℂ ((P₀ × P₁) × ((X × U) × F)))]

omit [DecidableEq P₀] [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem traceRight_thetaR (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    Matrix.traceRight (vecMulVec (thetaR θ).ofLp (star (thetaR θ).ofLp)) =
      rhoW θ := by
  ext i j
  simp [Matrix.traceRight, Matrix.traceLeft, thetaR, rhoW, margW, reindexE,
    vecMulVec]

theorem phaseDifference_thetaR
    (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    phaseDifference
      (posSemidef_vecMulVec_self_star (thetaR θ).ofLp).traceRight u =
      phaseDiffW θ u := by
  simp only [phaseDifference, hatPhase_eq_cfcC]
  rw [traceRight_thetaR, marginalXU_rhoW]
  rfl

theorem condMutualInfo_congr
    {A B : Matrix (X × (U × F)) (X × (U × F)) ℂ} (h : A = B)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    condMutualInfo A hA = condMutualInfo B hB := by
  subst h
  rfl

/-- The conditional mutual information used in the conditional skew estimate. -/
def skewEta (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : ℝ :=
  condMutualInfo (rhoW θ) (posSemidef_rhoW θ)

/-- The singular marginal-phase estimate applied to the purification `θ`. -/
theorem norm_liftR_phaseDiffW_le
    {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1)
    (u : ℝ) :
    ‖(WithLp.toLp 2 (liftR (phaseDiffW θ u) *ᵥ θ) : EuclideanSpace ℂ _)‖ ≤
      2 * |Real.sinh (Real.pi * u)| *
        phaseRate (Fintype.card X) (skewEta θ) := by
  have h := norm_phaseDifference_mulVec_le (thetaR θ) (norm_thetaR hθ) u
  rw [phaseDifference_thetaR, kronecker_one_mulVec_thetaR,
    norm_toLp_comp_equiv_symm,
    condMutualInfo_congr (traceRight_thetaR θ) _ (posSemidef_rhoW θ)] at h
  exact h

/-- Imaginary-axis comparison for the conditional skew function. -/
theorem norm_skewFun_imag_sub_le
    {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1)
    {h : Matrix (P₀ × X) (P₀ × X) ℂ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (u : ℝ) :
    ‖skewFun θ h ((u : ℂ) * Complex.I) - skewFun θ h 0‖ ≤
      4 * √((skewFun θ h 0).re) * |Real.sinh (Real.pi * u)| *
          phaseRate (Fintype.card X) (skewEta θ) +
        4 * Real.sinh (Real.pi * u) ^ 2 *
          phaseRate (Fintype.card X) (skewEta θ) ^ 2 := by
  have hH0 : 0 ≤ liftH (P₁ := P₁) (U := U) (F := F) h :=
    nonneg_iff_posSemidef.2
      (posSemidef_liftH (nonneg_iff_posSemidef.1 hh0))
  have hH1 : liftH (P₁ := P₁) (U := U) (F := F) h ≤ 1 := by
    rw [le_iff, ← liftH_one, ← liftH_sub]
    exact posSemidef_liftH (le_iff.1 hh1)
  set R := phaseRate (Fintype.card X) (skewEta θ)
  set s := |Real.sinh (Real.pi * u)|
  have hE := norm_liftR_phaseDiffW_le hθ u
  rw [skewFun_imag, imag_vector_eq, skewFun_zero,
    ← comparison_vector_quadForm θ h u]
  refine (norm_quadForm_sub_le hH0 hH1 _ _).trans ?_
  rw [imag_vector_sub_eq,
    norm_toLp_mulVec_of_unitary (relUnitary_unitary θ u),
    comparison_vector_quadForm]
  set E := ‖(WithLp.toLp 2 (liftR (phaseDiffW θ u) *ᵥ θ) :
    EuclideanSpace ℂ _)‖
  have hE0 : 0 ≤ E := norm_nonneg _
  have hs : Real.sinh (Real.pi * u) ^ 2 = s ^ 2 := (sq_abs _).symm
  rw [hs]
  have hp := Real.sqrt_nonneg
    ((star θ ⬝ᵥ
      (liftH (P₁ := P₁) (U := U) (F := F) h *ᵥ θ)).re)
  nlinarith [mul_le_mul_of_nonneg_left hE hp,
    mul_le_mul hE hE hE0 (le_trans hE0 hE)]

end Entropy.ConditionalSkew
