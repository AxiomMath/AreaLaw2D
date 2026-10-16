/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseQuantities.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
quadratic-form portion.
-/
import Arealaw.VonNeumann
import OpenAI.MarginalPhaseFaithful
import OpenAI.PartialTraceDomination
import OpenAI.PosDefInverseOrder

/-! # Quadratic inputs of the marginal-phase comparison -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F]

/-- The conditional mutual information `I(X:F|U)` of a positive semidefinite matrix on
`X × (U × F)`, expressed with the repository's canonical von Neumann entropy. -/
def condMutualInfo (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ)
    (hρ : ρ.PosSemidef) : ℝ :=
  Arealaw.vonNeumann ((hρ.submatrix assocE).traceRight.isHermitian) +
    Arealaw.vonNeumann hρ.traceLeft.isHermitian -
    Arealaw.vonNeumann ((hρ.submatrix assocE).traceRight.traceLeft.isHermitian) -
    Arealaw.vonNeumann hρ.isHermitian

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem trace_marginalXU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (marginalXU ρ).trace = ρ.trace := by
  rw [marginalXU, traceRight_trace, trace_submatrix]

theorem trace_marginalU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (marginalU ρ).trace = ρ.trace := by
  rw [marginalU, traceLeft_trace, trace_marginalXU]

theorem trace_sigmaS [Nonempty X]
    (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (sigmaS ρ).trace = ρ.trace := by
  rw [sigmaS, trace_kronecker, trace_smul, trace_one, trace_marginalU,
    smul_eq_mul]
  have : (Fintype.card X : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

section Faithful

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
  [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

theorem rpowSpec_mul_mul_rpowSpec_half {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef)
    (M : Matrix n n ℂ) :
    (rpowSpec hA (1 / 2) * M * rpowSpec hA (1 / 2)).trace =
      (M * rpowSpec hA 1).trace := by
  rw [trace_mul_cycle, rpowSpec_mul, trace_mul_comm]
  norm_num

/-- `⟨b₀, B b₀⟩ = tr σ_s = tr ρ`. -/
theorem compression_quadB :
    (compression hρ).quadB = ρ.trace.re := by
  set hs := posDef_marginalXU (F := F) hρ
  rw [ResolventCompression.quadB]
  simp only [ResolventCompression.weightB]
  rw [← re_dotProduct_spectralFun_ofReal]
  change (star (vec (rpowSpec hs (1 / 2))) ⬝ᵥ
    (spectralFun (unitaryB hρ) (fun p => (eigB hρ p : ℂ)) *ᵥ
      vec (rpowSpec hs (1 / 2)))).re = _
  rw [spectralFun_eigB, kronecker_mulVec_vec, transpose_transpose,
    star_vec_dotProduct_vec, rpowSpec_isHermitian, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, rpowSpec_mul, rpowSpec_mul]
  norm_num [rpowSpec_zero, trace_sigmaS]

omit [Nonempty X] [Nonempty F] in
theorem re_trace_mul_mul_mono {n : Type*} [Fintype n] [DecidableEq n]
    {R A B : Matrix n n ℂ} (hR : R.IsHermitian) (hAB : A ≤ B) :
    (R * A * R).trace.re ≤ (R * B * R).trace.re := by
  have h := (le_iff.1 hAB).conjTranspose_mul_mul_same R
  rw [hR.eq, Matrix.mul_sub, Matrix.sub_mul] at h
  have ht := h.trace_nonneg
  rw [trace_sub] at ht
  rw [Complex.nonneg_iff] at ht
  simp only [Complex.sub_re, Complex.zero_re] at ht
  linarith [ht.1]

omit [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]
    [Nonempty F] in
theorem sigmaF_eq_smul :
    (Fintype.card X : ℂ) •
        ((1 : Matrix X X ℂ) ⊗ₖ marginalUF ρ) =
      ((Fintype.card X : ℝ) ^ 2) • sigmaF ρ := by
  have hd : (Fintype.card X : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [sigmaF, smul_kronecker, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

omit [DecidableEq U] [DecidableEq F] [Nonempty F] in
theorem posDef_sigmaF (hρ : ρ.PosDef) : (sigmaF ρ).PosDef := by
  have hd : (0 : ℝ) < (Fintype.card X : ℝ)⁻¹ :=
    inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have h1 : ((Fintype.card X : ℝ)⁻¹ •
      (1 : Matrix X X ℂ)).PosDef := PosDef.one.smul hd
  rw [sigmaF, show ((Fintype.card X : ℂ)⁻¹ •
      (1 : Matrix X X ℂ)) =
      (Fintype.card X : ℝ)⁻¹ • (1 : Matrix X X ℂ) by
        rw [← Complex.coe_smul]
        push_cast
        rfl]
  exact h1.kronecker (posDef_marginalUF hρ)

/-- `⟨a₀, A⁻¹ a₀⟩ = tr (ρ σ_f⁻¹ ρ) ≤ |X|² tr ρ`. -/
theorem compression_invQuadA_le :
    (compression hρ).invQuadA ≤
      (Fintype.card X : ℝ) ^ 2 * ρ.trace.re := by
  set hUF := posDef_marginalUF (F := F) (U := U) hρ
  set Sinv := spectralFun (sigmaFUnitary hUF)
    (fun p => ((sigmaFEig hUF p)⁻¹ : ℝ))
  have hsf : ∀ p, 0 < sigmaFEig hUF p := fun p => by
    have hp := hUF.eigenvalues_pos p.2
    unfold sigmaFEig
    have : (0 : ℝ) < Fintype.card X :=
      Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hA : spectralFun (compression hρ).UA
      (fun k => (((compression hρ).lam k)⁻¹ : ℝ)) =
      (rpowSpec hρ 1)ᵀ ⊗ₖ Sinv := by
    refine spectralFun_leftRight_mul _ _ hρ.1.eigenvalues
      (sigmaFEig hUF) (fun t => ((t⁻¹ : ℝ) : ℂ))
      (fun a => ((a ^ (1 : ℝ) : ℝ) : ℂ))
      (fun b => ((b⁻¹ : ℝ) : ℂ)) fun k j => ?_
    have hk := hρ.eigenvalues_pos k
    rw [Real.rpow_one, Real.rpow_neg_one, mul_inv, inv_inv,
      Complex.ofReal_mul]
  have hform : (compression hρ).invQuadA =
      (Sinv * rpowSpec hρ 2).trace.re := by
    rw [ResolventCompression.invQuadA]
    simp only [ResolventCompression.weightA]
    rw [← re_dotProduct_spectralFun_ofReal, hA, compression_a0,
      kronecker_mulVec_vec, transpose_transpose, star_vec_dotProduct_vec,
      rpowSpec_isHermitian, trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, rpowSpec_mul, rpowSpec_mul]
    norm_num
  have hSinv : (sigmaF ρ)⁻¹ = Sinv := by
    refine inv_eq_left_inv ?_
    rw [← spectralFun_sigmaF hUF, spectralFun_mul,
      ← spectralFun_one (sigmaFUnitary hUF)]
    congr 1
    funext p
    simp only [Pi.mul_apply]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hsf p).ne',
      Complex.ofReal_one]
  set c : ℝ := (Fintype.card X : ℝ) ^ 2
  have hc : 0 < c := by
    have : (0 : ℝ) < Fintype.card X :=
      Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hσ := posDef_sigmaF hρ
  have hB : (c • sigmaF ρ).PosDef := hσ.smul hc
  have hle : ρ ≤ c • sigmaF ρ := by
    rw [← sigmaF_eq_smul]
    exact hρ.posSemidef.le_card_smul_one_kronecker_traceLeft
  have hinv := PosDef.inv_le_inv_of_le hρ hB hle
  have hBinv : (c • sigmaF ρ)⁻¹ = c⁻¹ • (sigmaF ρ)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc.ne', one_smul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hσ.isUnit)]
  have hmono := re_trace_mul_mul_mono hρ.1 hinv
  rw [hBinv, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hρ.isUnit),
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, trace_smul,
    Complex.real_smul, Complex.mul_re] at hmono
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hmono
  rw [hform, ← hSinv, show rpowSpec hρ 2 = ρ * ρ by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, ← rpowSpec_mul,
        rpowSpec_one],
    ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  have hc' : c⁻¹ * (ρ * (sigmaF ρ)⁻¹ * ρ).trace.re ≤
      ρ.trace.re := hmono
  rw [inv_mul_le_iff₀ hc] at hc'
  exact hc'

end Faithful

end Entropy.MarginalPhase

end
