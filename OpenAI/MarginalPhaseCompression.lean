/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseFaithful.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
Hilbert--Schmidt compression portion.
-/
import OpenAI.MarginalPhasePowers

/-! # The faithful three-system resolvent compression -/

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F]

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
variable [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

variable (ρ) in
/-- `Y ↦ (Y ρ_XU^{-1/2} ⊗ I_F) ρ^{1/2}`. -/
def isoMap (hρ : ρ.PosDef) [Nonempty X] [Nonempty F] :
    Matrix (X × U) (X × U) ℂ →ₗ[ℂ]
      Matrix (X × (U × F)) (X × (U × F)) ℂ where
  toFun Y :=
    embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
      rpowSpec hρ (1 / 2)
  map_add' A B := by
    rw [Matrix.add_mul, embedF_add, Matrix.add_mul]
  map_smul' c A := by
    rw [Matrix.smul_mul, embedF_smul, Matrix.smul_mul]
    rfl

theorem isoMap_apply (Y : Matrix (X × U) (X × U) ℂ) :
    isoMap ρ hρ Y =
      embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        rpowSpec hρ (1 / 2) :=
  rfl

theorem trace_isoMap_conjTranspose_mul
    (Z Y : Matrix (X × U) (X × U) ℂ)
    (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    ((isoMap ρ hρ Z)ᴴ * M * isoMap ρ hρ Y).trace =
      (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
        embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        (rpowSpec hρ (1 / 2) * rpowSpec hρ (1 / 2))).trace := by
  rw [isoMap_apply, isoMap_apply, conjTranspose_mul, conjTranspose_embedF,
    conjTranspose_mul, rpowSpec_isHermitian, rpowSpec_isHermitian]
  rw [show rpowSpec hρ (1 / 2) *
      embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
      (embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        rpowSpec hρ (1 / 2)) =
      rpowSpec hρ (1 / 2) *
        (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
          embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
          rpowSpec hρ (1 / 2)) by simp only [Matrix.mul_assoc]]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The compression map is an isometry. -/
theorem linMatrix_isoMap_isometry :
    (linMatrix (isoMap ρ hρ))ᴴ * linMatrix (isoMap ρ hρ) = 1 := by
  set hs := posDef_marginalXU (F := F) hρ
  refine ext_star_vec_dotProduct_mulVec_vec fun Z Y => ?_
  rw [← mulVec_mulVec, ← star_mulVec_dotProduct, linMatrix_mulVec_vec,
    linMatrix_mulVec_vec, one_mulVec, star_vec_dotProduct_vec,
    star_vec_dotProduct_vec, ← Matrix.mul_one (isoMap ρ hρ Z)ᴴ,
    trace_isoMap_conjTranspose_mul, Matrix.mul_one, embedF_mul, rpowSpec_mul,
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, rpowSpec_one,
    trace_mul_comm, trace_mul_embedF]
  change (marginalXU ρ *
      (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2)))).trace = _
  rw [show marginalXU ρ *
      (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2))) =
      rpowSpec hs 1 *
        (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2))) by
      rw [rpowSpec_one]]
  rw [show rpowSpec hs 1 *
      (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2))) =
      (rpowSpec hs 1 * rpowSpec hs (-1 / 2)) *
        (Zᴴ * Y * rpowSpec hs (-1 / 2)) by
      simp only [Matrix.mul_assoc],
    trace_mul_comm, rpowSpec_mul, Matrix.mul_assoc, rpowSpec_mul]
  norm_num [rpowSpec_zero]

theorem trace_isoMap_conjTranspose_mul_mul
    (Z Y : Matrix (X × U) (X × U) ℂ)
    (M N : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    ((isoMap ρ hρ Z)ᴴ * M * isoMap ρ hρ Y * N).trace =
      (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
        embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        (rpowSpec hρ (1 / 2) * N * rpowSpec hρ (1 / 2))).trace := by
  rw [isoMap_apply, isoMap_apply, conjTranspose_mul, conjTranspose_embedF,
    conjTranspose_mul, rpowSpec_isHermitian, rpowSpec_isHermitian]
  rw [show rpowSpec hρ (1 / 2) *
      embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
      (embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        rpowSpec hρ (1 / 2)) * N =
      rpowSpec hρ (1 / 2) *
        (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
          embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
          rpowSpec hρ (1 / 2) * N) by simp only [Matrix.mul_assoc]]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Eigenbasis of `L_{σ_f} R_{ρ⁻¹}`. -/
def unitaryA : unitary
    (Matrix ((X × (U × F)) × (X × (U × F)))
      ((X × (U × F)) × (X × (U × F))) ℂ) :=
  kroneckerUnitary (conjUnitary hρ.1.eigenvectorUnitary)
    (sigmaFUnitary (posDef_marginalUF hρ))

def eigA (p : (X × (U × F)) × (X × (U × F))) : ℝ :=
  hρ.1.eigenvalues p.1 ^ (-1 : ℝ) *
    sigmaFEig (posDef_marginalUF hρ) p.2

/-- Eigenbasis of `L_{σ_s} R_{ρ_XU⁻¹}`. -/
def unitaryB : unitary
    (Matrix ((X × U) × (X × U)) ((X × U) × (X × U)) ℂ) :=
  kroneckerUnitary
    (conjUnitary (posDef_marginalXU (F := F) hρ).1.eigenvectorUnitary)
    (sigmaSUnitary (posDef_marginalU hρ))

def eigB (p : (X × U) × (X × U)) : ℝ :=
  (posDef_marginalXU (F := F) hρ).1.eigenvalues p.1 ^ (-1 : ℝ) *
    sigmaSEig (posDef_marginalU (F := F) hρ) p.2

omit [Nonempty F] in
theorem spectralFun_eigA :
    spectralFun (unitaryA hρ) (fun p => (eigA hρ p : ℂ)) =
      (rpowSpec hρ (-1))ᵀ ⊗ₖ sigmaF ρ := by
  rw [rpowSpec, transpose_spectralFun,
    ← spectralFun_sigmaF (posDef_marginalUF hρ),
    spectralFun_kronecker, unitaryA]
  congr 1
  funext p
  simp [eigA]

theorem spectralFun_eigB :
    spectralFun (unitaryB hρ) (fun p => (eigB hρ p : ℂ)) =
      (rpowSpec (posDef_marginalXU (F := F) hρ) (-1))ᵀ ⊗ₖ sigmaS ρ := by
  rw [rpowSpec, transpose_spectralFun,
    ← spectralFun_sigmaS (posDef_marginalU hρ),
    spectralFun_kronecker, unitaryB]
  congr 1
  funext p
  simp [eigB]

omit [Nonempty F] in
theorem eigA_pos (p : (X × (U × F)) × (X × (U × F))) :
    0 < eigA hρ p := by
  have h1 := hρ.eigenvalues_pos p.1
  have h2 := (posDef_marginalUF hρ).eigenvalues_pos p.2.2
  unfold eigA sigmaFEig
  have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  positivity

theorem eigB_pos (p : (X × U) × (X × U)) :
    0 < eigB (F := F) hρ p := by
  have h1 := (posDef_marginalXU (F := F) hρ).eigenvalues_pos p.1
  have h2 := (posDef_marginalU (F := F) hρ).eigenvalues_pos p.2.2
  unfold eigB sigmaSEig
  have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  positivity

/-- `Vᴴ A V = B`. -/
theorem linMatrix_isoMap_compress :
    (linMatrix (isoMap ρ hρ))ᴴ *
        spectralFun (unitaryA hρ) (fun p => (eigA hρ p : ℂ)) *
        linMatrix (isoMap ρ hρ) =
      spectralFun (unitaryB hρ) (fun p => (eigB hρ p : ℂ)) := by
  set hs := posDef_marginalXU (F := F) hρ
  refine ext_star_vec_dotProduct_mulVec_vec fun Z Y => ?_
  rw [spectralFun_eigA, spectralFun_eigB, ← mulVec_mulVec,
    ← mulVec_mulVec, ← star_mulVec_dotProduct, linMatrix_mulVec_vec,
    linMatrix_mulVec_vec, kronecker_mulVec_vec, kronecker_mulVec_vec,
    transpose_transpose, transpose_transpose, star_vec_dotProduct_vec,
    star_vec_dotProduct_vec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    trace_isoMap_conjTranspose_mul_mul, rpowSpec_mul, rpowSpec_mul]
  norm_num [rpowSpec_zero]
  rw [trace_mul_comm, ← Matrix.mul_assoc, embedF_mul, trace_mul_comm,
    trace_mul_embedF, traceRight_sigmaF, Matrix.mul_assoc Y,
    ← Matrix.mul_assoc _ _ Zᴴ, rpowSpec_mul]
  norm_num
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]

/-- The faithful-state resolvent compression. -/
def compression : ResolventCompression
    ((X × (U × F)) × (X × (U × F))) ((X × U) × (X × U)) where
  UA := unitaryA hρ
  lam := eigA hρ
  UB := unitaryB hρ
  mu := eigB hρ
  V := linMatrix (isoMap ρ hρ)
  b0 := vec (rpowSpec (posDef_marginalXU hρ) (1 / 2))
  lam_pos := eigA_pos hρ
  mu_pos := eigB_pos hρ
  isometry := linMatrix_isoMap_isometry hρ
  compress := linMatrix_isoMap_compress hρ

theorem compression_a0 :
    (compression hρ).a0 = vec (rpowSpec hρ (1 / 2)) := by
  change linMatrix (isoMap ρ hρ) *ᵥ vec _ = _
  rw [linMatrix_mulVec_vec, isoMap_apply, rpowSpec_mul]
  norm_num [rpowSpec_zero, embedF_one]

end Entropy.MarginalPhase

end
