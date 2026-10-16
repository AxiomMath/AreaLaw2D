/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseFaithful.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
positive-marginal and spectral-power portion.
-/
import OpenAI.MarginalPhaseSetup
import OpenAI.ResolventPhaseBound
import OpenAI.SpectralKronecker
import QuantumInfo.Entropy.SSA

/-! # Spectral powers of faithful three-system marginals -/

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F]

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posDef_marginalUF [Nonempty X] (hρ : ρ.PosDef) :
    (marginalUF ρ).PosDef := by
  classical
  let A : HermitianMat (X × (U × F)) ℂ := ⟨ρ, hρ.1⟩
  change A.traceLeft.mat.PosDef
  exact PosDef_traceLeft A hρ

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posDef_marginalXU [Nonempty F] (hρ : ρ.PosDef) :
    (marginalXU ρ).PosDef := by
  classical
  let A : HermitianMat ((X × U) × F) ℂ :=
    ⟨ρ.submatrix assocE assocE, hρ.1.submatrix assocE⟩
  change A.traceRight.mat.PosDef
  exact PosDef_traceRight A (hρ.submatrix assocE.injective)

theorem posDef_marginalU [Nonempty X] [Nonempty F] (hρ : ρ.PosDef) :
    (marginalU ρ).PosDef := by
  classical
  let A : HermitianMat (X × U) ℂ :=
    ⟨marginalXU ρ, (posDef_marginalXU hρ).1⟩
  change A.traceLeft.mat.PosDef
  exact PosDef_traceLeft A (posDef_marginalXU hρ)

/-- Real spectral power of a positive definite matrix. -/
def rpowSpec {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (s : ℝ) : Matrix n n ℂ :=
  spectralFun hA.1.eigenvectorUnitary
    (fun k => ((hA.1.eigenvalues k ^ s : ℝ) : ℂ))

theorem rpowSpec_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (s t : ℝ) :
    rpowSpec hA s * rpowSpec hA t = rpowSpec hA (s + t) := by
  rw [rpowSpec, rpowSpec, rpowSpec, spectralFun_mul]
  congr 1
  funext k
  simp only [Pi.mul_apply, ← Complex.ofReal_mul,
    ← Real.rpow_add (hA.eigenvalues_pos k)]

theorem rpowSpec_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) : rpowSpec hA 1 = A := by
  rw [rpowSpec]
  simp only [Real.rpow_one]
  exact hA.1.spectralFun_eigenvectorUnitary

theorem rpowSpec_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) : rpowSpec hA 0 = 1 := by
  rw [rpowSpec]
  simp only [Real.rpow_zero, Complex.ofReal_one]
  exact spectralFun_one _

theorem rpowSpec_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (s : ℝ) :
    (rpowSpec hA s)ᴴ = rpowSpec hA s := by
  rw [rpowSpec, conjTranspose_spectralFun]
  congr 1
  funext k
  simp

/-- Eigenbasis of `I_X / |X| ⊗ ρ_UF`. -/
def sigmaFUnitary (hUF : (marginalUF ρ).PosDef) :
    unitary (Matrix (X × (U × F)) (X × (U × F)) ℂ) :=
  kroneckerUnitary 1 hUF.1.eigenvectorUnitary

def sigmaFEig (hUF : (marginalUF ρ).PosDef) (p : X × (U × F)) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * hUF.1.eigenvalues p.2

/-- Eigenbasis of `I_X / |X| ⊗ ρ_U`. -/
def sigmaSUnitary (hU : (marginalU ρ).PosDef) :
    unitary (Matrix (X × U) (X × U) ℂ) :=
  kroneckerUnitary 1 hU.1.eigenvectorUnitary

def sigmaSEig (hU : (marginalU ρ).PosDef) (p : X × U) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * hU.1.eigenvalues p.2

theorem spectralFun_one_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℂ) :
    spectralFun (1 : unitary (Matrix n n ℂ)) (fun _ => c) = c • 1 :=
  spectralFun_const _ _

theorem spectralFun_sigmaF (hUF : (marginalUF ρ).PosDef) :
    spectralFun (sigmaFUnitary hUF) (fun p => (sigmaFEig hUF p : ℂ)) =
      sigmaF ρ := by
  have h := spectralFun_kronecker
    (1 : unitary (Matrix X X ℂ)) hUF.1.eigenvectorUnitary
    (fun _ => ((Fintype.card X : ℂ)⁻¹))
    (fun k => (hUF.1.eigenvalues k : ℂ))
  rw [spectralFun_one_unitary, hUF.1.spectralFun_eigenvectorUnitary] at h
  rw [sigmaF, h, sigmaFUnitary]
  congr 1
  funext p
  simp [sigmaFEig]

omit [DecidableEq F] in
theorem spectralFun_sigmaS (hU : (marginalU ρ).PosDef) :
    spectralFun (sigmaSUnitary hU) (fun p => (sigmaSEig hU p : ℂ)) =
      sigmaS ρ := by
  have h := spectralFun_kronecker
    (1 : unitary (Matrix X X ℂ)) hU.1.eigenvectorUnitary
    (fun _ => ((Fintype.card X : ℂ)⁻¹))
    (fun k => (hU.1.eigenvalues k : ℂ))
  rw [spectralFun_one_unitary, hU.1.spectralFun_eigenvectorUnitary] at h
  rw [sigmaS, h, sigmaSUnitary]
  congr 1
  funext p
  simp [sigmaSEig]

omit [DecidableEq X] [DecidableEq U] [Fintype X] [Fintype U] [Fintype F] in
theorem embedF_add (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (A + B) = embedF A + embedF B := by
  ext i j
  simp [embedF, add_mul]

omit [DecidableEq X] [DecidableEq U] [Fintype X] [Fintype U] [Fintype F] in
theorem embedF_smul (c : ℂ) (A : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (c • A) = c • embedF A := by
  ext i j
  simp [embedF, mul_assoc]

end Entropy.MarginalPhase

end
