/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseFaithful.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
complex-power and phase-gap portion.
-/
import OpenAI.MarginalPhaseCompression

/-! # Concrete form of the faithful marginal phase gap -/

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F]

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
variable [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

/-- Complex spectral power of a positive definite matrix. -/
def cpowSpec {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) : Matrix n n ℂ :=
  spectralFun hA.1.eigenvectorUnitary
    (fun k => ((hA.1.eigenvalues k : ℝ) : ℂ) ^ z)

theorem ofReal_rpow_neg_one_mul_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) :
    (((a ^ (-1 : ℝ) * b : ℝ)) : ℂ) ^ z =
      (a : ℂ) ^ (-z) * (b : ℂ) ^ z := by
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) hb.le,
    Real.rpow_neg_one, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg ha.le]
      exact Real.pi_pos.ne), ← Complex.cpow_neg]

theorem rpowSpec_mul_cpowSpec_mul_rpowSpec
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) :
    rpowSpec hA (1 / 2) * cpowSpec hA z * rpowSpec hA (-1 / 2) =
      cpowSpec hA z := by
  rw [rpowSpec, cpowSpec, rpowSpec, spectralFun_mul, spectralFun_mul]
  congr 1
  funext k
  have hk := hA.eigenvalues_pos k
  simp only [Pi.mul_apply]
  rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hk]
  norm_num

theorem rpowSpec_mul_cpowSpec_comm
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (s : ℝ) (z : ℂ) :
    rpowSpec hA s * cpowSpec hA z = cpowSpec hA z * rpowSpec hA s := by
  rw [rpowSpec, cpowSpec, spectralFun_mul, spectralFun_mul, mul_comm]

/-- The abstract compression phase gap as the concrete marginal-power difference. -/
theorem compression_phaseGap (z : ℂ) :
    (compression hρ).phaseGap z =
      vec ((spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
          (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ z) *
        cpowSpec hρ (-z) -
        embedF (spectralFun
          (sigmaSUnitary (posDef_marginalU (F := F) hρ))
          (fun p => ((sigmaSEig
            (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ z) *
          cpowSpec (posDef_marginalXU (F := F) hρ) (-z))) *
        rpowSpec hρ (1 / 2)) := by
  set hs := posDef_marginalXU (F := F) hρ
  have hA : spectralFun (compression hρ).UA
      (fun k => ((compression hρ).lam k : ℂ) ^ z) =
      (cpowSpec hρ (-z))ᵀ ⊗ₖ
        spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
          (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ z) := by
    refine spectralFun_leftRight_mul _ _ hρ.1.eigenvalues
      (sigmaFEig (posDef_marginalUF hρ))
      (fun t => (t : ℂ) ^ z) (fun a => (a : ℂ) ^ (-z))
      (fun b => (b : ℂ) ^ z) fun k j => ?_
    refine ofReal_rpow_neg_one_mul_cpow (hρ.eigenvalues_pos k) ?_ z
    have h := (posDef_marginalUF hρ).eigenvalues_pos j.2
    unfold sigmaFEig
    have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hB : spectralFun (compression hρ).UB
      (fun k => ((compression hρ).mu k : ℂ) ^ z) =
      (cpowSpec hs (-z))ᵀ ⊗ₖ
        spectralFun (sigmaSUnitary (posDef_marginalU (F := F) hρ))
          (fun p => ((sigmaSEig
            (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ z) := by
    refine spectralFun_leftRight_mul _ _ hs.1.eigenvalues
      (sigmaSEig (posDef_marginalU (F := F) hρ))
      (fun t => (t : ℂ) ^ z) (fun a => (a : ℂ) ^ (-z))
      (fun b => (b : ℂ) ^ z) fun k j => ?_
    refine ofReal_rpow_neg_one_mul_cpow (hs.eigenvalues_pos k) ?_ z
    have h := (posDef_marginalU (F := F) hρ).eigenvalues_pos j.2
    unfold sigmaSEig
    have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    positivity
  set SF := spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
    (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ z)
  set SS := spectralFun (sigmaSUnitary (posDef_marginalU (F := F) hρ))
    (fun p => ((sigmaSEig
      (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ z)
  have h1 : SF * rpowSpec hρ (1 / 2) * cpowSpec hρ (-z) =
      SF * cpowSpec hρ (-z) * rpowSpec hρ (1 / 2) := by
    rw [Matrix.mul_assoc, rpowSpec_mul_cpowSpec_comm, Matrix.mul_assoc]
  have h2 : SS * rpowSpec hs (1 / 2) * cpowSpec hs (-z) *
      rpowSpec hs (-1 / 2) = SS * cpowSpec hs (-z) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (rpowSpec hs (1 / 2)),
      rpowSpec_mul_cpowSpec_mul_rpowSpec]
  rw [ResolventCompression.phaseGap, hA, hB, compression_a0,
    kronecker_mulVec_vec, transpose_transpose]
  change _ - linMatrix (isoMap ρ hρ) *ᵥ
      (_ *ᵥ vec (rpowSpec hs (1 / 2))) = _
  rw [kronecker_mulVec_vec, transpose_transpose, linMatrix_mulVec_vec,
    isoMap_apply, h1, h2, ← vec_sub, Matrix.sub_mul]

end Entropy.MarginalPhase

end
