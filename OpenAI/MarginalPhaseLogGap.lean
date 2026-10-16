/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseQuantities.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
logarithmic-form portion.
-/
import OpenAI.MarginalPhaseQuadratic

/-! # Logarithmic input of the marginal-phase comparison -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F]

section LogForm

variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty X]

/-- The relative logarithmic form of `M` against `I_X / |X| ⊗ tr_X M`. -/
theorem re_logForm {M : Matrix (X × T) (X × T) ℂ} (hM : M.PosDef)
    (hT : (Matrix.traceLeft M).PosDef) :
    (star (vec (rpowSpec hM (1 / 2))) ⬝ᵥ
      (spectralFun
        (kroneckerUnitary (conjUnitary hM.1.eigenvectorUnitary)
          (kroneckerUnitary 1 hT.1.eigenvectorUnitary))
        (fun p => ((Real.log (hM.1.eigenvalues p.1 ^ (-1 : ℝ) *
          ((Fintype.card X : ℝ)⁻¹ * hT.1.eigenvalues p.2.2)) : ℝ) : ℂ)) *ᵥ
        vec (rpowSpec hM (1 / 2)))).re =
      Arealaw.vonNeumann hM.1 -
        Real.log (Fintype.card X) * M.trace.re -
        Arealaw.vonNeumann hT.1 := by
  set d : ℝ := (Fintype.card X : ℝ)
  have hd : 0 < d := Nat.cast_pos.2 Fintype.card_pos
  set W := hT.1.eigenvectorUnitary
  set W1 := kroneckerUnitary (1 : unitary (Matrix X X ℂ)) W
  set μ := hT.1.eigenvalues
  set LT := spectralFun W (fun k => ((Real.log (μ k) : ℝ) : ℂ))
  have hsplit := spectralFun_leftRight_add hM.1.eigenvectorUnitary W1
    hM.1.eigenvalues (fun p => d⁻¹ * μ p.2)
    (fun t => ((Real.log t : ℝ) : ℂ))
    (fun a => ((-Real.log a : ℝ) : ℂ))
    (fun b => ((Real.log b : ℝ) : ℂ)) (fun k j => by
      have hk := hM.eigenvalues_pos k
      have hj := hT.eigenvalues_pos j.2
      rw [Real.log_mul (Real.rpow_pos_of_pos hk _).ne'
        (mul_pos (inv_pos.2 hd) hj).ne', Real.log_rpow hk]
      push_cast
      ring)
  have hLS : spectralFun W1
      (fun p => ((Real.log (d⁻¹ * μ p.2) : ℝ) : ℂ)) =
      ((-Real.log d : ℝ) : ℂ) • 1 +
        (1 : Matrix X X ℂ) ⊗ₖ LT := by
    rw [← spectralFun_const W1,
      show (1 : Matrix X X ℂ) = spectralFun 1 (fun _ => 1) from
        (spectralFun_one _).symm,
      spectralFun_kronecker, ← spectralFun_add]
    congr 1
    funext p
    have hj := hT.eigenvalues_pos p.2
    simp only [Pi.add_apply, one_mul]
    rw [Real.log_mul (inv_pos.2 hd).ne' hj.ne', Real.log_inv]
    push_cast
    ring
  set NL := spectralFun hM.1.eigenvectorUnitary
    (fun k => ((-Real.log (hM.1.eigenvalues k) : ℝ) : ℂ))
  rw [hsplit, add_mulVec, kronecker_mulVec_vec, kronecker_mulVec_vec,
    transpose_transpose, transpose_one, Matrix.one_mul, Matrix.mul_one,
    dotProduct_add, star_vec_dotProduct_vec, star_vec_dotProduct_vec,
    rpowSpec_isHermitian, hLS, ← Matrix.mul_assoc, rpowSpec_mul,
    ← Matrix.mul_assoc, rpowSpec_mul_mul_rpowSpec_half]
  norm_num only
  rw [rpowSpec_one, Matrix.add_mul, trace_add, Matrix.smul_mul,
    Matrix.one_mul, trace_smul,
    trace_mul_comm ((1 : Matrix X X ℂ) ⊗ₖ LT),
    trace_mul_one_kron_right]
  have h1 : (M * NL).trace =
      ((Arealaw.vonNeumann hM.1 : ℝ) : ℂ) := by
    calc
      (M * NL).trace =
          (spectralFun hM.1.eigenvectorUnitary
            (fun k => ((hM.1.eigenvalues k : ℝ) : ℂ)) * NL).trace := by
        rw [hM.1.spectralFun_eigenvectorUnitary]
      _ = _ := by
        rw [spectralFun_mul, trace_spectralFun,
          Arealaw.vonNeumann_eq_H, Arealaw.H, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Pi.mul_apply, Real.negMulLog]
        push_cast
        ring
  have h2 : (Matrix.traceLeft M * LT).trace =
      ((-Arealaw.vonNeumann hT.1 : ℝ) : ℂ) := by
    calc
      (Matrix.traceLeft M * LT).trace =
          (spectralFun W (fun k => ((μ k : ℝ) : ℂ)) * LT).trace := by
        rw [hT.1.spectralFun_eigenvectorUnitary]
      _ = _ := by
        rw [spectralFun_mul, trace_spectralFun,
          Arealaw.vonNeumann_eq_H, Arealaw.H,
          ← Finset.sum_neg_distrib, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Pi.mul_apply, Real.negMulLog]
        push_cast
        ring
  rw [h1, h2, smul_eq_mul, Complex.add_re, Complex.add_re,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

end LogForm

section FaithfulLog

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
  [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

/-- The logarithmic compression gap is `I(X:F|U)`. -/
theorem compression_logGap :
    (compression hρ).logGap = condMutualInfo ρ hρ.posSemidef := by
  set hs := posDef_marginalXU (F := F) hρ
  have hA : ∑ k, Real.log ((compression hρ).lam k) *
      (compression hρ).weightA k =
      Arealaw.vonNeumann hρ.1 -
        Real.log (Fintype.card X) * ρ.trace.re -
        Arealaw.vonNeumann (posDef_marginalUF hρ).1 := by
    have h := re_logForm hρ (posDef_marginalUF hρ)
    rw [← compression_a0 hρ] at h
    simp only [ResolventCompression.weightA]
    rw [← re_dotProduct_spectralFun_ofReal]
    exact h
  have hB : ∑ j, Real.log ((compression hρ).mu j) *
      (compression hρ).weightB j =
      Arealaw.vonNeumann hs.1 -
        Real.log (Fintype.card X) * ρ.trace.re -
        Arealaw.vonNeumann (posDef_marginalU (F := F) hρ).1 := by
    have h := re_logForm hs (posDef_marginalU (F := F) hρ)
    rw [trace_marginalXU] at h
    simp only [ResolventCompression.weightB]
    rw [← re_dotProduct_spectralFun_ofReal]
    exact h
  have hXU : Arealaw.vonNeumann hs.1 =
      Arealaw.vonNeumann
        ((hρ.posSemidef.submatrix assocE).traceRight.isHermitian) := by
    rfl
  have hUF : Arealaw.vonNeumann (posDef_marginalUF hρ).1 =
      Arealaw.vonNeumann hρ.posSemidef.traceLeft.isHermitian := by
    rfl
  have hU : Arealaw.vonNeumann (posDef_marginalU (F := F) hρ).1 =
      Arealaw.vonNeumann
        ((hρ.posSemidef.submatrix assocE).traceRight.traceLeft.isHermitian) := by
    rfl
  have hfull : Arealaw.vonNeumann hρ.1 =
      Arealaw.vonNeumann hρ.posSemidef.isHermitian := by
    rfl
  rw [ResolventCompression.logGap, hA, hB]
  unfold condMutualInfo
  rw [hXU, hUF, hU, hfull]
  ring

end FaithfulLog

end Entropy.MarginalPhase

end
