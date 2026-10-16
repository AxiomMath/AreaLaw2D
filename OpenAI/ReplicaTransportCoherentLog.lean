/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from QICLean, file `QICLean/Representation/ReplicaTransport/CoherentLog.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (final logarithmic-passage section).
-/
import OpenAI.CoherentLogJensen

/-!
# The logarithmic passage from a rank-one pin to every symmetric state

Let `X` be positive definite, commuting with copy permutations, with
`X ≥ e^{φ(θ)} P_{θ,k}` for every unit `θ`. Then for every density matrix `ρ` on `𝒮_k`,
`∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)`.

This file completes the split local port of QICLean's coherent-log module with the compressed
Jensen corollary, the logarithmic passage used by replica transport, and the polynomial bound on
the symmetric-sector dimension loss.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Operator Jensen inequality for the logarithm** (`06-transport.tex`, display
`transport:log-jensen`, lines 526--546), compressed to `𝒮_k`: for continuous `f > 0`,
`Π 𝒬_k(log f) Π ≤ Π log(𝒬_k(f) + (1 - Π)) Π`. -/
theorem coherentAverage_log_le (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) :
    coherentAverage k a (fun θ => Real.log (f θ)) ≤
      symProj (copyPerm Ω k) *
        CFC.log (coherentAverage k a f + (1 - symProj (copyPerm Ω k))) *
          symProj (copyPerm Ω k) := by
  simpa only [one_smul] using coherentAverage_log_le_of_pos k a hf hpos one_pos

/-- **Logarithmic passage** (`06-transport.tex` lines 520--575): a rank-one pin
`X ≥ e^{φ(θ)} P_{θ,k}` for all unit `θ`, with `X` positive definite and commuting with copy
permutations, gives `∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)` for every density matrix `ρ`
on `𝒮_k`. -/
theorem realCoherentIntegral_sub_log_le_re_trace_mul_log {k : ℕ} (a : Ω)
    {X : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hX : X.PosDef)
    (hXc : ∀ s, Commute (permOp (copyPerm Ω k) s) X) {φ : (Ω → ℂ) → ℝ} (hφ : Continuous φ)
    (hpin : ∀ θ : Ω → ℂ, star θ ⬝ᵥ θ = 1 → Real.exp (φ θ) • coherentProj k θ ≤ X)
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    realCoherentIntegral k a ρ φ - Real.log (symDim Ω k) ≤ (ρ * CFC.log X).trace.re := by
  set P := symProj (copyPerm Ω k) with hPdef
  set D : ℕ := symDim Ω k
  have hD : (0 : ℝ) < D := by exact_mod_cast symDim_pos k a
  set μ := unitaryHaar Ω
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  have hfe : Continuous fun θ => Real.exp (φ θ) := Real.continuous_exp.comp hφ
  set Q := coherentAverage k a (fun θ => Real.exp (φ θ))
  have hQX : (X - (D : ℝ)⁻¹ • Q).PosSemidef := by
    have hF := integrable_smul_coherentProj k a hfe
    have e1 : (D : ℝ)⁻¹ • Q =
        ∫ U, ((Real.exp (φ (θ U)) : ℝ) : ℂ) • coherentProj k (θ U) ∂μ := by
      simp only [Q, coherentAverage]
      rw [← Complex.coe_smul, smul_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hD.ne'), one_smul]
    rw [e1, ← Matrix.nonneg_iff_posSemidef]
    have e2 : X = ∫ _U, X ∂μ := by simp
    rw [e2, ← integral_sub (integrable_const X) hF]
    refine integral_nonneg fun U => ?_
    rw [Pi.zero_apply, sub_nonneg, Complex.coe_smul]
    exact hpin _ (star_coherentVec_dotProduct a U)
  have : Nonempty (Fin k → Ω) := ⟨fun _ => a⟩
  obtain ⟨ε, hε, hεX⟩ :=
    (CFC.exists_pos_algebraMap_le_iff (a := X) hX.isHermitian.isSelfAdjoint).mpr
      fun x hx => hX.isStrictlyPositive.spectrum_pos hx
  rw [Algebra.algebraMap_eq_smul_one] at hεX
  have hc : 0 < (D : ℝ) * ε := mul_pos hD hε
  set Y := Q + ((D : ℝ) * ε) • (1 - P)
  have hY : Y.PosDef :=
    posDef_coherentAverage_add_smul k a hfe (fun _ => Real.exp_pos _) hc
  have hPh : P.IsHermitian := isHermitian_symProj (k := k)
  have hPP : P * P = P := symProj_mul_self k
  have hXP : X * P = P * X := by
    simp only [hPdef, symProj, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => ((hXc σ).eq).symm
  have hQP : Q * P = Q := coherentAverage_mul_symProj k a hfe
  have hPQ : P * Q = Q := symProj_mul_coherentAverage k a hfe
  have hYX : (D : ℝ)⁻¹ • Y ≤ X := by
    rw [Matrix.le_iff]
    have e : X - (D : ℝ)⁻¹ • Y = Pᴴ * (X - (D : ℝ)⁻¹ • Q) * P +
        (1 - P)ᴴ * (X - ε • 1) * (1 - P) := by
      rw [conjTranspose_sub, conjTranspose_one, hPh.eq]
      simp only [Y, smul_add, smul_smul, inv_mul_cancel_left₀ hD.ne', mul_sub, sub_mul,
        Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hPP, hQP, hPQ]
      rw [hXP, Matrix.mul_assoc P X P, hXP, ← Matrix.mul_assoc, hPP]
      module
    rw [e]
    exact (hQX.conjTranspose_mul_mul_same P).add
      ((Matrix.le_iff.mp hεX).conjTranspose_mul_mul_same (1 - P))
  have hrY : ((D : ℝ)⁻¹ • Y).PosDef := hY.smul (inv_pos.mpr hD)
  have hlog : CFC.log ((D : ℝ)⁻¹ • Y) ≤ CFC.log X :=
    CFC.log_le_log hYX hrY.isStrictlyPositive
  rw [CFC.log_smul' Y (inv_pos.mpr hD) hY.isStrictlyPositive,
    Algebra.algebraMap_eq_smul_one, Real.log_inv] at hlog
  have hJ := coherentAverage_log_le_of_pos k a hfe (fun _ => Real.exp_pos _) hc
  simp only [Real.log_exp] at hJ
  have hρP : ρ * P = ρ := by
    have h := congrArg conjTranspose hsym
    rwa [conjTranspose_mul, hρ.isHermitian.eq, hPh.eq] at h
  have hmono : ∀ {A B : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}, A ≤ B →
      (ρ * A).trace.re ≤ (ρ * B).trace.re := fun {A B} h => by
    have := (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg (Matrix.le_iff.mp h))).1
    rwa [mul_sub, trace_sub, Complex.sub_re, sub_nonneg] at this
  have h1 := hmono hJ
  have h2 := hmono hlog
  rw [trace_mul_coherentAverage k a hφ] at h1
  have h3 : (ρ * (P * CFC.log Y * P)).trace = (ρ * CFC.log Y).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hρP, trace_mul_comm, ← Matrix.mul_assoc, hsym]
  rw [h3] at h1
  rw [mul_add, trace_add, Complex.add_re, mul_smul_comm, Matrix.mul_one, trace_smul, htr] at h2
  simp only [Complex.real_smul] at h2
  have hscalar : (((( -Real.log (D : ℝ) : ℝ) : ℂ) * 1).re) = -Real.log D := by
    change (-Real.log (D : ℝ)) * 1 - 0 * 0 = -Real.log D
    ring
  rw [hscalar] at h2
  linarith

/-- `D_k` is polynomial in `k`: `log D_k = O(log (k + 1))`. -/
theorem log_symDim_isBigO :
    (fun k : ℕ => Real.log (symDim Ω k)) =O[Filter.atTop] fun k : ℕ => Real.log (k + 1) := by
  refine Asymptotics.IsBigO.of_bound (Fintype.card Ω) (Filter.Eventually.of_forall fun k => ?_)
  have hk : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg _),
    abs_of_nonneg (Real.log_nonneg hk)]
  rcases Nat.eq_zero_or_pos (symDim Ω k) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hk)
  · calc
      Real.log (symDim Ω k) ≤ Real.log (((k + 1) ^ Fintype.card Ω : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast symDim_le k)
      _ = Fintype.card Ω * Real.log (k + 1) := by push_cast; rw [Real.log_pow]

end TensorPower
