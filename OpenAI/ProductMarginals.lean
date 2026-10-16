/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Entropy/ProductMarginals.lean` (Apache 2.0). QICLean's
`Matrix.partialTraceRight`/`partialTraceLeft` are Physlib's `Matrix.traceRight`/`traceLeft`,
and `vonNeumannEntropy ρ hρ` is `Arealaw.vonNeumann hρ`. Added here, being absent from the
repository: `Matrix.log_kronecker_posSemidef` (from `QICLean/Analysis/CfcKronecker.lean`, its
proof rewritten on Physlib's `Matrix.cfc_conj_unitary` and `Matrix.cfc_diagonal`), and
`Arealaw.vonNeumann_eq_neg_trace_mul_log` and
`Matrix.quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log` (from
`QICLean/Analysis/Entropy.lean`).
-/
import OpenAI.MarginalSupportAbsorption
import OpenAI.RootFidelityRelativeEntropy

/-!
# Relative entropy against product marginals

For every positive semidefinite `ρ` on `L × R`,
`D(ρ ‖ ρ_L ⊗ ρ_R) = S(ρ_L) + S(ρ_R) - S(ρ)`, with no invertibility assumption on either
marginal. The logarithm of `ρ_L ⊗ ρ_R` is `log ρ_L ⊗ P_R + P_L ⊗ log ρ_R`
(`Matrix.log_kronecker_posSemidef`), and the support projectors `P_L`, `P_R` are absorbed by
`ρ` (`OpenAI.MarginalSupportAbsorption`).

## References

* Hayden, Jozsa, Petz, Winter, "Structure of states which satisfy strong
  subadditivity of quantum entropy with equality", CMP 246, 359--374 (2004),
  arXiv:quant-ph/0304007v2, p. 3, equation (4).
-/

open scoped Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix

/-- The von Neumann entropy is `-Re tr(ρ log ρ)`, with `log` the continuous functional calculus
logarithm. -/
theorem Arealaw.vonNeumann_eq_neg_trace_mul_log {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    Arealaw.vonNeumann hρ = -(Matrix.trace (ρ * CFC.log ρ)).re := by
  have key : ρ * CFC.log ρ = hρ.cfc (fun x => x * Real.log x) := by
    rw [show CFC.log ρ = hρ.cfc Real.log from by
          rw [CFC.log]; exact Matrix.IsHermitian.cfc_eq hρ Real.log]
    exact hρ.self_mul_cfc Real.log
  rw [Arealaw.vonNeumann, key, map_neg, RCLike.re_eq_complex_re]

namespace Matrix

/-- For Hermitian `ρ`, `D(ρ‖σ) = -S(ρ) - Re tr(ρ log σ)`. -/
theorem quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log
    {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    quantumRelativeEntropy ρ σ =
      -Arealaw.vonNeumann hρ - (Matrix.trace (ρ * CFC.log σ)).re := by
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, Arealaw.vonNeumann_eq_neg_trace_mul_log hρ,
    neg_neg]

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **Logarithm of a Kronecker product on its support.** If $A,B\geq0$, then
\[
  \log(A\otimes B)=(\log A)\otimes P_B+P_A\otimes(\log B),
\]
where $P_A$ and $P_B$ are the orthogonal projections onto the respective
ranges. The logarithm vanishes on the kernel, so the support projections
remove precisely the terms for which $\log(ab)=\log a+\log b$ fails. -/
theorem log_kronecker_posSemidef {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.log (A ⊗ₖ B) =
      (CFC.log A) ⊗ₖ hB.isHermitian.supportProj +
        hA.isHermitian.supportProj ⊗ₖ (CFC.log B) := by
  set evA := hA.isHermitian.eigenvalues with hevA
  set evB := hB.isHermitian.eigenvalues with hevB
  set UA : Matrix m m ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix m m ℂ) with hUA
  set UB : Matrix n n ℂ := (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hUB
  set U : Matrix (m × n) (m × n) ℂ := UA ⊗ₖ UB with hU
  set g : m × n → ℝ := fun p ↦ evA p.1 * evB p.2 with hg
  have hUstar : star U = star UA ⊗ₖ star UB := by
    rw [hU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
  have hUmem : U ∈ Matrix.unitaryGroup (m × n) ℂ :=
    Matrix.kronecker_mem_unitary
      hA.isHermitian.eigenvectorUnitary.2 hB.isHermitian.eigenvectorUnitary.2
  set Uu : Matrix.unitaryGroup (m × n) ℂ := ⟨U, hUmem⟩ with hUu
  have hUuinv : ((Uu⁻¹ : Matrix.unitaryGroup (m × n) ℂ) : Matrix (m × n) (m × n) ℂ) =
      star U := rfl
  have hconj_eq : A ⊗ₖ B = (Uu : Matrix (m × n) (m × n) ℂ) *
      diagonal (fun p ↦ (g p : ℂ)) * (Uu⁻¹ : Matrix.unitaryGroup (m × n) ℂ) := by
    have hAeq := IsHermitian.spectral_form hA.isHermitian
    have hBeq := IsHermitian.spectral_form hB.isHermitian
    rw [hUuinv]
    conv_lhs => rw [hAeq, hBeq]
    rw [show ((Uu : Matrix.unitaryGroup (m × n) ℂ) : Matrix (m × n) (m × n) ℂ) = U from rfl,
      hU, hg, hUstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.kroneckerMap_diagonal_diagonal _ (by intro x; simp) (by intro x; simp)]
    congr 2
    ext p
    push_cast
    ring
  have hlogAB : CFC.log (A ⊗ₖ B) =
      U * diagonal (fun p ↦ ((Real.log (g p) : ℝ) : ℂ)) * star U := by
    have hD : cfc Real.log (diagonal fun p ↦ (g p : ℂ)) =
        diagonal fun p ↦ ((Real.log (g p) : ℝ) : ℂ) :=
      Matrix.cfc_diagonal (𝕜 := ℂ) g Real.log
    rw [CFC.log, hconj_eq, Matrix.cfc_conj_unitary Real.log Uu, hD, hUuinv]
  have hlogA : CFC.log A =
      UA * diagonal (fun i ↦ ((Real.log (evA i) : ℝ) : ℂ)) * star UA := by
    rw [CFC.log, hA.isHermitian.cfc_eq, hA.isHermitian.cfc_form]
  have hlogB : CFC.log B =
      UB * diagonal (fun j ↦ ((Real.log (evB j) : ℝ) : ℂ)) * star UB := by
    rw [CFC.log, hB.isHermitian.cfc_eq, hB.isHermitian.cfc_form]
  have hPA : hA.isHermitian.supportProj =
      UA * diagonal (fun i ↦ if evA i ≠ 0 then (1 : ℂ) else 0) * star UA := rfl
  have hPB : hB.isHermitian.supportProj =
      UB * diagonal (fun j ↦ if evB j ≠ 0 then (1 : ℂ) else 0) * star UB := rfl
  have htermA : (CFC.log A) ⊗ₖ hB.isHermitian.supportProj =
      U * (diagonal (fun i ↦ ((Real.log (evA i) : ℝ) : ℂ)) ⊗ₖ
        diagonal (fun j ↦ if evB j ≠ 0 then (1 : ℂ) else 0)) * star U := by
    rw [hlogA, hPB, hU, hUstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  have htermB : hA.isHermitian.supportProj ⊗ₖ (CFC.log B) =
      U * (diagonal (fun i ↦ if evA i ≠ 0 then (1 : ℂ) else 0) ⊗ₖ
        diagonal (fun j ↦ ((Real.log (evB j) : ℝ) : ℂ))) * star U := by
    rw [hPA, hlogB, hU, hUstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  have hdiag : diagonal (fun p ↦ ((Real.log (g p) : ℝ) : ℂ)) =
      diagonal (fun i ↦ ((Real.log (evA i) : ℝ) : ℂ)) ⊗ₖ
          diagonal (fun j ↦ if evB j ≠ 0 then (1 : ℂ) else 0) +
        diagonal (fun i ↦ if evA i ≠ 0 then (1 : ℂ) else 0) ⊗ₖ
          diagonal (fun j ↦ ((Real.log (evB j) : ℝ) : ℂ)) := by
    rw [Matrix.kroneckerMap_diagonal_diagonal _ (by intro x; simp) (by intro x; simp),
      Matrix.kroneckerMap_diagonal_diagonal _ (by intro x; simp) (by intro x; simp)]
    ext p q
    by_cases hpq : p = q
    · subst q
      simp only [Matrix.diagonal_apply_eq, Matrix.add_apply]
      by_cases ha0 : evA p.1 = 0
      · simp [hg, ha0]
      by_cases hb0 : evB p.2 = 0
      · simp [hg, hb0]
      simp only [ne_eq, ha0, hb0, not_false_eq_true, if_true, mul_one, one_mul, hg,
        Real.log_mul ha0 hb0, Complex.ofReal_add]
    · simp [Matrix.diagonal_apply_ne _ hpq]
  rw [hlogAB, htermA, htermB, hdiag]
  noncomm_ring

end Matrix

/-- **Relative entropy against the product of the marginals.** For every
positive semidefinite bipartite operator $\omega_{XY}$,
\[
  D(\omega_{XY}\,\|\,\omega_X\otimes\omega_Y)
  =S(\omega_X)+S(\omega_Y)-S(\omega_{XY}).
\]
No invertibility assumption is imposed on either marginal: the support
projections in `Matrix.log_kronecker_posSemidef` are absorbed by the joint
operator because each lifted marginal support projection fixes it.

Source: Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, p. 3,
equation (4). -/
theorem quantumRelativeEntropy_product_marginals
    {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    quantumRelativeEntropy ρ (Matrix.traceRight ρ ⊗ₖ Matrix.traceLeft ρ) =
      Arealaw.vonNeumann hρ.traceRight.isHermitian +
        Arealaw.vonNeumann hρ.traceLeft.isHermitian -
        Arealaw.vonNeumann hρ.isHermitian := by
  set ρL := Matrix.traceRight ρ with hρLdef
  set ρR := Matrix.traceLeft ρ with hρRdef
  have hρL : ρL.PosSemidef := hρ.traceRight
  have hρR : ρR.PosSemidef := hρ.traceLeft
  have hPLρ : Matrix.leftKroneckerEmbed (n := R) hρL.isHermitian.supportProj * ρ = ρ :=
    hρ.leftKroneckerEmbed_supportProj_mul_self
  have hPRρ : Matrix.rightKroneckerEmbed (m := L) hρR.isHermitian.supportProj * ρ = ρ :=
    hρ.rightKroneckerEmbed_supportProj_mul_self
  have hcrossL :
      (Matrix.trace (ρ * (CFC.log ρL ⊗ₖ hρR.isHermitian.supportProj))).re =
        (Matrix.trace (ρL * CFC.log ρL)).re := by
    rw [Matrix.trace_mul_comm]
    have hfactor : CFC.log ρL ⊗ₖ hρR.isHermitian.supportProj =
        Matrix.leftKroneckerEmbed (n := R) (CFC.log ρL) *
          Matrix.rightKroneckerEmbed (m := L) hρR.isHermitian.supportProj := by
      rw [Matrix.leftKroneckerEmbed_apply, Matrix.rightKroneckerEmbed_apply,
        ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hfactor, Matrix.mul_assoc, hPRρ, Matrix.trace_leftKroneckerEmbed_mul,
      ← hρLdef, Matrix.trace_mul_comm]
  have hcrossR :
      (Matrix.trace (ρ * (hρL.isHermitian.supportProj ⊗ₖ CFC.log ρR))).re =
        (Matrix.trace (ρR * CFC.log ρR)).re := by
    rw [Matrix.trace_mul_comm]
    have hfactor : hρL.isHermitian.supportProj ⊗ₖ CFC.log ρR =
        Matrix.rightKroneckerEmbed (m := L) (CFC.log ρR) *
          Matrix.leftKroneckerEmbed (n := R) hρL.isHermitian.supportProj := by
      rw [Matrix.leftKroneckerEmbed_apply, Matrix.rightKroneckerEmbed_apply,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    rw [hfactor, Matrix.mul_assoc, hPLρ, Matrix.trace_rightKroneckerEmbed_mul,
      ← hρRdef, Matrix.trace_mul_comm]
  rw [Matrix.quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log hρ.isHermitian,
    Matrix.log_kronecker_posSemidef hρL hρR,
    Matrix.mul_add, Matrix.trace_add, Complex.add_re, hcrossL, hcrossR]
  linarith [Arealaw.vonNeumann_eq_neg_trace_mul_log hρL.isHermitian,
    Arealaw.vonNeumann_eq_neg_trace_mul_log hρR.isHermitian]
