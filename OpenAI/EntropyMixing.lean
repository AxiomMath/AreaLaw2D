import Arealaw.Fidelity
import Arealaw.VonNeumann
import OpenAI.Embedding
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Scaling and subadditivity of the unnormalized von Neumann entropy

Two facts about `S(A) = -tr(A log A)` for Hermitian, and then positive semidefinite, matrices
of arbitrary trace, used in the proof of Lemma 2.1 of [OAI265] (the Alicki–Fannes–Winter
bound).  The scaling law `S(tA) = t S(A) + η(t) tr A`, with `η(x) = -x log x`, is the identity
`η(tx) = x η(t) + t η(x)` on the spectrum.  Subadditivity `S(A + B) ≤ S(A) + S(B)` for
`A, B ≥ 0` holds first for positive definite summands: `log` is operator monotone, so
`log A ≤ log (A + B)`, and pairing with `A ≥ 0` gives `tr(A log A) ≤ tr(A log(A + B))`; the
same for `B` and a sum give the claim.  The boundary follows by replacing `A, B` with
`A + t, B + t` and letting `t → 0⁺`, the entropy of a shift being continuous in `t`.

## Main statements

* `Arealaw.vonNeumann_smul`: the scaling law.
* `Arealaw.vonNeumann_add_le`: subadditivity of the unnormalized entropy.

## Implementation notes

Mathlib's operator monotonicity of the logarithm, `CFC.log_le_log`, is stated for a
`CStarAlgebra`, and Mathlib makes `Matrix n n 𝕜` one only for `𝕜 = ℂ`
(`Matrix.instCStarAlgebra`).  The positive definite case and the limit are therefore proved
over `ℂ` (`vonNeumann_add_le_of_posDef`, `vonNeumann_add_le_complex`), and
`vonNeumann_add_le` transfers them to `𝕜` through the embedding `OpenAI.toComplex`, which
preserves positive semidefiniteness, sums and the entropy.

The subadditivity argument and the scaling law are ported from QICLean,
`QICLean/Analysis/EntropySubadditivity.lean` at commit `32a5a1a8` (Apache 2.0), itself adapted
from `openai/math` at commit `adc7f1241b42`, file
`lean/OAI/MathematicalPhysics/PEPSMove/EntropyBounds.lean`, declarations
`traceEntropy_smul_real`, `trace_mul_mono_right`, `traceEntropy_add_le_posDef` and
`traceEntropy_add_le`.  The statements here are about `Arealaw.vonNeumann` over a general
`RCLike` field rather than QICLean's complex eigenvalue entropy; the pairing inequality is
derived from `Arealaw.re_trace_mul_nonneg` rather than through a square root; the shifted
entropy is computed as the spectral sum `∑ η(λᵢ + t)` by `vonNeumann_add_smul_one`; and the
`ℂ` result is carried to `𝕜` by the transfer above.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §2, Lemma 2.1.
-/

namespace Arealaw

open Matrix
open scoped ComplexOrder MatrixOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy is `-Re tr(A log A)`, with `log A` the functional calculus. -/
theorem vonNeumann_eq_neg_re_trace_mul_log {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    vonNeumann hA = -RCLike.re (A * cfc Real.log A).trace := by
  have hf : ContinuousOn Real.log (spectrum ℝ A) := (finite_real_spectrum).continuousOn _
  rw [vonNeumann, ← hA.cfc_eq, cfc_mul (fun x => x) Real.log A, cfc_id' ℝ A, map_neg]

/-- The entropy of the shift `A + t` of a Hermitian `A` is `∑ η(λᵢ + t)` over the
eigenvalues `λᵢ` of `A`. -/
theorem vonNeumann_add_smul_one {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : ℝ)
    (h : (A + t • (1 : Matrix n n 𝕜)).IsHermitian) :
    vonNeumann h = ∑ i, Real.negMulLog (hA.eigenvalues i + t) := by
  have hr : cfc (fun x : ℝ => x + t) A = A + t • (1 : Matrix n n 𝕜) := by
    rw [cfc_add_const t (fun x : ℝ => x) A, cfc_id' ℝ A, Algebra.algebraMap_eq_smul_one]
  rw [vonNeumann, ← h.cfc_eq, ← hr, ← cfc_comp (fun x : ℝ => x * Real.log x) (fun x => x + t) A,
    hA.cfc_eq, trace_cfc, map_neg, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.negMulLog]
  ring

omit [DecidableEq n] in
/-- Pairing with a positive semidefinite `A` is monotone: `B ≤ C` gives
`Re tr(A B) ≤ Re tr(A C)`. -/
theorem re_trace_mul_le_re_trace_mul {A B C : Matrix n n 𝕜} (hA : A.PosSemidef) (hBC : B ≤ C) :
    RCLike.re (A * B).trace ≤ RCLike.re (A * C).trace := by
  have h := re_trace_mul_nonneg hA (Matrix.le_iff.mp hBC)
  rwa [Matrix.mul_sub, trace_sub, map_sub, sub_nonneg] at h

/-- **Scaling law of the entropy**: `S(tA) = t S(A) + η(t) Re tr A` for Hermitian `A` and
real `t`. -/
theorem vonNeumann_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : ℝ) :
    vonNeumann (hA.smul_real t) = t * vonNeumann hA + Real.negMulLog t * RCLike.re A.trace := by
  have hc := cfc_comp_const_mul t (fun x : ℝ => x * Real.log x) A
    ((finite_real_spectrum.image _).continuousOn _) hA
  rw [vonNeumann, vonNeumann, ← (hA.smul_real t).cfc_eq, ← hc, hA.cfc_eq,
    hA.trace_eq_sum_eigenvalues, trace_cfc, trace_cfc]
  simp only [map_neg, map_sum, RCLike.ofReal_re]
  simp only [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Real.negMulLog_mul t (hA.eigenvalues i)
  simp only [Real.negMulLog] at h ⊢
  linear_combination h

-- `ℂ` only: `CFC.log_le_log` needs a C⋆-algebra; see the implementation notes.
open scoped Matrix.Norms.L2Operator in
/-- Subadditivity `S(A + B) ≤ S(A) + S(B)` for positive definite complex `A, B`. -/
theorem vonNeumann_add_le_of_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    vonNeumann (hA.posSemidef.add hB.posSemidef).isHermitian ≤
      vonNeumann hA.isHermitian + vonNeumann hB.isHermitian := by
  have ha := re_trace_mul_le_re_trace_mul hA.posSemidef
    (CFC.log_le_log (le_add_of_nonneg_right hB.posSemidef.nonneg) hA.isStrictlyPositive)
  have hb := re_trace_mul_le_re_trace_mul hB.posSemidef
    (CFC.log_le_log (le_add_of_nonneg_left hA.posSemidef.nonneg) hB.isStrictlyPositive)
  rw [vonNeumann_eq_neg_re_trace_mul_log, vonNeumann_eq_neg_re_trace_mul_log,
    vonNeumann_eq_neg_re_trace_mul_log, Matrix.add_mul, trace_add, map_add]
  simp only [CFC.log] at ha hb
  linarith

/-- Subadditivity `S(A + B) ≤ S(A) + S(B)` for positive semidefinite complex `A, B`. -/
theorem vonNeumann_add_le_complex {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    vonNeumann (hA.add hB).isHermitian ≤ vonNeumann hA.isHermitian + vonNeumann hB.isHermitian := by
  let f : ℝ → ℝ := fun t => ∑ i, Real.negMulLog ((hA.add hB).isHermitian.eigenvalues i + 2 * t)
  let g : ℝ → ℝ := fun t => ∑ i, Real.negMulLog (hA.isHermitian.eigenvalues i + t) +
    ∑ i, Real.negMulLog (hB.isHermitian.eigenvalues i + t)
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hle : ∀ t > 0, f t ≤ g t := fun t ht => by
    have hA' := PosDef.posSemidef_add hA (PosDef.one.smul ht)
    have hB' := PosDef.posSemidef_add hB (PosDef.one.smul ht)
    have hh := vonNeumann_add_le_of_posDef hA' hB'
    have e : A + t • (1 : Matrix n n ℂ) + (B + t • 1) = A + B + (2 * t) • 1 := by
      rw [two_mul, add_smul]; abel
    simp only [e] at hh
    rwa [vonNeumann_add_smul_one hA.isHermitian, vonNeumann_add_smul_one hB.isHermitian,
      vonNeumann_add_smul_one (hA.add hB).isHermitian] at hh
  have hh := le_of_tendsto_of_tendsto ((hf.tendsto 0).mono_left nhdsWithin_le_nhds)
    ((hg.tendsto 0).mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioi 0)) hle)
  simpa [f, g, vonNeumann_eq_H, H] using hh

/-- **Subadditivity of the unnormalized entropy**: `S(A + B) ≤ S(A) + S(B)` for positive
semidefinite `A, B`. -/
theorem vonNeumann_add_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    vonNeumann (hA.add hB).isHermitian ≤ vonNeumann hA.isHermitian + vonNeumann hB.isHermitian := by
  have h := vonNeumann_add_le_complex (OpenAI.posSemidef_map_toComplex_iff.2 hA)
    (OpenAI.posSemidef_map_toComplex_iff.2 hB)
  rw [← OpenAI.vonNeumann_map_toComplex, ← OpenAI.vonNeumann_map_toComplex hA.isHermitian,
    ← OpenAI.vonNeumann_map_toComplex hB.isHermitian]
  convert h using 2
  exact OpenAI.map_toComplex_add A B

end Arealaw
