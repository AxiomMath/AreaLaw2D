import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators
import QuantumInfo.ClassicalInfo.Entropy
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Shannon entropy of a finite real family, and of a spectrum

Extends Physlib's `QuantumInfo/ClassicalInfo/Entropy.lean` and Mathlib's
`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`: `H p = ∑ i, negMulLog (p i)` for an
arbitrary finite real family (no normalization), which depends only on the multiset of values;
it agrees with Physlib's `Hₛ` on probability vectors. For a positive semidefinite matrix of trace
at most one the eigenvalues lie in `[0, 1]`, so the entropy of the spectrum is nonnegative, and
at most `log (card ι)` for unit trace.
-/
namespace Arealaw

/-- Shannon entropy of a finite real family `p : ι → ℝ`, `H p = ∑ i, -p i · log (p i)`. -/
noncomputable def H {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- `H p` is the sum of `Real.negMulLog` over the multiset of values of `p`. -/
theorem H_eq_multiset_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    H p = (Multiset.map (fun x => Real.negMulLog x) (Finset.univ.val.map p)).sum := by
  rw [H, Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def]

/-- `H` depends only on the multiset of values: if two families have equal value
multisets, their entropies agree. -/
theorem H_eq_of_multiset_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → ℝ} {q : κ → ℝ}
    (h : Finset.univ.val.map p = Finset.univ.val.map q) : H p = H q := by
  rw [H_eq_multiset_sum, H_eq_multiset_sum, h]

/-- **Additivity over a product distribution**: for probability vectors `d₁`, `d₂`, the
entropy of `(i,j) ↦ d₁ i · d₂ j` is `H d₁ + H d₂`. -/
theorem H_mul_add {ι κ : Type*} [Fintype ι] [Fintype κ] (d₁ : ι → ℝ) (d₂ : κ → ℝ)
    (h1 : ∑ i, d₁ i = 1) (h2 : ∑ j, d₂ j = 1) :
    H (fun p : ι × κ => d₁ p.1 * d₂ p.2) = H d₁ + H d₂ := by
  simp [H, Fintype.sum_prod_type, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, h1, h2]

end Arealaw

namespace Arealaw

variable {ι : Type*} [Fintype ι]

/-- **Correspondence with physlib's Shannon entropy.** Physlib's `Hₛ` of a bare family,
bundled as a `ProbDistribution`, is `H`. -/
theorem Hₛ_mk'_eq_H (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    Hₛ (ProbDistribution.mk' p hp hsum) = H p := rfl

/-- Shannon entropy of a probability vector is at most the log of the dimension. -/
theorem H_le_log_card {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    H p ≤ Real.log (Fintype.card ι) := Hₛ_mk'_eq_H p hp hsum ▸ Hₛ_le_log_d _

end Arealaw

namespace Arealaw

open scoped ComplexOrder
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

/-- The real part of the trace equals the sum of eigenvalues. -/
theorem re_trace_eq_sum_eigenvalues {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) :
    RCLike.re M.trace = ∑ i, hM.isHermitian.eigenvalues i := by
  simp [hM.isHermitian.trace_eq_sum_eigenvalues]

/-- Each eigenvalue of a PSD matrix is at most its real trace: the others are nonnegative,
so they can only add. -/
theorem eigenvalues_le_re_trace {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) (i : ι) :
    hM.isHermitian.eigenvalues i ≤ RCLike.re M.trace :=
  (Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)).trans
    (re_trace_eq_sum_eigenvalues hM).ge

/-- Each eigenvalue of a PSD matrix with real trace at most one is at most one. -/
theorem eigenvalues_le_one {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) (htr : RCLike.re M.trace ≤ 1)
    (i : ι) : hM.isHermitian.eigenvalues i ≤ 1 :=
  (eigenvalues_le_re_trace hM i).trans htr

/-- The eigenvalue entropy of a subnormalized PSD matrix is nonnegative. -/
theorem entropy_nonneg {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) (htr : RCLike.re M.trace ≤ 1) :
    0 ≤ H hM.isHermitian.eigenvalues :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (hM.eigenvalues_nonneg i) (eigenvalues_le_one hM htr i)

/-- For a normalized state (unit trace), the eigenvalue entropy is at most the log of
the dimension. -/
theorem entropy_le_log_card {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) (htr : RCLike.re M.trace = 1) :
    H hM.isHermitian.eigenvalues ≤ Real.log (Fintype.card ι) :=
  H_le_log_card hM.eigenvalues_nonneg ((re_trace_eq_sum_eigenvalues hM).symm.trans htr)

end Arealaw
