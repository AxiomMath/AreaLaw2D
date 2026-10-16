import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Arealaw.Bridge.Entropy
import Arealaw.Entropy

/-!
# Entropy bounds

The three properties of the eigenvalue entropy that the saturation argument of the target
paper (its Lemma 16) instantiates: eigenvalues of a subnormalized state lie in `[0,1]`, the
entropy is therefore nonnegative, and for a normalized state it is bounded by the log of
the dimension.  The last one is the seed of the volume bound `S(X) ≤ |X| log d`.

The remaining hypothesis of the saturation engine, subadditivity, is not here: it needs
Klein's inequality and is tracked separately.
-/

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
