import Arealaw.Entropy
import QuantumInfo.ClassicalInfo.Entropy

/-!
# Bridge: Physlib classical entropy

The correspondence between physlib's `Hₛ` and `Arealaw.H`, and the bounds derived from it.

`Hₛ_nonneg` is not adapted: it requires `∑ i, p i = 1`, whereas `Arealaw.entropy_nonneg`
covers the subnormalized case (`RCLike.re M.trace ≤ 1`), which no `ProbDistribution`
expresses.
-/

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
