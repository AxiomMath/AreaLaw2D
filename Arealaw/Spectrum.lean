import Arealaw.Entropy
import Arealaw.Mixed

/-!
# Sorted eigenvalues

Mathlib indexes a Hermitian spectrum twice: `IsHermitian.eigenvalues` over the ambient `n`,
and the antitone `IsHermitian.eigenvalues₀` over `Fin (Fintype.card n)`.  The former is
*defined* as the latter precomposed with an arbitrary `Fintype.equivOfCardEq`, so a statement
about the sorted spectrum must be transported across that equivalence.  This file does it
once.

The target paper's bound is a tail sum on the ordered spectrum,
`Σ_{k ≥ 2^{a+l}} λ_k ≤ 2^{-l/8ξ}`, while the entropy is indexing-independent.
-/

namespace Arealaw

open scoped ComplexOrder
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- The entropy does not depend on the eigenvalue indexing. -/
theorem H_eigenvalues_eq_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    H hA.eigenvalues = H hA.eigenvalues₀ :=
  Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm fun k =>
    Real.negMulLog (hA.eigenvalues₀ k)

/-- The sorted eigenvalues sum to the trace. -/
theorem sum_eigenvalues₀_eq_trace {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ((∑ k, hA.eigenvalues₀ k : ℝ) : 𝕜) = A.trace := by
  rw [hA.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
  exact congrArg _ (Equiv.sum_comp _ hA.eigenvalues₀).symm

/-- For a positive semidefinite matrix the sorted eigenvalues are nonnegative. -/
theorem eigenvalues₀_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : Fin (Fintype.card n)) :
    0 ≤ hA.isHermitian.eigenvalues₀ k := by
  simpa [IsHermitian.eigenvalues] using
    hA.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin _) k)

/-- The von Neumann entropy of a state, computed on the sorted spectrum. -/
theorem entropy_eq_H_eigenvalues₀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : SubState ι 𝕜) :
    ρ.entropy = H ρ.psd.isHermitian.eigenvalues₀ := by
  rw [SubState.entropy, vonNeumann_eq_H, H_eigenvalues_eq_eigenvalues₀]

end Arealaw
