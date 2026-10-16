import Arealaw.State
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Von Neumann entropy and Brandão–Horodecki Eq. (3)

Brandão–Horodecki (arXiv:1309.3789) define the entanglement of a bipartite pure state as
`E(|ψ⟩_XY) = H(ρ_X) = -tr(ρ_X log ρ_X)`, their Eq. (3).  Our `EE` is the Shannon entropy of
the spectrum of `ρ_A`; this file identifies the two through `trace_cfc`, which reads the
trace of a Hermitian functional-calculus image off the spectrum.
-/

namespace Arealaw

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace-spectrum bridge**: for Hermitian `A` and real `f`, the trace of `f(A)` is
`∑ f(eigenvalueᵢ)`.  Mathlib has `IsHermitian.cfc` and `trace_eq_sum_eigenvalues`, not the
combination. -/
theorem trace_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : 𝕜) := by
  simp [IsHermitian.cfc, trace_mul_cycle]

/-- The von Neumann entropy `-tr(ρ log ρ)` of a Hermitian matrix, the operator form of
Brandão–Horodecki Eq. (3).  Here `ρ log ρ` is the spectral-decomposition matrix
`cfc (x ↦ x·log x) ρ`, whose trace is real, so the real part loses nothing. -/
noncomputable def vonNeumann {ρ : Matrix n n 𝕜} (hρ : ρ.IsHermitian) : ℝ :=
  RCLike.re (-(hρ.cfc (fun x => x * Real.log x)).trace)

/-- The operator definition `-tr(ρ log ρ)` equals the Shannon entropy of the eigenvalues:
`vonNeumann ρ = ∑ negMulLog(eigenvalueᵢ) = H (eigenvalues ρ)`. -/
theorem vonNeumann_eq_H {ρ : Matrix n n 𝕜} (hρ : ρ.IsHermitian) :
    vonNeumann hρ = H hρ.eigenvalues := by
  simp [vonNeumann, trace_cfc, H, Real.negMulLog]

/-- Reindexing a Hermitian matrix leaves its eigenvalue multiset unchanged. -/
theorem eigenvalues_multiset_submatrix_equiv {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (e : m ≃ n) :
    Finset.univ.val.map (hA.submatrix e).eigenvalues = Finset.univ.val.map hA.eigenvalues := by
  refine Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_
  rw [Multiset.map_map, Multiset.map_map, ← (hA.submatrix e).roots_charpoly_eq_eigenvalues,
    ← hA.roots_charpoly_eq_eigenvalues]
  exact congrArg Polynomial.roots (charpoly_reindex e.symm A)

/-- **The von Neumann entropy does not see a relabeling of the index.** -/
theorem vonNeumann_submatrix_equiv {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (e : m ≃ n) : vonNeumann (hA.submatrix e) = vonNeumann hA := by
  -- reindexing fixes the characteristic polynomial, hence the eigenvalue multiset
  simpa [vonNeumann_eq_H] using H_eq_of_multiset_eq (eigenvalues_multiset_submatrix_equiv hA e)

/-- **Brandão–Horodecki Eq. (3)**: `EE M = -tr(ρ_A log ρ_A)`, their `E(|ψ⟩) = H(ρ_X)`. -/
theorem EE_eq_vonNeumann {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (M : Matrix A B 𝕜) :
    EE M = vonNeumann (isHermitian_rhoA M) :=
  (vonNeumann_eq_H _).symm

end Arealaw
