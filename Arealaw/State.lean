import Arealaw.Entropy
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Bipartite pure states and entanglement entropy

A bipartite pure state on `A ⊗ B` is recorded by its coefficient matrix `M : Matrix A B 𝕜`
with `∑ a b, ‖M a b‖² = 1`, its reduced density operator on the `A` side is `ρ_A = M Mᴴ`, and
the entanglement entropy across the `A | B` cut is the Shannon entropy of `ρ_A`'s spectrum.

`EE_eq_of_unitary_diag` computes `EE` from any exhibited diagonalization of `ρ_A`, so the
eigenvalues are never computed explicitly.
-/

namespace Arealaw

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

/-- A bipartite pure state, given by its coefficient matrix together with normalization
`∑ a b, ‖M a b‖² = 1`. -/
structure PureState (𝕜 : Type*) [RCLike 𝕜] (A B : Type*) [Fintype A] [Fintype B] where
  /-- coefficient matrix of the pure state -/
  M : Matrix A B 𝕜
  /-- normalization: the state is a unit vector -/
  normalized : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1

/-- Reduced density operator on the `A` side, `ρ_A = M Mᴴ`. -/
def rhoA (M : Matrix A B 𝕜) : Matrix A A 𝕜 := M * Mᴴ

omit [Fintype A] [DecidableEq A] in
/-- `ρ_A = M Mᴴ` is Hermitian. -/
theorem isHermitian_rhoA (M : Matrix A B 𝕜) : (rhoA M).IsHermitian :=
  isHermitian_mul_conjTranspose_self M

/-- Entanglement entropy across the `A | B` cut: the Shannon entropy of the eigenvalues of
the reduced density operator `ρ_A`. -/
noncomputable def EE (M : Matrix A B 𝕜) : ℝ := H (isHermitian_rhoA M).eigenvalues

omit [Fintype A] in
/-- A real-diagonal matrix `diagonal (ofReal ∘ d)` is Hermitian. -/
theorem isHermitian_diagonal_ofReal (d : A → ℝ) :
    (diagonal (RCLike.ofReal ∘ d : A → 𝕜)).IsHermitian :=
  isHermitian_diagonal_iff.mpr fun i => RCLike.conj_ofReal (d i)

/-- The eigenvalues of `diagonal (ofReal ∘ d)` have the same value-multiset as `d` itself:
the spectrum of a (real) diagonal matrix is exactly its diagonal, up to order. -/
theorem eigenvalues_diagonal_multiset (d : A → ℝ) :
    Finset.univ.val.map (isHermitian_diagonal_ofReal (𝕜 := 𝕜) d).eigenvalues =
      Finset.univ.val.map d := by
  apply Multiset.map_injective (f := (RCLike.ofReal : ℝ → 𝕜)) RCLike.ofReal_injective
  simpa [charpoly_diagonal, Polynomial.roots_prod, Finset.prod_ne_zero_iff,
    Polynomial.X_sub_C_ne_zero] using
    (isHermitian_diagonal_ofReal (𝕜 := 𝕜) d).roots_charpoly_eq_eigenvalues.symm

/-- **A diagonalization computes the entropy**: if `ρ_A = U · diagonal (ofReal ∘ d) · Uᴴ` for
unitary `U` and real `d`, then `EE M = H d`. -/
theorem EE_eq_of_unitary_diag {M : Matrix A B 𝕜} {U : Matrix A A 𝕜} {d : A → ℝ} (hU : Uᴴ * U = 1)
    (hdiag : rhoA M = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) : EE M = H d := by
  have hU' := mul_eq_one_comm.mp hU
  rw [EE, (IsHermitian.eigenvalues_eq_eigenvalues_iff _ (isHermitian_diagonal_ofReal d)).mpr
    (by rw [hdiag, ← inv_eq_right_inv hU', charpoly_units_conj ⟨U, Uᴴ, hU', hU⟩])]
  exact H_eq_of_multiset_eq (eigenvalues_diagonal_multiset d)

/-- Special case `U = 1`: if `ρ_A` is already (real-)diagonal, `EE M = H d`. -/
theorem EE_eq_of_diag {M : Matrix A B 𝕜} {d : A → ℝ}
    (hdiag : rhoA M = diagonal (RCLike.ofReal ∘ d)) : EE M = H d :=
  EE_eq_of_unitary_diag (U := 1) (by simp) (by simpa using hdiag)

/-- **A maximally mixed reduced state carries maximal entanglement**: if `ρ_A = (1/d)·1` on a
`d`-dimensional cut side then `EE M = log d`.  For `d = 2` this is the Bell pair. -/
theorem EE_eq_log_card_of_maxMixed {M : Matrix A B 𝕜} (hpos : 0 < Fintype.card A)
    (hdiag : rhoA M = diagonal (RCLike.ofReal ∘ (fun _ : A => (1 / Fintype.card A : ℝ)))) :
    EE M = Real.log (Fintype.card A) := by
  simp [EE_eq_of_diag hdiag, H, Real.negMulLog, hpos.ne']

/-! ## Trace and normalization

The trace of `ρ_A` is the squared norm of the coefficient matrix, so a normalized state has
a unit-trace reduced operator and its eigenvalues sum to `1`. -/

section Trace
omit [DecidableEq A]

/-- The trace of `ρ_A = M Mᴴ` equals the total squared norm `∑ a b, ‖M a b‖²`. -/
theorem trace_rhoA (M : Matrix A B 𝕜) : (rhoA M).trace = ((∑ a, ∑ b, ‖M a b‖ ^ 2 : ℝ) : 𝕜) := by
  simp [rhoA, trace, mul_apply, RCLike.mul_conj]

/-- For a `PureState`, the reduced operator has unit trace. -/
theorem trace_rhoA_pureState (ψ : PureState 𝕜 A B) : (rhoA ψ.M).trace = 1 := by
  simp [trace_rhoA, ψ.normalized]

end Trace

/-- The eigenvalues of `ρ_A` for a `PureState` sum to `1`: they form a probability vector. -/
theorem sum_eigenvalues_pureState (ψ : PureState 𝕜 A B) :
    ∑ i, (isHermitian_rhoA ψ.M).eigenvalues i = 1 :=
  mod_cast (isHermitian_rhoA ψ.M).trace_eq_sum_eigenvalues.symm.trans (trace_rhoA_pureState ψ)

end Arealaw
