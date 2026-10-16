import Arealaw.State

/-!
# Additivity of entanglement entropy over tensor products

The reduced operator of a Kronecker product factors, so its spectrum is the pairwise
products of the factors' spectra, and for normalized states the cut entropy adds.  The
spectrum step is proved by diagonalizing each factor and taking the Kronecker product of
the two diagonalizations, Mathlib having no spectrum-of-Kronecker lemma.
-/

namespace Arealaw

open scoped Kronecker
open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {A₁ B₁ A₂ B₂ : Type*}
  [Fintype A₁] [Fintype B₁] [Fintype A₂] [Fintype B₂]
  [DecidableEq A₁] [DecidableEq A₂]

omit [Fintype A₁] [Fintype A₂] [DecidableEq A₁] [DecidableEq A₂] in
/-- **The reduced operator factors**: `ρ_A(M₁ ⊗ₖ M₂) = ρ_A(M₁) ⊗ₖ ρ_A(M₂)`. -/
theorem rhoA_kronecker (M₁ : Matrix A₁ B₁ 𝕜) (M₂ : Matrix A₂ B₂ 𝕜) :
    rhoA (M₁ ⊗ₖ M₂) = rhoA M₁ ⊗ₖ rhoA M₂ := by
  rw [rhoA, rhoA, rhoA, conjTranspose_kronecker, mul_kronecker_mul]

omit [Fintype A₁] [Fintype A₂] in
/-- The Kronecker product of two real diagonal matrices is the real diagonal matrix of the
pairwise products. -/
theorem diagonal_ofReal_kronecker_diagonal_ofReal (d₁ : A₁ → ℝ) (d₂ : A₂ → ℝ) :
    diagonal (RCLike.ofReal ∘ d₁ : A₁ → 𝕜) ⊗ₖ diagonal (RCLike.ofReal ∘ d₂ : A₂ → 𝕜)
      = diagonal (RCLike.ofReal ∘ (fun p : A₁ × A₂ => d₁ p.1 * d₂ p.2) : A₁ × A₂ → 𝕜) := by
  simp [diagonal_kronecker_diagonal]

/-- **Eigenvalues of a Kronecker product are the pairwise products**: `EE (M₁ ⊗ₖ M₂)` is the
entropy of the product spectrum `(i,j) ↦ d₁ i · d₂ j`. -/
theorem EE_kronecker_eq_H_product (M₁ : Matrix A₁ B₁ 𝕜) (M₂ : Matrix A₂ B₂ 𝕜) : EE (M₁ ⊗ₖ M₂)
      = H (fun p : A₁ × A₂ => (isHermitian_rhoA M₁).eigenvalues p.1 *
          (isHermitian_rhoA M₂).eigenvalues p.2) := by
  have h₁ := isHermitian_rhoA M₁
  have h₂ := isHermitian_rhoA M₂
  have e₁ := h₁.spectral_theorem
  have e₂ := h₂.spectral_theorem
  have hU := Unitary.mem_iff.mp
    (Matrix.kronecker_mem_unitary h₁.eigenvectorUnitary.2 h₂.eigenvectorUnitary.2)
  refine EE_eq_of_unitary_diag hU.1 ?_
  rw [rhoA_kronecker, conjTranspose_kronecker, ← diagonal_ofReal_kronecker_diagonal_ofReal,
    ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at e₁ e₂
  rw [← e₁, ← e₂]

/-- **Entanglement entropy is additive over tensor products**:
`EE (ψ₁ ⊗ₖ ψ₂) = EE ψ₁ + EE ψ₂` for normalized states. -/
theorem EE_kronecker_add (ψ₁ : PureState 𝕜 A₁ B₁) (ψ₂ : PureState 𝕜 A₂ B₂) :
    EE (ψ₁.M ⊗ₖ ψ₂.M) = EE ψ₁.M + EE ψ₂.M :=
  (EE_kronecker_eq_H_product _ _).trans
    (H_mul_add _ _ (sum_eigenvalues_pureState ψ₁) (sum_eigenvalues_pureState ψ₂))

end Arealaw
