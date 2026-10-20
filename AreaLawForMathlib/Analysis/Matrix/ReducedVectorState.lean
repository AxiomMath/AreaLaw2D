import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Reduced states of vectors and quadratic forms

For a vector `u` on `X ≃ X₁ × X₂` the reduced density matrix `Tr₂ |u⟩⟨u|` computes the
expectation of every operator of the form `M₁ ⊗ 1`. It is positive semidefinite with trace
`‖u‖²`, it is invariant under a permutation of `X₁` that `u` intertwines with a permutation of
`X₂`, and it is `‖φ‖² |ψ⟩⟨ψ|` for a product vector `ψ ⊗ φ`.

The file also compares Loewner order and quadratic forms, and bounds the quadratic form of a
positive semidefinite matrix on a sum of `N` vectors by `N` times the sum of the forms.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {X X₁ X₂ : Type*} [Fintype X₂]

/-- The reduced density matrix `Tr₂ |u⟩⟨u|` of a vector along `X ≃ X₁ × X₂`. -/
noncomputable def reducedVec (Φ : X ≃ X₁ × X₂) (u : X → ℂ) : Matrix X₁ X₁ ℂ :=
  Matrix.of fun a b => ∑ z, u (Φ.symm (a, z)) * star (u (Φ.symm (b, z)))

theorem reducedVec_apply (Φ : X ≃ X₁ × X₂) (u : X → ℂ) (a b : X₁) :
    reducedVec Φ u a b = ∑ z, u (Φ.symm (a, z)) * star (u (Φ.symm (b, z))) := rfl

variable [DecidableEq X₂]

/-- The expectation of `M₁ ⊗ 1` in `u` is `Tr (ρ₁ M₁)`, `ρ₁ = Tr₂ |u⟩⟨u|`. -/
theorem dotProduct_mulVec_eq_trace_reducedVec [Fintype X] [Fintype X₁] (Φ : X ≃ X₁ × X₂) (u : X → ℂ)
    {M : Matrix X X ℂ} {M₁ : Matrix X₁ X₁ ℂ}
    (hM : reindex Φ Φ M = M₁ ⊗ₖ (1 : Matrix X₂ X₂ ℂ)) :
    star u ⬝ᵥ (M *ᵥ u) = (reducedVec Φ u * M₁).trace := by
  have hMe : ∀ a z b z', M (Φ.symm (a, z)) (Φ.symm (b, z')) =
      M₁ a b * if z = z' then 1 else 0 := by
    intro a z b z'
    have h := congrFun (congrFun hM (a, z)) (b, z')
    simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, one_apply] at h
    exact h
  have e1 : star u ⬝ᵥ (M *ᵥ u) = ∑ a, ∑ z, ∑ b, ∑ z',
      star (u (Φ.symm (a, z))) * (M (Φ.symm (a, z)) (Φ.symm (b, z')) * u (Φ.symm (b, z'))) := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    rw [← Φ.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, ← Φ.symm.sum_comp, Fintype.sum_prod_type]
  rw [e1]
  simp only [hMe, trace, diag, mul_apply, reducedVec_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

omit [DecidableEq X₂] in
/-- `Tr₂ |u⟩⟨u| = Nᴴ N` with `N z a = conj u(a, z)`; in particular it is positive
semidefinite. -/
theorem posSemidef_reducedVec [Finite X₁] (Φ : X ≃ X₁ × X₂) (u : X → ℂ) :
    (reducedVec Φ u).PosSemidef := by
  have h : reducedVec Φ u = (Matrix.of fun z a => star (u (Φ.symm (a, z))))ᴴ *
      Matrix.of fun z a => star (u (Φ.symm (a, z))) := by
    ext a b
    simp [reducedVec_apply, mul_apply, conjTranspose_apply]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

omit [DecidableEq X₂] in
/-- `Tr Tr₂ |u⟩⟨u| = ‖u‖²`. -/
theorem trace_reducedVec [Fintype X] [Fintype X₁] (Φ : X ≃ X₁ × X₂) (u : X → ℂ) :
    (reducedVec Φ u).trace = star u ⬝ᵥ u := by
  simp only [trace, diag, reducedVec_apply, dotProduct, Pi.star_apply]
  rw [← Fintype.sum_prod_type', ← Φ.symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  simp [mul_comm]

omit [DecidableEq X₂] in
/-- For a product vector `u(a, z) = ψ(a) φ(z)`: `Tr₂ |u⟩⟨u| = ‖φ‖² |ψ⟩⟨ψ|`. -/
theorem reducedVec_of_prod (Φ : X ≃ X₁ × X₂) {u : X → ℂ} {ψ : X₁ → ℂ} {φ : X₂ → ℂ}
    (hu : ∀ a z, u (Φ.symm (a, z)) = ψ a * φ z) :
    reducedVec Φ u = (star φ ⬝ᵥ φ) • vecMulVec ψ (star ψ) := by
  ext a b
  simp only [reducedVec_apply, hu, smul_apply, vecMulVec_apply, dotProduct, Pi.star_apply,
    smul_eq_mul, star_mul', Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

omit [DecidableEq X₂] in
/-- If `u(π a, z) = u(a, τ z)` for permutations `π, τ`, then `Tr₂ |u⟩⟨u|` is `π`-invariant. -/
theorem reducedVec_apply_perm (Φ : X ≃ X₁ × X₂) {u : X → ℂ} (π : Equiv.Perm X₁)
    (τ : Equiv.Perm X₂) (hu : ∀ a z, u (Φ.symm (π a, z)) = u (Φ.symm (a, τ z))) (a b : X₁) :
    reducedVec Φ u (π a) (π b) = reducedVec Φ u a b := by
  simp only [reducedVec_apply, hu]
  exact Equiv.sum_comp τ fun z => u (Φ.symm (a, z)) * star (u (Φ.symm (b, z)))

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- Loewner order from quadratic forms of Hermitian matrices. -/
theorem le_of_re_dotProduct_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, (star x ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ (B *ᵥ x)).re) : A ≤ B := by
  rw [le_iff]
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) fun x => ?_
  have hH : (B - A).IsHermitian := hB.sub hA
  rw [Complex.nonneg_iff]
  constructor
  · rw [sub_mulVec, dotProduct_sub, Complex.sub_re]
    linarith [h x]
  · have := hH.im_star_dotProduct_mulVec_self x
    simpa using this.symm

/-- Quadratic forms are monotone in the Loewner order. -/
theorem re_dotProduct_le_of_le {A B : Matrix n n ℂ} (h : A ≤ B) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ (B *ᵥ x)).re := by
  have h0 := (le_iff.mp h).dotProduct_mulVec_nonneg x
  rw [sub_mulVec, dotProduct_sub] at h0
  have := (Complex.nonneg_iff.mp h0).1
  rw [Complex.sub_re] at this
  linarith

/-- `‖∑_{i ∈ s} vᵢ‖² ≤ |s| ∑_{i ∈ s} ‖vᵢ‖²` for vectors in `ℂⁿ`. -/
theorem re_star_sum_dotProduct_sum_le {ι : Type*} (s : Finset ι) (v : ι → n → ℂ) :
    (star (∑ i ∈ s, v i) ⬝ᵥ ∑ i ∈ s, v i).re ≤ s.card * ∑ i ∈ s, (star (v i) ⬝ᵥ v i).re := by
  have hpt : ∀ x : n, (star (∑ i ∈ s, v i x) * ∑ i ∈ s, v i x).re ≤
      s.card * ∑ i ∈ s, (star (v i x) * v i x).re := by
    intro x
    have hn : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    simp only [hn]
    calc ‖∑ i ∈ s, v i x‖ ^ 2 ≤ (∑ i ∈ s, ‖v i x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ s.card * ∑ i ∈ s, ‖v i x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  simp only [dotProduct, Pi.star_apply, Finset.sum_apply, Complex.re_sum]
  calc ∑ x, (star (∑ i ∈ s, v i x) * ∑ i ∈ s, v i x).re
      ≤ ∑ x, (s.card * ∑ i ∈ s, (star (v i x) * v i x).re) := Finset.sum_le_sum fun x _ => hpt x
    _ = s.card * ∑ i ∈ s, ∑ x, (star (v i x) * v i x).re := by
        rw [← Finset.mul_sum, Finset.sum_comm]

/-- For `M ≥ 0`: `⟨∑ vᵢ, M ∑ vᵢ⟩ ≤ |s| ∑ ⟨vᵢ, M vᵢ⟩` (Cauchy–Schwarz over the sum). -/
theorem re_dotProduct_sum_le_card_mul {M : Matrix n n ℂ} (hM : M.PosSemidef) {ι : Type*}
    (s : Finset ι) (v : ι → n → ℂ) :
    (star (∑ i ∈ s, v i) ⬝ᵥ (M *ᵥ ∑ i ∈ s, v i)).re ≤
      s.card * ∑ i ∈ s, (star (v i) ⬝ᵥ (M *ᵥ v i)).re := by
  classical
  have h0 : 0 ≤ M := nonneg_iff_posSemidef.mpr hM
  set S := CFC.sqrt M
  have hSH : Sᴴ = S := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  have hSS : S * S = M := CFC.sqrt_mul_sqrt_self M h0
  have hq : ∀ w : n → ℂ, star w ⬝ᵥ (M *ᵥ w) = star (S *ᵥ w) ⬝ᵥ (S *ᵥ w) := fun w => by
    rw [← hSS, ← mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, hSH]
  rw [hq]
  simp only [hq]
  rw [mulVec_sum]
  exact re_star_sum_dotProduct_sum_le s fun i => S *ᵥ v i

end Matrix
