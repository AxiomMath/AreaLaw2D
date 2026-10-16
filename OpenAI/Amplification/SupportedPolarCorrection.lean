/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/SupportedPolarCorrection.lean` (Apache 2.0), with four
declarations of `TNLean/PEPS/Approximation/SheetSplitting.lean` at the same commit.
Adaptations:
* Encoding.  TNLean's sites `ι` with configurations `ι → Fin q` are a finite site type `V` with
  local alphabets `β : V → Type*` (TNLean is the case `β = fun _ => Fin q`); states stay in the
  finite-product space `EuclideanSpace ℂ ((v : V) → β v)` of `OpenAI.FiniteProductEntropy`, so
  that `FiniteProduct.mutualInformation` applies unchanged.  TNLean's
  `U ∈ QuantumCircuit.supportedOperators q S` is
  `OpenAI.IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv)`, the
  repository's support predicate after the canonical identification `Arealaw.univEquiv` of
  `Reg β univ` with `(v : V) → β v`.  The ancilla instantiation (TNLean `AncillaSites Λ X`)
  and the consumers `AmplificationProofSteps`, `AmplificationProof` follow this spelling.
* Set disjointness `Disjoint (S : Set ι) (X : Set ι)` is Finset disjointness `Disjoint S X`.
* `QuantumCircuit.embedOp_val_eq_kronecker_one_submatrix` is
  `OpenAI.extendId_submatrix_univEquiv_symm` (TNLean `embedOp` is `Arealaw.extendId`);
  `QuantumCircuit.kronecker_one_submatrix_mem_supportedOperators` and SheetSplitting's
  `EncodedFrame.exists_kronecker_one_of_mem_supportedOperators` are the two directions of
  `OpenAI.isSupportedOn_submatrix_univEquiv_iff`; SheetSplitting's
  `EncodedFrame.exists_one_kronecker_of_mem_supportedOperators` is
  `OpenAI.exists_one_kronecker_of_isSupportedOn`;
  `exists_one_kronecker_unitary_of_mem_supportedOperators` is
  `OpenAI.exists_one_kronecker_unitary_of_isSupportedOn`.  SheetSplitting's
  `sheetSplit q S` is `FiniteProduct.splitEquiv β S`, and `rectKronecker_submatrix_sheetSplit`
  is not needed, since `IsSupportedOn` is defined through `extendId` rather than a span of
  product operators.
* The support lemmas are stated over `RCLike 𝕜`; the unitary and entropy statements are over
  `ℂ`, as `OpenAI.exists_unitary_kronecker_sub_le_of_good_realization` and
  `FiniteProduct.mutualInformation` are.  `nonempty_of_norm_eq_one` is stated for every finite
  index type and every `RCLike 𝕜`.
-/
import OpenAI.RegionLift
import OpenAI.FiniteProductChannel
import OpenAI.MatrixKroneckerContraction
import OpenAI.Amplification.GoodRealizationUnitary
import OpenAI.Amplification.EntropyComparison

/-!
# The local unitary of a good realization, on a set of sites

The deterministic steps after the choice of a good clock realization produce a unitary
`U` on a local factor `n` of a product `n × m` with `‖(U ⊗ 1) φ - η‖` small. On a
finite set of sites `V` with local alphabets `β`, the local factor is the set of
configurations of a region `S`. This module restates the result in that form: if the
restoring operator `R₀` and the truncated product `L'` act on `S`, the unitary acts on
`S` as well.  A unitary acting on a set disjoint from two regions `X, J` leaves their joint
reduction unchanged, which gives the final entropy comparison.

## Main statements

* `OpenAI.isSupportedOn_submatrix_univEquiv_iff`: an operator acts on `S` exactly when it is
  `K ⊗ 1` in the coordinates of `S` and its complement.
* `OpenAI.exists_supported_unitary_of_good_realization`: the unitary of
  `eq:amplification-unitary-error`, acting on `S`.
* `OpenAI.mutualInformation_le_inv_pow_of_supported_unitary`: the entropy comparison of
  `eq:amplification-output` for a unitary acting away from both regions.

## Implementation notes

An operator on the finite-product space `(v : V) → β v` is supported on `S` when
`IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv)`: the support predicate
of regions, read on the whole site set through `Arealaw.univEquiv`.  The configurations of
`univ \ S` and of `Sᶜ` coincide definitionally, so `extendId` and the split
`FiniteProduct.splitEquiv β S` are compared without a further reindexing.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 501–555, equations `eq:amplification-before-polar`,
  `eq:amplification-direct-error` and `eq:amplification-unitary-error`: the operator `R'`
  is supported on `s'` and `N_{2r}(S₀)`, and its polar unitary is tensored with the
  identity elsewhere.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix Arealaw
open scoped Kronecker Matrix.Norms.L2Operator

namespace OpenAI

open FiniteProduct

section Support

variable {V : Type*} [Fintype V] [DecidableEq V] {β : V → Type*} [∀ v, DecidableEq (β v)]
  {𝕜 : Type*} [RCLike 𝕜]

/-- An operator extended by the identity from a region `S` is `K ⊗ 1` in the coordinates of
`S` and its complement. -/
theorem extendId_submatrix_univEquiv_symm (S : Finset V)
    (A : Matrix (Configuration β S) (Configuration β S) 𝕜) :
    (extendId (Finset.subset_univ S) A).submatrix univEquiv.symm univEquiv.symm =
      (A ⊗ₖ (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) 𝕜)).submatrix
        (FiniteProduct.splitEquiv β S) (FiniteProduct.splitEquiv β S) := by
  ext x y
  simp only [extendId, restr, submatrix_apply, of_apply, kroneckerMap_apply, one_apply]
  change (if (FiniteProduct.splitEquiv β S x).2 = (FiniteProduct.splitEquiv β S y).2 then
    A (FiniteProduct.splitEquiv β S x).1 (FiniteProduct.splitEquiv β S y).1 else 0) = _
  split_ifs <;> simp

/-- An operator on the finite-product space acts on `S` exactly when it is `K ⊗ 1` in the
coordinates of `S` and its complement. -/
theorem isSupportedOn_submatrix_univEquiv_iff (S : Finset V)
    (U : Matrix ((v : V) → β v) ((v : V) → β v) 𝕜) :
    IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv) ↔
      ∃ U' : Matrix (Configuration β S) (Configuration β S) 𝕜,
        U.submatrix (FiniteProduct.splitEquiv β S).symm (FiniteProduct.splitEquiv β S).symm =
          U' ⊗ₖ (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) 𝕜) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    have hU : U = (U.submatrix univEquiv univEquiv).submatrix univEquiv.symm univEquiv.symm := by
      simp
    rw [hU, hB, extendId_submatrix_univEquiv_symm]
    simp
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    have hU : U = (U.submatrix (FiniteProduct.splitEquiv β S).symm
        (FiniteProduct.splitEquiv β S).symm).submatrix (FiniteProduct.splitEquiv β S)
          (FiniteProduct.splitEquiv β S) := by
      simp
    rw [hU, hB, ← extendId_submatrix_univEquiv_symm]
    simp

/-- An operator acting on a set disjoint from `X` is `1 ⊗ K` in the coordinates of `X` and its
complement. -/
theorem exists_one_kronecker_of_isSupportedOn {S X : Finset V} (hSX : Disjoint S X)
    {U : Matrix ((v : V) → β v) ((v : V) → β v) 𝕜}
    (hU : IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv)) :
    ∃ U' : Matrix (Configuration β Xᶜ) (Configuration β Xᶜ) 𝕜,
      U.submatrix (FiniteProduct.splitEquiv β X).symm (FiniteProduct.splitEquiv β X).symm =
        (1 : Matrix (Configuration β X) (Configuration β X) 𝕜) ⊗ₖ U' := by
  obtain ⟨U', hU'⟩ := (isSupportedOn_submatrix_univEquiv_iff Xᶜ U).1
    (hU.mono (Finset.subset_compl_iff_disjoint_right.mpr hSX) (Finset.subset_univ _))
  refine ⟨U', ?_⟩
  have hfst (x : Configuration β X) (y : Configuration β Xᶜ) :
      (FiniteProduct.splitEquiv β Xᶜ ((FiniteProduct.splitEquiv β X).symm (x, y))).1 = y := by
    funext v
    simp [splitEquiv_symm_apply_of_notMem _ _ _ _ _ (Finset.mem_compl.mp v.2)]
  have hsnd (x : Configuration β X) (y : Configuration β Xᶜ) :
      (FiniteProduct.splitEquiv β Xᶜ ((FiniteProduct.splitEquiv β X).symm (x, y))).2 =
        configurationCongr β (compl_compl X).symm x := by
    funext v
    have hv : (v : V) ∈ X := by simpa using v.2
    simp [splitEquiv_symm_apply_of_mem _ _ _ _ _ hv]
  ext ⟨x, y⟩ ⟨x', y'⟩
  have h := congrFun (congrFun hU' (FiniteProduct.splitEquiv β Xᶜ
    ((FiniteProduct.splitEquiv β X).symm (x, y)))) (FiniteProduct.splitEquiv β Xᶜ
      ((FiniteProduct.splitEquiv β X).symm (x', y')))
  simp only [submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply, hfst] at h
  rw [hsnd, hsnd, one_apply] at h
  simp only [EmbeddingLike.apply_eq_iff_eq] at h
  simp only [submatrix_apply, kroneckerMap_apply, h, one_apply]
  split_ifs <;> simp

end Support

section Polar

variable {V : Type*} [Fintype V] [DecidableEq V] {β : V → Type*} [∀ v, Fintype (β v)]
  [∀ v, DecidableEq (β v)]

/-- **The local unitary of a good realization, on a set of sites.** Let `R₀` and `L'` act on
a region `S`, and let `D, D_ret` be arbitrary. For unit vectors `φ, η`, suppose the ground
component `g` of `ζ = R₀ φ` is fixed by `D` with `‖g‖ ≤ 1`, `‖ζ‖ ≤ M₀`, the excited
component, the omitted events and `M₀` times the truncation error are at most `ε`, and the
adjoint error of `L' R₀` is at most `a`. Then some unitary `U` acting on `S` satisfies
`‖U φ - η‖ ≤ a + √(2a + 6ε + 9ε²)`.
Source: `09-amplification.tex`, lines 501–545. -/
theorem exists_supported_unitary_of_good_realization (S : Finset V)
    {R₀ L' D Dret : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hR₀ : IsSupportedOn (Finset.subset_univ S) (R₀.submatrix univEquiv univEquiv))
    (hL : IsSupportedOn (Finset.subset_univ S) (L'.submatrix univEquiv univEquiv))
    {φ η g : ((v : V) → β v) → ℂ} (hφ : ‖WithLp.toLp 2 φ‖ = 1) (hη : ‖WithLp.toLp 2 η‖ = 1)
    {M₀ ε a : ℝ} (hζ : ‖WithLp.toLp 2 (R₀ *ᵥ φ)‖ ≤ M₀) (hg : D *ᵥ g = g)
    (hgn : ‖WithLp.toLp 2 g‖ ≤ 1) (hexc : ‖WithLp.toLp 2 (D *ᵥ (R₀ *ᵥ φ - g))‖ ≤ ε)
    (hret : ‖WithLp.toLp 2 ((D - Dret) *ᵥ (R₀ *ᵥ φ))‖ ≤ ε) (htrunc : M₀ * ‖Dret - L'‖ ≤ ε)
    (hadj : ‖WithLp.toLp 2 ((L' * R₀)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ ≤ a) :
    ∃ U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ,
      IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv) ∧
      Uᴴ * U = 1 ∧ ‖WithLp.toLp 2 (U *ᵥ φ) - WithLp.toLp 2 η‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  set e := FiniteProduct.splitEquiv β S with he
  obtain ⟨R', hR'⟩ := (isSupportedOn_submatrix_univEquiv_iff S R₀).1 hR₀
  obtain ⟨L'', hL''⟩ := (isSupportedOn_submatrix_univEquiv_iff S L').1 hL
  -- Transport of vectors and matrices to the coordinates `S × Sᶜ`.
  have hvec (A : Matrix ((v : V) → β v) ((v : V) → β v) ℂ) (v : ((v : V) → β v) → ℂ) :
      A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
    rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hnorm (v : ((v : V) → β v) → ℂ) : ‖WithLp.toLp 2 (v ∘ e.symm)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv e.symm v
  have hcomp (f h : ((v : V) → β v) → ℂ) : (f - h) ∘ e.symm = f ∘ e.symm - h ∘ e.symm := rfl
  have hsubS (A B : Matrix ((v : V) → β v) ((v : V) → β v) ℂ) :
      A.submatrix e.symm e.symm - B.submatrix e.symm e.symm = (A - B).submatrix e.symm e.symm :=
    rfl
  have hRφ : (R' ⊗ₖ (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ)) *ᵥ (φ ∘ e.symm) =
      (R₀ *ᵥ φ) ∘ e.symm := by rw [← hR', hvec]
  have hprod : (L'' * R') ⊗ₖ (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ) =
      (L' * R₀).submatrix e.symm e.symm := by
    rw [← submatrix_mul_equiv _ _ _ e.symm, hR', hL'', ← mul_kronecker_mul, Matrix.one_mul]
  obtain ⟨U, hU⟩ := exists_unitary_kronecker_sub_le_of_good_realization
    (φ := WithLp.toLp 2 (φ ∘ e.symm)) (η := WithLp.toLp 2 (η ∘ e.symm))
    (g := WithLp.toLp 2 (g ∘ e.symm)) (D := D.submatrix e.symm e.symm)
    (Dret := Dret.submatrix e.symm e.symm) (M₀ := M₀) (ε := ε) (a := a) R' L''
    (by rw [hnorm]; exact hφ) (by rw [hnorm]; exact hη)
    (by rw [toEuclideanCLM_toLp, hRφ, hnorm]; exact hζ)
    (by rw [toEuclideanCLM_toLp, hvec, hg])
    (by rw [hnorm]; exact hgn)
    (by
      have e1 : toEuclideanCLM (𝕜 := ℂ) (D.submatrix e.symm e.symm) (toEuclideanCLM (𝕜 := ℂ)
          (R' ⊗ₖ (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ))
            (WithLp.toLp 2 (φ ∘ e.symm)) - WithLp.toLp 2 (g ∘ e.symm)) =
          WithLp.toLp 2 ((D *ᵥ (R₀ *ᵥ φ - g)) ∘ e.symm) := by
        apply WithLp.ofLp_injective 2
        simp only [ofLp_toEuclideanCLM, WithLp.ofLp_sub, hRφ, ← hcomp, hvec]
      rw [e1, hnorm]
      exact hexc)
    (by
      have e1 : toEuclideanCLM (𝕜 := ℂ) (D.submatrix e.symm e.symm - Dret.submatrix e.symm e.symm)
          (toEuclideanCLM (𝕜 := ℂ)
            (R' ⊗ₖ (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ))
            (WithLp.toLp 2 (φ ∘ e.symm))) =
          WithLp.toLp 2 (((D - Dret) *ᵥ (R₀ *ᵥ φ)) ∘ e.symm) := by
        apply WithLp.ofLp_injective 2
        simp only [ofLp_toEuclideanCLM, hRφ, hsubS, hvec]
      rw [e1, hnorm]
      exact hret)
    (by
      rw [← hL'', hsubS, l2_opNorm_toEuclideanCLM, l2_opNorm_submatrix]
      exact htrunc)
    (by
      rw [hprod, conjTranspose_submatrix, toEuclideanCLM_toLp, hvec, ← WithLp.toLp_sub,
        ← hcomp, hnorm, WithLp.toLp_sub]
      exact hadj)
  have hu : (U : Matrix (Configuration β S) (Configuration β S) ℂ)ᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self U
  refine ⟨((U : Matrix (Configuration β S) (Configuration β S) ℂ) ⊗ₖ
    (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ)).submatrix e e,
    (isSupportedOn_submatrix_univEquiv_iff S _).2 ⟨U, by simp [e]⟩, ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e, conjTranspose_kronecker,
      ← mul_kronecker_mul, hu, conjTranspose_one, Matrix.one_mul, one_kronecker_one,
      submatrix_one_equiv]
  · have hUe : (((U : Matrix (Configuration β S) (Configuration β S) ℂ) ⊗ₖ
        (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ)).submatrix e e).submatrix
          e.symm e.symm = (U : Matrix (Configuration β S) (Configuration β S) ℂ) ⊗ₖ
            (1 : Matrix (Configuration β Sᶜ) (Configuration β Sᶜ) ℂ) := by
      simp
    rw [← WithLp.toLp_sub, ← hnorm, hcomp, ← hvec, hUe, WithLp.toLp_sub]
    simpa only [toEuclideanCLM_toLp] using hU

/-- **A unitary acting away from a region.** Let `U` be a unitary acting on a set `S` disjoint
from a region `X`, on a nonempty configuration space. Then `U = 1 ⊗ U₂` in the coordinates of
`X` and its complement, for a unitary `U₂` on the complement.  Without a configuration the
second factor of `1 ⊗ U₂` cannot be read off, and the space must be nonempty.
Source: `09-amplification.tex`, lines 547–550. -/
theorem exists_one_kronecker_unitary_of_isSupportedOn [Nonempty ((v : V) → β v)]
    {X S : Finset V} (hS : Disjoint S X) {U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hU : IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv))
    (hUu : Uᴴ * U = 1) :
    ∃ U₂ : Matrix (Configuration β Xᶜ) (Configuration β Xᶜ) ℂ,
      U = ((1 : Matrix (Configuration β X) (Configuration β X) ℂ) ⊗ₖ U₂).submatrix
          (FiniteProduct.splitEquiv β X) (FiniteProduct.splitEquiv β X) ∧ U₂ᴴ * U₂ = 1 := by
  obtain ⟨U₂, hU₂⟩ := exists_one_kronecker_of_isSupportedOn hS hU
  set e := FiniteProduct.splitEquiv β X with he
  have hUeq : U = ((1 : Matrix (Configuration β X) (Configuration β X) ℂ) ⊗ₖ U₂).submatrix e e := by
    rw [← hU₂]
    simp
  refine ⟨U₂, hUeq, ?_⟩
  have h1 : ((1 : Matrix (Configuration β X) (Configuration β X) ℂ) ⊗ₖ
        (U₂ᴴ * U₂)).submatrix e e = 1 := by
    rw [← hUu, hUeq, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  have h2 : (1 : Matrix (Configuration β X) (Configuration β X) ℂ) ⊗ₖ (U₂ᴴ * U₂) = 1 := by
    simpa using congrArg (fun A => A.submatrix e.symm e.symm) h1
  obtain ⟨c⟩ := ‹Nonempty ((v : V) → β v)›
  ext i j
  have hij := congrFun (congrFun h2 ((e c).1, i)) ((e c).1, j)
  simpa [kroneckerMap_apply, one_apply] using hij

/-- A unit vector lives on a nonempty index type. -/
theorem nonempty_of_norm_eq_one {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] {φ : EuclideanSpace 𝕜 n}
    (hφ : ‖φ‖ = 1) : Nonempty n := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hz : φ = 0 := by
    ext c
    exact (IsEmpty.false c).elim
  rw [hz, norm_zero] at hφ
  exact zero_ne_one hφ

/-- **The entropy comparison for a unitary acting away from both regions.** Let `U` be a
unitary acting on a region `S` disjoint from `X ∪ J`, and let `η` be a unit vector with
`I_η(X : J) = 0`. Every unit vector `φ` then satisfies
`I_φ(X : J) ≤ 8 √‖U φ - η‖ log(e dim X)`. Only the dimension of `X` enters.
Source: `09-amplification.tex`, lines 547–555, and `02-information.tex`, lines 600–630. -/
theorem mutualInformation_le_of_supported_unitary
    {φ η : EuclideanSpace ℂ ((v : V) → β v)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset V} (hXJ : Disjoint X J) (hS : Disjoint S (X ∪ J))
    {U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hU : IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv))
    (hUu : Uᴴ * U = 1) (hprod : mutualInformation β η X J = 0) :
    mutualInformation β φ X J ≤
      8 * √‖WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) - η‖ *
        Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := by
  have := nonempty_of_norm_eq_one hφ
  obtain ⟨U₂, hUeq, hU₂u⟩ := exists_one_kronecker_unitary_of_isSupportedOn hS hU hUu
  have h := mutualInformation_le_of_unitary_sub_le β hφ hη hXJ U₂ hU₂u hprod
  have hφ' : toEuclideanCLM (n := (v : V) → β v) (𝕜 := ℂ) U φ =
      WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) := by
    rw [← toEuclideanCLM_toLp, WithLp.toLp_ofLp]
  rw [← hUeq, hφ'] at h
  exact h

/-- **The entropy comparison for a unitary acting away from both regions.** Let `U` be a
unitary acting on a region `S` disjoint from `X ∪ J`, and let `η` be a unit vector with
`I_η(X : J) = 0`. If `‖U φ - η‖ ≤ C₁ n^(-K/2)` with `K ≥ 4(M + 2)` and `log dim X ≤ C₂ n²`,
then every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` with `J` in
the unit vector `φ`. Source: `09-amplification.tex`, lines 547–561. -/
theorem mutualInformation_le_inv_pow_of_supported_unitary
    {φ η : EuclideanSpace ℂ ((v : V) → β v)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset V} (hXJ : Disjoint X J) (hS : Disjoint S (X ∪ J))
    {U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hU : IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv))
    (hUu : Uᴴ * U = 1) (hprod : mutualInformation β η X J = 0)
    {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n) (hK : 4 * (M + 2) ≤ K)
    (hδ : ‖WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) - η‖ ≤ C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : Real.log (Fintype.card (Configuration β X)) ≤ C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, mutualInformation β φ X' J ≤ 8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  have := nonempty_of_norm_eq_one hφ
  obtain ⟨U₂, hUeq, hU₂u⟩ := exists_one_kronecker_unitary_of_isSupportedOn hS hU hUu
  refine mutualInformation_le_inv_pow_of_unitary_sub_le β hφ hη hXJ U₂ hU₂u hprod hn hK ?_ hdim
  have hφ' : toEuclideanCLM (n := (v : V) → β v) (𝕜 := ℂ) U φ =
      WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) := by
    rw [← toEuclideanCLM_toLp, WithLp.toLp_ofLp]
  rw [← hUeq, hφ']
  exact hδ

end Polar

end OpenAI
