/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/Circuit/SupportedMatrixElements.lean` (Apache 2.0).  Adapted from TNLean's
`QuantumCircuit.supportedOperators` on `ι → Fin d` over `ℂ` to `OpenAI.IsSupportedOn` on
`Reg loc T` over any `RCLike` field; the product-vector and expectation lemmas are not ported.
-/
import OpenAI.RegionLift

/-!
# Computational-basis entries of supported operators

An operator on a region `T` supported in `S ⊆ T` has zero matrix elements between
configurations that differ at a site of `T \ S`.  Hence the diagonal entry of a product of two
operators supported in disjoint subregions is the product of their diagonal entries: an
intermediate configuration contributing to `(A B)_{ww}` agrees with `w` off `S` and off `S'`,
that is everywhere.

## Implementation notes

TNLean states these facts for the span `QuantumCircuit.supportedOperators` of product operators,
which is `OpenAI.IsSupportedOn` by `OpenAI.isSupportedOn_iff_mem_span`.  TNLean derives the
diagonal factorization from the expectation in the product vector `⊗ᵢ e_{wᵢ}`; here it follows
from the vanishing of the off-support entries alone.  TNLean's `productVector_single` has no
counterpart, the repository having no product vectors, and its `expect_single` and
`expect_smul_single_add_of_offDiag_zero` are closed by `simp` (and `ring`) once `expect ψ A` is
written `star ψ ⬝ᵥ A *ᵥ ψ`.
-/

namespace OpenAI

open Arealaw Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, DecidableEq (loc i)] {S S' T : Finset σ}

/-- A supported operator cannot change a configuration outside its support. -/
theorem IsSupportedOn.apply_eq_zero {h : S ⊆ T} {A : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hA : IsSupportedOn h A) {w w' : Reg loc T} (hw : ∃ i : T, i.1 ∉ S ∧ w i ≠ w' i) :
    A w w' = 0 := by
  obtain ⟨B, rfl⟩ := hA
  obtain ⟨i, hi, hne⟩ := hw
  rw [extendId_apply, if_neg]
  intro heq
  exact hne (congrFun heq ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩)

variable [∀ i, Fintype (loc i)]

/-- Diagonal entries of products of disjointly supported operators factor. -/
theorem IsSupportedOn.mul_apply_self_of_disjoint {hS : S ⊆ T} {hS' : S' ⊆ T}
    (hSS' : Disjoint S S') {A B : Matrix (Reg loc T) (Reg loc T) 𝕜} (hA : IsSupportedOn hS A)
    (hB : IsSupportedOn hS' B) (w : Reg loc T) : (A * B) w w = A w w * B w w := by
  rw [mul_apply, Finset.sum_eq_single w (fun v _ hv => ?_) (by simp)]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  by_cases hiS : i.1 ∈ S
  · rw [hB.apply_eq_zero ⟨i, Finset.disjoint_left.1 hSS' hiS, hi⟩, mul_zero]
  · rw [hA.apply_eq_zero ⟨i, hiS, Ne.symm hi⟩, zero_mul]

end OpenAI
