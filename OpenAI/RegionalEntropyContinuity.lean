/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/RegionalEntropyContinuity.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`. TNLean's `Site Λ` is
`↥(Λ : Set (ℤ × ℤ))`, its `StateSpace Λ q` is `EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and its
`regionalEntropy Λ q Ω A` is the `regionEntropy` of `OpenAI.pureState` on the region
`A.map (Function.Embedding.subtype _)`, with the normalization `star Ω ⬝ᵥ Ω = 1` supplied from
`‖Ω‖ = 1` by `OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one`. QICLean's
`Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`.
-/
import OpenAI.Scan.DomainFiniteProduct
import OpenAI.FiniteProductContinuity

/-!
# Regional entropy continuity on a finite lattice

For two normalized vectors on the same finite lattice, the entropy change on a fixed region is
bounded by the global trace distance and the number of sites in that region. The dimension
factor is `1 + |A| log q`.

The statement makes no geometric or Hamiltonian assumption and includes empty regions and local
dimension one.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 2.1 (`01-preliminaries.tex`, lines 33–46), as used in `08-scanner.tex`,
  lines 399–404, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI

open Arealaw Matrix

/-- Regional entropy continuity with the dimension of the actual region.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, and its application
in `08-scanner.tex`, lines 399–404. -/
theorem abs_regionalEntropy_sub_le_sqrt_traceDistance
    (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω Φ : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : ‖Ω‖ = 1) (hΦ : ‖Φ‖ = 1)
    (A : Finset ↥(Λ : Set (ℤ × ℤ))) :
    |(pureState (WithLp.ofLp Ω) (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
        (map_embeddingSubtype_subset (T := Λ) A) -
      (pureState (WithLp.ofLp Φ) (star_dotProduct_self_eq_one_of_norm_eq_one hΦ)).regionEntropy
        (map_embeddingSubtype_subset (T := Λ) A)| ≤
      4 * Real.sqrt ((vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) -
        vecMulVec (WithLp.ofLp Φ) (star (WithLp.ofLp Φ))).traceNorm / 2) *
        (1 + (A.card : ℝ) * Real.log q) := by
  have h := FiniteProduct.abs_entropy_sub_le_sqrt_traceDistance
    (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Φ hΩ hΦ A
  have hdim :
      (Fintype.card (FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) A) : ℝ)
        ≠ 0 := by
    have htr := FiniteProduct.trace_reducedPure (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω hΩ A
    have : Nonempty (FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) A) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      simp [Matrix.trace] at htr
    exact_mod_cast Fintype.card_ne_zero
  rw [Real.log_mul (Real.exp_ne_zero 1) hdim] at h
  rw [regionalEntropy_eq_finiteProduct, regionalEntropy_eq_finiteProduct]
  simpa [Nat.cast_pow, Real.log_pow] using h

end OpenAI
