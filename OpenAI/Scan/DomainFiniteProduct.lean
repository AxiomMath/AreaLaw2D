/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/TwoFamilies.lean` (Apache 2.0): `reducedState_eq_finiteProduct` and
`regionalEntropy_eq_finiteProduct` only.  Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.
TNLean's `Site Λ` is `↥(Λ : Set (ℤ × ℤ))`, its `StateSpace Λ q` is
`EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and a cut `A : Finset (Site Λ)` is the region
`A.map (Function.Embedding.subtype _) ⊆ Λ`.  TNLean's `reducedState Λ q Ω A` is the partial
trace `ptrace` of `|Ω⟩⟨Ω|` to that region, read in the coordinates `regEquivPiSubtype`, and
`regionalEntropy Λ q Ω A` is `regionEntropy` of `pureState`.  The ordered two-family part of
the source file is Lemma 11.1, `OpenAI.two_family_cancellation`, and is not ported.
-/
import OpenAI.Bridges
import OpenAI.FiniteProductEntropy

/-!
# Regional states of a lattice domain as finite-product reductions

On a finite domain `Λ ⊂ ℤ²` with local dimension `q`, the regional state of a vector `Ω` on a
cut `A` of the sites, computed by the partial trace `ptrace` to the region `A ⊆ Λ`, is the
finite-product reduced pure state `FiniteProduct.reducedPure` of `Ω` on `A`, and the region
entropy of the pure state `|Ω⟩⟨Ω|` is the finite-product entropy `FiniteProduct.entropy`.

## Implementation notes

The region `A.map (Function.Embedding.subtype _)` and the cut `A` index configurations by
different types, so the reduced state is compared after the reindexing `regEquivPiSubtype`.
The region entropy is defined on normalized states only, so the entropy identification assumes
`star Ω ⬝ᵥ Ω = 1`; the identification of the matrices holds for every vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap* (2026), Section 1 and
  Lemma 11.1 (`geometry:cancellation`), source revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI

open Arealaw Matrix
open scoped ComplexOrder

variable (Λ : Finset (ℤ × ℤ)) (q : ℕ)

/-- The domain model's partial trace equals the generic finite-product reduction. -/
theorem reducedState_eq_finiteProduct (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (A : Finset ↥(Λ : Set (ℤ × ℤ))) :
    (ptrace (map_embeddingSubtype_subset (T := Λ) A)
        (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).submatrix
      (regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) A)
        (mem_map_embeddingSubtype_iff A)).symm
      (regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) A)
        (mem_map_embeddingSubtype_iff A)).symm =
      FiniteProduct.reducedPure (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω A := by
  classical
  ext a b
  simp only [submatrix_apply, ptrace, of_apply, FiniteProduct.reducedPure,
    FiniteProduct.reducedMatrix_apply, vecMulVec_apply, Pi.star_apply]
  have hglue (x : FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) A)
      (z : Reg (Qudits q) (Λ \ A.map (Function.Embedding.subtype _))) :
      glue ((regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) A)
        (mem_map_embeddingSubtype_iff A)).symm x) z =
        (FiniteProduct.splitEquiv (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) A).symm
          (x, FiniteProduct.complementEquiv (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) A
            (regSdiffEquivPiSubtype (mem_map_embeddingSubtype_iff A) z)) := by
    rw [← piEquivPiSubtypeProd_symm_regEquivPiSubtype (map_embeddingSubtype_subset A)
      (mem_map_embeddingSubtype_iff A), Equiv.apply_symm_apply]
    rfl
  exact Fintype.sum_equiv ((regSdiffEquivPiSubtype (mem_map_embeddingSubtype_iff A)).trans
    (FiniteProduct.complementEquiv (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) A)) _ _ fun z => by
      rw [Equiv.trans_apply, hglue, hglue]

/-- The finite-domain regional entropy is the finite-product entropy. -/
theorem regionalEntropy_eq_finiteProduct (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (hΩ : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1) (A : Finset ↥(Λ : Set (ℤ × ℤ))) :
    (pureState (WithLp.ofLp Ω) hΩ).regionEntropy (map_embeddingSubtype_subset (T := Λ) A) =
      FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω A := by
  classical
  let e := regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) A)
    (mem_map_embeddingSubtype_iff A)
  let ρ := (pureState (WithLp.ofLp Ω) hΩ).restrict (map_embeddingSubtype_subset (T := Λ) A)
  change vonNeumann ρ.psd.isHermitian = _
  rw [← vonNeumann_submatrix_equiv ρ.psd.isHermitian e.symm, FiniteProduct.entropy]
  exact vonNeumann_congr _ _ (reducedState_eq_finiteProduct Λ q Ω A)

end OpenAI
