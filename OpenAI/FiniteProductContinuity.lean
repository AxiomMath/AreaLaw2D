/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Entropy/FiniteProductContinuity.lean` (Apache 2.0). QICLean's
`Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`, and its
`Entropy.abs_vonNeumannEntropy_sub_le_sqrt` with the contraction
`Matrix.traceDistance_partialTraceRight_le` is replaced by the bipartite Alicki–Fannes–Winter
bound `Arealaw.abs_vonNeumann_sub_traceLeft_sub_le_sqrt` applied to the global pure state.
-/
import OpenAI.ConditionalContinuity
import OpenAI.FiniteProductEntropy
import OpenAI.RegionLift

/-!
# Regional entropy under perturbation of a pure state

The entropy of a fixed region `R` depends continuously on the global pure state: for unit
vectors `Ω`, `Φ` on a finite product, `|S_R(Ω) - S_R(Φ)| ≤ 4 √δ log (e d_R)`, where `δ` is the
trace distance of `|Ω⟩⟨Ω|` and `|Φ⟩⟨Φ|` on the whole system and `d_R` the dimension of the
region.

## Implementation notes

The source contracts the trace distance under the partial trace and applies the unconditional
continuity bound on `R`.  Here the conditional bound of Lemma 2.1 is applied to the global pure
states split as `R ⊗ Rᶜ`: a normalized pure state has zero entropy, and its marginal on `Rᶜ` has
the entropy of its marginal on `R`, so the conditional entropy `S(R Rᶜ) - S(Rᶜ)` is `-S_R`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 2.1 (`01-preliminaries.tex`, lines 33–46), as used in `08-scanner.tex`,
  lines 399–404, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder

namespace Arealaw

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A normalized pure state has zero entropy. -/
theorem vonNeumann_vecMulVec_eq_zero {f : ι → ℂ} (hf : star f ⬝ᵥ f = 1) :
    vonNeumann (posSemidef_vecMulVec_self_star f).isHermitian = 0 := by
  let g : Unit × ι → ℂ := fun p ↦ f p.2
  have hL : traceLeft (vecMulVec g (star g)) = vecMulVec f (star f) := by
    ext i j
    simp [g, traceLeft, vecMulVec_apply]
  rw [vonNeumann_congr _ (posSemidef_vecMulVec_self_star g).traceLeft.isHermitian hL.symm,
    vonNeumann_traceLeft_vecMulVec_eq_traceRight g, vonNeumann_of_unique]
  have htr : (traceRight (vecMulVec g (star g))).trace = 1 := by
    rw [← hf]
    simp [g, traceRight, Matrix.trace, vecMulVec_apply, dotProduct, mul_comm]
  rw [htr]
  simp

end Arealaw

namespace FiniteProduct

open Matrix Arealaw

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The entropy change on a fixed region is bounded by the trace distance
of the original normalized pure states and the dimension of that region.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, and its application
in `08-scanner.tex`, lines 399–404. -/
theorem abs_entropy_sub_le_sqrt_traceDistance
    (Ω Φ : EuclideanSpace ℂ ((v : V) → β v))
    (hΩ : ‖Ω‖ = 1) (hΦ : ‖Φ‖ = 1) (R : Finset V) :
    |entropy β Ω R - entropy β Φ R| ≤
      4 * Real.sqrt ((vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) -
        vecMulVec (WithLp.ofLp Φ) (star (WithLp.ofLp Φ))).traceNorm / 2) *
        Real.log (Real.exp 1 * Fintype.card (Configuration β R)) := by
  let e := (splitEquiv β R).symm
  let ρ := (OpenAI.pureState (WithLp.ofLp Ω)
    (OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).submatrix e
  let τ := (OpenAI.pureState (WithLp.ofLp Φ)
    (OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one hΦ)).submatrix e
  have h := abs_vonNeumann_sub_traceLeft_sub_le_sqrt ρ τ
  have hD : ρ.toSubState.D₁ τ.toSubState =
      (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) -
        vecMulVec (WithLp.ofLp Φ) (star (WithLp.ofLp Φ))).traceNorm / 2 := by
    simp only [ρ, τ, MState.toSubState_submatrix, SubState.D₁_submatrix,
      MState.D₁_eq_traceNorm_div_two, OpenAI.pureState_M]
  have hM (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
      ((OpenAI.pureState (WithLp.ofLp ψ)
        (OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one hψ)).submatrix e).M =
        vecMulVec (fun x ↦ ψ (e x)) (star fun x ↦ ψ (e x)) := by
    ext a b
    simp [vecMulVec_apply]
  have hpure (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
      vonNeumann ((OpenAI.pureState (WithLp.ofLp ψ)
        (OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one hψ)).submatrix e).psd.isHermitian =
        0 := by
    have h1 : star (fun x ↦ ψ (e x)) ⬝ᵥ (fun x ↦ ψ (e x)) = 1 := by
      rw [← OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one hψ]
      exact e.sum_comp fun y ↦ star (ψ y) * ψ y
    rw [vonNeumann_congr _ (posSemidef_vecMulVec_self_star _).isHermitian (hM ψ hψ)]
    exact vonNeumann_vecMulVec_eq_zero h1
  have hmarg (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
      vonNeumann ((OpenAI.pureState (WithLp.ofLp ψ)
        (OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one hψ)).submatrix
          e).psd.isHermitian.traceLeft = entropy β ψ R := by
    rw [← entropy_compl β ψ R, entropy]
    refine vonNeumann_congr _ _ ?_
    rw [reducedPure_compl_eq_traceLeft, hM ψ hψ]
  rw [hD, hpure Ω hΩ, hpure Φ hΦ, hmarg Ω hΩ, hmarg Φ hΦ] at h
  rw [abs_sub_comm]
  convert h using 2
  ring

end FiniteProduct
