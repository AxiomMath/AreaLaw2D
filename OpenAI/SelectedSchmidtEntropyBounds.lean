/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/SelectedSchmidtEntropyBounds.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw` renamed to `OpenAI`. TNLean's `Site Λ` is `↥(Λ : Set (ℤ × ℤ))` and its
`StateSpace Λ q` is `EuclideanSpace ℂ (↥(Λ : Set (ℤ × ℤ)) → Fin q)`. TNLean's regional state
`reducedState Λ q Ωt X` (with `reducedState_isHermitian`) is the finite-product reduction
`FiniteProduct.reducedPure β Ωt X` it is equal to (`reducedState_eq_finiteProduct`), and its
`regionalEntropy Λ q Ωt X` is `FiniteProduct.entropy β Ωt X`. QICLean's
`partialTraceLeft` is Physlib's `Matrix.traceLeft`; `vonNeumannEntropy ρ h` is
`Arealaw.vonNeumann h`.
-/
import OpenAI.SelectedSchmidtEntropy
import OpenAI.FiniteProductEntropy

/-!
# Entropy and dimension of a supplied selected Schmidt spectrum

The selected vector is formed from the given physical state and spectral set.
Its auxiliary entropy and the logarithm of the selected dimension are compared
with the original regional entropy, retaining the selected-mass correction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:typical-entropies`, lines 37–55, and
`comparator:high-label`, lines 240–270, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder

namespace OpenAI

open Classical in
/-- For a unit physical state and a supplied positive-mass spectral set in an
exponential window, both the logarithmic selected dimension and the entropy of
the actual selected auxiliary marginal differ from the original regional
entropy by at most the window width minus the logarithm of the selected mass.
Source: `07-comparators.tex`, `comparator:typical-entropies`, lines 37–55,
and `comparator:high-label`, lines 240–270. -/
theorem abs_log_card_and_selectedSchmidtEntropy_sub_le
    {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : EuclideanSpace ℂ (↥(Λ : Set (ℤ × ℤ)) → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (X : Finset ↥(Λ : Set (ℤ × ℤ)))
    (E : Finset (FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) X))
    (w : ℝ)
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q)
      Ωt X).isHermitian.spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt X - w) ≤
          (FiniteProduct.reducedPure_posSemidef (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q)
            Ωt X).isHermitian.eigenvalues i ∧
        (FiniteProduct.reducedPure_posSemidef (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q)
            Ωt X).isHermitian.eigenvalues i ≤
          Real.exp (-FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt X + w)) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let split := FiniteProduct.splitEquiv β X
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ωt
    let z := (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let η := w - Real.log z
    |Real.log (E.card : ℝ) - FiniteProduct.entropy β Ωt X| ≤ η ∧
      |Arealaw.vonNeumann (Matrix.posSemidef_vecMulVec_self_star ψ).traceLeft.isHermitian -
        FiniteProduct.entropy β Ωt X| ≤ η := by
  intro β split ΩX z ψ η
  have hbounds :=
    (FiniteProduct.reducedPure_posSemidef β Ωt X).typicalSpectralRestriction_entropy_bounds
      E w hz hE
  have hz1 : z ≤ 1 := (FiniteProduct.reducedPure_posSemidef β Ωt X).spectralRestrictionMass_le_one
    (FiniteProduct.trace_reducedPure β Ωt hΩt X) E
  rw [(FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.rank_normalizedSpectralRestriction
    E hz.ne' (fun i hi => (Real.exp_pos _).trans_le (hE i hi).1),
    abs_of_nonpos (Real.log_nonpos hz.le hz1)] at hbounds
  have hselected := Matrix.entropy_compressedTypicalPureState_equivFin_swap ΩX E hz
  simp only at hselected
  refine ⟨?_, ?_⟩
  · simpa only [η, FiniteProduct.entropy, sub_eq_add_neg] using hbounds.1
  · rw [hselected]
    exact hbounds.2

end OpenAI
