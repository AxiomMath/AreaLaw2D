/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/PhysicalSingletonEntropy.lean` (Apache 2.0). Adaptations:
`vonNeumannEntropy ρ hρ` is `Arealaw.vonNeumann hρ`, with `Arealaw.vonNeumann_congr` and
`Arealaw.vonNeumann_submatrix_equiv` for `vonNeumannEntropy_congr` and
`vonNeumannEntropy_submatrix_equiv`; QICLean's `Matrix.partialTraceRight` is Physlib's
`Matrix.traceRight`, with `PosSemidef.traceRight`; `partialTraceRight_submatrix_prod_equiv` is
`Matrix.traceRight_submatrix_prodCongr` (`OpenAI.TraceRightSubmatrix`).
-/
import OpenAI.PhysicalSingletonDensity
import OpenAI.TraceRightSubmatrix
import OpenAI.FiniteProductEntropy

/-!
# The entropy difference of the original physical marginals

The three singleton densities are the reductions of one and the same
original pure physical state. Subadditivity on the two outer factors,
together with equality of complementary pure-state entropies, gives the
nonnegative difference `S(Q) + S(V) - S(Y)`. No marginal entropy identity
or full-rank condition is assumed.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 550--590, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower
open scoped BigOperators Matrix ComplexOrder

namespace Matrix

private theorem entropy_piSplitAt_eq_regional
    {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (j : V) :
    Arealaw.vonNeumann
      (posSemidef_vecMulVec_self_star
        (fun x => ψ ((Equiv.piSplitAt j β).symm x))).traceRight.isHermitian =
      FiniteProduct.entropy β ψ {j} := by
  let a : FiniteProduct.Configuration β {j} ≃ β j :=
    { toFun := fun x => x ⟨j, Finset.mem_singleton_self j⟩
      invFun := fun x v => by
        rcases v with ⟨v, hv⟩
        have hvj : v = j := Finset.mem_singleton.mp hv
        subst v
        exact x
      left_inv := by
        intro x
        funext v
        rcases v with ⟨v, hv⟩
        have hvj : v = j := Finset.mem_singleton.mp hv
        subst v
        rfl
      right_inv := by intro x; rfl }
  let b : FiniteProduct.Configuration β ({j} : Finset V)ᶜ ≃
      ((v : {v : V // v ≠ j}) → β v) :=
    { toFun := fun x v => x ⟨v, by simpa using v.property⟩
      invFun := fun x v => x ⟨v, fun hvj =>
        (Finset.mem_compl.mp v.property) (Finset.mem_singleton.mpr hvj)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hsplit (x : (v : V) → β v) :
      (a.prodCongr b) (FiniteProduct.splitEquiv β {j} x) =
        Equiv.piSplitAt j β x := rfl
  have hcoords (x : β j × ((v : {v : V // v ≠ j}) → β v)) :
      (FiniteProduct.splitEquiv β {j}).symm ((a.prodCongr b).symm x) =
        (Equiv.piSplitAt j β).symm x := by
    apply (Equiv.piSplitAt j β).injective
    rw [← hsplit, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  let R := (vecMulVec (fun x => ψ x) (star (fun x => ψ x))).submatrix
    (FiniteProduct.splitEquiv β {j}).symm (FiniteProduct.splitEquiv β {j}).symm
  have hρ : traceRight (vecMulVec
      (fun x => ψ ((Equiv.piSplitAt j β).symm x))
      (star (fun x => ψ ((Equiv.piSplitAt j β).symm x)))) =
      (FiniteProduct.reducedPure β ψ {j}).submatrix a.symm a.symm := by
    calc
      _ = traceRight (R.submatrix (a.prodCongr b).symm
          (a.prodCongr b).symm) := by
        congr 1
        ext x y
        change ψ ((Equiv.piSplitAt j β).symm x) *
            star (ψ ((Equiv.piSplitAt j β).symm y)) =
          ψ ((FiniteProduct.splitEquiv β {j}).symm ((a.prodCongr b).symm x)) *
            star (ψ ((FiniteProduct.splitEquiv β {j}).symm ((a.prodCongr b).symm y)))
        rw [hcoords, hcoords]
      _ = _ := traceRight_submatrix_prodCongr a b R
  exact (Arealaw.vonNeumann_congr _
    ((FiniteProduct.reducedPure_posSemidef β ψ {j}).isHermitian.submatrix a.symm) hρ).trans
      (Arealaw.vonNeumann_submatrix_equiv
        (FiniteProduct.reducedPure_posSemidef β ψ {j}).isHermitian a.symm)

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- The two outer physical entropies minus the middle physical entropy
are nonnegative for the original unit pure state, with exactly the
singleton marginals used in the component moment estimates.
Source: `07-comparators.tex`, lines 550--590. -/
theorem physicalSingletonEntropy_outer_sub_middle_nonneg
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) :
    0 ≤ Arealaw.vonNeumann (posSemidef_physicalSingletonDensity ι Ω 0).isHermitian +
      Arealaw.vonNeumann (posSemidef_physicalSingletonDensity ι Ω 2).isHermitian -
      Arealaw.vonNeumann (posSemidef_physicalSingletonDensity ι Ω 1).isHermitian := by
  let β := fun j : Fin 3 => ι (j.castAdd 2)
  let e := (physicalSingletonEquiv ι 0).trans (Equiv.piSplitAt 0 β).symm
  let ψ : EuclideanSpace ℂ ((j : Fin 3) → β j) := WithLp.toLp 2 (Ω ∘ e.symm)
  have hψ : ‖ψ‖ = 1 := by
    calc
      ‖ψ‖ = ‖WithLp.toLp 2 Ω‖ :=
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (WithLp.toLp 2 Ω)
      _ = 1 := hΩ
  have he (j : Fin 3) : physicalSingletonEquiv ι j =
      e.trans (Equiv.piSplitAt j β) := by
    simp only [e, physicalSingletonEquiv, β, Equiv.trans_assoc,
      Equiv.self_trans_symm, Equiv.trans_refl]
  have hS (j : Fin 3) :
      Arealaw.vonNeumann (posSemidef_physicalSingletonDensity ι Ω j).isHermitian =
      FiniteProduct.entropy β ψ {j} := by
    have hρ : physicalSingletonDensity ι Ω j =
        traceRight (vecMulVec
          (fun x => ψ ((Equiv.piSplitAt j β).symm x))
          (star (fun x => ψ ((Equiv.piSplitAt j β).symm x)))) := by
      rw [physicalSingletonDensity, he]
      rfl
    rw [Arealaw.vonNeumann_congr _
      ((posSemidef_vecMulVec_self_star _).traceRight.isHermitian) hρ]
    exact entropy_piSplitAt_eq_regional β ψ j
  rw [hS, hS, hS]
  have hsub := FiniteProduct.entropy_union_le β ψ hψ
    ({0} : Finset (Fin 3)) {2} (by simp)
  have hpure := FiniteProduct.entropy_compl β ψ ({1} : Finset (Fin 3))
  have hregions : ({0} : Finset (Fin 3)) ∪ {2} = ({1} : Finset (Fin 3))ᶜ := by
    ext j
    fin_cases j <;> simp
  rw [hregions, hpure] at hsub
  exact sub_nonneg.mpr hsub

end Matrix
