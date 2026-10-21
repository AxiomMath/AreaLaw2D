/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SchurLabelCommutation
import AreaLawRefactored.S06_Replicas.Ported.SchurSurprisal
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.MergeDimensions

/-!
# Merge deficits

The logarithmic merge deficit `F_Q + F_E - F_{QE}` is positive semidefinite (Lemma 6.1(3),
`05-replicas.tex`, `replicas:merge-dimensions`; `07-comparators.tex`, lines 501–549).
-/

open Matrix PermutationRepresentation
open scoped BigOperators Matrix.Norms.Operator

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φQ φE φQE : G →* Equiv.Perm X}

open scoped ComplexOrder in
/-- The logarithmic merge deficit is positive semidefinite. -/
theorem posSemidef_mergeDeficit (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) :
    (labelEntropy φQ + labelEntropy φE - labelEntropy φQE).PosSemidef := by
  classical
  have hc (l μ : IrrepLabel G) : Commute (labelProj φQ l) (labelProj φE μ) :=
    commute_groupAlgebraRep_of_commute φQ φE hcomm _ _
  have hc' (p : IrrepLabel G × IrrepLabel G) (ν : IrrepLabel G) :
      Commute (labelProj φQ p.1 * labelProj φE p.2) (labelProj φQE ν) :=
    (commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
      (IrrepLabel.centralIdem_mem_center p.1) _).mul_left
      (commute_groupAlgebraRep_of_eq_mul φE φQ φQE (fun g => by rw [hprod, (hcomm g g).eq])
        (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center p.2) _)
  let hQ := isOrthogonalResolution_labelProj φQ
  let hE := isOrthogonalResolution_labelProj φE
  let hQE := isOrthogonalResolution_labelProj φQE
  let R₀ := hQ.prod hE hc
  let R := R₀.prod hQE hc'
  have hL : R.hom (fun p => (Real.log p.1.1.dim : ℂ)) = labelEntropy φQ :=
    (R₀.prod_hom_fst hQE R (fun p => (Real.log p.1.dim : ℂ))).trans
      ((hQ.prod_hom_fst hE R₀ (fun l => (Real.log l.dim : ℂ))).trans
        (labelObservable_eq_hom φQ _).symm)
  have hM : R.hom (fun p => (Real.log p.1.2.dim : ℂ)) = labelEntropy φE :=
    (R₀.prod_hom_fst hQE R (fun p => (Real.log p.2.dim : ℂ))).trans
      ((hQ.prod_hom_snd hE R₀ (fun l => (Real.log l.dim : ℂ))).trans
        (labelObservable_eq_hom φE _).symm)
  have hR : R.hom (fun p => (Real.log p.2.dim : ℂ)) = labelEntropy φQE :=
    (R₀.prod_hom_snd hQE R (fun l => (Real.log l.dim : ℂ))).trans
      (labelObservable_eq_hom φQE _).symm
  have hD : labelEntropy φQ + labelEntropy φE - labelEntropy φQE =
      R.hom (fun p => ((Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim : ℝ) : ℂ)) := by
    rw [← hL, ← hM, ← hR, ← map_add, ← map_sub]
    congr 1
    funext p
    simp
  rw [hD]
  refine R.posSemidef_hom_of_ne_zero (fun p => ?_) fun p hp => ?_
  · exact ((((isHermitian_labelProj φQ p.1.1).commute_iff
      (isHermitian_labelProj φE p.1.2)).mp (hc _ _)).commute_iff
        (isHermitian_labelProj φQE p.2)).mp (hc' p.1 p.2)
  · have hx : (0 : ℝ) < p.1.1.dim := mod_cast p.1.1.dim_pos
    have hy : (0 : ℝ) < p.1.2.dim := mod_cast p.1.2.dim_pos
    have hlog := Real.log_le_log (mod_cast p.2.dim_pos)
      (show (p.2.dim : ℝ) ≤ (p.1.1.dim : ℝ) * p.1.2.dim from
        mod_cast dim_le_mul_dim_of_compatible hcomm hprod hp)
    rw [Real.log_mul hx.ne' hy.ne'] at hlog
    linarith

end PermutationRepresentation
