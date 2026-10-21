/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.GroupedCopies
import AreaLaw.S06_Replicas.Ported.MergeExponential
import AreaLaw.S06_Replicas.Ported.ReplicaSimilarity
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.TrivialLabel

/-!
# Signed subgroup labels on the simultaneous symmetric subspace

For three disjoint subsystems covering the whole space, the signed label operator of any
permutation subgroup is nonnegative on its simultaneous symmetric subspace
(`07-comparators.tex`, lines 454--480; `05-replicas.tex`, Lemma 6.1(2)).
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace PermutationRepresentation

/-- Complementary label entropies agree after simultaneous symmetrization. -/
theorem labelEntropy_mul_symProj_of_eq_mul
    {r : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (φ χ ψ : Equiv.Perm (Fin r) →* Equiv.Perm X)
    (hψ : ∀ σ, ψ σ = φ σ * χ σ) :
    labelEntropy φ * symProj ψ = labelEntropy χ * symProj ψ := by
  have hlabel (ell : IrrepLabel (Equiv.Perm (Fin r))) :
      labelProj φ ell * symProj ψ = labelProj χ ell * symProj ψ := by
    ext x y
    have h := groupAlgebraRep_mulVec_eq_of_eq_mul φ χ ψ hψ
      (a := IrrepLabel.centralIdem ell)
      (IrrepLabel.coeff_inv_of_mem_center (IrrepLabel.centralIdem_mem_center ell))
      (symProj_mulVec_mem ψ (Pi.single y 1))
    exact congrFun (by simpa only [mulVec_single_one] using h) x
  simp_rw [labelEntropy, labelObservable, Finset.sum_mul, smul_mul_assoc, hlabel]

end PermutationRepresentation

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

/-- Configurations of `k` copies have decidable equality through the finite product. -/
local instance groupedLabelSymmetricSupportDecidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

omit [Fintype V] [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] in
/-- Commuting permutations of copies induce commuting actions on arbitrary subsystems. -/
theorem commute_subsystemPerm_of_commute (k : ℕ) (S T : Finset V)
    {σ τ : Equiv.Perm (Fin k)} (hστ : Commute σ τ) :
    Commute (subsystemPerm k ι S σ) (subsystemPerm k ι T τ) := by
  ext x j v
  simp only [Equiv.Perm.mul_apply, subsystemPerm_apply]
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;>
    simp only [hS, hT, ite_true, ite_false]
  exact congrArg (fun i => x i v)
    (congrArg (fun π : Equiv.Perm (Fin k) => π j) hστ.inv_inv.eq).symm


/-- The signed subgroup label operator is nonnegative on its simultaneous symmetric
subspace. -/
theorem subgroup_signedLabelEntropy_symProj_nonneg
    {r k : ℕ} (θ : Equiv.Perm (Fin r) →* Equiv.Perm (Fin k))
    (P Y F : Finset V) (hPY : Disjoint P Y) (hPF : Disjoint P F)
    (hYF : Disjoint Y F) (hcover : Y ∪ (P ∪ F) = Finset.univ) :
    let L := fun S => labelEntropy ((subsystemPerm k ι S).comp θ)
    let Q := symProj ((subsystemPerm k ι Finset.univ).comp θ)
    let G := L P + L F - L Y
    Commute G Q ∧ 0 ≤ Q * G * Q := by
  intro L Q G
  have hc (S : Finset V) : Commute (L S) Q := by
    unfold L Q labelEntropy labelObservable symProj
    refine Commute.sum_left _ _ _ fun ell _ => ?_
    refine ((Commute.sum_right _ _ _ (fun σ _ => ?_)).smul_left _).smul_right _
    simpa only [labelProj, groupAlgebraRep_single, one_smul] using
      commute_groupAlgebraRep_of_eq_mul
        ((subsystemPerm k ι S).comp θ) ((subsystemPerm k ι (Finset.univ \ S)).comp θ)
        ((subsystemPerm k ι Finset.univ).comp θ)
        (fun τ => by
          change subsystemPerm k ι Finset.univ (θ τ) = _
          conv_lhs => rw [← Finset.union_sdiff_of_subset (Finset.subset_univ S)]
          exact subsystemPerm_union k ι Finset.disjoint_sdiff (θ τ))
        (fun σ τ => commute_subsystemPerm_of_disjoint k ι
          Finset.disjoint_sdiff (θ σ) (θ τ))
        (IrrepLabel.centralIdem_mem_center ell) (MonoidAlgebra.single σ (1 : ℂ))
  have hGQ : Commute G Q := ((hc P).add_left (hc F)).sub_left (hc Y)
  have hYPF : Disjoint Y (P ∪ F) := Finset.disjoint_union_right.mpr ⟨hPY.symm, hYF⟩
  have hY : L Y * Q = L (P ∪ F) * Q := by
    apply labelEntropy_mul_symProj_of_eq_mul
    intro σ
    change subsystemPerm k ι Finset.univ (θ σ) = _
    rw [← hcover]
    exact subsystemPerm_union k ι hYPF (θ σ)
  let D := L P + L F - L (P ∪ F)
  have hD : D.PosSemidef := posSemidef_mergeDeficit
    (fun σ τ => commute_subsystemPerm_of_disjoint k ι hPF (θ σ) (θ τ))
    (fun σ => subsystemPerm_union k ι hPF (θ σ))
  have hGQ' : G * Q = D * Q := by simp only [G, D, sub_mul, add_mul, hY]
  have hQH : Q.IsHermitian := (isStarProjection_symProj _).isSelfAdjoint.isHermitian
  refine ⟨hGQ, Matrix.le_iff.mpr ?_⟩
  rw [sub_zero, mul_assoc, hGQ', ← mul_assoc]
  simpa only [hQH.eq] using hD.conjTranspose_mul_mul_same Q

end TensorPower
