/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawRefactored.S06_Replicas.Ported.ReplicaWholeInverse
import AreaLawRefactored.S06_Replicas.Ported.ReplicaDisjointMetricPositivity
import AreaLawRefactored.S06_Replicas.Ported.GroupedLabelSymmetricSupport
import AreaLawForMathlib.Analysis.Matrix.ProjectionCfcUpperBound
import AreaLawRefactored.S06_Replicas.Ported.InverseCompressionLowerPin

/-!
# A polynomial floor on simultaneous symmetric copies

On the simultaneous symmetric space the inverse partition metric is bounded by a polynomial in
the copy number, and the metric has the reciprocal floor (`07-comparators.tex`, lines 603–615).
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
  [∀ v, Nonempty (ι v)]

/-- Polynomial bound for the inverse partition metric on the symmetric space, and the
reciprocal floor for the metric. -/
theorem exists_replicaMetric_symProj_inverse_bound_and_floor
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      P ∪ Y ∪ F = Finset.univ →
      let Q := symProj (copyPerm ((v : V) → ι v) k)
      let W := replicaMetric ι t k
      let A := ((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2
      Q * A⁻¹ * Q ≤ ((k : ℝ) + 2) ^ C • Q ∧
        ((k : ℝ) + 2) ^ (-C) • Q ≤ A := by
  obtain ⟨C, hC, hwhole⟩ := exists_replicaMetric_inv_square_le_exp ι ht
  refine ⟨C, hC, fun k P Y F hPY hPF hYF hcover => ?_⟩
  intro Q W A
  have hcover' : Y ∪ (P ∪ F) = Finset.univ := by
    rw [← hcover, Finset.union_left_comm, Finset.union_assoc]
  let L := fun S => labelEntropy (subsystemPerm k ι S)
  let G := L P + L F - L Y
  let p : ℝ := ((k : ℝ) + 2) ^ C
  have hp : 0 < p := Real.rpow_pos_of_pos (by positivity) C
  have hQ : IsStarProjection Q := isStarProjection_symProj _
  have hG : G.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hsupport : Commute G Q ∧ 0 ≤ Q * G * Q := by
    simpa only [MonoidHom.comp_id, subsystemPerm_univ] using
      subgroup_signedLabelEntropy_symProj_nonneg ι
        (MonoidHom.id (Equiv.Perm (Fin k))) P Y F hPY hPF hYF hcover'
  have hexp : Q * NormedSpace.exp ((-(2 * t)) • G) * Q ≤ Q := by
    simpa only [mul_zero, Real.exp_zero, one_smul] using
      hG.compression_exp_neg_smul_le_of_lower_bound (b := 0) hQ hsupport.1
        (by simpa only [zero_smul] using hsupport.2) (show 0 ≤ 2 * t by positivity)
  have hinv : A⁻¹ ≤ p • NormedSpace.exp ((-(2 * t)) • G) := by
    simpa only [Complex.coe_smul] using hwhole k P Y F hPY hPF hYF
  have hbound : Q * A⁻¹ * Q ≤ p • Q := (show Q * A⁻¹ * Q ≤
      p • (Q * NormedSpace.exp ((-(2 * t)) • G) * Q) from Matrix.le_iff.mpr (by
    simpa only [hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul] using
      (Matrix.le_iff.mp hinv).conjTranspose_mul_mul_same Q)).trans
    (smul_le_smul_of_nonneg_left hexp hp.le)
  refine ⟨hbound, ?_⟩
  simpa only [p, Real.rpow_neg (by positivity : 0 ≤ (k : ℝ) + 2)] using
    (posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k hPF hPY
      hYF.symm).inv_smul_projection_le_of_compression_inv_le hQ hp hbound

end TensorPower
