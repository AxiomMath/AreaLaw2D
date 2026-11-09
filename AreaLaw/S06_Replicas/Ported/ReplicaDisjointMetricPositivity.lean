/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLaw.S06_Replicas.Ported.ReplicaSimilarity
import AreaLawForMathlib.Analysis.Matrix.MatrixPowers

/-!
# Positive disjoint replica metric products

`(W_P^{-1} W_F^{-1} W_Y)²` is positive definite for pairwise disjoint `P, F, Y`
(`05-replicas.tex`, `replicas:leaf-metric`, lines 459--473).

Ported from `LionSR/QICLean`, file
`QICLean/Representation/ReplicaDisjointMetricPositivity.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
variable [∀ v, Nonempty (ι v)]

/-- The squared disjoint metric `(W_P^{-1} W_F^{-1} W_Y)²` is positive definite. -/
theorem posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P F Y : Finset V}
    (hPF : Disjoint P F) (hPY : Disjoint P Y) (hFY : Disjoint F Y) :
    (((replicaMetric ι t k P)⁻¹ * (replicaMetric ι t k F)⁻¹ *
      replicaMetric ι t k Y) ^ 2).PosDef := by
  have hinv (S : Finset V) : (replicaMetric ι t k S)⁻¹ =
      labelObservable (subsystemPerm k ι S) (fun ell => (replicaLabelWeight ι t ell)⁻¹) :=
    labelObservable_inv _ (fun ell => (replicaLabelWeight_pos ι ht ell).ne')
  have hc {S S' : Finset V} (h : Disjoint S S') (f f' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :=
    commute_labelObservable_of_commute _ _ (commute_subsystemPerm_of_disjoint k ι h) f f'
  have h := ((posDef_replicaMetric ι ht k P).inv.mul_of_commute
    (posDef_replicaMetric ι ht k F).inv (by rw [hinv, hinv]; exact hc hPF _ _)).mul_of_commute
      (posDef_replicaMetric ι ht k Y) (Commute.mul_left (by rw [hinv]; exact hc hPY _ _)
        (by rw [hinv]; exact hc hFY _ _))
  exact (h.posSemidef.pow 2).posDef_iff_isUnit.mpr (h.isUnit.pow 2)

end TensorPower
