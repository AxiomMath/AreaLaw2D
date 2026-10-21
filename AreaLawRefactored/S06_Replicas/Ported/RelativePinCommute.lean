/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawRefactored.S06_Replicas.Ported.RelativePinCompensator
import AreaLawRefactored.S06_Replicas.Ported.RelativePinAlgebra
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.MergeMoment

/-!
# Label functions commute with tensor powers of local operators

Every label function of a region `Q` commutes with `(M ⊗ 1)^{⊗k}` for `M` supported on a region
contained in or disjoint from `Q` (`05-replicas.tex`, lines 541–546).
-/

open Matrix PermutationRepresentation Entropy
open scoped Kronecker MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

theorem commute_permOp_subsystemPerm_tensorPow_of_subset {k : ℕ} {Q R : Finset V}
    (hRQ : R ⊆ Q) (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (π : Equiv.Perm (Fin k)) :
    Commute (permOp (subsystemPerm k (fun v => Fin (n v)) Q) π)
      (tensorPow (k := k) (localLift R M)) := by
  obtain ⟨K, hK⟩ := ((isSupportedOn_localLift R M).mono hRQ).exists_localLift σ₀
  rw [hK]
  set e := splitEquiv (fun v => Fin (n v)) k Q
  have hmul : ∀ A B : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ,
      reindex e e (A * B) = reindex e e A * reindex e e B := fun A B => by
    simp [reindex_apply, submatrix_mul_equiv]
  have hP : reindex e e (permOp (subsystemPerm k (fun v => Fin (n v)) Q) π) =
      permOp (copyPerm (RegionConfig n Q) k) π ⊗ₖ
        (1 : Matrix (Fin k → (v : {v // v ∉ Q}) → Fin (n v))
          (Fin k → (v : {v // v ∉ Q}) → Fin (n v)) ℂ) := by
    rw [← permOp_prodLeft, permOp_of_intertwine e
      (fun g x => splitEquiv_subsystemPerm (fun v => Fin (n v)) k Q g x) π]
  apply (reindex e e).injective
  rw [hmul, hmul, hP, reindex_tensorPow_localLift, ← mul_kronecker_mul, ← mul_kronecker_mul,
    (commute_permOp_copyPerm_tensorPow K π).eq]

/-- A label function of `Q` commutes with tensor powers of operators on `R ⊆ Q`. -/
theorem commute_labelObservable_tensorPow_of_subset {k : ℕ} {Q R : Finset V} (hRQ : R ⊆ Q)
    (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (tensorPow (k := k) (localLift R M)) :=
  commute_labelObservable_of_forall_commute _
    (fun π => commute_permOp_subsystemPerm_tensorPow_of_subset hRQ σ₀ M π) f

/-- A label function of `Q` commutes with tensor powers of operators on regions disjoint from
`Q`. -/
theorem commute_labelObservable_tensorPow_of_disjoint {k : ℕ} {Q R : Finset V}
    (hRQ : Disjoint R Q) (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (tensorPow (k := k) (localLift R M)) := by
  refine commute_labelObservable_of_forall_commute _ (fun π => ?_) f
  have hsub : R ⊆ Qᶜ := fun v hv => Finset.mem_compl.mpr (Finset.disjoint_left.mp hRQ hv)
  have hsplit : permOp (copyPerm (SiteConfig n) k) π =
      permOp (subsystemPerm k (fun v => Fin (n v)) Q) π *
        permOp (subsystemPerm k (fun v => Fin (n v)) Qᶜ) π :=
    permOp_of_eq_mul _ _ _ (fun g => copyPerm_eq_mul_compl (ι := fun v => Fin (n v)) Q g) π
  rw [show permOp (subsystemPerm k (fun v => Fin (n v)) Q) π =
      permOp (copyPerm (SiteConfig n) k) π *
        permOp (subsystemPerm k (fun v => Fin (n v)) Qᶜ) π⁻¹ by
    rw [hsplit, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]]
  exact (commute_permOp_copyPerm_tensorPow (localLift R M) π).mul_left
    (commute_permOp_subsystemPerm_tensorPow_of_subset hsub σ₀ M π⁻¹)

end TensorPower
