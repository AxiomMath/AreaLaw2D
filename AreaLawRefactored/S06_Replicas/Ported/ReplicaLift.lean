/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawRefactored.S06_Replicas.Ported.ReplicaIntegral
import AreaLawRefactored.S06_Replicas.Ported.CoherentResolution
import AreaLawRefactored.S06_Replicas.Ported.ReplicaRegionUnion
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The integral representation in lifted form

The integral representation `W_{Q,k} = ∫ ((τ^t ⊗ 1)^{⊗k}) dζ_Q(τ)` of the replica metrics
(`05-replicas.tex`, equation `replicas:W-integral`), and `‖v^{⊗k}‖ = ‖v‖^k`.
-/

open MeasureTheory Matrix Finset PermutationRepresentation Entropy
open scoped MatrixOrder ComplexOrder Kronecker

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

omit [Fintype V] in
theorem splitEquiv_symm_apply_eq (k : ℕ) (Q : Finset V)
    (p : (Fin k → RegionConfig n Q) × (Fin k → (v : {v // v ∉ Q}) → Fin (n v))) (j : Fin k) :
    (splitEquiv (fun v => Fin (n v)) k Q).symm p j =
      (Equiv.piEquivPiSubtypeProd (· ∈ Q) fun v => Fin (n v)).symm (p.1 j, p.2 j) := by
  funext v
  by_cases h : v ∈ Q <;> simp [splitEquiv, Equiv.piEquivPiSubtypeProd, h]

/-- The tensor power of a local lift, in split coordinates. -/
theorem reindex_tensorPow_localLift (k : ℕ) (Q : Finset V)
    (M : Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ) :
    reindex (splitEquiv (fun v => Fin (n v)) k Q) (splitEquiv (fun v => Fin (n v)) k Q)
        (tensorPow (k := k) (localLift Q M)) =
      tensorPow (k := k) M ⊗ₖ (1 : Matrix (Fin k → (v : {v // v ∉ Q}) → Fin (n v))
        (Fin k → (v : {v // v ∉ Q}) → Fin (n v)) ℂ) := by
  ext p p'
  simp [tensorPow_apply, splitEquiv_symm_apply_eq, localLift_eq_reindex_kronecker, one_apply,
    prod_ite_zero, ← funext_iff]

/-- **The integral representation in lifted form** (`05-replicas.tex`, equation
`replicas:W-integral`): `W_{Q,k} = ∫ ((τ^t ⊗ 1)^{⊗k}) dζ_Q(τ)` on `V^{⊗k}`, for
`0 < t ≤ 1` and every region `Q`. -/
theorem exists_replicaMetric_integral_localLift [∀ v, NeZero (n v)] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (Q : Finset V) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ τ : Ω → Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ,
        (∀ᵐ ω ∂P, (τ ω).PosDef ∧ (τ ω).trace.re ≤ 1) ∧
        (∀ (k : ℕ) (x y : Config k fun v => Fin (n v)),
          Integrable (fun ω => tensorPow (k := k) (localLift Q (τ ω ^ t)) x y) P) ∧
        ∀ (k : ℕ) (x y : Config k fun v => Fin (n v)),
          replicaMetric (fun v => Fin (n v)) t k Q x y =
            ∫ ω, tensorPow (k := k) (localLift Q (τ ω ^ t)) x y ∂P := by
  have : ∀ v, Nonempty (Fin (n v)) := fun v => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨Ω, _, P, hP, τ, hτ, hint, heq⟩ :=
    exists_replicaMetric_integral (fun v => Fin (n v)) ht0 ht1 Q
  have hentry : ∀ (k : ℕ) (x y : Config k fun v => Fin (n v)) (ω : Ω),
      tensorPow (k := k) (localLift Q (τ ω ^ t)) x y =
        tensorPow (k := k) (τ ω ^ t) (splitEquiv _ k Q x).1 (splitEquiv _ k Q y).1 *
          (1 : Matrix (Fin k → (v : {v // v ∉ Q}) → Fin (n v))
            (Fin k → (v : {v // v ∉ Q}) → Fin (n v)) ℂ) (splitEquiv _ k Q x).2
              (splitEquiv _ k Q y).2 := fun k x y ω => by
    simpa [reindex_apply, kroneckerMap_apply] using congrFun (congrFun
      (reindex_tensorPow_localLift k Q (τ ω ^ t)) (splitEquiv _ k Q x)) (splitEquiv _ k Q y)
  refine ⟨Ω, inferInstance, P, hP, τ, hτ, fun k x y => ?_, fun k x y => ?_⟩
  · simpa only [hentry] using (hint k _ _).mul_const _
  · have h := congrFun (congrFun (heq k) (splitEquiv _ k Q x)) (splitEquiv _ k Q y)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
      of_apply] at h
    simp only [h, hentry, integral_mul_const]

/-! ### Tensor-power vectors -/

section Vectors

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem norm_tensorVec (k : ℕ) (v : Ω → ℂ) :
    ‖(EuclideanSpace.equiv (Fin k → Ω) ℂ).symm (tensorVec k v)‖ =
      ‖(EuclideanSpace.equiv Ω ℂ).symm v‖ ^ k := by
  have h2 : ‖(EuclideanSpace.equiv (Fin k → Ω) ℂ).symm (tensorVec k v)‖ ^ 2 =
      (‖(EuclideanSpace.equiv Ω ℂ).symm v‖ ^ k) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), ← pow_mul,
      mul_comm, pow_mul, EuclideanSpace.norm_eq,
      Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    change ∑ x, ‖tensorVec k v x‖ ^ 2 = (∑ i, ‖v i‖ ^ 2) ^ k
    simp only [tensorVec, norm_prod]
    rw [show (∑ i : Ω, ‖v i‖ ^ 2) ^ k = ∏ _j : Fin k, ∑ i : Ω, ‖v i‖ ^ 2 by simp,
      Fintype.prod_sum]
    simp only [← prod_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (pow_nonneg (norm_nonneg _) _) two_ne_zero).mp h2

omit [DecidableEq Ω] in
/-- Bounding an averaged operator on a vector by its pointwise bound. -/
theorem norm_of_integral_mulVec_le {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] (G : Ω' → Matrix Ω Ω ℂ) (hG : ∀ x y, Integrable (fun ω => G ω x y) P)
    (u : Ω → ℂ) {B : ℝ} (hB : ∀ᵐ ω ∂P, ‖(EuclideanSpace.equiv Ω ℂ).symm (G ω *ᵥ u)‖ ≤ B) :
    ‖(EuclideanSpace.equiv Ω ℂ).symm ((Matrix.of fun x y => ∫ ω, G ω x y ∂P) *ᵥ u)‖ ≤ B := by
  set F : Ω' → EuclideanSpace ℂ Ω := fun ω => (EuclideanSpace.equiv Ω ℂ).symm (G ω *ᵥ u)
  have hF : ∀ x, Integrable (fun ω => F ω x) P := fun x => by
    change Integrable (fun ω => (G ω *ᵥ u) x) P
    simp only [mulVec, dotProduct]
    exact integrable_finsetSum _ fun y _ => (hG x y).mul_const _
  have heq : (EuclideanSpace.equiv Ω ℂ).symm ((Matrix.of fun x y => ∫ ω, G ω x y ∂P) *ᵥ u) =
      ∫ ω, F ω ∂P := by
    ext x
    rw [eval_integral_piLp hF]
    change ((Matrix.of fun x y => ∫ ω, G ω x y ∂P) *ᵥ u) x = ∫ ω, (G ω *ᵥ u) x ∂P
    simp only [mulVec, dotProduct, of_apply]
    simp only [integral_finsetSum _ fun y _ => (hG x y).mul_const _, integral_mul_const]
  simpa [heq] using norm_integral_le_of_norm_le_const (μ := P) (f := F) hB

omit [DecidableEq Ω] in
theorem mul_of_integral {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} (A : Matrix Ω Ω ℂ)
    (H : Ω' → Matrix Ω Ω ℂ) (hH : ∀ x y, Integrable (fun ω => H ω x y) P) :
    A * Matrix.of (fun x y => ∫ ω, H ω x y ∂P) = Matrix.of fun x y => ∫ ω, (A * H ω) x y ∂P := by
  ext x y
  simp only [Matrix.mul_apply, of_apply]
  simp only [integral_finsetSum _ fun z _ => (hH z y).const_mul _, integral_const_mul]

end Vectors

end TensorPower
