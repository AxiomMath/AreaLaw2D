/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/ReplicaMarginalSymmetry.lean` (Apache 2.0).
Adaptations: QICLean's `Matrix.partialTraceLeft` is Physlib's `Matrix.traceLeft`. The covariance
identity `Matrix.partialTraceLeft_kronecker_conj_of_left_isometry` of
`QICLean/Channel/PartialTrace.lean` is added here (same name, new proof), over a commutative
star semiring instead of `ℂ`.
-/
import OpenAI.PermutationRepresentation
import OpenAI.ReplicaExcitationSymmetry
import QuantumInfo.ForMathlib.Matrix

/-!
# Marginal symmetry of exact excitation components

A vector fixed by a simultaneous permutation of two registers has a reduced
density matrix commuting with the permutation on the retained register.
The same conclusion holds for an actual excitation component when the
physical permutation stabilizes its excitation set.

These are the partial-trace identities used in *A two-dimensional area law
from a global spectral gap*, `07-comparators.tex`, lines 540–549, following
equation `comparator:merge-moments`. No normalization or independent-copy
assumption is needed. Selecting and regrouping the good-copy registers and
proving the merge-moment bound are separate assertions.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix
open scoped Matrix Kronecker

namespace Matrix

/-- Conjugating by `A ⊗ B` with `A` an isometry and then tracing out the first factor is
tracing out first and then conjugating by `B`. -/
theorem partialTraceLeft_kronecker_conj_of_left_isometry
    {R : Type*} [CommSemiring R] [StarRing R] {α β γ δ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [Fintype γ]
    (A : Matrix γ α R) (B : Matrix δ β R) (hA : Aᴴ * A = 1)
    (X : Matrix (α × β) (α × β) R) :
    traceLeft ((A ⊗ₖ B) * X * (A ⊗ₖ B)ᴴ) = B * traceLeft X * Bᴴ := by
  ext i j
  have horth (x y : α) : (∑ k : γ, A k x * star (A k y)) = if y = x then 1 else 0 := by
    simpa [mul_apply, one_apply, mul_comm] using congrFun (congrFun hA y) x
  simp only [traceLeft, of_apply, mul_apply, conjTranspose_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, star_mul, Finset.sum_mul]
  calc _ = ∑ q : α, ∑ b : β, ∑ p : α, ∑ a : β,
        (∑ k : γ, A k p * star (A k q)) * (B i a * X (p, a) (q, b) * star (B j b)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
          simp only [horth, ite_mul, one_mul, zero_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          refine (Finset.sum_congr rfl fun q _ => Finset.sum_comm).trans ?_
          simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum, Finset.sum_mul]

end Matrix

namespace PermutationRepresentation

variable {G X Y : Type*} [Group G] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 540–549.
-/

/-- The literal reduced density of a simultaneously fixed vector commutes with
the permutation of its retained register. *A two-dimensional area law from a
global spectral gap*, `07-comparators.tex`, lines 540–549, following equation
`comparator:merge-moments`. The vector need not be normalized. -/
theorem commute_partialTraceLeft_vecMulVec_of_fixed_kronecker_permOp
    (φ : G →* Equiv.Perm X) (χ : G →* Equiv.Perm Y) (g : G)
    (v : X × Y → ℂ) (hv : (permOp φ g ⊗ₖ permOp χ g) *ᵥ v = v) :
    Commute (permOp χ g) (traceLeft (vecMulVec v (star v))) := by
  have hA : (permOp φ g)ᴴ * permOp φ g = 1 := by
    rw [conjTranspose_permOp, permOp_inv_mul_self]
  have hconj : (permOp φ g ⊗ₖ permOp χ g) * vecMulVec v (star v) *
      (permOp φ g ⊗ₖ permOp χ g)ᴴ = vecMulVec v (star v) := by
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hv]
  have hpartial := congrArg traceLeft hconj
  rw [partialTraceLeft_kronecker_conj_of_left_isometry _ _ hA] at hpartial
  have hright := congrArg (fun K => K * permOp χ g) hpartial
  change permOp χ g * traceLeft (vecMulVec v (star v)) =
    traceLeft (vecMulVec v (star v)) * permOp χ g
  simpa only [mul_assoc, conjTranspose_permOp, permOp_inv_mul_self, mul_one] using hright

end PermutationRepresentation

namespace Matrix

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

open PermutationRepresentation TensorPower

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 540–549.
-/

/-- Tracing the physical register of an actual excitation component preserves
its auxiliary permutation symmetry. The symmetry of the component is derived
from that of the original vector and the stabilizer condition.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 540–549, following equation `comparator:merge-moments`. -/
theorem commute_partialTraceLeft_replicaExcitationComponent
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) (σ : Equiv.Perm (Fin k))
    (hB : B.image σ = B) (χ : Equiv.Perm (Fin k) →* Equiv.Perm C)
    (v : (Fin k → A) × C → ℂ)
    (hv : (permOp (copyPerm A k) σ ⊗ₖ permOp χ σ) *ᵥ v = v) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v
    Commute (permOp χ σ) (traceLeft (vecMulVec w (star w))) := by
  exact commute_partialTraceLeft_vecMulVec_of_fixed_kronecker_permOp
    (copyPerm A k) χ σ _
    (replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B σ hB _ v hv)

end Matrix
