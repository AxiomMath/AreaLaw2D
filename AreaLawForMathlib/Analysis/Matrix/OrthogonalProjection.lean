/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Ported from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
file `QICLean/Algebra/OrthogonalProjection.lean`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import AreaLawForMathlib.Analysis.Matrix.MatrixProjectionAux

/-!
# Orthogonal projections in finite matrix algebras

This file collects the elementary definition and basic properties of orthogonal
projections in complex matrix algebras.  The material is independent of quantum
channels and irreducibility.

## Main declarations

* `IsOrthogonalProjection`
* `IsOrthogonalProjection.one_sub`
* `IsOrthogonalProjection.exists_range_isometry`
* `IsOrthogonalProjection.exists_support_isometry`
* `IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one`
* `isOrthogonalProjection_posSemidef`
* `isOrthogonalProjection_sum_of_pairwise_mul_eq_zero`
* `orthogonalProjection_mul_eq_zero_of_sum_eq_one`
-/

open scoped Matrix ComplexOrder BigOperators MatrixOrder

variable {D : ℕ}

/-- An orthogonal projection in `M_D(ℂ)`: a matrix that is both Hermitian and idempotent.
These correspond to projections onto subspaces of `ℂ^D`. -/
def IsOrthogonalProjection (P : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- An orthogonal projection is a star projection. -/
theorem IsOrthogonalProjection.isStarProjection {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) : IsStarProjection P := by
  rw [isStarProjection_iff']
  exact ⟨hP.2, by simpa [Matrix.star_eq_conjTranspose] using hP.1.eq⟩

/-- A star projection is an orthogonal projection. -/
theorem IsStarProjection.isOrthogonalProjection {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsStarProjection P) : IsOrthogonalProjection P := by
  rw [isStarProjection_iff'] at hP
  refine ⟨?_, hP.1⟩
  change Pᴴ = P
  simpa [Matrix.star_eq_conjTranspose] using hP.2

namespace Matrix

end Matrix

/-- The complement of an orthogonal projection is an orthogonal projection. -/
theorem IsOrthogonalProjection.one_sub {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) : IsOrthogonalProjection (1 - P) :=
  hP.isStarProjection.one_sub.isOrthogonalProjection
