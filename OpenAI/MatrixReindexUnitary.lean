/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Algebra/MatrixReindexUnitary.lean` (Apache 2.0). Adapted: scalars generalized from
`ℂ` to a commutative star ring.
-/
import OpenAI.MatrixUnitaryBetween

/-!
# Unitary group membership under matrix reindexing

Reindexing the rows and columns of a square matrix through one equivalence of index types
preserves membership in `Matrix.unitaryGroup`. Physlib's `Matrix.reindex_one_mem_unitaryGroup`
is the case of the identity matrix.

This standard fact is used in the physical-blocking argument for Matrix Product Unitaries
(Cirac--Perez-Garcia--Schuch--Verstraete, Section II, Definition `blocking`, lines 297--305).
-/

namespace Matrix

/-- Reindexing a square matrix through an equivalence of index types preserves
membership in the unitary group. -/
theorem reindex_mem_unitaryGroup {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [CommRing R] [StarRing R] (e : m ≃ n) (A : Matrix m m R)
    (hA : A ∈ unitaryGroup m R) :
    reindex e e A ∈ unitaryGroup n R := by
  rw [← isUnitaryBetween_iff_mem_unitaryGroup] at hA ⊢
  exact hA.reindex A e e

end Matrix
