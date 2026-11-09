/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
file `QICLean/Algebra/PosSemidefSupport.lean`.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import AreaLawForMathlib.Analysis.Matrix.OrthogonalProjection

/-!
# Support projections of finite Hermitian matrices

Extends `Mathlib/Analysis/Matrix/PosDef.lean`.

This file defines the spectral support projection for a Hermitian matrix on an
arbitrary finite index type. Its positive-semidefinite and `Fin`-indexed versions
are specializations of that construction.

## Main declarations

* `Matrix.IsHermitian.supportProj`: the spectral projection onto the nonzero
  eigenspaces of a Hermitian matrix.
* `Matrix.IsHermitian.supportProj_mul_self` and
  `Matrix.IsHermitian.mul_supportProj_self`: absorption on both sides.
* `Matrix.IsHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le`: right
  absorption under kernel inclusion.
* `Matrix.PosSemidef.supportProj`: the positive-semidefinite specialization.
* `Matrix.PosSemidef.isOrthogonalProjection_supportProj`: orthogonality of the
  positive-semidefinite support projection.
* `Matrix.supportProj_mul_conjTranspose_mul_self`: the support projection of
  $B B^\dagger$ fixes $B$.
* `Matrix.PosSemidef.supportProj_sq_eq_supportProj`: `A * A` and `A` share a
  support projection.
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- **Support projection of a Hermitian matrix.** Conjugating by the eigenvector
unitary the diagonal indicator of the nonzero eigenvalues yields the orthogonal
projection onto the range of the matrix. -/
noncomputable def supportProj (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => if hA.eigenvalues i ≠ 0 then (1 : ℂ) else 0) *
    (star (hA.eigenvectorUnitary : Matrix n n ℂ))

/-! ### Rank of a Hermitian projection -/

end Matrix.IsHermitian

namespace Matrix.PosSemidef

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The support projection of a positive-semidefinite matrix. -/
noncomputable def supportProj (hA : A.PosSemidef) : Matrix n n ℂ :=
  hA.isHermitian.supportProj

variable {D : ℕ} {ρ : Matrix (Fin D) (Fin D) ℂ}

end Matrix.PosSemidef

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Matrix
