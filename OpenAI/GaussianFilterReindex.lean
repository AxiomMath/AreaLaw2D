/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/GaussianFilter/Reindex.lean` (Apache 2.0). Only `Matrix.reindex_exp` is
ported, generalized from `ℂ` to `RCLike 𝕜`; the Gaussian-filter reindexing lemmas are left out.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The matrix exponential under reindexing

Simultaneous reindexing of rows and columns is a continuous algebra equivalence, so it
commutes with the matrix exponential.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
  [DecidableEq m]

/-- The matrix exponential is natural under a simultaneous finite reindexing. -/
theorem reindex_exp (e : n ≃ m) (A : Matrix n n 𝕜) :
    reindex e e (NormedSpace.exp A) = NormedSpace.exp (reindex e e A) := by
  let _ : NormedAlgebra ℚ (Matrix n n 𝕜) := NormedAlgebra.restrictScalars ℚ 𝕜 _
  exact NormedSpace.map_exp (reindexAlgEquiv 𝕜 𝕜 e)
    (reindexLinearEquiv 𝕜 𝕜 e e).toContinuousLinearEquiv.continuous A

end Matrix
