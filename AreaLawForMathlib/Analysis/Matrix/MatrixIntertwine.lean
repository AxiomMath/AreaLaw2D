/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI

Ported and specialized from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Entropy/ConditionalMovement/LogCompression.lean`,
`QICLean/Analysis/OperatorMean/RealPowerIntertwine.lean`,
`QICLean/Algebra/MatrixAux.lean`, and
`QICLean/Analysis/CoisometricCompression.lean`.
-/
import AreaLawForMathlib.Analysis.Matrix.MatrixPowers
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Rectangular matrix intertwining

Extends `Mathlib/Analysis/Matrix/Order.lean`.

Minimal finite-dimensional identities used to transport filtered vectors and
transport states along rectangular intertwiners.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- A matrix factor moves across the complex dot product as its conjugate
transpose. -/
theorem star_dotProduct_mulVec (A : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
/-- The real part of the standard self-pairing is the squared Euclidean norm. -/
theorem re_star_dotProduct_self_eq_norm_sq (v : n → ℂ) :
    RCLike.re (star v ⬝ᵥ v) = ‖(EuclideanSpace.equiv n ℂ).symm v‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
    PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp, dotProduct_comm]

end Matrix
