/-
Copyright (c) 2025–2026 TNLean and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors, QICLean contributors

Extracted from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`, files
`QICLean/Algebra/MatrixAux.lean` and
`QICLean/Algebra/MatrixIsometryEntries.lean`.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Matrix lemmas used by finite-dimensional orthogonal projections

Extends `Mathlib/Analysis/Matrix/PosDef.lean`.
-/

open scoped Matrix ComplexOrder BigOperators MatrixOrder

namespace Matrix

/-- A matrix factor moves across the complex dot product as its conjugate transpose. -/
theorem star_dotProduct_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]

section Columns

variable {m n : Type*} [Fintype m] [DecidableEq n]

end Columns

section Rows

variable {m n : Type*} [DecidableEq m] [Fintype n]

end Rows

section SumSquaresZero

variable {ι n : Type*} [Fintype ι] [Fintype n]

theorem eq_zero_of_sum_mul_conjTranspose_eq_zero
    (B : ι → Matrix n n ℂ)
    (h : ∑ i : ι, B i * (B i)ᴴ = 0) :
    ∀ i, B i = 0 := by
  intro i
  have htrace_nonneg :
      ∀ j : ι, 0 ≤ ((B j * (B j)ᴴ).trace).re :=
    fun j =>
      (Complex.le_def.mp (Matrix.posSemidef_self_mul_conjTranspose (B j)).trace_nonneg).1
  have htrace_sum :
      ∑ j : ι, ((B j * (B j)ᴴ).trace).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h]
    simp
  have htrace_re : ((B i * (B i)ᴴ).trace).re = 0 :=
    congrFun (Fintype.sum_eq_zero_iff_of_nonneg (fun j => htrace_nonneg j) |>.mp
      htrace_sum) i
  have htrace_zero : (B i * (B i)ᴴ).trace = 0 :=
    Complex.ext htrace_re
      (Complex.le_def.mp (Matrix.posSemidef_self_mul_conjTranspose (B i)).trace_nonneg).2.symm
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp htrace_zero

theorem eq_zero_of_sum_conjTranspose_mul_self_eq_zero
    (B : ι → Matrix n n ℂ)
    (h : ∑ i : ι, (B i)ᴴ * B i = 0) :
    ∀ i, B i = 0 := by
  have hstar :
      ∀ i, (B i)ᴴ = 0 :=
    eq_zero_of_sum_mul_conjTranspose_eq_zero (fun i => (B i)ᴴ) (by
      simpa only [Matrix.conjTranspose_conjTranspose] using h)
  intro i
  exact Matrix.conjTranspose_eq_zero.mp (hstar i)

end SumSquaresZero

end Matrix
