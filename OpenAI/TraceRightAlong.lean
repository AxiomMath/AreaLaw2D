/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Channel/PartialTrace.lean` (Apache 2.0). Adaptations: QICLean's
`Matrix.partialTraceRightAlong` is renamed `Matrix.traceRightAlong` after Physlib's
`Matrix.traceRight`, which replaces QICLean's `Matrix.partialTraceRight`, and is stated over any
additive commutative monoid instead of `ℂ`; `traceRightAlong_kronecker` and
`traceRightAlong_kronecker_mul_left` are stated over any (non-unital) semiring.
-/
import QuantumInfo.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Partial trace along a product decomposition

For a matrix on `α × β` and a decomposition `e : β ≃ β' × γ` of the right factor,
`Matrix.traceRightAlong e` traces out the `γ` component and keeps `α × β'`. Its entries are
`∑ c, X (a, e.symm (b, c)) (a', e.symm (b', c))`. It commutes with a Kronecker factor on the
left, both as a tensor factor (`Matrix.traceRightAlong_kronecker`) and as a left multiplication
by `P ⊗ₖ 1` (`Matrix.traceRightAlong_kronecker_mul_left`).
-/

open scoped BigOperators Matrix Kronecker

namespace Matrix

/-- The partial trace of the `γ` component of the right tensor factor, after choosing a product
decomposition `e : β ≃ β' × γ` of that factor. -/
def traceRightAlong {R α β β' γ : Type*} [AddCommMonoid R] [Fintype γ]
    (e : β ≃ β' × γ) (X : Matrix (α × β) (α × β) R) : Matrix (α × β') (α × β') R :=
  traceRight (X.submatrix
    (((Equiv.refl α).prodCongr e).trans (Equiv.prodAssoc α β' γ).symm).symm
    (((Equiv.refl α).prodCongr e).trans (Equiv.prodAssoc α β' γ).symm).symm)

@[simp]
theorem traceRightAlong_apply {R α β β' γ : Type*} [AddCommMonoid R] [Fintype γ]
    (e : β ≃ β' × γ) (X : Matrix (α × β) (α × β) R) (a a' : α) (b b' : β') :
    traceRightAlong e X (a, b) (a', b') =
      ∑ c : γ, X (a, e.symm (b, c)) (a', e.symm (b', c)) :=
  rfl

/-- Tracing part of the right factor of `A ⊗ₖ B` leaves `A` unchanged. -/
theorem traceRightAlong_kronecker {R α K C H : Type*} [NonUnitalNonAssocSemiring R]
    [Fintype H] (e : K ≃ C × H) (A : Matrix α α R) (B : Matrix K K R) :
    traceRightAlong e (A ⊗ₖ B) = A ⊗ₖ traceRight (B.submatrix e.symm e.symm) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [traceRightAlong_apply, kroneckerMap_apply, traceRight, of_apply, submatrix_apply,
    Finset.mul_sum]

/-- Tracing part of the right factor commutes with left multiplication by `P ⊗ₖ 1`. -/
theorem traceRightAlong_kronecker_mul_left {R A K G H : Type*} [Semiring R]
    [Fintype A] [Fintype K] [DecidableEq K] [Fintype G] [DecidableEq G] [Fintype H]
    (e : K ≃ G × H) (P : Matrix A A R) (M : Matrix (A × K) (A × K) R) :
    traceRightAlong e ((P ⊗ₖ (1 : Matrix K K R)) * M) =
      (P ⊗ₖ (1 : Matrix G G R)) * traceRightAlong e M := by
  ext ⟨a, g⟩ ⟨a', g'⟩
  simp only [traceRightAlong_apply, mul_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_one]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end Matrix
