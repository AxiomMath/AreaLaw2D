/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`partialTraceRight_submatrix_prod_equiv` (Apache 2.0). Adaptations: QICLean's
`Matrix.partialTraceRight` is Physlib's `Matrix.traceRight`; the scalars are any additive
commutative monoid instead of `ℂ`.
-/
import QuantumInfo.ForMathlib.Matrix

/-!
# Naturality of the right partial trace in a product reindexing

Reindexing both tensor factors of a square matrix on `α × β` by equivalences and then tracing
out the second factor is the same as tracing first and reindexing the remaining factor.
-/

namespace Matrix

/-- The right partial trace is natural in a product reindexing of both factors. -/
theorem traceRight_submatrix_prodCongr {R α α' β β' : Type*} [AddCommMonoid R]
    [Fintype β] [Fintype β'] (eα : α ≃ α') (eβ : β ≃ β') (Z : Matrix (α × β) (α × β) R) :
    traceRight (Z.submatrix (eα.prodCongr eβ).symm (eα.prodCongr eβ).symm) =
      (traceRight Z).submatrix eα.symm eα.symm := by
  ext i j
  simp only [traceRight, of_apply, submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map]
  exact eβ.symm.sum_comp (fun b => Z (eα.symm i, b) (eα.symm j, b))

end Matrix
