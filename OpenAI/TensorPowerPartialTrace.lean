/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Algebra/TensorPowerPartialTrace.lean` (Apache 2.0). Adaptations: QICLean's
`Matrix.partialTraceRight` is Physlib's `Matrix.traceRight`; `partialTraceRight_apply` is the
definitional unfolding of `Matrix.traceRight`; the unused `Fintype A`, `Fintype Q` binders are
dropped.
-/
import OpenAI.KroneckerFactorPositivity

/-!
# Partial traces of regrouped tensor powers

The partial trace of a tensor product is the tensor product of its partial
traces. The coordinate equivalence below applies one fixed bipartite
decomposition to each copy and then collects all copies of each factor.
No positivity or normalization is needed.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker

namespace TensorPower

/-- Apply a bipartite coordinate decomposition to each copy, then collect
the two families of factors. Source: `07-comparators.tex`, lines 550–560. -/
def copiesProductEquiv {A Q T : Type*} (e : A ≃ Q × T) (m : ℕ) :
    (Fin m → A) ≃ (Fin m → Q) × (Fin m → T) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) e).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Q) (fun _ => T))

end TensorPower

namespace Matrix

/-- The partial trace of the actual regrouped tensor product is the tensor
product of the actual one-copy partial traces. The factors need not agree.
Source: `07-comparators.tex`, lines 550–560. -/
theorem partialTraceRight_finKronecker_reindex
    {A Q T : Type*} [Fintype T]
    (e : A ≃ Q × T) (m : ℕ) (M : Fin m → Matrix A A ℂ) :
    traceRight ((finKronecker M).submatrix
      (TensorPower.copiesProductEquiv e m).symm
      (TensorPower.copiesProductEquiv e m).symm) =
        finKronecker (fun j => traceRight ((M j).submatrix e.symm e.symm)) := by
  ext x y
  simp only [traceRight, of_apply, submatrix_apply, finKronecker_apply]
  exact (Fintype.prod_sum
    (fun (j : Fin m) (t : T) => M j (e.symm (x j, t)) (e.symm (y j, t)))).symm

end Matrix
