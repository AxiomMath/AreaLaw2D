/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/TraceDistance.lean` (Apache 2.0), partially: only
`Matrix.trace_partialTraceRight_mul`. QICLean's `Matrix.partialTraceRight` is Physlib's
`Matrix.traceRight` (the same formula), and the statement is the reverse of Physlib's
`Matrix.trace_mul_kron_one_right`. The source's `Matrix.traceDistance` API is not ported:
the repo has `Arealaw.SubState.D₁` (`Arealaw.TraceDist`) and
`OpenAI.ConditionalMovement.traceDistance` (`OpenAI.ConditionalMovement.EntropyContinuity`).
-/
import QuantumInfo.ForMathlib.Matrix

/-!
# The right partial trace is adjoint to tensoring with the identity

`tr (tr_β(Y) X) = tr (Y (X ⊗ 1))` for `Y` on `α × β` and `X` on `α`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 2, `build/sections/01-preliminaries.tex`,
  lines 27–28 and 33–35.
-/

open scoped Kronecker

namespace Matrix

/-- The right partial trace is adjoint to tensoring with the identity on the
right: `tr (tr_β(Y) X) = tr (Y (X ⊗ 1))`. -/
theorem trace_partialTraceRight_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (X : Matrix α α ℂ) (Y : Matrix (α × β) (α × β) ℂ) :
    (traceRight Y * X).trace = (Y * (X ⊗ₖ (1 : Matrix β β ℂ))).trace :=
  (trace_mul_kron_one_right Y X).symm

end Matrix
