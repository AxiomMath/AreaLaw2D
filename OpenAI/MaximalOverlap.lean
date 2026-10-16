/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Channel/MaximalOverlap.lean` (Apache 2.0). Adapted: only
`Matrix.IsHermitian.trace_eq_ofReal_re`, `Matrix.partialTraceRight_vecMulVec_eq` and
`Matrix.star_dotProduct_eq_trace_conjTranspose_mul` are ported; QICLean's
`Matrix.partialTraceRight` is Physlib's `Matrix.traceRight`, the same formula; the proof of
`Matrix.IsHermitian.trace_eq_ofReal_re` goes through `Matrix.trace_conjTranspose` rather than
the spectral theorem.
-/
import OpenAI.SchmidtRank
import QuantumInfo.ForMathlib.Matrix

/-!
# Coefficient-matrix dictionary for bipartite vectors

For a bipartite vector `φ : m × n → ℂ` with coefficient matrix `C = schmidtCoeffMatrix φ`, the
reduced density matrix `tr₂ |φ⟩⟨φ|` on the first factor is `C Cᴴ`, and the overlap `⟨φ|ψ⟩` is
the Frobenius pairing `tr (C_φᴴ C_ψ)`.  These are the two identities through which Wolf's
Chapter 3, Lemma 3.1 (maximal overlap with a fixed Schmidt rank) passes from vectors to
matrices.  A Hermitian matrix has real trace.

## Implementation notes

Vectors are over `ℂ`, as in the source.  The source's variational part (the Ky-Fan maximum
principle and Lemma 3.1 itself) is not ported here.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Lemma 3.1][Wolf2012QChannels]
-/

open scoped Matrix

namespace Matrix

/-- A Hermitian matrix has real trace: it equals the real part of its own trace,
viewed back in the complex numbers. -/
theorem IsHermitian.trace_eq_ofReal_re {p : Type*} [Fintype p]
    {M : Matrix p p ℂ} (hM : M.IsHermitian) : M.trace = ((M.trace).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (by rw [← RCLike.star_def, ← trace_conjTranspose, hM.eq])).symm

variable {m n : Type*} [Fintype n]

/-- The reduced density matrix of |φ⟩⟨φ| on the first factor is C Cᴴ, where
C is the coefficient matrix of φ. -/
theorem partialTraceRight_vecMulVec_eq (φ : m × n → ℂ) :
    traceRight (vecMulVec φ (star φ))
      = (schmidtCoeffMatrix φ) * (schmidtCoeffMatrix φ)ᴴ := by
  ext i j
  simp only [traceRight, of_apply, vecMulVec_apply, Pi.star_apply,
    Matrix.mul_apply, conjTranspose_apply, schmidtCoeffMatrix_apply, RCLike.star_def]

/-- The overlap ⟨φ|ψ⟩ is the Frobenius pairing tr(C_φᴴ C_ψ) of the coefficient
matrices. -/
theorem star_dotProduct_eq_trace_conjTranspose_mul [Fintype m] (φ ψ : m × n → ℂ) :
    star φ ⬝ᵥ ψ = ((schmidtCoeffMatrix φ)ᴴ * (schmidtCoeffMatrix ψ)).trace := by
  simp only [dotProduct, Pi.star_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    conjTranspose_apply, schmidtCoeffMatrix_apply, RCLike.star_def]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

end Matrix
