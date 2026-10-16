/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/MarginalSupport.lean` (Apache 2.0). Only
`Matrix.PosSemidef.proj_mul_eq_zero_of_trace_eq_zero` is ported; the tripartite marginal
support lemma and its partial-trace helpers serve QICLean's derivation of strong subadditivity
from data processing, which the repository does not use.
-/
import OpenAI.MatrixSqrt

/-!
# A projection with zero expectation annihilates a positive semidefinite matrix

For positive semidefinite `ρ` and a Hermitian idempotent `Q`, `tr (Q ρ) = 0` forces `Q ρ = 0`.
Writing `ρ = R R` with `R = √ρ`, the hypothesis reads `tr ((Q R)ᴴ (Q R)) = 0`, so `Q R = 0`.
This is the operator core of the support-projector absorption identities of
`OpenAI.MarginalSupportAbsorption`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8
  (Distance Measures)][Wolf2012QChannels].
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- **A Hermitian idempotent with zero expectation annihilates a positive
semidefinite matrix.** For positive semidefinite $\rho$ and a projection $Q$
(`IsHermitian` together with $Q Q = Q$), $\operatorname{tr}(Q \rho) = 0$ forces
$Q \rho = 0$: indeed $\operatorname{tr}(Q \rho) = \lVert Q \sqrt\rho \rVert_2^2$. -/
theorem PosSemidef.proj_mul_eq_zero_of_trace_eq_zero {ρ Q : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (htr : (Q * ρ).trace = 0) : Q * ρ = 0 := by
  classical
  set R : Matrix n n ℂ := hρ.isHermitian.cfc Real.sqrt with hR
  have hR_herm : R.IsHermitian := hρ.cfc_sqrt_isHermitian
  have hRR : R * R = ρ := hρ.cfc_sqrt_mul_self
  have hconj : (Q * R)ᴴ = R * Q := by
    rw [Matrix.conjTranspose_mul, hR_herm.eq, hQ.eq]
  have hexp : (Q * R)ᴴ * (Q * R) = R * Q * R := by
    rw [hconj]
    calc R * Q * (Q * R) = R * (Q * Q) * R := by
            simp only [Matrix.mul_assoc]
      _ = R * Q * R := by rw [hQ2]
  have htr2 : ((Q * R)ᴴ * (Q * R)).trace = 0 := by
    rw [hexp]
    calc (R * Q * R).trace = (Q * R * R).trace := (Matrix.trace_mul_cycle Q R R).symm
      _ = (Q * ρ).trace := by rw [Matrix.mul_assoc, hRR]
      _ = 0 := htr
  have hQR : Q * R = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr2
  calc Q * ρ = Q * (R * R) := by rw [hRR]
    _ = (Q * R) * R := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hQR, Matrix.zero_mul]

end Matrix
