/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Channel/MaximallyEntangled.lean` (Apache 2.0). Only `Matrix.omegaVec` and
`MaximallyEntangled.omegaCoeff_eq_inv` are ported.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Maximally entangled vector

The maximally entangled vector `|Ω⟩ = (1/√d) Σⱼ |j,j⟩` on `ℂ^d ⊗ ℂ^d`, and the value
`1 / d` of its squared normalization coefficient
([M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2, Example 1.2]).

## Implementation notes

The scalars are `ℂ` rather than a general `RCLike 𝕜`, as in the source: the consumers
(`OpenAI.UniformBellLabel`) pair this vector with the label projectors
`PermutationRepresentation.labelProj`, which are `ℂ`-valued.
-/

namespace Matrix

/-- The maximally entangled vector `|Ω⟩ = (1/√d) Σⱼ |j,j⟩` as a function
`Fin d × Fin d → ℂ`. Entry `(i, j)` is `1/√d` if `i = j` and `0` otherwise. -/
noncomputable def omegaVec (d : ℕ) : Fin d × Fin d → ℂ :=
  fun ⟨i, j⟩ => if i = j then (1 : ℂ) / ((d : ℝ).sqrt : ℂ) else 0

theorem omegaVec_apply {d : ℕ} (i j : Fin d) :
    omegaVec d (i, j) = if i = j then (1 : ℂ) / ((d : ℝ).sqrt : ℂ) else 0 := rfl

end Matrix

namespace MaximallyEntangled

variable {d : ℕ}

/-- The squared maximally-entangled normalization coefficient is `1 / d`. -/
theorem omegaCoeff_eq_inv (hd : 0 < d) :
    (((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) *
      star ((1 : ℂ) / ((d : ℝ).sqrt : ℂ))) =
      1 / (d : ℂ) := by
  have hdr : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [show star ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) =
      1 / ((d : ℝ).sqrt : ℂ) from by simp [Complex.conj_ofReal]]
  rw [show (1 : ℂ) / ((d : ℝ).sqrt : ℂ) *
      (1 / ((d : ℝ).sqrt : ℂ)) =
      1 / (((d : ℝ).sqrt : ℂ) ^ 2) from by ring]
  rw [show (((d : ℝ).sqrt : ℂ) ^ 2) = (((d : ℝ).sqrt ^ 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [Real.sq_sqrt hdr.le]
  simp

end MaximallyEntangled
