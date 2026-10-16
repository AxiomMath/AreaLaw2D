/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/ShiftedDensityTruncation.lean` (Apache 2.0). Only the closed spectral
threshold `Matrix.spectralProjectionGE` and its two structural lemmas are ported; the head and
tail of the shifted power and their bounds are not.
-/
import OpenAI.HermitianCfcSpectral

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Closed spectral threshold projections

The canonical spectral projection of a matrix onto its eigenvalues in the closed interval
`[b, ∞)`, defined through the continuous functional calculus. For a Hermitian matrix it agrees
with the Hermitian functional calculus and is an orthogonal projection.

These support the inside-space estimates in OpenAI, *Polynomial PEPS approximation of gapped
square-grid ground states*, September 24, 2026, `03-patches.tex`, lines 484–502, equation
`eq:patch-head-tail-bounds`.
-/

open scoped Matrix

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The canonical spectral projection onto eigenvalues in the closed interval `[b, ∞)`. -/
def spectralProjectionGE (A : Matrix n n ℂ) (b : ℝ) : Matrix n n ℂ :=
  cfc (fun t : ℝ ↦ if b ≤ t then 1 else 0) A

/-- The threshold is closed: eigenvalues equal to `b` belong to the head. -/
theorem IsHermitian.spectralProjectionGE_eq_cfc (hA : A.IsHermitian) (b : ℝ) :
    spectralProjectionGE A b = hA.cfc (fun t ↦ if b ≤ t then 1 else 0) :=
  hA.cfc_eq _

/-- The canonical closed-threshold projection is an orthogonal projection. -/
theorem IsHermitian.isStarProjection_spectralProjectionGE (hA : A.IsHermitian) (b : ℝ) :
    IsStarProjection (spectralProjectionGE A b) := by
  rw [isStarProjection_iff']
  constructor
  · rw [hA.spectralProjectionGE_eq_cfc, ← hA.cfc_mul]
    congr 1
    funext t
    split_ifs <;> norm_num
  · exact (cfc_predicate _ A : IsSelfAdjoint (spectralProjectionGE A b))

end Matrix
