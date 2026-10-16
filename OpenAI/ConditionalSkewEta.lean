/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/ConditionalSkewPhase.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
conditional-mutual-information bounds portion.
-/
import OpenAI.ConditionalEntropy
import OpenAI.ConditionalSkewPhaseCore

/-! # Entropic bounds for the conditional skew estimate -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open Matrix Entropy.MarginalPhase

section EtaBounds

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- Strong subadditivity: `I(X:F|U) ≥ 0`. -/
theorem condMutualInfo_nonneg {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
    (hρ : ρ.PosSemidef) :
    0 ≤ condMutualInfo ρ hρ := by
  have h := Arealaw.vonNeumann_strong_subadditivity hρ
  have hU := marginalU_eq ρ
  change (ρ.submatrix assocE assocE).traceRight.traceLeft =
    ρ.traceLeft.traceRight at hU
  unfold condMutualInfo
  rw [Arealaw.vonNeumann_congr
    (hρ.submatrix assocE).traceRight.traceLeft.isHermitian
    hρ.traceLeft.traceRight.isHermitian hU]
  linarith

/-- `I(X:F|U) ≤ 2 log (dim X)` for a density matrix. -/
theorem condMutualInfo_le_two_log {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    condMutualInfo ρ hρ ≤ 2 * Real.log (Fintype.card X) := by
  have h1 := Arealaw.abs_vonNeumann_sub_traceLeft_le hρ
  have h2 := Arealaw.abs_vonNeumann_sub_traceLeft_le
    ((hρ.submatrix assocE).traceRight)
  rw [htr] at h1
  rw [traceRight_trace, trace_submatrix, htr] at h2
  norm_num at h1 h2
  rw [abs_le] at h1 h2
  unfold condMutualInfo
  linarith [h1.1, h1.2, h2.1, h2.2]

end EtaBounds

end Entropy.ConditionalSkew
