/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`, file `QICLean/Analysis/EntropyContinuity.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import Arealaw.VonNeumann
import OpenAI.HermitianCfcSpectral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Continuity of the von Neumann entropy

The von Neumann entropy `S(ρ) = Tr η(ρ)`, with `η(t) = -t log t`, is continuous along
continuous families of Hermitian matrices whose eigenvalues stay in `[0, 1]`, because `η` is
continuous on `[0, 1]` and the continuous functional calculus is continuous in the operator.

This version uses the repository's canonical `Arealaw.vonNeumann` definition.
-/

open Matrix Real
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem vonNeumann_eq_re_trace_cfc {ρ : Matrix m m ℂ} (hρ : ρ.IsHermitian) :
    Arealaw.vonNeumann hρ = RCLike.re (cfc negMulLog ρ).trace := by
  rw [Arealaw.vonNeumann, hρ.cfc_eq, IsHermitian.trace_cfc_eq_sum_re]
  simp only [map_neg]
  rw [hρ.trace_cfc_eq_sum_re]
  simp [Real.negMulLog]

/-- **Continuity of the entropy** along a continuous family of Hermitian matrices with
eigenvalues in `[0, 1]`. -/
theorem continuousOn_vonNeumann {X : Type*} [TopologicalSpace X]
    {ρ : X → Matrix m m ℂ} (hρ : ∀ x, (ρ x).IsHermitian) {T : Set X} (hc : ContinuousOn ρ T)
    (hspec : ∀ x ∈ T, ∀ i, (hρ x).eigenvalues i ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun x => Arealaw.vonNeumann (hρ x)) T := by
  simp_rw [vonNeumann_eq_re_trace_cfc]
  have hcfc : ContinuousOn (fun x => cfc negMulLog (ρ x)) T :=
    ContinuousOn.cfc' isCompact_Icc negMulLog hc (fun x hx => by
      rw [(hρ x).spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      exact hspec x hx i) (fun x _ => (hρ x).isSelfAdjoint) continuous_negMulLog.continuousOn
  exact RCLike.continuous_re.comp_continuousOn
    (continuous_id.matrix_trace.comp_continuousOn hcfc)

end Matrix
