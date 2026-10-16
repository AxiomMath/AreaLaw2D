/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit ed700e7b45ffea4379e980b222094136800de55e,
`QICLean/Entropy/RestoringMarginal.lean` (Apache 2.0).

Adaptations: QICLean `Matrix.partialTraceRight` is Physlib `Matrix.traceRight` (declaration
names keep `partialTraceRight`); `partialTraceRight_apply` is unfolded as `traceRight, of_apply`,
`map_sub partialTraceRightLM` is Physlib `Matrix.traceRight_sub`, and
`PosSemidef.partialTraceRight` is Physlib `PosSemidef.traceRight`.
-/
import OpenAI.PosSemidefCommute
import QuantumInfo.ForMathlib.Matrix
import Mathlib.Algebra.Star.StarProjection

/-!
# The reduced matrix in singular restoration

For a positive matrix `ρ` on `X × Y`, a spectral projection `Q` commuting
with `ρ`, and a projection `T` on `Y`, the actual reduced matrix
`tr_Y ((I ⊗ T) ρ Q)` is positive and bounded above by `tr_Y ρ`.
The projections `Q` and `I ⊗ T` need not commute. Cyclicity within the
traced factor converts the one-sided expression into a positive compression.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `09-amplification.tex`, lines 417–446.
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex>
Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open scoped MatrixOrder ComplexOrder Kronecker

namespace Matrix

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

/-- Factors acting only on the traced system can be cycled across the partial trace. -/
theorem partialTraceRight_mul_one_kronecker (A : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) :
    traceRight (A * ((1 : Matrix X X ℂ) ⊗ₖ T)) =
      traceRight (((1 : Matrix X X ℂ) ⊗ₖ T) * A) := by
  classical
  ext i j
  simp only [traceRight, of_apply, mul_apply, Fintype.sum_prod_type,
    kroneckerMap_apply, one_apply, mul_ite, ite_mul, one_mul, zero_mul, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [Fintype X] [DecidableEq X] in
/-- The partial trace preserves matrix order. -/
theorem partialTraceRight_mono [Finite X] {A B : Matrix (X × Y) (X × Y) ℂ}
    (h : A ≤ B) : traceRight A ≤ traceRight B := by
  classical
  let := Fintype.ofFinite X
  have hp := (nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).traceRight.nonneg
  have heq : traceRight (B - A) = traceRight B - traceRight A :=
    traceRight_sub
  rw [heq] at hp
  exact sub_nonneg.mp hp

/-- A projection on the traced factor can be placed on both sides without
changing the partial trace. -/
theorem partialTraceRight_projection_sandwich (A : Matrix (X × Y) (X × Y) ℂ)
    {T : Matrix Y Y ℂ} (hT : IsStarProjection T) :
    traceRight (((1 : Matrix X X ℂ) ⊗ₖ T) * A * (1 ⊗ₖ T)) =
      traceRight ((1 ⊗ₖ T) * A) := by
  classical
  let K := (1 : Matrix X X ℂ) ⊗ₖ T
  have hK : K * K = K := by
    dsimp [K]
    rw [← mul_kronecker_mul, one_mul, hT.isIdempotentElem.eq]
  change traceRight (K * A * K) = traceRight (K * A)
  calc
    _ = traceRight ((A * K) * K) := by
      rw [mul_assoc]
      exact (partialTraceRight_mul_one_kronecker (A * K) T).symm
    _ = traceRight (A * K) := by rw [mul_assoc, hK]
    _ = traceRight (K * A) := partialTraceRight_mul_one_kronecker A T

/-- Compressing a positive matrix on the traced factor decreases its partial trace. -/
theorem partialTraceRight_projection_sandwich_le {A : Matrix (X × Y) (X × Y) ℂ}
    (hA : A.PosSemidef) {T : Matrix Y Y ℂ} (hT : IsStarProjection T) :
    traceRight (((1 : Matrix X X ℂ) ⊗ₖ T) * A * (1 ⊗ₖ T)) ≤
      traceRight A := by
  classical
  let K := (1 : Matrix X X ℂ) ⊗ₖ T
  let J := (1 : Matrix X X ℂ) ⊗ₖ (1 - T)
  have hJstar : Jᴴ = J := by
    dsimp [J]
    rw [conjTranspose_kronecker, conjTranspose_one]
    exact congrArg ((1 : Matrix X X ℂ) ⊗ₖ ·) hT.one_sub.isSelfAdjoint.star_eq
  have hp : 0 ≤ traceRight (J * A * J) := by
    simpa only [hJstar] using (hA.mul_mul_conjTranspose_same J).traceRight.nonneg
  have hsum : traceRight (K * A * K) + traceRight (J * A * J) =
      traceRight A := by
    rw [partialTraceRight_projection_sandwich A hT,
      partialTraceRight_projection_sandwich A hT.one_sub,
      ← traceRight_add, ← add_mul]
    have hKJ : K + J = 1 := by
      dsimp [K, J]
      rw [← kronecker_add, add_sub_cancel, one_kronecker_one]
    rw [hKJ, one_mul]
  exact (le_add_of_nonneg_right hp).trans_eq hsum

/-- The actual reduced matrix used in the restoring-operator ground-component estimate. -/
noncomputable def restoringMarginal (ρ Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) : Matrix X X ℂ :=
  traceRight (((1 : Matrix X X ℂ) ⊗ₖ T) * ρ * Q)

/-- The reduced matrix is positive without commutation between the two projections.
Source: `09-amplification.tex`, lines 417–446. -/
theorem restoringMarginal_nonneg {ρ Q : Matrix (X × Y) (X × Y) ℂ}
    (hρ : ρ.PosSemidef) (hQ : IsStarProjection Q) (hρQ : Commute ρ Q)
    {T : Matrix Y Y ℂ} (hT : IsStarProjection T) : 0 ≤ restoringMarginal ρ Q T := by
  classical
  have hA := hρ.mul_of_commute (nonneg_iff_posSemidef.mp hQ.nonneg) hρQ.eq
  let K := (1 : Matrix X X ℂ) ⊗ₖ T
  have hKstar : Kᴴ = K := by
    dsimp [K]
    rw [conjTranspose_kronecker, conjTranspose_one]
    exact congrArg ((1 : Matrix X X ℂ) ⊗ₖ ·) hT.isSelfAdjoint.star_eq
  have hp := (hA.mul_mul_conjTranspose_same K).traceRight.nonneg
  rw [hKstar, partialTraceRight_projection_sandwich (ρ * Q) hT] at hp
  simpa only [restoringMarginal, mul_assoc] using hp

/-- The restoring reduced matrix is dominated by the original marginal; this
order relation is proved from the actual partial trace, not assumed.
Source: `09-amplification.tex`, lines 417–446. -/
theorem restoringMarginal_le {ρ Q : Matrix (X × Y) (X × Y) ℂ}
    (hρ : ρ.PosSemidef) (hQ : IsStarProjection Q) (hρQ : Commute ρ Q)
    {T : Matrix Y Y ℂ} (hT : IsStarProjection T) :
    restoringMarginal ρ Q T ≤ traceRight ρ := by
  classical
  have hA := hρ.mul_of_commute (nonneg_iff_posSemidef.mp hQ.nonneg) hρQ.eq
  have hcomp : ρ * (1 - Q) = (1 - Q) * ρ := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hρQ.eq]
  have hAQ : ρ * Q ≤ ρ := by
    have hp := (hρ.mul_of_commute (nonneg_iff_posSemidef.mp hQ.one_sub.nonneg) hcomp).nonneg
    exact sub_nonneg.mp (by simpa only [mul_sub, mul_one] using hp)
  have hle := partialTraceRight_projection_sandwich_le hA hT
  rw [partialTraceRight_projection_sandwich (ρ * Q) hT] at hle
  have hfirst : restoringMarginal ρ Q T ≤ traceRight (ρ * Q) := by
    simpa only [restoringMarginal, mul_assoc] using hle
  exact hfirst.trans (partialTraceRight_mono hAQ)

end Matrix
