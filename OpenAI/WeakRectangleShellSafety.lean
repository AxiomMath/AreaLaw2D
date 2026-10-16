/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/WeakRectangleShellSafety.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw` renamed to `OpenAI`. The rectangle encoding is that of
`OpenAI.SafeRectangleDilation`: `Q.toFinset` is `Q`, `Q.dilate j` is `ambientDilation Q j`,
`Q.size` is `boxSize Q`, and `IsSafe` takes a real `D₀ ≥ 0`. TNLean's
`Geometry.latticeDyadicRect k z` is `OpenAI.Geometry.latticeDyadicCell k z`, already a
`Finset`.
-/
import OpenAI.SafeRectangleDilation
import OpenAI.Geometry.CappedDyadicPartition

/-!
# Safety of selected squares in a weak-rectangle shell

A safe set `Q` controls the selected dyadic squares of side at most `2^K ≤ L` in its dilated
shell `Q^{+j} \ Q`, `j ≤ L`, whenever the square and dilation radii fit in its original
clearance, `D₀ L + L ≤ D₀ size Q`. This uses the safe-box condition and does not require
template separation.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026, proof
  of Proposition 9.5, `08-scanner.tex`, lines 717–729, at
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI

/-- Every selected square is safe when the cap and dilation radii fit in the parent clearance.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 723–729. -/
theorem IsSafe.isSafe_cappedDyadicPartition_shell {D₀ : ℝ} {Λ A Q : Finset (ℤ × ℤ)}
    (hsafe : IsSafe D₀ Λ A Q) (hD₀ : 0 ≤ D₀) (j L K k : ℕ) (z : ℤ × ℤ)
    (hj : j ≤ L) (hcap : 2 ^ K ≤ L)
    (hbudget : D₀ * L + L ≤ D₀ * boxSize Q)
    (hcell : (k, z) ∈ Geometry.cappedDyadicPartition (ambientDilation Q j \ Q) K) :
    IsSafe D₀ Λ A (Geometry.latticeDyadicCell k z) := by
  obtain ⟨hk, hsub, _⟩ := (Geometry.mem_cappedDyadicPartition _ _ _ _).mp hcell
  have hsize : boxSize (Geometry.latticeDyadicCell k z) ≤ L := by
    rw [Geometry.boxSize_latticeDyadicCell]
    exact (Nat.pow_le_pow_right (n := 2) (by decide) hk).trans hcap
  have hsizeR : (boxSize (Geometry.latticeDyadicCell k z) : ℝ) ≤ L := by exact_mod_cast hsize
  have hjR : (j : ℝ) ≤ L := by exact_mod_cast hj
  refine hsafe.of_subset_dilate hD₀ (j := j) (hsub.trans Finset.sdiff_subset) ?_
  nlinarith [mul_le_mul_of_nonneg_left hsizeR hD₀]

end OpenAI
