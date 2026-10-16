/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/SafeRectangleDilation.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw` renamed to `OpenAI`. The rectangle layer is the repository's
(`OpenAI.Rectangles`, as in `OpenAI.BufferedRectangles`): TNLean's `IntRect` is a
`Finset (ℤ × ℤ)`, `Q.size` is `boxSize Q`, `Q.dilate j` is `ambientDilation Q j`, the cut is a
`Finset (ℤ × ℤ)`, and `IsSafe` takes a real `D₀`, so the statement assumes `0 ≤ D₀` where the
source has `D₀ : ℕ`.
-/
import OpenAI.Rectangles

/-!
# Safety inside a dilated parent rectangle

A safe parent controls every smaller set contained in its dilation, provided the smaller set's
safety radius plus the dilation radius fits inside the parent's safety radius.

## Implementation notes

No rectangle structure is used: the statement holds for finite sets `Q` and `Q'` of `ℤ²`.
For negative `D₀` it fails: with `D₀ = -1`, `Q = {(0, 0)}`, `Q' = {(0, 0), (1, 0)}`, `j = 1`
and `(1, 0)` an endpoint of a crossing edge, `Q` is safe and the budget holds, but `Q'` meets
the cut.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026, proof
  of Proposition 9.5 (`prop:small-box`), `08-scanner.tex`, lines 707–729, at
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI

/-- Safety passes from a parent to a set in its dilation when the two radii fit inside the
parent's safety radius. Source: `08-scanner.tex`, lines 723–729, in the proof of
Proposition 9.5 (`prop:small-box`). -/
theorem IsSafe.of_subset_dilate {D₀ : ℝ} {Λ A Q Q' : Finset (ℤ × ℤ)} {j : ℕ}
    (hsafe : IsSafe D₀ Λ A Q) (hD₀ : 0 ≤ D₀) (hsub : Q' ⊆ ambientDilation Q j)
    (hbudget : D₀ * boxSize Q' + j ≤ D₀ * boxSize Q) : IsSafe D₀ Λ A Q' := by
  rw [isSafe_iff hD₀]
  intro x hx z hz
  obtain ⟨y, hy, h1, h2⟩ := mem_ambientDilation.mp (hsub hx)
  have hxy : dist y x ≤ j := by
    rw [dist_comm, dist_eq_max_abs]
    exact_mod_cast max_le h1 h2
  have hfar := hsafe.lt_dist hy hz
  have htri := dist_triangle y x z
  linarith

end OpenAI
