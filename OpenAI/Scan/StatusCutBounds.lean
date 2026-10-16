/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/StatusCutBounds.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Only the two region identities
are ported. The cut-edge bounds `state_cut_bounds_domainGraph` and
`oldChargeState_cut_bounds_domainGraph` (and their private core) are stated with TNLean's
unordered induced-graph `edgeBoundary Λ` on `Site Λ` and use the prefix boundary bounds of
`TNLean/PEPS/AreaLaw/Scan/PrefixBoundary.lean` and the calculus of
`TNLean/PEPS/AreaLaw/EdgeBoundaryCalculus.lean`, neither of which has a counterpart over this
project's `OpenAI.edgeBoundary`.
-/
import OpenAI.Scan.PrefixApproximation

/-!
# Region identities for actual scan statuses

Because the actual middle has positive depth, removing the positive-depth near region from
the positive-depth near-with-middle region leaves exactly the middle `Y`. The far receiving
side is the complement of the near side and the middle. These identities feed the cut-edge
bounds of Lemma 9.1(2): `20nD` edges for `U` and `UY`, hence `40nD` for `Y`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 243–260, at `openai/math@adc7f124`.
-/

namespace OpenAI.Scan

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing the near region from the near-with-middle region leaves exactly
Y, because the actual middle has positive depth. -/
theorem middle_eq_positiveNearMiddle_sdiff_positiveNear (depth : V → ℤ)
    (σ : PhysicalPartition V) (hpos : ∀ x, σ x = none → 0 < depth x) :
    middle σ = positiveNearMiddle depth σ \ positiveNear depth σ := by
  ext x
  cases he : σ x with
  | none => simp [middle, positiveNearMiddle, positiveNear, receiving, he, hpos x he]
  | some b => cases b <;> simp [middle, positiveNearMiddle, positiveNear, receiving, he]

/-- The far receiving side is the complement of the near side and middle. -/
theorem receiving_far_eq_compl (σ : PhysicalPartition V) :
    receiving σ true = (receiving σ false ∪ middle σ)ᶜ := by
  ext x
  cases he : σ x with
  | none => simp [receiving, middle, he]
  | some b => cases b <;> simp [receiving, middle, he]

end OpenAI.Scan
