/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/FrontPrefixFamily.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`.
-/
import OpenAI.Scan.FrontThresholds
import OpenAI.Scan.PrefixFiniteFamily

/-!
# One finite prefix family for all scanner fronts

The original region, depth function and collar depth determine a finite nested
family before any band, offset or round is chosen. Both deterministic comparison
fronts select members of this same family throughout the fill horizon.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, and Lemma 9.1(2), lines 243–250,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI.Scan.CollarScan

/-- Both actual deterministic comparison fronts select members of the same
finite prefix family, fixed before the band, offset and round are chosen. -/
theorem front_positiveDepthPrefix_mem_fixed_family {V I : Type*}
    (S : CollarScan V I) {L : ℕ} (hn : 0 < S.n) (hL : 8 * S.K * S.m ≤ L) :
    let Q := fun i : Fin (L + 1) ↦ positiveDepthPrefix S.A S.depth (i.val : ℤ)
    ∀ (g : Fin S.K) (r : Fin S.m) (t : ℕ), t ≤ S.n * S.m →
      positiveDepthPrefix S.A S.depth (S.front g r t false - 1) ∈ Set.range Q ∧
      positiveDepthPrefix S.A S.depth (-S.front g r t true) ∈ Set.range Q := by
  dsimp only
  intro g r t ht
  have hfront := S.front_comparison_thresholds_le g r hn ht hL
  exact ⟨positiveDepthPrefix_mem_range_fin_of_le S.A S.depth hfront.1,
    positiveDepthPrefix_mem_range_fin_of_le S.A S.depth hfront.2⟩

end OpenAI.Scan.CollarScan
