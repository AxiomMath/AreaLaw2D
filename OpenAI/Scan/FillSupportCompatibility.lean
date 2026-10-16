/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/FillSupportCompatibility.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's
domain encoding: TNLean's `Site Λ` and `domainGraph Λ` are `↥(Λ : Set (ℤ × ℤ))` and
`(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`, and `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, as in
`OpenAI.Scan.SupportLocalization`. The `_domainGraph` declaration names are kept.
-/
import OpenAI.Scan.FillTransport
import OpenAI.Scan.SupportCompatibility

/-!
# Designated supports at actual fill leaves

The completed and pre-charge support classifications apply to the two
terminal statuses of a deterministic fill. The support is embedded only
in the physical factors; neither auxiliary factor is added.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 336–352, and `08-scanner.tex`, Lemma 9.1(1),
at `openai/math@adc7f124`.
-/

namespace OpenAI.Scan

open SimpleGraph TensorPower.ReplicaTransport

variable {I : Type*} [Fintype I] [LinearOrder I]

namespace CollarScan

/-- Both endpoints of an actual fill satisfy designated-support compatibility,
derived from the geometric scanner hypotheses rather than supplied as a premise. -/
theorem fillTransportData_supportCompatible_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (n : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool → ℕ) (E : EnergyTerms (↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) :
    (S.fillTransportData histTree).SupportCompatible E := by
  rintro ⟨h, c⟩ i g
  simp only [hsupport]
  cases c with
  | none =>
    change (augmentedPartition (S.state h g)).Contains _ ∨ _
    rcases state_designatedSupport_classification_domainGraph hT S hgraph hdepth h
      hn (Nat.le_of_succ_le hk) hr hDpos hD hL hrows hclear g i with hc | ⟨side, hs⟩
    · exact Or.inl (augmentedPartition_contains_of_constant _ _ hc)
    · exact Or.inr hs.augmented
  | some c =>
    simp only [TransportData.leafPart, fillTransportData_new]
    rcases old_designatedSupport_classification_domainGraph hT S hgraph hdepth h
      hn hk hr hDpos hD hL hrows hclear g i with hc | ⟨side, hs⟩
    · exact Or.inl (augmentedPartition_contains_of_constant _ _ hc)
    · exact Or.inr hs.augmented

end CollarScan
end OpenAI.Scan
