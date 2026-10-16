/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/LatticeCounts.lean` (Apache 2.0). Namespace `TNLean.PEPS.AreaLaw`
renamed to `OpenAI`; TNLean's `Site Λ` and `domainGraph Λ` are replaced by the sites
`↥(Λ : Set (ℤ × ℤ))` and the induced square-lattice graph
`(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`, its `graphBall` by the corresponding filter of
`Finset.univ`, and its `AdmissibleSupport Λ R` by the subtype of `supports Λ R`.
`card_anchor_fiber_le` is renamed `card_anchor_fiber_le_diamond`, the name being taken by the
coarser bound of `OpenAI.FiniteSetTruncation`.
-/
import OpenAI.BufferedRectangles

/-!
# Counting bounds on an induced square-lattice domain

The graph-theoretic results of Section 4 of [OAI265] take as hypotheses the counts of §2.2:
graph balls of radius `d` have at most a constant times `(d + 1)²` sites, and at most
`μ_R = 2 ^ (v_R - 1)` supports contain a given site, `v_R = 1 + 2 R (R + 1)`, so at most `μ_R`
labels share an anchor. The count of supports containing a site is
`OpenAI.card_admissibleSupport_containing_le`; this file adds the ball count and the anchor
multiplicity on the induced nearest-neighbour graph of an arbitrary finite domain, holes and
disconnected components included, from the ambient diamond count `eq:ball-count`.

## Implementation notes

TNLean's `card_cutEdges_le_card_edgeBoundary`, which compares ordered cut edges of the induced
graph with its unordered edge boundary, is not ported: the edge boundary `edgeBoundary Λ X` is
already a set of ordered pairs.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `eq:ball-count` and the multiplicity bound after it (`01-preliminaries.tex`, lines 82–103),
  and `eq:quasilocal-budget` (`03-quasilocal.tex`, lines 30–40).
-/

namespace OpenAI

open SimpleGraph

variable {Λ : Finset (ℤ × ℤ)}

/-- **Ball count** [OAI265, §2.2, `eq:ball-count`]: a graph ball of radius `d` in an induced
domain has at most `1 + 2 d (d + 1) ≤ 2 (d + 1)²` sites. -/
theorem card_graphBall_domainGraph_le (x : (Λ : Set (ℤ × ℤ))) (d : ℕ) :
    ((Finset.univ.filter fun y ↦
        ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist x y ≤ d).card : ℝ) ≤
      2 * ((d : ℝ) + 1) ^ 2 := by
  classical
  have h := card_le_diamond_of_edist_le
    (G := (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))) Subtype.val
    (Finset.univ.filter fun y ↦
      ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist x y ≤ d) Subtype.val_injective
    (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h) x d fun y hy ↦ (Finset.mem_filter.1 hy).2
  have h' : ((Finset.univ.filter fun y ↦
      ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist x y ≤ d).card : ℝ) ≤
        1 + 2 * d * (d + 1) := by
    exact_mod_cast h
  nlinarith

/-- **Anchor multiplicity** [OAI265, §4, `eq:quasilocal-budget`]: if every label is anchored
inside its support, at most `μ_R = 2 ^ (v_R - 1)` labels share an anchor,
`v_R = 1 + 2 R (R + 1)`. -/
theorem card_anchor_fiber_le_diamond {R : ℕ} (a : supports Λ R → (Λ : Set (ℤ × ℤ)))
    (ha : ∀ X, (a X : ℤ × ℤ) ∈ X.1) (x : (Λ : Set (ℤ × ℤ))) :
    (Finset.univ.filter fun X ↦ a X = x).card ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
  (Finset.card_le_card fun X hX ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
    exact hX ▸ ha X).trans (card_admissibleSupport_containing_le (Λ := Λ) (R := R) x.1)

end OpenAI
