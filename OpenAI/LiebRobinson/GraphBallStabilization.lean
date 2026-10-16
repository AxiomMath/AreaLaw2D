/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/Circuit/LiebRobinson/GraphBallStabilization.lean` (Apache 2.0).  Adaptations: along the
cone TNLean's finite graph is only ever the induced square lattice `domainGraph Λ` on
`Site Λ`, so the statements are made there: `graphBall G a l` is `OpenAI.graphNbhd Λ {a} l`,
`G.edist a y` is `OpenAI.domainEDist Λ a y`, `{x | G.Reachable a x}` is
`OpenAI.domainComponent Λ a`, the cutoff `Finset.univ.sup (G.dist a)` is
`Λ.sup fun x => (domainEDist Λ a x).toNat`, and the equality of sets is an equality of
`Finset`s.  `graphNbhd_mono` is stated for every centre set `S`.  TNLean `mem_graphBall`
(`TNLean/Circuit/LiebRobinson/GraphLocalization.lean`) is
`mem_graphNbhd_singleton_iff_domainEDist_le`.
-/
import OpenAI.Basic

/-!
# Exact stabilization of graph balls

The graph balls `N_l(a)` of the induced square lattice on `Λ` increase with `l`, never contain a
site at infinite distance from `a`, and equal the connected component of `a` once `l` is at
least the largest finite distance from `a` [OAI265, §10.1, after eq. (10.9): exact component
support].  Membership in a ball is measured by the extended distance, so sites of other
components never enter, although their truncated natural distance is the junk value `0`.
-/

namespace OpenAI

variable {Λ : Finset (ℤ × ℤ)} {a x y : ℤ × ℤ}

/-- Membership in a graph ball in the orientation `d_Λ(a, x) ≤ l`. -/
theorem mem_graphNbhd_singleton_iff_domainEDist_le {l : ℕ} :
    x ∈ graphNbhd Λ {a} l ↔ domainEDist Λ a x ≤ l := by
  simp only [graphNbhd, Finset.mem_filter, Finset.mem_singleton, iInf_iInf_eq_left]
  rw [domainEDist_comm]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  by_contra hx
  rw [domainEDist_of_not_mem_right hx] at h
  exact absurd h (by simp)

/-- Graph neighbourhoods increase with their radius [OAI265, §10.1, eq. (10.9)]. -/
theorem graphNbhd_mono (Λ S : Finset (ℤ × ℤ)) : Monotone (graphNbhd Λ S) := by
  intro m n hmn z hz
  simp only [graphNbhd, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.trans (by exact_mod_cast hmn)⟩

/-- A site at infinite distance lies in no graph ball [OAI265, §10.1, after eq. (10.9)]. -/
theorem notMem_graphNbhd_singleton_of_domainEDist_eq_top (hy : domainEDist Λ a y = ⊤)
    (n : ℕ) : y ∉ graphNbhd Λ {a} n := by
  rw [mem_graphNbhd_singleton_iff_domainEDist_le, hy]
  exact not_le_of_gt (ENat.natCast_lt_top n)

/-- Beyond the largest finite distance from `a`, the graph ball of `a` is its connected
component; no connectedness or diameter assumption is needed
[OAI265, §10.1, after eq. (10.9)]. -/
theorem graphNbhd_singleton_eq_domainComponent_of_sup_le (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    {n : ℕ} (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n) :
    graphNbhd Λ {a} n = domainComponent Λ a := by
  ext x
  rw [mem_graphNbhd_singleton_iff_domainEDist_le, domainComponent, Finset.mem_filter]
  constructor
  · intro hx
    have hne : domainEDist Λ a x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hx
    refine ⟨?_, hne⟩
    by_contra hxΛ
    exact hne (domainEDist_of_not_mem_right hxΛ)
  · rintro ⟨hxΛ, hne⟩
    rw [← ENat.natCast_toNat hne]
    exact_mod_cast (Finset.le_sup (f := fun x => (domainEDist Λ a x).toNat) hxΛ).trans hn

/-- The graph balls of `a` stabilize exactly on its connected component
[OAI265, §10.1, after eq. (10.9)]. -/
theorem exists_graphNbhd_singleton_eq_domainComponent (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) :
    ∃ N, ∀ n ≥ N, graphNbhd Λ {a} n = domainComponent Λ a :=
  ⟨Λ.sup fun x => (domainEDist Λ a x).toNat, fun _ hn =>
    graphNbhd_singleton_eq_domainComponent_of_sup_le Λ a hn⟩

end OpenAI
