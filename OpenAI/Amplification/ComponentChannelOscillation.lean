/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ComponentChannelOscillation.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: TNLean's finite graph
`G : SimpleGraph ι` is only ever the induced square lattice on a domain `Λ`, so the statements
are made there, with sites `ℤ × ℤ`, the region `Λ` and an arbitrary local family `loc` (TNLean
`ι → Fin q`; `[NeZero q]` is `[∀ i, Nonempty (loc i)]`); `graphBall G a l` is
`OpenAI.graphNbhd Λ {a} l`, `G.edist a y` is `OpenAI.domainEDist Λ a y`, the cutoff
`Finset.univ.sup (G.dist a)` is `Λ.sup fun x => (domainEDist Λ a x).toNat`, and
`k ∈ supportedOperators q {x | G.Reachable a x}` is
`OpenAI.IsSupportedOn (domainComponent_subset Λ a) k`; `siteExpectation q K` is
`OpenAI.condExpect (h : K ⊆ Λ)`, and the localized channels and shells take the proofs
`graphNbhd_subset Λ {a}`.  TNLean `coe_graphBall_eq_reachable_of_sup_dist_le`,
`graphBall_mono`, `mem_graphBall` and `notMem_graphBall_of_edist_eq_top` are
`OpenAI.graphNbhd_singleton_eq_domainComponent_of_sup_le`, `OpenAI.graphNbhd_mono`,
`OpenAI.mem_graphNbhd_singleton_iff_domainEDist_le` and
`OpenAI.notMem_graphNbhd_singleton_of_domainEDist_eq_top`.  Declaration names are kept.
-/
import OpenAI.LiebRobinson.GraphBallStabilization
import OpenAI.Amplification.LocalChannelOscillation

/-!
# Full-channel oscillation from exact component support

An operator supported on the connected component of the anchor `a` in `Λ` is fixed by the
graph-ball expectations once the ball contains that component.  Its localized root channel then
equals its full root channel at every sufficiently large finite radius, and the finite-shell
oscillation estimate transfers to the full channel without a limit or a tail hypothesis.  A
site at infinite distance from the anchor cannot have its oscillation increased
[OAI265, §10.1, after eq. (10.9)].  The observables are arbitrary and the spectator is an
arbitrary finite system, with no spectator dimension factor.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 124–139.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Component support makes every sufficiently large ball expectation exact
[OAI265, §10.1, `09-amplification.tex`, lines 135–139]. -/
theorem siteExpectation_graphBall_eq_of_component_support (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    {n : ℕ} (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n) :
    condExpect (graphNbhd_subset Λ {a} n) k = k :=
  condExpect_of_isSupportedOn _
    (hk.mono (graphNbhd_singleton_eq_domainComponent_of_sup_le Λ a hn).superset _)

/-- The localization error vanishes beyond the component cutoff
[OAI265, §10.1, `09-amplification.tex`, lines 135–139]. -/
theorem norm_sub_siteExpectation_graphBall_eq_zero_of_component_support (Λ : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    {n : ℕ} (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n) :
    ‖k - condExpect (graphNbhd_subset Λ {a} n) k‖ = 0 := by
  rw [siteExpectation_graphBall_eq_of_component_support Λ a hk hn, sub_self, norm_zero]

/-- Component support makes the localized and full root channels equal at all sufficiently
large finite radii [OAI265, §10.1, `09-amplification.tex`, lines 124–139]. -/
theorem localRootChannel_graphBall_eq_of_component_support (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    {n : ℕ} (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n)
    (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    localRootChannel (graphNbhd_subset Λ {a} n) k B = spectatorRootChannel k B := by
  rw [localRootChannel, siteExpectation_graphBall_eq_of_component_support Λ a hk hn]

/-- One finite radius gives exact expectation and channel stabilization, uniformly over all
spectator observables [OAI265, §10.1, `09-amplification.tex`, lines 135–139]. -/
theorem exists_localRootChannel_graphBall_eq_of_component_support (Λ : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : IsSupportedOn (domainComponent_subset Λ a) k) :
    ∃ N, ∀ n ≥ N, condExpect (graphNbhd_subset Λ {a} n) k = k ∧
      ∀ B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ,
        localRootChannel (graphNbhd_subset Λ {a} n) k B = spectatorRootChannel k B :=
  ⟨Λ.sup fun x => (domainEDist Λ a x).toNat, fun _ hn =>
    ⟨siteExpectation_graphBall_eq_of_component_support Λ a hk hn,
      localRootChannel_graphBall_eq_of_component_support Λ a hk hn⟩⟩

/-- Every successor shell beyond the component cutoff vanishes
[OAI265, §10.1, `09-amplification.tex`, lines 124–139]. -/
theorem localRootChannelShell_graphBall_succ_eq_zero_of_component_support
    (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    {n : ℕ} (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n)
    (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    localRootChannelShell (graphNbhd Λ {a}) (graphNbhd_subset Λ {a}) k (n + 1) B = 0 := by
  rw [localRootChannelShell,
    localRootChannel_graphBall_eq_of_component_support Λ a hk (hn.trans (Nat.le_succ n)),
    localRootChannel_graphBall_eq_of_component_support Λ a hk hn, sub_self]

/-- The full root channel satisfies the finite-shell increment once the cutoff contains the
component of the anchor; only the localization errors up to that cutoff are used
[OAI265, §10.1, eq. (10.9), `09-amplification.tex`, lines 124–139]. -/
theorem siteOscillation_spectatorRootChannel_le_of_component_support (Λ : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    (ε : ℕ → ℝ) (n : ℕ) (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n)
    (hε : ∀ l ≤ n, ‖k - condExpect (graphNbhd_subset Λ {a} l) k‖ ≤ ε l)
    (y : ℤ × ℤ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    siteOscillation y (spectatorRootChannel k B) ≤ siteOscillation y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => domainEDist Λ a y ≤ l),
        localRootChannelShellBound ε l * ∑ z ∈ graphNbhd Λ {a} l, siteOscillation z B := by
  have h := siteOscillation_localRootChannel_le (graphNbhd Λ {a}) (graphNbhd_subset Λ {a})
    (graphNbhd_mono Λ {a}) hk₀ hk₁ ε n hε y B
  simpa only [localRootChannel_graphBall_eq_of_component_support Λ a hk hn,
    mem_graphNbhd_singleton_iff_domainEDist_le] using h

/-- A component-supported full channel cannot increase the oscillation at a site in a
different component [OAI265, §10.1, `09-amplification.tex`, lines 133–139]. -/
theorem siteOscillation_spectatorRootChannel_le_of_edist_eq_top (Λ : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    (y : ℤ × ℤ) (hy : domainEDist Λ a y = ⊤)
    (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    siteOscillation y (spectatorRootChannel k B) ≤ siteOscillation y B := by
  rw [← localRootChannel_graphBall_eq_of_component_support Λ a hk le_rfl B]
  exact siteOscillation_localRootChannel_le_of_notMem _ hk₀ hk₁ y
    (notMem_graphNbhd_singleton_of_domainEDist_eq_top hy _) B

end OpenAI
