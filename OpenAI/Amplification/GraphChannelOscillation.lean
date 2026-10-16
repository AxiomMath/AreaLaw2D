/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphChannelOscillation.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations as in
`OpenAI.Amplification.ComponentChannelOscillation`: the graph is the induced square lattice on
`Λ`, with sites `ℤ × ℤ` and an arbitrary local family `loc`; `graphBall G a l` is
`OpenAI.graphNbhd Λ {a} l`, `G.edist` is `OpenAI.domainEDist Λ`, the cutoff is
`Λ.sup fun x => (domainEDist Λ a x).toNat`, component support is
`OpenAI.IsSupportedOn (domainComponent_subset Λ a)`, and `siteExpectation q K` is
`OpenAI.condExpect (h : K ⊆ Λ)`.
-/
import OpenAI.Amplification.ComponentChannelOscillation
import OpenAI.Amplification.ExponentialChannelShells

/-!
# Full graph channels with explicit stretched-exponential shell bounds

Exact support on the component of the anchor identifies the full root channel with a
sufficiently large finite-ball channel, so its oscillation increment inherits the explicit
coefficients obtained from the localization errors [OAI265, §10.1, eq. (10.9)].  No series or
limit is used.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 101–139.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The full component-supported root channel has an explicit finite stretched-exponential
shell bound, with an arbitrary finite spectator; the cutoff need only contain the component
of the anchor [OAI265, §10.1, eq. (10.9), `09-amplification.tex`, lines 124–139]. -/
theorem siteOscillation_spectatorRootChannel_le_exp_of_component_support (Λ : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n)
    (hε : ∀ l ≤ n, ‖k - condExpect (graphNbhd_subset Λ {a} l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ℤ × ℤ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    siteOscillation y (spectatorRootChannel k B) ≤ siteOscillation y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => domainEDist Λ a y ≤ l),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
          ∑ z ∈ graphNbhd Λ {a} l, siteOscillation z B := by
  have h := siteOscillation_localRootChannel_le_exp (graphNbhd Λ {a}) (graphNbhd_subset Λ {a})
    (graphNbhd_mono Λ {a}) hk₀ hk₁ hC hc hα hα₁ n hε y B
  simpa only [localRootChannel_graphBall_eq_of_component_support Λ a hk hn,
    mem_graphNbhd_singleton_iff_domainEDist_le] using h

end OpenAI
