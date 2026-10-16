/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphChannelEventError.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the finite-region estimate
is stated for a region `T : Finset σ` with local family `loc`, as in
`OpenAI.Amplification.ChannelShellOscillation` (the localized channels take the proofs
`hregions : ∀ l, regions l ⊆ T`, the monotonicity hypothesis is named `hmono`); the graph
estimate is stated on the induced square lattice on `Λ`, as in
`OpenAI.Amplification.ComponentChannelOscillation` (`graphBall G a l` is
`OpenAI.graphNbhd Λ {a} l`, the cutoff is `Λ.sup fun x => (domainEDist Λ a x).toNat`,
component support is `OpenAI.IsSupportedOn (domainComponent_subset Λ a)`);
`siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ T)` and `[NeZero q]` is
`[∀ i, Nonempty (loc i)]`.
-/
import OpenAI.Amplification.ComponentChannelOscillation
import OpenAI.Amplification.ExponentialChannelShells

/-!
# One-event errors from channel shells

Summing the localized channel shells bounds the operator-norm error of a root channel by the
site oscillations.  At a finite radius containing the component of the anchor the localized
channel is the full channel.  The coefficient is the shell coefficient itself, without the
factor two of the oscillation increment [OAI265, §10.1, eq. (10.8) and the one-event error of
eq. (10.12)].

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 101–121 and 188–191.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The finite shell sum bounds the error of the localized channel in operator norm
[OAI265, §10.1, `09-amplification.tex`, lines 101–121 and 188–191]. -/
theorem norm_localRootChannel_sub_self_le_exp_sum_siteOscillation (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - condExpect (hregions l) k‖ ≤ C * Real.exp (-(c * (l : ℝ) ^ α)))
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannel (hregions n) k B - B‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
          ∑ z ∈ regions l, siteOscillation z B := by
  revert hε
  induction n with
  | zero =>
    intro hε
    simpa only [localRootChannelShell, Nat.zero_add, Finset.sum_range_one] using
      norm_localRootChannelShell_le_exp_sum_siteOscillation
        regions hregions hmono hk₀ hk₁ hC hc hα hα₁ 0 hε B
  | succ n ih =>
    intro hε
    have hprev := ih fun l hl => hε l (hl.trans (Nat.le_succ n))
    have hnext := norm_localRootChannelShell_le_exp_sum_siteOscillation
      regions hregions hmono hk₀ hk₁ hC hc hα hα₁ (n + 1) hε B
    change ‖localRootChannel (hregions (n + 1)) k B -
      localRootChannel (hregions n) k B‖ ≤ _ at hnext
    rw [Finset.sum_range_succ]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (localRootChannel (hregions n) k B) _).trans
      ((add_le_add hnext hprev).trans_eq (add_comm _ _))

end Region

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Once the cutoff contains the component of the anchor, the finite shell bound controls the
full one-event error [OAI265, §10.1, `09-amplification.tex`, lines 135–137 and 188–191]. -/
theorem norm_spectatorRootChannel_sub_self_le_exp_of_component_support (Λ : Finset (ℤ × ℤ))
    (a : ℤ × ℤ) {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : IsSupportedOn (domainComponent_subset Λ a) k)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Λ.sup (fun x => (domainEDist Λ a x).toNat) ≤ n)
    (hε : ∀ l ≤ n, ‖k - condExpect (graphNbhd_subset Λ {a} l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    ‖spectatorRootChannel k B - B‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
          ∑ z ∈ graphNbhd Λ {a} l, siteOscillation z B := by
  simpa only [localRootChannel_graphBall_eq_of_component_support Λ a hk hn] using
    norm_localRootChannel_sub_self_le_exp_sum_siteOscillation (graphNbhd Λ {a})
      (graphNbhd_subset Λ {a}) (graphNbhd_mono Λ {a}) hk₀ hk₁ hC hc hα hα₁ n hε B

end OpenAI
