/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphChannelPoissonGrowth.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the word identity is stated
for operators on any finite index type `n`; the growth statements are made on the induced
square lattice on `Λ`, with sites `ℤ × ℤ` and an arbitrary local family `loc`, as in
`OpenAI.Amplification.GraphChannelWeightedRow` (`graphBall G (a i) l` is
`OpenAI.graphNbhd Λ {a i} l`, the natural distance `G.dist y z` is
`(domainEDist Λ y z).toNat`, `¬ G.Reachable y z` is `domainEDist Λ y z = ⊤`, the cutoffs are
`Λ.sup fun x => (domainEDist Λ (a i) x).toNat`, component support is
`OpenAI.IsSupportedOn (domainComponent_subset Λ (a i))`, sums over all sites are sums over
`Λ`); `siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ Λ)`, `[NeZero q]` is
`[∀ i, Nonempty (loc i)]`.  The profile `Metric.exponentialDistanceProfile (S : Set ι)` of
`graphPseudoEMetricSpace G` is `OpenAI.domainDistanceProfile Λ S`, and
`Metric.infEDist y (S : Set ι) = ⊤` is `(⨅ s ∈ S, domainEDist Λ y s) = ⊤`, for which this file
imports `OpenAI.Amplification.GraphOmittedAnchorTail`.  The initial support `S` of `B` is a
subset of `Λ`, given by `hS : S ⊆ Λ`, and the block hypothesis
`Matrix.of (fun σ τ => B (σ, a) (τ, b)) ∈ supportedOperators q (S : Set ι)` is
`OpenAI.IsSupportedOn hS (Matrix.of fun σ τ => B (σ, a) (τ, b))`.
-/
import OpenAI.PoissonWordSpatialGrowth
import OpenAI.Amplification.ChannelWordObservables
import OpenAI.Amplification.GraphOmittedAnchorTail

/-!
# Spatial growth of words of root channels

The Poisson-word observable is the site oscillation of the chronological composition of
spectator root channels.  A supported initial operator supplies the initial indicator bound,
and the channel increment supplies the Poisson recurrence, so the expected oscillation is
integrable and decays like the stretched-exponential profile of the domain distance to the
initial support; it vanishes identically at infinite distance from it [OAI265, §10.1,
eq. (10.11) and the growth bound after it].  The lattice corollary derives the increment from
component-supported positive contractions with localization tails up to a finite cutoff, and
keeps the weighted row hypothesis on the event kernel.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 139–188.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

/-- Appending a letter to a Poisson word applies its channel after the whole prefix
[OAI265, §10.1, `09-amplification.tex`, lines 161–173]. -/
@[simp] theorem spectatorRootChannelWord_ofFn_append_singleton {n κ Aux : Type*} [Fintype n]
    [DecidableEq n] [Fintype Aux] [DecidableEq Aux] (k : κ → Matrix n n ℂ)
    (u : PoissonWord.Word κ) (i : κ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannelWord k
        (List.ofFn (PoissonWord.append u (PoissonWord.singleton i)).2) B =
      spectatorRootChannel (k i) (spectatorRootChannelWord k (List.ofFn u.2) B) := by
  simp only [PoissonWord.append, List.ofFn_fin_append, PoissonWord.ofFn_singleton,
    spectatorRootChannelWord_append_singleton]

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {κ : Type*} [Fintype κ] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- A weighted kernel controlling the one-step oscillations gives integrability, the expected
spatial decay and exact vanishing at infinite distance from the initial support.  The initial
coefficient comes from the supported blocks of `B`, with no Hermiticity and no nonempty
spectator [OAI265, §10.1, `09-amplification.tex`, lines 161–188]. -/
theorem integrable_and_integral_siteOscillation_le_of_graph_kernel (Λ : Finset (ℤ × ℤ))
    (k : κ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ) (A : ℤ × ℤ → ℤ × ℤ → ℝ) {β α v : ℝ}
    (hβ : 0 ≤ β) (hα : 0 < α) (hα₁ : α ≤ 1) (hv : 0 ≤ v)
    (hA : ∀ y z, 0 ≤ A y z)
    (hstep : ∀ (y : ℤ × ℤ) (W : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ),
      (∑ i, (siteOscillation y (spectatorRootChannel (k i) W) - siteOscillation y W)) ≤
        ∑ z ∈ Λ, A y z * siteOscillation z W)
    (hcomponent : ∀ y z, domainEDist Λ y z = ⊤ → A y z = 0)
    (hrow : ∀ y, (∑ z ∈ Λ, A y z * Real.exp (β * ((domainEDist Λ y z).toNat : ℝ) ^ α)) ≤ v)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ Λ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ)
    (hB : ∀ a b : Aux, IsSupportedOn hS (Matrix.of fun σ τ => B (σ, a) (τ, b)))
    (t : ℝ≥0) (y : ℤ × ℤ) :
    Integrable (fun u : PoissonWord.Word κ =>
        siteOscillation y (spectatorRootChannelWord k (List.ofFn u.2) B))
      (PoissonWord.measure κ t) ∧
      (∫ u, siteOscillation y (spectatorRootChannelWord k (List.ofFn u.2) B)
        ∂PoissonWord.measure κ t) ≤
        Real.exp (v * t) * (2 * ‖B‖) * domainDistanceProfile Λ S β α y ∧
      (∀ u : PoissonWord.Word κ, (⨅ s ∈ S, domainEDist Λ y s) = ⊤ →
        siteOscillation y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0) := by
  by_cases hy : y ∉ Λ
  · simp only [siteOscillation_of_notMem hy, integral_zero,
      domainDistanceProfile_of_notMem S β α hy, mul_zero, le_refl, implies_true, and_true]
    exact integrable_zero _ _ _
  rw [not_not] at hy
  let G := (SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ).induce (Λ : Set (ℤ × ℤ))
  let := graphPseudoEMetricSpace G
  let f (u : PoissonWord.Word κ) (z : (Λ : Set (ℤ × ℤ))) :=
    siteOscillation z.1 (spectatorRootChannelWord k (List.ofFn u.2) B)
  let A' (y z : (Λ : Set (ℤ × ℤ))) := A y.1 z.1
  let S' : Set (Λ : Set (ℤ × ℤ)) := Subtype.val ⁻¹' (S : Set (ℤ × ℤ))
  have hsum (g : ℤ × ℤ → ℝ) : ∑ z ∈ Λ, g z = ∑ z : (Λ : Set (ℤ × ℤ)), g z.1 :=
    Finset.sum_subtype Λ (fun _ => Finset.mem_coe.symm) g
  have hf (u : PoissonWord.Word κ) (z : (Λ : Set (ℤ × ℤ))) : 0 ≤ f u z :=
    siteOscillation_nonneg _ _
  have hnorm : 0 ≤ 2 * ‖B‖ := by positivity
  have hinitial (z : (Λ : Set (ℤ × ℤ))) :
      f PoissonWord.nil z ≤ 2 * ‖B‖ * S'.indicator (fun _ => (1 : ℝ)) z := by
    have h := siteOscillation_le_support_indicator hS B hB z.1
    have hind : S'.indicator (fun _ => (1 : ℝ)) z =
        (S : Set (ℤ × ℤ)).indicator (fun _ => (1 : ℝ)) z.1 := by
      by_cases hz : z.1 ∈ S
      · rw [Set.indicator_of_mem (show z ∈ S' from hz),
          Set.indicator_of_mem (Finset.mem_coe.2 hz)]
      · rw [Set.indicator_of_notMem (show z ∉ S' from hz),
          Set.indicator_of_notMem (by simpa using hz)]
    rw [hind]
    simpa only [f, PoissonWord.nil, List.ofFn_zero, spectatorRootChannelWord_nil] using h
  have hword (u : PoissonWord.Word κ) (z : (Λ : Set (ℤ × ℤ))) :
      (∑ i, (f (PoissonWord.append u (PoissonWord.singleton i)) z - f u z)) ≤
        ∑ x, A' z x * f u x := by
    have h := hstep z.1 (spectatorRootChannelWord k (List.ofFn u.2) B)
    rw [hsum] at h
    simpa only [f, A', spectatorRootChannelWord_ofFn_append_singleton] using h
  have hdist (z x : (Λ : Set (ℤ × ℤ))) : (G.edist z x : ℕ∞) = domainEDist Λ z.1 x.1 :=
    (domainEDist_of_mem z.2 x.2).symm
  -- The edistance of the graph pseudo-emetric is stated through `G.edist`: on the subtype the
  -- elaborator would otherwise pick the edistance inherited from `ℤ × ℤ`.
  have hsupport (z x : (Λ : Set (ℤ × ℤ))) (hzx : ((G.edist z x : ℕ∞) : ℝ≥0∞) = ⊤) :
      A' z x = 0 := by
    rw [ENat.toENNReal_eq_top, hdist] at hzx
    exact hcomponent z.1 x.1 hzx
  have hmetric (z : (Λ : Set (ℤ × ℤ))) :
      (∑ x, A' z x * Real.exp (β * ((G.edist z x : ℕ∞) : ℝ≥0∞).toReal ^ α)) ≤ v := by
    have htoReal (x : (Λ : Set (ℤ × ℤ))) :
        ((G.edist z x : ℕ∞) : ℝ≥0∞).toReal = ((domainEDist Λ z.1 x.1).toNat : ℝ) := by
      rw [← hdist]
      induction G.edist z x using ENat.recTopCoe <;> simp
    have h := hrow z.1
    rw [hsum] at h
    simpa only [A', htoReal] using h
  have hprofile := domainDistanceProfile_eq_exponentialDistanceProfile Λ S β α hy
  have h := PoissonWord.integrable_and_integral_le_of_spatial_growth t f A' S'
    hβ hα hα₁ hf (fun _ _ => hA _ _) hv hnorm hinitial hword hsupport hmetric ⟨y, hy⟩
  refine ⟨h.1, h.2.trans_eq (by rw [hprofile]), fun u htop => ?_⟩
  have hzero : Metric.infEDist (⟨y, hy⟩ : (Λ : Set (ℤ × ℤ))) S' = ⊤ := by
    have h0 := (domainDistanceProfile_eq_zero_iff Λ S β α y).2 htop
    rw [hprofile] at h0
    exact (Metric.exponentialDistanceProfile_eq_zero_iff _ _ _ _).1 h0
  exact PoissonWord.eq_zero_of_spatial_growth_of_infEDist_eq_top f A' S'
    hβ hα hα₁ hf (fun _ _ => hA _ _) hv hnorm hinitial hword hsupport hmetric ⟨y, hy⟩ hzero u

/-- **Expected oscillation of a channel word** for component-supported positive contractions
with localization tails: the cutoff covers every anchor, and the row bound is assumed for the
event kernel with the derived tail coefficient
[OAI265, §10.1, `09-amplification.tex`, lines 139–188]. -/
theorem integrable_and_integral_siteOscillation_le_graphChannelEventKernel
    (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ) (k : κ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, IsSupportedOn (domainComponent_subset Λ (a i)) (k i))
    {C c α v : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hv : 0 ≤ v) (N : ℕ) (hN : ∀ i, Λ.sup (fun x => (domainEDist Λ (a i) x).toNat) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (hrow : ∀ y, (∑ z ∈ Λ,
      graphChannelEventKernel Λ a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * ((domainEDist Λ y z).toNat : ℝ) ^ α)) ≤ v)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ Λ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ)
    (hB : ∀ a b : Aux, IsSupportedOn hS (Matrix.of fun σ τ => B (σ, a) (τ, b)))
    (t : ℝ≥0) (y : ℤ × ℤ) :
    Integrable (fun u : PoissonWord.Word κ =>
        siteOscillation y (spectatorRootChannelWord k (List.ofFn u.2) B))
      (PoissonWord.measure κ t) ∧
      (∫ u, siteOscillation y (spectatorRootChannelWord k (List.ofFn u.2) B)
        ∂PoissonWord.measure κ t) ≤
        Real.exp (v * t) * (2 * ‖B‖) *
          domainDistanceProfile Λ S (c / (4 * (2 : ℝ) ^ α)) α y ∧
      (∀ u : PoissonWord.Word κ, (⨅ s ∈ S, domainEDist Λ y s) = ⊤ →
        siteOscillation y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0) :=
  integrable_and_integral_siteOscillation_le_of_graph_kernel Λ k
    (graphChannelEventKernel Λ a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))) (c / 2) α N)
    (by positivity) hα hα₁ hv
    (graphChannelEventKernel_nonneg Λ a (by positivity) (c / 2) α N)
    (sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
      Λ a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε)
    (graphChannelEventKernel_eq_zero_of_not_reachable Λ a _ _ _ _) hrow S hS B hB t y

end OpenAI
