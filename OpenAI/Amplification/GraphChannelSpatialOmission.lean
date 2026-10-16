/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphChannelSpatialOmission.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the graph is the induced
square lattice on `Λ`, with sites `ℤ × ℤ`, as in `OpenAI.Amplification.GraphChannelWeightedRow`
(`graphBall G (a i) l` is `OpenAI.graphNbhd Λ {a i} l`, `G.edist` is `OpenAI.domainEDist Λ`,
the cutoffs are `Λ.sup fun x => (domainEDist Λ (a i) x).toNat`,
`k ∈ supportedOperators q {x | G.Reachable a x}` is
`OpenAI.IsSupportedOn (domainComponent_subset Λ a) k`, anchors are maps `a : κ → ℤ × ℤ`);
`siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ Λ)`.  In
`exists_integrable_and_integral_channelWordOmissionDefect_le` the quantification over the site
type, the graph and `q` with `[NeZero q]` becomes one over the domain `Λ` and an arbitrary local
family `loc` with `[∀ i, Nonempty (loc i)]`, and the support `S` of `B` comes with
`hS : S ⊆ Λ`, the block hypothesis being `OpenAI.IsSupportedOn hS` of the blocks.
-/
import OpenAI.Amplification.ChannelWordOmission
import OpenAI.Amplification.GraphChannelEventError
import OpenAI.Amplification.GraphChannelPoissonGrowth
import OpenAI.Amplification.GraphOmittedAnchorTail

/-!
# Spatial omission bounds for words of root channels

The full and the retained words are coupled by filtering the same Poisson word.  Their expected
operator-norm difference has a stretched-exponential spatial bound, uniform in the domain, the
labels, the local family, the spectator, the support and the cutoff
[OAI265, §10.1, eq. (10.12)].  The proof derives the oscillation growth from the effects and
their localization tails, and combines it with the omitted-prefix occupation identity and the
omitted-anchor tail.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 139–215.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

/-- Localization tails at every radius force exact support on the component of the anchor:
beyond the largest distance in the component the balls stop growing, while the tail tends to
zero [OAI265, §10.1, `09-amplification.tex`, lines 135–137]. -/
theorem mem_supportedOperators_reachable_of_forall_tail {loc : ℤ × ℤ → Type*}
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} {C c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hε : ∀ l : ℕ, ‖k - condExpect (graphNbhd_subset Λ {a} l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α))) :
    IsSupportedOn (domainComponent_subset Λ a) k := by
  set n := Λ.sup fun x => (domainEDist Λ a x).toNat
  have hcongr : ∀ {S S' : Finset (ℤ × ℤ)} (_ : S = S') (h : S ⊆ Λ) (h' : S' ⊆ Λ),
      condExpect h k = condExpect h' k := by
    intro S S' e h h'
    subst e
    rfl
  have hball (l : ℕ) (hl : n ≤ l) : condExpect (graphNbhd_subset Λ {a} l) k =
      condExpect (domainComponent_subset Λ a) k :=
    hcongr (graphNbhd_singleton_eq_domainComponent_of_sup_le Λ a hl) _ _
  have htend : Filter.Tendsto (fun l : ℕ => C * Real.exp (-(c * (l : ℝ) ^ α)))
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
    simpa using (Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h)).const_mul C
  have hzero : ‖k - condExpect (domainComponent_subset Λ a) k‖ ≤ 0 :=
    ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨n, fun l hl => by
      rw [← hball l hl]
      exact hε l⟩)
  have hk : condExpect (domainComponent_subset Λ a) k = k :=
    (sub_eq_zero.mp (norm_le_zero_iff.mp hzero)).symm
  exact hk ▸ isSupportedOn_condExpect _ k

/-- **Spatial omission bound.**  The expected operator-norm error of keeping only the retained
events is bounded by `D T |S| ‖B‖ e^{v T - γ r^α}` when every omitted anchor is farther than `r`
from the support `S` of `B`.  The constants are chosen before the label and spectator types, the
local family, the domain, the effects, the retained predicate, the cutoff, the observable and
the time; the observable may be non-Hermitian and the spectator empty
[OAI265, §10.1, eq. (10.12), `09-amplification.tex`, lines 139–215]. -/
theorem exists_integrable_and_integral_channelWordOmissionDefect_le {C K μ c α : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ D v γ : ℝ, 0 ≤ D ∧ 0 < v ∧ 0 < γ ∧
      γ = min (c / 2) (c / (4 * (2 : ℝ) ^ α)) / 2 ∧
      ∀ (κ Aux : Type*) [Fintype κ] [Fintype Aux] [DecidableEq Aux]
        (loc : ℤ × ℤ → Type*) [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
        [∀ i, Nonempty (loc i)] (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
        (k : κ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ i, IsSupportedOn (domainComponent_subset Λ (a i)) (k i)) →
        (∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        ∀ (N : ℕ), (∀ i, Λ.sup (fun x => (domainEDist Λ (a i) x).toNat) ≤ N) →
        (∀ i l, l ≤ N → ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (P : κ → Prop) [DecidablePred P] (S : Finset (ℤ × ℤ)) (hS : S ⊆ Λ)
          (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ),
          (∀ x y : Aux, IsSupportedOn hS (Matrix.of fun σ τ => B (σ, x) (τ, y))) →
          ∀ (r : ℝ), 0 ≤ r →
            (∀ i, ¬ P i → ∀ s ∈ S, ENNReal.ofReal r < (domainEDist Λ (a i) s : ℝ≥0∞)) →
            ∀ T : ℝ≥0,
              Integrable (fun w : PoissonWord.Word κ =>
                channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ T) ∧
              (∫ w : PoissonWord.Word κ,
                channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ T) ≤
                D * T * S.card * ‖B‖ * Real.exp (v * T - γ * r ^ α) := by
  obtain ⟨v, hv, hkernel⟩ := exists_graphChannelEventKernel_bounds_of_component_support
    hC hK hμ hc hα hα₁
  have hβ : 0 < c / (4 * (2 : ℝ) ^ α) := by positivity
  obtain ⟨L, γ, hL, hγ, hγeq, htail⟩ :=
    exists_sum_omitted_graphBall_exponentialDistanceProfile_le
      hK hμ (half_pos hc) hβ hα hα₁
  let A₀ := 2 + 8 * Real.sqrt C * Real.exp (c / 2)
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  refine ⟨2 * A₀ * L, v + 1, γ, by positivity, by linarith, hγ, hγeq, ?_⟩
  intro κ Aux _ _ _ loc _ _ _ Λ a k hk₀ hk₁ hk hball hfiber N hN hε P _ S hS B hB r hr hfar T
  let a' (i : {i // P i}) := a i
  let k' (i : {i // P i}) := k i
  have hfiber' (x : ℤ × ℤ) :
      ((Finset.univ.filter fun i : {i // P i} => a' i = x).card : ℝ) ≤ μ :=
    (Nat.cast_le.mpr (card_anchor_fiber_subtype_le a P x)).trans (hfiber x)
  obtain ⟨hrow, _⟩ := hkernel {i // P i} Aux loc Λ a' k'
    (fun i => hk₀ i) (fun i => hk₁ i) (fun i => hk i)
    hball hfiber' N (fun i => hN i) (fun i => hε i)
  let W (u : PoissonWord.Word {i // P i}) := spectatorRootChannelWord k' (List.ofFn u.2) B
  let d (u : PoissonWord.Word {i // P i}) (z : ℤ × ℤ) := siteOscillation z (W u)
  let F (u : PoissonWord.Word {i // P i}) (i : κ) :=
    ‖spectatorRootChannel (k i) (W u) - W u‖
  let p (z : ℤ × ℤ) := domainDistanceProfile Λ S (c / (4 * (2 : ℝ) ^ α)) α z
  let E := Finset.univ.filter fun i => ¬ P i
  have hgrowth (t : ℝ≥0) (z : ℤ × ℤ) :=
    integrable_and_integral_siteOscillation_le_graphChannelEventKernel
      Λ a' k' (fun i => hk₀ i) (fun i => hk₁ i) (fun i => hk i)
      hC hc hα hα₁ hv N (fun i => hN i) (fun i => hε i) hrow S hS B hB t z
  have hdint (t : ℝ≥0) (z : ℤ × ℤ) : Integrable (fun u => d u z)
      (PoissonWord.measure {i // P i} t) := (hgrowth t z).1
  have hdbound (t : ℝ≥0) (z : ℤ × ℤ) :
      (∫ u, d u z ∂PoissonWord.measure {i // P i} t) ≤
        Real.exp (v * t) * (2 * ‖B‖) * p z := (hgrowth t z).2.1
  have hevent (t : ℝ≥0) (i : κ) :
      (∫ u, F u i ∂PoissonWord.measure {i // P i} t) ≤
        A₀ * (Real.exp (v * t) * (2 * ‖B‖)) *
          ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ graphNbhd Λ {a i} l, p z := by
    let w (l : ℕ) := A₀ * Real.exp (-(c / 2 * (l : ℝ) ^ α))
    have hint (l : ℕ) : Integrable (fun u => w l *
        ∑ z ∈ graphNbhd Λ {a i} l, d u z) (PoissonWord.measure {i // P i} t) :=
      (integrable_finsetSum _ fun z _ => hdint t z).const_mul (w l)
    calc
      _ ≤ ∫ u, ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ graphNbhd Λ {a i} l, d u z ∂PoissonWord.measure {i // P i} t := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
          (integrable_finsetSum _ fun l _ => hint l)
        apply Filter.Eventually.of_forall
        intro u
        exact norm_spectatorRootChannel_sub_self_le_exp_of_component_support
          Λ (a i) (hk₀ i) (hk₁ i) (hk i) hC hc hα hα₁ N (hN i) (hε i) (W u)
      _ = ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ graphNbhd Λ {a i} l,
            ∫ u, d u z ∂PoissonWord.measure {i // P i} t := by
        rw [integral_finsetSum _ fun l _ => hint l]
        apply Finset.sum_congr rfl
        intro l _
        rw [integral_const_mul, integral_finsetSum _ fun z _ => hdint t z]
      _ ≤ ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ graphNbhd Λ {a i} l, Real.exp (v * t) * (2 * ‖B‖) * p z := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun z _ => hdbound t z) (by dsimp [w]; positivity)
      _ = _ := by
        simp only [w, Finset.mul_sum, neg_mul]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro z _
        ring
  have hspatial : (∑ i ∈ E, ∑ l ∈ Finset.range (N + 1),
      Real.exp (-(c / 2) * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd Λ {a i} l, p z) ≤
      L * S.card * Real.exp (-γ * r ^ α) :=
    htail κ Λ a hball hfiber E S N r hr
      (fun i hi => hfar i (Finset.mem_filter.mp hi).2)
  have hsum (s : ℝ) (hs : s ∈ Set.Ioc 0 (T : ℝ)) :
      (∑ i ∈ E, ∫ u, F u i ∂PoissonWord.measure {i // P i} (Real.toNNReal s)) ≤
        (2 * A₀ * L) * S.card * ‖B‖ * Real.exp ((v + 1) * T - γ * r ^ α) := by
    have hexp : Real.exp (v * (Real.toNNReal s : ℝ)) ≤ Real.exp ((v + 1) * T) := by
      rw [Real.toNNReal_of_nonneg hs.1.le]
      have hT : (0 : ℝ) ≤ T := T.coe_nonneg
      refine Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hs.2 hv).trans ?_)
      rw [add_mul, one_mul]
      linarith
    calc
      _ ≤ ∑ i ∈ E, A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ graphNbhd Λ {a i} l, p z := Finset.sum_le_sum fun i _ => hevent _ i
      _ = A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          ∑ i ∈ E, ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ graphNbhd Λ {a i} l, p z := (Finset.mul_sum _ _ _).symm
      _ ≤ A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          (L * S.card * Real.exp (-γ * r ^ α)) :=
        mul_le_mul_of_nonneg_left hspatial (by positivity)
      _ ≤ A₀ * (Real.exp ((v + 1) * T) * (2 * ‖B‖)) *
          (L * S.card * Real.exp (-γ * r ^ α)) := by gcongr
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring
  obtain ⟨hi, htime⟩ := integrable_and_integral_channelWordOmissionDefect_le k hk₀ hk₁ P B T
  refine ⟨hi, htime.trans ?_⟩
  change (∫ s : ℝ in Set.Ioc 0 (T : ℝ),
    ∑ i ∈ E, ∫ u, F u i ∂PoissonWord.measure {i // P i} (Real.toNNReal s)) ≤ _
  calc
    _ ≤ ∫ _s : ℝ in Set.Ioc 0 (T : ℝ),
        (2 * A₀ * L) * S.card * ‖B‖ * Real.exp ((v + 1) * T - γ * r ^ α) :=
      setIntegral_mono_of_nonneg
        (fun s _ => Finset.sum_nonneg fun i _ => integral_nonneg fun u => norm_nonneg _)
        hsum (integrable_const _)
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero, smul_eq_mul]
      ring

end OpenAI
