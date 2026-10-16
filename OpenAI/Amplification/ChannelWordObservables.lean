/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ChannelWordObservables.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: `spectatorRootChannelWord`
and its algebraic lemmas are stated for operators on any finite index type `n`, as
`OpenAI.spectatorRootChannel` is; the oscillation bounds are stated for a region
`T : Finset σ` with local family `loc` (`siteOscillation q y` is `OpenAI.siteOscillation y`),
and the kernel bound on the induced square lattice on `Λ`, as in
`OpenAI.Amplification.GraphChannelWeightedRow` (`graphBall G (a i) l` is
`OpenAI.graphNbhd Λ {a i} l`, the cutoffs are `Λ.sup fun x => (domainEDist Λ (a i) x).toNat`,
component support is `OpenAI.IsSupportedOn (domainComponent_subset Λ (a i))`, sums over all
sites are sums over `Λ`); `siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ Λ)` and
`[NeZero q]` is `[∀ i, Nonempty (loc i)]`.
-/
import OpenAI.SpectatorOscillationSupport
import OpenAI.Amplification.GraphChannelWeightedRow

/-!
# Observables evolved along finite words of root channels

A list of event labels is read chronologically: appending a label applies its spectator root
channel to the current observable [OAI265, §10.1, the evolution before eq. (10.11)].  Positive
contractions give uniform operator-norm and oscillation bounds, and the summed append
increments are controlled by the event kernel `graphChannelEventKernel`, evaluated at the
evolved observable.  At the empty word, `siteOscillation_le_support_indicator` supplies the
initial support bound.

## Main definitions

* `OpenAI.spectatorRootChannelWord`: the chronological composition of root channels.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 139–173.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

section Word

variable {n κ Aux : Type*} [Fintype n] [DecidableEq n] [Fintype Aux] [DecidableEq Aux]

/-- The observable after the events of `w` in chronological order, each event `i` acting by
the root channel of `k i` with the identity on the spectator
[OAI265, §10.1, `09-amplification.tex`, lines 161–173]. -/
noncomputable def spectatorRootChannelWord (k : κ → Matrix n n ℂ) (w : List κ)
    (B : Matrix (n × Aux) (n × Aux) ℂ) : Matrix (n × Aux) (n × Aux) ℂ :=
  w.foldl (fun B i => spectatorRootChannel (k i) B) B

/-- Relabelling a word evaluates the same channels in the same order; in particular,
forgetting membership in a retained family preserves the observable. -/
theorem spectatorRootChannelWord_map {η : Type*} (f : η → κ) (k : κ → Matrix n n ℂ)
    (w : List η) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannelWord k (w.map f) B = spectatorRootChannelWord (k ∘ f) w B :=
  List.foldl_map

@[simp] theorem spectatorRootChannelWord_nil (k : κ → Matrix n n ℂ)
    (B : Matrix (n × Aux) (n × Aux) ℂ) : spectatorRootChannelWord k [] B = B := rfl

/-- Appending an event applies its channel after all earlier events. -/
@[simp] theorem spectatorRootChannelWord_append_singleton (k : κ → Matrix n n ℂ) (w : List κ)
    (i : κ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannelWord k (w ++ [i]) B =
      spectatorRootChannel (k i) (spectatorRootChannelWord k w B) := by
  simp only [spectatorRootChannelWord, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Every finite word of root channels of positive contractions is a contraction in operator
norm, uniformly in the word and the spectator
[OAI265, §10.1, `09-amplification.tex`, lines 161–173]. -/
theorem norm_spectatorRootChannelWord_le (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ)
    (B : Matrix (n × Aux) (n × Aux) ℂ) :
    ‖spectatorRootChannelWord k w B‖ ≤ ‖B‖ := by
  induction w generalizing B with
  | nil => exact le_rfl
  | cons i w ih =>
    exact (ih (spectatorRootChannel (k i) B)).trans
      (norm_spectatorRootChannel_le (hk₀ i) (hk₁ i) B)

end Word

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T : Finset σ} {κ Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The oscillations along a word are nonnegative and bounded by twice the initial operator
norm, without Hermiticity [OAI265, §10.1, `09-amplification.tex`, lines 127 and 161–173]. -/
theorem siteOscillation_spectatorRootChannelWord_bounds
    (k : κ → Matrix (Reg loc T) (Reg loc T) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ) (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    0 ≤ siteOscillation y (spectatorRootChannelWord k w B) ∧
      siteOscillation y (spectatorRootChannelWord k w B) ≤ 2 * ‖B‖ :=
  ⟨siteOscillation_nonneg y _, (siteOscillation_le_two_mul_norm y _).trans <|
    mul_le_mul_of_nonneg_left (norm_spectatorRootChannelWord_le k hk₀ hk₁ w B) (by norm_num)⟩

end Region

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {κ : Type*} [Fintype κ] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The summed append increments of the evolved observable are dominated by the event kernel
at that observable [OAI265, §10.1, eq. (10.10), `09-amplification.tex`, lines 139–173]. -/
theorem sum_siteOscillation_spectatorRootChannelWord_append_sub_le_graphChannelEventKernel
    (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ) (k : κ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, IsSupportedOn (domainComponent_subset Λ (a i)) (k i))
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (N : ℕ) (hN : ∀ i, Λ.sup (fun x => (domainEDist Λ (a i) x).toNat) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (w : List κ) (y : ℤ × ℤ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    (∑ i, (siteOscillation y (spectatorRootChannelWord k (w ++ [i]) B) -
      siteOscillation y (spectatorRootChannelWord k w B))) ≤
      ∑ z ∈ Λ, graphChannelEventKernel Λ a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z * siteOscillation z (spectatorRootChannelWord k w B) := by
  simpa only [spectatorRootChannelWord_append_singleton] using
    sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
      Λ a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε y (spectatorRootChannelWord k w B)

end OpenAI
