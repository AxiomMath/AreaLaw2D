/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ChannelWordThinning.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the channel-word
statements are made for operators on any finite index type `n` instead of `ι → Fin q`, as for
`OpenAI.spectatorRootChannelWord`; the oscillation statement is made for a region
`T : Finset σ` with local family `loc`, with `siteOscillation q y` being
`OpenAI.siteOscillation y`.
-/
import OpenAI.PoissonWordPartition
import OpenAI.Amplification.ChannelWordObservables

/-!
# Retained channels in a full Poisson word

Filtering a full word keeps the order and multiplicity of the retained events, and its
composition of root channels is the composition indexed by the retained subtype word.  The
fixed-time marginal law therefore transfers integrability and expectations of any function of
this observable between the full and the retained alphabets [OAI265, §10.1, the coupling of
the full and retained words before eq. (10.12)].

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 161–188.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory
open scoped NNReal Matrix Matrix.Norms.L2Operator

namespace OpenAI

open Arealaw Matrix

section Word

variable {n κ Aux : Type*} [Fintype n] [DecidableEq n] [Fintype Aux] [DecidableEq Aux]

/-- Keeping the retained letters in their original order evaluates the same channels as the
retained subtype word, with all repetitions [OAI265, §10.1, `09-amplification.tex`,
lines 161–173]. -/
theorem spectatorRootChannelWord_filter (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix n n ℂ) (w : PoissonWord.Word κ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B =
      spectatorRootChannelWord (fun i : {i // P i} => k i)
        (List.ofFn (PoissonWord.partitionWords P w).1.2) B := by
  rw [← PoissonWord.ofFn_partitionWords_fst P w, spectatorRootChannelWord_map]
  rfl

variable [Fintype κ]

/-- Integrability of an observation of the filtered evolution under the full word law is
integrability under the retained word law [OAI265, §10.1, `09-amplification.tex`,
lines 161–188]. -/
theorem integrable_spectatorRootChannelWord_filter_iff {E : Type*} [NormedAddCommGroup E]
    (P : κ → Prop) [DecidablePred P] (k : κ → Matrix n n ℂ)
    (B : Matrix (n × Aux) (n × Aux) ℂ) (F : Matrix (n × Aux) (n × Aux) ℂ → E) (t : ℝ≥0) :
    Integrable (fun w : PoissonWord.Word κ =>
        F (spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B))
      (PoissonWord.measure κ t) ↔
      Integrable (fun u : PoissonWord.Word {i // P i} =>
        F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
        (PoissonWord.measure {i // P i} t) := by
  simp_rw [spectatorRootChannelWord_filter]
  rw [← PoissonWord.map_partitionWords_fst P t]
  exact (integrable_map_measure
    (f := fun w : PoissonWord.Word κ => (PoissonWord.partitionWords P w).1)
    (g := fun u : PoissonWord.Word {i // P i} =>
      F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
    (μ := PoissonWord.measure κ t) AEStronglyMeasurable.of_discrete
    Measurable.of_discrete.aemeasurable).symm

/-- The expectation of an observation of the filtered evolution is its expectation under the
retained word law, also for matrix-valued observations [OAI265, §10.1,
`09-amplification.tex`, lines 161–188]. -/
theorem integral_spectatorRootChannelWord_filter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : κ → Prop) [DecidablePred P] (k : κ → Matrix n n ℂ)
    (B : Matrix (n × Aux) (n × Aux) ℂ) (F : Matrix (n × Aux) (n × Aux) ℂ → E) (t : ℝ≥0) :
    (∫ w : PoissonWord.Word κ, F (spectatorRootChannelWord k
        ((List.ofFn w.2).filter (fun i => decide (P i))) B) ∂PoissonWord.measure κ t) =
      ∫ u : PoissonWord.Word {i // P i},
        F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B)
          ∂PoissonWord.measure {i // P i} t := by
  simp_rw [spectatorRootChannelWord_filter]
  rw [← PoissonWord.map_partitionWords_fst P t]
  exact (integral_map_of_stronglyMeasurable
    (φ := fun w : PoissonWord.Word κ => (PoissonWord.partitionWords P w).1)
    (f := fun u : PoissonWord.Word {i // P i} =>
      F (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
    (μ := PoissonWord.measure κ t)
    Measurable.of_discrete StronglyMeasurable.of_discrete).symm

end Word

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T : Finset σ} {κ Aux : Type*} [Fintype κ] [Fintype Aux]
  [DecidableEq Aux]

/-- An oscillation estimate under the retained law applies to the filtered full-word sample
with the same bound [OAI265, §10.1, `09-amplification.tex`, lines 174–188]. -/
theorem integrable_and_integral_siteOscillation_filter_le (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix (Reg loc T) (Reg loc T) ℂ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) (t : ℝ≥0) (y : σ) (R : ℝ)
    (h : Integrable (fun u : PoissonWord.Word {i // P i} =>
        siteOscillation y
          (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B))
        (PoissonWord.measure {i // P i} t) ∧
      (∫ u : PoissonWord.Word {i // P i}, siteOscillation y
        (spectatorRootChannelWord (fun i : {i // P i} => k i) (List.ofFn u.2) B)
          ∂PoissonWord.measure {i // P i} t) ≤ R) :
    Integrable (fun w : PoissonWord.Word κ => siteOscillation y
        (spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B))
      (PoissonWord.measure κ t) ∧
      (∫ w : PoissonWord.Word κ, siteOscillation y
        (spectatorRootChannelWord k ((List.ofFn w.2).filter (fun i => decide (P i))) B)
          ∂PoissonWord.measure κ t) ≤ R := by
  rw [integrable_spectatorRootChannelWord_filter_iff P k B (siteOscillation y),
    integral_spectatorRootChannelWord_filter P k B (siteOscillation y)]
  exact h

end OpenAI
