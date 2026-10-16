/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ChannelWordOmission.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptation: the statements are made for
operators on any finite index type `n` instead of `ι → Fin q`, as for
`OpenAI.spectatorRootChannelWord`.
-/
import OpenAI.PoissonWordJump
import OpenAI.PoissonWordRealOccupation
import OpenAI.Amplification.ChannelWordThinning

/-!
# Omitting events from words of root channels

Removing events from a chronological word costs at most the sum of the omitted one-event
errors at the retained prefixes, by subtraction and contraction of the spectator root channels
in operator norm.  The Poisson prefix identity and the retained-prefix occupation law then
bound the expected error by a time integral [OAI265, §10.1, eq. (10.12)].

## Main definitions

* `OpenAI.channelWordOmissionDefect`: the operator-norm error of keeping only the retained
  events.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 203–215.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory
open scoped NNReal Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

variable {n κ Aux : Type*} [Fintype n] [DecidableEq n] [Fintype Aux] [DecidableEq Aux]

theorem spectatorRootChannelWord_sub (k : κ → Matrix n n ℂ) (w : List κ)
    (B C : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannelWord k w (B - C) =
      spectatorRootChannelWord k w B - spectatorRootChannelWord k w C := by
  induction w generalizing B C with
  | nil => rfl
  | cons i w ih =>
    change spectatorRootChannelWord k w (spectatorRootChannel (k i) (B - C)) = _
    rw [spectatorRootChannel_sub, ih]
    rfl

/-- A word of root channels contracts differences in operator norm. -/
theorem norm_spectatorRootChannelWord_sub_le (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ)
    (B C : Matrix (n × Aux) (n × Aux) ℂ) :
    ‖spectatorRootChannelWord k w B - spectatorRootChannelWord k w C‖ ≤ ‖B - C‖ := by
  rw [← spectatorRootChannelWord_sub]
  exact norm_spectatorRootChannelWord_le k hk₀ hk₁ w (B - C)

/-- The operator-norm error `‖𝒲_w(B) - 𝒲_{w_P}(B)‖` of keeping only the events of `w` in `P`
[OAI265, §10.1, eq. (10.12)]. -/
noncomputable def channelWordOmissionDefect (k : κ → Matrix n n ℂ) (P : κ → Prop)
    [DecidablePred P] (w : List κ) (B : Matrix (n × Aux) (n × Aux) ℂ) : ℝ :=
  ‖spectatorRootChannelWord k w B -
    spectatorRootChannelWord k (w.filter (fun i => decide (P i))) B‖

/-- The omission defect is bounded independently of the word length. -/
theorem channelWordOmissionDefect_bounds (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (P : κ → Prop) [DecidablePred P]
    (w : List κ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    0 ≤ channelWordOmissionDefect k P w B ∧ channelWordOmissionDefect k P w B ≤ 2 * ‖B‖ :=
  ⟨norm_nonneg _, (norm_sub_le _ _).trans ((add_le_add
    (norm_spectatorRootChannelWord_le k hk₀ hk₁ w B)
    (norm_spectatorRootChannelWord_le k hk₀ hk₁ _ B)).trans_eq (by ring))⟩

/-- A retained event does not increase the defect; an omitted one costs its action on the
retained prefix [OAI265, §10.1, `09-amplification.tex`, lines 203–215]. -/
theorem channelWordOmissionDefect_append_sub_le (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (P : κ → Prop) [DecidablePred P]
    (w : List κ) (i : κ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    channelWordOmissionDefect k P (w ++ [i]) B - channelWordOmissionDefect k P w B ≤
      if P i then 0 else
        ‖spectatorRootChannel (k i)
            (spectatorRootChannelWord k (w.filter (fun j => decide (P j))) B) -
          spectatorRootChannelWord k (w.filter (fun j => decide (P j))) B‖ := by
  by_cases hi : P i
  · rw [if_pos hi]
    apply sub_nonpos.mpr
    simp only [channelWordOmissionDefect, List.filter_append,
      List.filter_cons, List.filter_nil, hi, decide_true, ite_true,
      spectatorRootChannelWord_append_singleton]
    rw [← spectatorRootChannel_sub]
    exact norm_spectatorRootChannel_le (hk₀ i) (hk₁ i) _
  · rw [if_neg hi]
    let F := spectatorRootChannelWord k w B
    let R := spectatorRootChannelWord k (w.filter (fun j => decide (P j))) B
    have hE : ‖spectatorRootChannel (k i) F - spectatorRootChannel (k i) R‖ ≤
        ‖F - R‖ := by
      rw [← spectatorRootChannel_sub]
      exact norm_spectatorRootChannel_le (hk₀ i) (hk₁ i) _
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (spectatorRootChannel (k i) F) (spectatorRootChannel (k i) R) R
    have hb : channelWordOmissionDefect k P (w ++ [i]) B =
        ‖spectatorRootChannel (k i) F - R‖ := by
      simp [channelWordOmissionDefect, List.filter_append, hi, F, R]
    rw [hb]
    change ‖spectatorRootChannel (k i) F - R‖ - ‖F - R‖ ≤
      ‖spectatorRootChannel (k i) R - R‖
    linarith

/-- The omitted-prefix telescope along a full Poisson word
[OAI265, §10.1, `09-amplification.tex`, lines 203–215]. -/
theorem channelWordOmissionDefect_le_sum_prefix (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (P : κ → Prop) [DecidablePred P]
    (w : PoissonWord.Word κ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    channelWordOmissionDefect k P (List.ofFn w.2) B ≤
      ∑ j : Fin w.1, if P (w.2 j) then 0 else
        ‖spectatorRootChannel (k (w.2 j))
            (spectatorRootChannelWord k
              ((List.ofFn (PoissonWord.take w j).2).filter (fun i => decide (P i))) B) -
          spectatorRootChannelWord k
            ((List.ofFn (PoissonWord.take w j).2).filter (fun i => decide (P i))) B‖ := by
  let f (u : PoissonWord.Word κ) := channelWordOmissionDefect k P (List.ofFn u.2) B
  have hzero : f PoissonWord.nil = 0 := by
    simp [f, channelWordOmissionDefect, PoissonWord.nil]
  have htel := PoissonWord.sum_prefix_increment f w
  rw [hzero, sub_zero] at htel
  change f w ≤ _
  rw [← htel]
  apply Finset.sum_le_sum
  intro j _
  simpa only [f, PoissonWord.append, List.ofFn_fin_append, PoissonWord.ofFn_singleton] using
    channelWordOmissionDefect_append_sub_le k hk₀ hk₁ P
      (List.ofFn (PoissonWord.take w j).2) (w.2 j) B

/-- **Expected omission error.**  The error of keeping only the retained events is integrable,
and its expectation is bounded by the time integral of the omitted one-event errors under the
retained-prefix law [OAI265, §10.1, eq. (10.12), `09-amplification.tex`, lines 203–215]. -/
theorem integrable_and_integral_channelWordOmissionDefect_le [Fintype κ]
    (k : κ → Matrix n n ℂ) (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (P : κ → Prop) [DecidablePred P] (B : Matrix (n × Aux) (n × Aux) ℂ) (T : ℝ≥0) :
    Integrable (fun w : PoissonWord.Word κ =>
        channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ T) ∧
      (∫ w : PoissonWord.Word κ,
        channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ T) ≤
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ),
        ∑ i ∈ Finset.univ.filter (fun i => ¬ P i),
          ∫ u : PoissonWord.Word {i // P i},
            ‖spectatorRootChannel (k i)
                (spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B) -
              spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B‖
            ∂PoissonWord.measure {i // P i} (Real.toNNReal s) := by
  let F (u : PoissonWord.Word {i // P i}) (i : κ) :=
    ‖spectatorRootChannel (k i)
        (spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B) -
      spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B‖
  have hF (u : PoissonWord.Word {i // P i}) (i : κ) : 0 ≤ F u i := norm_nonneg _
  have hbound (u : PoissonWord.Word {i // P i}) (i : κ) : F u i ≤ 2 * ‖B‖ := by
    have hword := norm_spectatorRootChannelWord_le (fun j : {i // P i} => k j)
      (fun j => hk₀ j) (fun j => hk₁ j) (List.ofFn u.2) B
    have hchannel := norm_spectatorRootChannel_le (hk₀ i) (hk₁ i)
      (spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B)
    have ht := norm_sub_le
      (spectatorRootChannel (k i)
        (spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B))
      (spectatorRootChannelWord (fun j : {i // P i} => k j) (List.ofFn u.2) B)
    dsimp only [F]
    linarith
  have hi := PoissonWord.integrable_of_nonneg_le_const T
    (fun w : PoissonWord.Word κ => channelWordOmissionDefect k P (List.ofFn w.2) B)
    (fun w => (channelWordOmissionDefect_bounds k hk₀ hk₁ P _ B).1)
    (fun w => (channelWordOmissionDefect_bounds k hk₀ hk₁ P _ B).2)
  have hsum := PoissonWord.integrable_sum_omitted_partition_prefix P T F hF hbound
  have hpath (w : PoissonWord.Word κ) :
      channelWordOmissionDefect k P (List.ofFn w.2) B ≤
        ∑ j : Fin w.1, if P (w.2 j) then 0 else
          F (PoissonWord.partitionWords P (PoissonWord.take w j)).1 (w.2 j) := by
    simpa only [F, spectatorRootChannelWord_filter] using
      channelWordOmissionDefect_le_sum_prefix k hk₀ hk₁ P w B
  refine ⟨hi, ?_⟩
  exact (integral_mono hi hsum hpath).trans_eq
    (PoissonWord.integral_sum_omitted_partition_prefix P T F hF hbound)

end OpenAI
