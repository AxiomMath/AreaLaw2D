/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/GraphInteractionDiamondCounting.lean`. Apache 2.0.
-/
import OpenAI.GraphInteractionBudget
import OpenAI.GraphLatticeDiamond
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Interaction budgets with the exact lattice diamond constant

For integer range `R`, the exact ambient count is `v_R = 1 + 2 * R * (R + 1)` and the
number of original supports containing a site is at most `μ_R = 2 ^ (v_R - 1)`.
A term-norm bound `J` therefore gives site budget `μ_R * J`, and the total weight of
length-`n` interaction-chain continuations is at most `(v_R * μ_R * J) ^ n`. These are the
ball count `eq:ball-count` and the multiplicity bound after it [OAI265, §2.2], and the budget
`eq:quasilocal-budget` [OAI265, §4].

The bounds use an arbitrary graph with an injective coordinate map, finite sets, and the
abstract interaction weights of `OpenAI.GraphInteractionBudget`. Walks may leave individual
supports and remain in the full graph. Holes and disconnected components are allowed.
-/

open scoped BigOperators

namespace OpenAI

variable {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}

omit [Finite V] [DecidableEq V] in
/-- Every finite support of graph range at most `R` has at most `v_R = 1 + 2 R (R + 1)` sites.
The empty support is included [OAI265, §2.2, `eq:ball-count`]. -/
theorem card_support_le_diamond (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (X : Finset V) (R : ℕ)
    (hrange : ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R) :
    X.card ≤ 1 + 2 * R * (R + 1) := by
  classical
  by_cases hX : X.Nonempty
  · obtain ⟨a, ha⟩ := hX
    exact card_le_diamond_of_walks coord X hcoord hstep a R (hrange a ha)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hX
    simp [hX]

/-- At most `μ_R = 2 ^ (v_R - 1)` original supports contain a specified site, with the exact
ambient diamond count `v_R` [OAI265, §2.2]. A finite set of supports enforces one term per
support. -/
theorem card_supports_containing_le_diamond (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (a : V) :
    (F.filter (fun X ↦ a ∈ X)).card ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
  classical
  let := Fintype.ofFinite V
  let B : Finset V := Finset.univ.filter (fun x ↦ ∃ p : G.Walk a x, p.length ≤ R)
  have haB : a ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ a, SimpleGraph.Walk.nil, by simp⟩
  have hB : B.card ≤ 1 + 2 * R * (R + 1) := by
    apply card_le_diamond_of_walks coord B hcoord hstep a R
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hFB : ∀ X ∈ F.filter (fun X ↦ a ∈ X), a ∈ X ∧ X ⊆ B := by
    intro X hX
    obtain ⟨hXF, haX⟩ := Finset.mem_filter.mp hX
    refine ⟨haX, ?_⟩
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hrange X hXF a haX x hx⟩
  calc
    (F.filter (fun X ↦ a ∈ X)).card ≤ 2 ^ (B.card - 1) :=
      card_supportFamily_le_pow _ B a haB hFB
    _ ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hB 1)

/-- Term weights bounded by `J ≥ 0` have site budget at most `μ_R * J`, using the exact
constant [OAI265, §4, `eq:quasilocal-budget`]. -/
theorem sum_supportWeights_containing_le_diamond (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J) (hw : ∀ X ∈ F, w X ≤ J) (a : V) :
    (∑ X ∈ F.filter (fun X ↦ a ∈ X), w X) ≤
      (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J := by
  have hcard := card_supports_containing_le_diamond coord hcoord hstep F R hrange a
  calc
    (∑ X ∈ F.filter (fun X ↦ a ∈ X), w X) ≤
        ((F.filter (fun X ↦ a ∈ X)).card : ℝ) * J := by
      simpa using Finset.sum_le_card_nsmul (F.filter (fun X ↦ a ∈ X)) w J
        (fun X hX ↦ hw X (Finset.mem_filter.mp hX).1)
    _ ≤ (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hJ

/-- Norms of original terms satisfy the site budget `μ_R * J`
[OAI265, §4, `eq:quasilocal-budget`]. The terms may live in any seminormed additive group. -/
theorem sum_supportNorms_containing_le_diamond {E : Type*} [SeminormedAddGroup E]
    (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (h : Finset V → E) (J : ℝ) (hJ : 0 ≤ J) (hh : ∀ X ∈ F, ‖h X‖ ≤ J) (a : V) :
    (∑ X ∈ F.filter (fun X ↦ a ∈ X), ‖h X‖) ≤
      (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J :=
  sum_supportWeights_containing_le_diamond coord hcoord hstep F R hrange
    (fun X ↦ ‖h X‖) J hJ hh a

/-- Weighted interaction-chain continuations are at most `(v_R * μ_R * J) ^ n`, with the
paper's exact diamond and multiplicity constants. Repeated supports are permitted
[OAI265, §4]. -/
theorem interactionChainWeightSum_le_diamond_pow (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hw0 : ∀ X ∈ F, 0 ≤ w X) (hwJ : ∀ X ∈ F, w X ≤ J)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F w X n ≤
      ((1 + 2 * R * (R + 1) : ℕ) *
        ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J)) ^ n := by
  apply interactionChainWeightSum_le_pow F w (1 + 2 * R * (R + 1))
    ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J)
    (mul_nonneg (Nat.cast_nonneg _) hJ) hw0 _ _ n X hX
  · intro Y hY
    exact card_support_le_diamond coord hcoord hstep Y R (hrange Y hY)
  · intro a
    exact sum_supportWeights_containing_le_diamond coord hcoord hstep F R hrange w J hJ hwJ a

/-- The exact continuation bound specialized to term norms [OAI265, §4]. -/
theorem interactionChainWeightSum_norm_le_diamond_pow {E : Type*} [SeminormedAddGroup E]
    (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (h : Finset V → E) (J : ℝ) (hJ : 0 ≤ J) (hh : ∀ X ∈ F, ‖h X‖ ≤ J)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F (fun Y ↦ ‖h Y‖) X n ≤
      ((1 + 2 * R * (R + 1) : ℕ) *
        ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J)) ^ n :=
  interactionChainWeightSum_le_diamond_pow coord hcoord hstep F R hrange
    (fun Y ↦ ‖h Y‖) J hJ (fun _ _ ↦ norm_nonneg _) hh n X hX

end OpenAI
