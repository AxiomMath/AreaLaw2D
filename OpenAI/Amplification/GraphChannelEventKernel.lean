/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphChannelEventKernel.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations as in
`OpenAI.Amplification.ComponentChannelOscillation`: the graph is the induced square lattice on
`Λ`, with sites `ℤ × ℤ` and an arbitrary local family `loc`; the anchors are maps
`a : κ → ℤ × ℤ`; `graphBall G (a i) l` is `OpenAI.graphNbhd Λ {a i} l`, `G.edist` is
`OpenAI.domainEDist Λ`, the cutoffs are `Λ.sup fun x => (domainEDist Λ (a i) x).toNat`,
component support is `OpenAI.IsSupportedOn (domainComponent_subset Λ (a i))`, and
`siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ Λ)`.  Sums over all sites `z : ι` are
sums over `z ∈ Λ`; the ball incidences vanish off `Λ`.
-/
import OpenAI.Amplification.GraphChannelOscillation

/-!
# Finite event-family bounds for full graph channels

The sum of the oscillation increments of the component-supported root channels of a finite
family of events is bounded by a finite weighted count of ball incidences
[OAI265, §10.1, eq. (10.10)].  Labels remain distinct even when their anchors coincide.  The
estimate holds for arbitrary operators with arbitrary finite spectators; the only reordering is
of finite sums.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 139–155.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

variable {κ : Type*} [Fintype κ]

/-- A sum over a graph ball is the sum over `Λ` of the ball indicator. -/
private theorem sum_graphNbhd_eq_sum_ite (Λ : Finset (ℤ × ℤ)) (x : ℤ × ℤ) (l : ℕ)
    (d : ℤ × ℤ → ℝ) :
    ∑ z ∈ graphNbhd Λ {x} l, d z = ∑ z ∈ Λ, if z ∈ graphNbhd Λ {x} l then d z else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (graphNbhd_subset Λ {x} l)]

private theorem sum_graphBall_eq_sum_card (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    (l : ℕ) (y : ℤ × ℤ) (d : ℤ × ℤ → ℝ) :
    (∑ i, if y ∈ graphNbhd Λ {a i} l then ∑ z ∈ graphNbhd Λ {a i} l, d z else 0) =
      ∑ z ∈ Λ, ((Finset.univ.filter fun i : κ =>
        y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l).card : ℝ) * d z := by
  classical
  calc
    _ = ∑ i, ∑ z ∈ Λ, if y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l
        then d z else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hy : y ∈ graphNbhd Λ {a i} l
      · simp only [hy, if_true, true_and, sum_graphNbhd_eq_sum_ite]
      · simp [hy]
    _ = ∑ z ∈ Λ, ∑ i, if y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l
        then d z else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.natCast_card_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

/-- Reorder the finite shell sum into a count of the labels whose ball contains both sites;
repeated anchors keep their multiplicity [OAI265, §10.1, `09-amplification.tex`,
lines 139–146, at a finite cutoff]. -/
theorem sum_graphBall_shell_eq_sum_card (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    (n : ℕ) (w : ℕ → ℝ) (y : ℤ × ℤ) (d : ℤ × ℤ → ℝ) :
    (∑ i, ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => domainEDist Λ (a i) y ≤ l),
      w l * ∑ z ∈ graphNbhd Λ {a i} l, d z) =
      ∑ l ∈ Finset.range (n + 1), w l *
        ∑ z ∈ Λ, ((Finset.univ.filter fun i : κ =>
          y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l).card : ℝ) * d z := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  calc
    _ = w l * ∑ i, if y ∈ graphNbhd Λ {a i} l
        then ∑ z ∈ graphNbhd Λ {a i} l, d z else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_graphNbhd_singleton_iff_domainEDist_le, mul_ite, mul_zero]
    _ = _ := by rw [sum_graphBall_eq_sum_card]

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The oscillation increments of the full channels of a finite family of component-supported
events are bounded by an explicit finite count of ball incidences.  No injectivity of the
anchors and no Hermiticity of the input is required; the common cutoff contains every anchor
component [OAI265, §10.1, eq. (10.10), `09-amplification.tex`, lines 139–146]. -/
theorem sum_siteOscillation_spectatorRootChannel_sub_le_exp_card (Λ : Finset (ℤ × ℤ))
    (a : κ → ℤ × ℤ) (k : κ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, IsSupportedOn (domainComponent_subset Λ (a i)) (k i))
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : ∀ i, Λ.sup (fun x => (domainEDist Λ (a i) x).toNat) ≤ n)
    (hε : ∀ i l, l ≤ n → ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ℤ × ℤ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    (∑ i, (siteOscillation y (spectatorRootChannel (k i) B) - siteOscillation y B)) ≤
      2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        ∑ l ∈ Finset.range (n + 1), Real.exp (-(c / 2 * (l : ℝ) ^ α)) *
          ∑ z ∈ Λ, ((Finset.univ.filter fun i : κ =>
            y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l).card : ℝ) *
              siteOscillation z B := by
  classical
  calc
    _ ≤ ∑ i, 2 *
        ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => domainEDist Λ (a i) y ≤ l),
          ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
            Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
              ∑ z ∈ graphNbhd Λ {a i} l, siteOscillation z B := by
      apply Finset.sum_le_sum
      intro i _
      exact sub_le_iff_le_add'.mpr
        (siteOscillation_spectatorRootChannel_le_exp_of_component_support
          Λ (a i) (hk₀ i) (hk₁ i) (hk i) hC hc hα hα₁ n (hn i) (hε i) y B)
    _ = _ := by
      rw [← Finset.mul_sum, sum_graphBall_shell_eq_sum_card]
      simp_rw [mul_assoc, ← Finset.mul_sum]

end OpenAI
