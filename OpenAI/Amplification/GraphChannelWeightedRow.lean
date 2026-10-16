/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphChannelWeightedRow.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations as in
`OpenAI.Amplification.GraphChannelEventKernel`: the graph is the induced square lattice on
`Λ`, with sites `ℤ × ℤ`; the anchors are maps `a : κ → ℤ × ℤ`; `graphBall G x l` is
`OpenAI.graphNbhd Λ {x} l`, `G.edist` is `OpenAI.domainEDist Λ`, the natural distance
`G.dist y z` is `(domainEDist Λ y z).toNat`, `G.Reachable y z` is
`domainEDist Λ y z ≠ ⊤`, the cutoffs are `Λ.sup fun x => (domainEDist Λ (a i) x).toNat`,
component support is `OpenAI.IsSupportedOn (domainComponent_subset Λ (a i))`, and
`siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ Λ)`; sums over all sites are sums over
`Λ`.  In `exists_graphChannelEventKernel_weighted_row_le` the quantification over the site type
and graph becomes one over the domain `Λ`; in
`exists_graphChannelEventKernel_bounds_of_component_support` the local family `Fin q` with
`[NeZero q]` is an arbitrary local family `loc` with `[∀ i, Nonempty (loc i)]`.
`card_anchor_fiber_subtype_le` is stated for anchors in an arbitrary type.  Added helper:
`OpenAI.domainEDist_triangle`, the triangle inequality of `OpenAI.domainEDist`.
-/
import OpenAI.Amplification.GraphChannelEventKernel
import OpenAI.TruncationSeries

/-!
# Uniform weighted rows of the graph-ball incidence kernel

The kernel `graphChannelEventKernel` counts, with stretched-exponential weights in the radius,
the labels whose balls contain two given sites [OAI265, §10.1, eq. (10.10)].  Quadratic bounds
on the graph balls and a uniform bound on the anchor fibers give a weighted row estimate whose
constant is chosen before the domain, the labels and the cutoff [OAI265, §10.1, eq. (10.11)].
Labels with the same anchor remain distinct.  Balls use the extended distance, so incidences
between different components vanish before the natural distance enters the weight.

## Main definitions

* `OpenAI.graphChannelEventKernel`: the finite event kernel.

## Main statements

* `OpenAI.exists_graphChannelEventKernel_weighted_row_le`: the uniform weighted row bound.
* `OpenAI.exists_graphChannelEventKernel_bounds_of_component_support`: the row bound together
  with the domination of the summed channel increments by the kernel.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 139–160.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

/-- The triangle inequality of the domain distance; it holds also off `Λ`, where the distance
is `⊤`. -/
theorem domainEDist_triangle (Λ : Finset (ℤ × ℤ)) (x y z : ℤ × ℤ) :
    domainEDist Λ x z ≤ domainEDist Λ x y + domainEDist Λ y z := by
  by_cases hx : x ∈ Λ
  · by_cases hy : y ∈ Λ
    · by_cases hz : z ∈ Λ
      · rw [domainEDist_of_mem hx hz, domainEDist_of_mem hx hy, domainEDist_of_mem hy hz]
        exact SimpleGraph.edist_triangle
      · rw [domainEDist_of_not_mem_right (x := y) hz]
        simp
    · rw [domainEDist_of_not_mem_right (x := x) hy]
      simp
  · rw [domainEDist_of_not_mem_left (y := y) hx]
    simp

/-- Retaining a predicate of labels does not increase any anchor fiber; distinct labels at the
same anchor stay distinct [OAI265, §10.1, `09-amplification.tex`, lines 139–160]. -/
theorem card_anchor_fiber_subtype_le {ι κ : Type*} [Fintype κ] [DecidableEq ι] (a : κ → ι)
    (P : κ → Prop) [DecidablePred P] (x : ι) :
    (Finset.univ.filter fun i : {i // P i} => a i = x).card ≤
      (Finset.univ.filter fun i : κ => a i = x).card := by
  classical
  exact Finset.card_le_card_of_injOn Subtype.val
    (fun i hi => by simpa using hi) (fun _ _ _ _ h => Subtype.ext h)

variable {κ : Type*} [Fintype κ]

/-- The finite kernel of the event-family oscillation estimate:
`D ∑_{l ≤ N} e^{-b l^α} #{i : y, z ∈ N_l(a_i)}`, counting labels with repeated anchors
[OAI265, §10.1, eq. (10.10), `09-amplification.tex`, lines 139–146]. -/
noncomputable def graphChannelEventKernel (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    (D b α : ℝ) (N : ℕ) (y z : ℤ × ℤ) : ℝ :=
  D * ∑ l ∈ Finset.range (N + 1), Real.exp (-(b * (l : ℝ) ^ α)) *
    ((Finset.univ.filter fun i : κ =>
      y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l).card : ℝ)

theorem graphChannelEventKernel_nonneg (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    {D : ℝ} (hD : 0 ≤ D) (b α : ℝ) (N : ℕ) (y z : ℤ × ℤ) :
    0 ≤ graphChannelEventKernel Λ a D b α N y z :=
  mul_nonneg hD (Finset.sum_nonneg fun l _ => by positivity)

/-- Different components of `Λ` have no common ball incidence, so the zero convention of the
natural distance never creates a kernel entry between components
[OAI265, §10.1, `09-amplification.tex`, lines 139–155]. -/
theorem graphChannelEventKernel_eq_zero_of_not_reachable (Λ : Finset (ℤ × ℤ))
    (a : κ → ℤ × ℤ) (D b α : ℝ) (N : ℕ) (y z : ℤ × ℤ) (hyz : domainEDist Λ y z = ⊤) :
    graphChannelEventKernel Λ a D b α N y z = 0 := by
  have hempty (l : ℕ) : (Finset.univ.filter fun i : κ =>
      y ∈ graphNbhd Λ {a i} l ∧ z ∈ graphNbhd Λ {a i} l) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun i hi => ?_
    obtain ⟨hy, hz⟩ := (Finset.mem_filter.mp hi).2
    rw [mem_graphNbhd_singleton_iff_domainEDist_le] at hy hz
    have h := (domainEDist_triangle Λ y (a i) z).trans
      (add_le_add (domainEDist_comm (Λ := Λ) ▸ hy) hz)
    rw [hyz] at h
    exact not_le_of_gt (ENat.natCast_lt_top (l + l)) (by exact_mod_cast h)
  simp [graphChannelEventKernel, hempty]

/-- The labels whose balls of radius `l` contain `y` number at most `μ` times the size of the
ball of radius `l` about `y` [OAI265, §10.1, `09-amplification.tex`, lines 152–154]. -/
theorem card_graphBall_anchors_le (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ) {μ : ℝ}
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (y : ℤ × ℤ) (l : ℕ) :
    ((Finset.univ.filter fun i : κ => y ∈ graphNbhd Λ {a i} l).card : ℝ) ≤
      μ * (graphNbhd Λ {y} l).card := by
  have hsub : (Finset.univ.filter fun i : κ => y ∈ graphNbhd Λ {a i} l) ⊆
      Finset.univ.filter fun i : κ => a i ∈ graphNbhd Λ {y} l := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_graphNbhd_singleton_iff_domainEDist_le] at hi ⊢
    rwa [domainEDist_comm]
  have hcount := Finset.sum_card_fiberwise_eq_card_filter Finset.univ (graphNbhd Λ {y} l) a
  calc ((Finset.univ.filter fun i : κ => y ∈ graphNbhd Λ {a i} l).card : ℝ)
      ≤ ((Finset.univ.filter fun i : κ => a i ∈ graphNbhd Λ {y} l).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ∑ x ∈ graphNbhd Λ {y} l, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) := by
        rw [← hcount, Nat.cast_sum]
    _ ≤ ∑ _x ∈ graphNbhd Λ {y} l, μ := Finset.sum_le_sum fun x _ => hfiber x
    _ = μ * (graphNbhd Λ {y} l).card := by simp [mul_comm]

/-- Two sites of a ball of radius `l` are at natural distance at most `2 l`. -/
private theorem toNat_domainEDist_le_two_mul_of_mem {Λ : Finset (ℤ × ℤ)} {x y z : ℤ × ℤ}
    {l : ℕ} (hy : y ∈ graphNbhd Λ {x} l) (hz : z ∈ graphNbhd Λ {x} l) :
    (domainEDist Λ y z).toNat ≤ 2 * l := by
  rw [mem_graphNbhd_singleton_iff_domainEDist_le] at hy hz
  have h : domainEDist Λ y z ≤ ((2 * l : ℕ) : ℕ∞) :=
    calc
      domainEDist Λ y z ≤ domainEDist Λ y x + domainEDist Λ x z := domainEDist_triangle Λ y x z
      _ ≤ (l : ℕ∞) + l := add_le_add (by rwa [domainEDist_comm]) hz
      _ = ((2 * l : ℕ) : ℕ∞) := by push_cast; ring
  exact ENat.toNat_le_of_le_natCast h

private theorem weighted_graphBall_term_le {Λ : Finset (ℤ × ℤ)} {b α : ℝ} (hb : 0 < b)
    (hα : 0 < α) {x y z : ℤ × ℤ} {l : ℕ} (hy : y ∈ graphNbhd Λ {x} l)
    (hz : z ∈ graphNbhd Λ {x} l) :
    Real.exp (-(b * (l : ℝ) ^ α)) *
        Real.exp (b / (2 * (2 : ℝ) ^ α) * ((domainEDist Λ y z).toNat : ℝ) ^ α) ≤
      Real.exp (-(b / 2 * (l : ℝ) ^ α)) := by
  have hdist := toNat_domainEDist_le_two_mul_of_mem hy hz
  have hpow : ((domainEDist Λ y z).toNat : ℝ) ^ α ≤ (2 : ℝ) ^ α * (l : ℝ) ^ α := by
    calc
      _ ≤ (2 * (l : ℝ)) ^ α := Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast hdist) hα.le
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  have htwo : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hweight : b / (2 * (2 : ℝ) ^ α) * ((domainEDist Λ y z).toNat : ℝ) ^ α ≤
      b / 2 * (l : ℝ) ^ α := by
    calc
      _ ≤ b / (2 * (2 : ℝ) ^ α) * ((2 : ℝ) ^ α * (l : ℝ) ^ α) := by
        gcongr
      _ = _ := by field_simp
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The finite geometric step: quadratic ball growth and bounded anchor fibers reduce every
weighted row to a fourth-power stretched-exponential sum
[OAI265, §10.1, eq. (10.11), `09-amplification.tex`, lines 146–160]. -/
theorem sum_graphChannelEventKernel_mul_exp_le (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    {D K μ b α : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hα : 0 < α)
    (hball : ∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (N : ℕ) (y : ℤ × ℤ) :
    (∑ z ∈ Λ, graphChannelEventKernel Λ a D b α N y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * ((domainEDist Λ y z).toNat : ℝ) ^ α)) ≤
      D * μ * K ^ 2 * ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 4 *
        Real.exp (-(b / 2 * (l : ℝ) ^ α)) := by
  let w (l : ℕ) := Real.exp (-(b * (l : ℝ) ^ α))
  let v (l : ℕ) := Real.exp (-(b / 2 * (l : ℝ) ^ α)) * K * ((l : ℝ) + 1) ^ 2
  let d (z : ℤ × ℤ) :=
    Real.exp (b / (2 * (2 : ℝ) ^ α) * ((domainEDist Λ y z).toNat : ℝ) ^ α)
  have hrow : (∑ z ∈ Λ, graphChannelEventKernel Λ a D b α N y z * d z) =
      D * ∑ i, ∑ l ∈ (Finset.range (N + 1)).filter
        (fun l : ℕ => domainEDist Λ (a i) y ≤ l), w l * ∑ z ∈ graphNbhd Λ {a i} l, d z := by
    rw [sum_graphBall_shell_eq_sum_card]
    simp only [graphChannelEventKernel, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hevent (i : κ) (l : ℕ) (hl : domainEDist Λ (a i) y ≤ l) :
      w l * ∑ z ∈ graphNbhd Λ {a i} l, d z ≤ v l := by
    calc
      _ = ∑ z ∈ graphNbhd Λ {a i} l, w l * d z := Finset.mul_sum ..
      _ ≤ ∑ _z ∈ graphNbhd Λ {a i} l, Real.exp (-(b / 2 * (l : ℝ) ^ α)) :=
        Finset.sum_le_sum fun z hz => weighted_graphBall_term_le hb hα
          (mem_graphNbhd_singleton_iff_domainEDist_le.mpr hl) hz
      _ = Real.exp (-(b / 2 * (l : ℝ) ^ α)) * (graphNbhd Λ {a i} l).card := by
        simp [mul_comm]
      _ ≤ v l := by
        dsimp [v]
        nlinarith [hball (a i) l, Real.exp_pos (-(b / 2 * (l : ℝ) ^ α))]
  have hanchors (l : ℕ) :
      ((Finset.univ.filter fun i : κ => y ∈ graphNbhd Λ {a i} l).card : ℝ) ≤
        μ * K * ((l : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ μ * (graphNbhd Λ {y} l).card := card_graphBall_anchors_le Λ a hfiber y l
      _ ≤ μ * (K * ((l : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left (hball y l) hμ
      _ = _ := by ring
  calc
    _ = D * ∑ i, ∑ l ∈ (Finset.range (N + 1)).filter
        (fun l : ℕ => domainEDist Λ (a i) y ≤ l), w l * ∑ z ∈ graphNbhd Λ {a i} l, d z :=
      hrow
    _ ≤ D * ∑ i, ∑ l ∈ (Finset.range (N + 1)).filter
        (fun l : ℕ => domainEDist Λ (a i) y ≤ l), v l := by
      gcongr with i _ l hl
      exact hevent i l (Finset.mem_filter.mp hl).2
    _ = D * ∑ l ∈ Finset.range (N + 1), v l *
        ((Finset.univ.filter fun i : κ => y ∈ graphNbhd Λ {a i} l).card : ℝ) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.natCast_card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_graphNbhd_singleton_iff_domainEDist_le]
      split_ifs <;> simp
    _ ≤ D * ∑ l ∈ Finset.range (N + 1), v l * (μ * K * ((l : ℝ) + 1) ^ 2) := by
      gcongr with l _
      exact hanchors l
    _ = _ := by
      simp only [v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

private theorem exists_sum_fourth_pow_mul_exp_neg_rpow_le {b α : ℝ}
    (hb : 0 < b) (hα : 0 < α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 4 *
        Real.exp (-(b / 2 * (l : ℝ) ^ α)) ≤ A := by
  obtain ⟨M, hM, hMb⟩ :=
    exists_one_add_pow_mul_exp_neg_rpow_le (b := b / 4) (by positivity) hα 2
  obtain ⟨S, hS, hSb⟩ := exists_sum_shell_le (c := b / 4) (by positivity) hα
  refine ⟨M * S, mul_nonneg hM hS, fun N => ?_⟩
  have hterm (l : ℕ) :
      ((l : ℝ) + 1) ^ 4 * Real.exp (-(b / 2 * (l : ℝ) ^ α)) ≤
        M * (((l : ℝ) + 1) ^ 2 *
          Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α))) := by
    have hfloor : ((l / 2 : ℕ) : ℝ) ^ α ≤ (l : ℝ) ^ α :=
      Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast Nat.div_le_self l 2) hα.le
    have hexp : Real.exp (-(b / 4 * (l : ℝ) ^ α)) ≤
        Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hfloor (by positivity))
    calc
      ((l : ℝ) + 1) ^ 4 * Real.exp (-(b / 2 * (l : ℝ) ^ α)) =
          (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * (l : ℝ) ^ α))) *
          (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * (l : ℝ) ^ α))) := by
        rw [show -(b / 2 * (l : ℝ) ^ α) =
          -(b / 4 * (l : ℝ) ^ α) + -(b / 4 * (l : ℝ) ^ α) by ring, Real.exp_add]
        ring
      _ ≤ M * (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * (l : ℝ) ^ α))) :=
        mul_le_mul_of_nonneg_right (hMb l (by positivity)) (by positivity)
      _ ≤ M * (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (by positivity)) hM
  have hsum : ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 2 *
      Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α)) ≤ S := by
    simpa [Real.zero_rpow (ne_of_gt hα)] using hSb 0 (N + 1)
  calc
    _ ≤ ∑ l ∈ Finset.range (N + 1), M * (((l : ℝ) + 1) ^ 2 *
        Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α))) :=
      Finset.sum_le_sum fun l _ => hterm l
    _ = M * ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 2 *
        Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α)) := by rw [Finset.mul_sum]
    _ ≤ M * S := mul_le_mul_of_nonneg_left hsum hM

/-- **Weighted row bound** for the finite ball-incidence kernel, independent of the volume and
the cutoff.  The constant depends only on `D, K, μ, b, α` and is chosen before the label type,
the domain, the anchors and the cutoff; the weight exponent is `b / (2 · 2^α)`
[OAI265, §10.1, eq. (10.11), `09-amplification.tex`, lines 146–160]. -/
theorem exists_graphChannelEventKernel_weighted_row_le {D K μ b α : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type*) [Fintype κ] (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ),
      (∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
      (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
      ∀ (N : ℕ) (y : ℤ × ℤ),
        (∑ z ∈ Λ, graphChannelEventKernel Λ a D b α N y z *
          Real.exp (b / (2 * (2 : ℝ) ^ α) * ((domainEDist Λ y z).toNat : ℝ) ^ α)) ≤ C := by
  obtain ⟨A, hA, hbound⟩ := exists_sum_fourth_pow_mul_exp_neg_rpow_le hb hα
  refine ⟨D * μ * K ^ 2 * A, by positivity, ?_⟩
  intro κ _ Λ a hball hfiber N y
  exact (sum_graphChannelEventKernel_mul_exp_le Λ a hD hK hμ hb hα hball hfiber N y).trans
    (mul_le_mul_of_nonneg_left (hbound N) (by positivity))

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The summed full-channel oscillation increments are dominated by the event kernel, with the
coefficient derived from the localization tails, factor two included
[OAI265, §10.1, eq. (10.10), `09-amplification.tex`, lines 139–146]. -/
theorem sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
    (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ) (k : κ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, IsSupportedOn (domainComponent_subset Λ (a i)) (k i))
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (N : ℕ) (hN : ∀ i, Λ.sup (fun x => (domainEDist Λ (a i) x).toNat) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ℤ × ℤ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ) :
    (∑ i, (siteOscillation y (spectatorRootChannel (k i) B) - siteOscillation y B)) ≤
      ∑ z ∈ Λ, graphChannelEventKernel Λ a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z * siteOscillation z B := by
  have h := sum_siteOscillation_spectatorRootChannel_sub_le_exp_card
    Λ a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε y B
  convert h using 1
  simp only [graphChannelEventKernel, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Event kernel bounds** for a finite family of component-supported positive contractions:
a uniform weighted row bound, and the domination of the summed channel increments by the
kernel.  With `A = 2 + 8 √C e^{c/2}` the kernel has `D = 2 A`, `b = c / 2` and the weight
exponent `c / (4 · 2^α)`.  The row constant is chosen before the label and spectator types, the
local family, the domain, the effects and the cutoff
[OAI265, §10.1, eqs. (10.10)–(10.11), `09-amplification.tex`, lines 139–160]. -/
theorem exists_graphChannelEventKernel_bounds_of_component_support {C K μ c α : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ R : ℝ, 0 ≤ R ∧
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
        (∀ y, (∑ z ∈ Λ,
          graphChannelEventKernel Λ a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
            (c / 2) α N y z * Real.exp (c / (4 * (2 : ℝ) ^ α) *
              ((domainEDist Λ y z).toNat : ℝ) ^ α)) ≤ R) ∧
        (∀ (y : ℤ × ℤ) (B : Matrix (Reg loc Λ × Aux) (Reg loc Λ × Aux) ℂ),
          (∑ i, (siteOscillation y (spectatorRootChannel (k i) B) - siteOscillation y B)) ≤
          ∑ z ∈ Λ,
            graphChannelEventKernel Λ a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
              (c / 2) α N y z * siteOscillation z B) := by
  obtain ⟨R, hR, hrows⟩ := exists_graphChannelEventKernel_weighted_row_le
    (D := 2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))) (by positivity) hK hμ (half_pos hc) hα
  refine ⟨R, hR, ?_⟩
  intro κ Aux _ _ _ loc _ _ _ Λ a k hk₀ hk₁ hk hball hfiber N hN hε
  constructor
  · intro y
    convert hrows κ Λ a hball hfiber N y using 1
    congr 1
    ext z
    congr 2
    ring
  · exact sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
      Λ a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε

end OpenAI
