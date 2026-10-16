/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/GraphOmittedAnchorTail.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the graph is the induced
square lattice on a domain `Λ`, with sites `ℤ × ℤ`, as in
`OpenAI.Amplification.GraphChannelWeightedRow` (`graphBall G x l` is `OpenAI.graphNbhd Λ {x} l`,
`G.edist` is `OpenAI.domainEDist Λ`, anchors are maps `a : κ → ℤ × ℤ`, the quantification over
the site type and graph becomes one over `Λ`, sums over all sites are sums over `Λ`).  TNLean's
profile `Metric.exponentialDistanceProfile (S : Set ι) β α` for the pseudo-emetric
`graphPseudoEMetricSpace G` is `OpenAI.domainDistanceProfile Λ S β α`, defined here directly from
the domain distance to `S`, `⨅ s ∈ S, domainEDist Λ y s`, the distance of `OpenAI.graphNbhd`; on
`Λ` it is the metric profile of the induced graph
(`OpenAI.domainDistanceProfile_eq_exponentialDistanceProfile`), and it vanishes off `Λ`.  The
target set `S` is a finite subset of `ℤ²`, not required to lie in `Λ`.
-/
import OpenAI.ExponentialDistanceProfile
import OpenAI.GraphExtendedMetric
import OpenAI.StretchedExponentialSummability
import OpenAI.Amplification.GraphChannelWeightedRow

/-!
# Exponential tails for omitted anchors

Quadratic growth of the graph balls of `Λ` and bounded anchor multiplicity control the sum of
the finite shell weights against the stretched-exponential profile `e^{-β d_Λ(·, S)^α}` of a
finite target set `S`.  If every omitted anchor is farther than `r` from `S`, the sum decays
like `e^{-γ r^α}` [OAI265, §10.1, the omitted-event estimate after eq. (10.12)].  The constants
precede the domain, all finite types, the omitted labels, the target and the cutoff.  Empty sets
and disconnected domains need no special hypotheses: the profile is zero at infinite distance.

## Main definitions

* `OpenAI.domainDistanceProfile`: the stretched-exponential profile of the domain distance to
  a finite set.

## Main statements

* `OpenAI.exists_sum_omitted_graphBall_exponentialDistanceProfile_le`: the omitted-anchor tail.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 188–215.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open SimpleGraph
open scoped ENNReal

namespace OpenAI

/-! ## The distance profile of a finite set -/

section Profile

variable {Λ S : Finset (ℤ × ℤ)}

/-- The stretched-exponential profile `e^{-β d_Λ(y, S)^α}` of the distance from `y` to `S` in
the induced graph on `Λ`, and `0` at infinite distance, in particular off `Λ` and for `S = ∅`
[OAI265, §10.1, the profile of eq. (10.11)]. -/
noncomputable def domainDistanceProfile (Λ S : Finset (ℤ × ℤ)) (β α : ℝ) (y : ℤ × ℤ) : ℝ :=
  if (⨅ s ∈ S, domainEDist Λ y s) = ⊤ then 0
  else Real.exp (-β * (((⨅ s ∈ S, domainEDist Λ y s).toNat : ℕ) : ℝ) ^ α)

theorem domainDistanceProfile_nonneg (Λ S : Finset (ℤ × ℤ)) (β α : ℝ) (y : ℤ × ℤ) :
    0 ≤ domainDistanceProfile Λ S β α y := by
  unfold domainDistanceProfile
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

@[simp]
theorem domainDistanceProfile_eq_zero_iff (Λ S : Finset (ℤ × ℤ)) (β α : ℝ) (y : ℤ × ℤ) :
    domainDistanceProfile Λ S β α y = 0 ↔ (⨅ s ∈ S, domainEDist Λ y s) = ⊤ := by
  unfold domainDistanceProfile
  split_ifs with h
  · simp [h]
  · simp [h, Real.exp_ne_zero]

theorem domainDistanceProfile_of_ne_top (Λ S : Finset (ℤ × ℤ)) (β α : ℝ) {y : ℤ × ℤ}
    (hy : (⨅ s ∈ S, domainEDist Λ y s) ≠ ⊤) :
    domainDistanceProfile Λ S β α y =
      Real.exp (-β * (((⨅ s ∈ S, domainEDist Λ y s).toNat : ℕ) : ℝ) ^ α) := by
  simp [domainDistanceProfile, hy]

@[simp]
theorem domainDistanceProfile_empty (Λ : Finset (ℤ × ℤ)) (β α : ℝ) (y : ℤ × ℤ) :
    domainDistanceProfile Λ ∅ β α y = 0 := by
  simp [domainDistanceProfile]

/-- The profile vanishes off `Λ`. -/
theorem domainDistanceProfile_of_notMem (S : Finset (ℤ × ℤ)) (β α : ℝ) {y : ℤ × ℤ}
    (hy : y ∉ Λ) : domainDistanceProfile Λ S β α y = 0 := by
  rw [domainDistanceProfile_eq_zero_iff]
  simp [domainEDist_of_not_mem_left hy]

/-- The profile is one on the sites of `S` in `Λ`. -/
theorem domainDistanceProfile_eq_one_of_mem (β : ℝ) {α : ℝ} (hα : 0 < α) {y : ℤ × ℤ}
    (hyΛ : y ∈ Λ) (hy : y ∈ S) : domainDistanceProfile Λ S β α y = 1 := by
  have h0 : (⨅ s ∈ S, domainEDist Λ y s) = 0 :=
    le_antisymm ((iInf₂_le y hy).trans (domainEDist_self hyΛ).le) bot_le
  simp [domainDistanceProfile, h0, Real.zero_rpow hα.ne']

/-- For `S ⊆ Λ` the profile dominates the indicator of `S`. -/
theorem indicator_one_le_domainDistanceProfile (hS : S ⊆ Λ) (β : ℝ) {α : ℝ} (hα : 0 < α)
    (y : ℤ × ℤ) :
    (S : Set (ℤ × ℤ)).indicator (fun _ => (1 : ℝ)) y ≤ domainDistanceProfile Λ S β α y := by
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem (Finset.mem_coe.2 hy),
      domainDistanceProfile_eq_one_of_mem β hα (hS hy) hy]
  · rw [Set.indicator_of_notMem (by simpa using hy)]
    exact domainDistanceProfile_nonneg Λ S β α y

/-- The domain distance to a nonempty finite set is attained. -/
private theorem exists_mem_domainEDist_eq_iInf {Λ S : Finset (ℤ × ℤ)} (hS : S.Nonempty)
    (z : ℤ × ℤ) : ∃ s ∈ S, domainEDist Λ z s = ⨅ t ∈ S, domainEDist Λ z t := by
  obtain ⟨s, hs, hmin⟩ := S.exists_min_image (fun t => domainEDist Λ z t) hS
  exact ⟨s, hs, le_antisymm (le_iInf₂ fun t ht => hmin t ht) (iInf₂_le s hs)⟩

/-- On `Λ` the profile is the exponential distance profile of the induced graph, with its
extended graph distance as pseudo-emetric. -/
theorem domainDistanceProfile_eq_exponentialDistanceProfile (Λ S : Finset (ℤ × ℤ)) (β α : ℝ)
    {y : ℤ × ℤ} (hy : y ∈ Λ) :
    letI := graphPseudoEMetricSpace ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    domainDistanceProfile Λ S β α y =
      Metric.exponentialDistanceProfile
        (Subtype.val ⁻¹' (S : Set (ℤ × ℤ)) : Set (Λ : Set (ℤ × ℤ))) β α ⟨y, hy⟩ := by
  let := graphPseudoEMetricSpace ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
  have hinf : Metric.infEDist (⟨y, hy⟩ : (Λ : Set (ℤ × ℤ)))
      (Subtype.val ⁻¹' (S : Set (ℤ × ℤ))) = ((⨅ s ∈ S, domainEDist Λ y s : ℕ∞) : ℝ≥0∞) := by
    apply le_antisymm
    · rcases S.eq_empty_or_nonempty with rfl | hS
      · simp
      obtain ⟨s₀, hs₀, heq⟩ := exists_mem_domainEDist_eq_iInf (Λ := Λ) hS y
      rw [← heq]
      by_cases hs₀Λ : s₀ ∈ Λ
      · refine (Metric.infEDist_le_edist_of_mem (show (⟨s₀, hs₀Λ⟩ : (Λ : Set (ℤ × ℤ))) ∈
          Subtype.val ⁻¹' (S : Set (ℤ × ℤ)) from hs₀)).trans_eq ?_
        rw [graphPseudoEMetricSpace_edist, domainEDist_of_mem hy hs₀Λ]
      · rw [domainEDist_of_not_mem_right hs₀Λ]
        simp
    · refine Metric.le_infEDist.mpr fun t ht => ?_
      rw [graphPseudoEMetricSpace_edist, ← domainEDist_of_mem hy t.2]
      exact ENat.toENNReal_mono (iInf₂_le t.1 ht)
  simp only [domainDistanceProfile, Metric.exponentialDistanceProfile, hinf]
  generalize (⨅ s ∈ S, domainEDist Λ y s) = X
  induction X using ENat.recTopCoe <;> simp

end Profile

/-! ## The omitted-anchor tail -/

private theorem profile_finset_le_sum_singleton (Λ S : Finset (ℤ × ℤ)) (c α : ℝ)
    (z : ℤ × ℤ) :
    domainDistanceProfile Λ S c α z ≤ ∑ s ∈ S, domainDistanceProfile Λ {s} c α z := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨s₀, hs₀, heq⟩ := exists_mem_domainEDist_eq_iInf (Λ := Λ) hS z
  have hsingle : (⨅ t ∈ ({s₀} : Finset (ℤ × ℤ)), domainEDist Λ z t) = domainEDist Λ z s₀ := by
    simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  have hp : domainDistanceProfile Λ S c α z = domainDistanceProfile Λ {s₀} c α z := by
    unfold domainDistanceProfile
    rw [hsingle, heq]
  rw [hp]
  exact Finset.single_le_sum (f := fun s => domainDistanceProfile Λ {s} c α z)
    (fun s _ => domainDistanceProfile_nonneg _ _ _ _ _) hs₀

variable {κ : Type*} [Fintype κ]

/-- The profile of a single site has a total mass independent of the volume under quadratic
ball growth, through the summable second moment of the stretched exponential
[OAI265, §10.1, `09-amplification.tex`, lines 188–212]. -/
theorem sum_graph_singleton_exponentialDistanceProfile_le (Λ : Finset (ℤ × ℤ))
    {K c α : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hα : 0 < α)
    (hball : ∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) (s : ℤ × ℤ) :
    (∑ z ∈ Λ, domainDistanceProfile Λ {s} c α z) ≤
      K * ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α) := by
  have hsingle (z : ℤ × ℤ) :
      (⨅ t ∈ ({s} : Finset (ℤ × ℤ)), domainEDist Λ z t) = domainEDist Λ z s := by
    simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  have hprofile (z : ℤ × ℤ) : domainDistanceProfile Λ {s} c α z =
      if domainEDist Λ z s ≠ ⊤ then Real.exp (-c * ((domainEDist Λ z s).toNat : ℝ) ^ α)
      else 0 := by
    unfold domainDistanceProfile
    rw [hsingle]
    by_cases h : domainEDist Λ z s = ⊤ <;> simp [h]
  let T := Λ.filter fun z => domainEDist Λ z s ≠ ⊤
  let D := T.image fun z => (domainEDist Λ z s).toNat
  have hfiber (n : ℕ) : ((T.filter fun z => (domainEDist Λ z s).toNat = n).card : ℝ) ≤
      K * ((n : ℝ) + 1) ^ 2 := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hball s n)
    intro z hz
    obtain ⟨hzT, hzn⟩ := Finset.mem_filter.mp hz
    have hne := (Finset.mem_filter.mp hzT).2
    rw [mem_graphNbhd_singleton_iff_domainEDist_le, domainEDist_comm, ← ENat.natCast_toNat hne, hzn]
  calc
    _ = ∑ z ∈ T, Real.exp (-c * ((domainEDist Λ z s).toNat : ℝ) ^ α) := by
      simp only [hprofile, T, Finset.sum_filter]
    _ = ∑ n ∈ D, ((T.filter fun z => (domainEDist Λ z s).toNat = n).card : ℝ) *
        Real.exp (-c * (n : ℝ) ^ α) := by
      have h := Finset.sum_fiberwise_of_maps_to' (s := T) (t := D)
        (g := fun z => (domainEDist Λ z s).toNat)
        (fun z hz => Finset.mem_image_of_mem _ hz)
        (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ α))
      simpa only [Finset.sum_const, nsmul_eq_mul] using h.symm
    _ ≤ ∑ n ∈ D, (K * ((n : ℝ) + 1) ^ 2) * Real.exp (-c * (n : ℝ) ^ α) :=
      Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hfiber n) (Real.exp_pos _).le
    _ = K * ∑ n ∈ D, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Real.summable_nat_pow_mul_exp_neg_mul_rpow 2 hc hα).sum_le_tsum D
        (fun _ _ => by positivity)) hK

/-- The total profile mass is at most the single-site mass times `|S|`
[OAI265, §10.1, `09-amplification.tex`, lines 188–212]. -/
theorem sum_graph_exponentialDistanceProfile_le (Λ : Finset (ℤ × ℤ))
    {K c α : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hα : 0 < α)
    (hball : ∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (S : Finset (ℤ × ℤ)) :
    (∑ z ∈ Λ, domainDistanceProfile Λ S c α z) ≤
      (S.card : ℝ) * K * ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α) := by
  calc
    _ ≤ ∑ z ∈ Λ, ∑ s ∈ S, domainDistanceProfile Λ {s} c α z :=
      Finset.sum_le_sum fun z _ => profile_finset_le_sum_singleton Λ S c α z
    _ = ∑ s ∈ S, ∑ z ∈ Λ, domainDistanceProfile Λ {s} c α z := Finset.sum_comm
    _ ≤ ∑ _s ∈ S, K * ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α) :=
      Finset.sum_le_sum fun s _ =>
        sum_graph_singleton_exponentialDistanceProfile_le Λ hK hc hα hball s
    _ = _ := by simp [mul_assoc]

/-- A shell meeting a profile based beyond radius `r` spends half its decay rate on `r`,
leaving both half-rate factors for the summation; at infinite distance from `S` both sides
vanish [OAI265, §10.1, `09-amplification.tex`, lines 188–212]. -/
theorem exp_mul_graph_exponentialDistanceProfile_le_of_anchor_far (Λ S : Finset (ℤ × ℤ))
    {b β α r : ℝ} (hb : 0 < b) (hβ : 0 < β) (hα : 0 < α) (hα₁ : α ≤ 1) (hr : 0 ≤ r)
    {x z : ℤ × ℤ} {l : ℕ} (hz : z ∈ graphNbhd Λ {x} l)
    (hfar : ∀ s ∈ S, ENNReal.ofReal r < (domainEDist Λ x s : ℝ≥0∞)) :
    Real.exp (-b * (l : ℝ) ^ α) * domainDistanceProfile Λ S β α z ≤
      Real.exp (-((min b β) / 2) * r ^ α) *
        (Real.exp (-(b / 2) * (l : ℝ) ^ α) * domainDistanceProfile Λ S (β / 2) α z) := by
  by_cases htop : (⨅ s ∈ S, domainEDist Λ z s) = ⊤
  · rw [(domainDistanceProfile_eq_zero_iff Λ S β α z).2 htop,
      (domainDistanceProfile_eq_zero_iff Λ S (β / 2) α z).2 htop]
    simp
  have hS : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact absurd (by simp) htop
    · exact hS
  obtain ⟨s₀, hs₀, heq⟩ := exists_mem_domainEDist_eq_iInf (Λ := Λ) hS z
  obtain ⟨dN, hdN⟩ := ENat.ne_top_iff_exists.mp htop
  have hxz : domainEDist Λ x z ≤ l := mem_graphNbhd_singleton_iff_domainEDist_le.mp hz
  have htri : domainEDist Λ x s₀ ≤ ((l + dN : ℕ) : ℕ∞) :=
    calc
      domainEDist Λ x s₀ ≤ domainEDist Λ x z + domainEDist Λ z s₀ :=
        domainEDist_triangle Λ x z s₀
      _ ≤ (l : ℕ∞) + dN := add_le_add hxz (by rw [heq, ← hdN])
      _ = ((l + dN : ℕ) : ℕ∞) := by push_cast; rfl
  obtain ⟨mN, hmN⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) htri)
  have hmle : mN ≤ l + dN := by
    rw [← hmN] at htri
    exact_mod_cast htri
  have hrm : r < mN := by
    have h := hfar s₀ hs₀
    rw [← hmN, ENNReal.ofReal_lt_iff_lt_toReal hr (by simp)] at h
    simpa using h
  have hrl : r ≤ (l : ℝ) + dN := by
    have : (mN : ℝ) ≤ l + dN := by exact_mod_cast hmle
    linarith
  have hpow : r ^ α ≤ (l : ℝ) ^ α + (dN : ℝ) ^ α :=
    (Real.rpow_le_rpow hr hrl hα.le).trans
      (Real.rpow_add_le_add_rpow (by positivity) (by positivity) hα.le hα₁)
  have hrate : (min b β) / 2 * r ^ α ≤ b / 2 * (l : ℝ) ^ α + β / 2 * (dN : ℝ) ^ α := by
    calc
      _ ≤ (min b β) / 2 * ((l : ℝ) ^ α + (dN : ℝ) ^ α) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := by
        rw [mul_add]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (min_le_left b β) (by norm_num)) (by positivity)
        · exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (min_le_right b β) (by norm_num)) (by positivity)
  have hprof (γ' : ℝ) : domainDistanceProfile Λ S γ' α z = Real.exp (-γ' * (dN : ℝ) ^ α) := by
    rw [domainDistanceProfile_of_ne_top Λ S γ' α htop, ← hdN, ENat.toNat_natCast]
  rw [hprof, hprof, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Bounded anchor fibers reduce the incidence sum of a nonnegative site function to its total
mass times the quadratic ball bound [OAI265, §10.1, `09-amplification.tex`, lines 188–212]. -/
theorem sum_graphBall_site_function_le (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ) {K μ : ℝ}
    (hμ : 0 ≤ μ) (hball : ∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (f : ℤ × ℤ → ℝ) (hf : ∀ z, 0 ≤ f z) (l : ℕ) :
    (∑ i, ∑ z ∈ graphNbhd Λ {a i} l, f z) ≤ μ * K * ((l : ℝ) + 1) ^ 2 * ∑ z ∈ Λ, f z := by
  have hcount (z : ℤ × ℤ) :
      ((Finset.univ.filter fun i : κ => z ∈ graphNbhd Λ {a i} l).card : ℝ) ≤
        μ * K * ((l : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ μ * (graphNbhd Λ {z} l).card := card_graphBall_anchors_le Λ a hfiber z l
      _ ≤ μ * (K * ((l : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left (hball z l) hμ
      _ = _ := by ring
  calc
    _ = ∑ z ∈ Λ, ((Finset.univ.filter fun i : κ =>
        z ∈ graphNbhd Λ {a i} l).card : ℝ) * f z := by
      calc
        _ = ∑ i, ∑ z ∈ Λ, if z ∈ graphNbhd Λ {a i} l then f z else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (graphNbhd_subset Λ {a i} l)]
        _ = ∑ z ∈ Λ, ∑ i, if z ∈ graphNbhd Λ {a i} l then f z else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.natCast_card_filter, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
    _ ≤ ∑ z ∈ Λ, (μ * K * ((l : ℝ) + 1) ^ 2) * f z :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hcount z) (hf z)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The unrestricted finite anchor-shell sum is bounded by the product of two summable second
moments, independently of the volume and the cutoff
[OAI265, §10.1, `09-amplification.tex`, lines 188–212]. -/
theorem sum_graphBall_exponentialDistanceProfile_le (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    {K μ b β α : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hβ : 0 < β) (hα : 0 < α)
    (hball : ∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (S : Finset (ℤ × ℤ)) (N : ℕ) :
    (∑ i, ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
      ∑ z ∈ graphNbhd Λ {a i} l, domainDistanceProfile Λ S β α z) ≤
      μ * K ^ 2 *
        (∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-b * (n : ℝ) ^ α)) *
        (∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-β * (n : ℝ) ^ α)) * S.card := by
  let M (c : ℝ) := ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α)
  have hM (c : ℝ) : 0 ≤ M c := tsum_nonneg fun _ => by positivity
  have hsite := sum_graph_exponentialDistanceProfile_le Λ hK hβ hα hball S
  have hshell (l : ℕ) :
      (∑ i, ∑ z ∈ graphNbhd Λ {a i} l, domainDistanceProfile Λ S β α z) ≤
        μ * K ^ 2 * M β * S.card * (1 + (l : ℝ)) ^ 2 := by
    calc
      _ ≤ μ * K * ((l : ℝ) + 1) ^ 2 * ∑ z ∈ Λ, domainDistanceProfile Λ S β α z :=
        sum_graphBall_site_function_le Λ a hμ hball hfiber _
          (domainDistanceProfile_nonneg _ _ _ _) l
      _ ≤ μ * K * ((l : ℝ) + 1) ^ 2 * ((S.card : ℝ) * K * M β) :=
        mul_le_mul_of_nonneg_left hsite (by positivity)
      _ = _ := by ring
  calc
    _ = ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
        ∑ i, ∑ z ∈ graphNbhd Λ {a i} l, domainDistanceProfile Λ S β α z := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
        (μ * K ^ 2 * M β * S.card * (1 + (l : ℝ)) ^ 2) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hshell l) (Real.exp_pos _).le
    _ = (μ * K ^ 2 * M β * S.card) * ∑ l ∈ Finset.range (N + 1),
        (1 + (l : ℝ)) ^ 2 * Real.exp (-b * (l : ℝ) ^ α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ (μ * K ^ 2 * M β * S.card) * M b :=
      mul_le_mul_of_nonneg_left
        ((Real.summable_nat_pow_mul_exp_neg_mul_rpow 2 hb hα).sum_le_tsum _
          (fun _ _ => by positivity)) (by positivity)
    _ = _ := by dsimp [M]; ring

/-- **Omitted-anchor tail.**  The shell weights of the anchors farther than `r` from `S` have a
uniform stretched-exponential tail with exponent `γ = min b β / 2`.  The constants depend only on
`K, μ, b, β, α` and precede the label type, the domain, the anchors, the omitted labels, the
target, the cutoff and the radius; empty sets and disconnected domains need no hypotheses
[OAI265, §10.1, `09-amplification.tex`, lines 188–215]. -/
theorem exists_sum_omitted_graphBall_exponentialDistanceProfile_le {K μ b β α : ℝ}
    (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hβ : 0 < β) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ γ = (min b β) / 2 ∧
      ∀ (κ : Type*) [Fintype κ] (Λ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ),
        (∀ x l, ((graphNbhd Λ {x} l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        ∀ (E : Finset κ) (S : Finset (ℤ × ℤ)) (N : ℕ) (r : ℝ), 0 ≤ r →
          (∀ i ∈ E, ∀ s ∈ S, ENNReal.ofReal r < (domainEDist Λ (a i) s : ℝ≥0∞)) →
          (∑ i ∈ E, ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
            ∑ z ∈ graphNbhd Λ {a i} l, domainDistanceProfile Λ S β α z) ≤
            C * S.card * Real.exp (-γ * r ^ α) := by
  let M (c : ℝ) := ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α)
  have hM (c : ℝ) : 0 ≤ M c := tsum_nonneg fun _ => by positivity
  refine ⟨μ * K ^ 2 * M (b / 2) * M (β / 2), (min b β) / 2,
    by positivity, by positivity, rfl, ?_⟩
  intro κ _ Λ a hball hfiber E S N r hr hfar
  let F (c d : ℝ) (i : κ) := ∑ l ∈ Finset.range (N + 1),
    Real.exp (-c * (l : ℝ) ^ α) *
      ∑ z ∈ graphNbhd Λ {a i} l, domainDistanceProfile Λ S d α z
  have hF (c d : ℝ) (i : κ) : 0 ≤ F c d i := by
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun z _ =>
      domainDistanceProfile_nonneg _ _ _ _ _)
  have hterm (i : κ) (hi : i ∈ E) : F b β i ≤
      Real.exp (-((min b β) / 2) * r ^ α) * F (b / 2) (β / 2) i := by
    dsimp [F]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun z hz =>
      exp_mul_graph_exponentialDistanceProfile_le_of_anchor_far Λ S
        hb hβ hα hα₁ hr hz (hfar i hi)
  have hfull := sum_graphBall_exponentialDistanceProfile_le Λ a hK hμ
    (half_pos hb) (half_pos hβ) hα hball hfiber S N
  calc
    _ = ∑ i ∈ E, F b β i := rfl
    _ ≤ ∑ i ∈ E, Real.exp (-((min b β) / 2) * r ^ α) * F (b / 2) (β / 2) i :=
      Finset.sum_le_sum hterm
    _ = Real.exp (-((min b β) / 2) * r ^ α) * ∑ i ∈ E, F (b / 2) (β / 2) i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-((min b β) / 2) * r ^ α) * ∑ i, F (b / 2) (β / 2) i :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
          (fun i _ _ => hF _ _ i)) (Real.exp_pos _).le
    _ ≤ Real.exp (-((min b β) / 2) * r ^ α) *
        (μ * K ^ 2 * M (b / 2) * M (β / 2) * S.card) :=
      mul_le_mul_of_nonneg_left hfull (Real.exp_pos _).le
    _ = _ := by ring

end OpenAI
