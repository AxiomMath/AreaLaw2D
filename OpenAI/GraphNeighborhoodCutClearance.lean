/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/GraphNeighborhoodCutClearance.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adapted to this project's domain
encoding: TNLean's regions `A J : Finset (Site Λ)` are finite sets `A J : Finset (ℤ × ℤ)`,
`A.filter (· ∈ ambientDilation T L)` is `A ∩ ambientDilation T L`,
`graphNeighborhood Λ R S` is `OpenAI.graphNbhd Λ S R`, `Geometry.boundaryEndpoints Λ A` is
`OpenAI.cutEndpoints Λ A`, and the complement `Aᶜ` in `Site Λ` is `Λ \ A`.  No hypothesis
`A ⊆ Λ` is needed; `exterior_union_subset_graphNeighborhood_compl_of_clearance` takes
`J ⊆ Λ`, which TNLean's `J : Finset (Site Λ)` carries.  Added
`graphNeighborhood_subset_of_lt_ambientEDist` and
`exterior_union_subset_graphNeighborhood_compl_of_lt_ambientEDist`, the same implications from
the set clearance `OpenAI.ambientEDist`, through
`natCast_lt_ambientSupDistance_of_lt_ambientEDist`.
-/
import OpenAI.Scan.AmbientDepth

/-!
# Graph neighborhoods separated from physical cuts

A graph neighborhood of the part of an ambient target collar inside a cut stays inside the cut
and the enlarged collar whenever every cut endpoint is farther from the target than the sum of
the two radii.  The estimate applies to arbitrary finite induced domains, including holes and
disconnected parts: a walk of length at most `R` from `A ∩ T_L` that leaves `A` crosses the
cut at an endpoint of ambient depth at most `L + R`, and ambient depth changes by at most one
along each step of a walk.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, `10-geometry.tex`,
lines 815–838, at revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI

open SimpleGraph

/-- A graph neighborhood of the part of an ambient target collar inside a cut remains inside
that cut and inside the enlarged ambient collar, provided every physical cut endpoint is farther
from the target than the two radii together.  No connectedness, convexity or
target-nonemptiness assumption is required.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, `10-geometry.tex`,
lines 815–838. -/
theorem graphNeighborhood_subset_of_cut_clearance
    (Λ T A : Finset (ℤ × ℤ)) (L R : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
      ((L + R : ℕ) : ℤ) < Scan.ambientSupDistance t z) :
    graphNbhd Λ (A ∩ ambientDilation T L) R ⊆ A ∩ ambientDilation T (L + R) := by
  classical
  intro x hx
  obtain ⟨hxΛ, y, hy, hyΛ, p, hp⟩ := mem_graphNbhd_iff_walk.mp hx
  rcases Finset.mem_inter.mp hy with ⟨hyA, hyDil⟩
  have hT : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := mem_ambientDilation.mp hyDil
    exact ⟨t, ht⟩
  have hydepth := (Scan.ambientDepth_le_iff_mem_dilation T hT y L).mpr hyDil
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · by_contra hxA
    obtain ⟨u, w, hcut, p', hp'⟩ := exists_edgeBoundary_of_walk p hyA hxA
    have hz : (u : ℤ × ℤ) ∈ cutEndpoints Λ A :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hcut)
    have hvariation := (Scan.abs_ambientDepth_sub_le_walk_length T hT Subtype.val
      (fun _ _ ↦ Scan.ambientSupDistance_le_one_of_domainGraph_adj) p').trans
        (Int.ofNat_le.mpr (hp'.trans hp))
    obtain ⟨t, ht, hmin⟩ := T.exists_mem_eq_inf' hT (Scan.ambientSupDistance u.val)
    have hdeep : ((L + R : ℕ) : ℤ) < Scan.ambientDepth T hT u.val := by
      simpa only [Scan.ambientDepth, hmin, Scan.ambientSupDistance, abs_sub_comm]
        using hclear t ht u.val hz
    rw [abs_le] at hvariation
    push_cast at hdeep
    simp only at hvariation
    omega
  · apply (Scan.ambientDepth_le_iff_mem_dilation T hT x (L + R)).mp
    have hvariation := (Scan.abs_ambientDepth_sub_le_walk_length T hT Subtype.val
      (fun _ _ ↦ Scan.ambientSupDistance_le_one_of_domainGraph_adj) p).trans
        (Int.ofNat_le.mpr hp)
    rw [abs_le] at hvariation
    simp only at hvariation
    push_cast
    omega

/-- A sup-norm clearance `dist_∞(T, Z) > k` between finite sets bounds the sup-norm distance
of every pair of points. -/
theorem natCast_lt_ambientSupDistance_of_lt_ambientEDist {T Z : Finset (ℤ × ℤ)} {k : ℕ}
    (hclear : (k : ENNReal) < ambientEDist T Z) :
    ∀ t ∈ T, ∀ z ∈ Z, (k : ℤ) < Scan.ambientSupDistance t z := by
  intro t ht z hz
  have h := (lt_ambientEDist_iff (ENNReal.natCast_lt_top _)).mp hclear t ht z hz
  rw [edist_dist, ← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff'] at h
  have h' : (((k : ℕ) : ℤ) : ℝ) < (Scan.ambientSupDistance t z : ℝ) := by
    rw [Scan.ambientSupDistance_eq_dist]
    exact_mod_cast h.1
  exact_mod_cast h'

/-- `graphNeighborhood_subset_of_cut_clearance` with the clearance stated as the ambient
distance `dist_∞(T, Z_A) > L + R` between the target and the cut endpoints. -/
theorem graphNeighborhood_subset_of_lt_ambientEDist
    (Λ T A : Finset (ℤ × ℤ)) (L R : ℕ)
    (hclear : ((L + R : ℕ) : ENNReal) < ambientEDist T (cutEndpoints Λ A)) :
    graphNbhd Λ (A ∩ ambientDilation T L) R ⊆ A ∩ ambientDilation T (L + R) :=
  graphNeighborhood_subset_of_cut_clearance Λ T A L R
    (natCast_lt_ambientSupDistance_of_lt_ambientEDist hclear)

/-- Clearance from physical cut endpoints and from an entire remote set excludes both the
exterior and that remote set from the graph neighborhood of the target collar inside the region.
In the area-law application, the remote set is the whole union of the earlier actual regions of
the same geometric family.

Source: OpenAI, proof of Theorem 1.1, `10-geometry.tex`, lines 825–838. -/
theorem exterior_union_subset_graphNeighborhood_compl_of_clearance
    (Λ T A J : Finset (ℤ × ℤ)) (L R : ℕ) (hJ : J ⊆ Λ)
    (hcut : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
      ((L + R : ℕ) : ℤ) < Scan.ambientSupDistance t z)
    (hremote : ∀ t ∈ T, ∀ x ∈ J, ((L + R : ℕ) : ℤ) < Scan.ambientSupDistance t x) :
    (Λ \ A) ∪ J ⊆ Λ \ graphNbhd Λ (A ∩ ambientDilation T L) R := by
  have hN := graphNeighborhood_subset_of_cut_clearance Λ T A L R hcut
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨?_, fun hxN ↦ ?_⟩
  · rcases Finset.mem_union.mp hx with h | h
    exacts [(Finset.mem_sdiff.mp h).1, hJ h]
  · obtain ⟨hxA, hxD⟩ := Finset.mem_inter.mp (hN hxN)
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.mem_sdiff.mp h).2 hxA
    · obtain ⟨t, ht, h1, h2⟩ := mem_ambientDilation.mp hxD
      have := hremote t ht x h
      simp only [Scan.ambientSupDistance, lt_max_iff] at this
      rw [abs_sub_comm x.1, abs_sub_comm x.2] at *
      push_cast at this h1 h2
      omega

/-- `exterior_union_subset_graphNeighborhood_compl_of_clearance` with both clearances stated
as ambient distances, `dist_∞(T, Z_A) > L + R` and `dist_∞(T, J) > L + R`. -/
theorem exterior_union_subset_graphNeighborhood_compl_of_lt_ambientEDist
    (Λ T A J : Finset (ℤ × ℤ)) (L R : ℕ) (hJ : J ⊆ Λ)
    (hcut : ((L + R : ℕ) : ENNReal) < ambientEDist T (cutEndpoints Λ A))
    (hremote : ((L + R : ℕ) : ENNReal) < ambientEDist T J) :
    (Λ \ A) ∪ J ⊆ Λ \ graphNbhd Λ (A ∩ ambientDilation T L) R :=
  exterior_union_subset_graphNeighborhood_compl_of_clearance Λ T A J L R hJ
    (natCast_lt_ambientSupDistance_of_lt_ambientEDist hcut)
    (natCast_lt_ambientSupDistance_of_lt_ambientEDist hremote)

end OpenAI
