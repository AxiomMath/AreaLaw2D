/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Geometry.DyadicExhaustion
import OpenAI.Geometry.DyadicRefinement
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic

/-!
# The half-open dyadic layer partition

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/LayerPartition.lean` (Apache 2.0).
-/

namespace OpenAI.Geometry

/-- An indexed fine cell is contained in its layer. -/
theorem dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
    (o : ℝ × ℝ) (k ℓ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (hℓk : ℓ ≤ k) (hz : z ∈ fineLayerIndices o k ℓ Z C) :
    dyadicCell o ℓ z ⊆ dyadicLayer o k Z C := by
  intro x hx
  rw [dyadicLayer_eq_iUnion_fine o k ℓ Z C hℓk]
  exact Set.mem_iUnion₂.mpr ⟨z, hz, hx⟩

private theorem neighborhood_mono (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    Monotone (fun k ↦ dyadicNeighborhood o k Z C) :=
  monotone_nat_of_le_succ (fun k ↦ dyadicNeighborhood_subset_succ o k Z C)

/-- Actual half-open layers are pairwise disjoint. -/
theorem dyadicLayer_pairwiseDisjoint (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    Pairwise (fun k h : ℕ ↦ Disjoint (dyadicLayer o k Z C) (dyadicLayer o h Z C)) := by
  have hdisj (k h : ℕ) (hkh : k < h) :
      Disjoint (dyadicLayer o k Z C) (dyadicLayer o h Z C) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    exact hy.2 (neighborhood_mono o Z C (Nat.succ_le_of_lt hkh) hx.1)
  intro k h hne
  rcases lt_or_gt_of_ne hne with hkh | hhk
  · exact hdisj k h hkh
  · exact (hdisj h k hhk).symm

/-- The initial dummy neighborhood is disjoint from every later layer. -/
theorem dyadicNeighborhood_disjoint_later_layer (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ k : ℕ) (hk : k₀ ≤ k) :
    Disjoint (dyadicNeighborhood o k₀ Z C) (dyadicLayer o k Z C) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  exact hy.2 (neighborhood_mono o Z C hk hx)

/-- Outside the initial dummy neighborhood there is a unique later layer. -/
theorem exists_unique_layer_of_not_mem_dyadicNeighborhood (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C)
    (x : ℝ × ℝ) (hx : x ∉ dyadicNeighborhood o k₀ Z C) :
    ∃! k : ℕ, k₀ ≤ k ∧ x ∈ dyadicLayer o k Z C := by
  classical
  have hex := exists_mem_dyadicNeighborhood o Z C hZ hC x
  let K := Nat.find hex
  have hxK : x ∈ dyadicNeighborhood o K Z C := Nat.find_spec hex
  have hk₀K : k₀ < K := by
    by_contra! h
    exact hx (neighborhood_mono o Z C h hxK)
  have hprev : x ∉ dyadicNeighborhood o (K - 1) Z C :=
    Nat.find_min hex (by dsimp [K] at hk₀K ⊢; omega)
  have hmem : x ∈ dyadicLayer o (K - 1) Z C := by
    change x ∈ dyadicNeighborhood o (K - 1 + 1) Z C ∧
      x ∉ dyadicNeighborhood o (K - 1) Z C
    have hK : K - 1 + 1 = K := by omega
    exact ⟨hK ▸ hxK, hprev⟩
  refine ⟨K - 1, ⟨by omega, hmem⟩, ?_⟩
  intro k hk
  by_contra hne
  exact (Set.disjoint_left.mp (dyadicLayer_pairwiseDisjoint o Z C hne)) hk.2 hmem

/-- The dummy neighborhood and all later layers cover the plane. -/
theorem dyadicNeighborhood_union_iUnion_layers_eq_univ (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) :
    dyadicNeighborhood o k₀ Z C ∪ (⋃ k ≥ k₀, dyadicLayer o k Z C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ dyadicNeighborhood o k₀ Z C
  · exact Set.mem_union_left _ hx
  · obtain ⟨k, hk, _⟩ :=
      exists_unique_layer_of_not_mem_dyadicNeighborhood o Z C k₀ hZ hC x hx
    exact Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨k, hk.1, hk.2⟩)

end OpenAI.Geometry
