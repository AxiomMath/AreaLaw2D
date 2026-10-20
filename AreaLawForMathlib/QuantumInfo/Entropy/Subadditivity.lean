import Arealaw.Subadditivity

/-!
# Subadditivity of region entropy over a finite family

Extends `Arealaw/Subadditivity.lean` (`Arealaw.regionEntropy_union_le`, two regions) to a finite
family of pairwise disjoint regions: `S(D ∪ ⋃_{i ∈ s} X_i) ≤ S(D) + ∑_{i ∈ s} S(X_i)`.
-/

namespace Arealaw

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ}

/-- **Subadditivity over a finite family**: `S(D ∪ ⋃_{i ∈ s} X_i) ≤ S(D) + ∑_{i ∈ s} S(X_i)`
for pairwise disjoint regions `X_i`, each disjoint from `D`. -/
theorem regionEntropy_union_biUnion_le {ι : Type*} (ρ : MState (Reg loc U) ℂ) {D : Finset σ}
    (hD : D ⊆ U) (s : Finset ι) {X : ι → Finset σ} (hX : ∀ i, X i ⊆ U)
    (hDX : ∀ i ∈ s, Disjoint D (X i)) (hXX : (s : Set ι).PairwiseDisjoint X) :
    ρ.toSubState.regionEntropy (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i) :
        D ∪ s.biUnion X ⊆ U) ≤
      ρ.toSubState.regionEntropy hD + ∑ i ∈ s, ρ.toSubState.regionEntropy (hX i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (ρ.toSubState.regionEntropy_congr (by simp) _ hD).le.trans (by simp)
  | insert a s has ih =>
    have hd : Disjoint (D ∪ s.biUnion X) (X a) :=
      Finset.disjoint_union_left.2 ⟨hDX a (Finset.mem_insert_self a s),
        (Finset.disjoint_biUnion_left _ _ _).2 fun i hi => hXX (by simp [hi]) (by simp)
          fun h => has (h ▸ hi)⟩
    rw [Finset.sum_insert has, ρ.toSubState.regionEntropy_congr
      (show D ∪ (insert a s).biUnion X = (D ∪ s.biUnion X) ∪ X a by
        rw [Finset.biUnion_insert]; ac_rfl) _
      (Finset.union_subset (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i))
        (hX a))]
    linarith [regionEntropy_union_le ρ hd
      (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i)) (hX a),
      ih (fun i hi => hDX i (Finset.mem_insert_of_mem hi))
        (hXX.subset (by simp [Set.subset_insert]))]

end Arealaw
