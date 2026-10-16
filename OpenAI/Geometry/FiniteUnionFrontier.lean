import Mathlib.Topology.Closure

/-!
# Frontiers of finite unions

Compatibility lemmas for the Mathlib version used by this project.  The same
statements are available as methods on finite sets in newer Mathlib versions.
-/

namespace OpenAI.Geometry

/-- The frontier of a union indexed by a finite set is contained in the union
of the individual frontiers. -/
theorem frontier_finiteSet_biUnion_subset {ι X : Type*} [TopologicalSpace X]
    (s : Set ι) (hs : s.Finite) (f : ι → Set X) :
    frontier (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ s, frontier (f i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha hs ih =>
      intro x hx
      have hx' : x ∈ frontier (f a ∪ ⋃ i ∈ s, f i) := by
        rw [← Set.biUnion_insert]
        exact hx
      rcases frontier_union_subset (f a) (⋃ i ∈ s, f i) hx' with hx | hx
      · exact Set.mem_iUnion₂.mpr ⟨a, Set.mem_insert a s, hx.1⟩
      · rcases Set.mem_iUnion₂.mp (ih hx.2) with ⟨i, hi, hxi⟩
        exact Set.mem_iUnion₂.mpr ⟨i, Set.mem_insert_of_mem a hi, hxi⟩

/-- Finset-indexed form of `frontier_finiteSet_biUnion_subset`. -/
theorem frontier_finset_biUnion_subset {ι X : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → Set X) :
    frontier (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ s, frontier (f i) :=
  frontier_finiteSet_biUnion_subset (s : Set ι) s.finite_toSet f

end OpenAI.Geometry
