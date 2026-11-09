import AreaLawForMathlib.QuantumInfo.Region.Physlib

/-!
# Subadditivity, Araki–Lieb and mutual information of region entropies

Extends Physlib's `QuantumInfo/Entropy/SSA.lean` (`Sᵥₙ_subadditivity`, `Sᵥₙ_triangle_subaddivity`)
to regions: `S(X ∪ Y) ≤ S(X) + S(Y)` for disjoint `X, Y`, its finite-family form
`S(D ∪ ⋃_{i ∈ s} X_i) ≤ S(D) + ∑_{i ∈ s} S(X_i)`, and `|S(X) - S(Y)| ≤ S(X ∪ Y)`.
-/
namespace Arealaw

open scoped ComplexOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U X Y : Finset σ}

/-- The restriction of `ρ` to `X ∪ Y`, transported across the bridge to `Reg X × Reg Y`.
Disjointness is what makes the transport exist. -/
noncomputable def unionState (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : _root_.MState (Reg loc X × Reg loc Y) :=
  MState.physlibEquiv
    ((ρ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm)

/-- The entropy of the transported state is the region entropy of `X ∪ Y`. -/
theorem Sᵥₙ_unionState (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) :
    Sᵥₙ (unionState ρ hd hX hY) = ρ.toSubState.regionEntropy (Finset.union_subset hX hY) := by
  simp [unionState, MState.Sᵥₙ_physlibEquiv, SubState.regionEntropy_def]

/-- Tracing out the right factor gives the region entropy of `X`. -/
theorem Sᵥₙ_traceRight_unionState (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    Sᵥₙ (unionState ρ hd hX hY).traceRight = ρ.toSubState.regionEntropy hX := by
  rw [unionState, traceRight_physlibEquiv_submatrix, MState.Sᵥₙ_physlibEquiv,
    SubState.regionEntropy_def, ← MState.toSubState_restrict, MState.restrict_restrict]

/-- Tracing out the left factor gives the region entropy of `Y`. -/
theorem Sᵥₙ_traceLeft_unionState (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    Sᵥₙ (unionState ρ hd hX hY).traceLeft = ρ.toSubState.regionEntropy hY := by
  rw [unionState, traceLeft_physlibEquiv_submatrix, MState.Sᵥₙ_physlibEquiv,
    SubState.regionEntropy_def, ← MState.toSubState_restrict, MState.restrict_restrict]

/-- **Subadditivity on regions**: `S(X ∪ Y) ≤ S(X) + S(Y)` for disjoint `X`, `Y`. -/
theorem regionEntropy_union_le (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : ρ.toSubState.regionEntropy (Finset.union_subset hX hY)
      ≤ ρ.toSubState.regionEntropy hX + ρ.toSubState.regionEntropy hY := by
  simpa [Sᵥₙ_unionState, Sᵥₙ_traceRight_unionState, Sᵥₙ_traceLeft_unionState] using
    Sᵥₙ_subadditivity (unionState ρ hd hX hY)

/-- Mutual information of disjoint regions is nonnegative. -/
theorem mutualInfo_nonneg (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : 0 ≤ ρ.toSubState.mutualInfo hX hY :=
  sub_nonneg.2 (regionEntropy_union_le ρ hd hX hY)

/-- **Araki–Lieb on regions**: two disjoint regions' entropies differ by at most the entropy
of their union. -/
theorem abs_regionEntropy_sub_regionEntropy_le (ρ : Arealaw.MState (Reg loc U) ℂ)
    (hd : Disjoint X Y) (hX : X ⊆ U) (hY : Y ⊆ U) :
    |ρ.toSubState.regionEntropy hX - ρ.toSubState.regionEntropy hY|
      ≤ ρ.toSubState.regionEntropy (Finset.union_subset hX hY) := by
  simpa [Sᵥₙ_unionState, Sᵥₙ_traceRight_unionState, Sᵥₙ_traceLeft_unionState] using
    Sᵥₙ_triangle_subaddivity (unionState ρ hd hX hY)

end Arealaw

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
