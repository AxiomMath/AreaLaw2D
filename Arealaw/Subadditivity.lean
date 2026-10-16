import Arealaw.Bridge.VonNeumann

/-!
# Subadditivity of the von Neumann entropy, on regions

Subadditivity and the Araki–Lieb triangle inequality in the region language, which is how
every statement of Brandão–Horodecki §III is written.  Each is one upstream result plus the
three `Sᵥₙ_*_unionState` rewrites.

Normalized states only; the subnormalized version needs a multiset argument.
`Disjoint X Y` lives on these theorems rather than on `mutualInfo`, whose definition stays
total.  Pinned to `ℂ`, inherited from `Arealaw.Bridge.VonNeumann`.
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

/-- **Subadditivity on regions, in base 2**: `S₂(X ∪ Y) ≤ S₂(X) + S₂(Y)` for disjoint `X`,
`Y`. -/
theorem regionEntropy₂_union_le (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : ρ.toSubState.regionEntropy₂ (Finset.union_subset hX hY)
      ≤ ρ.toSubState.regionEntropy₂ hX + ρ.toSubState.regionEntropy₂ hY :=
  (div_le_div_of_nonneg_right (regionEntropy_union_le ρ hd hX hY) (by positivity)).trans_eq
    (add_div ..)

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

/-- **The paper's Step-1 bound**, `I(X:Y) ≤ 2 H(Y)`.  Base-independent, so this nats
statement transcribes the paper's base-2 one faithfully. -/
theorem mutualInfo_le_two_mul_regionEntropy (ρ : Arealaw.MState (Reg loc U) ℂ) (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.toSubState.mutualInfo hX hY ≤ 2 * ρ.toSubState.regionEntropy hY := by
  rw [SubState.mutualInfo_def]
  linarith [(abs_sub_le_iff.mp (abs_regionEntropy_sub_regionEntropy_le ρ hd hX hY)).1]

end Arealaw
