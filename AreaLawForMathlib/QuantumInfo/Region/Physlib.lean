import AreaLawForMathlib.QuantumInfo.Region.State
import AreaLawForMathlib.QuantumInfo.Region.TraceDistance
import QuantumInfo.States.Mixed.Fidelity
import QuantumInfo.States.Mixed.MState
import QuantumInfo.States.Mixed.TraceDistance
import QuantumInfo.Entropy.SSA

/-!
# States on regions as Physlib states

Extends Physlib's `QuantumInfo/States/Mixed/MState.lean` and `QuantumInfo/Entropy/SSA.lean`:
normalized states over `ℂ` are Physlib's `MState` (`MState.physlibEquiv`), with the same entropy
(`Sᵥₙ`), trace distance (`TrDistance`) and, on a disjoint union of regions, the same partial
traces (`traceRight`, `traceLeft`).
-/
namespace Arealaw

open scoped ComplexOrder MatrixOrder

namespace MState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The equivalence between our normalized states over `ℂ` and Physlib's `MState`.  The
`DecidableEq ι` is Physlib's requirement; every region use site has it. -/
noncomputable def physlibEquiv : Arealaw.MState ι ℂ ≃ _root_.MState ι where
  toFun ρ := ⟨⟨ρ.M, ρ.psd.isHermitian⟩, HermitianMat.zero_le_iff.mpr ρ.psd, ρ.tr_eq_one⟩
  invFun Q := .mk' (HermitianMat.zero_le_iff.mp Q.nonneg) Q.tr
  left_inv _ := rfl
  right_inv _ := rfl

/-- The density matrix of a transported state. -/
@[simp] theorem physlibEquiv_m (ρ : Arealaw.MState ι ℂ) : (physlibEquiv ρ).m = ρ.M := rfl

/-- The density matrix of a state transported back. -/
@[simp] theorem physlibEquiv_symm_M (Q : _root_.MState ι) : (physlibEquiv.symm Q).M = Q.m := rfl

section Reindex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The bridge intertwines `submatrix` with Physlib's `relabel`. -/
theorem physlibEquiv_submatrix (ρ : Arealaw.MState ι ℂ) (e : m ≃ ι) :
    physlibEquiv (ρ.submatrix e) = (physlibEquiv ρ).relabel e := rfl

end Reindex

/-- The bridge intertwines the trace distances: Physlib's `TrDistance` is `D₁` on normalized
states. -/
theorem trDistance_physlibEquiv (ρ σ : Arealaw.MState ι ℂ) :
    _root_.TrDistance (physlibEquiv ρ) (physlibEquiv σ) = ρ.toSubState.D₁ σ.toSubState := by
  simp [MState.D₁_eq_traceNorm_div_two, TrDistance, div_eq_inv_mul]

end MState

end Arealaw

namespace Arealaw

/-! ## Entropy across the bridge -/

namespace MState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Physlib's `Sᵥₙ` agrees with our `entropy`. -/
theorem Sᵥₙ_physlibEquiv (ρ : Arealaw.MState ι ℂ) : Sᵥₙ (physlibEquiv ρ) = ρ.entropy :=
  (SubState.entropy_eq_H _).symm

end MState

/-! ## Compatibility with the region partial trace

`ptrace_eq_traceRight`/`_traceLeft` identify the region partial trace with the binary one; the
lemmas below lift that from matrices to states. -/

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {X Y : Finset σ}

/-- Physlib's `traceRight` of the product-transported state is our restriction to `X`. -/
theorem traceRight_physlibEquiv_submatrix (hd : Disjoint X Y)
    (τ : Arealaw.MState (Reg loc (X ∪ Y)) ℂ) :
    (MState.physlibEquiv (τ.submatrix (unionEquiv hd).symm)).traceRight
      = MState.physlibEquiv (τ.restrict Finset.subset_union_left) :=
  _root_.MState.ext_m (ptrace_eq_traceRight hd τ.M).symm

/-- Physlib's `traceLeft` of the product-transported state is our restriction to `Y`. -/
theorem traceLeft_physlibEquiv_submatrix (hd : Disjoint X Y)
    (τ : Arealaw.MState (Reg loc (X ∪ Y)) ℂ) :
    (MState.physlibEquiv (τ.submatrix (unionEquiv hd).symm)).traceLeft
      = MState.physlibEquiv (τ.restrict Finset.subset_union_right) :=
  _root_.MState.ext_m (ptrace_eq_traceLeft hd τ.M).symm

end Arealaw
