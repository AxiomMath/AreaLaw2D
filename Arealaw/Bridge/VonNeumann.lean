import Arealaw.Bridge.MState
import QuantumInfo.Entropy.SSA

/-!
# The entropy bridge to Physlib

Physlib's `Sᵥₙ` and our `SubState.entropy` are the same number, which lets the upstream
inequalities (subadditivity, Araki–Lieb) be read in the region language.  Both are in nats, so
no conversion factor intervenes.  Pinned to `ℂ`, inherited from `Arealaw.Bridge.MState`.
-/

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
