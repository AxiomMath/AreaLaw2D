import Arealaw.Fidelity
import Arealaw.Mixed
import Arealaw.TraceDist
import QuantumInfo.States.Mixed.Fidelity
import QuantumInfo.States.Mixed.MState
import QuantumInfo.States.Mixed.TraceDistance

/-!
# The state bridge to Physlib

Our normalized states over `ℂ` and Physlib's `MState` are the same structure, related by
`physlibEquiv`.

Pinned to `ℂ`: Physlib's `MState d` carries a `HermitianMat d ℂ`, so there is no `𝕜`-generic
form to bridge to.  Physlib's `MState` is in the root namespace, hence `_root_.MState` here.
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

/-- The Hermitian-matrix carrier of a transported state.  Not `@[simp]`: the left-hand side
is not simp-normal. -/
theorem physlibEquiv_M_mat (ρ : Arealaw.MState ι ℂ) : (physlibEquiv ρ).M.mat = ρ.M := rfl

/-- The density matrix of a state transported back. -/
@[simp] theorem physlibEquiv_symm_M (Q : _root_.MState ι) : (physlibEquiv.symm Q).M = Q.m := rfl

section Reindex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The bridge intertwines `submatrix` with Physlib's `relabel`. -/
theorem physlibEquiv_submatrix (ρ : Arealaw.MState ι ℂ) (e : m ≃ ι) :
    physlibEquiv (ρ.submatrix e) = (physlibEquiv ρ).relabel e := rfl

end Reindex

/-- Physlib's `HermitianMat.sqrt` is the functional-calculus square root of the carrier. -/
private theorem mat_sqrt_of_nonneg {𝕜 : Type*} [RCLike 𝕜] {A : HermitianMat ι 𝕜} (hA : 0 ≤ A) :
    A.sqrt.mat = CFC.sqrt A.mat := by
  simp [HermitianMat.sqrt, cfcSqrt_eq_cfc_real_sqrt (HermitianMat.zero_le_iff.mp hA).nonneg]

/-- The bridge intertwines the fidelities.  Physlib spells the product in the other order; the
two agree by `fidelity_comm`. -/
theorem fidelity_physlibEquiv (ρ σ : Arealaw.MState ι ℂ) :
    (physlibEquiv ρ).fidelity (physlibEquiv σ) = fidelity ρ.M σ.M := by
  simp [_root_.MState.fidelity_eq_traceNorm_sqrt_mul_sqrt,
    mat_sqrt_of_nonneg (physlibEquiv σ).nonneg, mat_sqrt_of_nonneg (physlibEquiv ρ).nonneg,
    ← fidelity_def, fidelity_comm]

/-- The bridge intertwines the trace distances: Physlib's `TrDistance` is `D₁` on normalized
states. -/
theorem trDistance_physlibEquiv (ρ σ : Arealaw.MState ι ℂ) :
    _root_.TrDistance (physlibEquiv ρ) (physlibEquiv σ) = ρ.toSubState.D₁ σ.toSubState := by
  simp [MState.D₁_eq_traceNorm_div_two, TrDistance, div_eq_inv_mul]

end MState

end Arealaw
