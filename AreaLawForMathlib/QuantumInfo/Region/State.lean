import AreaLawForMathlib.QuantumInfo.ClassicalInfo.Entropy
import AreaLawForMathlib.QuantumInfo.Region.PartialTrace
import AreaLawForMathlib.QuantumInfo.Entropy.VonNeumann

/-!
# States on regions, region entropy and mutual information

Extends `Mathlib/Analysis/Matrix/PosDef.lean`: `SubState ι 𝕜` (positive semidefinite, real
trace at most one) and `MState ι 𝕜` (unit trace), restriction to a subregion by the partial
trace, the von Neumann entropy `SubState.entropy`, `SubState.regionEntropy` of a region and
`SubState.mutualInfo` of two regions.
-/
namespace Arealaw

open scoped ComplexOrder
open Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {S T U : Finset σ}

/-! ## Subnormalized and normalized states -/

/-- A subnormalized state: positive semidefinite with real trace at most one. -/
@[ext] structure SubState (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜] where
  /-- the (sub)density matrix -/
  M : Matrix ι ι 𝕜
  /-- positive semidefiniteness -/
  psd : M.PosSemidef
  /-- subnormalization: real trace at most one -/
  tr_le_one : RCLike.re M.trace ≤ 1

/-- A (normalized) state: a subnormalized state of unit trace. -/
structure MState (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜] extends SubState ι 𝕜 where
  /-- normalization: unit trace -/
  tr_eq_one : RCLike.re M.trace = 1

/-- A normalized state is determined by its density matrix. -/
@[ext] theorem MState.ext {ι : Type*} [Fintype ι] {ρ τ : MState ι 𝕜} (h : ρ.M = τ.M) : ρ = τ := by
  rwa [MState.mk.injEq, SubState.ext_iff]

namespace SubState

/-- Restrict a state on the region `T` to a subregion `S ⊆ T` by the partial trace. -/
noncomputable def restrict (h : S ⊆ T) (ρ : SubState (Reg loc T) 𝕜) : SubState (Reg loc S) 𝕜 where
  M := ptrace h ρ.M
  psd := posSemidef_ptrace h ρ.psd
  tr_le_one := trace_ptrace h ρ.M ▸ ρ.tr_le_one

/-- **Functoriality of restriction**: restricting `U → T → S` equals restricting
`U → S`. -/
theorem restrict_restrict (hST : S ⊆ T) (hTU : T ⊆ U) (ρ : SubState (Reg loc U) 𝕜) :
    (ρ.restrict hTU).restrict hST = ρ.restrict (hST.trans hTU) :=
  SubState.ext (ptrace_ptrace hST hTU ρ.M)

/-- The density matrix of a restricted subnormalized state is the partial trace. -/
@[simp] theorem restrict_M (h : S ⊆ T) (ρ : SubState (Reg loc T) 𝕜) :
    (ρ.restrict h).M = ptrace h ρ.M := rfl

/-- **Identity law** for restriction: the state-level counterpart of `ptrace_self`. -/
@[simp] theorem restrict_self (ρ : SubState (Reg loc U) 𝕜) :
    ρ.restrict (Finset.Subset.refl U) = ρ :=
  SubState.ext (ptrace_self _)

/-- The von Neumann entropy of a subnormalized state (natural-log convention). -/
noncomputable def entropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : SubState ι 𝕜) : ℝ :=
  vonNeumann ρ.psd.isHermitian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entropy of a state is the Shannon entropy of its spectrum. -/
theorem entropy_eq_H (ρ : SubState ι 𝕜) : ρ.entropy = H ρ.psd.isHermitian.eigenvalues :=
  vonNeumann_eq_H _

/-- The entropy of a subnormalized state is nonnegative: subnormalization confines every
eigenvalue to `[0,1]`, where `negMulLog` is nonnegative. -/
theorem entropy_nonneg (ρ : SubState ι 𝕜) : 0 ≤ ρ.entropy :=
  ρ.entropy_eq_H ▸ Arealaw.entropy_nonneg ρ.psd ρ.tr_le_one

/-- Every eigenvalue of a subnormalized state lies in `[0,1]`. -/
theorem eigenvalues_le_one (ρ : SubState ι 𝕜) (i : ι) : ρ.psd.isHermitian.eigenvalues i ≤ 1 :=
  Arealaw.eigenvalues_le_one ρ.psd ρ.tr_le_one i

/-- A state on a one-dimensional space has the entropy of its total weight. -/
theorem entropy_of_unique [Unique ι] (ρ : SubState ι 𝕜) :
    ρ.entropy = Real.negMulLog (RCLike.re ρ.M.trace) := by
  rw [entropy_eq_H, H, re_trace_eq_sum_eigenvalues ρ.psd, Fintype.sum_unique, Fintype.sum_unique]

/-! ### Relabelling the index

Every region transport (`regEquivOfEq`, `unionEquiv`, `embedEquiv`) lands a state on a
relabelled index, so the identities the geometry layer needs hold only up to reindexing. -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Relabel the index of a subnormalized state along an equivalence. -/
def submatrix (ρ : SubState ι 𝕜) (e : m ≃ ι) : SubState m 𝕜 where
  M := ρ.M.submatrix e e
  psd := ρ.psd.submatrix e
  tr_le_one := trace_submatrix ρ.M e ▸ ρ.tr_le_one

omit [DecidableEq ι] [DecidableEq m] in
/-- The density matrix of a relabelled state is the relabelled density matrix. -/
@[simp] theorem submatrix_M (ρ : SubState ι 𝕜) (e : m ≃ ι) :
    (ρ.submatrix e).M = ρ.M.submatrix e e := rfl

/-- **The entropy of a state does not see a relabelling of its index**: the state-level
form of `vonNeumann_submatrix_equiv`. -/
@[simp] theorem entropy_submatrix (ρ : SubState ι 𝕜) (e : m ≃ ι) :
    (ρ.submatrix e).entropy = ρ.entropy :=
  vonNeumann_submatrix_equiv ρ.psd.isHermitian e

end SubState

namespace MState

/-- Alternative constructor: one does not need to check subnormalization, since unit trace
implies it.  This discharges the inherited `tr_le_one` field. -/
@[simps] def mk' {ι : Type*} [Fintype ι] {M : Matrix ι ι 𝕜} (psd : M.PosSemidef)
    (tr_eq_one : RCLike.re M.trace = 1) : MState ι 𝕜 where
  M := M
  psd := psd
  tr_le_one := tr_eq_one.le
  tr_eq_one := tr_eq_one

/-- Normalization in `𝕜`: a state's trace is `1`, not merely of real part `1`. -/
theorem trace_eq_one {ι : Type*} [Fintype ι] (ρ : MState ι 𝕜) : ρ.M.trace = 1 :=
  RCLike.ext (by simpa using ρ.tr_eq_one)
    (by simpa using (RCLike.nonneg_iff.1 ρ.psd.trace_nonneg).2)

/-- Restriction of a normalized state to a subregion.  The partial trace preserves the
trace, so the result is again normalized. -/
noncomputable def restrict (h : S ⊆ T) (ρ : MState (Reg loc T) 𝕜) : MState (Reg loc S) 𝕜 :=
  ⟨ρ.toSubState.restrict h, trace_ptrace h ρ.M ▸ ρ.tr_eq_one⟩

/-- The density matrix of a restricted normalized state is the partial trace. -/
@[simp] theorem restrict_M (h : S ⊆ T) (ρ : MState (Reg loc T) 𝕜) :
    (ρ.restrict h).M = ptrace h ρ.M := rfl

/-- **Identity law** for restriction of a normalized state. -/
@[simp] theorem restrict_self (ρ : MState (Reg loc U) 𝕜) :
    ρ.restrict (Finset.Subset.refl U) = ρ :=
  MState.ext (ptrace_self _)

/-- Restricting a normalized state agrees with restricting it as a subnormalized one. -/
@[simp] theorem toSubState_restrict (h : S ⊆ T) (ρ : MState (Reg loc T) 𝕜) :
    (ρ.restrict h).toSubState = ρ.toSubState.restrict h := rfl

/-- **Functoriality of restriction** for normalized states. -/
theorem restrict_restrict (hST : S ⊆ T) (hTU : T ⊆ U) (ρ : MState (Reg loc U) 𝕜) :
    (ρ.restrict hTU).restrict hST = ρ.restrict (hST.trans hTU) :=
  MState.ext (ptrace_ptrace hST hTU ρ.M)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entropy of a normalized state is at most the log of the dimension. -/
theorem entropy_le_log_card (ρ : MState ι 𝕜) : ρ.entropy ≤ Real.log (Fintype.card ι) :=
  ρ.toSubState.entropy_eq_H ▸ Arealaw.entropy_le_log_card ρ.psd ρ.tr_eq_one

/-- The eigenvalues of a state form a probability vector: they sum to one. -/
theorem sum_eigenvalues_eq_one (ρ : MState ι 𝕜) : ∑ i, ρ.psd.isHermitian.eigenvalues i = 1 := by
  rw [← re_trace_eq_sum_eigenvalues ρ.psd, ρ.tr_eq_one]

section Submatrix

variable {m : Type*} [Fintype m]

omit [DecidableEq ι]

/-- Relabel the index of a normalized state along an equivalence. -/
def submatrix (ρ : MState ι 𝕜) (e : m ≃ ι) : MState m 𝕜 :=
  mk' (ρ.psd.submatrix e) (trace_submatrix ρ.M e ▸ ρ.tr_eq_one)

/-- The density matrix of a relabelled normalized state. -/
@[simp] theorem submatrix_M (ρ : MState ι 𝕜) (e : m ≃ ι) :
    (ρ.submatrix e).M = ρ.M.submatrix e e := rfl

/-- Relabelling a normalized state agrees with relabelling it as a subnormalized one. -/
@[simp] theorem toSubState_submatrix (ρ : MState ι 𝕜) (e : m ≃ ι) :
    (ρ.submatrix e).toSubState = ρ.toSubState.submatrix e := rfl

end Submatrix

end MState

/-! ## Region entropies of a global state -/

-- `entropy` needs a decidable index, so decidability enters with the region entropies; the
-- restriction layer above is free of it.
variable {X Y : Finset σ} [∀ i, DecidableEq (loc i)]

namespace SubState

/-- Entropy of the region `X` of a global (sub)state on `U`. -/
noncomputable def regionEntropy (ρ : SubState (Reg loc U) 𝕜) (h : X ⊆ U) : ℝ :=
  (ρ.restrict h).entropy

/-- Mutual information of two *disjoint* regions of a global state.  For overlapping `X`,
`Y` this quantity is not the mutual information, so results about it take `Disjoint X Y`. -/
noncomputable def mutualInfo (ρ : SubState (Reg loc U) 𝕜) (hX : X ⊆ U) (hY : Y ⊆ U) : ℝ :=
  ρ.regionEntropy hX + ρ.regionEntropy hY - ρ.regionEntropy (Finset.union_subset hX hY)

/-! ### The region-entropy API

`regionEntropy` and `mutualInfo` are the paper-facing quantities: every statement of §III is
written in them. -/

/-- `regionEntropy` unfolds to the entropy of the restricted state. -/
theorem regionEntropy_def (ρ : SubState (Reg loc U) 𝕜) (h : X ⊆ U) :
    ρ.regionEntropy h = (ρ.restrict h).entropy := rfl

/-- `mutualInfo` unfolds to the usual three-term combination. -/
theorem mutualInfo_def (ρ : SubState (Reg loc U) 𝕜) (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.mutualInfo hX hY =
      ρ.regionEntropy hX + ρ.regionEntropy hY - ρ.regionEntropy (Finset.union_subset hX hY) :=
  rfl

/-- Region entropies of a subnormalized state are nonnegative. -/
theorem regionEntropy_nonneg (ρ : SubState (Reg loc U) 𝕜) (h : X ⊆ U) : 0 ≤ ρ.regionEntropy h :=
  entropy_nonneg _

/-- Equal regions give equal entropies; the subset proof is irrelevant. -/
theorem regionEntropy_congr (ρ : SubState (Reg loc U) 𝕜) {X X' : Finset σ} (hXX : X = X')
    (hX : X ⊆ U) (hX' : X' ⊆ U) : ρ.regionEntropy hX = ρ.regionEntropy hX' := hXX ▸ rfl

/-- The entropy of the whole region is the entropy of the state. -/
@[simp] theorem regionEntropy_self (ρ : SubState (Reg loc U) 𝕜) :
    ρ.regionEntropy (Finset.Subset.refl U) = ρ.entropy := by
  rw [regionEntropy_def, restrict_self]

/-- The entropy of the empty region is the entropy of the total weight. -/
theorem regionEntropy_empty (ρ : SubState (Reg loc U) 𝕜) :
    ρ.regionEntropy (Finset.empty_subset U) = Real.negMulLog (RCLike.re ρ.M.trace) := by
  rw [regionEntropy_def, entropy_of_unique, restrict_M, trace_ptrace]

/-- Mutual information is symmetric. -/
theorem mutualInfo_comm (ρ : SubState (Reg loc U) 𝕜) (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.mutualInfo hX hY = ρ.mutualInfo hY hX := by
  grind [mutualInfo_def, regionEntropy_congr ρ (Finset.union_comm X Y)]

end SubState

/-- The empty region of a normalized state carries no entropy. -/
@[simp] theorem MState.regionEntropy_empty (ρ : MState (Reg loc U) 𝕜) :
    ρ.toSubState.regionEntropy (Finset.empty_subset U) = 0 := by
  simp [SubState.regionEntropy_empty, ρ.tr_eq_one]

end Arealaw
