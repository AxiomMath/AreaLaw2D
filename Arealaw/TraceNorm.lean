import Arealaw.Mixed
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Trace-norm adapters

Facts about `Matrix.traceNorm` in this project's language, for the correlation measure and
trace distance of later milestones.

The Hermitian and positive-semidefinite facts are `RCLike`-generic;
`MState.norm_trace_mul_le_one` is pinned to `ℂ` because the bounds it composes come from the
singular-value decomposition, which the upstream gives for complex matrices only.  Its norm is
Mathlib's L2 operator norm, not Physlib's separate `Matrix.opNorm`.
-/

namespace Arealaw

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

/-- A sum of `f` over a family depends only on the multiset of its values. -/
theorem sum_eq_of_multiset_map_eq {γ δ : Type*} [Fintype γ] [Fintype δ] (f : ℝ → ℝ) {p : γ → ℝ}
    {q : δ → ℝ} (h : Finset.univ.val.map p = Finset.univ.val.map q) : ∑ i, f (p i) = ∑ j, f (q j) :=
  congrArg Multiset.sum
    (by simpa [Multiset.map_map, Function.comp] using congrArg (Multiset.map f) h)

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

/-- The trace norm of a subnormalized state is its trace. -/
theorem SubState.traceNorm_eq_trace (ρ : SubState ι 𝕜) : ρ.M.traceNorm = RCLike.re ρ.M.trace := by
  simp [← Matrix.PosSemidef.traceNorm_eq_trace ρ.psd]

/-- A normalized state has trace norm one. -/
@[simp] theorem MState.traceNorm_eq_one (ρ : Arealaw.MState ι 𝕜) : ρ.M.traceNorm = 1 := by
  rw [SubState.traceNorm_eq_trace ρ.toSubState, ρ.tr_eq_one]

/-- The trace norm of the identity is the dimension. -/
@[simp] theorem traceNorm_one [DecidableEq ι] : (1 : Matrix ι ι 𝕜).traceNorm = Fintype.card ι :=
  mod_cast (Matrix.PosSemidef.one (n := ι) (R := 𝕜)).traceNorm_eq_trace.trans Matrix.trace_one

/-- The trace norm `tr √(XᴴX)` sees `X` only through `XᴴX`. -/
theorem traceNorm_eq_of_conjTranspose_mul_self_eq {κ μ : Type*} [Fintype κ] [Fintype μ]
    {X : Matrix ι κ 𝕜} {Y : Matrix μ κ 𝕜} (h : Xᴴ * X = Yᴴ * Y) : X.traceNorm = Y.traceNorm := by
  rw [Matrix.traceNorm, h, Matrix.traceNorm]

section Reindex

variable {m : Type*} [Fintype m]

/-- The trace norm is invariant under reindexing.  Hermitian-only; the rectangular case
follows from `traceNorm_isometry_left`/`_right`. -/
theorem traceNorm_submatrix_equiv {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (e : m ≃ ι) :
    (A.submatrix e e).traceNorm = A.traceNorm := by
  classical
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues (hA.submatrix e),
    Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hA]
  exact sum_eq_of_multiset_map_eq abs (eigenvalues_multiset_submatrix_equiv hA e)

/-- The state-level form of `traceNorm_submatrix_equiv`.  Not `@[simp]`: the left-hand side
exposes `.M`, which `SubState.submatrix_M` rewrites. -/
theorem SubState.traceNorm_submatrix (ρ : SubState ι 𝕜) (e : m ≃ ι) :
    (ρ.submatrix e).M.traceNorm = ρ.M.traceNorm :=
  traceNorm_submatrix_equiv ρ.psd.isHermitian e

end Reindex

section Expectation

variable [DecidableEq ι]

/-- In any state, the expectation of an operator of norm at most one has modulus at most one.
This bounds the supremum defining the correlation measure. -/
theorem MState.norm_trace_mul_le_one (ρ : Arealaw.MState ι ℂ) {M : Matrix ι ι ℂ} (hM : ‖M‖ ≤ 1) :
    ‖(ρ.M * M).trace‖ ≤ 1 :=
  (Matrix.abs_trace_le_traceNorm _).trans <|
    (Matrix.traceNorm_mul_le_traceNorm_opNorm ρ.M M).trans (by simpa using hM)

end Expectation

end Arealaw
