import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The L2 operator norm of matrices: columns, two-sided contractions; unitaries are compact

Extends `Mathlib.Analysis.CStarAlgebra.Matrix`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 l m n p : Type*} [RCLike 𝕜] [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The entries of a column have square sum at most the squared L2 operator norm. -/
theorem sum_norm_apply_sq_le_l2_opNorm_sq [DecidableEq n] (A : Matrix m n 𝕜) (j : n) :
    ∑ i, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h := l2_opNorm_mulVec A (EuclideanSpace.single j 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
  simpa [mulVec, dotProduct, Pi.single_apply] using h2

/-- Multiplying by contractions on both sides does not increase the L2 operator norm. -/
theorem l2_opNorm_mul_mul_le_of_le_one [DecidableEq m] [DecidableEq n] [DecidableEq p]
    {A : Matrix l m 𝕜} {B : Matrix n p 𝕜} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (X : Matrix m n 𝕜) :
    ‖A * X * B‖ ≤ ‖X‖ :=
  calc ‖A * X * B‖ ≤ ‖A‖ * ‖X‖ * ‖B‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖X‖ * 1 := by gcongr
    _ = ‖X‖ := by ring

/-- The unitary matrices form a compact set. -/
theorem isCompact_setOf_conjTranspose_mul_self_eq_one [DecidableEq m] :
    IsCompact {U : Matrix m m 𝕜 | Uᴴ * U = 1} := by
  refine (isCompact_univ_pi fun _ : m ↦ isCompact_univ_pi fun _ : m ↦
    isCompact_closedBall (0 : 𝕜) 1).of_isClosed_subset
    (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const)
    fun (U : Matrix m m 𝕜) hU ↦ Set.mem_univ_pi.mpr fun i ↦ Set.mem_univ_pi.mpr fun j ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary (mem_unitaryGroup_iff'.mpr hU) i j

end Matrix
