import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The L2 operator norm of matrices

Extends `Mathlib/Analysis/CStarAlgebra/Matrix.lean`: column sums and two-sided contractions,
compactness of the unitaries, entrywise and submatrix bounds, Kronecker products with the
identity, and rectangular matrices (the bounds go through `l2_opNorm_mulVec`, not the
C*-algebra structure Mathlib has for square matrices only).

Some declarations here come from the v1 files `OpenAI/ConditionalSkewPhaseCore.lean`,
`OpenAI/FilterMaximizer.lean`, `OpenAI/MatrixKroneckerContraction.lean`,
`OpenAI/RestoringVectors.lean`, whose header records them as ported or adapted from `LionSR/QICLean`
and `LionSR/TNLean` (see `NOTICE`).
-/
namespace Arealaw

open scoped Matrix.Norms.L2Operator Kronecker MatrixOrder
open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*}
  [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- The Euclidean norm of a subvector along an injection.  Injectivity keeps a coordinate
from being counted twice. -/
private theorem euclidean_norm_comp_le (y : n → 𝕜) {f : p → n} (hf : Function.Injective f) :
    ‖(EuclideanSpace.equiv p 𝕜).symm (y ∘ f)‖ ≤ ‖(EuclideanSpace.equiv n 𝕜).symm y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  gcongr
  exact (Finset.sum_map _ ⟨f, hf⟩ fun j => ‖y j‖ ^ 2).symm.trans_le
    (Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity)

/-- Pythagoras over a product index. -/
private theorem euclidean_norm_sq_prod (v : EuclideanSpace 𝕜 (m × p)) :
    ‖v‖ ^ 2 = ∑ b : p, ‖(EuclideanSpace.equiv m 𝕜).symm fun i => v.ofLp (i, b)‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]

/-- `A ⊗ₖ 1` acts fibrewise: on the fibre over `b` of the second factor it is `A`. -/
private theorem kronecker_one_mulVec_apply {ι : Type*} [DecidableEq p] (A : Matrix ι n 𝕜)
    (v : n × p → 𝕜) (i : ι) (b : p) :
    ((A ⊗ₖ (1 : Matrix p p 𝕜)) *ᵥ v) (i, b) = (A *ᵥ fun j => v (j, b)) i := by
  simp [mulVec, dotProduct, Fintype.sum_prod_type, one_apply]

omit [Fintype m] [Fintype n] [Fintype p] [Fintype q] in
/-- The Kronecker product commutes up to swapping both index pairs. -/
theorem kronecker_comm_submatrix (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    A ⊗ₖ B = (B ⊗ₖ A).submatrix (Equiv.prodComm m p) (Equiv.prodComm n q) := by
  ext ⟨a, b⟩ ⟨i, j⟩
  simp [mul_comm]

section DecEqRight

-- the L2 operator norm on `Matrix m n 𝕜` is an instance only under `[DecidableEq n]`
variable [DecidableEq n] [DecidableEq q]

/-- Upper-bound criterion for the L2 operator norm; the converse is
`Matrix.l2_opNorm_mulVec`. -/
theorem l2_opNorm_le_bound (A : Matrix m n 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : EuclideanSpace 𝕜 n,
      ‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ WithLp.ofLp x)‖ ≤ c * ‖x‖) : ‖A‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc h

/-- Every entry of a matrix is bounded by its L2 operator norm. -/
theorem norm_entry_le_l2_opNorm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ :=
  (PiLp.norm_apply_le (WithLp.toLp 2 (A.col j) : EuclideanSpace 𝕜 m) i).trans <| by
    simpa using Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j 1)

/-- Selecting rows along an injection cannot increase the norm. -/
private theorem l2_opNorm_submatrix_id_le (A : Matrix m n 𝕜) {f : p → m}
    (hf : Function.Injective f) : ‖A.submatrix f id‖ ≤ ‖A‖ :=
  l2_opNorm_le_bound _ (norm_nonneg _) fun x =>
    (euclidean_norm_comp_le (A *ᵥ WithLp.ofLp x) hf).trans (Matrix.l2_opNorm_mulVec A x)

/-- **Taking a submatrix along injections does not increase the L2 operator norm.**
Injectivity is necessary: duplicating the row of `(1 : Matrix Unit Unit ℝ)` gives norm `√2`. -/
theorem l2_opNorm_submatrix_le (A : Matrix m n 𝕜) {f : p → m} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) : ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  refine le_trans ?_ (l2_opNorm_submatrix_id_le A hf)
  rw [← Matrix.l2_opNorm_conjTranspose (A.submatrix f id), ← Matrix.l2_opNorm_conjTranspose]
  exact l2_opNorm_submatrix_id_le (A.submatrix f id)ᴴ hg

/-- **The L2 operator norm is invariant under reindexing** along equivalences. -/
@[simp] theorem l2_opNorm_submatrix (A : Matrix m n 𝕜) (e : p ≃ m) (f : q ≃ n) :
    ‖A.submatrix e f‖ = ‖A‖ :=
  le_antisymm (l2_opNorm_submatrix_le A e.injective f.injective)
    (by simpa using l2_opNorm_submatrix_le (A.submatrix e f) e.symm.injective f.symm.injective)

variable [DecidableEq p] in
/-- Padding on the right by an identity factor does not increase the L2 operator norm. -/
theorem l2_opNorm_kronecker_one_le (A : Matrix m n 𝕜) : ‖A ⊗ₖ (1 : Matrix p p 𝕜)‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [euclidean_norm_sq_prod, mul_pow, euclidean_norm_sq_prod, Finset.mul_sum]
  simp_rw [← mul_pow]
  gcongr with b _
  simpa [kronecker_one_mulVec_apply] using
    Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv n 𝕜).symm fun j => x.ofLp (j, b))

/-- Padding on the left by an identity factor does not increase the L2 operator norm. -/
theorem l2_opNorm_one_kronecker_le (B : Matrix p q 𝕜) : ‖(1 : Matrix n n 𝕜) ⊗ₖ B‖ ≤ ‖B‖ := by
  rw [kronecker_comm_submatrix, l2_opNorm_submatrix]
  exact l2_opNorm_kronecker_one_le B

/-- **Submultiplicativity of the L2 operator norm over the Kronecker product.** -/
theorem l2_opNorm_kronecker_le (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) : ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  classical
  conv_lhs => rw [← Matrix.mul_one A, ← Matrix.one_mul B, mul_kronecker_mul]
  grw [l2_opNorm_mul, l2_opNorm_kronecker_one_le, l2_opNorm_one_kronecker_le]

/-- The identity is a contraction. -/
theorem l2_opNorm_one_le : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
  simp

/-- An isometry is a contraction. -/
theorem l2_opNorm_le_one_of_conjTranspose_mul_self {A : Matrix m n 𝕜} (hA : Aᴴ * A = 1) :
    ‖A‖ ≤ 1 :=
  (sq_le_one_iff₀ (norm_nonneg _)).1 <| by
    rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, hA]; exact l2_opNorm_one_le

variable [DecidableEq m] in
/-- A matrix unit has the operator norm of its entry. -/
@[simp]
theorem l2_opNorm_single (i : m) (j : n) (a : 𝕜) : ‖single i j a‖ = ‖a‖ := by
  refine (mul_self_inj (norm_nonneg _) (norm_nonneg a)).1 ?_
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self, conjTranspose_single, single_mul_single_same,
    ← diagonal_single, l2_opNorm_diagonal, Pi.norm_single]
  simp

/-- An effect `0 ≤ M ≤ 1` is a contraction: its spectrum lies in `[0, 1]`. -/
theorem l2_opNorm_le_one_of_nonneg_of_le_one {M : Matrix n n 𝕜} (h₀ : 0 ≤ M) (h₁ : M ≤ 1) :
    ‖M‖ ≤ 1 := by
  have hM : IsSelfAdjoint M := IsSelfAdjoint.of_nonneg h₀
  rw [← cfcHom_id (R := ℝ) hM,
    (isometry_cfcHom (R := ℝ) M hM).norm_map_of_map_zero (map_zero _)]
  exact (ContinuousMap.norm_le _ zero_le_one).mpr fun x =>
    (Real.norm_of_nonneg (spectrum_nonneg_of_nonneg h₀ x.2)).trans_le <|
      (CFC.le_one_iff (R := ℝ) M).mp h₁ x x.2

end DecEqRight

end Arealaw

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
