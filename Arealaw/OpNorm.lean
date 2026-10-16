import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# L2 operator-norm adapters

Facts about Mathlib's L2 operator norm (`Matrix.Norms.L2Operator`) that the correlation
measure `Arealaw.Cor` needs and the upstream does not provide.  The norm is *defined* through
`toEuclideanLin`, so the bounds below go through `Matrix.l2_opNorm_mulVec` and sums in
`EuclideanSpace`, not through the C*-algebra structure Mathlib has for square matrices only.

`l2_opNorm_submatrix` duplicates Physlib's `Matrix.opNorm_reindex_proven`, which is stated for
Physlib's own `Matrix.opNorm` rather than the instance norm, demands `DecidableEq` on four
index types rather than two, and sits in a file that transitively `import Mathlib`.

`l2_opNorm_le_one_of_nonneg_of_le_one` reads the norm off the spectrum through Mathlib's
isometric functional calculus on matrices.  Mathlib's `CStarAlgebra.norm_le_one_iff_of_nonneg`
states it, but the matrix `CStarAlgebra` instance is `ℂ`-only, and `norm_cfc_le` needs a
`NormedAlgebra ℝ` instance the matrices over `𝕜` lack, so the proof applies the isometry of
`cfcHom` directly.
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

/-- A Kronecker product of two contractions is a contraction. -/
theorem l2_opNorm_kronecker_le_one {A : Matrix m n 𝕜} {B : Matrix p q 𝕜} (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) : ‖A ⊗ₖ B‖ ≤ 1 :=
  (l2_opNorm_kronecker_le A B).trans (mul_le_one₀ hA (norm_nonneg B) hB)

/-- The identity is a contraction. -/
theorem l2_opNorm_one_le : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
  simp

/-- An isometry is a contraction. -/
theorem l2_opNorm_le_one_of_conjTranspose_mul_self {A : Matrix m n 𝕜} (hA : Aᴴ * A = 1) :
    ‖A‖ ≤ 1 :=
  (sq_le_one_iff₀ (norm_nonneg _)).1 <| by
    rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, hA]; exact l2_opNorm_one_le

/-- A unitary matrix is a contraction, for any `DecidableEq` instance on the index type. -/
theorem l2_opNorm_le_one_of_mem_unitaryGroup {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    (dec : DecidableEq n) {M : Matrix n n 𝕜} (hM : M ∈ @unitaryGroup n dec _ 𝕜 _ _) :
    ‖M‖ ≤ 1 := by
  classical
  refine l2_opNorm_le_one_of_conjTranspose_mul_self ?_
  rw [← Matrix.star_eq_conjTranspose]
  exact hM.1.trans (by ext a b; simp [Matrix.one_apply])

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
