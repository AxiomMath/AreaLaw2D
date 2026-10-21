import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
# Tensor products of copy-dependent matrices

Extends `Mathlib/LinearAlgebra/PiTensorProduct.lean`.

`⨂_j A_j` on `(ℂ^Ω)^{⊗k}`, the matrix `(x, y) ↦ ∏_j A_j(x_j, y_j)` on configurations
`Fin k → Ω`. It is multiplicative and `*`-preserving, and choosing one of two matrices at every
copy and summing over the choices gives `⨂_j (E + G)`.
-/

open Matrix Finset

namespace Matrix

variable {k : ℕ} {Ω : Type*} [Fintype Ω]

/-- The tensor product `⨂_j A_j` of `k` matrices on `(ℂ^Ω)^{⊗k}`. -/
def piTensorOp (A : Fin k → Matrix Ω Ω ℂ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  Matrix.of fun x y => ∏ j, A j (x j) (y j)

omit [Fintype Ω] in
theorem piTensorOp_apply (A : Fin k → Matrix Ω Ω ℂ) (x y : Fin k → Ω) :
    piTensorOp A x y = ∏ j, A j (x j) (y j) := rfl

/-- `(⨂_j A_j)(⨂_j B_j) = ⨂_j A_j B_j`. -/
theorem piTensorOp_mul (A B : Fin k → Matrix Ω Ω ℂ) :
    piTensorOp A * piTensorOp B = piTensorOp fun j => A j * B j := by
  ext x y
  simp only [mul_apply, piTensorOp_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun w => ?_
  rw [Finset.prod_mul_distrib]

omit [Fintype Ω] in
/-- `(⨂_j A_j)ᴴ = ⨂_j A_jᴴ`. -/
theorem conjTranspose_piTensorOp (A : Fin k → Matrix Ω Ω ℂ) :
    (piTensorOp A)ᴴ = piTensorOp fun j => (A j)ᴴ := by
  ext x y
  simp [piTensorOp_apply, conjTranspose_apply]

omit [Fintype Ω] in
/-- `⨂_j 1 = 1`. -/
theorem piTensorOp_one [DecidableEq Ω] : piTensorOp (fun _ : Fin k => (1 : Matrix Ω Ω ℂ)) = 1 := by
  ext x y
  simp only [piTensorOp_apply, one_apply]
  by_cases h : x = y
  · simp [h]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (mem_univ j) (if_neg hj)

omit [Fintype Ω] in
/-- `∑_B ⨂_j (E if j ∈ B else G) = ⨂_j (E + G)`. -/
theorem sum_piTensorOp_ite (E G : Matrix Ω Ω ℂ) :
    ∑ B : Finset (Fin k), piTensorOp (fun j => if j ∈ B then E else G) =
      piTensorOp fun _ => E + G := by
  ext x y
  simp only [Matrix.sum_apply, piTensorOp_apply, add_apply]
  rw [Finset.prod_add, powerset_univ]
  refine Fintype.sum_congr _ _ fun B => ?_
  have hi : ∀ j, (if j ∈ B then E else G) (x j) (y j) =
      if j ∈ B then E (x j) (y j) else G (x j) (y j) := fun j => by split_ifs <;> rfl
  simp only [hi]
  rw [Finset.prod_ite, filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp

end Matrix
