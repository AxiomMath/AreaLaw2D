/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Algebra/HermitianHelpers.lean`
(Apache 2.0), restricted to `Matrix.one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one`. Its
helper `Matrix.star_dotProduct_vecMulVec_mulVec` is ported from
`QICLean/Algebra/MatrixAux.lean` at the same commit.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef

/-!
# Rank-one positivity criteria

If `∑ i, ‖v i‖ ^ 2 ≤ 1`, then `1 - |v⟩⟨v|` is positive semidefinite: its quadratic form at
`w` is `‖w‖² - |⟨v, w⟩|²`, nonnegative by Cauchy–Schwarz.
-/

open scoped Matrix ComplexOrder InnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- The quadratic form of a rank-one outer product `vecMulVec a b` reads off as
`(b ⬝ᵥ w)((conj w) ⬝ᵥ a)`. -/
theorem star_dotProduct_vecMulVec_mulVec (a b w : ι → ℂ) :
    star w ⬝ᵥ (Matrix.vecMulVec a b *ᵥ w) = (b ⬝ᵥ w) * (star w ⬝ᵥ a) := by
  have lhs : star w ⬝ᵥ (Matrix.vecMulVec a b *ᵥ w)
      = ∑ i, ∑ j, star (w i) * a i * b j * w j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have rhs : (b ⬝ᵥ w) * (star w ⬝ᵥ a) = ∑ i, ∑ j, star (w i) * a i * b j * w j := by
    simp only [dotProduct, Pi.star_apply]
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [lhs, rhs]

variable [DecidableEq ι]

/-- If the squared norm of a vector is at most one, then `I - |v><v|` is
positive semidefinite. -/
theorem one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one (v : ι → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 ≤ 1) :
    ((1 : Matrix ι ι ℂ) - vecMulVec v (star v)).PosSemidef := by
  classical
  set V : EuclideanSpace ℂ ι := WithLp.toLp 2 v with hV
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact isHermitian_one.sub (Matrix.posSemidef_vecMulVec_self_star v).1
  · intro w
    set W : EuclideanSpace ℂ ι := WithLp.toLp 2 w with hW
    have hQ :
        star w ⬝ᵥ (((1 : Matrix ι ι ℂ) - vecMulVec v (star v)) *ᵥ w) =
          star w ⬝ᵥ w - (star v ⬝ᵥ w) * (star w ⬝ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
        star_dotProduct_vecMulVec_mulVec]
    rw [hQ]
    have hVW : star v ⬝ᵥ w = ⟪V, W⟫_ℂ := by
      rw [hV, hW, EuclideanSpace.inner_toLp_toLp]
      exact (dotProduct_comm w (star v)).symm
    have hWV : star w ⬝ᵥ v = ⟪W, V⟫_ℂ := by
      rw [hV, hW, EuclideanSpace.inner_toLp_toLp]
      exact (dotProduct_comm v (star w)).symm
    have hWW : star w ⬝ᵥ w = ⟪W, W⟫_ℂ := by
      rw [hW, EuclideanSpace.inner_toLp_toLp]
      exact (dotProduct_comm w (star w)).symm
    rw [hVW, hWV, hWW]
    have hVVnorm : ‖V‖ ^ 2 ≤ 1 := by
      rw [hV, EuclideanSpace.norm_sq_eq]
      simpa using hv
    have hinner_le : ‖⟪V, W⟫_ℂ‖ ^ 2 ≤ ‖W‖ ^ 2 := by
      have hCS := norm_inner_le_norm (𝕜 := ℂ) V W
      have hsq : ‖⟪V, W⟫_ℂ‖ ^ 2 ≤ (‖V‖ * ‖W‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hCS 2
      nlinarith [hVVnorm, hsq, norm_nonneg V, norm_nonneg W]
    have hWWreal : ⟪W, W⟫_ℂ = ((‖W‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) W]
      norm_cast
    have hprod : ⟪V, W⟫_ℂ * ⟪W, V⟫_ℂ =
        ((‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_conj_symm W V, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hWWreal, hprod]
    rw [show ((‖W‖ ^ 2 : ℝ) : ℂ) - ((‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
        ((‖W‖ ^ 2 - ‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) by norm_num]
    rw [Complex.zero_le_real]
    linarith

end Matrix
