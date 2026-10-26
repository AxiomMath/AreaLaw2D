import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Complex powers of a positive matrix in a fixed eigenbasis

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`.

For `W` unitary and `l : n → ℝ`, the complex power `W diag(e^{z log l}) W*` is entire in `z`,
equals `1` at `z = 0` and `W diag(l) W*` at `z = 1` (for `l > 0`), satisfies
`M^{z+w} = M^z M^w`, is unitary on the imaginary axis and bounded on the strip `0 ≤ Re z ≤ 1`.
-/

namespace Matrix

open Complex
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `‖A v‖ ≤ ‖A‖ ‖v‖` for the `L²` operator norm. -/
theorem norm_toEuclideanLin_le (A : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    ‖toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  l2_opNorm_mulVec A v

/-- A matrix `A` with `A A* = 1` is a contraction for the `L²` operator norm. -/
theorem l2_opNorm_le_one_of_mul_conjTranspose {A : Matrix n n ℂ} (hA : A * Aᴴ = 1) :
    ‖A‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self Aᴴ
  rw [conjTranspose_conjTranspose, hA, l2_opNorm_conjTranspose] at h
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty n with hn | hn
    · simp [Subsingleton.elim (1 : Matrix n n ℂ) 0]
    · exact norm_one.le
  nlinarith [norm_nonneg A]

/-- The complex power `W diag(e^{z log l}) W*`. -/
noncomputable def specPow (W : Matrix n n ℂ) (l : n → ℝ) (z : ℂ) : Matrix n n ℂ :=
  W * diagonal (fun k ↦ exp (z * Real.log (l k))) * Wᴴ

variable {W : Matrix n n ℂ} {l : n → ℝ}

theorem specPow_zero (hW : Wᴴ * W = 1) (l : n → ℝ) : specPow W l 0 = 1 := by
  simp [specPow, mul_eq_one_comm.1 hW]

theorem specPow_one (W : Matrix n n ℂ) (hl : ∀ k, 0 < l k) :
    specPow W l 1 = W * diagonal (fun k ↦ (l k : ℂ)) * Wᴴ := by
  simp only [specPow, one_mul, ← ofReal_exp, Real.exp_log (hl _)]

theorem specPow_add (hW : Wᴴ * W = 1) (l : n → ℝ) (z w : ℂ) :
    specPow W l (z + w) = specPow W l z * specPow W l w := by
  simp only [specPow, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal]
  simp only [add_mul, exp_add]

theorem conjTranspose_specPow (W : Matrix n n ℂ) (l : n → ℝ) (z : ℂ) :
    (specPow W l z)ᴴ = specPow W l ((starRingEnd ℂ) z) := by
  simp only [specPow, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  simp [← exp_conj]

/-- The imaginary powers are unitary. -/
theorem specPow_mul_conjTranspose_I (hW : Wᴴ * W = 1) (l : n → ℝ) (y : ℝ) :
    specPow W l (y * I) * (specPow W l (y * I))ᴴ = 1 := by
  rw [conjTranspose_specPow, ← specPow_add hW, map_mul, conj_ofReal, conj_I, mul_neg,
    add_neg_cancel, specPow_zero hW]

/-- The complex power has derivative `W diag(log l · e^{z log l}) W*`. -/
theorem hasDerivAt_specPow (W : Matrix n n ℂ) (l : n → ℝ) (z : ℂ) :
    HasDerivAt (specPow W l)
      (W * diagonal (fun k ↦ (Real.log (l k) : ℂ) * exp (z * Real.log (l k))) * Wᴴ) z := by
  have hpi : HasDerivAt (fun z : ℂ ↦ fun k ↦ exp (z * Real.log (l k)))
      (fun k ↦ (Real.log (l k) : ℂ) * exp (z * Real.log (l k))) z :=
    hasDerivAt_pi.2 fun k ↦ (((hasDerivAt_id' z).mul_const _).cexp).congr_deriv (by ring)
  let Φ : (n → ℂ) →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun v ↦ W * diagonal v * Wᴴ
      map_add' := fun v w ↦ by
        rw [show diagonal (v + w) = diagonal v + diagonal w from (diagonal_add v w).symm,
          Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v ↦ by
        rw [RingHom.id_apply, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul] }
  exact (LinearMap.toContinuousLinearMap Φ).hasFDerivAt.comp_hasDerivAt z hpi

/-- On the strip `0 ≤ Re z ≤ 1` the complex powers are bounded by `exp ‖log l‖`. -/
theorem norm_specPow_le (hW : Wᴴ * W = 1) (l : n → ℝ) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1) : ‖specPow W l z‖ ≤ Real.exp ‖fun k ↦ Real.log (l k)‖ := by
  have hW1 := l2_opNorm_le_one_of_mul_conjTranspose (mul_eq_one_comm.1 hW)
  refine (l2_opNorm_mul _ _).trans <| (mul_le_mul_of_nonneg_left (l2_opNorm_conjTranspose W ▸ hW1)
    (norm_nonneg _)).trans ?_
  rw [mul_one]
  refine (l2_opNorm_mul _ _).trans <| (mul_le_mul_of_nonneg_right hW1 (norm_nonneg _)).trans ?_
  rw [one_mul, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2 fun k ↦ ?_
  rw [norm_exp, Real.exp_le_exp, re_mul_ofReal]
  have hk := norm_le_pi_norm (fun k ↦ Real.log (l k)) k
  rw [Real.norm_eq_abs] at hk
  nlinarith [le_abs_self (Real.log (l k)), neg_abs_le (Real.log (l k)), abs_nonneg (Real.log (l k))]

end Matrix
