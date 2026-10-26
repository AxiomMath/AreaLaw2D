import AreaLawForMathlib.Analysis.Matrix.FilteredNorm
import AreaLawForMathlib.Analysis.Matrix.MatrixPowers
import AreaLawForMathlib.Analysis.Matrix.PosDefInverseOrder

/-!
# A floor bounds the filtered norm

Extends `AreaLawForMathlib/Analysis/Matrix/FilteredNorm.lean` (and Mathlib's
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean`): if a positive
definite `M` has the floor `c • 1 ≤ M`, `c > 0`, then `‖M^{-1/4} v‖² ≤ c^{-1/2} ‖v‖²`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.Transport

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem smul_one_inv {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Matrix n n ℂ))⁻¹ = c⁻¹ • (1 : Matrix n n ℂ) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hc, one_smul]

/-- A floor `c • 1 ≤ M` gives `‖M^{-1/4} v‖² ≤ c^{-1/2} ‖v‖²`. -/
theorem filteredNormSq_le_of_smul_one_le {M : Matrix n n ℂ} (hM : M.PosDef) {c : ℝ}
    (hc : 0 < c) (hcM : c • (1 : Matrix n n ℂ) ≤ M) (pre : n → ℂ) :
    filteredNormSq M pre ≤ (c ^ (1 / 2 : ℝ))⁻¹ * (star pre ⬝ᵥ pre).re := by
  have hc2 : 0 < c ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc _
  have hsq : (c • (1 : Matrix n n ℂ)) ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) :=
    CFC.rpow_le_rpow ⟨by norm_num, by norm_num⟩ hcM
  rw [PosDef.smul_rpow PosDef.one hc, CFC.one_rpow] at hsq
  have hinv := PosDef.inv_le_inv_of_le (PosDef.one.smul hc2) (hM.rpow (1 / 2)) hsq
  rw [smul_one_inv hc2.ne',
    Matrix.inv_eq_left_inv (hM.rpow_neg_mul_rpow (1 / 2 : ℝ))] at hinv
  rw [filteredNormSq_eq hM]
  have h := (Matrix.le_iff.1 hinv).re_dotProduct_nonneg pre
  rw [Matrix.sub_mulVec, dotProduct_sub, RCLike.re_to_complex, Complex.sub_re,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, Complex.real_smul,
    Complex.re_ofReal_mul] at h
  linarith

end Matrix.Transport
