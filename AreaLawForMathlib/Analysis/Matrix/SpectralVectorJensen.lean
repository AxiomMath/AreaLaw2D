import AreaLawForMathlib.Analysis.Matrix.SpectralQuadraticForm
import AreaLawForMathlib.Analysis.Matrix.MatrixPowers
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Jensen inequalities for vector states of a positive definite matrix

Extends `AreaLawForMathlib/Analysis/Matrix/SpectralQuadraticForm.lean`: for a positive definite
matrix `M` and a unit vector `v`, the spectral measure of `M` in `v` gives
`⟨v, log M v⟩ ≤ log ⟨v, M v⟩` (concavity of `log`) and
`exp(-2s ⟨v, log M v⟩) ≤ ‖M^{-s} v‖²` (convexity of `exp`). Also Cauchy–Schwarz for
`star u ⬝ᵥ v` and its form with opposite powers of `M`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cauchy–Schwarz: `|⟨u, v⟩|² ≤ ‖u‖² ‖v‖²`. -/
theorem norm_star_dotProduct_sq_le (u v : n → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ n)
    (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
  have hn : ∀ w : n → ℂ, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ ^ 2 = (star w ⬝ᵥ w).re :=
    fun w => by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      rfl
  calc ‖star u ⬝ᵥ v‖ ^ 2 ≤ (‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [mul_pow, hn, hn]

variable {M : Matrix n n ℂ}

/-- `⟨M^r u, M^r u⟩ = ⟨u, M^{2r} u⟩`. -/
theorem PosDef.star_rpow_mulVec_dotProduct (hM : M.PosDef) (r : ℝ) (u : n → ℂ) :
    star (M ^ r *ᵥ u) ⬝ᵥ (M ^ r *ᵥ u) = star u ⬝ᵥ (M ^ (2 * r) *ᵥ u) := by
  rw [star_mulVec, ← dotProduct_mulVec, ← star_eq_conjTranspose, hM.star_rpow, mulVec_mulVec,
    hM.rpow_mul_rpow, two_mul]

/-- Cauchy–Schwarz with opposite powers: `|⟨u, x⟩|² ≤ ⟨u, M^{2s} u⟩ ‖M^{-s} x‖²`. -/
theorem PosDef.norm_star_dotProduct_sq_le_rpow (hM : M.PosDef) (s : ℝ) (u x : n → ℂ) :
    ‖star u ⬝ᵥ x‖ ^ 2 ≤
      (star u ⬝ᵥ (M ^ (2 * s) *ᵥ u)).re * (star (M ^ (-s) *ᵥ x) ⬝ᵥ (M ^ (-s) *ᵥ x)).re := by
  have h1 : star u ⬝ᵥ x = star (M ^ s *ᵥ u) ⬝ᵥ (M ^ (-s) *ᵥ x) := by
    rw [star_mulVec, ← dotProduct_mulVec, ← star_eq_conjTranspose, hM.star_rpow, mulVec_mulVec,
      hM.rpow_mul_rpow_neg, one_mulVec]
  rw [h1, ← hM.star_rpow_mulVec_dotProduct]
  exact norm_star_dotProduct_sq_le _ _

/-- Concavity of `log` on the spectral measure of `M` in a unit vector:
`⟨v, log M v⟩ ≤ log ⟨v, M v⟩`. -/
theorem PosDef.re_dotProduct_log_mulVec_le (hM : M.PosDef) {v : n → ℂ}
    (hv : star v ⬝ᵥ v = 1) :
    (star v ⬝ᵥ (CFC.log M *ᵥ v)).re ≤ Real.log (star v ⬝ᵥ (M *ᵥ v)).re := by
  have hH := hM.isHermitian
  rw [CFC.log, hH.cfc_eq, hH.re_dotProduct_cfc_mulVec_eq_sum, hH.re_dotProduct_mulVec_eq_sum]
  simpa [smul_eq_mul] using (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
    (t := Finset.univ) (fun i _ => hH.spectralWeight_nonneg v i) (hH.sum_spectralWeight hv)
    (fun i _ => hM.eigenvalues_pos i)

/-- Convexity of `exp` on the spectral measure of `M` in a unit vector:
`exp(-2s ⟨v, log M v⟩) ≤ ‖M^{-s} v‖²`. -/
theorem PosDef.exp_neg_two_mul_le_rpow (hM : M.PosDef) (s : ℝ) {v : n → ℂ}
    (hv : star v ⬝ᵥ v = 1) :
    Real.exp (-2 * s * (star v ⬝ᵥ (CFC.log M *ᵥ v)).re) ≤
      (star (M ^ (-s) *ᵥ v) ⬝ᵥ (M ^ (-s) *ᵥ v)).re := by
  have hH := hM.isHermitian
  rw [hM.star_rpow_mulVec_dotProduct, CFC.rpow_eq_cfc_real hM.posSemidef.nonneg, CFC.log,
    hH.cfc_eq, hH.cfc_eq, hH.re_dotProduct_cfc_mulVec_eq_sum, hH.re_dotProduct_cfc_mulVec_eq_sum,
    Finset.mul_sum]
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (fun i _ => hH.spectralWeight_nonneg v i) (hH.sum_spectralWeight hv)
    (p := fun i => -2 * s * Real.log (hH.eigenvalues i)) (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  refine le_of_eq_of_le (congrArg Real.exp (Finset.sum_congr rfl fun i _ => by ring)) (h.trans ?_)
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [Real.rpow_def_of_pos (hM.eigenvalues_pos i)]
  ring_nf

end Matrix
