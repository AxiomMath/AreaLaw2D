/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.Analysis.Matrix.WeightedGeometricMean
import AreaLawForMathlib.Analysis.Matrix.OrthogonalResolutionCfc
import AreaLawForMathlib.Analysis.Matrix.SpectralQuadraticForm
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operators that are scalar on the two ranges of an orthogonal projection

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`.

For an orthogonal projection `P` and reals `b, d`, the operator `b (1 - P) + d P` is the
scalar `b` on `ran (1 - P)` and `d` on `ran P`. Such operators multiply, take real powers and
functional calculus sectorwise, and their weighted geometric mean is sectorwise the weighted
geometric mean of the scalars.

Also: the exponential Jensen inequality `exp (r ⟨v, log M v⟩) ≤ ⟨v, M^r v⟩` for a positive
definite `M` and a unit vector `v`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}

/-- Sectorwise product. -/
theorem projSector_mul (hP : IsStarProjection P) (a b c d : ℝ) :
    (a • (1 - P) + b • P) * (c • (1 - P) + d • P) = (a * c) • (1 - P) + (b * d) • P := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hP.one_sub.isIdempotentElem.eq, hP.isIdempotentElem.eq, hP.mul_one_sub_self,
    hP.one_sub_mul_self, smul_zero, add_zero, zero_add]
  rw [mul_comm c a, mul_comm d b]

/-- Positive scalars on the two ranges give a positive definite operator. -/
theorem posDef_projSector (hP : IsStarProjection P) {b d : ℝ} (hb : 0 < b)
    (hd : 0 < d) : (b • (1 - P) + d • P).PosDef := by
  have hnonneg : 0 ≤ b • (1 - P) + d • P :=
    add_nonneg (smul_nonneg hb.le hP.one_sub.nonneg) (smul_nonneg hd.le hP.nonneg)
  refine (nonneg_iff_posSemidef.mp hnonneg).posDef_iff_isUnit.mpr ?_
  refine isUnit_iff_exists_inv.mpr ⟨b⁻¹ • (1 - P) + d⁻¹ • P, ?_⟩
  rw [projSector_mul hP, mul_inv_cancel₀ hb.ne', mul_inv_cancel₀ hd.ne', one_smul, one_smul,
    sub_add_cancel]

/-- Functional calculus acts by the scalar value on each range. -/
theorem cfc_projSector (hP : IsStarProjection P) (b d : ℝ) (f : ℝ → ℝ) :
    cfc f (b • (1 - P) + d • P) = f b • (1 - P) + f d • P := by
  let sectors : Bool → Matrix n n ℂ := fun j => if j then P else 1 - P
  have hres : IsOrthogonalResolution sectors := by
    constructor
    · intro i j
      cases i <;> cases j <;>
        simp only [sectors, Bool.false_eq_true, ite_true, ite_false,
          hP.isIdempotentElem.eq, hP.one_sub.isIdempotentElem.eq, hP.mul_one_sub_self,
          hP.one_sub_mul_self, reduceCtorEq]
    · simp only [Fintype.sum_bool, sectors, ite_true, Bool.false_eq_true, ite_false]
      rw [← add_sub_assoc, add_sub_cancel_left]
  have hH : ∀ j, (sectors j).IsHermitian :=
    fun j => Bool.rec hP.one_sub.isSelfAdjoint.isHermitian hP.isSelfAdjoint.isHermitian j
  have hcalc := hres.cfc_hom hH f (fun j => if j then d else b)
  have hop : hres.hom (fun j => ((if j then d else b : ℝ) : ℂ)) = b • (1 - P) + d • P := by
    simp only [IsOrthogonalResolution.hom_apply, Fintype.sum_bool, sectors, ite_true,
      Bool.false_eq_true, ite_false, Complex.coe_smul]
    abel
  rw [hop] at hcalc
  rw [hcalc]
  simp only [IsOrthogonalResolution.hom_apply, Fintype.sum_bool, sectors, ite_true,
    Bool.false_eq_true, ite_false, Complex.coe_smul]
  abel

/-- Real powers act by the scalar power on each range. -/
theorem projSector_rpow (hP : IsStarProjection P) {b d : ℝ} (hb : 0 < b)
    (hd : 0 < d) (r : ℝ) :
    (b • (1 - P) + d • P) ^ r = (b ^ r) • (1 - P) + (d ^ r) • P := by
  rw [CFC.rpow_eq_cfc_real (posDef_projSector hP hb hd).posSemidef.nonneg, cfc_projSector hP]

private theorem rpow_half_mul_whiten_rpow_mul_rpow_half {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (p : ℝ) :
    b ^ (1 / 2 : ℝ) * (b ^ (-(1 / 2) : ℝ) * c * b ^ (-(1 / 2) : ℝ)) ^ p * b ^ (1 / 2 : ℝ) =
      b ^ (1 - p) * c ^ p := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hc.le,
    ← Real.rpow_mul hb.le]
  have h : b ^ (1 - p) = b ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) * p) * b ^ (-(1 / 2) * p) *
      b ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hb, ← Real.rpow_add hb, ← Real.rpow_add hb]
    ring_nf
  rw [h]
  ring

/-- The weighted geometric mean of two sector operators is sectorwise the weighted geometric
mean of the scalars. -/
theorem geomMean_projSector (hP : IsStarProjection P) {b d b' d' : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d') (p : ℝ) :
    geomMean p (b • (1 - P) + d • P) (b' • (1 - P) + d' • P) =
      (b ^ (1 - p) * b' ^ p) • (1 - P) + (d ^ (1 - p) * d' ^ p) • P := by
  have hw : (b • (1 - P) + d • P) ^ (-(1 / 2) : ℝ) * (b' • (1 - P) + d' • P) *
      (b • (1 - P) + d • P) ^ (-(1 / 2) : ℝ) =
      (b ^ (-(1 / 2) : ℝ) * b' * b ^ (-(1 / 2) : ℝ)) • (1 - P) +
        (d ^ (-(1 / 2) : ℝ) * d' * d ^ (-(1 / 2) : ℝ)) • P := by
    rw [projSector_rpow hP hb hd, projSector_mul hP, projSector_mul hP]
  rw [geomMean, hw, projSector_rpow hP hb hd, projSector_rpow hP (by positivity) (by positivity),
    projSector_mul hP, projSector_mul hP, rpow_half_mul_whiten_rpow_mul_rpow_half hb hb',
    rpow_half_mul_whiten_rpow_mul_rpow_half hd hd']

/-- **Exponential Jensen.** For positive definite `M`, a unit vector `v` and a real `r`:
`exp (r ⟨v, log M v⟩) ≤ ⟨v, M^r v⟩`. -/
theorem PosDef.exp_mul_re_dotProduct_log_le {M : Matrix n n ℂ} (hM : M.PosDef) (r : ℝ)
    {v : n → ℂ} (hv : star v ⬝ᵥ v = 1) :
    Real.exp (r * (star v ⬝ᵥ (CFC.log M *ᵥ v)).re) ≤ (star v ⬝ᵥ (M ^ r *ᵥ v)).re := by
  have hH := hM.isHermitian
  have hlog : (star v ⬝ᵥ (CFC.log M *ᵥ v)).re =
      ∑ i, hH.spectralWeight v i * Real.log (hH.eigenvalues i) := by
    rw [CFC.log, hH.cfc_eq, hH.re_dotProduct_cfc_mulVec_eq_sum]
  have hpow : (star v ⬝ᵥ (M ^ r *ᵥ v)).re =
      ∑ i, hH.spectralWeight v i * hH.eigenvalues i ^ r := by
    rw [CFC.rpow_eq_cfc_real hM.posSemidef.nonneg, hH.cfc_eq,
      hH.re_dotProduct_cfc_mulVec_eq_sum]
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := hH.spectralWeight v)
    (p := fun i => r * Real.log (hH.eigenvalues i))
    (fun i _ => hH.spectralWeight_nonneg v i) (hH.sum_spectralWeight hv)
    (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  rw [hlog, hpow, Finset.mul_sum]
  calc Real.exp (∑ i, r * (hH.spectralWeight v i * Real.log (hH.eigenvalues i)))
      = Real.exp (∑ i, hH.spectralWeight v i * (r * Real.log (hH.eigenvalues i))) := by
        congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i, hH.spectralWeight v i * Real.exp (r * Real.log (hH.eigenvalues i)) := hj
    _ = ∑ i, hH.spectralWeight v i * hH.eigenvalues i ^ r := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.rpow_def_of_pos (hM.eigenvalues_pos i), mul_comm (Real.log _) r]

end Matrix
