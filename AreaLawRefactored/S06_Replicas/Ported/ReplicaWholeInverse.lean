/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawRefactored.S06_Replicas.Ported.ReplicaSimilarity

/-!
# Whole-space comparison for the inverse replica metric

For pairwise disjoint `P, Y, F`, `((W_P⁻¹ W_F⁻¹ W_Y)²)⁻¹` is bounded by a polynomial in the
number of copies times `exp(-2t(F_P + F_F - F_Y))` (`05-replicas.tex`, lines 287–316;
`07-comparators.tex`, lines 454–476).
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
  [∀ v, Nonempty (ι v)]

/-- A uniform upper bound for the inverse of the squared replica-metric product. -/
theorem exists_replicaMetric_inv_square_le_exp {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      let W := replicaMetric ι t k
      let L := fun S => labelEntropy (subsystemPerm k ι S)
      (((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2)⁻¹ ≤
        (((((k : ℝ) + 2) ^ C : ℝ) : ℂ)) •
          NormedSpace.exp (((-(2 * t) : ℝ) : ℂ) • (L P + L F - L Y)) := by
  classical
  obtain ⟨C₀, hC₀, hweight⟩ := exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨6 * C₀, by positivity, fun k P Y F hPY hdisPF hYF => ?_⟩
  dsimp only
  let hP := isOrthogonalResolution_labelProj (subsystemPerm k ι P)
  let hF := isOrthogonalResolution_labelProj (subsystemPerm k ι F)
  let hY := isOrthogonalResolution_labelProj (subsystemPerm k ι Y)
  let hPF := hP.prod hF (fun α β =>
    commute_labelProj_subsystemPerm_of_disjoint ι k hdisPF α β)
  let R := hPF.prod hY (fun ab γ =>
    (commute_labelProj_subsystemPerm_of_disjoint ι k hPY ab.1 γ).mul_left
      (commute_labelProj_subsystemPerm_of_disjoint ι k hYF.symm ab.2 γ))
  have hRP (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.1) = hP.hom f :=
    (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_fst hF hPF f)
  have hRF (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.2) = hF.hom f :=
    (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_snd hF hPF f)
  have hRY (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.2) = hY.hom f :=
    hPF.prod_hom_snd hY R f
  let w := replicaLabelWeight ι t (k := k)
  have hw (l : IrrepLabel (Equiv.Perm (Fin k))) : 0 < w l :=
    replicaLabelWeight_pos ι ht.le l
  have hWP : (replicaMetric ι t k P)⁻¹ =
      R.hom (fun p => (((w p.1.1)⁻¹ : ℝ) : ℂ)) := by
    rw [replicaMetric, labelObservable_inv _ (fun l => (hw l).ne')]
    simpa only [labelObservable_eq_hom] using
      (hRP (fun l => (((w l)⁻¹ : ℝ) : ℂ))).symm
  have hWF : (replicaMetric ι t k F)⁻¹ =
      R.hom (fun p => (((w p.1.2)⁻¹ : ℝ) : ℂ)) := by
    rw [replicaMetric, labelObservable_inv _ (fun l => (hw l).ne')]
    simpa only [labelObservable_eq_hom] using
      (hRF (fun l => (((w l)⁻¹ : ℝ) : ℂ))).symm
  have hWY : replicaMetric ι t k Y = R.hom (fun p => (w p.2 : ℂ)) := by
    simpa only [replicaMetric, labelObservable_eq_hom] using
      (hRY (fun l => (w l : ℂ))).symm
  let q : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => (w p.1.1 * w p.1.2 / w p.2) ^ 2
  have hInv : (((replicaMetric ι t k P)⁻¹ * (replicaMetric ι t k F)⁻¹ *
      replicaMetric ι t k Y) ^ 2)⁻¹ = R.hom (fun p => (q p : ℂ)) := by
    apply Matrix.inv_eq_left_inv
    rw [hWP, hWF, hWY, ← map_mul, ← map_mul, ← map_pow, ← map_mul, ← map_one R.hom]
    congr 1
    ext p
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.one_apply]
    norm_cast
    dsimp only [q]
    field_simp [(hw p.1.1).ne', (hw p.1.2).ne', (hw p.2).ne']
  let g : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim
  have hG : labelEntropy (subsystemPerm k ι P) + labelEntropy (subsystemPerm k ι F) -
      labelEntropy (subsystemPerm k ι Y) = R.hom (fun p => (g p : ℂ)) := by
    simp only [labelEntropy, labelObservable_eq_hom]
    rw [← hRP, ← hRF, ← hRY, ← map_add, ← map_sub]
    congr 1
    ext p
    simp [g]
  have hExp : NormedSpace.exp (((-(2 * t) : ℝ) : ℂ) •
      (labelEntropy (subsystemPerm k ι P) + labelEntropy (subsystemPerm k ι F) -
        labelEntropy (subsystemPerm k ι Y))) =
      R.hom (fun p => (Real.exp (-(2 * t) * g p) : ℂ)) := by
    rw [hG, ← map_smul, R.exp_hom]
    simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_exp]
  have hHerm (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k))) :
      (labelProj (subsystemPerm k ι P) p.1.1 * labelProj (subsystemPerm k ι F) p.1.2 *
        labelProj (subsystemPerm k ι Y) p.2).IsHermitian :=
    ((((isHermitian_labelProj _ p.1.1).commute_iff
      (isHermitian_labelProj _ p.1.2)).mp
        (commute_labelProj_subsystemPerm_of_disjoint ι k hdisPF p.1.1 p.1.2)).commute_iff
          (isHermitian_labelProj _ p.2)).mp
            ((commute_labelProj_subsystemPerm_of_disjoint ι k hPY p.1.1 p.2).mul_left
              (commute_labelProj_subsystemPerm_of_disjoint ι k hYF.symm p.1.2 p.2))
  have hcoef (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k)))
      (hp : labelProj (subsystemPerm k ι P) p.1.1 *
        labelProj (subsystemPerm k ι F) p.1.2 * labelProj (subsystemPerm k ι Y) p.2 ≠ 0) :
      q p ≤ ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (-(2 * t) * g p) := by
    have hPn : labelProj (subsystemPerm k ι P) p.1.1 ≠ 0 := fun hz =>
      hp (by simp only [hz, zero_mul])
    have hFn : labelProj (subsystemPerm k ι F) p.1.2 ≠ 0 := fun hz =>
      hp (by simp only [hz, mul_zero, zero_mul])
    have hYn : labelProj (subsystemPerm k ι Y) p.2 ≠ 0 := fun hz =>
      hp (by simp only [hz, mul_zero])
    have heP := (abs_le.mp (hweight k P p.1.1 hPn)).2
    have heF := (abs_le.mp (hweight k F p.1.2 hFn)).2
    have heY := (abs_le.mp (hweight k Y p.2 hYn)).1
    have hqpos : 0 < q p :=
      pow_pos (div_pos (mul_pos (hw p.1.1) (hw p.1.2)) (hw p.2)) 2
    have hlog : Real.log (q p) ≤ 6 * C₀ * Real.log ((k : ℝ) + 2) -
        (2 * t) * g p := by
      simp only [q, g, Real.log_pow,
        Real.log_div (mul_pos (hw p.1.1) (hw p.1.2)).ne' (hw p.2).ne',
        Real.log_mul (hw p.1.1).ne' (hw p.1.2).ne']
      dsimp only [w]
      norm_num only
      linarith only [heP, heF, heY]
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_log hqpos]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [hInv, hExp, ← sub_nonneg, ← map_smul, ← map_sub]
  convert (R.posSemidef_hom_of_ne_zero hHerm
    (f := fun p => ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (-(2 * t) * g p) - q p)
    (fun p hp => sub_nonneg.mpr (hcoef p hp))).nonneg using 2
  ext p
  simp

end TensorPower
