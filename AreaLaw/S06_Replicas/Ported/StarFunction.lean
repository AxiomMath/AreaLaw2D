/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLaw.S06_Replicas.Ported.ReplicaMarkedRatio
import AreaLaw.S06_Replicas.Ported.UniformHusimi

/-!
# Polynomial approximation of functions of the star operator

Star spectra lie in `[-1, 1]`, so `‖φ(J_{Q,k}) - p(J_{Q,k})‖ ≤ sup_{[-1,1]} |φ - p|`.

Reference: OpenAI, *A two-dimensional area law from a global spectral gap*, Lemma 6.4,
`05-replicas.tex`, lines 693–702.
-/

open Matrix PermutationRepresentation Polynomial
open scoped Matrix.Norms.L2Operator

namespace Matrix.IsOrthogonalResolution

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  {P : ι → Matrix n n ℂ} (hP : IsOrthogonalResolution P)
include hP

/-- On a nonzero part, the coefficient is bounded by the norm of `∑_i c_i P_i`. -/
theorem norm_le_l2_opNorm_hom {c : ι → ℂ} {i : ι} (hi : P i ≠ 0) : ‖c i‖ ≤ ‖hP.hom c‖ := by
  have hmul : hP.hom c * P i = c i • P i := by
    rw [hom_apply, Finset.sum_mul, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, hP.mul_self]
    · intro j _ hj
      rw [smul_mul_assoc, hP.mul_of_ne hj, smul_zero]
    · simp
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hi)
  rw [← norm_smul, ← hmul]
  exact l2_opNorm_mul _ _

end Matrix.IsOrthogonalResolution

namespace TensorPower

variable {F : Type*} [DecidableEq F] [Fintype F] {ι : F → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-- The star operator has norm at most one. -/
theorem l2_opNorm_starOp_le {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (φ : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm X) : ‖starOp φ‖ ≤ 1 := by
  rw [starOp]
  refine (norm_smul_le _ _).trans ?_
  have hsum : ‖∑ j : Fin m, permOp φ (Equiv.swap (Fin.castSucc j) (Fin.last m))‖ ≤ m :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => Matrix.l2_opNorm_permOp_le _ _).trans
      (by simp))
  rw [norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ (by positivity)]
  push_cast
  linarith

/-- **Star spectra lie in `[-1, 1]`** (`05-replicas.tex`, line 697). -/
theorem abs_starValue_le_one (m : ℕ) (Q : Finset F)
    {p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m))}
    (hp : labelProj (subsystemPerm (m + 1) ι Q) p.1 *
      labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) p.2 ≠ 0) :
    |starValue p| ≤ 1 := by
  have h := (isOrthogonalResolution_branch (ι := ι) m Q).norm_le_l2_opNorm_hom
    (c := fun p => (starValue p : ℂ)) hp
  rw [← starOp_subsystemPerm_eq_hom, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (l2_opNorm_starOp_le _)

/-- `‖φ(J_{Q,k}) - p(J_{Q,k})‖ ≤ M` if `|φ - p| ≤ M` on `[-1, 1]`. -/
theorem l2_opNorm_cfc_starOp_sub_aeval_le (m : ℕ) (Q : Finset F) (φ : ℝ → ℝ) (p : ℝ[X])
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |φ x - p.eval x| ≤ M) :
    ‖cfc φ (starOp (subsystemPerm (m + 1) ι Q)) -
        aeval (starOp (subsystemPerm (m + 1) ι Q)) p‖ ≤ M := by
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  rw [starOp_subsystemPerm_eq_hom, hJ.cfc_hom (isHermitian_branch ι m Q), hJ.aeval_hom,
    ← map_sub]
  refine hJ.l2_opNorm_hom_le (isHermitian_branch ι m Q) hM0 fun q hq => ?_
  rw [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hM _ (abs_le.mp (abs_starValue_le_one m Q hq))

/-- If `|p| ≤ M` on `[-1, 1]`, then `‖p(J_{Q,k})‖ ≤ M`. -/
theorem l2_opNorm_aeval_starOp_le (m : ℕ) (Q : Finset F) (p : ℝ[X]) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    ‖aeval (starOp (subsystemPerm (m + 1) ι Q)) p‖ ≤ M := by
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  rw [starOp_subsystemPerm_eq_hom, hJ.aeval_hom]
  refine hJ.l2_opNorm_hom_le (isHermitian_branch ι m Q) hM0 fun q hq => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hM _ (abs_le.mp (abs_starValue_le_one m Q hq))

theorem isHermitian_aeval_starOp (m : ℕ) (Q : Finset F) (p : ℝ[X]) :
    (aeval (starOp (subsystemPerm (m + 1) ι Q)) p).IsHermitian := by
  rw [starOp_subsystemPerm_eq_hom, (isOrthogonalResolution_branch m Q).aeval_hom]
  exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch ι m Q) _

end TensorPower
