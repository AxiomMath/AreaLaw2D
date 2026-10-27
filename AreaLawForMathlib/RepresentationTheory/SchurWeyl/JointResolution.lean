/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import AreaLawForMathlib.Analysis.Matrix.PosSemidefSupport
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.CommutantDimension

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The joint resolution of a permutation-invariant matrix and the label projectors

Extends `Mathlib/Analysis/Matrix/Spectrum.lean`.

For a positive semidefinite `ρ` commuting with a permutation representation, the spectral
projectors of `ρ` and the label projectors form one orthogonal resolution `E_u π^λ`.

Ported from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
`QICLean/Representation/SchurSurprisal.lean`.
-/

open MonoidAlgebra Matrix Module
open scoped ComplexOrder MatrixOrder

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  (φ : G →* Equiv.Perm X)

/-- The label projectors form an orthogonal resolution of the identity. -/
theorem isOrthogonalResolution_labelProj :
    IsOrthogonalResolution fun l : IrrepLabel G => labelProj φ l where
  mul_eq := labelProj_mul_labelProj φ
  sum_eq := sum_labelProj φ

theorem labelObservable_eq_hom (f : IrrepLabel G → ℝ) :
    labelObservable φ f = (isOrthogonalResolution_labelProj φ).hom fun l => (f l : ℂ) := by
  rw [IsOrthogonalResolution.hom_apply, labelObservable]

variable {φ} {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) (hinv : ∀ g, Commute (permOp φ g) ρ)
include hρ hinv

theorem commute_spectralProj_labelProj (u : ℝ) (l : IrrepLabel G) :
    Commute (hρ.isHermitian.spectralProj u) (labelProj φ l) :=
  hρ.isHermitian.commute_spectralProj (commute_labelProj_of_forall_commute φ hinv l).symm u

/-- The joint resolution `E_u π^λ` of a permutation-invariant positive semidefinite
matrix and the label projectors. -/
theorem isOrthogonalResolution_joint :
    IsOrthogonalResolution fun p : hρ.isHermitian.eigenvalueSet × IrrepLabel G =>
      hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 :=
  hρ.isHermitian.isOrthogonalResolution_spectralProj.prod (isOrthogonalResolution_labelProj φ)
    fun u l => commute_spectralProj_labelProj hρ hinv u l

/-- The joint projections are Hermitian. -/
theorem isHermitian_joint (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2).IsHermitian := by
  rw [IsHermitian, conjTranspose_mul, (isHermitian_labelProj φ p.2).eq,
    (hρ.isHermitian.isHermitian_spectralProj p.1).eq]
  exact (commute_spectralProj_labelProj hρ hinv p.1 p.2).eq.symm

/-- Functions of the eigenvalue factor of the joint resolution. -/
theorem joint_hom_fst (f : ℝ → ℝ) :
    (isOrthogonalResolution_joint hρ hinv).hom (fun p => (f p.1 : ℂ)) = hρ.isHermitian.cfc f := by
  rw [hρ.isHermitian.cfc_eq_hom, IsOrthogonalResolution.hom_apply,
    IsOrthogonalResolution.hom_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  dsimp only
  rw [← Finset.smul_sum, ← Finset.mul_sum, sum_labelProj, mul_one]

/-- Functions of the label factor of the joint resolution. -/
theorem joint_hom_snd (f : IrrepLabel G → ℝ) :
    (isOrthogonalResolution_joint hρ hinv).hom (fun p => (f p.2 : ℂ)) = labelObservable φ f := by
  rw [labelObservable, IsOrthogonalResolution.hom_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp_rw [← Finset.smul_sum, ← Finset.sum_mul,
    hρ.isHermitian.isOrthogonalResolution_spectralProj.sum_eq,
    one_mul]

/-- The trace of a joint projection is the dimension of its range. -/
theorem trace_joint (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2).trace =
      finrank ℂ (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2))) :=
  trace_eq_finrank_range_of_mul_self ((isOrthogonalResolution_joint hρ hinv).mul_self p)

omit [Fintype G] hinv in
theorem eigenvalue_nonneg (u : hρ.isHermitian.eigenvalueSet) : 0 ≤ (u : ℝ) := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp u.2
  rw [← hi]
  exact hρ.eigenvalues_nonneg i

/-- **Eigenvalue repetition** (`05-replicas.tex`, lines 223–226). If `tr ρ = 1` and the
eigenvalue `u` of `ρ` occurs in the `λ`-isotypic component, then `u d_λ ≤ 1`. -/
theorem mul_dim_le_one_of_ne_zero (htr : ρ.trace = 1)
    (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G)
    (hp : hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 ≠ 0) :
    (p.1 : ℝ) * p.2.dim ≤ 1 := by
  set R := isOrthogonalResolution_joint hρ hinv
  set n : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℕ := fun p => finrank ℂ
    (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2)))
  have hdim : p.2.dim ≤ n p := by
    have hPg : ∀ g, Commute (permOp φ g)
        (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2) := fun g =>
      (((hρ.isHermitian.commute_spectralProj (hinv g).symm p.1).symm).mul_right
        (commute_labelProj_permOp φ p.2 g).symm)
    refine dim_le_finrank_of_invariant φ p.2 (fun g w hw => ?_) (fun w hw => ?_) ?_
    · obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
      exact LinearMap.mem_range.mpr ⟨permOp φ g *ᵥ v, by
        simp only [toLin'_apply, mulVec_mulVec, (hPg g).eq]⟩
    · obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
      simp only [toLin'_apply, mulVec_mulVec]
      rw [← mul_assoc, ← (commute_spectralProj_labelProj hρ hinv p.1 p.2).eq, mul_assoc,
        labelProj_mul_self, (commute_spectralProj_labelProj hρ hinv p.1 p.2).eq]
    · rwa [Ne, LinearMap.range_eq_bot, ← map_zero toLin', toLin'.injective.eq_iff]
  have htrace : ∑ q, (q.1 : ℝ) * n q = 1 := by
    have h1 : ρ = R.hom fun q => ((q.1 : ℝ) : ℂ) := by
      simpa [Matrix.IsHermitian.cfc_id] using (joint_hom_fst hρ hinv id).symm
    have h2 := congrArg Matrix.trace h1
    rw [htr, IsOrthogonalResolution.trace_hom] at h2
    simp_rw [trace_joint hρ hinv] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.one_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero] at h3
    exact h3.symm
  calc (p.1 : ℝ) * p.2.dim ≤ (p.1 : ℝ) * n p :=
        mul_le_mul_of_nonneg_left (mod_cast hdim) (eigenvalue_nonneg hρ p.1)
    _ ≤ 1 := htrace ▸ Finset.single_le_sum (f := fun q => (q.1 : ℝ) * n q)
      (fun q _ => mul_nonneg (eigenvalue_nonneg hρ q.1) (Nat.cast_nonneg _)) (Finset.mem_univ p)

end PermutationRepresentation
