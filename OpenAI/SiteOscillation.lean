/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/Circuit/SiteOscillation.lean` (Apache 2.0).  Adaptations: the sites are a region
`T : Finset σ` with local family `loc` instead of `ι → Fin q`; `U ∈ supportedOperators q {y}`
is `OpenAI.IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U`, which makes the
oscillation total in `y : σ`; the field is a general `RCLike 𝕜` instead of `ℂ`.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import OpenAI.Bridges
import OpenAI.RegionLift

/-!
# Site oscillation with a finite spectator

For an operator `B` on the sites `T` and a finite spectator `Aux`, its oscillation at the site
`y` is `d_y(B) = sup_U ‖(U ⊗ 1) B - B (U ⊗ 1)‖`, the supremum over the unitaries `U` on `T`
supported on `{y} ∩ T` [OAI265, §10.1, the oscillation defined before eq. (10.8)].  The norm is
the matrix operator norm.  Operators need not be Hermitian, and the spectator has arbitrary
finite dimension.

The defining set contains `0` (take `U = 1`) and is bounded by `2 ‖B‖`.  Hence `d_y` bounds every
admissible commutator, is subadditive and absolutely homogeneous, and vanishes on operators
commuting with the operators at `y`; all of this holds uniformly in the spectator dimension.

## Implementation notes

The unitaries at `y` are those supported on `{y} ∩ T`, not on `{y}`: then `siteOscillation y B`
is defined for every `y : σ`, and vanishes for `y ∉ T`, so sums over finite sets of sites need no
membership proofs.  For `y ∈ T` the two supports agree (`isSupportedOn_singleton_inter_iff`).
-/

namespace OpenAI

open Arealaw Matrix
open scoped Kronecker Matrix.Norms.L2Operator

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux] {𝕜 : Type*} [RCLike 𝕜]

omit [∀ i, Fintype (loc i)] in
/-- For a site `y ∈ T`, support on `{y} ∩ T` is support on `{y}`. -/
theorem isSupportedOn_singleton_inter_iff {y : σ} (hy : y ∈ T)
    {U : Matrix (Reg loc T) (Reg loc T) 𝕜} :
    IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U ↔
      IsSupportedOn (Finset.singleton_subset_iff.2 hy) U :=
  ⟨fun hU => hU.mono Finset.inter_subset_left _,
    fun hU => hU.mono
      (Finset.singleton_subset_iff.2 (Finset.mem_inter.2 ⟨Finset.mem_singleton_self y, hy⟩)) _⟩

/-- The oscillation `d_y(B)` of an operator on the sites `T` and a finite spectator `Aux` at the
site `y`: the supremum of `‖(U ⊗ 1) B - B (U ⊗ 1)‖` over the unitaries `U` at `y`
[OAI265, §10.1, before eq. (10.8)]. -/
noncomputable def siteOscillation (y : σ) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    ℝ :=
  sSup {r | ∃ U : Matrix (Reg loc T) (Reg loc T) 𝕜,
    IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U ∧
    U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜) ∧
    ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ = r}

private theorem norm_siteUnitary_commutator_le
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    {U : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hU : U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜)) :
    ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ ≤ 2 * ‖B‖ := by
  have hUA := Matrix.kronecker_mem_unitary hU
    (show (1 : Matrix Aux Aux 𝕜) ∈ unitary _ from one_mem _)
  calc
    _ ≤ ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B‖ + ‖B * (U ⊗ₖ 1)‖ := norm_sub_le _ _
    _ = ‖B‖ + ‖B‖ := by
      rw [CStarRing.norm_mem_unitary_mul B hUA, CStarRing.norm_mul_mem_unitary B hUA]
    _ = 2 * ‖B‖ := (two_mul _).symm

/-- The set defining the oscillation is bounded above, uniformly in `Aux`
[OAI265, §10.1, `d_y(C) ≤ 2‖C‖` before eq. (10.9)]. -/
theorem siteOscillation_bddAbove (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    BddAbove {r | ∃ U : Matrix (Reg loc T) (Reg loc T) 𝕜,
      IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U ∧
      U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜) ∧
      ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ = r} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro _ ⟨U, _, hU, rfl⟩
  exact norm_siteUnitary_commutator_le B hU

private theorem zero_mem_siteOscillation_values (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    0 ∈ {r | ∃ U : Matrix (Reg loc T) (Reg loc T) 𝕜,
      IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U ∧
      U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜) ∧
      ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ = r} :=
  ⟨1, isSupportedOn_one _, one_mem _, by simp⟩

/-- The commutator with a unitary at `y` is bounded by the oscillation
[OAI265, §10.1, before eq. (10.8)]. -/
theorem norm_commutator_le_siteOscillation (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    {U : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hSupport : IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U)
    (hUnitary : U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜)) :
    ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ ≤ siteOscillation y B :=
  le_csSup (siteOscillation_bddAbove y B) ⟨U, hSupport, hUnitary, rfl⟩

/-- `norm_commutator_le_siteOscillation` with the commutator written the other way round. -/
theorem norm_commutator_le_siteOscillation_right (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    {U : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hSupport : IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U)
    (hUnitary : U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜)) :
    ‖B * (U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) - (U ⊗ₖ 1) * B‖ ≤ siteOscillation y B := by
  rw [norm_sub_rev]
  exact norm_commutator_le_siteOscillation y B hSupport hUnitary

theorem siteOscillation_nonneg (y : σ) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    0 ≤ siteOscillation y B :=
  le_csSup (siteOscillation_bddAbove y B) (zero_mem_siteOscillation_values y B)

/-- A common bound on the commutators with the unitaries at `y` bounds the oscillation. -/
theorem siteOscillation_le (y : σ) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) {r : ℝ}
    (h : ∀ U : Matrix (Reg loc T) (Reg loc T) 𝕜,
      IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U →
      U ∈ unitary (Matrix (Reg loc T) (Reg loc T) 𝕜) →
      ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ ≤ r) :
    siteOscillation y B ≤ r := by
  refine csSup_le ⟨0, zero_mem_siteOscillation_values y B⟩ ?_
  rintro _ ⟨U, hSupport, hUnitary, rfl⟩
  exact h U hSupport hUnitary

/-- `d_y(B) ≤ 2 ‖B‖`, with no spectator dimension factor
[OAI265, §10.1, before eq. (10.9)]. -/
theorem siteOscillation_le_two_mul_norm (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y B ≤ 2 * ‖B‖ :=
  siteOscillation_le y B fun _ _ hU => norm_siteUnitary_commutator_le B hU

/-- The oscillation is subadditive [OAI265, §10.1, proof of eq. (10.9)]. -/
theorem siteOscillation_add_le (y : σ) (B C : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y (B + C) ≤ siteOscillation y B + siteOscillation y C := by
  apply siteOscillation_le
  intro U hSupport hUnitary
  calc
    _ = ‖((U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)) +
        ((U ⊗ₖ 1) * C - C * (U ⊗ₖ 1))‖ := by
      rw [mul_add, add_mul, add_sub_add_comm]
    _ ≤ ‖(U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B - B * (U ⊗ₖ 1)‖ +
        ‖(U ⊗ₖ 1) * C - C * (U ⊗ₖ 1)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_commutator_le_siteOscillation y B hSupport hUnitary)
      (norm_commutator_le_siteOscillation y C hSupport hUnitary)

/-- The oscillation vanishes on operators commuting with every operator at `y`. -/
theorem siteOscillation_eq_zero_of_commute (y : σ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    (h : ∀ U : Matrix (Reg loc T) (Reg loc T) 𝕜,
      IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U →
      Commute (U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) B) :
    siteOscillation y B = 0 := by
  apply le_antisymm _ (siteOscillation_nonneg y B)
  apply siteOscillation_le
  intro U hSupport _
  simp [(h U hSupport).eq]

@[simp]
theorem siteOscillation_zero (y : σ) :
    siteOscillation y (0 : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) = 0 :=
  siteOscillation_eq_zero_of_commute y 0 fun _ _ => Commute.zero_right _

/-- An operator acting only on the spectator has zero oscillation at every site. -/
@[simp]
theorem siteOscillation_one_kronecker (y : σ) (C : Matrix Aux Aux 𝕜) :
    siteOscillation (T := T) y ((1 : Matrix (Reg loc T) (Reg loc T) 𝕜) ⊗ₖ C) = 0 := by
  apply siteOscillation_eq_zero_of_commute
  intro U _
  change (U ⊗ₖ 1) * (1 ⊗ₖ C) = (1 ⊗ₖ C) * (U ⊗ₖ 1)
  simp only [← Matrix.mul_kronecker_mul, mul_one, one_mul]

/-- Outside the region the oscillation vanishes: the only operators supported on `∅` are the
scalars. -/
theorem siteOscillation_of_notMem {y : σ} (hy : y ∉ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) : siteOscillation y B = 0 := by
  refine siteOscillation_eq_zero_of_commute y B fun U hU => ?_
  obtain ⟨U', rfl⟩ := hU
  have hne (i : ({y} ∩ T : Finset σ)) : False := by
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 i.2
    exact hy (Finset.mem_singleton.1 h1 ▸ h2)
  have e : Reg loc ({y} ∩ T) := fun i => (hne i).elim
  have : Subsingleton (Reg loc ({y} ∩ T)) := ⟨fun u v => funext fun i => (hne i).elim⟩
  have hc : U' = U' e e • (1 : Matrix (Reg loc ({y} ∩ T)) (Reg loc ({y} ∩ T)) 𝕜) := by
    ext u v
    rw [Subsingleton.elim u e, Subsingleton.elim v e]
    simp
  rw [hc, extendId_smul, extendId_one, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  exact (Commute.one_left B).smul_left _

private theorem siteOscillation_smul_le (y : σ) (c : 𝕜)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y (c • B) ≤ ‖c‖ * siteOscillation y B := by
  apply siteOscillation_le
  intro U hSupport hUnitary
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_commutator_le_siteOscillation y B hSupport hUnitary) (norm_nonneg c)

/-- The oscillation is absolutely homogeneous. -/
@[simp]
theorem siteOscillation_smul (y : σ) (c : 𝕜)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y (c • B) = ‖c‖ * siteOscillation y B := by
  by_cases hc : c = 0
  · simp [hc]
  apply le_antisymm (siteOscillation_smul_le y c B)
  have h := siteOscillation_smul_le y c⁻¹ (c • B)
  rw [inv_smul_smul₀ hc, norm_inv] at h
  have hcNorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  simpa only [← mul_assoc, mul_inv_cancel₀ hcNorm, one_mul] using
    mul_le_mul_of_nonneg_left h (norm_nonneg c)

@[simp]
theorem siteOscillation_neg (y : σ) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y (-B) = siteOscillation y B := by
  simpa using siteOscillation_smul y (-1 : 𝕜) B

theorem siteOscillation_sub_le (y : σ) (B C : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y (B - C) ≤ siteOscillation y B + siteOscillation y C := by
  simpa only [sub_eq_add_neg, siteOscillation_neg] using siteOscillation_add_le y B (-C)

theorem siteOscillation_sum_le {κ : Type*} (y : σ) (s : Finset κ)
    (B : κ → Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    siteOscillation y (∑ k ∈ s, B k) ≤ ∑ k ∈ s, siteOscillation y (B k) := by
  apply siteOscillation_le
  intro U hSupport hUnitary
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ =>
    norm_commutator_le_siteOscillation y (B k) hSupport hUnitary

end OpenAI
