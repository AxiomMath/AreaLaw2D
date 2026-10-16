/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
TNLean/PEPS/AreaLaw/PositiveConstraints.lean. Apache 2.0; adapted to the frozen
`OpenAI.PositiveReplacement`, `OpenAI.IsSupportedOn`, and `OpenAI.condExpect` interfaces.
-/
import OpenAI.LiebRobinson.ComponentLocality
import OpenAI.LiebRobinson.HamiltonianLocalization
import OpenAI.SpectralFilter.FilterLocality

/-!
# Positive quasi-local constraints

This module assembles the complex-field positive spectral constraints, their graph-ball
conditional-expectation tails, and their exact connected-component support.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix SimpleGraph
open SpectralFilter

/-- If every evolved operator commutes with `B`, then its spectral-filter integral commutes
with `B`. -/
theorem commute_filterIntegral_of_forall_commute {p : ℕ} (hp : 1 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) {n : Type*} [Fintype n] [DecidableEq n]
    {H A B : Matrix n n ℂ} (hH : H.IsHermitian)
    (h : ∀ t : ℝ, Commute (hermitianUnitaryPath H t * A *
      hermitianUnitaryPath H (-t)) B) :
    Commute (filterIntegral p δ H A) B := by
  let Ψ : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
    (ContinuousLinearMap.mul ℂ _).flip B - ContinuousLinearMap.mul ℂ _ B
  have hΨ : ∀ M, Ψ M = M * B - B * M := fun M => rfl
  have h0 : Ψ (filterIntegral p δ H A) = 0 := by
    rw [filterIntegral, ← Ψ.integral_comp_comm (integrable_filterIntegrand hp hδ hH A)]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans
      (integral_zero ℝ _)
    change Ψ ((spectralKernel p δ t : ℂ) • _) = 0
    rw [map_smul, hΨ, (h t).eq, sub_self, smul_zero]
  rw [hΨ, sub_eq_zero] at h0
  exact h0

/-- The absolute value of a Hermitian matrix commuting with `B` also commutes with `B`. -/
theorem _root_.Commute.cfcAbs_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : Commute A B) (hA : A.IsHermitian) :
    Commute (CFC.abs A) B := by
  rw [CFC.abs_eq_cfc_norm A hA.isSelfAdjoint]
  exact h.cfc_real _

/-- A positive spectral constraint is supported on the connected component of the anchor of
its Hamiltonian term. -/
theorem positiveConstraint_isSupportedOn_domainComponent {p q R : ℕ} (hp : 1 ≤ p)
    {δ J : ℝ} (hδ : 0 < δ) (hq : 1 ≤ q) {Λ : Finset (ℤ × ℤ)}
    {Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ}
    (hΦ : IsAdmissible Λ R J Φ)
    (anchor : Finset (ℤ × ℤ) → ℤ × ℤ)
    (hanchor : ∀ Y ∈ supports Λ R, anchor Y ∈ Y)
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (c : ℝ) (X : supports Λ R) :
    IsSupportedOn (domainComponent_subset Λ (anchor X.1))
      (positiveConstraint c (centeredFilter p δ (hamiltonian Λ Φ) Ω
        (extendId (subset_of_mem_supports X.2) (Φ X)))) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let G := (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))
  let C := domainComponent Λ (anchor X.1)
  let D := Λ \ C
  let term : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun Y => extendId (subset_of_mem_supports Y.2) (Φ Y)
  have hroot : anchor X.1 ∈ Λ :=
    subset_of_mem_supports X.2 (hanchor X.1 X.2)
  have hmemC (z : ℤ × ℤ) (hz : z ∈ Λ) :
      z ∈ C ↔ G.Reachable ⟨anchor X.1, hroot⟩ ⟨z, hz⟩ := by
    simp only [C, domainComponent, Finset.mem_filter, hz, true_and]
    rw [domainEDist_of_mem hroot hz, SimpleGraph.edist_ne_top_iff_reachable]
  have hClosed : ∀ Y : supports Λ R, Y.1 ⊆ C ∨ Disjoint Y.1 C := by
    intro Y
    obtain ⟨hYΛ, -, hYwalk⟩ := mem_supports_iff_walk.1 Y.2
    by_cases hYC : ∃ y ∈ Y.1, y ∈ C
    · obtain ⟨y, hyY, hyC⟩ := hYC
      refine Or.inl fun z hzY => ?_
      rw [hmemC z (hYΛ hzY)]
      have hay : G.Reachable ⟨anchor X.1, hroot⟩ ⟨y, hYΛ hyY⟩ :=
        (hmemC y (hYΛ hyY)).mp hyC
      obtain ⟨w, -⟩ := hYwalk y hyY z hzY
      exact hay.trans w.reachable
    · push Not at hYC
      exact Or.inr (Finset.disjoint_left.mpr fun y hyY hyC => hYC y hyY hyC)
  have hXC : X.1 ⊆ C := by
    obtain ⟨hXΛ, -, hXwalk⟩ := mem_supports_iff_walk.1 X.2
    intro z hzX
    rw [hmemC z (hXΛ hzX)]
    obtain ⟨w, -⟩ := hXwalk (anchor X.1) (hanchor X.1 X.2) z hzX
    exact w.reachable
  have hH : (hamiltonian Λ Φ).IsHermitian := hΦ.isHermitian_hamiltonian
  set A := term X
  set M := centeredFilter p δ (hamiltonian Λ Φ) Ω A
  set k := positiveConstraint c M
  have hMh : M.IsHermitian :=
    isHermitian_centeredFilter p δ hH Ω (hΦ.isHermitian_extendId X)
  have hkcomm : ∀ B : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ,
      IsSupportedOn (Finset.sdiff_subset : D ⊆ Λ) B → Commute k B := by
    intro B hB
    have hτ : ∀ t : ℝ, Commute
        (hermitianUnitaryPath (hamiltonian Λ Φ) t * A *
          hermitianUnitaryPath (hamiltonian Λ Φ) (-t)) B := by
      intro t
      have ht := LiebRobinson.commute_heisenbergEvolution_of_closed
        (domainComponent_subset Λ (anchor X.1))
        (Finset.sdiff_subset : D ⊆ Λ) term (fun Y : supports Λ R => Y.1)
        (fun Y => subset_of_mem_supports Y.2)
        (fun Y => isSupportedOn_extendId _ _) hClosed
        (by
          rw [Finset.disjoint_left]
          intro z hzC hzD
          exact (Finset.mem_sdiff.mp (by simpa only [D] using hzD)).2
            (by simpa only [C] using hzC))
        ((isSupportedOn_extendId (subset_of_mem_supports X.2) (Φ X)).mono hXC
          (domainComponent_subset Λ (anchor X.1))) hB t
      rw [← hΦ.hamiltonian_eq_sum_supports] at ht
      exact ht
    have hF := commute_filterIntegral_of_forall_commute hp hδ hH hτ
    have hMcomm : Commute M B :=
      hF.sub_left ((Commute.one_left B).smul_left _)
    exact (hMcomm.cfcAbs_of_isHermitian hMh).smul_left _
  have hnorm : ‖k - condExpect (domainComponent_subset Λ (anchor X.1)) k‖ ≤ 0 := by
    apply norm_sub_condExpect_le_of_forall_commutator
    intro B hB _
    rw [(hkcomm B hB).eq, sub_self, norm_zero]
  have heq : k = condExpect (domainComponent_subset Λ (anchor X.1)) k := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm hnorm (norm_nonneg _)
  change IsSupportedOn (domainComponent_subset Λ (anchor X.1)) k
  rw [heq]
  exact isSupportedOn_condExpect _ _

/-- Proposition 4.3 over `ℂ`, assembled from the positive spectral filter and the induced
square-lattice localization estimate. -/
theorem positive_replacement_complex (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q)
    (hJ : 0 < J) (hΔ : 0 < Δ) (hp : 1 ≤ p) : PositiveReplacement ℂ q R J Δ p := by
  let cs := positiveNormalization p (Δ / 2) J
  obtain ⟨C, c, hC, hc, htail⟩ := exists_norm_positiveConstraint_sub_map_le hp
    (C := LiebRobinson.localizationPrefactor R)
    (v := LiebRobinson.localizationVelocity R J) (c := 1) hΔ hJ.le
    (LiebRobinson.localizationPrefactor_nonneg R)
    (LiebRobinson.localizationVelocity_pos (R := R) hJ) one_pos
  refine ⟨cs, positiveNormalization_pos p (Δ / 2) J, C, c, hc, ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor
  classical
  letI : NeZero q := ⟨by omega⟩
  let Ωe : EuclideanSpace ℂ (Reg (Qudits q) Λ) := WithLp.toLp 2 Ω
  let term : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X => extendId (subset_of_mem_supports X.2) (Φ X)
  let ksub : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X => positiveConstraint cs
      (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ωe (term X))
  let k : Finset (ℤ × ℤ) → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X => if hX : X ∈ supports Λ R then ksub ⟨X, hX⟩ else 0
  obtain ⟨hΩe, -, -⟩ :=
    (normalized_eigen_hasGlobalGap_iff_euclidean (hamiltonian Λ Φ) Ω E₀ Δ).mp
      ⟨hΩ, hHΩ, hgap⟩
  have hgapC : (hamiltonian Λ Φ - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef := by
    rw [← Matrix.le_iff]
    exact hgap
  have hspectral :=
      SpectralFilter.positive_replacement (E₀ := E₀) (J := J) hp hΔ hΩe
        (by
          change hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω
          funext x
          have hx := congrFun hHΩ x
          simpa [Matrix.mulVec, dotProduct, smul_eq_mul] using hx)
        (by simpa only [Ωe, WithLp.ofLp_toLp] using hgapC) term
        (fun X => hΦ.isHermitian_extendId X) (fun X => hΦ.norm_extendId_le X)
        hΦ.hamiltonian_eq_sum_supports.symm
  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    simpa only [k, dif_pos hX, ksub, term, cs, Ωe, WithLp.ofLp_toLp] using
      hspectral.1 ⟨X, hX⟩
  · have hsum : ∑ X ∈ supports Λ R, k X = ∑ X : supports Λ R, ksub X := by
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      apply Finset.sum_congr rfl
      intro X _
      simp only [k, dif_pos X.2]
    rw [hsum]
    convert hspectral.2.1 using 1 <;>
      ext i j <;> simp [cs, ksub, term, Ωe, smul_eq_mul]
  · convert hspectral.2.2 using 1 <;>
      ext i j <;> simp [cs, Ωe, smul_eq_mul]
  · intro X hX l
    let hN := graphNbhd_subset Λ {anchor X} l
    have hkX := hspectral.1 ⟨X, hX⟩
    have hk0 : 0 ≤ k X := by
      simpa only [k, dif_pos hX, ksub, term, cs, Ωe, WithLp.ofLp_toLp] using hkX.1
    have hk1 : k X ≤ 1 := by
      simpa only [k, dif_pos hX, ksub, term, cs, Ωe, WithLp.ofLp_toLp] using hkX.2.1
    refine ⟨condExpect_nonneg hN hk0, condExpect_le_one hN hk1, ?_⟩
    have hraw := htail
      (n := Reg (Qudits q) Λ)
      (H := hamiltonian Λ Φ) (Ω := Ωe) (h := term ⟨X, hX⟩)
      hΦ.isHermitian_hamiltonian hΩe (hΦ.isHermitian_extendId ⟨X, hX⟩)
      (hΦ.norm_extendId_le ⟨X, hX⟩)
      (condExpectₗ hN) (norm_condExpect_le hN) (condExpect_one hN)
      (fun Y hY => isHermitian_condExpect hN hY)
      (condExpect_cfcAbs_condExpect hN
        (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ωe (term ⟨X, hX⟩)))
      (show 0 ≤ (l : ℝ) by positivity)
      (fun t => by
        have hlr := LiebRobinson.norm_heisenberg_sub_condExpect_graphNbhd_le
          hq hJ hΦ anchor hanchor ⟨X, hX⟩ l t
        simpa only [term, condExpectₗ_apply, one_mul] using hlr)
    simpa only [k, dif_pos hX, ksub, term, cs, Ωe, condExpectₗ_apply,
      SpectralFilter.kernelExponent, one_mul, neg_mul] using hraw
  · intro X hX
    simpa only [k, dif_pos hX, ksub, term, cs, Ωe] using
      positiveConstraint_isSupportedOn_domainComponent hp (half_pos hΔ) hq hΦ anchor
        hanchor (WithLp.toLp 2 Ω) cs ⟨X, hX⟩

end OpenAI
