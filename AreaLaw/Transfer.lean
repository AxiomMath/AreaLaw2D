import AreaLaw.S01_AreaLaw
import AreaLaw.S02_Preliminaries
import AreaLaw.S03_InitialBox
import AreaLaw.S04_Quasilocal.Positive
import AreaLawForMathlib.QuantumInfo.StateToComplex
import AreaLaw.S09_Scanner

/-!
# From `ℂ` to an arbitrary `RCLike` field

The development works over `ℂ`; the frozen statements of `OpenAI/Statements.lean` quantify over
`[RCLike 𝕜]`.  Each is transferred here along the entrywise embedding `RCLike.toComplex`: the
hypotheses over `𝕜` embed into hypotheses over `ℂ`, and an existential witness over `ℂ` is
pulled back by `Matrix.complexPullback` when `im I = 1`, and by its entrywise real part
`Matrix.realProjection` when `I = 0`.  Entropies and mutual informations of states are
unchanged by the embedding (`Arealaw.SubState.regionEntropy_toComplex`,
`Arealaw.SubState.mutualInfo_toComplex`, `OpenAI.pureState_toComplex`).

Proposition 11.2 (`TwoFamilyDecomposition`) has no scalar field and needs no transfer.

Some declarations here come from the v1 files `OpenAI/BufferDiscount.lean`,
`OpenAI/Scan/MarginalTailsBridge.lean`, whose header records them as ported or adapted from
`LionSR/TNLean` (see `NOTICE`).

## Main statements

* `AreaLaw.conditionalContinuity`: Lemma 2.1 over every `RCLike` field.
* `AreaLaw.marginalTails`: Lemma 3.1.
* `AreaLaw.bufferDiscount`, `AreaLaw.initialBoxEstimate`: Lemma 3.2 and Proposition 3.3.
* `AreaLaw.positiveReplacement`: Proposition 4.3.
* `AreaLaw.collarBound_of_complex`: Proposition 9.6 over `ℂ` gives it over every field.
* `AreaLaw.amplification`: Proposition 10.2.
* `AreaLaw.twoFamilyCancellation`: Lemma 11.1.
* `AreaLaw.areaLaw_of_collarBound`, `AreaLaw.areaLawCorollary_of_collarBound`: Theorem 1.1
  and Corollary 1.2 over every field, from Proposition 9.6 over `ℂ`.
* `AreaLaw.areaLaw`, `AreaLaw.areaLawCorollary`: Theorem 1.1 and Corollary 1.2 over every
  field, with Proposition 9.6 discharged by `AreaLaw.Scanner.prop_9_6`.
-/

namespace AreaLaw

open Arealaw OpenAI Matrix RCLike
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Hamiltonian-level notions under the embedding -/

theorem hamiltonian_map_toComplex {q : ℕ} (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) :
    hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)) = (hamiltonian Λ Φ).map (toComplex 𝕜) := by
  simp only [hamiltonian, map_toComplex_sum, extendId_map_toComplex]

theorem isAdmissible_map_toComplex {q : ℕ} {Λ : Finset (ℤ × ℤ)} {R : ℕ} {J : ℝ}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}
    (hΦ : IsAdmissible Λ R J Φ) : IsAdmissible Λ R J (fun X => (Φ X).map (toComplex 𝕜)) := by
  simpa only [IsAdmissible, isHermitian_map_toComplex_iff, norm_map_toComplex,
    map_toComplex_eq_zero_iff] using hΦ

theorem map_toComplex_smul_one_sub_vecMulVec {ι : Type*} [DecidableEq ι]
    (Ω : ι → 𝕜) (r : ℝ) :
    ((r : 𝕜) • (1 - vecMulVec Ω (star Ω))).map (toComplex 𝕜) =
      (r : ℂ) • (1 - vecMulVec (fun i => toComplex 𝕜 (Ω i)) (star fun i => toComplex 𝕜 (Ω i))) := by
  rw [map_toComplex_smul, toComplex_ofReal, map_toComplex_sub, map_toComplex_one,
    star_comp_toComplex, vecMulVec_comp_toComplex]

theorem map_toComplex_sub_smul_one {ι : Type*} [DecidableEq ι] (H : Matrix ι ι 𝕜)
    (E₀ : ℝ) : (H - (E₀ : 𝕜) • 1).map (toComplex 𝕜) = H.map (toComplex 𝕜) - (E₀ : ℂ) • 1 := by
  rw [map_toComplex_sub, map_toComplex_smul, toComplex_ofReal, map_toComplex_one]

theorem hasGlobalGap_map_toComplex {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι 𝕜}
    {Ω : ι → 𝕜} {E₀ Δ : ℝ} (h : HasGlobalGap H Ω E₀ Δ) :
    HasGlobalGap (H.map (toComplex 𝕜)) (fun i => toComplex 𝕜 (Ω i)) E₀ Δ := by
  have := (map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)).2 h
  rwa [map_toComplex_smul_one_sub_vecMulVec, map_toComplex_sub_smul_one] at this

/-! ### Proposition 4.3 -/

/-- Proposition 4.3 over `ℂ` implies Proposition 4.3 over every `RCLike` field. -/
theorem positiveReplacement_of_complex {q R : ℕ} {J Δ : ℝ} {p : ℕ}
    (hC : PositiveReplacement ℂ q R J Δ p) : PositiveReplacement 𝕜 q R J Δ p := by
  classical
  obtain ⟨cstar, hcstar, C, c, hc, hC⟩ := hC
  refine ⟨cstar, hcstar, C, c, hc, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor => ?_⟩
  set ΩC : Reg (Qudits q) Λ → ℂ := fun i => toComplex 𝕜 (Ω i)
  have hH := hamiltonian_map_toComplex Λ Φ
  have hΩC : star ΩC ⬝ᵥ ΩC = 1 := star_dotProduct_comp_toComplex hΩ
  have hHΩC : hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)) *ᵥ ΩC = (E₀ : ℂ) • ΩC := by
    rw [hH, mulVec_map_toComplex, hHΩ]
    ext; simp [ΩC]
  obtain ⟨kC, hk, hsum, hgapC, htail, hsupp⟩ :=
    hC Λ _ (isAdmissible_map_toComplex hΦ) ΩC hΩC E₀ hHΩC
      (hH ▸ hasGlobalGap_map_toComplex hgap) anchor hanchor
  rw [hH] at hsum hgapC
  have hE : ((cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1)).map (toComplex 𝕜) =
      (cstar : ℂ)⁻¹ • ((hamiltonian Λ Φ).map (toComplex 𝕜) - (E₀ : ℂ) • 1) := by
    rw [map_toComplex_smul, map_inv₀, toComplex_ofReal, map_toComplex_sub_smul_one]
  have hG := map_toComplex_smul_one_sub_vecMulVec Ω (Δ / cstar)
  replace hsum : _ ≤ ∑ X ∈ supports Λ R, kC X := hE ▸ hsum
  replace hgapC : _ ≤ ((cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1)).map (toComplex 𝕜) :=
    hG ▸ hE ▸ hgapC
  rcases I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · have hmono {A B : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ} (h : A ≤ B) :=
      realProjection_mono (𝕜 := 𝕜) h
    refine ⟨fun X => realProjection (kC X), fun X hX => ⟨?_, ?_, ?_⟩, ?_, ?_,
      fun X hX l => ⟨?_, ?_, ?_⟩, fun X hX => (hsupp X hX).realProjection _⟩
    · simpa using hmono (hk X hX).1
    · simpa using hmono (hk X hX).2.1
    · exact realProjection_mulVec_eq_zero hI (hk X hX).2.2
    · simpa [realProjection_map_toComplex hI] using hmono hsum
    · simpa only [realProjection_map_toComplex hI] using hmono hgapC
    · simpa [realProjection_condExpect] using hmono (htail X hX l).1
    · simpa [realProjection_condExpect] using hmono (htail X hX l).2.1
    · rw [← realProjection_condExpect, ← realProjection_sub]
      exact ((hk X hX).1.posSemidef.isHermitian.sub
        (htail X hX l).1.posSemidef.isHermitian).norm_realProjection_le.trans (htail X hX l).2.2
  · refine ⟨fun X => complexPullback hI (kC X), fun X hX => ⟨?_, ?_, ?_⟩, ?_, ?_,
      fun X hX l => ⟨?_, ?_, ?_⟩, fun X hX => (hsupp X hX).complexPullback hI _⟩
    · simpa [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)] using (hk X hX).1
    · simpa [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), map_toComplex_one] using
        (hk X hX).2.1
    · refine funext fun i => toComplex_injective ?_
      rw [← congrFun (mulVec_map_toComplex _ Ω) i, complexPullback_map_toComplex]
      simpa using congrFun (hk X hX).2.2 i
    · simpa [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), map_toComplex_sum] using hsum
    · exact (map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)).1 hgapC
    · simpa [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), condExpect_map_toComplex] using
        (htail X hX l).1
    · simpa [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), condExpect_map_toComplex,
        map_toComplex_one] using (htail X hX l).2.1
    · rw [← norm_map_toComplex, map_toComplex_sub, condExpect_map_toComplex,
        complexPullback_map_toComplex]
      exact (htail X hX l).2.2

/-- D4.6 (Proposition 4.3) over every `RCLike` field: the frozen `PositiveReplacement 𝕜`. -/
theorem positiveReplacement (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (hp : 1 ≤ p) : PositiveReplacement 𝕜 q R J Δ p :=
  positiveReplacement_of_complex (positiveReplacement_complex q R J Δ p hq hΔ hp)

/-! ### The gapped-Hamiltonian hypotheses and the pure-state entropies -/

/-- The hypotheses shared by the Hamiltonian-level frozen statements, embedded into `ℂ`. -/
theorem gapped_map_toComplex {q R : ℕ} {J Δ : ℝ} {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}
    (hΦ : IsAdmissible Λ R J Φ) {Ω : Reg (Qudits q) Λ → 𝕜} {E₀ : ℝ}
    (hHΩ : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ) :
    IsAdmissible Λ R J (fun X => (Φ X).map (toComplex 𝕜)) ∧
      hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)) *ᵥ (fun i => toComplex 𝕜 (Ω i)) =
        (E₀ : ℂ) • (fun i => toComplex 𝕜 (Ω i)) ∧
      HasGlobalGap (hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)))
        (fun i => toComplex 𝕜 (Ω i)) E₀ Δ := by
  rw [hamiltonian_map_toComplex]
  refine ⟨isAdmissible_map_toComplex hΦ, ?_, hasGlobalGap_map_toComplex hgap⟩
  rw [mulVec_map_toComplex, hHΩ]
  ext; simp

section PureState

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U X Y : Finset σ} {Ω : Reg loc U → 𝕜}

theorem regionEntropy_pureState_toComplex (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hΩC : star (fun i => toComplex 𝕜 (Ω i)) ⬝ᵥ (fun i => toComplex 𝕜 (Ω i)) = 1)
    (h : X ⊆ U) :
    (pureState (fun i => toComplex 𝕜 (Ω i)) hΩC).regionEntropy h =
      (pureState Ω hΩ).regionEntropy h := by
  rw [← pureState_toComplex Ω hΩ, MState.toSubState_toComplex, SubState.regionEntropy_toComplex]

theorem mutualInfo_pureState_toComplex (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hΩC : star (fun i => toComplex 𝕜 (Ω i)) ⬝ᵥ (fun i => toComplex 𝕜 (Ω i)) = 1)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    (pureState (fun i => toComplex 𝕜 (Ω i)) hΩC).mutualInfo hX hY =
      (pureState Ω hΩ).mutualInfo hX hY := by
  rw [← pureState_toComplex Ω hΩ, MState.toSubState_toComplex, SubState.mutualInfo_toComplex]

end PureState

/-! ### Lemma 2.1 -/

/-- D2.1 (Lemma 2.1) over every `RCLike` field: the frozen `ConditionalContinuity`. -/
theorem conditionalContinuity (σ : Type*) [DecidableEq σ] (loc : σ → Type*)
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (𝕜 : Type*) [RCLike 𝕜] :
    ConditionalContinuity σ loc 𝕜 := by
  intro U X Y hX hY hd ρ τ
  simpa only [MState.toSubState_toComplex, SubState.regionEntropy_toComplex,
    ← SubState.toComplex_restrict, SubState.D₁_toComplex] using
    lemma_2_1 U X Y hX hY hd ρ.toComplex τ.toComplex

/-! ### Lemma 3.1 -/

/-- The two conclusions of Lemma 3.1 depend on a state only through its spectrum. -/
theorem marginalTails_conclusion_toComplex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SubState κ 𝕜) (a b : ℝ) (m : ℝ → ℝ) (ρC : SubState κ ℂ) (hρ : ρC = ρ.toComplex)
    (h : (∀ u : ℝ, |u| ≤ a →
        Real.log (∑ j ∈ Finset.univ.filter (fun j => 0 < ρC.psd.isHermitian.eigenvalues j),
            ρC.psd.isHermitian.eigenvalues j *
              Real.exp (-u * Real.log (ρC.psd.isHermitian.eigenvalues j))) ≤
          u * ρC.entropy + b * u ^ 2) ∧
      ∀ w : ℝ, 0 ≤ w →
        ∑ j ∈ Finset.univ.filter (fun j => 0 < ρC.psd.isHermitian.eigenvalues j ∧
            w < |-Real.log (ρC.psd.isHermitian.eigenvalues j) - ρC.entropy|),
          ρC.psd.isHermitian.eigenvalues j ≤ m w) :
    (∀ u : ℝ, |u| ≤ a →
        Real.log (∑ j ∈ Finset.univ.filter (fun j => 0 < ρ.psd.isHermitian.eigenvalues j),
            ρ.psd.isHermitian.eigenvalues j *
              Real.exp (-u * Real.log (ρ.psd.isHermitian.eigenvalues j))) ≤
          u * ρ.entropy + b * u ^ 2) ∧
      ∀ w : ℝ, 0 ≤ w →
        ∑ j ∈ Finset.univ.filter (fun j => 0 < ρ.psd.isHermitian.eigenvalues j ∧
            w < |-Real.log (ρ.psd.isHermitian.eigenvalues j) - ρ.entropy|),
          ρ.psd.isHermitian.eigenvalues j ≤ m w := by
  subst hρ
  have hs (P : ℝ → Prop) [DecidablePred P] (g : ℝ → ℝ) :
      ∑ j ∈ Finset.univ.filter (fun j => P (ρ.toComplex.psd.isHermitian.eigenvalues j)),
          g (ρ.toComplex.psd.isHermitian.eigenvalues j) =
        ∑ j ∈ Finset.univ.filter (fun j => P (ρ.psd.isHermitian.eigenvalues j)),
          g (ρ.psd.isHermitian.eigenvalues j) := by
    simp only [Finset.sum_filter]
    exact sum_eq_of_multiset_map_eq (fun x => if P x then g x else 0) ρ.eigenvalues_toComplex
  rw [SubState.entropy_toComplex] at h
  refine ⟨fun u hu => ?_, fun w hw => ?_⟩
  · simpa only [hs (0 < ·) fun x => x * Real.exp (-u * Real.log x)] using h.1 u hu
  · have := hs (fun x => 0 < x ∧ w < |-Real.log x - ρ.entropy|) id
    simp only [id] at this
    simpa only [this] using h.2 w hw

/-- D3.1 (Lemma 3.1) over every `RCLike` field: the frozen `MarginalTails`. -/
theorem marginalTails (σ : Type*) [DecidableEq σ] (loc : σ → Type*)
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (𝕜 : Type*) [RCLike 𝕜] :
    MarginalTails σ loc 𝕜 := by
  intro U ι _ D hD h c₀ g₀ E₀ Ψ hΨ hsupp hherm hc₀ hnorm hg₀ heig hgap B hB ρ p 𝓑
  have hsum : (∑ i, h i).map (toComplex 𝕜) = ∑ i, (h i).map (toComplex 𝕜) :=
    map_toComplex_sum _ _
  have hC := lemma_3_1 U ι D hD (fun i => (h i).map (toComplex 𝕜)) c₀ g₀ E₀
    (fun x => toComplex 𝕜 (Ψ x)) (star_dotProduct_comp_toComplex hΨ)
    (fun i => by
      obtain ⟨B', hB'⟩ := hsupp i
      exact ⟨B'.map (toComplex 𝕜), by rw [hB', extendId_map_toComplex]⟩)
    (fun i => isHermitian_map_toComplex_iff.2 (hherm i)) hc₀
    (fun i => (norm_map_toComplex _).trans_le (hnorm i)) hg₀
    (by
      rw [← hsum, mulVec_map_toComplex, heig]
      ext; simp)
    (hsum ▸ hasGlobalGap_map_toComplex hgap) B hB
  refine marginalTails_conclusion_toComplex ρ _ _ _ _ ?_ hC
  rw [SubState.toComplex_restrict, ← MState.toSubState_toComplex, pureState_toComplex]

/-! ### Lemma 3.2 and Proposition 3.3 -/

/-- The frozen `BufferDiscount` over `ℂ` implies it over every `RCLike` field. -/
theorem bufferDiscount_of_complex {q R : ℕ} {J Δ : ℝ} (hC : BufferDiscount ℂ q R J Δ) :
    BufferDiscount 𝕜 q R J Δ := by
  obtain ⟨Cpad, hCpad, Cbuf, hC⟩ := hC
  refine ⟨Cpad, hCpad, Cbuf, fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA Q hQ hsafe r hr Q₀ hQ₀
    hsize hdil => ?_⟩
  obtain ⟨hΦC, hHC, hgapC⟩ := gapped_map_toComplex hΦ hHΩ hgap
  simpa only [regionEntropy_pureState_toComplex hΩ] using
    hC D₀ hD₀ Λ _ hΦC _ (star_dotProduct_comp_toComplex hΩ) E₀ hHC hgapC A hA Q hQ hsafe r hr
      Q₀ hQ₀ hsize hdil

/-- D3.2 (Lemma 3.2) over every `RCLike` field: the frozen `BufferDiscount`. -/
theorem bufferDiscount (𝕜 : Type*) [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) : BufferDiscount 𝕜 q R J Δ :=
  bufferDiscount_of_complex (lemma_3_2 hq hJ hΔ)

/-- The frozen `InitialBoxEstimate` over `ℂ` implies it over every `RCLike` field. -/
theorem initialBoxEstimate_of_complex {q R : ℕ} {J Δ : ℝ} (hC : InitialBoxEstimate ℂ q R J Δ) :
    InitialBoxEstimate 𝕜 q R J Δ := by
  obtain ⟨C, e₀, he₀, he₀', hC⟩ := hC
  refine ⟨C, e₀, he₀, he₀', fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA Q r hr hQ hsafe hsize => ?_⟩
  obtain ⟨hΦC, hHC, hgapC⟩ := gapped_map_toComplex hΦ hHΩ hgap
  simpa only [regionEntropy_pureState_toComplex hΩ] using
    hC D₀ hD₀ Λ _ hΦC _ (star_dotProduct_comp_toComplex hΩ) E₀ hHC hgapC A hA Q r hr hQ hsafe
      hsize

/-- D3.3 (Proposition 3.3) over every `RCLike` field: the frozen `InitialBoxEstimate`. -/
theorem initialBoxEstimate (𝕜 : Type*) [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q)
    (hJ : 0 < J) (hΔ : 0 < Δ) : InitialBoxEstimate 𝕜 q R J Δ :=
  initialBoxEstimate_of_complex (prop_3_3 hq hJ hΔ)

/-! ### Proposition 9.6 -/

/-- Proposition 9.6 over `ℂ` implies Proposition 9.6 over every `RCLike` field. -/
theorem collarBound_of_complex {q R : ℕ} {J Δ : ℝ} (hC : CollarBound ℂ q R J Δ) :
    CollarBound 𝕜 q R J Δ := by
  intro D₀ hD₀
  obtain ⟨Ctpl₀, hC⟩ := hC D₀ hD₀
  refine ⟨Ctpl₀, fun Ctpl hCtpl => ?_⟩
  obtain ⟨C, n₀, hC⟩ := hC Ctpl hCtpl
  refine ⟨C, n₀, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA T n s₀ hT hsep hL hn => ?_⟩
  obtain ⟨hΦC, hHC, hgapC⟩ := gapped_map_toComplex hΦ hHΩ hgap
  simpa only [mutualInfo_pureState_toComplex hΩ] using
    hC Λ _ hΦC _ (star_dotProduct_comp_toComplex hΩ) E₀ hHC hgapC A hA T n s₀ hT hsep hL hn

/-! ### Proposition 10.2 -/

/-- Proposition 10.2 over `ℂ` implies Proposition 10.2 over every `RCLike` field. -/
theorem amplification_of_complex {q R : ℕ} {J Δ : ℝ} {p : ℕ}
    (hC : Amplification ℂ q R J Δ p) : Amplification 𝕜 q R J Δ p := by
  intro C₀ hC₀ M hM
  obtain ⟨C_M, n₀, hC⟩ := hC C₀ hC₀ M hM
  refine ⟨C_M, n₀, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA T n hn hn₀ hS₀ hX hS₀X hS₀' hI => ?_⟩
  obtain ⟨hΦC, hHC, hgapC⟩ := gapped_map_toComplex hΦ hHΩ hgap
  simpa only [mutualInfo_pureState_toComplex hΩ] using
    hC Λ _ hΦC _ (star_dotProduct_comp_toComplex hΩ) E₀ hHC hgapC A hA T n hn hn₀ hS₀ hX hS₀X
      hS₀' (by rwa [mutualInfo_pureState_toComplex hΩ])

/-- D10.2 (Proposition 10.2) over every `RCLike` field: the frozen `Amplification`. -/
theorem amplification (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (hp : 10 ^ 6 ≤ p) : Amplification 𝕜 q R J Δ p :=
  amplification_of_complex (amplification_complex q R J Δ p hq hΔ hp)

/-! ### Lemma 11.1 -/

/-- D11.1 (Lemma 11.1) over every `RCLike` field: the frozen `TwoFamilyCancellation`. -/
theorem twoFamilyCancellation (σ : Type*) [DecidableEq σ] (loc : σ → Type*)
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (𝕜 : Type*) [RCLike 𝕜] :
    TwoFamilyCancellation σ loc 𝕜 := by
  intro Λ ψ hψ A D hA hD m X hX f ε hAD hDX hXX hε
  simpa only [regionEntropy_pureState_toComplex hψ] using
    lemma_11_1 Λ _ (star_dotProduct_comp_toComplex hψ) A D hA hD m X hX f ε hAD hDX hXX
      fun i => by rw [mutualInfo_pureState_toComplex hψ]; exact hε i

/-! ### Theorem 1.1 and Corollary 1.2 -/

/-- Theorem 1.1 over `ℂ` implies Theorem 1.1 over every `RCLike` field. -/
theorem areaLaw_of_complex {q R : ℕ} {J Δ : ℝ} (hC : AreaLaw ℂ q R J Δ) : AreaLaw 𝕜 q R J Δ := by
  obtain ⟨C, hC⟩ := hC
  refine ⟨C, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA => ?_⟩
  obtain ⟨hΦC, hHC, hgapC⟩ := gapped_map_toComplex hΦ hHΩ hgap
  simpa only [regionEntropy_pureState_toComplex hΩ] using
    hC Λ _ hΦC _ (star_dotProduct_comp_toComplex hΩ) E₀ hHC hgapC A hA

theorem vertexAreaLaw_of_complex {q R : ℕ} {J Δ : ℝ} (hC : VertexAreaLaw ℂ q R J Δ) :
    VertexAreaLaw 𝕜 q R J Δ := by
  obtain ⟨C, hC⟩ := hC
  refine ⟨C, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA => ?_⟩
  obtain ⟨hΦC, hHC, hgapC⟩ := gapped_map_toComplex hΦ hHΩ hgap
  simpa only [regionEntropy_pureState_toComplex hΩ] using
    hC Λ _ hΦC _ (star_dotProduct_comp_toComplex hΩ) E₀ hHC hgapC A hA

/-- Corollary 1.2 over `ℂ` implies Corollary 1.2 over every `RCLike` field. -/
theorem areaLawCorollary_of_complex {q : ℕ} {J Δ : ℝ} (hC : AreaLawCorollary ℂ q J Δ) :
    AreaLawCorollary 𝕜 q J Δ :=
  ⟨areaLaw_of_complex hC.1, fun R => vertexAreaLaw_of_complex (hC.2 R)⟩

/-- D1.4 (Theorem 1.1) over every `RCLike` field, from Proposition 9.6 over `ℂ`. -/
theorem areaLaw_of_collarBound (𝕜 : Type*) [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (prop_9_6 : CollarBound ℂ q R J Δ) : AreaLaw 𝕜 q R J Δ :=
  areaLaw_of_complex (theorem_1_1' hq hΔ prop_9_6)

/-- D1.7 (Corollary 1.2) over every `RCLike` field, from Proposition 9.6 over `ℂ`. -/
theorem areaLawCorollary_of_collarBound (𝕜 : Type*) [RCLike 𝕜] {q : ℕ} {J Δ : ℝ} (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (prop_9_6 : ∀ R, CollarBound ℂ q R J Δ) : AreaLawCorollary 𝕜 q J Δ :=
  areaLawCorollary_of_complex (corollary_1_2' hq hΔ prop_9_6)

/-- D1.4 **Theorem 1.1** (area law). For all integers `q ≥ 1`, `R ≥ 0` and reals `J > 0`,
`Δ > 0` there is `C = C(q, R, J, Δ)` such that for every finite domain `Λ ⊂ ℤ²`, every
admissible `H` with gapped ground vector `Ω` and every `A ⊆ Λ`, `S_Ω(A) ≤ C |∂_Λ A|`; over every
`RCLike` field. -/
theorem areaLaw (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) : AreaLaw 𝕜 q R J Δ :=
  areaLaw_of_collarBound 𝕜 hq hΔ (Scanner.prop_9_6 hq hJ hΔ)

/-- D1.7 **Corollary 1.2**: the area law for range `R = 1` and the vertex-boundary forms for
every range `R`; over every `RCLike` field. -/
theorem areaLawCorollary (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) : AreaLawCorollary 𝕜 q J Δ :=
  areaLawCorollary_of_collarBound 𝕜 hq hΔ fun _ => Scanner.prop_9_6 hq hJ hΔ

end AreaLaw
