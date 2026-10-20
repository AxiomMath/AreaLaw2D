import AreaLawRefactored.S04_Quasilocal.Positive
import AreaLawForMathlib.QuantumInfo.RegionToComplex

/-!
# From `ℂ` to an arbitrary `RCLike` field

The development works over `ℂ`; the frozen statements of `OpenAI/Statements.lean` quantify over
`[RCLike 𝕜]`.  Each is transferred here along the entrywise embedding `RCLike.toComplex`: the
hypotheses over `𝕜` embed into hypotheses over `ℂ`, and an existential witness over `ℂ` is
pulled back by `Matrix.complexPullback` when `im I = 1`, and by its entrywise real part
`Matrix.realProjection` when `I = 0`.

## Main statements

* `AreaLaw.positiveReplacement`: Proposition 4.3 over every `RCLike` field.
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
  have hΩC : star ΩC ⬝ᵥ ΩC = 1 := by
    rw [star_comp_toComplex]
    simpa [ΩC, dotProduct, map_sum] using congrArg (toComplex 𝕜) hΩ
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

end AreaLaw
