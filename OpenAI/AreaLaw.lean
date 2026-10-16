import OpenAI.Amplification
import OpenAI.BoxEntropy
import OpenAI.CollarBound
import OpenAI.Corollary
import OpenAI.TwoFamily
import OpenAI.TwoFamilyDecomposition
import OpenAI.ZeroBoundary

/-!
# The area law

Theorem 1.1 of [OAI265, §11.8], and Corollary 1.2 from it.  A cut with no crossing edge has
zero entropy (Lemma 2.2).  Otherwise Proposition 11.2 decomposes the cut as
`A = D ∪ ⋃ᵢ Xᵢ`, each `Xᵢ` inside a template `Tᵢ` of scale `nᵢ`; Proposition 9.6 supplies the
collar bounds for each template, and Proposition 10.2, at `M = 100`, turns them into
`I_Ω(Xᵢ : Jᵢ) ≤ C nᵢ^{-100}`, where `Jᵢ` is the exterior of the cut together with the earlier
regions of the same family.  Lemma 11.1 then gives
`S_Ω(A) ≤ |D| log q + (C / 2) ∑ᵢ nᵢ^{-100}`, which is `O(|∂_Λ A|)`.

## Implementation notes

The exponent `p` of Propositions 4.3 and 10.2 is fixed at `10⁶`, as in the paper's choice
`α = p / (p + 1) > 1 - 10⁻⁶`, and the constant `D₀` of §3.2 at `2R + 11`.
-/

namespace OpenAI

open Arealaw Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The mutual-information bound of the proof of Theorem 1.1 [OAI265, §11.8], from
Propositions 9.6 and 10.2: for a template `T` of scale `n` separated from the cut, with
`dist_∞(T, Z_A) > 2 n^β` and `dist_∞(T, Y) > 2 n^β` for a set `Y ⊆ Λ`, every `X ⊆ A ∩ T`
satisfies `I_Ω(X : (Λ \ A) ∪ Y) ≤ C n^{-100}`, for one constant `C` and all `n` beyond a
threshold. -/
theorem exists_mutualInfo_exterior_union_le (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) :
    ∃ Ctpl C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s : ℕ),
      IsTemplate Ctpl n s T → IsSeparatedFromCut (2 * R + 11) s Λ A T →
      collarWidth n ≤ s → n₀ ≤ n →
      ENNReal.ofReal (2 * (n : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
        ambientEDist T (cutEndpoints Λ A) →
    ∀ (Y : Finset (ℤ × ℤ)) (hY : Y ⊆ Λ),
      ENNReal.ofReal (2 * (n : ℝ) ^ (1 - (2 / 1000000 : ℝ))) < ambientEDist T Y →
    ∀ (X : Finset (ℤ × ℤ)) (hX : X ⊆ A ∩ T),
      (pureState Ω hΩ).mutualInfo (hX.trans (Finset.inter_subset_left.trans hA))
          (Finset.union_subset Finset.sdiff_subset hY : Λ \ A ∪ Y ⊆ Λ) ≤
        C * ((n : ℝ) ^ 100)⁻¹ := by
  have hp : 1 - (1 / 1000000 : ℝ) < ((1000000 : ℕ) : ℝ) / ((1000000 : ℕ) + 1) := by norm_num
  obtain ⟨Ctpl, hcol⟩ := collar_bound (𝕜 := 𝕜) q R J Δ hq hJ hΔ (2 * R + 11) (by linarith)
  obtain ⟨C₁, n₁, hcol⟩ := hcol Ctpl le_rfl
  obtain ⟨CM, n₂, hamp⟩ := amplification (𝕜 := 𝕜) q R J Δ 1000000 hq hJ hΔ hp (max C₁ 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) 100 (by norm_num)
  obtain ⟨N, hN2, hN⟩ := Exponents.exists_collar_radius_threshold hp CM 1 one_pos
  refine ⟨Ctpl, max CM 0, le_max_right _ _, max (max n₁ n₂) N, le_max_of_le_right hN2,
    fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s htpl hsep hL hn hcut Y hY hYfar X hX => ?_⟩
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hI, hbX, hbS, hbSX, hcard⟩ :=
    hcol Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s htpl hsep hL hn₁
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC : C₁ ≤ max C₁ 1 := le_max_left _ _
  obtain ⟨r, hr, hout, -⟩ := hamp Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n (hN2.trans hnN) hn₂
    (hcard.trans (mul_le_mul_of_nonneg_right hC (by positivity)))
    (hbX.trans (mul_le_mul_of_nonneg_right hC hn0))
    (hbSX.trans (mul_le_mul_of_nonneg_right hC hn0))
    (hbS.trans (mul_le_mul_of_nonneg_right hC hn0))
    (hI.trans (mul_le_mul_of_nonneg_right hC (by positivity)))
  -- `L + 2r < n^β ≤ 2 n^β`, so both clearances exceed `L + 2r`.
  have hsmall : ((collarWidth n + 2 * r : ℕ) : ENNReal) <
      ENNReal.ofReal (2 * (n : ℝ) ^ (1 - (2 / 1000000 : ℝ))) := by
    have h := hN n hnN r hr
    have hpos : (0 : ℝ) < (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)) :=
      Real.rpow_pos_of_pos
        (by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) (hN2.trans hnN)) _
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    push_cast
    linarith
  have hJ' := exterior_union_subset_graphNeighborhood_compl_of_lt_ambientEDist Λ T A Y
    (collarWidth n) (2 * r) hY (hsmall.trans hcut) (hsmall.trans hYfar)
  exact (hout X hX _ hJ').trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- **Theorem 1.1 (area law)** [OAI265, §1.1 and §11.8]: for `q ≥ 1`, `J > 0` and `Δ > 0` the
constant exists. -/
theorem area_law (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    AreaLaw 𝕜 q R J Δ := by
  obtain ⟨Ctpl, CM, hCM, n₀, hn₀, hinfo⟩ :=
    exists_mutualInfo_exterior_union_le (𝕜 := 𝕜) q R J Δ hq hJ hΔ
  obtain ⟨C, hdec⟩ := two_family_decomposition (2 * R + 11) Ctpl n₀ (by omega)
  refine ⟨C * (Real.log q + CM / 2), fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA => ?_⟩
  rcases Nat.eq_zero_or_pos (edgeBoundary Λ A).card with hb | hb
  · rw [regionEntropy_eq_zero_of_edgeBoundary_eq_empty hΦ hΔ hΩ hE hgap hA
      (Finset.card_eq_zero.mp hb), hb]
    simp
  obtain ⟨D, m, X, f, T, n, s, hAD, hDX, hXX, hD, hi, hsum⟩ := hdec Λ A hA hb
  have hDA : D ⊆ A := by rw [hAD]; exact Finset.subset_union_left
  have hXA (i : Fin m) : X i ⊆ A := ((hi i).2.1).trans Finset.inter_subset_left
  have hXΛ (i : Fin m) : X i ⊆ Λ := (hXA i).trans hA
  have hcancel := two_family_cancellation (𝕜 := 𝕜) Λ Ω hΩ A D hA (hDA.trans hA) m X hXΛ f
    (fun i => CM * ((n i : ℝ) ^ 100)⁻¹) hAD hDX hXX fun i => by
      obtain ⟨-, hXi, hni, htpl, hsep, hL, hcut, hprev⟩ := hi i
      have hprev' : ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
          ambientEDist (T i)
            ((Finset.univ.filter fun j => f j = f i ∧ j < i).biUnion X) := by
        simpa only [and_comm] using hprev
      exact hinfo Λ Φ hΦ Ω hΩ E₀ hE hgap A hA (T i) (n i) (s i) htpl hsep hL hni hcut _
        (Finset.biUnion_subset.2 fun j _ => hXΛ j) hprev' (X i) hXi
  have hDent := (pureState Ω hΩ).regionEntropy_le_card_mul_log (hDA.trans hA)
    (d := q) fun _ => Fintype.card_fin q
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hb' : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  have hD' : (D.card : ℝ) * Real.log q ≤ C * (edgeBoundary Λ A).card * Real.log q :=
    mul_le_mul_of_nonneg_right hD hlog
  have hsum' : CM * ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ CM * (C * (edgeBoundary Λ A).card) :=
    mul_le_mul_of_nonneg_left hsum hCM
  simp only [← Finset.mul_sum] at hcancel
  linarith

/-- **Corollary 1.2** [OAI265, §1.1]. -/
theorem area_law_corollary (q : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    AreaLawCorollary 𝕜 q J Δ :=
  areaLawCorollary_of_areaLaw fun R => area_law q R J Δ hq hJ hΔ

end OpenAI
