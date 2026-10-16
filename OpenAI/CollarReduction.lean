import OpenAI.Geometry.TemplateCollar

/-!
# Proposition 9.6 from its mutual-information inequality

The size and boundary assertions of Proposition 9.6 hold for every separated template
(`OpenAI.IsTemplate.collar_cut_card_le`), so `OpenAI.CollarBound` follows from its
mutual-information inequality `I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}` alone.

## Main definitions

* `OpenAI.CollarInformationBound`: the mutual-information inequality of Proposition 9.6.

## Main statements

* `OpenAI.collarBound_of_collarInformationBound`: `CollarInformationBound` implies
  `CollarBound`.
-/

namespace OpenAI

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder

/-- The mutual-information inequality of **Proposition 9.6** [OAI265, §9.5, eq. (9.16)]: with
the quantifiers of `CollarBound`, `I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}` for `X = A ∩ T`,
`S₀ = A ∩ T_L`, `L = ⌊n^{1-ε}⌋` and `ε = 10⁻⁵`. -/
def CollarInformationBound (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∀ D₀ : ℝ, 2 * R + 10 < D₀ → ∃ Ctpl₀ : ℝ, ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∃ C : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s₀ : ℕ),
      IsTemplate Ctpl n s₀ T → IsSeparatedFromCut D₀ s₀ Λ A T →
      collarWidth n ≤ s₀ → n₀ ≤ n →
      (pureState Ω hΩ).mutualInfo (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
          (Finset.sdiff_subset :
            Λ \ (A ∩ ambientDilation T (collarWidth n)) ⊆ Λ) ≤
        C * (n : ℝ) ^ (1 - (1 / 100000 : ℝ))

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}

/-- **Proposition 9.6 from its mutual-information inequality** [OAI265, §9.5]: the size and
boundary assertions hold for every separated template, so the mutual-information inequality
alone gives `CollarBound`. -/
theorem collarBound_of_collarInformationBound (h : CollarInformationBound 𝕜 q R J Δ) :
    CollarBound 𝕜 q R J Δ := by
  intro D₀ hD₀
  obtain ⟨Ctpl₀, hC⟩ := h D₀ hD₀
  refine ⟨max Ctpl₀ 24, fun Ctpl hCtpl => ?_⟩
  obtain ⟨C, n₀, hCn⟩ := hC Ctpl (le_of_max_le_left hCtpl)
  refine ⟨max C 10, n₀, fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hT hsep hL hn => ?_⟩
  have hD : 1 ≤ D₀ := by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    hT.collar_cut_card_le (le_of_max_le_right hCtpl) hsep hD hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlin {k m : ℕ} (hk : k ≤ m * n) (hm : (m : ℝ) ≤ 10) : (k : ℝ) ≤ max C 10 * n := by
    calc (k : ℝ) ≤ m * n := by exact_mod_cast hk
      _ ≤ 10 * n := mul_le_mul_of_nonneg_right hm hn0
      _ ≤ max C 10 * n := mul_le_mul_of_nonneg_right (le_max_right _ _) hn0
  refine ⟨(hCn Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hT hsep hL hn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    hlin h₁ (by norm_num), hlin h₂ (by norm_num), hlin h₃ (by norm_num), ?_⟩
  calc ((A ∩ ambientDilation T (collarWidth n)).card : ℝ) ≤ 10 * (n : ℝ) ^ 2 := by
        exact_mod_cast h₄
    _ ≤ max C 10 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end OpenAI
