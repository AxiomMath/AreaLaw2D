import OpenAI.Scan.RectangleBootstrap
import OpenAI.ExponentBootstrap
import OpenAI.InitialBoxEstimate
import OpenAI.Scan.BoxImprovementStep

/-!
# Proposition 9.5: the improved safe-box estimate

`F_box(r) ≤ C r^{1+e_*}` with `e_* = 2·10⁻⁶` [OAI265, §9.4, Proposition 9.5].  Proposition 3.3
supplies an initial exponent `e₀ < 1`; the one-step improvement
(`OpenAI.Scan.isSafe_regionEntropy_le_of_boxEntropy_le`) replaces a current exponent
`e_* < e ≤ e₀` by `(1 - ℓ) e` with a fraction `ℓ` fixed by `e₀`; finitely many steps reach
`e_*` (`OpenAI.exists_boxEntropy_le_rpow_of_eventual_improvement`).

## Implementation notes

The estimate is stated over `ℂ`: the scanner layer it rests on is ported over `ℂ`.
-/

namespace OpenAI

open Arealaw Matrix

/-- **The eventual one-step improvement of `F_box`** [OAI265, proof of Proposition 9.5]: for
`e_* < e ≤ e₀ < 1`, a bound `F_box(r) ≤ C r^{1+e}` on `r ≥ 1` gives
`F_box(r) ≤ C' r^{1+(1-ℓ)e}` on all large `r`, with `ℓ` the bootstrap fraction of `e₀`.  Large
safe rectangles are the one-step improvement; small ones cost at most `N² log q`. -/
theorem boxEntropy_eventually_improves (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) {e₀ : ℝ} (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) :
    ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ → ∀ C : ℝ,
      (∀ r : ℕ, 1 ≤ r → boxEntropy ℂ q R J Δ r ≤ C * (r : ℝ) ^ (1 + e)) →
      ∃ (C' : ℝ) (N : ℕ), ∀ r : ℕ, N ≤ r →
        boxEntropy ℂ q R J Δ r ≤
          C' * (r : ℝ) ^ (1 + (1 - Scan.BootstrapParameters.ell e₀) * e) := by
  intro e he hee₀ C hC
  obtain ⟨C₁, N, hstep⟩ :=
    Scan.isSafe_regionEntropy_le_of_boxEntropy_le q R J Δ hq hJ hΔ he₀ he₀₁ he hee₀ hC
  have he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  obtain ⟨-, -, -, hℓ₁, -⟩ := Scan.BootstrapParameters.parameter_bounds he₀pos he₀₁
  set p : ℝ := 1 + (1 - Scan.BootstrapParameters.ell e₀) * e with hp_def
  have hp : 0 ≤ p := by
    have : 0 ≤ (1 - Scan.BootstrapParameters.ell e₀) * e :=
      mul_nonneg (by linarith) hepos.le
    linarith
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  refine ⟨max C₁ 0 + (N : ℝ) ^ 2 * Real.log q, max N 1, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (le_max_right N 1).trans hr
  have hrp : (1 : ℝ) ≤ (r : ℝ) ^ p := Real.one_le_rpow hr1 hp
  have hbound : 0 ≤ (max C₁ 0 + (N : ℝ) ^ 2 * Real.log q) * (r : ℝ) ^ p :=
    mul_nonneg (add_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg _) hlogq))
      (by positivity)
  refine Real.sSup_le (fun s hs => ?_) hbound
  obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hsafe, hQr, rfl⟩ := hs
  by_cases hN : N ≤ boxSize Q
  · have h := hstep D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hsafe hN
    have hb : ((boxSize Q : ℕ) : ℝ) ^ p ≤ (r : ℝ) ^ p :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hQr) hp
    calc _ ≤ C₁ * ((boxSize Q : ℕ) : ℝ) ^ p := h
      _ ≤ max C₁ 0 * ((boxSize Q : ℕ) : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C₁ 0 * (r : ℝ) ^ p := mul_le_mul_of_nonneg_left hb (le_max_right _ _)
      _ ≤ (max C₁ 0 + (N : ℝ) ^ 2 * Real.log q) * (r : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
            (mul_nonneg (sq_nonneg _) hlogq)) (by positivity)
  · have hmem : (pureState Ω hΩ).regionEntropy
        (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ∈
        boxEntropyValues ℂ q R J Δ (boxSize Q) :=
      ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hsafe, le_rfl, rfl⟩
    have hsmall : ((boxSize Q : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      have : (boxSize Q : ℝ) ≤ N := by exact_mod_cast (not_le.1 hN).le
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
    calc _ ≤ ((boxSize Q : ℕ) : ℝ) ^ 2 * Real.log q := le_of_mem_boxEntropyValues hmem
      _ ≤ (N : ℝ) ^ 2 * Real.log q := mul_le_mul_of_nonneg_right hsmall hlogq
      _ ≤ (N : ℝ) ^ 2 * Real.log q * (r : ℝ) ^ p :=
          le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hlogq) hrp
      _ ≤ (max C₁ 0 + (N : ℝ) ^ 2 * Real.log q) * (r : ℝ) ^ p := by
          rw [add_mul]
          exact le_add_of_nonneg_left (mul_nonneg (le_max_right _ _) (by positivity))

/-- **Proposition 9.5, the improved safe-box estimate** [OAI265, §9.4]: there is `C > 0`,
depending only on `q, R, J, Δ`, with `F_box(r) ≤ C r^{1+e_*}` for every `r ≥ 1`,
`e_* = 2·10⁻⁶`. -/
theorem improved_box_estimate (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
      boxEntropy ℂ q R J Δ r ≤ C * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  obtain ⟨C₀, e₀, he₀, he₀₁, h₃₃⟩ := initial_box_estimate (𝕜 := ℂ) q R J Δ hq hJ hΔ
  have hinit : ∀ r : ℕ, 1 ≤ r →
      boxEntropy ℂ q R J Δ r ≤ max C₀ 0 * (r : ℝ) ^ (1 + e₀) := by
    intro r hr
    refine Real.sSup_le (fun s hs => ?_) (mul_nonneg (le_max_right _ _) (by positivity))
    obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hsafe, hQr, rfl⟩ := hs
    exact (h₃₃ D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q r hr hQ hsafe hQr).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hε : (0 : ℝ) < Exponents.boxError := by norm_num [Exponents.boxError]
  by_cases he : e₀ ≤ (Exponents.boxError : ℝ)
  · refine ⟨max C₀ 0 + 1, by positivity, fun r hr => (hinit r hr).trans ?_⟩
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    calc max C₀ 0 * (r : ℝ) ^ (1 + e₀)
        ≤ max C₀ 0 * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith))
            (le_max_right _ _)
      _ ≤ (max C₀ 0 + 1) * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have he' : (Exponents.boxError : ℝ) < e₀ := lt_of_not_ge he
    obtain ⟨-, -, hℓ, hℓ₁, -⟩ := Scan.BootstrapParameters.parameter_bounds he₀ he₀₁
    exact exists_boxEntropy_le_rpow_of_eventual_improvement he₀ hε hℓ hℓ₁ hinit
      (boxEntropy_eventually_improves q R J Δ hq hJ hΔ he' he₀₁)

end OpenAI
