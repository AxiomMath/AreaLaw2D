import OpenAI.Scan.SourceScan
import OpenAI.Scan.BootstrapRoundedClearance

/-!
# The test geometry of a safe rectangle

The scale and clearance conditions of eq. (9.2) for a safe rectangle scanned at `n = ⌈C₂ s₀⌉`
[OAI265, proof of Proposition 9.5].
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- For `C₂ ≥ 1`, the rounded splitting radius at the scale `n = ⌈C₂ s⌉` is eventually at
most `9s/10`. -/
theorem exists_ten_mul_roundedLogRadius_ceil_mul_le {C₂ Ctr : ℝ} (hC₂ : 1 ≤ C₂)
    (hCtr : 0 ≤ Ctr) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → 10 * roundedLogRadius Ctr ⌈C₂ * (s : ℝ)⌉₊ ≤ 9 * s := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_const_mul_roundedLogRadius_le_rpow hCtr one_pos (10 * (C₂ + 1) / 9))
  refine ⟨max N₀ 1, fun s hs ↦ ?_⟩
  have hs₁ : (1 : ℝ) ≤ s := by exact_mod_cast (le_max_right N₀ 1).trans hs
  have hCs : (s : ℝ) ≤ C₂ * s := le_mul_of_one_le_left (by positivity) hC₂
  have hn : N₀ ≤ ⌈C₂ * (s : ℝ)⌉₊ := by
    have : (s : ℝ) ≤ ⌈C₂ * (s : ℝ)⌉₊ := hCs.trans (Nat.le_ceil _)
    exact (le_max_left N₀ 1).trans (hs.trans (by exact_mod_cast this))
  have hr := hN₀ _ hn
  rw [Real.rpow_one] at hr
  have hceil := Nat.ceil_le_add_one_mul_of_le_mul (by positivity) le_rfl hs₁ (A := C₂)
  have hreal : (10 : ℝ) * roundedLogRadius Ctr ⌈C₂ * (s : ℝ)⌉₊ ≤ 9 * s := by
    have hC : (0 : ℝ) < C₂ + 1 := by linarith
    have := hr.trans hceil
    rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 9)] at this
    nlinarith
  exact_mod_cast hreal

/-- **The test geometry of a safe rectangle** [OAI265, proof of Proposition 9.5, lines
709–715].  For `C₂ ≥ 8`, a rectangle `Q` of size `s₀` safe at `D₀ ≥ 10`, `n = ⌈C₂ s₀⌉` and
`L = ⌊n^{1-ℓ}⌋`, at all large `s₀`: `|Q| ≤ n²`, every depth layer `Q_d \ Q_{d-1}` with
`1 ≤ d ≤ L` has at most `n` sites, `2L ≤ s₀`, and `dist_∞(Q, Z_A) > 2L + 10 r₀`. -/
theorem isSafe_test_geometry {C₂ ℓ Ctr : ℝ} (hC₂ : 8 ≤ C₂) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hCtr : 0 ≤ Ctr) :
    ∃ N : ℕ, ∀ s₀ : ℕ, N ≤ s₀ → ∀ D₀ : ℝ, 10 ≤ D₀ → ∀ Λ A Q : Finset (ℤ × ℤ),
      IsIntRect Q → IsSafe D₀ Λ A Q → boxSize Q = s₀ →
      let n := ⌈C₂ * (s₀ : ℝ)⌉₊
      let L := ⌊(n : ℝ) ^ (1 - ℓ)⌋₊
      (Q.card : ℝ) ≤ (n : ℝ) ^ 2 ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ L →
        (ambientDilation Q d \ ambientDilation Q (d - 1)).card ≤ n) ∧
      2 * L ≤ s₀ ∧
      ∀ t ∈ Q, ∀ z ∈ cutEndpoints Λ A,
        ((2 * L + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) < ambientSupDistance t z := by
  obtain ⟨N₁, hN₁⟩ := exists_two_mul_floor_rpow_ceil_mul_le (C₂ := C₂) (by linarith)
    (sub_pos.mpr hℓ₁) (sub_lt_self 1 hℓ)
  obtain ⟨N₂, hN₂⟩ := exists_ten_mul_roundedLogRadius_ceil_mul_le (by linarith : 1 ≤ C₂) hCtr
  refine ⟨max N₁ N₂, fun s₀ hs₀ D₀ hD₀ Λ A Q hQ hsafe hsize ↦ ?_⟩
  intro n L
  have hL : 2 * L ≤ s₀ := hN₁ s₀ ((le_max_left _ _).trans hs₀)
  have hr : 10 * roundedLogRadius Ctr n ≤ 9 * s₀ := hN₂ s₀ ((le_max_right _ _).trans hs₀)
  have hn : 8 * s₀ ≤ n := by
    have : (8 * s₀ : ℝ) ≤ n :=
      (mul_le_mul_of_nonneg_right hC₂ (Nat.cast_nonneg _)).trans (Nat.le_ceil _)
    exact_mod_cast this
  refine ⟨?_, fun d hd hdL ↦ ?_, hL, fun t ht z hz ↦ ?_⟩
  · have h := card_le_boxSize_sq Q
    rw [hsize] at h
    have : Q.card ≤ n ^ 2 := h.trans (Nat.pow_le_pow_left (by omega) 2)
    exact_mod_cast this
  · have h := hQ.card_ambientDilation_sdiff_le (d := d) (k := 1) hd
    rw [hsize] at h
    omega
  · have hdist := hsafe.lt_dist ht hz
    rw [hsize, dist_eq_max_abs] at hdist
    have hD : (10 * s₀ : ℝ) ≤ D₀ * s₀ := mul_le_mul_of_nonneg_right hD₀ (Nat.cast_nonneg _)
    have hsum : ((2 * L + 10 * roundedLogRadius Ctr n : ℕ) : ℝ) ≤ 10 * s₀ := by
      exact_mod_cast (show 2 * L + 10 * roundedLogRadius Ctr n ≤ 10 * s₀ by omega)
    have : ((2 * L + 10 * roundedLogRadius Ctr n : ℕ) : ℝ) <
        ((ambientSupDistance t z : ℤ) : ℝ) := by
      unfold ambientSupDistance
      linarith
    exact_mod_cast this

end OpenAI.Scan
