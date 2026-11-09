import AreaLaw.S11_Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# §11 Scales

The pitch `s_k`, the strip width `t_k` of layer `k` (layer-cell side `r = 2^k`), and the
scanner scales of primaries, belt tiles and replacements. The collar width
`L = ⌊n^{1-ℓ}⌋₊` is `OpenAI.collarWidth n`.

Digest `digest/11-geometry.md` D11.8, D11.9.4, D11.21, D11.22, D11.24, D11.25.4.
-/

namespace AreaLaw

namespace Geometry

open Filter Topology

/-- D11.8. The pitch of the primaries in layer `k`, `s_k = 2^⌊(1+δ₀)k⌋`. -/
noncomputable def s (k : ℕ) : ℕ := 2 ^ ⌊(1 + δ₀) * k⌋₊

/-- D11.8. The strip width (fine-cell side) in layer `k`, `t_k = 2^⌊ζk⌋`. -/
noncomputable def t (k : ℕ) : ℕ := 2 ^ ⌊ζ * k⌋₊

/-- D11.21. The scanner scale of a primary in layer `k`: `n = ⌈C_P r^{1+2δ₀}⌉`, `r = 2^k`. -/
noncomputable def primaryScale (CP : ℝ) (k : ℕ) : ℕ := ⌈CP * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀)⌉₊

/-- D11.22. The scanner scale of a belt tile or replacement of side scale `u`: `n = ⌈C_B u⌉`. -/
noncomputable def beltScale (CB : ℝ) (u : ℕ) : ℕ := ⌈CB * u⌉₊

/-- `r^y / 2 ≤ 2^⌊yk⌋ ≤ r^y` for `r = 2^k`, `y ≥ 0`. -/
private theorem two_pow_floor_mul (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ((2 : ℝ) ^ k) ^ y / 2 ≤ (2 : ℝ) ^ ⌊y * k⌋₊ ∧ (2 : ℝ) ^ ⌊y * k⌋₊ ≤ ((2 : ℝ) ^ k) ^ y := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (k : ℝ) y,
    ← Real.rpow_natCast]
  refine ⟨?_, Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (by positivity))⟩
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add_one (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.lt_floor_add_one _).le

private theorem s_bounds (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (1 + δ₀) / 2 ≤ s k ∧ (s k : ℝ) ≤ ((2 : ℝ) ^ k) ^ (1 + δ₀) := by
  simpa [s] using two_pow_floor_mul k (y := 1 + δ₀) (by simp only [δ₀]; norm_num)

private theorem t_bounds (k : ℕ) :
    ((2 : ℝ) ^ k) ^ ζ / 2 ≤ t k ∧ (t k : ℝ) ≤ ((2 : ℝ) ^ k) ^ ζ := by
  simpa [t] using two_pow_floor_mul k (y := ζ) (by simp only [ζ, δ₀]; norm_num)

/-- `K x^a < c x^e` for large `x` when `a < e` and `c > 0`. -/
private theorem eventually_mul_rpow_lt (K : ℝ) {c : ℝ} (hc : 0 < c) {a e : ℝ} (hae : a < e) :
    ∀ᶠ x : ℝ in atTop, K * x ^ a < c * x ^ e := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hae)).const_mul K
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hc), eventually_gt_atTop 0] with x hx hx0
  calc K * x ^ a = K * x ^ (-(e - a)) * x ^ e := by
        rw [mul_assoc, ← Real.rpow_add hx0, show -(e - a) + e = a by ring]
    _ < c * x ^ e := mul_lt_mul_of_pos_right hx (Real.rpow_pos_of_pos hx0 _)

/-- The same along `r = 2^k`. -/
private theorem eventually_two_pow (K : ℝ) {c : ℝ} (hc : 0 < c) {a e : ℝ} (hae : a < e) :
    ∀ᶠ k : ℕ in atTop, K * ((2 : ℝ) ^ k) ^ a < c * ((2 : ℝ) ^ k) ^ e :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_mul_rpow_lt K hc hae)

/-- D11.8. For every `k`: `t_k ∣ r ∣ s_k` (`r = 2^k`) and `t_{k+1}/t_k ∈ {1, 2}`; and
`t_k ≪ r ≪ s_k`: `t_k/r → 0` and `r/s_k → 0`. -/
theorem step_11_8 :
    (∀ k, t k ∣ 2 ^ k ∧ 2 ^ k ∣ s k ∧ (t (k + 1) = t k ∨ t (k + 1) = 2 * t k)) ∧
      Tendsto (fun k => (t k : ℝ) / 2 ^ k) atTop (𝓝 0) ∧
      Tendsto (fun k => (2 : ℝ) ^ k / s k) atTop (𝓝 0) := by
  obtain ⟨-, hζ1, -⟩ := eq_exponent_gaps
  have hζ0 : 0 ≤ ζ := by simp only [ζ, δ₀]; norm_num
  have hδ : 0 < δ₀ := by simp only [δ₀]; norm_num
  have h2 := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  refine ⟨fun k => ⟨pow_dvd_pow 2 ?_, pow_dvd_pow 2 ?_, ?_⟩, ?_, ?_⟩
  · exact Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg k) hζ1.le)
  · exact Nat.le_floor (le_mul_of_one_le_left (Nat.cast_nonneg k) (by linarith))
  · -- the floor `⌊ζk⌋` grows by `0` or `1` since `0 ≤ ζ < 1`
    have h1 : ⌊ζ * k⌋₊ ≤ ⌊ζ * ↑(k + 1)⌋₊ :=
      Nat.floor_le_floor (by push_cast; nlinarith)
    have h2 : ⌊ζ * ↑(k + 1)⌋₊ < ⌊ζ * k⌋₊ + 2 := by
      have := Nat.floor_le (show 0 ≤ ζ * ↑(k + 1) by positivity)
      have := Nat.lt_floor_add_one (ζ * k)
      have : (⌊ζ * ↑(k + 1)⌋₊ : ℝ) < ⌊ζ * k⌋₊ + 2 := by push_cast at *; linarith
      exact_mod_cast this
    unfold t
    rcases (show ⌊ζ * ↑(k + 1)⌋₊ = ⌊ζ * k⌋₊ ∨ ⌊ζ * ↑(k + 1)⌋₊ = ⌊ζ * k⌋₊ + 1 by omega) with h | h
    · left; rw [h]
    · right; rw [h, pow_succ, mul_comm]
  · -- `t_k / r ≤ r^{ζ-1}`
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_rpow_neg_atTop (sub_pos.2 hζ1)).comp h2) (fun k => by positivity) fun k => ?_
    have hr : (0 : ℝ) < 2 ^ k := by positivity
    simp only [Function.comp, div_le_iff₀ hr]
    calc (t k : ℝ) ≤ ((2 : ℝ) ^ k) ^ ζ := (t_bounds k).2
      _ = ((2 : ℝ) ^ k) ^ (-(1 - ζ)) * 2 ^ k := by
        rw [← Real.rpow_add_one hr.ne', show -(1 - ζ) + 1 = ζ by ring]
  · -- `r / s_k ≤ 2 r^{-δ₀}`
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ((tendsto_rpow_neg_atTop hδ).comp h2).const_mul 2)
      (fun k => by positivity) fun k => ?_
    have hr : (0 : ℝ) < 2 ^ k := by positivity
    have hs : (0 : ℝ) < s k := by unfold s; positivity
    simp only [div_le_iff₀ hs]
    calc (2 : ℝ) ^ k = 2 * ((2 : ℝ) ^ k) ^ (-δ₀) * (((2 : ℝ) ^ k) ^ (1 + δ₀) / 2) := by
          rw [mul_comm (2 : ℝ), mul_assoc, mul_div_cancel₀ _ two_ne_zero, ← Real.rpow_add hr,
            show -δ₀ + (1 + δ₀) = 1 by ring, Real.rpow_one]
      _ ≤ 2 * ((2 : ℝ) ^ k) ^ (-δ₀) * s k :=
          mul_le_mul_of_nonneg_left (s_bounds k).1 (by positivity)

/-- D11.9.4. `s_k t_k ≥ 2^{-2} 2^{k(2+δ₀/2)}` and `r² = 2^{2k}`, so
`r²/(s_k t_k) ≤ 4·2^{-kδ₀/2}`.
2D only: `r²` is the number of fine-cell rows times columns of a planar `r`-cell; in `ℤ^d` the
decay needs `ζ > 1 - δ₀/(d-1)`. -/
theorem step_11_9_4 (k : ℕ) :
    ((2 : ℝ) ^ k) ^ 2 / (s k * t k) ≤ 4 * (2 : ℝ) ^ (-(k * δ₀ / 2)) := by
  set r : ℝ := 2 ^ k with hr_def
  have hr : 0 < r := by positivity
  have hst0 : (0 : ℝ) < s k * t k := by unfold s t; push_cast; positivity
  have e : (2 : ℝ) ^ (-(k * δ₀ / 2)) = r ^ (-(δ₀ / 2)) := by
    rw [show -(k * δ₀ / 2) = (k : ℝ) * (-(δ₀ / 2)) by ring,
      Real.rpow_natCast_mul (by norm_num)]
  -- D11.9.4: `s_k t_k ≥ r^{2+δ₀/2} / 4`
  have hst : r ^ (2 + δ₀ / 2) / 4 ≤ s k * t k := by
    calc r ^ (2 + δ₀ / 2) / 4 = (r ^ (1 + δ₀) / 2) * (r ^ ζ / 2) := by
          rw [div_mul_div_comm, ← Real.rpow_add hr, show 1 + δ₀ + ζ = 2 + δ₀ / 2 by
            simp only [ζ]; ring]
          norm_num
      _ ≤ s k * t k := mul_le_mul (s_bounds k).1 (t_bounds k).1 (by positivity) (by positivity)
  rw [e, div_le_iff₀ hst0]
  calc r ^ 2 = 4 * r ^ (-(δ₀ / 2)) * (r ^ (2 + δ₀ / 2) / 4) := by
        rw [mul_comm (4 : ℝ), mul_assoc, mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0),
          ← Real.rpow_add hr, show -(δ₀ / 2) + (2 + δ₀ / 2) = (2 : ℕ) by norm_num,
          Real.rpow_natCast]
    _ ≤ 4 * r ^ (-(δ₀ / 2)) * (s k * t k) := mul_le_mul_of_nonneg_left hst (by positivity)

/-- D11.21.1. `s_k/r = 2^{⌊(1+δ₀)k⌋-k} ≤ r^{δ₀}`, so `N₀ ≤ C(s_k/r+2)²` (D11.10) gives
`N₀ ≤ C(r^{δ₀}+2)² ≤ 9C r^{2δ₀}`. -/
theorem step_11_21_1 (k : ℕ) {C N₀ : ℝ} (hC : 0 ≤ C)
    (hN₀ : N₀ ≤ C * ((s k : ℝ) / 2 ^ k + 2) ^ 2) :
    (s k : ℝ) / 2 ^ k ≤ ((2 : ℝ) ^ k) ^ δ₀ ∧ N₀ ≤ C * (((2 : ℝ) ^ k) ^ δ₀ + 2) ^ 2 ∧
      N₀ ≤ 9 * C * ((2 : ℝ) ^ k) ^ (2 * δ₀) := by
  have hr : (0 : ℝ) < 2 ^ k := by positivity
  have hδ : 0 ≤ δ₀ := by simp only [δ₀]; norm_num
  have h1 : (s k : ℝ) / 2 ^ k ≤ ((2 : ℝ) ^ k) ^ δ₀ := by
    rw [div_le_iff₀ hr, ← Real.rpow_add_one hr.ne', add_comm δ₀]
    exact (s_bounds k).2
  have h2 : N₀ ≤ C * (((2 : ℝ) ^ k) ^ δ₀ + 2) ^ 2 :=
    hN₀.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) hC)
  refine ⟨h1, h2, h2.trans ?_⟩
  have h3 : 1 ≤ ((2 : ℝ) ^ k) ^ δ₀ := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hδ
  rw [mul_comm 2 δ₀, show δ₀ * 2 = δ₀ * ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_mul_natCast hr.le, mul_assoc]
  have h4 : (((2 : ℝ) ^ k) ^ δ₀ + 2) ^ 2 ≤ 9 * (((2 : ℝ) ^ k) ^ δ₀) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hC]

/-- D11.21.2. With `s₀ = r = 2^k` and `N₀ ≤ 9C r^{2δ₀}`:
`C_tpl N₀ (s₀+1) ≤ 2C_tpl·9C r^{1+2δ₀} ≤ n` for `C_P ≥ 18 C C_tpl`, and
`s_k ≤ r^{1+δ₀} ≤ r^{1+2δ₀} ≤ n` (`C_P ≥ 1`). -/
theorem step_11_21_2 (k : ℕ) {CP C Ctpl N₀ : ℝ} (hC : 0 ≤ C) (hCtpl : 0 ≤ Ctpl)
    (hN₀ : N₀ ≤ 9 * C * ((2 : ℝ) ^ k) ^ (2 * δ₀)) (hCP : 18 * C * Ctpl ≤ CP) (hCP1 : 1 ≤ CP) :
    Ctpl * N₀ * (2 ^ k + 1) ≤ primaryScale CP k ∧ s k ≤ primaryScale CP k := by
  have hr1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hr : (0 : ℝ) < 2 ^ k := by positivity
  have hδ : 0 ≤ δ₀ := by simp only [δ₀]; norm_num
  have hceil := Nat.le_ceil (CP * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀))
  have hpow : ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) = ((2 : ℝ) ^ k) ^ (2 * δ₀) * 2 ^ k := by
    rw [← Real.rpow_add_one hr.ne', add_comm]
  have hp0 : 0 ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := by positivity
  constructor
  · -- D11.21.2
    calc Ctpl * N₀ * (2 ^ k + 1) ≤ Ctpl * (9 * C * ((2 : ℝ) ^ k) ^ (2 * δ₀)) * (2 * 2 ^ k) := by
          have : 0 ≤ Ctpl * (9 * C * ((2 : ℝ) ^ k) ^ (2 * δ₀)) := by positivity
          calc Ctpl * N₀ * (2 ^ k + 1) ≤ Ctpl * (9 * C * ((2 : ℝ) ^ k) ^ (2 * δ₀)) * (2 ^ k + 1) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN₀ hCtpl) (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) this
      _ = 18 * C * Ctpl * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := by rw [hpow]; ring
      _ ≤ CP * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := mul_le_mul_of_nonneg_right hCP hp0
      _ ≤ _ := hceil
  · have : (s k : ℝ) ≤ primaryScale CP k :=
      calc (s k : ℝ) ≤ ((2 : ℝ) ^ k) ^ (1 + δ₀) := (s_bounds k).2
        _ ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
        _ ≤ CP * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := le_mul_of_one_le_left hp0 hCP1
        _ ≤ _ := hceil
    exact_mod_cast this

/-- `n^γ ≤ (C_P+1)^γ r^{(1+2δ₀)γ}` for the primary scale `n`. -/
private theorem primaryScale_rpow_le {CP : ℝ} (hCP : 0 ≤ CP) (k : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (primaryScale CP k : ℝ) ^ γ ≤ (CP + 1) ^ γ * ((2 : ℝ) ^ k) ^ ((1 + 2 * δ₀) * γ) := by
  have hr1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hδ : 0 ≤ δ₀ := by simp only [δ₀]; norm_num
  have h1 : 1 ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := Real.one_le_rpow hr1 (by linarith)
  have hn : (primaryScale CP k : ℝ) ≤ (CP + 1) * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ CP * ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) by positivity)
    unfold primaryScale
    nlinarith
  rw [Real.rpow_mul (by positivity), ← Real.mul_rpow (by linarith) (by positivity)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hn hγ

/-- D11.21.4. `n^{1-ℓ} ≤ C r^{(1+2δ₀)(1-ℓ)} = o(r)`; `n^β ≤ C r^{(1+2δ₀)β} = o(t_k)`;
`n^β = o(r)`; in particular `L = ⌊n^{1-ℓ}⌋ ≤ s₀ = r`. -/
theorem step_11_21_4 {CP : ℝ} (hCP : 0 ≤ CP) {c : ℝ} (hc : 0 < c) :
    (∀ᶠ k in atTop, (⌊(primaryScale CP k : ℝ) ^ (1 - ℓ)⌋₊ : ℝ) ≤ c * 2 ^ k) ∧
      (∀ᶠ k in atTop, (primaryScale CP k : ℝ) ^ β ≤ c * t k) ∧
      (∀ᶠ k in atTop, (primaryScale CP k : ℝ) ^ β ≤ c * 2 ^ k) ∧
      ∀ᶠ k in atTop, ⌊(primaryScale CP k : ℝ) ^ (1 - ℓ)⌋₊ ≤ 2 ^ k := by
  obtain ⟨hβζ, hζ1, hℓ, -, -, -⟩ := eq_exponent_gaps
  have hℓ0 : 0 ≤ 1 - ℓ := by simp only [ℓ]; norm_num
  have hβ0 : 0 ≤ β := by simp only [β]; norm_num
  have hL : ∀ c > 0, ∀ᶠ k in atTop,
      (⌊(primaryScale CP k : ℝ) ^ (1 - ℓ)⌋₊ : ℝ) ≤ c * 2 ^ k := fun c hc => by
    filter_upwards [eventually_two_pow ((CP + 1) ^ (1 - ℓ)) hc hℓ] with k hk
    rw [Real.rpow_one] at hk
    exact (Nat.floor_le (by positivity)).trans ((primaryScale_rpow_le hCP k hℓ0).trans hk.le)
  have hnr : ∀ c > 0, ∀ᶠ k in atTop, (primaryScale CP k : ℝ) ^ β ≤ c * 2 ^ k := fun c hc => by
    filter_upwards [eventually_two_pow ((CP + 1) ^ β) hc (hβζ.trans hζ1)] with k hk
    rw [Real.rpow_one] at hk
    exact (primaryScale_rpow_le hCP k hβ0).trans hk.le
  refine ⟨hL c hc, ?_, hnr c hc, ?_⟩
  · filter_upwards [eventually_two_pow ((CP + 1) ^ β) (half_pos hc) hβζ] with k hk
    calc (primaryScale CP k : ℝ) ^ β ≤ c / 2 * ((2 : ℝ) ^ k) ^ ζ :=
          (primaryScale_rpow_le hCP k hβ0).trans hk.le
      _ = c * (((2 : ℝ) ^ k) ^ ζ / 2) := by ring
      _ ≤ c * t k := mul_le_mul_of_nonneg_left (t_bounds k).1 hc.le
  · filter_upwards [hL 1 one_pos] with k hk
    exact_mod_cast (one_mul (2 ^ k : ℝ)) ▸ hk

/-- D11.22.1. `N₀ ≤ 8` and `s₀ ≤ 2u`: `C_tpl N₀ (s₀+1) ≤ 8C_tpl(2u+1) ≤ 24C_tpl u ≤ n` for
`C_B ≥ 24 C_tpl` (`u ≥ 1`). -/
theorem step_11_22_1 {CB Ctpl : ℝ} (hCtpl : 0 ≤ Ctpl) (hCB : 24 * Ctpl ≤ CB) {u N₀ s₀ : ℕ}
    (hu : 1 ≤ u) (hN₀ : N₀ ≤ 8) (hs₀ : s₀ ≤ 2 * u) :
    Ctpl * N₀ * (s₀ + 1) ≤ beltScale CB u := by
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hN : (N₀ : ℝ) ≤ 8 := by exact_mod_cast hN₀
  have hs : (s₀ : ℝ) ≤ 2 * u := by exact_mod_cast hs₀
  calc Ctpl * N₀ * (s₀ + 1) ≤ Ctpl * 8 * (2 * u + 1) := by gcongr
    _ ≤ 24 * Ctpl * u := by nlinarith
    _ ≤ CB * u := mul_le_mul_of_nonneg_right hCB (by positivity)
    _ ≤ _ := Nat.le_ceil _

/-- D11.22.2. `diam_∞ ≤ 2u ≤ n` for `C_B ≥ 2`. -/
theorem step_11_22_2 {CB : ℝ} (hCB : 2 ≤ CB) (u : ℕ) : 2 * u ≤ beltScale CB u := by
  have : ((2 * u : ℕ) : ℝ) ≤ beltScale CB u := by
    push_cast
    exact (mul_le_mul_of_nonneg_right hCB (Nat.cast_nonneg u)).trans (Nat.le_ceil _)
  exact_mod_cast this

/-- `n^γ ≤ (C_B+1)^γ u^γ` for the belt scale `n`, `u ≥ 1`. -/
private theorem beltScale_rpow_le {CB : ℝ} (hCB : 0 ≤ CB) {u : ℕ} (hu : 1 ≤ u) {γ : ℝ}
    (hγ : 0 ≤ γ) : (beltScale CB u : ℝ) ^ γ ≤ (CB + 1) ^ γ * (u : ℝ) ^ γ := by
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hn : (beltScale CB u : ℝ) ≤ (CB + 1) * u := by
    have := Nat.ceil_lt_add_one (show 0 ≤ CB * u by positivity)
    unfold beltScale
    nlinarith
  rw [← Real.mul_rpow (by linarith) (by positivity)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hn hγ

/-- D11.22.3. `L = ⌊n^{1-ℓ}⌋ ≤ (C_B u+1)^{1-ℓ} = o(u)`. -/
theorem step_11_22_3 {CB : ℝ} (hCB : 0 ≤ CB) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ u : ℕ in atTop, (⌊(beltScale CB u : ℝ) ^ (1 - ℓ)⌋₊ : ℝ) ≤ c * u := by
  have hℓ0 : 0 ≤ 1 - ℓ := by simp only [ℓ]; norm_num
  have hℓ : 1 - ℓ < 1 := by simp only [ℓ]; norm_num
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_mul_rpow_lt ((CB + 1) ^ (1 - ℓ)) hc hℓ), eventually_ge_atTop 1] with u hu hu1
  rw [Real.rpow_one] at hu
  exact (Nat.floor_le (by positivity)).trans ((beltScale_rpow_le hCB hu1 hℓ0).trans hu.le)

/-- D11.24 (`geometry:fine-clearance`). For `c₁ > 0`, `c₁u^{ρ₀} > 2⌈C_B u⌉^β` for all large
`u`: `2⌈C_B u⌉^β ≤ C u^β` and `ρ₀ > β`. -/
theorem step_11_24 {CB : ℝ} (hCB : 0 ≤ CB) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∀ᶠ u : ℕ in atTop, 2 * (beltScale CB u : ℝ) ^ β < c₁ * (u : ℝ) ^ ρ₀ := by
  obtain ⟨-, -, -, -, hβρ, -⟩ := eq_exponent_gaps
  have hβ0 : 0 ≤ β := by simp only [β]; norm_num
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_mul_rpow_lt (2 * (CB + 1) ^ β) hc₁ hβρ), eventually_ge_atTop 1] with u hu hu1
  calc 2 * (beltScale CB u : ℝ) ^ β ≤ 2 * ((CB + 1) ^ β * (u : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left (beltScale_rpow_le hCB hu1 hβ0) (by norm_num)
    _ = 2 * (CB + 1) ^ β * (u : ℝ) ^ β := by ring
    _ < _ := hu

/-- D11.25.4. `∑_k 2^{-100(1+2δ₀)k}` converges, so `C b ∑_{k ≥ k₀} 2^{-100(1+2δ₀)k} ≤ C' b`
with `C'` independent of `b` and `k₀`. -/
theorem step_11_25_4 :
    Summable (fun k : ℕ => (2 : ℝ) ^ (-(100 * (1 + 2 * δ₀) * k))) ∧
      ∀ C : ℝ, 0 ≤ C → ∃ C' : ℝ, ∀ b : ℝ, 0 ≤ b → ∀ k₀ : ℕ,
        C * b * ∑' k : ℕ, (2 : ℝ) ^ (-(100 * (1 + 2 * δ₀) * (k₀ + k : ℕ))) ≤ C' * b := by
  set q : ℝ := (2 : ℝ) ^ (-(100 * (1 + 2 * δ₀)))
  have hterm : ∀ m : ℕ, (2 : ℝ) ^ (-(100 * (1 + 2 * δ₀) * m)) = q ^ m := fun m => by
    rw [neg_mul_eq_neg_mul, Real.rpow_mul_natCast (by norm_num)]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by simp only [δ₀]; norm_num)
  have hsum := summable_geometric_of_lt_one hq0 hq1
  refine ⟨by simpa only [hterm] using hsum, fun C hC => ⟨C * ∑' k : ℕ, q ^ k, fun b hb k₀ => ?_⟩⟩
  simp only [hterm, pow_add, tsum_mul_left]
  calc C * b * (q ^ k₀ * ∑' k : ℕ, q ^ k) ≤ C * b * (1 * ∑' k : ℕ, q ^ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le)
          (tsum_nonneg fun k => pow_nonneg hq0 k)) (by positivity)
    _ = (C * ∑' k : ℕ, q ^ k) * b := by ring

end Geometry

end AreaLaw
