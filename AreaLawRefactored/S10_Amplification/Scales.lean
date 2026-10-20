import AreaLawRefactored.S10_Amplification.Setup

/-!
# §10 The scales: clock time, radius, failure probabilities, containment

Digest `digest/10-amplification.md` (D10.11, D10.12.4, D10.13.6, D10.14.4, D10.15.5–6, D10.16),
paper `paper/sections/09-amplification.tex` lines 449–499 and 547–575. Real arithmetic, except
the containment D10.16.3, which is graph-level, with its `ℤ²` form for the frozen statements.
-/

namespace AreaLaw

open Real Finset

/-! ## D10.11 Clock time and radius -/

/-- D10.11. `t_* = C (𝓘 + w + K log n)`, `w = n^{3/5}`. -/
noncomputable def tStar (C 𝓘 : ℝ) (K n : ℕ) : ℝ := C * (𝓘 + (n : ℝ) ^ (3 / 5 : ℝ) + K * Real.log n)

/-- D10.11. `r = ⌈(C' (t_* + K log n))^{1/α}⌉`. -/
noncomputable def radius (C C' 𝓘 a : ℝ) (K n : ℕ) : ℕ :=
  ⌈(C' * (tStar C 𝓘 K n + K * Real.log n)) ^ (1 / a)⌉₊

/-- D10.11. Run the clocks of Lemma 10.1 with `S = S₀` for time and radius
`t_* = C (𝓘 + w + K log n)`, `r = ⌈(C' (t_* + K log n))^{1/α}⌉`, `C` then `C'` chosen large.
Requirements: `C ≥ max {6/g, 2}` (so `g t_* ≥ 𝓘 + 3w + 6K log n` and `log M₀ ≤ t_*`) and `C'`
large enough that `c C' (t_* + K log n) ≥ log M₀ + v t_* + 3K log n + log poly`, with `poly` the
prefactor `C t_* |S₀| (1 + r)^2` of D10.2 (B) and (A), so
`C t_* |S₀| (1 + r)^2 M₀ e^{v t_* - c r^α} ≤ n^{-3K}`. Moreover `r ≤ C_M n^{(1-ε)/α}`. -/
theorem step_10_11 {g v c a : ℝ} (hg : 0 < g) (hv : 0 ≤ v) (hc : 0 < c) (ha : 0 < a)
    (_ha1 : a ≤ 1) {CA CB C₀ : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hC₀ : 0 < C₀) (d m₀ K : ℕ)
    (hK : 1 ≤ K) :
    ∃ C C' Cr : ℝ, 0 < C ∧ 0 < C' ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓘 : ℝ, 0 ≤ 𝓘 →
      𝓘 ≤ C₀ * (n : ℝ) ^ (1 - ε) →
      let w := (n : ℝ) ^ (3 / 5 : ℝ)
      let M₀ := Real.exp ((𝓘 + 3 * w) / 2)
      let t := tStar C 𝓘 K n
      let r := radius C C' 𝓘 a K n
      0 ≤ t ∧ 1 ≤ r ∧ 1 ≤ M₀ ∧
      M₀ ^ 2 * Real.exp (-g * t) ≤ ((n : ℝ) ^ (6 * K))⁻¹ ∧
      CB * t * (C₀ * (n : ℝ) ^ d) * M₀ * Real.exp (v * t - c * (r : ℝ) ^ a) ≤
        ((n : ℝ) ^ (3 * K))⁻¹ ∧
      M₀ * (CA * t * (C₀ * (n : ℝ) ^ d) * ((r : ℝ) + 1) ^ m₀ * Real.exp (-c * (r : ℝ) ^ a)) ≤
        ((n : ℝ) ^ (3 * K))⁻¹ ∧
      (r : ℝ) ≤ Cr * (n : ℝ) ^ ((1 - ε) / a) := by
  set C : ℝ := 6 / g + 2 with hCdef
  set B₁ : ℝ := C * (C₀ + 1 + 2 * K) + 2 * K with hB₁def
  set C' : ℝ := (v + d + 6 + m₀ / a) / c with hC'def
  set Cr : ℝ := (C' * B₁) ^ (1 / a) + 1 with hCrdef
  have hC : 2 ≤ C := by have := div_pos (by norm_num : (0 : ℝ) < 6) hg; linarith
  have hgC : g * C = 6 + 2 * g := by rw [hCdef]; field_simp
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hC' : 0 < C' := by positivity
  have hcC' : c * C' = v + d + 6 + m₀ / a := by rw [hC'def]; field_simp
  have hB₁ : 0 ≤ B₁ := by positivity
  have hCr : 1 ≤ Cr := by have := rpow_nonneg (mul_nonneg hC'.le hB₁) (1 / a); linarith
  clear_value C B₁ C' Cr
  refine ⟨C, C', Cr, by linarith, hC', max 2 ⌈CB * C₀ + CA * C₀ * (2 * Cr) ^ m₀⌉₊, ?_⟩
  intro n hn 𝓘 h𝓘0 h𝓘
  dsimp only
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnn : CB * C₀ + CA * C₀ * (2 * Cr) ^ m₀ ≤ exp (log n) := by
    rw [exp_log hn0]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  set L := log n with hLdef
  set w := (n : ℝ) ^ (3 / 5 : ℝ)
  set u := (n : ℝ) ^ (1 - ε)
  set t := tStar C 𝓘 K n with htdef
  have hL : 0 ≤ L := log_nonneg hn1
  have hKL : 0 ≤ K * L := by positivity
  have hw0 : 0 < w := rpow_pos_of_pos hn0 _
  have hε : (1 : ℝ) - ε = 99999 / 100000 := by norm_num [ε]
  have hwu : w ≤ u := rpow_le_rpow_of_exponent_le hn1 (by rw [hε]; norm_num)
  have h1ε : (1 : ℝ) / 2 ≤ 1 - ε := by rw [hε]; norm_num
  have hu : 0 ≤ u := rpow_nonneg hn0.le _
  have hLu : L ≤ 2 * u := by
    have h := log_le_rpow_div hn0.le (by linarith : (0 : ℝ) < 1 - ε)
    have h' : u / (1 - ε) ≤ 2 * u := by
      rw [div_le_iff₀ (by linarith)]
      linarith [mul_le_mul_of_nonneg_left h1ε hu]
    exact h.trans h'
  have hS0 : 0 < 𝓘 + w + K * L := by linarith
  have ht : t = C * (𝓘 + w + K * L) := rfl
  have ht0 : 0 < t := by rw [ht]; positivity
  have hnd : (n : ℝ) ^ d = exp (d * L) := by rw [exp_nat_mul, exp_log hn0]
  have hinv : ∀ j : ℕ, ((n : ℝ) ^ j)⁻¹ = exp (-(j * L)) := fun j => by
    rw [exp_neg, exp_nat_mul, exp_log hn0]
  obtain ⟨x, hxdef⟩ : ∃ x, x = C' * (t + K * L) := ⟨_, rfl⟩
  have hx : 0 < x := by rw [hxdef]; positivity
  have hrx : x ^ (1 / a) ≤ radius C C' 𝓘 a K n := by rw [hxdef]; exact Nat.le_ceil _
  have hr1 : 1 ≤ radius C C' 𝓘 a K n := by
    have := rpow_pos_of_pos hx (1 / a)
    rw [hxdef] at this
    exact Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 this))
  have hr2 : (radius C C' 𝓘 a K n : ℝ) < x ^ (1 / a) + 1 := by
    have := hx.le
    rw [hxdef] at this ⊢
    exact Nat.ceil_lt_add_one (rpow_nonneg this _)
  generalize radius C C' 𝓘 a K n = r at hrx hr1 hr2 ⊢
  have hue : (n : ℝ) ^ ((1 - ε) / a) = u ^ (1 / a) := by
    rw [div_eq_mul_one_div (1 - ε) a]; exact rpow_mul hn0.le _ _
  clear_value L w u t
  -- D10.11.1
  have hT : t + K * L ≤ B₁ * u := by
    rw [hB₁def]
    have h1 : 𝓘 + w + K * L ≤ (C₀ + 1 + 2 * K) * u := by
      linarith [mul_le_mul_of_nonneg_left hLu (Nat.cast_nonneg (α := ℝ) K)]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ C)
    linarith [mul_le_mul_of_nonneg_left hLu (Nat.cast_nonneg (α := ℝ) K)]
  have hrCr : (r : ℝ) ≤ Cr * (n : ℝ) ^ ((1 - ε) / a) := by
    have h1 : x ^ (1 / a) ≤ (C' * B₁) ^ (1 / a) * (n : ℝ) ^ ((1 - ε) / a) := by
      rw [hue, ← mul_rpow (by positivity) hu]
      refine rpow_le_rpow hx.le ?_ (by positivity)
      rw [hxdef]
      exact (mul_le_mul_of_nonneg_left hT hC'.le).trans_eq (by ring)
    have h3 : 1 ≤ (n : ℝ) ^ ((1 - ε) / a) := one_le_rpow hn1 (by rw [hε]; positivity)
    calc (r : ℝ) ≤ (C' * B₁) ^ (1 / a) * (n : ℝ) ^ ((1 - ε) / a) + (n : ℝ) ^ ((1 - ε) / a) := by
          linarith
      _ = Cr * (n : ℝ) ^ ((1 - ε) / a) := by rw [hCrdef]; ring
  -- D10.11.2
  have hpoly : ((r : ℝ) + 1) ^ m₀ ≤ (2 * Cr) ^ m₀ * exp (m₀ / a * L) := by
    have h1 : (n : ℝ) ^ ((1 - ε) / a) ≤ (n : ℝ) ^ (1 / a) :=
      rpow_le_rpow_of_exponent_le hn1 (div_le_div_of_nonneg_right (by rw [hε]; norm_num) ha.le)
    have h3 : 1 ≤ (n : ℝ) ^ ((1 - ε) / a) := one_le_rpow hn1 (by rw [hε]; positivity)
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Cr)
    have h5 : Cr ≤ Cr * (n : ℝ) ^ (1 / a) := le_mul_of_one_le_right (by linarith) (h3.trans h1)
    have h2 : (r : ℝ) + 1 ≤ 2 * Cr * (n : ℝ) ^ (1 / a) := by linarith
    calc ((r : ℝ) + 1) ^ m₀ ≤ (2 * Cr * (n : ℝ) ^ (1 / a)) ^ m₀ := by gcongr
      _ = (2 * Cr) ^ m₀ * exp (m₀ / a * L) := by
        rw [mul_pow, rpow_def_of_pos hn0, ← exp_nat_mul, hLdef]; ring_nf
  -- D10.11.3
  have hM₀ : exp ((𝓘 + 3 * w) / 2) ≤ exp t :=
    exp_le_exp.2 (by rw [ht]; linarith [mul_le_mul_of_nonneg_right hC hS0.le])
  have htexp : t ≤ exp t := by linarith [add_one_le_exp t]
  -- D10.11.4
  have hra : (v + d + 6 + m₀ / a) * (t + K * L) ≤ c * (r : ℝ) ^ a := by
    rw [← hcC', mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    rw [← hxdef]
    calc x = (x ^ (1 / a)) ^ a := by rw [← rpow_mul hx.le, one_div_mul_cancel ha.ne', rpow_one]
      _ ≤ (r : ℝ) ^ a := rpow_le_rpow (by positivity) hrx ha.le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hma : 0 ≤ (m₀ : ℝ) / a := by positivity
  have hK1L : 0 ≤ ((K : ℝ) - 1) * L := mul_nonneg (by linarith) hL
  refine ⟨ht0.le, hr1, one_le_exp (by positivity), ?_, ?_, ?_, hrCr⟩
  · -- D10.12.1 exponent: `M₀² e^{-g t_*} ≤ n^{-6K}`
    have hgt : g * t = (6 + 2 * g) * (𝓘 + w + K * L) := by rw [ht, ← mul_assoc, hgC]
    rw [hinv, sq, ← exp_add, ← exp_add, exp_le_exp]
    push_cast
    linarith [mul_nonneg hg.le hS0.le]
  · have h1 : CB * C₀ ≤ exp L := by
      linarith [mul_nonneg (mul_nonneg hCA hC₀.le) (pow_nonneg (by linarith : (0 : ℝ) ≤ 2 * Cr) m₀)]
    have hA := mul_le_mul (mul_le_mul (mul_le_mul h1 htexp ht0.le (exp_pos _).le) hnd.le
      (by positivity) (by positivity)) hM₀ (by positivity) (by positivity)
    calc CB * t * (C₀ * (n : ℝ) ^ d) * exp ((𝓘 + 3 * w) / 2) * exp (v * t - c * (r : ℝ) ^ a)
        = (CB * C₀) * t * (n : ℝ) ^ d * exp ((𝓘 + 3 * w) / 2) *
            exp (v * t - c * (r : ℝ) ^ a) := by ring
      _ ≤ exp L * exp t * exp (d * L) * exp t * exp (v * t - c * (r : ℝ) ^ a) :=
          mul_le_mul_of_nonneg_right hA (exp_pos _).le
      _ = exp (L + t + d * L + t + (v * t - c * (r : ℝ) ^ a)) := by simp only [exp_add]
      _ ≤ exp (-(((3 * K : ℕ) : ℝ) * L)) := by
          rw [exp_le_exp]
          push_cast
          linarith [mul_nonneg hd0 hK1L, mul_nonneg hv hKL, mul_nonneg hma ht0.le,
            mul_nonneg hd0 ht0.le, mul_nonneg hma hKL]
      _ = _ := (hinv _).symm
  · have h1 : CA * C₀ * (2 * Cr) ^ m₀ ≤ exp L := by linarith [mul_nonneg hCB hC₀.le]
    have hCA₀ : 0 ≤ CA * C₀ := mul_nonneg hCA hC₀.le
    have hA := mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left htexp hCA₀) hnd.le
      (by positivity) (by positivity)) hM₀ (by positivity) (by positivity)) hpoly
      (by positivity) (by positivity)
    calc exp ((𝓘 + 3 * w) / 2) * (CA * t * (C₀ * (n : ℝ) ^ d) * ((r : ℝ) + 1) ^ m₀ *
          exp (-c * (r : ℝ) ^ a))
        = (CA * C₀) * t * (n : ℝ) ^ d * exp ((𝓘 + 3 * w) / 2) * ((r : ℝ) + 1) ^ m₀ *
            exp (-c * (r : ℝ) ^ a) := by ring
      _ ≤ (CA * C₀) * exp t * exp (d * L) * exp t * ((2 * Cr) ^ m₀ * exp (m₀ / a * L)) *
            exp (-c * (r : ℝ) ^ a) := mul_le_mul_of_nonneg_right hA (exp_pos _).le
      _ = (CA * C₀ * (2 * Cr) ^ m₀) * exp (t + d * L + t + m₀ / a * L + -c * (r : ℝ) ^ a) := by
          simp only [exp_add]; ring
      _ ≤ exp L * exp (t + d * L + t + m₀ / a * L + -c * (r : ℝ) ^ a) :=
          mul_le_mul_of_nonneg_right h1 (exp_pos _).le
      _ = exp (L + (t + d * L + t + m₀ / a * L + -c * (r : ℝ) ^ a)) := (exp_add _ _).symm
      _ ≤ exp (-(((3 * K : ℕ) : ℝ) * L)) := by
          rw [exp_le_exp]
          push_cast
          linarith [mul_nonneg hd0 hK1L, mul_nonneg hv hKL, mul_nonneg hma ht0.le,
            mul_nonneg hd0 ht0.le, mul_nonneg hma hK1L, mul_nonneg hv ht0.le]
      _ = _ := (hinv _).symm

/-! ## D10.12.4 Union bound -/

/-- D10.12.4. Union bound: failure `≤ n^{-4K} + 2 n^{-2K} < 1` for large `n`; here
`n^{-6K}/(n^{-K})^2 + 2 n^{-3K}/n^{-K}`, the three Markov bounds with thresholds `n^{-2K}`
(squared norm) and `n^{-K}`. -/
theorem step_10_12_4 {K n : ℕ} (hK : 1 ≤ K) (hn : 2 ≤ n) :
    ((n : ℝ) ^ (6 * K))⁻¹ / (((n : ℝ) ^ K)⁻¹) ^ 2 +
      2 * (((n : ℝ) ^ (3 * K))⁻¹ / ((n : ℝ) ^ K)⁻¹) < 1 := by
  have hy : (2 : ℝ) ≤ (n : ℝ) ^ K :=
    (by exact_mod_cast hn : (2 : ℝ) ≤ n).trans
      (le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ n)) (by omega))
  rw [pow_mul', pow_mul']
  set y := (n : ℝ) ^ K
  have hy0 : 0 < y := by linarith
  field_simp
  nlinarith [mul_pos hy0 hy0, mul_pos (mul_pos hy0 hy0) hy0]

/-! ## D10.13.6, D10.14.4 Constants -/

/-- D10.13.6, D10.14.4. `14 n^{-K} + 9 n^{-2K} ≤ 23 n^{-K}`, and
`√(23 n^{-K}) + 4 n^{-K} ≤ 9 n^{-K/2}`. -/
theorem step_10_13_6' :
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 14 * x + 9 * x ^ 2 ≤ 23 * x) ∧
    ∀ n K : ℕ, 1 ≤ n →
      √(23 * ((n : ℝ) ^ K)⁻¹) + 4 * ((n : ℝ) ^ K)⁻¹ ≤ 9 * √(((n : ℝ) ^ K)⁻¹) := by
  refine ⟨fun x hx0 hx1 => by nlinarith, fun n K hn => ?_⟩
  set y := ((n : ℝ) ^ K)⁻¹
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn))
  have h23 : √23 ≤ 5 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have hyy : y ≤ √y := by
    rw [le_sqrt hy0 hy0]; nlinarith
  rw [sqrt_mul (by norm_num)]
  nlinarith [sqrt_nonneg y]

/-! ## D10.15.5–6 The mutual information exponent -/

/-- D10.15.5–6. `log dim e' ≤ C₀ n^d log q`; with `K ≥ 4 (M + d + 1)` the continuity bound
`2 · 4 √δ' log(e dim e')`, `δ' = 9 n^{-K/2}`, is `≤ 24 (1 + C₀ log q) n^{-M}`. -/
theorem step_10_15_6 {n M d K : ℕ} (hn : 1 ≤ n) (hK : 4 * (M + d + 1) ≤ K) {C₀ q D : ℝ}
    (hC₀ : 0 ≤ C₀) (hq : 1 ≤ q) (hD : 1 ≤ D) (hDq : log D ≤ C₀ * (n : ℝ) ^ d * log q) :
    8 * √(9 * √(((n : ℝ) ^ K)⁻¹)) * log (exp 1 * D) ≤
      24 * (1 + C₀ * log q) * ((n : ℝ) ^ M)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (n : ℝ) ^ (M + d + 1) := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; positivity
  -- D10.15.5
  have hδ : √(9 * √(((n : ℝ) ^ K)⁻¹)) ≤ 3 * N⁻¹ := by
    have h1 : ((n : ℝ) ^ K)⁻¹ ≤ ((N ^ 2)⁻¹) ^ 2 := by
      rw [show ((N ^ 2)⁻¹) ^ 2 = ((n : ℝ) ^ (4 * (M + d + 1)))⁻¹ by
        rw [hNdef, inv_pow, ← pow_mul, ← pow_mul]; ring_nf]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 hK)
    have h2 : √(((n : ℝ) ^ K)⁻¹) ≤ (N ^ 2)⁻¹ :=
      (sqrt_le_sqrt h1).trans_eq (sqrt_sq (by positivity))
    calc √(9 * √(((n : ℝ) ^ K)⁻¹)) ≤ √((3 * N⁻¹) ^ 2) := by
          refine sqrt_le_sqrt ?_
          rw [mul_pow, inv_pow]; linarith
      _ = 3 * N⁻¹ := sqrt_sq (by positivity)
  have hlog : log (exp 1 * D) = 1 + log D := by
    rw [log_mul (exp_pos 1).ne' (by linarith), log_exp]
  have hlogD : 0 ≤ log D := log_nonneg hD
  have hlq : 0 ≤ log q := log_nonneg hq
  -- D10.15.6
  have hpow : 1 + log D ≤ (1 + C₀ * log q) * (n : ℝ) ^ (d + 1) := by
    have h1 : 1 ≤ (n : ℝ) ^ (d + 1) := one_le_pow₀ hn1
    have h2 : (n : ℝ) ^ d ≤ (n : ℝ) ^ (d + 1) := pow_le_pow_right₀ hn1 (by omega)
    nlinarith [mul_nonneg hC₀ hlq, mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₀ hlq)]
  have hNM : N = (n : ℝ) ^ M * (n : ℝ) ^ (d + 1) := by rw [hNdef, ← pow_add, add_assoc]
  rw [hlog]
  calc 8 * √(9 * √(((n : ℝ) ^ K)⁻¹)) * (1 + log D) ≤ 8 * (3 * N⁻¹) * (1 + log D) := by
        gcongr
    _ = 24 * ((1 + log D) / (n : ℝ) ^ (d + 1)) * ((n : ℝ) ^ M)⁻¹ := by
        rw [hNM]; field_simp; ring
    _ ≤ 24 * (1 + C₀ * log q) * ((n : ℝ) ^ M)⁻¹ := by
        gcongr
        rw [div_le_iff₀ (by positivity)]; exact hpow

/-! ## D10.16 Radius bounds and containment in `A` -/

/-- D10.16.2. `α > 1 - 10⁻⁶` and `β = 1 - 2·10⁻⁶` give `(1 - ε)/α < β`, hence
`r = O(n^{(1-ε)/α}) = o(n^β)`: for every `C_r`, eventually `2 C_r n^{(1-ε)/α} < n^β`. -/
theorem step_10_16_2 {p : ℕ} (hp : 10 ^ 6 ≤ p) (Cr : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 2 * Cr * (n : ℝ) ^ ((1 - ε) / α p) < (n : ℝ) ^ β := by
  have hgap := sub_pos.2 (exponent_gap hp).1
  have h := ((tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
    (2 * Cr)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h2
  have h3 : (n : ℝ) ^ β = (n : ℝ) ^ (β - (1 - ε) / α p) * (n : ℝ) ^ ((1 - ε) / α p) := by
    rw [← rpow_add hn0]; ring_nf
  rw [h3]
  exact mul_lt_mul_of_pos_right h1 (rpow_pos_of_pos hn0 _)

/-- D10.16.3. Containment: `S₀ ⊆ A ⊆ Λ`. If every endpoint of the cut `∂_Λ A` is at
`d_Λ`-distance more than `2r` from `S₀`, then `N_{2r}(S₀) ⊆ A`: a graph path of length `≤ 2r`
from `S₀` leaving `A` contains an edge of the cut. -/
theorem step_10_16_3 {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]
    {Λ A S₀ : Finset σ} (hA : A ⊆ Λ) (hS : S₀ ⊆ A) (r : ℕ) :
    (∀ s ∈ S₀, ∀ z ∈ GraphDomain.cutEndpoints G Λ A,
      ((2 * r : ℕ) : ℕ∞) < GraphDomain.domainEDist G Λ s z) →
    GraphDomain.graphNbhd G Λ S₀ (2 * r) ⊆ A := by
  intro hclear x hx
  obtain ⟨hxΛ, hx⟩ := mem_filter.1 hx
  by_contra hxA
  have hfar : ∀ y ∈ S₀, ((2 * r : ℕ) : ℕ∞) + 1 ≤ GraphDomain.domainEDist G Λ x y := by
    intro y hy
    refine Order.add_one_le_of_lt (lt_of_not_ge fun hle => ?_)
    have hyΛ := hA (hS hy)
    rw [GraphDomain.domainEDist_eq G ⟨x, hxΛ⟩ ⟨y, hyΛ⟩] at hle
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (hle.trans_lt (ENat.natCast_lt_top _)).ne
    obtain ⟨z, hz, p', hp'⟩ :=
      GraphDomain.exists_cutEndpoints_of_walk (D := A) G p.reverse (by simp [hS hy, hxA])
    refine (hclear y hy z hz).not_ge ?_
    rw [GraphDomain.domainEDist_eq G ⟨y, hyΛ⟩ z]
    refine p'.edist_le.trans ((Nat.cast_le.2 (hp'.trans_eq p.length_reverse)).trans ?_)
    exact hp ▸ hle
  exact absurd ((le_iInf₂ hfar).trans hx)
    (not_le.2 ((ENat.lt_add_one_iff (ENat.natCast_ne_top _)).2 le_rfl))

/-- D10.16.3 on `ℤ²`, for the frozen objects: if `dist_∞(T, Z_A) > L + 2r` then
`N_{2r}(A ∩ T_L) ⊆ A`.
2D only: the clearance is the sup-norm distance of ℤ² -/
theorem step_10_16_3_sq {Λ A T : Finset (ℤ × ℤ)} {L r : ℕ} (hA : A ⊆ Λ)
    (hclear : ENNReal.ofReal (L + 2 * r) < OpenAI.ambientEDist T (OpenAI.cutEndpoints Λ A)) :
    OpenAI.graphNbhd Λ (A ∩ OpenAI.ambientDilation T L) (2 * r) ⊆ A := by
  refine step_10_16_3 squareLattice hA inter_subset_left r fun s hs z hz => ?_
  obtain ⟨t, ht, e, he, rfl⟩ := mem_add.1 (mem_inter.1 hs).2
  rw [mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk] at he
  refine lt_of_not_ge fun hle => ?_
  have hsΛ := hA (mem_inter.1 hs).1
  have hzΛ : z ∈ Λ := by
    rcases mem_union.1 hz with h | h <;> obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.1 h
    · exact hA (squareLattice.mem_interedges_iff.1 hxy).1
    · exact (mem_sdiff.1 (squareLattice.mem_interedges_iff.1 hxy).2.1).1
  rw [GraphDomain.domainEDist_eq squareLattice ⟨_, hsΛ⟩ ⟨z, hzΛ⟩] at hle
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (hle.trans_lt (ENat.natCast_lt_top _)).ne
  have hl1 := (natAbs_add_natAbs_le_length p).trans (ENat.natCast_le_natCast.1 (hp ▸ hle))
  simp only [Prod.fst_add, Prod.snd_add] at hl1
  have h1 : OpenAI.ambientEDist T (OpenAI.cutEndpoints Λ A) ≤ edist t z :=
    (iInf₂_le t ht).trans (Metric.infEDist_le_edist_of_mem (mem_coe.2 (by exact hz)))
  have h2 : edist t z ≤ ENNReal.ofReal (L + 2 * r) := by
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Prod.dist_eq, Int.dist_eq, Int.dist_eq]
    have h3 : |t.1 - z.1| ≤ ((L + 2 * r : ℕ) : ℤ) := abs_le.2 ⟨by omega, by omega⟩
    have h4 : |t.2 - z.2| ≤ ((L + 2 * r : ℕ) : ℤ) := abs_le.2 ⟨by omega, by omega⟩
    exact max_le (by exact_mod_cast h3) (by exact_mod_cast h4)
  exact (hclear.trans_le (h1.trans h2)).false

end AreaLaw
