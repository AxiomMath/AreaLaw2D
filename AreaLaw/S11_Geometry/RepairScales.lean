import AreaLaw.S11_Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # §11.5, §11.7 Repair scales

Digest `digest/11-geometry.md` D11.14, D11.15.6–7, D11.19

Some declarations here come from the v1 file `OpenAI/Geometry/RepairDepth.lean`, whose header
records it as ported or adapted from `LionSR/TNLean` (see `NOTICE`).
-/

open Real Finset

namespace AreaLaw.Geometry

/-- D11.14 (`geometry:trim-radius`). The trim halfside `d(S) = 2^⌊ρ₀ log₂ S⌋`. -/
noncomputable def d (S : ℝ) : ℝ := (2 : ℝ) ^ ⌊ρ₀ * logb 2 S⌋

lemma ρ₀_pos : 0 < ρ₀ := by norm_num [ρ₀, β]

lemma d_pos (S : ℝ) : 0 < d S := by unfold d; positivity

/-- For `S ≥ 1`, `d(S)` is a power of two with natural exponent. -/
lemma d_eq_two_pow {S : ℝ} (hS : 1 ≤ S) : d S = 2 ^ ⌊ρ₀ * logb 2 S⌋.toNat := by
  have : 0 ≤ ⌊ρ₀ * logb 2 S⌋ :=
    Int.floor_nonneg.2 (mul_nonneg ρ₀_pos.le (logb_nonneg (by norm_num) hS))
  rw [d, ← zpow_natCast, Int.toNat_of_nonneg this]

lemma rpow_ρ₀_eq {S : ℝ} (hS : 0 < S) : S ^ ρ₀ = (2 : ℝ) ^ (ρ₀ * logb 2 S) := by
  conv_lhs => rw [← rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hS]
  rw [← rpow_mul (by norm_num), mul_comm]

/-- D11.14.1. For `S > 0`, `½S^{ρ₀} < d(S) ≤ S^{ρ₀}`. -/
lemma step_11_14_1 {S : ℝ} (hS : 0 < S) : 1 / 2 * S ^ ρ₀ < d S ∧ d S ≤ S ^ ρ₀ := by
  set x := ρ₀ * logb 2 S
  have h : (2 : ℝ) ^ x < (2 : ℝ) ^ ((⌊x⌋ : ℝ) + 1) :=
    rpow_lt_rpow_of_exponent_lt (by norm_num) (Int.lt_floor_add_one x)
  rw [rpow_add (by norm_num), rpow_one, rpow_intCast] at h
  rw [rpow_ρ₀_eq hS, d]
  refine ⟨by linarith, ?_⟩
  rw [← rpow_intCast]
  exact rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)

/-- D11.14 (`geometry:trim-margins`). For `S ≥ S_* := (1000/a₀)^{1/(1-ρ₀)}`,
`½S^{ρ₀} < d(S) ≤ S^{ρ₀}` and `d(S) ≤ (a₀/1000)S`. -/
theorem eq_trim_margins {a₀ S : ℝ} (ha₀ : 0 < a₀) (hS : (1000 / a₀) ^ (1 - ρ₀)⁻¹ ≤ S) :
    1 / 2 * S ^ ρ₀ < d S ∧ d S ≤ S ^ ρ₀ ∧ d S ≤ a₀ / 1000 * S := by
  have hρ := eq_exponent_gaps.2.2.2.2.2
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  -- D11.14.1
  obtain ⟨h2, h1⟩ := step_11_14_1 hS0
  -- D11.14.2
  have h3 : 1000 / a₀ ≤ S ^ (1 - ρ₀) := by
    calc 1000 / a₀ = ((1000 / a₀) ^ (1 - ρ₀)⁻¹) ^ (1 - ρ₀) :=
          (rpow_inv_rpow (by positivity) (by linarith)).symm
      _ ≤ S ^ (1 - ρ₀) := rpow_le_rpow (by positivity) hS (by linarith)
  have h4 : S ^ ρ₀ ≤ a₀ / 1000 * S := by
    have hsplit : S ^ ρ₀ * S ^ (1 - ρ₀) = S := by
      rw [← rpow_add hS0, add_sub_cancel, rpow_one]
    have : S ^ ρ₀ * (1000 / a₀) ≤ S :=
      (mul_le_mul_of_nonneg_left h3 (by positivity)).trans_eq hsplit
    calc S ^ ρ₀ = a₀ / 1000 * (S ^ ρ₀ * (1000 / a₀)) := by field_simp
      _ ≤ a₀ / 1000 * S := by gcongr
  exact ⟨h2, h1, h1.trans h4⟩

/-- D11.14. Given `a₀ > 0`, there is a stopping scale `S_* ≥ max T 1` such that
both margins hold for all `S ≥ S_*`. -/
theorem exists_stopping_scale {a₀ : ℝ} (ha₀ : 0 < a₀) (T : ℝ) :
    ∃ S_star : ℝ, T ≤ S_star ∧ 1 ≤ S_star ∧ ∀ S, S_star ≤ S →
      1 / 2 * S ^ ρ₀ < d S ∧ d S ≤ S ^ ρ₀ ∧ d S ≤ a₀ / 1000 * S :=
  ⟨max T (max 1 ((1000 / a₀) ^ (1 - ρ₀)⁻¹)), le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _), fun _ hS =>
      eq_trim_margins ha₀ (((le_max_right _ _).trans (le_max_right _ _)).trans hS)⟩

/-- D11.15.6 (arithmetic part). If `d_{i+1} ≤ ε d_i` with `0 ≤ ε < ½`, then
`∑_{i≤m} d_i ≤ d_0/(1-ε) < 2d_0`. -/
theorem step_11_15_6 {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (d : ℕ → ℝ) (h0 : 0 < d 0)
    (hstep : ∀ i, d (i + 1) ≤ ε * d i) (m : ℕ) :
    ∑ i ∈ range (m + 1), d i ≤ d 0 / (1 - ε) ∧ d 0 / (1 - ε) < 2 * d 0 := by
  have hpow : ∀ i, d i ≤ ε ^ i * d 0 := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      calc d (i + 1) ≤ ε * d i := hstep i
        _ ≤ ε * (ε ^ i * d 0) := mul_le_mul_of_nonneg_left ih hε0
        _ = ε ^ (i + 1) * d 0 := by ring
  have hgeom : ∑ i ∈ range (m + 1), ε ^ i ≤ 1 / (1 - ε) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1) hε0 (by linarith)
    rwa [← range_eq_Ico, pow_zero] at this
  refine ⟨?_, (div_lt_iff₀ (by linarith)).2 (by nlinarith)⟩
  calc ∑ i ∈ range (m + 1), d i ≤ ∑ i ∈ range (m + 1), ε ^ i * d 0 :=
        sum_le_sum fun i _ => hpow i
    _ = (∑ i ∈ range (m + 1), ε ^ i) * d 0 := (sum_mul ..).symm
    _ ≤ 1 / (1 - ε) * d 0 := by gcongr
    _ = d 0 / (1 - ε) := by ring

lemma iterate_d_pos {S : ℝ} (hS : 0 < S) : ∀ j, 0 < d^[j] S
  | 0 => hS
  | j + 1 => by rw [Function.iterate_succ_apply']; exact d_pos _

/-- D11.15.7 / D11.19.1, first line: `log S_j ≤ ρ₀^j log S` along a branch. -/
lemma log_iterate_d_le {S : ℝ} (hS : 0 < S) (j : ℕ) : log (d^[j] S) ≤ ρ₀ ^ j * log S := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpos := iterate_d_pos hS j
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    calc log (d (d^[j] S)) ≤ log ((d^[j] S) ^ ρ₀) :=
          log_le_log (d_pos _) (step_11_14_1 hpos).2
      _ ≤ ρ₀ * (ρ₀ ^ j * log S) := by
          rw [log_rpow hpos]; exact mul_le_mul_of_nonneg_left ih ρ₀_pos.le

/-- A generation `j` with `S_* ≤ S_j` has `log S_* ≤ ρ₀^j log S`, and `log S > 0`. -/
lemma branch_log {S_star S : ℝ} (hS_star : 1 < S_star) (hS : 0 < S) {j : ℕ}
    (hj : S_star ≤ d^[j] S) : log S_star ≤ ρ₀ ^ j * log S ∧ 0 < log S := by
  have h1 := (log_le_log (by linarith) hj).trans (log_iterate_d_le hS j)
  refine ⟨h1, lt_of_not_ge fun h => ?_⟩
  linarith [log_pos hS_star, mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ρ₀_pos.le j) h]

/-- D11.15.7 / D11.19.1 (`geometry:descendant-count`, depth). Along a branch
`S_{j+1} = d(S_j)`, `log S_j ≤ ρ₀^j log S`; termination once `ρ₀^{j+1} log S < log S_*`,
so a generation `j` with `S_j ≥ S_*` has `j ≤ C + C log log(e^e + S)`. -/
theorem step_11_19_1 {S_star : ℝ} (hS_star : 1 < S_star) :
    (∀ S, 0 < S → ∀ j, log (d^[j] S) ≤ ρ₀ ^ j * log S) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ S, 0 < S → ∀ j : ℕ, S_star ≤ d^[j] S →
      (j : ℝ) ≤ C + C * log (log (exp (exp 1) + S)) := by
  have hc : 0 < -log ρ₀ := neg_pos.2 (log_neg ρ₀_pos eq_exponent_gaps.2.2.2.2.2)
  set a := log (log S_star)
  refine ⟨fun S hS => log_iterate_d_le hS, (|a| + 1) / -log ρ₀, by positivity,
    fun S hS j hj => ?_⟩
  obtain ⟨h1, hlogS⟩ := branch_log hS_star hS hj
  -- D11.19.1: `log log S_* ≤ j log ρ₀ + log log S`
  have h2 : a ≤ j * log ρ₀ + log (log S) := by
    have := log_le_log (log_pos hS_star) h1
    rwa [log_mul (pow_ne_zero _ ρ₀_pos.ne') hlogS.ne', log_pow] at this
  set L := log (log (exp (exp 1) + S))
  have hL : log (log S) ≤ L :=
    log_le_log hlogS (log_le_log hS (by linarith [exp_pos (exp 1)]))
  have hL0 : 0 ≤ L := log_nonneg ((le_log_iff_exp_le (by positivity)).2
    (by linarith [exp_le_exp.2 (one_le_exp zero_le_one)]))
  have key : (j : ℝ) * -log ρ₀ ≤ (|a| + 1) * (1 + L) := by
    nlinarith [neg_abs_le a, mul_nonneg (abs_nonneg a) hL0]
  calc (j : ℝ) ≤ (|a| + 1) * (1 + L) / -log ρ₀ := (le_div_iff₀ hc).2 key
    _ = _ := by ring

lemma log_exp_exp_add_le {S : ℝ} (hS : 1 ≤ S) :
    log (exp (exp 1) + S) ≤ 4 * log (S + 2) := by
  have hx : 1 ≤ log (S + 2) :=
    (le_log_iff_exp_le (by positivity)).2 (by linarith [exp_one_lt_three])
  calc log (exp (exp 1) + S) ≤ log (exp (exp 1) * (S + 2)) :=
        log_le_log (by positivity) (by nlinarith [one_le_exp (exp_pos 1).le])
    _ = exp 1 + log (S + 2) := by rw [log_mul (exp_pos _).ne' (by positivity), log_exp]
    _ ≤ 4 * log (S + 2) := by linarith [exp_one_lt_three]

/-- `9^{m+1} ≤ 9^{C₁+1} 4^p (log(S+2))^p`, `p = C₁ log 9`, when
`m ≤ C₁ + C₁ log log(e^e + S)`. -/
lemma nine_pow_le {C₁ S : ℝ} (hC₁ : 0 ≤ C₁) (hS : 1 ≤ S) {m : ℕ}
    (hm : (m : ℝ) ≤ C₁ + C₁ * log (log (exp (exp 1) + S))) :
    (9 : ℝ) ^ (m + 1) ≤ 9 ^ (C₁ + 1) * 4 ^ (C₁ * log 9) * log (S + 2) ^ (C₁ * log 9) := by
  set ℓ := log (exp (exp 1) + S)
  have hℓ : 0 < ℓ := log_pos (by linarith [one_le_exp (exp_pos 1).le])
  have hx : 0 ≤ log (S + 2) := log_nonneg (by linarith)
  have h9 : 0 ≤ log 9 := log_nonneg (by norm_num)
  calc (9 : ℝ) ^ (m + 1) = 9 ^ ((m : ℝ) + 1) := by rw [← rpow_natCast]; push_cast; rfl
    _ ≤ 9 ^ ((C₁ + 1) + C₁ * log ℓ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 9 ^ (C₁ + 1) * ℓ ^ (C₁ * log 9) := by
        rw [rpow_add (by norm_num), rpow_def_of_pos (by norm_num : (0 : ℝ) < 9) (C₁ * log ℓ),
          rpow_def_of_pos hℓ]
        ring_nf
    _ ≤ 9 ^ (C₁ + 1) * (4 * log (S + 2)) ^ (C₁ * log 9) := by
        gcongr; exact log_exp_exp_add_le hS
    _ = _ := by rw [mul_rpow (by norm_num) hx]; ring

/-- D11.19.2 (`geometry:descendant-count`). The marks descended from an initial mark of
scale `S` up to a generation `m` with `S_m ≥ S_*` number
`≤ ∑_{j≤m} 9^j ≤ 9^{depth+1} ≤ C (log(S+2))^C`.
2D only: at most nine children per mark (centre, corners and side midpoints of `Q_v`). -/
theorem step_11_19_2 {S_star : ℝ} (hS_star : 1 < S_star) :
    ∃ C : ℝ, 0 < C ∧ ∀ S, 0 < S → ∀ m : ℕ, S_star ≤ d^[m] S →
      ∑ j ∈ range (m + 1), (9 : ℝ) ^ j ≤ C * log (S + 2) ^ C := by
  obtain ⟨C₁, hC₁, hdepth⟩ := (step_11_19_1 hS_star).2
  set p := C₁ * log 9
  set K : ℝ := 9 ^ (C₁ + 1) * 4 ^ p
  have hK : 0 < K := by positivity
  refine ⟨max K p, lt_max_of_lt_left hK, fun S hS m hm => ?_⟩
  have hS1 : 1 ≤ S := by
    by_contra h
    linarith [(branch_log hS_star hS hm).2, log_nonpos hS.le (le_of_not_ge h)]
  have hx : 1 ≤ log (S + 2) :=
    (le_log_iff_exp_le (by positivity)).2 (by linarith [exp_one_lt_three])
  -- D11.19.2: `∑_{j≤m} 9^j ≤ 9^{m+1}`
  have hsum : ∑ j ∈ range (m + 1), (9 : ℝ) ^ j ≤ 9 ^ (m + 1) := by
    rw [geom_sum_eq (by norm_num), div_le_iff₀ (by norm_num)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) (m + 1)]
  calc ∑ j ∈ range (m + 1), (9 : ℝ) ^ j ≤ K * log (S + 2) ^ p :=
        hsum.trans (nine_pow_le hC₁.le hS1 (hdepth S hS m hm))
    _ ≤ max K p * log (S + 2) ^ max K p :=
        mul_le_mul (le_max_left _ _) (rpow_le_rpow_of_exponent_le hx (le_max_right _ _))
          (by positivity) (by positivity)

lemma summable_two_rpow_mul_rpow {δ : ℝ} (hδ : 0 < δ) (E : ℝ) :
    Summable fun k : ℕ => (2 : ℝ) ^ (-(k * δ)) * ((k : ℝ) + 1) ^ E := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (-δ) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := hr ▸ rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, E ≤ N := ⟨⌈E⌉₊, Nat.le_ceil E⟩
  have hg0 : Summable fun k : ℕ => (k : ℝ) ^ N * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one N (by rwa [norm_of_nonneg hr0.le])
  have hg : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ N * r ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr hg0
  refine (hg.mul_left r⁻¹).of_nonneg_of_le (fun k => by positivity) fun k => ?_
  have e1 : (2 : ℝ) ^ (-(k * δ)) = r ^ k := by
    rw [hr, show -(k * δ) = -δ * k by ring, rpow_mul (by norm_num), rpow_natCast]
  have e2 : r⁻¹ * (((k + 1 : ℕ) : ℝ) ^ N * r ^ (k + 1)) = r ^ k * ((k : ℝ) + 1) ^ N := by
    rw [pow_succ]; push_cast; field_simp
  rw [e1, e2]
  gcongr
  calc ((k : ℝ) + 1) ^ E ≤ ((k : ℝ) + 1) ^ (N : ℝ) :=
        rpow_le_rpow_of_exponent_le (by linarith [k.cast_nonneg (α := ℝ)]) hN
    _ = _ := rpow_natCast _ _

/-- D11.19.4 (`geometry:total-repairs`). `∑_{k≥k₀} 2^{-kδ₀/2}(k+1)^C` converges, so
`Cb ∑_{k≥k₀} 2^{-kδ₀/2}(k+1)^C ≤ C'b`. -/
theorem step_11_19_4 (C E : ℝ) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => (2 : ℝ) ^ (-(k * δ₀ / 2)) * ((k : ℝ) + 1) ^ E) ∧
    ∃ C' : ℝ, ∀ k₀ : ℕ, ∀ b : ℝ, 0 ≤ b →
      C * b * ∑' k : ℕ, (2 : ℝ) ^ (-(((k + k₀ : ℕ) : ℝ) * δ₀ / 2)) *
        (((k + k₀ : ℕ) : ℝ) + 1) ^ E ≤ C' * b := by
  set f := fun k : ℕ => (2 : ℝ) ^ (-(k * δ₀ / 2)) * ((k : ℝ) + 1) ^ E
  have hf : Summable f := (summable_two_rpow_mul_rpow (δ := δ₀ / 2) (by norm_num [δ₀]) E).congr
    fun k => by simp only [f, mul_div_assoc]
  refine ⟨hf, C * ∑' k, f k, fun k₀ b hb => ?_⟩
  change C * b * ∑' k, f (k + k₀) ≤ _
  -- D11.19.4: the tail is at most the whole series
  have h : ∑' k, f (k + k₀) ≤ ∑' k, f k := by
    rw [← hf.sum_add_tsum_nat_add k₀]
    exact le_add_of_nonneg_left (sum_nonneg fun _ _ => by positivity)
  calc C * b * ∑' k, f (k + k₀) ≤ C * b * ∑' k, f k := by gcongr
    _ = (C * ∑' k, f k) * b := by ring

end AreaLaw.Geometry
