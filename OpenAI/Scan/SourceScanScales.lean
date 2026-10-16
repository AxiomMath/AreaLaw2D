import OpenAI.Scan.SourceScan
import OpenAI.Scan.BadOldHistoryDecay
import OpenAI.Scan.Budgets
import OpenAI.Scan.SubsystemDimensionScale

/-!
# Scale facts of the collar scan for general exponents

For a fixed `ScannerExponents` tuple, the rounded scales of eq. (9.1) of [OAI265] satisfy, at
every large scale `n`, the separations `2 r₀ ≤ D`, `4 (D + 2 r₀) ≤ m` and `8 K m ≤ L` used by the
history and split-counting lemmas; the per-band weight `a = W / K` with `1 ≤ W ≤ n^ω`,
`ω < 1 - ℓ - μ`, makes `a ℓ_tr` arbitrarily small, where `ℓ_tr` is the logarithmic support
dimension; and the bad old histories of the collar scan have mass at most any fixed inverse
power of `n`, uniformly over the domain, the cut, the target and the round.

## Main statements

* `OpenAI.Scan.eventually_sourceScan_scales`: the scale separations.
* `OpenAI.Scan.eventually_div_bandCount_mul_transportLogDimBound_le`: smallness of `a ℓ_tr`.
* `OpenAI.Scan.eventually_sourceScan_badOldHistory_le`: the bad-old-history tail.
-/

namespace OpenAI.Scan

open Arealaw Filter SimpleGraph Asymptotics
open scoped BigOperators Topology

/-- The cut endpoints of the collar scan are those of the cut, when the cut lies in the
domain. -/
theorem sourceScan_cutEndpoints (X : ScannerExponents) (Ctr : ℝ) (R : ℕ)
    {Λ A T : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) (hT : T.Nonempty) (n : ℕ) :
    cutEndpoints Λ ((sourceScan X Ctr R Λ A T hT n).A.map (Function.Embedding.subtype _)) =
      cutEndpoints Λ A := by
  congr 1
  change (A.subtype (· ∈ (Λ : Set (ℤ × ℤ)))).map (Function.Embedding.subtype _) = A
  rw [Finset.subtype_map]
  exact Finset.filter_true_of_mem fun x hx => Finset.mem_coe.2 (hA hx)

/-- **Scale separations of the collar scan**: at every large scale, `2 ≤ n`, `r₀ ≤ D`,
`2 r₀ ≤ D`, `1 ≤ D`, `4 (D + 2 r₀) ≤ m` and `8 K m ≤ L`. -/
theorem eventually_sourceScan_scales (X : ScannerExponents) {Ctr : ℝ} (hCtr : 0 ≤ Ctr) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ roundedLogRadius Ctr n ≤ X.D n ∧
      2 * roundedLogRadius Ctr n ≤ X.D n ∧ 1 ≤ X.D n ∧
      4 * (X.D n + 2 * roundedLogRadius Ctr n) ≤ X.m n ∧ 8 * X.K n * X.m n ≤ X.L n := by
  filter_upwards [eventually_split_counting_scale_separation (ell := X.ell) hCtr X.kappa_pos
      X.kappa_lt_mu,
    eventually_const_mul_roundedLogRadius_le_rpow hCtr X.kappa_pos 2] with n h h2
  obtain ⟨hn, hr, hD, hmargin, hL⟩ := h
  refine ⟨hn, hr, ?_, hD, hmargin, hL⟩
  have hceil : (n : ℝ) ^ X.kappa ≤ (X.D n : ℝ) := Nat.le_ceil _
  exact_mod_cast h2.trans hceil

/-- The band count grows like `n^{1-ℓ-μ}`: eventually `n^{1-ℓ-μ} ≤ 32 K`. -/
theorem eventually_rpow_le_bandCount (X : ScannerExponents) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - X.ell - X.mu) ≤ 32 * X.K n := by
  obtain ⟨C₁, hC₁⟩ := eventually_scaleFacts X
  have hμ : 0 < X.mu := X.kappa_pos.trans X.kappa_lt_mu
  have hℓ : 0 < 1 - X.ell := sub_pos.2 X.ell_lt_one
  filter_upwards [hC₁, eventually_le_natCast_rpow hℓ 2] with n hF hL
  have hn0 : (0 : ℝ) < n := by have := hF.two_le_n; positivity
  have hm_le : (X.m n : ℝ) ≤ (n : ℝ) ^ X.mu := Nat.floor_le (by positivity)
  have hm_pos : (0 : ℝ) < X.m n := by exact_mod_cast hF.one_le_m
  have hL_ge : (n : ℝ) ^ (1 - X.ell) / 2 ≤ X.L n := half_le_floor hL
  have hK1 : (1 : ℝ) ≤ X.K n := by exact_mod_cast hF.one_le_K
  have hdivN : X.L n < (X.K n + 1) * (8 * X.m n) := by
    have h := Nat.lt_div_mul_add (a := X.L n) (b := 8 * X.m n) (by
      have : 0 < X.m n := by exact_mod_cast hm_pos
      omega)
    simpa only [ScannerExponents.K, add_mul, one_mul] using h
  have hdiv : (X.L n : ℝ) < (X.K n + 1) * (8 * X.m n) := by exact_mod_cast hdivN
  have hsplit : (n : ℝ) ^ (1 - X.ell) = (n : ℝ) ^ (1 - X.ell - X.mu) * (n : ℝ) ^ X.mu := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hp : 0 < (n : ℝ) ^ (1 - X.ell - X.mu) := by positivity
  have h1 : (n : ℝ) ^ (1 - X.ell - X.mu) * X.m n ≤ (n : ℝ) ^ (1 - X.ell) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_left hm_le hp.le
  nlinarith

/-- **Smallness of the per-band weight**: for `ω < 1 - ℓ - μ` and `c > 0`, at every large
scale every weight `0 ≤ W ≤ n^ω` has `(W / K) ℓ_tr ≤ c`, where `ℓ_tr` is the logarithmic
support dimension at radius `r₀`. -/
theorem eventually_div_bandCount_mul_transportLogDimBound_le (X : ScannerExponents)
    (q : ℕ) [NeZero q] {Ctr ω c : ℝ} (hCtr : 0 ≤ Ctr) (hω : ω < 1 - X.ell - X.mu)
    (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℝ, 0 ≤ W → W ≤ (n : ℝ) ^ ω →
      W / (X.K n : ℝ) * transportLogDimBound q (roundedLogRadius Ctr n) ≤ c := by
  set γ := 1 - X.ell - X.mu - ω with hγ
  have hγpos : 0 < γ := by rw [hγ]; linarith
  set Cq : ℝ := 1 + (2 * Ctr + 3) ^ 2 * Real.log q
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hCq : 0 < Cq := by positivity
  have hlo := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) hγpos).natCast_atTop).bound
    (show 0 < c / (32 * Cq) by positivity)
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlo, hlog, eventually_rpow_le_bandCount X, eventually_ge_atTop 1]
    with n hlo hlog hK hn1 W hW0 hW
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hKpos : (0 : ℝ) < X.K n := by
    have : (0 : ℝ) < (n : ℝ) ^ (1 - X.ell - X.mu) := by positivity
    linarith
  have hlogpos : 0 ≤ Real.log n := by linarith
  have hT := transportLogDimBound_roundedLogRadius_le (q := q) NeZero.one_le hCtr hlog
  have hlo' : Real.log n ^ 4 ≤ c / (32 * Cq) * (n : ℝ) ^ γ := by
    have h := hlo
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  have hsplit : (n : ℝ) ^ (1 - X.ell - X.mu) = (n : ℝ) ^ γ * (n : ℝ) ^ ω := by
    rw [← Real.rpow_add hn0, hγ]; ring_nf
  have hpγ : 0 < (n : ℝ) ^ γ := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
  calc W * transportLogDimBound q (roundedLogRadius Ctr n)
      ≤ (n : ℝ) ^ ω * (Cq * Real.log n ^ 4) :=
        mul_le_mul hW hT (by
          exact zero_le_one.trans (one_le_transportLogDimBound NeZero.one_le _))
          (by positivity)
    _ ≤ (n : ℝ) ^ ω * (Cq * (c / (32 * Cq) * (n : ℝ) ^ γ)) := by gcongr
    _ = c / 32 * ((n : ℝ) ^ γ * (n : ℝ) ^ ω) := by field_simp
    _ ≤ c / 32 * (32 * X.K n) := by rw [← hsplit]; gcongr
    _ = c * X.K n := by ring

open Classical in
/-- **Bad old histories of the collar scan** (Lemma 9.1 of [OAI265] with an arbitrary tail
power): at every large scale, uniformly over the domain, the cut, the target and the round
`s ≤ n m`, the bad old histories have total weight at most `n^{-P}`. -/
theorem eventually_sourceScan_badOldHistory_le (X : ScannerExponents) {Ctr CT : ℝ}
    (hCtr : 0 < Ctr) (hCT : 0 ≤ CT) (R : ℕ) (P : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)]
      (hT : T.Nonempty), A ⊆ Λ →
      (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
      (∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * X.L n + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) < ambientSupDistance t z) →
      let S := sourceScan X Ctr R Λ A T hT n
      ∀ s : ℕ, s ≤ S.n * S.m →
        (∑ h : History S.K S.m S.M s,
          if S.IsGoodOldHistory h then 0 else historyWeight h) ≤ (n : ℝ) ^ (-P) := by
  have hμ : 0 < X.mu := X.kappa_pos.trans X.kappa_lt_mu
  have hC1 : (0 : ℝ) < 3 * (anchorMultiplicityBound R : ℝ) := by
    unfold anchorMultiplicityBound; positivity
  filter_upwards [eventually_bad_history_probability_le.{0} X.ell_pos X.kappa_pos
      X.kappa_lt_mu X.mu_lt_one_sub_ell hCtr hC1 hCT (anchorMultiplicityBound R) P,
    eventually_sourceScan_scales X hCtr.le] with n htail hscales
  intro Λ A T _ hT hA hTcard hrows hclear S s hs
  obtain ⟨hn, -, -, hD, -, -⟩ := hscales
  have hMpos : 0 < S.M :=
    chargeSlotCount_pos (show (0 : ℝ) < S.C₁ from hC1) (by change 1 ≤ n; omega)
      hD
  refine (S.sum_historyWeight_bad_old_le_bad_through hMpos hs).trans ?_
  exact htail (supports Λ R) Λ T hT S rfl rfl rfl rfl rfl rfl hTcard rfl rfl
    (by rw [sourceScan_cutEndpoints X Ctr R hA hT n]; exact hclear) hrows
    (sourceScan_anchor_card_le X Ctr R Λ A T hT n)

end OpenAI.Scan
