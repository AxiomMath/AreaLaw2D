import OpenAI.Scan.SourceScan

/-!
# The exponent count of the final collar parameters

The two scalar estimates of the proof of Proposition 9.6 [OAI265, §9.5] at the final
parameters of eq. (9.17), `ℓ = 10⁻⁵`, `κ = 10⁻⁶`, `μ = 1/4`, `ν = 10⁻³`, `W = n^ω`,
`ω = 1/20000`, entropy exponent `e_* = 2·10⁻⁶`: the scanner energy output (9.5) is at most
`n^{-1/2000}` (eq. (9.18)), and the six error terms of eq. (9.19), with `τ = n^{-1/4000}`,
sum to at most `n^{1-10⁻⁵}` (the table after eq. (9.20)).  Fixed constants and logarithmic
powers are absorbed at large `n`.
-/

namespace OpenAI.Scan

open Filter

/-- A fixed multiple of `n^p` is eventually at most `n^q` when `p < q`. -/
theorem eventually_mul_rpow_le_rpow {p q : ℝ} (hpq : p < q) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ p ≤ (n : ℝ) ^ q := by
  filter_upwards [eventually_le_natCast_rpow (sub_pos.2 hpq) A, eventually_gt_atTop 0]
    with n hA hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc A * (n : ℝ) ^ p ≤ (n : ℝ) ^ (q - p) * (n : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ q := by rw [← Real.rpow_add hn0, sub_add_cancel]

/-- Every real power of `log n` is eventually at most any positive power of `n`. -/
theorem eventually_log_rpow_le_rpow {η : ℝ} (hη : 0 < η) (r : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ r ≤ (n : ℝ) ^ η := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop r hη).natCast_atTop.eventuallyLE]
    with n hn
  exact (Real.le_norm_self _).trans (hn.trans_eq
    (Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)))

/-- At the final exponents the per-band weight `a = n^ω / K` eventually lies between
`n^{ω-1}` and `n^{-7499/10000}`. -/
theorem eventually_final_bandWeight_mem :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      (n : ℝ) ^ ((Exponents.scannerOmega : ℝ) - 1) ≤
        (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ) ∧
      (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ) ≤
        (n : ℝ) ^ (-(7499 / 10000 : ℝ)) := by
  set X := finalExponents
  have hℓ : X.ell = 1 / 100000 := by norm_num [X, finalExponents, Exponents.scannerEll]
  have hμ : X.mu = 1 / 4 := by norm_num [X, finalExponents, Exponents.scannerMu]
  have hω : (Exponents.scannerOmega : ℝ) = 1 / 20000 := by norm_num [Exponents.scannerOmega]
  obtain ⟨C, -, hK⟩ := X.exists_eventually_rpow_le_mul_K
  filter_upwards [hK, eventually_mul_rpow_le_rpow
    (p := (Exponents.scannerOmega : ℝ) - (1 - X.ell - X.mu)) (q := -(7499 / 10000 : ℝ))
    (by rw [hω, hℓ, hμ]; norm_num) C] with n ⟨hn2, hK1, hKn⟩ hsmall
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hK0 : (0 : ℝ) < X.K n := by exact_mod_cast (show 0 < X.K n by omega)
  have hKle : (X.K n : ℝ) ≤ n := by
    have hL : X.L n ≤ n := Nat.floor_le_of_le (by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1
        (by rw [hℓ]; norm_num : 1 - X.ell ≤ 1))
    exact_mod_cast (Nat.div_le_self _ _).trans hL
  refine ⟨by omega, ?_, ?_⟩
  · rw [Real.rpow_sub_one hn0.ne']
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _) hK0 hKle
  · rw [div_le_iff₀ hK0]
    calc (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
        = (n : ℝ) ^ ((Exponents.scannerOmega : ℝ) - (1 - X.ell - X.mu)) *
            (n : ℝ) ^ (1 - X.ell - X.mu) := by
          rw [← Real.rpow_add hn0, sub_add_cancel]
      _ ≤ (n : ℝ) ^ ((Exponents.scannerOmega : ℝ) - (1 - X.ell - X.mu)) *
            (C * (X.K n : ℝ)) := mul_le_mul_of_nonneg_left hKn (Real.rpow_nonneg hn0.le _)
      _ = C * (n : ℝ) ^ ((Exponents.scannerOmega : ℝ) - (1 - X.ell - X.mu)) *
            (X.K n : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (-(7499 / 10000 : ℝ)) * (X.K n : ℝ) :=
          mul_le_mul_of_nonneg_right hsmall hK0.le

/-- **The final energy estimate** [OAI265, eq. (9.18)]: for fixed constants, at all large `n`
the energy output `C n^ℓ D² W² (log n)^{C_l} (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000}` of
Proposition 9.2, with `δ_n = C_δ ε⁻¹ (n^{e_*-μ} + a^{1/4} (log n)^{C_l})`, `ε = n^{-ν}` and
`a = W / K`, is at most `n^{-1/2000}`.  The exponents are `ℓ + 2κ + 2ω - ν = -0.000888` and
`δ_n ≤ n^{-0.18}`. -/
theorem eventually_final_energy_le (C Cδ Cl : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) :
    ∀ᶠ n : ℕ in atTop,
      let X := finalExponents
      let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
      let a := W / (X.K n : ℝ)
      let ε := (n : ℝ) ^ (-X.nu)
      let δ := Cδ * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl)
      C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
          (δ ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ)) + C * (n : ℝ) ^ (-1000 : ℝ) ≤
        (n : ℝ) ^ (-(1 / 2000 : ℝ)) := by
  have hℓ : finalExponents.ell = 1 / 100000 := by
    norm_num [finalExponents, Exponents.scannerEll]
  have hκ : finalExponents.kappa = 1 / 1000000 := by
    norm_num [finalExponents, Exponents.scannerKappa]
  have hμ : finalExponents.mu = 1 / 4 := by norm_num [finalExponents, Exponents.scannerMu]
  have hν : finalExponents.nu = 1 / 1000 := by norm_num [finalExponents, Exponents.scannerNu]
  have he : finalExponents.e = 2 / 1000000 := by norm_num [finalExponents, Exponents.boxError]
  have hω : (Exponents.scannerOmega : ℝ) = 1 / 20000 := by norm_num [Exponents.scannerOmega]
  filter_upwards [eventually_final_bandWeight_mem,
    eventually_log_rpow_le_rpow (η := 1 / 200) (by norm_num) Cl,
    eventually_log_rpow_le_rpow (η := 1 / 10000) (by norm_num) Cl,
    eventually_mul_rpow_le_rpow (p := -(179 / 1000)) (q := -(178 / 1000)) (by norm_num) (2 * Cδ),
    eventually_mul_rpow_le_rpow (p := -(788 / 1000000)) (q := -(7 / 10000)) (by norm_num)
      (12 * C),
    eventually_mul_rpow_le_rpow (p := -1000) (q := -(7 / 10000)) (by norm_num) C,
    eventually_mul_rpow_le_rpow (p := -(7 / 10000)) (q := -(1 / 2000)) (by norm_num) 2]
    with n ⟨hn, haLow, haUp⟩ hlogδ hlogE hδsmall hmain htail hfin
  dsimp only
  rw [hω] at haLow haUp ⊢
  rw [hℓ, hμ, hν, he]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  set a := (n : ℝ) ^ (1 / 20000 : ℝ) / (finalExponents.K n : ℝ) with ha_def
  have ha0 : 0 ≤ a := (Real.rpow_nonneg hn0.le _).trans haLow
  have hD : (finalExponents.D n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 1000000 : ℝ) := by
    have hceil : (finalExponents.D n : ℝ) < (n : ℝ) ^ finalExponents.kappa + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le _)
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 1000000 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    rw [hκ] at hceil
    linarith
  have ha14 : a ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (-(7499 / 40000 : ℝ)) :=
    (Real.rpow_le_rpow ha0 haUp (by norm_num)).trans_eq (by
      rw [← Real.rpow_mul hn0.le]; norm_num)
  have hsum : (n : ℝ) ^ ((2 / 1000000 : ℝ) - 1 / 4) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl ≤
      2 * (n : ℝ) ^ (-(18 / 100 : ℝ)) := by
    have h1 : (n : ℝ) ^ ((2 / 1000000 : ℝ) - 1 / 4) ≤ (n : ℝ) ^ (-(18 / 100 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have h2 : a ^ (1 / 4 : ℝ) * Real.log n ^ Cl ≤ (n : ℝ) ^ (-(18 / 100 : ℝ)) :=
      calc a ^ (1 / 4 : ℝ) * Real.log n ^ Cl
          ≤ (n : ℝ) ^ (-(7499 / 40000 : ℝ)) * (n : ℝ) ^ (1 / 200 : ℝ) :=
            mul_le_mul ha14 hlogδ (Real.rpow_nonneg hlog0 _) (Real.rpow_nonneg hn0.le _)
        _ = (n : ℝ) ^ (-(7499 / 40000 : ℝ) + 1 / 200) := (Real.rpow_add hn0 _ _).symm
        _ ≤ (n : ℝ) ^ (-(18 / 100 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    linarith
  set δ := Cδ * ((n : ℝ) ^ (-(1 / 1000 : ℝ)))⁻¹ *
    ((n : ℝ) ^ ((2 / 1000000 : ℝ) - 1 / 4) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl) with hδ_def
  have hεinv : ((n : ℝ) ^ (-(1 / 1000 : ℝ)))⁻¹ = (n : ℝ) ^ (1 / 1000 : ℝ) := by
    rw [Real.rpow_neg hn0.le, inv_inv]
  have hδ0 : 0 ≤ δ := by
    rw [hδ_def, hεinv]
    exact mul_nonneg (mul_nonneg hCδ (Real.rpow_nonneg hn0.le _))
      (add_nonneg (Real.rpow_nonneg hn0.le _)
        (mul_nonneg (Real.rpow_nonneg ha0 _) (Real.rpow_nonneg hlog0 _)))
  have hδ : δ ≤ (n : ℝ) ^ (-(178 / 1000 : ℝ)) :=
    calc δ = Cδ * (n : ℝ) ^ (1 / 1000 : ℝ) *
          ((n : ℝ) ^ ((2 / 1000000 : ℝ) - 1 / 4) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl) := by
          rw [hδ_def, hεinv]
      _ ≤ Cδ * (n : ℝ) ^ (1 / 1000 : ℝ) * (2 * (n : ℝ) ^ (-(18 / 100 : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hCδ (Real.rpow_nonneg hn0.le _))
      _ = 2 * Cδ * ((n : ℝ) ^ (1 / 1000 : ℝ) * (n : ℝ) ^ (-(18 / 100 : ℝ))) := by ring
      _ = 2 * Cδ * (n : ℝ) ^ (-(179 / 1000 : ℝ)) := by
          rw [← Real.rpow_add hn0]; norm_num
      _ ≤ _ := hδsmall
  have hbracket : δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-(1 / 1000 : ℝ)) + (n : ℝ) ^ (-100 : ℝ) ≤
      3 * (n : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    have hroot : δ ^ (1 / 8 : ℝ) ≤ (n : ℝ) ^ (-(1 / 1000 : ℝ)) :=
      calc δ ^ (1 / 8 : ℝ) ≤ ((n : ℝ) ^ (-(178 / 1000 : ℝ))) ^ (1 / 8 : ℝ) :=
            Real.rpow_le_rpow hδ0 hδ (by norm_num)
        _ = (n : ℝ) ^ (-(178 / 1000 : ℝ) * (1 / 8)) := (Real.rpow_mul hn0.le _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have h100 : (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-(1 / 1000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    linarith
  have hW2 : ((n : ℝ) ^ (1 / 20000 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 20000 + 1 / 20000 : ℝ) := by
    rw [sq, ← Real.rpow_add hn0]
  have hprin : C * (n : ℝ) ^ (1 / 100000 : ℝ) * (finalExponents.D n : ℝ) ^ 2 *
      ((n : ℝ) ^ (1 / 20000 : ℝ)) ^ 2 * Real.log n ^ Cl *
      (δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-(1 / 1000 : ℝ)) + (n : ℝ) ^ (-100 : ℝ)) ≤
        (n : ℝ) ^ (-(7 / 10000 : ℝ)) :=
    calc _ ≤ C * (n : ℝ) ^ (1 / 100000 : ℝ) * (2 * (n : ℝ) ^ (1 / 1000000 : ℝ)) ^ 2 *
          ((n : ℝ) ^ (1 / 20000 : ℝ)) ^ 2 * (n : ℝ) ^ (1 / 10000 : ℝ) *
          (3 * (n : ℝ) ^ (-(1 / 1000 : ℝ))) := by
          have hDn : (0 : ℝ) ≤ finalExponents.D n := Nat.cast_nonneg _
          gcongr
      _ = 12 * C * (n : ℝ) ^ (1 / 100000 + 1 / 1000000 + 1 / 1000000 + 1 / 20000 +
          1 / 20000 + 1 / 10000 + -(1 / 1000) : ℝ) := by
          simp only [Real.rpow_add hn0]
          ring
      _ = 12 * C * (n : ℝ) ^ (-(788 / 1000000 : ℝ)) := by norm_num
      _ ≤ _ := hmain
  linarith


/-- **The final error table** [OAI265, proof of Proposition 9.6, eq. (9.19) and the table of
error exponents]: with `τ = n^{-1/4000}`, `W = n^{1/20000}`, `a = W / K` and a fixed constant
and logarithmic power, at all large `n` the error terms `(n^{1+e_*} + 1)/W`, `n^{3/5}`,
`(τ + n^{-1/2000}/τ) n^{1+e_*}`, `h(τ)/a`, `a n D (log n)^{C_l}` and `n^{-100}/a`, of powers
`0.999952`, `0.6`, `0.999752`, `0.74969`, `0.250061` and `-99.25`, sum to at most
`n^{1-10⁻⁵}` after multiplication by the constant. -/
theorem eventually_final_collar_errors_le (c Cl : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop,
      let X := finalExponents
      let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
      let a := W / (X.K n : ℝ)
      let τ := (n : ℝ) ^ (-(1 / 4000 : ℝ))
      let e := (Exponents.boxError : ℝ)
      c * (((n : ℝ) ^ (1 + e) + 1) / W + (n : ℝ) ^ (3 / 5 : ℝ) +
          (τ + (n : ℝ) ^ (-(1 / 2000 : ℝ)) / τ) * (n : ℝ) ^ (1 + e) +
          Real.binEntropy τ / a + a * n * (X.D n : ℝ) * Real.log n ^ Cl +
          (n : ℝ) ^ (-100 : ℝ) / a) ≤
        (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by
  have hω : (Exponents.scannerOmega : ℝ) = 1 / 20000 := by norm_num [Exponents.scannerOmega]
  have hbe : (Exponents.boxError : ℝ) = 2 / 1000000 := by norm_num [Exponents.boxError]
  have hκ : finalExponents.kappa = 1 / 1000000 := by
    norm_num [finalExponents, Exponents.scannerKappa]
  have hq : (99996 / 100000 : ℝ) < 1 - 1 / 100000 := by norm_num
  filter_upwards [eventually_final_bandWeight_mem,
    eventually_log_rpow_le_rpow (η := 1 / 100) (by norm_num) Cl,
    eventually_mul_rpow_le_rpow (p := 999952 / 1000000) (q := 99996 / 100000) (by norm_num) 2,
    eventually_mul_rpow_le_rpow (p := 999752 / 1000000) (q := 99996 / 100000) (by norm_num) 2,
    eventually_mul_rpow_le_rpow (p := 1 - 1 / 20000) (q := 99996 / 100000) (by norm_num)
      (Real.log 2),
    eventually_mul_rpow_le_rpow (p := 260101 / 1000000) (q := 99996 / 100000) (by norm_num) 2,
    eventually_mul_rpow_le_rpow hq (6 * c)]
    with n ⟨hn, haLow, haUp⟩ hlog hT1 hT3 hT4 hT5 hfin
  dsimp only
  rw [hω] at haLow haUp ⊢
  rw [hbe]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  set a := (n : ℝ) ^ (1 / 20000 : ℝ) / (finalExponents.K n : ℝ) with ha_def
  have hlow0 : 0 < (n : ℝ) ^ ((1 / 20000 : ℝ) - 1) := Real.rpow_pos_of_pos hn0 _
  have ha0 : 0 < a := hlow0.trans_le haLow
  have hD : (finalExponents.D n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 1000000 : ℝ) := by
    have hceil : (finalExponents.D n : ℝ) < (n : ℝ) ^ finalExponents.kappa + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le _)
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 1000000 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    rw [hκ] at hceil
    linarith
  have hinv : ∀ x : ℝ, 0 ≤ x → x / a ≤ x * (n : ℝ) ^ (1 - (1 / 20000 : ℝ)) := by
    intro x hx
    calc x / a ≤ x / (n : ℝ) ^ ((1 / 20000 : ℝ) - 1) :=
          div_le_div_of_nonneg_left hx hlow0 haLow
      _ = x * (n : ℝ) ^ (1 - (1 / 20000 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le, neg_sub]
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 + 2 / 1000000 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have h1 : ((n : ℝ) ^ (1 + 2 / 1000000 : ℝ) + 1) / (n : ℝ) ^ (1 / 20000 : ℝ) ≤
      (n : ℝ) ^ (99996 / 100000 : ℝ) :=
    calc _ ≤ (2 * (n : ℝ) ^ (1 + 2 / 1000000 : ℝ)) / (n : ℝ) ^ (1 / 20000 : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) (Real.rpow_nonneg hn0.le _)
      _ = 2 * (n : ℝ) ^ (1 + 2 / 1000000 - 1 / 20000 : ℝ) := by
          rw [Real.rpow_sub hn0, mul_div_assoc]
      _ = 2 * (n : ℝ) ^ (999952 / 1000000 : ℝ) := by norm_num
      _ ≤ _ := hT1
  have h2 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (99996 / 100000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h3 : ((n : ℝ) ^ (-(1 / 4000 : ℝ)) +
      (n : ℝ) ^ (-(1 / 2000 : ℝ)) / (n : ℝ) ^ (-(1 / 4000 : ℝ))) *
        (n : ℝ) ^ (1 + 2 / 1000000 : ℝ) ≤ (n : ℝ) ^ (99996 / 100000 : ℝ) :=
    calc _ = 2 * (n : ℝ) ^ (-(1 / 4000 : ℝ) + (1 + 2 / 1000000)) := by
          rw [← Real.rpow_sub hn0,
            show (-(1 / 2000 : ℝ) - -(1 / 4000)) = -(1 / 4000) by norm_num,
            Real.rpow_add hn0 (-(1 / 4000)) (1 + 2 / 1000000)]
          ring
      _ = 2 * (n : ℝ) ^ (999752 / 1000000 : ℝ) := by norm_num
      _ ≤ _ := hT3
  have h4 : Real.binEntropy ((n : ℝ) ^ (-(1 / 4000 : ℝ))) / a ≤
      (n : ℝ) ^ (99996 / 100000 : ℝ) :=
    calc _ ≤ Real.log 2 / a := div_le_div_of_nonneg_right Real.binEntropy_le_log_two ha0.le
      _ ≤ Real.log 2 * (n : ℝ) ^ (1 - (1 / 20000 : ℝ)) :=
          hinv _ (Real.log_nonneg (by norm_num))
      _ ≤ _ := hT4
  have h5 : a * n * (finalExponents.D n : ℝ) * Real.log n ^ Cl ≤
      (n : ℝ) ^ (99996 / 100000 : ℝ) :=
    calc _ ≤ (n : ℝ) ^ (-(7499 / 10000 : ℝ)) * (n : ℝ) ^ (1 : ℝ) *
          (2 * (n : ℝ) ^ (1 / 1000000 : ℝ)) * (n : ℝ) ^ (1 / 100 : ℝ) := by
          rw [Real.rpow_one]
          gcongr
      _ = 2 * (n : ℝ) ^ (-(7499 / 10000) + 1 + 1 / 1000000 + 1 / 100 : ℝ) := by
          simp only [Real.rpow_add hn0]
          ring
      _ = 2 * (n : ℝ) ^ (260101 / 1000000 : ℝ) := by norm_num
      _ ≤ _ := hT5
  have h6 : (n : ℝ) ^ (-100 : ℝ) / a ≤ (n : ℝ) ^ (99996 / 100000 : ℝ) :=
    calc _ ≤ (n : ℝ) ^ (-100 : ℝ) * (n : ℝ) ^ (1 - (1 / 20000 : ℝ)) :=
          hinv _ (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-100 + (1 - 1 / 20000) : ℝ) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  calc _ ≤ c * (6 * (n : ℝ) ^ (99996 / 100000 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        linarith
    _ = 6 * c * (n : ℝ) ^ (99996 / 100000 : ℝ) := by ring
    _ ≤ _ := hfin


end OpenAI.Scan
