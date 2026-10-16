import OpenAI.Geometry.SimultaneousRepair
import OpenAI.Geometry.DyadicScales
import OpenAI.Statements

/-!
# Scanner scales and thresholds for Proposition 11.2

The scanner scales of the three tile classes of Proposition 11.2 and the order in which the
thresholds are fixed [OAI265, §11, lines 690–743]: first the layer constant `C₀` and the scale
multipliers `C_P`, `C_B`, then the stopping scale `S_*`, then the lowest layer `k₀`.

* A primary of layer `k` has `s₀ = 2 ^ k` and `n = ⌈C_P (2 ^ k) ^ (1 + 2 δ₀)⌉`.
* A belt run of fine side `u` has `s₀ = u` and `n = ⌈C_B u⌉`; a replacement of removal
  half-side `u` has `s₀ = 2 u` and the same `n`.

## Main definitions

* `primaryScanScale`, `tileScanScale`.

## Main statements

* `tileScanScale_bounds`, `primaryScanScale_bounds`: the scanner-scale inequalities at a single
  scale, given the power comparisons that hold for all large scales.
* `exists_twoFamily_constants`: one choice of `C₀, C_P, C_B, S_*, k₀` meeting every
  inequality the assembly of Proposition 11.2 uses, for fixed `D₀`, `C_tpl` and `n_*`.

## Implementation notes

The constants are `C₀ = ⌈4 D₀ + 2⌉ + 2`, `C_B = 24 max C_tpl 0 + 2` and
`C_P = 18 max C_tpl 0 + 1`.  Every remaining inequality compares two powers of the scale with
distinct exponents, and holds for large scales by `eventually_mul_rpow_lt_rpow`; ceilings and
floors cost only the constant `C + 1`.
-/

noncomputable section

namespace OpenAI.Geometry

open Filter

/-- A power with the smaller exponent, times any constant, is eventually below a power with
the larger exponent. -/
theorem eventually_mul_rpow_lt_rpow {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a < x ^ b := by
  have hC : 0 < max C 1 := lt_max_of_lt_right one_pos
  have hlim : Tendsto (fun x : ℝ ↦ x ^ (-(b - a))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  filter_upwards [hlim.eventually (gt_mem_nhds (inv_pos.2 hC)), eventually_gt_atTop 0]
    with x hx hx0
  have hsplit : x ^ a = x ^ (-(b - a)) * x ^ b := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  have ha : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hx0 a).le
  calc C * x ^ a ≤ max C 1 * x ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) ha
    _ = max C 1 * x ^ (-(b - a)) * x ^ b := by rw [hsplit]; ring
    _ < max C 1 * (max C 1)⁻¹ * x ^ b := by gcongr
    _ = x ^ b := by rw [mul_inv_cancel₀ hC.ne', one_mul]

/-- A real power of a dyadic scale is a real power of two. -/
theorem two_pow_rpow (t : ℝ) (k : ℕ) : ((2 : ℝ) ^ k) ^ t = (2 : ℝ) ^ (t * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

/-- The fine side `2 ^ ⌊ζ k⌋` is at least half of `(2 ^ k) ^ ζ`. -/
theorem half_rpow_le_two_pow_fineScaleIndex (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (Exponents.zeta : ℝ) / 2 ≤ (2 : ℝ) ^ fineScaleIndex k := by
  have hf := Nat.lt_floor_add_one ((Exponents.zeta : ℝ) * (k : ℝ))
  change (Exponents.zeta : ℝ) * (k : ℝ) < (fineScaleIndex k : ℝ) + 1 at hf
  rw [two_pow_rpow, ← Real.rpow_natCast, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc (2 : ℝ) ^ ((Exponents.zeta : ℝ) * k) ≤ (2 : ℝ) ^ ((fineScaleIndex k : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hf.le
    _ = (2 : ℝ) ^ (fineScaleIndex k : ℝ) * 2 := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]

/-- The belt pitch `2 ^ ⌊(1 + δ₀) k⌋` is at most `(2 ^ k) ^ (1 + δ₀)`. -/
theorem two_pow_pitchScaleIndex_le (k : ℕ) :
    (2 : ℝ) ^ pitchScaleIndex k ≤ ((2 : ℝ) ^ k) ^ (1 + (Exponents.geometryDelta : ℝ)) := by
  rw [two_pow_rpow, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (by
    have : (0 : ℝ) ≤ Exponents.geometryDelta := by norm_num [Exponents.geometryDelta]
    positivity))

/-- The ratio `2 ^ (p - k)` of the belt pitch to the layer side is at most `(2 ^ k) ^ δ₀`. -/
theorem two_pow_pitchScaleIndex_sub_le (k : ℕ) :
    (2 : ℝ) ^ (pitchScaleIndex k - k) ≤ ((2 : ℝ) ^ k) ^ (Exponents.geometryDelta : ℝ) := by
  rw [two_pow_rpow, ← Real.rpow_natCast, Nat.cast_sub (le_pitchScaleIndex k)]
  have hp : (pitchScaleIndex k : ℝ) ≤ (1 + (Exponents.geometryDelta : ℝ)) * k :=
    Nat.floor_le (by
      have : (0 : ℝ) ≤ Exponents.geometryDelta := by norm_num [Exponents.geometryDelta]
      positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The scanner scale `⌈C_P (2 ^ k) ^ (1 + 2 δ₀)⌉` of a primary of layer `k`
(`geometry:primary-scale`). -/
def primaryScanScale (CP : ℝ) (k : ℕ) : ℕ :=
  ⌈CP * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊

/-- The scanner scale `⌈C_B u⌉` of a belt run of fine side `u` or of a replacement of removal
half-side `u`. -/
def tileScanScale (CB u : ℝ) : ℕ :=
  ⌈CB * u⌉₊

/-- The scanner scale `⌈C_B u⌉` with `C_B = 24 max C_tpl 0 + 2` meets the template, size,
collar and clearance bounds at every scale `u ≥ 1` past the two power comparisons. -/
theorem tileScanScale_bounds (Ctpl : ℝ) {u : ℝ} (hu : 1 ≤ u)
    (hcol : (24 * max Ctpl 0 + 2 + 1) ^ (1 - (1 / 100000 : ℝ)) * u ^ (1 - (1 / 100000 : ℝ)) <
      u ^ (1 : ℝ))
    (hclr : 8 * (2 : ℝ) ^ (Exponents.rho : ℝ) *
        (24 * max Ctpl 0 + 2 + 1) ^ (1 - (2 / 1000000 : ℝ)) * u ^ (1 - (2 / 1000000 : ℝ)) <
      u ^ (Exponents.rho : ℝ)) :
    (u ≤ tileScanScale (24 * max Ctpl 0 + 2) u) ∧
    max Ctpl 0 * 8 * (2 * u + 1) ≤ tileScanScale (24 * max Ctpl 0 + 2) u ∧
    2 * u ≤ tileScanScale (24 * max Ctpl 0 + 2) u ∧
    (collarWidth (tileScanScale (24 * max Ctpl 0 + 2) u) : ℝ) ≤ u ∧
    2 * (tileScanScale (24 * max Ctpl 0 + 2) u : ℝ) ^ (1 - (2 / 1000000 : ℝ)) <
      repairHalfSide (u / 2) / 2 := by
  set M := max Ctpl 0
  set CB := 24 * M + 2
  have hM : 0 ≤ M := le_max_right _ _
  have hu0 : 0 < u := by linarith
  have hCBu : 0 ≤ CB * u := by positivity
  set n := tileScanScale CB u
  have hn1 : CB * u ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < CB * u + 1 := Nat.ceil_lt_add_one hCBu
  have hn3 : (n : ℝ) ≤ (CB + 1) * u := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨by nlinarith, by nlinarith [mul_nonneg hM (by linarith : (0 : ℝ) ≤ u - 1)],
    by nlinarith, ?_, ?_⟩
  · have hle : (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) ≤
        (CB + 1) ^ (1 - (1 / 100000 : ℝ)) * u ^ (1 - (1 / 100000 : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) hu0.le]
      exact Real.rpow_le_rpow hn0 hn3 (by norm_num)
    rw [Real.rpow_one] at hcol
    exact (Nat.floor_le (Real.rpow_nonneg hn0 _)).trans (hle.trans hcol.le)
  · have hle : (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)) ≤
        (CB + 1) ^ (1 - (2 / 1000000 : ℝ)) * u ^ (1 - (2 / 1000000 : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) hu0.le]
      exact Real.rpow_le_rpow hn0 hn3 (by norm_num)
    have hd := half_rpow_le_repairHalfSide (S := u / 2) (by positivity)
    rw [Real.div_rpow hu0.le (by norm_num)] at hd
    have hP : 0 < (2 : ℝ) ^ (Exponents.rho : ℝ) := by positivity
    have key : 2 * ((CB + 1) ^ (1 - (2 / 1000000 : ℝ)) * u ^ (1 - (2 / 1000000 : ℝ))) <
        1 / 2 * (u ^ (Exponents.rho : ℝ) / (2 : ℝ) ^ (Exponents.rho : ℝ)) / 2 := by
      rw [div_eq_mul_inv _ ((2 : ℝ) ^ (Exponents.rho : ℝ))]
      have : u ^ (Exponents.rho : ℝ) * ((2 : ℝ) ^ (Exponents.rho : ℝ))⁻¹ *
          (2 : ℝ) ^ (Exponents.rho : ℝ) = u ^ (Exponents.rho : ℝ) := by
        field_simp
      nlinarith
    linarith

/-- The primary scanner scale `⌈C_P (2 ^ k) ^ (1 + 2 δ₀)⌉` with `C_P ≥ 18 max C_tpl 0` and `C_P ≥ 1`
meets the template, pitch, collar and clearance bounds once `2 ^ k` is past the power
comparisons. -/
theorem primaryScanScale_bounds (Ctpl CP : ℝ) (hCP : 18 * max Ctpl 0 ≤ CP) (hCP1 : 1 ≤ CP)
    (k : ℕ)
    (hcol : (CP + 1) ^ (1 - (1 / 100000 : ℝ)) * ((2 : ℝ) ^ k) ^
        ((1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (1 / 100000 : ℝ))) <
          ((2 : ℝ) ^ k) ^ (1 : ℝ))
    (hfine : 4 * (CP + 1) ^ (1 - (2 / 1000000 : ℝ)) * ((2 : ℝ) ^ k) ^
        ((1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (2 / 1000000 : ℝ))) <
          ((2 : ℝ) ^ k) ^ (Exponents.zeta : ℝ))
    (hlay : 4 * (CP + 1) ^ (1 - (2 / 1000000 : ℝ)) * ((2 : ℝ) ^ k) ^
        ((1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (2 / 1000000 : ℝ))) <
          ((2 : ℝ) ^ k) ^ (1 : ℝ)) :
    (2 : ℝ) ^ k ≤ primaryScanScale CP k ∧
    max Ctpl 0 * (2 ^ (pitchScaleIndex k - k) + 2) ^ 2 * ((2 : ℝ) ^ k + 1) ≤
      primaryScanScale CP k ∧
    (2 : ℝ) ^ pitchScaleIndex k ≤ primaryScanScale CP k ∧
    collarWidth (primaryScanScale CP k) ≤ 2 ^ k ∧
    2 * (primaryScanScale CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < (2 : ℝ) ^ fineScaleIndex k ∧
    2 * (primaryScanScale CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < (2 : ℝ) ^ k / 2 := by
  set δ := (Exponents.geometryDelta : ℝ)
  have hδ : δ = 2 / 10000000 := by simp [δ, Exponents.geometryDelta]
  set M := max Ctpl 0
  have hM : 0 ≤ M := le_max_right _ _
  set x := (2 : ℝ) ^ k
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by linarith
  set y := x ^ (1 + 2 * δ)
  have hxy : x ≤ y := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by rw [hδ]; norm_num : (1 : ℝ) ≤ 1 + 2 * δ)
  have hy0 : 0 ≤ y := by positivity
  set n := primaryScanScale CP k
  have hn1 : CP * y ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < CP * y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hn3 : (n : ℝ) ≤ (CP + 1) * y := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hpow : ∀ e : ℝ, 0 ≤ e → (n : ℝ) ^ e ≤ (CP + 1) ^ e * x ^ ((1 + 2 * δ) * e) := by
    intro e he
    rw [Real.rpow_mul hx0.le, ← Real.mul_rpow (by positivity) hy0]
    exact Real.rpow_le_rpow hn0 hn3 he
  have hβ := hpow (1 - (2 / 1000000 : ℝ)) (by norm_num)
  rw [Real.rpow_one] at hcol hlay
  refine ⟨by nlinarith, ?_, ?_, ?_, ?_, by linarith⟩
  · have h1 : (2 : ℝ) ^ (pitchScaleIndex k - k) ≤ x ^ δ := two_pow_pitchScaleIndex_sub_le k
    have h2 : 1 ≤ x ^ δ := Real.one_le_rpow hx (by rw [hδ]; norm_num)
    have h3 : x ^ δ * x ^ δ * x = y := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; congr 1; ring
    have h4 : ((2 : ℝ) ^ (pitchScaleIndex k - k) + 2) ^ 2 ≤ 9 * (x ^ δ * x ^ δ) := by
      have : 0 ≤ (2 : ℝ) ^ (pitchScaleIndex k - k) := by positivity
      nlinarith
    calc M * ((2 : ℝ) ^ (pitchScaleIndex k - k) + 2) ^ 2 * (x + 1)
        ≤ M * (9 * (x ^ δ * x ^ δ)) * (2 * x) := by gcongr; linarith
      _ = 18 * M * y := by rw [← h3]; ring
      _ ≤ CP * y := by gcongr
      _ ≤ n := hn1
  · calc (2 : ℝ) ^ pitchScaleIndex k ≤ x ^ (1 + δ) := two_pow_pitchScaleIndex_le k
      _ ≤ y := Real.rpow_le_rpow_of_exponent_le hx (by rw [hδ]; norm_num)
      _ ≤ CP * y := le_mul_of_one_le_left hy0 hCP1
      _ ≤ n := hn1
  · apply Nat.floor_le_of_le
    push_cast
    exact (hpow _ (by norm_num)).trans hcol.le
  · linarith [half_rpow_le_two_pow_fineScaleIndex k]

/-- **Threshold choice** [OAI265, §11, lines 724–743].  For fixed `D₀`, `C_tpl` and `n_*` there
are a layer constant `C₀ ≥ 2` beyond `4 D₀ + 2`, multipliers `C_P`, `C_B`, a stopping scale
`S_*` and a lowest layer `k₀ ≥ 5 · 10⁷` such that:

* `S_*` satisfies the trim margins for `a₀ = 1 / 64`, and every fine side from layer `k₀` on is
  at least `2 S_*`;
* every tile scale `u ≥ S_*` has scanner scale `n = ⌈C_B u⌉` at least `n_*`, the template bound
  `C_tpl · 8 · (2 u + 1) ≤ n`, `2 u ≤ n`, collar width at most `u`, and the fine clearance
  `2 n ^ β < d(u / 2) / 2`;
* every primary of layer `k ≥ k₀` has scanner scale `n` at least `n_*`, the template bounds
  `C_tpl (2 ^ (p - k) + 2) ^ 2 (2 ^ k + 1) ≤ n` and `2 ^ p ≤ n` for the pitch exponent `p`,
  collar width at most `2 ^ k`, and `2 n ^ β` below the fine side and below `(C₀ - 1) / 2 · 2 ^ k`.
-/
theorem exists_twoFamily_constants (D₀ Ctpl : ℝ) (nStar : ℕ) :
    ∃ (C₀ : ℕ) (CP CB Sstar : ℝ) (k₀ : ℕ),
      2 ≤ C₀ ∧ 4 * D₀ + 2 ≤ (C₀ : ℝ) ∧ 50000000 ≤ k₀ ∧ 2 ≤ Sstar ∧ 0 < CB ∧
      (∀ S, Sstar ≤ S → repairHalfSide S ≤ 1 / 64 / 1000 * S) ∧
      (∀ k, k₀ ≤ k → 2 * Sstar ≤ (2 : ℝ) ^ fineScaleIndex k) ∧
      (∀ u : ℝ, Sstar ≤ u →
        nStar ≤ tileScanScale CB u ∧
        max Ctpl 0 * 8 * (2 * u + 1) ≤ tileScanScale CB u ∧
        2 * u ≤ tileScanScale CB u ∧
        (collarWidth (tileScanScale CB u) : ℝ) ≤ u ∧
        2 * (tileScanScale CB u : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < repairHalfSide (u / 2) / 2) ∧
      (∀ k, k₀ ≤ k →
        nStar ≤ primaryScanScale CP k ∧
        max Ctpl 0 * (2 ^ (pitchScaleIndex k - k) + 2) ^ 2 * ((2 : ℝ) ^ k + 1) ≤
          primaryScanScale CP k ∧
        (2 : ℝ) ^ pitchScaleIndex k ≤ primaryScanScale CP k ∧
        collarWidth (primaryScanScale CP k) ≤ 2 ^ k ∧
        2 * (primaryScanScale CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) <
          (2 : ℝ) ^ fineScaleIndex k ∧
        2 * (primaryScanScale CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) <
          ((C₀ : ℝ) - 1) / 2 * (2 : ℝ) ^ k) := by
  set M := max Ctpl 0
  have hM : 0 ≤ M := le_max_right _ _
  have hδ : (Exponents.geometryDelta : ℝ) = 2 / 10000000 := by
    norm_num [Exponents.geometryDelta]
  have hζ : (Exponents.zeta : ℝ) = 1 - 1 / 10000000 := by
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  have hρ : (Exponents.rho : ℝ) = 1 - 1 / 1000000 := by
    norm_num [Exponents.rho, Exponents.beta, Exponents.boxError]
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.1
    ((eventually_repairHalfSide_le (a₀ := 1 / 64) (by norm_num)).and
      ((eventually_mul_rpow_lt_rpow (a := 1 - (1 / 100000 : ℝ)) (b := 1) (by norm_num)
        ((24 * M + 2 + 1) ^ (1 - (1 / 100000 : ℝ)))).and
      (eventually_mul_rpow_lt_rpow (a := 1 - (2 / 1000000 : ℝ)) (b := Exponents.rho)
        (by rw [hρ]; norm_num) (8 * (2 : ℝ) ^ (Exponents.rho : ℝ) *
          (24 * M + 2 + 1) ^ (1 - (2 / 1000000 : ℝ))))))
  set Sstar := max S₀ (max 2 (nStar : ℝ))
  have hS₀le : S₀ ≤ Sstar := le_max_left _ _
  have h2le : 2 ≤ Sstar := (le_max_left _ _).trans (le_max_right _ _)
  have hnle : (nStar : ℝ) ≤ Sstar := (le_max_right _ _).trans (le_max_right _ _)
  set CP := 18 * M + 1
  obtain ⟨X, hX⟩ := eventually_atTop.1
    ((eventually_mul_rpow_lt_rpow
        (a := (1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (1 / 100000 : ℝ))) (b := 1)
        (by rw [hδ]; norm_num) ((CP + 1) ^ (1 - (1 / 100000 : ℝ)))).and
      ((eventually_mul_rpow_lt_rpow
        (a := (1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (2 / 1000000 : ℝ)))
        (b := Exponents.zeta) (by rw [hδ, hζ]; norm_num)
        (4 * (CP + 1) ^ (1 - (2 / 1000000 : ℝ)))).and
      ((eventually_mul_rpow_lt_rpow
        (a := (1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (2 / 1000000 : ℝ))) (b := 1)
        (by rw [hδ]; norm_num) (4 * (CP + 1) ^ (1 - (2 / 1000000 : ℝ)))).and
      (((tendsto_rpow_atTop (by rw [hζ]; norm_num : (0 : ℝ) < Exponents.zeta)).eventually_ge_atTop
        (4 * Sstar)).and (eventually_ge_atTop (nStar : ℝ))))))
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)).eventually_ge_atTop X)
  refine ⟨⌈4 * D₀ + 2⌉₊ + 2, CP, 24 * M + 2, Sstar, max K 50000000, by omega, ?_,
    le_max_right _ _, h2le, by positivity, fun S hS ↦ (hS₀ S (hS₀le.trans hS)).1, ?_, ?_, ?_⟩
  · push_cast
    linarith [Nat.le_ceil (4 * D₀ + 2)]
  · intro k hk
    obtain ⟨-, -, -, h4, -⟩ := hX _ (hK k ((le_max_left _ _).trans hk))
    linarith [half_rpow_le_two_pow_fineScaleIndex k]
  · intro u hu
    obtain ⟨-, hcol, hclr⟩ := hS₀ u (hS₀le.trans hu)
    obtain ⟨h1, h2, h3, h4, h5⟩ := tileScanScale_bounds Ctpl (by linarith : 1 ≤ u) hcol hclr
    exact ⟨by exact_mod_cast hnle.trans (hu.trans h1), h2, h3, h4, h5⟩
  · intro k hk
    obtain ⟨hcol, hfine, hlay, -, hn⟩ := hX _ (hK k ((le_max_left _ _).trans hk))
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      primaryScanScale_bounds Ctpl CP (by linarith) (by linarith) k hcol hfine hlay
    have hC : (1 : ℝ) / 2 ≤ ((⌈4 * D₀ + 2⌉₊ + 2 : ℕ) - 1 : ℝ) / 2 := by
      push_cast; linarith [(Nat.cast_nonneg ⌈4 * D₀ + 2⌉₊ : (0 : ℝ) ≤ _)]
    have hx : (0 : ℝ) ≤ 2 ^ k := by positivity
    refine ⟨by exact_mod_cast hn.trans h1, h2, h3, h4, h5, ?_⟩
    nlinarith

/-- `repairHalfSide` is monotone on positive scales. -/
theorem repairHalfSide_le_repairHalfSide {S T : ℝ} (hS : 0 < S) (hST : S ≤ T) :
    repairHalfSide S ≤ repairHalfSide T := by
  have hρ : (0 : ℝ) ≤ Exponents.rho := rho_pos_lt_one.1.le
  exact zpow_le_zpow_right₀ (by norm_num) (Int.floor_le_floor (mul_le_mul_of_nonneg_left
    (Real.logb_le_logb_of_le (by norm_num) hS hST) hρ))

end OpenAI.Geometry
