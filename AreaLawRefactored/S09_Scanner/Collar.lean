import AreaLawRefactored.S09_Scanner.Planar

/-!
# §9.5 The collar mutual information: Proposition 9.6

Digest `digest/09-scanner.md` D9.25–D9.30. Proposition 9.6 (`prop_9_6_of`) from Proposition 9.2
(`Prop_9_2`, through `prop_9_2_planar`), Lemma 9.4 (`Lemma_9_4`) and Proposition 9.5
(`Prop_9_5`). The numerical steps D9.26 and D9.29 carry no geometry; D9.27 and D9.28 are stated
for an arbitrary physical site type, as the comparisons of §8 are.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Finset Asymptotics
open OpenAI (pureState HasGlobalGap ambientDilation ambientEDist)

namespace AreaLaw.Scanner

/-! ## D9.26 The parameters -/

namespace Collar

/-- D9.25. `ε = 10⁻⁵`. -/
noncomputable def ε : ℝ := 1 / 100000

/-- D9.26. `μ = 1/4`. -/
noncomputable def μ : ℝ := 1 / 4

/-- D9.26. `ν = 1/1000`. -/
noncomputable def ν : ℝ := 1 / 1000

/-- D9.26. `ℓ = 1/100000`, the `ε` of D9.25. -/
noncomputable def ℓ : ℝ := ε

/-- D9.26. `ω = 1/20000`. -/
noncomputable def ω : ℝ := 1 / 20000

/-- D9.26. `κ = 1/1000000`. -/
noncomputable def κ : ℝ := 1 / 1000000

/-- D9.19. `e_* = 2·10⁻⁶`. -/
noncomputable def eStar : ℝ := 2 / 1000000

/-- D9.26. The total weight `W = n^ω`. -/
noncomputable def W (n : ℕ) : ℝ := (n : ℝ) ^ ω

/-- D9.26.7. `τ = n^{-0.00025}`. -/
noncomputable def τ (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 4000 : ℝ))

/-- D9.26. The `k`-independent part of the energy bound of Proposition 9.2 at the parameters of
D9.26 (`e = e_*`, `W = n^ω`). -/
noncomputable def Edef₀ (C Cl : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) ^ ℓ * (D κ n : ℝ) ^ 2 * W n ^ 2 * Real.log n ^ Cl *
      ((C * (n : ℝ) ^ ν * ((n : ℝ) ^ (eStar - μ) +
          a ℓ μ (W n) n ^ (1 / 4 : ℝ) * Real.log n ^ Cl)) ^ (1 / 8 : ℝ) +
        (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) +
    C * (n : ℝ) ^ (-1000 : ℝ)

end Collar

/-- A constant times `n^p (log n)^c` is eventually below `n^{p'}` when `p < p'`. -/
theorem eventually_rpow_log_le (A c p p' : ℝ) (h : p < p') :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ p * Real.log n ^ c ≤ (n : ℝ) ^ p' := by
  have h₁ := (isLittleO_log_rpow_rpow_atTop c (sub_pos.2 h)).def
    (show (0 : ℝ) < 1 / (|A| + 1) by positivity)
  have h₂ : ∀ᶠ x : ℝ in atTop, A * x ^ p * Real.log x ^ c ≤ x ^ p' := by
    filter_upwards [h₁, eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx
    have hxp := Real.rpow_pos_of_pos hx0 p
    calc A * x ^ p * Real.log x ^ c ≤ |A| * x ^ p * |Real.log x ^ c| :=
          (le_abs_self _).trans_eq (by rw [abs_mul, abs_mul, abs_of_pos hxp])
      _ ≤ |A| * x ^ p * (1 / (|A| + 1) * x ^ (p' - p)) := by gcongr
      _ = |A| / (|A| + 1) * (x ^ p * x ^ (p' - p)) := by ring
      _ ≤ 1 * x ^ p' := by
          rw [← Real.rpow_add hx0, add_sub_cancel]
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = x ^ p' := one_mul _
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₂

/-- D9.26.4–5 at one `n`: the energy bound of Proposition 9.2 from the powers of its terms. -/
theorem edef_le_of_powers (C Cl x Lg A Dk ℓ κ ω ν e μ : ℝ) (hx1 : 1 ≤ x) (hlg : 1 ≤ Lg)
    (hA0 : 0 ≤ A) (hA : A ≤ x ^ (-(7 / 10 : ℝ))) (hD0 : 0 ≤ Dk) (hD : Dk ≤ 2 * x ^ κ)
    (h1 : 2 * |C| * x ^ (ν + (e - μ)) ≤ x ^ (-(17 / 100 : ℝ)))
    (h2 : 2 * |C| * x ^ (ν + -(7 / 10 : ℝ) / 4) * Lg ^ Cl ≤ x ^ (-(17 / 100 : ℝ)))
    (h3 : 16 * |C| * x ^ (ℓ + 2 * κ + 2 * ω + -(17 / 100 : ℝ) / 8) * Lg ^ Cl ≤
      x ^ (-(1 / 2000 : ℝ)))
    (h4 : 16 * |C| * x ^ (ℓ + 2 * κ + 2 * ω + -ν) * Lg ^ Cl ≤ x ^ (-(1 / 2000 : ℝ)))
    (h5 : 16 * |C| * x ^ (ℓ + 2 * κ + 2 * ω + -100) * Lg ^ Cl ≤ x ^ (-(1 / 2000 : ℝ)))
    (h6 : 4 * |C| * x ^ (-1000 : ℝ) ≤ x ^ (-(1 / 2000 : ℝ))) :
    C * x ^ ℓ * Dk ^ 2 * (x ^ ω) ^ 2 * Lg ^ Cl *
      ((C * x ^ ν * (x ^ (e - μ) + A ^ (1 / 4 : ℝ) * Lg ^ Cl)) ^ (1 / 8 : ℝ) + x ^ (-ν) +
        x ^ (-100 : ℝ)) + C * x ^ (-1000 : ℝ) ≤ x ^ (-(1 / 2000 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hLg0 : 0 < Lg := by linarith
  have hC := abs_nonneg C
  have hLC := Real.rpow_pos_of_pos hLg0 Cl
  -- D9.26.4: `δ_n ≤ n^{-0.17}`, `δ_n^{1/8} ≤ n^{-0.02125}`
  have hA4 : A ^ (1 / 4 : ℝ) ≤ x ^ (-(7 / 10 : ℝ) / 4) := by
    rw [div_eq_mul_one_div (-(7 / 10 : ℝ)), Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow hA0 hA (by norm_num)
  set inner := C * x ^ ν * (x ^ (e - μ) + A ^ (1 / 4 : ℝ) * Lg ^ Cl)
  have hin : |inner| ≤ x ^ (-(17 / 100 : ℝ)) := by
    have hbr : 0 ≤ x ^ (e - μ) + A ^ (1 / 4 : ℝ) * Lg ^ Cl :=
      add_nonneg (Real.rpow_nonneg hx0.le _) (mul_nonneg (Real.rpow_nonneg hA0 _) hLC.le)
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 ν), abs_of_nonneg hbr]
    have e1 : x ^ ν * x ^ (e - μ) = x ^ (ν + (e - μ)) := (Real.rpow_add hx0 _ _).symm
    have e2 : x ^ ν * x ^ (-(7 / 10 : ℝ) / 4) = x ^ (ν + -(7 / 10 : ℝ) / 4) :=
      (Real.rpow_add hx0 _ _).symm
    have : x ^ ν * (A ^ (1 / 4 : ℝ) * Lg ^ Cl) ≤ x ^ (ν + -(7 / 10 : ℝ) / 4) * Lg ^ Cl := by
      rw [← e2, mul_assoc]; gcongr
    calc |C| * x ^ ν * (x ^ (e - μ) + A ^ (1 / 4 : ℝ) * Lg ^ Cl)
        = |C| * (x ^ ν * x ^ (e - μ)) + |C| * (x ^ ν * (A ^ (1 / 4 : ℝ) * Lg ^ Cl)) := by ring
      _ ≤ |C| * x ^ (ν + (e - μ)) + |C| * (x ^ (ν + -(7 / 10 : ℝ) / 4) * Lg ^ Cl) := by
        rw [e1]; gcongr
      _ ≤ _ := by linarith
  have hroot : |inner| ^ (1 / 8 : ℝ) ≤ x ^ (-(17 / 100 : ℝ) / 8) := by
    rw [div_eq_mul_one_div (-(17 / 100 : ℝ)), Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (abs_nonneg _) hin (by norm_num)
  have hB1 : |inner ^ (1 / 8 : ℝ)| ≤ x ^ (-(17 / 100 : ℝ) / 8) :=
    (Real.abs_rpow_le_abs_rpow _ _).trans hroot
  -- D9.26.5: the prefactor `n^ℓ D² W²` has power `ℓ + 2κ + 2ω`
  set P := x ^ ℓ * Dk ^ 2 * (x ^ ω) ^ 2 * Lg ^ Cl
  have hP : P ≤ 4 * x ^ (ℓ + 2 * κ + 2 * ω) * Lg ^ Cl := by
    have e : x ^ (ℓ + 2 * κ + 2 * ω) = x ^ ℓ * (x ^ κ) ^ 2 * (x ^ ω) ^ 2 := by
      rw [Real.rpow_add hx0, Real.rpow_add hx0, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
      ring_nf
    rw [e]
    have : Dk ^ 2 ≤ (2 * x ^ κ) ^ 2 := pow_le_pow_left₀ hD0 hD 2
    have hpos2 := Real.rpow_pos_of_pos hx0 ℓ
    have hpos3 := pow_pos (Real.rpow_pos_of_pos hx0 ω) 2
    calc P ≤ x ^ ℓ * (2 * x ^ κ) ^ 2 * (x ^ ω) ^ 2 * Lg ^ Cl := by
          simp only [P]; gcongr
      _ = _ := by ring
  have hP0 : 0 ≤ P := by positivity
  set Bk := inner ^ (1 / 8 : ℝ) + x ^ (-ν) + x ^ (-100 : ℝ)
  have hBk : |Bk| ≤ x ^ (-(17 / 100 : ℝ) / 8) + x ^ (-ν) + x ^ (-100 : ℝ) := by
    have h0 := neg_abs_le (inner ^ (1 / 8 : ℝ))
    have h0' := le_abs_self (inner ^ (1 / 8 : ℝ))
    have := Real.rpow_pos_of_pos hx0 (-ν)
    have := Real.rpow_pos_of_pos hx0 (-100 : ℝ)
    have := Real.rpow_pos_of_pos hx0 (-(17 / 100 : ℝ) / 8)
    rw [abs_le]; constructor <;> linarith
  have hsplit : ∀ q : ℝ, 4 * x ^ (ℓ + 2 * κ + 2 * ω) * Lg ^ Cl * x ^ q =
      4 * x ^ (ℓ + 2 * κ + 2 * ω + q) * Lg ^ Cl := fun q => by
    rw [Real.rpow_add hx0 (ℓ + 2 * κ + 2 * ω) q]; ring
  have e1 : C * P * Bk ≤ |C| * P * |Bk| :=
    (le_abs_self _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hP0])
  have e2 : C * x ^ (-1000 : ℝ) ≤ |C| * x ^ (-1000 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
  calc _ = C * P * Bk + C * x ^ (-1000 : ℝ) := by simp only [P, Bk]; ring
    _ ≤ |C| * P * |Bk| + |C| * x ^ (-1000 : ℝ) := add_le_add e1 e2
    _ ≤ |C| * (4 * x ^ (ℓ + 2 * κ + 2 * ω) * Lg ^ Cl) *
          (x ^ (-(17 / 100 : ℝ) / 8) + x ^ (-ν) + x ^ (-100 : ℝ)) + |C| * x ^ (-1000 : ℝ) := by
        gcongr
    _ = |C| * (4 * x ^ (ℓ + 2 * κ + 2 * ω + -(17 / 100 : ℝ) / 8) * Lg ^ Cl) +
          |C| * (4 * x ^ (ℓ + 2 * κ + 2 * ω + -ν) * Lg ^ Cl) +
          |C| * (4 * x ^ (ℓ + 2 * κ + 2 * ω + -100) * Lg ^ Cl) + |C| * x ^ (-1000 : ℝ) := by
        rw [← hsplit, ← hsplit, ← hsplit]; ring
    _ ≤ x ^ (-(1 / 2000 : ℝ)) := by linarith

/-- D9.26 (parameters). `0 < ℓ < 1`, `0 < κ < μ < 1 - ℓ`, `ν > 0`, `0 < e_* < 1`, `κ ≤ e_*`. -/
theorem step_9_26_params :
    0 < Collar.ℓ ∧ Collar.ℓ < 1 ∧ 0 < Collar.κ ∧ Collar.κ < Collar.μ ∧
      Collar.μ < 1 - Collar.ℓ ∧ 0 < Collar.ν ∧ 0 < Collar.eStar ∧ Collar.eStar < 1 ∧
      Collar.κ ≤ Collar.eStar := by
  norm_num [Collar.ℓ, Collar.ε, Collar.κ, Collar.μ, Collar.ν, Collar.eStar]

/-- D9.26. With `μ = 1/4`, `ν = 1/1000`, `ℓ = 1/100000`, `ω = 1/20000`, `κ = 1/1000000`,
`W = n^ω`, for all large `n`: `L ≥ 1`, `K ≥ 1`, `a ≤ n^{-7/10}` (`a ≍ n^{-0.74994}`, D9.26.3),
`1/a ≤ n^{1-ε}`, `a r₀² ≤ c` (D9.26.6), `a √(C n D (log n)^{C_l}) ≤ c_sh` (D9.26.7),
`2L + 10 r₀ < 4 D₀ L` (D9.26.2), `0 < τ < 1/2`, and the energy bound of Proposition 9.2 is
`E_def ≤ n^{-0.0005} + o_k(1)` (D9.26.4–5). -/
theorem step_9_26 (C₁ c csh C Cl D₀ : ℝ) (hC₁ : 0 < C₁) (hc : 0 < c) (hcsh : 0 < csh)
    (hD₀ : 10 < D₀) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ L Collar.ℓ n ∧ 0 < K Collar.ℓ Collar.μ n ∧ 1 ≤ Collar.W n ∧
      0 < a Collar.ℓ Collar.μ (Collar.W n) n ∧
      a Collar.ℓ Collar.μ (Collar.W n) n ≤ (n : ℝ) ^ (-(7 / 10 : ℝ)) ∧
      (a Collar.ℓ Collar.μ (Collar.W n) n)⁻¹ ≤ (n : ℝ) ^ (1 - Collar.ε) ∧
      a Collar.ℓ Collar.μ (Collar.W n) n * (r₀ C₁ n : ℝ) ^ 2 ≤ c ∧
      a Collar.ℓ Collar.μ (Collar.W n) n * Real.sqrt (C * n * D Collar.κ n * Real.log n ^ Cl) ≤
        csh ∧
      (2 * L Collar.ℓ n + 10 * r₀ C₁ n : ℝ) < 4 * D₀ * L Collar.ℓ n ∧
      0 < Collar.τ n ∧ Collar.τ n < 1 / 2 ∧ Collar.Edef₀ C Cl n ≤ (n : ℝ) ^ (-(1 / 2000 : ℝ)) := by
  set p : ℝ := 1 - Collar.ℓ - Collar.μ with hpdef
  have hp : 0 < p := by norm_num [p, Collar.ℓ, Collar.ε, Collar.μ]
  -- D9.26.3: `K ≍ n^{1-ℓ-μ}`
  have evp : ∀ᶠ n : ℕ in atTop, (22 : ℝ) ≤ (n : ℝ) ^ p :=
    ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 22
  have eva := eventually_rpow_log_le 32 0 (Collar.ω - p) (-(7 / 10)) (by
    norm_num [p, Collar.ℓ, Collar.ε, Collar.μ, Collar.ω])
  -- D9.26.6, D9.26.7, D9.26.2
  have evr := eventually_rpow_log_le ((C₁ + 1) ^ 2 / c) 4 (-(7 / 10)) 0 (by norm_num)
  have evs := eventually_rpow_log_le (2 * |C| / csh ^ 2) Cl (-(7 / 5) + (1 + Collar.κ)) 0 (by
    norm_num [Collar.κ])
  have evc := eventually_rpow_log_le (C₁ + 2) 2 0 (1 - Collar.ℓ) (by
    norm_num [Collar.ℓ, Collar.ε])
  have evτ : ∀ᶠ n : ℕ in atTop, Collar.τ n < 1 / 2 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4000)).comp
      tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num))
  -- D9.26.4, D9.26.5
  have ev1 := eventually_rpow_log_le (2 * |C|) 0 (Collar.ν + (Collar.eStar - Collar.μ))
    (-(17 / 100)) (by norm_num [Collar.ν, Collar.eStar, Collar.μ])
  have ev2 := eventually_rpow_log_le (2 * |C|) Cl (Collar.ν + -(7 / 10) / 4) (-(17 / 100))
    (by norm_num [Collar.ν])
  have ev3 := eventually_rpow_log_le (16 * |C|) Cl
    (Collar.ℓ + 2 * Collar.κ + 2 * Collar.ω + -(17 / 100) / 8) (-(1 / 2000))
    (by norm_num [Collar.ℓ, Collar.ε, Collar.κ, Collar.ω])
  have ev4 := eventually_rpow_log_le (16 * |C|) Cl
    (Collar.ℓ + 2 * Collar.κ + 2 * Collar.ω + -Collar.ν) (-(1 / 2000))
    (by norm_num [Collar.ℓ, Collar.ε, Collar.κ, Collar.ω, Collar.ν])
  have ev5 := eventually_rpow_log_le (16 * |C|) Cl
    (Collar.ℓ + 2 * Collar.κ + 2 * Collar.ω + -100) (-(1 / 2000))
    (by norm_num [Collar.ℓ, Collar.ε, Collar.κ, Collar.ω])
  have ev6 := eventually_rpow_log_le (4 * |C|) 0 (-1000) (-(1 / 2000)) (by norm_num)
  filter_upwards [eventually_ge_atTop 3, evp, eva, evr, evs, evc, evτ, ev1, ev2, ev3, ev4, ev5,
    ev6] with n hn3 hnp ha32 hr hs hcl hτ h1 h2 h3 h4 h5 h6
  have hx3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hx0 : (0 : ℝ) < n := by linarith
  have hx1 : (1 : ℝ) ≤ n := by linarith
  have hlg : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hx0]; linarith [Real.exp_one_lt_d9]
  simp only [Real.rpow_zero, mul_one] at ha32 hcl h1 h6
  rw [Real.rpow_zero] at hr hs
  -- `L`, `m`, `K`
  have hL1 : 1 ≤ L Collar.ℓ n :=
    Nat.one_le_floor_iff _ |>.2 (Real.one_le_rpow hx1 (by norm_num [Collar.ℓ, Collar.ε]))
  have hLle : (L Collar.ℓ n : ℝ) ≤ (n : ℝ) ^ (1 - Collar.ℓ) := Nat.floor_le (by positivity)
  have hLgt : (n : ℝ) ^ (1 - Collar.ℓ) < L Collar.ℓ n + 1 := Nat.lt_floor_add_one _
  have hmle : (m Collar.μ n : ℝ) ≤ (n : ℝ) ^ Collar.μ := Nat.floor_le (by positivity)
  have hμ1 : 1 ≤ (n : ℝ) ^ Collar.μ := Real.one_le_rpow hx1 (by norm_num [Collar.μ])
  have hm1 : 1 ≤ m Collar.μ n := Nat.one_le_floor_iff _ |>.2 hμ1
  have hdivR : (L Collar.ℓ n : ℝ) <
      K Collar.ℓ Collar.μ n * (8 * m Collar.μ n) + 8 * m Collar.μ n := by
    exact_mod_cast Nat.lt_div_mul_add (a := L Collar.ℓ n) (show 0 < 8 * m Collar.μ n by omega)
  have hsplit : (n : ℝ) ^ (1 - Collar.ℓ) = (n : ℝ) ^ p * (n : ℝ) ^ Collar.μ := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hK0 : (0 : ℝ) ≤ K Collar.ℓ Collar.μ n := Nat.cast_nonneg _
  have hKp : (n : ℝ) ^ p < 8 * (K Collar.ℓ Collar.μ n + 1) + 1 := by
    have h1 : (n : ℝ) ^ p * (n : ℝ) ^ Collar.μ <
        (8 * (K Collar.ℓ Collar.μ n + 1) + 1) * (n : ℝ) ^ Collar.μ := by
      have : (K Collar.ℓ Collar.μ n + 1 : ℝ) * (8 * m Collar.μ n) ≤
          (K Collar.ℓ Collar.μ n + 1) * (8 * (n : ℝ) ^ Collar.μ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    exact lt_of_mul_lt_mul_right h1 (by positivity)
  have hK : (n : ℝ) ^ p / 32 ≤ K Collar.ℓ Collar.μ n := by linarith
  have hKpos : (0 : ℝ) < K Collar.ℓ Collar.μ n := lt_of_lt_of_le (by positivity) hK
  have hW1 : 1 ≤ Collar.W n := Real.one_le_rpow hx1 (by norm_num [Collar.ω])
  have ha0 : 0 < a Collar.ℓ Collar.μ (Collar.W n) n := div_pos (by linarith) hKpos
  have ha : a Collar.ℓ Collar.μ (Collar.W n) n ≤ (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
    refine le_trans ?_ ha32
    rw [a, Real.rpow_sub hx0, div_le_iff₀ hKpos]
    calc Collar.W n = 32 * ((n : ℝ) ^ Collar.ω / (n : ℝ) ^ p) * ((n : ℝ) ^ p / 32) := by
          rw [Collar.W]; field_simp
      _ ≤ _ := by gcongr
  have hD : (D Collar.κ n : ℝ) ≤ 2 * (n : ℝ) ^ Collar.κ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ Collar.κ by positivity)
    have := Real.one_le_rpow hx1 (show 0 ≤ Collar.κ by norm_num [Collar.κ])
    rw [D]; linarith
  refine ⟨by omega, hL1, by exact_mod_cast hKpos, hW1, ha0, ha, ?_, ?_, ?_, ?_,
    Real.rpow_pos_of_pos hx0 _, hτ, ?_⟩
  · -- `1/a = K/W ≤ L ≤ n^{1-ℓ}`
    rw [a, inv_div]
    calc (K Collar.ℓ Collar.μ n : ℝ) / Collar.W n ≤ K Collar.ℓ Collar.μ n := div_le_self hK0 hW1
      _ ≤ L Collar.ℓ n := by exact_mod_cast Nat.div_le_self _ _
      _ ≤ _ := hLle
  · -- D9.26.6
    have hr0 : (r₀ C₁ n : ℝ) ≤ (C₁ + 1) * Real.log n ^ 2 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ C₁ * Real.log n ^ 2 by positivity)
      have := one_le_pow₀ (n := 2) hlg
      rw [r₀]; linarith
    have h4 : Real.log n ^ (4 : ℝ) = Real.log n ^ 4 := by exact_mod_cast Real.rpow_natCast _ 4
    rw [h4, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hc] at hr
    calc a Collar.ℓ Collar.μ (Collar.W n) n * (r₀ C₁ n : ℝ) ^ 2
        ≤ (n : ℝ) ^ (-(7 / 10 : ℝ)) * ((C₁ + 1) * Real.log n ^ 2) ^ 2 := by gcongr
      _ = (C₁ + 1) ^ 2 * (n : ℝ) ^ (-(7 / 10 : ℝ)) * Real.log n ^ 4 := by ring
      _ ≤ c := hr
  · -- D9.26.7: `a √𝓑 → 0`
    set Y := C * n * D Collar.κ n * Real.log n ^ Cl
    have hLC := Real.rpow_nonneg (show 0 ≤ Real.log n by linarith) Cl
    have hY : Y ≤ 2 * |C| * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl := by
      have e : (n : ℝ) ^ (1 + Collar.κ) = n * (n : ℝ) ^ Collar.κ := by
        rw [Real.rpow_add hx0, Real.rpow_one]
      rw [e]
      calc Y ≤ |C| * n * D Collar.κ n * Real.log n ^ Cl := by
            simp only [Y]; gcongr; exact le_abs_self C
        _ ≤ |C| * n * (2 * (n : ℝ) ^ Collar.κ) * Real.log n ^ Cl := by gcongr
        _ = _ := by ring
    have ha2 : a Collar.ℓ Collar.μ (Collar.W n) n ^ 2 ≤ (n : ℝ) ^ (-(7 / 5 : ℝ)) := by
      calc a Collar.ℓ Collar.μ (Collar.W n) n ^ 2 ≤ ((n : ℝ) ^ (-(7 / 10 : ℝ))) ^ 2 := by gcongr
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have hY2 : a Collar.ℓ Collar.μ (Collar.W n) n ^ 2 * Y ≤ csh ^ 2 := by
      have hpos : 0 ≤ 2 * |C| * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one (by positivity)] at hs
      calc a Collar.ℓ Collar.μ (Collar.W n) n ^ 2 * Y
          ≤ a Collar.ℓ Collar.μ (Collar.W n) n ^ 2 *
              (2 * |C| * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl) := by gcongr
        _ ≤ (n : ℝ) ^ (-(7 / 5 : ℝ)) * (2 * |C| * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl) := by
            gcongr
        _ = 2 * |C| * (n : ℝ) ^ (-(7 / 5) + (1 + Collar.κ)) * Real.log n ^ Cl := by
            rw [Real.rpow_add hx0 (-(7 / 5)) (1 + Collar.κ)]; ring
        _ ≤ _ := hs
    rw [← Real.sqrt_sq ha0.le, ← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_sq hcsh.le]
    exact Real.sqrt_le_sqrt hY2
  · -- D9.26.2: `2L + 10 r₀ < 4 D₀ L`
    have hr0 : (r₀ C₁ n : ℝ) < C₁ * Real.log n ^ 2 + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ C₁ * Real.log n ^ 2 by positivity)
    have h2 : Real.log n ^ (2 : ℝ) = Real.log n ^ 2 := by exact_mod_cast Real.rpow_natCast _ 2
    rw [h2] at hcl
    have hl2 : 1 ≤ Real.log n ^ 2 := one_le_pow₀ hlg
    have hL1' : (1 : ℝ) ≤ L Collar.ℓ n := by exact_mod_cast hL1
    have hrL : (r₀ C₁ n : ℝ) < L Collar.ℓ n := by linarith
    have : 40 * (L Collar.ℓ n : ℝ) ≤ 4 * D₀ * L Collar.ℓ n :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · -- D9.26.4, D9.26.5
    unfold Collar.Edef₀
    rw [Collar.W]
    exact edef_le_of_powers C Cl n (Real.log n) _ _ Collar.ℓ Collar.κ Collar.ω Collar.ν
      Collar.eStar Collar.μ hx1 hlg ha0.le (by rw [← Collar.W]; exact ha) (Nat.cast_nonneg _) hD
      h1 h2 h3 h4 h5 h6

/-! ## D9.27, D9.28 The comparison difference and the purity identity -/

section Comparison

open Comparators

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}
  {K : ℕ} {St : Type*} [Fintype St] [DecidableEq St] (Γ : Statuses σ K St X)

theorem le_avg {T : Transport.MeanTree St} {f : St → Fin K → ℝ} {b : ℝ}
    (hK : 0 < K) (h : ∀ s g, b ≤ f s g) : b ≤ avg T f := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hsum : ∑ g : Fin K, ∑ s, T.weight s * b = K * b := by
    simp [← Finset.sum_mul, T.sum_weight]
  rw [avg, le_inv_mul_iff₀ hK', ← hsum]
  exact Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (h s g) (T.weight_nonneg s)

theorem avg_le {T : Transport.MeanTree St} {f : St → Fin K → ℝ} {b : ℝ}
    (hK : 0 < K) (h : ∀ s g, f s g ≤ b) : avg T f ≤ b := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hsum : ∑ g : Fin K, ∑ s, T.weight s * b = K * b := by
    simp [← Finset.sum_mul, T.sum_weight]
  rw [avg, inv_mul_le_iff₀ hK', ← hsum]
  exact Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (h s g) (T.weight_nonneg s)

theorem avg_sub (T : Transport.MeanTree St) (f h : St → Fin K → ℝ) :
    avg T f - avg T h = avg T fun s g => f s g - h s g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

private theorem sdiff_eq_of_disjoint {A B : Finset σ} (h : Disjoint A B)
    (hAB : A ∪ B = Finset.univ) : Finset.univ \ A = B := by
  rw [← hAB, Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint]
  exact h.symm

omit [Fintype St] [DecidableEq St] in
theorem S'_nonneg (E : TypicalSet D X) : 0 ≤ E.S' := by
  have hp : ∀ i ∈ E.E, 0 < D.p X i := fun i hi => (Real.exp_pos _).trans_le (E.lower i hi)
  have hz : 0 < E.z := Finset.sum_pos hp E.nonempty
  refine Finset.sum_nonneg fun i hi => Real.negMulLog_nonneg (div_nonneg (hp i hi).le hz.le) ?_
  rw [TypicalSet.p', div_le_one hz]
  exact Finset.single_le_sum (fun j hj => (hp j hj).le) hi

omit [Fintype St] [DecidableEq St] in
/-- D9.27.1. A region matched to a prefix `B` (`S(B) ≤ B_sh`, `1 + log dim 𝓗_{B △ Q} ≤ B_exc`)
has `S(Q) ≤ B_sh + B_exc`. -/
theorem S_le_of_matched {Bsh Bexc : ℝ} {Q B : Finset σ} (hB : D.S B ≤ Bsh)
    (h : (Q ⊆ B ∧ 1 + Real.log (dimReg n (B \ Q)) ≤ Bexc) ∨
      (B ⊆ Q ∧ 1 + Real.log (dimReg n (Q \ B)) ≤ Bexc)) : D.S Q ≤ Bsh + Bexc := by
  have hcard : ∀ P : Finset σ, Real.log (Fintype.card (Reg (fun v => Fin (n v)) P)) =
      Real.log (dimReg n P) := fun P => by
    congr 1; exact_mod_cast (dimReg_eq_card P).symm
  rcases h with ⟨hQB, hlog⟩ | ⟨hBQ, hlog⟩
  · have h1 := D.state.abs_regionEntropy_union_sub_le_log_card
      (disjoint_sdiff_self_left : Disjoint (B \ Q) Q) (subset_univ (B \ Q)) (subset_univ Q)
    rw [D.state.toSubState.regionEntropy_congr (sdiff_union_of_subset hQB) _ (subset_univ B),
      hcard] at h1
    have h2 : |D.S B - D.S Q| ≤ Real.log (dimReg n (B \ Q)) := h1
    linarith [(abs_le.1 h2).1]
  · have h1 := D.state.abs_regionEntropy_union_sub_le_log_card
      (disjoint_sdiff_self_left : Disjoint (Q \ B) B) (subset_univ (Q \ B)) (subset_univ B)
    rw [D.state.toSubState.regionEntropy_congr (sdiff_union_of_subset hBQ) _ (subset_univ Q),
      hcard] at h1
    have h2 : |D.S Q - D.S B| ≤ Real.log (dimReg n (Q \ B)) := h1
    linarith [(abs_le.1 h2).2]

omit [Fintype St] [DecidableEq St] in
/-- D9.27 (a), D9.27.1. `0 ≤ g^pre ≤ 2 S(X) + 2 (B_sh + B_exc)` for every status and band. -/
theorem gpre_le {𝓡 : Finset (Finset σ)} {Bsh Bexc : ℝ} (hP : PrefixData D Γ 𝓡 Bsh Bexc)
    (s : St) (g : Fin K) : 0 ≤ gpre D Γ s g ∧ gpre D Γ s g ≤ 2 * D.S X + 2 * (Bsh + Bexc) := by
  have hm : ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g} : Finset (Finset σ)), D.S Q ≤ Bsh + Bexc :=
    fun Q hQ => by
      obtain ⟨B, hB, h⟩ := hP.matched s g Q hQ
      exact S_le_of_matched (hP.entropy_le B hB) h
  have hU := hm (Γ.U s g) (by simp)
  have hUY := hm (Γ.U s g ∪ Γ.Y s g) (by simp)
  have hXU := Γ.disjoint_XU s g
  have hXY := Γ.disjoint_XY s g
  -- `S(XU) ≤ S(X) + S(U)`
  have h₁ := D.S_union_le hXU
  -- purity: `S(V) = S(XUY) ≤ S(X) + S(UY)`
  have h₂ : D.S (X ∪ (Γ.U s g ∪ Γ.Y s g)) = D.S (Γ.V s g) :=
    D.S_eq_of_compl (sdiff_eq_of_disjoint (by
      simp [Γ.disjoint_XV s g, Γ.disjoint_UV s g, Γ.disjoint_YV s g,
        Finset.disjoint_union_left]) (by rw [← Γ.cover s g]; ac_rfl))
  have h₃ := D.S_union_le (Finset.disjoint_union_right.2 ⟨hXU, hXY⟩)
  have h₄ : 0 ≤ D.S (Γ.Y s g) := SubState.regionEntropy_nonneg _ _
  refine ⟨gpre_nonneg Γ s g, ?_⟩
  rw [gpre]
  linarith

/-- D9.27 (b), D9.27.2–3. From the sharp comparisons of Proposition 8.1 (`C_sl ≥ 0`), with
`δ = w + |log z|` and `G = 2 S(X) + 2 (B_sh + B_exc) ≥ g_max`, for every `k ≥ 1` and tree:
`2 S(X) + ⟨g^pre - g^post⟩ ≤ 2δ + τ G + (2 (S(X) + δ) + |log z|)/(W/2) + C_su (a𝓑 + |log z|/a)
+ C_sl (τ (S(X) + δ) + h(τ)/a + a𝓑) + C_sl (E_def⁺/τ)(S(X) + δ + G) + o_k(1)`, `W = aK`. -/
theorem step_9_27 (hK : 0 < K) (E : TypicalSet D X) {𝓡 : Finset (Finset σ)} {Bsh Bexc : ℝ}
    (hP : PrefixData D Γ 𝓡 Bsh Bexc) {Csu Csl a τ 𝓑 : ℝ}
    {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} (hCsl : 0 ≤ Csl) (ha : 0 < a) (hτ : 0 < τ)
    (hU : SharpUpper D Γ E Csu a 𝓑 l) (hL : SharpLower D Γ E Csl a τ 𝓑 l) :
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k → ∀ T : Transport.MeanTree St,
      2 * D.S X + avg T (gpre D Γ) - avg T (gpost D Γ) ≤
        2 * (E.w + |Real.log E.z|) + τ * (2 * D.S X + 2 * (Bsh + Bexc)) +
          (2 * (D.S X + (E.w + |Real.log E.z|)) + |Real.log E.z|) / (a * K / 2) +
          Csu * (a * 𝓑 + |Real.log E.z| / a) +
          Csl * (τ * (D.S X + (E.w + |Real.log E.z|)) + Real.binEntropy τ / a + a * 𝓑) +
          Csl * (max (Edef D Γ E T a k (l k)) 0 / τ) *
            (D.S X + (E.w + |Real.log E.z|) + (2 * D.S X + 2 * (Bsh + Bexc))) + ρ k := by
  obtain ⟨r₁, hr₁, hU⟩ := hU
  obtain ⟨r₂, hr₂, hL⟩ := hL
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hW : 0 < a * K / 2 := by positivity
  refine ⟨fun k => (r₁ k + r₂ k) / (a * K / 2), by
    simpa using (hr₁.add hr₂).div_const (a * K / 2), fun k hk T => ?_⟩
  have hG : ∀ s g, gpre D Γ s g ≤ 2 * D.S X + 2 * (Bsh + Bexc) := fun s g => (gpre_le Γ hP s g).2
  have hpre0 : 0 ≤ avg T (gpre D Γ) := le_avg hK fun s g => gpre_nonneg Γ s g
  have hpreG : avg T (gpre D Γ) ≤ 2 * D.S X + 2 * (Bsh + Bexc) := avg_le hK hG
  have hu := hU k hk T
  have hl := hL k hk T (2 * D.S X + 2 * (Bsh + Bexc)) fun s g _ => hG s g
  obtain ⟨hd, hS'⟩ := step_8_3 E
  have hS'0 := S'_nonneg E
  -- D9.27.2: lower ≤ upper, divided by `2sW = W/2`
  set Yl := 2 * E.S' + (1 - τ) * avg T (gpre D Γ) -
    Csl * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑) -
    Csl * (Edef D Γ E T a k (l k) / τ) * (E.S' + (2 * D.S X + 2 * (Bsh + Bexc)))
  set Zu := avg T (gpost D Γ) + Csu * (a * 𝓑 + |Real.log E.z| / a)
  have hmul : 2 * (1 / 4) * (a * K) * (Yl - Zu) ≤
      2 * Real.log E.d - Real.log E.z + r₁ k + r₂ k := by
    have : 2 * (1 / 4) * (a * K) * (Yl - Zu) =
        2 * (1 / 4) * (a * K) * Yl - 2 * (1 / 4) * (a * K) * Zu := by ring
    linarith
  have hdiv : Yl - Zu ≤ (2 * Real.log E.d - Real.log E.z) / (a * K / 2) +
      (r₁ k + r₂ k) / (a * K / 2) := by
    rw [← add_div, le_div_iff₀ hW]
    linarith
  -- D9.27.3: `S' = S(X) + O(w + |log z|)`, `log d_* = S(X) + O(w + |log z|)`
  have hd' := (abs_le.1 hd).2
  have hS'1 := (abs_le.1 hS').1
  have hS'2 := (abs_le.1 hS').2
  have h1 : (2 * Real.log E.d - Real.log E.z) / (a * K / 2) ≤
      (2 * (D.S X + (E.w + |Real.log E.z|)) + |Real.log E.z|) / (a * K / 2) :=
    div_le_div_of_nonneg_right (by linarith [neg_abs_le (Real.log E.z)]) hW.le
  have h2 : Csl * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑) ≤
      Csl * (τ * (D.S X + (E.w + |Real.log E.z|)) + Real.binEntropy τ / a + a * 𝓑) :=
    mul_le_mul_of_nonneg_left (by
      linarith [mul_le_mul_of_nonneg_left (show Real.log E.d ≤ D.S X + (E.w + |Real.log E.z|) by
        linarith) hτ.le]) hCsl
  have h3 : Csl * (Edef D Γ E T a k (l k) / τ) * (E.S' + (2 * D.S X + 2 * (Bsh + Bexc))) ≤
      Csl * (max (Edef D Γ E T a k (l k)) 0 / τ) *
        (D.S X + (E.w + |Real.log E.z|) + (2 * D.S X + 2 * (Bsh + Bexc))) := by
    have hm : Edef D Γ E T a k (l k) / τ ≤ max (Edef D Γ E T a k (l k)) 0 / τ :=
      div_le_div_of_nonneg_right (le_max_left _ _) hτ.le
    have hm0 : 0 ≤ max (Edef D Γ E T a k (l k)) 0 / τ := div_nonneg (le_max_right _ _) hτ.le
    have hG0 : 0 ≤ E.S' + (2 * D.S X + 2 * (Bsh + Bexc)) := by linarith
    calc Csl * (Edef D Γ E T a k (l k) / τ) * (E.S' + (2 * D.S X + 2 * (Bsh + Bexc)))
        ≤ Csl * (max (Edef D Γ E T a k (l k)) 0 / τ) *
            (E.S' + (2 * D.S X + 2 * (Bsh + Bexc))) := by gcongr
      _ ≤ _ := by gcongr; linarith
  have h4 : (1 - τ) * avg T (gpre D Γ) = avg T (gpre D Γ) - τ * avg T (gpre D Γ) := by ring
  have h5 : τ * avg T (gpre D Γ) ≤ τ * (2 * D.S X + 2 * (Bsh + Bexc)) :=
    mul_le_mul_of_nonneg_left hpreG hτ.le
  simp only [Yl, Zu] at hdiv
  linarith

/-- D9.28. If `Λ \ S₀ ⊆ V` in every status then, for every tree,
`I(X : Λ \ S₀) ≤ 2 S(X) + ⟨g^pre - g^post⟩`: leafwise `2 S(X) + g^pre - g^post =
I(X : V) + I(X : YV) ≥ I(X : Λ \ S₀)` (D8.36, monotonicity of mutual information). -/
theorem step_9_28 (hK : 0 < K) {Fr : Finset σ} (hFr : ∀ s g, Fr ⊆ Γ.V s g)
    (T : Transport.MeanTree St) :
    D.I X Fr ≤ 2 * D.S X + avg T (gpre D Γ) - avg T (gpost D Γ) := by
  have h : ∀ s g, D.I X Fr - 2 * D.S X ≤ gpre D Γ s g - gpost D Γ s g := fun s g => by
    have hXV := Γ.disjoint_XV s g
    -- D9.28.2: monotonicity in the second argument
    have hmono : D.I X Fr ≤ D.I X (Fr ∪ (Γ.V s g \ Fr)) :=
      D.state.mutualInfo_le_mutualInfo_union (hXV.mono_right (hFr s g))
        (hXV.mono_right sdiff_subset) disjoint_sdiff (subset_univ _) (subset_univ _)
        (subset_univ _)
    rw [union_sdiff_of_subset (hFr s g)] at hmono
    have h0 : 0 ≤ D.I X (Γ.Y s g ∪ Γ.V s g) :=
      mutualInfo_nonneg D.state (disjoint_union_right.2 ⟨Γ.disjoint_XY s g, hXV⟩)
        (subset_univ _) (subset_univ _)
    -- D9.28.1: the identity D8.36
    have hid := step_8_36 (D := D) Γ s g
    linarith
  have := le_avg (T := T) hK h
  rw [← avg_sub] at this
  linarith

end Comparison

/-! ## D9.29 The error table -/

/-- D9.29. After `k → ∞` every row of D9.27 (b) is below `C n^{1-ε}`: with `S ≤ C_S n^{1+e_*}`,
`δ ≤ n^{3/5} + 1`, `|log z| ≤ 1`, `G ≤ C_G n^{1+e_*}`, `𝓑 ≤ C_B n^{1+κ}(log n)^{C_l}`,
`a ≤ n^{-7/10}`, `1/a ≤ n^{1-ε}`, `W = n^ω`, `h(τ) ≤ 1`, `0 ≤ E_def ≤ n^{-0.0005}`: the rows have
powers `0.6` (`w`), `0.999752` (`τ G`, `(E_def/τ) n^{1+e}`), `0.999952` (`(S + 1)/W`),
`0.300001` (`a𝓑`), `1 - ε` (`|log z|/a`, `h(τ)/a`). -/
theorem step_9_29 (CS CG CB Cl Csu Csl : ℝ) (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hCB : 0 ≤ CB)
    (hCsu : 0 ≤ Csu) (hCsl : 0 ≤ Csl) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ n : ℕ in atTop, ∀ S δ Lz G 𝓑 a' W' h Ed : ℝ,
      0 ≤ S → S ≤ CS * (n : ℝ) ^ (1 + Collar.eStar) → 0 ≤ δ → δ ≤ (n : ℝ) ^ (3 / 5 : ℝ) + 1 →
      |Lz| ≤ 1 → 0 ≤ G → G ≤ CG * (n : ℝ) ^ (1 + Collar.eStar) →
      𝓑 ≤ CB * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl →
      0 < a' → a' ≤ (n : ℝ) ^ (-(7 / 10 : ℝ)) → a'⁻¹ ≤ (n : ℝ) ^ (1 - Collar.ε) →
      W' = Collar.W n → h ≤ 1 → 0 ≤ Ed → Ed ≤ (n : ℝ) ^ (-(1 / 2000 : ℝ)) →
      2 * δ + Collar.τ n * G + (2 * (S + δ) + |Lz|) / (W' / 2) + Csu * (a' * 𝓑 + |Lz| / a') +
          Csl * (Collar.τ n * (S + δ) + h / a' + a' * 𝓑) +
          Csl * (Ed / Collar.τ n) * (S + δ + G) ≤
        C' * (n : ℝ) ^ (1 - Collar.ε) := by
  refine ⟨4 + CG + 2 * (2 * CS + 5) + 2 * Csu + Csl * (CS + 4) + Csl * (CS + 2 + CG),
    by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1, eventually_rpow_log_le CB Cl (-(7 / 10) + (1 + Collar.κ))
    (1 - Collar.ε) (by norm_num [Collar.κ, Collar.ε])] with n hn hB S δ Lz G 𝓑 a' W' h Ed hS0 hS
    hδ0 hδ hLz hG0 hG h𝓑 ha0 ha ha' hW hh hEd0 hEd
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hpow : ∀ q, q ≤ 1 - Collar.ε → (n : ℝ) ^ q ≤ (n : ℝ) ^ (1 - Collar.ε) := fun q hq =>
    Real.rpow_le_rpow_of_exponent_le hx1 hq
  have hP1 : 1 ≤ (n : ℝ) ^ (1 - Collar.ε) := Real.one_le_rpow hx1 (by norm_num [Collar.ε])
  have he1 : 1 ≤ (n : ℝ) ^ (1 + Collar.eStar) :=
    Real.one_le_rpow hx1 (by norm_num [Collar.eStar])
  have h35 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (1 + Collar.eStar) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num [Collar.eStar])
  -- row `w`: power `0.6`
  have h35' : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (1 - Collar.ε) := hpow _ (by norm_num [Collar.ε])
  have hτ0 : 0 < Collar.τ n := Real.rpow_pos_of_pos hx0 _
  -- rows `τ G`, `(E_def/τ) n^{1+e}`: power `1 + e_* - 0.00025 = 0.999752`
  have hτe : Collar.τ n * (n : ℝ) ^ (1 + Collar.eStar) ≤ (n : ℝ) ^ (1 - Collar.ε) := by
    rw [Collar.τ, ← Real.rpow_add hx0]; exact hpow _ (by norm_num [Collar.eStar, Collar.ε])
  have hW0 : 0 < W' := hW ▸ Real.rpow_pos_of_pos hx0 _
  -- row `(S(X) + 1)/W`: power `1 + e_* - ω = 0.999952`
  have hWe : (n : ℝ) ^ (1 + Collar.eStar) / W' ≤ (n : ℝ) ^ (1 - Collar.ε) := by
    rw [hW, Collar.W, ← Real.rpow_sub hx0]
    exact hpow _ (by norm_num [Collar.eStar, Collar.ε, Collar.ω])
  have hLg : 0 ≤ Real.log n ^ Cl := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hEτ : Ed / Collar.τ n ≤ Collar.τ n := by
    rw [div_le_iff₀ hτ0]
    calc Ed ≤ (n : ℝ) ^ (-(1 / 2000 : ℝ)) := hEd
      _ = Collar.τ n * Collar.τ n := by rw [Collar.τ, ← Real.rpow_add hx0]; norm_num
  -- row `a𝓑`: power `-7/10 + 1 + κ`
  have t4 : a' * 𝓑 ≤ (n : ℝ) ^ (1 - Collar.ε) := by
    calc a' * 𝓑 ≤ a' * (CB * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl) := by gcongr
      _ ≤ (n : ℝ) ^ (-(7 / 10 : ℝ)) * (CB * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl) := by
          gcongr
      _ = CB * (n : ℝ) ^ (-(7 / 10) + (1 + Collar.κ)) * Real.log n ^ Cl := by
          rw [Real.rpow_add hx0 (-(7 / 10)) (1 + Collar.κ)]; ring
      _ ≤ _ := hB
  -- rows `|log z|/a`, `h(τ)/a`: `1/a ≤ n^{1-ε}`
  have hinv : |Lz| / a' ≤ (n : ℝ) ^ (1 - Collar.ε) := by
    rw [div_eq_mul_inv]; nlinarith [inv_pos.2 ha0]
  have hh' : h / a' ≤ (n : ℝ) ^ (1 - Collar.ε) := by
    rw [div_eq_mul_inv]; nlinarith [inv_pos.2 ha0]
  clear hB hpow h𝓑 ha ha' hEd
  generalize (n : ℝ) ^ (1 - Collar.ε) = P at *
  generalize (n : ℝ) ^ (1 + Collar.eStar) = N at *
  generalize Collar.τ n = τ at *
  have hSδ : S + δ ≤ (CS + 2) * N := by nlinarith
  have t2 : τ * G ≤ CG * P := by
    calc τ * G ≤ τ * (CG * N) := by gcongr
      _ = CG * (τ * N) := by ring
      _ ≤ CG * P := by gcongr
  have t3 : (2 * (S + δ) + |Lz|) / (W' / 2) ≤ 2 * (2 * CS + 5) * P := by
    have : 2 * (S + δ) + |Lz| ≤ (2 * CS + 5) * N := by nlinarith
    calc (2 * (S + δ) + |Lz|) / (W' / 2) = 2 * ((2 * (S + δ) + |Lz|) / W') := by
          field_simp
      _ ≤ 2 * ((2 * CS + 5) * N / W') := by gcongr
      _ = 2 * (2 * CS + 5) * (N / W') := by ring
      _ ≤ _ := by gcongr
  have t6 : Ed / τ * (S + δ + G) ≤ (CS + 2 + CG) * P := by
    have : S + δ + G ≤ (CS + 2 + CG) * N := by nlinarith
    calc Ed / τ * (S + δ + G) ≤ τ * ((CS + 2 + CG) * N) := by gcongr
      _ = (CS + 2 + CG) * (τ * N) := by ring
      _ ≤ _ := by gcongr
  have t5 : τ * (S + δ) ≤ (CS + 2) * P := by
    calc τ * (S + δ) ≤ τ * ((CS + 2) * N) := by gcongr
      _ = (CS + 2) * (τ * N) := by ring
      _ ≤ _ := by gcongr
  have u1 : Csu * (a' * 𝓑 + |Lz| / a') ≤ Csu * (2 * P) :=
    mul_le_mul_of_nonneg_left (by linarith) hCsu
  have u2 : Csl * (τ * (S + δ) + h / a' + a' * 𝓑) ≤ Csl * ((CS + 4) * P) :=
    mul_le_mul_of_nonneg_left (by linarith) hCsl
  have u3 : Csl * (Ed / τ) * (S + δ + G) ≤ Csl * ((CS + 2 + CG) * P) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left t6 hCsl
  calc _ ≤ 2 * (2 * P) + CG * P + 2 * (2 * CS + 5) * P + Csu * (2 * P) +
        Csl * ((CS + 4) * P) + Csl * ((CS + 2 + CG) * P) := by linarith
    _ = _ := by ring

/-! ## D9.30 Sizes and transfer back -/

/-- D9.30.2. For a nonempty `T` with `|T| ≤ C n s₀` and `|T_j \ T_{j-1}| ≤ n` (`1 ≤ j ≤ s₀`), and
`L ≤ s₀ ≤ n`: `|S₀| = |A ∩ T_L| ≤ |T| + nL ≤ (C + 1) n²`. 2D only: consumes the planar template
bounds of Lemma 9.4 and the frozen ℤ² statement. -/
theorem step_9_30 {T : Finset (ℤ × ℤ)} (hT : T.Nonempty) {n s₀ L : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcard : (#T : ℝ) ≤ C * n * s₀)
    (hrow : ∀ j, 1 ≤ j → j ≤ s₀ → #(ambientDilation T j \ ambientDilation T (j - 1)) ≤ n)
    (hL : L ≤ s₀) (hs₀ : s₀ ≤ n) (A : Finset (ℤ × ℤ)) :
    (#(A ∩ ambientDilation T L) : ℝ) ≤ (C + 1) * (n : ℝ) ^ 2 := by
  have h0 : ambientDilation T 0 = T := by
    ext x; rw [mem_ambientDilation (hT := hT), Nat.le_zero, depth_eq_zero]
  have key : ∀ j, j ≤ s₀ → (#(ambientDilation T j) : ℝ) ≤ #T + j * n := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ j ih =>
      intro hj
      have h1 := card_le_card_sdiff_add_card (s := ambientDilation T (j + 1))
        (t := ambientDilation T j)
      have h2 := hrow (j + 1) (by omega) hj
      rw [Nat.add_sub_cancel] at h2
      have h3 := ih (by omega)
      have h1' : (#(ambientDilation T (j + 1)) : ℝ) ≤
          #(ambientDilation T (j + 1) \ ambientDilation T j) + #(ambientDilation T j) := by
        exact_mod_cast h1
      have h2' : (#(ambientDilation T (j + 1) \ ambientDilation T j) : ℝ) ≤ n := by
        exact_mod_cast h2
      push_cast
      linarith
  have hLn : (L : ℝ) ≤ s₀ := by exact_mod_cast hL
  have hsn : (s₀ : ℝ) ≤ n := by exact_mod_cast hs₀
  have hA : (#(A ∩ ambientDilation T L) : ℝ) ≤ #(ambientDilation T L) := by
    exact_mod_cast card_le_card inter_subset_right
  have := key L hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs0 : (0 : ℝ) ≤ s₀ := Nat.cast_nonneg s₀
  have e1 : C * n * s₀ ≤ C * n * n := mul_le_mul_of_nonneg_left hsn (mul_nonneg hC hn0)
  have e2 : (L : ℝ) * n ≤ n * n := mul_le_mul_of_nonneg_right (hLn.trans hsn) hn0
  have e3 : (n : ℝ) ^ 2 = n * n := sq _
  linarith

theorem mutualInfo_congr {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {U : Finset σ} (ρ : SubState (Reg loc U) ℂ)
    {X X' Y Y' : Finset σ} (hX : X = X') (hY : Y = Y') (h₁ : X ⊆ U) (h₂ : Y ⊆ U) (h₃ : X' ⊆ U)
    (h₄ : Y' ⊆ U) : ρ.mutualInfo h₁ h₂ = ρ.mutualInfo h₃ h₄ := by
  subst hX hY; rfl

/-- If `a ≤ b + ρ k` for every `k ≥ 1` and `ρ k → 0`, then `a ≤ b`. -/
theorem le_of_le_add_tendsto {a b : ℝ} {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (h : ∀ k : ℕ, 0 < k → a ≤ b + ρ k) : a ≤ b :=
  ge_of_tendsto (by simpa using tendsto_const_nhds.add hρ)
    (eventually_atTop.2 ⟨1, fun k hk => h k hk⟩)

/-! ## Proposition 9.6 -/

open Comparators in
/-- D9.25 **Proposition 9.6** (a sublinear collar bound), from Propositions 9.2, 9.5 and
Lemma 9.4. Let `T` be a template separated from the cut with parameters `(n, s₀)`,
`L = ⌊n^{1-10⁻⁵}⌋ ≤ s₀`, `X = A ∩ T`, `S₀ = A ∩ T_L`. For all sufficiently large `n`,
`I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}`, `ε = 10⁻⁵`; the cuts of `X`, `S₀`, `S₀ \ X` have `O(n)` edges and
`|S₀| = O(n²)`; constant and threshold independent of `T`, `s₀`, `n`, `Λ`, `A`. 2D only:
consumes the planar template bounds of Lemma 9.4 and the frozen ℤ² statement. -/
theorem prop_9_6_of (h92 : Prop_9_2.{0}) (h94 : Lemma_9_4) (h95 : Prop_9_5) {q R : ℕ}
    {J Δ : ℝ} (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) : OpenAI.CollarBound ℂ q R J Δ := by
  have : NeZero q := ⟨by omega⟩
  intro D₀ hD₀
  have hD₀' : 10 < D₀ := by have : (0 : ℝ) ≤ R := Nat.cast_nonneg R; linarith
  obtain ⟨Ctpl₀, h94⟩ := h94
  refine ⟨max Ctpl₀ 1, fun Ctpl hCtpl => ?_⟩
  obtain ⟨C₄, hC₄, hgeo, hent⟩ := h94 Ctpl (le_of_max_le_left hCtpl)
  -- D9.26.1: the entropy input with `e = e_*`, from Proposition 9.5 and Lemma 9.4
  obtain ⟨C₅, hF⟩ := h95 q R J Δ hq hJ hΔ
  obtain ⟨Ce, hCe, hent⟩ := hent q R J Δ Collar.eStar (max C₅ 1)
    (by norm_num [Collar.eStar]) (by norm_num [Collar.eStar]) (by positivity)
  have hent := hent D₀ hD₀ fun r hr => (hF r hr).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  -- D9.26: the parameters, Proposition 9.2 on `ℤ × ℤ`
  obtain ⟨hℓ, hℓ₁, hκ, hκμ, hμ, hν, he, he₁, hκe⟩ := step_9_26_params
  obtain ⟨C₁, c, Crl, csh, Csu, Csl, C₀, c₀, C, Cl, n₁, hC₁, hc, hcsh, hCsl, hCsu, H⟩ :=
    prop_9_2_planar h92 q R J Δ hΔ Collar.ℓ Collar.κ Collar.μ Collar.ν Collar.eStar Ce C₄ hℓ
      hℓ₁ hκ hκμ hμ hν he he₁ hκe hCe hC₄
  -- D9.29: the error table
  obtain ⟨C', hC', h29⟩ := step_9_29 (Ce + 1 + C₄) (2 * (Ce + 1 + C₄) + 8 * |C|) (2 * |C|) Cl
    Csu Csl (by positivity) (by positivity) (by positivity) hCsu.le hCsl.le
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 ((step_9_26 C₁ c csh C Cl D₀ hC₁ hc hcsh hD₀').and h29)
  refine ⟨C' + 1 + C₄, max n₁ n₂,
    fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hTpl hsep hLs hn => ?_⟩
  obtain ⟨⟨h2n, hL1, hK, hW1, ha0, ha, ha', har, hash, hclr, hτ0, hτ1, hBE⟩, h29⟩ :=
    hn₂ n (le_of_max_le_right hn)
  simp only [show OpenAI.collarWidth n = L Collar.ℓ n from rfl] at hLs ⊢
  set Lc := L Collar.ℓ n
  set a₀ := a Collar.ℓ Collar.μ (Collar.W n) n
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : (0 : ℝ) < n := by linarith
  have hN1 : 1 ≤ (n : ℝ) ^ (1 + Collar.eStar) :=
    Real.one_le_rpow hx1 (by norm_num [Collar.eStar])
  have hP1 : 1 ≤ (n : ℝ) ^ (1 - Collar.ε) := Real.one_le_rpow hx1 (by norm_num [Collar.ε])
  -- the template: `T ≠ ∅`, `s₀ ≤ n`
  obtain ⟨-, -, hTne, N₀, -, hN₀, -, -, hCN, -⟩ := id hTpl
  have hs₀n : s₀ ≤ n := by
    have h1 : (1 : ℝ) ≤ Ctpl := (le_max_right _ _).trans hCtpl
    have hN : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
    have hCN1 : 1 ≤ Ctpl * N₀ := one_le_mul_of_one_le_of_one_le h1 hN
    have : ((s₀ : ℝ) + 1) ≤ n := le_trans (le_mul_of_one_le_left (by positivity) hCN1) hCN
    exact_mod_cast (by linarith : (s₀ : ℝ) ≤ n)
  have hsn : (s₀ : ℝ) ≤ n := by exact_mod_cast hs₀n
  have hLn : (Lc : ℝ) ≤ n := by exact_mod_cast hLs.trans hs₀n
  obtain ⟨hTc, hrow, -⟩ := hgeo n s₀ T hTpl
  obtain ⟨hSX, hSQ, hcut⟩ := hent Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hTpl hsep
  -- D9.26.2: the test geometry
  have hTcard : (#T : ℝ) ≤ C₄ * (n : ℝ) ^ 2 := by
    calc (#T : ℝ) ≤ C₄ * n * s₀ := hTc
      _ ≤ C₄ * n * n := by gcongr
      _ = _ := by ring
  have hclear : ((2 * Lc + 10 * r₀ C₁ n : ℕ) : ENNReal) <
      ambientEDist T (OpenAI.cutEndpoints Λ A) := by
    refine lt_of_le_of_lt ?_ hsep
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (Lc : ℝ) ≤ s₀ := by exact_mod_cast hLs
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 4 * D₀ by linarith)
    push_cast
    linarith
  -- D9.26.1: `S_Ω(X) ≤ C' n s₀^{e_*} ≤ C' n^{1+e_*}`, `S_Ω(Q_j) ≤ C' n L^{e_*}`
  have hSX' : (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ) ≤
      Ce * (n : ℝ) ^ (1 + Collar.eStar) := by
    refine hSX.trans ?_
    rw [Real.rpow_add hx0, Real.rpow_one, ← mul_assoc]
    gcongr
  have hSQ' : ∀ j ≤ Lc, (pureState Ω hΩ).regionEntropy
      (inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
        Ce * ((n : ℝ) * (Lc : ℝ) ^ Collar.eStar + n) := fun j hj => by
    refine (hSQ Lc hL1 hLs j hj).1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) hCe.le
  -- Proposition 9.2
  obtain ⟨X, Fr, hXup, hFrup, Dt, E, St, _, _, Γ, l, 𝓡, Bsh, Bexc, 𝓑, hS, hI, hw, hz, hP,
      hBsh, hBexc, hM, h𝓑, hFr, -, -, hsharp, r, hr, hsel⟩ :=
    H n (le_of_max_le_left hn) (Collar.W n) hW1 har Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T hTne hTcard
      (fun j hj hjL => hrow j hj (hjL.trans hLs)) hclear hSX' hSQ'
  -- D9.26.7: the sharp condition `a ≤ c_sh / √𝓑`
  have h𝓑0 : 0 < 𝓑 := zero_lt_one.trans_le hM.one_le
  have hsc : a₀ ≤ csh / Real.sqrt 𝓑 := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 h𝓑0)]
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h𝓑) ha0.le).trans hash
  obtain ⟨hU, hL⟩ := hsharp hsc
  -- D9.27
  obtain ⟨ρ, hρ, h27⟩ := step_9_27 Γ hK E hP hCsl.le ha0 hτ0 hU (hL (Collar.τ n) hτ0 hτ1)
  -- the bounds of D9.29
  have hXcard : (#X : ℝ) ≤ C₄ * (n : ℝ) ^ 2 := by
    have : #X = #(A ∩ T) := by rw [← hXup, up, card_map]
    rw [this]
    exact le_trans (by exact_mod_cast card_le_card inter_subset_right) hTcard
  have hsmall : (n : ℝ) ^ (-200 : ℝ) * (1 + #X) ≤ 1 + C₄ := by
    have h1 : (n : ℝ) ^ (-200 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have h2 : (n : ℝ) ^ (-200 : ℝ) * (n : ℝ) ^ 2 ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have h0 : 0 ≤ (n : ℝ) ^ (-200 : ℝ) := Real.rpow_nonneg hx0.le _
    have h3 := mul_le_mul_of_nonneg_left hXcard h0
    have h4 : C₄ * ((n : ℝ) ^ (-200 : ℝ) * (n : ℝ) ^ 2) ≤ C₄ :=
      mul_le_of_le_one_right hC₄.le h2
    have h5 : (n : ℝ) ^ (-200 : ℝ) * (C₄ * (n : ℝ) ^ 2) =
        C₄ * ((n : ℝ) ^ (-200 : ℝ) * (n : ℝ) ^ 2) := by ring
    linarith
  have hS0 : 0 ≤ Dt.S X := SubState.regionEntropy_nonneg _ _
  have hSb : Dt.S X ≤ (Ce + 1 + C₄) * (n : ℝ) ^ (1 + Collar.eStar) := by
    have h := (abs_le.1 (hS X)).2
    rw [(pureState Ω hΩ).regionEntropy_congr hXup (up_subset X)
      (inter_subset_left.trans hA)] at h
    have := le_mul_of_one_le_right (show 0 ≤ 1 + C₄ by linarith) hN1
    linarith
  have hz1 : E.z ≤ 1 := TypicalSet.z_le_one step_8_11 E
  have hz2 : 1 / 2 ≤ E.z := by
    have : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
      calc (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by
            rw [inv_eq_one_div]
            exact div_le_div_of_nonneg_left zero_le_one (by norm_num)
              (by exact_mod_cast h2n)
    linarith
  have hLz : |Real.log E.z| ≤ 1 := by
    have h1 := Real.log_nonpos (by linarith) hz1
    have h2 : Real.log (1 / 2) ≤ Real.log E.z := Real.log_le_log (by norm_num) hz2
    rw [one_div, Real.log_inv] at h2
    rw [abs_le]
    constructor <;> linarith [Real.log_two_lt_d9]
  have hδ0 : 0 ≤ E.w + |Real.log E.z| := add_nonneg E.w_nonneg (abs_nonneg _)
  have hδb : E.w + |Real.log E.z| ≤ (n : ℝ) ^ (3 / 5 : ℝ) + 1 := by rw [hw]; linarith
  have hDk : (D Collar.κ n : ℝ) ≤ 2 * (n : ℝ) ^ Collar.κ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ Collar.κ by positivity)
    have := Real.one_le_rpow hx1 (show 0 ≤ Collar.κ by norm_num [Collar.κ])
    rw [D]; linarith
  have hnκ : (n : ℝ) * (n : ℝ) ^ Collar.κ = (n : ℝ) ^ (1 + Collar.κ) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  have hκN : (n : ℝ) ^ (1 + Collar.κ) ≤ (n : ℝ) ^ (1 + Collar.eStar) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num [Collar.κ, Collar.eStar])
  have hnN : (n : ℝ) ≤ (n : ℝ) ^ (1 + Collar.eStar) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1
      (show (1 : ℝ) ≤ 1 + Collar.eStar by norm_num [Collar.eStar])
  have hLe : (n : ℝ) * (Lc : ℝ) ^ Collar.eStar ≤ (n : ℝ) ^ (1 + Collar.eStar) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
    gcongr
  have hBshb : Bsh ≤ 2 * |C| * (n : ℝ) ^ (1 + Collar.eStar) := by
    have : C * ((n : ℝ) * (Lc : ℝ) ^ Collar.eStar + n) ≤
        |C| * ((n : ℝ) * (Lc : ℝ) ^ Collar.eStar + n) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have := mul_le_mul_of_nonneg_left (add_le_add hLe hnN) (abs_nonneg C)
    linarith
  have hBexcb : Bexc ≤ 2 * |C| * (n : ℝ) ^ (1 + Collar.eStar) := by
    have : C * n * D Collar.κ n ≤ |C| * n * D Collar.κ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hx0.le)
        (Nat.cast_nonneg _)
    have h2 : |C| * n * D Collar.κ n ≤ |C| * n * (2 * (n : ℝ) ^ Collar.κ) := by gcongr
    have h3 : |C| * n * (2 * (n : ℝ) ^ Collar.κ) = 2 * |C| * (n : ℝ) ^ (1 + Collar.κ) := by
      rw [← hnκ]; ring
    have h4 := mul_le_mul_of_nonneg_left hκN (show 0 ≤ 2 * |C| by positivity)
    linarith
  have h𝓑b : 𝓑 ≤ 2 * |C| * (n : ℝ) ^ (1 + Collar.κ) * Real.log n ^ Cl := by
    have hLC := Real.rpow_nonneg (Real.log_nonneg hx1) Cl
    calc 𝓑 ≤ C * n * D Collar.κ n * Real.log n ^ Cl := h𝓑
      _ ≤ |C| * n * D Collar.κ n * Real.log n ^ Cl := by gcongr; exact le_abs_self C
      _ ≤ |C| * n * (2 * (n : ℝ) ^ Collar.κ) * Real.log n ^ Cl := by gcongr
      _ = _ := by rw [← hnκ]; ring
  -- `St` is inhabited (a mean tree has weights summing to one), so `G ≥ g^pre ≥ 0`
  obtain ⟨T₁, -⟩ := hsel 1 one_pos
  have hSt : Nonempty St := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := T₁.sum_weight
    simp at this
  obtain ⟨s₁⟩ := hSt
  have hG0 : 0 ≤ 2 * Dt.S X + 2 * (Bsh + Bexc) :=
    (gpre_nonneg Γ s₁ ⟨0, hK⟩).trans (gpre_le Γ hP s₁ ⟨0, hK⟩).2
  have hGb : 2 * Dt.S X + 2 * (Bsh + Bexc) ≤
      (2 * (Ce + 1 + C₄) + 8 * |C|) * (n : ℝ) ^ (1 + Collar.eStar) := by linarith
  have hWK : a₀ * K Collar.ℓ Collar.μ n = Collar.W n := by
    simp only [a₀, a]
    exact div_mul_cancel₀ _ (by exact_mod_cast hK.ne')
  have hh : Real.binEntropy (Collar.τ n) ≤ 1 :=
    Real.binEntropy_le_log_two.trans (by linarith [Real.log_two_lt_d9])
  have hF := h29 (Dt.S X) (E.w + |Real.log E.z|) (Real.log E.z) (2 * Dt.S X + 2 * (Bsh + Bexc))
    𝓑 a₀ (a₀ * K Collar.ℓ Collar.μ n) (Real.binEntropy (Collar.τ n))
    (max (Collar.Edef₀ C Cl n) 0) hS0 hSb hδ0 hδb hLz hG0 hGb h𝓑b ha0 ha ha' hWK hh
    (le_max_right _ _) (max_le hBE (Real.rpow_nonneg hx0.le _))
  -- D9.29.1: `I_Ω̃(X : Λ \ S₀) ≤ ⟨2 S(X) + g^pre - g^post⟩ ≤ C n^{1-ε}`, after `k → ∞`
  have hSδG : 0 ≤ Dt.S X + (E.w + |Real.log E.z|) + (2 * Dt.S X + 2 * (Bsh + Bexc)) := by
    linarith
  have hIt : Dt.I X Fr ≤ C' * (n : ℝ) ^ (1 - Collar.ε) := by
    refine le_trans ?_ hF
    refine le_of_le_add_tendsto (ρ := fun k => ρ k + Csl * (|r k| / Collar.τ n) *
      (Dt.S X + (E.w + |Real.log E.z|) + (2 * Dt.S X + 2 * (Bsh + Bexc)))) ?_ fun k hk => ?_
    · simpa using hρ.add (((hr.abs.div_const (Collar.τ n)).const_mul Csl).mul_const
        (Dt.S X + (E.w + |Real.log E.z|) + (2 * Dt.S X + 2 * (Bsh + Bexc))))
    obtain ⟨T', hT'⟩ := hsel k hk
    have hT'' : Edef Dt Γ E T' a₀ k (l k) ≤ Collar.Edef₀ C Cl n + r k := hT'
    have h28 := step_9_28 (D := Dt) Γ hK hFr T'
    have h27k := h27 k hk T'
    -- D9.29.2: the defect energy, uniformly before the limit
    have hmax : max (Edef Dt Γ E T' a₀ k (l k)) 0 ≤ max (Collar.Edef₀ C Cl n) 0 + |r k| :=
      max_le (by linarith [le_max_left (Collar.Edef₀ C Cl n) 0, le_abs_self (r k)])
        (by positivity)
    have hm : max (Edef Dt Γ E T' a₀ k (l k)) 0 / Collar.τ n ≤
        max (Collar.Edef₀ C Cl n) 0 / Collar.τ n + |r k| / Collar.τ n := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hmax hτ0.le
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hCsl.le) hSδG
    have e : Csl * (max (Collar.Edef₀ C Cl n) 0 / Collar.τ n + |r k| / Collar.τ n) *
        (Dt.S X + (E.w + |Real.log E.z|) + (2 * Dt.S X + 2 * (Bsh + Bexc))) =
        Csl * (max (Collar.Edef₀ C Cl n) 0 / Collar.τ n) *
          (Dt.S X + (E.w + |Real.log E.z|) + (2 * Dt.S X + 2 * (Bsh + Bexc))) +
        Csl * (|r k| / Collar.τ n) *
          (Dt.S X + (E.w + |Real.log E.z|) + (2 * Dt.S X + 2 * (Bsh + Bexc))) := by ring
    linarith
  -- D9.30.1: transfer back to `Ω`
  have hdisj : Disjoint X Fr := by
    rw [← Finset.disjoint_map (Function.Embedding.subtype (· ∈ Λ))]
    change Disjoint (up X) (up Fr)
    rw [hXup, hFrup]
    refine Finset.disjoint_sdiff.mono_left (inter_subset_inter_left fun x hx => ?_)
    exact (mem_ambientDilation (hT := hTne)).2 ((depth_eq_zero.2 hx).symm ▸ Nat.zero_le _)
  have htr := (abs_le.1 (hI X Fr hdisj)).1
  rw [mutualInfo_congr (pureState Ω hΩ).toSubState hXup hFrup _ _ (inter_subset_left.trans hA)
    sdiff_subset] at htr
  obtain ⟨hc1, hc2, hc3⟩ := hcut Lc hLs
  have hCn : C₄ * (n : ℝ) ≤ (C' + 1 + C₄) * n := by
    have := mul_nonneg (show 0 ≤ C' + 1 by linarith) hx0.le
    linarith
  refine ⟨?_, hc1.trans hCn, hc3.trans hCn, ?_, ?_⟩
  · -- `I_Ω(X : Λ \ S₀) ≤ I_Ω̃ + n^{-200}(1 + |X|) ≤ C n^{1-ε}`
    have : (pureState Ω hΩ).mutualInfo (inter_subset_left.trans hA : A ∩ T ⊆ Λ)
        (sdiff_subset : Λ \ (A ∩ ambientDilation T Lc) ⊆ Λ) ≤
        C' * (n : ℝ) ^ (1 - Collar.ε) + (1 + C₄) := by linarith
    have := le_mul_of_one_le_right (show 0 ≤ 1 + C₄ by linarith) hP1
    change _ ≤ (C' + 1 + C₄) * (n : ℝ) ^ (1 - Collar.ε)
    linarith
  · have e : (A ∩ ambientDilation T Lc) \ (A ∩ T) = A ∩ (ambientDilation T Lc \ T) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [e]
    exact hc2.trans hCn
  · -- D9.30.2
    refine (step_9_30 hTne hC₄.le hTc hrow hLs hs₀n A).trans ?_
    have := mul_nonneg hC' (show (0 : ℝ) ≤ (n : ℝ) ^ 2 by positivity)
    linarith

end AreaLaw.Scanner
