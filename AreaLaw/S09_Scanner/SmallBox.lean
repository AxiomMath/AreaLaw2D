import AreaLaw.S09_Scanner.Collar
import AreaLaw.S09_Scanner.Templates

/-!
# §9.4 A small safe-box exponent: Proposition 9.5

Digest `digest/09-scanner.md` D9.19–D9.24. Proposition 9.5 (`prop_9_5_of`) from Proposition 9.2
(`Prop_9_2`, through `prop_9_2_planar`), the initial box estimate (`AreaLaw.prop_3_3`) and the
shell entropy of a safe rectangle (`step_9_21_2`). The numerical steps D9.20, D9.22 and the
iteration D9.24.5 carry no geometry; the comparison step D9.23 is stated for an arbitrary physical
site type, as the comparisons of §8 are.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Finset
open OpenAI (pureState HasGlobalGap ambientDilation ambientEDist IsIntRect IsSafe boxSize)

namespace AreaLaw.Scanner

/-! ## D9.20 The bootstrap parameters -/

namespace SmallBox

variable (e₀ : ℝ)

/-- D9.20. `g₀ = (1 - e₀)/2`. -/
noncomputable def g₀ : ℝ := (1 - e₀) / 2

/-- D9.20. `μ = 1 - g₀`. -/
noncomputable def μ : ℝ := 1 - g₀ e₀

/-- D9.20. `ν = g₀/1000`. -/
noncomputable def ν : ℝ := g₀ e₀ / 1000

/-- D9.20. `ℓ = ν/100 = g₀/10⁵`. -/
noncomputable def ℓ : ℝ := ν e₀ / 100

/-- D9.20. `κ = min(ν/100, e_*/4)`. -/
noncomputable def κ : ℝ := min (ν e₀ / 100) (Collar.eStar / 4)

/-- D9.20. The total weight `W = 4`. -/
noncomputable def W : ℝ := 4

/-- D9.23. `τ = n^{-ν/4}`. -/
noncomputable def τ (n : ℕ) : ℝ := (n : ℝ) ^ (-(ν e₀ / 4))

/-- D9.22. `δ_n = C ε^{-1} (n^{e-μ} + a^{1/4} (log n)^C)` of Proposition 9.2, `ε = n^{-ν}`. -/
noncomputable def δ (e C Cl : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) ^ ν e₀ * ((n : ℝ) ^ (e - μ e₀) + a (ℓ e₀) (μ e₀) W n ^ (1 / 4 : ℝ) * Real.log n ^ Cl)

/-- D9.22. The `k`-independent part of the energy bound of Proposition 9.2 at the parameters of
D9.20. -/
noncomputable def Edef₀ (e C Cl : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) ^ ℓ e₀ * (D (κ e₀) n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
      (δ e₀ e C Cl n ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-ν e₀) + (n : ℝ) ^ (-100 : ℝ)) +
    C * (n : ℝ) ^ (-1000 : ℝ)

end SmallBox


/-- D9.20 (`scanner:bootstrap-parameters`). For `e₀ ∈ (0, 1)` the parameters
`g₀ = (1 - e₀)/2`, `μ = 1 - g₀`, `ν = g₀/1000`, `ℓ = ν/100 = g₀/10⁵`, `κ = min(ν/100, e_*/4)`,
`W = 4`, fixed once for the whole bootstrap, satisfy `g₀ ∈ (0, 1/2)`, `0 < κ < μ < 1 - ℓ`,
`κ ≤ e_*/4 < (1 - ℓ) e` for every `e > e_*`, and `s W = 1` (`s = 1/4`). -/
theorem step_9_20 {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    0 < SmallBox.g₀ e₀ ∧ SmallBox.g₀ e₀ < 1 / 2 ∧ e₀ = 1 - 2 * SmallBox.g₀ e₀ ∧
      0 < SmallBox.ℓ e₀ ∧ SmallBox.ℓ e₀ < 1 ∧ 0 < SmallBox.κ e₀ ∧
      SmallBox.κ e₀ < SmallBox.μ e₀ ∧ SmallBox.μ e₀ < 1 - SmallBox.ℓ e₀ ∧ 0 < SmallBox.ν e₀ ∧
      SmallBox.κ e₀ ≤ SmallBox.ν e₀ / 100 ∧ SmallBox.κ e₀ ≤ Collar.eStar / 4 ∧
      (∀ e, Collar.eStar < e → SmallBox.κ e₀ < (1 - SmallBox.ℓ e₀) * e) ∧ 1 ≤ SmallBox.W ∧
      1 / 4 * SmallBox.W = 1 := by
  have hg : 0 < SmallBox.g₀ e₀ := by unfold SmallBox.g₀; linarith
  have hg' : SmallBox.g₀ e₀ < 1 / 2 := by unfold SmallBox.g₀; linarith
  have hν : SmallBox.ν e₀ = SmallBox.g₀ e₀ / 1000 := rfl
  have hℓ : SmallBox.ℓ e₀ = SmallBox.g₀ e₀ / 100000 := by unfold SmallBox.ℓ SmallBox.ν; ring
  have hκν : SmallBox.κ e₀ ≤ SmallBox.ν e₀ / 100 := min_le_left _ _
  have hκS : SmallBox.κ e₀ ≤ Collar.eStar / 4 := min_le_right _ _
  have hS : (0 : ℝ) < Collar.eStar := by norm_num [Collar.eStar]
  have hκ : 0 < SmallBox.κ e₀ := lt_min (by rw [hν]; positivity) (by positivity)
  refine ⟨hg, hg', by unfold SmallBox.g₀; ring, by rw [hℓ]; positivity, by rw [hℓ]; linarith,
    hκ, ?_, ?_, by rw [hν]; positivity, hκν, hκS, fun e he => ?_, by norm_num [SmallBox.W],
    by norm_num [SmallBox.W]⟩
  · change SmallBox.κ e₀ < 1 - SmallBox.g₀ e₀
    rw [hν] at hκν
    linarith
  · change 1 - SmallBox.g₀ e₀ < 1 - SmallBox.ℓ e₀
    rw [hℓ]
    linarith
  · have h1 : 0 < 1 / 2 - SmallBox.ℓ e₀ := by rw [hℓ]; linarith
    nlinarith [mul_pos h1 (hS.trans he)]

/-! ## D9.21 The hypotheses of Proposition 9.2 for a safe rectangle -/

/-- D9.21. Suppose `F_box(r) ≤ C_e r^{1+e}` (`r ≥ 1`, `0 < e`). Let `T` be a safe integer
rectangle of maximal side `s₀` (`dist_∞(T, Z) > D₀ s₀`, `D₀ > 2R + 10`), `n = C₂ s₀` with
`C₂ = 5`, and `L ≥ 1`, `r₀` with `40 (L + 1) ≤ n`, `2L + 10 r₀ ≤ 2n` (large `s₀`). Then the
hypotheses of Proposition 9.2 hold with this `e`: `scanner:test-geometry` (`|T| ≤ n²`,
`|T_j \ T_{j-1}| ≤ n` for `1 ≤ j ≤ L`, `dist_∞(T, Z) > 2L + 10 r₀`) and `scanner:entropy-input`
(`S_Ω(A ∩ T) ≤ C_e n^{1+e}`, `S_Ω(A ∩ (T_j \ T)) ≤ C'_e (n L^e + n)` for `j ≤ L`); `C'_e`
depends only on `e`, `C_e`. 2D only: `F_box` is defined over planar safe rectangles. -/
theorem step_9_21 (q R : ℕ) (J Δ e Ce : ℝ) (he : 0 < e) (hCe : 0 < Ce) :
    ∃ Ce' : ℝ, 0 < Ce' ∧ ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
      (∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) →
      ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (OpenAI.Qudits q) X) (Reg (OpenAI.Qudits q) X) ℂ),
        OpenAI.IsAdmissible Λ R J Φ →
      ∀ (Ω : Reg (OpenAI.Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        OpenAI.hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω →
        HasGlobalGap (OpenAI.hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)), IsIntRect T → IsSafe D₀ Λ A T →
      ∀ n L' r : ℕ, n = 5 * boxSize T → 1 ≤ L' → 40 * (L' + 1) ≤ n → 2 * L' + 10 * r ≤ 2 * n →
        T.Nonempty ∧ (#T : ℝ) ≤ 1 * (n : ℝ) ^ 2 ∧
        (∀ j, 1 ≤ j → j ≤ L' → #(ambientDilation T j \ ambientDilation T (j - 1)) ≤ n) ∧
        ((2 * L' + 10 * r : ℕ) : ENNReal) < ambientEDist T (OpenAI.cutEndpoints Λ A) ∧
        (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ) ≤
          Ce * (n : ℝ) ^ (1 + e) ∧
        ∀ j ≤ L', (pureState Ω hΩ).regionEntropy
            (inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
          Ce' * ((n : ℝ) * (L' : ℝ) ^ e + n) := by
  obtain ⟨Ce', hCe', H⟩ := step_9_21_2 q R J Δ e Ce he hCe
  refine ⟨Ce', hCe', fun D₀ hD₀ hF Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T hT hsafe n L' r hn hL1 h40
    hclr => ?_⟩
  obtain ⟨⟨hTcard, hrow⟩, hshell⟩ := H D₀ hD₀ hF Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T hT hsafe
  have hTne : T.Nonempty := by
    obtain ⟨a', b', hab, rfl⟩ := hT
    exact nonempty_Icc.2 hab
  have hs₀ : 1 ≤ boxSize T := by
    by_contra h
    have : boxSize T = 0 := by omega
    have := hTne.card_pos
    simp_all
  have hD₀1 : (10 : ℝ) ≤ D₀ := by have : (0 : ℝ) ≤ R := Nat.cast_nonneg R; linarith
  have hsn : ((boxSize T : ℕ) : ℝ) ≤ n := by exact_mod_cast (show boxSize T ≤ n by omega)
  -- D9.21.1: `L = o(s₀)`, here `8 (L + 1) ≤ s₀`
  have h8 : 8 * (L' + 1) ≤ boxSize T := by omega
  refine ⟨hTne, ?_, fun j hj hjL => (hrow j hj).trans (by omega), ?_, ?_, fun j hj => ?_⟩
  · -- D9.21.1: `|T| ≤ s₀² ≤ n²`
    have h1 : (#T : ℝ) ≤ (boxSize T : ℝ) ^ 2 := by exact_mod_cast hTcard
    have h2 : (boxSize T : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by gcongr
    linarith
  · -- D9.21.1: `dist_∞(T, Z) > D₀ s₀ ≥ 10 s₀ = 2n ≥ 2L + 10 r₀`
    refine lt_of_le_of_lt ?_ hsafe
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ((2 * L' + 10 * r : ℕ) : ℝ) ≤ 10 * (boxSize T : ℝ) := by
      exact_mod_cast (show 2 * L' + 10 * r ≤ 10 * boxSize T by omega)
    have h2 : (10 : ℝ) * boxSize T ≤ D₀ * boxSize T :=
      mul_le_mul_of_nonneg_right hD₀1 (Nat.cast_nonneg _)
    linarith
  · -- D9.21.3: `S_Ω(A ∩ T) ≤ F_box(s₀) ≤ C_e s₀^{1+e} ≤ C_e n^{1+e}`
    refine (le_F_box hD₀ hΦ hΩ hE hgap hA hT hsafe le_rfl).trans ((hF _ hs₀).trans ?_)
    gcongr
  · -- D9.21.2: the shell entropy, squares of side `≤ L` safe since `(D₀ + 1) L ≤ D₀ s₀`
    have hLs : (D₀ + 1) * (L' : ℝ) ≤ D₀ * boxSize T := by
      have h1 : (8 * ((L' : ℝ) + 1)) ≤ boxSize T := by exact_mod_cast h8
      have hL0 : (0 : ℝ) ≤ L' := Nat.cast_nonneg _
      nlinarith
    refine (hshell L' n hL1 hLs (by omega) j hj).1.trans ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith

/-! ## D9.22 The quantitative output of Proposition 9.2 -/

/-- D9.22 (`scanner:bootstrap-energy`). With the parameters of D9.20 and `e ≤ e₀`, for all large
`n`: `δ_n ≤ n^{-0.24 g₀}` and the energy bound of Proposition 9.2 is `E_def ≤ n^{-ν/2} + o_k(1)`;
and the scale conditions hold (D9.22.3): `L ≥ 1`, `K ≥ 1`, `a r₀² ≤ c`, `40 (L + 1) ≤ n`,
`2L + 10 r₀ ≤ 2n`, `τ = n^{-ν/4} < 1/2`. -/
theorem step_9_22 {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) {e : ℝ} (he : e ≤ e₀)
    (C₁ c C Cl : ℝ) (hC₁ : 0 < C₁) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ 1 ≤ L (SmallBox.ℓ e₀) n ∧
      0 < K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n ∧
      a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n * (r₀ C₁ n : ℝ) ^ 2 ≤ c ∧
      40 * (L (SmallBox.ℓ e₀) n + 1) ≤ n ∧ 2 * L (SmallBox.ℓ e₀) n + 10 * r₀ C₁ n ≤ 2 * n ∧
      |SmallBox.δ e₀ e C Cl n| ≤ (n : ℝ) ^ (-(24 / 100 * SmallBox.g₀ e₀)) ∧
      SmallBox.Edef₀ e₀ e C Cl n ≤ (n : ℝ) ^ (-(SmallBox.ν e₀ / 2)) ∧ SmallBox.τ e₀ n < 1 / 2 := by
  obtain ⟨hg, hg', he₀g, hℓ0, -, hκ0, -, -, hν0, hκν, -, -, -, -⟩ := step_9_20 he₀ he₀₁
  have hν : SmallBox.ν e₀ = SmallBox.g₀ e₀ / 1000 := rfl
  have hℓ : SmallBox.ℓ e₀ = SmallBox.g₀ e₀ / 100000 := by unfold SmallBox.ℓ SmallBox.ν; ring
  have hμ : SmallBox.μ e₀ = 1 - SmallBox.g₀ e₀ := rfl
  rw [hν] at hκν
  set p : ℝ := 1 - SmallBox.ℓ e₀ - SmallBox.μ e₀ with hpdef
  have hp : p = SmallBox.g₀ e₀ - SmallBox.ℓ e₀ := by rw [hpdef, hμ]; ring
  have hp0 : 0 < p := by rw [hp, hℓ]; linarith
  -- D9.2: `K ≍ n^{g₀-ℓ}`
  have evp : ∀ᶠ n : ℕ in atTop, (22 : ℝ) ≤ (n : ℝ) ^ p :=
    ((tendsto_rpow_atTop hp0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 22
  -- D9.22.3: `a r₀² → 0`, `L = o(n)`, `r₀ = o(n)`
  have evr := eventually_rpow_log_le (128 * (C₁ + 1) ^ 2 / c) 4 (-p) 0 (by linarith)
  have evL := eventually_rpow_log_le 80 0 (1 - SmallBox.ℓ e₀) 1 (by linarith)
  have evr' := eventually_rpow_log_le (10 * (C₁ + 1)) 2 0 1 (by norm_num)
  -- D9.22.1: the two powers of `δ_n`, `-0.999 g₀` and `-0.2489975 g₀`, below `-0.24 g₀`
  have ev1 := eventually_rpow_log_le (2 * |C|) 0 (SmallBox.ν e₀ + (e - SmallBox.μ e₀))
    (-(24 / 100 * SmallBox.g₀ e₀)) (by rw [hν, hμ]; linarith)
  have ev2 := eventually_rpow_log_le (8 * |C|) Cl (SmallBox.ν e₀ + -p / 4)
    (-(24 / 100 * SmallBox.g₀ e₀)) (by rw [hν, hp, hℓ]; linarith)
  -- D9.22.2: the prefactor `n^ℓ D² W²` has power `ℓ + 2κ ≤ 3·10⁻⁵ g₀`
  have ev3 := eventually_rpow_log_le (256 * |C|) Cl
    (SmallBox.ℓ e₀ + 2 * SmallBox.κ e₀ + -(3 / 100 * SmallBox.g₀ e₀))
    (-(SmallBox.ν e₀ / 2)) (by rw [hν, hℓ]; linarith)
  have ev4 := eventually_rpow_log_le (256 * |C|) Cl
    (SmallBox.ℓ e₀ + 2 * SmallBox.κ e₀ + -SmallBox.ν e₀) (-(SmallBox.ν e₀ / 2))
    (by rw [hν, hℓ]; linarith)
  have ev5 := eventually_rpow_log_le (256 * |C|) Cl (SmallBox.ℓ e₀ + 2 * SmallBox.κ e₀ + -100)
    (-(SmallBox.ν e₀ / 2)) (by rw [hν, hℓ]; linarith)
  have ev6 := eventually_rpow_log_le (4 * |C|) 0 (-1000) (-(SmallBox.ν e₀ / 2))
    (by rw [hν]; linarith)
  have evτ : ∀ᶠ n : ℕ in atTop, SmallBox.τ e₀ n < 1 / 2 :=
    ((tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < SmallBox.ν e₀ / 4)).comp
      tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 3, evp, evr, evL, evr', ev1, ev2, ev3, ev4, ev5, ev6, evτ]
    with n hn3 hnp hr hL hr' h1 h2 h3 h4 h5 h6 hτ
  have hx3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hx0 : (0 : ℝ) < n := by linarith
  have hx1 : (1 : ℝ) ≤ n := by linarith
  have hlg : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hx0]; linarith [Real.exp_one_lt_d9]
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at hr hL hr' h1 h6
  -- `L`, `m`, `K`
  have hL1 : 1 ≤ L (SmallBox.ℓ e₀) n :=
    Nat.one_le_floor_iff _ |>.2 (Real.one_le_rpow hx1 (by rw [hℓ]; linarith))
  have hLle : (L (SmallBox.ℓ e₀) n : ℝ) ≤ (n : ℝ) ^ (1 - SmallBox.ℓ e₀) :=
    Nat.floor_le (by positivity)
  have hLgt : (n : ℝ) ^ (1 - SmallBox.ℓ e₀) < L (SmallBox.ℓ e₀) n + 1 := Nat.lt_floor_add_one _
  have hn1ℓ : 1 ≤ (n : ℝ) ^ (1 - SmallBox.ℓ e₀) := Real.one_le_rpow hx1 (by rw [hℓ]; linarith)
  have hmle : (m (SmallBox.μ e₀) n : ℝ) ≤ (n : ℝ) ^ SmallBox.μ e₀ := Nat.floor_le (by positivity)
  have hμ1 : 1 ≤ (n : ℝ) ^ SmallBox.μ e₀ := Real.one_le_rpow hx1 (by rw [hμ]; linarith)
  have hm1 : 1 ≤ m (SmallBox.μ e₀) n := Nat.one_le_floor_iff _ |>.2 hμ1
  have hdivR : (L (SmallBox.ℓ e₀) n : ℝ) <
      K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n * (8 * m (SmallBox.μ e₀) n) +
        8 * m (SmallBox.μ e₀) n := by
    exact_mod_cast Nat.lt_div_mul_add (a := L (SmallBox.ℓ e₀) n)
      (show 0 < 8 * m (SmallBox.μ e₀) n by omega)
  have hsplit : (n : ℝ) ^ (1 - SmallBox.ℓ e₀) = (n : ℝ) ^ p * (n : ℝ) ^ SmallBox.μ e₀ := by
    rw [← Real.rpow_add hx0]; congr 1; rw [hpdef]; ring
  have hK0 : (0 : ℝ) ≤ K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n := Nat.cast_nonneg _
  have hKp : (n : ℝ) ^ p < 8 * (K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n + 1) + 1 := by
    have h1 : (n : ℝ) ^ p * (n : ℝ) ^ SmallBox.μ e₀ <
        (8 * (K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n + 1) + 1) * (n : ℝ) ^ SmallBox.μ e₀ := by
      have : (K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n + 1 : ℝ) * (8 * m (SmallBox.μ e₀) n) ≤
          (K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n + 1) * (8 * (n : ℝ) ^ SmallBox.μ e₀) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    exact lt_of_mul_lt_mul_right h1 (by positivity)
  have hK : (n : ℝ) ^ p / 32 ≤ K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n := by linarith
  have hKpos : (0 : ℝ) < K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n := lt_of_lt_of_le (by positivity) hK
  have ha0 : 0 < a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n :=
    div_pos (by norm_num [SmallBox.W]) hKpos
  have hnp0 : 0 < (n : ℝ) ^ p := by positivity
  have ha : a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n ≤ 128 * (n : ℝ) ^ (-p) := by
    rw [a, div_le_iff₀ hKpos, Real.rpow_neg hx0.le]
    calc SmallBox.W = 128 * ((n : ℝ) ^ p)⁻¹ * ((n : ℝ) ^ p / 32) := by
          rw [SmallBox.W]; field_simp; norm_num
      _ ≤ _ := by gcongr
  have hr0 : (r₀ C₁ n : ℝ) ≤ (C₁ + 1) * Real.log n ^ 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ C₁ * Real.log n ^ 2 by positivity)
    have := one_le_pow₀ (n := 2) hlg
    rw [r₀]; linarith
  have hlc := Real.rpow_nonneg (show 0 ≤ Real.log n by linarith) Cl
  have hC := abs_nonneg C
  -- D9.22.1: `|δ_n| ≤ n^{-0.24 g₀}`
  have hA4 : a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n ^ (1 / 4 : ℝ) ≤
      4 * (n : ℝ) ^ (-p / 4) := by
    have h256 : (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
      rw [show (256 : ℝ) = 4 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    calc a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n ^ (1 / 4 : ℝ)
        ≤ (256 * (n : ℝ) ^ (-p)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow ha0.le (by linarith [Real.rpow_pos_of_pos hx0 (-p)]) (by norm_num)
      _ = 4 * (n : ℝ) ^ (-p / 4) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), h256, ← Real.rpow_mul hx0.le,
            show -p * (1 / 4 : ℝ) = -p / 4 by ring]
  have hδ : |SmallBox.δ e₀ e C Cl n| ≤ (n : ℝ) ^ (-(24 / 100 * SmallBox.g₀ e₀)) := by
    have ha4 := Real.rpow_nonneg ha0.le (1 / 4 : ℝ)
    rw [SmallBox.δ]
    generalize a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n ^ (1 / 4 : ℝ) = a4 at hA4 ha4 ⊢
    generalize SmallBox.ν e₀ = ν' at h1 h2 ⊢
    generalize e - SmallBox.μ e₀ = q' at h1 ⊢
    have hbr : 0 ≤ (n : ℝ) ^ q' + a4 * Real.log n ^ Cl :=
      add_nonneg (by positivity) (mul_nonneg ha4 hlc)
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 ν'), abs_of_nonneg hbr]
    have e1 : (n : ℝ) ^ ν' * (n : ℝ) ^ q' = (n : ℝ) ^ (ν' + q') := (Real.rpow_add hx0 _ _).symm
    have e3 : (n : ℝ) ^ ν' * (a4 * Real.log n ^ Cl) ≤
        4 * (n : ℝ) ^ (ν' + -p / 4) * Real.log n ^ Cl := by
      rw [Real.rpow_add hx0]
      calc (n : ℝ) ^ ν' * (a4 * Real.log n ^ Cl)
          ≤ (n : ℝ) ^ ν' * (4 * (n : ℝ) ^ (-p / 4) * Real.log n ^ Cl) := by gcongr
        _ = _ := by ring
    calc |C| * (n : ℝ) ^ ν' * ((n : ℝ) ^ q' + a4 * Real.log n ^ Cl)
        = |C| * ((n : ℝ) ^ ν' * (n : ℝ) ^ q') + |C| * ((n : ℝ) ^ ν' * (a4 * Real.log n ^ Cl)) := by
          ring
      _ ≤ |C| * (n : ℝ) ^ (ν' + q') + |C| * (4 * (n : ℝ) ^ (ν' + -p / 4) * Real.log n ^ Cl) := by
          rw [e1]; gcongr
      _ ≤ _ := by linarith
  -- D9.22.2: `δ_n^{1/8} ≤ n^{-0.03 g₀}`, `D ≤ 2 n^κ`, `W² = 16`
  have hroot : |SmallBox.δ e₀ e C Cl n ^ (1 / 8 : ℝ)| ≤
      (n : ℝ) ^ (-(3 / 100 * SmallBox.g₀ e₀)) := by
    refine (Real.abs_rpow_le_abs_rpow _ _).trans ?_
    calc |SmallBox.δ e₀ e C Cl n| ^ (1 / 8 : ℝ)
        ≤ ((n : ℝ) ^ (-(24 / 100 * SmallBox.g₀ e₀))) ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow (abs_nonneg _) hδ (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hx0.le]; congr 1; ring
  have hD : (D (SmallBox.κ e₀) n : ℝ) ≤ 2 * (n : ℝ) ^ SmallBox.κ e₀ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ SmallBox.κ e₀ by positivity)
    have := Real.one_le_rpow hx1 hκ0.le
    rw [D]; linarith
  have hD0 : (0 : ℝ) ≤ D (SmallBox.κ e₀) n := Nat.cast_nonneg _
  have hEd : SmallBox.Edef₀ e₀ e C Cl n ≤ (n : ℝ) ^ (-(SmallBox.ν e₀ / 2)) := by
    rw [SmallBox.Edef₀, SmallBox.W]
    generalize SmallBox.δ e₀ e C Cl n ^ (1 / 8 : ℝ) = d8 at hroot ⊢
    generalize (D (SmallBox.κ e₀) n : ℝ) = Dk at hD hD0 ⊢
    generalize SmallBox.ℓ e₀ = ℓ' at h3 h4 h5 ⊢
    generalize SmallBox.κ e₀ = κ' at h3 h4 h5 hD ⊢
    generalize SmallBox.ν e₀ = ν' at h3 h4 h5 h6 ⊢
    generalize -(3 / 100 * SmallBox.g₀ e₀) = t at h3 hroot
    set Lg := Real.log n ^ Cl with hLg
    have hP0 : 0 ≤ (n : ℝ) ^ ℓ' * Dk ^ 2 * 4 ^ 2 * Lg := by positivity
    have hP : (n : ℝ) ^ ℓ' * Dk ^ 2 * 4 ^ 2 * Lg ≤ 64 * (n : ℝ) ^ (ℓ' + 2 * κ') * Lg := by
      have e : (n : ℝ) ^ (ℓ' + 2 * κ') = (n : ℝ) ^ ℓ' * ((n : ℝ) ^ κ') ^ 2 := by
        rw [Real.rpow_add hx0, mul_comm 2 κ', Real.rpow_mul hx0.le, Real.rpow_two]
      rw [e]
      have : Dk ^ 2 ≤ (2 * (n : ℝ) ^ κ') ^ 2 := pow_le_pow_left₀ hD0 hD 2
      calc (n : ℝ) ^ ℓ' * Dk ^ 2 * 4 ^ 2 * Lg
          ≤ (n : ℝ) ^ ℓ' * (2 * (n : ℝ) ^ κ') ^ 2 * 4 ^ 2 * Lg := by gcongr
        _ = _ := by ring
    have hBk : |d8 + (n : ℝ) ^ (-ν') + (n : ℝ) ^ (-100 : ℝ)| ≤
        (n : ℝ) ^ t + (n : ℝ) ^ (-ν') + (n : ℝ) ^ (-100 : ℝ) := by
      have := Real.rpow_pos_of_pos hx0 (-ν')
      have := Real.rpow_pos_of_pos hx0 (-100 : ℝ)
      have h0 := abs_le.1 hroot
      rw [abs_le]; constructor <;> linarith
    have hsp : ∀ s : ℝ, 64 * (n : ℝ) ^ (ℓ' + 2 * κ') * Lg * (n : ℝ) ^ s =
        64 * (n : ℝ) ^ (ℓ' + 2 * κ' + s) * Lg := fun s => by
      rw [Real.rpow_add hx0 (ℓ' + 2 * κ') s]; ring
    set P := (n : ℝ) ^ ℓ' * Dk ^ 2 * 4 ^ 2 * Lg with hPdef
    set Bk := d8 + (n : ℝ) ^ (-ν') + (n : ℝ) ^ (-100 : ℝ) with hBkdef
    have e1 : C * P * Bk ≤ |C| * P * |Bk| :=
      (le_abs_self _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hP0])
    have e2 : C * (n : ℝ) ^ (-1000 : ℝ) ≤ |C| * (n : ℝ) ^ (-1000 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
    calc C * (n : ℝ) ^ ℓ' * Dk ^ 2 * 4 ^ 2 * Lg * Bk + C * (n : ℝ) ^ (-1000 : ℝ)
        = C * P * Bk + C * (n : ℝ) ^ (-1000 : ℝ) := by rw [hPdef]; ring
      _ ≤ |C| * P * |Bk| + |C| * (n : ℝ) ^ (-1000 : ℝ) := add_le_add e1 e2
      _ ≤ |C| * (64 * (n : ℝ) ^ (ℓ' + 2 * κ') * Lg) *
            ((n : ℝ) ^ t + (n : ℝ) ^ (-ν') + (n : ℝ) ^ (-100 : ℝ)) +
            |C| * (n : ℝ) ^ (-1000 : ℝ) := by gcongr
      _ = |C| * (64 * (n : ℝ) ^ (ℓ' + 2 * κ' + t) * Lg) +
            |C| * (64 * (n : ℝ) ^ (ℓ' + 2 * κ' + -ν') * Lg) +
            |C| * (64 * (n : ℝ) ^ (ℓ' + 2 * κ' + -100) * Lg) +
            |C| * (n : ℝ) ^ (-1000 : ℝ) := by
          rw [← hsp, ← hsp, ← hsp]; ring
      _ ≤ _ := by linarith
  refine ⟨hn3, hL1, by exact_mod_cast hKpos, ?_, ?_, ?_, hδ, hEd, hτ⟩
  · -- D9.22.3: `a r₀² ≤ c`
    have h4 : Real.log n ^ (4 : ℝ) = Real.log n ^ 4 := by exact_mod_cast Real.rpow_natCast _ 4
    rw [h4, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hc] at hr
    calc a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n * (r₀ C₁ n : ℝ) ^ 2
        ≤ 128 * (n : ℝ) ^ (-p) * ((C₁ + 1) * Real.log n ^ 2) ^ 2 := by gcongr
      _ = 128 * (C₁ + 1) ^ 2 * (n : ℝ) ^ (-p) * Real.log n ^ 4 := by ring
      _ ≤ c := hr
  · -- D9.22.3: `40 (L + 1) ≤ n`
    have : (40 * ((L (SmallBox.ℓ e₀) n : ℝ) + 1)) ≤ n := by linarith
    exact_mod_cast this
  · -- D9.22.3: `2L + 10 r₀ ≤ 2n`
    have h2' : Real.log n ^ (2 : ℝ) = Real.log n ^ 2 := by exact_mod_cast Real.rpow_natCast _ 2
    rw [h2'] at hr'
    have : (2 * (L (SmallBox.ℓ e₀) n : ℝ) + 10 * r₀ C₁ n) ≤ 2 * n := by linarith
    exact_mod_cast this

/-! ## D9.23 The rough comparisons -/

section Comparison

open Comparators

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {nd : σ → ℕ} {Dt : PhysData nd}
  {X : Finset σ} {K' : ℕ} {St : Type*} [Fintype St] [DecidableEq St]

/-- D9.23 (`scanner:bootstrap-comparison`). Let the rough comparisons of Proposition 8.1 hold
with `s = 1/4`, `W = aK = 4`, `0 < τ < 1/2`, and the constant `C ≥ 0` of the lower one; let the
selected point have `E_def,k ≤ Ē + o_k(1)` for every `k ≥ 1`, with the relative loss
`2C(τ + Ē₊/τ) ≤ 1` below the margin `4 - 2`; `z ∈ [1/2, 1]`, `B_sh ≤ C_b (n L^e + n)`,
`B_exc ≤ C_b n D`, `n ≤ n L^e`. Then, after `k → ∞`,
`S_X ≤ (16|C_b| + 2C + 8)(n L^e + n D + w + h(τ)/a + 1)`. -/
theorem step_9_23 (Γ : Statuses σ K' St X) (E : TypicalSet Dt X)
    {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} {a' τ' Crl Bsh Bexc Ebar Cb NL n Dk : ℝ}
    (hCrl : 0 ≤ Crl) (ha : 0 < a') (haK : a' * K' = SmallBox.W) (hτ : 0 < τ') (hτ₁ : τ' < 1 / 2)
    (hU : RoughUpper Dt Γ E a' l Bsh Bexc) (hL : RoughLower Dt Γ E Crl a' τ' l)
    (hsel : ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
      ∃ T : Transport.MeanTree St, Edef Dt Γ E T a' k (l k) ≤ Ebar + r k)
    (hmargin : 2 * Crl * (τ' + max Ebar 0 / τ') ≤ 1) (hz : 1 / 2 ≤ E.z) (hz₁ : E.z ≤ 1)
    (hBsh : Bsh ≤ Cb * (NL + n)) (hBexc : Bexc ≤ Cb * n * Dk) (hn : 0 ≤ n) (hnNL : n ≤ NL)
    (hDk : 0 ≤ Dk) :
    Dt.S X ≤ (16 * |Cb| + 2 * Crl + 8) * (NL + n * Dk + E.w + Real.binEntropy τ' / a' + 1) := by
  obtain ⟨r₁, hr₁, hU⟩ := hU
  obtain ⟨r₂, hr₂, hL⟩ := hL
  obtain ⟨r, hr, hsel⟩ := hsel
  have hz0 : 0 < E.z := by linarith
  have hS'0 := S'_nonneg E
  have hld0 : 0 ≤ Real.log E.d :=
    Real.log_nonneg (by exact_mod_cast E.nonempty.card_pos)
  have hh0 : 0 ≤ Real.binEntropy τ' := Real.binEntropy_nonneg hτ.le (by linarith)
  have hS0 : 0 ≤ Dt.S X := SubState.regionEntropy_nonneg _ _
  set Ep := max Ebar 0
  have hEp : 0 ≤ Ep := le_max_right _ _
  -- D9.23.1: at the selected tree, the rough lower bound is below the rough upper bound
  have hk : ∀ k : ℕ, 0 < k →
      4 * E.S' - 2 * Crl * (τ' * Real.log E.d + Real.binEntropy τ' / a') -
          2 * Crl * (Ep / τ') * E.S' ≤
        2 * Real.log E.d - Real.log E.z + (4 * Bsh / E.z + 4 * Bexc) +
          (r₁ k + r₂ k + 2 * Crl * (|r k| / τ') * E.S') := by
    intro k hk
    obtain ⟨T, hT⟩ := hsel k hk
    have h1 := hU k hk T
    have h2 := hL k hk T
    rw [haK, SmallBox.W] at h1 h2
    have hE : Edef Dt Γ E T a' k (l k) / τ' * E.S' ≤ (Ep + |r k|) / τ' * E.S' := by
      have : Edef Dt Γ E T a' k (l k) ≤ Ep + |r k| := hT.trans (add_le_add (le_max_left _ _)
        (le_abs_self _))
      gcongr
    have hE' := mul_le_mul_of_nonneg_left hE hCrl
    have e : (Ep + |r k|) / τ' * E.S' = Ep / τ' * E.S' + |r k| / τ' * E.S' := by ring
    rw [e] at hE'
    have e1 : 2 * (1 / 4) * 4 * (2 * Bsh / E.z + 2 * Bexc) = 4 * Bsh / E.z + 4 * Bexc := by ring
    linarith
  have hlim := le_of_le_add_tendsto (ρ := fun k => r₁ k + r₂ k + 2 * Crl * (|r k| / τ') * E.S')
    (by simpa using (hr₁.add hr₂).add (((hr.abs.div_const τ').const_mul (2 * Crl)).mul_const
      E.S')) hk
  -- D9.23.2: replace `log d_*` and `S'` by `S_X` at cost `δ = w + |log z|`; `z ≥ 1/2`
  obtain ⟨hd, hS'⟩ := step_8_3 E
  obtain ⟨hd1, hd2⟩ := abs_le.1 hd
  obtain ⟨hs1, hs2⟩ := abs_le.1 hS'
  set S := Dt.S X
  set δ' := E.w + |Real.log E.z|
  have hLz : |Real.log E.z| ≤ 1 := by
    have h1 := Real.log_nonpos hz0.le hz₁
    have h2 : Real.log (1 / 2) ≤ Real.log E.z := Real.log_le_log (by norm_num) hz
    rw [one_div, Real.log_inv] at h2
    rw [abs_le]
    constructor <;> linarith [Real.log_two_lt_d9]
  have hδ0 : 0 ≤ δ' := add_nonneg E.w_nonneg (abs_nonneg _)
  have hBz : 4 * Bsh / E.z ≤ 8 * max Bsh 0 := by
    rw [mul_div_assoc]
    have h1 : Bsh / E.z ≤ max Bsh 0 / E.z := div_le_div_of_nonneg_right (le_max_left _ _) hz0.le
    have h2 : max Bsh 0 / E.z ≤ max Bsh 0 / (1 / 2) :=
      div_le_div_of_nonneg_left (le_max_right _ _) (by norm_num) hz
    have h3 : max Bsh 0 / (1 / 2) = 2 * max Bsh 0 := by ring
    linarith
  -- D9.23.3: the relative loss `m₁ + m₂ = 2C(τ + Ē₊/τ)` is below the margin `4 - 2`
  set m₁ := 2 * Crl * τ'
  set m₂ := 2 * Crl * (Ep / τ')
  have hm₁ : 0 ≤ m₁ := by positivity
  have hm₂ : 0 ≤ m₂ := by positivity
  have hm : m₁ + m₂ ≤ 1 := by simp only [m₁, m₂]; linarith
  have t1 : 0 ≤ (4 - m₂) * (E.S' - (S - δ')) := mul_nonneg (by linarith) (by linarith)
  have t2 : m₁ * Real.log E.d ≤ m₁ * (S + δ') := mul_le_mul_of_nonneg_left (by linarith) hm₁
  have t3 : 0 ≤ (1 - m₁ - m₂) * S := mul_nonneg (by linarith) hS0
  have t4 : 0 ≤ (1 - m₁ + m₂) * δ' := mul_nonneg (by linarith) hδ0
  have hS : S ≤ 8 * max Bsh 0 + 4 * Bexc + 7 * δ' + 1 + 2 * Crl * (Real.binEntropy τ' / a') := by
    have e : 2 * Crl * (τ' * Real.log E.d + Real.binEntropy τ' / a') =
        m₁ * Real.log E.d + 2 * Crl * (Real.binEntropy τ' / a') := by simp only [m₁]; ring
    have e' : 2 * Crl * (Ep / τ') * E.S' = m₂ * E.S' := rfl
    rw [e, e'] at hlim
    nlinarith [neg_abs_le (Real.log E.z)]
  -- D9.23.4: `B_sh ≤ C_b (n L^e + n) ≤ 2|C_b| n L^e`, `B_exc ≤ |C_b| n D`, `|log z| ≤ 1`
  have hB1 : max Bsh 0 ≤ 2 * |Cb| * NL := by
    have : Cb * (NL + n) ≤ |Cb| * (NL + n) :=
      mul_le_mul_of_nonneg_right (le_abs_self Cb) (by linarith)
    have : |Cb| * (NL + n) ≤ |Cb| * (2 * NL) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg Cb)
    exact max_le (by linarith) (mul_nonneg (by positivity) (by linarith))
  have hB2 : Bexc ≤ |Cb| * (n * Dk) := by
    have : Cb * n * Dk ≤ |Cb| * n * Dk :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cb) hn) hDk
    linarith
  have hNL : 0 ≤ NL := by linarith
  have hnD : 0 ≤ n * Dk := mul_nonneg hn hDk
  have hha : 0 ≤ Real.binEntropy τ' / a' := div_nonneg hh0 ha.le
  have hw := E.w_nonneg
  have hC := abs_nonneg Cb
  nlinarith [mul_nonneg hC hNL, mul_nonneg hC hnD, mul_nonneg hC hw, mul_nonneg hC hha,
    mul_nonneg hCrl hNL, mul_nonneg hCrl hnD, mul_nonneg hCrl hw, mul_nonneg hCrl hha]

end Comparison

/-! ## D9.24 The exponent improvement and the iteration -/

/-- D9.24.5. If a property `P` of exponents holds at `e₀ > 0`, passes from `e ∈ (e_*, e₀]` to
`(1 - ℓ) e` (`0 < ℓ < 1`) and from `e` to every `e' ≥ e`, then it holds at `e_* > 0`: the
exponents `e₀, (1-ℓ)e₀, …` decrease geometrically and reach `≤ e_*` after finitely many steps. -/
theorem step_9_24_5 {P : ℝ → Prop} {e₀ eS ℓ' : ℝ} (he₀ : 0 < e₀) (hℓ : 0 < ℓ') (hℓ₁ : ℓ' < 1)
    (hS : 0 < eS) (h₀ : P e₀) (hstep : ∀ e, eS < e → e ≤ e₀ → P e → P ((1 - ℓ') * e))
    (hmono : ∀ e e', e ≤ e' → P e → P e') : P eS := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hS he₀) (by linarith : 1 - ℓ' < 1)
  have key : ∀ j : ℕ, P ((1 - ℓ') ^ j * e₀) ∨ ∃ e ≤ eS, P e := by
    intro j
    induction j with
    | zero => left; simpa using h₀
    | succ j ih =>
      rcases ih with h | h
      · by_cases hj : eS < (1 - ℓ') ^ j * e₀
        · left
          have hle : (1 - ℓ') ^ j * e₀ ≤ e₀ :=
            mul_le_of_le_one_left he₀.le (pow_le_one₀ (by linarith) (by linarith))
          have := hstep _ hj hle h
          rwa [pow_succ, mul_comm ((1 - ℓ') ^ j), mul_assoc]
        · exact Or.inr ⟨_, not_lt.1 hj, h⟩
      · exact Or.inr h
  rcases key N with h | ⟨e, he, h⟩
  · exact hmono _ _ (by rw [lt_div_iff₀ he₀] at hN; linarith) h
  · exact hmono _ _ he h

/-- D9.24. Let `e_* < e ≤ e₀` (`e₀` of Proposition 3.3, parameters of D9.20) and
`F_box(r) ≤ C_e r^{1+e}` for `r ≥ 1`. Then `F_box(r) ≤ C''_e r^{1+(1-ℓ)e}` for `r ≥ 1`.
2D only: `F_box` is defined over planar safe rectangles. -/
theorem step_9_24 (h92 : Prop_9_2.{0}) {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hΔ : 0 < Δ)
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) {e Ce : ℝ} (heS : Collar.eStar < e) (he : e ≤ e₀)
    (hCe : 0 < Ce) (hF : ∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) :
    ∃ C'' : ℝ, ∀ r : ℕ, 1 ≤ r →
      F_box q R J Δ r ≤ C'' * (r : ℝ) ^ (1 + (1 - SmallBox.ℓ e₀) * e) := by
  have : NeZero q := ⟨by omega⟩
  -- D9.20
  obtain ⟨-, -, -, hℓ, hℓ₁, hκ, hκμ, hμ, hν, -, hκS, hκe, hW1, -⟩ := step_9_20 he₀ he₀₁
  have hS0 : (0 : ℝ) < Collar.eStar := by norm_num [Collar.eStar]
  have he0 : 0 < e := hS0.trans heS
  have he1 : e < 1 := he.trans_lt he₀₁
  have hκe' : SmallBox.κ e₀ ≤ e := hκS.trans (by linarith)
  set x := 1 + (1 - SmallBox.ℓ e₀) * e with hx
  have hx1 : 1 ≤ x := by
    have : 0 ≤ (1 - SmallBox.ℓ e₀) * e := mul_nonneg (by linarith) he0.le
    linarith
  have hx2 : x ≤ 2 := by
    have : (1 - SmallBox.ℓ e₀) * e ≤ 1 * 1 :=
      mul_le_mul (by linarith) he1.le he0.le zero_le_one
    linarith
  -- D9.21
  obtain ⟨Ce', hCe', H21⟩ := step_9_21 q R J Δ e Ce he0 hCe
  -- Proposition 9.2 on `ℤ × ℤ` with the parameters of D9.20 and the inputs of D9.21
  obtain ⟨C₁, c, Crl, csh, Csu, Csl, C₀, c₀, C, Cl, n₀, hC₁, hc, -, -, -, hCrl, H⟩ :=
    prop_9_2_planar h92 q R J Δ hΔ (SmallBox.ℓ e₀) (SmallBox.κ e₀) (SmallBox.μ e₀)
      (SmallBox.ν e₀) e (max Ce Ce') 1 hℓ hℓ₁ hκ hκμ hμ hν he0 he1 hκe'
      (lt_max_of_lt_left hCe) one_pos
  -- D9.22, and the margin of D9.23.3 (`4 C τ ≤ 1`), for all large `n`
  have evm : ∀ᶠ n : ℕ in atTop, 4 * Crl * SmallBox.τ e₀ n ≤ 1 := by
    have h := ((tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < SmallBox.ν e₀ / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul (4 * Crl)
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds one_pos)).mono fun n hn => hn.le
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (((step_9_22 he₀ he₀₁ he C₁ c C Cl hC₁ hc).and
    evm).and (eventually_ge_atTop n₀))
  set C' := 16 * |C| + 2 * Crl + 8 with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set M := 25 * (6 * C' + 2) with hM
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  refine ⟨max M (n₁ * Real.log q), fun r hr => Real.sSup_le (fun s hs => ?_) (by positivity)⟩
  obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, T, hT, hsafe, hTr, rfl⟩ := hs
  have hs₀ : 1 ≤ boxSize T := by
    obtain ⟨a', b', hab, rfl⟩ := hT
    have := (nonempty_Icc.2 hab).card_pos
    have := card_le_boxSize_sq (Icc a' b')
    by_contra h
    have h0 : boxSize (Icc a' b') = 0 := by omega
    rw [h0] at this
    omega
  have hs₀R : (1 : ℝ) ≤ boxSize T := by exact_mod_cast hs₀
  have hpow : (boxSize T : ℝ) ^ x ≤ (r : ℝ) ^ x :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hTr) (by linarith)
  have hs₀x : (boxSize T : ℝ) ≤ (boxSize T : ℝ) ^ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hs₀R hx1
  suffices h : (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ) ≤
      max M (n₁ * Real.log q) * (boxSize T : ℝ) ^ x from
    h.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  by_cases hsmall : boxSize T < n₁
  · -- D9.24.4: bounded `s₀`, `S ≤ s₀² log q`, absorbed in the constant
    have h := ((pureState Ω hΩ).restrict
      (inter_subset_left.trans hA : A ∩ T ⊆ Λ)).entropy_le_log_card
    rw [card_reg_const (fun _ => Fintype.card_fin q), Nat.cast_pow, Real.log_pow] at h
    have hcard : (#(A ∩ T) : ℝ) ≤ boxSize T * n₁ := by
      have h1 : ((#(A ∩ T) : ℕ) : ℝ) ≤ (boxSize T : ℝ) ^ 2 := by
        exact_mod_cast (card_le_card inter_subset_right).trans (card_le_boxSize_sq T)
      have : (boxSize T : ℝ) ≤ n₁ := by exact_mod_cast hsmall.le
      calc (#(A ∩ T) : ℝ) ≤ (boxSize T : ℝ) ^ 2 := h1
        _ = boxSize T * boxSize T := sq _
        _ ≤ boxSize T * n₁ := mul_le_mul_of_nonneg_left this (by positivity)
    calc (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ)
        ≤ #(A ∩ T) * Real.log q := h
      _ ≤ (boxSize T * n₁) * Real.log q := by gcongr
      _ = n₁ * Real.log q * boxSize T := by ring
      _ ≤ max M (n₁ * Real.log q) * (boxSize T : ℝ) ^ x := by
          gcongr
          exact le_max_right _ _
  push Not at hsmall
  set n := 5 * boxSize T with hn
  obtain ⟨⟨⟨h3n, hL1, hK, har, h40, hclr, -, hEd, hτ⟩, hm⟩, hn₀⟩ := hn₁ n (by omega)
  -- D9.21: the hypotheses of Proposition 9.2
  obtain ⟨hTne, hTcard, hrow, hclear, hSX, hSQ⟩ := H21 D₀ hD₀ hF Λ Φ hΦ Ω hΩ E₀ hE hgap A hA
    T hT hsafe n (L (SmallBox.ℓ e₀) n) (r₀ C₁ n) hn hL1 h40 hclr
  obtain ⟨X, -, hXup, -, Dt, E, St, _, _, Γ, l, 𝓡, Bsh, Bexc, 𝓑, hS, -, hw, hz, -, hBsh, hBexc,
      -, -, -, hU, hL, -, r, hr, hsel⟩ :=
    H n hn₀ SmallBox.W hW1 har Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T hTne hTcard hrow hclear
      (hSX.trans (by gcongr; exact le_max_left _ _))
      (fun j hj => (hSQ j hj).trans (by gcongr; exact le_max_right _ _))
  have hx1' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : (0 : ℝ) < n := by linarith
  -- D9.23
  have hKpos : (0 : ℝ) < K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n := by exact_mod_cast hK
  have ha0 : 0 < a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n :=
    div_pos (by norm_num [SmallBox.W]) hKpos
  have haK : a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n *
      K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n = SmallBox.W := div_mul_cancel₀ _ hKpos.ne'
  have hτ0 : 0 < SmallBox.τ e₀ n := Real.rpow_pos_of_pos hx0 _
  have hτ2 : SmallBox.τ e₀ n * SmallBox.τ e₀ n = (n : ℝ) ^ (-(SmallBox.ν e₀ / 2)) := by
    rw [SmallBox.τ, ← Real.rpow_add hx0]; congr 1; ring
  have hmargin : 2 * Crl * (SmallBox.τ e₀ n +
      max (SmallBox.Edef₀ e₀ e C Cl n) 0 / SmallBox.τ e₀ n) ≤ 1 := by
    have : max (SmallBox.Edef₀ e₀ e C Cl n) 0 / SmallBox.τ e₀ n ≤ SmallBox.τ e₀ n := by
      rw [div_le_iff₀ hτ0, hτ2]
      exact max_le hEd (by positivity)
    calc 2 * Crl * (SmallBox.τ e₀ n + max (SmallBox.Edef₀ e₀ e C Cl n) 0 / SmallBox.τ e₀ n)
        ≤ 2 * Crl * (SmallBox.τ e₀ n + SmallBox.τ e₀ n) := by gcongr
      _ = 4 * Crl * SmallBox.τ e₀ n := by ring
      _ ≤ 1 := hm
  have hz2 : 1 / 2 ≤ E.z := by
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
      calc (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
        _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by
            rw [inv_eq_one_div]
            exact div_le_div_of_nonneg_left zero_le_one (by norm_num) h2n
    linarith
  have hLe1 : 1 ≤ (L (SmallBox.ℓ e₀) n : ℝ) ^ e :=
    Real.one_le_rpow (by exact_mod_cast hL1) he0.le
  have hnNL : (n : ℝ) ≤ n * (L (SmallBox.ℓ e₀) n : ℝ) ^ e := le_mul_of_one_le_right hx0.le hLe1
  have h23 := step_9_23 Γ E hCrl.le ha0 haK hτ0 hτ hU (hL (SmallBox.τ e₀ n) hτ0 hτ)
    ⟨r, hr, hsel⟩ hmargin hz2 (E.z_le_one Comparators.step_8_11) hBsh hBexc hx0.le hnNL
    (Nat.cast_nonneg _)
  -- D9.24.1: `h(τ)/a ≤ n` (`h ≤ log 2 < 1`, `1/a = K/W ≤ L ≤ n`)
  have hLn : (L (SmallBox.ℓ e₀) n : ℝ) ≤ n :=
    (Nat.floor_le (by positivity)).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1' (show 1 - SmallBox.ℓ e₀ ≤ 1 by linarith))
  have hKL : K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n ≤ L (SmallBox.ℓ e₀) n := Nat.div_le_self _ _
  have hKn : (K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n : ℝ) ≤ n :=
    (Nat.cast_le.2 hKL).trans hLn
  have hh : Real.binEntropy (SmallBox.τ e₀ n) / a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n ≤
      n := by
    rw [div_le_iff₀ ha0]
    have hb : Real.binEntropy (SmallBox.τ e₀ n) ≤ 1 :=
      Real.binEntropy_le_log_two.trans (by linarith [Real.log_two_lt_d9])
    have haK4 : a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n *
        K (SmallBox.ℓ e₀) (SmallBox.μ e₀) n = 4 := haK
    have := mul_le_mul_of_nonneg_left hKn ha0.le
    linarith
  -- D9.24.2: `w = n^{3/5} ≤ n`, `n D ≤ 2 n^{1+κ} ≤ 2 n^{1+(1-ℓ)e}` (`κ < (1-ℓ)e`)
  have hw' : E.w ≤ n := by
    rw [hw]; simpa using Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num : (3 / 5 : ℝ) ≤ 1)
  have hN1 : 1 ≤ (n : ℝ) ^ x := Real.one_le_rpow hx1' (by linarith)
  have hnN : (n : ℝ) ≤ (n : ℝ) ^ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx1' hx1
  have hDk : (D (SmallBox.κ e₀) n : ℝ) ≤ 2 * (n : ℝ) ^ SmallBox.κ e₀ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ SmallBox.κ e₀ by positivity)
    have := Real.one_le_rpow hx1' hκ.le
    rw [D]; linarith
  have hnD : (n : ℝ) * D (SmallBox.κ e₀) n ≤ 2 * (n : ℝ) ^ x := by
    have e1 : (n : ℝ) * (n : ℝ) ^ SmallBox.κ e₀ = (n : ℝ) ^ (1 + SmallBox.κ e₀) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    have e2 : (n : ℝ) ^ (1 + SmallBox.κ e₀) ≤ (n : ℝ) ^ x :=
      Real.rpow_le_rpow_of_exponent_le hx1' (by rw [hx]; linarith [hκe e heS])
    calc (n : ℝ) * D (SmallBox.κ e₀) n ≤ n * (2 * (n : ℝ) ^ SmallBox.κ e₀) :=
          mul_le_mul_of_nonneg_left hDk hx0.le
      _ = 2 * ((n : ℝ) * (n : ℝ) ^ SmallBox.κ e₀) := by ring
      _ ≤ 2 * (n : ℝ) ^ x := by rw [e1]; linarith
  -- D9.24.3: `n L^e ≤ n^{1+(1-ℓ)e}`
  have hNL : (n : ℝ) * (L (SmallBox.ℓ e₀) n : ℝ) ^ e ≤ (n : ℝ) ^ x := by
    have h1 : (L (SmallBox.ℓ e₀) n : ℝ) ^ e ≤ ((n : ℝ) ^ (1 - SmallBox.ℓ e₀)) ^ e :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) he0.le
    rw [← Real.rpow_mul hx0.le] at h1
    calc (n : ℝ) * (L (SmallBox.ℓ e₀) n : ℝ) ^ e
        ≤ (n : ℝ) * (n : ℝ) ^ ((1 - SmallBox.ℓ e₀) * e) := by gcongr
      _ = (n : ℝ) ^ x := by rw [hx, Real.rpow_add hx0, Real.rpow_one]
  -- D9.24.3: transfer back `Ω̃ → Ω`, `n^{-200} (1 + |X|) ≤ 2`
  have hXcard : (#X : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : #X = #(A ∩ T) := by rw [← hXup, up, card_map]
    rw [this]
    have h1 : ((#(A ∩ T) : ℕ) : ℝ) ≤ #T := Nat.cast_le.2 (card_le_card inter_subset_right)
    linarith
  have hsmall' : (n : ℝ) ^ (-200 : ℝ) * (1 + #X) ≤ 2 := by
    have h1 : (n : ℝ) ^ (-200 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by norm_num)
    have h2 : (n : ℝ) ^ (-200 : ℝ) * (n : ℝ) ^ 2 ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1' (by norm_num)
    have h0 : 0 ≤ (n : ℝ) ^ (-200 : ℝ) := Real.rpow_nonneg hx0.le _
    have h3 := mul_le_mul_of_nonneg_left hXcard h0
    have e : (n : ℝ) ^ (-200 : ℝ) * (1 + #X) =
        (n : ℝ) ^ (-200 : ℝ) + (n : ℝ) ^ (-200 : ℝ) * #X := by ring
    linarith
  have htr := (abs_le.1 (hS X)).1
  rw [(pureState Ω hΩ).regionEntropy_congr hXup (up_subset X)
    (inter_subset_left.trans hA)] at htr
  -- D9.24.3: `S_Ω(A ∩ T) ≤ C' n^{1+(1-ℓ)e} ≤ C'' s₀^{1+(1-ℓ)e}` (`n = 5 s₀`)
  have h5 : (n : ℝ) ^ x ≤ 25 * (boxSize T : ℝ) ^ x := by
    have e1 : (n : ℝ) ^ x = (5 : ℝ) ^ x * (boxSize T : ℝ) ^ x := by
      rw [hn]; push_cast; exact Real.mul_rpow (by norm_num) (by positivity)
    have e2 : (5 : ℝ) ^ x ≤ 25 := by
      calc (5 : ℝ) ^ x ≤ (5 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx2
        _ = 25 := by norm_num
    rw [e1]
    exact mul_le_mul_of_nonneg_right e2 (by positivity)
  have hsum : (n : ℝ) * (L (SmallBox.ℓ e₀) n : ℝ) ^ e + n * D (SmallBox.κ e₀) n + E.w +
      Real.binEntropy (SmallBox.τ e₀ n) / a (SmallBox.ℓ e₀) (SmallBox.μ e₀) SmallBox.W n + 1 ≤
        6 * (n : ℝ) ^ x := by linarith
  calc (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ)
      ≤ Dt.S X + 2 := by linarith
    _ ≤ C' * (6 * (n : ℝ) ^ x) + 2 * (n : ℝ) ^ x := by
        rw [← hC'] at h23
        linarith [mul_le_mul_of_nonneg_left hsum hC'0]
    _ = (6 * C' + 2) * (n : ℝ) ^ x := by ring
    _ ≤ (6 * C' + 2) * (25 * (boxSize T : ℝ) ^ x) := by gcongr
    _ = M * (boxSize T : ℝ) ^ x := by rw [hM]; ring
    _ ≤ max M (n₁ * Real.log q) * (boxSize T : ℝ) ^ x := by
        gcongr
        exact le_max_left _ _

/-! ## Proposition 9.5 -/

/-- D9.19 **Proposition 9.5** (improved safe-box estimate), from Proposition 9.2. There is `C`
depending only on `q, R, J, Δ` with `F_box(r) ≤ C r^{1+e_*}` (`r ≥ 1`), `e_* = 2·10⁻⁶`.
2D only: `F_box` is defined over planar safe rectangles. -/
theorem prop_9_5_of (h92 : Prop_9_2.{0}) : Prop_9_5 := by
  intro q R J Δ hq hJ hΔ
  -- D3.16 (Proposition 3.3): `e₀ ∈ (0, 1)` and `F_box(r) ≤ C r^{1+e₀}`
  obtain ⟨C₀, e₀, he₀, he₀₁, h33⟩ := prop_3_3 (R := R) hq hJ hΔ
  have hF₀ : ∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ max C₀ 1 * (r : ℝ) ^ (1 + e₀) := fun r hr =>
    Real.sSup_le (fun s hs => by
      obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hQr, rfl⟩ := hs
      exact (h33 D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q r hr hQ hs hQr).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (by positivity)
  obtain ⟨-, -, -, hℓ, hℓ₁, -⟩ := step_9_20 he₀ he₀₁
  -- D9.19: if `e₀ ≤ e_*` done; else D9.20–D9.24 improve `e ↦ (1-ℓ)e`, D9.24.5 iterates
  obtain ⟨C, -, hC⟩ := step_9_24_5
    (P := fun e => ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ C * (r : ℝ) ^ (1 + e))
    he₀ hℓ hℓ₁ (by norm_num [Collar.eStar] : (0 : ℝ) < Collar.eStar)
    ⟨max C₀ 1, by positivity, hF₀⟩
    (fun e heS he ⟨Ce, hCe, hF⟩ => by
      obtain ⟨C'', hC''⟩ := step_9_24 h92 hq hΔ he₀ he₀₁ heS he hCe hF
      exact ⟨max C'' 1, by positivity, fun r hr => (hC'' r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩)
    (fun e e' hee' ⟨Ce, hCe, hF⟩ => ⟨Ce, hCe, fun r hr => (hF r hr).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hr)
        (by linarith)) hCe.le)⟩)
  exact ⟨C, hC⟩

end AreaLaw.Scanner
