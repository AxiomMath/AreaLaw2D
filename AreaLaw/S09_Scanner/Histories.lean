import AreaLaw.S09_Scanner.Histories.Ancestry

/-!
# §9.1 Lemma 9.1: geometry and probabilities of the scan (D9.8)

Digest `digest/09-scanner.md` D9.8, paper `paper/sections/08-scanner.tex` 195–338. Graph-level
(Map.md, Dimension: `any d`). The items are proved in `Histories/Geometry.lean` (items 1–3 and
the availability of item 4, D9.8.1–11, 16) and `Histories/Ancestry.lean` (the tail of item 4,
D9.8.12–15), under the standing hypotheses `Scan.Hyp`; here the scales of D9.2 are shown to
satisfy them for large `n` (`scanner:scales`, D9.8 Pitfall (a): `r₀ ≪ D ≪ m ≪ L`).
-/

open scoped Matrix
open Finset Filter Topology Arealaw Asymptotics

namespace AreaLaw.Scanner

universe u

/-! ## Scales -/

/-- Polylogarithms are eventually below any power: `c (C₁ (log n)² + 2)^k ≤ n^s`. -/
theorem eventually_polylog_le {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (c s : ℝ) (k : ℕ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, c * (C₁ * Real.log n ^ 2 + 2) ^ k ≤ (n : ℝ) ^ s := by
  set ε : ℝ := 1 / ((|c| + 1) * (C₁ + 2) ^ k)
  have hε : 0 < ε := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop ((2 * k : ℕ) : ℝ) hs).bound hε
  have h2 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have h3 : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (h1.and (h2.and h3))] with n hn
  obtain ⟨hb, hlog, hpos⟩ := hn
  rw [Real.rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg hpos.le _)] at hb
  have hl2 : (1 : ℝ) ≤ Real.log n ^ 2 := one_le_pow₀ hlog
  have h4 : C₁ * Real.log n ^ 2 + 2 ≤ (C₁ + 2) * Real.log n ^ 2 := by nlinarith
  have h5 : (C₁ * Real.log n ^ 2 + 2) ^ k ≤ (C₁ + 2) ^ k * Real.log n ^ (2 * k) := by
    calc (C₁ * Real.log n ^ 2 + 2) ^ k ≤ ((C₁ + 2) * Real.log n ^ 2) ^ k :=
          pow_le_pow_left₀ (by positivity) h4 k
      _ = (C₁ + 2) ^ k * Real.log n ^ (2 * k) := by rw [mul_pow, ← pow_mul]
  have h6 : c * (C₁ * Real.log n ^ 2 + 2) ^ k ≤ (|c| + 1) * ((C₁ + 2) ^ k *
      Real.log n ^ (2 * k)) := by
    have : 0 ≤ (C₁ * Real.log n ^ 2 + 2) ^ k := by positivity
    calc c * (C₁ * Real.log n ^ 2 + 2) ^ k ≤ (|c| + 1) * (C₁ * Real.log n ^ 2 + 2) ^ k := by
          gcongr; linarith [le_abs_self c]
      _ ≤ _ := by gcongr
  calc c * (C₁ * Real.log n ^ 2 + 2) ^ k
      ≤ (|c| + 1) * ((C₁ + 2) ^ k * Real.log n ^ (2 * k)) := h6
    _ ≤ (|c| + 1) * ((C₁ + 2) ^ k * (ε * (n : ℝ) ^ s)) := by gcongr
    _ = (n : ℝ) ^ s := by
        simp only [ε]
        field_simp

/-- A smaller power is eventually below any fraction of a larger one: `c n^κ ≤ n^μ`. -/
theorem eventually_rpow_le {κ μ : ℝ} (hκμ : κ < μ) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ κ ≤ (n : ℝ) ^ μ := by
  have h1 : Tendsto (fun x : ℝ => x ^ (μ - κ)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (h1.eventually_ge_atTop c),
    eventually_gt_atTop 0] with n hn hn0
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn0
  calc c * (n : ℝ) ^ κ ≤ (n : ℝ) ^ (μ - κ) * (n : ℝ) ^ κ :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hpos.le _)
    _ = (n : ℝ) ^ μ := by rw [← Real.rpow_add hpos]; ring_nf

/-- A positive power is eventually above any constant. -/
theorem eventually_le_rpow {s : ℝ} (hs : 0 < s) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ s :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hs).eventually_ge_atTop c)

theorem r₀_le (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (n : ℕ) : (r₀ C₁ n : ℝ) ≤ C₁ * Real.log n ^ 2 + 1 :=
  (Nat.ceil_lt_add_one (by positivity)).le

theorem le_D (κ : ℝ) (n : ℕ) : (n : ℝ) ^ κ ≤ D κ n := Nat.le_ceil _

theorem D_le (κ : ℝ) (n : ℕ) : (D κ n : ℝ) ≤ (n : ℝ) ^ κ + 1 :=
  (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)).le

/-- D9.2–D9.3 (`scanner:scales`). For large `n`: `m ≥ 1`, `D ≥ 1`, `2 r₀ ≤ D`,
`4 (D + r₀ + 1) ≤ m`, `m ≤ n`, `L ≤ n`. -/
theorem eventually_scales {ℓ κ μ C₁ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) (hκμ : κ < μ)
    (hμ : μ < 1 - ℓ) (hC₁ : 0 < C₁) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 ≤ m μ n ∧ 1 ≤ D κ n ∧ 2 * r₀ C₁ n ≤ D κ n ∧
      4 * (D κ n + r₀ C₁ n + 1) ≤ m μ n ∧ m μ n ≤ n ∧ L ℓ n ≤ n := by
  have hμ0 : 0 < μ := hκ.trans hκμ
  filter_upwards [eventually_ge_atTop 1, eventually_polylog_le hC₁.le 2 κ 1 hκ,
    eventually_rpow_le hκμ 32, eventually_polylog_le hC₁.le 32 μ 1 hμ0,
    eventually_le_rpow hμ0 160] with n hn h2 h3 h4 h5
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [pow_one] at h2 h4
  have hκn : 0 < (n : ℝ) ^ κ := Real.rpow_pos_of_pos (by linarith) _
  have hr₀ := r₀_le C₁ hC₁.le n
  have hD := le_D κ n
  have hD' := D_le κ n
  have hm : (n : ℝ) ^ μ - 1 < m μ n := Nat.sub_one_lt_floor _
  have hlog : 0 ≤ C₁ * Real.log n ^ 2 := by positivity
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Nat.one_le_floor_iff _).2 (Real.one_le_rpow hn' hμ0.le)
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hκn).ne'
  · have : ((2 * r₀ C₁ n : ℕ) : ℝ) ≤ D κ n := by push_cast; linarith
    exact_mod_cast this
  · have : ((4 * (D κ n + r₀ C₁ n + 1) : ℕ) : ℝ) < m μ n := by push_cast; linarith
    exact_mod_cast this.le
  · have h1 : (n : ℝ) ^ μ ≤ n := by
      calc (n : ℝ) ^ μ ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
        _ = n := Real.rpow_one _
    exact Nat.floor_le_of_le h1
  · have h1 : (n : ℝ) ^ (1 - ℓ) ≤ n := by
      calc (n : ℝ) ^ (1 - ℓ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
        _ = n := Real.rpow_one _
    exact Nat.floor_le_of_le h1

/-- D9.8.15, the arithmetic of the tail: with `ρ = e · 4 n (2 r₀ + 3) μ_R V(r₀)² / (2M)`,
`M ≥ C_l n D`, `V(r₀) ≤ K₀ (r₀ + 1)^{m₀}`, `D ≥ n^κ` and a polylogarithmic `r₀`, the ratio is
`ρ ≤ C r₀^{2m₀+1}/D ≤ n^{-κ/2}`, and the union bound `2K · 5mn · (2nm + 1) · ρ^{ℓ₀}` over
chains of length `≥ ℓ₀ ≥ 2(M + 6)/κ` is `≤ n^{-M}`. -/
theorem tail_arith {n K m D r₀ M μR V₀ ℓ₀ A m₀ : ℕ} {K₀ κ Cl Mt ℒ : ℝ} (hn : 30 ≤ n)
    (hK : K ≤ n) (hm : m ≤ n) (hκ : 0 < κ) (hCl : (μR : ℝ) ≤ Cl) (hCl0 : 0 < Cl)
    (hM : Cl * n * D ≤ M) (hV₀ : (V₀ : ℝ) ≤ K₀ * ℒ ^ m₀) (hr : (r₀ : ℝ) + 1 ≤ ℒ)
    (hD : (n : ℝ) ^ κ ≤ D)
    (hpoly : 6 * Real.exp 1 * K₀ ^ 2 * ℒ ^ (2 * m₀ + 1) ≤ (n : ℝ) ^ (κ / 2))
    (hA : Mt + 6 ≤ κ * A / 2) (hℓ₀ : A ≤ ℓ₀) :
    Real.exp 1 * (4 * n * (2 * r₀ + 3)) * (μR * V₀ * V₀) / (2 * M) ≤ 1 ∧
      2 * K * (5 * m * n) * (2 * n * m + 1) *
        (Real.exp 1 * (4 * n * (2 * r₀ + 3)) * (μR * V₀ * V₀) / (2 * M)) ^ ℓ₀ ≤
        (n : ℝ) ^ (-Mt) := by
  set N : ℝ := (n : ℝ) with hNdef
  have hN : (30 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  set X : ℝ := N ^ (κ / 2)
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by linarith)
  have hX0 : 0 < X := by linarith
  have hNκ : N ^ κ = X * X := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hD0 : 0 < (D : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 κ) hD
  have hM0 : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hM
  have hℒ1 : 1 ≤ ℒ := by have : (0 : ℝ) ≤ r₀ := Nat.cast_nonneg _; linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set ρ := Real.exp 1 * (4 * n * (2 * r₀ + 3)) * (μR * V₀ * V₀) / (2 * M) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- `ρ ≤ 6 e K₀² ℒ^{2m₀+1} / n^κ ≤ 1/X`
  have hρX : ρ ≤ 1 / X := by
    have hV0 : (0 : ℝ) ≤ V₀ := Nat.cast_nonneg _
    have hμ0 : (0 : ℝ) ≤ μR := Nat.cast_nonneg _
    have h1 : ρ ≤
        Real.exp 1 * (4 * N * (2 * r₀ + 3)) * (μR * V₀ * V₀) / (2 * (Cl * N * D)) := by
      rw [hρ]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    have h2 : Real.exp 1 * (4 * N * (2 * r₀ + 3)) * (μR * V₀ * V₀) / (2 * (Cl * N * D)) =
        2 * Real.exp 1 * (2 * r₀ + 3) * (μR / Cl) * V₀ ^ 2 / D := by
      field_simp
      ring
    have h3 : 2 * Real.exp 1 * (2 * r₀ + 3) * (μR / Cl) * V₀ ^ 2 ≤
        6 * Real.exp 1 * K₀ ^ 2 * ℒ ^ (2 * m₀ + 1) := by
      have h4 : (2 * r₀ + 3 : ℝ) ≤ 3 * ℒ := by linarith
      have h5 : μR / Cl ≤ 1 := (div_le_one hCl0).2 hCl
      have h6 : (V₀ : ℝ) ^ 2 ≤ (K₀ * ℒ ^ m₀) ^ 2 := pow_le_pow_left₀ hV0 hV₀ 2
      have h7 : (0 : ℝ) ≤ μR / Cl := by positivity
      calc 2 * Real.exp 1 * (2 * r₀ + 3) * (μR / Cl) * V₀ ^ 2
          ≤ 2 * Real.exp 1 * (3 * ℒ) * 1 * (K₀ * ℒ ^ m₀) ^ 2 := by gcongr
        _ = 6 * Real.exp 1 * K₀ ^ 2 * ℒ ^ (2 * m₀ + 1) := by ring
    calc ρ ≤ 2 * Real.exp 1 * (2 * r₀ + 3) * (μR / Cl) * V₀ ^ 2 / D := h1.trans h2.le
      _ ≤ 6 * Real.exp 1 * K₀ ^ 2 * ℒ ^ (2 * m₀ + 1) / N ^ κ := by
          apply div_le_div₀ (by positivity) h3 (Real.rpow_pos_of_pos hN0 κ) hD
      _ ≤ X / (X * X) := by rw [hNκ]; exact div_le_div_of_nonneg_right hpoly (by positivity)
      _ = 1 / X := by field_simp
  have hρ1 : ρ ≤ 1 := hρX.trans (by rw [div_le_one hX0]; exact hX1)
  refine ⟨hρ1, ?_⟩
  -- `ρ^{ℓ₀} ≤ X^{-A} ≤ n^{-(M + 6)}`
  have hpow : ρ ^ ℓ₀ ≤ 1 / N ^ (Mt + 6) := by
    calc ρ ^ ℓ₀ ≤ ρ ^ A := pow_le_pow_of_le_one hρ0 hρ1 hℓ₀
      _ ≤ (1 / X) ^ A := pow_le_pow_left₀ hρ0 hρX A
      _ = 1 / N ^ (κ / 2 * A) := by
          rw [one_div_pow, Real.rpow_mul hN0.le, Real.rpow_natCast]
      _ ≤ 1 / N ^ (Mt + 6) := by
          apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _)
          exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpre : 2 * (K : ℝ) * (5 * m * N) * (2 * N * m + 1) ≤ 30 * N ^ 5 := by
    have hK' : (K : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hK
    have hm' : (m : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hm
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    calc 2 * (K : ℝ) * (5 * m * N) * (2 * N * m + 1) ≤
          2 * N * (5 * N * N) * (2 * N * N + N * N) := by
          gcongr
          nlinarith
      _ = 30 * N ^ 5 := by ring
  have hsplit : N ^ (Mt + 6) = N ^ Mt * N ^ 5 * N := by
    rw [Real.rpow_add hN0, show (6 : ℝ) = ((5 : ℕ) : ℝ) + 1 by norm_num, Real.rpow_add hN0,
      Real.rpow_natCast, Real.rpow_one]
    ring
  have hMt0 : 0 < N ^ Mt := Real.rpow_pos_of_pos hN0 _
  calc 2 * (K : ℝ) * (5 * m * N) * (2 * N * m + 1) * ρ ^ ℓ₀
      ≤ 30 * N ^ 5 * (1 / N ^ (Mt + 6)) := by gcongr
    _ = 30 / N * (1 / N ^ Mt) := by
        rw [hsplit]
        field_simp
    _ ≤ 1 * (1 / N ^ Mt) := by
        gcongr
        rw [div_le_one hN0]
        exact hN
    _ = N ^ (-Mt) := by rw [one_mul, Real.rpow_neg hN0.le, one_div]

section Hyp

variable {σ : Type u} [DecidableEq σ]

/-- The scan at the scales of D9.2 satisfies the standing hypotheses of Lemma 9.1, with the
charge list length `M_n = ⌈(3 μ_R + 1) n D⌉`. -/
theorem hyp_scanAt (G : SimpleGraph σ) [DecidableRel G.Adj] (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(GraphDomain.ball G Λ x r) ≤ V r) (R : ℕ)
    (ℓ κ μ CT C₁ : ℝ) (Λ A : Finset σ) (dep : σ → ℕ) (a : Finset σ → σ) (n : ℕ)
    (hm : 0 < m μ n) (hM : 0 < Mn (3 * AreaLaw.μ V R + 1) n (D κ n)) (hA : A ⊆ Λ)
    (ha : ∀ Y ∈ GraphDomain.supports G Λ R, a Y ∈ Y)
    (htg : TestGeometry G Λ A dep CT n (L ℓ n) (r₀ C₁ n)) (hn : 1 ≤ n) (hD : 1 ≤ D κ n)
    (h2 : 2 * r₀ C₁ n ≤ D κ n) (h4 : 4 * (D κ n + r₀ C₁ n + 1) ≤ m μ n) :
    (scanAt G Λ A dep R a ℓ κ μ C₁ (3 * AreaLaw.μ V R + 1) n hm hM).Hyp V CT where
  tg := htg
  hV := hV
  hA := hA
  anchor := ha
  n_pos := hn
  D_pos := hD
  r₀_le := h2
  m_ge := h4
  KL := by
    change 8 * (L ℓ n / (8 * m μ n)) * m μ n ≤ L ℓ n
    have := Nat.div_mul_le_self (L ℓ n) (8 * m μ n)
    calc 8 * (L ℓ n / (8 * m μ n)) * m μ n = L ℓ n / (8 * m μ n) * (8 * m μ n) := by ring
      _ ≤ L ℓ n := this
  M_ge := by
    change AreaLaw.μ V R * (n * (D κ n + r₀ C₁ n + 1)) ≤
      ⌈(3 * (AreaLaw.μ V R : ℝ) + 1) * n * D κ n⌉₊
    have h1 : AreaLaw.μ V R * (n * (D κ n + r₀ C₁ n + 1)) ≤ 3 * AreaLaw.μ V R * n * D κ n := by
      have : D κ n + r₀ C₁ n + 1 ≤ 3 * D κ n := by omega
      calc AreaLaw.μ V R * (n * (D κ n + r₀ C₁ n + 1))
          ≤ AreaLaw.μ V R * (n * (3 * D κ n)) := by gcongr
        _ = 3 * AreaLaw.μ V R * n * D κ n := by ring
    refine h1.trans ?_
    have h3 : ((3 * AreaLaw.μ V R * n * D κ n : ℕ) : ℝ) ≤
        (3 * (AreaLaw.μ V R : ℝ) + 1) * n * D κ n := by
      push_cast
      have : (0 : ℝ) ≤ n * D κ n := by positivity
      nlinarith
    exact_mod_cast h3.trans (Nat.le_ceil _)

end Hyp

end AreaLaw.Scanner

namespace AreaLaw.Scanner

universe u

/-- D9.8 **Lemma 9.1** (geometry and probabilities of the scan). -/
theorem lemma_9_1 : Lemma_9_1.{u} := by
  intro σ _ G _ V hV K₀ m₀ _hK₀ hK R ℓ κ μ CT C₁ hℓ _hℓ1 hκ hκμ hμ _hCT hC₁
  set Cl : ℝ := 3 * AreaLaw.μ V R + 1 with hCl
  have hμ0 : (0 : ℝ) ≤ AreaLaw.μ V R := Nat.cast_nonneg _
  have hCl1 : 1 ≤ Cl := by linarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_scales hℓ hκ hκμ hμ hC₁)
  have hC₂ := (Scan.C₂_ge V R).1
  refine ⟨Cl, Scan.C₂ V R, 1 / (4 * Cl), n₀, by linarith, by linarith, by positivity, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨h1, hm, hD, -⟩ := hn₀ n hn
    refine ⟨hm, ?_⟩
    unfold Mn
    apply Nat.ceil_pos.2
    have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    have : (1 : ℝ) ≤ D κ n := by exact_mod_cast hD
    positivity
  · intro n hn Λ A dep a hm hM hA ha htg
    obtain ⟨h1, -, hD, h2, h4, -, -⟩ := hn₀ n hn
    have H := hyp_scanAt G V hV R ℓ κ μ CT C₁ Λ A dep a n hm hM hA ha htg h1 hD h2 h4
    refine ⟨H.item1, H.item2, H.item3, H.item4 _ ?_⟩
    change 1 / (4 * Cl) * (2 * (Mn Cl n (D κ n) : ℝ)) ≤ n * D κ n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    have hD1 : (1 : ℝ) ≤ D κ n := by exact_mod_cast hD
    have hM1 : (Mn Cl n (D κ n) : ℝ) ≤ Cl * n * D κ n + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h3 : (1 : ℝ) ≤ Cl * n * D κ n := by
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ Cl * n * D κ n := by gcongr
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  · intro Mt hMt
    set A : ℕ := ⌈2 * (Mt + 6) / κ⌉₊ with hAdef
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((eventually_ge_atTop 30).and
      ((eventually_polylog_le hC₁.le (6 * Real.exp 1 * K₀ ^ 2) (κ / 2) (2 * m₀ + 1)
        (by positivity)).and (eventually_polylog_le hC₁.le (4 * (A + 1) + 1) κ 1 hκ)))
    refine ⟨max n₀ n₁, fun n hn Λ A' dep a hm hM hA ha htg t => ?_⟩
    obtain ⟨h1, -, hD, h2, h4, hmn, hLn⟩ := hn₀ n (le_of_max_le_left hn)
    obtain ⟨h30, hpoly, hpoly2⟩ := hn₁ n (le_of_max_le_right hn)
    have H := hyp_scanAt G V hV R ℓ κ μ CT C₁ Λ A' dep a n hm hM hA ha htg h1 hD h2 h4
    have hK' : K ℓ μ n ≤ n := (Nat.div_le_self _ _).trans hLn
    have hr := r₀_le C₁ hC₁.le n
    have hr' : (r₀ C₁ n : ℝ) + 1 ≤ C₁ * Real.log n ^ 2 + 2 := by linarith
    have hV₀ : (V (r₀ C₁ n) : ℝ) ≤ K₀ * (C₁ * Real.log n ^ 2 + 2) ^ m₀ := by
      refine (hK (r₀ C₁ n)).trans ?_
      gcongr
    have hMnD : Cl * n * D κ n ≤ Mn Cl n (D κ n) := Nat.le_ceil _
    have hAκ : Mt + 6 ≤ κ * A / 2 := by
      have := Nat.le_ceil (2 * (Mt + 6) / κ)
      rw [← hAdef] at this
      rw [div_le_iff₀ hκ] at this
      linarith
    have hℓ₀ : A ≤ (D κ n / 2) / (2 * r₀ C₁ n + 1) := by
      rw [Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
      have hDκ := le_D κ n
      simp only [pow_one] at hpoly2
      have hlog : 0 ≤ C₁ * Real.log n ^ 2 := by positivity
      have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
      have : ((A * (2 * r₀ C₁ n + 1) * 2 : ℕ) : ℝ) ≤ D κ n := by
        push_cast
        nlinarith
      exact_mod_cast this
    obtain ⟨hρ, hfin⟩ := tail_arith (K := K ℓ μ n) (m := m μ n) (D := D κ n) (r₀ := r₀ C₁ n)
      (M := Mn Cl n (D κ n)) (μR := AreaLaw.μ V R) (V₀ := V (r₀ C₁ n))
      (ℓ₀ := (D κ n / 2) / (2 * r₀ C₁ n + 1)) (A := A) (m₀ := m₀) h30 hK' hmn hκ
      (by linarith) (by linarith) hMnD hV₀ hr' (le_D κ n) hpoly hAκ hℓ₀
    refine (H.tail_le t hρ).trans (Eq.trans_le ?_ hfin)
    change 2 * (K ℓ μ n : ℝ) * (5 * m μ n * n) * ((2 * n * m μ n : ℕ) + 1) * _ = _
    push_cast
    ring

end AreaLaw.Scanner
