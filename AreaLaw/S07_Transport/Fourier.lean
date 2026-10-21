import AreaLawForMathlib.Analysis.SpecialFunctions.SinhRatio.Shift

/-!
# §7.2 Fourier formulas for inverse powers

Digest `digest/07-transport.md` D7.6–D7.7, paper `paper/sections/06-transport.tex` 181–243.
The classical part of Lemma 7.3 (the Fourier transform of `m_s`, Bhatia–Parthasarathy) and the
pole-free contour shift are the library's
(`AreaLawForMathlib/Analysis/SpecialFunctions/SinhRatio/`); the functions `h_±`, the densities
`q_±` and the bound `|q_±| ≤ m_s/√2` at `s = 1/4` are here. No geometry.
-/

open Real MeasureTheory Set
open Complex (I)

namespace AreaLaw.Transport

/-! ## D7.6 The multipliers `g_s` and `m_s` -/

/-- D7.6 (`transport:fourier-density`). For `0 < s < 1/2`:
`g_s(z) = sinh(sz)/sinh(z/2)`, `g_s(0) = 2s`. -/
noncomputable abbrev g (s z : ℝ) : ℝ := Real.sinhRatio s z

/-- D7.6 (`transport:fourier-density`). For `0 < s < 1/2`:
`m_s(u) = sin(2πs)/(cosh(2πu) + cos(2πs))`. -/
noncomputable abbrev m (s u : ℝ) : ℝ := Real.sinhRatioDensity s u

/-! ## D7.7 Lemma 7.3 -/

/-- D7.7 (`transport:h-def`). `h_+(z) = (e^{sz} − 1)/(2 sinh(z/2))` at `s = 1/4`, read
continuously at `0` (value `s`). -/
noncomputable def hPlus (z : ℝ) : ℝ :=
  if z = 0 then 1 / 4 else (Real.exp (1 / 4 * z) - 1) / (2 * Real.sinh (z / 2))

/-- D7.7 (`transport:h-def`). `h_-(z) = (e^{-sz} − 1)/(2 sinh(z/2))` at `s = 1/4`, read
continuously at `0` (value `-s`). -/
noncomputable def hMinus (z : ℝ) : ℝ :=
  if z = 0 then -(1 / 4) else (Real.exp (-(1 / 4 * z)) - 1) / (2 * Real.sinh (z / 2))

/-- D7.7 (`transport:q-density`). `q_+(u) = m_{s/2}(u + is/2)` at `s = 1/4`. -/
noncomputable def qPlus (u : ℝ) : ℂ := Complex.sinhRatioDensity (1 / 8) (u + (1 / 8 : ℝ) * I)

/-- D7.7 (`transport:q-density`). `q_-(u) = -m_{s/2}(u - is/2)` at `s = 1/4`. -/
noncomputable def qMinus (u : ℝ) : ℂ :=
  -Complex.sinhRatioDensity (1 / 8) (u + (-(1 / 8) : ℝ) * I)

/-- D7.7.5. `e^{σsz} − 1 = e^{σsz/2}(2σ sinh(sz/2))`, so for `z ≠ 0`
`(e^{σsz} − 1)/(2 sinh(z/2)) = σ e^{σsz/2} g_{s/2}(z)` (`σ = ±1`). -/
theorem step_7_7_5 (s : ℝ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {z : ℝ} (hz : z ≠ 0) :
    (Real.exp (σ * (s * z)) - 1) / (2 * Real.sinh (z / 2)) =
      σ * (Real.exp (σ * (s * z) / 2) * g (s / 2) z) := by
  have hne : Real.sinh (z / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact div_ne_zero hz two_ne_zero
  have h1 : Real.exp (σ * (s * z)) - 1 =
      Real.exp (σ * (s * z) / 2) * (2 * Real.sinh (σ * (s / 2 * z))) := by
    have e1 : Real.exp (σ * (s * z)) = Real.exp (σ * (s * z) / 2) * Real.exp (σ * (s * z) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(σ * (s * z) / 2)) * Real.exp (σ * (s * z) / 2) = 1 := by
      rw [← Real.exp_add]; simp
    rw [Real.sinh_eq, show σ * (s / 2 * z) = σ * (s * z) / 2 by ring, e1]
    linear_combination e2
  have h2 : Real.sinh (σ * (s / 2 * z)) = σ * Real.sinh (s / 2 * z) := by
    rcases hσ with rfl | rfl <;> simp [Real.sinh_neg]
  rw [h1, h2, g, Real.sinhRatio_of_ne_zero _ hz]
  field_simp

/-- D7.7.7. At `s = 1/4`, with `c = cosh 2πu`: `m_{1/8}(u ± i/8) = 1/(c + 1 ± i sinh 2πu)`,
`|c + 1 ± i sinh 2πu|² = 2c(c + 1)`, so `|q_±(u)| ≤ m_s(u)/√2`. -/
theorem step_7_7_7 (u : ℝ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖Complex.sinhRatioDensity (1 / 8) (u + σ * I / 8)‖ ≤ m (1 / 4) u / √2 := by
  set c := Real.cosh (2 * π * u)
  set sh := Real.sinh (2 * π * u)
  have hc : 1 ≤ c := Real.one_le_cosh _
  have hcs : sh ^ 2 = c ^ 2 - 1 := by
    have := Real.cosh_sq (2 * π * u); simp only [c, sh]; linarith
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hcosσ : Real.cos (σ * (π / 4)) = √2 / 2 := by
    rcases hσ with rfl | rfl <;> simp [Real.cos_pi_div_four]
  have hsinσ : Real.sin (σ * (π / 4)) = σ * (√2 / 2) := by
    rcases hσ with rfl | rfl <;> simp [Real.sin_pi_div_four]
  have harg : (2 * (π : ℂ) * (u + σ * I / 8)) =
      ((2 * π * u : ℝ) : ℂ) + ((σ * (π / 4) : ℝ) : ℂ) * I := by
    push_cast; ring
  -- `cosh(2πu ± iπ/4) = (c ± i sinh 2πu)/√2`, `m_{1/8}(u ± i/8) = 1/(c + 1 ± i sinh 2πu)`
  have hval : Complex.sinhRatioDensity (1 / 8) (u + σ * I / 8) =
      1 / (((c + 1 : ℝ) : ℂ) + ((σ * sh : ℝ) : ℂ) * I) := by
    rw [Complex.sinhRatioDensity, harg, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      hcosσ, hsinσ, show 2 * π * (1 / 8 : ℝ) = π / 4 by ring, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
    simp only [c, sh]
    push_cast
    field_simp
    ring
  -- `m_s = 1/c` at `s = 1/4`
  have hm : m (1 / 4) u = 1 / c := by
    rw [m, Real.sinhRatioDensity, show 2 * π * (1 / 4 : ℝ) = π / 2 by ring, Real.sin_pi_div_two,
      Real.cos_pi_div_two, add_zero]
  -- ratio `c/√(2c(c+1)) ≤ 1/√2`
  rw [hval, hm, norm_div, norm_one, Complex.norm_add_mul_I]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  rw [show c * √2 = √(2 * c ^ 2) by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith), mul_comm]]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, hσ2, hcs]
  nlinarith

/-- D7.7 **Lemma 7.3** (the two Fourier multipliers). Fix `0 < s < 1/2`.
1. For real `z`: `g_s(z) = ∫_ℝ e^{iuz} m_s(u) du`, `m_s > 0`, `∫_ℝ m_s = 2s`.
2. For `s = 1/4` the functions (quotients read continuously at `0`)
   `h_±(z) = (e^{±sz} − 1)/(2 sinh(z/2)) = ±e^{±sz/2} g_{s/2}(z)` have Fourier densities
   `q_±(u) = ±m_{s/2}(u ± is/2)`, i.e. `h_±(z) = ∫ e^{iuz} q_±(u) du`, with
   `|q_±(u)| ≤ m_s(u)/√2`. -/
theorem lemma_7_3 :
    (∀ s ∈ Ioo (0 : ℝ) (1 / 2),
      (∀ z : ℝ, ∫ u : ℝ, Complex.exp (I * u * z) * (m s u : ℂ) = (g s z : ℂ)) ∧
      (∀ u, 0 < m s u) ∧ ∫ u, m s u = 2 * s) ∧
    (∀ z : ℝ, hPlus z = Real.exp (1 / 4 * z / 2) * g (1 / 8) z ∧
      hMinus z = -(Real.exp (-(1 / 4 * z) / 2) * g (1 / 8) z)) ∧
    (∀ z : ℝ, ∫ u : ℝ, Complex.exp (I * u * z) * qPlus u = (hPlus z : ℂ) ∧
      ∫ u : ℝ, Complex.exp (I * u * z) * qMinus u = (hMinus z : ℂ)) ∧
    ∀ u : ℝ, ‖qPlus u‖ ≤ m (1 / 4) u / √2 ∧ ‖qMinus u‖ ≤ m (1 / 4) u / √2 := by
  have hs : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2) := by norm_num
  -- D7.7.5, with the value at `0`: `h_±(0) = ±s = ±e^0 g_{s/2}(0)`
  have h5 : ∀ z : ℝ, hPlus z = Real.exp (1 / 4 * z / 2) * g (1 / 8) z ∧
      hMinus z = -(Real.exp (-(1 / 4 * z) / 2) * g (1 / 8) z) := fun z ↦ by
    rcases eq_or_ne z 0 with rfl | hz
    · simp [hPlus, hMinus, g, Real.sinhRatio_zero]; norm_num
    · have hp := step_7_7_5 (1 / 4) (Or.inl rfl) hz
      have hm := step_7_7_5 (1 / 4) (Or.inr rfl) hz
      simp only [one_mul, neg_mul, show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at hp hm
      exact ⟨by rw [hPlus, if_neg hz, hp], by rw [hMinus, if_neg hz, hm]⟩
  refine ⟨fun s hs ↦ ⟨?_, ?_, ?_⟩, h5, fun z ↦ ⟨?_, ?_⟩, fun u ↦ ⟨?_, ?_⟩⟩
  -- D7.7.1–D7.7.3: residues in the strip `0 < Im u < 1`, rectangle contour, periodicity
  · exact Complex.integral_exp_mul_sinhRatioDensity hs
  -- D7.7.4: positivity
  · exact Real.sinhRatioDensity_pos hs
  -- D7.7.3: the value at `0` (total mass `2s`)
  · exact Real.integral_sinhRatioDensity hs
  -- D7.7.6: `e^{sz/2} e^{iuz} = e^{i(u - is/2)z}`; shift by `is/2` crosses no pole
  · have h := Complex.integral_exp_mul_sinhRatioDensity_shift hs z (σ := 1 / 8)
      (by rw [abs_of_pos (by norm_num)]; norm_num)
    simp only [qPlus, show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at h ⊢
    rw [h, (h5 z).1]
    push_cast; ring_nf
  · have h := Complex.integral_exp_mul_sinhRatioDensity_shift hs z (σ := -(1 / 8))
      (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num)
    simp only [qMinus, mul_neg, show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at h ⊢
    rw [integral_neg, h, (h5 z).2]
    push_cast; ring_nf
  -- D7.7.7
  · have := step_7_7_7 u (σ := 1) (Or.inl rfl)
    simp only [qPlus]; convert this using 3; push_cast; ring
  · have := step_7_7_7 u (σ := -1) (Or.inr rfl)
    rw [show qMinus u = -Complex.sinhRatioDensity (1 / 8) (u + ((-1 : ℝ) : ℂ) * I / 8) by
      simp only [qMinus]; congr 2; push_cast; ring, norm_neg]
    exact this

/-- D7.7 Output: `∫ m_{1/4} = 1/2`. -/
theorem integral_m_quarter : ∫ u, m (1 / 4) u = 1 / 2 := by
  rw [(lemma_7_3.1 (1 / 4) (by norm_num)).2.2]; norm_num

theorem integrable_m {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) : Integrable (m s) :=
  Real.integrable_sinhRatioDensity hs

private theorem densityDenom_ne_zero_shift (u σ : ℝ) (hσ : |σ| ≤ 1 / 8) :
    Complex.densityDenom (1 / 8) (u + σ * I) ≠ 0 := by
  have h := Complex.densityDenom_half_ne_zero (s := 1 / 4) (w := u + σ * I) (by norm_num)
    (by
      have : ((u : ℂ) + σ * I).im = σ := by simp
      rw [this]; linarith)
  rwa [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at h

theorem continuous_qPlus : Continuous qPlus := by
  unfold qPlus Complex.sinhRatioDensity
  refine Continuous.div continuous_const (by fun_prop) fun u ↦ ?_
  exact densityDenom_ne_zero_shift u (1 / 8) (by rw [abs_of_pos (by norm_num)])

theorem continuous_qMinus : Continuous qMinus := by
  unfold qMinus Complex.sinhRatioDensity
  refine (Continuous.div continuous_const (by fun_prop) fun u ↦ ?_).neg
  exact densityDenom_ne_zero_shift u (-(1 / 8)) (by rw [abs_neg, abs_of_pos (by norm_num)])

/-- D7.7 Output (used in D7.23.6): `q_±` are integrable and `∫ |q_±| ≤ 1/(2√2)`. -/
theorem integral_norm_q_le :
    Integrable qPlus ∧ Integrable qMinus ∧ ∫ u, ‖qPlus u‖ ≤ 1 / (2 * √2) ∧
      ∫ u, ‖qMinus u‖ ≤ 1 / (2 * √2) := by
  have hm := (integrable_m (s := 1 / 4) (by norm_num)).div_const √2
  have hb := lemma_7_3.2.2.2
  have hP : Integrable qPlus := hm.mono' continuous_qPlus.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ (hb u).1)
  have hM : Integrable qMinus := hm.mono' continuous_qMinus.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ (hb u).2)
  have hint : ∫ u, m (1 / 4) u / √2 = 1 / (2 * √2) := by
    rw [integral_div, integral_m_quarter]; ring
  refine ⟨hP, hM, ?_, ?_⟩
  · rw [← hint]; exact integral_mono hP.norm hm fun u ↦ (hb u).1
  · rw [← hint]; exact integral_mono hM.norm hm fun u ↦ (hb u).2

end AreaLaw.Transport
