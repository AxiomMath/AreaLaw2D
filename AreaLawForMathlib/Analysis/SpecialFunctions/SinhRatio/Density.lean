/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/SinhRatioDensity.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The hyperbolic-sine ratio and its Fourier density

For `0 < s < 1/2` set
\[
  g_s(z) = \frac{\sinh(sz)}{\sinh(z/2)}, \qquad g_s(0) = 2s, \qquad
  m_s(u) = \frac{\sin(2\pi s)}{\cosh(2\pi u) + \cos(2\pi s)} .
\]
This file proves the elementary parts of the area-law Lemma 7.3: `g_s` is continuous
(the quotient is interpreted continuously at zero), `m_s` is positive, integrable, and
has total mass `2s`.

The total mass is computed from the primitive
`u ↦ arctan((e^{2πu} + cos 2πs) / sin 2πs) / π`, whose limits at `-∞` and `+∞` are
`1/2 - 2s` and `1/2`.

## Main definitions

* `Real.sinhRatio s z` — `g_s(z)`, with the value `2s` at `z = 0`.
* `Real.sinhRatioDensity s u` — `m_s(u)`.
* `Complex.sinhRatioDensity s w` — the same formula at a complex argument.

## Main results

* `Real.continuous_sinhRatio` — `g_s` is continuous.
* `Real.sinhRatioDensity_pos`, `Real.integrable_sinhRatioDensity`,
  `Real.integral_sinhRatioDensity` — positivity, integrability and mass `2s`.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.3 (`transport:fourier`), lines 183--244.
  The proofs are written independently from the paper.
-/

open Real Filter Topology MeasureTheory Set

namespace Real

/-- The hyperbolic-sine ratio `g_s(z) = sinh(s z) / sinh(z/2)`, interpreted continuously at
`z = 0` by its limit `2s`.

Area-law paper, display `transport:fourier-density`, `06-transport.tex` lines 184--188. -/
noncomputable def sinhRatio (s z : ℝ) : ℝ := if z = 0 then 2 * s else sinh (s * z) / sinh (z / 2)

/-- The Fourier density `m_s(u) = sin(2πs) / (cosh(2πu) + cos(2πs))`.

Area-law paper, display `transport:fourier-density`, `06-transport.tex` lines 184--188. -/
noncomputable def sinhRatioDensity (s u : ℝ) : ℝ :=
  sin (2 * π * s) / (cosh (2 * π * u) + cos (2 * π * s))

theorem sinhRatio_zero (s : ℝ) : sinhRatio s 0 = 2 * s := by simp [sinhRatio]

theorem sinhRatio_of_ne_zero (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    sinhRatio s z = sinh (s * z) / sinh (z / 2) := by simp [sinhRatio, hz]

/-- `sinh(c z) / z → c` as `z → 0`. -/
private theorem tendsto_sinh_mul_div (c : ℝ) :
    Tendsto (fun z : ℝ ↦ sinh (c * z) / z) (𝓝[≠] 0) (𝓝 c) := by
  have h : HasDerivAt (fun z : ℝ ↦ sinh (c * z)) c 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul c).sinh
    simpa using this
  have := h.tendsto_slope_zero
  simp only [zero_add, mul_zero, sinh_zero, sub_zero, smul_eq_mul] at this
  refine this.congr fun z ↦ ?_
  rw [inv_mul_eq_div]

/-- **Positivity of the density** for `0 < s < 1/2`.

Area-law paper, display `transport:g-fourier`, `06-transport.tex` line 198. -/
theorem sinhRatioDensity_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (u : ℝ) :
    0 < sinhRatioDensity s u := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  refine div_pos (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) ?_
  have hc : -1 < cos (2 * π * s) := by
    rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
  linarith [one_le_cosh (2 * π * u)]

/-- The primitive `u ↦ arctan((e^{2πu} + cos 2πs) / sin 2πs) / π` of the density. -/
noncomputable def sinhRatioDensityPrimitive (s u : ℝ) : ℝ :=
  arctan ((exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s)) / π

/-- The derivative of the primitive is the density. -/
theorem hasDerivAt_sinhRatioDensityPrimitive {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (u : ℝ) :
    HasDerivAt (sinhRatioDensityPrimitive s) (sinhRatioDensity s u) u := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : 0 < sin (2 * π * s) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hexp : HasDerivAt (fun u ↦ (exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s))
      (exp (2 * π * u) * (2 * π) / sin (2 * π * s)) u := by
    have := ((((hasDerivAt_id u).const_mul (2 * π)).exp).add_const
      (cos (2 * π * s))).div_const (sin (2 * π * s))
    simpa [mul_comm] using this
  refine (hexp.arctan.div_const π).congr_deriv ?_
  have hsc := sin_sq_add_cos_sq (2 * π * s)
  have hE : 0 < exp (2 * π * u) := exp_pos _
  have hpos := sinhRatioDensity_pos hs u
  rw [sinhRatioDensity] at hpos ⊢
  have hden : 0 < cosh (2 * π * u) + cos (2 * π * s) := by
    by_contra h; push Not at h
    exact absurd hpos (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hS.le h))
  rw [cosh_eq, exp_neg] at hden ⊢
  have hq : 0 < 1 + ((exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s)) ^ 2 := by positivity
  rw [div_eq_div_iff (by positivity) hden.ne']
  field_simp
  nlinarith [hsc, hE, sq_nonneg (exp (2 * π * u))]

/-- The density is even. -/
theorem sinhRatioDensity_neg (s u : ℝ) : sinhRatioDensity s (-u) = sinhRatioDensity s u := by
  simp [sinhRatioDensity, mul_neg, cosh_neg]

/-- The primitive tends to `1/2` at `+∞`. -/
theorem tendsto_sinhRatioDensityPrimitive_atTop {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (sinhRatioDensityPrimitive s) atTop (𝓝 (1 / 2)) := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : 0 < sin (2 * π * s) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 : Tendsto (fun u : ℝ ↦ (exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s))
      atTop atTop := by
    refine Tendsto.atTop_div_const hS (tendsto_atTop_add_const_right _ _ ?_)
    exact tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have h2 := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp h1
  have h3 := h2.div_const π
  rw [show π / 2 / π = 1 / 2 by field_simp] at h3
  exact h3

/-- The primitive tends to `1/2 - 2s` at `-∞`. -/
theorem tendsto_sinhRatioDensityPrimitive_atBot {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (sinhRatioDensityPrimitive s) atBot (𝓝 (1 / 2 - 2 * s)) := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have h1 : Tendsto (fun u : ℝ ↦ (exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s))
      atBot (𝓝 ((0 + cos (2 * π * s)) / sin (2 * π * s))) := by
    refine ((Tendsto.add ?_ tendsto_const_nhds).div_const _)
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by positivity))
  have h2 := ((continuous_arctan.tendsto _).comp h1).div_const π
  have harg : arctan ((0 + cos (2 * π * s)) / sin (2 * π * s)) = π / 2 - 2 * π * s := by
    rw [zero_add, ← inv_div, ← tan_eq_sin_div_cos, ← tan_pi_div_two_sub]
    exact arctan_tan (by linarith [hθ.2]) (by linarith [hθ.1])
  rw [harg, show (π / 2 - 2 * π * s) / π = 1 / 2 - 2 * s by field_simp] at h2
  exact h2

/-- **The density is integrable** for `0 < s < 1/2`. -/
theorem integrable_sinhRatioDensity {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Integrable (sinhRatioDensity s) := by
  have hIoi : ∀ a : ℝ, IntegrableOn (sinhRatioDensity s) (Ioi a) := fun a ↦
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ ↦ hasDerivAt_sinhRatioDensityPrimitive hs x)
      (fun x _ ↦ (sinhRatioDensity_pos hs x).le) (tendsto_sinhRatioDensityPrimitive_atTop hs)
  have hIio : IntegrableOn (sinhRatioDensity s) (Iio 0) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (measurableEmbedding_neg) (f := sinhRatioDensity s) (s := Ioi 0)
    have hcomp : sinhRatioDensity s ∘ Neg.neg = sinhRatioDensity s := by
      ext u; exact sinhRatioDensity_neg s u
    rw [hcomp, Set.neg_preimage, Set.neg_Ioi, neg_zero] at h
    exact h.mpr (hIoi 0)
  rw [← integrableOn_univ, show (univ : Set ℝ) = Iio 0 ∪ Ioi (-1) by
    ext x; simp only [mem_univ, mem_union, mem_Iio, mem_Ioi, true_iff]; by_contra h
    push Not at h; linarith [h.1, h.2]]
  exact hIio.union (hIoi (-1))

/-- **The total mass of the density is `2s`** for `0 < s < 1/2`.

Area-law paper, display `transport:g-fourier`, `06-transport.tex` line 198. -/
theorem integral_sinhRatioDensity {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    ∫ u, sinhRatioDensity s u = 2 * s := by
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_sinhRatioDensityPrimitive hs)
    (integrable_sinhRatioDensity hs) (tendsto_sinhRatioDensityPrimitive_atBot hs)
    (tendsto_sinhRatioDensityPrimitive_atTop hs)]
  ring

end Real

namespace Complex

/-- The Fourier density at a complex argument,
`m_s(w) = sin(2πs) / (cosh(2πw) + cos(2πs))`. -/
noncomputable def sinhRatioDensity (s : ℝ) (w : ℂ) : ℂ :=
  Real.sin (2 * Real.pi * s) / (cosh (2 * Real.pi * w) + Real.cos (2 * Real.pi * s))

end Complex
