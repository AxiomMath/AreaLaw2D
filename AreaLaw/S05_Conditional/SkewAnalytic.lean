import AreaLaw.S05_Conditional.Defs
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# §5.3 Lemma 5.3, the complex-analysis half (D5.16.6, D5.18, D5.19)

Digest `digest/05-conditional.md`, D5.15–D5.19, for an arbitrary entire `f : ℂ → ℂ` with the
properties D5.16.3–5, D5.17 and D5.18.1 establish for `Conditional.f`.

Some declarations here come from the v1 file `OpenAI/SkewFromPhases.lean`, whose header records it
as ported or adapted from `LionSR/QICLean` (see `NOTICE`).
-/

namespace AreaLaw

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real

namespace Conditional

/-- Three lines on `0 ≤ Re z ≤ w`, bound `A` on the imaginary axis and `B` on the strip. -/
theorem three_lines {F : ℂ → ℂ} (hF : Differentiable ℂ F) {w A B : ℝ} (hw : 0 < w)
    (hA : ∀ u : ℝ, ‖F (u * I)‖ ≤ A) (hB : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ w → ‖F z‖ ≤ B)
    {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ w) :
    ‖F z‖ ≤ A ^ (1 - z.re / w) * B ^ (z.re / w) := by
  have := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hw ⟨h0, h1⟩
    hF.diffContOnCl ⟨B, by rintro _ ⟨v, ⟨hv0, hv1⟩, rfl⟩; exact hB v hv0 hv1⟩
    (fun v (hv : v.re = 0) ↦ by
      rw [show v = (v.im : ℂ) * I from Complex.ext (by simp [hv]) (by simp)]; exact hA v.im)
    (fun v (hv : v.re = w) ↦ hB v (hv ▸ hw.le) hv.le)
  simpa using this

/-- Second-order Taylor remainder from a disk bound (Cauchy estimates):
`‖g t − g 0 − t g'(0)‖ ≤ 3 M ‖t‖² / δ²` for `‖t‖ ≤ δ`, if `‖g‖ ≤ M` on the closed `δ`-disk. -/
theorem norm_sub_sub_deriv_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {M δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ z ∈ closedBall (0 : ℂ) δ, ‖g z‖ ≤ M) {t : ℂ} (ht : ‖t‖ ≤ δ) :
    ‖g t - g 0 - t * deriv g 0‖ ≤ 3 * M * ‖t‖ ^ 2 / δ ^ 2 := by
  set k : ℂ → ℂ := fun w ↦ g w - g 0 - w * deriv g 0
  have hk : Differentiable ℂ k :=
    (hg.sub (differentiable_const _)).sub (differentiable_id.mul (differentiable_const _))
  have hkd : deriv k 0 = 0 := by
    have h2 : HasDerivAt k (deriv g 0 - 0 - 1 * deriv g 0) 0 :=
      ((hg 0).hasDerivAt.sub (hasDerivAt_const _ _)).sub ((hasDerivAt_id 0).mul_const _)
    simpa using h2.deriv
  have hds : ∀ {h : ℂ → ℂ}, Differentiable ℂ h → Differentiable ℂ (dslope h 0) := fun hh _ ↦
    ((differentiableOn_dslope (s := univ) univ_mem).mpr hh.differentiableOn).differentiableAt
      univ_mem
  set q := dslope (dslope k 0) 0
  have hkq : ∀ w, k w = w ^ 2 * q w := fun w ↦ by
    have e1 := sub_smul_dslope k 0 w
    have e2 := sub_smul_dslope (dslope k 0) 0 w
    rw [dslope_same, hkd] at e2
    simp only [k, sub_zero, smul_eq_mul, sub_self, zero_mul] at e1 e2 ⊢
    rw [← e1, ← e2]; ring
  have hgd : ‖deriv g 0‖ ≤ M / δ :=
    norm_deriv_le_of_forall_mem_sphere_norm_le hδ hg.diffContOnCl
      fun z hz ↦ hM z (sphere_subset_closedBall hz)
  have hqb : ∀ w ∈ closedBall (0 : ℂ) δ, ‖q w‖ ≤ 3 * M / δ ^ 2 := by
    intro w hw
    rw [← closure_ball (0 : ℂ) hδ.ne'] at hw
    refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hds (hds hk)).diffContOnCl
      (fun v hv ↦ ?_) hw
    rw [frontier_ball (0 : ℂ) hδ.ne'] at hv
    have hvn : ‖v‖ = δ := by simpa using hv
    have hkv : ‖k v‖ ≤ M + M + δ * (M / δ) :=
      calc ‖k v‖ ≤ ‖g v‖ + ‖g 0‖ + ‖v * deriv g 0‖ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
        _ ≤ _ := by
          rw [norm_mul, hvn]
          gcongr
          exacts [hM v (sphere_subset_closedBall hv), hM 0 (mem_closedBall_self hδ.le)]
    rw [hkq v, norm_mul, norm_pow, hvn, mul_div_cancel₀ _ hδ.ne'] at hkv
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc ‖g t - g 0 - t * deriv g 0‖ = ‖t‖ ^ 2 * ‖q t‖ := by
        rw [show g t - g 0 - t * deriv g 0 = k t from rfl, hkq, norm_mul, norm_pow]
    _ ≤ ‖t‖ ^ 2 * (3 * M / δ ^ 2) := by gcongr; exact hqb t (by simpa using ht)
    _ = 3 * M * ‖t‖ ^ 2 / δ ^ 2 := by ring

/-- The Gaussian damps the phase error: for `0 ≤ R ≤ 1`,
`(2K |sinh πu| R + K² sinh²(πu) R²) e^{-u²} ≤ (2K + K²) e^{π²} R`. -/
theorem phase_mul_exp_le {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hR1 : R ≤ 1) (u : ℝ) :
    (2 * K * |Real.sinh (π * u)| * R + K ^ 2 * Real.sinh (π * u) ^ 2 * R ^ 2) *
      Real.exp (-u ^ 2) ≤ (2 * K + K ^ 2) * Real.exp (π ^ 2) * R := by
  have hs : |Real.sinh (π * u)| ≤ Real.exp (π * |u|) := by
    rw [Real.sinh_eq, abs_div, abs_two, div_le_iff₀ two_pos, abs_le]
    have := Real.exp_le_exp.2 (le_abs_self (π * u))
    have := Real.exp_le_exp.2 (neg_le_abs (π * u))
    rw [abs_mul, abs_of_pos Real.pi_pos] at *
    constructor <;> nlinarith [Real.exp_pos (π * u), Real.exp_pos (-(π * u))]
  have he1 : |Real.sinh (π * u)| * Real.exp (-u ^ 2) ≤ Real.exp (π ^ 2) := by
    refine (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (|u| - π / 2), sq_abs u, Real.pi_pos]
  have he2 : Real.sinh (π * u) ^ 2 * Real.exp (-u ^ 2) ≤ Real.exp (π ^ 2) := by
    rw [← sq_abs]
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hs 2)
      (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_le_exp.2
    push_cast; nlinarith [sq_nonneg (|u| - π), sq_abs u]
  have hR2 : K ^ 2 * R ^ 2 ≤ K ^ 2 * R := by gcongr; nlinarith
  calc _ = 2 * K * R * (|Real.sinh (π * u)| * Real.exp (-u ^ 2)) +
        K ^ 2 * R ^ 2 * (Real.sinh (π * u) ^ 2 * Real.exp (-u ^ 2)) := by ring
    _ ≤ 2 * K * R * Real.exp (π ^ 2) + K ^ 2 * R * Real.exp (π ^ 2) := by
        gcongr
    _ = _ := by ring

theorem tendsto_sinh_pi_mul_div :
    Tendsto (fun u : ℝ ↦ Real.sinh (π * u) / u) (𝓝[≠] 0) (𝓝 π) := by
  have h := hasDerivAt_iff_tendsto_slope.1 <|
    (Real.hasDerivAt_sinh _).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul π)
  simp only [id, mul_zero, Real.cosh_zero, one_mul, mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp [slope_def_field, div_eq_inv_mul]

end Conditional

open Conditional

/-- D5.16.6. Three lines on `0 ≤ Re z ≤ 1/4`: `f` entire, `|f(iu)| ≤ 1` (D5.16.5), `|f| ≤ D`
on `0 ≤ Re z ≤ 1/4` (D5.16.3, `D = d_h²`) and `f(-z̄) = \overline{f(z)}` (D5.16.4) give
`|f(z)| ≤ 1^{1-4 Re z} D^{4 Re z}`; negative side by D5.16.4. -/
theorem step_5_16_6 {f : ℂ → ℂ} (hf : Differentiable ℂ f) {D : ℝ}
    (him : ∀ u : ℝ, ‖f (u * I)‖ ≤ 1) (hstrip : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 4 → ‖f z‖ ≤ D)
    (hsymm : ∀ z, f (-conj z) = conj (f z)) {z : ℂ} (hz : |z.re| ≤ 1 / 4) :
    ‖f z‖ ≤ D ^ (4 * |z.re|) := by
  wlog h0 : 0 ≤ z.re generalizing z
  · simpa [hsymm] using this (z := -conj z) (by simpa using hz) (by simp; linarith)
  rw [abs_of_nonneg h0] at hz ⊢
  simpa [div_eq_mul_inv, mul_comm] using three_lines hf (by norm_num) him hstrip h0 hz

/-- D5.16.6, consequence. With `D = d_h²` and `log d_h ≤ ℓ_h`: `|f(z)| ≤ d_h^{8 |Re z|} ≤ e^{8 c₀}`
on `|Re z| ≤ c₀/ℓ_h`, `c₀ ≤ 1/4`. -/
theorem step_5_16_6_narrow {f : ℂ → ℂ} (hf : Differentiable ℂ f) {dh : ℕ} (hdh : 1 ≤ dh)
    (him : ∀ u : ℝ, ‖f (u * I)‖ ≤ 1)
    (hstrip : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 4 → ‖f z‖ ≤ (dh : ℝ) ^ 2)
    (hsymm : ∀ z, f (-conj z) = conj (f z)) {c₀ : ℝ} (hc₀ : c₀ ≤ 1 / 4) {z : ℂ}
    (hz : |z.re| ≤ c₀ / ℓ dh) : ‖f z‖ ≤ Real.exp (8 * c₀) := by
  have hL := one_le_ℓ hdh
  have hd : (1 : ℝ) ≤ dh := by exact_mod_cast hdh
  have hc0 : 0 ≤ c₀ := by
    have := mul_nonneg ((abs_nonneg _).trans hz) (zero_le_one.trans hL)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  have hlog : Real.log dh ≤ ℓ dh := by
    rw [ℓ, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]; linarith
  have h := step_5_16_6 hf him hstrip hsymm (hz.trans <| (div_le_self hc0 hL).trans hc₀)
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow] at h
  refine h.trans (Real.exp_le_exp.2 ?_)
  have := mul_le_mul hlog hz (abs_nonneg _) (by linarith)
  rw [mul_div_cancel₀ _ (by positivity)] at this
  push_cast; nlinarith [abs_nonneg z.re, Real.log_nonneg hd]

/-- D5.18.2–3. `f` entire, `f(0) = p`, `f(iu)` real, and
`|f(iu) − p| ≤ 2√p K |sinh πu| R + K² sinh²(πu) R²` for all real `u` (D5.18.1, D5.17):
`f'(0) ∈ iℝ` and `|f'(0)| ≤ 2π K √p R`. -/
theorem step_5_18 {f : ℂ → ℂ} (hf : Differentiable ℂ f) {p K R : ℝ} (hf0 : f 0 = p)
    (hreal : ∀ u : ℝ, (f (u * I)).im = 0)
    (hphase : ∀ u : ℝ, ‖f (u * I) - p‖ ≤
      2 * √p * K * |Real.sinh (π * u)| * R + K ^ 2 * Real.sinh (π * u) ^ 2 * R ^ 2) :
    (deriv f 0).re = 0 ∧ ‖deriv f 0‖ ≤ 2 * π * K * √p * R := by
  set g : ℝ → ℂ := fun u ↦ f (u * I)
  have hg : HasDerivAt g (deriv f 0 * I) 0 := by
    have h2 : HasDerivAt f (deriv f 0) ((0 : ℝ) * I : ℂ) := by simpa using (hf 0).hasDerivAt
    exact h2.comp (0 : ℝ) (by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I)
  constructor
  · -- D5.18.3
    have h := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg).unique
      ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Eventually.of_forall fun u ↦ hreal u))
    simpa using h
  · -- D5.18.2
    have hnorm := (hasDerivAt_iff_tendsto_slope.1 hg).norm
    rw [norm_mul, norm_I, mul_one] at hnorm
    have h1 := tendsto_sinh_pi_mul_div.abs
    have h2 : Tendsto (fun u : ℝ ↦ |Real.sinh (π * u)|) (𝓝[≠] 0) (𝓝 |Real.sinh (π * 0)|) :=
      ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).abs.tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hB := ((tendsto_const_nhds (x := 2 * √p * K)).mul h1 |>.mul_const R).add
      (((tendsto_const_nhds (x := K ^ 2)).mul h1).mul h2 |>.mul_const (R ^ 2))
    simp only [mul_zero, Real.sinh_zero, abs_zero, abs_of_pos Real.pi_pos, zero_mul,
      add_zero] at hB
    rw [show 2 * π * K * √p * R = 2 * √p * K * π * R by ring]
    refine le_of_tendsto_of_tendsto hnorm hB ?_
    filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
    rw [slope_def_module, norm_smul, sub_zero, norm_inv, Real.norm_eq_abs]
    calc |u|⁻¹ * ‖g u - g 0‖ ≤ |u|⁻¹ * (2 * √p * K * |Real.sinh (π * u)| * R +
            K ^ 2 * Real.sinh (π * u) ^ 2 * R ^ 2) := by
          gcongr; simpa [g, hf0] using hphase u
      _ = _ := by
          simp only [abs_div, ← sq_abs (Real.sinh _)]
          field_simp

/-- D5.19 (D5.15.4–5). Universal `c₀ = 1/8` and `C` (depending on the constant `K` of Lemma 5.2)
such that: `f` entire with `f(-z̄) = \overline{f(z)}`, `f(0) = p`, `f(iu) ∈ [0,1]`,
`|f| ≤ d_h²` on `|Re z| ≤ 1/4`, `|f(iu) − p| ≤ 2√p K |sinh πu| R + K² sinh²(πu) R²`, `R ≥ 0`,
`m = min(1, R)`, `0 < a`, `a ℓ_h ≤ c₀/4`, `t = a/2 ≤ b/8` (`b = c₀/ℓ_h`):
`|f(t)| − Re f(t) ≤ C a² (ℓ_h² m^{1/2} + R²)`. -/
theorem step_5_19 (K : ℝ) (hK : 0 ≤ K) : ∃ c₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (f : ℂ → ℂ) (p R a : ℝ) (dh : ℕ), Differentiable ℂ f →
      (∀ z, f (-conj z) = conj (f z)) → f 0 = p →
      (∀ u : ℝ, (f (u * I)).im = 0 ∧ 0 ≤ (f (u * I)).re ∧ (f (u * I)).re ≤ 1) →
      1 ≤ dh → (∀ z : ℂ, |z.re| ≤ 1 / 4 → ‖f z‖ ≤ (dh : ℝ) ^ 2) →
      (∀ u : ℝ, ‖f (u * I) - p‖ ≤
        2 * √p * K * |Real.sinh (π * u)| * R + K ^ 2 * Real.sinh (π * u) ^ 2 * R ^ 2) →
      0 ≤ R → 0 < a → a * ℓ dh ≤ c₀ / 4 →
      ‖f ((a / 2 : ℝ) : ℂ)‖ - (f ((a / 2 : ℝ) : ℂ)).re ≤
        C * a ^ 2 * (ℓ dh ^ 2 * √(min 1 R) + R ^ 2) := by
  set K1 := (8 + 2 * K + K ^ 2) * Real.exp (π ^ 2)
  have hE : 1 ≤ Real.exp (π ^ 2) := Real.one_le_exp (sq_nonneg _)
  have hK1 : 8 * Real.exp (π ^ 2) + (2 * K + K ^ 2) * Real.exp (π ^ 2) ≤ K1 := by
    simp only [K1]; nlinarith
  have hK10 : 0 < K1 := by positivity
  have hK2 : 0 ≤ (2 * K + K ^ 2) * Real.exp (π ^ 2) := by positivity
  refine ⟨1 / 8, 384 * Real.exp 1 * K1 + π ^ 2 * K ^ 2 + 1, by norm_num, by norm_num,
    by positivity, fun f p R a dh hf hsymm hf0 hax hdh hstrip hphase hR ha hal ↦ ?_⟩
  set L := ℓ dh
  have hL : 1 ≤ L := one_le_ℓ hdh
  set b := 1 / 8 / L
  have hb0 : 0 < b := by positivity
  have hb8 : b ≤ 1 / 8 := div_le_self (by norm_num) hL
  set m := min 1 R
  have hm0 : 0 ≤ m := le_min zero_le_one hR
  have hm1 : m ≤ 1 := min_le_left _ _
  obtain ⟨hp0, hp1⟩ : 0 ≤ p ∧ p ≤ 1 := by simpa [hf0] using hax 0
  have him : ∀ u : ℝ, ‖f (u * I)‖ ≤ 1 := fun u ↦ by
    rw [← Complex.re_add_im (f _), (hax u).1, ofReal_zero, zero_mul, add_zero, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hax u).2.1]
    exact (hax u).2.2
  have hnarrow : ∀ z : ℂ, |z.re| ≤ b → ‖f z‖ ≤ Real.exp 1 := fun z hz ↦ by
    simpa using step_5_16_6_narrow hf hdh him (fun w h0 h1 ↦ hstrip w (by rwa [abs_of_nonneg h0]))
      hsymm (c₀ := 1 / 8) (by norm_num) hz
  set F : ℂ → ℂ := fun z ↦ (f z - p) * Complex.exp (z ^ 2)
  have hF : Differentiable ℂ F :=
    (hf.sub (differentiable_const _)).mul (differentiable_exp.comp (differentiable_id.pow 2))
  have hnormexp : ∀ z : ℂ, ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := fun z ↦ by
    rw [Complex.norm_exp]; congr 1; simp [sq]
  have hfp : ∀ z, ‖f z‖ ≤ Real.exp 1 → ‖f z - p‖ ≤ Real.exp 1 + 1 := fun z hz ↦
    (norm_sub_le _ _).trans (by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]; linarith)
  -- D5.19.1 imaginary axis: `|F(iu)| ≤ K₁ m`
  have hFim : ∀ u : ℝ, ‖F (u * I)‖ ≤ K1 * m := fun u ↦ by
    have hnorm : ‖F (u * I)‖ = ‖f (u * I) - p‖ * Real.exp (-u ^ 2) := by
      simp only [F, norm_mul, hnormexp]; congr 2; simp
    rw [hnorm]
    rcases le_total R 1 with hR1 | hR1
    · rw [show m = R from min_eq_right hR1]
      have hsp : √p ≤ 1 := (Real.sqrt_le_sqrt hp1).trans_eq Real.sqrt_one
      have h1 : ‖f (u * I) - p‖ ≤ 2 * K * |Real.sinh (π * u)| * R +
          K ^ 2 * Real.sinh (π * u) ^ 2 * R ^ 2 := (hphase u).trans (by
        gcongr; nlinarith [mul_nonneg (mul_nonneg hK (abs_nonneg (Real.sinh (π * u)))) hR])
      calc _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ (2 * K + K ^ 2) * Real.exp (π ^ 2) * R := phase_mul_exp_le hK hR hR1 u
        _ ≤ K1 * R := by gcongr; linarith
    · rw [show m = 1 from min_eq_left hR1, mul_one]
      have h2 : ‖f (u * I) - p‖ ≤ 2 := (norm_sub_le _ _).trans (by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]; linarith [him u])
      calc _ ≤ 2 * 1 := by gcongr; exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
        _ ≤ K1 := by linarith
  -- D5.19.2 outer lines: `|F| ≤ K₁` on `|Re z| ≤ b`
  have hFstrip : ∀ z : ℂ, |z.re| ≤ b → ‖F z‖ ≤ K1 := fun z hz ↦ by
    have hz2 : z.re ^ 2 - z.im ^ 2 ≤ 1 := by
      have : z.re ^ 2 ≤ b ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
      nlinarith [sq_nonneg z.im]
    have hE2 : Real.exp 1 * Real.exp 1 ≤ Real.exp (π ^ 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [Real.two_le_pi])
    have hE1 : Real.exp 1 ≤ Real.exp (π ^ 2) := Real.exp_le_exp.2 (by nlinarith [Real.two_le_pi])
    calc ‖F z‖ = ‖f z - p‖ * Real.exp (z.re ^ 2 - z.im ^ 2) := by
          simp only [F, norm_mul, hnormexp]
      _ ≤ (Real.exp 1 + 1) * Real.exp 1 := by
          gcongr; exact hfp z (hnarrow z hz)
      _ ≤ K1 := by nlinarith
  -- D5.19.3 three lines on `0 ≤ Re z ≤ b`: `|F| ≤ K₁ m^{1/2}` on `0 ≤ Re z ≤ b/2`
  have hthree : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ b / 2 → ‖F z‖ ≤ K1 * √m := fun z hz0 hz1 ↦ by
    have h3 := three_lines hF hb0 hFim (fun w h0 h1 ↦ hFstrip w (by rwa [abs_of_nonneg h0]))
      hz0 (by linarith)
    have hs1 : z.re / b ≤ 1 / 2 := by rw [div_le_iff₀ hb0]; linarith
    rw [Real.mul_rpow hK10.le hm0, mul_comm (K1 ^ _), mul_assoc, ← Real.rpow_add hK10,
      sub_add_cancel, Real.rpow_one, mul_comm] at h3
    rw [Real.sqrt_eq_rpow]
    exact h3.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' hm0 hm1
      (by norm_num) (by linarith)) hK10.le)
  have hthree' : ∀ z : ℂ, |z.re| ≤ b / 2 → ‖F z‖ ≤ K1 * √m := fun z hz ↦ by
    rcases le_total 0 z.re with h0 | h0
    · exact hthree z h0 ((le_abs_self _).trans hz)
    · have h := hthree (-conj z) (by simp; linarith) (by simp; linarith [neg_abs_le z.re])
      have hFsymm : F (-conj z) = conj (F z) := by
        simp only [F, map_mul, map_sub, conj_ofReal, hsymm, ← Complex.exp_conj, map_pow, neg_sq]
      rwa [hFsymm, norm_conj] at h
  -- D5.19.4 Cauchy on `|z| ≤ b/2` for `g = f - p = F e^{-z²}`
  set M := Real.exp 1 * (K1 * √m)
  have hdisk : ∀ z ∈ closedBall (0 : ℂ) (b / 2), ‖f z - p‖ ≤ M := fun z hz ↦ by
    have hzn : ‖z‖ ≤ b / 2 := by simpa using hz
    have heq : f z - p = F z * Complex.exp (-(z ^ 2)) := by
      simp only [F, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    have hexp : Real.exp (-(z ^ 2)).re ≤ Real.exp 1 := Real.exp_le_exp.2 <| by
      have := abs_re_le_norm (z ^ 2); rw [norm_pow] at this
      have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      simp only [neg_re]; linarith [neg_abs_le (z ^ 2).re]
    rw [heq, norm_mul, Complex.norm_exp, mul_comm, show M = Real.exp 1 * (K1 * √m) from rfl]
    exact mul_le_mul hexp (hthree' z ((abs_re_le_norm z).trans hzn)) (norm_nonneg _)
      (Real.exp_pos _).le
  set t := a / 2
  obtain ⟨hReD, hD⟩ := step_5_18 hf hf0 (fun u ↦ (hax u).1) hphase
  set D := deriv f 0
  have htn : ‖(t : ℂ)‖ ≤ b / 2 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : a * L ≤ 1 / 32 := by linarith
    simp only [t, b]; rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
  have htaylor := norm_sub_sub_deriv_le (g := fun z ↦ f z - p) (hf.sub_const _)
    (by positivity) hdisk htn
  simp only [deriv_sub_const, hf0, sub_self, sub_zero] at htaylor
  set Rm := f t - p - t * D
  -- `|p + i t b₁| − p ≤ t² b₁² / (2p) ≤ 2π² K² t² R²`
  have hlin : ‖(p : ℂ) + t * D‖ - p ≤ 2 * π ^ 2 * K ^ 2 * t ^ 2 * R ^ 2 := by
    have hsq : ‖(p : ℂ) + t * D‖ ^ 2 = p ^ 2 + t ^ 2 * ‖D‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
      simp [hReD]; ring
    have hD2 : t ^ 2 * ‖D‖ ^ 2 ≤ t ^ 2 * (4 * π ^ 2 * K ^ 2 * p * R ^ 2) := by
      gcongr
      calc ‖D‖ ^ 2 ≤ (2 * π * K * √p * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
        _ = _ := by rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hp0]; ring
    have : ‖(p : ℂ) + t * D‖ ≤ p + 2 * π ^ 2 * K ^ 2 * t ^ 2 * R ^ 2 := by
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hsq]
      nlinarith [sq_nonneg (2 * π ^ 2 * K ^ 2 * t ^ 2 * R ^ 2), sq_nonneg t, sq_nonneg R,
        sq_nonneg K]
    linarith
  have hRm : 2 * ‖Rm‖ ≤ 384 * Real.exp 1 * K1 * a ^ 2 * (L ^ 2 * √m) := by
    have hb2 : (b / 2) ^ 2 = 1 / (256 * L ^ 2) := by simp only [b]; field_simp; ring
    rw [norm_real, Real.norm_eq_abs, sq_abs, hb2] at htaylor
    calc 2 * ‖Rm‖ ≤ 2 * (3 * M * t ^ 2 / (1 / (256 * L ^ 2))) := by gcongr
      _ = _ := by simp only [M, t]; field_simp; ring
  have hft : f t = p + t * D + Rm := by simp only [Rm]; ring
  have hRe : (f t).re = p + Rm.re := by rw [hft]; simp [hReD]
  have hnorm : ‖f t‖ ≤ ‖(p : ℂ) + t * D‖ + ‖Rm‖ := by rw [hft]; exact norm_add_le _ _
  have h4 : 0 ≤ a ^ 2 * (L ^ 2 * √m) := by positivity
  have h5 : 0 ≤ a ^ 2 * R ^ 2 := by positivity
  calc ‖f t‖ - (f t).re ≤ (‖(p : ℂ) + t * D‖ - p) + 2 * ‖Rm‖ := by
        rw [hRe]; linarith [neg_abs_le Rm.re, abs_re_le_norm Rm]
    _ ≤ 2 * π ^ 2 * K ^ 2 * t ^ 2 * R ^ 2 + 384 * Real.exp 1 * K1 * a ^ 2 * (L ^ 2 * √m) :=
        add_le_add hlin hRm
    _ ≤ _ := by
        have hC1 : (0 : ℝ) ≤ 384 * Real.exp 1 * K1 := by positivity
        have hC2 : (0 : ℝ) ≤ π ^ 2 * K ^ 2 := by positivity
        simp only [t]
        nlinarith [mul_nonneg hC1 h5, mul_nonneg hC2 h4, mul_nonneg hC2 h5]

end AreaLaw
