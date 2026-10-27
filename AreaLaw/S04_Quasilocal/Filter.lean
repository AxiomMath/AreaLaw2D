import AreaLawForMathlib.Analysis.Fourier.GevreyBumpFourier
import AreaLaw.S04_Quasilocal.Setup

/-!
# §4.1 The compactly supported spectral filter (Lemma 4.2)

Digest `digest/04-quasilocal.md` (D4.5), paper `paper/sections/03-quasilocal.tex`
lines 135–201. No geometry (`Map.md`, Dimension: any d). The analysis is
`AreaLawForMathlib/Analysis/Fourier/GevreyBump.lean` (D4.5.1–6) and
`AreaLawForMathlib/Analysis/Fourier/GevreyBumpFourier.lean` (D4.5.7–9).
-/

namespace AreaLaw

open MeasureTheory Real
open Complex (I)
open scoped Complex

/-- D4.5. The cutoff `χ(ω) = e exp[-(1-(ω/δ)²)^{-p}]` for `|ω| < δ`, `0` for `|ω| ≥ δ`. -/
noncomputable def χ (p : ℕ) (δ ω : ℝ) : ℝ :=
  if |ω| < δ then exp 1 * exp (-((1 - (ω / δ) ^ 2) ^ p)⁻¹) else 0

/-- D4.5. The filter `f(t) = (2π)⁻¹ ∫ χ(ω) e^{-itω} dω`, written as the real integral
`(2π)⁻¹ ∫ χ(ω) cos(tω) dω` (`χ` is even); `lemma_4_2` proves the two agree. -/
noncomputable def f (p : ℕ) (δ t : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ ω, χ p δ ω * cos (t * ω)

theorem χ_eq_bump (p : ℕ) (δ : ℝ) : χ p δ = GevreyBump.bump p δ := rfl

theorem f_eq_kernel (p : ℕ) (δ : ℝ) : f p δ = GevreyBump.kernel p δ := rfl

/-- D4.5 (Lemma 4.2). Fix integer $p\ge1$, $\alpha=p/(p+1)$, $\delta>0$. Define the real even
function
$$\chi(\omega)=\begin{cases}e\exp[-(1-(\omega/\delta)^2)^{-p}],&|\omega|<\delta,\\
0,&|\omega|\ge\delta.\end{cases}$$
Then $\chi\in C_c^\infty(\mathbb R)$, $\chi(0)=1$, and
$f(t)=\frac1{2\pi}\int\chi(\omega)e^{-it\omega}d\omega$ is real, even, with
$$\chi(\omega)=\int_{\mathbb R}f(t)e^{it\omega}dt,\qquad|f(t)|\le Ce^{-c|t|^\alpha},$$
$C,c>0$ depending only on $p,\delta$. In particular $f\in L^1$ and $\int f=\chi(0)=1$. -/
theorem lemma_4_2 (p : ℕ) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (χ p δ) ∧ HasCompactSupport (χ p δ) ∧
      Function.support (χ p δ) ⊆ Set.Icc (-δ) δ ∧ χ p δ 0 = 1 ∧
      (∀ ω, χ p δ (-ω) = χ p δ ω) ∧
      (∀ t, (f p δ t : ℂ) = (2 * π : ℂ)⁻¹ * ∫ ω, (χ p δ ω : ℂ) * cexp (-(t * ω) * I)) ∧
      (∀ t, f p δ (-t) = f p δ t) ∧
      (∀ ω, (χ p δ ω : ℂ) = ∫ t, (f p δ t : ℂ) * cexp (t * ω * I)) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ t, |f p δ t| ≤ C * exp (-(c * |t| ^ ((p : ℝ) / (p + 1))))) ∧
      Integrable (f p δ) ∧ ∫ t, f p δ t = 1 := by
  rw [χ_eq_bump, f_eq_kernel]
  -- D4.5.2 (complex disk) is `GevreyBump.norm_profile_le`, D4.5.3 (Cauchy)
  -- `GevreyBump.norm_iteratedDeriv_profile_le_cauchy`, D4.5.5 (uniformity in `u`)
  -- `GevreyBump.norm_iteratedDeriv_profile_le`; they enter through D4.5.4 and D4.5.6.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- D4.5.4: all derivatives of the profile vanish at `±1`, the zero extension is smooth
    exact GevreyBump.contDiff_bump hp hδ
  · -- D4.5.1
    exact GevreyBump.hasCompactSupport_bump p δ
  · -- D4.5.1
    exact GevreyBump.support_bump_subset p δ
  · -- D4.5.1
    exact GevreyBump.bump_zero p hδ
  · -- D4.5.1
    exact GevreyBump.bump_neg p δ
  · -- D4.5.9 (reality: `f` is the real cosine integral, by evenness of `χ`)
    exact GevreyBump.kernel_eq_integral_exp hp hδ
  · -- D4.5.9 (evenness)
    exact GevreyBump.kernel_neg p δ
  · -- D4.5.9 (inversion; needs `f ∈ L¹` from D4.5.8)
    exact fun ω => (GevreyBump.integral_kernel_mul_exp hp hδ ω).symm
  · -- D4.5.8, from the moment bound D4.5.7 `GevreyBump.pow_abs_mul_abs_kernel_le` and
    -- the Gevrey bound D4.5.6 `GevreyBump.abs_iteratedDeriv_bump_le`
    exact GevreyBump.exists_abs_kernel_le_exp hp hδ
  · -- D4.5.8
    exact GevreyBump.integrable_kernel hp hδ
  · -- D4.5.9 at `ω = 0`, `χ(0) = 1`
    exact GevreyBump.integral_kernel hp hδ

end AreaLaw
