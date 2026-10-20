import AreaLawRefactored.S05_Conditional.Defs
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# §5 Lemma 5.1: the scalar and complex-analytic pieces

Digest `digest/05-conditional.md`, anchors D5.11 (log-interpolation on the strip), D5.5.10 (the
sum of the two boundary bounds), D5.7.3–4 (the concavity/affinity inequality behind the
Hellinger estimate), in scalar form.
-/

namespace AreaLaw

open Complex Set Complex.HadamardThreeLines
open scoped ComplexConjugate

namespace Conditional

/-- D5.11.2, scalar case, paired form: a bounded `f`, analytic in `0 < Re z < 1` and continuous
on the closed strip, with `|f(iu)| |f(1+iu)| ≤ exp(A + B u²)` for every real `u`, satisfies
`|f(1/2)| ≤ exp(A/2 + B/8)`. -/
theorem paired_three_lines (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hbdd : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (A B : ℝ) (hB : 0 ≤ B)
    (hpair : ∀ u : ℝ, ‖f (u * I)‖ * ‖f (1 + u * I)‖ ≤ Real.exp (A + B * u ^ 2)) :
    ‖f (1 / 2)‖ ≤ Real.exp (A / 2 + B / 8) := by
  -- reflection `z ↦ 1 - z̄` fixes the strip and pairs `iu` with `1 + iu`
  let r : ℂ → ℂ := fun z ↦ 1 - conj z
  have hr : Continuous r := continuous_const.sub continuous_conj
  have hrs : MapsTo r (verticalStrip 0 1) (verticalStrip 0 1) := fun z hz ↦ by
    simp only [verticalStrip, mem_preimage, mem_Ioo, r, sub_re, one_re, conj_re] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  have hrc : MapsTo r (verticalClosedStrip 0 1) (verticalClosedStrip 0 1) := fun z hz ↦ by
    simp only [verticalClosedStrip, mem_preimage, mem_Icc, r, sub_re, one_re, conj_re] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  let ref : ℂ → ℂ := fun z ↦ conj (f (r z))
  have href : DiffContOnCl ℂ ref (verticalStrip 0 1) := by
    refine ⟨fun z hz ↦ ?_, ?_⟩
    · have hopen : IsOpen (verticalStrip 0 1) := isOpen_Ioo.preimage continuous_re
      have h1 : DifferentiableAt ℂ f (conj (1 - z)) := by
        refine hf.differentiableAt hopen ?_
        simpa [r] using hrs hz
      have h2 := (differentiableAt_conj_conj_iff.mpr h1).comp z
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
      refine (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)
        ).differentiableWithinAt
      simp [ref, r, Function.comp_def]
    · exact continuous_conj.comp_continuousOn
        (hf.continuousOn.comp hr.continuousOn (hrs.closure hr))
  let damp : ℂ → ℂ := fun z ↦ exp (B * (z - 1 / 2) ^ 2)
  have hdn (z : ℂ) : ‖damp z‖ = Real.exp (B * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) := by
    simp only [damp, norm_exp]; congr 1; simp [sq]
  let g : ℂ → ℂ := fun z ↦ f z * ref z * damp z
  have hg : DiffContOnCl ℂ g (verticalStrip 0 1) :=
    (hf.smul href).smul (((differentiable_id.sub_const _).pow 2).const_mul _).cexp.diffContOnCl
  have hnorm (z : ℂ) : ‖g z‖ = ‖f z‖ * ‖f (r z)‖ * Real.exp (B * ((z.re - 1 / 2) ^ 2 - z.im ^ 2))
    := by simp only [g, ref, norm_mul, Complex.norm_conj, hdn]
  obtain ⟨K, hK⟩ := hbdd
  have hK' : ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ K := fun z hz ↦ hK ⟨z, hz, rfl⟩
  have hgb : BddAbove ((norm ∘ g) '' verticalClosedStrip 0 1) := by
    refine ⟨K * K * Real.exp (B / 4), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
    have hq : (z.re - 1 / 2) ^ 2 - z.im ^ 2 ≤ 1 / 4 := by
      nlinarith [mul_nonneg hz'.1 (sub_nonneg.mpr hz'.2), sq_nonneg z.im]
    have he : Real.exp (B * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) ≤ Real.exp (B / 4) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hq hB])
    have h1 := hK' z hz
    have h2 := hK' _ (hrc hz)
    have hK0 : 0 ≤ K := h1.trans' (norm_nonneg _)
    rw [Function.comp_apply, hnorm]
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hK0) he (Real.exp_pos _).le
      (mul_nonneg hK0 hK0)
  -- on both boundary lines `‖g‖ ≤ exp (A + B/4)`
  have hbd (u : ℝ) (x : ℝ) (hx : x = 0 ∨ x = 1) :
      ‖g (x + u * I)‖ ≤ Real.exp (A + B / 4) := by
    rw [hnorm]
    have hre : ((x : ℂ) + u * I).re = x := by simp
    have him : ((x : ℂ) + u * I).im = u := by simp
    have hp : ‖f (x + u * I)‖ * ‖f (r (x + u * I))‖ ≤ Real.exp (A + B * u ^ 2) := by
      rcases hx with rfl | rfl
      · have : r (((0 : ℝ) : ℂ) + u * I) = 1 + u * I := by apply Complex.ext <;> simp [r]
        rw [this]; simpa using hpair u
      · have : r (((1 : ℝ) : ℂ) + u * I) = u * I := by apply Complex.ext <;> simp [r]
        rw [this, mul_comm]; simpa using hpair u
    calc _ ≤ Real.exp (A + B * u ^ 2) * Real.exp (B * ((x - 1 / 2) ^ 2 - u ^ 2)) := by
          rw [hre, him]; gcongr
      _ = Real.exp (A + B / 4) := by
          rw [← Real.exp_add]; congr 1; rcases hx with rfl | rfl <;> ring
  have ha := norm_le_interp_of_mem_verticalClosedStrip₀₁' g (z := 1 / 2)
    (by constructor <;> norm_num) hg hgb
    (fun z hz ↦ by
      have h := hbd z.im 0 (Or.inl rfl)
      rwa [show ((0 : ℝ) : ℂ) + z.im * I = z from
        Complex.ext (by simpa using hz.symm) (by simp)] at h)
    (fun z hz ↦ by
      have h := hbd z.im 1 (Or.inr rfl)
      rwa [show ((1 : ℝ) : ℂ) + z.im * I = z from
        Complex.ext (by simpa using hz.symm) (by simp)] at h)
  have hc : ‖g (1 / 2)‖ = ‖f (1 / 2)‖ ^ 2 := by
    rw [hnorm, show r (1 / 2) = 1 / 2 by apply Complex.ext <;> norm_num [r]]; norm_num; ring
  rw [hc, ← Real.rpow_add (Real.exp_pos _)] at ha
  norm_num at ha
  have hs : Real.exp (A / 2 + B / 8) ^ 2 = Real.exp (A + B / 4) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  nlinarith [Real.exp_pos (A / 2 + B / 8), norm_nonneg (f (1 / 2))]

end Conditional

open Conditional

/-- D5.11. `G` vector-valued, analytic in `0 < Re z < 1`, bounded and continuous on the closed
strip. Then `log ‖G(1/2)‖ ≤ ∫ log ‖G(iu)‖ du/(2 cosh πu) + ∫ log ‖G(1+iu)‖ du/(2 cosh πu)`.

Formal route (paired Gaussian three-lines): if `‖G(iu)‖ ‖G(1+iu)‖ ≤ exp(A + B u²)` for every real
`u` (the same `u` on both lines, as D5.5.10 pairs them), then `‖G(1/2)‖ ≤ exp(A/2 + B/8)`. -/
theorem step_5_11 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (G : ℂ → E)
    (hG : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hbdd : BddAbove ((norm ∘ G) '' verticalClosedStrip 0 1)) (A B : ℝ) (hB : 0 ≤ B)
    (hpair : ∀ u : ℝ, ‖G (u * I)‖ * ‖G (1 + u * I)‖ ≤ Real.exp (A + B * u ^ 2)) :
    ‖G (1 / 2)‖ ≤ Real.exp (A / 2 + B / 8) := by
  -- D5.11.3: `φ = ⟨e, G⟩` with `‖e‖ ≤ 1`, `φ(1/2) = ‖G(1/2)‖`
  obtain ⟨e, he, heG⟩ := exists_dual_vector'' ℂ (G (1 / 2))
  have hn (z : ℂ) : ‖e (G z)‖ ≤ ‖G z‖ :=
    (e.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right he (norm_nonneg (G z)))
  -- D5.11.2: the scalar case
  have h := paired_three_lines (fun z ↦ e (G z)) (e.differentiable.comp_diffContOnCl hG)
    (let ⟨K, hK⟩ := hbdd; ⟨K, by rintro _ ⟨z, hz, rfl⟩; exact (hn z).trans (hK ⟨z, hz, rfl⟩)⟩)
    A B hB fun u ↦ (mul_le_mul (hn _) (hn _) (norm_nonneg _) (norm_nonneg _)).trans (hpair u)
  rwa [heG, norm_algebraMap', norm_norm] at h

/-- D5.5.10. Insert D5.5.4 and D5.5.8 at the same `u`: if for every real `u`
`‖G(iu)‖ ≤ exp(-a d_U + C₀ a² ℓ² - λ(u))` with `λ(u) ≥ 0` and
`‖G(1+iu)‖ ≤ exp(-a d_P + C a² ℓ² + C a ℓ (1+|u|)^{1/2} (λ(u)^{1/4} + a^{1/4} ℓ^{1/2}))`, then for
`0 < a ≤ 1`, `ℓ ≥ 1`: `‖G(1/2)‖ ≤ exp(-(a/2)(d_U + d_P) + C' a^{5/4} ℓ²)`,
`C' = C₀ + 3C + 2C^{4/3}`.

Formal route: the weights `du/(2 cosh πu)` are replaced by the Gaussian three-lines `step_5_11`,
so the `u`-growth `(1+|u|)^{2/3}`, `(1+|u|)^{1/2}` is bounded by `(3 + u²)/2` instead of
integrated. -/
theorem step_5_5_10 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (G : ℂ → E)
    (hG : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hbdd : BddAbove ((norm ∘ G) '' verticalClosedStrip 0 1)) {a ℓ dU dP C₀ C : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hℓ : 1 ≤ ℓ) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (lam : ℝ → ℝ)
    (hlam : ∀ u, 0 ≤ lam u)
    (hL : ∀ u : ℝ, ‖G (u * I)‖ ≤ Real.exp (-a * dU + C₀ * a ^ 2 * ℓ ^ 2 - lam u))
    (hR : ∀ u : ℝ, ‖G (1 + u * I)‖ ≤ Real.exp (-a * dP + C * a ^ 2 * ℓ ^ 2 +
      C * a * ℓ * (1 + |u|) ^ (1 / 2 : ℝ) *
        (lam u ^ (1 / 4 : ℝ) + a ^ (1 / 4 : ℝ) * ℓ ^ (1 / 2 : ℝ)))) :
    ‖G (1 / 2)‖ ≤
      Real.exp (-(a / 2) * (dU + dP) + (C₀ + 3 * C + 2 * C ^ (4 / 3 : ℝ)) * a ^ (5 / 4 : ℝ) * ℓ ^ 2)
    := by
  -- D5.5.10, Young: `-λ + Bλ^{1/4} ≤ B^{4/3}`
  have young (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : -x + y * x ^ (1 / 4 : ℝ) ≤ y ^ (4 / 3 : ℝ) := by
    have h := Real.young_inequality_of_nonneg (Real.rpow_nonneg hx (1 / 4)) hy
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (4 : ℝ).HolderConjugate (4 / 3))
    rw [← Real.rpow_mul hx] at h
    norm_num at h
    nlinarith [Real.rpow_nonneg hy (4 / 3)]
  have hℓ0 : 0 ≤ ℓ := by linarith
  set K := (C * a * ℓ) ^ (4 / 3 : ℝ) + C * a ^ (5 / 4 : ℝ) * ℓ ^ (3 / 2 : ℝ)
  have hK0 : 0 ≤ K := by positivity
  -- D5.5.10: insert D5.5.4 and D5.5.8 at the same `u`; the `u`-growth is `≤ K (3 + u²)/2`
  have hpair (u : ℝ) : ‖G (u * I)‖ * ‖G (1 + u * I)‖ ≤
      Real.exp ((-a * (dU + dP) + (C₀ + C) * a ^ 2 * ℓ ^ 2 + 3 / 2 * K) + K / 2 * u ^ 2) := by
    have h1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
    have hs : (1 + |u|) ^ (1 / 2 : ℝ) ≤ 1 + |u| := by
      simpa using Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hs' : (1 + |u|) ^ (2 / 3 : ℝ) ≤ 1 + |u| := by
      simpa using Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (2 / 3 : ℝ) ≤ 1)
    have hY : (C * a * ℓ * (1 + |u|) ^ (1 / 2 : ℝ)) ^ (4 / 3 : ℝ) =
        (C * a * ℓ) ^ (4 / 3 : ℝ) * (1 + |u|) ^ (2 / 3 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num
    have hY' := young (lam u) _ (hlam u) (by positivity : 0 ≤ C * a * ℓ * (1 + |u|) ^ (1 / 2 : ℝ))
    have h54 : a * a ^ (1 / 4 : ℝ) = a ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_one_add' ha.le (by norm_num)]; norm_num
    have h32 : ℓ * ℓ ^ (1 / 2 : ℝ) = ℓ ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hℓ0 (by norm_num)]; norm_num
    have hu : 1 + |u| ≤ 3 / 2 + u ^ 2 / 2 := by nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
    have hA := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ (C * a * ℓ) ^ (4 / 3 : ℝ))
    have hB := mul_le_mul_of_nonneg_left hs
      (by positivity : 0 ≤ C * a ^ (5 / 4 : ℝ) * ℓ ^ (3 / 2 : ℝ))
    have hKu := mul_le_mul_of_nonneg_left hu hK0
    calc _ ≤ Real.exp (-a * dU + C₀ * a ^ 2 * ℓ ^ 2 - lam u) * Real.exp (-a * dP +
          C * a ^ 2 * ℓ ^ 2 + C * a * ℓ * (1 + |u|) ^ (1 / 2 : ℝ) *
            (lam u ^ (1 / 4 : ℝ) + a ^ (1 / 4 : ℝ) * ℓ ^ (1 / 2 : ℝ))) :=
          mul_le_mul (hL u) (hR u) (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ _ := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          rw [hY] at hY'
          have e : C * a * ℓ * (1 + |u|) ^ (1 / 2 : ℝ) * (a ^ (1 / 4 : ℝ) * ℓ ^ (1 / 2 : ℝ)) =
              C * a ^ (5 / 4 : ℝ) * ℓ ^ (3 / 2 : ℝ) * (1 + |u|) ^ (1 / 2 : ℝ) := by
            rw [← h54, ← h32]; ring
          nlinarith [e]
  -- D5.5.9 (via `step_5_11`), then collect `a² ℓ², a^{4/3} ℓ^{4/3}, a^{5/4} ℓ^{3/2} ≤ a^{5/4} ℓ²`
  refine (step_5_11 G hG hbdd _ _ (by positivity) hpair).trans (Real.exp_le_exp.mpr ?_)
  have hX0 : 0 ≤ a ^ (5 / 4 : ℝ) * ℓ ^ 2 := by positivity
  have hℓ2 : ℓ ^ (2 : ℝ) = ℓ ^ 2 := by norm_cast
  have ha2 : a ^ 2 * ℓ ^ 2 ≤ a ^ (5 / 4 : ℝ) * ℓ ^ 2 := by
    gcongr
    simpa using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (5 / 4 : ℝ) ≤ 2)
  have hℓ' (t : ℝ) (ht : t ≤ 2) : ℓ ^ t ≤ ℓ ^ 2 := by
    rw [← hℓ2]; exact Real.rpow_le_rpow_of_exponent_le hℓ ht
  have hK : K ≤ (C ^ (4 / 3 : ℝ) + C) * (a ^ (5 / 4 : ℝ) * ℓ ^ 2) := by
    have h1 : (C * a * ℓ) ^ (4 / 3 : ℝ) ≤ C ^ (4 / 3 : ℝ) * (a ^ (5 / 4 : ℝ) * ℓ ^ 2) := by
      rw [Real.mul_rpow (by positivity) hℓ0, Real.mul_rpow hC ha.le, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul
        (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)) (hℓ' _ (by norm_num))
        (by positivity) (by positivity)) (by positivity)
    have h2 : C * a ^ (5 / 4 : ℝ) * ℓ ^ (3 / 2 : ℝ) ≤ C * (a ^ (5 / 4 : ℝ) * ℓ ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hℓ' _ (by norm_num)) (by positivity)) hC
    linarith
  nlinarith [mul_le_mul_of_nonneg_left ha2 hC₀, mul_le_mul_of_nonneg_left ha2 hC,
    mul_nonneg hC hX0, mul_nonneg hC₀ hX0, mul_nonneg (Real.rpow_nonneg hC (4 / 3)) hX0]

/-- D5.7.3–4, scalar core. Eigenbasis form of `Tr ρ^{[1-b]} ξ^{[b]} = ∑ w_{ij} p_i^{1-b} q_j^b`
(`w_{ij} = |⟨p_i, q_j⟩|² ≥ 0`, `∑ w p = ∑ w q = 1`): for `0 < b ≤ 1/2`,
`1 - ∑ w_{ij} √p_i √q_j ≤ (1 - ∑ w_{ij} p_i^{1-b} q_j^b) / (2b)`. -/
theorem step_5_7 {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → κ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hp1 : ∑ i, ∑ j, w i j * p i = 1) (hq1 : ∑ i, ∑ j, w i j * q j = 1) {b : ℝ} (hb : 0 < b)
    (hb2 : b ≤ 1 / 2) :
    1 - ∑ i, ∑ j, w i j * (√(p i) * √(q j)) ≤
      (1 - ∑ i, ∑ j, w i j * (p i ^ (1 - b) * q j ^ b)) / (2 * b) := by
  -- D5.7.3: concavity of `b ↦ x^{1-b} y^b` between `b` and `1/2`, termwise
  have hy (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      b * (√x - √y) ^ 2 ≤ (1 - b) * x + b * y - x ^ (1 - b) * y ^ b := by
    have ham := Real.geom_mean_le_arith_mean2_weighted (p₁ := x) (p₂ := √x * √y)
      (w₁ := 1 - 2 * b) (w₂ := 2 * b) (by linarith) (by linarith) hx (by positivity) (by ring)
    have he : x ^ (1 - 2 * b) * (√x * √y) ^ (2 * b) = x ^ (1 - b) * y ^ b := by
      rcases hx.eq_or_lt with rfl | hx'
      · simp [Real.zero_rpow (by linarith : 1 - b ≠ 0), Real.zero_rpow (by linarith : 2 * b ≠ 0)]
      rw [Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hx, ← Real.rpow_mul hy, ← mul_assoc, ← Real.rpow_add hx']
      ring_nf
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  -- D5.7.4: sum against `w` and divide by `2b`
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ Finset.sum_le_sum
    fun j (_ : j ∈ Finset.univ) ↦ mul_le_mul_of_nonneg_left (hy _ _ (hp i) (hq j)) (hw i j)
  have e1 (i : ι) (j : κ) : w i j * (b * (√(p i) - √(q j)) ^ 2) =
      b * (w i j * p i) + b * (w i j * q j) - 2 * b * (w i j * (√(p i) * √(q j))) := by
    rw [sub_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hq j)]; ring
  have e2 (i : ι) (j : κ) : w i j * ((1 - b) * p i + b * q j - p i ^ (1 - b) * q j ^ b) =
      (1 - b) * (w i j * p i) + b * (w i j * q j) - w i j * (p i ^ (1 - b) * q j ^ b) := by ring
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1,
    hq1] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

end AreaLaw
