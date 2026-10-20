import Mathlib
import AreaLawRefactored.S05_Conditional.Defs

/-!
# §5.2 Resolvent compression (D5.13, D5.14)

The abstract part of Lemma 5.2 (digest D5.13.1–2, D5.14.3–5), over finite-dimensional complex
inner product spaces `E = H_f`, `F = H_s`. The positive operators are given with an orthonormal
eigenbasis (`ResolventCompression`); every spectral function of them (resolvent, inverse,
logarithm) is the diagonal operator `Conditional.spec` in that basis.

For the instantiation of D5.12 (`A = L_{σ_f} R_{ρ_f⁻¹}`, `B = L_{σ_s} R_{ρ_s⁻¹}` on
Hilbert–Schmidt spaces) the eigenbasis of `A` is `u_i w_jᴴ` (`u`, `w` eigenbases of `σ_f`, `ρ_f`)
with eigenvalue `s_i / p_j`; `compress` is D5.12.3 and `V.norm_map` is D5.12.2.
-/

namespace AreaLaw

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace Conditional

section Spec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
  (e : OrthonormalBasis ι ℂ E)

/-- The operator `x ↦ ∑ᵢ fᵢ ⟪eᵢ, x⟫ eᵢ`, diagonal in the orthonormal basis `e`. -/
noncomputable def spec (f : ι → ℂ) (x : E) : E := ∑ i, (f i * ⟪e i, x⟫_ℂ) • e i

theorem inner_spec (f : ι → ℂ) (x : E) (j : ι) : ⟪e j, spec e f x⟫_ℂ = f j * ⟪e j, x⟫_ℂ :=
  e.orthonormal.inner_right_fintype _ j

theorem spec_spec (f g : ι → ℂ) (x : E) : spec e f (spec e g x) = spec e (f * g) x :=
  Finset.sum_congr rfl fun i _ ↦ by rw [inner_spec, Pi.mul_apply, mul_assoc]

theorem spec_one (x : E) : spec e 1 x = x := by simp [spec, e.sum_repr']

theorem inner_spec_self (f : ι → ℝ) (x : E) :
    ⟪x, spec e (fun i ↦ f i) x⟫_ℂ = ((∑ i, f i * ‖⟪e i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  simp only [spec, inner_sum, inner_smul_right]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc, ← inner_conj_symm x (e i), RCLike.mul_conj]
  rfl

theorem inner_spec_left (f : ι → ℝ) (x y : E) :
    ⟪spec e (fun i ↦ f i) x, y⟫_ℂ = ⟪x, spec e (fun i ↦ f i) y⟫_ℂ := by
  simp only [spec, sum_inner, inner_sum, inner_smul_left, inner_smul_right, map_mul,
    Complex.conj_ofReal, inner_conj_symm]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

end Spec

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] (ι κ : Type*) [Fintype ι] [Fintype κ]

/-- D5.12.1–4 data. Strictly positive `A` on `E`, `B` on `F`, with orthonormal eigenbases; an
isometry `V : F → E` with `V* A V = B`; a vector `b₀ ∈ F`. -/
structure ResolventCompression where
  /-- `A`. -/
  A : E →ₗ[ℂ] E
  /-- `B`. -/
  B : F →ₗ[ℂ] F
  /-- An orthonormal eigenbasis of `A`. -/
  eA : OrthonormalBasis ι ℂ E
  /-- An orthonormal eigenbasis of `B`. -/
  eB : OrthonormalBasis κ ℂ F
  /-- The eigenvalues of `A`. -/
  lam : ι → ℝ
  /-- The eigenvalues of `B`. -/
  mu : κ → ℝ
  lam_pos : ∀ i, 0 < lam i
  mu_pos : ∀ j, 0 < mu j
  apply_eA : ∀ i, A (eA i) = (lam i : ℂ) • eA i
  apply_eB : ∀ j, B (eB j) = (mu j : ℂ) • eB j
  /-- The isometry `V`. -/
  V : F →ₗᵢ[ℂ] E
  /-- `V* A V = B`. -/
  compress : ∀ x y, ⟪V x, A (V y)⟫_ℂ = ⟪x, B y⟫_ℂ
  /-- `b₀`. -/
  b₀ : F

namespace ResolventCompression

variable {E F ι κ} (R : ResolventCompression E F ι κ)

/-- `a₀ = V b₀`. -/
noncomputable def a₀ : E := R.V R.b₀

/-- The resolvent `(A + v)⁻¹`. -/
noncomputable def resA (v : ℝ) : E → E := spec R.eA fun i ↦ ((R.lam i + v)⁻¹ : ℝ)

/-- The resolvent `(B + v)⁻¹`. -/
noncomputable def resB (v : ℝ) : F → F := spec R.eB fun j ↦ ((R.mu j + v)⁻¹ : ℝ)

/-- `A⁻¹`. -/
noncomputable def invA : E → E := spec R.eA fun i ↦ ((R.lam i)⁻¹ : ℝ)

/-- `log A`. -/
noncomputable def logA : E → E := spec R.eA fun i ↦ (Real.log (R.lam i) : ℝ)

/-- `log B`. -/
noncomputable def logB : F → F := spec R.eB fun j ↦ (Real.log (R.mu j) : ℝ)

/-- `δ_v = (A + v)⁻¹ a₀ - V (B + v)⁻¹ b₀`. -/
noncomputable def δ (v : ℝ) : E := R.resA v R.a₀ - R.V (R.resB v R.b₀)

/-- `h(v) = ⟨a₀, (A + v)⁻¹ a₀⟩ - ⟨b₀, (B + v)⁻¹ b₀⟩`, in the eigenbases. -/
noncomputable def h (v : ℝ) : ℝ :=
  ∑ i, (R.lam i + v)⁻¹ * ‖⟪R.eA i, R.a₀⟫_ℂ‖ ^ 2 - ∑ j, (R.mu j + v)⁻¹ * ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2

theorem A_eq (x : E) : R.A x = spec R.eA (fun i ↦ (R.lam i : ℝ)) x := by
  conv_lhs => rw [← R.eA.sum_repr' x]
  simp only [spec, map_sum, map_smul, R.apply_eA, smul_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem B_eq (y : F) : R.B y = spec R.eB (fun j ↦ (R.mu j : ℝ)) y := by
  conv_lhs => rw [← R.eB.sum_repr' y]
  simp only [spec, map_sum, map_smul, R.apply_eB, smul_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem inner_A_left (x y : E) : ⟪R.A x, y⟫_ℂ = ⟪x, R.A y⟫_ℂ := by
  rw [R.A_eq, R.A_eq, inner_spec_left]

/-- `(A + v) y = spec (λ + v) y`. -/
theorem A_add_smul (v : ℝ) (y : E) :
    R.A y + (v : ℂ) • y = spec R.eA (fun i ↦ (R.lam i + v : ℝ)) y := by
  rw [R.A_eq]
  nth_rw 2 [← spec_one R.eA y]
  simp only [spec, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by congr 1; simp only [Pi.one_apply]; push_cast; ring

theorem B_add_smul (v : ℝ) (y : F) :
    R.B y + (v : ℂ) • y = spec R.eB (fun j ↦ (R.mu j + v : ℝ)) y := by
  rw [R.B_eq]
  nth_rw 2 [← spec_one R.eB y]
  simp only [spec, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by congr 1; simp only [Pi.one_apply]; push_cast; ring

theorem A_add_resA {v : ℝ} (hv : 0 ≤ v) (x : E) : R.A (R.resA v x) + (v : ℂ) • R.resA v x = x := by
  rw [A_add_smul, resA, spec_spec]
  convert spec_one R.eA x using 2
  funext i
  have : (R.lam i + v : ℂ) ≠ 0 := by exact_mod_cast (add_pos_of_pos_of_nonneg (R.lam_pos i) hv).ne'
  simp [this]

theorem B_add_resB {v : ℝ} (hv : 0 ≤ v) (y : F) : R.B (R.resB v y) + (v : ℂ) • R.resB v y = y := by
  rw [B_add_smul, resB, spec_spec]
  convert spec_one R.eB y using 2
  funext j
  have : (R.mu j + v : ℂ) ≠ 0 := by exact_mod_cast (add_pos_of_pos_of_nonneg (R.mu_pos j) hv).ne'
  simp [this]

theorem A_invA (x : E) : R.A (R.invA x) = x := by
  rw [A_eq, invA, spec_spec]
  convert spec_one R.eA x using 2
  funext i
  simp [(R.lam_pos i).ne']

theorem norm_a₀ : ‖R.a₀‖ = ‖R.b₀‖ := R.V.norm_map _

/-- `⟪x, (A + v) x⟫ = ∑ (λᵢ + v) ‖⟪eᵢ, x⟫‖²`. -/
theorem inner_A_add_smul (v : ℝ) (x : E) :
    ⟪x, R.A x + (v : ℂ) • x⟫_ℂ = ((∑ i, (R.lam i + v) * ‖⟪R.eA i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [A_add_smul, inner_spec_self]

theorem h_eq (v : ℝ) :
    (R.h v : ℂ) = ⟪R.a₀, R.resA v R.a₀⟫_ℂ - ⟪R.b₀, R.resB v R.b₀⟫_ℂ := by
  rw [resA, resB, inner_spec_self, inner_spec_self, h]
  push_cast; rfl

end ResolventCompression

end Conditional

open Conditional ResolventCompression

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] {ι κ : Type*} [Fintype ι] [Fintype κ]
  (R : ResolventCompression E F ι κ)

/-- The scalar log formula `∫_{(0,∞)} ((l + v)⁻¹ - (1 + v)⁻¹) dv = -log l`, `l > 0`. -/
theorem Conditional.integral_inv_add_sub_inv_one_add {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun v : ℝ ↦ (l + v)⁻¹ - (1 + v)⁻¹) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), ((l + v)⁻¹ - (1 + v)⁻¹) = -Real.log l := by
  set G : ℝ → ℝ := fun v ↦ Real.log (l + v) - Real.log (1 + v)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt G ((l + x)⁻¹ - (1 + x)⁻¹) x := fun x hx ↦ by
    have hx : (0 : ℝ) < x := hx
    convert! (((hasDerivAt_id x).const_add l).log (by simp; linarith)).sub
      (((hasDerivAt_id x).const_add 1).log (by simp; linarith)) using 1; simp [one_div]
  have hcont : ContinuousWithinAt G (Ici 0) 0 :=
    (((continuousAt_const.add continuousAt_id).log (by simp; linarith)).sub
      ((continuousAt_const.add continuousAt_id).log (by simp))).continuousWithinAt
  have hlim : Filter.Tendsto G Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun v : ℝ ↦ (l + v) / (1 + v)) Filter.atTop (nhds 1) := by
      have h' := ((tendsto_const_nhds (x := l - 1)).div_atTop
        (Filter.tendsto_atTop_add_const_left Filter.atTop 1 Filter.tendsto_id)).const_add 1
      rw [add_zero] at h'
      refine h'.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with v hv
      simp only [id]
      field_simp
      ring
    have h' := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    rw [Real.log_one] at h'
    refine h'.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with v hv
    simp only [Function.comp, G, Real.log_div (by linarith : l + v ≠ 0) (by linarith : 1 + v ≠ 0)]
  have hint : IntegrableOn (fun v : ℝ ↦ (l + v)⁻¹ - (1 + v)⁻¹) (Ioi 0) := by
    rcases le_total l 1 with h | h
    · exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun x (hx : 0 < x) ↦
        sub_nonneg.2 (inv_anti₀ (by linarith) (by linarith))) hlim
    · exact integrableOn_Ioi_deriv_of_nonpos hcont hderiv (fun x (hx : 0 < x) ↦
        sub_nonpos.2 (inv_anti₀ (by linarith) (by linarith))) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [G]

/-- D5.13. `‖(A+v)^{1/2} δ_v‖² = ⟨a₀,(A+v)⁻¹a₀⟩ - ⟨b₀,(B+v)⁻¹b₀⟩ =: h(v) ≥ 0`, and
`∫_0^∞ h = -⟨a₀, log A a₀⟩ + ⟨b₀, log B b₀⟩`. -/
theorem step_5_13 :
    (∀ v : ℝ, 0 ≤ v → ⟪R.δ v, R.A (R.δ v) + (v : ℂ) • R.δ v⟫_ℂ = R.h v ∧ 0 ≤ R.h v) ∧
      IntegrableOn R.h (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), R.h v = -(⟪R.a₀, R.logA R.a₀⟫_ℂ).re + (⟪R.b₀, R.logB R.b₀⟫_ℂ).re := by
  refine ⟨fun v hv ↦ ?_, ?_⟩
  · -- D5.13.1
    set g := R.resA v R.a₀
    set k := R.resB v R.b₀
    have hg : R.A g + (v : ℂ) • g = R.a₀ := R.A_add_resA hv _
    have hVk : ⟪R.V k, R.A (R.V k) + (v : ℂ) • R.V k⟫_ℂ = ⟪k, R.b₀⟫_ℂ := by
      rw [inner_add_right, R.compress, inner_smul_right, R.V.inner_map_map, ← inner_smul_right,
        ← inner_add_right, R.B_add_resB hv]
    have hgVk : ⟪g, R.A (R.V k) + (v : ℂ) • R.V k⟫_ℂ = ⟪R.b₀, k⟫_ℂ := by
      rw [inner_add_right, ← R.inner_A_left, inner_smul_right, ← Complex.conj_ofReal,
        ← inner_smul_left, ← inner_add_left, hg, a₀, R.V.inner_map_map]
    have hVka : ⟪R.V k, R.a₀⟫_ℂ = ⟪k, R.b₀⟫_ℂ := R.V.inner_map_map _ _
    have hga : ⟪g, R.a₀⟫_ℂ = ⟪R.a₀, g⟫_ℂ := by
      rw [← inner_conj_symm]
      simp only [g, resA, inner_spec_self, Complex.conj_ofReal]
    have hq : ⟪δ R v, R.A (δ R v) + (v : ℂ) • δ R v⟫_ℂ = R.h v := by
      rw [δ, map_sub, smul_sub, sub_add_sub_comm, hg, inner_sub_left, inner_sub_right,
        inner_sub_right, hVk, hgVk, hVka, hga, R.h_eq]
      ring
    refine ⟨hq, ?_⟩
    rw [Complex.ofReal_inj.1 (hq.symm.trans (R.inner_A_add_smul v _))]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (by linarith [R.lam_pos i]) (sq_nonneg _)
  · -- D5.13.2
    have hsum : ∑ i, ‖⟪R.eA i, R.a₀⟫_ℂ‖ ^ 2 = ∑ j, ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 := by
      rw [R.eA.sum_sq_norm_inner_right, R.eB.sum_sq_norm_inner_right, R.norm_a₀]
    have hfun : R.h = fun v ↦ ∑ i, ‖⟪R.eA i, R.a₀⟫_ℂ‖ ^ 2 * ((R.lam i + v)⁻¹ - (1 + v)⁻¹) -
        ∑ j, ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 * ((R.mu j + v)⁻¹ - (1 + v)⁻¹) := by
      funext v
      simp only [h, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
      simp only [mul_comm]
      ring
    have hA := fun i ↦ integral_inv_add_sub_inv_one_add (R.lam_pos i)
    have hB := fun j ↦ integral_inv_add_sub_inv_one_add (R.mu_pos j)
    have hiA := integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) Finset.univ
      fun i _ ↦ ((hA i).1.const_mul (‖⟪R.eA i, R.a₀⟫_ℂ‖ ^ 2))
    have hiB := integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) Finset.univ
      fun j _ ↦ ((hB j).1.const_mul (‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2))
    refine ⟨hfun ▸ hiA.sub hiB, ?_⟩
    rw [hfun, integral_sub hiA hiB, integral_finsetSum _ fun i _ ↦ (hA i).1.const_mul _,
      integral_finsetSum _ fun j _ ↦ (hB j).1.const_mul _, logA, logB, inner_spec_self,
      inner_spec_self, Complex.ofReal_re, Complex.ofReal_re]
    simp only [integral_const_mul, (hA _).2, (hB _).2]
    have e1 : ∀ w l : ℝ, w * -l = -(l * w) := fun _ _ ↦ by ring
    simp only [e1, Finset.sum_neg_distrib]
    ring

/-- D5.14 (abstract part). For `v > 0`: `0 ≤ h(v) ≤ ⟨a₀, A⁻¹ a₀⟩`, `h(v) ≤ ⟨b₀, B b₀⟩ / v²`, and
`v ‖δ_v‖² ≤ h(v)`. -/
theorem step_5_14 {v : ℝ} (hv : 0 < v) :
    0 ≤ R.h v ∧ R.h v ≤ (⟪R.a₀, R.invA R.a₀⟫_ℂ).re ∧ R.h v ≤ (⟪R.b₀, R.B R.b₀⟫_ℂ).re / v ^ 2 ∧
      v * ‖R.δ v‖ ^ 2 ≤ R.h v := by
  have wA := fun i ↦ sq_nonneg ‖⟪R.eA i, R.a₀⟫_ℂ‖
  have wB := fun j ↦ sq_nonneg ‖⟪R.eB j, R.b₀⟫_ℂ‖
  have hB0 : 0 ≤ ∑ j, (R.mu j + v)⁻¹ * ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (inv_nonneg.2 (by linarith [R.mu_pos j])) (wB j)
  refine ⟨((step_5_13 R).1 v hv.le).2, ?_, ?_, ?_⟩
  · -- D5.14.3
    rw [invA, inner_spec_self, Complex.ofReal_re, h]
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ mul_le_mul_of_nonneg_right
      (inv_anti₀ (R.lam_pos i) (by linarith : R.lam i ≤ R.lam i + v)) (wA i)
    linarith
  · -- D5.14.4
    rw [B_eq, inner_spec_self, Complex.ofReal_re, h, Finset.sum_div]
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ mul_le_mul_of_nonneg_right
      (inv_anti₀ hv (by linarith [R.lam_pos i] : v ≤ R.lam i + v)) (wA i)
    have h2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦
      (show (v⁻¹ - R.mu j / v ^ 2) * ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 ≤
          (R.mu j + v)⁻¹ * ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 from by
        refine mul_le_mul_of_nonneg_right ?_ (wB j)
        have hμ := R.mu_pos j
        rw [show v⁻¹ - R.mu j / v ^ 2 = (v - R.mu j) / v ^ 2 by field_simp,
          div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by linarith)]
        nlinarith [sq_nonneg (R.mu j)])
    have hsum : ∑ i, ‖⟪R.eA i, R.a₀⟫_ℂ‖ ^ 2 = ∑ j, ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 := by
      rw [R.eA.sum_sq_norm_inner_right, R.eB.sum_sq_norm_inner_right, R.norm_a₀]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1 h2
    have : ∑ j, R.mu j / v ^ 2 * ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 =
        ∑ j, R.mu j * ‖⟪R.eB j, R.b₀⟫_ℂ‖ ^ 2 / v ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum] at h1
    linarith
  · -- D5.14.5
    have hq := ((step_5_13 R).1 v hv.le).1.symm.trans (R.inner_A_add_smul v _)
    rw [Complex.ofReal_inj] at hq
    rw [hq, ← R.eA.sum_sq_norm_inner_right, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (by linarith [R.lam_pos i]) (sq_nonneg _)

end AreaLaw
