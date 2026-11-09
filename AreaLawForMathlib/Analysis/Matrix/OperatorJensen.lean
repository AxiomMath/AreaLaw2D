import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Tools for operator Jensen inequalities

Extends `Mathlib.Analysis.Matrix.Order` and `Mathlib.LinearAlgebra.Matrix.PosDef`.

* `Matrix.PosSemidef.of_integral`: an entrywise integral of positive semidefinite matrices is
  positive semidefinite.
* `Matrix.PosSemidef.fromBlocks_smul_inv`: `[[a R, R], [R, a⁻¹ R]] ≥ 0` for `R ≥ 0`, `a > 0`.
* `Real.log_eq_integral_inv_sub_inv`: `log x = ∫_0^∞ ((1 + t)⁻¹ - (x + t)⁻¹) dt` for `x > 0`.
* `Matrix.PosDef.re_dotProduct_cfc_log_eq_integral`: the same formula for the quadratic form of
  `cfc log X`, `X > 0`, and `Matrix.PosDef.cfc_inv_one_add_sub_inv_add` identifies the integrand
  `cfc ((1 + t)⁻¹ - (· + t)⁻¹) X = (1 + t)⁻¹ - (X + t)⁻¹`.
-/

open MeasureTheory Set Filter
open scoped Matrix ComplexOrder MatrixOrder Topology

namespace Matrix

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

theorem dotProduct_mulVec_of_integral {M : α → Matrix n n 𝕜}
    (hM : ∀ i j, Integrable (fun a => M a i j) μ) (x : n → 𝕜) :
    star x ⬝ᵥ (of fun i j => ∫ a, M a i j ∂μ) *ᵥ x = ∫ a, star x ⬝ᵥ M a *ᵥ x ∂μ := by
  simp only [dotProduct, mulVec, of_apply]
  rw [integral_finsetSum _ fun i _ => ((integrable_finsetSum _ fun j _ =>
    (hM i j).mul_const _)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hM i j).mul_const _]
  simp only [integral_mul_const]

theorem trace_mul_of_integral {M : α → Matrix n n 𝕜}
    (hM : ∀ i j, Integrable (fun a => M a i j) μ) (A : Matrix n n 𝕜) :
    (A * of fun i j => ∫ a, M a i j ∂μ).trace = ∫ a, (A * M a).trace ∂μ := by
  have h : ∀ N : Matrix n n 𝕜, (A * N).trace = ∑ i, ∑ j, A i j * N j i := fun N => by
    simp [trace, mul_apply]
  simp_rw [h, of_apply]
  refine Eq.trans ?_ (integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hM j i).const_mul (A i j)).symm
  refine Finset.sum_congr rfl fun i _ => Eq.trans ?_
    (integral_finsetSum _ fun j _ => (hM j i).const_mul (A i j)).symm
  simp only [integral_const_mul]

omit [Fintype n] in
theorem isHermitian_of_integral {M : α → Matrix n n 𝕜} (h : ∀ a, (M a).IsHermitian) :
    (of fun i j => ∫ a, M a i j ∂μ).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, of_apply, RCLike.star_def, ← integral_conj]
  exact integral_congr_ae (Eventually.of_forall fun a => by
    simpa [RCLike.star_def] using (h a).apply i j)

omit [Fintype n] in
/-- An entrywise integral of positive semidefinite matrices is positive semidefinite. -/
theorem PosSemidef.of_integral [Finite n] {M : α → Matrix n n 𝕜}
    (hM : ∀ i j, Integrable (fun a => M a i j) μ) (h : ∀ a, (M a).PosSemidef) :
    (of fun i j => ∫ a, M a i j ∂μ).PosSemidef := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_of_integral fun a => (h a).1) fun x => ?_
  have hint : Integrable (fun a => star x ⬝ᵥ M a *ᵥ x) μ := by
    simp only [dotProduct, mulVec]
    exact integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      (hM i j).mul_const _).const_mul _
  rw [dotProduct_mulVec_of_integral hM, RCLike.nonneg_iff, ← integral_re hint,
    ← integral_im hint]
  have hx := fun a => RCLike.nonneg_iff.mp ((h a).dotProduct_mulVec_nonneg x)
  exact ⟨integral_nonneg fun a => (hx a).1, by simp [fun a => (hx a).2]⟩

omit [Fintype n] in
/-- `[[a R, R], [R, a⁻¹ R]] ≥ 0` for `R ≥ 0` and `a > 0`. -/
theorem PosSemidef.fromBlocks_smul_inv [Finite n] {R : Matrix n n 𝕜} (hR : R.PosSemidef)
    {a : ℝ} (ha : 0 < a) :
    (fromBlocks ((a : 𝕜) • R) R R ((a : 𝕜)⁻¹ • R)).PosSemidef := by
  classical
  have := Fintype.ofFinite n
  obtain ⟨X, hX, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hR.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hR.nonneg)
  set s : 𝕜 := ((√a : ℝ) : 𝕜)
  have hs : star s = s := RCLike.conj_ofReal _
  have hs0 : s ≠ 0 := RCLike.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr ha)
  have hss : s * s = a := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt ha.le]
  have hX' : Xᴴ = X := hX.star_eq
  have h := posSemidef_conjTranspose_mul_self (fromCols (s • X) (s⁻¹ • X))
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols] at h
  simp only [conjTranspose_smul, star_inv₀, hs, hX', smul_mul_smul_comm, hss,
    mul_inv_cancel₀ hs0, inv_mul_cancel₀ hs0, one_smul, ← mul_inv, ] at h
  exact h

/-! ## The integral formula for the logarithm -/

private theorem hasDerivAt_log_one_add_sub_log_add {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    HasDerivAt (fun t => Real.log (1 + t) - Real.log (x + t)) ((1 + t)⁻¹ - (x + t)⁻¹) t := by
  have h1 : HasDerivAt (fun t => Real.log (1 + t)) (1 + t)⁻¹ t := by
    simpa using ((hasDerivAt_id t).const_add 1).log (by positivity)
  have h2 : HasDerivAt (fun t => Real.log (x + t)) (x + t)⁻¹ t := by
    simpa using ((hasDerivAt_id t).const_add x).log (by positivity)
  exact h1.sub h2

private theorem tendsto_log_one_add_sub_log_add {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => Real.log (1 + t) - Real.log (x + t)) atTop (𝓝 0) := by
  have hq : Tendsto (fun t : ℝ => 1 + (1 - x) / (x + t)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_id)).const_add (1 : ℝ)
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hq
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h2 : 0 < x + t := by linarith
  rw [Function.comp_apply, ← Real.log_div (by linarith) h2.ne']
  congr 1
  field_simp
  ring

theorem _root_.Real.integrableOn_inv_sub_inv {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (1 + t)⁻¹ - (x + t)⁻¹) (Ioi 0) := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t => Real.log (1 + t) - Real.log (x + t))
      ((1 + t)⁻¹ - (x + t)⁻¹) t := fun t ht => hasDerivAt_log_one_add_sub_log_add hx ht
  rcases le_total 1 x with h | h
  · refine integrableOn_Ioi_deriv_of_nonneg' hd (fun t (ht : 0 < t) => ?_)
      (tendsto_log_one_add_sub_log_add hx)
    exact sub_nonneg.mpr (inv_anti₀ (by linarith) (by linarith))
  · refine integrableOn_Ioi_deriv_of_nonpos (hd 0 self_mem_Ici).continuousAt.continuousWithinAt
      (fun t ht => hd t (Ioi_subset_Ici_self ht)) (fun t (ht : 0 < t) => ?_)
      (tendsto_log_one_add_sub_log_add hx)
    exact sub_nonpos.mpr (inv_anti₀ (by linarith) (by linarith))

/-- `log x = ∫_0^∞ ((1 + t)⁻¹ - (x + t)⁻¹) dt` for `x > 0`. -/
theorem _root_.Real.log_eq_integral_inv_sub_inv {x : ℝ} (hx : 0 < x) :
    Real.log x = ∫ t in Ioi 0, ((1 + t)⁻¹ - (x + t)⁻¹) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t ht => hasDerivAt_log_one_add_sub_log_add hx ht)
    (Real.integrableOn_inv_sub_inv hx) (tendsto_log_one_add_sub_log_add hx)]
  simp

/-- `x ↦ (1 + t)⁻¹ - (x + t)⁻¹` is monotone on `x > 0` and bounded on `[m, M]`. -/
theorem _root_.Real.abs_inv_sub_inv_le {t x m M : ℝ} (ht : 0 ≤ t) (hm : 0 < m) (hmx : m ≤ x)
    (hxM : x ≤ M) :
    |(1 + t)⁻¹ - (x + t)⁻¹| ≤ |(1 + t)⁻¹ - (m + t)⁻¹| + |(1 + t)⁻¹ - (M + t)⁻¹| := by
  have h1 : (x + t)⁻¹ ≤ (m + t)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have h2 : (M + t)⁻¹ ≤ (x + t)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  rw [abs_le]
  constructor <;> cases abs_cases ((1 + t)⁻¹ - (m + t)⁻¹) <;>
    cases abs_cases ((1 + t)⁻¹ - (M + t)⁻¹) <;> linarith

/-! ## Quadratic forms of the functional calculus -/

variable [DecidableEq n]

/-- `⟨v, g(X) v⟩ = ∑ᵢ g(xᵢ) |⟨eᵢ, v⟩|²` over the eigenbasis of a Hermitian `X`. -/
theorem IsHermitian.dotProduct_cfc_mulVec {X : Matrix n n 𝕜} (hX : X.IsHermitian) (g : ℝ → ℝ)
    (v : n → 𝕜) :
    star v ⬝ᵥ cfc g X *ᵥ v = ((∑ i, g (hX.eigenvalues i) *
      ‖(star (↑hX.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ v) i‖ ^ 2 : ℝ) : 𝕜) := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec,
    ← mulVec_mulVec, dotProduct_mulVec]
  have hc : star v ᵥ* (↑hX.eigenvectorUnitary : Matrix n n 𝕜) =
      star (star (↑hX.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ v) := by
    rw [star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [hc]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Pi.star_apply, RCLike.ofReal_sum,
    RCLike.ofReal_mul, RCLike.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← RCLike.conj_mul, RCLike.star_def]
  ring

/-- The quadratic form of `log X` is `∫_0^∞ ⟨v, ((1 + t)⁻¹ - (X + t)⁻¹) v⟩ dt` for `X > 0`
(the integrand written as `cfc`). -/
theorem PosDef.re_dotProduct_cfc_log_eq_integral {X : Matrix n n 𝕜} (hX : X.PosDef)
    (v : n → 𝕜) :
    IntegrableOn
      (fun t : ℝ => RCLike.re (star v ⬝ᵥ cfc (fun x : ℝ => (1 + t)⁻¹ - (x + t)⁻¹) X *ᵥ v))
      (Ioi 0) ∧
    RCLike.re (star v ⬝ᵥ cfc Real.log X *ᵥ v) =
      ∫ t in Ioi 0,
        RCLike.re (star v ⬝ᵥ cfc (fun x : ℝ => (1 + t)⁻¹ - (x + t)⁻¹) X *ᵥ v) := by
  simp only [hX.isHermitian.dotProduct_cfc_mulVec, RCLike.ofReal_re]
  have hint : ∀ i ∈ Finset.univ, IntegrableOn (fun t => ((1 + t)⁻¹ - (hX.isHermitian.eigenvalues i
      + t)⁻¹) * ‖(star (↑hX.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ v) i‖ ^ 2)
      (Ioi 0) := fun i _ => (Real.integrableOn_inv_sub_inv (hX.eigenvalues_pos i)).mul_const _
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, ← Real.log_eq_integral_inv_sub_inv (hX.eigenvalues_pos i)]

/-- `cfc ((1 + t)⁻¹ - (· + t)⁻¹) X = (1 + t)⁻¹ - (X + t)⁻¹` for `X > 0` and `t ≥ 0`. -/
theorem PosDef.cfc_inv_one_add_sub_inv_add {X : Matrix n n 𝕜} (hX : X.PosDef) {t : ℝ}
    (ht : 0 ≤ t) :
    cfc (fun x : ℝ => (1 + t)⁻¹ - (x + t)⁻¹) X =
      (1 + t)⁻¹ • (1 : Matrix n n 𝕜) - (X + t • 1)⁻¹ := by
  have hself : IsSelfAdjoint X := hX.isHermitian
  have hsp : ∀ x ∈ spectrum ℝ X, x + t ≠ 0 := fun x hx =>
    (add_pos_of_pos_of_nonneg (hX.isStrictlyPositive.spectrum_pos hx) ht).ne'
  have hcont : ContinuousOn (fun x : ℝ => (x + t)⁻¹) (spectrum ℝ X) :=
    (continuous_id.add continuous_const).continuousOn.inv₀ hsp
  rw [cfc_sub _ _ X continuousOn_const hcont, cfc_const _ _ hself,
    cfc_inv _ _ hsp (continuous_id.add continuous_const).continuousOn hself,
    cfc_add_const t (fun x => x) X continuous_id.continuousOn hself, cfc_id' ℝ X hself,
    ← nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]

end Matrix
