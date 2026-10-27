import AreaLaw.S07_Transport.ExactDerivative

/-!
# §7.4 Endpoints and uniformity (D7.26)

Digest `digest/07-transport.md` D7.26, paper `paper/sections/06-transport.tex` 762–771: for fixed
`k`, `N(p)` is continuous on `[0, 1]`, the exact derivative is bounded uniformly in
`p ∈ (0, 1)`, and `log N²` at the endpoints is the integral of the derivative. No geometry.

Some declarations here come from the v1 file `OpenAI/Transport/Derivative.lean`, whose header
records it as ported or adapted from `LionSR/QICLean` (see `NOTICE`).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Set Filter Topology Entropy
open Matrix.Transport (filteredVector filteredNormSq imagPow fourierWeight)

namespace AreaLaw.Transport

namespace Round

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {K : ℕ} {H : Type*}
  [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)] (R : Round V K H C)

/-- D7.26.1: the interpolated subtree depends continuously on `p ∈ [0, 1]`. -/
theorem continuous_eval_itree [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : R.CrossBandCommute n t k) (T₀ : MeanTree H) :
    Continuous fun x : I => (R.itree T₀ x).eval (R.input n t k) := by
  have hIn := R.posDef_input hR ht hcomm
  induction T₀ with
  | leaf h₀ =>
    have hA : (R.oldMetric n t k h₀).PosDef := hIn ⟨h₀, none⟩
    have hB := R.posDef_choiceRoot hR ht hcomm h₀
    have hfun : (fun x : I => (R.itree (.leaf h₀) x).eval (R.input n t k)) =
        fun x : I => geomMean x (R.oldMetric n t k h₀) (R.choiceRoot n t k h₀) := by
      funext x
      simp only [itree, MeanTree.bind, MeanTree.eval_node, MeanTree.eval_leaf, eval_map_choice]
      rfl
    rw [hfun]
    exact (continuous_iff_continuousAt.mpr fun q =>
      (hasDerivAt_geomMean_param hA hB q).continuousAt).comp continuous_subtype_val
  | node r l rr ihl ihr =>
    refine continuous_iff_continuousAt.mpr fun x => ?_
    rw [← continuousWithinAt_univ]
    have hg := (differentiableWithinAt_geomMean (MeanTree.posDef_eval hIn (R.itree l x))
      (MeanTree.posDef_eval hIn (R.itree rr x)) r.2).continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun y : I => ((R.itree l y).eval (R.input n t k),
        (R.itree rr y).eval (R.input n t k))) hg (ihl.prodMk ihr).continuousWithinAt
      fun y _ => ⟨(MeanTree.posDef_eval hIn (R.itree l y)).isHermitian,
        (MeanTree.posDef_eval hIn (R.itree rr y)).isHermitian⟩

/-- D7.26.1: `p ↦ 𝓜(p)` is continuous (constant outside `[0, 1]`). -/
theorem continuous_root [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : R.CrossBandCommute n t k) : Continuous fun q => R.root n t k q :=
  (R.continuous_eval_itree hR ht hcomm R.histTree).comp continuous_projIcc

/-- D7.26.1: `N(p)²` is continuous and, for `pre ≠ 0`, positive. -/
theorem continuous_normSq [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : R.CrossBandCommute n t k) (pre : Config n k → ℂ) :
    Continuous (fun q => R.normSq n t k pre q) ∧
      (pre ≠ 0 → ∀ q, 0 < R.normSq n t k pre q) := by
  have hM := R.posDef_root hR ht hcomm
  refine ⟨?_, fun hpre q => Matrix.Transport.filteredNormSq_pos (hM q) hpre⟩
  simp_rw [normSq, Matrix.Transport.filteredNormSq_eq (hM _)]
  have hc : Continuous fun q => R.root n t k q ^ (-(1 / 2) : ℝ) := by
    refine continuous_iff_continuousAt.mpr fun q => ?_
    rw [← continuousWithinAt_univ]
    exact (differentiableWithinAt_rpow_neg_half (hM q)).continuousWithinAt.comp
      (R.continuous_root hR ht hcomm).continuousWithinAt fun y _ => (hM y).isHermitian
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (hc.matrix_mulVec continuous_const))

omit [Fintype V] [DecidableEq V] [DecidableEq H] [∀ h, DecidableEq (C h)] in
/-- `|Re Tr(ρ X)| ≤ ‖X‖ Re Tr ρ` for `ρ ≥ 0`, `X` Hermitian. -/
theorem abs_re_trace_mul_le {m : Type*} [Fintype m] [DecidableEq m] {ρ X : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hX : X.IsHermitian) : |(ρ * X).trace.re| ≤ ‖X‖ * ρ.trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have h1 : X ≤ ‖X‖ • (1 : Matrix m m ℂ) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hsa.le_algebraMap_norm_self
  have h2 : -(‖X‖ • (1 : Matrix m m ℂ)) ≤ X := by
    simpa [Algebra.algebraMap_eq_smul_one] using hsa.neg_algebraMap_norm_le_self
  have u := (Complex.nonneg_iff.mp (PosSemidef.trace_mul_nonneg (Matrix.le_iff.mp h1) hρ)).1
  have l := (Complex.nonneg_iff.mp (PosSemidef.trace_mul_nonneg (Matrix.le_iff.mp h2) hρ)).1
  rw [Matrix.sub_mul, trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.one_mul, trace_smul,
    Complex.real_smul, Complex.re_ofReal_mul, trace_mul_comm X] at u
  rw [Matrix.sub_mul, trace_sub, Complex.sub_re, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.one_mul, trace_neg, trace_smul, Complex.neg_re, Complex.real_smul,
    Complex.re_ofReal_mul, trace_mul_comm X] at l
  rw [abs_le]
  constructor <;> linarith

variable [Fintype H]

/-- D7.26.2: the exact derivative is bounded uniformly in `p ∈ (0, 1)` (the states are
densities, `∑_h w_h = 1`, `∫ m_s = 1/2`). -/
theorem exists_abs_exactDerivative_le [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (hcomm : R.CrossBandCommute n t k) {pre : Config n k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k) (hpre : pre ≠ 0) :
    ∃ B : ℝ, ∀ p : I, 0 < (p : ℝ) → (p : ℝ) < 1 → |R.exactDerivative n t k pre p| ≤ B := by
  refine ⟨∑ h, R.histTree.weight h * ∫ u, m (1 / 4) u * ‖CFC.log (R.relRatio n t k h)‖,
    fun p hp0 hp1 => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  rw [abs_mul, abs_of_pos (hR.histWeight_pos h)]
  refine mul_le_mul_of_nonneg_left ?_ (hR.histWeight_pos h).le
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _)
    ((integrable_m (s := 1 / 4) (by norm_num)).mul_const _) (Eventually.of_forall fun u => ?_))
  have hlog : (CFC.log (R.relRatio n t k h)).IsHermitian := by
    unfold CFC.log; exact cfc_predicate _ _
  obtain ⟨hσ, hσ1, -⟩ := R.isSymDensity_state hR ht hcomm hpreS hpre hp0 hp1 ⟨h, none⟩ u
  have hb := abs_re_trace_mul_le hσ hlog
  rw [hσ1, Complex.one_re, mul_one] at hb
  have hm : 0 < m (1 / 4) u := Real.sinhRatioDensity_pos (by norm_num) u
  simp only [abs_mul, abs_of_pos hm]
  exact mul_le_mul_of_nonneg_left hb hm.le

/-- D7.26.3: for `0 ≤ p₀ ≤ p₁ ≤ 1` the exact derivative is interval integrable on
`[p₀, p₁]` and `log N(p₀)² − log N(p₁)² = ∫_{p₀}^{p₁} (−∂_p log N²)`, with the continuous
endpoint values of `N`. -/
theorem log_normSq_sub_eq_integral [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (hcomm : R.CrossBandCommute n t k) {pre : Config n k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k) (hpre : pre ≠ 0) {p₀ p₁ : ℝ}
    (h0 : 0 ≤ p₀) (h01 : p₀ ≤ p₁) (h1 : p₁ ≤ 1) :
    IntervalIntegrable (fun p => R.exactDerivative n t k pre (projIcc 0 1 zero_le_one p))
        volume p₀ p₁ ∧
      Real.log (R.normSq n t k pre p₀) - Real.log (R.normSq n t k pre p₁) =
        ∫ p in p₀..p₁, R.exactDerivative n t k pre (projIcc 0 1 zero_le_one p) := by
  set F := fun q => -Real.log (R.normSq n t k pre q)
  set F' := fun p => R.exactDerivative n t k pre (projIcc 0 1 zero_le_one p)
  have hsub : Ioo p₀ p₁ ⊆ Ioo 0 1 := Ioo_subset_Ioo h0 h1
  have hd : ∀ p ∈ Ioo p₀ p₁, HasDerivAt F (F' p) p := fun p hp => by
    have hp' := hsub hp
    obtain ⟨hD, hE, -⟩ := R.step_7_16 hR ht hcomm hpreS hpre hp'
    have hpI : (projIcc (0 : ℝ) 1 zero_le_one p : I) = ⟨p, Ioo_subset_Icc_self hp'⟩ :=
      projIcc_of_mem _ (Ioo_subset_Icc_self hp')
    simp only [F', hpI]
    rw [← hE]
    exact hD
  obtain ⟨hcN, hpos⟩ := R.continuous_normSq hR ht hcomm pre
  have hcont : Continuous F := (hcN.log fun q => (hpos hpre q).ne').neg
  obtain ⟨B, hB⟩ := R.exists_abs_exactDerivative_le hR ht hcomm hpreS hpre
  have hint : IntervalIntegrable F' volume p₀ p₁ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le h01]
    have hderiv : IntegrableOn (deriv F) (Ioo p₀ p₁) := by
      refine Measure.integrableOn_of_bounded (M := B) (by simp)
        (stronglyMeasurable_deriv F).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
      rw [(hd p hp).deriv, Real.norm_eq_abs]
      have hp' := hsub hp
      exact hB _ (by rw [projIcc_of_mem _ (Ioo_subset_Icc_self hp')]; exact hp'.1)
        (by rw [projIcc_of_mem _ (Ioo_subset_Icc_self hp')]; exact hp'.2)
    exact hderiv.congr_fun (fun p hp => (hd p hp).deriv) measurableSet_Ioo
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h01 hcont.continuousOn hd hint]
  simp only [F]
  ring

end Round

end AreaLaw.Transport
