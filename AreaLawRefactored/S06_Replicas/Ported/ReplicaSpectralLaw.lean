/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.WeylCharacter
import AreaLawRefactored.S06_Replicas.Ported.ReplicaGammaIntegral
import AreaLawForMathlib.Analysis.Matrix.CfcConjugation

/-!
# The spectral law of the replica metrics

The samples `σ = U diag(x/∑ x) U†`, with `x` of density `a_δ(x) a_δ(x^t) e^{-∑ x}` on the
orthant and `U` Haar, satisfy `∫ (σ^t)^{⊗k} = ∑_λ w_k(λ) π^λ` (`05-replicas.tex`, l. 336–364).
-/

open MeasureTheory Matrix Finset PermutationRepresentation Partition
open scoped MatrixOrder ComplexOrder ENNReal NNReal

namespace TensorPower

variable {d : ℕ}

/-! ### The spectral density -/

/-- The unnormalized spectral density `a_δ(x) a_δ(x^t) e^{-∑ x}` on the orthant. -/
noncomputable def specDensity (d : ℕ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  alternant (delta d) x * alternant (delta d) (fun i => x i ^ t) * Real.exp (-∑ i, x i)

/-- The normalization `∫ a_δ(x) a_δ(x^t) e^{-∑ x} dx`. -/
noncomputable def specNorm (d : ℕ) (t : ℝ) : ℝ := gammaIntegral d t (delta d) 0

theorem gammaIntegrand_zero (t : ℝ) (x : Fin d → ℝ) :
    alternant (delta d) x * alternant (delta d) (fun i => x i ^ t) * (∑ i, x i) ^ (-(0 : ℝ)) *
      Real.exp (-∑ i, x i) = specDensity d t x := by
  simp [specDensity]

theorem specNorm_eq_integral (t : ℝ) : specNorm d t = ∫ x, specDensity d t x ∂(orthant d) := by
  simp only [specNorm, gammaIntegral, gammaIntegrand_zero]

theorem specDensity_nonneg {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    0 ≤ specDensity d t x :=
  mul_nonneg (alternant_delta_mul_rpow_nonneg ht hx) (Real.exp_pos _).le

theorem specNorm_pos (hd : 0 < d) {t : ℝ} (ht : 0 < t) : 0 < specNorm d t := by
  have hnn : 0 ≤ specNorm d t := by
    rw [specNorm_eq_integral]
    exact integral_nonneg_of_ae (ae_orthant_pos.mono fun x hx => specDensity_nonneg ht.le hx)
  refine hnn.lt_of_ne fun h0 => ?_
  have hD : (0 : ℝ) < d + (d.choose 2 : ℕ) + t * ∑ i, ((delta d i : ℕ) : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have h := gammaIntegral_eq hd ht.le (delta d) le_rfl hD
  rw [← specNorm, ← h0, sub_zero, div_self (Real.Gamma_pos_of_pos hD).ne', mul_one] at h
  have hG : (0 : ℝ) < ∏ j, Real.Gamma (1 + t * ((delta d j : ℕ) : ℝ)) :=
    prod_pos fun j _ => Real.Gamma_pos_of_pos (by positivity)
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  have := alternant_delta_ne_zero (y := fun i : Fin d => ((delta d i : ℕ) : ℝ)) fun i j h => by
    have h'' : ((delta d i : ℕ) : ℝ) = delta d j := h
    have h' : delta d i = delta d j := by exact_mod_cast h''
    simp only [shiftedPart, Pi.zero_apply, zero_add] at h'
    exact Fin.ext (by have := i.2; have := j.2; omega)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hf (pow_ne_zero _ ht.ne')) hG.ne') this) h.symm

/-- The normalized spectral density, as a nonnegative function. -/
noncomputable def specWeight (d : ℕ) (t : ℝ) (x : Fin d → ℝ) : ℝ≥0 :=
  Real.toNNReal (specDensity d t x / specNorm d t)

/-- The spectral law on the orthant. -/
noncomputable def specMeasure (d : ℕ) (t : ℝ) : Measure (Fin d → ℝ) :=
  (orthant d).withDensity fun x => (specWeight d t x : ℝ≥0∞)

theorem measurable_specWeight {t : ℝ} (ht : 0 ≤ t) : Measurable (specWeight d t) :=
  ((by unfold specDensity alternant; fun_prop (disch := assumption) :
    Continuous (specDensity d t)).measurable.div_const _).real_toNNReal

theorem coe_specWeight_ae (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(orthant d), (specWeight d t x : ℝ) = specDensity d t x / specNorm d t := by
  filter_upwards [ae_orthant_pos] with x hx
  exact Real.coe_toNNReal _ (div_nonneg (specDensity_nonneg ht.le hx) (specNorm_pos hd ht).le)

theorem isProbabilityMeasure_specMeasure (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (specMeasure d t) := by
  constructor
  rw [specMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun x => (specWeight d t x : ℝ)) (orthant d) := by
    refine (Integrable.div_const ?_ (specNorm d t)).congr
      ((coe_specWeight_ae hd ht).mono fun x hx => hx.symm)
    simpa only [gammaIntegrand_zero] using integrable_gammaIntegrand hd ht.le (delta d) le_rfl
      (by have : (0 : ℝ) < d := by exact_mod_cast hd
          positivity)
  rw [lintegral_coe_eq_integral _ hint, integral_congr_ae (coe_specWeight_ae hd ht),
    integral_div, ← specNorm_eq_integral, div_self (specNorm_pos hd ht).ne', ENNReal.ofReal_one]

theorem integral_specMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hd : 0 < d) {t : ℝ} (ht : 0 < t) (g : (Fin d → ℝ) → E) :
    ∫ x, g x ∂(specMeasure d t) = ∫ x, (specDensity d t x / specNorm d t) • g x ∂(orthant d) := by
  rw [specMeasure, integral_withDensity_eq_integral_smul (measurable_specWeight ht.le)]
  refine integral_congr_ae ((coe_specWeight_ae hd ht).mono fun x hx => ?_)
  simp only [NNReal.smul_def, hx]

theorem ae_specMeasure_pos {t : ℝ} :
    ∀ᵐ x ∂(specMeasure d t), ∀ i, 0 < x i :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_orthant_pos

/-! ### Characters at real diagonal matrices -/

theorem glChar_mul_left {q k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) (c : ℂ)
    (y : Fin q → ℂ) : glChar q l (fun i => c * y i) = c ^ k * glChar q l y := by
  have : diagonal (fun i => c * y i) = c • diagonal y := by
    rw [← diagonal_smul]; rfl
  have tensorPow_smul : tensorPow (k := k) (c • diagonal y) = c ^ k • tensorPow (diagonal y) := by
    ext x y
    simp [tensorPow_apply, prod_mul_distrib, prod_const]
  rw [glChar, glChar, this, tensorPow_smul, mul_smul_comm, trace_smul, smul_eq_mul]

/-- The spectral density times the eigenvalue of the twirl is the gamma integrand. -/
theorem specDensity_mul_glChar {t : ℝ} {k : ℕ} {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : HasRows d l) (hd : 0 < d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    (specDensity d t x : ℂ) * glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) =
      ((alternant (delta d) x * alternant (shiftedPart (part d l)) (fun i => x i ^ t) *
        (∑ i, x i) ^ (-(t * k)) * Real.exp (-∑ i, x i) : ℝ) : ℂ) := by
  set S := ∑ i, x i
  have hS : 0 < S := sum_pos (fun i _ => hx i) ⟨⟨0, hd⟩, mem_univ _⟩
  have hy : (fun i => (((x i / S) ^ t : ℝ) : ℂ)) =
      fun i => ((S ^ (-t) : ℝ) : ℂ) * ((x i ^ t : ℝ) : ℂ) := by
    funext i
    rw [Real.div_rpow (hx i).le hS.le, Real.rpow_neg hS.le]
    push_cast
    ring
  rw [hy, glChar_mul_left]
  have alternant_ofReal (α : Fin d → ℕ) (y : Fin d → ℝ) :
      alternant α (fun i => (y i : ℂ)) = (alternant (R := ℝ) α y : ℂ) := by
    simp only [alternant_eq_sum]; push_cast; rfl
  have hw := alternant_mul_glChar hl (fun i => ((x i ^ t : ℝ) : ℂ))
  rw [alternant_ofReal, alternant_ofReal] at hw
  have hpow : ((S ^ (-t) : ℝ) : ℂ) ^ k = ((S ^ (-(t * k)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hS.le]
    congr 2
    ring
  rw [hpow]
  simp only [specDensity, Complex.ofReal_mul]
  linear_combination (alternant (R := ℝ) (delta d) x : ℂ) * ((S ^ (-(t * k)) : ℝ) : ℂ) *
    (Real.exp (-S) : ℂ) * hw

/-! ### Samples -/

/-- The sample `σ = U diag(x/∑ x) U†`. -/
noncomputable def specSample (x : Fin d → ℝ) (U : unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun i => ((x i / ∑ j, x j : ℝ) : ℂ)) *
    star (U : Matrix (Fin d) (Fin d) ℂ)

theorem specSample_rpow (hd : 0 < d) {t : ℝ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i)
    (U : unitaryGroup (Fin d) ℂ) :
    specSample x U ^ t = (U : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) *
        star (U : Matrix (Fin d) (Fin d) ℂ) := by
  have hS : 0 < ∑ j, x j := sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  have hD : (diagonal (fun i => ((x i / ∑ j, x j : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (div_nonneg (hx i).le hS.le)
  rw [specSample, rpow_conj_unitary hD t U, CFC.rpow_eq_cfc_real hD.nonneg]
  have hcfc : cfc (fun x : ℝ => x ^ t)
      (diagonal fun i => ((x i / ∑ j, x j : ℝ) : ℂ)) =
      diagonal (RCLike.ofReal ∘ (fun x : ℝ => x ^ t) ∘
        (fun i => x i / ∑ j, x j)) :=
    Matrix.cfc_diagonal (𝕜 := ℂ) _ _
  simpa [Function.comp_def] using congrArg
    (fun X : Matrix (Fin d) (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) * X * star (U : Matrix (Fin d) (Fin d) ℂ)) hcfc

theorem specSample_posDef (hd : 0 < d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i)
    (U : unitaryGroup (Fin d) ℂ) :
    (specSample x U).PosDef := by
  have hS : 0 < ∑ j, x j := sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  have hD : (diagonal (fun i => ((x i / ∑ j, x j : ℝ) : ℂ))).PosDef :=
    posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (div_pos (hx i) hS)
  have hinj : Function.Injective (star (U : Matrix (Fin d) (Fin d) ℂ)).mulVec := by
    refine Function.LeftInverse.injective (g := fun v => (U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v)
      fun v => ?_
    simp only [mulVec_mulVec, (mem_unitaryGroup_iff.mp U.2), one_mulVec]
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [star_eq_conjTranspose, conjTranspose_conjTranspose] at this

theorem trace_specSample (hd : 0 < d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i)
    (U : unitaryGroup (Fin d) ℂ) :
    (specSample x U).trace = 1 := by
  have hS : 0 < ∑ j, x j := sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  rw [specSample, trace_mul_cycle, mem_unitaryGroup_iff'.mp U.2, Matrix.one_mul, trace_diagonal,
    ← Complex.ofReal_sum, ← sum_div, div_self hS.ne', Complex.ofReal_one]

/-! ### The full-dimensional integral -/

/-- The entries of `(σ^t)^{⊗k}` for `σ = U diag(x/∑ x) U†`, written explicitly. -/
noncomputable def sampleEntry (t : ℝ) {k : ℕ} (a b : Fin k → Fin d)
    (ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ) : ℂ :=
  ∏ m, ∑ c, (ω.2 : Matrix (Fin d) (Fin d) ℂ) (a m) c * (((ω.1 c / ∑ j, ω.1 j) ^ t : ℝ) : ℂ) *
    star ((ω.2 : Matrix (Fin d) (Fin d) ℂ) (b m) c)

theorem tensorPow_specSample_rpow_apply (hd : 0 < d) {t : ℝ} {k : ℕ}
    {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) (a b : Fin k → Fin d) :
    tensorPow (k := k) (specSample x U ^ t) a b = sampleEntry t a b (x, U) := by
  rw [specSample_rpow hd hx, tensorPow_apply, sampleEntry]
  refine prod_congr rfl fun m _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, star_apply]

theorem measurable_sampleEntry (t : ℝ) {k : ℕ} (a b : Fin k → Fin d) :
    Measurable (sampleEntry t a b) := by
  have hU : ∀ i j, Measurable fun ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ =>
      (ω.2 : Matrix (Fin d) (Fin d) ℂ) i j := fun i j =>
    ((continuous_unitary_apply (Fin d) i j).comp continuous_snd).measurable
  have hx : ∀ c, Measurable fun ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ =>
      ((((ω.1 c / ∑ j, ω.1 j) ^ t : ℝ)) : ℂ) := fun c => by fun_prop
  unfold sampleEntry
  refine Finset.measurable_prod _ fun m _ => Finset.measurable_sum _ fun c _ => ?_
  exact ((hU _ _).mul (hx c)).mul (continuous_star.measurable.comp (hU _ _))

theorem norm_sampleEntry_le (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (a b : Fin k → Fin d)
    {ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ} (hx : ∀ i, 0 < ω.1 i) :
    ‖sampleEntry t a b ω‖ ≤ (d : ℝ) ^ k := by
  have hS : 0 < ∑ j, ω.1 j := sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  unfold sampleEntry
  rw [norm_prod]
  refine (prod_le_prod (fun _ _ => norm_nonneg _) fun m _ => (norm_sum_le _ _).trans
    ((sum_le_sum fun c _ => ?_).trans (by simp : ∑ _c : Fin d, (1 : ℝ) = d).le)).trans (by simp)
  have hq : 0 ≤ ω.1 c / ∑ j, ω.1 j := div_nonneg (hx c).le hS.le
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hq t)]
  exact mul_le_one₀ (mul_le_one₀ (norm_apply_le_one_of_mem_unitaryGroup ω.2.2 (a m) c)
    (Real.rpow_nonneg hq t) (Real.rpow_le_one hq ((div_le_one hS).2
      (single_le_sum (fun j _ => (hx j).le) (mem_univ c))) ht)) (norm_nonneg _)
    (norm_apply_le_one_of_mem_unitaryGroup ω.2.2 (b m) c)

theorem ae_prod_pos {t : ℝ} :
    ∀ᵐ ω ∂((specMeasure d t).prod (unitaryHaar (Fin d))), ∀ i, 0 < ω.1 i := by
  exact Measure.quasiMeasurePreserving_fst.ae ae_specMeasure_pos

/-- The average over the unitary eigenbasis is the twirl, a central label function with
eigenvalue `χ_λ(y)/dim V_λ`. -/
theorem integral_unitary_sampleEntry (hd : 0 < d) {t : ℝ} {k : ℕ}
    (a b : Fin k → Fin d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    ∫ U, sampleEntry t a b (x, U) ∂(unitaryHaar (Fin d)) =
      ∑ l, glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) /
        multiplicity (copyPerm (Fin d) k) l * labelProj (copyPerm (Fin d) k) l a b := by
  set y : Fin d → ℂ := fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)
  set A := tensorPow (k := k) (diagonal y)
  have hcongr : ∀ U : unitaryGroup (Fin d) ℂ, sampleEntry t a b (x, U) =
      (tensorPow (k := k) (U : Matrix (Fin d) (Fin d) ℂ) * A *
        tensorPow (k := k) (star U : Matrix (Fin d) (Fin d) ℂ)) a b := by
    intro U
    rw [← tensorPow_specSample_rpow_apply hd hx U, specSample_rpow hd hx, tensorPow_mul,
      tensorPow_mul]
  simp only [hcongr]
  change unitaryTwirl A a b = _
  obtain ⟨c, hc, hctr⟩ := unitaryTwirl_eq_sum_labelProj
    (fun σ => commute_permOp_copyPerm_tensorPow (k := k) (diagonal y) σ)
  rw [hc, Matrix.sum_apply]
  refine sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hm : multiplicity (copyPerm (Fin d) k) l = 0
  · have htr := trace_labelProj (copyPerm (Fin d) k) l
    rw [hm, mul_zero, Nat.cast_zero, trace_eq_finrank_range_of_mul_self (labelProj_mul_self _ l)]
      at htr
    have h0 : LinearMap.range (toLin' (labelProj (copyPerm (Fin d) k) l)) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by exact_mod_cast htr)
    rw [LinearMap.range_eq_bot] at h0
    simp [toLin'.injective (by rw [h0, map_zero] : toLin' (labelProj (copyPerm (Fin d) k) l) =
      toLin' 0)]
  · congr 1
    have h1 := hctr l
    rw [trace_labelProj, trace_labelProj_mul_tensorPow] at h1
    have hdim : (l.dim : ℂ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
    have hm' : (multiplicity (copyPerm (Fin d) k) l : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [eq_div_iff hm']
    push_cast at h1
    apply mul_left_cancel₀ hdim
    linear_combination h1

/-- The average of one label term over the spectral law is `w_k(λ) π^λ`. -/
theorem integral_specMeasure_label (hd : 0 < d) {t : ℝ} (ht : 0 < t) {k : ℕ}
    (a b : Fin k → Fin d) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Integrable (fun x => glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) /
        multiplicity (copyPerm (Fin d) k) l * labelProj (copyPerm (Fin d) k) l a b)
      (specMeasure d t) ∧
    ∫ x, glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) /
        multiplicity (copyPerm (Fin d) k) l * labelProj (copyPerm (Fin d) k) l a b
        ∂(specMeasure d t) =
      (replicaWeight t (part d l) : ℂ) * labelProj (copyPerm (Fin d) k) l a b := by
  by_cases hπ : labelProj (copyPerm (Fin d) k) l = 0
  · simp [hπ]
  have hl : HasRows d l := labelPart_eq_zero_of_labelProj_ne_zero hπ
  have hm := multiplicity_eq_weylFormula (q := d) l hl
  have hW : weylFormula (part d l) ≠ 0 := by
    rw [← hm]; exact_mod_cast (multiplicity_pos hl).ne'
  set Z := specNorm d t
  have hZ : 0 < Z := specNorm_pos hd ht
  set G : (Fin d → ℝ) → ℝ := fun x => alternant (delta d) x *
    alternant (shiftedPart (part d l)) (fun i => x i ^ t) * (∑ i, x i) ^ (-(t * k)) *
      Real.exp (-∑ i, x i)
  have hsum : ((∑ i, part d l i : ℕ) : ℝ) = k := by rw [sum_part hl]
  have hD : t * k < d + ((∑ i, delta d i : ℕ) : ℝ) +
      t * ∑ i, ((shiftedPart (part d l) i : ℕ) : ℝ) := by
    have h1 : ∑ i, ((shiftedPart (part d l) i : ℕ) : ℝ) = k + (d.choose 2 : ℕ) := by
      rw [← Nat.cast_sum, sum_shiftedPart_nat, Nat.cast_add, hsum]
    have h2 : (0 : ℝ) ≤ ((∑ i, delta d i : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ ((d.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [h1]
    nlinarith
  have hGint : Integrable G (orthant d) := integrable_gammaIntegrand hd ht.le _ (by positivity) hD
  have hpt : ∀ᵐ x ∂(orthant d), (specDensity d t x / Z) •
      (glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) /
        multiplicity (copyPerm (Fin d) k) l * labelProj (copyPerm (Fin d) k) l a b) =
      ((G x / (Z * weylFormula (part d l)) : ℝ) : ℂ) * labelProj (copyPerm (Fin d) k) l a b := by
    filter_upwards [ae_orthant_pos] with x hx
    have h := specDensity_mul_glChar (t := t) hl hd hx
    rw [Complex.real_smul, ← hm]
    have hm' : ((multiplicity (copyPerm (Fin d) k) l : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (multiplicity_pos hl).ne'
    have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
    push_cast
    rw [← h]
    field_simp
  -- integrability over the spectral law
  have hint0 : Integrable (fun x => (specDensity d t x / Z) •
      (glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) /
        multiplicity (copyPerm (Fin d) k) l * labelProj (copyPerm (Fin d) k) l a b))
      (orthant d) :=
    (((hGint.div_const _).ofReal (𝕜 := ℂ)).mul_const _).congr
      (hpt.mono fun x hx => hx.symm)
  refine ⟨?_, ?_⟩
  · rw [specMeasure, integrable_withDensity_iff_integrable_smul (measurable_specWeight ht.le)]
    refine hint0.congr ((coe_specWeight_ae hd ht).mono fun x hx => ?_)
    simp only [NNReal.smul_def, hx]
    rfl
  · rw [integral_specMeasure hd ht, integral_congr_ae hpt, integral_mul_const,
      integral_complex_ofReal, integral_div, replicaWeight_eq_gammaIntegral hd ht
      (antitone_part l), hsum]
    rfl

/-- Lemma 6.2, equation `replicas:W-integral`: `∫ (σ^t)^{⊗k} = ∑_λ w_k(λ) π^λ`. -/
theorem integral_specSample_tensorPow (hd : 0 < d) {t : ℝ} (ht : 0 < t) {k : ℕ}
    (a b : Fin k → Fin d) :
    Integrable (fun ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ =>
        tensorPow (k := k) (specSample ω.1 ω.2 ^ t) a b)
      ((specMeasure d t).prod (unitaryHaar (Fin d))) ∧
    ∫ ω, tensorPow (k := k) (specSample ω.1 ω.2 ^ t) a b
        ∂((specMeasure d t).prod (unitaryHaar (Fin d))) =
      ∑ l, (replicaWeight t (part d l) : ℂ) * labelProj (copyPerm (Fin d) k) l a b := by
  have := isProbabilityMeasure_specMeasure hd ht
  have heq : (fun ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ =>
      tensorPow (k := k) (specSample ω.1 ω.2 ^ t) a b) =ᵐ[(specMeasure d t).prod
        (unitaryHaar (Fin d))] sampleEntry t a b :=
    ae_prod_pos.mono fun ω hω => tensorPow_specSample_rpow_apply hd hω ω.2 a b
  have hint : Integrable (sampleEntry t a b) ((specMeasure d t).prod (unitaryHaar (Fin d))) :=
    Integrable.of_bound (measurable_sampleEntry t a b).aestronglyMeasurable ((d : ℝ) ^ k)
      (ae_prod_pos.mono fun ω hω => norm_sampleEntry_le hd ht.le a b hω)
  refine ⟨hint.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_prod _ hint]
  have hinner : ∀ᵐ x ∂(specMeasure d t), ∫ U, sampleEntry t a b (x, U) ∂(unitaryHaar (Fin d)) =
      ∑ l, glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) /
        multiplicity (copyPerm (Fin d) k) l * labelProj (copyPerm (Fin d) k) l a b :=
    ae_specMeasure_pos.mono fun x hx => integral_unitary_sampleEntry hd a b hx
  rw [integral_congr_ae hinner, integral_finsetSum _ fun l _ =>
    (integral_specMeasure_label hd ht a b l).1]
  exact sum_congr rfl fun l _ => (integral_specMeasure_label hd ht a b l).2

end TensorPower
