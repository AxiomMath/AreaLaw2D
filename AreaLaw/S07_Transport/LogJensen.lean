import AreaLaw.S06_Replicas.Coherent
import AreaLawForMathlib.Analysis.Matrix.OperatorJensen
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# §7 Operator Jensen for coherent integrals (D7.19)

Digest `digest/07-transport.md` D7.19, paper `06-transport.tex` lines 520–547.
-/

namespace AreaLaw.Transport

open Matrix MeasureTheory Set Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {J : Type*} [Fintype J] [DecidableEq J] (ι : J → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] (k : ℕ)

/-- D7.19. The coherent integral `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ`. -/
noncomputable def Q (f : Replicas.Sphere ι → ℝ) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  (Replicas.D ι k : ℂ) • Matrix.of fun x y => ∫ θ, ((f θ : ℂ) • Replicas.P ι k θ.1) x y
    ∂Replicas.dθ ι

variable {ι k}

theorem integrable_Q_apply {f : Replicas.Sphere ι → ℝ} (hf : Continuous f)
    (x y : Replicas.Config ι k) :
    Integrable (fun θ : Replicas.Sphere ι => ((f θ : ℂ) • Replicas.P ι k θ.1) x y)
      (Replicas.dθ ι) := by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact ((Complex.continuous_ofReal.comp hf).mul ((Replicas.continuous_P_apply ι k x y).comp
    continuous_subtype_val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Fintype J] [DecidableEq J] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)] in
theorem posSemidef_P [Finite J] [∀ f, Finite (ι f)] (θ : ((f : J) → ι f) → ℂ) :
    (Replicas.P ι k θ).PosSemidef := by
  have := Fintype.ofFinite J
  have := fun f => Fintype.ofFinite (ι f)
  rw [Replicas.P, TensorPower.coherentProj]
  exact posSemidef_vecMulVec_self_star _

variable (ι k) in
theorem D_ne_zero : (Replicas.D ι k : ℂ) ≠ 0 := by
  rw [← Replicas.trace_projS, Replicas.projS_eq]
  exact TensorPower.trace_symProj_ne_zero (Classical.arbitrary _)

variable (ι k) in
theorem projS_eq_D_smul :
    Replicas.projS ι k = (Replicas.D ι k : ℂ) • Matrix.of fun x y =>
      ∫ θ, Replicas.P ι k θ.1 x y ∂Replicas.dθ ι := by
  rw [Replicas.eq_replicas_resolution, smul_smul, mul_inv_cancel₀ (D_ne_zero ι k), one_smul]

variable (ι k) in
theorem Q_const (c : ℝ) : Q ι k (fun _ => c) = (c : ℂ) • Replicas.projS ι k := by
  rw [projS_eq_D_smul, smul_comm, Q]
  congr 1
  ext x y
  simp only [of_apply, Matrix.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

theorem Q_sub {f g : Replicas.Sphere ι → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Q ι k (f - g) = Q ι k f - Q ι k g := by
  rw [Q, Q, Q, ← smul_sub]
  congr 1
  ext x y
  simp only [of_apply, Matrix.sub_apply, Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  exact integral_sub (integrable_Q_apply hf x y) (integrable_Q_apply hg x y)

theorem Q_add {f g : Replicas.Sphere ι → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Q ι k (f + g) = Q ι k f + Q ι k g := by
  rw [Q, Q, Q, ← smul_add]
  congr 1
  ext x y
  simp only [of_apply, Matrix.add_apply, Pi.add_apply, Complex.ofReal_add, add_smul]
  exact integral_add (integrable_Q_apply hf x y) (integrable_Q_apply hg x y)

theorem isHermitian_Q (f : Replicas.Sphere ι → ℝ) : (Q ι k f).IsHermitian := by
  have h := isHermitian_of_integral (μ := Replicas.dθ ι) (M := fun θ : Replicas.Sphere ι =>
    (f θ : ℂ) • Replicas.P ι k θ.1) fun θ => by
      rw [IsHermitian, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      exact congrArg _ (posSemidef_P θ.1).1
  rw [IsHermitian, Q, conjTranspose_smul, star_natCast, h.eq]

/-- D7.19.1. `𝒬_k(f) ≥ 0` for `f ≥ 0`. -/
theorem posSemidef_Q {f : Replicas.Sphere ι → ℝ} (hf : Continuous f) (h0 : 0 ≤ f) :
    (Q ι k f).PosSemidef :=
  (PosSemidef.of_integral (integrable_Q_apply hf) fun θ =>
    (posSemidef_P θ.1).smul (Complex.zero_le_real.mpr (h0 θ))).smul
      (Nat.cast_nonneg (α := ℂ) _)

/-- D7.19 (used in D7.20.3). `Tr(ρ 𝒬_k(f)) = ∫ f dμ_ρ` for `ρ ≥ 0`. -/
theorem trace_mul_Q {ρ : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ}
    (hρ : ρ.PosSemidef) {f : Replicas.Sphere ι → ℝ} (hf : Continuous f) :
    (ρ * Q ι k f).trace = ∫ θ, (f θ : ℂ) ∂(Replicas.μ ι k ρ) := by
  have hd : Continuous fun θ : Replicas.Sphere ι =>
      (Replicas.D ι k : ℝ) * (ρ * Replicas.P ι k θ.1).trace.re :=
    continuous_const.mul (Complex.continuous_re.comp
      ((Replicas.continuous_trace_mul_P ι k ρ).comp continuous_subtype_val))
  rw [Q, mul_smul_comm, trace_smul, trace_mul_of_integral (integrable_Q_apply hf), smul_eq_mul,
    ← integral_const_mul, Replicas.μ, integral_withDensity_eq_integral_toReal_smul
      hd.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  have h := Replicas.trace_mul_P_nonneg ι k hρ θ.1
  have hre : (((ρ * Replicas.P ι k θ.1).trace.re : ℝ) : ℂ) = (ρ * Replicas.P ι k θ.1).trace :=
    Complex.ext rfl (by simp [(Complex.nonneg_iff.mp h).2])
  simp only [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (Complex.nonneg_iff.mp h).1),
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_natCast, hre, mul_smul_comm, trace_smul,
    smul_eq_mul]
  ring

omit [∀ f, Nonempty (ι f)] in
theorem isStarProjection_projS : IsStarProjection (Replicas.projS ι k) :=
  PermutationRepresentation.isStarProjection_symProj _

/-- D7.19.2. `𝒬_k(g) + c (1 - Π_k)` is positive definite for continuous `g > 0` and `c > 0`. -/
theorem posDef_Q_add {g : Replicas.Sphere ι → ℝ} (hg : Continuous g) (hpos : ∀ θ, 0 < g θ)
    {c : ℝ} (hc : 0 < c) :
    (Q ι k g + (c : ℂ) • (1 - Replicas.projS ι k)).PosDef := by
  obtain ⟨θ₀, -, hθ₀⟩ := isCompact_univ.exists_isMinOn
    ⟨Replicas.sphereMap ι (Classical.arbitrary _) 1, mem_univ _⟩ hg.continuousOn
  set m := g θ₀
  set r := min m c
  have hr : 0 < r := lt_min (hpos θ₀) hc
  have hQ : (Q ι k g - (m : ℂ) • Replicas.projS ι k).PosSemidef := by
    rw [← Q_const, ← Q_sub hg continuous_const]
    exact posSemidef_Q (hg.sub continuous_const) fun θ => sub_nonneg.mpr (hθ₀ (mem_univ θ))
  have hPi := isStarProjection_projS (ι := ι) (k := k)
  have hsum := (hQ.add ((hPi.nonneg.posSemidef).smul (Complex.zero_le_real.mpr
    (sub_nonneg.mpr (min_le_left m c))))).add ((hPi.one_sub.nonneg.posSemidef).smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr (min_le_right m c))))
  have h := (PosDef.one.smul (Complex.zero_lt_real.mpr hr)).add_posSemidef hsum
  convert h using 1
  push_cast
  module

/-- D7.19.2 (with the filler `c` on `𝒮_k^⊥`). `(𝒬_k(g) + c (1 - Π_k))⁻¹ ≤ 𝒬_k(g⁻¹) + c⁻¹ (1 - Π_k)`
for continuous `g > 0` and `c > 0`: the block `[[g, 1], [1, g⁻¹]] ≥ 0` integrated against
`D_k P_{θ,k} dθ`, then the Schur complement. -/
theorem Q_add_inv_le {g : Replicas.Sphere ι → ℝ} (hg : Continuous g) (hpos : ∀ θ, 0 < g θ)
    {c : ℝ} (hc : 0 < c) :
    (Q ι k g + (c : ℂ) • (1 - Replicas.projS ι k))⁻¹ ≤
      Q ι k g⁻¹ + (c : ℂ)⁻¹ • (1 - Replicas.projS ι k) := by
  have hg' : Continuous g⁻¹ := hg.inv₀ fun θ => (hpos θ).ne'
  have hP1 : Continuous fun _ : Replicas.Sphere ι => (1 : ℝ) := continuous_const
  have hblock : (fromBlocks (Q ι k g) (Replicas.projS ι k) (Replicas.projS ι k)
      (Q ι k g⁻¹)).PosSemidef := by
    have he : fromBlocks (Q ι k g) (Replicas.projS ι k) (Replicas.projS ι k) (Q ι k g⁻¹) =
        (Replicas.D ι k : ℂ) • of fun i j => ∫ θ, fromBlocks ((g θ : ℂ) • Replicas.P ι k θ.1)
          (Replicas.P ι k θ.1) (Replicas.P ι k θ.1) ((g θ : ℂ)⁻¹ • Replicas.P ι k θ.1) i j
          ∂Replicas.dθ ι := by
      rw [projS_eq_D_smul, Q, Q]
      ext (i | i) (j | j) <;> simp [Complex.ofReal_inv]
    have hpt : ∀ θ : Replicas.Sphere ι, (fromBlocks ((g θ : ℂ) • Replicas.P ι k θ.1)
        (Replicas.P ι k θ.1) (Replicas.P ι k θ.1)
        ((g θ : ℂ)⁻¹ • Replicas.P ι k θ.1)).PosSemidef := fun θ =>
      (posSemidef_P θ.1).fromBlocks_smul_inv (𝕜 := ℂ) (hpos θ)
    rw [he]
    refine (PosSemidef.of_integral ?_ hpt).smul (Nat.cast_nonneg (α := ℂ) _)
    rintro (i | i) (j | j)
    · simpa using integrable_Q_apply hg i j
    · simpa using integrable_Q_apply hP1 i j
    · simpa using integrable_Q_apply hP1 i j
    · simpa [Complex.ofReal_inv] using integrable_Q_apply hg' i j
  have hcomp := (isStarProjection_projS (ι := ι) (k := k)).one_sub.nonneg.posSemidef
    |>.fromBlocks_smul_inv hc
  have hsum := hblock.add hcomp
  rw [fromBlocks_add, add_sub_cancel] at hsum
  have hA := posDef_Q_add (k := k) hg hpos hc
  let := hA.isUnit.invertible
  have h := (PosDef.fromBlocks₁₁ (1 : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ)
    (Q ι k g⁻¹ + (c : ℂ)⁻¹ • (1 - Replicas.projS ι k)) hA).mp (by simpa using hsum)
  rw [Matrix.le_iff]
  simpa using h

omit [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] in
theorem trace_vecMulVec_mul (v : Replicas.Config ι k → ℂ)
    (M : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ) :
    (vecMulVec v (star v) * M).trace = star v ⬝ᵥ M *ᵥ v := by
  rw [vecMulVec_mul, trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec]

/-- D7.19 Step `transport:log-jensen`. `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ` is a unital positive map
from functions to operators on `𝒮_k`, and for positive bounded `f` bounded away from `0`:
`𝒬_k(f)⁻¹ ≤ 𝒬_k(f⁻¹)` and `log 𝒬_k(f) ≥ 𝒬_k(log f)`. The logarithm is operator monotone on
positive definite operators.
(An operator `X` on `𝒮_k` is written `X + (1 - Π_k)` on `𝒱^{⊗k}`: extended by the identity on
`𝒮_k^⊥`.) -/
theorem step_7_19 :
    Q ι k 1 = Replicas.projS ι k ∧
    (∀ f : Replicas.Sphere ι → ℝ, Continuous f → 0 ≤ f → (Q ι k f).PosSemidef) ∧
    (∀ f : Replicas.Sphere ι → ℝ, Continuous f → (∀ θ, 0 < f θ) →
      (Q ι k f + (1 - Replicas.projS ι k))⁻¹ ≤ Q ι k f⁻¹ + (1 - Replicas.projS ι k) ∧
      Q ι k (Real.log ∘ f) ≤ CFC.log (Q ι k f + (1 - Replicas.projS ι k))) ∧
    ∀ A B : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ, A.PosDef → A ≤ B →
      CFC.log A ≤ CFC.log B := by
  -- D7.19.1
  have h1 : Q ι k 1 = Replicas.projS ι k :=
    (Q_const ι k 1).trans (by rw [Complex.ofReal_one, one_smul])
  refine ⟨h1, fun f hf h0 => posSemidef_Q hf h0, fun f hf hpos => ?_,
    -- D7.19.5
    fun A B hA hAB => CFC.log_le_log hAB hA.isStrictlyPositive⟩
  set X := Q ι k f + (1 - Replicas.projS ι k) with hXdef
  have hX : X.PosDef := by simpa using posDef_Q_add (k := k) hf hpos one_pos
  -- D7.19.2
  have h2 : X⁻¹ ≤ Q ι k f⁻¹ + (1 - Replicas.projS ι k) := by
    simpa using Q_add_inv_le (k := k) hf hpos one_pos
  refine ⟨h2, ?_⟩
  -- D7.19.3
  have h3 : ∀ t : ℝ, 0 < t → (X + t • 1)⁻¹ ≤ Q ι k (fun θ => (f θ + t)⁻¹) +
      ((1 + t : ℝ) : ℂ)⁻¹ • (1 - Replicas.projS ι k) := fun t ht => by
    have he : X + t • 1 = Q ι k (f + fun _ => t) +
        ((1 + t : ℝ) : ℂ) • (1 - Replicas.projS ι k) := by
      rw [Q_add hf continuous_const, Q_const, hXdef, ← Complex.coe_smul]
      push_cast
      module
    rw [he]
    exact Q_add_inv_le (k := k) (hf.add continuous_const) (fun θ => add_pos (hpos θ) ht)
      (by linarith)
  -- D7.19.4
  have hlogf : Continuous (Real.log ∘ f) :=
    Real.continuousOn_log.comp_continuous hf fun θ => (hpos θ).ne'
  have hL : (CFC.log X).IsHermitian := cfc_predicate _ _
  rw [Matrix.le_iff]
  refine .of_dotProduct_mulVec_nonneg (hL.sub (isHermitian_Q _)) fun v => ?_
  set ν := Replicas.μ ι k (vecMulVec v (star v))
  have hqf : ∀ g : Replicas.Sphere ι → ℝ, Continuous g →
      star v ⬝ᵥ Q ι k g *ᵥ v = ((∫ θ, g θ ∂ν : ℝ) : ℂ) := fun g hg => by
    rw [← trace_vecMulVec_mul, trace_mul_Q (posSemidef_vecMulVec_self_star v) hg,
      integral_complex_ofReal]
  obtain ⟨hint, hlog⟩ := hX.re_dotProduct_cfc_log_eq_integral v
  have hreal : star v ⬝ᵥ CFC.log X *ᵥ v =
      ((RCLike.re (star v ⬝ᵥ cfc Real.log X *ᵥ v) : ℝ) : ℂ) := by
    change star v ⬝ᵥ cfc Real.log X *ᵥ v = _
    rw [hX.isHermitian.dotProduct_cfc_mulVec, RCLike.ofReal_re]
    rfl
  rw [sub_mulVec, dotProduct_sub, hreal, hqf _ hlogf, ← Complex.ofReal_sub, Complex.zero_le_real,
    sub_nonneg]
  obtain ⟨θ₀, -, hθ₀⟩ := isCompact_univ.exists_isMinOn
    ⟨Replicas.sphereMap ι (Classical.arbitrary _) 1, mem_univ _⟩ hf.continuousOn
  obtain ⟨θ₁, -, hθ₁⟩ := isCompact_univ.exists_isMaxOn
    ⟨Replicas.sphereMap ι (Classical.arbitrary _) 1, mem_univ _⟩ hf.continuousOn
  have hF : Integrable (Function.uncurry fun (θ : Replicas.Sphere ι) (t : ℝ) =>
      (1 + t)⁻¹ - (f θ + t)⁻¹) (ν.prod (volume.restrict (Ioi 0))) := by
    refine (((Real.integrableOn_inv_sub_inv (hpos θ₀)).abs.add
      (Real.integrableOn_inv_sub_inv (hpos θ₁)).abs).comp_snd ν).mono'
      ((measurable_const.add measurable_snd).inv.sub
        ((hf.measurable.comp measurable_fst).add measurable_snd).inv).aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
      with p (hp : 0 < p.2)
    rw [Real.norm_eq_abs]
    exact Real.abs_inv_sub_inv_le hp.le (hpos θ₀) (hθ₀ (mem_univ p.1)) (hθ₁ (mem_univ p.1))
  calc ∫ θ, (Real.log ∘ f) θ ∂ν = ∫ θ, (∫ t in Ioi 0, ((1 + t)⁻¹ - (f θ + t)⁻¹)) ∂ν :=
        integral_congr_ae (Eventually.of_forall fun θ => Real.log_eq_integral_inv_sub_inv (hpos θ))
    _ = ∫ t in Ioi 0, ∫ θ, ((1 + t)⁻¹ - (f θ + t)⁻¹) ∂ν := integral_integral_swap hF
    _ ≤ ∫ t in Ioi 0, RCLike.re (star v ⬝ᵥ cfc (fun x : ℝ => (1 + t)⁻¹ - (x + t)⁻¹) X *ᵥ v) := by
      refine setIntegral_mono_on hF.integral_prod_right hint measurableSet_Ioi fun t ht => ?_
      have ht : 0 < t := ht
      have hk : Continuous fun θ => (1 + t)⁻¹ - (f θ + t)⁻¹ :=
        continuous_const.sub ((hf.add continuous_const).inv₀ fun θ => (add_pos (hpos θ) ht).ne')
      have hdiff : (cfc (fun x : ℝ => (1 + t)⁻¹ - (x + t)⁻¹) X -
          Q ι k fun θ => (1 + t)⁻¹ - (f θ + t)⁻¹).PosSemidef := by
        have hQk : Q ι k (fun θ => (1 + t)⁻¹ - (f θ + t)⁻¹) =
            (((1 + t)⁻¹ : ℝ) : ℂ) • Replicas.projS ι k - Q ι k (fun θ => (f θ + t)⁻¹) := by
          have h := Q_sub (k := k) (f := fun _ => (1 + t)⁻¹) (g := fun θ => (f θ + t)⁻¹)
            continuous_const ((hf.add continuous_const).inv₀ fun θ => (add_pos (hpos θ) ht).ne')
          rw [Q_const] at h
          exact h
        have e : cfc (fun x : ℝ => (1 + t)⁻¹ - (x + t)⁻¹) X -
            Q ι k (fun θ => (1 + t)⁻¹ - (f θ + t)⁻¹) = (Q ι k (fun θ => (f θ + t)⁻¹) +
              ((1 + t : ℝ) : ℂ)⁻¹ • (1 - Replicas.projS ι k)) - (X + t • 1)⁻¹ := by
          rw [hX.cfc_inv_one_add_sub_inv_add ht.le, hQk, ← Complex.coe_smul]
          push_cast
          module
        rw [e]
        exact Matrix.le_iff.mp (h3 t ht)
      have h := Complex.nonneg_iff.mp (hdiff.dotProduct_mulVec_nonneg v)
      rw [sub_mulVec, dotProduct_sub, hqf _ hk, Complex.sub_re, Complex.ofReal_re] at h
      change _ ≤ Complex.re _
      linarith [h.1]
    _ = RCLike.re (star v ⬝ᵥ cfc Real.log X *ᵥ v) := hlog.symm

end AreaLaw.Transport
