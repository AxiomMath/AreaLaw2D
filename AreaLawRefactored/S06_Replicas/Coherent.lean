import AreaLawRefactored.S06_Replicas.InjectionAverage
import AreaLawRefactored.S06_Replicas.Ported.UniformHusimi
import AreaLawRefactored.S06_Replicas.Ported.CoherentSymbol
import AreaLawRefactored.S06_Replicas.Ported.MarkedStar

/-!
# §6 The coherent measure (D6.11, D6.14, D6.15)

Digest `digest/06-replicas.md` D6.11, D6.14, D6.15; paper `05-replicas.tex` lines 596–811.
-/

namespace AreaLaw.Replicas

open Matrix MeasureTheory PermutationRepresentation Finset
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

variable {I : Type*} [Fintype I] [DecidableEq I] (ι : I → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] (k : ℕ)

set_option hygiene false in
/-- The one-copy basis `(f : I) → ι f` of `𝒱`. -/
local notation "Ω" => (f : I) → ι f

/-! ## D6.11 The coherent probability measure -/

/-- D6.11. The unit sphere of `𝒱 = ⨂_f ℂ^{ι f}`. -/
abbrev Sphere := ↥(TensorPower.unitSphere : Set (Ω → ℂ))

/-- D6.11. The coherent projector `P_{θ,k} = |θ^{⊗k}⟩⟨θ^{⊗k}|`. -/
abbrev P (θ : Ω → ℂ) : Matrix (Config ι k) (Config ι k) ℂ :=
  TensorPower.coherentProj k θ

/-- D6.11. The unit vector `θ = U e_a`. -/
def sphereMap (a : Ω) (V : unitaryGroup Ω ℂ) : Sphere ι :=
  ⟨(V : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1, TensorPower.unitary_mulVec_single_mem_unitSphere V a⟩

theorem continuous_sphereMap (a : Ω) : Continuous (sphereMap ι a) :=
  (TensorPower.continuous_unitary_mulVec_single a).subtype_mk _

/-- D6.11. A unitary `V` rotates the sphere, `θ ↦ V θ`. -/
def rotate (V : unitaryGroup Ω ℂ) (θ : Sphere ι) : Sphere ι :=
  ⟨(V : Matrix Ω Ω ℂ) *ᵥ θ.1, by
    have h := θ.2
    simp only [TensorPower.unitSphere, Set.mem_ofPred_eq] at h ⊢
    rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp V.2, one_mulVec, dotProduct_comm, h]⟩

theorem rotate_sphereMap (V W : unitaryGroup Ω ℂ) (a : Ω) :
    rotate ι V (sphereMap ι a W) = sphereMap ι a (V * W) := by
  apply Subtype.ext
  exact mulVec_mulVec _ _ _

theorem continuous_rotate (V : unitaryGroup Ω ℂ) : Continuous (rotate ι V) :=
  (continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _

/-- D6.1. `Π_k` is the symmetric projector of the whole-copy permutations. -/
theorem projS_eq : projS ι k = symProj (TensorPower.copyPerm Ω k) := by
  rw [projS, copyPerm, TensorPower.subsystemPerm_univ]

/-- D6.1. `U(π)` is the permutation operator of the whole-copy permutations. -/
theorem U_univ_eq (π : Equiv.Perm (Fin k)) :
    U ι k Finset.univ π = permOp (TensorPower.copyPerm Ω k) π := by
  rw [U, copyPerm, TensorPower.subsystemPerm_univ]

/-- D6.1. `Tr Π_k = D_k`. -/
theorem trace_projS : (projS ι k).trace = D ι k := by
  have h : LinearMap.IsProj (S ι k) (projS ι k).toLin' :=
    ⟨fun x => symProj_mulVec_mem _ x, fun x hx => symProj_mulVec_of_mem _ hx⟩
  rw [← Matrix.trace_toLin'_eq, h.trace, D]

variable [∀ f, Nonempty (ι f)]

/-- D6.11. `dθ`, the image of the Haar probability measure under `U ↦ U e_a`. -/
noncomputable def dθ : Measure (Sphere ι) :=
  (unitaryHaar Ω).map (sphereMap ι (Classical.arbitrary _))

omit [∀ f, Nonempty (ι f)] in
/-- The Haar measure is right invariant (a compact group is unimodular). -/
theorem map_mul_right_unitaryHaar (W : unitaryGroup Ω ℂ) :
    (unitaryHaar Ω).map (· * W) = unitaryHaar Ω := by
  have := Measure.isProbabilityMeasure_map (μ := unitaryHaar Ω)
    (measurable_mul_const W).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The permutation unitary of the transposition `(a b)`. -/
private def swapUnitary (a b : Ω) : unitaryGroup Ω ℂ :=
  ⟨(Equiv.swap a b).permMatrix ℂ, by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix,
      ← permMatrix_mul, inv_mul_cancel, permMatrix_one]⟩

/-- D6.11. `dθ` does not depend on the base point `a` of `θ = U e_a`. -/
theorem map_sphereMap (a : Ω) : (unitaryHaar Ω).map (sphereMap ι a) = dθ ι := by
  set b : Ω := Classical.arbitrary _
  have hcomp : sphereMap ι b = sphereMap ι a ∘ (· * swapUnitary ι a b) := by
    have hW : (Equiv.swap a b).permMatrix ℂ *ᵥ Pi.single a 1 = Pi.single b 1 := by
      ext i
      simp [mulVec, dotProduct, Equiv.Perm.permMatrix, Pi.single_apply, Equiv.swap_apply_eq_iff]
    funext V
    apply Subtype.ext
    change (V : Matrix Ω Ω ℂ) *ᵥ Pi.single b 1 =
      ((V : Matrix Ω Ω ℂ) * (Equiv.swap a b).permMatrix ℂ) *ᵥ Pi.single a 1
    rw [← mulVec_mulVec, hW]
  rw [dθ, hcomp, ← Measure.map_map (continuous_sphereMap ι a).measurable
    (measurable_mul_const _), map_mul_right_unitaryHaar]

instance : IsProbabilityMeasure (dθ ι) :=
  Measure.isProbabilityMeasure_map (continuous_sphereMap ι _).aemeasurable

/-- D6.11. `dθ` is unitarily invariant. -/
theorem map_rotate_dθ (V : unitaryGroup Ω ℂ) : (dθ ι).map (rotate ι V) = dθ ι := by
  have h : rotate ι V ∘ sphereMap ι (Classical.arbitrary _) =
      sphereMap ι (Classical.arbitrary _) ∘ (V * ·) := funext fun W => rotate_sphereMap ι V W _
  rw [dθ, Measure.map_map (continuous_rotate ι V).measurable
    (continuous_sphereMap ι _).measurable, h, ← Measure.map_map
    (continuous_sphereMap ι _).measurable (measurable_const_mul V), map_mul_left_eq_self]

omit [Fintype I] [DecidableEq I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)] in
theorem continuous_P_apply (x y : Config ι k) :
    Continuous fun θ : Ω → ℂ => P ι k θ x y := by
  simp only [P, TensorPower.coherentProj, vecMulVec_apply, TensorPower.tensorVec, Pi.star_apply]
  fun_prop

/-- D6.11 `replicas:resolution`. `∫ P_{θ,k} dθ = D_k⁻¹ Π_k`. -/
theorem eq_replicas_resolution :
    Matrix.of (fun x y => ∫ θ, P ι k θ.1 x y ∂dθ ι) = ((D ι k : ℂ))⁻¹ • projS ι k := by
  set a : Ω := Classical.arbitrary _
  ext x y
  have h := integral_map (μ := unitaryHaar Ω) (continuous_sphereMap ι a).aemeasurable
    ((continuous_P_apply ι k x y).comp continuous_subtype_val).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [Matrix.of_apply, dθ, h, ← trace_projS, projS_eq, ← TensorPower.unitaryTwirl_coherentProj a]
  simp only [sphereMap, P, TensorPower.unitaryTwirl, TensorPower.coherentProj_mulVec]

instance : CompactSpace (Sphere ι) :=
  isCompact_iff_compactSpace.mp TensorPower.isCompact_unitSphere

omit [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] in
/-- `Tr(σ P_{θ,k}) = ⟨θ^{⊗k}, σ θ^{⊗k}⟩ ≥ 0` for `σ ≥ 0`. -/
theorem trace_mul_P_nonneg {σ : Matrix (Config ι k) (Config ι k) ℂ} (hσ : σ.PosSemidef)
    (θ : Ω → ℂ) : 0 ≤ (σ * P ι k θ).trace := by
  rw [P, TensorPower.coherentProj, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  exact hσ.dotProduct_mulVec_nonneg _

omit [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] in
theorem continuous_trace_mul_P (σ : Matrix (Config ι k) (Config ι k) ℂ) :
    Continuous fun θ : Ω → ℂ => (σ * P ι k θ).trace := by
  simp only [trace, diag_apply, mul_apply]
  exact continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
    continuous_const.mul (continuous_P_apply ι k y x)

/-- D6.11 `replicas:husimi`. The Husimi measure `dμ_σ(θ) = D_k Tr(σ P_{θ,k}) dθ`. -/
noncomputable def μ (σ : Matrix (Config ι k) (Config ι k) ℂ) : Measure (Sphere ι) :=
  (dθ ι).withDensity fun θ => ENNReal.ofReal (D ι k * (σ * P ι k θ.1).trace.re)

instance (σ : Matrix (Config ι k) (Config ι k) ℂ) : IsFiniteMeasure (μ ι k σ) :=
  isFiniteMeasure_withDensity_ofReal (((continuous_const.mul (Complex.continuous_re.comp
    ((continuous_trace_mul_P ι k σ).comp continuous_subtype_val)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

/-- D6.11. The Husimi integral is the coherent integral `D_k ∫ Tr(σ P_{U e_a,k}) φ(U e_a) dU`
over the Haar measure, for every base point `a`. -/
theorem coherentIntegral_eq_integral_μ {σ : Matrix (Config ι k) (Config ι k) ℂ}
    (hσ : σ.PosSemidef) (a : Ω) {φ : (Ω → ℂ) → ℂ}
    (hφ : ContinuousOn φ TensorPower.unitSphere) :
    TensorPower.coherentIntegral a σ φ = ∫ θ, φ θ.1 ∂μ ι k σ := by
  have hφc : Continuous fun θ : Sphere ι => φ θ.1 := hφ.comp_continuous continuous_subtype_val
    fun θ => θ.2
  have hd : Continuous fun θ : Sphere ι => (D ι k : ℝ) * (σ * P ι k θ.1).trace.re :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_trace_mul_P ι k σ).comp continuous_subtype_val))
  have hreal : ∀ θ : Ω → ℂ, (((σ * P ι k θ).trace.re : ℝ) : ℂ) = (σ * P ι k θ).trace := fun θ =>
    Complex.ext rfl (by simp [(Complex.nonneg_iff.mp (trace_mul_P_nonneg ι k hσ θ)).2])
  have hm := integral_map (μ := unitaryHaar Ω) (continuous_sphereMap ι a).aemeasurable
    (f := fun θ : Sphere ι => (ENNReal.ofReal (D ι k * (σ * P ι k θ.1).trace.re)).toReal • φ θ.1)
    (hd.measurable.ennreal_ofReal.ennreal_toReal.smul hφc.measurable).aestronglyMeasurable
  rw [μ, integral_withDensity_eq_integral_toReal_smul hd.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← map_sphereMap ι a, hm,
    TensorPower.coherentIntegral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only [sphereMap, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _)
    (Complex.nonneg_iff.mp (trace_mul_P_nonneg ι k hσ _)).1), Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_natCast, hreal, ← projS_eq, trace_projS]
  ring

/-- D6.11 `replicas:husimi`. For a density `σ` on `𝒮_k`, `μ_σ` is a probability measure:
`∫ dμ_σ = Tr σ Π_k = 1`. -/
theorem eq_replicas_husimi {σ : Matrix (Config ι k) (Config ι k) ℂ} (hσp : σ.PosSemidef)
    (hσt : σ.trace = 1) (hσ : ∀ π, U ι k Finset.univ π * σ = σ) :
    IsProbabilityMeasure (μ ι k σ) := by
  have hσ' : ∀ π, permOp (TensorPower.copyPerm Ω k) π * σ = σ := fun π => by
    rw [← U_univ_eq]; exact hσ π
  have h := coherentIntegral_eq_integral_μ ι k hσp (Classical.arbitrary _)
    (φ := fun _ => 1) continuousOn_const
  rw [TensorPower.coherentIntegral_one hσ', hσt, integral_const, Complex.real_smul,
    mul_one] at h
  have h1 : (μ ι k σ).real Set.univ = 1 := by exact_mod_cast h.symm
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def, h1, ENNReal.ofReal_one]

/-- The uniform trace limit of a sequence with coherent symbol `f`, against `μ_σ`:
`Tr σ X_k - ∫ f dμ_σ → 0` uniformly in densities `σ` on `𝒮_k`. -/
theorem eventually_norm_trace_sub_integral_μ_le
    {X : ∀ k, Matrix (Config ι k) (Config ι k) ℂ} {f : (Ω → ℂ) → ℂ}
    (hX : TensorPower.HasCoherentSymbol X f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ σ : Matrix (Config ι k) (Config ι k) ℂ, σ.PosSemidef →
      σ.trace = 1 → (∀ π, U ι k Finset.univ π * σ = σ) →
        ‖(σ * X k).trace - ∫ θ, f θ.1 ∂μ ι k σ‖ ≤ ε := by
  filter_upwards [hX.eventually_norm_trace_sub_le hε] with k hk σ hσp hσt hσ
  rw [← coherentIntegral_eq_integral_μ ι k hσp (Classical.arbitrary _) hX.continuousOn]
  exact hk _ σ hσp hσt fun π => by rw [← U_univ_eq]; exact hσ π

/-! ## D6.14 The coherent measure on a fixed number of copies -/

variable {ι k} {m : ℕ}

omit [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] in
/-- `⟨θ^{⊗m}, G θ^{⊗m}⟩ = Tr(G P_{θ,m})`. -/
theorem inner_tensorVec_eq_trace (G : Matrix (Config ι m) (Config ι m) ℂ) (θ : Ω → ℂ) :
    star (TensorPower.tensorVec m θ) ⬝ᵥ (G *ᵥ TensorPower.tensorVec m θ) =
      (G * P ι m θ).trace := by
  rw [P, TensorPower.coherentProj, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

omit [Fintype I] [DecidableEq I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)] in
/-- D6.14. `σ ⊗ G` on `k + m` copies is the ported `copyKronecker`. -/
theorem tensorCopies_eq (σ : Matrix (Config ι k) (Config ι k) ℂ)
    (G : Matrix (Config ι m) (Config ι m) ℂ) :
    tensorCopies σ G = TensorPower.copyKronecker σ G := rfl

omit [DecidableEq I] [∀ f, Fintype (ι f)] [∀ f, Nonempty (ι f)] in
/-- D6.14. `𝒯_{k,m}` is the ported injection average. -/
theorem T_eq_injectionAverage (G : Matrix (Config ι m) (Config ι m) ℂ) :
    T k m G = TensorPower.injectionAverage k m G := by
  rw [T, TensorPower.injectionAverage]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  ext x y
  rw [TensorPower.placeOp_apply, embed]
  have : (TensorPower.placeSplit e x).2 = (TensorPower.placeSplit e y).2 ↔
      ∀ j, (∀ a, e a ≠ j) → x j = y j := by
    refine ⟨fun h j hj => congrFun h ⟨j, fun ⟨a, ha⟩ => hj a ha⟩, fun h => funext fun j => ?_⟩
    exact h j fun a ha => j.2 ⟨a, ha⟩
  by_cases h : ∀ j, (∀ a, e a ≠ j) → x j = y j
  · rw [if_pos h, if_pos (this.mpr h), mul_one]
  · rw [if_neg h, if_neg (fun h' => h (this.mp h')), mul_zero]

omit [∀ f, Nonempty (ι f)] in
/-- D6.1. `𝒮_k` is the invariant subspace of the whole-copy permutations. -/
theorem S_eq : S ι k = invariantSubspace (TensorPower.copyPerm Ω k) := by
  rw [S, copyPerm, TensorPower.subsystemPerm_univ]

omit [∀ f, Nonempty (ι f)] in
/-- D6.14. `𝒯_{k,m}(G)` commutes with every `U(π)`. -/
theorem commute_U_T (π : Equiv.Perm (Fin k)) (G : Matrix (Config ι m) (Config ι m) ℂ) :
    Commute (U ι k Finset.univ π) (T k m G) := by
  rw [U_univ_eq, T_eq_injectionAverage]
  exact TensorPower.permOp_mul_injectionAverage π G

omit [∀ f, Nonempty (ι f)] in
/-- D6.14. `𝒯_{k,m}(G)` preserves `𝒮_k`. -/
theorem T_mulVec_mem_S (G : Matrix (Config ι m) (Config ι m) ℂ) {v : Config ι k → ℂ}
    (hv : v ∈ S ι k) : T k m G *ᵥ v ∈ S ι k := by
  rw [S_eq, mem_invariantSubspace] at hv ⊢
  intro π
  rw [mulVec_mulVec, ← U_univ_eq, (commute_U_T π G).eq, ← mulVec_mulVec, U_univ_eq, hv π]

/-- D6.14. The `m`-copy marginal `σ^{(m)}`: the partial trace of `σ` over the copies
`m, …, k - 1`. -/
noncomputable def marginal (hm : m ≤ k) (σ : Matrix (Config ι k) (Config ι k) ℂ) :
    Matrix (Config ι m) (Config ι m) ℂ :=
  (reindex (TensorPower.placeSplit (Fin.castLEEmb hm))
    (TensorPower.placeSplit (Fin.castLEEmb hm)) σ).traceRight

omit [∀ f, Nonempty (ι f)] in
/-- `Tr σ G^{(e)} = Tr σ^{(m)} G` for the first `m` copies. -/
theorem trace_mul_placeOp_first (hm : m ≤ k) (σ : Matrix (Config ι k) (Config ι k) ℂ)
    (G : Matrix (Config ι m) (Config ι m) ℂ) :
    (σ * TensorPower.placeOp (Fin.castLEEmb hm) G).trace = (marginal hm σ * G).trace := by
  set e : Config ι k ≃ _ := TensorPower.placeSplit (Fin.castLEEmb hm)
  rw [marginal, ← trace_mul_kron_one_right, TensorPower.placeOp]
  rw [← Matrix.trace_submatrix (σ * reindex e.symm e.symm _) e.symm]
  simp only [reindex_apply, Equiv.symm_symm]
  rw [← submatrix_mul_equiv _ _ _ e.symm, submatrix_submatrix, Equiv.self_comp_symm,
    submatrix_id_id]

omit [∀ f, Nonempty (ι f)] in
/-- A symmetric `σ` sees every placement of `G` alike. -/
theorem trace_mul_placeOp_eq {σ : Matrix (Config ι k) (Config ι k) ℂ} (hσp : σ.PosSemidef)
    (hσ : ∀ π, U ι k Finset.univ π * σ = σ) (e e' : Fin m ↪ Fin k)
    (G : Matrix (Config ι m) (Config ι m) ℂ) :
    (σ * TensorPower.placeOp e' G).trace = (σ * TensorPower.placeOp e G).trace := by
  classical
  let r : {x // x ∈ Set.range e} ≃ {x // x ∈ Set.range e'} :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective e' e'.injective)
  set π : Equiv.Perm (Fin k) := r.extendSubtype
  have hπ : e.trans π.toEmbedding = e' := by
    ext j
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, π,
      Equiv.extendSubtype_apply_of_mem r _ ⟨j, rfl⟩, r, Equiv.trans_apply]
    rw [Equiv.ofInjective_symm_apply]
    rfl
  have hl : ∀ g, permOp (TensorPower.copyPerm Ω k) g * σ = σ := fun g => by
    rw [← U_univ_eq]; exact hσ g
  have hr : ∀ g, σ * permOp (TensorPower.copyPerm Ω k) g = σ := fun g => by
    have := congrArg conjTranspose (hl g⁻¹)
    rwa [conjTranspose_mul, hσp.isHermitian.eq, conjTranspose_permOp, inv_inv] at this
  rw [← hπ, TensorPower.placeOp_trans_perm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hr,
    trace_mul_cycle, hl]

omit [∀ f, Nonempty (ι f)] in
/-- D6.14. For a density `σ` on `𝒮_k` and `k ≥ m`, `Tr σ 𝒯_{k,m}(G) = Tr σ^{(m)} G`. -/
theorem trace_mul_T_eq_marginal (hm : m ≤ k) {σ : Matrix (Config ι k) (Config ι k) ℂ}
    (hσp : σ.PosSemidef) (hσ : ∀ π, U ι k Finset.univ π * σ = σ)
    (G : Matrix (Config ι m) (Config ι m) ℂ) :
    (σ * T k m G).trace = (marginal hm σ * G).trace := by
  have : Nonempty (Fin m ↪ Fin k) := ⟨Fin.castLEEmb hm⟩
  have hN : (Fintype.card (Fin m ↪ Fin k) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [T_eq_injectionAverage, TensorPower.injectionAverage, Matrix.mul_smul, trace_smul,
    Matrix.mul_sum, trace_sum, Finset.sum_congr rfl fun e _ =>
      trace_mul_placeOp_eq hσp hσ (Fin.castLEEmb hm) e G, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul,
    trace_mul_placeOp_first]

/-- D6.14 `replicas:finite-husimi`.
`∫ ⟨θ^{⊗m}, G θ^{⊗m}⟩ dμ_σ = D_k / D_{k+m} Tr[(σ ⊗ G) Π_{k+m}]`. -/
theorem eq_replicas_finite_husimi {σ : Matrix (Config ι k) (Config ι k) ℂ}
    (hσ : σ.PosSemidef) (G : Matrix (Config ι m) (Config ι m) ℂ) :
    ∫ θ, star (TensorPower.tensorVec m θ.1) ⬝ᵥ (G *ᵥ TensorPower.tensorVec m θ.1) ∂μ ι k σ =
      (D ι k : ℂ) / D ι (k + m) * (tensorCopies σ G * projS ι (k + m)).trace := by
  simp_rw [inner_tensorVec_eq_trace]
  -- D6.14.1 `P_{θ,k} ⊗ P_{θ,m} = P_{θ,k+m}` and `replicas:resolution` at `k + m`
  rw [← coherentIntegral_eq_integral_μ ι k hσ (Classical.arbitrary _)
    (φ := fun θ => (G * P ι m θ).trace) (TensorPower.continuous_coherentExpect G).continuousOn,
    TensorPower.coherentIntegral_trace_coherentProj, ← projS_eq, ← projS_eq, trace_projS,
    trace_projS, tensorCopies_eq, TensorPower.copyKronecker]
  ring

/-- D6.14 `replicas:uniform-husimi`. For a density `σ` on `𝒮_k`, `k ≥ 1`:
`|Tr σ 𝒯_{k,m}(G) - ∫ ⟨θ^{⊗m}, G θ^{⊗m}⟩ dμ_σ| ≤ C_{d,m} ‖G‖ / k`,
`C_{d,m} = 4 m² (1 + d^m)²`, `d = dim 𝒱`, uniformly in `σ`. -/
theorem eq_replicas_uniform_husimi (hk : 0 < k) {σ : Matrix (Config ι k) (Config ι k) ℂ}
    (hσp : σ.PosSemidef) (hσt : σ.trace = 1) (hσ : ∀ π, U ι k Finset.univ π * σ = σ)
    (G : Matrix (Config ι m) (Config ι m) ℂ) :
    ‖(σ * T k m G).trace -
        ∫ θ, star (TensorPower.tensorVec m θ.1) ⬝ᵥ (G *ᵥ TensorPower.tensorVec m θ.1)
          ∂μ ι k σ‖ ≤
      4 * m ^ 2 * (1 + (Fintype.card Ω : ℝ) ^ m) ^ 2 * ‖G‖ / k := by
  simp_rw [inner_tensorVec_eq_trace]
  -- D6.14.2–D6.14.5 good permutations, normal form, value, rest
  rw [← coherentIntegral_eq_integral_μ ι k hσp (Classical.arbitrary _)
    (φ := fun θ => (G * P ι m θ).trace) (TensorPower.continuous_coherentExpect G).continuousOn,
    T_eq_injectionAverage]
  exact TensorPower.norm_trace_mul_injectionAverage_sub_coherentIntegral_le hk _ hσp hσt
    (fun π => by rw [← U_univ_eq]; exact hσ π) G

/-! ## D6.15 Products after compression -/

variable (k) in
/-- D6.15. `𝒯_k(B) = (k!)⁻¹ ∑_π U(π) B U(π)^†`. -/
noncomputable def Tk (B : Matrix (Config ι k) (Config ι k) ℂ) :
    Matrix (Config ι k) (Config ι k) ℂ :=
  ((k.factorial : ℕ) : ℂ)⁻¹ • ∑ π, U ι k Finset.univ π * B * (U ι k Finset.univ π)ᴴ

omit [∀ f, Nonempty (ι f)] in
/-- D6.15. `𝒯_k(B)` commutes with every `U(π)`. -/
theorem commute_U_Tk (σ : Equiv.Perm (Fin k)) (B : Matrix (Config ι k) (Config ι k) ℂ) :
    Commute (U ι k Finset.univ σ) (Tk k B) := by
  simp only [Commute, SemiconjBy, Tk, U, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul, conjTranspose_permOp]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun π => ?_
  simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev, Matrix.mul_assoc,
    permOp_inv_mul_self, Matrix.mul_one]

omit [∀ f, Nonempty (ι f)] in
/-- D6.15. `𝒯_k(B)` preserves `𝒮_k`. -/
theorem Tk_mulVec_mem_S (B : Matrix (Config ι k) (Config ι k) ℂ) {v : Config ι k → ℂ}
    (hv : v ∈ S ι k) : Tk k B *ᵥ v ∈ S ι k := by
  rw [S_eq, mem_invariantSubspace] at hv ⊢
  intro π
  rw [mulVec_mulVec, ← U_univ_eq, (commute_U_Tk π B).eq, ← mulVec_mulVec, U_univ_eq, hv π]

omit [∀ f, Nonempty (ι f)] in
/-- D6.15.1. On `𝒮_k`, `Π_k B Π_k = 𝒯_k(B)`. -/
theorem projS_mul_mul_projS_mulVec (B : Matrix (Config ι k) (Config ι k) ℂ)
    {z : Config ι k → ℂ} (hz : z ∈ S ι k) :
    (projS ι k * B * projS ι k) *ᵥ z = Tk k B *ᵥ z := by
  have hz' : ∀ π, permOp (TensorPower.copyPerm Ω k) π *ᵥ z = z := by
    have := hz; rwa [S_eq, mem_invariantSubspace] at this
  have hP : projS ι k *ᵥ z = z := by
    rw [projS_eq]; exact symProj_mulVec_of_mem _ (S_eq (ι := ι) (k := k) ▸ hz)
  have hPU : projS ι k = ((k.factorial : ℕ) : ℂ)⁻¹ • ∑ π, U ι k Finset.univ π := by
    rw [projS_eq, symProj, Fintype.card_perm, Fintype.card_fin]
    simp only [U_univ_eq]
  rw [← mulVec_mulVec, hP, ← mulVec_mulVec, hPU, Tk, smul_mulVec, smul_mulVec, sum_mulVec,
    sum_mulVec]
  refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
  simp only [← mulVec_mulVec]
  rw [U_univ_eq, conjTranspose_permOp, hz']

section Words

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)

/-- D6.15. The letters of a polynomial word (D6.13): a marked operator `a`, or a star `J_Q`. -/
abbrev Letter := Matrix ((v : V) → Fin (n v)) ((v : V) → Fin (n v)) ℂ ⊕ Finset V

variable {n}

/-- D6.15. A polynomial word on `k + 1` copies with the marked copy last: a marked operator `a`
acts on the marked copy, a star is `J_{Q,k+1} = (k+1)⁻¹ ∑_{j<k} U_Q((j k))`. -/
noncomputable def word (k : ℕ) :
    FreeAlgebra ℂ (Letter n) →ₐ[ℂ] Matrix (Config (fun v => Fin (n v)) (k + 1))
      (Config (fun v => Fin (n v)) (k + 1)) ℂ :=
  FreeAlgebra.lift ℂ (Sum.elim (TensorPower.siteOp (Fin.last k))
    fun Q => starOp (copyPerm (fun v => Fin (n v)) (k + 1) Q))

/-- D6.15. The operator symbol of a word on the centre, in operator order: `a ↦ a` and
`J_Q ↦ ρ_Q(θ) ⊗ 1`, with `ρ_Q(θ)` the marginal of `|θ⟩⟨θ|` on `Q`. -/
noncomputable def wordSymbol (θ : ((v : V) → Fin (n v)) → ℂ) :
    FreeAlgebra ℂ (Letter n) →ₐ[ℂ] Matrix ((v : V) → Fin (n v)) ((v : V) → Fin (n v)) ℂ :=
  FreeAlgebra.lift ℂ (Sum.elim id fun Q => TensorPower.margLift Q θ)

/-- D6.15. The scalar symbol `⟨θ, F(θ) θ⟩` of the compressed word. -/
noncomputable def scalarSymbol (w : FreeAlgebra ℂ (Letter n))
    (θ : ((v : V) → Fin (n v)) → ℂ) : ℂ :=
  star θ ⬝ᵥ (wordSymbol θ w *ᵥ θ)

/-- D6.15.3–D6.15.5. A word has the marked symbol `wordSymbol`: stars contract to `ρ_Q`,
products multiply the symbols on the centre. -/
theorem hasMarkedSymbol_word (w : FreeAlgebra ℂ (Letter n)) :
    TensorPower.HasMarkedSymbol (fun k => word k w) (fun θ => wordSymbol θ w) := by
  induction w using FreeAlgebra.induction with
  | grade0 c =>
    simp only [Algebra.algebraMap_eq_smul_one]
    simpa [TensorPower.siteOp_one] using
      (TensorPower.HasMarkedSymbol.center (1 : Matrix ((v : V) → Fin (n v)) _ ℂ)).smul c
  | grade1 x =>
    rcases x with a | Q
    · simpa [word, wordSymbol] using TensorPower.HasMarkedSymbol.center a
    · simpa [word, wordSymbol] using TensorPower.hasMarkedSymbol_starOp Q
  | mul a b ha hb => simpa using ha.mul hb
  | add a b ha hb => simpa using ha.add hb

variable [∀ v, NeZero (n v)]

/-- D6.15 `replicas:injection-product`, symbol form. For fixed words `w, w'` (D6.13) in marked
operators and stars, with compressions `B_k = Π_k w Π_k`: `B_k` has scalar symbol
`⟨θ, F_w(θ) θ⟩` (each star `J_{Q,k} ↦ ρ_Q`); `B_k^†` has the conjugate symbol; `B_k B'_k` has the
product symbol; and `Tr σ B_k - ∫ ⟨θ, F_w(θ) θ⟩ dμ_σ → 0` uniformly in densities `σ` on `𝒮_k`. -/
theorem eq_replicas_injection_product_symbol (w w' : FreeAlgebra ℂ (Letter n)) :
    TensorPower.HasCoherentSymbol (TensorPower.HasMarkedSymbol.compress (word · w))
        (scalarSymbol w) ∧
      TensorPower.HasCoherentSymbol
        (fun k => (TensorPower.HasMarkedSymbol.compress (word · w) k)ᴴ)
        (fun θ => star (scalarSymbol w θ)) ∧
      TensorPower.HasCoherentSymbol
        (fun k => TensorPower.HasMarkedSymbol.compress (word · w) k *
          TensorPower.HasMarkedSymbol.compress (word · w') k)
        (fun θ => scalarSymbol w θ * scalarSymbol w' θ) ∧
      ∀ ε > 0, ∀ᶠ k in Filter.atTop,
        ∀ σ : Matrix (Config (fun v => Fin (n v)) (k + 1)) (Config (fun v => Fin (n v)) (k + 1)) ℂ,
          σ.PosSemidef → σ.trace = 1 → (∀ π, U _ (k + 1) Finset.univ π * σ = σ) →
          ‖(σ * (projS _ (k + 1) * word k w * projS _ (k + 1))).trace -
            ∫ θ, scalarSymbol w θ.1 ∂μ _ (k + 1) σ‖ ≤ ε := by
  -- D6.15.1 compression, D6.15.7 `replicas:uniform-husimi`
  have h := (hasMarkedSymbol_word w).hasCoherentSymbol_compress
  have h' := (hasMarkedSymbol_word w').hasCoherentSymbol_compress
  refine ⟨h, h.conjTranspose, h.mul h', fun ε hε => ?_⟩
  -- D6.15.4 several words, D6.15.6 multiplicativity
  filter_upwards [(Filter.tendsto_add_atTop_nat 1).eventually
    (eventually_norm_trace_sub_integral_μ_le _ h hε)] with k hk
  rw [projS_eq]
  exact hk

end Words

end AreaLaw.Replicas
