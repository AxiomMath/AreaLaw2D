import AreaLawRefactored.S06_Replicas.Ported.MarkedSimilaritySymbol
import AreaLawRefactored.S05_Conditional.Lemma53

/-!
# §6 Lemma 6.4: marked-copy scalar symbols (D6.12, D6.13, D6.16)

Digest `digest/06-replicas.md` §6.3, paper `paper/sections/05-replicas.tex` lines 615–845.
The system is `𝒱 = ⨂_{v : V} ℂ^{n_v}` over an arbitrary finite site type `V` (local dimensions
`Fin (n v)`, as in the ported files). `coherentIntegral b σ φ` is `∫ φ dμ_σ` (D6.11). Item 4
uses `AreaLaw.lemma_5_3` (§5); the bridges below read the §5 region encoding
(`Reg`, `extendId`, `marg`, `bracketPow`) on the full region `Reg (Fin ∘ n) univ ≃ SiteConfig n`.
-/

namespace AreaLaw.Replicas

universe u

open Matrix PermutationRepresentation Filter Arealaw TensorPower Entropy
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-! ### Bridges between the region encodings -/

section Bridges

/-- `extendId` on the full region is `localLift`, read through `univEquiv`. -/
theorem extendId_univ (D : Finset V) (hD : D ⊆ Finset.univ)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    extendId hD K = (localLift D K).submatrix univEquiv univEquiv := by
  ext w w'
  simp only [extendId, of_apply, submatrix_apply, localLift_apply, univEquiv_apply]
  have e : (restr (S := Finset.univ \ D) Finset.sdiff_subset w =
      restr (S := Finset.univ \ D) Finset.sdiff_subset w') ↔
      ∀ v ∉ D, w ⟨v, Finset.mem_univ v⟩ = w' ⟨v, Finset.mem_univ v⟩ :=
    ⟨fun h v hv => congrFun h ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hv⟩⟩,
      fun h => funext fun i => h i.1 (Finset.mem_sdiff.1 i.2).2⟩
  simp only [e]
  rfl

/-- The marginal `marg` of §5 is the marginal `margMatrix` of the ported §6 files. -/
theorem marg_univ (θ : SiteConfig n → ℂ) (D : Finset V) (hD : D ⊆ Finset.univ) :
    marg (θ ∘ univEquiv) hD = margMatrix D θ := by
  ext x y
  simp only [marg, ptrace, margMatrix, of_apply, traceRight, vecMulVec_apply,
    Function.comp_apply, Pi.star_apply]
  let e : Reg (fun v => Fin (n v)) (Finset.univ \ D) ≃ ((v : {v // v ∉ D}) → Fin (n v)) :=
    { toFun := fun z v => z ⟨v.1, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, v.2⟩⟩
      invFun := fun c i => c ⟨i.1, (Finset.mem_sdiff.1 i.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ fun z => ?_
  congr 2

/-- Bracket powers of §5 are the support powers `suppRpow` of the ported files. -/
theorem bracketPow_eq_cfc_suppRpow {m : Type*} [Fintype m] [DecidableEq m] {ρ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (s : ℝ) : bracketPow ρ (s : ℂ) = cfc (suppRpow s) ρ := by
  rw [bracketPow, dif_pos hρ.isHermitian, hρ.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  congr 2
  ext i j
  simp only [diagonal_apply, Function.comp_apply, suppRpow]
  split_ifs with hij hp hz hz <;> try rfl
  · exact absurd hz hp.ne'
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.rpow_def_of_pos hp, mul_comm]
    rfl
  · exact absurd (lt_of_le_of_ne (hρ.eigenvalues_nonneg i) (Ne.symm hz)) hp

theorem posSemidef_margMatrix (Q : Finset V) (θ : SiteConfig n → ℂ) :
    (margMatrix Q θ).PosSemidef :=
  (posSemidef_vecMulVec_self_star _).traceRight

/-- The function `f` of Lemma 5.3 on the full region is `markedScalarSymbol` (`f_θ`). -/
theorem f_univ {P₀ P₁ X U : Finset V} (hP : P₀ ∪ P₁ ⊆ Finset.univ)
    (hY : X ∪ U ⊆ Finset.univ) (hPX : P₀ ∪ X ⊆ Finset.univ) (θ : SiteConfig n → ℂ)
    (K : Matrix (RegionConfig n (P₀ ∪ X)) (RegionConfig n (P₀ ∪ X)) ℂ) (s : ℝ) :
    Conditional.f hP hY hPX (θ ∘ univEquiv) K (s : ℂ) =
      markedScalarSymbol s (P₀ ∪ P₁) (X ∪ U) (localLift (P₀ ∪ X) K) θ := by
  have hneg : -(s : ℂ) = ((-s : ℝ) : ℂ) := by push_cast; ring
  rw [Conditional.f, hneg, marg_univ, marg_univ,
    bracketPow_eq_cfc_suppRpow (posSemidef_margMatrix _ _),
    bracketPow_eq_cfc_suppRpow (posSemidef_margMatrix _ _),
    bracketPow_eq_cfc_suppRpow (posSemidef_margMatrix _ _),
    bracketPow_eq_cfc_suppRpow (posSemidef_margMatrix _ _), extendId_univ, extendId_univ,
    extendId_univ, extendId_univ, extendId_univ]
  simp only [submatrix_mul_equiv, submatrix_mulVec_equiv, markedScalarSymbol, regionPow,
    dotProduct, Function.comp_apply, Pi.star_apply]
  exact univEquiv.sum_comp (fun w => star (θ w) * _)

/-- A lift from a region `D` is a lift from any region `D' = D`. -/
theorem exists_localLift_eq {D D' : Finset V} (hDD : D = D')
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    ∃ K' : Matrix (RegionConfig n D') (RegionConfig n D') ℂ, localLift D K = localLift D' K' ∧
      (0 ≤ K → 0 ≤ K') ∧ (K ≤ 1 → K' ≤ 1) ∧
        Fintype.card (RegionConfig n D) = Fintype.card (RegionConfig n D') := by
  subst hDD
  exact ⟨K, rfl, id, id, rfl⟩

end Bridges

/-! ### Coherent integrals -/

section CoherentIntegral

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

theorem coherentIntegral_const_mul (a : Ω) (σ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (c : ℂ)
    (φ : (Ω → ℂ) → ℂ) : coherentIntegral a σ (fun θ => c * φ θ) = c * coherentIntegral a σ φ := by
  simp only [coherentIntegral, mul_left_comm _ c, MeasureTheory.integral_const_mul]

theorem continuous_comp_unitary_mulVec_single {φ : (Ω → ℂ) → ℂ}
    (hφ : ContinuousOn φ unitSphere) (a : Ω) :
    Continuous fun U : unitaryGroup Ω ℂ => φ ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) :=
  hφ.comp_continuous (continuous_unitary_mulVec_single a) fun U =>
    unitary_mulVec_single_mem_unitSphere U a

/-- `Re φ ≤ Re ψ` on unit vectors gives `Re ∫ φ dμ_σ ≤ Re ∫ ψ dμ_σ`. -/
theorem re_coherentIntegral_le {σ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hσp : σ.PosSemidef)
    (a : Ω) {φ ψ : (Ω → ℂ) → ℂ} (hφ : ContinuousOn φ unitSphere)
    (hψ : ContinuousOn ψ unitSphere) (hle : ∀ θ ∈ unitSphere, (φ θ).re ≤ (ψ θ).re) :
    (coherentIntegral a σ φ).re ≤ (coherentIntegral a σ ψ).re := by
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  set G : unitaryGroup Ω ℂ → ℂ := fun U => (σ * coherentProj k (θ U)).trace
  have hG0 : ∀ U, 0 ≤ G U := fun U => by
    change 0 ≤ (σ * coherentProj k (θ U)).trace
    rw [coherentProj, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
    exact hσp.dotProduct_mulVec_nonneg _
  have hT : 0 ≤ (symProj (copyPerm Ω k)).trace := by
    have e : symProj (copyPerm Ω k) = (symProj (copyPerm Ω k))ᴴ * symProj (copyPerm Ω k) := by
      rw [isHermitian_symProj.eq, symProj_mul_symProj]
    rw [e]; exact (posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hiφ := integrable_coherentIntegrand a σ (continuous_comp_unitary_mulVec_single hφ a)
  have hiψ := integrable_coherentIntegrand a σ (continuous_comp_unitary_mulVec_single hψ a)
  simp only [coherentIntegral, Complex.mul_re, ((Complex.nonneg_iff.mp hT).2).symm, zero_mul,
    sub_zero]
  refine mul_le_mul_of_nonneg_left ?_ (Complex.nonneg_iff.mp hT).1
  rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← integral_re hiφ, ← integral_re hiψ]
  refine MeasureTheory.integral_mono hiφ.re hiψ.re fun U => ?_
  simp only [RCLike.re_to_complex, Complex.mul_re]
  change (G U).re * (φ (θ U)).re - (G U).im * (φ (θ U)).im ≤
    (G U).re * (ψ (θ U)).re - (G U).im * (ψ (θ U)).im
  rw [← (Complex.nonneg_iff.mp (hG0 U)).2, zero_mul, zero_mul, sub_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (hle _ (unitary_mulVec_single_mem_unitSphere U a))
    (Complex.nonneg_iff.mp (hG0 U)).1

end CoherentIntegral

/-! ### The gain `η_θ` and its continuity -/

section Eta

/-- D6.12 item 4. `η_θ = I_θ(x:F|Y₀)` of the pure state of `θ`, read on `Reg (Fin ∘ n) univ`
(`0` off the unit sphere, where it is not used). -/
noncomputable def η (X U F : Finset V) (θ : SiteConfig n → ℂ) : ℝ :=
  if hθ : star (θ ∘ univEquiv) ⬝ᵥ (θ ∘ univEquiv) = 1 then
    condMutualInfo (pureState (θ ∘ univEquiv) hθ).toSubState (Finset.subset_univ X)
      (Finset.subset_univ U) (Finset.subset_univ F)
  else 0

theorem spectrum_subset_Icc_of_trace_eq_one {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℂ} (hM : M.PosSemidef) (htr : M.trace = 1) :
    spectrum ℝ M ⊆ Set.Icc 0 1 := by
  rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  refine ⟨hM.eigenvalues_nonneg i, ?_⟩
  have hsum : ∑ j, hM.isHermitian.eigenvalues j = 1 := by
    simpa [htr] using (congrArg Complex.re hM.isHermitian.trace_eq_sum_eigenvalues).symm
  exact hsum ▸ Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- Continuity of the von Neumann entropy along Hermitian families with spectrum in `[0, 1]`. -/
theorem continuousOn_vonNeumann {X m : Type*} [TopologicalSpace X] [Fintype m] [DecidableEq m]
    {ρ : X → Matrix m m ℂ} (hρ : ∀ x, (ρ x).IsHermitian) {T : Set X} (hc : ContinuousOn ρ T)
    (hspec : ∀ x ∈ T, spectrum ℝ (ρ x) ⊆ Set.Icc 0 1) :
    ContinuousOn (fun x => vonNeumann (hρ x)) T := by
  have e : ∀ x, vonNeumann (hρ x) =
      RCLike.re (-(cfc (fun y : ℝ => y * Real.log y) (ρ x)).trace) := fun x => by
    rw [vonNeumann, (hρ x).cfc_eq]
  simp_rw [e]
  exact RCLike.continuous_re.comp_continuousOn (continuous_id.matrix_trace.neg.comp_continuousOn
    (ContinuousOn.cfc' isCompact_Icc _ hc hspec (fun x _ => (hρ x).isSelfAdjoint)
      Real.continuous_mul_log.continuousOn))

theorem dotProduct_star_comp_univEquiv (θ : SiteConfig n → ℂ) :
    (θ ∘ univEquiv) ⬝ᵥ star (θ ∘ univEquiv) = θ ⬝ᵥ star θ :=
  univEquiv.sum_comp fun x => θ x * star (θ x)

/-- `θ ↦ η_θ` is continuous on unit vectors. -/
theorem continuousOn_η (X U F : Finset V) : ContinuousOn (η (n := n) X U F) unitSphere := by
  have hunit : ∀ θ ∈ (unitSphere : Set (SiteConfig n → ℂ)),
      star (θ ∘ univEquiv) ⬝ᵥ (θ ∘ univEquiv) = 1 := fun θ hθ => by
    rw [dotProduct_comm, dotProduct_star_comp_univEquiv]; exact hθ
  have hS : ∀ A : Finset V, ContinuousOn (fun θ : SiteConfig n → ℂ => vonNeumann
      (posSemidef_ptrace (Finset.subset_univ A)
        (posSemidef_vecMulVec_self_star (θ ∘ univEquiv))).isHermitian) unitSphere := fun A => by
    refine continuousOn_vonNeumann _ (Continuous.continuousOn ?_) fun θ hθ =>
      spectrum_subset_Icc_of_trace_eq_one (posSemidef_ptrace _
        (posSemidef_vecMulVec_self_star _)) ?_
    · refine continuous_pi fun x => continuous_pi fun y => ?_
      simp only [ptrace, of_apply, vecMulVec_apply, Function.comp_apply, Pi.star_apply]
      exact continuous_finsetSum _ fun z _ =>
        (continuous_apply _).mul (continuous_apply _).star
    · rw [trace_ptrace, trace_vecMulVec, dotProduct_comm]; exact hunit θ hθ
  refine ((((hS (X ∪ U)).add (hS (U ∪ F))).sub (hS U)).sub (hS (X ∪ U ∪ F))).congr
    fun θ hθ => ?_
  simp only [η, dif_pos (hunit θ hθ)]
  rfl

end Eta

variable [∀ v, NeZero (n v)]

/-! ### D6.13 Bounded approximation on symmetric inputs -/

/-- `R_P R_Y^{-1} H R_P^{-1} R_Y = W_Y^{-1} W_P H W_P^{-1} W_Y` for `H` on the last copy. -/
theorem markedWord_eq {t : ℝ} (ht : 0 ≤ t) (m : ℕ) {P Y : Finset V} (hPY : Disjoint P Y)
    (c : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    markedRatio (fun v => Fin (n v)) t m P * (markedRatio (fun v => Fin (n v)) t m Y)⁻¹ *
        siteOp (Fin.last m) c * (markedRatio (fun v => Fin (n v)) t m P)⁻¹ *
          markedRatio (fun v => Fin (n v)) t m Y =
      (replicaMetric (fun v => Fin (n v)) t (m + 1) Y)⁻¹ *
        replicaMetric (fun v => Fin (n v)) t (m + 1) P * siteOp (Fin.last m) c *
          ((replicaMetric (fun v => Fin (n v)) t (m + 1) P)⁻¹ *
            replicaMetric (fun v => Fin (n v)) t (m + 1) Y) := by
  have hw : ∀ l, replicaLabelWeight (k := m + 1) (fun v => Fin (n v)) t l ≠ 0 :=
    fun l => (replicaLabelWeight_pos _ ht l).ne'
  have hw' : ∀ l, replicaLabelWeight (k := m) (fun v => Fin (n v)) t l ≠ 0 :=
    fun l => (replicaLabelWeight_pos _ ht l).ne'
  set WP := replicaMetric (fun v => Fin (n v)) t (m + 1) P
  set WY := replicaMetric (fun v => Fin (n v)) t (m + 1) Y
  set VP := replicaMetricFirst (fun v => Fin (n v)) t m P
  set VY := replicaMetricFirst (fun v => Fin (n v)) t m Y
  set H := siteOp (Fin.last m) c
  have hWPi : WP⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) P)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hWYi : WY⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) Y)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hVPi : VP⁻¹ = labelObservable ((subsystemPerm (m + 1) (fun v => Fin (n v)) P).comp
      (firstCopies m)) fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ :=
    labelObservable_inv _ hw'
  have hWP1 : WP⁻¹ * WP = 1 := labelObservable_inv_mul_self _ hw
  have hWY1 : WY⁻¹ * WY = 1 := labelObservable_inv_mul_self _ hw
  have hVP1 : VP⁻¹ * VP = 1 := labelObservable_inv_mul_self _ hw'
  have hVP2 : VP * VP⁻¹ = 1 := labelObservable_mul_inv_self _ hw'
  have hVY2 : VY * VY⁻¹ = 1 := labelObservable_mul_inv_self _ hw'
  have hRPi : (markedRatio (fun v => Fin (n v)) t m P)⁻¹ = VP * WP⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    change VP * WP⁻¹ * (WP * VP⁻¹) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc WP⁻¹, hWP1, Matrix.one_mul, hVP2]
  have hRYi : (markedRatio (fun v => Fin (n v)) t m Y)⁻¹ = VY * WY⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    change VY * WY⁻¹ * (WY * VY⁻¹) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc WY⁻¹, hWY1, Matrix.one_mul, hVY2]
  have hff : Commute VP⁻¹ VY := by
    rw [hVPi]
    exact commute_labelObservable_of_commute _ _ (fun g g' => by
      simpa only [MonoidHom.comp_apply] using commute_subsystemPerm_of_disjoint (m + 1)
        (fun v => Fin (n v)) hPY (firstCopies m g) (firstCopies m g')) _ _
  have h1 : Commute VP⁻¹ (VY * WY⁻¹ * H) := by
    refine (hff.mul_right ?_).mul_right ?_
    · rw [hVPi, hWYi]; exact (commute_labelObservable_first_of_disjoint hPY.symm _ _).symm
    · rw [hVPi]; exact commute_labelObservable_first_siteOp_last P c _
  have h2 : Commute VY (WY⁻¹ * H * WP⁻¹ * WY) := by
    refine (((?_ : Commute VY WY⁻¹).mul_right ?_).mul_right ?_).mul_right ?_
    · rw [hWYi]; exact (commute_labelObservable_first Y _ _).symm
    · exact commute_labelObservable_first_siteOp_last Y c _
    · rw [hWPi]; exact (commute_labelObservable_first_of_disjoint hPY _ _).symm
    · exact (commute_labelObservable_first Y _ _).symm
  have h3 : Commute WP WY⁻¹ := by
    rw [hWYi]; exact commute_labelObservable_of_commute _ _
      (commute_subsystemPerm_of_disjoint (m + 1) _ hPY) _ _
  rw [hRPi, hRYi]
  change WP * VP⁻¹ * (VY * WY⁻¹) * H * (VP * WP⁻¹) * (WY * VY⁻¹) = _
  calc WP * VP⁻¹ * (VY * WY⁻¹) * H * (VP * WP⁻¹) * (WY * VY⁻¹)
      = WP * (VP⁻¹ * (VY * WY⁻¹ * H)) * VP * WP⁻¹ * WY * VY⁻¹ := by simp only [Matrix.mul_assoc]
    _ = WP * (VY * (WY⁻¹ * H * WP⁻¹ * WY)) * VY⁻¹ := by
        rw [h1.eq]; simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc VP⁻¹, hVP1, Matrix.one_mul]
    _ = WY⁻¹ * WP * H * (WP⁻¹ * WY) := by
        rw [h2.eq]
        simp only [Matrix.mul_assoc]
        rw [hVY2, Matrix.mul_one, ← Matrix.mul_assoc WP, h3.eq, Matrix.mul_assoc]

/-- D6.13. (a) `O_k`, as a quadratic form on `𝒮_k`, is the compression of
`R_{P,k} R_{Y,k}^{-1} h^{(k)} R_{P,k}^{-1} R_{Y,k}`; `sup_k ‖O_k‖ < ∞`. (b) Every `ε > 0`: there
are a product decomposition `h = ∑ b_i a_i` (`a_i` on `P`, `b_i` on `Y`) and polynomials `p, q`
such that the compressions `B_k = Π_k W_k Π_k` of the polynomial word
`W_k = ∑_i (q(J_Y) b_i^{(k)} p(J_Y))(p(J_P) a_i^{(k)} q(J_P))` in the marked operators and the
stars `J_{Q,k}` have a common `sup_k ‖B_k‖` bound and `limsup_k ‖O_k - B_k‖ ≤ ε` on `𝒮_k`. -/
theorem step_6_13 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) {P Y F : Finset V}
    (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h (P ∪ Y)) :
    ((∀ (m : ℕ) (u z : Config (m + 1) (fun v => Fin (n v)) → ℂ),
      u ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) →
      z ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) →
        star u ⬝ᵥ (markedSimilarity n t (m + 1) P Y F h *ᵥ z) =
          star u ⬝ᵥ ((markedRatio (fun v => Fin (n v)) t m P *
            (markedRatio (fun v => Fin (n v)) t m Y)⁻¹ * siteOp (Fin.last m) h *
              (markedRatio (fun v => Fin (n v)) t m P)⁻¹ *
                markedRatio (fun v => Fin (n v)) t m Y) *ᵥ z)) ∧
      ∃ M, ∀ (k : ℕ) (z : Config k (fun v => Fin (n v)) → ℂ),
        z ∈ symmetricSubspace k (fun v => Fin (n v)) →
          ‖(EuclideanSpace.equiv _ ℂ).symm (markedSimilarity n t k P Y F h *ᵥ z)‖ ≤
            M * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) ∧
    ∀ ε > 0, ∃ (N : ℕ) (a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ) (p q : ℝ[X]),
      (∀ i, IsSupportedOn (a i) P) ∧ (∀ i, IsSupportedOn (b i) Y) ∧ h = ∑ i, b i * a i ∧
      (∃ M, ∀ k, ‖HasMarkedSymbol.compress (polyWord P Y a b p q) k‖ ≤ M) ∧
        ∀ᶠ k in atTop, ‖(markedSimilarity n t k P Y F h -
          HasMarkedSymbol.compress (polyWord P Y a b p q) k) *
            symProj (copyPerm (SiteConfig n) k)‖ ≤ ε := by
  refine ⟨⟨fun m u z hu hz => ?_,
    -- D6.13.3–D6.13.5: both inverses act on symmetric vectors, polarization
    exists_norm_markedSimilarity_mulVec_le ht0 ht1 hPY hPF hYF hh⟩, fun ε hε => ?_⟩
  · -- D6.13.1: `O_k = W_Y^{-1} W_P h̄ W_P^{-1} W_Y`
    rw [markedSimilarity_succ_eq ht0.le m hPY hPF hYF hh]
    -- D6.13.2: `h̄ ↦ h^{(k)}` between symmetric vectors, `W_{Q,k} = R_{Q,k} W_{Q,k-1}`
    have hc : ∀ (Q : Finset V) τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ)
        (replicaMetric (fun v => Fin (n v)) t (m + 1) Q) ∧
        Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ)
          (replicaMetric (fun v => Fin (n v)) t (m + 1) Q)⁻¹ := fun Q τ =>
      ⟨commute_copyPerm_labelObservable _ Q _ τ, by
        rw [replicaMetric_inv_eq ht0.le]; exact commute_copyPerm_labelObservable _ Q _ τ⟩
    rw [star_dotProduct_copyMean_eq (Fin.last m) h (fun τ => (hc Y τ).2.mul_right (hc P τ).1)
      (fun τ => (hc P τ).2.mul_right (hc Y τ).1) hu hz, markedWord_eq ht0.le m hPY]
  · -- D6.13.6–D6.13.8: clip, then polynomials, then `k → ∞`
    obtain ⟨N, a, b, p, q, ha, hb, hdec, -, hev⟩ := exists_polyWord_approx ht0 ht1 hPY hPF hYF hh hε
    refine ⟨N, a, b, p, q, ha, hb, hdec, ?_, hev⟩
    -- D6.13.8: the common bound, `B_k = Π_k W_k Π_k = B_k Π_k`
    obtain ⟨M, hM⟩ := (hasMarkedSymbol_polyWord P Y a b p q).hasCoherentSymbol_compress.bounded
    refine ⟨M, fun k => ?_⟩
    have hBP : HasMarkedSymbol.compress (polyWord P Y a b p q) k *
        symProj (copyPerm (SiteConfig n) k) =
          HasMarkedSymbol.compress (polyWord P Y a b p q) k := by
      cases k with
      | zero => simp [HasMarkedSymbol.compress]
      | succ m => simp only [HasMarkedSymbol.compress, Matrix.mul_assoc, symProj_mul_symProj]
    simpa only [hBP] using hM k

/-! ### D6.16 Removing clipping; absolute values -/

/-- D6.16. Rest of D6.12 after D6.13–D6.15: (i) `f_θ` bounded, continuous in `θ`;
(ii) `replicas:polynomial-symbol` for every fixed `q`; `O_k^† O_k`, `O_k O_k^†` have symbol
`|f_θ|²`; (iii) `replicas:skew-symbol`; (iv) `replicas:skew-bound` is `step_6_12_4`.
"`X_k` has symbol `g`" is `HasCoherentSymbol X g`. -/
theorem step_6_16 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) {P Y F : Finset V}
    (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h (P ∪ Y)) :
    (ContinuousOn (markedScalarSymbol t P Y h) unitSphere ∧
      ∃ B, ∀ θ ∈ unitSphere, ‖markedScalarSymbol t P Y h θ‖ ≤ B) ∧
    (∀ q : FreeAlgebra ℂ (Fin 2),
      HasCoherentSymbol (fun k => FreeAlgebra.lift ℂ
          ![markedSimilarity n t k P Y F h, (markedSimilarity n t k P Y F h)ᴴ] q)
        (fun θ => FreeAlgebra.lift ℂ
          ![markedScalarSymbol t P Y h θ, star (markedScalarSymbol t P Y h θ)] q)) ∧
    HasCoherentSymbol (fun k => (markedSimilarity n t k P Y F h)ᴴ * markedSimilarity n t k P Y F h)
      (fun θ => ((‖markedScalarSymbol t P Y h θ‖ ^ 2 : ℝ) : ℂ)) ∧
    HasCoherentSymbol (fun k => markedSimilarity n t k P Y F h * (markedSimilarity n t k P Y F h)ᴴ)
      (fun θ => ((‖markedScalarSymbol t P Y h θ‖ ^ 2 : ℝ) : ℂ)) ∧
    HasCoherentSymbol (fun k => skewOperator k (markedSimilarity n t k P Y F h))
      (fun θ => ((2 * (‖markedScalarSymbol t P Y h θ‖ -
        (markedScalarSymbol t P Y h θ).re) : ℝ) : ℂ)) := by
  -- D6.16.1–D6.16.4: clipped symbols converge uniformly, polynomial words approximate `O_k`
  have hO := hasCoherentSymbol_markedSimilarity ht0 ht1 hPY hPF hYF hh
  -- D6.16.3: `f_θ` is continuous, hence bounded on the compact unit sphere
  obtain ⟨B, -, hB⟩ := hO.exists_bound
  -- D6.16.5: `O^† O`, `O O^†` have symbol `f̄ f = f f̄ = |f|²`
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    push_cast; exact Complex.conj_mul' z
  refine ⟨⟨hO.continuousOn, B, hB⟩, hO.freeAlgebra, ?_, ?_, hO.skew⟩
  · simpa only [hsq] using hO.conjTranspose.mul hO
  · simpa only [mul_comm _ (star _), hsq] using hO.mul hO.conjTranspose

/-! ### D6.12 Lemma 6.4 -/

/-- D6.12.5. Exchange: `A_k(P, Y, F) = A_k(F, Y, P)` (D6.8), so `O_k` is unchanged under
`P ↔ F` and Lemma 6.4 at `(F, Y, P)` is Lemma 6.4 with the outer parts exchanged. -/
theorem step_6_12_5 {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P F : Finset V} (hPF : Disjoint P F)
    (Y : Finset V) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    markedSimilarity n t k P Y F h = markedSimilarity n t k F Y P h := by
  have e : leafRoot n t k P Y F = leafRoot n t k F Y P := by
    simp only [leafRoot, replicaMetric_inv_eq ht, (commute_replicaMetric_of_disjoint' k hPF _ _).eq]
  simp only [markedSimilarity, leafMetric, e]

/-- D6.12.4. Item 4 of Lemma 6.4 pointwise. For `h = lift_D K`, `0 ≤ K ≤ I`, `D ⊆ PY` the
designated support, `f_θ = f(t)` of Lemma 5.3 with `a = 2t`, `x = Y ∩ D`, `U = Y₀ = Y \ D`,
`P₀ = P ∩ D`, `P₁ = P \ D`; so `a log(e d_h) ≤ c` gives
`|f_θ| - Re f_θ ≤ C a² log⁴(e d_h) η_θ^{1/8}`, `η_θ = I_θ(x:F|Y₀)`, `c, C` of Lemma 5.3. -/
theorem step_6_12_4 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
      (P Y F : Finset V), Disjoint P Y → Disjoint P F → Disjoint Y F →
      P ∪ Y ∪ F = Finset.univ →
    ∀ (D : Finset V) (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ), D ⊆ P ∪ Y →
      0 ≤ K → K ≤ 1 → ∀ t : ℝ, 0 < t → 2 * t * ℓ (Fintype.card (RegionConfig n D)) ≤ c →
    ∀ θ ∈ unitSphere, ‖markedScalarSymbol t P Y (localLift D K) θ‖ -
        (markedScalarSymbol t P Y (localLift D K) θ).re ≤
      C * (2 * t) ^ 2 * ℓ (Fintype.card (RegionConfig n D)) ^ 4 *
        η (Y ∩ D) (Y \ D) F θ ^ (1 / 8 : ℝ) := by
  obtain ⟨c, C, hc, hC, hL⟩ := lemma_5_3.{u, 0}
  refine ⟨c, C, hc, hC, fun V _ _ n _ P Y F hPY hPF hYF hcov D K hD hK0 hK1 t ht hac θ hθ => ?_⟩
  have hPeq : P ∩ D ∪ P \ D = P := by rw [Finset.union_comm]; exact Finset.sdiff_union_inter P D
  have hYeq : Y ∩ D ∪ Y \ D = Y := by rw [Finset.union_comm]; exact Finset.sdiff_union_inter Y D
  have hDeq : D = P ∩ D ∪ Y ∩ D := by
    rw [← Finset.union_inter_distrib_right, Finset.inter_eq_right.mpr hD]
  obtain ⟨K', hK', hK0', hK1', hcard⟩ := exists_localLift_eq hDeq K
  have hθ' : star (θ ∘ univEquiv) ⬝ᵥ (θ ∘ univEquiv) = 1 := by
    rw [dotProduct_comm, dotProduct_star_comp_univEquiv]; exact hθ
  have hℓ : 0 < ℓ (Fintype.card (RegionConfig n D)) := by
    have : (1 : ℝ) ≤ Fintype.card (RegionConfig n D) := by exact_mod_cast Fintype.card_pos
    exact Real.log_pos (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
  -- Lemma 5.3 at `P₀ = P ∩ D`, `P₁ = P \ D`, `x = Y ∩ D`, `U = Y \ D`, `a = 2t`
  have h53 := hL V (fun v => Fin (n v)) Finset.univ (P ∩ D) (P \ D) (Y ∩ D) (Y \ D) F
    (Finset.subset_univ _) (Finset.subset_univ _) (Finset.subset_univ _) (Finset.subset_univ _)
    (Finset.subset_univ _)
    (by rw [hPeq, Finset.union_assoc _ (Y ∩ D), hYeq]; exact hcov.symm)
    (Finset.disjoint_sdiff_inter P D).symm
    (by rw [hPeq]; exact hPY.mono_right Finset.inter_subset_left)
    (by rw [hPeq]; exact hPY.mono_right Finset.sdiff_subset)
    (by rw [hPeq]; exact hPF) (Finset.disjoint_sdiff_inter Y D).symm
    (hYF.mono_left Finset.inter_subset_left) (hYF.mono_left Finset.sdiff_subset)
    (θ ∘ univEquiv) hθ' K' (hK0' hK0) (by convert hK1' hK1 using 2)
    (2 * t) (by rw [← hcard]; positivity) (by rw [← hcard]; exact hac)
  rw [f_univ, show 2 * t / 2 = t by ring, hPeq, hYeq, ← hK', ← hcard] at h53
  simpa only [η, dif_pos hθ'] using h53

/-- D6.12 **Lemma 6.4** (marked-copy scalar symbols). Fix a partition `P, Y, F` of `𝒱`,
`0 < t < 1/4`, `a = 2t`, and a one-copy operator `h` supported on `PY`. With `A_k` of D6.8
and `h̄ = k⁻¹ ∑_j h^{(j)}`, on `𝒮_k` define `O_k = A_k^{-1/2} h̄ A_k^{1/2}` and
`f_θ = ⟨θ, ρ_P^t ρ_Y^{-t} h ρ_P^{-t} ρ_Y^t θ⟩`, `ρ_Q` the `Q`-marginal of `θ`, powers zero on
kernels. Then:
1. `sup_k ‖O_k‖ < ∞` (bound depends on the fixed system and `h`).
2. Every fixed noncommutative polynomial `q` in two variables:
   `sup_σ |Tr σ q(O_k, O_k^†) - ∫ q(f_θ, f̄_θ) dμ_σ(θ)| → 0`, sup over all densities on `𝒮_k`.
3. With `𝒟_k = |O_k| + |O_k^†| - O_k - O_k^†`, uniformly in `σ`:
   `Tr σ 𝒟_k = 2 ∫ (|f_θ| - Re f_θ) dμ_σ(θ) + o_k(1)`.
4. If `0 ≤ h ≤ I` with a designated supporting subsystem of dimension `d_h`,
   `x = Y ∩ supp h`, `Y₀ = Y \ x`, `η_θ = I_θ(x:F|Y₀)`, and `a log(e d_h) ≤ c`:
   `Tr σ 𝒟_k ≤ C a² log^C(e d_h) ∫ η_θ^{1/8} dμ_σ(θ) + o_k(1)`.

Here `O_k = markedSimilarity`, `f_θ = markedScalarSymbol`, `𝒟_k = skewOperator`,
`coherentIntegral b σ φ = ∫ φ dμ_σ` (D6.11); the support `D` of `h = lift_D K` is designated,
`log^C` is `ℓ(d_h)⁴`, `0 < t < 1/2` (weaker than `t < 1/4`), and `c, C` are universal.
Item 4 with the outer parts exchanged is item 4 at `(F, Y, P)`, by `step_6_12_5`. -/
theorem lemma_6_4 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)] (t : ℝ),
      0 < t → t < 1 / 2 → ∀ (P Y F : Finset V), Disjoint P Y → Disjoint P F → Disjoint Y F →
    ∀ h : Matrix (SiteConfig n) (SiteConfig n) ℂ, IsSupportedOn h (P ∪ Y) →
      -- 1.
      (∃ M, ∀ (k : ℕ) (z : Config k (fun v => Fin (n v)) → ℂ),
        z ∈ symmetricSubspace k (fun v => Fin (n v)) →
          ‖(EuclideanSpace.equiv _ ℂ).symm (markedSimilarity n t k P Y F h *ᵥ z)‖ ≤
            M * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) ∧
      -- 2.
      (∀ (q : FreeAlgebra ℂ (Fin 2)), ∀ ε > 0, ∀ᶠ k in atTop, ∀ (b : SiteConfig n)
        (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
        σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
          ‖(σ * FreeAlgebra.lift ℂ ![markedSimilarity n t k P Y F h,
              (markedSimilarity n t k P Y F h)ᴴ] q).trace -
            coherentIntegral b σ (fun θ => FreeAlgebra.lift ℂ
              ![markedScalarSymbol t P Y h θ, star (markedScalarSymbol t P Y h θ)] q)‖ ≤ ε) ∧
      -- 3.
      (∀ ε > 0, ∀ᶠ k in atTop, ∀ (b : SiteConfig n)
        (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
        σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
          ‖(σ * skewOperator k (markedSimilarity n t k P Y F h)).trace -
            2 * coherentIntegral b σ (fun θ => ((‖markedScalarSymbol t P Y h θ‖ -
              (markedScalarSymbol t P Y h θ).re : ℝ) : ℂ))‖ ≤ ε) ∧
      -- 4.
      (P ∪ Y ∪ F = Finset.univ → ∀ (D : Finset V)
        (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ), D ⊆ P ∪ Y → h = localLift D K →
        0 ≤ K → K ≤ 1 → 2 * t * ℓ (Fintype.card (RegionConfig n D)) ≤ c →
        ∀ ε > 0, ∀ᶠ k in atTop, ∀ (b : SiteConfig n)
          (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
          σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
            ((σ * skewOperator k (markedSimilarity n t k P Y F h)).trace).re ≤
              C * (2 * t) ^ 2 * ℓ (Fintype.card (RegionConfig n D)) ^ 4 *
                (coherentIntegral b σ fun θ =>
                  ((η (Y ∩ D) (Y \ D) F θ ^ (1 / 8 : ℝ) : ℝ) : ℂ)).re + ε) := by
  obtain ⟨c, C, hc, hC, h4⟩ := step_6_12_4
  refine ⟨c, 2 * C, hc, by positivity, fun V _ _ n _ t ht0 ht1 P Y F hPY hPF hYF h hh => ?_⟩
  obtain ⟨⟨hfc, -⟩, hpoly, -, -, hskew⟩ := step_6_16 (F := F) ht0 ht1 hPY hPF hYF hh
  -- D6.12.3, item 3: `2 (|f| - Re f)` is the symbol of `𝒟_k`
  have h3 : ∀ ε > 0, ∀ᶠ k in atTop, ∀ (b : SiteConfig n)
      (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
      σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
        ‖(σ * skewOperator k (markedSimilarity n t k P Y F h)).trace -
          2 * coherentIntegral b σ (fun θ => ((‖markedScalarSymbol t P Y h θ‖ -
            (markedScalarSymbol t P Y h θ).re : ℝ) : ℂ))‖ ≤ ε := fun ε hε => by
    filter_upwards [hskew.eventually_norm_trace_sub_le hε] with k hk b σ hσp hσt hσ
    simpa only [← coherentIntegral_const_mul, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      hk b σ hσp hσt hσ
  -- D6.12.1, item 1: D6.13
  refine ⟨exists_norm_markedSimilarity_mulVec_le ht0 ht1 hPY hPF hYF hh,
    -- D6.12.3, item 2: D6.16.4
    fun q ε hε => (hpoly q).eventually_norm_trace_sub_le hε, h3, ?_⟩
  -- D6.12.4, item 4: Lemma 5.3 pointwise, integrated against `μ_σ` in item 3
  intro hcov D K hD hK hK0 hK1 hac ε hε
  subst hK
  set f := markedScalarSymbol t P Y (localLift D K)
  set L := C * (2 * t) ^ 2 * ℓ (Fintype.card (RegionConfig n D)) ^ 4
  have hηc : ContinuousOn (fun θ => ((η (n := n) (Y ∩ D) (Y \ D) F θ ^ (1 / 8 : ℝ) : ℝ) : ℂ))
      unitSphere := Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_η _ _ _).rpow_const fun _ _ => Or.inr (by norm_num))
  filter_upwards [h3 ε hε] with k hk b σ hσp hσt hσ
  have hle : (coherentIntegral b σ fun θ => ((‖f θ‖ - (f θ).re : ℝ) : ℂ)).re ≤
      (coherentIntegral b σ fun θ => (L : ℂ) *
        ((η (Y ∩ D) (Y \ D) F θ ^ (1 / 8 : ℝ) : ℝ) : ℂ)).re := by
    refine re_coherentIntegral_le hσp b (Complex.continuous_ofReal.comp_continuousOn
      (hfc.norm.sub (Complex.continuous_re.comp_continuousOn hfc)))
      (continuousOn_const.mul hηc) fun θ hθ => ?_
    simp only [Complex.ofReal_re, ← Complex.ofReal_mul]
    exact h4 V n P Y F hPY hPF hYF hcov D K hD hK0 hK1 t ht0 hac θ hθ
  rw [coherentIntegral_const_mul, Complex.re_ofReal_mul] at hle
  have h1 := (Complex.re_le_norm _).trans (hk b σ hσp hσt hσ)
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero] at h1
  simp only [L] at hle
  linarith

end AreaLaw.Replicas
