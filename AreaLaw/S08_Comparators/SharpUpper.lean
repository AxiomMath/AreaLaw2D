import AreaLaw.S08_Comparators.RoughUpper
import AreaLawForMathlib.Analysis.MeanInequalitiesCubic

/-!
# §8.3 Upper comparisons: the sharp upper bound (D8.21–D8.22)

Digest `digest/08-comparators.md` D8.21, D8.22, paper `paper/sections/07-comparators.tex`
383–418. No geometry: arbitrary finite site type and local dimensions. On the whole tensor
space, with `ψ̂_k = π^λ_R post_k / √q_k ∈ 𝒮_k ∩ ran 𝖯`: exponential and logarithmic Jensen on
the spectral measures of `𝓜` and `𝓜_g`, vector Jensen through the band trees, then the leaf
expectations `⟨post_k, Ã_{j,g} post_k⟩` by Hölder over the joint label decomposition of
`U, UY, Y` and the marginal moment bounds D8.10 under `ρ_{ψ,Q}^{⊗k} ≤ z^{-k} ρ_Q^{⊗k}` (D8.17).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

section Sharp

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  {D : PhysData n} {X : Finset σ}

/-- `π^λ_R` commutes with the pinned metric `Ã_{j,g}` (regions `U, UY, Y` are physical). -/
theorem commute_piR_Atil {K : ℕ} {St : Type v} (Γ : Statuses σ K St X) (d : ℕ) [NeZero d]
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) (s : St) (g : Fin K) :
    Commute (piR (n := n) d k l) (Γ.Atil n d t k s g) := by
  rw [Statuses.Atil, Replicas.W_inv _ ht, Replicas.W_inv _ ht]
  refine Commute.pow_right (Commute.mul_right (Commute.mul_right ?_ ?_) ?_) 2
  · exact commute_piR_labelObservable _ _ _ (disjoint_physReg_R _) _
  · exact commute_piR_labelObservable _ _ _ (disjoint_physReg_R _) _
  · exact commute_piR_labelObservable _ _ _ (disjoint_physReg_R _) _

/-- `π^λ_R post_k ∈ 𝒮_k ∩ ran 𝖯`. -/
theorem piR_post_mem (h11 : Step_8_11.{u}) (E : TypicalSet D X) (k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    piR E.d k l *ᵥ post E k ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧
      pinProj E k *ᵥ (piR E.d k l *ᵥ post E k) = piR E.d k l *ᵥ post E k := by
  have hR : piR E.d k l = labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k
      {Site.R}) fun l' => if l' = l then 1 else 0 := by
    rw [piR, Replicas.π, labelProj_eq_labelObservable_ite]
  refine ⟨hR ▸ Upper.labelObservable_mulVec_mem_S n _ _ _ _ (post_mem_S E k), ?_⟩
  rw [mulVec_mulVec, hR, (Upper.commute_pinProj_labelObservable E k
    (Finset.disjoint_singleton_left.mpr Upper.R_not_mem_XC) _).eq, ← mulVec_mulVec,
    pinProj_mulVec_post h11 E k]

/-- `ψ̂_k = π^λ_R post_k / √q_k`. -/
noncomputable def ψh (E : TypicalSet D X) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Transport.Config (dims n E.d) k → ℂ :=
  (((Real.sqrt (q E k l))⁻¹ : ℝ) : ℂ) • (piR E.d k l *ᵥ post E k)

/-- D8.21 (`comparator:sharp-jensen`). `ψ̂_k = π^λ_R post_k / √q_k`. Then
`‖𝓜^{-s} π^λ_R post_k‖² ≥ q_k exp{-2s ⟨ψ̂_k, log 𝓜 ψ̂_k⟩}`, and for each band
`⟨ψ̂_k, log 𝓜_g ψ̂_k⟩ ≤ log ⟨ψ̂_k, 𝓜_g ψ̂_k⟩ ≤ O(log(k + 1)) + ∑_j w_j log ⟨post_k, Ã_{j,g} post_k⟩`
(the `O(log(k + 1))` is the conditioning cost `-log q_k`). -/
theorem step_8_21 (h1 : Step_8_1.{u, v}) (h11 : Step_8_11.{u}) (h16 : Step_8_16.{u, v})
    (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
    (Γ : Statuses σ K St X) (T : Transport.MeanTree St) {a : ℝ} (ha : 0 < a) (k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) (hq : 0 < q E k l) :
    q E k l * Real.exp (-2 * (1 / 4) *
        (star (ψh E k l) ⬝ᵥ (CFC.log (Γ.root n E.d T (a / 2) k) *ᵥ ψh E k l)).re) ≤
        Matrix.Transport.filteredNormSq (Γ.root n E.d T (a / 2) k) (piR E.d k l *ᵥ post E k) ∧
      (star (ψh E k l) ⬝ᵥ (CFC.log (Γ.root n E.d T (a / 2) k) *ᵥ ψh E k l)).re =
        ∑ g, (star (ψh E k l) ⬝ᵥ (CFC.log (Γ.bandRoot n E.d T (a / 2) k g) *ᵥ ψh E k l)).re ∧
      ∀ g, (star (ψh E k l) ⬝ᵥ (CFC.log (Γ.bandRoot n E.d T (a / 2) k g) *ᵥ ψh E k l)).re ≤
          Real.log (star (ψh E k l) ⬝ᵥ (Γ.bandRoot n E.d T (a / 2) k g *ᵥ ψh E k l)).re ∧
        Real.log (star (ψh E k l) ⬝ᵥ (Γ.bandRoot n E.d T (a / 2) k g *ᵥ ψh E k l)).re ≤
          -Real.log (q E k l) + ∑ s, T.weight s *
            Real.log (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re := by
  set x := piR E.d k l *ᵥ post E k
  set r := Real.sqrt (q E k l)
  have hr : 0 < r := Real.sqrt_pos.mpr hq
  have hrr : r ^ 2 = q E k l := Real.sq_sqrt hq.le
  have ht : (0 : ℝ) ≤ a / 2 := by linarith
  have hψ1 : star (ψh E k l) ⬝ᵥ ψh E k l = 1 := (Matrix.normalize_spec x hq).1
  have hBand : ∀ s g, (Γ.bandA n E.d (a / 2) k s g).PosDef :=
    fun s g => posDef_bandA Γ E.d ht k s g
  have hA : ∀ s, (Γ.leafA n E.d (a / 2) k s).PosDef := fun s => posDef_leafA h1 Γ E.d ht k s
  have hM : (Γ.root n E.d T (a / 2) k).PosDef := Transport.MeanTree.posDef_eval hA T
  have hMg : ∀ g, (Γ.bandRoot n E.d T (a / 2) k g).PosDef :=
    fun g => Transport.MeanTree.posDef_eval (fun s => hBand s g) T
  refine ⟨?_, ?_, fun g => ⟨?_, ?_⟩⟩
  -- D8.21.1: `‖𝓜^{-s} π post‖² = q_k ⟨ψ̂, e^{-2s log 𝓜} ψ̂⟩ ≥ q_k e^{-2s ⟨ψ̂, log 𝓜 ψ̂⟩}`
  · have h := hM.exp_neg_two_mul_le_rpow (1 / 4) hψ1
    have hf : Matrix.Transport.filteredNormSq (Γ.root n E.d T (a / 2) k) x =
        q E k l * (star (Γ.root n E.d T (a / 2) k ^ (-(1 / 4) : ℝ) *ᵥ ψh E k l) ⬝ᵥ
          (Γ.root n E.d T (a / 2) k ^ (-(1 / 4) : ℝ) *ᵥ ψh E k l)).re := by
      rw [ψh, mulVec_smul, Matrix.re_star_smul_dotProduct_smul, inv_pow, hrr, ← mul_assoc,
        mul_inv_cancel₀ hq.ne', one_mul]
      rfl
    rw [hf]
    exact mul_le_mul_of_nonneg_left h hq.le
  -- D8.21.2: `log 𝓜 = ∑_g log 𝓜_g` (commuting band factors, D8.1 (ii))
  · have h6 := Transport.lemma_7_1_6 (D := fun s g => Γ.bandA n E.d (a / 2) k s g)
      hBand (fun s s' g g' h => (h1 Γ).2 n E.d (a / 2) ht k s s' g g' h) T
    have hroot : Γ.root n E.d T (a / 2) k =
        (List.ofFn fun g => Γ.bandRoot n E.d T (a / 2) k g).prod := h6.1
    rw [hroot, cfc_log_listProd_ofFn hMg h6.2, sum_mulVec, dotProduct_sum, Complex.re_sum]
  -- D8.21.3: concavity of `log` on the spectral measure of `𝓜_g` in `ψ̂`
  · exact (hMg g).re_dotProduct_log_mulVec_le hψ1
  -- D8.21.4: vector Jensen, then `⟨ψ̂, Ã ψ̂⟩ ≤ q_k^{-1} ⟨post, Ã post⟩`
  · have hψ0 : ψh E k l ≠ 0 := fun h0 => by
      rw [h0, dotProduct_zero] at hψ1; exact zero_ne_one hψ1
    obtain ⟨hxS, hxP⟩ := piR_post_mem h11 E k l
    have hψS : ψh E k l ∈ Replicas.S (fun f => Fin (dims n E.d f)) k :=
      Submodule.smul_mem _ _ hxS
    have hψP : pinProj E k *ᵥ ψh E k l = ψh E k l := by
      rw [ψh, mulVec_smul, hxP]
    have hpos : ∀ s, 0 < (star (ψh E k l) ⬝ᵥ (Γ.bandA n E.d (a / 2) k s g *ᵥ ψh E k l)).re :=
      fun s => (hBand s g).re_dotProduct_pos hψ0
    have hJ := Transport.lemma_7_1_4 (fun s => hBand s g) T (ψh E k l)
    have hMpos := (hMg g).re_dotProduct_pos hψ0
    have hlogJ := Real.log_le_log hMpos hJ
    rw [Real.log_prod (fun s _ => (Real.rpow_pos_of_pos (hpos s) _).ne')] at hlogJ
    simp only [Real.log_rpow (hpos _)] at hlogJ
    refine hlogJ.trans ?_
    have hpost0 : post E k ≠ 0 := fun h0 => by
      have : x = 0 := by simp [x, h0]
      have h2 : q E k l = 0 := by simp [q, show piR E.d k l *ᵥ post E k = 0 from this]
      linarith
    have hterm : ∀ s,
        Real.log (star (ψh E k l) ⬝ᵥ (Γ.bandA n E.d (a / 2) k s g *ᵥ ψh E k l)).re ≤
        -Real.log (q E k l) +
          Real.log (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re := by
      intro s
      obtain ⟨h16a, h16b, -⟩ := (h16 E Γ).1 (a / 2) ht k s g
      have hAt := h16b.posSemidef
      have hpp : 0 < (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re :=
        h16b.re_dotProduct_pos hpost0
      rw [(h16a _ hψS hψP).1]
      have h2 : (star (ψh E k l) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ ψh E k l)).re =
          (q E k l)⁻¹ * (star x ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ x)).re := by
        rw [ψh, mulVec_smul, Matrix.re_star_smul_dotProduct_smul, inv_pow, hrr]
      have hπ := labelObservable_indicator_proj
        (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k {Site.R}) (fun l' => l' = l)
      rw [← labelProj_eq_labelObservable_ite] at hπ
      have h3 := Matrix.re_dotProduct_proj_mulVec_le hπ.1 hπ.2 hAt
        (commute_piR_Atil Γ E.d ht k l s g) (post E k)
      rw [← Real.log_inv, ← Real.log_mul (inv_pos.mpr hq).ne' hpp.ne']
      refine Real.log_le_log ?_ ?_
      · rw [← (h16a _ hψS hψP).1]; exact hpos s
      · rw [h2]
        exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hq.le)
    calc ∑ s, T.weight s * Real.log
          (star (ψh E k l) ⬝ᵥ (Γ.bandA n E.d (a / 2) k s g *ᵥ ψh E k l)).re ≤
        ∑ s, T.weight s * (-Real.log (q E k l) +
          Real.log (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hterm s) (T.weight_nonneg s)
      _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, T.sum_weight, one_mul]

omit [∀ v, NeZero (n v)] in
/-- `ρ_Q` is a density. -/
theorem posSemidef_ρ (Q : Finset σ) : (D.ρ Q).PosSemidef :=
  (D.state.restrict (Finset.subset_univ Q)).psd

omit [∀ v, NeZero (n v)] in
theorem trace_ρ (Q : Finset σ) : (D.ρ Q).trace = 1 :=
  Arealaw.MState.trace_eq_one (D.state.restrict (Finset.subset_univ Q))

/-- D8.22.2–D8.22.3: for `Q` disjoint from `X`,
`⟨e^{± u F_Q}⟩_{post} ≤ z^{-k} Tr ρ_Q^{⊗k} e^{± u F_Q}`
`≤ z^{-k} exp{± u k S(Q) + 2C₀ k 𝓑 u² + O(log(k+1))}`. -/
theorem post_moment_le (h11 : Step_8_11.{u}) (E : TypicalSet D X) {Q : Finset σ}
    (hQ : Disjoint Q X) {C₀ c₁ 𝓑 Cp Np : ℝ}
    (hm : ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c₁ / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      Real.log (trace (TensorPower.tensorPow (k := k) (D.ρ Q) *
          cfc (fun x => Real.exp (ε * u * (x - k * D.S Q)))
            (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
              fun l => Real.log l.dim))).re ≤
        2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1))
    (k : ℕ) {u ε : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ c₁ / Real.sqrt 𝓑) (hε : ε = 1 ∨ ε = -1) :
    (star (post E k) ⬝ᵥ (labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k
        (physReg Q)) (fun l => Real.exp (ε * u * Real.log l.dim)) *ᵥ post E k)).re ≤
      E.z⁻¹ ^ k * Real.exp (ε * u * (k * D.S Q) +
        (2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1))) := by
  obtain ⟨-, -, -, hout⟩ := step_8_17 h11 E hQ
  rw [(hout k _).1]
  have hL : (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
      fun l => Real.exp (ε * u * Real.log l.dim)).PosSemidef := by
    rw [labelObservable_eq_resolutionHom]
    exact (labelProj_isOrthogonalResolution _).posSemidef_hom (isHermitian_labelProj _)
      fun l => (Real.exp_pos _).le
  -- D8.22.2: `ρ_{ψ,Q}^{⊗k} ≤ z^{-k} ρ_Q^{⊗k}` (D8.17)
  have h1 := hL.re_trace_mul_mono (hout k (fun l => Real.exp (ε * u * Real.log l.dim))).2
  rw [trace_mul_comm (labelObservable _ _), trace_mul_comm (labelObservable _ _),
    Matrix.smul_mul, trace_smul, Complex.smul_re, smul_eq_mul] at h1
  -- D8.22.3: D8.10 at `u`
  have hsplit : (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
      fun l => Real.exp (ε * u * Real.log l.dim)) = Real.exp (ε * u * (k * D.S Q)) •
      cfc (fun x => Real.exp (ε * u * (x - k * D.S Q)))
        (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
          fun l => Real.log l.dim) := by
    rw [cfc_labelObservable, ← labelObservable_const_mul]
    congr 1
    funext l
    simp only [Function.comp, ← Real.exp_add]
    ring_nf
  have h2 : (TensorPower.tensorPow (k := k) (D.ρ Q) *
      labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
        (fun l => Real.exp (ε * u * Real.log l.dim))).trace.re ≤
      Real.exp (ε * u * (k * D.S Q)) *
        Real.exp (2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1)) := by
    rw [hsplit, mul_smul_comm, trace_smul, Complex.smul_re, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left ((Real.le_exp_log _).trans (Real.exp_le_exp.mpr
      (hm k u hu0 hu ε hε))) (Real.exp_pos _).le
  rw [Real.exp_add]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by have := E.z_pos; positivity))

/-- The joint label projectors `π^α_{Q₁} π^β_{Q₂} π^γ_{Q₃}`. -/
noncomputable def jointProj (d k : ℕ) (Q₁ Q₂ Q₃ : Finset (Site σ))
    (p : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k))) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  Replicas.π (fun f => Fin (dims n d f)) k Q₁ p.1.1 *
    Replicas.π (fun f => Fin (dims n d f)) k Q₂ p.1.2 *
    Replicas.π (fun f => Fin (dims n d f)) k Q₃ p.2

omit [∀ v, NeZero (n v)] in
/-- Labels of `Q₁ ⊆ Q₂ ⊇ Q₃`, `Q₁ ∩ Q₃ = ∅` form a joint orthogonal resolution, and the label
functions of each region are functions of the joint label. -/
theorem jointProj_resolution (d k : ℕ) {Q₁ Q₂ Q₃ : Finset (Site σ)} (h12 : Q₁ ⊆ Q₂)
    (h32 : Q₃ ⊆ Q₂) (h13 : Disjoint Q₁ Q₃) :
    ∃ R : IsOrthogonalResolution (jointProj (n := n) d k Q₁ Q₂ Q₃),
      (∀ p, (jointProj (n := n) d k Q₁ Q₂ Q₃ p).IsHermitian) ∧
      (∀ f, labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q₁) f =
        R.hom fun p => (f p.1.1 : ℂ)) ∧
      (∀ f, labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q₂) f =
        R.hom fun p => (f p.1.2 : ℂ)) ∧
      (∀ f, labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q₃) f =
        R.hom fun p => (f p.2 : ℂ)) := by
  set ι := fun f : Site σ => Fin (dims n d f)
  have hU := labelProj_isOrthogonalResolution (Replicas.copyPerm ι k Q₁)
  have hUY := labelProj_isOrthogonalResolution (Replicas.copyPerm ι k Q₂)
  have hY := labelProj_isOrthogonalResolution (Replicas.copyPerm ι k Q₃)
  have c12 : ∀ α β, Commute (Replicas.π ι k Q₁ α) (Replicas.π ι k Q₂ β) := fun α β =>
    Replicas.step_6_4_8 ι k (Or.inl h12) α β
  have c23 : ∀ β γ, Commute (Replicas.π ι k Q₂ β) (Replicas.π ι k Q₃ γ) := fun β γ =>
    (Replicas.step_6_4_8 ι k (Or.inl h32) γ β).symm
  have c13 : ∀ α γ, Commute (Replicas.π ι k Q₁ α) (Replicas.π ι k Q₃ γ) := fun α γ =>
    Replicas.step_6_4_8 ι k (Or.inr h13) α γ
  have hP12 := hU.prod hUY c12
  have R := hP12.prod hY fun p γ => (c13 p.1 γ).mul_left (c23 p.2 γ)
  refine ⟨R, fun p => ?_, fun f => ?_, fun f => ?_, fun f => ?_⟩
  · exact ((((isHermitian_labelProj _ _).commute_iff (isHermitian_labelProj _ _)).mp
      (c12 _ _)).commute_iff
      (isHermitian_labelProj _ _)).mp ((c13 _ _).mul_left (c23 _ _))
  · rw [labelObservable_eq_resolutionHom, ← hU.prod_hom_fst hUY hP12, ← hP12.prod_hom_fst hY R]
    rfl
  · rw [labelObservable_eq_resolutionHom, ← hU.prod_hom_snd hUY hP12, ← hP12.prod_hom_fst hY R]
    rfl
  · rw [labelObservable_eq_resolutionHom, ← hP12.prod_hom_snd hY R]
    rfl

/-- D8.22.1 labelwise: `(w(α)^{-1} w(β)^{-1} w(γ))² ≤ K^{6C} e^{2t d_α} e^{2t d_β} e^{-2t d_γ}`
from `K^{-C} e^{-t d} ≤ w ≤ K^C e^{-t d}`. -/
theorem weight_cube_le {K C t wa wb wc da db dc : ℝ} (hK : 0 < K) (hwa : 0 < wa)
    (hwb : 0 < wb) (hwc : 0 < wc) (ha : K ^ (-C) * Real.exp (-t * da) ≤ wa)
    (hb : K ^ (-C) * Real.exp (-t * db) ≤ wb) (hc : wc ≤ K ^ C * Real.exp (-t * dc)) :
    (wa⁻¹ * wb⁻¹ * wc) ^ 2 ≤
      K ^ (6 * C) * (Real.exp (2 * t * da) * Real.exp (2 * t * db) * Real.exp (-(2 * t) * dc)) := by
  have inv_le : ∀ {w d : ℝ}, 0 < w → K ^ (-C) * Real.exp (-t * d) ≤ w →
      w⁻¹ ≤ K ^ C * Real.exp (t * d) := fun {w d} hw h => by
    calc w⁻¹ ≤ (K ^ (-C) * Real.exp (-t * d))⁻¹ := inv_anti₀ (by positivity) h
      _ = K ^ C * Real.exp (t * d) := by
          rw [mul_inv, ← Real.rpow_neg hK.le, neg_neg, ← Real.exp_neg]
          ring_nf
  calc (wa⁻¹ * wb⁻¹ * wc) ^ 2 ≤ (K ^ C * Real.exp (t * da) * (K ^ C * Real.exp (t * db)) *
        (K ^ C * Real.exp (-t * dc))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul (mul_le_mul (inv_le hwa ha) (inv_le hwb hb)
          (inv_nonneg.mpr hwb.le) (by positivity)) hc hwc.le (by positivity)) 2
    _ = _ := by
        simp only [Real.rpow_def_of_pos hK, ← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- D8.22.1–D8.22.4. Over the joint labels `(α, β, γ)` of `U, UY, Y` (they commute),
`Ã_{j,g} = (w(α)^{-1} w(β)^{-1} w(γ))² ≤ (k + 2)^{6C} e^{a F_U} e^{a F_{UY}} e^{-a F_Y}`;
Hölder with
exponents `3, 3, 3` and D8.17, D8.10 at `u = 3a` give
`log ⟨post_k, Ã_{j,g} post_k⟩ ≤ k a g^post_{j,g} + 18 C₀ k a² 𝓑 + k |log z| + O(log(k + 1))`. -/
theorem leaf_expectation (h11 : Step_8_11.{u}) (E : TypicalSet D X) {K : ℕ} {St : Type v}
    (Γ : Statuses σ K St X) {a C : ℝ} (ha : 0 < a)
    (hC : ∀ (k : ℕ) (Q : Finset (Site σ)) (l : IrrepLabel (Equiv.Perm (Fin k))),
      Replicas.π (fun f => Fin (dims n E.d f)) k Q l ≠ 0 →
        ((k : ℝ) + 2) ^ (-C) * Real.exp (-(a / 2) * Real.log l.dim) ≤
          Replicas.w (fun f => Fin (dims n E.d f)) (a / 2) l ∧
        Replicas.w (fun f => Fin (dims n E.d f)) (a / 2) l ≤
          ((k : ℝ) + 2) ^ C * Real.exp (-(a / 2) * Real.log l.dim))
    {C₀ c₁ 𝓑 : ℝ} (h3a : 3 * a ≤ c₁ / Real.sqrt 𝓑) (s : St) (g : Fin K) {Cp Np : Finset σ → ℝ}
    (hm : ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g, Γ.Y s g} : Finset (Finset σ)),
      ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c₁ / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        Real.log (trace (TensorPower.tensorPow (k := k) (D.ρ Q) *
            cfc (fun x => Real.exp (ε * u * (x - k * D.S Q)))
              (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
                fun l => Real.log l.dim))).re ≤
          2 * C₀ * k * 𝓑 * u ^ 2 + Cp Q + Np Q * Real.log (k + 1))
    (k : ℕ) (hpost : post E k ≠ 0) :
    Real.log (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re ≤
      k * a * gpost D Γ s g + 18 * C₀ * k * 𝓑 * a ^ 2 + k * |Real.log E.z| +
        6 * C * Real.log ((k : ℝ) + 2) +
        (Cp (Γ.U s g) + Cp (Γ.U s g ∪ Γ.Y s g) + Cp (Γ.Y s g) +
          (Np (Γ.U s g) + Np (Γ.U s g ∪ Γ.Y s g) + Np (Γ.Y s g)) * Real.log (k + 1)) / 3 := by
  set ι := fun f : Site σ => Fin (dims n E.d f)
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have ht : (0 : ℝ) ≤ a / 2 := by linarith
  have hz := E.z_pos
  obtain ⟨R, hH, eU, eUY, eY⟩ := jointProj_resolution (n := n) E.d k
    (physReg_subset (Finset.subset_union_left : Γ.U s g ⊆ Γ.U s g ∪ Γ.Y s g))
    (physReg_subset (Finset.subset_union_right : Γ.Y s g ⊆ Γ.U s g ∪ Γ.Y s g))
    (disjoint_physReg (Γ.disjoint_UY s g))
  set wt := IsOrthogonalResolution.weight (P := jointProj (n := n) E.d k (physReg (Γ.U s g))
    (physReg (Γ.U s g ∪ Γ.Y s g)) (physReg (Γ.Y s g))) (post E k)
  have hwt0 : ∀ p, 0 ≤ wt p := fun p => R.weight_nonneg hH _ p
  have hwtsum : ∑ p, wt p = (star (post E k) ⬝ᵥ post E k).re := R.sum_weight _
  have hpp : 0 < (star (post E k) ⬝ᵥ post E k).re :=
    (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hpost)).1
  obtain ⟨p₀, hp₀⟩ : ∃ p, 0 < wt p := by
    by_contra h
    push Not at h
    have : ∑ p, wt p ≤ 0 := Finset.sum_nonpos fun p _ => h p
    linarith
  set w := fun l : IrrepLabel (Equiv.Perm (Fin k)) => Replicas.w ι (a / 2) l
  have hw : ∀ l, 0 < w l := fun l => TensorPower.replicaLabelWeight_pos ι ht l
  -- D8.22.1: `Ã = (w(α)^{-1} w(β)^{-1} w(γ))²` on the joint label
  have eA : Γ.Atil n E.d (a / 2) k s g =
      R.hom fun p => ((((w p.1.1)⁻¹ * (w p.1.2)⁻¹ * w p.2) ^ 2 : ℝ) : ℂ) := by
    rw [Statuses.Atil, Replicas.W_inv _ ht, Replicas.W_inv _ ht]
    change (labelObservable (Replicas.copyPerm ι k (physReg (Γ.U s g))) (fun l => (w l)⁻¹) *
      labelObservable (Replicas.copyPerm ι k (physReg (Γ.U s g ∪ Γ.Y s g))) (fun l => (w l)⁻¹) *
      labelObservable (Replicas.copyPerm ι k (physReg (Γ.Y s g))) (fun l => w l)) ^ 2 = _
    rw [eU, eUY, eY, ← map_mul, ← map_mul, ← map_pow]
    congr 1
    funext p
    simp only [Pi.mul_apply, Pi.pow_apply]
    push_cast
    ring
  set Xf := fun p : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
    IrrepLabel (Equiv.Perm (Fin k)) => Real.exp (2 * (a / 2) * Real.log (p.1.1.dim : ℝ))
  set Yf := fun p : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
    IrrepLabel (Equiv.Perm (Fin k)) => Real.exp (2 * (a / 2) * Real.log (p.1.2.dim : ℝ))
  set Zf := fun p : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
    IrrepLabel (Equiv.Perm (Fin k)) => Real.exp (-(2 * (a / 2)) * Real.log (p.2.dim : ℝ))
  -- D8.22.1: `Ã ≤ (k + 2)^{6C} e^{a F_U} e^{a F_{UY}} e^{-a F_Y}`, labelwise
  have hterm : ∀ p, ((w p.1.1)⁻¹ * (w p.1.2)⁻¹ * w p.2) ^ 2 * wt p ≤
      ((k : ℝ) + 2) ^ (6 * C) * (wt p * (Xf p * Yf p * Zf p)) := by
    intro p
    rcases (hwt0 p).lt_or_eq with hp | hp
    · have hP : jointProj (n := n) E.d k (physReg (Γ.U s g)) (physReg (Γ.U s g ∪ Γ.Y s g))
          (physReg (Γ.Y s g)) p ≠ 0 := fun h0 => by
        have : wt p = 0 := by
          simp only [wt, IsOrthogonalResolution.weight, h0, zero_mulVec, dotProduct_zero]
          rfl
        linarith
      have hα : Replicas.π ι k (physReg (Γ.U s g)) p.1.1 ≠ 0 := fun h0 => hP (by
        rw [jointProj, h0, zero_mul, zero_mul])
      have hβ : Replicas.π ι k (physReg (Γ.U s g ∪ Γ.Y s g)) p.1.2 ≠ 0 := fun h0 => hP (by
        rw [jointProj, h0, mul_zero, zero_mul])
      have hγ : Replicas.π ι k (physReg (Γ.Y s g)) p.2 ≠ 0 := fun h0 => hP (by
        rw [jointProj, h0, mul_zero])
      have hb := weight_cube_le hk2 (hw p.1.1) (hw p.1.2) (hw p.2) (hC k _ _ hα).1
        (hC k _ _ hβ).1 (hC k _ _ hγ).2
      calc _ ≤ ((k : ℝ) + 2) ^ (6 * C) * (Xf p * Yf p * Zf p) * wt p :=
            mul_le_mul_of_nonneg_right hb (hwt0 p)
        _ = _ := by ring
    · rw [← hp]; simp
  -- D8.22.2–D8.22.3: the three moments
  have hXc : ∀ p, Xf p ^ 3 = Real.exp (1 * (3 * a) * Real.log (p.1.1.dim : ℝ)) := fun p => by
    simp only [Xf, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hYc : ∀ p, Yf p ^ 3 = Real.exp (1 * (3 * a) * Real.log (p.1.2.dim : ℝ)) := fun p => by
    simp only [Yf, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hZc : ∀ p, Zf p ^ 3 = Real.exp (-1 * (3 * a) * Real.log (p.2.dim : ℝ)) := fun p => by
    simp only [Zf, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hXU : Disjoint (Γ.U s g) X := (Γ.disjoint_XU s g).symm
  have hXUY : Disjoint (Γ.U s g ∪ Γ.Y s g) X :=
    Finset.disjoint_union_left.mpr ⟨(Γ.disjoint_XU s g).symm, (Γ.disjoint_XY s g).symm⟩
  have hXY : Disjoint (Γ.Y s g) X := (Γ.disjoint_XY s g).symm
  have h3a0 : 0 ≤ 3 * a := by linarith
  have mA := post_moment_le h11 E hXU (hm (Γ.U s g) (by simp)) k h3a0 h3a (Or.inl rfl)
  have mB := post_moment_le h11 E hXUY (hm (Γ.U s g ∪ Γ.Y s g) (by simp)) k h3a0 h3a
    (Or.inl rfl)
  have mC := post_moment_le h11 E hXY (hm (Γ.Y s g) (by simp)) k h3a0 h3a (Or.inr rfl)
  rw [eU, Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_ofReal_mulVec] at mA
  rw [eUY, Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_ofReal_mulVec] at mB
  rw [eY, Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_ofReal_mulVec] at mC
  set A := ∑ p, wt p * Xf p ^ 3
  set B := ∑ p, wt p * Yf p ^ 3
  set Cc := ∑ p, wt p * Zf p ^ 3
  have hA : A = ∑ i, Real.exp (1 * (3 * a) * Real.log (i.1.1.dim : ℝ)) * wt i :=
    Finset.sum_congr rfl fun p _ => by rw [hXc, mul_comm]
  have hB : B = ∑ i, Real.exp (1 * (3 * a) * Real.log (i.1.2.dim : ℝ)) * wt i :=
    Finset.sum_congr rfl fun p _ => by rw [hYc, mul_comm]
  have hCc : Cc = ∑ i, Real.exp (-1 * (3 * a) * Real.log (i.2.dim : ℝ)) * wt i :=
    Finset.sum_congr rfl fun p _ => by rw [hZc, mul_comm]
  have hA0 : 0 < A := Finset.sum_pos' (fun p _ => mul_nonneg (hwt0 p) (by positivity))
    ⟨p₀, Finset.mem_univ _, mul_pos hp₀ (by positivity)⟩
  have hB0 : 0 < B := Finset.sum_pos' (fun p _ => mul_nonneg (hwt0 p) (by positivity))
    ⟨p₀, Finset.mem_univ _, mul_pos hp₀ (by positivity)⟩
  have hC0 : 0 < Cc := Finset.sum_pos' (fun p _ => mul_nonneg (hwt0 p) (by positivity))
    ⟨p₀, Finset.mem_univ _, mul_pos hp₀ (by positivity)⟩
  -- D8.22.1: Hölder with exponents `3, 3, 3` for the commuting positive factors
  have hH3 := Real.sum_mul_mul_le_rpow_one_third Finset.univ (w := wt) (X := Xf) (Y := Yf)
    (Z := Zf) (fun p _ => hwt0 p) (fun p _ => by positivity) (fun p _ => by positivity)
    (fun p _ => by positivity) hA0 hB0 hC0
  have hexp : (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re =
      ∑ p, ((w p.1.1)⁻¹ * (w p.1.2)⁻¹ * w p.2) ^ 2 * wt p := by
    rw [eA, Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_ofReal_mulVec]
  have hle : (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re ≤
      ((k : ℝ) + 2) ^ (6 * C) * (A ^ (1 / 3 : ℝ) * B ^ (1 / 3 : ℝ) * Cc ^ (1 / 3 : ℝ)) := by
    rw [hexp]
    calc _ ≤ ∑ p, ((k : ℝ) + 2) ^ (6 * C) * (wt p * (Xf p * Yf p * Zf p)) :=
          Finset.sum_le_sum fun p _ => hterm p
      _ = ((k : ℝ) + 2) ^ (6 * C) * ∑ p, wt p * (Xf p * Yf p * Zf p) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH3 (Real.rpow_pos_of_pos hk2 _).le
  have hpos : 0 < (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re := by
    rw [hexp]
    exact Finset.sum_pos' (fun p _ => mul_nonneg (sq_nonneg _) (hwt0 p))
      ⟨p₀, Finset.mem_univ _, mul_pos (pow_pos (mul_pos (mul_pos (inv_pos.mpr (hw _))
        (inv_pos.mpr (hw _))) (hw _)) 2) hp₀⟩
  -- D8.22.4: `⅓ log` of each moment, added
  have hlog := Real.log_le_log hpos hle
  have p1 : 0 < ((k : ℝ) + 2) ^ (6 * C) := Real.rpow_pos_of_pos hk2 _
  have pa := Real.rpow_pos_of_pos hA0 (1 / 3 : ℝ)
  have pb := Real.rpow_pos_of_pos hB0 (1 / 3 : ℝ)
  have pc := Real.rpow_pos_of_pos hC0 (1 / 3 : ℝ)
  rw [Real.log_mul p1.ne' (mul_pos (mul_pos pa pb) pc).ne', Real.log_mul (mul_pos pa pb).ne'
    pc.ne', Real.log_mul pa.ne' pb.ne', Real.log_rpow hk2, Real.log_rpow hA0,
    Real.log_rpow hB0, Real.log_rpow hC0] at hlog
  have hzk : ∀ x : ℝ, Real.log (E.z⁻¹ ^ k * Real.exp x) = k * -Real.log E.z + x := fun x => by
    rw [Real.log_mul (pow_pos (inv_pos.mpr hz) k).ne' (Real.exp_pos _).ne', Real.log_pow,
      Real.log_inv, Real.log_exp]
  have lA := Real.log_le_log hA0 (hA ▸ mA)
  have lB := Real.log_le_log hB0 (hB ▸ mB)
  have lC := Real.log_le_log hC0 (hCc ▸ mC)
  rw [hzk] at lA lB lC
  have habs : |Real.log E.z| = -Real.log E.z :=
    abs_of_nonpos (Real.log_nonpos hz.le (E.z_le_one h11))
  rw [habs, gpost]
  nlinarith

omit [∀ v, NeZero (n v)] in
theorem natCast_mul_avg {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
    (T : Transport.MeanTree St) (f : St → Fin K → ℝ) :
    (K : ℝ) * avg T f = ∑ g, ∑ s, T.weight s * f s g := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [avg]
  · rw [avg, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hK.ne'), one_mul]

omit [∀ v, NeZero (n v)] in
theorem neg_sum_abs_le_avg {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
    (T : Transport.MeanTree St) (f : St → Fin K → ℝ) :
    -∑ s, ∑ g, |f s g| ≤ avg T f := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [avg]
  have hM : ∀ s g, -∑ s, ∑ g, |f s g| ≤ f s g := fun s g => by
    have h1 : |f s g| ≤ ∑ g, |f s g| :=
      Finset.single_le_sum (f := fun g => |f s g|) (fun _ _ => abs_nonneg _) (Finset.mem_univ g)
    have h2 : ∑ g, |f s g| ≤ ∑ s, ∑ g, |f s g| :=
      Finset.single_le_sum (f := fun s => ∑ g, |f s g|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    linarith [neg_abs_le (f s g)]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [avg, le_inv_mul_iff₀ hK']
  set M := -∑ s, ∑ g, |f s g|
  calc (K : ℝ) * M = ∑ g : Fin K, ∑ s, T.weight s * M := by
        rw [Finset.sum_congr rfl fun g _ => by rw [← Finset.sum_mul, T.sum_weight, one_mul],
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (hM s g) (T.weight_nonneg s)

end Sharp

/-- D8.22 (`comparator:sharp-upper`).
`log ⟨post_k, Ã_{j,g} post_k⟩ ≤ k a g^post_{j,g} + C k a² 𝓑 + k |log z| + O(log(k + 1))`, hence
(comparator:sharp-upper). -/
theorem step_8_22 (h1 : Step_8_1.{u, v}) (h10 : Step_8_10.{u}) (h11 : Step_8_11.{u})
    (h15 : Step_8_15.{u, v}) (h16 : Step_8_16.{u, v}) : Step_8_22.{u, v} := by
  intro C₀ c₀ hC₀ hc₀
  obtain ⟨c₁, hc₁, H⟩ := h10 C₀ c₀ hC₀ hc₀
  refine ⟨c₁ / 3, max (18 * C₀) 1, by positivity, by positivity, ?_⟩
  intro σ _ _ n _ D X E K St _ _ Γ l hl 𝓑 h𝓑 a ha hac
  set Cm := max (18 * C₀) 1
  have h𝓑1 := h𝓑.one_le
  have hs : 0 < Real.sqrt 𝓑 := Real.sqrt_pos.mpr (by linarith)
  have h3a : 3 * a ≤ c₁ / Real.sqrt 𝓑 := by
    rw [div_div] at hac
    rw [le_div_iff₀ hs]
    rw [le_div_iff₀ (by positivity)] at hac
    linarith
  have hz := E.z_pos
  have hz1 := E.z_le_one h11
  have hd : (0 : ℝ) < E.d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne E.d)
  have ht : 0 < a / 2 := by linarith
  obtain ⟨Cw, hCw⟩ := exists_w_bounds (fun f : Site σ => Fin (dims n E.d f)) ht
  -- D8.10 for each of the regions `U, UY, Y` (D8.5)
  have hmom : ∀ s g, ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g, Γ.Y s g} : Finset (Finset σ)),
      ∃ Cp Np : ℝ, ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c₁ / Real.sqrt 𝓑 → ∀ ε : ℝ,
        (ε = 1 ∨ ε = -1) →
        Real.log (trace (TensorPower.tensorPow (k := k) (D.ρ Q) *
            cfc (fun x => Real.exp (ε * u * (x - k * D.S Q)))
              (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) Q) k)
                fun l => Real.log l.dim))).re ≤
          2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1) := by
    intro s g Q hQ
    have hQ5 : Q ∈ ({X ∪ Γ.U s g, Γ.V s g, Γ.Y s g, Γ.U s g, Γ.U s g ∪ Γ.Y s g} :
        Finset (Finset σ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
      tauto
    exact H (D.ρ Q) (posSemidef_ρ Q) (trace_ρ Q) 𝓑 (D.S Q) h𝓑1
      (fun u hu => h𝓑.bound s g Q hQ5 u hu)
  choose! Cp Np hCp using hmom
  set Cs : ℝ := ∑ s, ∑ g, (|Cp s g (Γ.U s g)| + |Cp s g (Γ.U s g ∪ Γ.Y s g)| +
    |Cp s g (Γ.Y s g)|)
  set Ns : ℝ := ∑ s, ∑ g, (|Np s g (Γ.U s g)| + |Np s g (Γ.U s g ∪ Γ.Y s g)| +
    |Np s g (Γ.Y s g)|)
  obtain ⟨c', N', hc', ε', -, hq⟩ := hl
  -- the uniform leaf bound (D8.22.1–D8.22.4)
  set Lc : ℕ → ℝ := fun k => 18 * C₀ * k * 𝓑 * a ^ 2 + k * |Real.log E.z| +
    6 * Cw * Real.log ((k : ℝ) + 2) + (Cs + Ns * Real.log (k + 1))
  have hleaf : ∀ (k : ℕ) (s : St) (g : Fin K), post E k ≠ 0 →
      Real.log (star (post E k) ⬝ᵥ (Γ.Atil n E.d (a / 2) k s g *ᵥ post E k)).re ≤
        k * a * gpost D Γ s g + Lc k := by
    intro k s g hpost
    refine (leaf_expectation h11 E Γ ha hCw h3a s g (hCp s g) k hpost).trans ?_
    simp only [Lc]
    have hlog1 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith [(k.cast_nonneg :
      (0 : ℝ) ≤ k)])
    have hCs : |Cp s g (Γ.U s g)| + |Cp s g (Γ.U s g ∪ Γ.Y s g)| + |Cp s g (Γ.Y s g)| ≤ Cs :=
      (Finset.single_le_sum (f := fun g => |Cp s g (Γ.U s g)| +
        |Cp s g (Γ.U s g ∪ Γ.Y s g)| + |Cp s g (Γ.Y s g)|) (fun _ _ => by positivity)
          (Finset.mem_univ g)).trans
        (Finset.single_le_sum (f := fun s => ∑ g, (|Cp s g (Γ.U s g)| +
          |Cp s g (Γ.U s g ∪ Γ.Y s g)| + |Cp s g (Γ.Y s g)|))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ s))
    have hNs : |Np s g (Γ.U s g)| + |Np s g (Γ.U s g ∪ Γ.Y s g)| + |Np s g (Γ.Y s g)| ≤ Ns :=
      (Finset.single_le_sum (f := fun g => |Np s g (Γ.U s g)| +
        |Np s g (Γ.U s g ∪ Γ.Y s g)| + |Np s g (Γ.Y s g)|) (fun _ _ => by positivity)
          (Finset.mem_univ g)).trans
        (Finset.single_le_sum (f := fun s => ∑ g, (|Np s g (Γ.U s g)| +
          |Np s g (Γ.U s g ∪ Γ.Y s g)| + |Np s g (Γ.Y s g)|))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ s))
    have e1 := le_abs_self (Cp s g (Γ.U s g))
    have e2 := le_abs_self (Cp s g (Γ.U s g ∪ Γ.Y s g))
    have e3 := le_abs_self (Cp s g (Γ.Y s g))
    have f1 := le_abs_self (Np s g (Γ.U s g))
    have f2 := le_abs_self (Np s g (Γ.U s g ∪ Γ.Y s g))
    have f3 := le_abs_self (Np s g (Γ.Y s g))
    have g0 : 0 ≤ |Cp s g (Γ.U s g)| + |Cp s g (Γ.U s g ∪ Γ.Y s g)| + |Cp s g (Γ.Y s g)| := by
      positivity
    have g1 : 0 ≤ |Np s g (Γ.U s g)| + |Np s g (Γ.U s g ∪ Γ.Y s g)| + |Np s g (Γ.Y s g)| := by
      positivity
    have hN : (Np s g (Γ.U s g) + Np s g (Γ.U s g ∪ Γ.Y s g) + Np s g (Γ.Y s g)) *
        Real.log (k + 1) ≤ Ns * Real.log (k + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog1
    have hN0 : 0 ≤ Ns * Real.log (k + 1) := mul_nonneg (g1.trans hNs) hlog1
    linarith
  -- D8.22.5: assemble with D8.15 and D8.21
  set base : ℝ := 2 * Real.log E.d - Real.log E.z
  have hmain : ∀ (k : ℕ) (T : Transport.MeanTree St), -Real.log (N2 D Γ E T a k (l k)) ≤
      k * base + (1 / 2) * (a * K) * k * avg T (gpost D Γ) +
        (K / 2) * (18 * C₀ * k * 𝓑 * a ^ 2 + k * |Real.log E.z|) +
        (1 + K / 2) * (-Real.log c' + N' * Real.log ((k : ℝ) + 1)) +
        (K / 2) * (6 * Cw * Real.log ((k : ℝ) + 2) + (Cs + Ns * Real.log (k + 1))) := by
    intro k T
    have hq0 : 0 < q E k (l k) := lt_of_lt_of_le (by positivity) (hq k).1
    have hpost : post E k ≠ 0 := fun h0 => by
      have : q E k (l k) = 0 := by simp [q, h0]
      linarith
    obtain ⟨ha21, hb21, hc21⟩ := step_8_21 h1 h11 h16 E Γ T ha k (l k) hq0
    set Lψ := (star (ψh E k (l k)) ⬝ᵥ (CFC.log (Γ.root n E.d T (a / 2) k) *ᵥ ψh E k (l k))).re
    -- D8.21: `⟨ψ̂, log 𝓜 ψ̂⟩ ≤ ∑_g (-log q_k + ∑_j w_j log ⟨post, Ã_{j,g} post⟩)`
    have hL : Lψ ≤ ∑ g : Fin K, (-Real.log (q E k (l k)) +
        ∑ s, T.weight s * (k * a * gpost D Γ s g + Lc k)) := by
      rw [hb21]
      refine Finset.sum_le_sum fun g _ => ((hc21 g).1.trans (hc21 g).2).trans ?_
      gcongr with s
      · exact T.weight_nonneg s
      · exact hleaf k s g hpost
    have hsum : ∑ g : Fin K, (-Real.log (q E k (l k)) +
        ∑ s, T.weight s * (k * a * gpost D Γ s g + Lc k)) =
        K * (-Real.log (q E k (l k))) + a * k * (K * avg T (gpost D Γ)) + K * Lc k := by
      have e1 : ∀ g : Fin K, ∑ s, T.weight s * (k * a * gpost D Γ s g + Lc k) =
          a * k * ∑ s, T.weight s * gpost D Γ s g + Lc k := fun g => by
        rw [Finset.sum_congr rfl fun s _ => (show T.weight s * (k * a * gpost D Γ s g + Lc k) =
          a * k * (T.weight s * gpost D Γ s g) + T.weight s * Lc k by ring),
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, T.sum_weight, one_mul]
      rw [Finset.sum_congr rfl fun g _ => by rw [e1 g], natCast_mul_avg, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    -- D8.15, D8.21.1: `N² ≥ (z/d_*²)^k q_k e^{-2s ⟨ψ̂, log 𝓜 ψ̂⟩}`
    have h15' := h15 D E Γ T a ha.le k (l k)
    have hlow : (E.z / E.d ^ 2) ^ k * (q E k (l k) * Real.exp (-2 * (1 / 4) * Lψ)) ≤
        N2 D Γ E T a k (l k) :=
      le_trans (mul_le_mul_of_nonneg_left ha21 (by positivity)) h15'
    have hP0 : 0 < (E.z / E.d ^ 2) ^ k * (q E k (l k) * Real.exp (-2 * (1 / 4) * Lψ)) := by
      positivity
    have hlog := Real.log_le_log hP0 hlow
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hq0.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_pow, Real.log_div hz.ne' (by positivity), Real.log_pow] at hlog
    have hlq : -Real.log (q E k (l k)) ≤ -Real.log c' + N' * Real.log ((k : ℝ) + 1) := by
      have := Real.log_le_log (by positivity) (hq k).1
      rw [Real.log_mul hc'.ne' (by positivity), Real.log_rpow (by positivity)] at this
      linarith
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hlq' := mul_le_mul_of_nonneg_left hlq (by positivity : (0 : ℝ) ≤ 1 + K / 2)
    simp only [base, Lc] at hsum ⊢
    push_cast at hlog
    linarith [hL, hsum, hlq']
  -- `o_k(1)`: the remainder, uniform in the tree
  set Gk : ℕ → ℝ := fun k => (1 + K / 2) * (-Real.log c' + N' * Real.log ((k : ℝ) + 1)) +
    (K / 2) * (6 * Cw * Real.log ((k : ℝ) + 2) + (Cs + Ns * Real.log (k + 1)))
  set M := ∑ s, ∑ g, |gpost D Γ s g|
  refine ⟨fun k => if k = 0 then |base| + (1 / 2) * (a * K) * M else Gk k / k, ?_,
    fun k _ T => ?_⟩
  · have hev : (fun k : ℕ => Gk k / k) =ᶠ[atTop]
        fun k => if k = 0 then |base| + (1 / 2) * (a * K) * M else Gk k / k := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      simp only [Nat.one_le_iff_ne_zero.mp hk, if_false]
    refine Tendsto.congr' hev ?_
    have h := (((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((1 + K / 2) * (-Real.log c') + K / 2 * Cs)).add
      ((Real.tendsto_log_natCast_add_div 1).const_mul ((1 + K / 2) * N' + K / 2 * Ns))).add
      ((Real.tendsto_log_natCast_add_div 2).const_mul (K / 2 * (6 * Cw)))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun k => ?_
    simp only [Gk]
    ring
  · have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hcm1 : 1 ≤ Cm := le_max_right _ _
    have hcm2 : 18 * C₀ ≤ Cm := le_max_left _ _
    have habs := abs_nonneg (Real.log E.z)
    have hextra : 0 ≤ Cm * (a * 𝓑 + |Real.log E.z| / a) := by positivity
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.cast_zero, div_zero, if_true]
      have := neg_sum_abs_le_avg T (gpost D Γ)
      have h2 : (1 / 2) * (a * K) * (-M) ≤ (1 / 2) * (a * K) * avg T (gpost D Γ) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      have h3 : 0 ≤ (1 / 2) * (a * K) * (Cm * (a * 𝓑 + |Real.log E.z| / a)) := by positivity
      linarith [neg_abs_le base]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      simp only [hk, if_false]
      rw [div_le_iff₀ hk']
      have hm := hmain k T
      have e1 : (K / 2) * (18 * C₀ * k * 𝓑 * a ^ 2) ≤ (1 / 2) * (a * K) * (Cm * (a * 𝓑)) * k := by
        have : 18 * C₀ * a ≤ Cm * a := mul_le_mul_of_nonneg_right hcm2 ha.le
        have h4 : 0 ≤ (K / 2) * k * 𝓑 * a := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h4]
      have e2 : (K / 2) * (k * |Real.log E.z|) ≤
          (1 / 2) * (a * K) * (Cm * (|Real.log E.z| / a)) * k := by
        have h5 : (1 / 2) * (a * K) * (Cm * (|Real.log E.z| / a)) * k =
            (K / 2) * (k * |Real.log E.z|) * Cm := by field_simp
        rw [h5]
        exact le_mul_of_one_le_right (by positivity) hcm1
      calc -Real.log (N2 D Γ E T a k (l k)) ≤ _ := hm
        _ ≤ (base + 2 * (1 / 4) * (a * K) * (avg T (gpost D Γ) +
              Cm * (a * 𝓑 + |Real.log E.z| / a)) + Gk k / k) * k := by
            have hexpand : (base + 2 * (1 / 4) * (a * K) * (avg T (gpost D Γ) +
                Cm * (a * 𝓑 + |Real.log E.z| / a)) + Gk k / k) * k =
                k * base + (1 / 2) * (a * K) * k * avg T (gpost D Γ) +
                  (1 / 2) * (a * K) * (Cm * (a * 𝓑)) * k +
                  (1 / 2) * (a * K) * (Cm * (|Real.log E.z| / a)) * k + Gk k := by
              have e3 : Gk k / k * k = Gk k := div_mul_cancel₀ _ hk'.ne'
              rw [add_mul, e3]
              ring
            rw [hexpand]
            simp only [Gk]
            linarith [e1, e2]

end AreaLaw.Comparators
