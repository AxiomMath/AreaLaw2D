import AreaLaw.S09_Scanner.Histories
import AreaLaw.S09_Scanner.ComparatorData

/-!
# §9.2 The entropy cost of the old splits and the entropy production per round (D9.10, D9.11)

Digest `digest/09-scanner.md` D9.10–D9.11, paper `paper/sections/08-scanner.tex` 416–455.
Graph-level (Map.md, Dimension: `any d`).

Some declarations here come from the v1 files `OpenAI/ReplicaTransportEnergy.lean`,
`OpenAI/Scan/ActualChargeEntropySum.lean`, `OpenAI/Scan/OldStateIntegral.lean`,
`OpenAI/Scan/SplitEntropyBound.lean`, whose header records them as ported or adapted from
`LionSR/QICLean` and `LionSR/TNLean` (see `NOTICE`).
-/

open scoped Matrix ComplexOrder MatrixOrder
open Finset MeasureTheory Arealaw Entropy
open OpenAI (pureState)

namespace AreaLaw.Scanner

open Transport (Round EnergyTerms PYF)
open Comparators (physReg)

universe u

/-! ## The split entropies -/

section Eta

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- `η_θ = I_θ(X:F|U) ≥ 0` (strong subadditivity, D2.2). -/
theorem η_nonneg {X U F : Finset V} (hXU : Disjoint X U) (hXF : Disjoint X F)
    (hUF : Disjoint U F) (θ : SiteConfig n → ℂ) : 0 ≤ Replicas.η X U F θ := by
  unfold Replicas.η
  split_ifs
  · exact (step_2_2 _ _ _ _ hXU hXF hUF).1
  · exact le_rfl

omit [Fintype V] in
theorem one_le_card_reg [∀ v, NeZero (n v)] (X : Finset V) :
    (1 : ℝ) ≤ Fintype.card (Reg (fun v => Fin (n v)) X) := by
  exact_mod_cast Fintype.card_pos

/-- `η_θ = S_θ(X|U) - S_θ(X|UF) ≤ 2 log dim 𝓗_X` (D2.2 item 4). -/
theorem η_le [∀ v, NeZero (n v)] {X U F : Finset V} (hXU : Disjoint X U) (hXF : Disjoint X F)
    (θ : SiteConfig n → ℂ) :
    Replicas.η X U F θ ≤ 2 * Real.log (Fintype.card (Reg (fun v => Fin (n v)) X)) := by
  have h0 := Real.log_nonneg (one_le_card_reg (n := n) X)
  unfold Replicas.η
  split_ifs with hθ
  · set ρ := pureState (θ ∘ univEquiv) hθ
    have h1 := (step_2_2 ρ (subset_univ X) (subset_univ U) (empty_subset _) hXU
      (disjoint_empty_right _) (disjoint_empty_right _)).2.2.2.1
    have h2 := (step_2_2 ρ (subset_univ X) (subset_univ (U ∪ F)) (empty_subset _)
      (disjoint_union_right.2 ⟨hXU, hXF⟩) (disjoint_empty_right _)
      (disjoint_empty_right _)).2.2.2.1
    have he : ρ.toSubState.regionEntropy (union_subset (union_subset (subset_univ X)
        (subset_univ U)) (subset_univ F)) = ρ.toSubState.regionEntropy
        (union_subset (subset_univ X) (subset_univ (U ∪ F))) :=
      ρ.toSubState.regionEntropy_congr (union_assoc X U F) _ _
    simp only [condEntropy] at h1 h2
    rw [condMutualInfo, he]
    have := (abs_le.1 h1).2
    have := (abs_le.1 h2).1
    linarith
  · linarith

omit [Fintype V] in
theorem log_card_reg_mono [∀ v, NeZero (n v)] {X Y : Finset V} (h : X ⊆ Y) :
    Real.log (Fintype.card (Reg (fun v => Fin (n v)) X)) ≤
      Real.log (Fintype.card (Reg (fun v => Fin (n v)) Y)) := by
  refine Real.log_le_log (by linarith [one_le_card_reg (n := n) X]) ?_
  have hc (Z : Finset V) : Fintype.card (Reg (fun v => Fin (n v)) Z) = ∏ v ∈ Z, n v := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact Finset.prod_coe_sort Z (fun v => n v)
  rw [hc, hc]
  exact_mod_cast Finset.prod_le_prod_of_subset_of_one_le' h fun i _ _ =>
    Nat.one_le_iff_ne_zero.2 (NeZero.ne _)

variable {π : PYF V} (hπ : π.IsPartition) (D : Finset V)
include hπ

/-- The split entropy `η_{i,j}` of one band is nonnegative. -/
theorem splitBandEta_nonneg (θ : SiteConfig n → ℂ) : 0 ≤ Round.splitBandEta π D θ := by
  unfold Round.splitBandEta
  split_ifs
  · exact η_nonneg (disjoint_sdiff.mono_left inter_subset_left)
      (hπ.2.2.1.mono_left inter_subset_right) (hπ.2.2.1.mono_left sdiff_subset) θ
  · exact η_nonneg (disjoint_sdiff.mono_left inter_subset_left)
      (hπ.1.symm.mono_left inter_subset_right) (hπ.1.symm.mono_left sdiff_subset) θ

/-- D9.10. `η_{i,j} ≤ 2 log dim 𝓗_{X̃_i}`. -/
theorem splitBandEta_le [∀ v, NeZero (n v)] (θ : SiteConfig n → ℂ) :
    Round.splitBandEta π D θ ≤ 2 * Real.log (Fintype.card (Reg (fun v => Fin (n v)) D)) := by
  have hm := log_card_reg_mono (n := n) (inter_subset_left : D ∩ π.Y ⊆ D)
  unfold Round.splitBandEta
  split_ifs
  · linarith [η_le (n := n) (X := D ∩ π.Y) (U := π.Y \ D)
      (disjoint_sdiff.mono_left inter_subset_left) (hπ.2.2.1.mono_left inter_subset_right) θ]
  · linarith [η_le (n := n) (X := D ∩ π.Y) (U := π.Y \ D)
      (disjoint_sdiff.mono_left inter_subset_left) (hπ.1.symm.mono_left inter_subset_right) θ]

omit hπ in
theorem continuous_splitBandEta :
    Continuous fun θ : Replicas.Sphere (fun v => Fin (n v)) => Round.splitBandEta π D θ.1 := by
  unfold Round.splitBandEta
  split_ifs
  · exact (Replicas.continuousOn_η _ _ _).comp_continuous continuous_subtype_val fun θ => θ.2
  · exact (Replicas.continuousOn_η _ _ _).comp_continuous continuous_subtype_val fun θ => θ.2

end Eta

/-! ## Integrals against the transported states -/

section Round

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)] {K : ℕ}
  {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)] (R : Round V K H C)

theorem m_nonneg (u : ℝ) : 0 ≤ Transport.m (1 / 4) u :=
  (Real.sinhRatioDensity_pos ⟨by norm_num, by norm_num⟩ u).le

omit [∀ v, NeZero (n v)] in
/-- A move entropy `η_{h,c,g}` is nonnegative (D9.11.1). -/
theorem eta_nonneg (hR : R.IsAdmissible) (h : H) (c : C h) (g : Fin K) (θ : SiteConfig n → ℂ) :
    0 ≤ R.eta h c g θ := by
  have hm := hR.move_subset h c g
  have hπ := hR.old_isPartition h g
  unfold Round.eta
  revert hm
  cases R.move h c g with
  | stay => intro _; exact le_rfl
  | toP x =>
    intro hm
    exact η_nonneg (X := x) disjoint_sdiff (hπ.2.2.1.mono_left hm)
      (hπ.2.2.1.mono_left sdiff_subset) θ
  | toF x =>
    intro hm
    exact η_nonneg (X := x) disjoint_sdiff (hπ.1.symm.mono_left hm)
      (hπ.1.symm.mono_left sdiff_subset) θ

variable {t : ℝ} {k : ℕ} {pre : Transport.Config n k → ℂ} {p : unitInterval}

/-- Continuous functions of `θ` are integrable against `μ_σ` for a density `σ` on `𝒮_k`. -/
theorem integrable_of_isSymDensity {ρ : Matrix (Transport.Config n k) (Transport.Config n k) ℂ}
    (hσ : Transport.IsSymDensity n ρ) {f : Replicas.Sphere (fun v => Fin (n v)) → ℝ}
    (hf : Continuous f) : Integrable f (Replicas.μ (fun v => Fin (n v)) k ρ) := by
  have := Replicas.eq_replicas_husimi (fun v => Fin (n v)) k hσ.1 hσ.2.1 hσ.2.2
  exact hf.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- `u ↦ m_s(u) ∫ f dμ_{σ_{j,u}}` is integrable for continuous `f`. -/
theorem integrable_m_mul_integral (hR : R.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : R.CrossBandCommute n t k) (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k)
    (hpre : pre ≠ 0) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : Round.Leaf H C)
    {f : Replicas.Sphere (fun v => Fin (n v)) → ℝ} (hf : Continuous f) :
    Integrable fun u => Transport.m (1 / 4) u *
      ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) := by
  refine (R.integrable_m_mul_trace_state hR ht hcomm pre p j
    (Transport.Q (fun v => Fin (n v)) k f)).congr (Filter.Eventually.of_forall fun u => ?_)
  have hσ := R.isSymDensity_state hR ht hcomm hpreS hpre hp0 hp1 j u
  simp only
  rw [Transport.trace_mul_Q hσ.1 hf, integral_complex_ofReal, Complex.ofReal_re]

/-- `∫ m_s(u) ∫ f dμ_{σ_{j,u}} du ≥ 0` for `f ≥ 0`. -/
theorem integral_m_mul_integral_nonneg (j : Round.Leaf H C)
    {f : Replicas.Sphere (fun v => Fin (n v)) → ℝ} (hf : ∀ θ, 0 ≤ f θ) :
    0 ≤ ∫ u, Transport.m (1 / 4) u *
      ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) :=
  integral_nonneg fun u => mul_nonneg (m_nonneg u) (integral_nonneg hf)

/-- Monotonicity of `∫ m_s(u) ∫ f dμ_{σ_{j,u}} du` in a continuous `f`. -/
theorem integral_m_mul_integral_mono (hR : R.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : R.CrossBandCommute n t k) (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k)
    (hpre : pre ≠ 0) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : Round.Leaf H C)
    {f f' : Replicas.Sphere (fun v => Fin (n v)) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hle : ∀ θ, f θ ≤ f' θ) :
    ∫ u, Transport.m (1 / 4) u *
        ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) ≤
      ∫ u, Transport.m (1 / 4) u *
        ∫ θ, f' θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) := by
  refine integral_mono (integrable_m_mul_integral R hR ht hcomm hpreS hpre hp0 hp1 j hf)
    (integrable_m_mul_integral R hR ht hcomm hpreS hpre hp0 hp1 j hf') fun u => ?_
  have hσ := R.isSymDensity_state hR ht hcomm hpreS hpre hp0 hp1 j u
  exact mul_le_mul_of_nonneg_left (integral_mono (integrable_of_isSymDensity hσ hf)
    (integrable_of_isSymDensity hσ hf') hle) (m_nonneg u)

/-- Linearity of `∫ m_s(u) ∫ f dμ_{σ_{j,u}} du` over a finite sum of continuous functions. -/
theorem integral_m_mul_integral_sum (hR : R.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : R.CrossBandCommute n t k) (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k)
    (hpre : pre ≠ 0) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : Round.Leaf H C)
    {β : Type*} (s : Finset β) {f : β → Replicas.Sphere (fun v => Fin (n v)) → ℝ}
    (hf : ∀ b, Continuous (f b)) :
    ∫ u, Transport.m (1 / 4) u * ∫ θ, (∑ b ∈ s, f b θ)
        ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) =
      ∑ b ∈ s, ∫ u, Transport.m (1 / 4) u *
        ∫ θ, f b θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) := by
  rw [← integral_finsetSum _ fun b _ =>
    integrable_m_mul_integral R hR ht hcomm hpreS hpre hp0 hp1 j (hf b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hσ := R.isSymDensity_state hR ht hcomm hpreS hpre hp0 hp1 j u
  simp only
  rw [integral_finsetSum _ fun b _ => integrable_of_isSymDensity hσ (hf b), Finset.mul_sum]

/-- `∫ m_s(u) ∫ c f dμ du = c ∫ m_s(u) ∫ f dμ du`. -/
theorem integral_m_mul_integral_const_mul (j : Round.Leaf H C) (c : ℝ)
    (f : Replicas.Sphere (fun v => Fin (n v)) → ℝ) :
    ∫ u, Transport.m (1 / 4) u * ∫ θ, c * f θ
        ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) =
      c * ∫ u, Transport.m (1 / 4) u *
        ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [integral_const_mul]
  ring

/-- `∫ m_s(u) ∫ f dμ du ≤ B/2` for `f ≤ B` (`∫ m_s = 1/2`, `μ` a probability). -/
theorem integral_m_mul_integral_le (hR : R.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : R.CrossBandCommute n t k) (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k)
    (hpre : pre ≠ 0) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : Round.Leaf H C)
    {f : Replicas.Sphere (fun v => Fin (n v)) → ℝ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ θ, f θ ≤ B) :
    ∫ u, Transport.m (1 / 4) u *
      ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) ≤ B / 2 := by
  have h := integral_m_mul_integral_mono R hR ht hcomm hpreS hpre hp0 hp1 j hf
    continuous_const hB
  refine h.trans (le_of_eq ?_)
  have e : ∀ u, Transport.m (1 / 4) u * ∫ θ, B ∂(Replicas.μ (fun v => Fin (n v)) k
      (R.state n t k pre p j u)) = B * Transport.m (1 / 4) u := fun u => by
    have hσ := R.isSymDensity_state hR ht hcomm hpreS hpre hp0 hp1 j u
    have := Replicas.eq_replicas_husimi (fun v => Fin (n v)) k hσ.1 hσ.2.1 hσ.2.2
    rw [integral_const, probReal_univ, one_smul]; ring
  simp only [e]
  rw [integral_const_mul, Transport.integral_m_quarter]; ring

variable {ι : Type*} (E : EnergyTerms V n ι)

omit [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)] in
theorem continuous_splitEta (i : ι) (j : Round.Leaf H C) :
    Continuous fun θ : Replicas.Sphere (fun v => Fin (n v)) => R.splitEta E i j θ.1 :=
  continuous_finsetSum _ fun _ _ => continuous_splitBandEta _

omit [∀ v, NeZero (n v)] in
theorem splitEta_nonneg (hR : R.IsAdmissible) (i : ι) (j : Round.Leaf H C)
    (θ : SiteConfig n → ℂ) : 0 ≤ R.splitEta E i j θ :=
  sum_nonneg fun g _ => splitBandEta_nonneg (R.isPartition_leafPart hR j g) _ θ

open Classical in
/-- The labelled terms split at the old leaf `(h, old)`. -/
noncomputable def splitAt [Fintype ι] (h : H) : Finset ι :=
  univ.filter fun i => ∃ g, ¬ (R.old h g).Contains (E.support i)

open Classical in
/-- D9.10 (`scanner:Q-definition`). The entropy cost of the old splits on good histories: for a
round, `h` an old history of weight `w_h`, `σ_{h,u}` its transported state (Prop 7.4) and `μ_σ`
the coherent probability measure (Lemma 6.4),
`𝒬(p) = ∑_{h good} w_h ∫ m_s(u) ∫ ∑_{i split in h} η_{i,h}(θ) dμ_{σ_{h,u}}(θ) du`, where
`η_{i,h} = S_θ(x|P) + S_θ(x|Y \ x)` with `x = Y ∩ X̃_i` for the near side (exchange `P, F` for
the far side) in the unique splitting band; `0 ≤ η ≤ C (log n)^C`, `m_s(u) du` has mass `2s`. -/
@[nolint defsWithUnderscore]
noncomputable def step_9_10 [Fintype H] [Fintype ι] (good : H → Prop) (t : ℝ) (k : ℕ)
    (pre : Transport.Config n k → ℂ) (p : unitInterval) : ℝ :=
  ∑ h ∈ univ.filter good, R.histTree.weight h * ∫ u, Transport.m (1 / 4) u *
    ∫ θ, (∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ.1)
      ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p ⟨h, none⟩ u))

theorem step_9_10_nonneg [Fintype H] [Fintype ι] (hR : R.IsAdmissible) (good : H → Prop)
    (t : ℝ) (k : ℕ)
    (pre : Transport.Config n k → ℂ) (p : unitInterval) : 0 ≤ step_9_10 R E good t k pre p := by
  classical
  unfold step_9_10
  exact sum_nonneg fun h _ => mul_nonneg (R.histTree.weight_nonneg h)
    (integral_m_mul_integral_nonneg R _ fun θ =>
      sum_nonneg fun i _ => splitEta_nonneg R E hR i _ θ.1)

/-- D9.11.1. The gain of every round is nonnegative. -/
theorem entropyGain_nonneg [Fintype H] [∀ h, Fintype (C h)] (hR : R.IsAdmissible) (t : ℝ) (k : ℕ)
    (pre : Transport.Config n k → ℂ) (p : unitInterval) : 0 ≤ R.entropyGain n t k pre p := by
  unfold Round.entropyGain
  exact sum_nonneg fun h _ => sum_nonneg fun g _ => mul_nonneg (R.histTree.weight_nonneg h)
    (integral_m_mul_integral_nonneg R _ fun θ => sum_nonneg fun c _ =>
      mul_nonneg ((R.choiceTree h).weight_nonneg c) (eta_nonneg R hR h c g θ.1))

end Round

/-! ## D9.11 Entropy production per round -/

section Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ) {nl : Comparators.Site S.Λ → ℕ}
  [∀ v, NeZero (nl v)] (E : EnergyTerms (Comparators.Site S.Λ) nl S.Term)

omit [∀ v, NeZero (nl v)] in
open Classical in
/-- D9.11.2–D9.11.3, pointwise in `θ`: on a good old history at a charge round,
`∑_g ∑_c q_{c|h} η_{h,c,g} ≥ (c/(nD)) ∑_{i split in h} η_{i,h}`. -/
theorem step_9_11_pointwise (hE : S.HasSupports E) {c₁ : ℝ} (h4 : S.Item4 c₁) (t : Fin S.T)
    (ht : t.1 % 2 = 1) (h : S.Hist t) (hgood : S.Good t h) (θ : SiteConfig nl → ℂ) :
    c₁ / (S.n * S.D) * ∑ i ∈ splitAt (S.round t) E h, (S.round t).splitEta E i ⟨h, none⟩ θ ≤
      ∑ g, ∑ c, ((S.round t).choiceTree h).weight c * (S.round t).eta h c g θ := by
  set R := S.round t
  have hR := S.round_isAdmissible t
  -- D9.11.3: a split term belongs to one band, so the sum over split terms is the sum over the
  -- bands of the terms split there
  have e1 : ∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ =
      ∑ g, ∑ i ∈ univ.filter (fun i => ¬ (R.old h g).Contains (physReg (S.Xt i))),
        Round.splitBandEta (R.old h g) (physReg (S.Xt i)) θ := by
    have hl : ∀ g, R.leafPart ⟨h, none⟩ g = R.old h g := fun g => rfl
    have hE' : ∀ i, E.support i = physReg (S.Xt i) := hE
    simp only [Round.splitEta, splitAt, hl, hE', Finset.sum_filter]
    conv_rhs => rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : ∃ g, ¬ (R.old h g).Contains (physReg (S.Xt i))
    · rw [if_pos hi]
    · rw [if_neg hi]
      push Not at hi
      exact (sum_eq_zero fun g _ => if_neg (not_not.2 (hi g))).symm
  rw [e1, mul_sum]
  refine sum_le_sum fun g _ => ?_
  obtain ⟨v, hinj, hv⟩ := h4 t ht h hgood g
  set sb := univ.filter (fun i => ¬ (R.old h g).Contains (physReg (S.Xt i)))
  set fil : S.Term → Finset (S.Ch t) := fun i => univ.filter fun c : S.Ch t => c g = v i
  have hπ := hR.old_isPartition h g
  -- D9.11.2: each split term is chosen with weight `≥ c/(nD)` and its move has exactly `η_{i,h}`;
  -- distinct terms occupy distinct slots
  calc c₁ / (S.n * S.D) * ∑ i ∈ sb, Round.splitBandEta (R.old h g) (physReg (S.Xt i)) θ
      ≤ ∑ i ∈ sb, (∑ c ∈ fil i, (R.choiceTree h).weight c) *
          Round.splitBandEta (R.old h g) (physReg (S.Xt i)) θ := by
        rw [mul_sum]
        refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hv i (mem_filter.1 hi).2).1 (splitBandEta_nonneg hπ _ θ)
    _ = ∑ i ∈ sb, ∑ c ∈ fil i, (R.choiceTree h).weight c * R.eta h c g θ := by
        refine sum_congr rfl fun i hi => ?_
        rw [sum_mul]
        refine sum_congr rfl fun c hc => ?_
        rw [((hv i (mem_filter.1 hi).2).2 c (mem_filter.1 hc).2).2 nl θ]
    _ = ∑ c ∈ sb.biUnion fil, (R.choiceTree h).weight c * R.eta h c g θ := by
        refine (sum_biUnion fun i hi i' hi' hii' => ?_).symm
        refine Finset.disjoint_left.2 fun c hc hc' => hii' (hinj i i' (mem_filter.1 hi).2
          (mem_filter.1 hi').2 ?_)
        exact (mem_filter.1 hc).2.symm.trans (mem_filter.1 hc').2
    _ ≤ ∑ c, (R.choiceTree h).weight c * R.eta h c g θ :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ =>
          mul_nonneg ((R.choiceTree h).weight_nonneg c) (eta_nonneg R hR h c g θ)

/-- D9.11.1–D9.11.3. At a charge round the gain of Proposition 7.4 (b) dominates the entropy cost
of the old splits: `∑_{h,g} w_h ∫ m_s ∫ ∑_c q_{c|h} η_{h,c,g} dμ du ≥ (c/(nD)) 𝒬(p)`. -/
theorem gain_ge_step_9_10 (hE : S.HasSupports E) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (h4 : S.Item4 c₁)
    (t : Fin S.T) (ht : t.1 % 2 = 1) {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ}
    (hcomm : (S.round t).CrossBandCommute nl τ k) {pre : Transport.Config nl k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (nl v)) k) (hpre : pre ≠ 0) {p : unitInterval}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    c₁ / (S.n * S.D) * step_9_10 (S.round t) E (S.Good t) τ k pre p ≤
      (S.round t).entropyGain nl τ k pre p := by
  classical
  set R := S.round t
  have hR := S.round_isAdmissible t
  have hc : 0 ≤ c₁ / (S.n * S.D) := by positivity
  unfold step_9_10 Round.entropyGain
  rw [mul_sum]
  refine le_trans (sum_le_sum fun h hh => ?_) (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun h _ _ => sum_nonneg fun g _ => mul_nonneg (R.histTree.weight_nonneg h)
      (integral_m_mul_integral_nonneg R _ fun θ => sum_nonneg fun c _ =>
        mul_nonneg ((R.choiceTree h).weight_nonneg c) (eta_nonneg R hR h c g θ.1)))
  rw [← mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (R.histTree.weight_nonneg h)
  rw [← integral_m_mul_integral_const_mul R, ← integral_m_mul_integral_sum R hR hτ hcomm hpreS hpre
    hp0 hp1 _ univ (f := fun g θ => ∑ c, (R.choiceTree h).weight c * R.eta h c g θ.1)
    fun g => continuous_finsetSum _ fun c _ =>
      continuous_const.mul (R.continuous_eta h c g)]
  exact integral_m_mul_integral_mono R hR hτ hcomm hpreS hpre hp0 hp1 _
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_splitEta R E i _))
    (continuous_finsetSum _ fun g _ => continuous_finsetSum _ fun c _ =>
      continuous_const.mul (R.continuous_eta h c g))
    fun θ => step_9_11_pointwise S E hE h4 t ht h (mem_filter.1 hh).2 θ.1

/-- D9.11 (`scanner:charge-gain`). At a charge round
`-∂_p log N² ≥ (c k a/(nD)) 𝒬(p) - C k a K a^{1/4} (log n)^C - O_fixed(log(k+2))`; at a fill
round the same without the gain. Here Proposition 7.4 (b) is the hypothesis `hb` (its error
`C k a K a^{1/4} ℓ^C + β_k` is `Err`, with `ℓ ≤ C (1 + r₀)^{m₀}` the support bound of D9.11.4),
and the gain is bounded below by D9.11.1–D9.11.3. -/
theorem step_9_11 (hE : S.HasSupports E) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (h4 : S.Item4 c₁)
    (t : Fin S.T) {a : ℝ} (ha : 0 ≤ a) {k : ℕ}
    (hcomm : (S.round t).CrossBandCommute nl (a / 2) k) {pre : Transport.Config nl k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (nl v)) k) (hpre : pre ≠ 0) {p : unitInterval}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {Err : ℝ}
    (hb : (k : ℝ) * a * (S.round t).entropyGain nl (a / 2) k pre p - Err ≤
      (S.round t).exactDerivative nl (a / 2) k pre p) :
    (t.1 % 2 = 1 → (k : ℝ) * a * (c₁ / (S.n * S.D)) *
        step_9_10 (S.round t) E (S.Good t) (a / 2) k pre p - Err ≤
      (S.round t).exactDerivative nl (a / 2) k pre p) ∧
    -Err ≤ (S.round t).exactDerivative nl (a / 2) k pre p := by
  have hka : 0 ≤ (k : ℝ) * a := by positivity
  -- D9.11.5: at a fill round the gains are `≥ 0`
  have h0 := entropyGain_nonneg (S.round t) (S.round_isAdmissible t) (a / 2) k pre p
  refine ⟨fun ht => le_trans ?_ hb, by nlinarith⟩
  -- D9.11.1–D9.11.3 at a charge round
  have := gain_ge_step_9_10 S E hE hc₁ h4 t ht (by positivity) hcomm hpreS hpre hp0 hp1
  rw [mul_assoc]
  linarith [mul_le_mul_of_nonneg_left this hka]

end Scan

end AreaLaw.Scanner
