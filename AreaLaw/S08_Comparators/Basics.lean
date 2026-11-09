import AreaLaw.S08_Comparators.Interfaces

/-!
# §8.0 Statuses commute across bands (D8.1) and the Schmidt decomposition (D8.11)

Digest `digest/08-comparators.md` D8.1 (Output (ii), (iii)) and D8.11.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

/-! ## Label observables on the symmetric subspace -/

section LabelObservable

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {k : ℕ}

/-- A label observable of a subsystem preserves `𝒮_k`. -/
private theorem labelObservable_mulVec_mem_S (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {z : Replicas.Config (fun v => Fin (n v)) k → ℂ}
    (hz : z ∈ Replicas.S (fun v => Fin (n v)) k) :
    labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q) f *ᵥ z ∈
      Replicas.S (fun v => Fin (n v)) k := by
  rw [Replicas.S_eq, mem_invariantSubspace] at hz ⊢
  intro τ
  have hc := TensorPower.commute_copyPerm_labelObservable (n := n) k Q f τ
  calc _ = (permOp (TensorPower.copyPerm (SiteConfig n) k) τ *
        labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q) f) *ᵥ z := mulVec_mulVec _ _ _
    _ = (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q) f *
        permOp (TensorPower.copyPerm (SiteConfig n) k) τ) *ᵥ z := congrArg (· *ᵥ z) hc.eq
    _ = _ := by rw [← mulVec_mulVec, hz τ]

/-- On `𝒮_k` a label observable of `Q` equals that of `Q^c` (Lemma 6.1 (2)). -/
private theorem labelObservable_mulVec_compl (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {z : Replicas.Config (fun v => Fin (n v)) k → ℂ}
    (hz : z ∈ Replicas.S (fun v => Fin (n v)) k) :
    labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q) f *ᵥ z =
      labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Qᶜ) f *ᵥ z := by
  simp only [labelObservable, sum_mulVec, smul_mulVec]
  exact Finset.sum_congr rfl fun l _ =>
    congrArg _ (Replicas.step_6_4_9 (fun v => Fin (n v)) k Q l hz)

variable (n) in
/-- `(W_{Q₁}^{-1} W_{Q₂}^{-1} W_{Q₃})²`, the factors written as label observables. -/
private noncomputable def Bm (t : ℝ) (k : ℕ) (Q₁ Q₂ Q₃ : Finset V) :
    Matrix (Replicas.Config (fun v => Fin (n v)) k) (Replicas.Config (fun v => Fin (n v)) k) ℂ :=
  (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₁)
      (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
    labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₂)
      (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
    labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₃)
      (fun l => Replicas.w (fun v => Fin (n v)) t l)) ^ 2

private theorem Bm_mulVec_mem_S (t : ℝ) (Q₁ Q₂ Q₃ : Finset V)
    {z : Replicas.Config (fun v => Fin (n v)) k → ℂ} (hz : z ∈ Replicas.S (fun v => Fin (n v)) k) :
    Bm n t k Q₁ Q₂ Q₃ *ᵥ z ∈ Replicas.S (fun v => Fin (n v)) k := by
  have hM : ∀ z ∈ Replicas.S (fun v => Fin (n v)) k,
      (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₁)
          (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
        labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₂)
          (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
        labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₃)
          (fun l => Replicas.w (fun v => Fin (n v)) t l)) *ᵥ z ∈
        Replicas.S (fun v => Fin (n v)) k := fun z hz => by
    simp only [← mulVec_mulVec]
    exact labelObservable_mulVec_mem_S _ _ (labelObservable_mulVec_mem_S _ _
      (labelObservable_mulVec_mem_S _ _ hz))
  rw [Bm, pow_two, ← mulVec_mulVec]
  exact hM _ (hM _ hz)

/-- On `𝒮_k`, for `F^c = P ∪ Y`: `A_k(P, Y, F) = (W_P^{-1} W_{PY}^{-1} W_Y)²` (Lemma 6.2,
`W_F = W_{F^c}`). -/
private theorem A_mulVec_eq [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) {P Y F : Finset V}
    (hF : Fᶜ = P ∪ Y) {z : Replicas.Config (fun v => Fin (n v)) k → ℂ}
    (hz : z ∈ Replicas.S (fun v => Fin (n v)) k) :
    Replicas.A (fun v => Fin (n v)) t k P Y F *ᵥ z = Bm n t k P (P ∪ Y) Y *ᵥ z := by
  have hW : ∀ Q, Replicas.W (fun v => Fin (n v)) t k Q =
      labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q)
        (fun l => Replicas.w (fun v => Fin (n v)) t l) := fun _ => rfl
  have hM : ∀ z ∈ Replicas.S (fun v => Fin (n v)) k,
      ((Replicas.W (fun v => Fin (n v)) t k P)⁻¹ * (Replicas.W (fun v => Fin (n v)) t k F)⁻¹ *
          Replicas.W (fun v => Fin (n v)) t k Y) *ᵥ z =
        (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k P)
            (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
          labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k (P ∪ Y))
            (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
          labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Y)
            (fun l => Replicas.w (fun v => Fin (n v)) t l)) *ᵥ z := fun z hz => by
    rw [Replicas.W_inv _ ht, Replicas.W_inv _ ht, hW]
    simp only [← mulVec_mulVec]
    rw [labelObservable_mulVec_compl F _ (labelObservable_mulVec_mem_S _ _ hz), hF]
  have hM' : ∀ z ∈ Replicas.S (fun v => Fin (n v)) k,
      (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k P)
            (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
          labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k (P ∪ Y))
            (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
          labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Y)
            (fun l => Replicas.w (fun v => Fin (n v)) t l)) *ᵥ z ∈
        Replicas.S (fun v => Fin (n v)) k := fun z hz => by
    simp only [← mulVec_mulVec]
    exact labelObservable_mulVec_mem_S _ _ (labelObservable_mulVec_mem_S _ _
      (labelObservable_mulVec_mem_S _ _ hz))
  have key : ∀ M M' : Matrix (Replicas.Config (fun v => Fin (n v)) k)
      (Replicas.Config (fun v => Fin (n v)) k) ℂ,
      (∀ z ∈ Replicas.S (fun v => Fin (n v)) k, M *ᵥ z = M' *ᵥ z) →
      (∀ z ∈ Replicas.S (fun v => Fin (n v)) k, M' *ᵥ z ∈ Replicas.S (fun v => Fin (n v)) k) →
      (M ^ 2) *ᵥ z = (M' ^ 2) *ᵥ z := fun M M' h1 h2 => by
    rw [pow_two, pow_two, ← mulVec_mulVec, ← mulVec_mulVec, h1 z hz, h1 _ (h2 z hz)]
  exact key _ _ hM hM'

/-- Products `(W_{Q₁}^{-1} W_{Q₂}^{-1} W_{Q₃})²` commute when every `Q_i` is nested in or
disjoint from every `Q'_j` (Lemma 6.1 (2)). -/
private theorem commute_Bm (t : ℝ) {Q₁ Q₂ Q₃ Q₁' Q₂' Q₃' : Finset V}
    (h : ∀ Q ∈ [Q₁, Q₂, Q₃], ∀ Q' ∈ [Q₁', Q₂', Q₃'], Q ⊆ Q' ∨ Disjoint Q Q') :
    Commute (Bm n t k Q₁ Q₂ Q₃) (Bm n t k Q₁' Q₂' Q₃') := by
  have c : ∀ Q ∈ [Q₁, Q₂, Q₃], ∀ Q' ∈ [Q₁', Q₂', Q₃'], ∀ f f',
      Commute (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q) f)
        (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q') f') :=
    fun Q hQ Q' hQ' f f' => Replicas.commute_labelObservable _ k (h Q hQ Q' hQ') f f'
  have c' : ∀ Q ∈ [Q₁, Q₂, Q₃], ∀ f, Commute
      (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q) f)
      (labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₁')
          (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
        labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₂')
          (fun l => (Replicas.w (fun v => Fin (n v)) t l)⁻¹) *
        labelObservable (Replicas.copyPerm (fun v => Fin (n v)) k Q₃')
          (fun l => Replicas.w (fun v => Fin (n v)) t l)) := fun Q hQ f =>
    ((c Q hQ _ (by simp) _ _).mul_right (c Q hQ _ (by simp) _ _)).mul_right
      (c Q hQ _ (by simp) _ _)
  exact Commute.pow_pow (((c' _ (by simp) _).mul_left (c' _ (by simp) _)).mul_left
    (c' _ (by simp) _)) 2 2

end LabelObservable

/-! ## D8.1 The regions of a status -/

section Regions

variable {σ : Type u}

private theorem phys_mem_physReg {Q : Finset σ} {v : σ} : Site.phys v ∈ physReg Q ↔ v ∈ Q := by
  rw [physReg, Finset.mem_map]
  exact ⟨fun ⟨_, ha, h⟩ => Site.phys.inj h ▸ ha, fun h => ⟨v, h, rfl⟩⟩

private theorem C_not_mem_physReg {Q : Finset σ} : Site.C ∉ physReg Q := by
  simp [physReg, Finset.mem_map]

private theorem R_not_mem_physReg {Q : Finset σ} : Site.R ∉ physReg Q := by
  simp [physReg, Finset.mem_map]

variable [Fintype σ] [DecidableEq σ]

variable {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

/-- `X U_g Y_g ⊆ X U_{g'}` (nesting) with `U_g, Y_g` disjoint from `X`: `U_g Y_g ⊆ U_{g'}`. -/
private theorem union_subset_U {s s' : St} {g g' : Fin K} (h : g < g') :
    Γ.U s g ∪ Γ.Y s g ⊆ Γ.U s' g' := by
  intro v hv
  have hX : v ∉ X := by
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.disjoint_right.mp (Γ.disjoint_XU s g) hv
    · exact Finset.disjoint_right.mp (Γ.disjoint_XY s g) hv
  have := Γ.nesting s s' g g' h (by
    rw [Finset.union_assoc]; exact Finset.mem_union_right _ hv)
  rcases Finset.mem_union.mp this with h' | h'
  · exact absurd h' hX
  · exact h'

/-- `F_{j,g}^c = P_{j,g} ∪ Y_{j,g}`. -/
private theorem compl_F (s : St) (g : Fin K) : (Γ.F s g)ᶜ = Γ.P s g ∪ Γ.Yr s g := by
  ext x
  have hcov := fun v => Finset.ext_iff.mp (Γ.cover s g) v
  cases x with
  | phys v =>
    simp only [Statuses.F, Statuses.P, Statuses.Yr, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_union, phys_mem_physReg, reduceCtorEq, false_or]
    have := hcov v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true] at this
    have h1 : v ∈ X → v ∉ Γ.V s g := fun h => Finset.disjoint_left.mp (Γ.disjoint_XV s g) h
    have h2 : v ∈ Γ.U s g → v ∉ Γ.V s g := fun h =>
      Finset.disjoint_left.mp (Γ.disjoint_UV s g) h
    have h3 : v ∈ Γ.Y s g → v ∉ Γ.V s g := fun h =>
      Finset.disjoint_left.mp (Γ.disjoint_YV s g) h
    tauto
  | C => simp [Statuses.F, Statuses.P, C_not_mem_physReg]
  | R => simp [Statuses.F, Statuses.P, Statuses.Yr, R_not_mem_physReg]

/-- `P_{j,g}` and `Y_{j,g}` are disjoint. -/
private theorem disjoint_P_Yr (s : St) (g : Fin K) : Disjoint (Γ.P s g) (Γ.Yr s g) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  cases x with
  | phys v =>
    simp only [Statuses.P, Statuses.Yr, Finset.mem_insert, Finset.mem_union, phys_mem_physReg,
      reduceCtorEq, false_or] at hx hy
    rcases hx with hx | hx
    · exact Finset.disjoint_left.mp (Γ.disjoint_XY s g) hx hy
    · exact Finset.disjoint_left.mp (Γ.disjoint_UY s g) hx hy
  | C => exact C_not_mem_physReg hy
  | R => exact R_not_mem_physReg hy

/-- For `g < g'`: `C X U_g Y_g ⊆ C X U_{g'}` (nesting). -/
private theorem P_union_Yr_subset {s s' : St} {g g' : Fin K} (h : g < g') :
    Γ.P s g ∪ Γ.Yr s g ⊆ Γ.P s' g' := by
  intro x hx
  cases x with
  | phys v =>
    simp only [Statuses.P, Statuses.Yr, Finset.mem_insert, Finset.mem_union, phys_mem_physReg,
      reduceCtorEq, false_or] at hx ⊢
    have := Γ.nesting s s' g g' h
    have h' : v ∈ X ∪ Γ.U s g ∪ Γ.Y s g := by
      simp only [Finset.mem_union]; tauto
    simpa only [Finset.mem_union] using this h'
  | C => simp [Statuses.P]
  | R => simp [Statuses.P, Statuses.Yr, R_not_mem_physReg] at hx

/-- For `g < g'`: every band-`g` region (`C X U_g`, `C X U_g Y_g`, `Y_g`) is nested in or
disjoint from every band-`g'` region (`C X U_{g'}`, `C X U_{g'} Y_{g'}`, `Y_{g'}`). -/
private theorem band_regions {s s' : St} {g g' : Fin K} (h : g < g') :
    ∀ Q ∈ [Γ.P s g, Γ.P s g ∪ Γ.Yr s g, Γ.Yr s g],
      ∀ Q' ∈ [Γ.P s' g', Γ.P s' g' ∪ Γ.Yr s' g', Γ.Yr s' g'], Q ⊆ Q' ∨ Disjoint Q Q' := by
  have hsub := P_union_Yr_subset Γ (s := s) (s' := s') h
  have hR : ∀ Q ∈ [Γ.P s g, Γ.P s g ∪ Γ.Yr s g, Γ.Yr s g], Q ⊆ Γ.P s' g' := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨Finset.subset_union_left.trans hsub, hsub, Finset.subset_union_right.trans hsub⟩
  intro Q hQ Q' hQ'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ'
  rcases hQ' with rfl | rfl | rfl
  · exact Or.inl (hR Q hQ)
  · exact Or.inl ((hR Q hQ).trans Finset.subset_union_left)
  · exact Or.inr ((disjoint_P_Yr Γ s' g').mono_left (hR Q hQ))

end Regions

/-- D8.1, Output (ii), (iii). (iii) Within one leaf, the regions `U_{j,g}, U_{j,g}Y_{j,g}, Y_{j,g}`
of any two bands are nested or disjoint (so all their labels commute, Lemma 6.1 (2)). (ii) Band
factors of different bands commute, at any two leaves: `[A_{j,g}, A_{j',g'}] = 0` for `g ≠ g'`
(the hypothesis of Lemma 7.1 (6)). -/
theorem step_8_1 : Step_8_1.{u, v} := by
  intro σ _ _ K St X Γ
  refine ⟨?_, ?_⟩
  · -- Output (iii)
    have key : ∀ (s : St) (g g' : Fin K), g < g' →
        ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g, Γ.Y s g} : Finset (Finset σ)),
        ∀ Q' ∈ ({Γ.U s g', Γ.U s g' ∪ Γ.Y s g', Γ.Y s g'} : Finset (Finset σ)),
          Q ⊆ Γ.U s g' ∧ Disjoint Q (Γ.Y s g') ∧ (Q' = Γ.Y s g' ∨ Γ.U s g' ⊆ Q') := by
      intro s g g' h Q hQ Q' hQ'
      have hsub := union_subset_U Γ (s := s) (s' := s) h
      have hQs : Q ⊆ Γ.U s g' := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with rfl | rfl | rfl
        · exact Finset.subset_union_left.trans hsub
        · exact hsub
        · exact Finset.subset_union_right.trans hsub
      refine ⟨hQs, (Γ.disjoint_UY s g').mono_left hQs, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
      rcases hQ' with rfl | rfl | rfl
      · exact Or.inr subset_rfl
      · exact Or.inr Finset.subset_union_left
      · exact Or.inl rfl
    intro s g g' Q hQ Q' hQ'
    rcases lt_trichotomy g g' with h | rfl | h
    · obtain ⟨hQs, hQd, hQ'⟩ := key s g g' h Q hQ Q' hQ'
      rcases hQ' with rfl | hQ'
      · exact Or.inr (Or.inr hQd)
      · exact Or.inl (hQs.trans hQ')
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ hQ'
      have hUY := Γ.disjoint_UY s g
      rcases hQ with rfl | rfl | rfl <;> rcases hQ' with rfl | rfl | rfl <;>
        first
        | exact Or.inl subset_rfl
        | exact Or.inl Finset.subset_union_left
        | exact Or.inl Finset.subset_union_right
        | exact Or.inr (Or.inl Finset.subset_union_left)
        | exact Or.inr (Or.inl Finset.subset_union_right)
        | exact Or.inr (Or.inr hUY)
        | exact Or.inr (Or.inr hUY.symm)
    · obtain ⟨hQs, hQd, hQ⟩ := key s g' g h Q' hQ' Q hQ
      rcases hQ with rfl | hQ
      · exact Or.inr (Or.inr hQd.symm)
      · exact Or.inr (Or.inl (hQs.trans hQ))
  · -- Output (ii)
    intro n _ d _ t ht k s s' g g' hgg'
    have key : ∀ (s s' : St) (g g' : Fin K), g < g' →
        Commute (Γ.bandA n d t k s g) (Γ.bandA n d t k s' g') := by
      intro s s' g g' h
      rw [Statuses.bandA, Statuses.bandA, Transport.commute_bandMetric_iff]
      intro w hw
      have hF : ∀ s g, ((Γ.part s g).F)ᶜ = (Γ.part s g).P ∪ (Γ.part s g).Y := compl_F Γ
      rw [A_mulVec_eq ht (hF s' g') hw, A_mulVec_eq ht (hF s g) hw,
        A_mulVec_eq ht (hF s g) (Bm_mulVec_mem_S _ _ _ _ hw),
        A_mulVec_eq ht (hF s' g') (Bm_mulVec_mem_S _ _ _ _ hw), mulVec_mulVec, mulVec_mulVec]
      exact congrArg (· *ᵥ w) (commute_Bm t (band_regions Γ (s := s) (s' := s') h)).eq
    rcases lt_or_gt_of_ne hgg' with h | h
    · exact key s s' g g' h
    · exact (key s' s g' g h).symm

/-! ## D8.11 The Schmidt decomposition -/

section Schmidt

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} (D : PhysData n) (X : Finset σ)

/-- `Ω̃` as a matrix `X × X^c`: `Θ(a, z) = Ω̃(a z)`. -/
private noncomputable def Θ :
    Matrix (Reg (fun v => Fin (n v)) X) (Reg (fun v => Fin (n v)) (Finset.univ \ X)) ℂ :=
  Matrix.of fun a z => D.Ω (univEquiv (glue a z))

/-- `ρ_X = Θ Θ^*`. -/
private theorem ρ_eq_Θ : D.ρ X = Θ D X * (Θ D X)ᴴ := by
  ext a b
  simp [PhysData.ρ, marg, ptrace, Θ, mul_apply, vecMulVec_apply, conjTranspose_apply]

variable {X}

private theorem replaceX_univEquiv_glue (a : Reg (fun v => Fin (n v)) X)
    (z : Reg (fun v => Fin (n v)) (Finset.univ \ X)) (y : Reg (fun v => Fin (n v)) X) :
    replaceX (univEquiv (glue a z)) y = univEquiv (glue y z) := by
  funext v
  by_cases hv : v ∈ X <;> simp [replaceX, univEquiv, glue, hv]

private theorem restrictX_univEquiv_glue (a : Reg (fun v => Fin (n v)) X)
    (z : Reg (fun v => Fin (n v)) (Finset.univ \ X)) :
    restrictX (X := X) (univEquiv (glue a z)) = a := by
  funext ⟨v, hv⟩
  simp [restrictX, univEquiv, glue, hv]

variable (X) in
/-- `𝓗_X ⊗ 𝓗_{X^c} = 𝓗_phys` on configurations. -/
private def splitX :
    Reg (fun v => Fin (n v)) X × Reg (fun v => Fin (n v)) (Finset.univ \ X) ≃ SiteConfig n :=
  (glueEquiv (Finset.subset_univ X)).trans univEquiv

private theorem splitX_apply (a : Reg (fun v => Fin (n v)) X)
    (z : Reg (fun v => Fin (n v)) (Finset.univ \ X)) :
    splitX X (a, z) = univEquiv (glue a z) := rfl

/-- The unitary with columns `|i⟩_X`. -/
private theorem eigenvectorUnitary_apply_eq (a i : Reg (fun v => Fin (n v)) X) :
    ((D.isHermitian_ρ X).eigenvectorUnitary : Matrix _ _ ℂ) a i = schmidtX (D := D) i a := by
  rw [IsHermitian.eigenvectorUnitary_apply]; rfl

/-- `⟨i|_X Ω̃ = u_i` on `X^c`, so `w_i = p_i^{-1/2} u_i`. -/
private theorem schmidtW_glue (i a : Reg (fun v => Fin (n v)) X)
    (z : Reg (fun v => Fin (n v)) (Finset.univ \ X)) :
    schmidtW (D := D) i (univEquiv (glue a z)) =
      ((Real.sqrt (D.p X i))⁻¹ : ℝ) * (star (schmidtX (D := D) i) ᵥ* Θ D X) z := by
  simp only [schmidtW, replaceX_univEquiv_glue, vecMul, dotProduct, Θ, of_apply, Pi.star_apply]

/-- `⟨i|j⟩ = δ_ij`. -/
private theorem star_schmidtX_dotProduct (i j : Reg (fun v => Fin (n v)) X) :
    star (schmidtX (D := D) j) ⬝ᵥ schmidtX (D := D) i = if j = i then 1 else 0 := by
  have hU := congrFun (congrFun (mem_unitaryGroup_iff'.mp
    (D.isHermitian_ρ X).eigenvectorUnitary.2) j) i
  rw [one_apply] at hU
  rw [← hU]
  simp only [mul_apply, star_apply, eigenvectorUnitary_apply_eq, dotProduct, Pi.star_apply]

/-- Completeness: `∑_i |i⟩⟨i| = 1`. -/
private theorem sum_schmidtX (φ : Reg (fun v => Fin (n v)) X → ℂ) (a : Reg (fun v => Fin (n v)) X) :
    ∑ i, schmidtX (D := D) i a * (star (schmidtX (D := D) i) ⬝ᵥ φ) = φ a := by
  have hU := congrFun (congrArg (· *ᵥ φ) (mem_unitaryGroup_iff.mp
    (D.isHermitian_ρ X).eigenvectorUnitary.2)) a
  simp only [one_mulVec, ← mulVec_mulVec] at hU
  rw [← hU]
  simp only [mulVec, dotProduct, star_apply, eigenvectorUnitary_apply_eq, Pi.star_apply]

/-- `⟨u_i, u_j⟩ = ⟨j|ρ_X|i⟩ = p_i δ_ij`. -/
private theorem star_u_dotProduct (i j : Reg (fun v => Fin (n v)) X) :
    star (star (schmidtX (D := D) i) ᵥ* Θ D X) ⬝ᵥ (star (schmidtX (D := D) j) ᵥ* Θ D X) =
      (D.p X i : ℂ) * if j = i then 1 else 0 := by
  have hρ : D.ρ X *ᵥ schmidtX (D := D) i = D.p X i • schmidtX (D := D) i :=
    (D.isHermitian_ρ X).mulVec_eigenvectorBasis i
  rw [star_vecMul, star_star, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec,
    ← ρ_eq_Θ, hρ, dotProduct_smul, star_schmidtX_dotProduct, Complex.real_smul]

/-- `p_i = 0 ⇒ ⟨i|_X Ω̃ = 0`. -/
private theorem u_eq_zero {i : Reg (fun v => Fin (n v)) X} (hi : D.p X i = 0) :
    star (schmidtX (D := D) i) ᵥ* Θ D X = 0 := by
  have h := star_u_dotProduct D i i
  rw [hi, Complex.ofReal_zero, zero_mul] at h
  exact dotProduct_star_self_eq_zero.mp h

/-- D8.11. The Schmidt decomposition `Ω̃ = ∑_i √p_i |i⟩_X |w_i⟩` across `X | X^c` (`|i⟩_X` the
eigenbasis of `ρ_X`, `p_i ≥ 0`, `∑ p_i = 1`); `w_i` ignores the `X`-part, and the `w_i` with
`p_i > 0` are orthonormal on `X^c` (sums over all physical configurations count each
`X^c`-configuration `dim 𝓗_X` times). -/
theorem step_8_11 : Step_8_11.{u} := by
  intro σ _ _ n D X
  have hp : ∀ i, 0 ≤ D.p X i := fun i =>
    (posSemidef_marg (D.Ω ∘ univEquiv) (Finset.subset_univ X)).eigenvalues_nonneg i
  refine ⟨?_, ?_, ?_, hp, ?_⟩
  · -- (a) `Ω̃ = ∑_i √p_i |i⟩_X |w_i⟩`, also through the `p_i = 0` terms
    intro x
    obtain ⟨⟨a, z⟩, rfl⟩ := (splitX X).surjective x
    simp only [splitX_apply, restrictX_univEquiv_glue, schmidtW_glue]
    have hterm : ∀ i, (Real.sqrt (D.p X i) : ℂ) * schmidtX (D := D) i a *
        (((Real.sqrt (D.p X i))⁻¹ : ℝ) * (star (schmidtX (D := D) i) ᵥ* Θ D X) z) =
        schmidtX (D := D) i a * (star (schmidtX (D := D) i) ⬝ᵥ fun y => Θ D X y z) := by
      intro i
      have hu : (star (schmidtX (D := D) i) ᵥ* Θ D X) z =
          star (schmidtX (D := D) i) ⬝ᵥ fun y => Θ D X y z := rfl
      by_cases h0 : D.p X i = 0
      · rw [← hu, u_eq_zero D h0, h0]; simp
      · have hs : (Real.sqrt (D.p X i) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hp i) (Ne.symm h0)))
        rw [hu, Complex.ofReal_inv]
        field_simp
    rw [Finset.sum_congr rfl fun i _ => hterm i, sum_schmidtX D (fun y => Θ D X y z) a]
    rfl
  · -- (b) `w_i` ignores the `X`-part
    intro i x y
    simp only [schmidtW]
    congr 2
    funext y'
    congr 2
    funext v
    by_cases hv : v ∈ X <;> simp [replaceX, hv]
  · -- (c) the `w_i` with `p_i > 0` are orthonormal on `X^c`
    intro i j hi hj
    rw [← (splitX X).sum_comp, Fintype.sum_prod_type]
    simp only [splitX_apply, schmidtW_glue, star_mul', Complex.star_def, Complex.conj_ofReal]
    have hz :
        ∑ z, ((Real.sqrt (D.p X i))⁻¹ : ℝ) * (starRingEnd ℂ)
            ((star (schmidtX (D := D) i) ᵥ* Θ D X) z) *
          (((Real.sqrt (D.p X j))⁻¹ : ℝ) * (star (schmidtX (D := D) j) ᵥ* Θ D X) z) =
        (((Real.sqrt (D.p X i))⁻¹ * (Real.sqrt (D.p X j))⁻¹ : ℝ) : ℂ) *
          (star (star (schmidtX (D := D) i) ᵥ* Θ D X) ⬝ᵥ
            (star (schmidtX (D := D) j) ᵥ* Θ D X)) := by
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Pi.star_apply, Complex.star_def, Complex.ofReal_mul]
      ring
    have hcard : (Fintype.card (Reg (fun v => Fin (n v)) X) : ℂ) = dimReg n X := by
      simp only [dimReg, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
      exact Finset.prod_coe_sort X fun v => (n v : ℂ)
    rw [Finset.sum_congr rfl fun a _ => hz, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      star_u_dotProduct, hcard]
    by_cases hij : i = j
    · subst hij
      have h1 : (Real.sqrt (D.p X i))⁻¹ * (Real.sqrt (D.p X i))⁻¹ * D.p X i = 1 := by
        rw [← mul_inv, Real.mul_self_sqrt hi.le, inv_mul_cancel₀ hi.ne']
      have h2 : (((Real.sqrt (D.p X i))⁻¹ * (Real.sqrt (D.p X i))⁻¹ : ℝ) : ℂ) *
          (D.p X i : ℂ) = 1 := by
        exact_mod_cast h1
      rw [if_pos rfl, if_pos rfl, mul_one, h2, mul_one]
    · rw [if_neg (Ne.symm hij), if_neg hij]
      simp
  · -- (d) `∑ p_i = Tr ρ_X = ‖Ω̃‖² = 1`
    have h := (D.isHermitian_ρ X).trace_eq_sum_eigenvalues
    have h1 : (D.ρ X).trace = 1 := by
      rw [show D.ρ X = marg (D.Ω ∘ univEquiv) (Finset.subset_univ X) from rfl, trace_marg,
        D.norm_Ω_univEquiv]
    rw [h1] at h
    have h2 : ((∑ i, D.p X i : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]; exact h.symm
    exact_mod_cast h2

end Schmidt

end AreaLaw.Comparators
