import AreaLaw.S10_Amplification.Setup

/-!
# §10 Mutual information on the reference copy (D10.6.1–2, D10.15)

Digest `digest/10-amplification.md` (D10.6, D10.15), paper
`paper/sections/09-amplification.tex` lines 324–346 and 547–561. No geometry.

The global space is `Reg Λ × (Reg X × Reg X)`, the physical region with the copies `s'`
(first factor) and `e'` (second factor). `redEJ` is the `e'J`-marginal of a unit vector.
-/

namespace AreaLaw

open Arealaw Matrix Finset Amplification
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder Kronecker

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-! ## Trace distance under relabelling and partial trace -/

section TrDist

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem trDistance_eq_D₁ (ρ τ : _root_.MState α) : -- helper
    TrDistance ρ τ = (MState.physlibEquiv.symm ρ).toSubState.D₁
      (MState.physlibEquiv.symm τ).toSubState := by
  rw [← MState.trDistance_physlibEquiv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem trDistance_nonneg (ρ τ : _root_.MState α) : 0 ≤ TrDistance ρ τ := by -- helper
  rw [trDistance_eq_D₁]; exact SubState.D₁_nonneg _ _

theorem trDistance_le_one (ρ τ : _root_.MState α) : TrDistance ρ τ ≤ 1 := by -- helper
  rw [trDistance_eq_D₁]; exact SubState.D₁_le_one _ _

omit [DecidableEq α] in
theorem trace_mul_traceRight (M : Matrix α α ℂ) (D : Matrix (α × β) (α × β) ℂ) : -- helper
    (M * D.traceRight).trace = ((M ⊗ₖ (1 : Matrix β β ℂ)) * D).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.traceRight, of_apply,
    kroneckerMap_apply, Fintype.sum_prod_type, one_apply, mul_boole, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Trace distance contracts under the right partial trace. -/
theorem trDistance_traceRight_le (ρ τ : _root_.MState (α × β)) : -- helper
    TrDistance ρ.traceRight τ.traceRight ≤ TrDistance ρ τ := by
  rw [trDistance_eq_D₁, trDistance_eq_D₁]
  obtain ⟨M, hM, hM1, hval⟩ := (SubState.isGreatest_D₁
    (MState.physlibEquiv.symm ρ.traceRight).toSubState
    (MState.physlibEquiv.symm τ.traceRight).toSubState).1
  rw [hval]
  have htr : (M * ((MState.physlibEquiv.symm ρ.traceRight).toSubState.M -
      (MState.physlibEquiv.symm τ.traceRight).toSubState.M)).trace =
      ((M ⊗ₖ (1 : Matrix β β ℂ)) * ((MState.physlibEquiv.symm ρ).toSubState.M -
        (MState.physlibEquiv.symm τ).toSubState.M)).trace := by
    rw [← trace_mul_traceRight, Matrix.traceRight_sub]
    rfl
  rw [htr]
  refine SubState.abs_re_trace_mul_le_D₁ _ _ ?_ ?_
  · rw [Matrix.nonneg_iff_posSemidef] at hM ⊢
    exact hM.PosSemidef_kronecker Matrix.PosSemidef.one
  · rw [Matrix.le_iff] at hM1 ⊢
    have : (1 : Matrix (α × β) (α × β) ℂ) - M ⊗ₖ (1 : Matrix β β ℂ) =
        (1 - M) ⊗ₖ (1 : Matrix β β ℂ) := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp [kroneckerMap_apply, one_apply]
      split_ifs <;> simp_all
    rw [this]
    exact hM1.PosSemidef_kronecker Matrix.PosSemidef.one

end TrDist

/-! ## Marginals of pure states -/

section PureMarg

variable {G A B : Type*} [Fintype G] [DecidableEq G] [Fintype A] [DecidableEq A] [Fintype B]

omit [Fintype A] in
/-- A unitary acting on the traced factor only does not change the marginal: if
`U (e⁻¹(a, b)) (e⁻¹(a', b')) = δ_{a a'} F b b'`, then
`∑_b (Uψ)(a, b) conj (Uψ)(a', b) = ∑_b ψ(a, b) conj ψ(a', b)`. -/
theorem sum_mulVec_mul_star_mulVec [Finite A] (e : G ≃ A × B) {U : Matrix G G ℂ} -- helper
    (hU : Uᴴ * U = 1)
    (F : B → B → ℂ) (hF : ∀ a a' b b', U (e.symm (a, b)) (e.symm (a', b')) =
      if a = a' then F b b' else 0) (ψ : G → ℂ) (a a' : A) :
    ∑ b, (U *ᵥ ψ) (e.symm (a, b)) * star ((U *ᵥ ψ) (e.symm (a', b))) =
      ∑ b, ψ (e.symm (a, b)) * star (ψ (e.symm (a', b))) := by
  classical
  have := Fintype.ofFinite A
  have hv (a : A) (b : B) : (U *ᵥ ψ) (e.symm (a, b)) = ∑ b₁, F b b₁ * ψ (e.symm (a, b₁)) := by
    rw [mulVec, dotProduct, ← e.symm.sum_comp, Fintype.sum_prod_type]
    simp [hF]
  have hFu (b₁ b₂ : B) : ∑ b, star (F b b₂) * F b b₁ = if b₂ = b₁ then 1 else 0 := by
    have h := congrFun (congrFun hU (e.symm (a, b₂))) (e.symm (a, b₁))
    rw [Matrix.mul_apply, ← e.symm.sum_comp, Fintype.sum_prod_type, one_apply] at h
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, true_and] at h
    rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun y _ => by
      rw [hF, if_neg hx, mul_zero]) (fun h => absurd (Finset.mem_univ a) h)] at h
    simp only [conjTranspose_apply, hF, if_true] at h
    exact h
  simp only [hv, star_sum, star_mul', Finset.sum_mul_sum]
  calc ∑ b, ∑ b₁, ∑ b₂, F b b₁ * ψ (e.symm (a, b₁)) * (star (F b b₂) * star (ψ (e.symm (a', b₂))))
      = ∑ b₁, ∑ b₂, (∑ b, star (F b b₂) * F b b₁) *
          (ψ (e.symm (a, b₁)) * star (ψ (e.symm (a', b₂)))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by
      simp only [hFu, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]

end PureMarg

/-! ## The `e'J`-marginal -/

section Marginal

variable {Λ X J : Finset σ}

/-- The splitting `(w, (s, e)) ↦ ((e, w|_J), (w|_{Λ∖J}, s))` of `ℋ_Λ ⊗ ℋ_{s'} ⊗ ℋ_{e'}`
into `(ℋ_{e'} ⊗ ℋ_J) ⊗ (ℋ_{Λ∖J} ⊗ ℋ_{s'})`. -/
def splitEJ (hJ : J ⊆ Λ) (X : Finset σ) :
    Reg loc Λ × (Reg loc X × Reg loc X) ≃
      (Reg loc X × Reg loc J) × (Reg loc (Λ \ J) × Reg loc X) :=
  ((glueEquiv hJ).symm.prodCongr (Equiv.prodComm _ _)).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans ((Equiv.prodComm _ _).prodCongr (Equiv.refl _)))

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
@[simp] theorem splitEJ_symm_apply (hJ : J ⊆ Λ) (e : Reg loc X) (j : Reg loc J)
    (r : Reg loc (Λ \ J)) (s : Reg loc X) :
    (splitEJ hJ X).symm ((e, j), (r, s)) = (glue j r, (s, e)) := rfl

/-- The `e'J`-marginal of `|ψ⟩⟨ψ|` on `Reg Λ × (Reg X × Reg X)`. -/
noncomputable def redEJ (hJ : J ⊆ Λ) (ψ : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) : _root_.MState (Reg loc X × Reg loc J) :=
  (MState.physlibEquiv ((pureState ψ hψ).submatrix (splitEJ hJ X).symm)).traceRight

theorem redEJ_m (hJ : J ⊆ Λ) (ψ : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (a a' : Reg loc X × Reg loc J) :
    (redEJ hJ ψ hψ).m a a' =
      ∑ b, ψ ((splitEJ hJ X).symm (a, b)) * star (ψ ((splitEJ hJ X).symm (a', b))) := by
  rfl

/-- D10.15.3. The trace distance of the `e'J`-reductions of unit vectors is at most
`½‖|ψ₁⟩⟨ψ₁| - |ψ₂⟩⟨ψ₂|‖₁ ≤ ‖ψ₁ - ψ₂‖` (D2.5). -/
theorem step_10_15_3 (hJ : J ⊆ Λ) (ψ₁ ψ₂ : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ)
    (h₁ : star ψ₁ ⬝ᵥ ψ₁ = 1) (h₂ : star ψ₂ ⬝ᵥ ψ₂ = 1) :
    TrDistance (redEJ hJ ψ₁ h₁) (redEJ hJ ψ₂ h₂) ≤ vnorm (ψ₁ - ψ₂) := by
  -- partial trace contracts, relabelling is isometric
  refine (trDistance_traceRight_le _ _).trans ?_
  rw [MState.trDistance_physlibEquiv, MState.toSubState_submatrix, MState.toSubState_submatrix,
    SubState.D₁_submatrix, MState.D₁_eq_traceNorm_div_two]
  -- D2.5.1
  have e : (pureState ψ₁ h₁).M - (pureState ψ₂ h₂).M =
      vecMulVec ψ₁ (star ψ₁) - vecMulVec ψ₂ (star ψ₂) := rfl
  rw [e, traceNorm_vecMulVec_sub_vecMulVec_div_two h₁ h₂, vnorm_eq_sqrt]
  -- D2.5.2
  refine Real.sqrt_le_sqrt ?_
  have hηξ : star ψ₂ ⬝ᵥ ψ₁ = star (star ψ₁ ⬝ᵥ ψ₂) := by
    rw [← Matrix.star_dotProduct_star, star_star, dotProduct_comm]
  have hre := Complex.re_le_norm (star ψ₁ ⬝ᵥ ψ₂)
  rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h₁, h₂, hηξ]
  simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  nlinarith [sq_nonneg (1 - ‖star ψ₁ ⬝ᵥ ψ₂‖)]

end Marginal

/-! ## D10.15.1 The unitary does not touch `e' ∪ J` -/

section Unitary

variable {Λ X N J : Finset σ}

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem splitN_apply (hN : N ⊆ Λ) (w : Reg loc Λ) (s e : Reg loc X) : -- helper
    splitN hN X (w, (s, e)) = ((restr hN w, s), (restr sdiff_subset w, e)) := rfl

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem restr_glue_of_subset_sdiff (hN : N ⊆ Λ) (hNJ : N ⊆ Λ \ J) -- helper
    (j : Reg loc J) (r : Reg loc (Λ \ J)) : restr hN (glue j r) = restr hNJ r := by
  funext i
  have hi : (i : σ) ∉ J := (mem_sdiff.1 (hNJ i.2)).2
  simp only [restr, Finset.restrict₂, glue, dif_neg hi]

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem restr_glue_eq_iff (hJ : J ⊆ Λ \ N) (j j' : Reg loc J) (r r' : Reg loc (Λ \ J)) : -- helper
    restr (sdiff_subset : Λ \ N ⊆ Λ) (glue j r) = restr sdiff_subset (glue j' r') ↔
      j = j' ∧ restr (sdiff_subset : (Λ \ J) \ N ⊆ Λ \ J) r = restr sdiff_subset r' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h ⟨i, hJ i.2⟩
      simpa [restr, Finset.restrict₂, glue, i.2] using this
    · obtain ⟨hi, hiN⟩ := mem_sdiff.1 i.2
      have hiJ := (mem_sdiff.1 hi).2
      have := congrFun h ⟨i, mem_sdiff.2 ⟨(mem_sdiff.1 hi).1, hiN⟩⟩
      simpa [restr, Finset.restrict₂, glue, hiJ] using this
  · rintro ⟨rfl, h⟩
    funext i
    by_cases hiJ : (i : σ) ∈ J
    · simp [restr, Finset.restrict₂, glue, hiJ]
    · have := congrFun h
        ⟨i, mem_sdiff.2 ⟨mem_sdiff.2 ⟨(mem_sdiff.1 i.2).1, hiJ⟩, (mem_sdiff.1 i.2).2⟩⟩
      simpa [restr, Finset.restrict₂, glue, hiJ] using this

omit [∀ i, DecidableEq (loc i)] in
theorem conjTranspose_mul_self_submatrix_kronecker {m n : Type*} [Fintype m] -- helper
    [DecidableEq m] [Finite n] [DecidableEq n] {V : Matrix m m ℂ}
    (hV : V ∈ unitary (Matrix m m ℂ)) {G : Type*} [Fintype G] [DecidableEq G] (f : G ≃ m × n) :
    ((V ⊗ₖ (1 : Matrix n n ℂ)).submatrix f f)ᴴ * (V ⊗ₖ (1 : Matrix n n ℂ)).submatrix f f = 1 := by
  have := Fintype.ofFinite n
  rw [conjTranspose_submatrix, submatrix_mul_equiv, ← star_eq_conjTranspose,
    Unitary.star_mul_self_of_mem (kronecker_mem_unitary hV (one_mem _)), submatrix_one_equiv]

omit [∀ i, DecidableEq (loc i)] in
theorem star_unitary_mulVec_dotProduct_mulVec {G : Type*} [Fintype G] [DecidableEq G] -- helper
    {U : Matrix G G ℂ} (hU : Uᴴ * U = 1) (ψ : G → ℂ) : star (U *ᵥ ψ) ⬝ᵥ (U *ᵥ ψ) = star ψ ⬝ᵥ ψ := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hU, vecMul_one]

/-- D10.15.1. `U' = V ⊗ I` acts on `N ∪ s'`, disjoint from `e'` and `J ⊆ Λ ∖ N`: the
`e'J`-reductions of `U'ψ` and `ψ` agree. -/
theorem redEJ_unitary (hN : N ⊆ Λ) (hJ : J ⊆ Λ \ N)
    {V : Matrix (Reg loc N × Reg loc X) (Reg loc N × Reg loc X) ℂ} (hV : V ∈ unitary _)
    (ψ : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hψ' : star (((V ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X) _ ℂ)).submatrix
      (splitN hN X) (splitN hN X)) *ᵥ ψ) ⬝ᵥ
        (((V ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X) _ ℂ)).submatrix
          (splitN hN X) (splitN hN X)) *ᵥ ψ) = 1) :
    redEJ (hJ.trans sdiff_subset)
      (((V ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X) _ ℂ)).submatrix
        (splitN hN X) (splitN hN X)) *ᵥ ψ) hψ' = redEJ (hJ.trans sdiff_subset) ψ hψ := by
  have hNJ : N ⊆ Λ \ J := fun i hi => mem_sdiff.2 ⟨hN hi, fun h => (mem_sdiff.1 (hJ h)).2 hi⟩
  apply _root_.MState.ext_m
  ext a a'
  rw [redEJ_m, redEJ_m]
  refine sum_mulVec_mul_star_mulVec (splitEJ _ X) (conjTranspose_mul_self_submatrix_kronecker hV _)
    (fun b b' => V (restr hNJ b.1, b.2) (restr hNJ b'.1, b'.2) *
      if restr (sdiff_subset : (Λ \ J) \ N ⊆ Λ \ J) b.1 = restr sdiff_subset b'.1 then 1 else 0)
    ?_ ψ a a'
  rintro ⟨e, j⟩ ⟨e', j'⟩ ⟨r, s⟩ ⟨r', s'⟩
  rw [splitEJ_symm_apply, splitEJ_symm_apply, submatrix_apply, splitN_apply, splitN_apply,
    kroneckerMap_apply, restr_glue_of_subset_sdiff hN hNJ, restr_glue_of_subset_sdiff hN hNJ,
    one_apply]
  simp only [Prod.mk.injEq, restr_glue_eq_iff hJ]
  by_cases h₁ : e = e' <;> by_cases h₂ : j = j' <;> simp [h₁, h₂, and_comm]

end Unitary

/-! ## D10.6.1 The `e'J`-marginal of `φ` -/

section Copy

variable [∀ i, Nonempty (loc i)] {Λ X J : Finset σ}

/-- The configuration of `Λ ∖ J` blank on `X` and `z` on `Λ ∖ (X ∪ J)`. -/
noncomputable def padX (z : Reg loc (Λ \ (X ∪ J))) : Reg loc (Λ \ J) := fun i => -- helper
  if h : (i : σ) ∈ X then blank X ⟨i, h⟩ else
    z ⟨i, mem_sdiff.2 ⟨(mem_sdiff.1 i.2).1, by simp [h, (mem_sdiff.1 i.2).2]⟩⟩

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem padX_injective : Function.Injective (padX (loc := loc) (Λ := Λ) (X := X) (J := J)) := by
  intro z z' h
  funext i
  obtain ⟨hiΛ, hi⟩ := mem_sdiff.1 i.2
  simp only [mem_union, not_or] at hi
  have := congrFun h ⟨i, mem_sdiff.2 ⟨hiΛ, hi.2⟩⟩
  simpa [padX, hi.1] using this

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem restr_glue_padX (hJ : J ⊆ Λ \ X) (hX : X ⊆ Λ) (j : Reg loc J) -- helper
    (z : Reg loc (Λ \ (X ∪ J))) : restr hX (glue j (padX z)) = blank X := by
  funext i
  have hi : (i : σ) ∉ J := fun h => (mem_sdiff.1 (hJ h)).2 i.2
  simp [restr, Finset.restrict₂, glue, padX, hi, i.2]

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem glue_restr_glue_padX (hJ : J ⊆ Λ \ X) (e : Reg loc X) (j : Reg loc J) -- helper
    (z : Reg loc (Λ \ (X ∪ J))) :
    glue e (restr sdiff_subset (glue j (padX z))) =
      glue (T := Λ) ((unionEquiv (disjoint_sdiff.mono_right hJ : Disjoint X J)).symm (e, j)) z := by
  funext i
  by_cases hX : (i : σ) ∈ X
  · simp [glue, hX]
  · by_cases hJ' : (i : σ) ∈ J
    · simp [glue, restr, Finset.restrict₂, hX, hJ', sdiffEquiv]
    · simp [glue, restr, Finset.restrict₂, hX, hJ', padX]

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem mem_range_padX (hX : X ⊆ Λ) (hJ : J ⊆ Λ \ X) (j : Reg loc J) -- helper
    (r : Reg loc (Λ \ J)) (h : restr hX (glue j r) = blank X) :
    r = padX (X := X)
      (restr (sdiff_subset_sdiff le_rfl subset_union_right : Λ \ (X ∪ J) ⊆ Λ \ J) r) := by
  funext i
  by_cases hi : (i : σ) ∈ X
  · have hiJ : (i : σ) ∉ J := fun h' => (mem_sdiff.1 (hJ h')).2 hi
    have := congrFun h ⟨i, hi⟩
    simp only [restr, Finset.restrict₂, glue, dif_neg hiJ] at this
    simp [padX, hi, ← this]
  · simp [padX, hi, restr, Finset.restrict₂]

/-- `φ = 𝓡_X Ω` has the norm of `Ω`. -/
theorem dotProduct_copyVec' (hX : X ⊆ Λ) (Ω : Reg loc Λ → ℂ) : -- helper
    star (copyVec hX Ω) ⬝ᵥ copyVec hX Ω = star Ω ⬝ᵥ Ω := by
  symm
  refine Fintype.sum_of_injective
    (fun w => (glue (blank X) (restr sdiff_subset w), (blank X, restr hX w))) ?_ _ _ ?_ ?_
  · intro w w' h
    simp only [Prod.mk.injEq] at h
    rw [← glue_restr hX w, ← glue_restr hX w', h.2.2,
      ← restr_glue_compl (blank X) (restr sdiff_subset w), h.1, restr_glue_compl]
  · rintro ⟨w, s, e⟩ hw
    simp only [Pi.star_apply, copyVec, glueEquiv_symm_apply, glueEquiv_apply]
    by_cases h : restr hX w = blank X ∧ s = blank X
    · exfalso
      obtain ⟨h₁, rfl⟩ := h
      refine hw ⟨glue e (restr sdiff_subset w), ?_⟩
      simp only [restr_glue, restr_glue_compl]
      rw [← h₁, glue_restr]
    · simp [h]
  · intro w
    simp [copyVec]

/-- D10.6.1. `φ = 𝓡_X Ω`, so for every physical `J ⊆ Λ ∖ X` the `(e', J)`-reduction of `φ`
equals the `(X, J)`-reduction of `Ω` with `X → e'`. -/
theorem step_10_6_1 (hX : X ⊆ Λ) (hJ : J ⊆ Λ \ X) (Ω : Reg loc Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hφ : star (copyVec hX Ω) ⬝ᵥ copyVec hX Ω = 1) :
    redEJ (hJ.trans sdiff_subset) (copyVec hX Ω) hφ =
      unionState (pureState Ω hΩ) (disjoint_sdiff.mono_right hJ) hX (hJ.trans sdiff_subset) := by
  apply _root_.MState.ext_m
  ext ⟨e, j⟩ ⟨e', j'⟩
  rw [redEJ_m]
  symm
  refine Fintype.sum_of_injective (fun z => (padX z, blank X))
    (fun z z' h => padX_injective (congrArg Prod.fst h)) _ _ ?_ ?_
  · rintro ⟨r, s⟩ hb
    have key (e : Reg loc X) (j : Reg loc J) :
        copyVec hX Ω ((splitEJ (hJ.trans sdiff_subset) X).symm ((e, j), (r, s))) = 0 := by
      rw [splitEJ_symm_apply]
      simp only [copyVec, glueEquiv_symm_apply, glueEquiv_apply]
      by_cases h : restr hX (glue j r) = blank X ∧ s = blank X
      · refine absurd ⟨restr (sdiff_subset_sdiff le_rfl subset_union_right) r, ?_⟩ hb
        simp only [h.2, Prod.mk.injEq, and_true]
        exact (mem_range_padX hX hJ j r h.1).symm
      · simp [h]
    rw [key, zero_mul]
  · intro z
    simp only [splitEJ_symm_apply, copyVec, glueEquiv_symm_apply, glueEquiv_apply,
      restr_glue_padX hJ hX, and_self, if_true, glue_restr_glue_padX hJ]
    rfl

end Copy

/-! ## D10.6.2 The `e'J`-marginal of `η` is a product -/

section Restored

/-- Von Neumann entropy is additive on product states. -/
theorem Sᵥₙ_prod {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ₁ : _root_.MState d₁) (ρ₂ : _root_.MState d₂) : -- helper
    Sᵥₙ (ρ₁ ⊗ᴹ ρ₂) = Sᵥₙ ρ₁ + Sᵥₙ ρ₂ := by
  obtain ⟨π, hπ⟩ := _root_.MState.spectrum_prod ρ₁ ρ₂
  have h := H_mul_add (fun i => (ρ₁.spectrum i : ℝ)) (fun j => (ρ₂.spectrum j : ℝ))
    ρ₁.spectrum.normalized ρ₂.spectrum.normalized
  simp only [Sᵥₙ, Hₛ, H₁]
  rw [← π.sum_comp, Fintype.sum_prod_type]
  simp only [hπ, Prob.coe_mul]
  simpa [H, Fintype.sum_prod_type] using h

/-- A state whose density matrix is a Kronecker product has zero mutual information. -/
theorem qMutualInfo_eq_zero_of_kronecker {α β : Type*} [Fintype α] [DecidableEq α] -- helper
    [Fintype β] [DecidableEq β] (ρ : _root_.MState (α × β)) (A : Matrix α α ℂ)
    (B : Matrix β β ℂ) (h : ρ.m = A ⊗ₖ B) : qMutualInfo ρ = 0 := by
  have hR : ρ.traceRight.m = B.trace • A := by
    change ρ.m.traceRight = _
    ext i i'
    simp [h, Matrix.traceRight, Matrix.trace, kroneckerMap_apply, Finset.mul_sum, mul_comm]
  have hL : ρ.traceLeft.m = A.trace • B := by
    change ρ.m.traceLeft = _
    ext j j'
    simp [h, Matrix.traceLeft, Matrix.trace, kroneckerMap_apply, Finset.sum_mul]
  have htr : A.trace * B.trace = 1 := by rw [← trace_kronecker, ← h, ρ.tr']
  have hprod : ρ = ρ.traceRight ⊗ᴹ ρ.traceLeft := by
    apply _root_.MState.ext_m
    change ρ.m = ρ.traceRight.m ⊗ₖ ρ.traceLeft.m
    rw [hR, hL, smul_kronecker, kronecker_smul, smul_smul, mul_comm, htr, one_smul, h]
  rw [qMutualInfo, (congrArg Sᵥₙ hprod).trans (Sᵥₙ_prod _ _)]
  ring

variable {Λ X J : Finset σ}

theorem redEJ_m_of_tensor (hJ : J ⊆ Λ) (Ω : Reg loc Λ → ℂ) (ξ : Reg loc X × Reg loc X → ℂ) -- helper
    (ψ : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ) (hψ : ∀ w v, ψ (w, v) = Ω w * ξ v)
    (h : star ψ ⬝ᵥ ψ = 1) :
    (redEJ hJ ψ h).m =
      (Matrix.of fun e e' => ∑ s, ξ (s, e) * star (ξ (s, e'))) ⊗ₖ
        (Matrix.of fun j j' => ∑ r : Reg loc (Λ \ J), Ω (glue j r) * star (Ω (glue j' r))) := by
  ext ⟨e, j⟩ ⟨e', j'⟩
  rw [redEJ_m, kroneckerMap_apply, of_apply, of_apply, Fintype.sum_prod_type, Finset.sum_mul_sum,
    Finset.sum_comm]
  simp only [splitEJ_symm_apply, hψ, star_mul']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- D10.6.2. In `η`, `e'` is purified by `s'` and `Ω` is a tensor factor:
`ρ^η_{e'J} = ρ^η_{e'} ⊗ ρ^η_J`, `I(e' : J)_η = 0`. -/
theorem step_10_6_2 [∀ i, Nonempty (loc i)] (hX : X ⊆ Λ) (hJ : J ⊆ Λ) (Ω : Reg loc Λ → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hη : star (restoredVec hX Ω hΩ) ⬝ᵥ restoredVec hX Ω hΩ = 1) :
    qMutualInfo (redEJ hJ (restoredVec hX Ω hΩ) hη) = 0 :=
  qMutualInfo_eq_zero_of_kronecker _ _ _ (redEJ_m_of_tensor hJ Ω
    (fun v => ∑ x, (Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x) : ℂ) *
      ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) v.1 x *
      ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) v.2 x)
    _ (fun _ _ => rfl) hη)

/-- `∑_x √p_x |x⟩|x⟩` is a unit vector when `p` is a probability vector and `|x⟩` the columns of
a unitary. -/
theorem dotProduct_schmidt {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ} -- helper
    (hU : star U * U = 1) {p : n → ℝ} (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) :
    star (fun v : n × n => ∑ x, (Real.sqrt (p x) : ℂ) * U v.1 x * U v.2 x) ⬝ᵥ
      (fun v : n × n => ∑ x, (Real.sqrt (p x) : ℂ) * U v.1 x * U v.2 x) = 1 := by
  set a : n → ℂ := fun x => (Real.sqrt (p x) : ℂ)
  have hU' (x y : n) : ∑ s, star (U s x) * U s y = if x = y then 1 else 0 := by
    have h := congrFun (congrFun hU x) y
    simpa [Matrix.mul_apply, star_apply, one_apply] using h
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, star_sum, Finset.sum_mul_sum]
  calc ∑ s, ∑ e, ∑ x, ∑ y, star (a x * U s x * U e x) * (a y * U s y * U e y)
      = ∑ s, ∑ x, ∑ e, ∑ y, star (a x * U s x * U e x) * (a y * U s y * U e y) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s, ∑ x, ∑ y, ∑ e, star (a x * U s x * U e x) * (a y * U s y * U e y) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x, ∑ s, ∑ y, ∑ e, star (a x * U s x * U e x) * (a y * U s y * U e y) :=
        Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ s, ∑ e, star (a x * U s x * U e x) * (a y * U s y * U e y) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x, ∑ y, star (a x) * a y *
          ((∑ s, star (U s x) * U s y) * (∑ e, star (U e x) * U e y)) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [star_mul']
        ring
    _ = ∑ x, ((p x : ℝ) : ℂ) := by
        simp only [hU', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [a, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (hp x)]
    _ = 1 := by rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]

/-- `η` is a unit vector. -/
theorem dotProduct_restoredVec' [∀ i, Nonempty (loc i)] (hX : X ⊆ Λ) (Ω : Reg loc Λ → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) : star (restoredVec hX Ω hΩ) ⬝ᵥ restoredVec hX Ω hΩ = 1 := by
  have hξ := dotProduct_schmidt (Unitary.coe_star_mul_self
    (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary) (marg Ω hΩ hX).psd.eigenvalues_nonneg
    (MState.sum_eigenvalues_eq_one ((pureState Ω hΩ).restrict hX))
  set ξ : Reg loc X × Reg loc X → ℂ := fun v =>
    ∑ x, (Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x) : ℂ) *
      ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) v.1 x *
      ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) v.2 x
  have e : restoredVec hX Ω hΩ = fun q => Ω q.1 * ξ q.2 := rfl
  rw [e]
  calc star (fun q : Reg loc Λ × (Reg loc X × Reg loc X) => Ω q.1 * ξ q.2) ⬝ᵥ
        (fun q => Ω q.1 * ξ q.2) = (star Ω ⬝ᵥ Ω) * (star ξ ⬝ᵥ ξ) := by
        simp only [dotProduct, Pi.star_apply, star_mul']
        refine (Fintype.sum_prod_type _).trans ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 1 := by rw [hΩ, hξ, one_mul]

end Restored

/-! ## D10.15 The mutual-information bound -/

section MutualInfo

/-- Trace distance does not see a relabelling. -/
theorem trDistance_relabel {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] -- helper
    [DecidableEq β] (ρ τ : _root_.MState α) (e : β ≃ α) :
    TrDistance (ρ.relabel e) (τ.relabel e) = TrDistance ρ τ := by
  have h (ω : _root_.MState α) :
      MState.physlibEquiv.symm (ω.relabel e) = (MState.physlibEquiv.symm ω).submatrix e := by
    apply MState.physlibEquiv.injective
    rw [Equiv.apply_symm_apply, MState.physlibEquiv_submatrix, Equiv.apply_symm_apply]
  rw [trDistance_eq_D₁, trDistance_eq_D₁, h, h, MState.toSubState_submatrix,
    MState.toSubState_submatrix, SubState.D₁_submatrix]

/-- D10.15.4. Lemma 2.1 with first argument `D`, for `S(D|E)` and for `S(D)` (`E` trivial),
through `I(D:E) = S(D) - S(D|E)`: `|ΔI| ≤ 2 · 4 √δ log(e d_D)`. -/
theorem abs_qMutualInfo_sub_le {D E : Type*} [Fintype D] [DecidableEq D] [Nonempty D] -- helper
    [Fintype E] [DecidableEq E] (ρ τ : _root_.MState (D × E)) :
    |qMutualInfo ρ - qMutualInfo τ| ≤
      8 * Real.sqrt (TrDistance ρ τ) * Real.log (Real.exp 1 * Fintype.card D) := by
  have hd : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hl : 0 ≤ Real.log (Real.exp 1 * Fintype.card D) := Real.log_nonneg (by nlinarith)
  have hC : 2 * C_h ≤ 4 := by
    have := (div_le_one (Real.exp_pos 1)).2 he
    rw [C_h]; linarith
  have hC0 : 0 ≤ 2 * C_h := by unfold C_h; positivity
  -- `S(D|E)`
  have h₁ := (step_2_4_3 ρ τ).trans
    (step_2_4_4 (trDistance_nonneg ρ τ) (trDistance_le_one ρ τ) hd)
  -- `S(D)`: `E` trivial
  have hδ : TrDistance (ρ.traceRight.relabel (Equiv.prodPUnit.{1} D))
      (τ.traceRight.relabel (Equiv.prodPUnit.{1} D)) ≤ TrDistance ρ τ :=
    (trDistance_relabel _ _ _).trans_le (trDistance_traceRight_le ρ τ)
  have h₂ := (step_2_4_3 (ρ.traceRight.relabel (Equiv.prodPUnit.{1} D))
    (τ.traceRight.relabel (Equiv.prodPUnit.{1} D))).trans
    (step_2_4_4 (trDistance_nonneg _ _) (trDistance_le_one _ _) hd)
  have hS (ω : _root_.MState (D × E)) :
      qConditionalEnt (ω.traceRight.relabel (Equiv.prodPUnit.{1} D)) = Sᵥₙ ω.traceRight := by
    rw [qConditionalEnt, Sᵥₙ_relabel,
      Sᵥₙ_unit_zero (ω.traceRight.relabel (Equiv.prodPUnit.{1} D)).traceLeft, sub_zero]
  rw [hS ρ, hS τ] at h₂
  have k₁ := mul_le_mul_of_nonneg_right hC (mul_nonneg (Real.sqrt_nonneg (TrDistance ρ τ)) hl)
  have k₂ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hδ) hl) hC0
  have e : qMutualInfo ρ - qMutualInfo τ =
      (Sᵥₙ ρ.traceRight - Sᵥₙ τ.traceRight) - (qConditionalEnt ρ - qConditionalEnt τ) := by
    rw [qMutualInfo, qMutualInfo, qConditionalEnt, qConditionalEnt]; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have k₃ : 2 * C_h * Real.sqrt (TrDistance ρ τ) * Real.log (Real.exp 1 * Fintype.card D) ≤
      4 * (Real.sqrt (TrDistance ρ τ) * Real.log (Real.exp 1 * Fintype.card D)) := by
    rw [mul_assoc]; exact k₁
  have k₄ : 2 * C_h * Real.sqrt (TrDistance (ρ.traceRight.relabel (Equiv.prodPUnit.{1} D))
      (τ.traceRight.relabel (Equiv.prodPUnit.{1} D))) * Real.log (Real.exp 1 * Fintype.card D) ≤
      2 * C_h * (Real.sqrt (TrDistance ρ τ) * Real.log (Real.exp 1 * Fintype.card D)) := by
    rw [mul_assoc]; exact k₂
  linarith

/-- The mutual information of two disjoint regions of `Ω` is that of their `unionState`. -/
theorem qMutualInfo_unionState {U X J : Finset σ} (ρ : Arealaw.MState (Reg loc U) ℂ) -- helper
    (hd : Disjoint X J) (hX : X ⊆ U) (hJ : J ⊆ U) :
    qMutualInfo (unionState ρ hd hX hJ) = ρ.toSubState.mutualInfo hX hJ := by
  rw [qMutualInfo, Sᵥₙ_traceLeft_unionState, Sᵥₙ_traceRight_unionState, Sᵥₙ_unionState,
    SubState.mutualInfo_def]
  ring

/-- D10.15.7. Discarding systems: `I_Ω(X' : J) ≤ I_Ω(X : J)` for `X' ⊆ X` (D2.2 item 3). -/
theorem mutualInfo_le_of_subset {Λ X X' J : Finset σ} (ρ : Arealaw.MState (Reg loc Λ) ℂ) -- helper
    (hX : X ⊆ Λ) (hX' : X' ⊆ X) (hJ : J ⊆ Λ) (hXJ : Disjoint X J) :
    ρ.toSubState.mutualInfo (hX'.trans hX) hJ ≤ ρ.toSubState.mutualInfo hX hJ := by
  have key : ∀ (Y : Finset σ) (hY : Y ⊆ Λ), Y = X →
      ρ.toSubState.mutualInfo hJ hY = ρ.toSubState.mutualInfo hJ hX := by
    rintro Y hY rfl; rfl
  have h := ρ.mutualInfo_le_mutualInfo_union (hXJ.symm.mono_right hX')
    (hXJ.symm.mono_right sdiff_subset) disjoint_sdiff hJ (hX'.trans hX) (sdiff_subset.trans hX)
  rw [SubState.mutualInfo_comm, SubState.mutualInfo_comm _ hX]
  exact h.trans_eq (key _ _ (union_sdiff_of_subset hX'))

variable [∀ i, Nonempty (loc i)]

/-- D10.15 (D10.15.1–4, 7). Let `X ⊆ N ⊆ Λ`, `J ⊆ Λ ∖ N`, `V` a unitary on `N ∪ s'` and
`U' = V ⊗ I`, with `‖U'φ - η‖ ≤ δ'`. Then for every `X' ⊆ X`,
`I_Ω(X' : J) ≤ 8 √δ' log(e d_{e'})`, `d_{e'} = dim e' = |Reg X|`. -/
theorem step_10_15 {Λ X N J : Finset σ} (hX : X ⊆ Λ) (hN : N ⊆ Λ) (hXN : X ⊆ N)
    (hJ : J ⊆ Λ \ N) (Ω : Reg loc Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (V : Matrix (Reg loc N × Reg loc X) (Reg loc N × Reg loc X) ℂ) (hV : V ∈ unitary _)
    {δ' : ℝ}
    (hδ : vnorm ((((V ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X) _ ℂ)).submatrix (splitN hN X)
      (splitN hN X)) *ᵥ copyVec hX Ω) - restoredVec hX Ω hΩ) ≤ δ') :
    ∀ (X' : Finset σ) (hX' : X' ⊆ X),
      (pureState Ω hΩ).toSubState.mutualInfo (hX'.trans hX) (hJ.trans sdiff_subset) ≤
        8 * Real.sqrt δ' * Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
  intro X' hX'
  have hU := conjTranspose_mul_self_submatrix_kronecker hV (splitN hN X)
  have hφ := (dotProduct_copyVec' hX Ω).trans hΩ
  have hη := dotProduct_restoredVec' hX Ω hΩ
  have hUφ := (star_unitary_mulVec_dotProduct_mulVec hU (copyVec hX Ω)).trans hφ
  have hJX : J ⊆ Λ \ X := fun i hi =>
    mem_sdiff.2 ⟨(mem_sdiff.1 (hJ hi)).1, fun h => (mem_sdiff.1 (hJ hi)).2 (hXN h)⟩
  have hl : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
    have hd : (1 : ℝ) ≤ Fintype.card (Reg loc X) := by exact_mod_cast Fintype.card_pos
    exact Real.log_nonneg (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
  -- D10.15.1: `I(e' : J)_{U'φ} = I_Ω(X : J)`
  have h₁ : qMutualInfo (redEJ (hJ.trans sdiff_subset) _ hUφ) =
      (pureState Ω hΩ).toSubState.mutualInfo hX (hJ.trans sdiff_subset) := by
    rw [redEJ_unitary hN hJ hV _ hφ, step_10_6_1 hX hJX Ω hΩ hφ, qMutualInfo_unionState]
  -- D10.15.2: `I(e' : J)_η = 0`
  have h₂ := step_10_6_2 hX (hJ.trans sdiff_subset) Ω hΩ hη
  -- D10.15.3: trace distance of the `e'J`-reductions `≤ ‖U'φ - η‖ ≤ δ'`
  have h₃ := (step_10_15_3 (hJ.trans sdiff_subset) _ _ hUφ hη).trans hδ
  -- D10.15.4: Lemma 2.1 with first argument `e'`
  have h₄ := abs_qMutualInfo_sub_le (redEJ (hJ.trans sdiff_subset) _ hUφ)
    (redEJ (hJ.trans sdiff_subset) _ hη)
  rw [h₁, h₂, sub_zero] at h₄
  -- D10.15.7: subsets of `X`
  calc (pureState Ω hΩ).toSubState.mutualInfo (hX'.trans hX) (hJ.trans sdiff_subset)
      ≤ (pureState Ω hΩ).toSubState.mutualInfo hX (hJ.trans sdiff_subset) :=
        mutualInfo_le_of_subset _ hX hX' _ (disjoint_sdiff.mono_right hJX)
    _ ≤ _ := (le_abs_self _).trans h₄
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h₃)
        (by norm_num)) hl

end MutualInfo

end AreaLaw
