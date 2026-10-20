import AreaLawRefactored.S03_InitialBox.BufferDiscount
import AreaLawForMathlib.Analysis.Matrix.TraceHolder

/-!
# §3.2 Optimized filters (proof of Lemma 3.2, D3.7–D3.13)

Digest `digest/03-initial-box.md` (D3.7–D3.13), paper `paper/sections/02-initial.tex`,
lines 335–573.
-/

namespace AreaLaw

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker

/-! ## D3.7 Optimized filters commute with their marginals -/

/-- The ordered product `f (k-1) ⋯ f 0`. -/
def prodDesc {n : Type*} [Fintype n] [DecidableEq n] (f : ℕ → Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 1
  | k + 1 => f k * prodDesc f k

section D371

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.7. A feasible filter `L ≥ ε`, `Tr L^{2/a} = 1`, written spectrally:
`L = V diag(x^{a/2}) V*` with `V` unitary, `x_i = l_i^{2/a} ≥ f = ε^{2/a}` and `∑ x_i = 1`. -/
def IsFilter (f a : ℝ) (L : Matrix m m ℂ) : Prop :=
  ∃ V : Matrix m m ℂ, Vᴴ * V = 1 ∧ ∃ x : m → ℝ, (∀ i, f ≤ x i) ∧ ∑ i, x i = 1 ∧
    L = V * diagonal (fun i ↦ ((x i ^ (a / 2) : ℝ) : ℂ)) * Vᴴ

/-- D3.7.1. The feasible filters form a compact set (`0 ≤ x_i ≤ 1`, `V` unitary). -/
theorem isCompact_setOf_isFilter {f a : ℝ} (hf : 0 ≤ f) (ha : 0 ≤ a) :
    IsCompact {L : Matrix m m ℂ | IsFilter f a L} := by
  have hS : IsCompact {x : m → ℝ | (∀ i, f ≤ x i) ∧ ∑ i, x i = 1} := by
    refine (isCompact_univ_pi fun _ : m ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_id).inter
        (isClosed_eq (by fun_prop) continuous_const) : IsClosed {x : m → ℝ | (fun _ ↦ f) ≤ x ∧
          ∑ i, x i = 1}) fun x hx ↦ Set.mem_univ_pi.mpr fun i ↦ ?_
    have h0 : ∀ k, 0 ≤ x k := fun k ↦ hf.trans (hx.1 k)
    exact ⟨h0 i, hx.2 ▸ Finset.single_le_sum (fun k _ ↦ h0 k) (Finset.mem_univ i)⟩
  have heq : {L : Matrix m m ℂ | IsFilter f a L} = (fun p : Matrix m m ℂ × (m → ℝ) ↦
      p.1 * diagonal (fun i ↦ ((p.2 i ^ (a / 2) : ℝ) : ℂ)) * p.1ᴴ) ''
      ({V : Matrix m m ℂ | Vᴴ * V = 1} ×ˢ {x | (∀ i, f ≤ x i) ∧ ∑ i, x i = 1}) := by
    ext L
    exact ⟨fun ⟨V, hV, x, hx, hs, e⟩ ↦ ⟨(V, x), ⟨hV, hx, hs⟩, e.symm⟩,
      fun ⟨⟨V, x⟩, ⟨hV, hx, hs⟩, e⟩ ↦ ⟨V, hV, x, hx, hs, e.symm⟩⟩
  rw [heq]
  refine (isCompact_setOf_conjTranspose_mul_self_eq_one.prod hS).image ?_
  have hd : Continuous fun p : Matrix m m ℂ × (m → ℝ) ↦
      diagonal (fun i ↦ ((p.2 i ^ (a / 2) : ℝ) : ℂ)) :=
    continuous_id.matrix_diagonal.comp (continuous_pi fun i ↦ Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity)).comp ((continuous_apply i).comp
        continuous_snd)))
  exact (continuous_fst.matrix_mul hd).matrix_mul continuous_fst.matrix_conjTranspose

/-- D3.7.1. A feasible filter with floor `f > 0` is invertible. -/
theorem IsFilter.isUnit_det {f a : ℝ} (hf : 0 < f) {L : Matrix m m ℂ} (hL : IsFilter f a L) :
    IsUnit L.det := by
  obtain ⟨V, hV, x, hx, -, rfl⟩ := hL
  have hV' : IsUnit V.det := isUnit_det_of_left_inverse hV
  rw [det_mul, det_mul, det_diagonal, isUnit_iff_ne_zero]
  refine mul_ne_zero (mul_ne_zero hV'.ne_zero (Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_))
    (isUnit_det_of_right_inverse (by rwa [mul_eq_one_comm] at hV)).ne_zero
  exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hf.trans_le (hx i)) _).ne'

/-- D3.7.1. The uniform filter `(dim)^{-a/2}` is feasible when `dim · f ≤ 1`. -/
theorem isFilter_uniform [Nonempty m] {f a : ℝ} (hcard : Fintype.card m * f ≤ 1) :
    IsFilter f a (diagonal fun _ : m ↦ ((((Fintype.card m : ℝ)⁻¹) ^ (a / 2) : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  refine ⟨1, by simp, fun _ ↦ (Fintype.card m : ℝ)⁻¹, fun _ ↦ ?_, ?_, by simp⟩
  · rw [inv_eq_one_div, le_div_iff₀ hpos, mul_comm]; exact hcard
  · simp [Finset.sum_const, Finset.card_univ, hpos.ne']

/-- D3.7.2. Feasibility is invariant under unitary conjugation (same spectrum). -/
theorem IsFilter.conj {f a : ℝ} {L W : Matrix m m ℂ} (hL : IsFilter f a L) (hW : Wᴴ * W = 1) :
    IsFilter f a (W * L * Wᴴ) := by
  obtain ⟨V, hV, x, hx, hs, rfl⟩ := hL
  refine ⟨W * V, ?_, x, hx, hs, by simp only [conjTranspose_mul, Matrix.mul_assoc]⟩
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul, hV]

/-- D3.7.2. For anti-Hermitian `B` and real `t`, `L(t) = e^{tB} L e^{-tB}` is feasible
whenever `L` is. -/
theorem IsFilter.exp_conj {f a : ℝ} {L B : Matrix m m ℂ} (hL : IsFilter f a L) (hB : Bᴴ = -B)
    (t : ℝ) :
    IsFilter f a (NormedSpace.exp ((t : ℂ) • B) * L * NormedSpace.exp ((-(t : ℂ)) • B)) := by
  have hc : (NormedSpace.exp ((t : ℂ) • B))ᴴ = NormedSpace.exp ((-(t : ℂ)) • B) := by
    rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hB, Complex.star_def, Complex.conj_ofReal,
      smul_neg, neg_smul]
  have hu : (NormedSpace.exp ((t : ℂ) • B))ᴴ * NormedSpace.exp ((t : ℂ) • B) = 1 := by
    rw [hc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl B).smul_left _ |>.smul_right _),
      neg_smul, neg_add_cancel, NormedSpace.exp_zero]
  have := hL.conj hu
  rwa [hc] at this

end D371

section D371chain

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

omit [∀ i, Fintype (loc i)] in
/-- `A ↦ A ⊗ 1` is continuous. -/
theorem continuous_extendId {S T : Finset σ} (h : S ⊆ T) :
    Continuous (Arealaw.extendId (loc := loc) (𝕜 := ℂ) h) :=
  continuous_pi fun w ↦ continuous_pi fun w' ↦ by
    simp only [Arealaw.extendId, Matrix.of_apply]
    split_ifs
    exacts [(continuous_apply _).comp (continuous_apply _), continuous_const]

/-- D3.7. The product `K = (L_{k-1} ⊗ 1) ⋯ (L_0 ⊗ 1)` of filters on `X_j ⊆ U`. -/
noncomputable def filterProd (hX : ∀ j, X j ⊆ U)
    (L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ) (k : ℕ) :
    Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ :=
  prodDesc (fun j ↦ Arealaw.extendId (hX j) (L j)) k

/-- `L ↦ K` is continuous (D3.7.1: `N` is continuous). -/
theorem continuous_filterProd (hX : ∀ j, X j ⊆ U) (k : ℕ) :
    Continuous fun L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ ↦
      filterProd hX L k := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    exact ((continuous_extendId (hX k)).comp (continuous_apply k)).matrix_mul ih

/-- D3.7.1. Feasible products with positive floors are invertible. -/
theorem isUnit_det_filterProd (hX : ∀ j, X j ⊆ U)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsUnit (L j).det) (k : ℕ) : IsUnit (filterProd hX L k).det := by
  induction k with
  | zero => simp [filterProd, prodDesc]
  | succ k ih =>
    rw [filterProd, prodDesc, det_mul]
    refine IsUnit.mul (isUnit_det_of_left_inverse (B := Arealaw.extendId (hX k) (L k)⁻¹) ?_) ih
    rw [← Arealaw.extendId_mul, nonsing_inv_mul _ (hL k), Arealaw.extendId_one]

/-- D3.7.1. Existence: for floors `f_j > 0` with `(dim H_{X_j}) f_j ≤ 1`, the norm
`N = ‖L_{k-1} ⋯ L_0 Ω‖` attains its maximum over feasible filters, and `N > 0`. -/
theorem step_3_7_1 (hX : ∀ j, X j ⊆ U) (k : ℕ) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    (ha : ∀ j, 0 ≤ a j) (hne : ∀ j, Nonempty (Arealaw.Reg loc (X j)))
    (hcard : ∀ j, Fintype.card (Arealaw.Reg loc (X j)) * f j ≤ 1)
    {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)} (hΩ : Ω ≠ 0) :
    ∃ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L j)) ∧
      (∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
        (∀ j, IsFilter (f j) (a j) (L' j)) →
          ‖toEuclideanLin (filterProd hX L' k) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L k) Ω‖) ∧
      0 < ‖toEuclideanLin (filterProd hX L k) Ω‖ := by
  -- D3.7.1: the feasible set is nonempty and compact, `N` is continuous
  have hcpt := isCompact_univ_pi fun j ↦ isCompact_setOf_isFilter (m := Arealaw.Reg loc (X j))
    (hf j).le (ha j)
  have hne' : (Set.univ.pi fun j ↦ {M | IsFilter (f j) (a j) M}).Nonempty :=
    ⟨fun j ↦ diagonal fun _ ↦ ((((Fintype.card (Arealaw.Reg loc (X j)) : ℝ)⁻¹) ^ (a j / 2) : ℝ)
      : ℂ), fun j _ ↦ isFilter_uniform (hcard j)⟩
  have hcont : Continuous fun L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j))
      (Arealaw.Reg loc (X j)) ℂ ↦ ‖toEuclideanLin (filterProd hX L k) Ω‖ := by
    refine continuous_norm.comp ?_
    simp only [toLpLin_apply]
    exact (PiLp.continuous_toLp 2 _).comp ((continuous_filterProd hX k).matrix_mulVec
      continuous_const)
  obtain ⟨L, hL, hmax⟩ := hcpt.exists_isMaxOn hne' hcont.continuousOn
  refine ⟨L, fun j ↦ hL j trivial, fun L' hL' ↦ hmax (fun j _ ↦ hL' j), norm_pos_iff.2 ?_⟩
  -- D3.7.1: feasible products are invertible, so `N > 0`
  intro h0
  have hK := isUnit_det_filterProd hX (fun j ↦ (hL j trivial).isUnit_det (hf j)) k
  apply hΩ
  have := congrArg (toEuclideanLin (filterProd hX L k)⁻¹) h0
  rwa [← LinearMap.comp_apply, ← toLpLin_mul_same, nonsing_inv_mul _ hK, toLpLin_one,
    LinearMap.id_apply, map_zero] at this

end D371chain

section D37

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The derivative at `0` of `z ↦ e^{zB} K e^{-zB}` is `BK - KB`. -/
theorem hasDerivAt_exp_conj (B K : Matrix m m ℂ) :
    HasDerivAt (fun z : ℂ ↦ NormedSpace.exp (z • B) * K * NormedSpace.exp ((-z) • B))
      (B * K - K * B) 0 := by
  have h2 : HasDerivAt (fun z : ℂ ↦ NormedSpace.exp ((-z) • B)) (-B) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_exp_smul_const (𝕂 := ℂ) B (-0 : ℂ)).scomp (0 : ℂ) (hasDerivAt_neg 0)
  refine (((hasDerivAt_exp_smul_const (𝕂 := ℂ) B (0 : ℂ)).mul_const K).mul h2).congr_deriv ?_
  simp [sub_eq_add_neg]

/-- D3.7.2. If `t ↦ ‖A Φ(e^{tB} L e^{-tB}) w‖²` has a local maximum at `t = 0` (`Φ` the lift to
the whole region, `A = K_{>j}`, `w = K_{<j} Ω`), then `Re ⟨A Φ(L) w, A Φ(BL - LB) w⟩ = 0`. -/
theorem step_3_7_2 {p : Type*} [Fintype p] [DecidableEq p]
    (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix p p ℂ) (A : Matrix p p ℂ) (L B : Matrix m m ℂ)
    (w : EuclideanSpace ℂ p)
    (hmax : IsLocalMax (fun t : ℝ ↦ ‖toEuclideanLin (A * Φ (NormedSpace.exp ((t : ℂ) • B) * L *
      NormedSpace.exp ((-(t : ℂ)) • B))) w‖ ^ 2) 0) :
    (inner ℂ (toEuclideanLin (A * Φ L) w) (toEuclideanLin (A * Φ (B * L - L * B)) w)).re = 0 := by
  let T : Matrix m m ℂ →L[ℂ] EuclideanSpace ℂ p := LinearMap.toContinuousLinearMap
    { toFun := fun X ↦ toEuclideanLin (A * Φ X) w
      map_add' := fun X Y ↦ by simp [Matrix.mul_add]
      map_smul' := fun c X ↦ by simp }
  have hMF : HasFDerivAt (fun z : ℂ ↦ NormedSpace.exp (z • B) * L * NormedSpace.exp ((-z) • B))
      ((ContinuousLinearMap.toSpanSingleton ℂ (B * L - L * B)).restrictScalars ℝ)
      ((fun t : ℝ ↦ (t : ℂ)) 0) := by
    simpa using (hasDerivAt_exp_conj B L).hasFDerivAt.restrictScalars ℝ
  have hv := (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hMF.comp_hasDerivAt (0 : ℝ) (Complex.ofRealCLM.hasDerivAt (x := 0)))
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.inner ℂ hv)
  have hfun : (⇑Complex.reCLM ∘ fun t ↦ inner ℂ ((⇑(T.restrictScalars ℝ) ∘
      (fun z : ℂ ↦ NormedSpace.exp (z • B) * L * NormedSpace.exp ((-z) • B)) ∘ Complex.ofReal) t)
      ((⇑(T.restrictScalars ℝ) ∘
      (fun z : ℂ ↦ NormedSpace.exp (z • B) * L * NormedSpace.exp ((-z) • B)) ∘ Complex.ofReal) t)) =
      fun t : ℝ ↦ ‖toEuclideanLin (A * Φ (NormedSpace.exp ((t : ℂ) • B) * L *
        NormedSpace.exp ((-(t : ℂ)) • B))) w‖ ^ 2 := by
    funext t
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [← RCLike.re_to_complex, ← @norm_sq_eq_re_inner ℂ]
    rfl
  rw [hfun] at hre
  have h0 := hmax.hasDerivAt_eq_zero hre
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.add_re, Complex.ofReal_zero,
    zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h0
  rw [← inner_conj_symm (T (B * L - L * B)), Complex.conj_re] at h0
  change (inner ℂ (toEuclideanLin (A * Φ L) w) (toEuclideanLin (A * Φ (B * L - L * B)) w)).re +
    (inner ℂ (toEuclideanLin (A * Φ L) w) (toEuclideanLin (A * Φ (B * L - L * B)) w)).re = 0
    at h0
  linarith

/-- D3.7.3 (one peel). If `L` is invertible on `X ⊆ U` and commutes with the marginal
`ρ_{φ,X}`, then `⟨φ, L W L⁻¹ φ⟩ = ⟨φ, W φ⟩` for every `W` on `X`. -/
theorem step_3_7_3 {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {X U : Finset σ} (hX : X ⊆ U) (φ : Arealaw.Reg loc U → ℂ)
    {L : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ} (hL : IsUnit L.det)
    (hc : L * Arealaw.ptrace hX (vecMulVec φ (star φ)) =
      Arealaw.ptrace hX (vecMulVec φ (star φ)) * L)
    (W : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ) :
    star φ ⬝ᵥ (Arealaw.extendId hX (L * W * L⁻¹) *ᵥ φ) =
      star φ ⬝ᵥ (Arealaw.extendId hX W *ᵥ φ) := by
  rw [Arealaw.dotProduct_extendId_mulVec, Arealaw.dotProduct_extendId_mulVec, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← hc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    nonsing_inv_mul _ hL, Matrix.one_mul]

/-- D3.7.4. If `L > 0`, `ρ = ρ*` and `Re Tr(L⁻¹ ρ L B) = 0` for every anti-Hermitian `B`,
then `[L, ρ] = 0`. -/
theorem step_3_7_4 {L ρ : Matrix m m ℂ} (hL : L.PosDef) (hρ : ρ.IsHermitian)
    (h : ∀ B : Matrix m m ℂ, Bᴴ = -B → (L⁻¹ * ρ * L * B).trace.re = 0) : L * ρ = ρ * L := by
  generalize hY : L⁻¹ * ρ * L = Y at h
  -- `Y_a = Y - Y*` is anti-Hermitian, `Tr(Y_a B) = 2i Im Tr(Y B) = 0`; `B = Y_a`: `‖Y_a‖₂ = 0`
  set N := Y - Yᴴ
  have hN : Nᴴ = -N := by simp [N]
  have hNB : ∀ B : Matrix m m ℂ, Bᴴ = -B → (N * B).trace = 0 := by
    intro B hB
    have h2 : (Yᴴ * B).trace = -star (Y * B).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hB, Matrix.neg_mul, trace_neg, neg_neg,
        trace_mul_comm]
    rw [show N * B = Y * B - Yᴴ * B by simp [N, Matrix.sub_mul], trace_sub, h2, sub_neg_eq_add,
      RCLike.star_def, RCLike.add_conj, RCLike.re_to_complex, h B hB]
    simp
  have hNN : (Nᴴ * N).trace = 0 := by rw [hN, Matrix.neg_mul, trace_neg, hNB N hN, neg_zero]
  rw [trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero] at hNN
  -- `L⁻¹ ρ L = L ρ L⁻¹`, so `ρ L² = L² ρ`
  have hLu : IsUnit L.det := (isUnit_iff_isUnit_det L).mp hL.isUnit
  have h1 : L⁻¹ * ρ * L = L * ρ * L⁻¹ := by
    have := hNN
    rw [← hY] at this
    simp only [conjTranspose_mul, hρ.eq, hL.1.eq, conjTranspose_nonsing_inv] at this
    rw [this, Matrix.mul_assoc]
  have h2 : Commute (L * L) ρ := by
    have := congrArg (fun X ↦ L * X * L) h1
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hLu, Matrix.one_mul] at this
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hLu, Matrix.mul_one] at this
    simpa [Commute, SemiconjBy, Matrix.mul_assoc] using this.symm
  -- `L = (L²)^{1/2}` commutes with `ρ`
  have hL0 : 0 ≤ L := hL.posSemidef.nonneg
  have := h2.cfc_nnreal NNReal.sqrt
  rw [← CFC.sqrt_eq_cfc, CFC.sqrt_mul_self L hL0] at this
  exact this

/-- D3.7.4. A feasible filter with floor `f > 0` is positive definite. -/
theorem IsFilter.posDef {f a : ℝ} (hf : 0 < f) {L : Matrix m m ℂ} (hL : IsFilter f a L) :
    L.PosDef := by
  obtain ⟨V, hV, x, hx, -, rfl⟩ := hL
  have hD : (diagonal fun i ↦ ((x i ^ (a / 2) : ℝ) : ℂ)).PosDef :=
    posDef_diagonal_iff.2 fun i ↦ by
      exact_mod_cast Real.rpow_pos_of_pos (hf.trans_le (hx i)) _
  have hinj : Function.Injective (Vᴴ).mulVec := fun u v huv ↦ by
    have hV' : V * Vᴴ = 1 := by rwa [mul_eq_one_comm] at hV
    simpa [mulVec_mulVec, hV'] using congrArg (V *ᵥ ·) huv
  simpa using hD.conjTranspose_mul_mul_same hinj

omit [DecidableEq m] in
/-- D3.7.4. `Tr(ρB)` is imaginary for `ρ = ρ*` and `B = -B*`. -/
theorem re_trace_mul_eq_zero {ρ B : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hB : Bᴴ = -B) :
    (ρ * B).trace.re = 0 := by
  have h : star (ρ * B).trace = -(ρ * B).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hB, hρ.eq, Matrix.neg_mul, trace_neg,
      trace_mul_comm]
  have := congrArg Complex.re h
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
  linarith

end D37

section D37chain

/-- Splitting `f (j+n) ⋯ f 0` at index `j`. -/
theorem prodDesc_add {n : Type*} [Fintype n] [DecidableEq n] (f : ℕ → Matrix n n ℂ) (j k : ℕ) :
    prodDesc f (j + 1 + k) = prodDesc (fun i ↦ f (j + 1 + i)) k * f j * prodDesc f j := by
  induction k with
  | zero => simp [prodDesc]
  | succ k ih => rw [← add_assoc, prodDesc, ih, prodDesc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc]

/-- `prodDesc f k` depends only on `f 0, …, f (k-1)`. -/
theorem prodDesc_congr {n : Type*} [Fintype n] [DecidableEq n] {f g : ℕ → Matrix n n ℂ} {k : ℕ}
    (h : ∀ i < k, f i = g i) : prodDesc f k = prodDesc g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prodDesc, prodDesc, h k k.lt_succ_self, ih fun i hi ↦ h i (hi.trans k.lt_succ_self)]

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

/-- D3.7.2. `K = K_{>j} (L_j ⊗ 1) K_{<j}`. -/
theorem filterProd_add (hX : ∀ j, X j ⊆ U)
    (L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ) (j k : ℕ) :
    filterProd hX L (j + 1 + k) = prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i))
      (L (j + 1 + i))) k * Arealaw.extendId (hX j) (L j) * filterProd hX L j := by
  rw [filterProd, filterProd, prodDesc_add]

/-- D3.7.2 at the maximizer of D3.7.1: for anti-Hermitian `B` on `X_j`, with
`K_{>j} = L_{j+k} ⋯ L_{j+1}` and `w = K_{<j} Ω`, `Re ⟨K_{>j} L_j w, K_{>j} (BL_j - L_jB) w⟩ = 0`. -/
theorem step_3_7_2_filter (hX : ∀ j, X j ⊆ U) {f a : ℕ → ℝ}
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (j k : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' (j + 1 + k)) Ω‖ ≤
          ‖toEuclideanLin (filterProd hX L (j + 1 + k)) Ω‖)
    {B : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (hB : Bᴴ = -B) :
    (inner ℂ (toEuclideanLin (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i))
        (L (j + 1 + i))) k * Arealaw.extendId (hX j) (L j)) (toEuclideanLin (filterProd hX L j) Ω))
      (toEuclideanLin (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k *
        Arealaw.extendId (hX j) (B * L j - L j * B)) (toEuclideanLin (filterProd hX L j) Ω))).re
      = 0 := by
  let Φ : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ →ₗ[ℂ]
      Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ :=
    { toFun := Arealaw.extendId (hX j)
      map_add' := Arealaw.extendId_add _
      map_smul' := Arealaw.extendId_smul _ }
  refine step_3_7_2 Φ _ (L j) B _ (Filter.Eventually.of_forall fun t ↦ ?_)
  have hΦ : ∀ M, Φ M = Arealaw.extendId (hX j) M := fun _ ↦ rfl
  beta_reduce
  simp only [hΦ, Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul,
    Matrix.mul_one]
  -- D3.7.2: `L_j(t) = e^{tB} L_j e^{-tB}` is feasible, the other filters are unchanged
  set M := NormedSpace.exp ((t : ℂ) • B) * L j * NormedSpace.exp ((-(t : ℂ)) • B)
  have hfeas : ∀ i, IsFilter (f i) (a i) (Function.update L j M i) := by
    intro i
    rcases eq_or_ne i j with rfl | hi
    · rw [Function.update_self]; exact (hL i).exp_conj hB t
    · rw [Function.update_of_ne hi]; exact hL i
  have h := hmax _ hfeas
  have hpre : filterProd hX (Function.update L j M) j = filterProd hX L j :=
    prodDesc_congr fun i hi ↦ by rw [Function.update_of_ne hi.ne]
  have hpost : prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i))
      (Function.update L j M (j + 1 + i))) k =
      prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k :=
    prodDesc_congr fun i _ ↦ by rw [Function.update_of_ne (by omega)]
  have e : ∀ Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ,
      toEuclideanLin (Q * filterProd hX L j) Ω =
      toEuclideanLin Q (toEuclideanLin (filterProd hX L j) Ω) := fun Q ↦ by
    rw [toLpLin_mul_same]; rfl
  rw [filterProd_add, filterProd_add, hpre, hpost, Function.update_self, e, e] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- D3.7.2. `BL - LB = (B - LBL⁻¹)L` for invertible `L`. -/
theorem sub_mul_inv_mul {n : Type*} [Fintype n] [DecidableEq n] {L : Matrix n n ℂ}
    (hL : IsUnit L.det) (B : Matrix n n ℂ) : B * L - L * B = (B - L * B * L⁻¹) * L := by
  rw [Matrix.sub_mul, Matrix.mul_assoc (L * B), nonsing_inv_mul _ hL, Matrix.mul_one]

/-- D3.7.2 in the paper's form: at the maximizer, with `φ = K Ω` and `K_{>j} = L_{j+k} ⋯ L_{j+1}`,
`Re ⟨φ, K_{>j} (B - L_jBL_j⁻¹) K_{>j}⁻¹ φ⟩ = 0` for anti-Hermitian `B` on `X_j`. -/
theorem step_3_7_2_pairing (hX : ∀ j, X j ⊆ U) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (j k : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' (j + 1 + k)) Ω‖ ≤
          ‖toEuclideanLin (filterProd hX L (j + 1 + k)) Ω‖)
    {B : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (hB : Bᴴ = -B) :
    (inner ℂ (toEuclideanLin (filterProd hX L (j + 1 + k)) Ω)
      (toEuclideanLin (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k *
        Arealaw.extendId (hX j) (B - L j * B * (L j)⁻¹) *
        (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k)⁻¹)
        (toEuclideanLin (filterProd hX L (j + 1 + k)) Ω))).re = 0 := by
  set K := prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k
  have hK : IsUnit K.det :=
    isUnit_det_filterProd (X := fun i ↦ X (j + 1 + i)) (fun i ↦ hX (j + 1 + i))
      (fun i ↦ (hL (j + 1 + i)).isUnit_det (hf _)) k
  have h := step_3_7_2_filter hX hL j k hmax hB
  rw [sub_mul_inv_mul ((hL j).isUnit_det (hf j)), Arealaw.extendId_mul] at h
  have e : ∀ Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ,
      toEuclideanLin (Q * filterProd hX L j) Ω =
      toEuclideanLin Q (toEuclideanLin (filterProd hX L j) Ω) := fun Q ↦ by
    rw [toLpLin_mul_same]; rfl
  have e2 : ∀ P Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ, ∀ v,
      toEuclideanLin (P * Q) v = toEuclideanLin P (toEuclideanLin Q v) := fun P Q v ↦ by
    rw [toLpLin_mul_same]; rfl
  have hM : K * (Arealaw.extendId (hX j) (B - L j * B * (L j)⁻¹) *
      Arealaw.extendId (hX j) (L j)) = K * Arealaw.extendId (hX j) (B - L j * B * (L j)⁻¹) *
      K⁻¹ * (K * Arealaw.extendId (hX j) (L j)) := by
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hK]
  rw [hM, e2 _ (K * _)] at h
  rw [filterProd_add, e]
  exact h

omit [∀ i, Fintype (loc i)] in
/-- `(A ⊗ 1_{T∖S}) ⊗ 1_{U∖T} = A ⊗ 1_{U∖S}`: extension by the identity is transitive. -/
theorem extendId_extendId {S T V : Finset σ} (hST : S ⊆ T) (hTV : T ⊆ V)
    (A : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ) :
    Arealaw.extendId hTV (Arealaw.extendId hST A) = Arealaw.extendId (hST.trans hTV) A := by
  ext w w'
  simp only [Arealaw.extendId, Matrix.of_apply]
  have h3 : ∀ {u u' : Arealaw.Reg loc V},
      Arealaw.restr (S := V \ S) Finset.sdiff_subset u =
        Arealaw.restr (S := V \ S) Finset.sdiff_subset u' ↔
      Arealaw.restr (S := V \ T) Finset.sdiff_subset u =
        Arealaw.restr (S := V \ T) Finset.sdiff_subset u' ∧
      Arealaw.restr (S := T \ S) Finset.sdiff_subset (Arealaw.restr hTV u) =
        Arealaw.restr (S := T \ S) Finset.sdiff_subset (Arealaw.restr hTV u') := by
    intro u u'
    refine ⟨fun h ↦ ⟨funext fun i ↦ congrFun h ⟨i, Finset.sdiff_subset_sdiff le_rfl hST i.2⟩,
      funext fun i ↦ congrFun h ⟨i, Finset.sdiff_subset_sdiff hTV le_rfl i.2⟩⟩,
      fun ⟨h1, h2⟩ ↦ funext fun i ↦ ?_⟩
    by_cases hi : (i : σ) ∈ T
    · exact congrFun h2 ⟨i, Finset.mem_sdiff.2 ⟨hi, (Finset.mem_sdiff.1 i.2).2⟩⟩
    · exact congrFun h1 ⟨i, Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 i.2).1, hi⟩⟩
  split_ifs with h1 h2 h4 h4 h4 <;> first
    | rfl
    | exact absurd (h3.2 ⟨h1, h2⟩) h4
    | exact absurd (h3.1 h4).2 h2
    | exact absurd (h3.1 h4).1 h1

end D37chain

/-! ## D3.9 The optimized vector has small excitation energy -/

section D39

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D3.9.1. If `HΩ = E₀Ω`, `K` is invertible and `φ = c KΩ`, then `KHK⁻¹φ = E₀φ`, so
`⟨φ, (H - E₀)φ⟩ = ⟨φ, (H - KHK⁻¹)φ⟩`. -/
theorem step_3_9_1 {H K : Matrix n n ℂ} {Ω : n → ℂ} {E₀ : ℝ} (hΩ : H *ᵥ Ω = (E₀ : ℂ) • Ω)
    (hK : IsUnit K.det) (c : ℂ) :
    star (c • K *ᵥ Ω) ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ (c • K *ᵥ Ω)) =
      star (c • K *ᵥ Ω) ⬝ᵥ ((H - K * H * K⁻¹) *ᵥ (c • K *ᵥ Ω)) := by
  have h : (K * H * K⁻¹) *ᵥ (c • K *ᵥ Ω) = (E₀ : ℂ) • (c • K *ᵥ Ω) := by
    rw [mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hK, Matrix.mul_one,
      ← mulVec_mulVec, hΩ, mulVec_smul, smul_comm]
  rw [sub_mulVec, sub_mulVec, h, smul_mulVec, one_mulVec]

end D39

section D393

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- D3.9.3 (pairing `(i,k)` with `(k,i)`). For `H_{ki} = conj H_{ik}` and `l > 0`:
`Re ∑_{i,k} (1 - l_i/l_k) H_{ik} = -∑_{i,k} (cosh log (l_i/l_k) - 1) Re H_{ik}`. -/
theorem re_sum_pairing {ι : Type*} [Fintype ι] {H : ι → ι → ℂ}
    (hH : ∀ i k, H k i = star (H i k)) {l : ι → ℝ} (hl : ∀ i, 0 < l i) :
    (∑ i, ∑ k, ((1 - l i / l k : ℝ) : ℂ) * H i k).re =
      -∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) * (H i k).re := by
  have hc : ∀ i k, Real.cosh (Real.log (l i / l k)) = (l i / l k + l k / l i) / 2 := by
    intro i k
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log (div_pos (hl i) (hl k)), inv_div]
  have hsw : ∑ i, ∑ k, l i / l k * (H i k).re = ∑ i, ∑ k, l k / l i * (H i k).re := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hH k i, Complex.star_def, Complex.conj_re]
  simp only [Complex.re_sum, Complex.re_ofReal_mul, hc]
  have e1 : ∑ i, ∑ k, (1 - l i / l k) * (H i k).re =
      ∑ i, ∑ k, (H i k).re - ∑ i, ∑ k, l i / l k * (H i k).re := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  have e2 : ∑ i, ∑ k, ((l i / l k + l k / l i) / 2 - 1) * (H i k).re =
      (∑ i, ∑ k, l i / l k * (H i k).re + ∑ i, ∑ k, l k / l i * (H i k).re) / 2 -
        ∑ i, ∑ k, (H i k).re := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, add_div, add_mul, div_mul_eq_mul_div,
      Finset.sum_add_distrib, Finset.sum_div]
  rw [e1, e2, ← hsw]; ring

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- `X ↦ ⟨Θ_j, X_{jk} Θ_k⟩` is additive. -/
theorem pair_sum (Θ : EuclideanSpace ℂ (α × β)) {κ : Type*} [Fintype κ]
    (X : κ → Matrix (α × β) (α × β) ℂ) (j k : α) :
    pair Θ (∑ x, X x) j k = ∑ x, pair Θ (X x) j k := by
  simp only [pair, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (γ := κ)]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm

/-- D3.9.3. Split term in Schmidt coordinates: for `h = h*` on `X_j ∪ X_j^c` and
`L_j = diag l` (`l > 0`) in the common eigenbasis of `L_j` and `ρ_{φ,X_j}`,
`Re ⟨φ, (h - L_j h L_j⁻¹) φ⟩ = -∑_{i,k} (cosh log (l_i/l_k) - 1) Re H_{ik}`,
`H_{ik} = ⟨φ_i, h_{ik} φ_k⟩ = √(p_i p_k) ∑_α (c_α)_{ik} (d_α)_{ik}`. -/
theorem step_3_9_3 {h : Matrix (α × β) (α × β) ℂ} (hh : h.IsHermitian) {l : α → ℝ}
    (hl : ∀ i, 0 < l i) (Θ : EuclideanSpace ℂ (α × β)) :
    (⟪Θ, toEuclideanLin (h - diagonal (fun x ↦ (l x.1 : ℂ)) * h *
      diagonal (fun x ↦ ((l x.1)⁻¹ : ℂ))) Θ⟫_ℂ).re =
      -∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) * (pair Θ h i k).re := by
  rw [← re_sum_pairing (H := pair Θ h) ?_ hl, ← rowWeight_one Θ, inner_rowWeight, rowWeight_one]
  · congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [pair, Matrix.sub_apply, mul_diagonal, diagonal_mul, Finset.mul_sum, star_one,
      one_mul]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    have := (hl k).ne'
    push_cast
    field_simp
  · intro i k
    simp only [pair, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    rw [← hh.apply (k, b') (i, b)]; ring

/-- D3.9.5. For `h = ∑_α c_α ⊗ d_α` Hermitian, `φ` in Schmidt form with weights `p`, and
`L_j = diag l` with the clipping bound of D3.8 and `0 ≤ a_j ≤ ½`: the split term is at most
`(16/e²) a_j² ∑_α ‖c_α‖ ‖d_α‖` (D3.9.3, D3.9.4, row/column sums as in D3.1.6). -/
theorem step_3_9_5 {Θ : EuclideanSpace ℂ (α × β)} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hΘ : IsSchmidt Θ p) {κ : Type*} [Fintype κ]
    (c : κ → Matrix α α ℂ) (d : κ → Matrix β β ℂ) (hh : (∑ x, c x ⊗ₖ d x).IsHermitian)
    {l : α → ℝ} (hl : ∀ i, 0 < l i) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hclip : ∀ i k, 0 < p i → 0 < p k →
      |Real.log (l i / l k)| ≤ a / 2 * |Real.log (p i / p k)|) :
    |(⟪Θ, toEuclideanLin ((∑ x, c x ⊗ₖ d x) - diagonal (fun x ↦ (l x.1 : ℂ)) *
      (∑ x, c x ⊗ₖ d x) * diagonal (fun x ↦ ((l x.1)⁻¹ : ℂ))) Θ⟫_ℂ).re| ≤
      16 / Real.exp 2 * a ^ 2 * ∑ x, ‖c x‖ * ‖d x‖ := by
  set ω := unitRow Θ p
  set C := 8 / Real.exp 2 * a ^ 2
  have hC : 0 ≤ C := by positivity
  have hcosh : ∀ i k, 0 ≤ Real.cosh (Real.log (l i / l k)) - 1 := fun i k ↦
    sub_nonneg.2 (Real.one_le_cosh _)
  -- D3.9.4 for each pair, trivially when `p_i p_k = 0`
  have hcoef : ∀ i k, (Real.cosh (Real.log (l i / l k)) - 1) * (√(p i) * √(p k)) ≤
      C * (p i + p k) := by
    intro i k
    rcases (hp i).eq_or_lt with hi | hi
    · calc _ = 0 := by rw [← hi]; simp
        _ ≤ _ := mul_nonneg hC (add_nonneg (hp i) (hp k))
    rcases (hp k).eq_or_lt with hk | hk
    · calc _ = 0 := by rw [← hk]; simp
        _ ≤ _ := mul_nonneg hC (add_nonneg (hp i) (hp k))
    rw [mul_comm, ← Real.sqrt_mul hi.le]
    exact step_3_9_4 ha ha2 hi hk (hclip i k hi hk)
  -- the matrix elements `H_{ik} = √(p_i p_k) ∑_α (c_α)_{ik} ⟨g_i, d_α g_k⟩`
  have hpair : ∀ i k, ‖pair Θ (∑ x, c x ⊗ₖ d x) i k‖ ≤
      ∑ x, √(p i) * √(p k) * (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) := by
    intro i k
    rw [pair_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ ↦ le_of_eq ?_)
    rw [pair_kronecker, row_eq_smul_unitRow hp hΘ i, row_eq_smul_unitRow hp hΘ k, map_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring
  -- D3.9.3
  rw [step_3_9_3 hh hl, abs_neg]
  calc _ ≤ ∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) *
        ‖pair Θ (∑ x, c x ⊗ₖ d x) i k‖ :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ by
            rw [abs_mul, abs_of_nonneg (hcosh i k)]
            exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (hcosh i k)))
    _ ≤ ∑ i, ∑ k, ∑ x, C * ((p i + p k) *
        (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖)) := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
      refine (mul_le_mul_of_nonneg_left (hpair i k) (hcosh i k)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc _ = (Real.cosh (Real.log (l i / l k)) - 1) * (√(p i) * √(p k)) *
            (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) := by ring
        _ ≤ C * (p i + p k) * (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) :=
          mul_le_mul_of_nonneg_right (hcoef i k) (by positivity)
        _ = _ := by ring
    _ = ∑ x, C * ∑ i, ∑ k, (p i + p k) *
        (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) := by
      simp only [Finset.mul_sum]
      exact (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm).trans Finset.sum_comm
    -- D3.9.5: row/column sums
    _ ≤ ∑ x, C * (2 * (‖c x‖ * ‖d x‖)) := Finset.sum_le_sum fun x _ ↦
        mul_le_mul_of_nonneg_left (sum_add_mul_unitRow_le hp hsum hΘ (c x) (d x)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; simp only [C]; ring

end D393

/-! ## D3.11 First norm comparison -/

section D311

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.11.2. For `L_j = L_j*`, `N_j = ‖L_j K_{<j} Ω‖` and an overlap
`s ≤ |⟨Ω, φ_j⟩|`, `φ_j = L_j K_{<j} Ω / N_j`: `s N_j ≤ |⟨L_j Ω, K_{<j} Ω⟩| ≤ ‖L_j Ω‖ ‖K_{<j} Ω‖`. -/
theorem step_3_11_2 {L : Matrix m m ℂ} (hL : L.IsHermitian) (Ω ψ : EuclideanSpace ℂ m) {s : ℝ}
    (hs : s ≤ ‖inner ℂ Ω (((‖toEuclideanLin L ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin L ψ)‖) :
    s * ‖toEuclideanLin L ψ‖ ≤ ‖toEuclideanLin L Ω‖ * ‖ψ‖ := by
  rcases (norm_nonneg (toEuclideanLin L ψ)).lt_or_eq with hN | hN
  · rw [inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hN, ← isSymmetric_toEuclideanLin_iff.2 hL] at hs
    calc s * ‖toEuclideanLin L ψ‖
        ≤ ‖toEuclideanLin L ψ‖⁻¹ * ‖inner ℂ (toEuclideanLin L Ω) ψ‖ * ‖toEuclideanLin L ψ‖ := by
          gcongr
      _ = ‖inner ℂ (toEuclideanLin L Ω) ψ‖ := by field_simp
      _ ≤ _ := norm_inner_le_norm _ _
  · rw [← hN, mul_zero]; positivity

/-- D3.11.3. Schatten Hölder with exponents `1/(1-a)`, `1/a`: for `ρ ≥ 0` and `B ≥ 0` with
`Tr B^{1/a} = 1` (`B = L_j²`, `Tr L_j^{2/a} = 1`), `Tr(ρ B) ≤ (Tr ρ^{1/(1-a)})^{1-a}`. -/
theorem step_3_11_3 {ρ B : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hB : B.PosSemidef) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1) :
    (ρ * B).trace.re ≤ (∑ i, hρ.1.eigenvalues i ^ (1 / (1 - a))) ^ (1 - a) := by
  have := hρ.re_trace_mul_le hB 
    (Real.holderConjugate_one_div (a := 1 - a) (b := a) (by linarith) ha0 (by ring))
  rwa [hBn, Real.one_rpow, mul_one, one_div_one_div, RCLike.re_to_complex] at this


/-- `Tr ρ^{1/(1-a)} = ∑_{p_j > 0} p_j e^{-u log p_j}` at `u = -a/(1-a)`
(D3.11.4: `1 - u = 1/(1-a)`). -/
theorem sum_rpow_eq_sum_exp {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ j, 0 ≤ p j) {a : ℝ}
    (ha1 : a < 1) :
    ∑ j, p j ^ (1 / (1 - a)) = ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < p j),
      p j * Real.exp (-(-a / (1 - a)) * Real.log (p j)) := by
  have h1 : 0 < 1 - a := by linarith
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs with hj
  · have hne : 1 + a / (1 - a) ≠ 0 := by
      rw [show 1 + a / (1 - a) = 1 / (1 - a) by field_simp; ring]; positivity
    rw [show -(-a / (1 - a)) * Real.log (p j) = Real.log (p j) * (a / (1 - a)) by ring,
      ← Real.rpow_def_of_pos hj, ← Real.rpow_one_add' (hp j) hne]
    congr 1; field_simp; ring
  · rw [le_antisymm (not_lt.1 hj) (hp j), Real.zero_rpow (by positivity)]

/-- D3.11.3 on a region. For a unit vector `Ω` on `U`, `X ⊆ U` and `L = L*` on `X` with
`Tr (L²)^{1/a} = 1`: `‖L Ω‖² ≤ (Tr ρ_{Ω,X}^{1/(1-a)})^{1-a}`. -/
theorem step_3_11_3_region {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {X U : Finset σ} (hX : X ⊆ U) (Ω : Arealaw.Reg loc U → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) {L : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ}
    (hL : L.IsHermitian) (hB : (L * L).PosSemidef) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1) :
    (star (Arealaw.extendId hX L *ᵥ Ω) ⬝ᵥ (Arealaw.extendId hX L *ᵥ Ω)).re ≤
      (∑ j, ((OpenAI.pureState Ω hΩ).toSubState.restrict hX).psd.isHermitian.eigenvalues j ^
        (1 / (1 - a))) ^ (1 - a) := by
  have hρ := ((OpenAI.pureState Ω hΩ).toSubState.restrict hX).psd
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Arealaw.extendId_conjTranspose, hL.eq,
    ← Arealaw.extendId_mul, Arealaw.dotProduct_extendId_mulVec]
  exact step_3_11_3 hρ hB ha0 ha1 hBn


/-- D3.11.3–D3.11.4 on a region. With Lemma 3.1 at `u = -a/(1-a)` for the cut `X | U ∖ X`
(hypothesis `hM`, admissible by D3.10(iii)) and `0 < a ≤ ½`:
`log ‖L Ω‖² ≤ -a S(X) + 1024 e ϑ 𝓑 a²`. -/
theorem step_3_11_4_region {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {X U : Finset σ} (hX : X ⊆ U) (Ω : Arealaw.Reg loc U → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) {L : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ}
    (hL : L.IsHermitian) (hB : (L * L).PosSemidef) {a ϑ 𝓑 : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    (hϑ : 0 ≤ ϑ) (h𝓑 : 0 ≤ 𝓑) (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1)
    (hpos : 0 < (star (Arealaw.extendId hX L *ᵥ Ω) ⬝ᵥ (Arealaw.extendId hX L *ᵥ Ω)).re)
    (hM : let ρ := (OpenAI.pureState Ω hΩ).toSubState.restrict hX
      let p := ρ.psd.isHermitian.eigenvalues
      Real.log (∑ j ∈ Finset.univ.filter (fun j ↦ 0 < p j),
          p j * Real.exp (-(-a / (1 - a)) * Real.log (p j))) ≤
        -a / (1 - a) * ρ.entropy + 512 * Real.exp 1 * ϑ * 𝓑 * (-a / (1 - a)) ^ 2) :
    Real.log (star (Arealaw.extendId hX L *ᵥ Ω) ⬝ᵥ (Arealaw.extendId hX L *ᵥ Ω)).re ≤
      -a * ((OpenAI.pureState Ω hΩ).toSubState.restrict hX).entropy +
        1024 * Real.exp 1 * ϑ * 𝓑 * a ^ 2 := by
  have ha1 : a < 1 := by linarith
  set ρ := (OpenAI.pureState Ω hΩ).toSubState.restrict hX
  -- D3.11.3
  have h3 := step_3_11_3_region hX Ω hΩ hL hB ha0 ha1 hBn
  rw [sum_rpow_eq_sum_exp (fun j ↦ ρ.psd.eigenvalues_nonneg j) ha1] at h3
  set T := ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < ρ.psd.isHermitian.eigenvalues j),
    ρ.psd.isHermitian.eigenvalues j *
      Real.exp (-(-a / (1 - a)) * Real.log (ρ.psd.isHermitian.eigenvalues j))
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j hj ↦
    mul_nonneg (Finset.mem_filter.1 hj).2.le (Real.exp_pos _).le
  have hT : 0 < T := by
    rcases hT0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow (by linarith)] at h3; linarith
  -- D3.11.4
  calc _ ≤ Real.log (T ^ (1 - a)) := Real.log_le_log hpos h3
    _ = (1 - a) * Real.log T := Real.log_rpow hT _
    _ ≤ _ := step_3_11_4 ha0 ha2 hϑ h𝓑 hM

end D311

/-! ## D3.12 Zero-floor limit and the trial-norm bound -/

section D312

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D3.12.4. Moving the unitaries `U_j = M_j^{iy}` to the left: with `V_j = U_j ⋯ U_1`,
`(U_m M_m) ⋯ (U_1 M_1) = (U_m ⋯ U_1) (V_{m-1}^* M_m V_{m-1}) ⋯ (V_0^* M_1 V_0)`. -/
theorem step_3_12_4 (U M : ℕ → Matrix n n ℂ) (hU : ∀ j, U j * (U j)ᴴ = 1) (k : ℕ) :
    prodDesc (fun j ↦ U j * M j) k =
      prodDesc U k * prodDesc (fun j ↦ (prodDesc U j)ᴴ * M j * prodDesc U j) k := by
  have hV : ∀ j, prodDesc U j * (prodDesc U j)ᴴ = 1 := by
    intro j
    induction j with
    | zero => simp [prodDesc]
    | succ j ih =>
      simp only [prodDesc, conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (prodDesc U j), ih, Matrix.one_mul, hU]
  induction k with
  | zero => simp [prodDesc]
  | succ k ih =>
    simp only [prodDesc]
    rw [ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (prodDesc U k) (prodDesc U k)ᴴ, hV, Matrix.one_mul]

end D312

/-! ## D3.13 Schmidt-averaged upper bound on `-2 log N` -/

section D313

/-- D3.13. Schmidt weights `p_i > 0`, `∑ p_i = 1`, `S(X) = ∑ p_i (-log p_i)`. From the per-`i`
bounds `-2 log N ≤ -log p_i + ∑_j a_j S_{w_i}(T_j)` (D3.13.1, from D3.12) and concavity
`∑_i p_i S_{w_i}(T_j) ≤ S(T_j)` (D3.13.2): `-2 log N ≤ S(X) + ∑_j a_j S(T_j)`. -/
theorem step_3_13 {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    {J : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ j ∈ J, 0 ≤ a j) {Sw : ι → ℕ → ℝ} {ST : ℕ → ℝ}
    {SX N : ℝ} (hSX : SX = ∑ i, p i * -Real.log (p i))
    (h1 : ∀ i, -2 * Real.log N ≤ -Real.log (p i) + ∑ j ∈ J, a j * Sw i j)
    (h2 : ∀ j ∈ J, ∑ i, p i * Sw i j ≤ ST j) :
    -2 * Real.log N ≤ SX + ∑ j ∈ J, a j * ST j := by
  -- D3.13.1, averaged with weights `p_i`
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (h1 i) (hp i).le
  rw [← Finset.sum_mul, hp1, one_mul] at h
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at h
  rw [Finset.sum_comm, ← hSX] at h
  -- D3.13.2
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum fun j hj ↦ ?_))
  calc ∑ i, p i * (a j * Sw i j) = a j * ∑ i, p i * Sw i j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ a j * ST j := mul_le_mul_of_nonneg_left (h2 j hj) (ha j hj)

end D313

end AreaLaw
