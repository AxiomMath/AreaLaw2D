import AreaLawRefactored.S03_InitialBox.Filters

/-!
# §3.2, D3.12.1–D3.12.2 of digest/03-initial-box.md: zero-floor limit and Schmidt pinning
-/

namespace AreaLaw

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker

section ZeroFloor

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

/-- `L ↦ ‖L_{k-1} ⋯ L_0 Ω‖` is continuous. -/
theorem continuous_norm_filterProd (hX : ∀ j, X j ⊆ U) (k : ℕ)
    (Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)) :
    Continuous fun L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ ↦
      ‖toEuclideanLin (filterProd hX L k) Ω‖ := by
  refine continuous_norm.comp ?_
  simp only [toLpLin_apply]
  exact (PiLp.continuous_toLp 2 _).comp ((continuous_filterProd hX k).matrix_mulVec
    continuous_const)

/-- D3.12.1. The floor-raised filter `x ↦ (1 - δ) x + δ/dim` is feasible at floor `δ/dim`. -/
theorem isFilter_floorRaise {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m] {a δ : ℝ}
    (hδ : δ ≤ 1) {V : Matrix m m ℂ} (hV : Vᴴ * V = 1) {x : m → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hs : ∑ i, x i = 1) :
    IsFilter (δ / Fintype.card m) a
      (V * diagonal (fun i ↦ ((((1 - δ) * x i + δ / Fintype.card m) ^ (a / 2) : ℝ) : ℂ)) * Vᴴ) :=
  have hd : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  ⟨V, hV, fun i ↦ (1 - δ) * x i + δ / Fintype.card m,
    fun i ↦ by nlinarith [hx i], by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp; ring, rfl⟩

/-- D3.12.1. (a) The bound `B` for filters of positive floor passes to zero floor. -/
theorem step_3_12_1 (hX : ∀ j, X j ⊆ U) {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hne : ∀ j, Nonempty (Arealaw.Reg loc (X j))) (Ω : EuclideanSpace ℂ (Arealaw.Reg loc U))
    (m : ℕ) {B : ℝ}
    (hB : ∀ f : ℕ → ℝ, (∀ j, 0 < f j) →
      (∀ j, (Fintype.card (Arealaw.Reg loc (X j)) : ℝ) * f j < 1) →
      ∀ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
        (∀ j, IsFilter (f j) (a j) (L j)) → ‖toEuclideanLin (filterProd hX L m) Ω‖ ≤ B)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter 0 (a j) (L j)) :
    ‖toEuclideanLin (filterProd hX L m) Ω‖ ≤ B := by
  choose V hV y hy hs hLeq using hL
  have hc : ∀ j, (0 : ℝ) < Fintype.card (Arealaw.Reg loc (X j)) := fun j ↦ by
    have := hne j; exact_mod_cast Fintype.card_pos
  -- D3.12.1: `R δ` is `L` with floor raised by `δ`; `R 0 = L`
  set R : ℝ → (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ := fun δ j ↦
    V j * diagonal (fun i ↦ ((((1 - δ) * y j i + δ / Fintype.card (Arealaw.Reg loc (X j))) ^
      (a j / 2) : ℝ) : ℂ)) * (V j)ᴴ with hR
  have hR0 : R 0 = L := funext fun j ↦ by simp [hR, hLeq j]
  have hRc : Continuous R := continuous_pi fun j ↦
    (continuous_const.matrix_mul (continuous_id.matrix_diagonal.comp (continuous_pi fun i ↦
      Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by linarith [ha j])).comp
        (by fun_prop))))).matrix_mul continuous_const
  have hlim : Filter.Tendsto (fun δ ↦ ‖toEuclideanLin (filterProd hX (R δ) m) Ω‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖toEuclideanLin (filterProd hX L m) Ω‖) := by
    rw [← hR0]
    exact (((continuous_norm_filterProd hX m Ω).comp hRc).tendsto 0).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  exact hB (fun j ↦ δ / Fintype.card (Arealaw.Reg loc (X j))) (fun j ↦ div_pos hδ.1 (hc j))
    (fun j ↦ by rw [mul_div_cancel₀ _ (hc j).ne']; exact hδ.2) (R δ) fun j ↦
    isFilter_floorRaise hδ.2.le (hV j) (fun i ↦ by simpa using hy j i) (hs j)

end ZeroFloor

/-! ## D3.12.2 Schmidt pinning -/

section Pin

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal `|i⟩⟨i|`. -/
private noncomputable abbrev pinDiag (i : n) : Matrix n n ℂ :=
  diagonal fun k ↦ if k = i then 1 else 0

/-- D3.12.2. The projection `|u_i⟩⟨u_i| = W |i⟩⟨i| Wᴴ` onto the `i`-th column of `W`. -/
noncomputable def pinProj (W : Matrix n n ℂ) (i : n) : Matrix n n ℂ := W * pinDiag i * Wᴴ

private theorem pinDiag_mul_self (i : n) : pinDiag i * pinDiag i = pinDiag i := by
  rw [diagonal_mul_diagonal]; congr 1; funext k; split_ifs <;> simp

theorem pinProj_conjTranspose (W : Matrix n n ℂ) (i : n) : (pinProj W i)ᴴ = pinProj W i := by
  have : (pinDiag i)ᴴ = pinDiag i := by
    rw [diagonal_conjTranspose]; congr 1; funext k; split_ifs <;> simp_all
  rw [pinProj, conjTranspose_mul, conjTranspose_mul, this, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem pinProj_mul_self {W : Matrix n n ℂ} (hW : Wᴴ * W = 1) (i : n) :
    pinProj W i * pinProj W i = pinProj W i := by
  calc _ = W * (pinDiag i * (Wᴴ * W) * pinDiag i) * Wᴴ := by simp only [pinProj, Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_one, pinDiag_mul_self, pinProj]

theorem sum_pinProj {W : Matrix n n ℂ} (hW' : W * Wᴴ = 1) : ∑ i, pinProj W i = 1 := by
  have : ∑ i : n, pinDiag i = 1 := by
    ext a b; simp [Matrix.sum_apply, diagonal_apply, one_apply]
  simp only [pinProj, ← Finset.sum_mul, ← Finset.mul_sum, this, Matrix.mul_one, hW']

/-- `Tr (W diag(p) Wᴴ · |u_i⟩⟨u_i|) = p_i`. -/
theorem trace_mul_pinProj {W : Matrix n n ℂ} (hW : Wᴴ * W = 1) (p : n → ℝ) (i : n) :
    (W * diagonal (fun k ↦ (p k : ℂ)) * Wᴴ * pinProj W i).trace = p i := by
  calc _ = (W * (diagonal (fun k ↦ (p k : ℂ)) * (Wᴴ * W) * pinDiag i) * Wᴴ).trace := by
        simp only [pinProj, Matrix.mul_assoc]
    _ = p i := by
      rw [hW, Matrix.mul_one, trace_mul_cycle, hW, Matrix.one_mul, diagonal_mul_diagonal,
        trace_diagonal]
      simp

/-- `⟨Aψ, Bψ⟩ = ⟨ψ, AᴴB ψ⟩`. -/
theorem inner_toEuclideanLin_toEuclideanLin (A B : Matrix n n ℂ) (ψ : EuclideanSpace ℂ n) :
    ⟪toEuclideanLin A ψ, toEuclideanLin B ψ⟫_ℂ = ⟪ψ, toEuclideanLin (Aᴴ * B) ψ⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, star_mulVec,
    ← mulVec_mulVec]
  rw [dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]

/-- Hermitian idempotents do not increase norms. -/
theorem norm_toEuclideanLin_le_of_proj {Q : Matrix n n ℂ} (hQh : Qᴴ = Q) (hQ : Q * Q = Q)
    (v : EuclideanSpace ℂ n) : ‖toEuclideanLin Q v‖ ≤ ‖v‖ := by
  have h : ‖toEuclideanLin Q v‖ ^ 2 ≤ ‖v‖ * ‖toEuclideanLin Q v‖ := by
    rw [@norm_sq_eq_re_inner ℂ, inner_toEuclideanLin_toEuclideanLin, hQh, hQ]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg (toEuclideanLin Q v)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Pin

section Schmidt

open Arealaw

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U Y : Finset σ}

/-- `⟨ψ, (K ⊗ 1) ψ⟩ = Tr (ρ_{ψ,Y} K)`. -/
theorem inner_extendId (hY : Y ⊆ U) (ψ : EuclideanSpace ℂ (Reg loc U))
    (K : Matrix (Reg loc Y) (Reg loc Y) ℂ) :
    ⟪ψ, toEuclideanLin (extendId hY K) ψ⟫_ℂ =
      (ptrace hY (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) * K).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, WithLp.ofLp_toLp, dotProduct_comm,
    dotProduct_extendId_mulVec]

/-- `‖(K ⊗ 1) ψ‖² = Re Tr (ρ_{ψ,Y} Kᴴ K)`. -/
theorem norm_sq_extendId (hY : Y ⊆ U) (ψ : EuclideanSpace ℂ (Reg loc U))
    (K : Matrix (Reg loc Y) (Reg loc Y) ℂ) :
    ‖toEuclideanLin (extendId hY K) ψ‖ ^ 2 =
      (ptrace hY (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) * (Kᴴ * K)).trace.re := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toEuclideanLin_toEuclideanLin, ← extendId_conjTranspose,
    ← extendId_mul, inner_extendId]
  rfl

/-- `(M ⊗ N) ⊗ 1 = (M ⊗ 1)(N ⊗ 1)` for disjoint `Y, T ⊆ U`. -/
theorem extendId_kronUnion {T : Finset σ} (hY : Y ⊆ U) (hT : T ⊆ U) (hd : Disjoint Y T)
    (P : Matrix (Reg loc Y) (Reg loc Y) ℂ) (M : Matrix (Reg loc T) (Reg loc T) ℂ) :
    extendId (Finset.union_subset hY hT) (kronUnion hd P M) = extendId hY P * extendId hT M := by
  ext w w'
  rw [extendId_mul_extendId_apply hY hT hd]
  simp only [extendId, kronUnion, of_apply, unionEquiv_apply]
  have : restr (S := U \ (Y ∪ T)) Finset.sdiff_subset w =
      restr (S := U \ (Y ∪ T)) Finset.sdiff_subset w' ↔
        ∀ i : U, i.1 ∉ Y → i.1 ∉ T → w i = w' i := by
    refine ⟨fun h i hY hT ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩
    · exact congrFun h ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, by simp [hY, hT]⟩⟩
    · have := (Finset.mem_sdiff.1 i.2).2
      exact h ⟨i.1, Finset.sdiff_subset i.2⟩ (fun h' ↦ this (Finset.mem_union_left _ h'))
        (fun h' ↦ this (Finset.mem_union_right _ h'))
  simp only [this]
  rfl

/-- D3.12.2. `‖(|u_i⟩⟨u_i| ⊗ 1) Ω‖² = p_i` when `ρ_{Ω,Y} = W diag(p) Wᴴ`. -/
theorem step_3_12_2_norm (hY : Y ⊆ U) {Ω : EuclideanSpace ℂ (Reg loc U)}
    {W : Matrix (Reg loc Y) (Reg loc Y) ℂ} (hW : Wᴴ * W = 1) {p : Reg loc Y → ℝ}
    (hρ : ptrace hY (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) =
      W * diagonal (fun k ↦ (p k : ℂ)) * Wᴴ) (i : Reg loc Y) :
    ‖toEuclideanLin (extendId hY (pinProj W i)) Ω‖ ^ 2 = p i := by
  rw [norm_sq_extendId, pinProj_conjTranspose, pinProj_mul_self hW, hρ, trace_mul_pinProj hW]
  rfl

/-- D3.13.2. On `T ⊆ U` disjoint from `Y`, `ρ_{Ω,T} = ∑ᵢ ρ_{PᵢΩ,T}`. -/
theorem step_3_13_2_marginal {T : Finset σ} (hY : Y ⊆ U) (hT : T ⊆ U) (hYT : Disjoint Y T)
    {W : Matrix (Reg loc Y) (Reg loc Y) ℂ} (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1)
    (Ω : EuclideanSpace ℂ (Reg loc U)) :
    ∑ i, ptrace hT
        (vecMulVec (WithLp.ofLp (toEuclideanLin (extendId hY (pinProj W i)) Ω))
          (star (WithLp.ofLp (toEuclideanLin (extendId hY (pinProj W i)) Ω)))) =
      ptrace hT (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) := by
  refine ext_iff_trace_mul_right.mpr fun A ↦ ?_
  -- D3.13.2: test against `A` on `T`; `A ⊗ 1` commutes with the projectors
  have hterm : ∀ i, ⟪toEuclideanLin (extendId hY (pinProj W i)) Ω,
      toEuclideanLin (extendId hT A) (toEuclideanLin (extendId hY (pinProj W i)) Ω)⟫_ℂ =
      ⟪Ω, toEuclideanLin (extendId hT A * extendId hY (pinProj W i)) Ω⟫_ℂ := fun i ↦ by
    rw [show toEuclideanLin (extendId hT A) (toEuclideanLin (extendId hY (pinProj W i)) Ω) =
        toEuclideanLin (extendId hT A * extendId hY (pinProj W i)) Ω by
      simp only [toLpLin_mul_same, LinearMap.comp_apply], inner_toEuclideanLin_toEuclideanLin,
      ← extendId_conjTranspose, pinProj_conjTranspose, ← Matrix.mul_assoc,
      (commute_extendId_extendId hY hT hYT (pinProj W i) A).eq, Matrix.mul_assoc,
      ← extendId_mul, pinProj_mul_self hW]
  have hsum : ∑ i, extendId hY (pinProj W i) = 1 := by
    have h : ∀ s : Finset (Reg loc Y), extendId hY (∑ i ∈ s, pinProj W i) =
        ∑ i ∈ s, extendId hY (pinProj W i) := fun s ↦ by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, extendId_add, ih]
    rw [← h, sum_pinProj hW', extendId_one]
  rw [Finset.sum_mul, trace_sum]
  simp only [← inner_extendId, hterm]
  symm
  calc _ = ⟪Ω, toEuclideanLin (extendId hT A * ∑ i, extendId hY (pinProj W i)) Ω⟫_ℂ := by
        rw [hsum, Matrix.mul_one]
    _ = _ := by rw [Finset.mul_sum, map_sum, LinearMap.sum_apply, inner_sum]

/-- D3.12.2. `|u_i⟩⟨u_i| ⊗ M` is a zero-floor filter:
`Tr L^{2/a} = Tr |u_i⟩⟨u_i| · Tr M^{2/a} = 1`. -/
theorem isFilter_kronUnion_pinProj {A B : Finset σ} (hd : Disjoint A B) {a : ℝ} (ha : 0 < a)
    {W : Matrix (Reg loc A) (Reg loc A) ℂ} (hW : Wᴴ * W = 1) (i : Reg loc A)
    {M : Matrix (Reg loc B) (Reg loc B) ℂ} (hM : IsFilter 0 a M) :
    IsFilter 0 a (kronUnion hd (pinProj W i) M) := by
  obtain ⟨V, hV, x, hx, hs, rfl⟩ := hM
  set e := unionEquiv hd
  set d : Reg loc A → ℝ := fun k ↦ if k = i then 1 else 0
  refine ⟨(W ⊗ₖ V).submatrix e e, ?_, fun w ↦ d (e w).1 * x (e w).2,
    fun w ↦ mul_nonneg (by simp only [d]; split_ifs <;> norm_num) (hx _), ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
      ← mul_kronecker_mul, hW, hV, one_kronecker_one, submatrix_one_equiv]
  · rw [e.sum_comp fun p : Reg loc A × Reg loc B ↦ d p.1 * x p.2, Fintype.sum_prod_type]
    simp [d, hs]
  · -- the middle factor is the transported diagonal
    have hdiag : (diagonal fun k ↦ ((if k = i then 1 else 0 : ℝ) : ℂ)) = pinDiag i := by
      congr 1; funext k; split_ifs <;> simp
    have : ∀ w, (((d (e w).1 * x (e w).2) ^ (a / 2) : ℝ) : ℂ) =
        (if (e w).1 = i then 1 else 0 : ℂ) * (((x (e w).2 ^ (a / 2) : ℝ)) : ℂ) := fun w ↦ by
      simp only [d]; split_ifs
      · simp
      · simp [Real.zero_rpow (by positivity : a / 2 ≠ 0)]
    simp only [this]
    have hk : (diagonal fun w ↦ (if (e w).1 = i then 1 else 0 : ℂ) * (((x (e w).2 ^ (a / 2) : ℝ)) :
        ℂ)) = ((diagonal fun k : Reg loc A ↦ (if k = i then 1 else 0 : ℂ)) ⊗ₖ
          diagonal fun k : Reg loc B ↦ (((x k ^ (a / 2) : ℝ)) : ℂ)).submatrix e e := by
      rw [diagonal_kronecker_diagonal, submatrix_diagonal_equiv]; rfl
    rw [hk, kronUnion_eq_submatrix, pinProj, conjTranspose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

/-- An idempotent commuting with each factor is absorbed by the product:
`Q (Q B_{k-1}) ⋯ (Q B_0) = Q B_{k-1} ⋯ B_0`. -/
theorem mul_prodDesc_mul_of_commute {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q * Q = Q) {B : ℕ → Matrix n n ℂ} (h : ∀ j, Commute Q (B j)) (k : ℕ) :
    Q * prodDesc (fun j ↦ Q * B j) k = Q * prodDesc B k := by
  induction k with
  | zero => simp [prodDesc]
  | succ k ih =>
    simp only [prodDesc]
    calc Q * (Q * B k * prodDesc (fun j ↦ Q * B j) k)
        = Q * Q * B k * prodDesc (fun j ↦ Q * B j) k := by simp only [Matrix.mul_assoc]
      _ = B k * (Q * prodDesc (fun j ↦ Q * B j) k) := by
        rw [hQ, (h k).eq, Matrix.mul_assoc]
      _ = Q * (B k * prodDesc B k) := by rw [ih, ← Matrix.mul_assoc, ← (h k).eq, Matrix.mul_assoc]

/-- D3.12.2. Pinning: with `L_j = |u_i⟩⟨u_i| ⊗ M_j` (zero-floor filters on `Y ∪ T_j`),
`‖M_{m-1} ⋯ M_0 (|u_i⟩⟨u_i| ⊗ 1) Ω‖ ≤ ‖L_{m-1} ⋯ L_0 Ω‖`. -/
theorem step_3_12_2 {T : ℕ → Finset σ} (hY : Y ⊆ U) (hTU : ∀ j, T j ⊆ U)
    (hYT : ∀ j, Disjoint Y (T j)) {a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    {W : Matrix (Reg loc Y) (Reg loc Y) ℂ} (hW : Wᴴ * W = 1) (i : Reg loc Y)
    {M : (j : ℕ) → Matrix (Reg loc (T j)) (Reg loc (T j)) ℂ} (hM : ∀ j, IsFilter 0 (a j) (M j))
    (Ω : EuclideanSpace ℂ (Reg loc U)) (m : ℕ) :
    ∃ L : (j : ℕ) → Matrix (Reg loc (Y ∪ T j)) (Reg loc (Y ∪ T j)) ℂ,
      (∀ j, IsFilter 0 (a j) (L j)) ∧
      ‖toEuclideanLin (filterProd hTU M m) (toEuclideanLin (extendId hY (pinProj W i)) Ω)‖ ≤
        ‖toEuclideanLin (filterProd (fun j ↦ Finset.union_subset hY (hTU j)) L m) Ω‖ := by
  refine ⟨fun j ↦ kronUnion (hYT j) (pinProj W i) (M j),
    fun j ↦ isFilter_kronUnion_pinProj (hYT j) (ha j) hW i (hM j), ?_⟩
  set Q := extendId hY (pinProj W i) with hQdef
  have hQ : Q * Q = Q := by rw [hQdef, ← extendId_mul, pinProj_mul_self hW]
  have hQh : Qᴴ = Q := by rw [hQdef, ← extendId_conjTranspose, pinProj_conjTranspose]
  have hc : ∀ j, Commute Q (extendId (hTU j) (M j)) := fun j ↦
    commute_extendId_extendId hY (hTU j) (hYT j) _ _
  have hcomp : ∀ (A B : Matrix (Reg loc U) (Reg loc U) ℂ) v,
      toEuclideanLin A (toEuclideanLin B v) = toEuclideanLin (A * B) v := fun A B v ↦ by
    simp only [toLpLin_mul_same, LinearMap.comp_apply]
  -- D3.12.2: `L_{m-1} ⋯ L_0 = ∏ (Q ⊗ 1)(M_j ⊗ 1)`
  have hL : filterProd (fun j ↦ Finset.union_subset hY (hTU j))
      (fun j ↦ kronUnion (hYT j) (pinProj W i) (M j)) m =
        prodDesc (fun j ↦ Q * extendId (hTU j) (M j)) m := by
    simp only [filterProd, extendId_kronUnion hY (hTU _) (hYT _)]
    rfl
  have hcomm : ∀ k, Commute Q (filterProd hTU M k) := fun k ↦ by
    induction k with
    | zero => exact Commute.one_right _
    | succ k ih => exact (hc k).mul_right ih
  -- `K Q Ω = Q K Ω = Q L Ω`, and `Q` is a projection
  calc _ = ‖toEuclideanLin Q
        (toEuclideanLin (prodDesc (fun j ↦ Q * extendId (hTU j) (M j)) m) Ω)‖ := by
        rw [hcomp, hcomp, mul_prodDesc_mul_of_commute hQ hc, ← (hcomm m).eq]; rfl
    _ ≤ _ := hL ▸ norm_toEuclideanLin_le_of_proj hQh hQ _

end Schmidt

end AreaLaw
