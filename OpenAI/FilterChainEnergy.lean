import OpenAI.CutTransport
import OpenAI.FilterChain
import OpenAI.FilterEnergy

/-!
# Conjugation of one term by a nested product of filters

Let `K = L_{m-1} ⋯ L_0` be a nested product of filters on subregions `D_0 ⊆ ⋯ ⊆ D_{m-1}` of a
region `U`, each commuting with the marginal of a unit vector `φ` on its region and clipped
relative to it.  For an interaction term `X` supported on `S`, conjugation by `K` changes the
expectation of `X` only through the one filter whose region splits `S`, if any: the outer
filters, whose regions contain `S`, drop out by the descending trace argument, and the inner
filters, whose regions are disjoint from `S`, commute with `X`.  The remaining conjugation is
bounded by the common-basis estimate `OpenAI.abs_re_inner_sub_conj_le_of_common_basis_sharp`,
applied across the cut `D_j | U \ D_j` to a product decomposition of `X` with at most
`(dim (S ∩ D_j))²` terms.

## Main statements

* `OpenAI.IsSupportedOn.hasProductDecomposition_inter_submatrix_glueEquiv`: an operator
  supported on `S` is, across the cut `B | U \ B`, a sum of at most `(dim (S ∩ B))²` products.
* `OpenAI.liftProd_mul_mul_liftProdInv_of_disjoint`: inner filters commute with the term.
* `OpenAI.abs_re_inner_sub_conj_extendId_le_sharp`: the single-split conjugation estimate.
* `OpenAI.abs_re_inner_sub_chain_conj_le_sharp`: the estimate for one term of the Hamiltonian.

## Implementation notes

Ported from QICLean (LionSR/QICLean), `QICLean/Entropy/FilterChainEnergy.lean` at commit
`32a5a1a8` (Apache 2.0), written there from the proof of Lemma 3.2 of [OAI265]; the sharp
refinement follows the polynomial-PEPS manuscript of the same authors (24 September 2026).
This file is the first part of that file; the excitation bounds are in
`OpenAI.FilterExcitation`.  Changes: the namespace `Entropy` is `OpenAI`, and the region model
is that of `OpenAI.chainList`.  QICLean's `localLift B` is `Arealaw.extendId hB`, so
`abs_re_inner_sub_conj_localLift_le(_sharp)` are `abs_re_inner_sub_conj_extendId_le(_sharp)`;
the regional state `regionState B φ` is `Arealaw.ptrace hB (vecMulVec φ (star φ))`; the inside
configurations `InnerConfig n B S` are `Reg loc (S ∩ B)` and `supportDim n S` is
`Fintype.card (Reg loc S)`.  QICLean's cut coordinates `cutVector B`, `cutOperator B` are the
relabelling along `Arealaw.glueEquiv hB`, with `inner_cutOperator` and `cutOperator_mul`
replaced by `OpenAI.inner_toEuclideanLin_submatrix_equiv` and Mathlib's
`Matrix.submatrix_mul_equiv`.  QICLean's `hasProductDecomposition_inner` is
`OpenAI.IsSupportedOn.hasProductDecomposition_inter_submatrix_glueEquiv`, proved here by a block
decomposition along `S ∩ B ⊆ S`.  The witness configuration `σ₀` is no longer an argument; the
coarse bounds, which compare `dim (S ∩ B)` with `dim S`, obtain a configuration of `S` from the
unit vector instead (QICLean's `hn : ∀ v ∈ S, 1 ≤ n v`).  `splitIndices` is stated through
`Finset.Nonempty`, the form of `OpenAI.crossingTerms`; `OpenAI.mem_splitIndices` is QICLean's.
`inv_conj_diagonal` takes an arbitrary nowhere-zero diagonal over `RCLike 𝕜`.

The conjugation estimates are over `ℂ`, as is the common-basis estimate they transport; the
list algebra, the reindexing lemmas and the product decomposition are over `RCLike 𝕜`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.2, proof of Lemma 3.2.
-/

namespace OpenAI

open Arealaw Matrix
open scoped InnerProductSpace ComplexOrder Kronecker Matrix.Norms.L2Operator

section Decomposition

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U B S T : Finset σ}

/-- Block decomposition of an operator on `S` along `T ⊆ S`. -/
theorem submatrix_glueEquiv_eq_sum_single_kronecker (hT : T ⊆ S)
    (Y : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    Y.submatrix (glueEquiv hT) (glueEquiv hT) =
      ∑ x : Reg loc T, ∑ y : Reg loc T,
        single x y (1 : 𝕜) ⊗ₖ Y.submatrix (fun z ↦ glue x z) (fun z ↦ glue y z) := by
  ext ⟨u, z⟩ ⟨u', z'⟩
  simp [Matrix.sum_apply, single_apply, kroneckerMap_apply, ite_and]

/-- An operator on `S` is a sum of the products `(E_{xy} ⊗ 1) (1 ⊗ Y_{xy})` along `T ⊆ S`. -/
theorem eq_sum_extendId_single_mul_extendId (hT : T ⊆ S)
    (Y : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    Y = ∑ x : Reg loc T, ∑ y : Reg loc T, extendId hT (single x y (1 : 𝕜)) *
      extendId Finset.sdiff_subset (Y.submatrix (fun z ↦ glue x z) (fun z ↦ glue y z)) := by
  have key : Y.submatrix (glueEquiv hT) (glueEquiv hT) =
      (∑ x : Reg loc T, ∑ y : Reg loc T, extendId hT (single x y (1 : 𝕜)) *
        extendId Finset.sdiff_subset (Y.submatrix (fun z ↦ glue x z) (fun z ↦ glue y z))).submatrix
        (glueEquiv hT) (glueEquiv hT) := by
    rw [submatrix_glueEquiv_eq_sum_single_kronecker, submatrix_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [submatrix_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← submatrix_mul_equiv (e₂ := glueEquiv hT), extendId_submatrix_glueEquiv,
      extendId_sdiff_submatrix_glueEquiv, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have h := congrArg (fun M ↦ M.submatrix (glueEquiv hT).symm (glueEquiv hT).symm) key
  simpa [submatrix_submatrix] using h

/-- **Product decomposition at the inside support.** An operator `X` supported on `S` is,
across the cut `B | U \ B`, a sum of at most `(dim (S ∩ B))²` products `c ⊗ d` with
`‖c‖ ‖d‖ ≤ ‖X‖`. -/
theorem IsSupportedOn.hasProductDecomposition_inter_submatrix_glueEquiv (hB : B ⊆ U)
    (hSU : S ⊆ U) {X : Matrix (Reg loc U) (Reg loc U) 𝕜} (hX : IsSupportedOn hSU X) :
    HasProductDecomposition (X.submatrix (glueEquiv hB) (glueEquiv hB)) ‖X‖
      (Fintype.card (Reg loc (S ∩ B)) ^ 2) := by
  obtain ⟨Y, rfl⟩ := hX
  by_cases hU : IsEmpty (Reg loc U)
  · refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, ?_, fun a ↦ a.elim0⟩
    ext p
    exact (hU.false (glueEquiv hB p)).elim
  obtain ⟨w⟩ := not_isEmpty_iff.1 hU
  have : Nonempty (Reg loc (U \ S)) := ⟨restr Finset.sdiff_subset w⟩
  have hAS : S ∩ B ⊆ S := Finset.inter_subset_left
  have hAB : S ∩ B ⊆ B := Finset.inter_subset_right
  have hCU : S \ (S ∩ B) ⊆ U \ B := fun v hv ↦ by
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hv ⊢
    exact ⟨hSU hv.1, hv.2 hv.1⟩
  let c : Reg loc (S ∩ B) × Reg loc (S ∩ B) → Matrix (Reg loc B) (Reg loc B) 𝕜 :=
    fun p ↦ extendId hAB (single p.1 p.2 1)
  let d : Reg loc (S ∩ B) × Reg loc (S ∩ B) → Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) 𝕜 :=
    fun p ↦ extendId hCU (Y.submatrix (fun z ↦ glue p.1 z) (fun z ↦ glue p.2 z))
  let e := Fintype.equivFin (Reg loc (S ∩ B) × Reg loc (S ∩ B))
  refine ⟨Fintype.card (Reg loc (S ∩ B) × Reg loc (S ∩ B)), fun a ↦ c (e.symm a),
    fun a ↦ d (e.symm a), by rw [Fintype.card_prod, sq], ?_, fun a ↦ ?_⟩
  · rw [Equiv.sum_comp e.symm (fun p ↦ c p ⊗ₖ d p), Fintype.sum_prod_type]
    conv_lhs => rw [eq_sum_extendId_single_mul_extendId hAS Y]
    simp only [extendId_sum, submatrix_sum, extendId_mul, extendId_extendId]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← extendId_extendId hAB hB, ← extendId_extendId hCU Finset.sdiff_subset,
      ← submatrix_mul_equiv (e₂ := glueEquiv hB), extendId_submatrix_glueEquiv,
      extendId_sdiff_submatrix_glueEquiv, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  · calc ‖c (e.symm a)‖ * ‖d (e.symm a)‖ ≤ 1 * ‖Y‖ := by
          refine mul_le_mul ((l2_opNorm_extendId_le _ _).trans (by simp))
            ((l2_opNorm_extendId_le _ _).trans
              (l2_opNorm_submatrix_le _ (glue_right_injective _) (glue_right_injective _)))
            (norm_nonneg _) zero_le_one
      _ = ‖extendId hSU Y‖ := by rw [one_mul, l2_opNorm_extendId hSU Y]

end Decomposition

/-! ## Cut coordinates -/

section Reindex

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- Relabelling the basis of a vector preserves its norm. -/
theorem norm_toLp_ofLp_comp_equiv (e : n ≃ m) (φ : EuclideanSpace 𝕜 m) :
    ‖WithLp.toLp 2 (WithLp.ofLp φ ∘ e)‖ = ‖φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp e fun i ↦ ‖WithLp.ofLp φ i‖ ^ 2

/-- Expectations can be computed after relabelling the basis. -/
theorem inner_toEuclideanLin_submatrix_equiv (e : n ≃ m) (Y : Matrix m m 𝕜)
    (φ : EuclideanSpace 𝕜 m) :
    ⟪WithLp.toLp 2 (WithLp.ofLp φ ∘ e),
        toEuclideanLin (Y.submatrix e e) (WithLp.toLp 2 (WithLp.ofLp φ ∘ e))⟫_𝕜 =
      ⟪φ, toEuclideanLin Y φ⟫_𝕜 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, submatrix_mulVec_equiv,
    Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, dotProduct, Function.comp_apply,
    Pi.star_apply]
  exact Equiv.sum_comp e fun i ↦ (Y *ᵥ WithLp.ofLp φ) i * star (WithLp.ofLp φ i)

/-- The inverse of `W diag(d) W*` with `W` unitary and `d` nowhere zero. -/
theorem inv_conj_diagonal {W : Matrix m m 𝕜} (hW : Wᴴ * W = 1) {d : m → 𝕜}
    (hd : ∀ i, d i ≠ 0) :
    (W * diagonal d * Wᴴ)⁻¹ = W * diagonal (fun i ↦ (d i)⁻¹) * Wᴴ := by
  refine inv_eq_right_inv ?_
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hdd : diagonal d * diagonal (fun i ↦ (d i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i ↦ mul_inv_cancel₀ (hd i))
  calc W * diagonal d * Wᴴ * (W * diagonal (fun i ↦ (d i)⁻¹) * Wᴴ)
      = W * (diagonal d * (Wᴴ * W) * diagonal (fun i ↦ (d i)⁻¹)) * Wᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hW, Matrix.mul_one, hdd, Matrix.mul_one, hW']

end Reindex

/-! ## Conjugation by one filter -/

section Single

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U B S : Finset σ}

omit [∀ i, DecidableEq (loc i)] in
/-- A subregion has at most as many configurations as a region that carries one. -/
theorem card_reg_le_of_subset [Nonempty (Reg loc S)] {T : Finset σ} (hTS : T ⊆ S) :
    Fintype.card (Reg loc T) ≤ Fintype.card (Reg loc S) := by
  obtain ⟨w⟩ := ‹Nonempty (Reg loc S)›
  exact Fintype.card_le_of_injective _ (glue_left_injective hTS (restr Finset.sdiff_subset w))

omit [DecidableEq σ] [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
/-- A region carries a configuration as soon as an ambient region carries a nonzero vector. -/
theorem nonempty_reg_of_ne_zero {𝕜 : Type*} [RCLike 𝕜] (hSU : S ⊆ U)
    {φ : EuclideanSpace 𝕜 (Reg loc U)} (hφ : φ ≠ 0) : Nonempty (Reg loc S) := by
  obtain ⟨w, -⟩ : ∃ w, WithLp.ofLp φ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (WithLp.ofLp_injective 2 (funext h))
  exact ⟨restr hSU w⟩

/-- **Conjugation by the splitting filter.** Let `φ` be a unit vector on `U`, `B ⊆ U` a
subregion, and let `L = W diag(l) W*` and `ρ_{φ,B} = W diag(q) W*` with `W` unitary, `l > 0`
and clipped eigenvalue ratios `|log l_i - log l_k| ≤ (a/2) |log q_i - log q_k|`, `a ≤ 1`.  For
a Hermitian `X` supported on `S` with `‖X‖ ≤ c₀`,
`|Re (⟨φ, X φ⟩ - ⟨φ, L X L⁻¹ φ⟩)| ≤ a² d_{S∩B}² c₀`, `d_{S∩B} = dim (S ∩ B)`. -/
theorem abs_re_inner_sub_conj_extendId_le_sharp (hB : B ⊆ U)
    {L W : Matrix (Reg loc B) (Reg loc B) ℂ} {l q : Reg loc B → ℝ}
    {φ : EuclideanSpace ℂ (Reg loc U)} (hφ : ‖φ‖ = 1) (hW : Wᴴ * W = 1)
    (hl : ∀ i, 0 < l i) (hL : L = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ)
    (hρ : ptrace hB (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
      W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ)
    (hSU : S ⊆ U) {X : Matrix (Reg loc U) (Reg loc U) ℂ} (hX : IsSupportedOn hSU X)
    (hXh : X.IsHermitian) {c₀ : ℝ} (hXn : ‖X‖ ≤ c₀) {a : ℝ} (ha : a ≤ 1)
    (hclip : ∀ i k, 0 < q i → 0 < q k →
      |Real.log (l i) - Real.log (l k)| ≤ a / 2 * |Real.log (q i) - Real.log (q k)|) :
    |(⟪φ, toEuclideanLin X φ⟫_ℂ -
        ⟪φ, toEuclideanLin (extendId hB L * X * extendId hB L⁻¹) φ⟫_ℂ).re| ≤
      a ^ 2 * (Fintype.card (Reg loc (S ∩ B)) ^ 2 * c₀) := by
  set e := glueEquiv (loc := loc) hB
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hLinv : L⁻¹ = W * diagonal (fun i ↦ ((l i)⁻¹ : ℂ)) * Wᴴ := by
    rw [hL]
    exact inv_conj_diagonal hW fun i ↦ Complex.ofReal_ne_zero.mpr (hl i).ne'
  obtain ⟨M, c, d, hM, hdec, hcd⟩ := hX.hasProductDecomposition_inter_submatrix_glueEquiv hB hSU
  rw [← inner_toEuclideanLin_submatrix_equiv e X φ,
    ← inner_toEuclideanLin_submatrix_equiv e (extendId hB L * X * extendId hB L⁻¹) φ,
    ← submatrix_mul_equiv (e₂ := e), ← submatrix_mul_equiv (e₂ := e),
    extendId_submatrix_glueEquiv, extendId_submatrix_glueEquiv, hLinv, hL]
  have hρ' : traceRight (vecMulVec (WithLp.ofLp (WithLp.toLp 2 (WithLp.ofLp φ ∘ e)))
      (star (WithLp.ofLp (WithLp.toLp 2 (WithLp.ofLp φ ∘ e))))) =
      W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ :=
    (ptrace_eq_traceRight_submatrix_glueEquiv hB _).symm.trans hρ
  refine (abs_re_inner_sub_conj_le_of_common_basis_sharp
    (by rw [norm_toLp_ofLp_comp_equiv, hφ]) hW hW' hl hρ' (hXh.submatrix _) c d hdec ha
    hclip).trans ?_
  gcongr
  calc ∑ α', ‖c α'‖ * ‖d α'‖ ≤ ∑ _α' : Fin M, ‖X‖ := Finset.sum_le_sum fun α' _ ↦ hcd α'
    _ = M * ‖X‖ := by simp
    _ ≤ Fintype.card (Reg loc (S ∩ B)) ^ 2 * c₀ := by
      gcongr
      exact_mod_cast hM

/-- The coarse conjugation bound of [OAI265]: under the hypotheses of
`OpenAI.abs_re_inner_sub_conj_extendId_le_sharp` with `a ≤ 1/2`, the defect is at most
`4 a² d_S² c₀`, `d_S = dim S`. -/
theorem abs_re_inner_sub_conj_extendId_le (hB : B ⊆ U)
    {L W : Matrix (Reg loc B) (Reg loc B) ℂ} {l q : Reg loc B → ℝ}
    {φ : EuclideanSpace ℂ (Reg loc U)} (hφ : ‖φ‖ = 1) (hW : Wᴴ * W = 1)
    (hl : ∀ i, 0 < l i) (hL : L = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ)
    (hρ : ptrace hB (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
      W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ)
    (hSU : S ⊆ U) {X : Matrix (Reg loc U) (Reg loc U) ℂ} (hX : IsSupportedOn hSU X)
    (hXh : X.IsHermitian) {c₀ : ℝ} (hXn : ‖X‖ ≤ c₀) {a : ℝ} (ha : a ≤ 1 / 2)
    (hclip : ∀ i k, 0 < q i → 0 < q k →
      |Real.log (l i) - Real.log (l k)| ≤ a / 2 * |Real.log (q i) - Real.log (q k)|) :
    |(⟪φ, toEuclideanLin X φ⟫_ℂ -
        ⟪φ, toEuclideanLin (extendId hB L * X * extendId hB L⁻¹) φ⟫_ℂ).re| ≤
      4 * a ^ 2 * (Fintype.card (Reg loc S) ^ 2 * c₀) := by
  have hne : Nonempty (Reg loc S) :=
    nonempty_reg_of_ne_zero hSU (φ := φ) (by rintro rfl; simp at hφ)
  have hc₀ : 0 ≤ c₀ := (norm_nonneg X).trans hXn
  have hdim : (Fintype.card (Reg loc (S ∩ B)) : ℝ) ^ 2 ≤ Fintype.card (Reg loc S) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left (card_reg_le_of_subset Finset.inter_subset_left) 2
  calc _ ≤ a ^ 2 * (Fintype.card (Reg loc (S ∩ B)) ^ 2 * c₀) :=
        abs_re_inner_sub_conj_extendId_le_sharp hB hφ hW hl hL hρ hSU hX hXh hXn
          (by linarith) hclip
    _ ≤ a ^ 2 * (Fintype.card (Reg loc S) ^ 2 * c₀) := by gcongr
    _ ≤ 4 * a ^ 2 * (Fintype.card (Reg loc S) ^ 2 * c₀) := by
      nlinarith [mul_nonneg (sq_nonneg a) (mul_nonneg (sq_nonneg (Fintype.card (Reg loc S) : ℝ))
        hc₀)]

end Single

/-! ## Splitting a nested product -/

/-- In a strictly increasing list, the elements failing an upward closed predicate come
first. -/
theorem List.filter_not_append_filter_of_upward {α : Type*} [Preorder α] (Q : α → Prop)
    [DecidablePred Q] (hQ : ∀ i j, i ≤ j → Q i → Q j) :
    ∀ {l : List α}, l.Pairwise (· < ·) →
      l.filter (fun i ↦ decide (¬ Q i)) ++ l.filter (fun i ↦ decide (Q i)) = l
  | [], _ => rfl
  | a :: t, hp => by
    rw [List.pairwise_cons] at hp
    by_cases ha : Q a
    · have h1 : t.filter (fun i ↦ decide (¬ Q i)) = [] :=
        List.filter_eq_nil_iff.mpr fun i hi ↦ by simpa using hQ a i (hp.1 i hi).le ha
      have h2 : t.filter (fun i ↦ decide (Q i)) = t :=
        List.filter_eq_self.mpr fun i hi ↦ by simpa using hQ a i (hp.1 i hi).le ha
      simpa [ha, h2] using fun i hi ↦ hQ a i (hp.1 i hi).le ha
    · simp only [List.filter_cons, ha, decide_false, decide_true, not_false_eq_true]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      exact congrArg (a :: ·) (List.filter_not_append_filter_of_upward Q hQ hp.2)

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U : Finset σ} {m : ℕ}

theorem liftProdInv_append (l₁ l₂ : List (RegionFilter 𝕜 loc U)) :
    liftProdInv (l₁ ++ l₂) = liftProdInv l₂ * liftProdInv l₁ := by
  simp [liftProdInv]

section ChainList

omit [RCLike 𝕜] [DecidableEq σ] [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

variable (D : ℕ → Finset σ) (hDU : ∀ i : Fin m, D i ⊆ U)
  (K : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) 𝕜)

/-- The members of a nested product are the filters at the indices satisfying the
predicate. -/
theorem exists_eq_of_mem_chainList {P : Fin m → Prop} [DecidablePred P]
    {p : RegionFilter 𝕜 loc U} (hp : p ∈ chainList D hDU K P) :
    ∃ i, P i ∧ p = ⟨⟨D i, hDU i⟩, K i⟩ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  simp only [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hi
  exact ⟨i, hi.2, rfl⟩

/-- The nested product splits into the filters satisfying an upward closed predicate, applied
last, and the others. -/
theorem chainList_eq_append_of_upward (Q : Fin m → Prop) [DecidablePred Q]
    (hQ : ∀ i j, i ≤ j → Q i → Q j) :
    chainList D hDU K (fun _ ↦ True) =
      chainList D hDU K Q ++ chainList D hDU K (fun i ↦ ¬ Q i) := by
  unfold chainList
  have htrue : (List.finRange m).filter (fun _ ↦ decide True) = List.finRange m := by simp
  rw [htrue, ← List.map_append, ← List.reverse_append,
    List.filter_not_append_filter_of_upward Q hQ (List.pairwise_lt_finRange m)]

/-- The nested product splits at an index, as a list of filters. -/
theorem chainList_eq_split (j : Fin m) :
    chainList D hDU K (fun _ ↦ True) =
      chainList D hDU K (j < ·) ++
        (⟨⟨D j, hDU j⟩, K j⟩ : RegionFilter 𝕜 loc U) :: chainList D hDU K (· < j) := by
  have hsplit := List.eq_filter_lt_append_cons_filter_gt (List.pairwise_lt_finRange m)
    (List.mem_finRange j)
  have htrue : (List.finRange m).filter (fun _ ↦ decide True) = List.finRange m := by simp
  unfold chainList
  rw [htrue]
  conv_lhs => rw [hsplit]
  simp

end ChainList

/-- Filters on regions disjoint from the support of `X` commute with `X`. -/
theorem liftProd_mul_mul_liftProdInv_of_disjoint {S : Finset σ} {hSU : S ⊆ U}
    {X : Matrix (Reg loc U) (Reg loc U) 𝕜} (hX : IsSupportedOn hSU X) :
    ∀ {l : List (RegionFilter 𝕜 loc U)}, (∀ p ∈ l, IsUnit p.2.det ∧ Disjoint p.1.1 S) →
      liftProd l * X * liftProdInv l = X
  | [], _ => by simp
  | p :: l, h => by
    rw [liftProd_cons, liftProdInv_cons,
      show extendId p.1.2 p.2 * liftProd l * X * (liftProdInv l * extendId p.1.2 p.2⁻¹) =
        extendId p.1.2 p.2 * (liftProd l * X * liftProdInv l) * extendId p.1.2 p.2⁻¹ by
          simp only [Matrix.mul_assoc],
      liftProd_mul_mul_liftProdInv_of_disjoint hX fun q hq ↦ h q (List.mem_cons_of_mem p hq)]
    have hc := (isSupportedOn_extendId p.1.2 p.2).commute hX (h p List.mem_cons_self).2
    rw [hc.eq, Matrix.mul_assoc, extendId_mul_extendId_inv _ (h p List.mem_cons_self).1,
      Matrix.mul_one]

/-! ## One term of the Hamiltonian -/

section Term

/-- The indices `j` whose region `D j` splits `S`: it meets `S` without containing it. -/
def splitIndices (S : Finset σ) (D : ℕ → Finset σ) (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j : Fin m ↦ (S ∩ D j).Nonempty ∧ (S \ D j).Nonempty

theorem mem_splitIndices {S : Finset σ} {D : ℕ → Finset σ} {j : Fin m} :
    j ∈ splitIndices S D m ↔ (∃ v ∈ S, v ∈ D j) ∧ ∃ v ∈ S, v ∉ D j := by
  simp [splitIndices, Finset.Nonempty]

/-- **One term of the Hamiltonian.** Let `K_j` be filters on nested subregions `D_j ⊆ U`, each
invertible, commuting with the marginal of the unit vector `φ` on its region, and clipped
relative to it, with weights `a_j ≤ 1`.  Let `X` be Hermitian, supported on `S`, with
`‖X‖ ≤ c₀`, and suppose at most one region splits `S`.  Then conjugation by the nested product
changes the real part of the expectation of `X` by at most `∑_{j splits S} a_j² d_{S∩D_j}² c₀`,
`d_{S∩D_j} = dim (S ∩ D_j)`. -/
theorem abs_re_inner_sub_chain_conj_le_sharp (D : ℕ → Finset σ) (hDU : ∀ i : Fin m, D i ⊆ U)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (K : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) ℂ)
    (hunit : ∀ i, IsUnit (K i).det) {φ : EuclideanSpace ℂ (Reg loc U)} (hφ : ‖φ‖ = 1)
    (a : Fin m → ℝ) (ha : ∀ j, a j ≤ 1)
    (hcl : ∀ j, K j * ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) * K j ∧
      ∃ (W : Matrix (Reg loc (D j)) (Reg loc (D j)) ℂ) (l q : Reg loc (D j) → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
          W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a j / 2 * |Real.log (q i) - Real.log (q k)|)
    {S : Finset σ} (hSU : S ⊆ U) {X : Matrix (Reg loc U) (Reg loc U) ℂ}
    (hX : IsSupportedOn hSU X) (hXh : X.IsHermitian) {c₀ : ℝ} (hXn : ‖X‖ ≤ c₀)
    (hsingle : ∀ j ∈ splitIndices S D m, ∀ j' ∈ splitIndices S D m, j = j') :
    |(⟪φ, toEuclideanLin X φ⟫_ℂ - ⟪φ, toEuclideanLin
        (liftProd (chainList D hDU K fun _ ↦ True) * X *
          liftProdInv (chainList D hDU K fun _ ↦ True)) φ⟫_ℂ).re| ≤
      ∑ j ∈ splitIndices S D m, a j ^ 2 * (Fintype.card (Reg loc (S ∩ D j)) ^ 2 * c₀) := by
  have hc₀ : 0 ≤ c₀ := (norm_nonneg X).trans hXn
  have hnn : ∀ j ∈ splitIndices S D m,
      0 ≤ a j ^ 2 * (Fintype.card (Reg loc (S ∩ D j)) ^ 2 * c₀) :=
    fun j _ ↦ by positivity
  by_cases hex : ∃ j, j ∈ splitIndices S D m
  · obtain ⟨j, hj⟩ := hex
    obtain ⟨⟨w₁, hw₁S, hw₁D⟩, ⟨w₂, hw₂S, hw₂D⟩⟩ := mem_splitIndices.mp hj
    -- the inner filters avoid `S`, the outer ones contain it
    have hin : ∀ p ∈ chainList D hDU K (· < j), IsUnit p.2.det ∧ Disjoint p.1.1 S := by
      intro p hp
      obtain ⟨i, hij, rfl⟩ := exists_eq_of_mem_chainList D hDU K hp
      refine ⟨hunit i, Finset.disjoint_left.mpr fun v hvD hvS ↦ ?_⟩
      have hi : i ∈ splitIndices S D m :=
        mem_splitIndices.mpr ⟨⟨v, hvS, hvD⟩, ⟨w₂, hw₂S, fun h ↦ hw₂D (hD i j hij.le h)⟩⟩
      exact lt_irrefl j (hsingle i hi j hj ▸ hij)
    have hout : ∀ p ∈ chainList D hDU K (j < ·), D j ⊆ p.1.1 ∧ S ⊆ p.1.1 := by
      intro p hp
      obtain ⟨i, hji, rfl⟩ := exists_eq_of_mem_chainList D hDU K hp
      refine ⟨hD j i hji.le, fun v hvS ↦ ?_⟩
      by_contra hvD
      have hi : i ∈ splitIndices S D m :=
        mem_splitIndices.mpr ⟨⟨w₁, hw₁S, hD j i hji.le hw₁D⟩, ⟨v, hvS, hvD⟩⟩
      exact lt_irrefl j (hsingle i hi j hj ▸ hji)
    have hchain : IsDescendingChain φ (chainList D hDU K (j < ·)) :=
      isDescendingChain_map D hDU hD K hunit (pairwise_gt_reverse_filter_finRange _)
        fun i _ ↦ (hcl i).1
    set Lj := extendId (hDU j) (K j)
    set Lj' := extendId (hDU j) (K j)⁻¹
    have hconj : liftProd (chainList D hDU K fun _ ↦ True) * X *
        liftProdInv (chainList D hDU K fun _ ↦ True) =
        liftProd (chainList D hDU K (j < ·)) * (Lj * X * Lj') *
          liftProdInv (chainList D hDU K (j < ·)) := by
      rw [chainList_eq_split D hDU K j, liftProd_append, liftProd_cons, liftProdInv_append,
        liftProdInv_cons]
      conv_rhs => rw [← liftProd_mul_mul_liftProdInv_of_disjoint hX hin]
      simp only [Lj, Lj', Matrix.mul_assoc]
    have hsupp : ∀ p ∈ chainList D hDU K (j < ·), IsSupportedOn p.1.2 (Lj * X * Lj') := by
      intro p hp
      obtain ⟨h1, h2⟩ := hout p hp
      exact (((isSupportedOn_extendId (hDU j) (K j)).mono h1 p.1.2).mul
        (hX.mono h2 p.1.2)).mul ((isSupportedOn_extendId (hDU j) _).mono h1 p.1.2)
    rw [hconj, inner_liftProd_conj hchain hsupp]
    obtain ⟨-, W, l, q, hW, hl, hKj, hρ, hclip⟩ := hcl j
    exact (abs_re_inner_sub_conj_extendId_le_sharp (hDU j) hφ hW hl hKj hρ hSU hX hXh hXn
      (ha j) hclip).trans (Finset.single_le_sum hnn hj)
  · -- no region splits `S`: the filters avoid `S` or contain it
    push Not at hex
    have hQ : ∀ i j : Fin m, i ≤ j → S ⊆ D i → S ⊆ D j := fun i j hij h ↦ h.trans (hD i j hij)
    have hin : ∀ p ∈ chainList D hDU K (fun i ↦ ¬ S ⊆ D i),
        IsUnit p.2.det ∧ Disjoint p.1.1 S := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_chainList D hDU K hp
      refine ⟨hunit i, Finset.disjoint_left.mpr fun v hvD hvS ↦ ?_⟩
      obtain ⟨w, hwS, hwD⟩ := Finset.not_subset.mp hi
      exact hex i (mem_splitIndices.mpr ⟨⟨v, hvS, hvD⟩, ⟨w, hwS, hwD⟩⟩)
    have hchain : IsDescendingChain φ (chainList D hDU K fun i ↦ S ⊆ D i) :=
      isDescendingChain_map D hDU hD K hunit (pairwise_gt_reverse_filter_finRange _)
        fun i _ ↦ (hcl i).1
    have hsupp : ∀ p ∈ chainList D hDU K (fun i ↦ S ⊆ D i), IsSupportedOn p.1.2 X := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_chainList D hDU K hp
      exact hX.mono hi (hDU i)
    have hconj : liftProd (chainList D hDU K fun _ ↦ True) * X *
        liftProdInv (chainList D hDU K fun _ ↦ True) =
        liftProd (chainList D hDU K fun i ↦ S ⊆ D i) * X *
          liftProdInv (chainList D hDU K fun i ↦ S ⊆ D i) := by
      rw [chainList_eq_append_of_upward D hDU K (fun i ↦ S ⊆ D i) hQ, liftProd_append,
        liftProdInv_append]
      conv_rhs => rw [← liftProd_mul_mul_liftProdInv_of_disjoint hX hin]
      simp only [Matrix.mul_assoc]
    rw [hconj, inner_liftProd_conj hchain hsupp, sub_self, Complex.zero_re, abs_zero]
    exact Finset.sum_nonneg hnn

/-- The coarse bound of [OAI265] for one term: under the hypotheses of
`OpenAI.abs_re_inner_sub_chain_conj_le_sharp` with weights `a_j ≤ 1/2`, the defect is at most
`∑_{j splits S} 4 a_j² d_S² c₀`, `d_S = dim S`. -/
theorem abs_re_inner_sub_chain_conj_le (D : ℕ → Finset σ) (hDU : ∀ i : Fin m, D i ⊆ U)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (K : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) ℂ)
    (hunit : ∀ i, IsUnit (K i).det) {φ : EuclideanSpace ℂ (Reg loc U)} (hφ : ‖φ‖ = 1)
    (a : Fin m → ℝ) (ha : ∀ j, a j ≤ 1 / 2)
    (hcl : ∀ j, K j * ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) * K j ∧
      ∃ (W : Matrix (Reg loc (D j)) (Reg loc (D j)) ℂ) (l q : Reg loc (D j) → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
          W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a j / 2 * |Real.log (q i) - Real.log (q k)|)
    {S : Finset σ} (hSU : S ⊆ U) {X : Matrix (Reg loc U) (Reg loc U) ℂ}
    (hX : IsSupportedOn hSU X) (hXh : X.IsHermitian) {c₀ : ℝ} (hXn : ‖X‖ ≤ c₀)
    (hsingle : ∀ j ∈ splitIndices S D m, ∀ j' ∈ splitIndices S D m, j = j') :
    |(⟪φ, toEuclideanLin X φ⟫_ℂ - ⟪φ, toEuclideanLin
        (liftProd (chainList D hDU K fun _ ↦ True) * X *
          liftProdInv (chainList D hDU K fun _ ↦ True)) φ⟫_ℂ).re| ≤
      ∑ j ∈ splitIndices S D m, 4 * a j ^ 2 * (Fintype.card (Reg loc S) ^ 2 * c₀) := by
  refine (abs_re_inner_sub_chain_conj_le_sharp D hDU hD K hunit hφ a
    (fun j ↦ by linarith [ha j]) hcl hSU hX hXh hXn hsingle).trans ?_
  have hne : Nonempty (Reg loc S) :=
    nonempty_reg_of_ne_zero hSU (φ := φ) (by rintro rfl; simp at hφ)
  have hc₀ : 0 ≤ c₀ := (norm_nonneg X).trans hXn
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hdim : (Fintype.card (Reg loc (S ∩ D j)) : ℝ) ^ 2 ≤ Fintype.card (Reg loc S) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left (card_reg_le_of_subset Finset.inter_subset_left) 2
  calc a j ^ 2 * (Fintype.card (Reg loc (S ∩ D j)) ^ 2 * c₀)
      ≤ a j ^ 2 * (Fintype.card (Reg loc S) ^ 2 * c₀) := by gcongr
    _ ≤ 4 * a j ^ 2 * (Fintype.card (Reg loc S) ^ 2 * c₀) := by
      nlinarith [mul_nonneg (sq_nonneg (a j))
        (mul_nonneg (sq_nonneg (Fintype.card (Reg loc S) : ℝ)) hc₀)]

end Term

end OpenAI
