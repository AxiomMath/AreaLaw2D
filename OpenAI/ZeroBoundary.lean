import OpenAI.Basic
import OpenAI.Bridges
import OpenAI.RegionEntropy

/-!
# A cut with no crossing edge

Lemma 2.2 of [OAI265] and the degenerate cases of its §2.2.  If no nearest-neighbour edge of
`Λ` crosses the cut `A | Λ \ A`, every admissible support lies on one side of it, so the
Hamiltonian is the sum of a term supported in `A` and one supported in `Λ \ A`.  The two
commute, and a gapped ground vector, being unique up to scalars, is then a product across the
cut: its reduced state on `A` is a rank-one projection and `S_Ω(A) = 0`.  Range zero is the
special case of on-site terms; one-dimensional sites and the empty domain carry no entropy
for any normalized state.

## Main statements

* `extendId_extendId`: extending by the identity in two steps is extending in one.
* `commute_extendId_extendId`: operators extended from disjoint regions commute.
* `entropy_eq_zero_of_mul_self_eq`: an idempotent state has zero entropy.
* `exists_eq_vecMulVec_of_forall_commute`: a nonzero matrix on which every operator commuting
  with a Hermitian `K` acts by a scalar has rank one.
* `regionEntropy_pureState_eq_zero_of_split`: the entropy of `A` vanishes when every nonzero
  term of the interaction lies in `A` or in `Λ \ A`.
* `subset_or_subset_sdiff_of_edgeBoundary_eq_empty`: without crossing edges every admissible
  support lies on one side of the cut.
* `regionEntropy_eq_zero_of_edgeBoundary_eq_empty`: **Lemma 2.2**.
* `regionEntropy_eq_zero_of_range_zero`, `regionEntropy_eq_zero_of_q_eq_one`,
  `regionEntropy_eq_zero_of_eq_empty`: the degenerate cases `R = 0`, `q = 1` and `Λ = ∅`.

## Implementation notes

The paper factors `H` as a tensor sum of component Hamiltonians.  Here the factorization is
replaced by commutation: every operator `K` on `A` commuting with `H_A = ∑_{X ⊆ A} h_X`
extends to an operator commuting with `H`, hence maps `Ω` to a multiple of itself.  Applied to
`H_A` and then to the projection onto one column of the coefficient matrix of `Ω`, this forces
that matrix to have rank one.  The empty support belongs to both sides of the cut, so `H` is
split as `H_A` plus the sum of the terms not contained in `A`, rather than as `H_A + H_{Λ \ A}`.

The vanishing for `q = 1` and `Λ = ∅` is stated for normalized states: a subnormalized state
`ρ` on a one-dimensional space has entropy `negMulLog (re (trace ρ))`, which is positive for
trace strictly between `0` and `1`.
-/

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder
open Matrix SimpleGraph

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Product operators -/

section PiProd

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → Type*} [∀ i, Fintype (d i)]
  [∀ i, DecidableEq (d i)] {R : Type*} [CommSemiring R]

omit [∀ i, DecidableEq (d i)] in
/-- Product operators multiply factorwise. -/
theorem piProd_mul (m m' : ∀ i, Matrix (d i) (d i) R) :
    piProd m * piProd m' = piProd fun i => m i * m' i := by
  ext x y
  simp only [piProd, mul_apply, of_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- Two product operators commute when at every site one of their factors is the identity. -/
theorem commute_piProd {m m' : ∀ i, Matrix (d i) (d i) R} (h : ∀ i, m i = 1 ∨ m' i = 1) :
    Commute (piProd m) (piProd m') := by
  rw [Commute, SemiconjBy, piProd_mul, piProd_mul]
  congr 1
  funext i
  rcases h i with h | h <;> simp [h]

end PiProd

/-! ## Extension by the identity -/

section Extend

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T U : Finset σ}

omit [∀ i, Fintype (loc i)] in
/-- Extension by the identity commutes with finite sums. -/
theorem extendId_sum {κ : Type*} (h : S ⊆ T) (s : Finset κ)
    (f : κ → Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (∑ k ∈ s, f k) = ∑ k ∈ s, extendId h (f k) :=
  map_sum (AddMonoidHom.mk' (extendId h) (extendId_add h)) f s

omit [∀ i, Fintype (loc i)] in
/-- **Nested extension**: extending from `S` to `T` and then from `T` to `U` is extending from
`S` to `U`. -/
theorem extendId_extendId (hST : S ⊆ T) (hTU : T ⊆ U) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId hTU (extendId hST A) = extendId (hST.trans hTU) A := by
  ext w w'
  have hiff : (restr (S := U \ T) Finset.sdiff_subset w = restr Finset.sdiff_subset w' ∧
      restr (S := T \ S) Finset.sdiff_subset (restr hTU w) =
        restr Finset.sdiff_subset (restr hTU w')) ↔
      restr (S := U \ S) Finset.sdiff_subset w = restr Finset.sdiff_subset w' := by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩ i ⟨hiU, hiS⟩
      by_cases hiT : i ∈ T
      · exact h2 i ⟨hiT, hiS⟩
      · exact h1 i ⟨hiU, hiT⟩
    · intro h
      exact ⟨fun i hi => h i ⟨hi.1, fun hS => hi.2 (hST hS)⟩,
        fun i hi => h i ⟨hTU hi.1, hi.2⟩⟩
  simp only [extendId, of_apply]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- **Operators on disjoint regions commute**: extensions to `T` of operators on disjoint
regions `S, U ⊆ T` commute. -/
theorem commute_extendId_extendId (hS : S ⊆ T) (hU : U ⊆ T) (hd : Disjoint S U)
    (K : Matrix (Reg loc S) (Reg loc S) 𝕜) (L : Matrix (Reg loc U) (Reg loc U) 𝕜) :
    Commute (extendId hS K) (extendId hU L) := by
  have hsingle : ∀ {V : Finset σ} (x y : Reg loc V) (c : 𝕜),
      single x y c = c • single x y (1 : 𝕜) := fun x y c => by
    rw [smul_single, smul_eq_mul, mul_one]
  induction K using Matrix.induction_on' with
  | h_zero => rw [extendId_zero]; exact Commute.zero_left _
  | h_add K K' hK hK' => rw [extendId_add]; exact hK.add_left hK'
  | h_std_basis x y c =>
    induction L using Matrix.induction_on' with
    | h_zero => rw [extendId_zero]; exact Commute.zero_right _
    | h_add L L' hL hL' => rw [extendId_add]; exact hL.add_right hL'
    | h_std_basis x' y' c' =>
      rw [hsingle x y c, hsingle x' y' c', extendId_smul, extendId_smul, single_eq_piProd,
        single_eq_piProd, extendId_piProd, extendId_piProd]
      refine ((commute_piProd fun i => ?_).smul_left c).smul_right c'
      by_cases hi : i.1 ∈ S
      · exact Or.inr (dif_neg (Finset.disjoint_left.1 hd hi))
      · exact Or.inl (dif_neg hi)

end Extend

/-! ## Coefficient matrices across a cut -/

section CoeffMatrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} {S T : Finset σ} {α : Type*}

/-- For `S ⊆ T` a vector is determined by its coefficient matrix. -/
theorem coeffMatrix_eq_zero_iff [Zero α] (h : S ⊆ T) {v : Reg loc T → α} :
    coeffMatrix S v = 0 ↔ v = 0 := by
  refine ⟨fun hv => funext fun w => ?_, fun hv => hv ▸ rfl⟩
  obtain ⟨⟨x, z⟩, rfl⟩ := (glueEquiv h).surjective w
  exact congrFun (congrFun hv x) z

variable [∀ i, Fintype (loc i)]

/-- An operator extended from `S` acts on the coefficient matrix by left multiplication. -/
theorem coeffMatrix_extendId_mulVec [∀ i, DecidableEq (loc i)] (h : S ⊆ T)
    (K : Matrix (Reg loc S) (Reg loc S) 𝕜) (v : Reg loc T → 𝕜) :
    coeffMatrix S (extendId h K *ᵥ v) = K * coeffMatrix S v := by
  ext x z
  simp only [coeffMatrix_apply, mulVec, dotProduct, mul_apply, ← (glueEquiv h).sum_comp,
    Fintype.sum_prod_type, glueEquiv_apply, extendId_apply_glue, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end CoeffMatrix

/-! ## Symmetries of a gapped ground vector -/

section Gap

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}

/-- **Symmetries act on a gapped ground vector by scalars**: an operator on `S` whose extension
commutes with `H` multiplies the coefficient matrix of the ground vector by a scalar. -/
theorem HasGlobalGap.mul_coeffMatrix_eq_smul {H : Matrix (Reg loc T) (Reg loc T) 𝕜}
    {Ω : Reg loc T → 𝕜} {E₀ Δ : ℝ} (hgap : HasGlobalGap H Ω E₀ Δ) (hΔ : 0 < Δ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hE : H *ᵥ Ω = (E₀ : 𝕜) • Ω) (h : S ⊆ T)
    {K : Matrix (Reg loc S) (Reg loc S) 𝕜} (hK : Commute (extendId h K) H) :
    K * coeffMatrix S Ω = (star Ω ⬝ᵥ (extendId h K *ᵥ Ω)) • coeffMatrix S Ω := by
  have hv : H *ᵥ (extendId h K *ᵥ Ω) = (E₀ : 𝕜) • (extendId h K *ᵥ Ω) := by
    rw [mulVec_mulVec, ← hK.eq, ← mulVec_mulVec, hE, mulVec_smul]
  rw [← coeffMatrix_extendId_mulVec h]
  conv_lhs => rw [hgap.eq_smul_of_mulVec_eq hΔ hΩ hE hv]
  rw [coeffMatrix_smul]

end Gap

/-! ## Idempotent and rank-one matrices -/

section Idempotent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A Hermitian eigenvalue is real. -/
theorem star_eq_of_mulVec_eq_smul {K : Matrix ι ι 𝕜} (hK : K.IsHermitian) {u : ι → 𝕜} {a : 𝕜}
    (hu : K *ᵥ u = a • u) (h0 : u ≠ 0) : star a = a := by
  have him := hK.im_star_dotProduct_mulVec_self u
  rw [hu, dotProduct_smul, smul_eq_mul, RCLike.mul_im] at him
  obtain ⟨hre, hims⟩ := RCLike.nonneg_iff.1 (dotProduct_star_self_nonneg u)
  have hne : RCLike.re (star u ⬝ᵥ u) ≠ 0 := fun hr =>
    h0 (dotProduct_star_self_eq_zero.1 (RCLike.ext (by simpa using hr) (by simpa using hims)))
  rw [hims, mul_zero, zero_add] at him
  exact RCLike.conj_eq_iff_im.2 ((mul_eq_zero.1 him).resolve_right hne)

/-- The eigenvalues of a Hermitian idempotent are `0` or `1`. -/
theorem eigenvalues_eq_zero_or_one_of_mul_self_eq {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (h : A * A = A) (i : ι) : hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have he : (hA.eigenvectorBasis i).ofLp ≠ 0 := fun h0 =>
    hA.eigenvectorBasis.orthonormal.ne_zero i (by simpa using congrArg (WithLp.toLp 2) h0)
  have h1 := hA.mulVec_eigenvectorBasis i
  have h2 : (A * A) *ᵥ (hA.eigenvectorBasis i).ofLp =
      (hA.eigenvalues i * hA.eigenvalues i) • (hA.eigenvectorBasis i).ofLp := by
    rw [← mulVec_mulVec, h1, mulVec_smul, h1, smul_smul]
  rw [h, h1, ← sub_eq_zero, ← sub_smul] at h2
  have h3 := (smul_eq_zero.1 h2).resolve_right he
  have h4 : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by linear_combination -h3
  rcases mul_eq_zero.1 h4 with h4 | h4
  · exact Or.inl h4
  · exact Or.inr (sub_eq_zero.1 h4)

/-- **An idempotent state has zero entropy**: every eigenvalue is `0` or `1`. -/
theorem entropy_eq_zero_of_mul_self_eq (ρ : SubState ι 𝕜) (h : ρ.M * ρ.M = ρ.M) :
    ρ.entropy = 0 := by
  rw [ρ.entropy_eq_H, H]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eigenvalues_eq_zero_or_one_of_mul_self_eq ρ.psd.isHermitian h i with h' | h' <;>
    simp [h']

omit [DecidableEq ι] in
/-- A rank-one matrix squares to its trace times itself. -/
theorem vecMulVec_mul_self (x y : ι → 𝕜) :
    vecMulVec x y * vecMulVec x y = (vecMulVec x y).trace • vecMulVec x y := by
  rw [vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  ext i j
  simp [vecMulVec_apply, mul_left_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- A rank-one matrix times its adjoint is again rank one. -/
theorem vecMulVec_mul_conjTranspose {κ : Type*} [Fintype κ] (u : ι → 𝕜) (w : κ → 𝕜) :
    vecMulVec u w * (vecMulVec u w)ᴴ = vecMulVec u ((w ⬝ᵥ star w) • star u) := by
  rw [conjTranspose_vecMulVec, vecMulVec_mul_vecMulVec]

omit [DecidableEq ι] in
/-- **Rank one from a scalar commutant action**: if every operator commuting with a Hermitian
`K` multiplies the nonzero matrix `M` by a scalar, then `M` has rank one.  The operators used
are `K` itself and the projection onto a column of `M`, which lies in an eigenspace of `K`. -/
theorem exists_eq_vecMulVec_of_forall_commute {κ : Type*} {K : Matrix ι ι 𝕜}
    (hK : K.IsHermitian) {M : Matrix ι κ 𝕜} (hM : M ≠ 0)
    (h : ∀ L : Matrix ι ι 𝕜, Commute L K → ∃ c : 𝕜, L * M = c • M) :
    ∃ (u : ι → 𝕜) (w : κ → 𝕜), M = vecMulVec u w := by
  obtain ⟨a, ha⟩ := h K (Commute.refl K)
  obtain ⟨x₀, z₀, hxz⟩ : ∃ x z, M x z ≠ 0 := by
    by_contra hc
    exact hM (Matrix.ext fun x z => not_not.1 fun h' => hc ⟨x, z, h'⟩)
  have hu0 : (fun x => M x z₀) ≠ 0 := fun h0 => hxz (congrFun h0 x₀)
  have hKu : K *ᵥ (fun x => M x z₀) = a • fun x => M x z₀ := funext fun x => by
    simpa [mul_apply, mulVec, dotProduct] using congrFun (congrFun ha x) z₀
  have hreal := star_eq_of_mulVec_eq_smul hK hKu hu0
  have hl : star (fun x => M x z₀) ᵥ* K = a • star fun x => M x z₀ := by
    conv_lhs => rw [← hK.eq]
    rw [← star_mulVec, hKu, star_smul, hreal]
  obtain ⟨c, hc⟩ := h (vecMulVec (fun x => M x z₀) (star fun x => M x z₀)) (by
    rw [Commute, SemiconjBy, vecMulVec_mul, mul_vecMulVec, hl, hKu, smul_vecMulVec,
      vecMulVec_smul])
  rw [vecMulVec_mul] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := congrFun (congrFun hc x₀) z₀
    rw [zero_smul, Matrix.zero_apply, vecMulVec_apply] at h1
    exact mul_ne_zero hxz (fun h0 => hu0 (dotProduct_star_self_eq_zero.1 h0)) h1
  refine ⟨fun x => M x z₀, c⁻¹ • (star (fun x => M x z₀) ᵥ* M), ?_⟩
  rw [vecMulVec_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Idempotent

/-! ## Vanishing entropy across a split interaction -/

section Split

variable {q : ℕ} {Λ A : Finset (ℤ × ℤ)}
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}

/-- The Hamiltonian as a sum over all subsets of `Λ`. -/
theorem hamiltonian_eq_sum_powerset (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) :
    hamiltonian Λ Φ =
      ∑ X ∈ Λ.powerset, if h : X ⊆ Λ then extendId h (Φ X) else 0 := by
  rw [hamiltonian, ← Finset.sum_attach Λ.powerset]
  exact Finset.sum_congr rfl fun X _ => by rw [dif_pos (Finset.mem_powerset.1 X.2)]

/-- The Hamiltonian of a subregion, extended to `Λ`, is the sum of the terms supported in
it. -/
theorem extendId_hamiltonian (hA : A ⊆ Λ) :
    extendId hA (hamiltonian A Φ) =
      ∑ X ∈ Λ.powerset with X ⊆ A, if h : X ⊆ Λ then extendId h (Φ X) else 0 := by
  have hpow : (Λ.powerset.filter fun X => X ⊆ A) = A.powerset := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.trans hA, h⟩⟩
  rw [hpow, hamiltonian, extendId_sum, ← Finset.sum_attach A.powerset]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [extendId_extendId, dif_pos]

/-- **Extensions commuting with a split Hamiltonian**: if every nonzero term of the interaction
lies in `A` or in `Λ \ A`, an operator on `A` commuting with the Hamiltonian of `A` extends to
an operator commuting with the Hamiltonian of `Λ`. -/
theorem commute_extendId_hamiltonian (hA : A ⊆ Λ)
    (hsplit : ∀ X ⊆ Λ, Φ X ≠ 0 → X ⊆ A ∨ X ⊆ Λ \ A)
    {K : Matrix (Reg (Qudits q) A) (Reg (Qudits q) A) 𝕜} (hK : Commute K (hamiltonian A Φ)) :
    Commute (extendId hA K) (hamiltonian Λ Φ) := by
  rw [hamiltonian_eq_sum_powerset, ← Finset.sum_filter_add_sum_filter_not _ fun X => X ⊆ A,
    ← extendId_hamiltonian hA]
  refine Commute.add_right ?_ (Commute.sum_right _ _ _ fun X hX => ?_)
  · exact (extendId_mul hA _ _).symm.trans
      ((congrArg (extendId hA) hK.eq).trans (extendId_mul hA _ _))
  · obtain ⟨hXΛ, hXA⟩ := Finset.mem_filter.1 hX
    rw [Finset.mem_powerset] at hXΛ
    rw [dif_pos hXΛ]
    by_cases h0 : Φ X = 0
    · rw [h0, extendId_zero]
      exact Commute.zero_right _
    · have hXB := (hsplit X hXΛ h0).resolve_left hXA
      exact commute_extendId_extendId hA hXΛ
        (Finset.disjoint_of_subset_right hXB Finset.disjoint_sdiff) K (Φ X)

/-- **A split interaction gives a product ground state**: if every nonzero term of the
interaction lies in `A` or in `Λ \ A`, the gapped ground vector has zero entanglement entropy
across `A`. -/
theorem regionEntropy_pureState_eq_zero_of_split (hherm : ∀ X ⊆ A, (Φ X).IsHermitian)
    (hsplit : ∀ X ⊆ Λ, Φ X ≠ 0 → X ⊆ A ∨ X ⊆ Λ \ A) {Δ E₀ : ℝ} (hΔ : 0 < Δ)
    {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω)
    (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ) (hA : A ⊆ Λ) :
    (pureState Ω hΩ).regionEntropy hA = 0 := by
  have hM0 : coeffMatrix A Ω ≠ 0 := fun h0 => by
    rw [(coeffMatrix_eq_zero_iff hA).1 h0, star_zero, zero_dotProduct] at hΩ
    exact zero_ne_one hΩ
  -- Staged application: elaborating `mul_coeffMatrix_eq_smul` against `hgap` in one step
  -- exhausts the heartbeat budget in `whnf`.
  have hsym₀ := @HasGlobalGap.mul_coeffMatrix_eq_smul 𝕜 _ (ℤ × ℤ) _ (Qudits q) _ _ A Λ
    (hamiltonian Λ Φ) Ω E₀ Δ
  have hsym₁ := hsym₀ hgap
  have hsym := fun K : Matrix (Reg (Qudits q) A) (Reg (Qudits q) A) 𝕜 =>
    hsym₁ hΔ hΩ hE hA (K := K)
  have key : ∀ K : Matrix (Reg (Qudits q) A) (Reg (Qudits q) A) 𝕜,
      Commute K (hamiltonian A Φ) → ∃ c : 𝕜, K * coeffMatrix A Ω = c • coeffMatrix A Ω :=
    fun K hK => ⟨_, hsym K (commute_extendId_hamiltonian hA hsplit hK)⟩
  obtain ⟨u, w, hw⟩ := exists_eq_vecMulVec_of_forall_commute (isHermitian_hamiltonian hherm) hM0 key
  have hρ : ((pureState Ω hΩ).toSubState.restrict hA).M =
      vecMulVec u ((w ⬝ᵥ star w) • star u) := by
    rw [SubState.restrict_M, pureState_M, ptrace_vecMulVec_star hA, rhoA, hw,
      vecMulVec_mul_conjTranspose]
  have htr : ((pureState Ω hΩ).toSubState.restrict hA).M.trace = 1 :=
    ((pureState Ω hΩ).restrict hA).trace_eq_one
  refine entropy_eq_zero_of_mul_self_eq _ ?_
  rw [hρ, vecMulVec_mul_self, ← hρ, htr, one_smul]

end Split

/-! ## Lemma 2.2 and the degenerate cases -/

section Boundary

variable {Λ A X : Finset (ℤ × ℤ)} {R : ℕ}

/-- **Supports do not straddle an uncut boundary**: if no edge of `Λ` crosses the cut
`A | Λ \ A`, every admissible support lies in `A` or in `Λ \ A`, since a walk inside `Λ`
from a site of `X ∩ A` to a site of `X \ A` would cross the cut. -/
theorem subset_or_subset_sdiff_of_edgeBoundary_eq_empty (h : edgeBoundary Λ A = ∅)
    (hX : X ∈ supports Λ R) : X ⊆ A ∨ X ⊆ Λ \ A := by
  obtain ⟨hXΛ, -, hw⟩ := mem_supports_iff_walk.1 hX
  by_contra hc
  obtain ⟨y, hyX, hyA⟩ := Finset.not_subset.1 (not_or.1 hc).1
  obtain ⟨x, hxX, hxB⟩ := Finset.not_subset.1 (not_or.1 hc).2
  have hxA : x ∈ A := by_contra fun hxA => hxB (Finset.mem_sdiff.2 ⟨hXΛ hxX, hxA⟩)
  obtain ⟨p, -⟩ := hw x hxX y hyX
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {v | v.1 ∈ A} hxA hyA
  have hmem : (d.toProd.1.1, d.toProd.2.1) ∈ edgeBoundary Λ A :=
    mem_edgeBoundary.2 ⟨hd1, Finset.mem_sdiff.2 ⟨d.toProd.2.2, hd2⟩, d.adj⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem

variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ} {J Δ E₀ : ℝ}
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}
  {Ω : Reg (Qudits q) Λ → 𝕜}

/-- **Lemma 2.2 (a cut with no crossing edge)** [OAI265, §2.2]: under the hypotheses of
Theorem 1.1, if `∂_Λ A = ∅` then `S_Ω(A) = 0`. -/
theorem regionEntropy_eq_zero_of_edgeBoundary_eq_empty (hΦ : IsAdmissible Λ R J Φ)
    (hΔ : 0 < Δ) (hΩ : star Ω ⬝ᵥ Ω = 1) (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω)
    (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ) (hA : A ⊆ Λ) (h : edgeBoundary Λ A = ∅) :
    (pureState Ω hΩ).regionEntropy hA = 0 :=
  regionEntropy_pureState_eq_zero_of_split (fun X hX => (hΦ X (hX.trans hA)).1)
    (fun X hX h0 => subset_or_subset_sdiff_of_edgeBoundary_eq_empty h
      (by_contra fun hn => h0 ((hΦ X hX).2.2 hn)))
    hΔ hΩ hE hgap hA

/-- **Range zero** [OAI265, §2.2]: for on-site interactions the gapped ground state has zero
entropy across every cut, since a single site lies in `A` or in `Λ \ A`. -/
theorem regionEntropy_eq_zero_of_range_zero (hΦ : IsAdmissible Λ 0 J Φ) (hΔ : 0 < Δ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω)
    (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ) (hA : A ⊆ Λ) :
    (pureState Ω hΩ).regionEntropy hA = 0 := by
  refine regionEntropy_pureState_eq_zero_of_split (fun X hX => (hΦ X (hX.trans hA)).1)
    (fun X hX h0 => ?_) hΔ hΩ hE hgap hA
  obtain ⟨x, hx, rfl⟩ := hΦ.exists_eq_singleton hX h0
  by_cases hxA : x ∈ A
  · exact Or.inl (Finset.singleton_subset_iff.2 hxA)
  · exact Or.inr (Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hx, hxA⟩))

end Boundary

section Trivial

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U X : Finset σ}

/-- A region with a one-dimensional state space carries no entropy in a normalized state. -/
theorem regionEntropy_eq_zero_of_unique [Unique (Reg loc X)] (ρ : MState (Reg loc U) 𝕜)
    (h : X ⊆ U) : ρ.regionEntropy h = 0 := by
  rw [SubState.regionEntropy_def, SubState.entropy_of_unique, SubState.restrict_M, trace_ptrace,
    ρ.tr_eq_one, Real.negMulLog_one]

/-- **One-dimensional sites** [OAI265, §2.2]: for `q = 1` every region entropy of a normalized
state vanishes. -/
theorem regionEntropy_eq_zero_of_q_eq_one {q : ℕ} (hq : q = 1) {Λ X : Finset (ℤ × ℤ)}
    (ρ : MState (Reg (Qudits q) Λ) 𝕜) (h : X ⊆ Λ) : ρ.regionEntropy h = 0 := by
  subst hq
  exact regionEntropy_eq_zero_of_unique ρ h

/-- **The empty domain** [OAI265, §2.2]: on `Λ = ∅` every region entropy of a normalized state
vanishes. -/
theorem regionEntropy_eq_zero_of_eq_empty (hU : U = ∅) (ρ : MState (Reg loc U) 𝕜)
    (h : X ⊆ U) : ρ.regionEntropy h = 0 := by
  have : IsEmpty X := ⟨fun i => by simpa [hU] using h i.2⟩
  exact regionEntropy_eq_zero_of_unique ρ h

end Trivial

end OpenAI
