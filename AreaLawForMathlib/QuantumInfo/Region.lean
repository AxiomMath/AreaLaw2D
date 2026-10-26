import OpenAI.Statements
import AreaLawForMathlib.QuantumInfo.Entropy.Subadditivity
import QuantumInfo.Entropy.SSA

/-!
# Entropy inequalities and trace distance on regions

Extends `Arealaw/Subadditivity.lean` (regions of `Arealaw.Reg`) with Physlib
`QuantumInfo/Entropy/SSA.lean`: strong subadditivity and its corollaries on regions, the pure-state
complement identity, contractivity of the trace distance under restriction, the trace distance of
two pure states, and the vanishing entropy of a projection.

Some declarations here come from the v1 file `OpenAI/PureStateTraceDistance.lean`, whose header
records it as ported or adapted from `LionSR/QICLean` (see `NOTICE`).
-/

namespace Matrix

open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n]

open scoped Classical in
/-- If `X` is Hermitian and `X³ = c X` with `c > 0`, then `|X| = c^{-1/2} X²`. -/
theorem abs_eq_inv_sqrt_smul_mul_self {X : Matrix n n ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) (h3 : X * X * X = (c : ℂ) • X) :
    CFC.abs X = (√c)⁻¹ • (X * X) := by
  have hXX : 0 ≤ X * X := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [hX.eq] using Matrix.posSemidef_conjTranspose_mul_self X
  rw [CFC.abs, Matrix.star_eq_conjTranspose, hX.eq]
  refine CFC.sqrt_unique ?_ (smul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c)) hXX)
  have h4 : X * X * (X * X) = (c : ℂ) • (X * X) := by
    rw [← Matrix.mul_assoc, h3, Matrix.smul_mul]
  have hr : (√c)⁻¹ * (√c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  rw [smul_mul_smul_comm, h4, ← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, hr,
    Complex.ofReal_one, one_smul]

/-- **Trace distance of two pure states**: for unit vectors `ξ, η`,
`½‖|ξ⟩⟨ξ| - |η⟩⟨η|‖₁ = √(1 - |⟨ξ, η⟩|²)`. -/
theorem traceNorm_vecMulVec_sub_vecMulVec_div_two {ξ η : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1)
    (hη : star η ⬝ᵥ η = 1) :
    (vecMulVec ξ (star ξ) - vecMulVec η (star η)).traceNorm / 2 = √(1 - ‖star ξ ⬝ᵥ η‖ ^ 2) := by
  classical
  set P := vecMulVec ξ (star ξ)
  set Q := vecMulVec η (star η)
  set a : ℂ := star ξ ⬝ᵥ η with ha
  have hηξ : star η ⬝ᵥ ξ = star a := by
    rw [ha, ← Matrix.star_dotProduct_star, star_star, dotProduct_comm]
  have hvmv (x y z w : n → ℂ) : vecMulVec x y * vecMulVec z w = (y ⬝ᵥ z) • vecMulVec x w := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp [vecMulVec_apply, mul_left_comm]
  have hP : P * P = P := by rw [hvmv, hξ, one_smul]
  have hQ : Q * Q = Q := by rw [hvmv, hη, one_smul]
  have hs : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set c : ℝ := 1 - ‖a‖ ^ 2 with hc
  set X := P - Q with hX
  have hXh : X.IsHermitian :=
    (by rw [IsHermitian, conjTranspose_vecMulVec, star_star] : P.IsHermitian).sub
      (by rw [IsHermitian, conjTranspose_vecMulVec, star_star] : Q.IsHermitian)
  have hPQP : P * Q * P = (a * star a) • P := by
    rw [hvmv, smul_mul, hvmv, hηξ, smul_smul, ← ha]
  have hQPQ : Q * P * Q = (a * star a) • Q := by
    rw [hvmv, smul_mul, hvmv, ← ha, hηξ, smul_smul, mul_comm]
  have h3 : X * X * X = (c : ℂ) • X := by
    have hexp : X * X * X = P * P * P - P * P * Q - P * Q * P + P * Q * Q - Q * P * P +
        Q * P * Q + Q * Q * P - Q * Q * Q := by rw [hX]; noncomm_ring
    rw [hexp, hPQP, hQPQ, hP, hQ, Matrix.mul_assoc P Q Q, Matrix.mul_assoc Q P P, hP, hQ, hs,
      hc, hX]
    push_cast
    simp only [sub_smul, one_smul, smul_sub]
    abel
  have htr : (X * X).trace = ((2 * c : ℝ) : ℂ) := by
    have hXX : X * X = P * P - P * Q - Q * P + Q * Q := by rw [hX]; noncomm_ring
    rw [hXX, hP, hQ, trace_add, trace_sub, trace_sub, hvmv, hvmv, trace_smul, trace_smul,
      trace_vecMulVec, trace_vecMulVec, trace_vecMulVec, trace_vecMulVec,
      dotProduct_comm ξ (star ξ), hξ, dotProduct_comm η (star η), hη,
      dotProduct_comm ξ (star η), hηξ, dotProduct_comm η (star ξ), ← ha, smul_eq_mul,
      smul_eq_mul, mul_comm (star a), hs, hc]
    push_cast
    ring
  have hc0 : 0 ≤ c := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
    rw [hXh.eq, htr, Complex.zero_le_real] at h
    linarith
  have htn : X.traceNorm = (CFC.abs X).trace.re := by
    rw [Matrix.traceNorm, CFC.abs, Matrix.star_eq_conjTranspose, hXh.eq]
    rfl
  rcases hc0.lt_or_eq with hcpos | hczero
  · rw [htn, abs_eq_inv_sqrt_smul_mul_self hXh hcpos h3, trace_smul, htr, Complex.real_smul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    have hsq : √c * √c = c := Real.mul_self_sqrt hcpos.le
    have hs0 : 0 < √c := Real.sqrt_pos.mpr hcpos
    field_simp
    linarith
  · have hX0 : X = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
      (by rw [hXh.eq, htr, ← hczero]; simp)
    rw [htn, hX0, CFC.abs_zero, ← hczero, Real.sqrt_zero]
    simp

end Matrix

namespace Arealaw

open Matrix
open scoped ComplexOrder MatrixOrder

/-- Tracing out the first factor commutes with reindexing the second. -/
theorem traceLeft_submatrix_prodMap {R : Type*} [AddCommMonoid R] {m n n' : Type*} [Fintype m]
    (A : Matrix (m × n) (m × n) R) (f g : n' → n) :
    (A.submatrix (Prod.map id f) (Prod.map id g)).traceLeft = A.traceLeft.submatrix f g := by
  ext; simp [traceLeft]

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} {X Y Z : Finset σ}

/-- Gluing a configuration on pairwise disjoint `X`, `Y`, `Z` as `X ∪ (Y ∪ Z)` agrees with
gluing `X ∪ Y` first and then `Z`. -/
theorem unionEquiv_symm_union_eq_glue (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (x : Reg loc X) (y : Reg loc Y) (z : Reg loc Z) :
    (unionEquiv (Finset.disjoint_union_right.2 ⟨hXY, hXZ⟩)).symm
        (x, (unionEquiv hYZ).symm (y, z)) =
      glue ((unionEquiv hXY).symm (x, y))
        (regEquivOfEq (by rw [← Finset.union_assoc, Finset.union_sdiff_cancel_left
          (Finset.disjoint_union_left.2 ⟨hXZ, hYZ⟩)] : (X ∪ (Y ∪ Z)) \ (X ∪ Y) = Z).symm z) := by
  funext j
  by_cases hX : (j : σ) ∈ X
  · simp [glue, hX]
  · by_cases hY : (j : σ) ∈ Y
    · simp [glue, hX, hY, sdiffEquiv]
    · simp [glue, hX, hY, sdiffEquiv, restr]

variable [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U : Finset σ}

namespace MState

/-- The tripartite state on `X × Y × Z` of a state on `U ⊇ X ∪ Y ∪ Z`. -/
noncomputable def tripartite (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    _root_.MState (Reg loc X × Reg loc Y × Reg loc Z) :=
  (unionState ρ (Finset.disjoint_union_right.2 ⟨hXY, hXZ⟩) hX (Finset.union_subset hY hZ)).relabel
    ((Equiv.refl _).prodCongr (unionEquiv hYZ).symm)

theorem traceLeft_tripartite (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    (tripartite ρ hXY hXZ hYZ hX hY hZ).traceLeft = unionState ρ hYZ hY hZ := by
  apply _root_.MState.ext_m
  change ((unionState ρ _ hX (Finset.union_subset hY hZ)).m.submatrix
    (Prod.map id (unionEquiv hYZ).symm) (Prod.map id (unionEquiv hYZ).symm)).traceLeft = _
  rw [traceLeft_submatrix_prodMap]
  change (unionState ρ _ hX (Finset.union_subset hY hZ)).traceLeft.m.submatrix _ _ = _
  rw [unionState, traceLeft_physlibEquiv_submatrix, unionState, MState.restrict_restrict]
  rfl

theorem assoc'_traceRight_tripartite (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    (tripartite ρ hXY hXZ hYZ hX hY hZ).assoc'.traceRight = unionState ρ hXY hX hY := by
  have hd : Disjoint X (Y ∪ Z) := Finset.disjoint_union_right.2 ⟨hXY, hXZ⟩
  have hW : X ∪ (Y ∪ Z) ⊆ U := Finset.union_subset hX (Finset.union_subset hY hZ)
  have hXYW : X ∪ Y ⊆ X ∪ (Y ∪ Z) := Finset.union_subset Finset.subset_union_left
    (Finset.subset_union_left.trans Finset.subset_union_right)
  apply _root_.MState.ext_m
  ext ⟨x, y⟩ ⟨x', y'⟩
  change ∑ z, (ρ.restrict hW).M ((unionEquiv hd).symm (x, (unionEquiv hYZ).symm (y, z)))
      ((unionEquiv hd).symm (x', (unionEquiv hYZ).symm (y', z))) =
    ptrace (Finset.union_subset hX hY) ρ.M ((unionEquiv hXY).symm (x, y))
      ((unionEquiv hXY).symm (x', y'))
  rw [← ptrace_ptrace hXYW hW, ← MState.restrict_M]
  have hc : (X ∪ (Y ∪ Z)) \ (X ∪ Y) = Z := by
    rw [← Finset.union_assoc, Finset.union_sdiff_cancel_left
      (Finset.disjoint_union_left.2 ⟨hXZ, hYZ⟩)]
  exact Fintype.sum_equiv (regEquivOfEq hc).symm _ _ fun z => by
    rw [unionEquiv_symm_union_eq_glue hXY hXZ hYZ, unionEquiv_symm_union_eq_glue hXY hXZ hYZ]
    rfl

/-- **Strong subadditivity on regions** [Lieb–Ruskai 1973]:
`S(X ∪ Y ∪ Z) + S(Y) ≤ S(X ∪ Y) + S(Y ∪ Z)` for pairwise disjoint regions. -/
theorem regionEntropy_strong_subadditivity (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    ρ.toSubState.regionEntropy (Finset.union_subset (Finset.union_subset hX hY) hZ) +
        ρ.toSubState.regionEntropy hY ≤
      ρ.toSubState.regionEntropy (Finset.union_subset hX hY) +
        ρ.toSubState.regionEntropy (Finset.union_subset hY hZ) := by
  have h := Sᵥₙ_strong_subadditivity (tripartite ρ hXY hXZ hYZ hX hY hZ)
  dsimp only at h
  rw [assoc'_traceRight_tripartite, traceLeft_tripartite, Sᵥₙ_traceRight_unionState,
    Sᵥₙ_unionState, Sᵥₙ_unionState, tripartite, Sᵥₙ_relabel, Sᵥₙ_unionState] at h
  rwa [ρ.toSubState.regionEntropy_congr (Finset.union_assoc X Y Z) _
    (Finset.union_subset hX (Finset.union_subset hY hZ))]

/-- **Conditioning reduces entropy**: `S(X | Y ∪ Z) ≤ S(X | Y)` for pairwise disjoint regions,
with `S(X | Y) = S(X ∪ Y) - S(Y)`. -/
theorem regionEntropy_union_sub_le (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    ρ.toSubState.regionEntropy (Finset.union_subset hX (Finset.union_subset hY hZ)) -
        ρ.toSubState.regionEntropy (Finset.union_subset hY hZ) ≤
      ρ.toSubState.regionEntropy (Finset.union_subset hX hY) - ρ.toSubState.regionEntropy hY := by
  have h := regionEntropy_strong_subadditivity ρ hXY hXZ hYZ hX hY hZ
  rw [ρ.toSubState.regionEntropy_congr (Finset.union_assoc X Y Z) _
    (Finset.union_subset hX (Finset.union_subset hY hZ))] at h
  linarith

/-- **Monotonicity of mutual information**: `I(X : Y) ≤ I(X : Y ∪ Z)` for pairwise disjoint
regions. -/
theorem mutualInfo_le_mutualInfo_union (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    ρ.toSubState.mutualInfo hX hY ≤ ρ.toSubState.mutualInfo hX (Finset.union_subset hY hZ) := by
  have h := regionEntropy_union_sub_le ρ hXY hXZ hYZ hX hY hZ
  rw [SubState.mutualInfo_def, SubState.mutualInfo_def]
  linarith

/-- **Conditional entropy is bounded by the first dimension**:
`|S(X ∪ Y) - S(Y)| ≤ log dim X` for disjoint regions. -/
theorem abs_regionEntropy_union_sub_le_log_card (ρ : MState (Reg loc U) ℂ) (hXY : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    |ρ.toSubState.regionEntropy (Finset.union_subset hX hY) - ρ.toSubState.regionEntropy hY| ≤
      Real.log (Fintype.card (Reg loc X)) := by
  have hX₀ : ρ.toSubState.regionEntropy hX ≤ Real.log (Fintype.card (Reg loc X)) :=
    (ρ.restrict hX).entropy_le_log_card
  have h₁ := regionEntropy_union_le ρ hXY hX hY
  have h₂ := (abs_sub_le_iff.1 (abs_regionEntropy_sub_regionEntropy_le ρ hXY hX hY)).2
  rw [abs_le]
  constructor <;> linarith

/-- **Pure states on a bipartition**: for a pure state on `A ∪ B`, `A`, `B` disjoint,
`S(A) = S(B)`. -/
theorem regionEntropy_pureState_union {A B : Finset σ} (Ω : Reg loc U → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hd : Disjoint A B) (hU : A ∪ B = U) (hA : A ⊆ U) (hB : B ⊆ U) :
    (OpenAI.pureState Ω hΩ).toSubState.regionEntropy hA =
      (OpenAI.pureState Ω hΩ).toSubState.regionEntropy hB := by
  subst hU
  let ψ : Ket (Reg loc (A ∪ B)) := ⟨Ω, by
    have h := hΩ
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul'] at h
    exact_mod_cast h⟩
  have hρ : unionState (OpenAI.pureState Ω hΩ) hd hA hB =
      (_root_.MState.pure ψ).relabel (unionEquiv hd).symm := by
    apply _root_.MState.ext_m
    ext i j
    simp [unionState, OpenAI.pureState, vecMulVec_apply]
    rfl
  have h := Sᵥₙ_pure_complement ψ (unionEquiv hd).symm
  rw [← hρ, Sᵥₙ_traceLeft_unionState, Sᵥₙ_traceRight_unionState] at h
  exact h.symm

/-- **Pure states**: `S(A) = S(U \ A)` for a pure state on `U` and `A ⊆ U`. -/
theorem regionEntropy_pureState_sdiff {A : Finset σ} (Ω : Reg loc U → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hA : A ⊆ U) :
    (OpenAI.pureState Ω hΩ).toSubState.regionEntropy hA =
      (OpenAI.pureState Ω hΩ).toSubState.regionEntropy (Finset.sdiff_subset : U \ A ⊆ U) :=
  regionEntropy_pureState_union Ω hΩ Finset.disjoint_sdiff (Finset.union_sdiff_of_subset hA) _ _

end MState

namespace SubState

variable {𝕜 : Type*} [RCLike 𝕜] {S T : Finset σ}

omit [∀ i, DecidableEq (loc i)] in
/-- **Contractivity of the trace distance under partial trace**. -/
theorem D₁_restrict_le (h : S ⊆ T) (ρ τ : SubState (Reg loc T) 𝕜) :
    (ρ.restrict h).D₁ (τ.restrict h) ≤ ρ.D₁ τ := by
  classical
  obtain ⟨M, hM, hM1, hval⟩ := ((ρ.restrict h).isGreatest_D₁ (τ.restrict h)).1
  have hE0 : 0 ≤ extendId h M := by
    rw [Matrix.nonneg_iff_posSemidef] at hM ⊢
    exact posSemidef_extendId h hM
  have hE1 : extendId h M ≤ 1 := by
    rw [Matrix.le_iff] at hM1 ⊢
    have : (1 : Matrix (Reg loc T) (Reg loc T) 𝕜) - extendId h M = extendId h (1 - M) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, extendId_add, extendId_one, ← neg_one_smul 𝕜 M,
        extendId_smul, neg_one_smul]
    rw [this]
    exact posSemidef_extendId h hM1
  have htr : (M * ((ρ.restrict h).M - (τ.restrict h).M)).trace =
      (extendId h M * (ρ.M - τ.M)).trace := by
    rw [restrict_M, restrict_M, ← ptrace_sub, Matrix.trace_mul_comm, trace_ptrace_mul,
      Matrix.trace_mul_comm]
  rw [hval, htr]
  exact ρ.abs_re_trace_mul_le_D₁ τ hE0 hE1

end SubState

end Arealaw

namespace Arealaw

open Matrix
open scoped ComplexOrder

section Idempotent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A state with idempotent density matrix has zero entropy: its eigenvalues are `0` or `1`. -/
theorem SubState.entropy_eq_zero_of_isIdempotentElem (ρ : SubState ι ℂ)
    (h : IsIdempotentElem ρ.M) : ρ.entropy = 0 := by
  rw [ρ.entropy_eq_H, H]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hρ := ρ.psd.isHermitian
  have he : (hρ.eigenvectorBasis i).ofLp ≠ 0 := fun h0 =>
    hρ.eigenvectorBasis.orthonormal.ne_zero i (by simpa using congrArg (WithLp.toLp 2) h0)
  have h1 := hρ.mulVec_eigenvectorBasis i
  have h2 : (ρ.M * ρ.M) *ᵥ (hρ.eigenvectorBasis i).ofLp =
      (hρ.eigenvalues i * hρ.eigenvalues i) • (hρ.eigenvectorBasis i).ofLp := by
    rw [← mulVec_mulVec, h1, mulVec_smul, h1, smul_smul]
  rw [h.eq, h1, ← sub_eq_zero, ← sub_smul] at h2
  have h3 := (smul_eq_zero.1 h2).resolve_right he
  have h4 : hρ.eigenvalues i * (hρ.eigenvalues i - 1) = 0 := by linear_combination -h3
  rcases mul_eq_zero.1 h4 with h4 | h4
  · simp [h4]
  · simp [sub_eq_zero.1 h4]

end Idempotent

section Lift

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {S T : Finset σ}

/-- Extension by the identity is multiplicative. -/
theorem extendId_mul (h : S ⊆ T) (A B : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (A * B) = extendId h A * extendId h B := by
  rw [extendId_eq_kronecker, extendId_eq_kronecker, extendId_eq_kronecker,
    submatrix_mul_equiv, ← mul_kronecker_mul, one_mul]

/-- The expectation of `A ⊗ 1` in `φ` is `Tr(ρ_{φ,S} A)`. -/
theorem dotProduct_extendId_mulVec (h : S ⊆ T) (φ : Reg loc T → 𝕜)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    star φ ⬝ᵥ (extendId h A *ᵥ φ) = (ptrace h (vecMulVec φ (star φ)) * A).trace := by
  rw [trace_ptrace_mul, vecMulVec_mul, trace_vecMulVec, dotProduct_comm φ, ← dotProduct_mulVec]

/-- Entries of a product of extensions from disjoint regions `S, U ⊆ T`: the product is
diagonal off `S ∪ U` and acts by `A` on `S` and by `B` on `U`. -/
theorem extendId_mul_extendId_apply {U : Finset σ} (hS : S ⊆ T) (hU : U ⊆ T)
    (hd : Disjoint S U) (A : Matrix (Reg loc S) (Reg loc S) 𝕜)
    (B : Matrix (Reg loc U) (Reg loc U) 𝕜) (w w' : Reg loc T) :
    (extendId hS A * extendId hU B) w w' =
      if ∀ i : T, i.1 ∉ S → i.1 ∉ U → w i = w' i then
        A (restr hS w) (restr hS w') * B (restr hU w) (restr hU w') else 0 := by
  classical
  let v₀ : Reg loc T := fun i ↦ if i.1 ∈ S then w' i else w i
  rw [mul_apply, Finset.sum_eq_single v₀]
  · have h1 : restr (S := T \ S) Finset.sdiff_subset w =
        restr (S := T \ S) Finset.sdiff_subset v₀ := by
      funext i
      simp [restr, Finset.restrict₂, v₀, (Finset.mem_sdiff.1 i.2).2]
    have h2 : restr hS v₀ = restr hS w' := by
      funext i
      simp [restr, Finset.restrict₂, v₀, i.2]
    have h3 : restr hU v₀ = restr hU w := by
      funext i
      simp [restr, Finset.restrict₂, v₀, Finset.disjoint_right.1 hd i.2]
    simp only [extendId, of_apply, h1, h2, h3, if_true]
    by_cases hc : ∀ i : T, i.1 ∉ S → i.1 ∉ U → w i = w' i
    · have h4 : restr (S := T \ U) Finset.sdiff_subset v₀ =
          restr (S := T \ U) Finset.sdiff_subset w' := by
        funext i
        have hiU := (Finset.mem_sdiff.1 i.2).2
        simp only [restr, Finset.restrict₂, v₀]
        split_ifs with hiS
        · rfl
        · exact hc ⟨i.1, Finset.sdiff_subset i.2⟩ hiS hiU
      rw [if_pos h4, if_pos hc]
    · have h4 : restr (S := T \ U) Finset.sdiff_subset v₀ ≠
          restr (S := T \ U) Finset.sdiff_subset w' := by
        intro he
        apply hc
        intro i hiS hiU
        have := congrFun he ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, hiU⟩⟩
        simpa [restr, Finset.restrict₂, v₀, hiS] using this
      rw [if_neg h4, if_neg hc, mul_zero]
  · intro v _ hv
    simp only [extendId, of_apply]
    split_ifs with ha hb
    · exfalso
      apply hv
      funext i
      by_cases hiS : i.1 ∈ S
      · have := congrFun hb ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, Finset.disjoint_left.1 hd hiS⟩⟩
        simpa [restr, Finset.restrict₂, v₀, hiS] using this
      · have := congrFun ha ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, hiS⟩⟩
        simpa [restr, Finset.restrict₂, v₀, hiS] using this.symm
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Operators on disjoint regions commute**: for `A` on `S`, `B` on `U` with `S ∩ U = ∅`,
`(A ⊗ 1)(B ⊗ 1) = (B ⊗ 1)(A ⊗ 1)` on `T ⊇ S ∪ U`. -/
theorem commute_extendId_extendId {U : Finset σ} (hS : S ⊆ T) (hU : U ⊆ T)
    (hd : Disjoint S U) (A : Matrix (Reg loc S) (Reg loc S) 𝕜)
    (B : Matrix (Reg loc U) (Reg loc U) 𝕜) :
    Commute (extendId hS A) (extendId hU B) := by
  ext w w'
  rw [extendId_mul_extendId_apply hS hU hd, extendId_mul_extendId_apply hU hS hd.symm,
    mul_comm]
  exact if_congr ⟨fun h i hU hS ↦ h i hS hU, fun h i hS hU ↦ h i hU hS⟩ rfl rfl

omit [∀ i, Fintype (loc i)] in
/-- Extension by the identity is transitive: `(A ⊗ 1_{T∖S}) ⊗ 1_{V∖T} = A ⊗ 1_{V∖S}`. -/
theorem extendId_extendId {V : Finset σ} (hST : S ⊆ T) (hTV : T ⊆ V)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId hTV (extendId hST A) = extendId (hST.trans hTV) A := by
  ext w w'
  have hiff : (restr (S := V \ T) Finset.sdiff_subset w = restr Finset.sdiff_subset w' ∧
      restr (S := T \ S) Finset.sdiff_subset (restr hTV w) =
        restr Finset.sdiff_subset (restr hTV w')) ↔
      restr (S := V \ S) Finset.sdiff_subset w = restr Finset.sdiff_subset w' := by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩ i ⟨hiV, hiS⟩
      by_cases hiT : i ∈ T
      · exact h2 i ⟨hiT, hiS⟩
      · exact h1 i ⟨hiV, hiT⟩
    · intro h
      exact ⟨fun i hi ↦ h i ⟨hi.1, fun hS ↦ hi.2 (hST hS)⟩, fun i hi ↦ h i ⟨hTV hi.1, hi.2⟩⟩
  simp only [extendId, Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; tauto)

end Lift

end Arealaw
