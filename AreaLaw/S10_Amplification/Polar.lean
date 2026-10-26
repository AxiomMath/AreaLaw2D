import AreaLaw.S10_Amplification.ExcitedDecay
import AreaLawForMathlib.LinearAlgebra.Matrix.UnitaryCompletion

/-!
# §10.2 The local unitary `U'` via polar decomposition (D10.14)

Digest `digest/10-amplification.md` (D10.14), paper `paper/sections/09-amplification.tex`
lines 524–545. No geometry: the support of `U'` is a region `N ⊆ Λ` together with the copy
`s'`, in the coordinates `splitN` of Setup.
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (IsSupportedOn)
open scoped Kronecker MatrixOrder ComplexOrder InnerProductSpace

section Polar

variable {n A B' : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A] [Fintype B']
  [DecidableEq B']

-- helper
theorem vnorm_unitary_mulVec {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) (v : n → ℂ) :
    vnorm (U *ᵥ v) = vnorm v := by
  have h := vnorm_mulVec_sq U v
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hU, one_mulVec, ← vnorm_sq] at h
  exact (sq_eq_sq₀ (vnorm_nonneg _) (vnorm_nonneg _)).1 h

omit [DecidableEq n] in
-- helper
/-- D10.14.4. `H₊ ≥ 0 ⇒ ‖v‖ ≤ ‖(I + H₊) v‖`. -/
theorem vnorm_le_vnorm_add_mulVec {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) :
    vnorm v ≤ vnorm (v + H *ᵥ v) := by
  have h0 : 0 ≤ RCLike.re ⟪(WithLp.toLp 2 v : EuclideanSpace ℂ n), WithLp.toLp 2 (H *ᵥ v)⟫_ℂ := by
    rw [inner_toLp]; exact (Complex.le_def.mp (hH.dotProduct_mulVec_nonneg v)).1
  have h := norm_add_sq (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ n) (WithLp.toLp 2 (H *ᵥ v))
  rw [← WithLp.toLp_add] at h
  change vnorm (v + H *ᵥ v) ^ 2 = vnorm v ^ 2 + _ + vnorm (H *ᵥ v) ^ 2 at h
  exact (pow_le_pow_iff_left₀ (vnorm_nonneg _) (vnorm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg (vnorm (H *ᵥ v))])

/-- D10.14.3–5. For `U'` unitary and `H₊ ≥ 0`, with `ξ = U'^† η`:
`‖U'φ - η‖ = ‖φ - ξ‖ ≤ ‖(I + H₊)(ξ - φ)‖ ≤ ‖H₊ξ - φ‖ + ‖H₊φ - ξ‖
= ‖(U'H₊)^† η - φ‖ + ‖U'H₊ φ - η‖`. -/
theorem vnorm_unitary_sub_le {U H : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (hH : H.PosSemidef) (φ η : n → ℂ) :
    vnorm (U *ᵥ φ - η) ≤ vnorm ((U * H) *ᵥ φ - η) + vnorm ((U * H)ᴴ *ᵥ η - φ) := by
  set ξ := Uᴴ *ᵥ η
  have hUξ : U *ᵥ ξ = η := by
    rw [mulVec_mulVec, ← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hU, one_mulVec]
  -- D10.14.3
  have e1 : vnorm (U *ᵥ φ - η) = vnorm (φ - ξ) := by
    rw [show U *ᵥ φ - η = U *ᵥ (φ - ξ) by rw [mulVec_sub, hUξ], vnorm_unitary_mulVec hU]
  have e2 : vnorm ((U * H) *ᵥ φ - η) = vnorm (H *ᵥ φ - ξ) := by
    rw [show (U * H) *ᵥ φ - η = U *ᵥ (H *ᵥ φ - ξ) by rw [mulVec_sub, hUξ, mulVec_mulVec],
      vnorm_unitary_mulVec hU]
  have e3 : (U * H)ᴴ *ᵥ η = H *ᵥ ξ := by
    rw [conjTranspose_mul, hH.isHermitian.eq, ← mulVec_mulVec]
  -- D10.14.4
  have e4 : (ξ - φ) + H *ᵥ (ξ - φ) = (H *ᵥ ξ - φ) - (H *ᵥ φ - ξ) := by
    rw [mulVec_sub]; abel
  -- D10.14.5
  rw [e1, e2, e3, vnorm_sub_rev]
  have := vnorm_le_vnorm_add_mulVec hH (ξ - φ)
  rw [e4] at this
  linarith [vnorm_sub_le (H *ᵥ ξ - φ) (H *ᵥ φ - ξ)]

-- helper
/-- D10.14.2. Polar decomposition `M = V H₊` with `V` unitary and `H₊ ≥ 0` (here
`H₊ = Q diag(√λ) Q^†` for the eigenvector unitary `Q` of `M^† M`), for singular `M` too. -/
theorem exists_polar (M : Matrix A A ℂ) :
    ∃ V ∈ unitary (Matrix A A ℂ), ∃ H : Matrix A A ℂ, H.PosSemidef ∧ M = V * H := by
  have hM := posSemidef_conjTranspose_mul_self M
  set Q := hM.isHermitian.eigenvectorUnitary
  set Dg : Matrix A A ℂ := diagonal fun j => ((√(hM.isHermitian.eigenvalues j) : ℝ) : ℂ)
  obtain ⟨V, hV, hMQ⟩ := exists_mem_unitaryGroup_eq_mul_diagonal (M := M * Q.1)
    (d := hM.isHermitian.eigenvalues) (by
      simpa [mul_assoc, star_eq_conjTranspose] using
        hM.isHermitian.conjStarAlgAut_star_eigenvectorUnitary)
  refine ⟨V * star Q.1, mul_mem hV (Unitary.star_mem Q.2), Q.1 * Dg * star Q.1, ?_, ?_⟩
  · have hD : Dg.PosSemidef := posSemidef_diagonal_iff.2 fun j =>
      Complex.zero_le_real.2 (Real.sqrt_nonneg _)
    simpa [star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same Q.1
  · calc M = M * Q.1 * star Q.1 := by
          rw [mul_assoc, Unitary.mul_star_self_of_mem Q.2, mul_one]
      _ = V * Dg * star Q.1 := by rw [hMQ]; rfl
      _ = V * star Q.1 * (Q.1 * Dg * star Q.1) := by
          simp only [mul_assoc]
          rw [← mul_assoc (star Q.1) Q.1, Unitary.star_mul_self_of_mem Q.2, one_mul]

omit [Fintype B'] in
-- helper
theorem kronecker_one_submatrix_mem_unitary [Finite B'] (e : n ≃ A × B') {V : Matrix A A ℂ}
    (hV : V ∈ unitary (Matrix A A ℂ)) :
    (V ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e ∈ unitary (Matrix n n ℂ) := by
  have := Fintype.ofFinite B'
  rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_submatrix, conjTranspose_kronecker,
    conjTranspose_one, submatrix_mul_equiv, submatrix_mul_equiv, ← mul_kronecker_one,
    ← mul_kronecker_one, ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hV,
    Unitary.mul_star_self_of_mem hV, one_kronecker_one, submatrix_one_equiv]
  exact ⟨rfl, rfl⟩

omit [DecidableEq n] [Fintype B'] in
/-- D10.14. `R' = (M ⊗ I)` (reindexed by `e`) is supported on the first factor; there is a
unitary `U'` on it (tensored with the identity elsewhere), `R' = U' H₊`, with
`‖U'φ - η‖ ≤ ‖R'φ - η‖ + ‖R'^†η - φ‖`. -/
theorem step_10_14 [Finite B'] (e : n ≃ A × B') (M : Matrix A A ℂ) {φ η : n → ℂ} {a b : ℝ}
    (ha : vnorm ((M ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e *ᵥ φ - η) ≤ a)
    (hb : vnorm (((M ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e)ᴴ *ᵥ η - φ) ≤ b) :
    ∃ V ∈ unitary (Matrix A A ℂ),
      vnorm (((V : Matrix A A ℂ) ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e *ᵥ φ - η) ≤ a + b := by
  classical
  have := Fintype.ofFinite B'
  -- D10.14.2
  obtain ⟨V, hV, H, hH, rfl⟩ := exists_polar M
  refine ⟨V, hV, ?_⟩
  have hR : ((V * H) ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e =
      (V ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e * (H ⊗ₖ (1 : Matrix B' B' ℂ)).submatrix e e := by
    rw [submatrix_mul_equiv, mul_kronecker_one]
  -- D10.14.3–5
  have h := vnorm_unitary_sub_le (kronecker_one_submatrix_mem_unitary e hV)
    ((hH.kronecker PosSemidef.one).submatrix e) φ η
  rw [← hR] at h
  linarith

end Polar

/-! ## Operators acting on `N ∪ s'` -/

section ActsOn

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, DecidableEq (loc i)]
  {Λ N : Finset σ} (hN : N ⊆ Λ) (X : Finset σ)

theorem ActsOn.one : ActsOn (loc := loc) hN X 1 :=
  ⟨1, by rw [one_kronecker_one, submatrix_one_equiv]⟩

variable {hN X} in
theorem ActsOn.mul [∀ i, Fintype (loc i)] {R R' : Matrix (Reg loc Λ × (Reg loc X × Reg loc X))
    (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ} (h : ActsOn hN X R) (h' : ActsOn hN X R') :
    ActsOn hN X (R * R') := by
  obtain ⟨M, rfl⟩ := h
  obtain ⟨M', rfl⟩ := h'
  exact ⟨M * M', by rw [submatrix_mul_equiv, mul_kronecker_one]⟩

omit [∀ i, DecidableEq (loc i)] in
-- helper
theorem restr_sdiff_eq_iff {N' : Finset σ} (hNN' : N ⊆ N') (hN' : N' ⊆ Λ) (w w' : Reg loc Λ) :
    restr (Finset.sdiff_subset : Λ \ N ⊆ Λ) w = restr Finset.sdiff_subset w' ↔
      restr ((Finset.sdiff_subset : N' \ N ⊆ N').trans hN') w =
          restr (Finset.sdiff_subset.trans hN') w' ∧
        restr (Finset.sdiff_subset : Λ \ N' ⊆ Λ) w = restr Finset.sdiff_subset w' := by
  simp only [funext_iff, restr, Finset.restrict₂, Subtype.forall, Finset.mem_sdiff]
  constructor
  · intro h
    exact ⟨fun j hj => h j ⟨hN' hj.1, hj.2⟩, fun j hj => h j ⟨hj.1, fun h' => hj.2 (hNN' h')⟩⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj' : j ∈ N'
    · exact h1 j ⟨hj', hj.2⟩
    · exact h2 j ⟨hj.1, hj'⟩

variable {hN X} in
/-- D10.14.1. An operator acting on `N ∪ s'` acts on `N' ∪ s'` for `N ⊆ N' ⊆ Λ`. -/
theorem ActsOn.mono {N' : Finset σ} (hNN' : N ⊆ N') (hN' : N' ⊆ Λ)
    {R : Matrix (Reg loc Λ × (Reg loc X × Reg loc X)) (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ}
    (h : ActsOn hN X R) : ActsOn hN' X R := by
  obtain ⟨M, rfl⟩ := h
  refine ⟨Matrix.of fun p q =>
    if restr (Finset.sdiff_subset : N' \ N ⊆ N') p.1 = restr Finset.sdiff_subset q.1 then
      M (restr hNN' p.1, p.2) (restr hNN' q.1, q.2) else 0, ?_⟩
  ext a b
  simp only [submatrix_apply, kroneckerMap_apply, splitN, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.prodProdProdComm_apply, of_apply, one_apply, Prod.mk.injEq]
  have key := restr_sdiff_eq_iff hNN' hN' a.1 b.1
  split_ifs <;> simp_all

variable {hN} in
/-- D10.14.1. An operator supported in `N ⊆ Λ` acts on `N ∪ s'` (as `A ⊗ I_{s'e'}`). -/
theorem actsOn_kronecker_one {A : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hA : IsSupportedOn hN A) :
    ActsOn hN X (A ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) := by
  obtain ⟨A', rfl⟩ := hA
  refine ⟨A' ⊗ₖ (1 : Matrix (Reg loc X) (Reg loc X) ℂ), ?_⟩
  ext a b
  simp only [extendId_eq_kronecker, submatrix_apply, kroneckerMap_apply, splitN,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodProdProdComm_apply, glueEquiv_symm_apply,
    one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

variable {hN X} in
/-- D10.14. If `R'` acts on `N ∪ s'` and `‖R'φ - η‖ ≤ a`, `‖R'^†η - φ‖ ≤ b`, there is a
unitary `U'` on `ℋ_N ⊗ ℋ_{s'}` (identity on `Λ \ N` and `e'`) with `‖U'φ - η‖ ≤ a + b`. -/
theorem step_10_14_supported [∀ i, Fintype (loc i)]
    {R' : Matrix (Reg loc Λ × (Reg loc X × Reg loc X)) (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ}
    (hR : ActsOn hN X R') {φ η : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ} {a b : ℝ}
    (ha : vnorm (R' *ᵥ φ - η) ≤ a) (hb : vnorm (R'ᴴ *ᵥ η - φ) ≤ b) :
    ∃ V ∈ unitary (Matrix (Reg loc N × Reg loc X) (Reg loc N × Reg loc X) ℂ),
      vnorm (((V : Matrix _ _ ℂ) ⊗ₖ
        (1 : Matrix (Reg loc (Λ \ N) × Reg loc X) (Reg loc (Λ \ N) × Reg loc X) ℂ)).submatrix
          (splitN hN X) (splitN hN X) *ᵥ φ - η) ≤ a + b := by
  obtain ⟨M, rfl⟩ := hR
  exact step_10_14 _ M ha hb

variable {hN X} in
/-- D10.14. The operator `U' = (V ⊗ I)` in the coordinates of `splitN` is unitary. -/
theorem unitary_actsOn [∀ i, Fintype (loc i)]
    {V : Matrix (Reg loc N × Reg loc X) (Reg loc N × Reg loc X) ℂ}
    (hV : V ∈ unitary (Matrix (Reg loc N × Reg loc X) (Reg loc N × Reg loc X) ℂ)) :
    (V ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X) (Reg loc (Λ \ N) × Reg loc X) ℂ)).submatrix
        (splitN hN X) (splitN hN X) ∈
      unitary (Matrix (Reg loc Λ × (Reg loc X × Reg loc X))
        (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ) :=
  kronecker_one_submatrix_mem_unitary _ hV

end ActsOn

end AreaLaw
