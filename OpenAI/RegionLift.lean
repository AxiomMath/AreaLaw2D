import OpenAI.CutTransport

/-!
# Operators and pure states on a subregion

Fix a region `U` of sites, a subregion `T ⊆ U`, and a vector `ξ` on the configurations of `U`.
An operator `K` on `T` acts on `U` as `K ⊗ 1`, `Arealaw.extendId`, and the marginal of `ξ` on
`T` is `ρ_{ξ,T} = Tr_{U \ T} |ξ⟩⟨ξ|`, `Arealaw.ptrace` of the rank-one matrix.  Expectations of
lifted operators are traces against the marginal, `⟨ξ, (K ⊗ 1) ξ⟩ = Tr (ρ_{ξ,T} K)`, and so are
their norms and mutual inner products.  Hence an invertible `K` commuting with `ρ_{ξ,T}` can be
removed from a conjugated expectation by cyclicity of the trace: this is the descending trace
argument of the proof of Lemma 3.2 of [OAI265].  Operators on disjoint subregions commute, and
for disjoint `X` and `T` the lift of a product `A ⊗ B` on `X ∪ T` is the product of the lifts:
the trial filters `|uᵢ⟩⟨uᵢ| ⊗ Mⱼ` of the same proof.

## Main definitions

* `OpenAI.crossingTerms`: the terms whose support meets both sides of a cut.
* `OpenAI.extendIdₗ`: `Arealaw.extendId` as a linear map.

## Main statements

* `OpenAI.inner_toEuclideanLin_extendId`: `⟨ξ, (K ⊗ 1) ξ⟩ = Tr (ρ_{ξ,T} K)`.
* `OpenAI.norm_toEuclideanLin_extendId_sq`: `‖(K ⊗ 1) ξ‖² = Re Tr (ρ_{ξ,T} Kᴴ K)`.
* `OpenAI.inner_toEuclideanLin_extendId_conj`: the trace argument.
* `OpenAI.IsSupportedOn.commute`: operators supported on disjoint regions commute.
* `OpenAI.extendId_kronUnion`: `(A ⊗ B) ⊗ 1 = (A ⊗ 1) (B ⊗ 1)` for disjoint regions.
* `OpenAI.regionEntropy_pureState_eq_sum_negMulLog_ptrace`: the entropy of the marginal of a unit
  vector.

## Implementation notes

Ported from QICLean at commit `32a5a1a8` (Apache 2.0): `QICLean/Entropy/LocalLift.lean`, the
first half of `QICLean/Entropy/RegionUnion.lean`, and the region layer of
`QICLean/Entropy/SupportedMarginalTails.lean` they rest on.  QICLean works on the full
configuration space `∀ v, Fin (n v)` of a finite site set, with regions cut out by
`Equiv.piEquivPiSubtypeProd`.  Here sites carry arbitrary local types `loc`, the ambient space
is a region `U`, and a subregion is `T ⊆ U`: `localLift T K` becomes `extendId hT K`,
`regionState T ξ` becomes `ptrace hT (vecMulVec ξ (star ξ))`, `regionEntropy T ξ` becomes the
region entropy of `pureState ξ`, `IsSupportedOn` is `OpenAI.IsSupportedOn`, and
`regionUnionEquiv` is `Arealaw.unionEquiv`.  The lift of a Kronecker product along
`regionUnionEquiv` is `Arealaw.kronUnion`.  QICLean's `supportDim n D` is
`Fintype.card (Reg loc D)`, computed by `Arealaw.card_reg`.

QICLean states these facts over `ℂ`; they are stated here over any `RCLike` field, with vectors
in `EuclideanSpace 𝕜 (Reg loc U)`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.2, proof of Lemma 3.2.
-/

namespace OpenAI

open Arealaw Matrix
open scoped InnerProductSpace ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Expectations as traces -/

section Euclidean

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The expectation of `Y` in `ψ` is the trace of `Y` against `|ψ⟩⟨ψ|`. -/
theorem inner_toEuclideanLin_eq_trace (Y : Matrix m m 𝕜) (ψ : EuclideanSpace 𝕜 m) :
    ⟪ψ, toEuclideanLin Y ψ⟫_𝕜 =
      (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) * Y).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, WithLp.ofLp_toLp, trace_mul_comm,
    mul_vecMulVec, trace_vecMulVec]

/-- `⟨Xψ, Yψ⟩ = ⟨ψ, XᴴY ψ⟩`. -/
theorem inner_toEuclideanLin_toEuclideanLin (X Y : Matrix m m 𝕜) (ψ : EuclideanSpace 𝕜 m) :
    ⟪toEuclideanLin X ψ, toEuclideanLin Y ψ⟫_𝕜 = ⟪ψ, toEuclideanLin (Xᴴ * Y) ψ⟫_𝕜 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, star_mulVec,
    ← mulVec_mulVec]
  rw [dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]

/-- `‖Yψ‖² = Re ⟨ψ, YᴴY ψ⟩`. -/
theorem norm_toEuclideanLin_sq (Y : Matrix m m 𝕜) (ψ : EuclideanSpace 𝕜 m) :
    ‖toEuclideanLin Y ψ‖ ^ 2 = RCLike.re ⟪ψ, toEuclideanLin (Yᴴ * Y) ψ⟫_𝕜 := by
  rw [← inner_toEuclideanLin_toEuclideanLin, @norm_sq_eq_re_inner 𝕜]

omit [DecidableEq m] in
/-- A unit vector of `EuclideanSpace` satisfies the normalization `star ξ ⬝ᵥ ξ = 1` of
`OpenAI.pureState`. -/
theorem star_dotProduct_self_eq_one_of_norm_eq_one {ξ : EuclideanSpace 𝕜 m} (hξ : ‖ξ‖ = 1) :
    star (WithLp.ofLp ξ) ⬝ᵥ WithLp.ofLp ξ = 1 :=
  (norm_toLp_eq_one_iff _).1 hξ

end Euclidean

/-! ## Crossing terms -/

section Crossing

variable {σ : Type*} [DecidableEq σ] {ι : Type*} [Fintype ι]

/-- The terms whose support `D i` meets both `B` and its complement. -/
def crossingTerms (D : ι → Finset σ) (B : Finset σ) : Finset ι :=
  Finset.univ.filter fun i => (D i ∩ B).Nonempty ∧ (D i \ B).Nonempty

theorem mem_crossingTerms {D : ι → Finset σ} {B : Finset σ} {i : ι} :
    i ∈ crossingTerms D B ↔ (D i ∩ B).Nonempty ∧ (D i \ B).Nonempty := by
  simp [crossingTerms]

/-- A term is not crossing exactly when its support lies on one side of the cut. -/
theorem notMem_crossingTerms_iff {D : ι → Finset σ} {B : Finset σ} {i : ι} :
    i ∉ crossingTerms D B ↔ D i ⊆ B ∨ Disjoint (D i) B := by
  rw [mem_crossingTerms, ← Finset.not_disjoint_iff_nonempty_inter, Finset.nonempty_iff_ne_empty,
    Ne, Finset.sdiff_eq_empty_iff_subset]
  tauto

end Crossing

/-! ## Lifts of operators on a subregion -/

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T U : Finset σ}

section Lift

omit [∀ i, Fintype (loc i)]

/-- Matrix elements of `K ⊗ 1`: `K` on the subregion when the configurations agree off it,
zero otherwise. -/
theorem extendId_apply (hT : T ⊆ U) (K : Matrix (Reg loc T) (Reg loc T) 𝕜) (w w' : Reg loc U) :
    extendId hT K w w' =
      if restr (S := U \ T) Finset.sdiff_subset w = restr Finset.sdiff_subset w' then
        K (restr hT w) (restr hT w')
      else 0 := rfl

/-- `Arealaw.extendId` as a linear map. -/
noncomputable def extendIdₗ (hT : T ⊆ U) :
    Matrix (Reg loc T) (Reg loc T) 𝕜 →ₗ[𝕜] Matrix (Reg loc U) (Reg loc U) 𝕜 where
  toFun := extendId hT
  map_add' := extendId_add hT
  map_smul' := extendId_smul hT

@[simp] theorem extendIdₗ_apply (hT : T ⊆ U) (K : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    extendIdₗ hT K = extendId hT K := rfl

@[simp] theorem extendId_neg (hT : T ⊆ U) (K : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    extendId hT (-K) = -extendId hT K :=
  map_neg (extendIdₗ hT) K

@[simp] theorem extendId_sub (hT : T ⊆ U) (K L : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    extendId hT (K - L) = extendId hT K - extendId hT L :=
  map_sub (extendIdₗ hT) K L

/-- Support is monotone in the region. -/
theorem IsSupportedOn.mono {hS : S ⊆ U} {X : Matrix (Reg loc U) (Reg loc U) 𝕜}
    (hX : IsSupportedOn hS X) (hST : S ⊆ T) (hT : T ⊆ U) : IsSupportedOn hT X := by
  obtain ⟨B, rfl⟩ := hX
  exact ⟨extendId hST B, (extendId_extendId hST hT B).symm⟩

end Lift

/-- The lift of `K⁻¹` is a right inverse of the lift of an invertible `K`. -/
theorem extendId_mul_extendId_inv (hT : T ⊆ U) {K : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hK : IsUnit K.det) : extendId hT K * extendId hT K⁻¹ = 1 := by
  rw [← extendId_mul, mul_nonsing_inv _ hK, extendId_one]

/-- The lift of `K⁻¹` is a left inverse of the lift of an invertible `K`. -/
theorem extendId_inv_mul_extendId (hT : T ⊆ U) {K : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hK : IsUnit K.det) : extendId hT K⁻¹ * extendId hT K = 1 := by
  rw [← extendId_mul, nonsing_inv_mul _ hK, extendId_one]

/-- **Operators supported on disjoint regions commute.** -/
theorem IsSupportedOn.commute {hS : S ⊆ U} {hT : T ⊆ U} {X Y : Matrix (Reg loc U) (Reg loc U) 𝕜}
    (hX : IsSupportedOn hS X) (hY : IsSupportedOn hT Y) (hd : Disjoint S T) : Commute X Y := by
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨C, rfl⟩ := hY
  exact commute_extendId_extendId hS hT hd B C

/-! ## Marginals of a vector -/

section Marginal

variable (hT : T ⊆ U) (ξ : EuclideanSpace 𝕜 (Reg loc U))

omit [∀ i, DecidableEq (loc i)] in
/-- The marginal `ρ_{ξ,T}` of a vector is positive semidefinite. -/
theorem posSemidef_ptrace_vecMulVec_star :
    (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))).PosSemidef :=
  posSemidef_ptrace hT (posSemidef_vecMulVec_self_star _)

omit [∀ i, DecidableEq (loc i)] in
/-- The marginal `ρ_{ξ,T}` of a vector is Hermitian. -/
theorem isHermitian_ptrace_vecMulVec_star :
    (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))).IsHermitian :=
  (posSemidef_ptrace_vecMulVec_star hT ξ).isHermitian

omit [∀ i, DecidableEq (loc i)] in
/-- The marginal `ρ_{ξ,T}` has trace `‖ξ‖²`. -/
theorem trace_ptrace_vecMulVec_star :
    (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))).trace =
      ((‖ξ‖ ^ 2 : ℝ) : 𝕜) := by
  rw [trace_ptrace, trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

omit [∀ i, DecidableEq (loc i)] in
/-- The marginal of `c ξ` is `|c|²` times the marginal of `ξ`. -/
theorem ptrace_vecMulVec_star_smul (c : 𝕜) :
    ptrace hT (vecMulVec (WithLp.ofLp (c • ξ)) (star (WithLp.ofLp (c • ξ)))) =
      ((‖c‖ ^ 2 : ℝ) : 𝕜) • ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))) := by
  rw [← ptrace_smul]
  congr 1
  ext x y
  simp only [WithLp.ofLp_smul, vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_smul,
    smul_eq_mul, Matrix.smul_apply, RCLike.ofReal_pow, ← RCLike.mul_conj, RCLike.star_def]
  ring

/-- **Expectations of lifted operators**: `⟨ξ, (K ⊗ 1) ξ⟩ = Tr (ρ_{ξ,T} K)`. -/
theorem inner_toEuclideanLin_extendId (K : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ⟪ξ, toEuclideanLin (extendId hT K) ξ⟫_𝕜 =
      (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))) * K).trace := by
  rw [inner_toEuclideanLin_eq_trace, trace_ptrace_mul]

/-- Inner products of lifted operators applied to a vector:
`⟨(K ⊗ 1) ξ, (L ⊗ 1) ξ⟩ = Tr (ρ_{ξ,T} Kᴴ L)`. -/
theorem inner_toEuclideanLin_extendId_toEuclideanLin_extendId
    (K L : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ⟪toEuclideanLin (extendId hT K) ξ, toEuclideanLin (extendId hT L) ξ⟫_𝕜 =
      (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))) * (Kᴴ * L)).trace := by
  rw [inner_toEuclideanLin_toEuclideanLin, ← extendId_conjTranspose, ← extendId_mul,
    inner_toEuclideanLin_extendId]

/-- Norms of lifted operators applied to a vector: `‖(K ⊗ 1) ξ‖² = Re Tr (ρ_{ξ,T} Kᴴ K)`. -/
theorem norm_toEuclideanLin_extendId_sq (K : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ‖toEuclideanLin (extendId hT K) ξ‖ ^ 2 =
      RCLike.re (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))) *
        (Kᴴ * K)).trace := by
  rw [@norm_sq_eq_re_inner 𝕜, inner_toEuclideanLin_extendId_toEuclideanLin_extendId]

/-- **The trace argument**: if `K` is invertible and commutes with the marginal `ρ_{ξ,T}`,
conjugating a lifted observable by the lift of `K` does not change its expectation in `ξ`. -/
theorem inner_toEuclideanLin_extendId_conj {K : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hK : IsUnit K.det)
    (hcomm : Commute K (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))))
    (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ⟪ξ, toEuclideanLin (extendId hT K * extendId hT A * extendId hT K⁻¹) ξ⟫_𝕜 =
      ⟪ξ, toEuclideanLin (extendId hT A) ξ⟫_𝕜 := by
  have h : K⁻¹ * ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))) * K =
      ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))) := by
    rw [Matrix.mul_assoc, ← hcomm.eq, ← Matrix.mul_assoc, nonsing_inv_mul _ hK, Matrix.one_mul]
  rw [← extendId_mul, ← extendId_mul, inner_toEuclideanLin_extendId,
    inner_toEuclideanLin_extendId, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

/-- The trace argument for an arbitrary operator supported on the subregion. -/
theorem IsSupportedOn.inner_toEuclideanLin_conj {K : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hK : IsUnit K.det)
    (hcomm : Commute K (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))))
    {Y : Matrix (Reg loc U) (Reg loc U) 𝕜} (hY : IsSupportedOn hT Y) :
    ⟪ξ, toEuclideanLin (extendId hT K * Y * extendId hT K⁻¹) ξ⟫_𝕜 =
      ⟪ξ, toEuclideanLin Y ξ⟫_𝕜 := by
  obtain ⟨A, rfl⟩ := hY
  exact inner_toEuclideanLin_extendId_conj hT ξ hK hcomm A

/-- **Entropy of the marginal of a unit vector**: the region entropy of the pure state of `ξ`
is the von Neumann entropy of `ρ_{ξ,T}`. -/
theorem regionEntropy_pureState_eq_vonNeumann (hξ : star (WithLp.ofLp ξ) ⬝ᵥ WithLp.ofLp ξ = 1)
    (hρ : (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))).IsHermitian) :
    (pureState (WithLp.ofLp ξ) hξ).toSubState.regionEntropy hT = vonNeumann hρ :=
  rfl

/-- The region entropy of the pure state of `ξ` is `∑ -pₓ log pₓ` over the eigenvalues `pₓ`
of `ρ_{ξ,T}`. -/
theorem regionEntropy_pureState_eq_sum_negMulLog_ptrace
    (hξ : star (WithLp.ofLp ξ) ⬝ᵥ WithLp.ofLp ξ = 1)
    (hρ : (ptrace hT (vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)))).IsHermitian) :
    (pureState (WithLp.ofLp ξ) hξ).toSubState.regionEntropy hT =
      ∑ x, Real.negMulLog (hρ.eigenvalues x) :=
  vonNeumann_eq_H hρ

end Marginal

/-! ## Lifts on a disjoint union -/

section Union

variable {A B : Finset σ}

section
omit [∀ i, Fintype (loc i)]

omit [DecidableEq σ] [∀ i, DecidableEq (loc i)] in
/-- Restrictions to equal subregions see the same coincidences. -/
theorem restr_eq_restr_iff_of_eq {S' : Finset σ} (hSS : S = S') (hS : S ⊆ T) (hS' : S' ⊆ T)
    (w w' : Reg loc T) : restr hS w = restr hS w' ↔ restr hS' w = restr hS' w' := by
  subst hSS; rfl

/-- `M ⊗ 1` on a disjoint union is the extension of `M` by the identity. -/
theorem kronUnion_one (hd : Disjoint A B) (M : Matrix (Reg loc A) (Reg loc A) 𝕜) :
    kronUnion hd M 1 = extendId Finset.subset_union_left M := by
  ext w w'
  simp only [kronUnion, extendId, of_apply, unionEquiv_apply, one_apply,
    restr_eq_restr_iff_of_eq (Finset.union_sdiff_cancel_left hd).symm Finset.subset_union_right
      Finset.sdiff_subset]
  split_ifs <;> simp

/-- `1 ⊗ N` on a disjoint union is the extension of `N` by the identity. -/
theorem one_kronUnion (hd : Disjoint A B) (N : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    kronUnion hd 1 N = extendId Finset.subset_union_right N := by
  ext w w'
  simp only [kronUnion, extendId, of_apply, unionEquiv_apply, one_apply,
    restr_eq_restr_iff_of_eq (Finset.union_sdiff_cancel_right hd).symm Finset.subset_union_left
      Finset.sdiff_subset]
  split_ifs <;> simp

end

omit [∀ i, DecidableEq (loc i)] in
/-- Kronecker products on a disjoint union multiply factorwise. -/
theorem kronUnion_mul_kronUnion (hd : Disjoint A B) (M M' : Matrix (Reg loc A) (Reg loc A) 𝕜)
    (N N' : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    kronUnion hd M N * kronUnion hd M' N' = kronUnion hd (M * M') (N * N') := by
  rw [kronUnion_eq_submatrix, kronUnion_eq_submatrix, kronUnion_eq_submatrix,
    submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

/-- `M ⊗ N` on a disjoint union is the product of the extensions of `M` and `N`. -/
theorem kronUnion_eq_extendId_mul_extendId (hd : Disjoint A B)
    (M : Matrix (Reg loc A) (Reg loc A) 𝕜) (N : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    kronUnion hd M N =
      extendId Finset.subset_union_left M * extendId Finset.subset_union_right N := by
  rw [← kronUnion_one hd, ← one_kronUnion hd, kronUnion_mul_kronUnion, Matrix.mul_one,
    Matrix.one_mul]

/-- **Lifts of product operators on a disjoint union**: for disjoint `A, B ⊆ U`,
`(M ⊗ N) ⊗ 1 = (M ⊗ 1) (N ⊗ 1)`. -/
theorem extendId_kronUnion (hA : A ⊆ U) (hB : B ⊆ U) (hd : Disjoint A B)
    (M : Matrix (Reg loc A) (Reg loc A) 𝕜) (N : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    extendId (Finset.union_subset hA hB) (kronUnion hd M N) = extendId hA M * extendId hB N := by
  rw [kronUnion_eq_extendId_mul_extendId hd, extendId_mul, extendId_extendId, extendId_extendId]

end Union

end OpenAI
