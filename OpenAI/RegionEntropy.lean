import Arealaw.Subadditivity
import OpenAI.Embedding

/-!
# Region entropies of pure and mixed states

Three facts about the region entropies of a state on a finite tensor product, stated over an
arbitrary `RCLike` field.

* **Purity.**  For a pure state `|ψ⟩⟨ψ|` on `Λ` and `A ⊆ Λ`, `S(A) = S(Λ \ A)`.  The reduced
  matrices across the cut are `M Mᴴ` and `Mᵀ (Mᵀ)ᴴ` for the coefficient matrix
  `M x z = ψ (x, z)`; `M Mᴴ` and `Mᴴ M` share their nonzero spectrum, and the Shannon entropy
  of a spectrum ignores zeros.
* **Subadditivity over a family.**  `S(D ∪ ⋃_{i ∈ s} X_i) ≤ S(D) + ∑_{i ∈ s} S(X_i)` for
  pairwise disjoint regions `X_i`, each disjoint from `D`.
* **The chain rule.**  For an ordered family, `S(Y ∪ ⋃_{i ∈ s} X_i)` equals
  `S(Y) + ∑ S(X_i) - ∑ I(X_i : Y ∪ ⋃_{j ∈ s, j < i} X_j)`.  This is a telescoping identity of
  the definition of `mutualInfo` and needs no disjointness.

## Main definitions

* `OpenAI.coeffMatrix`: the coefficient matrix of a vector on `T` across the cut `S | T \ S`.

## Main statements

* `Arealaw.EE_transpose`: the entanglement entropy of a bipartite pure state is the same from
  either side.
* `OpenAI.regionEntropy_pureState_sdiff`: purity on regions.
* `Arealaw.MState.regionEntropy_union_le`: subadditivity over `𝕜`.
* `Arealaw.MState.regionEntropy_union_biUnion_le`: subadditivity over a finite family.
* `Arealaw.SubState.regionEntropy_union_biUnion`: the chain rule.

## Implementation notes

Subadditivity rests on `Arealaw.regionEntropy_union_le`, which is stated over `ℂ` because
Physlib's `Sᵥₙ_subadditivity` is; it reaches `𝕜` through `OpenAI.Embedding`.  Purity is proved
natively over `𝕜`.
-/

namespace Arealaw

open Matrix

/-! ## Spectra that agree away from zero -/

section Spectrum

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Shannon entropy of a family is the sum of `negMulLog` over its nonzero values. -/
theorem H_eq_sum_filter_ne_zero (p : ι → ℝ) :
    H p = (((Finset.univ.val.map p).filter (· ≠ 0)).map Real.negMulLog).sum := by
  rw [H_eq_multiset_sum]
  conv_lhs => rw [← Multiset.filter_add_not (· ≠ 0) (Finset.univ.val.map p)]
  rw [Multiset.map_add, Multiset.sum_add, add_eq_left]
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
  rw [not_not.1 (Multiset.mem_filter.1 hy).2, Real.negMulLog_zero]

/-- **The Shannon entropy ignores zeros**: two families with the same nonzero values, counted
with multiplicity, have the same entropy. -/
theorem H_eq_of_filter_ne_zero_eq {p : ι → ℝ} {q : κ → ℝ}
    (h : (Finset.univ.val.map p).filter (· ≠ 0) = (Finset.univ.val.map q).filter (· ≠ 0)) :
    H p = H q := by
  rw [H_eq_sum_filter_ne_zero, H_eq_sum_filter_ne_zero, h]

/-- `AB` and `BA` have the same nonzero characteristic roots, with multiplicity, for
rectangular `A` and `B`. -/
theorem roots_charpoly_mul_comm_filter_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).charpoly.roots.filter (· ≠ 0) = (B * A).charpoly.roots.filter (· ≠ 0) := by
  have h := congrArg (fun p : Polynomial R => p.roots.filter (· ≠ 0)) (charpoly_mul_comm' A B)
  have hz (n : ℕ) : (Multiset.replicate n (0 : R)).filter (· ≠ 0) = 0 :=
    Multiset.filter_eq_nil.2 fun a ha => by simp [Multiset.eq_of_mem_replicate ha]
  simpa [Polynomial.roots_mul, Polynomial.Monic.ne_zero, Matrix.charpoly_monic,
    Polynomial.X_ne_zero, pow_ne_zero, Multiset.nsmul_singleton, hz] using h

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] [DecidableEq κ]

/-- Two Hermitian matrices whose characteristic polynomials have the same nonzero roots have
the same spectral entropy, whatever their sizes. -/
theorem H_eigenvalues_eq_of_roots_charpoly_filter_eq {A : Matrix ι ι 𝕜} {B : Matrix κ κ 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly.roots.filter (· ≠ 0) = B.charpoly.roots.filter (· ≠ 0)) :
    H hA.eigenvalues = H hB.eigenvalues := by
  refine H_eq_of_filter_ne_zero_eq (Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_)
  rw [hA.roots_charpoly_eq_eigenvalues, hB.roots_charpoly_eq_eigenvalues] at h
  simpa [Multiset.filter_map, Multiset.map_map, Function.comp_def] using h

/-- Equal Hermitian matrices have equal spectral entropies; the Hermiticity proofs are
irrelevant. -/
theorem H_eigenvalues_congr {A B : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : H hA.eigenvalues = H hB.eigenvalues := by
  subst h; rfl

/-- **Purity across a cut**: the entanglement entropy of a bipartite pure state is the same
from either side, `S(ρ_A) = S(ρ_B)`, where `ρ_B = Mᵀ (Mᵀ)ᴴ`. -/
theorem EE_transpose (M : Matrix ι κ 𝕜) : EE Mᵀ = EE M := by
  refine H_eigenvalues_eq_of_roots_charpoly_filter_eq _ _ ?_
  rw [rhoA, rhoA, conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul,
    charpoly_transpose]
  exact roots_charpoly_mul_comm_filter_ne_zero _ _

omit [DecidableEq κ] in
/-- Relabelling the traced-out side of a bipartite pure state leaves its entanglement entropy
unchanged. -/
theorem EE_submatrix_id_equiv {μ : Type*} [Fintype μ] (M : Matrix ι κ 𝕜) (e : μ ≃ κ) :
    EE (M.submatrix id e) = EE M :=
  H_eigenvalues_congr _ _ (by
    rw [rhoA, rhoA, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id])

end Spectrum

/-! ## Subadditivity and the chain rule on regions -/

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U : Finset σ}

namespace SubState

/-- Equal pairs of regions have equal mutual information; the subset proofs are irrelevant. -/
theorem mutualInfo_congr (ρ : SubState (Reg loc U) 𝕜) {X X' Y Y' : Finset σ} (hXX : X = X')
    (hYY : Y = Y') (hX : X ⊆ U) (hY : Y ⊆ U) (hX' : X' ⊆ U) (hY' : Y' ⊆ U) :
    ρ.mutualInfo hX hY = ρ.mutualInfo hX' hY' := by
  subst hXX hYY; rfl

/-- **The chain rule for an ordered family**: adding the regions `X_i`, `i ∈ s`, to `Y` one at
a time in increasing order,
`S(Y ∪ ⋃_{i ∈ s} X_i) = S(Y) + ∑_{i ∈ s} S(X_i) - ∑_{i ∈ s} I(X_i : Y ∪ ⋃_{j ∈ s, j < i} X_j)`.
No disjointness is needed: the identity telescopes the definition of `mutualInfo`. -/
theorem regionEntropy_union_biUnion {ι : Type*} [LinearOrder ι] (ρ : SubState (Reg loc U) 𝕜)
    {Y : Finset σ} (hY : Y ⊆ U) (s : Finset ι) {X : ι → Finset σ} (hX : ∀ i, X i ⊆ U) :
    ρ.regionEntropy (Finset.union_subset hY (Finset.biUnion_subset.2 fun i _ => hX i) :
        Y ∪ s.biUnion X ⊆ U) =
      ρ.regionEntropy hY + ∑ i ∈ s, ρ.regionEntropy (hX i) -
        ∑ i ∈ s, ρ.mutualInfo (hX i)
          (Finset.union_subset hY (Finset.biUnion_subset.2 fun j _ => hX j) :
            Y ∪ (s.filter (· < i)).biUnion X ⊆ U) := by
  induction s using Finset.induction_on_max with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, add_zero, sub_zero]
    exact ρ.regionEntropy_congr (by simp) _ _
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has, Finset.sum_insert has]
    have hlt : (insert a s).filter (· < a) = s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      exact ⟨fun h => h.1.resolve_left (ne_of_lt h.2), fun hx => ⟨Or.inr hx, ha x hx⟩⟩
    have hs : ∀ i ∈ s, (insert a s).filter (· < i) = s.filter (· < i) := fun i hi => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (ha i hi).le)]
    rw [Finset.sum_congr rfl fun i hi => ρ.mutualInfo_congr rfl
      (congrArg (Y ∪ ·.biUnion X) (hs i hi)) (hX i)
      (Finset.union_subset hY (Finset.biUnion_subset.2 fun j _ => hX j)) (hX i)
      (Finset.union_subset hY (Finset.biUnion_subset.2 fun j _ => hX j)),
      ρ.mutualInfo_congr rfl (congrArg (Y ∪ ·.biUnion X) hlt) (hX a)
      (Finset.union_subset hY (Finset.biUnion_subset.2 fun j _ => hX j)) (hX a)
      (Finset.union_subset hY (Finset.biUnion_subset.2 fun j _ => hX j)), mutualInfo_def,
      ρ.regionEntropy_congr (show Y ∪ (insert a s).biUnion X = X a ∪ (Y ∪ s.biUnion X) by
        rw [Finset.biUnion_insert]; ac_rfl) _ (Finset.union_subset (hX a)
          (Finset.union_subset hY (Finset.biUnion_subset.2 fun j _ => hX j)))]
    linarith [ih]

end SubState

namespace MState

/-- **Subadditivity on regions** over any `RCLike` field: `S(X ∪ Y) ≤ S(X) + S(Y)` for
disjoint `X`, `Y`. -/
theorem regionEntropy_union_le (ρ : MState (Reg loc U) 𝕜) {X Y : Finset σ} (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.regionEntropy (Finset.union_subset hX hY) ≤ ρ.regionEntropy hX + ρ.regionEntropy hY := by
  -- Deviation (docs/charter-quantum-arealaw.md criterion 3, decision 4.3 in docs/oai265/Memory.md): proved over `ℂ` because
  -- `Arealaw.regionEntropy_union_le` (Physlib's `Sᵥₙ_subadditivity`) is `ℂ`-only; transferred
  -- by `OpenAI/Embedding.lean`.
  simpa using Arealaw.regionEntropy_union_le ρ.toComplex hd hX hY

/-- Mutual information of disjoint regions is nonnegative, over any `RCLike` field. -/
theorem mutualInfo_nonneg (ρ : MState (Reg loc U) 𝕜) {X Y : Finset σ} (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) : 0 ≤ ρ.mutualInfo hX hY :=
  sub_nonneg.2 (ρ.regionEntropy_union_le hd hX hY)

/-- **Subadditivity over a finite family**: `S(D ∪ ⋃_{i ∈ s} X_i) ≤ S(D) + ∑_{i ∈ s} S(X_i)`
for pairwise disjoint regions `X_i`, each disjoint from `D`. -/
theorem regionEntropy_union_biUnion_le {ι : Type*} (ρ : MState (Reg loc U) 𝕜) {D : Finset σ}
    (hD : D ⊆ U) (s : Finset ι) {X : ι → Finset σ} (hX : ∀ i, X i ⊆ U)
    (hDX : ∀ i ∈ s, Disjoint D (X i)) (hXX : (s : Set ι).PairwiseDisjoint X) :
    ρ.regionEntropy (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i) :
        D ∪ s.biUnion X ⊆ U) ≤
      ρ.regionEntropy hD + ∑ i ∈ s, ρ.regionEntropy (hX i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (ρ.regionEntropy_congr (show D ∪ (∅ : Finset ι).biUnion X = D by simp) _ hD).le.trans
      (by simp)
  | insert a s has ih =>
    have hDX' : ∀ i ∈ s, Disjoint D (X i) := fun i hi => hDX i (Finset.mem_insert_of_mem hi)
    have hXX' : (s : Set ι).PairwiseDisjoint X :=
      hXX.subset (by simp [Set.subset_insert])
    have hd : Disjoint (D ∪ s.biUnion X) (X a) :=
      Finset.disjoint_union_left.2 ⟨hDX a (Finset.mem_insert_self a s),
        (Finset.disjoint_biUnion_left _ _ _).2 fun i hi => hXX (by simp [hi]) (by simp)
          fun h => has (h ▸ hi)⟩
    rw [Finset.sum_insert has, ρ.regionEntropy_congr
      (show D ∪ (insert a s).biUnion X = (D ∪ s.biUnion X) ∪ X a by
        rw [Finset.biUnion_insert]; ac_rfl) _
      (Finset.union_subset (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i))
        (hX a))]
    linarith [ρ.regionEntropy_union_le hd
      (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i)) (hX a), ih hDX' hXX']

end MState

end Arealaw

/-! ## Purity on regions -/

namespace OpenAI

open Arealaw Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {S T : Finset σ}

section CoeffMatrix

omit [∀ i, Fintype (loc i)]

variable {α : Type*}

/-- The coefficient matrix of a vector `v` on `T` across the cut `S | T \ S`: the entry at
`(x, z)` is the amplitude of `v` on the glued configuration `x ∪ z`. -/
def coeffMatrix (S : Finset σ) (v : Reg loc T → α) : Matrix (Reg loc S) (Reg loc (T \ S)) α :=
  of fun x z => v (glue x z)

@[simp] theorem coeffMatrix_apply (v : Reg loc T → α) (x : Reg loc S) (z : Reg loc (T \ S)) :
    coeffMatrix S v x z = v (glue x z) := rfl

@[simp] theorem coeffMatrix_smul {R : Type*} [SMul R α] (c : R) (v : Reg loc T → α) :
    coeffMatrix S (c • v) = c • coeffMatrix S v := rfl

end CoeffMatrix

/-- The reduced matrix of `|ψ⟩⟨ψ|` on `S ⊆ T` is `M Mᴴ` for the coefficient matrix `M` of `ψ`
across the cut `S | T \ S`. -/
theorem ptrace_vecMulVec_star (h : S ⊆ T) (ψ : Reg loc T → 𝕜) :
    ptrace h (vecMulVec ψ (star ψ)) = rhoA (coeffMatrix S ψ) := by
  ext x y
  simp [ptrace, rhoA, mul_apply, vecMulVec_apply]

variable [∀ i, DecidableEq (loc i)]

/-- The entropy of a region `S ⊆ T` of a pure state on `T` is the entanglement entropy of its
coefficient matrix across the cut `S | T \ S`. -/
theorem regionEntropy_pureState (h : S ⊆ T) (ψ : Reg loc T → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (pureState ψ hψ).regionEntropy h =
      EE (coeffMatrix S ψ) := by
  rw [SubState.regionEntropy_def, SubState.entropy, vonNeumann_eq_H, EE]
  exact H_eigenvalues_congr _ _ (ptrace_vecMulVec_star h ψ)

/-- **Purity on regions**: a pure state on `Λ` has the same entropy on `A ⊆ Λ` and on its
complement `Λ \ A`. -/
theorem regionEntropy_pureState_sdiff {Λ A : Finset σ} (hA : A ⊆ Λ) (ψ : Reg loc Λ → 𝕜)
    (hψ : star ψ ⬝ᵥ ψ = 1) :
    (pureState ψ hψ).regionEntropy (Finset.sdiff_subset : Λ \ A ⊆ Λ) =
      (pureState ψ hψ).regionEntropy hA := by
  rw [regionEntropy_pureState, regionEntropy_pureState]
  refine (congrArg EE (?_ : _ = (coeffMatrix A ψ)ᵀ.submatrix
    id (regEquivOfEq (Finset.sdiff_sdiff_eq_self hA)))).trans
    ((EE_submatrix_id_equiv _ _).trans (EE_transpose _))
  ext z w
  simp only [coeffMatrix_apply, submatrix_apply, transpose_apply, id, regEquivOfEq_apply]
  congr 1
  funext j
  by_cases hj : (j : σ) ∈ A <;> simp [glue, restr, hj, j.2]

end OpenAI
