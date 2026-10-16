import Arealaw.OpNorm
import OpenAI.CutTerms
import OpenAI.FinSum
import OpenAI.Statements
import OpenAI.ZeroBoundary

/-!
# Region operators across a cut

A cut `B ⊆ U` of a region splits its configurations as `Reg loc B × Reg loc (U \ B)` along
`Arealaw.glueEquiv`.  Transported along this splitting, the region partial trace onto `B` is
the binary right partial trace, an operator supported on `D` with `D ⊆ B` or `D` disjoint
from `B` acts on one tensor factor, and every operator `X` supported on `D` is a sum of at most
`(dim D)²` products `c ⊗ d` with `‖c‖ ‖d‖ ≤ ‖X‖`.  These are the two shapes of a term in
Lemma 3.1 of [OAI265], `OpenAI.IsOneSided` and `OpenAI.HasProductDecomposition`.

## Main statements

* `ptrace_eq_traceRight_submatrix_glueEquiv`: the region partial trace is `Matrix.traceRight`.
* `IsSupportedOn.isOneSided_submatrix_glueEquiv`: a term on one side of the cut is one-sided.
* `IsSupportedOn.hasProductDecomposition_submatrix_glueEquiv`: every term decomposes into at
  most `(dim D)²` products.
* `piProd_submatrix_glueEquiv`: a product operator on `U` splits as a Kronecker product.
* `l2_opNorm_extendId`: extension by the identity is isometric for the L2 operator norm.

## Implementation notes

The decomposition expands `X = extendId Y` in the matrix units of `Y`.  Each extended matrix
unit is a product operator, with a matrix unit at the sites of `D` and the identity elsewhere,
and so splits across the cut into a product of two operators of the same form, each the
extension of a matrix unit and hence of norm at most `1`.  The coefficient is an entry of `Y`,
bounded by `‖Y‖ = ‖X‖`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.1, Lemma 3.1.
-/

namespace OpenAI

open Arealaw Matrix
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U B D : Finset σ}

/-! ## The partial trace across a cut -/

section PTrace
omit [∀ i, DecidableEq (loc i)]

/-- **The region partial trace is the right partial trace** across the cut `B | U \ B`. -/
theorem ptrace_eq_traceRight_submatrix_glueEquiv (hB : B ⊆ U)
    (M : Matrix (Reg loc U) (Reg loc U) 𝕜) :
    ptrace hB M = traceRight (M.submatrix (glueEquiv hB) (glueEquiv hB)) :=
  rfl

end PTrace

/-! ## Product operators across a cut -/

section PiProd
omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

/-- A product operator on `U` is, across the cut `B | U \ B`, the Kronecker product of its
products over `B` and over `U \ B`. -/
theorem piProd_submatrix_glueEquiv {R : Type*} [CommSemiring R] (hB : B ⊆ U)
    (m : ∀ i : U, Matrix (loc i) (loc i) R) :
    (piProd m).submatrix (glueEquiv hB) (glueEquiv hB) =
      piProd (fun i : B => m ⟨i, hB i.2⟩) ⊗ₖ
        piProd (fun i : ↥(U \ B) => m ⟨i, Finset.sdiff_subset i.2⟩) := by
  ext ⟨x, z⟩ ⟨x', z'⟩
  simp only [submatrix_apply, glueEquiv_apply, piProd, of_apply, kroneckerMap_apply]
  have hsplit : ∀ i : U, m i (glue x z i) (glue x' z' i) =
      if hi : i.1 ∈ B then m i (x ⟨i, hi⟩) (x' ⟨i, hi⟩)
      else m i (z ⟨i, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩) (z' ⟨i, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩) :=
    fun i => by by_cases hi : i.1 ∈ B <;> simp [glue, hi]
  rw [Fintype.prod_congr _ _ hsplit, Fintype.prod_dite]
  congr 1
  · exact Fintype.prod_equiv (Equiv.subtypeSubtypeEquivSubtype fun hx => hB hx) _ _
      fun _ => rfl
  · exact Fintype.prod_equiv
      { toFun := fun a => ⟨a.1, Finset.mem_sdiff.2 ⟨a.1.2, a.2⟩⟩
        invFun := fun j => ⟨⟨j, (Finset.mem_sdiff.1 j.2).1⟩, (Finset.mem_sdiff.1 j.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ fun _ => rfl

end PiProd

/-! ## Extension by the identity across a cut -/

section Extend
omit [∀ i, Fintype (loc i)]

/-- An operator extended from `B` acts on the first factor of the cut `B | U \ B`. -/
theorem extendId_submatrix_glueEquiv (hB : B ⊆ U) (A : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    (extendId hB A).submatrix (glueEquiv hB) (glueEquiv hB) = A ⊗ₖ (1 : Matrix _ _ 𝕜) := by
  rw [extendId_eq_kronecker, submatrix_submatrix]
  simp

omit [∀ i, DecidableEq (loc i)] in
/-- Restricting a configuration glued from `x` on `B` to `U \ (U \ B) = B` returns `x`. -/
theorem restr_sdiff_sdiff_glue (hB : B ⊆ U) (x : Reg loc B) (z : Reg loc (U \ B)) :
    restr (S := U \ (U \ B)) Finset.sdiff_subset (glue x z) =
      regEquivOfEq (Finset.sdiff_sdiff_eq_self hB).symm x := by
  funext j
  have hj : (j : σ) ∈ B := by simpa [Finset.sdiff_sdiff_eq_self hB] using j.2
  simp [restr, glue, hj, Finset.restrict₂]

/-- An operator extended from `U \ B` acts on the second factor of the cut `B | U \ B`. -/
theorem extendId_sdiff_submatrix_glueEquiv (hB : B ⊆ U)
    (A : Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) 𝕜) :
    (extendId (Finset.sdiff_subset : U \ B ⊆ U) A).submatrix (glueEquiv hB) (glueEquiv hB) =
      (1 : Matrix (Reg loc B) (Reg loc B) 𝕜) ⊗ₖ A := by
  ext ⟨x, z⟩ ⟨x', z'⟩
  simp only [submatrix_apply, glueEquiv_apply, extendId, of_apply, kroneckerMap_apply,
    restr_sdiff_sdiff_glue hB, (regEquivOfEq _).injective.eq_iff, restr_glue_compl, one_apply]
  split_ifs <;> simp

end Extend

/-! ## Norms of extended operators -/

section Norm

/-- Extension by the identity does not increase the L2 operator norm. -/
theorem l2_opNorm_extendId_le {S T : Finset σ} (h : S ⊆ T)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) : ‖extendId h A‖ ≤ ‖A‖ := by
  rw [extendId_eq_kronecker, l2_opNorm_submatrix]
  exact l2_opNorm_kronecker_one_le A

/-- **Extension by the identity is isometric** for the L2 operator norm.  The added region
must carry a configuration: if `Reg loc (T \ S)` is empty, every operator on `T` is `0`. -/
theorem l2_opNorm_extendId {S T : Finset σ} [Nonempty (Reg loc (T \ S))] (h : S ⊆ T)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) : ‖extendId h A‖ = ‖A‖ := by
  refine le_antisymm (l2_opNorm_extendId_le h A) ?_
  obtain ⟨z⟩ := ‹Nonempty (Reg loc (T \ S))›
  have hA : A = (extendId h A).submatrix (fun x => glue x z) (fun x => glue x z) := by
    ext x y
    simp
  conv_lhs => rw [hA]
  exact l2_opNorm_submatrix_le _ (glue_left_injective h z) (glue_left_injective h z)

/-- The product operator on `T` that is a matrix unit at the sites of `S` and the identity
elsewhere is a contraction. -/
theorem l2_opNorm_piProd_dite_single_le (S T : Finset σ) (x y : Reg loc S) :
    ‖piProd (fun i : T => if hi : (i : σ) ∈ S then
      (single (x ⟨i, hi⟩) (y ⟨i, hi⟩) 1 : Matrix (loc i) (loc i) 𝕜) else 1)‖ ≤ 1 := by
  have hext : piProd (fun i : T => if hi : (i : σ) ∈ S then
      (single (x ⟨i, hi⟩) (y ⟨i, hi⟩) 1 : Matrix (loc i) (loc i) 𝕜) else 1) =
      extendId (Finset.inter_subset_right : S ∩ T ⊆ T)
        (single (restr Finset.inter_subset_left x) (restr Finset.inter_subset_left y) 1) := by
    rw [single_eq_piProd, extendId_piProd]
    congr 1
    funext i
    by_cases hi : (i : σ) ∈ S
    · rw [dif_pos hi, dif_pos (Finset.mem_inter.2 ⟨hi, i.2⟩)]
      rfl
    · rw [dif_neg hi, dif_neg fun h => hi (Finset.mem_inter.1 h).1]
  rw [hext]
  exact (l2_opNorm_extendId_le _ _).trans (by simp)

end Norm

/-! ## Terms across a cut -/

section OneSided
omit [∀ i, Fintype (loc i)]

/-- An extended matrix unit splits across the cut `B | U \ B` as a Kronecker product of
product operators, each a matrix unit on its sites in `D` and the identity elsewhere. -/
theorem extendId_single_submatrix_glueEquiv (hB : B ⊆ U) (hDU : D ⊆ U) (x y : Reg loc D) :
    (extendId hDU (single x y (1 : 𝕜))).submatrix (glueEquiv hB) (glueEquiv hB) =
      piProd (fun i : B => if hi : (i : σ) ∈ D then single (x ⟨i, hi⟩) (y ⟨i, hi⟩) 1
        else 1) ⊗ₖ
      piProd (fun i : ↥(U \ B) => if hi : (i : σ) ∈ D then single (x ⟨i, hi⟩) (y ⟨i, hi⟩) 1
        else 1) := by
  rw [single_eq_piProd, extendId_piProd, piProd_submatrix_glueEquiv]

/-- **A term on one side of the cut is one-sided**: an operator supported on `D`, with `D ⊆ B`
or `D` disjoint from `B`, acts on a single factor of `B | U \ B`. -/
theorem IsSupportedOn.isOneSided_submatrix_glueEquiv (hB : B ⊆ U) (hDU : D ⊆ U)
    {X : Matrix (Reg loc U) (Reg loc U) 𝕜} (hX : IsSupportedOn hDU X)
    (hD : D ⊆ B ∨ Disjoint D B) :
    IsOneSided (X.submatrix (glueEquiv hB) (glueEquiv hB)) := by
  obtain ⟨Y, rfl⟩ := hX
  rcases hD with hD | hD
  · refine Or.inl ⟨extendId hD Y, ?_⟩
    rw [← extendId_submatrix_glueEquiv hB, extendId_extendId]
  · have hD' : D ⊆ U \ B := fun i hi =>
      Finset.mem_sdiff.2 ⟨hDU hi, Finset.disjoint_left.1 hD hi⟩
    refine Or.inr ⟨extendId hD' Y, ?_⟩
    rw [← extendId_sdiff_submatrix_glueEquiv hB, extendId_extendId]

end OneSided

/-- **Product decomposition of a crossing term**: an operator `X` supported on `D` is, across
the cut `B | U \ B`, a sum of at most `(dim D)²` products `c ⊗ d` with `‖c‖ ‖d‖ ≤ ‖X‖`. -/
theorem IsSupportedOn.hasProductDecomposition_submatrix_glueEquiv (hB : B ⊆ U) (hDU : D ⊆ U)
    {X : Matrix (Reg loc U) (Reg loc U) 𝕜} (hX : IsSupportedOn hDU X) :
    HasProductDecomposition (X.submatrix (glueEquiv hB) (glueEquiv hB)) ‖X‖
      (Fintype.card (Reg loc D) ^ 2) := by
  obtain ⟨Y, rfl⟩ := hX
  by_cases hU : IsEmpty (Reg loc U)
  · refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, ?_, fun a => a.elim0⟩
    ext p
    exact (hU.false (glueEquiv hB p)).elim
  obtain ⟨w⟩ := not_isEmpty_iff.1 hU
  have : Nonempty (Reg loc (U \ D)) := ⟨restr Finset.sdiff_subset w⟩
  let c : Reg loc D × Reg loc D → Matrix (Reg loc B) (Reg loc B) 𝕜 := fun p =>
    Y p.1 p.2 • piProd (fun i : B => if hi : (i : σ) ∈ D then
      single (p.1 ⟨i, hi⟩) (p.2 ⟨i, hi⟩) 1 else 1)
  let d : Reg loc D × Reg loc D → Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) 𝕜 := fun p =>
    piProd (fun i : ↥(U \ B) => if hi : (i : σ) ∈ D then
      single (p.1 ⟨i, hi⟩) (p.2 ⟨i, hi⟩) 1 else 1)
  let e := Fintype.equivFin (Reg loc D × Reg loc D)
  refine ⟨Fintype.card (Reg loc D × Reg loc D), fun a => c (e.symm a), fun a => d (e.symm a),
    by rw [Fintype.card_prod, sq], ?_, fun a => ?_⟩
  · rw [Equiv.sum_comp e.symm (fun p => c p ⊗ₖ d p), Fintype.sum_prod_type]
    conv_lhs => rw [matrix_eq_sum_single Y]
    simp only [extendId_sum, submatrix_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show single x y (Y x y) = Y x y • single x y (1 : 𝕜) by
      rw [smul_single, smul_eq_mul, mul_one], extendId_smul]
    exact (congrArg (fun A : Matrix (Reg loc B × Reg loc (U \ B)) _ 𝕜 => Y x y • A)
      (extendId_single_submatrix_glueEquiv hB hDU x y)).trans
      (smul_kronecker _ _ _).symm
  · calc ‖c (e.symm a)‖ * ‖d (e.symm a)‖
        ≤ ‖Y (e.symm a).1 (e.symm a).2‖ * 1 * 1 := by
          refine mul_le_mul ((norm_smul_le _ _).trans ?_) (l2_opNorm_piProd_dite_single_le _ _ _ _)
            (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left (l2_opNorm_piProd_dite_single_le _ _ _ _)
            (norm_nonneg _)
      _ ≤ ‖Y‖ := by rw [mul_one, mul_one]; exact norm_entry_le_l2_opNorm _ _ _
      _ = ‖extendId hDU Y‖ := (l2_opNorm_extendId hDU Y).symm

end OpenAI
