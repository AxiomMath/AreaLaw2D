import AreaLawForMathlib.QuantumInfo.Region.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QuantumInfo.ForMathlib.Matrix

/-!
# The partial trace onto a subregion

Extends `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` and Physlib's
`QuantumInfo/ForMathlib/Matrix.lean`:
`ptrace (h : S ⊆ T)` traces out `T \ S` from a matrix on `Reg loc T`; it is linear, functorial,
trace preserving, positive, and dual to `extendId h` (tensoring with the identity on `T \ S`).
On a disjoint union it is Physlib's `traceRight`/`traceLeft`.
-/
namespace Arealaw

open scoped ComplexOrder Matrix.Norms.L2Operator
open Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] {𝕜 : Type*} [RCLike 𝕜] {S T U : Finset σ}

/-- The partial trace from region `T` down to `S ⊆ T`: sum over configurations of the
complement `T \ S`. -/
noncomputable def ptrace (_h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    Matrix (Reg loc S) (Reg loc S) 𝕜 :=
  Matrix.of fun x y => ∑ z : Reg loc (T \ S), M (glue x z) (glue y z)

/-- **Identity law**: tracing a region down to itself changes nothing.  Together with
`ptrace_ptrace` this says the partial trace is functorial on the inclusion order. -/
@[simp] theorem ptrace_self (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace (Finset.Subset.refl T) M = M := by
  ext x y
  simp [ptrace]

/-- **Functoriality**: tracing `U → T → S` equals tracing `U → S`. -/
theorem ptrace_ptrace (hST : S ⊆ T) (hTU : T ⊆ U) (M : Matrix (Reg loc U) (Reg loc U) 𝕜) :
    ptrace hST (ptrace hTU M) = ptrace (hST.trans hTU) M := by
  ext x y
  simp only [ptrace, Matrix.of_apply]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (splitEquiv (loc := loc) hST hTU) _ _ fun (z, w) => by
    rw [glue_splitEquiv, glue_splitEquiv]

/-! ## Linearity

The partial trace is a fibre sum, hence linear in the traced matrix. -/

/-- The partial trace of `0` is `0`. -/
@[simp] theorem ptrace_zero (h : S ⊆ T) :
    ptrace h (0 : Matrix (Reg loc T) (Reg loc T) 𝕜) = 0 := by
  ext x y
  simp [ptrace]

/-- The partial trace is additive. -/
@[simp] theorem ptrace_add (h : S ⊆ T) (M N : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h (M + N) = ptrace h M + ptrace h N := by
  ext x y
  simp [ptrace, Finset.sum_add_distrib]

/-- The partial trace commutes with scalar multiplication. -/
@[simp] theorem ptrace_smul {R : Type*} [DistribSMul R 𝕜] (h : S ⊆ T) (c : R)
    (M : Matrix (Reg loc T) (Reg loc T) 𝕜) : ptrace h (c • M) = c • ptrace h M := by
  ext x y
  simp [ptrace, Finset.smul_sum]

/-- The partial trace as a linear map. -/
noncomputable def ptraceₗ (h : S ⊆ T) :
    Matrix (Reg loc T) (Reg loc T) 𝕜 →ₗ[𝕜] Matrix (Reg loc S) (Reg loc S) 𝕜 where
  toFun := ptrace h
  map_add' := ptrace_add h
  map_smul' := ptrace_smul h

/-- `ptraceₗ` applies as `ptrace`. -/
@[simp] theorem ptraceₗ_apply (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptraceₗ h M = ptrace h M := rfl

/-- The partial trace commutes with negation. -/
@[simp] theorem ptrace_neg (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h (-M) = -ptrace h M :=
  map_neg (ptraceₗ h) M

/-- The partial trace commutes with subtraction. -/
@[simp] theorem ptrace_sub (h : S ⊆ T) (M N : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h (M - N) = ptrace h M - ptrace h N :=
  map_sub (ptraceₗ h) M N

/-- The partial trace commutes with finite sums. -/
@[simp] theorem ptrace_sum {κ : Type*} (h : S ⊆ T) (s : Finset κ)
    (M : κ → Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h (∑ k ∈ s, M k) = ∑ k ∈ s, ptrace h (M k) :=
  map_sum (ptraceₗ h) M s

/-- **The partial trace onto the empty region is the trace**, as the unique entry of a
`1 × 1` matrix. -/
@[simp] theorem ptrace_empty (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace (Finset.empty_subset T) M = M.trace • 1 := by
  ext x y
  obtain rfl := Subsingleton.elim x y
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  exact Fintype.sum_equiv (regEquivOfEq (loc := loc) Finset.sdiff_empty) _ _ fun _ => rfl

/-- **The bridge**: the region partial trace onto `A ⊆ A ∪ B` is `Matrix.traceRight`, the
binary right partial trace, after transporting along `unionEquiv`. -/
theorem ptrace_eq_traceRight {A B : Finset σ} (hd : Disjoint A B)
    (M : Matrix (Reg loc (A ∪ B)) (Reg loc (A ∪ B)) 𝕜) :
    ptrace Finset.subset_union_left M
      = traceRight (M.submatrix (unionEquiv hd).symm (unionEquiv hd).symm) :=
  Matrix.ext fun _ _ => (Fintype.sum_equiv (sdiffEquiv (loc := loc) hd) _ _ fun _ => rfl).symm

/-- The mirror bridge: the region partial trace onto `B ⊆ A ∪ B` is `Matrix.traceLeft`.
Not definitional, unlike `ptrace_eq_traceRight`: `glue` branches on `B` where `unionEquiv`
branches on `A`, so disjointness is used. -/
theorem ptrace_eq_traceLeft {A B : Finset σ} (hd : Disjoint A B)
    (M : Matrix (Reg loc (A ∪ B)) (Reg loc (A ∪ B)) 𝕜) :
    ptrace Finset.subset_union_right M
      = traceLeft (M.submatrix (unionEquiv hd).symm (unionEquiv hd).symm) :=
  Matrix.ext fun x y =>
    Fintype.sum_equiv (regEquivOfEq (Finset.union_sdiff_cancel_right hd)) _ _ fun _ => by
      simp [-unionEquiv_symm_apply, unionEquiv_symm_apply_eq_glue_right]

section DecEqLoc
variable [∀ i, DecidableEq (loc i)]

/-- The `z`-slice isometry `Reg S → Reg T`: the column-selection matrix of `glue · z`. -/
noncomputable def sliceIsometry (𝕜 : Type*) [RCLike 𝕜] (z : Reg loc (T \ S)) :
    Matrix (Reg loc T) (Reg loc S) 𝕜 :=
  Matrix.of fun w x => if w = glue x z then 1 else 0

omit [∀ i, Fintype (loc i)] in
/-- `sliceIsometry` selects columns of the identity: it is `1` reindexed along `glue · z`. -/
theorem sliceIsometry_eq_submatrix_one (z : Reg loc (T \ S)) :
    sliceIsometry 𝕜 z =
      (1 : Matrix (Reg loc T) (Reg loc T) 𝕜).submatrix id (fun x => glue x z) := by
  ext w x
  simp [sliceIsometry, Matrix.one_apply]

/-- `sliceIsometry` is an isometry: its columns are distinct standard basis vectors.  This is
`Matrix.submatrix_one`, whose injectivity hypothesis is exactly `glue_left_injective`. -/
theorem sliceIsometry_conjTranspose_mul_self (h : S ⊆ T) (z : Reg loc (T \ S)) :
    (sliceIsometry 𝕜 z)ᴴ * (sliceIsometry 𝕜 z) = 1 := by
  simp [sliceIsometry_eq_submatrix_one, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_one _ (glue_left_injective h z)]

/-- The partial trace as a sum of isometry conjugations. -/
theorem ptrace_eq_sum_conj (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h M = ∑ z : Reg loc (T \ S),
      ((sliceIsometry 𝕜 z)ᴴ * M * (sliceIsometry 𝕜 z) : Matrix (Reg loc S) (Reg loc S) 𝕜) := by
  ext x y
  simp [ptrace, Matrix.sum_apply, mul_apply, sliceIsometry]

/-- Tracing out `T \ S` scales the identity by its dimension: the maximally mixed state on
`T` restricts to the maximally mixed state on `S`. -/
@[simp] theorem ptrace_one (h : S ⊆ T) : ptrace h (1 : Matrix (Reg loc T) (Reg loc T) 𝕜)
    = (Fintype.card (Reg loc (T \ S)) : 𝕜) • 1 := by
  simp only [ptrace_eq_sum_conj h, Matrix.mul_one, sliceIsometry_conjTranspose_mul_self h,
    Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

end DecEqLoc

/-! ## Structure preservation

Positivity, Hermiticity and the trace survive the fibre sum.  `posSemidef_ptrace` needs no
decidable equality on the local family, reaching `ptrace_eq_sum_conj` through `classical`. -/

/-- The partial trace of a positive semidefinite matrix is positive semidefinite. -/
theorem posSemidef_ptrace (h : S ⊆ T) {M : Matrix (Reg loc T) (Reg loc T) 𝕜} (hM : M.PosSemidef) :
    (ptrace h M).PosSemidef := by
  classical
  rw [ptrace_eq_sum_conj]
  exact Matrix.posSemidef_sum _ fun z _ => hM.conjTranspose_mul_mul_same _

/-- The partial trace commutes with conjugate transposition. -/
@[simp] theorem ptrace_conjTranspose (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h Mᴴ = (ptrace h M)ᴴ := by
  ext x y
  simp [ptrace]

/-- The partial trace of a Hermitian matrix is Hermitian. -/
theorem isHermitian_ptrace (h : S ⊆ T) {M : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hM : M.IsHermitian) : (ptrace h M).IsHermitian := by
  rw [Matrix.IsHermitian, ← ptrace_conjTranspose, hM]

/-- The partial trace preserves the trace. -/
theorem trace_ptrace (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    (ptrace h M).trace = M.trace := by
  simp [trace, ptrace, ← Fintype.sum_prod_type', ← (glueEquiv h).sum_comp]

section DecEqLoc
variable [∀ i, DecidableEq (loc i)]

/-- Extend a matrix on the subregion `S` to `T` by tensoring with the identity on
`T \ S` (entrywise form). -/
noncomputable def extendId (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    Matrix (Reg loc T) (Reg loc T) 𝕜 :=
  Matrix.of fun w w' =>
    if restr (S := T \ S) (T := T) Finset.sdiff_subset w
        = restr (S := T \ S) (T := T) Finset.sdiff_subset w'
    then A (restr h w) (restr h w') else 0

section
omit [∀ i, Fintype (loc i)]

/-- Extending `0` gives `0`. -/
@[simp] theorem extendId_zero (h : S ⊆ T) :
    extendId h (0 : Matrix (Reg loc S) (Reg loc S) 𝕜) = 0 := by
  ext w w'
  simp [extendId]

/-- Extension by the identity is additive. -/
@[simp] theorem extendId_add (h : S ⊆ T) (A B : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (A + B) = extendId h A + extendId h B := by
  ext w w'
  simp [extendId, apply_ite₂]

/-- Extension by the identity commutes with scalar multiplication. -/
@[simp] theorem extendId_smul (h : S ⊆ T) (c : 𝕜) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (c • A) = c • extendId h A := by
  ext w w'
  simp [extendId, apply_ite₂]

/-- How `extendId` acts on glued configurations: diagonal on the added region, `A` on the
subregion. -/
@[simp] theorem extendId_apply_glue (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜)
    (u u' : Reg loc S) (z z' : Reg loc (T \ S)) :
    extendId h A (glue u z) (glue u' z') = if z = z' then A u u' else 0 := by
  simp [extendId]

/-- `extendId` is the Kronecker product with the identity, transported along `glueEquiv`. -/
theorem extendId_eq_kronecker (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h A = (Matrix.kroneckerMap (· * ·) A
        (1 : Matrix (Reg loc (T \ S)) (Reg loc (T \ S)) 𝕜)).submatrix
      (glueEquiv h).symm (glueEquiv h).symm := by
  ext w w'
  simp [extendId, Matrix.one_apply]

/-- Extending the identity gives the identity. -/
@[simp] theorem extendId_one (h : S ⊆ T) :
    extendId h (1 : Matrix (Reg loc S) (Reg loc S) 𝕜) = 1 := by
  simp [extendId_eq_kronecker, Matrix.submatrix_one _ (glueEquiv h).symm.injective]

/-- Extension by the identity commutes with conjugate transposition. -/
@[simp] theorem extendId_conjTranspose (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h Aᴴ = (extendId h A)ᴴ := by
  simp [extendId_eq_kronecker, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

/-- Extension by the identity preserves Hermitianness. -/
theorem isHermitian_extendId (h : S ⊆ T) {A : Matrix (Reg loc S) (Reg loc S) 𝕜}
    (hA : A.IsHermitian) : (extendId h A).IsHermitian := by
  rw [Matrix.IsHermitian, ← extendId_conjTranspose, hA]

end

omit [∀ i, Fintype (loc i)] in
/-- Extension by the identity preserves positive semidefiniteness. -/
theorem posSemidef_extendId [∀ i, Finite (loc i)] (h : S ⊆ T)
    {A : Matrix (Reg loc S) (Reg loc S) 𝕜} (hA : A.PosSemidef) : (extendId h A).PosSemidef :=
  extendId_eq_kronecker h A ▸ (hA.kronecker .one).submatrix _

/-- The trace of an extended observable is scaled by the dimension of the added region. -/
theorem trace_extendId (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    (extendId h A).trace = (Fintype.card (Reg loc (T \ S)) : 𝕜) * A.trace := by
  simp [extendId_eq_kronecker, Matrix.trace_kronecker, mul_comm]

/-- A row vector paired with the `glue · z`-column of an extended matrix only sees the
`z`-slice of the vector. -/
theorem sum_mul_extendId_apply_glue (h : S ⊆ T) (v : Reg loc T → 𝕜)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) (y : Reg loc S) (z : Reg loc (T \ S)) :
    ∑ w, v w * extendId h A w (glue y z) = ∑ u, v (glue u z) * A u y := by
  simp [← (glueEquiv h).sum_comp, Fintype.sum_prod_type]

/-- **The pull-out law**: a factor already supported on the subregion passes through the
partial trace. -/
theorem ptrace_mul_extendId (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    ptrace h (M * extendId h A) = ptrace h M * A := by
  ext x y
  simp only [ptrace, Matrix.of_apply, Matrix.mul_apply, sum_mul_extendId_apply_glue, Finset.sum_mul]
  exact Finset.sum_comm

/-- The left-hand mirror of `ptrace_mul_extendId`. -/
theorem extendId_mul_ptrace (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    ptrace h (extendId h A * M) = A * ptrace h M := by
  simpa [← conjTranspose_mul] using congrArg (·ᴴ) (ptrace_mul_extendId h Mᴴ Aᴴ)

/-- **Adjointness of the partial trace**: tracing against a local observable equals
pairing the full state with the observable extended by the identity. -/
theorem trace_ptrace_mul (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    (ptrace h M * A).trace = (M * extendId h A).trace := by
  rw [← ptrace_mul_extendId, trace_ptrace]

end DecEqLoc

/-! ## The tensor product of two disjoint regions

`kronUnion` branches on `A` alone, so unlike `extendId` nothing here needs decidable
equality on the local family. -/

/-- Combine states on two disjoint regions into a state on the union (Kronecker product
transported along `unionEquiv`). -/
noncomputable def kronUnion {A B : Finset σ} (hd : Disjoint A B)
    (M : Matrix (Reg loc A) (Reg loc A) 𝕜) (N : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    Matrix (Reg loc (A ∪ B)) (Reg loc (A ∪ B)) 𝕜 :=
  Matrix.of fun w w' =>
    M ((unionEquiv hd w).1) ((unionEquiv hd w').1) * N ((unionEquiv hd w).2) ((unionEquiv hd w').2)

omit [∀ i, Fintype (loc i)] in
/-- `kronUnion` is the Kronecker product, transported along `unionEquiv`. -/
theorem kronUnion_eq_submatrix {A B : Finset σ} (hd : Disjoint A B)
    (M : Matrix (Reg loc A) (Reg loc A) 𝕜) (N : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    kronUnion hd M N = (Matrix.kroneckerMap (· * ·) M N).submatrix
      (unionEquiv hd) (unionEquiv hd) := rfl

/-! ### Structure of a tensor product

`kronUnion` is the Kronecker product transported along `unionEquiv`, so the standard
structure-preservation facts follow from Mathlib's. -/

end Arealaw
