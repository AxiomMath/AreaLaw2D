import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order

/-!
# The embedding of an `RCLike` field into `ℂ`, applied to matrices

Extends `Mathlib.Analysis.RCLike.Basic`, where the canonical map is the `ℝ`-linear
`RCLike.map 𝕜 ℂ`, and `Mathlib.Analysis.CStarAlgebra.Matrix`.

`RCLike.toComplex 𝕜 : 𝕜 →⋆ₐ[ℝ] ℂ` bundles `RCLike.map 𝕜 ℂ` as a star algebra homomorphism.
Applied entrywise it preserves Hermiticity, the eigenvalue multiset of a Hermitian matrix,
positive semidefiniteness, the Loewner order and the `L²` operator norm.

In the other direction, `Matrix.realProjection` takes entrywise real parts of a complex matrix;
it is monotone for the Loewner order and contractive on Hermitian matrices.  When
`im I = 1`, `Matrix.complexPullback` inverts the entrywise embedding.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace RCLike

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The canonical embedding `x ↦ re x + im x * I` of an `RCLike` field into `ℂ`. -/
noncomputable def toComplex : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun := map 𝕜 ℂ
  map_one' := by simp
  map_mul' x y := by apply Complex.ext <;> simp [mul_re, mul_im]
  map_zero' := by simp
  map_add' := map_add _
  commutes' r := by simp
  map_star' x := by apply Complex.ext <;> simp

variable {𝕜}

theorem toComplex_apply (x : 𝕜) : toComplex 𝕜 x = (re x : ℂ) + (im x : ℂ) * Complex.I := rfl

@[simp] theorem re_toComplex (x : 𝕜) : (toComplex 𝕜 x).re = re x := by simp [toComplex_apply]

@[simp] theorem im_toComplex (x : 𝕜) : (toComplex 𝕜 x).im = im x := by simp [toComplex_apply]

@[simp] theorem toComplex_ofReal (r : ℝ) : toComplex 𝕜 (r : 𝕜) = r := by
  apply Complex.ext <;> simp [toComplex_apply]

theorem toComplex_injective : Function.Injective (toComplex 𝕜) := fun x y h =>
  ext (by simpa using congrArg Complex.re h) (by simpa using congrArg Complex.im h)

/-- If `im I = 1`, `toComplex` is the ring isomorphism `complexRingEquiv`. -/
theorem toComplex_complexRingEquiv_symm (hI : im (I : 𝕜) = 1) (z : ℂ) :
    toComplex 𝕜 ((complexRingEquiv hI).symm z) = z :=
  (complexRingEquiv hI).apply_symm_apply z

end RCLike

namespace Matrix

open RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-! ### The entrywise embedding -/

theorem map_toComplex_injective :
    Function.Injective fun A : Matrix m n 𝕜 => A.map (toComplex 𝕜) :=
  map_injective toComplex_injective

@[simp] theorem map_toComplex_eq_zero_iff {A : Matrix m n 𝕜} : A.map (toComplex 𝕜) = 0 ↔ A = 0 :=
  map_toComplex_injective.eq_iff' (Matrix.map_zero _ (_root_.map_zero _))

theorem map_toComplex_sub (A B : Matrix m n 𝕜) :
    (A - B).map (toComplex 𝕜) = A.map (toComplex 𝕜) - B.map (toComplex 𝕜) :=
  Matrix.map_sub _ (_root_.map_sub _) A B

theorem map_toComplex_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    (c • A).map (toComplex 𝕜) = toComplex 𝕜 c • A.map (toComplex 𝕜) := by
  ext; simp

theorem map_toComplex_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n 𝕜) :
    (∑ i ∈ s, A i).map (toComplex 𝕜) = ∑ i ∈ s, (A i).map (toComplex 𝕜) := by
  ext; simp [sum_apply]

theorem map_toComplex_one [DecidableEq n] : (1 : Matrix n n 𝕜).map (toComplex 𝕜) = 1 :=
  Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)

theorem star_comp_toComplex (v : n → 𝕜) :
    star (fun i => toComplex 𝕜 (v i)) = fun i => toComplex 𝕜 (star v i) :=
  funext fun i => (map_star (toComplex 𝕜) (v i)).symm

theorem mulVec_map_toComplex [Fintype n] (A : Matrix m n 𝕜) (v : n → 𝕜) :
    A.map (toComplex 𝕜) *ᵥ (fun i => toComplex 𝕜 (v i)) = fun i => toComplex 𝕜 ((A *ᵥ v) i) :=
  funext fun i => (RingHom.map_mulVec (toComplex 𝕜 : 𝕜 →+* ℂ) A v i).symm

theorem vecMulVec_comp_toComplex (v : m → 𝕜) (w : n → 𝕜) :
    vecMulVec (fun i => toComplex 𝕜 (v i)) (fun i => toComplex 𝕜 (w i)) =
      (vecMulVec v w).map (toComplex 𝕜) := by
  ext; simp [vecMulVec_apply]

@[simp] theorem isHermitian_map_toComplex_iff {A : Matrix n n 𝕜} :
    (A.map (toComplex 𝕜)).IsHermitian ↔ A.IsHermitian :=
  isHermitian_map_iff (map_star (toComplex 𝕜)) toComplex_injective

variable [Fintype n] [DecidableEq n]

/-- The embedding into `ℂ` preserves the eigenvalue multiset of a Hermitian matrix. -/
theorem IsHermitian.eigenvalues_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Finset.univ.val.map (isHermitian_map_toComplex_iff.2 hA).eigenvalues =
      Finset.univ.val.map hA.eigenvalues := by
  have hc : (A.map (toComplex 𝕜)).charpoly = A.charpoly.map (toComplex 𝕜 : 𝕜 →+* ℂ) :=
    charpoly_map A _
  refine Multiset.map_injective (RCLike.ofReal_injective (K := ℂ)) ?_
  rw [Multiset.map_map, Multiset.map_map,
    ← (isHermitian_map_toComplex_iff.2 hA).roots_charpoly_eq_eigenvalues, hc, hA.charpoly_eq,
    Polynomial.map_prod,
    Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem posSemidef_map_toComplex_iff [Finite n] {A : Matrix n n 𝕜} :
    (A.map (toComplex 𝕜)).PosSemidef ↔ A.PosSemidef := by
  classical
  have := Fintype.ofFinite n
  by_cases hA : A.IsHermitian
  · rw [(isHermitian_map_toComplex_iff.2 hA).posSemidef_iff_eigenvalues_nonneg,
      hA.posSemidef_iff_eigenvalues_nonneg, Pi.le_def, Pi.le_def]
    have h := congrArg (∀ x ∈ ·, 0 ≤ x) hA.eigenvalues_map_toComplex
    simpa only [Multiset.forall_mem_map_iff, Finset.mem_val, Finset.mem_univ, true_imp_iff,
      Pi.zero_apply]
      using h.to_iff
  · exact iff_of_false (fun h => hA (isHermitian_map_toComplex_iff.1 h.isHermitian))
      fun h => hA h.isHermitian

omit [Fintype n] [DecidableEq n] in
@[simp] theorem map_toComplex_le_map_toComplex_iff [Finite n] {A B : Matrix n n 𝕜} :
    A.map (toComplex 𝕜) ≤ B.map (toComplex 𝕜) ↔ A ≤ B := by
  rw [le_iff, le_iff, ← map_toComplex_sub, posSemidef_map_toComplex_iff]

/-- The `L²` operator norm of a Hermitian matrix is the largest modulus of an eigenvalue. -/
theorem IsHermitian.nnnorm_eq_iSup_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (‖A‖₊ : ℝ≥0∞) = ⨆ x ∈ Set.range hA.eigenvalues, (‖x‖₊ : ℝ≥0∞) := by
  have h : (‖A‖₊ : ℝ≥0∞) = spectralRadius 𝕜 A := by
    have hT : IsSelfAdjoint (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := hA.isSelfAdjoint.map _
    rw [spectralRadius, ← AlgEquiv.spectrum_eq (toEuclideanCLM (n := n) (𝕜 := 𝕜)) A]
    exact (ContinuousLinearMap.spectralRadius_eq_nnnorm _ hT).symm
  rw [h, spectralRadius, hA.spectrum_eq_image_range, iSup_image]
  simp

/-- Hermitian matrices with the same eigenvalue multiset have the same `L²` operator norm. -/
theorem IsHermitian.norm_eq_of_eigenvalues {𝕜' : Type*} [RCLike 𝕜'] {A : Matrix n n 𝕜}
    {B : Matrix n n 𝕜'} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : Finset.univ.val.map hA.eigenvalues = Finset.univ.val.map hB.eigenvalues) :
    ‖A‖ = ‖B‖ := by
  have hr : Set.range hA.eigenvalues = Set.range hB.eigenvalues := by
    ext x; simpa using congrArg (x ∈ ·) h
  have h' := hA.nnnorm_eq_iSup_eigenvalues
  rw [hr, ← hB.nnnorm_eq_iSup_eigenvalues, ENNReal.coe_inj] at h'
  exact congrArg NNReal.toReal h'

/-- The embedding into `ℂ` preserves the `L²` operator norm. -/
@[simp] theorem norm_map_toComplex [Fintype m] (A : Matrix m n 𝕜) :
    ‖A.map (toComplex 𝕜)‖ = ‖A‖ := by
  have hA := isHermitian_conjTranspose_mul_self A
  have h := (isHermitian_map_toComplex_iff.2 hA).norm_eq_of_eigenvalues hA
    hA.eigenvalues_map_toComplex
  rw [Matrix.map_mul, conjTranspose_map _ (map_star (toComplex 𝕜)),
    l2_opNorm_conjTranspose_mul_self,
    l2_opNorm_conjTranspose_mul_self] at h
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h

/-- A Hermitian complex matrix and its transpose have the same `L²` operator norm. -/
theorem IsHermitian.norm_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) : ‖Aᵀ‖ = ‖A‖ := by
  refine hA.transpose.norm_eq_of_eigenvalues hA ?_
  apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
  rw [Multiset.map_map, Multiset.map_map, ← hA.transpose.roots_charpoly_eq_eigenvalues,
    charpoly_transpose, hA.roots_charpoly_eq_eigenvalues]

/-! ### Real parts and the inverse embedding -/

omit [Fintype n] [DecidableEq n]

/-- Entrywise real part of a complex matrix, as a matrix over an `RCLike` field. -/
noncomputable def realProjection (A : Matrix m n ℂ) : Matrix m n 𝕜 :=
  fun i j => (A i j).re

@[simp] theorem realProjection_apply (A : Matrix m n ℂ) (i : m) (j : n) :
    realProjection (𝕜 := 𝕜) A i j = (A i j).re := rfl

@[simp] theorem realProjection_zero : realProjection (𝕜 := 𝕜) (0 : Matrix m n ℂ) = 0 := by
  ext; simp

@[simp] theorem realProjection_sub (A B : Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) (A - B) = realProjection A - realProjection B := by
  ext; simp

@[simp] theorem realProjection_ofReal_smul (r : ℝ) (A : Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) ((r : ℂ) • A) = (r : 𝕜) • realProjection A := by
  ext; simp

@[simp] theorem realProjection_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) (∑ i ∈ s, A i) = ∑ i ∈ s, realProjection (A i) := by
  ext; simp [sum_apply]

@[simp] theorem realProjection_one [DecidableEq n] :
    realProjection (𝕜 := 𝕜) (1 : Matrix n n ℂ) = 1 := by
  ext i j
  rw [realProjection_apply, one_apply, one_apply]
  split_ifs <;> simp

/-- If `I = 0`, taking real parts inverts the entrywise embedding. -/
theorem realProjection_map_toComplex (hI : (I : 𝕜) = 0) (A : Matrix m n 𝕜) :
    realProjection (A.map (toComplex 𝕜)) = A := by
  ext i j
  rw [realProjection_apply, map_apply, re_toComplex, ← re_add_im (A i j), im_eq_zero hI]
  simp

/-- For Hermitian `A`, the embedded real part of `A` is the average `(A + Aᵀ) / 2`. -/
theorem IsHermitian.map_toComplex_realProjection {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (realProjection (𝕜 := 𝕜) A).map (toComplex 𝕜) = (2 : ℝ)⁻¹ • (A + Aᵀ) := by
  ext i j
  have hij : star (A i j) = A j i := by simpa using congrFun (congrFun hA.eq j) i
  rw [map_apply, realProjection_apply, toComplex_ofReal, smul_apply, add_apply,
    transpose_apply, Complex.real_smul, ← hij]
  apply Complex.ext <;> simp
  ring

theorem PosSemidef.realProjection [Finite n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (realProjection (𝕜 := 𝕜) A).PosSemidef := by
  have := Fintype.ofFinite n
  rw [← posSemidef_map_toComplex_iff, hA.isHermitian.map_toComplex_realProjection]
  exact (hA.add hA.transpose).smul (by positivity)

theorem realProjection_mono [Finite n] {A B : Matrix n n ℂ} (hAB : A ≤ B) :
    realProjection (𝕜 := 𝕜) A ≤ realProjection B := by
  rw [le_iff] at hAB ⊢
  rw [← realProjection_sub]
  exact hAB.realProjection

/-- If `I = 0` and `A` annihilates the embedding of `v`, the real part of `A` annihilates `v`. -/
theorem realProjection_mulVec_eq_zero [Fintype n] (hI : (I : 𝕜) = 0) {A : Matrix m n ℂ}
    {v : n → 𝕜} (h : A *ᵥ (fun i => toComplex 𝕜 (v i)) = 0) :
    realProjection A *ᵥ v = 0 := by
  funext i
  apply (realRingEquiv hI).injective
  simpa [mulVec, dotProduct, map_sum, Complex.mul_re, mul_re, im_eq_zero hI]
    using congrArg Complex.re (congrFun h i)

/-- On Hermitian matrices, taking real parts does not increase the `L²` operator norm. -/
theorem IsHermitian.norm_realProjection_le [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    ‖realProjection (𝕜 := 𝕜) A‖ ≤ ‖A‖ := by
  rw [← norm_map_toComplex, hA.map_toComplex_realProjection, smul_add]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_smul, norm_smul, hA.norm_transpose, Real.norm_of_nonneg (by positivity)]
  ring

/-- If `im I = 1`, the inverse of the entrywise embedding into `ℂ`. -/
noncomputable def complexPullback (hI : im (I : 𝕜) = 1) (A : Matrix m n ℂ) : Matrix m n 𝕜 :=
  A.map (complexRingEquiv hI).symm

@[simp] theorem complexPullback_map_toComplex (hI : im (I : 𝕜) = 1) (A : Matrix m n ℂ) :
    (complexPullback hI A).map (toComplex 𝕜) = A := by
  ext; exact toComplex_complexRingEquiv_symm hI _

end Matrix
