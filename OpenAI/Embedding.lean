import OpenAI.Statements
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The embedding of an `RCLike` field into `ℂ`

Every `RCLike` field `𝕜` embeds into `ℂ` by `x ↦ re x + im x * I`, a star algebra
homomorphism over `ℝ`.  Applied entrywise it preserves Hermiticity, positive
semidefiniteness, the Loewner order, the trace, products, partial traces and tensor
constructions, the eigenvalue multiset of a Hermitian matrix, and the `L²` operator norm.  On
states it commutes with restriction and preserves every entropy, so an entropy statement
proved over `ℂ` holds over `𝕜`.  The Hamiltonian-level notions of [OAI265, §1.1]
(`hamiltonian`, `IsAdmissible`, `HasGlobalGap`, `pureState`) transfer along it.

## Main definitions

* `OpenAI.toComplex`: the embedding `𝕜 →⋆ₐ[ℝ] ℂ`.
* `Arealaw.SubState.toComplex`, `Arealaw.MState.toComplex`: a state over `𝕜` read over `ℂ`.

## Main statements

* `OpenAI.eigenvalues_multiset_map_toComplex`: the spectrum is unchanged.
* `OpenAI.posSemidef_map_toComplex_iff`, `OpenAI.map_toComplex_le_map_toComplex_iff`.
* `Arealaw.SubState.entropy_toComplex`, `Arealaw.SubState.regionEntropy_toComplex`,
  `Arealaw.SubState.mutualInfo_toComplex`: entropies are unchanged.
* `OpenAI.pureState_toComplex`: the pure state of a vector embeds as the pure state of the
  embedded vector.
* `OpenAI.norm_map_toComplex`: the `L²` operator norm is unchanged.
* `OpenAI.hasGlobalGap_map_toComplex_iff`, `OpenAI.isAdmissible_map_toComplex_iff`,
  `OpenAI.hamiltonian_map_toComplex`.

## Implementation notes

This file is the transfer layer of decision 4.3 in docs/oai265/Memory.md.  Physlib's entropy theory (strong
subadditivity, `Sᵥₙ_pure_complement`, subadditivity) and `Arealaw.Subadditivity` are stated
over `ℂ` only, while the statements of [OAI265] are over an arbitrary `RCLike 𝕜`.  Results
that need those upstreams are proved over `ℂ` and transferred to `𝕜` through the lemmas
here; each downstream use is to be marked as a deviation in place.

Mathlib has the canonical map only as the `ℝ`-linear `RCLike.map 𝕜 ℂ`, and as ring
isomorphisms `RCLike.complexRingEquiv` under `im I = 1`.  `toComplex` bundles `RCLike.map 𝕜 ℂ`
as a star algebra homomorphism, which holds without that hypothesis (for `𝕜 = ℝ` it is the
inclusion), so that Mathlib's `RingHom` and `StarHom` matrix lemmas apply.

Spectral facts go through the characteristic polynomial: `charpoly_map` and
`IsHermitian.charpoly_eq` identify the roots of both sides.  The operator norm of a Hermitian
matrix is its spectral radius (`ContinuousLinearMap.spectralRadius_eq_nnnorm`, valid over any
`RCLike` field), and the general case reduces to it by the C⋆-identity
`‖Aᴴ * A‖ = ‖A‖ * ‖A‖`.
-/

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix

/-- The canonical embedding `x ↦ re x + im x * I` of an `RCLike` field into `ℂ`. -/
noncomputable def toComplex (𝕜 : Type*) [RCLike 𝕜] : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun := RCLike.map 𝕜 ℂ
  map_one' := by simp
  map_mul' x y := by
    apply Complex.ext <;> simp [RCLike.mul_re, RCLike.mul_im]
  map_zero' := by simp
  map_add' := map_add _
  commutes' r := by simp
  map_star' x := by apply Complex.ext <;> simp

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `toComplex` is Mathlib's canonical `ℝ`-linear map `RCLike.map 𝕜 ℂ`. -/
theorem coe_toComplex : ⇑(toComplex 𝕜) = RCLike.map 𝕜 ℂ := rfl

/-- `toComplex` sends `x` to `re x + im x * I`. -/
theorem toComplex_apply (x : 𝕜) :
    toComplex 𝕜 x = (RCLike.re x : ℂ) + (RCLike.im x : ℂ) * Complex.I := rfl

@[simp] theorem re_toComplex (x : 𝕜) : (toComplex 𝕜 x).re = RCLike.re x := by
  simp [toComplex_apply]

@[simp] theorem im_toComplex (x : 𝕜) : (toComplex 𝕜 x).im = RCLike.im x := by
  simp [toComplex_apply]

@[simp] theorem toComplex_ofReal (r : ℝ) : toComplex 𝕜 (r : 𝕜) = r := by
  apply Complex.ext <;> simp

@[simp] theorem norm_toComplex (x : 𝕜) : ‖toComplex 𝕜 x‖ = ‖x‖ :=
  RCLike.norm_to_complex x

/-- The embedding into `ℂ` is injective. -/
theorem toComplex_injective : Function.Injective (toComplex 𝕜) := fun x y h =>
  RCLike.ext (by simpa using congrArg Complex.re h) (by simpa using congrArg Complex.im h)

@[simp] theorem toComplex_inj {x y : 𝕜} : toComplex 𝕜 x = toComplex 𝕜 y ↔ x = y :=
  toComplex_injective.eq_iff

/-- On `ℂ` itself the embedding is the identity. -/
@[simp] theorem toComplex_complex : toComplex ℂ = StarAlgHom.id ℝ ℂ := by
  ext x
  apply Complex.ext <;> simp

/-! ## Matrices -/

section Matrix

variable {m n : Type*}

theorem conjTranspose_map_toComplex (A : Matrix m n 𝕜) :
    (A.map (toComplex 𝕜))ᴴ = Aᴴ.map (toComplex 𝕜) :=
  (conjTranspose_map _ fun x => map_star (toComplex 𝕜) x).symm

theorem map_toComplex_injective :
    Function.Injective (fun A : Matrix m n 𝕜 => A.map (toComplex 𝕜)) :=
  map_injective toComplex_injective

@[simp] theorem map_toComplex_inj {A B : Matrix m n 𝕜} :
    A.map (toComplex 𝕜) = B.map (toComplex 𝕜) ↔ A = B :=
  map_toComplex_injective.eq_iff

/-- On complex matrices the entrywise embedding is the identity. -/
theorem map_toComplex_complex (A : Matrix m n ℂ) : A.map (toComplex ℂ) = A := by
  ext; simp

/-- A matrix embeds as zero iff it is zero. -/
@[simp] theorem map_toComplex_eq_zero_iff {A : Matrix m n 𝕜} : A.map (toComplex 𝕜) = 0 ↔ A = 0 :=
  ⟨fun h => map_toComplex_injective (h.trans (Matrix.map_zero _ (map_zero _)).symm),
    fun h => h ▸ Matrix.map_zero _ (map_zero _)⟩

theorem map_toComplex_add (A B : Matrix m n 𝕜) :
    (A + B).map (toComplex 𝕜) = A.map (toComplex 𝕜) + B.map (toComplex 𝕜) :=
  Matrix.map_add _ (map_add _) A B

theorem map_toComplex_sub (A B : Matrix m n 𝕜) :
    (A - B).map (toComplex 𝕜) = A.map (toComplex 𝕜) - B.map (toComplex 𝕜) :=
  Matrix.map_sub _ (map_sub _) A B

theorem map_toComplex_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    (c • A).map (toComplex 𝕜) = toComplex 𝕜 c • A.map (toComplex 𝕜) := by
  ext; simp

theorem map_toComplex_sum {κ : Type*} (s : Finset κ) (A : κ → Matrix m n 𝕜) :
    (∑ k ∈ s, A k).map (toComplex 𝕜) = ∑ k ∈ s, (A k).map (toComplex 𝕜) := by
  ext; simp [Matrix.sum_apply]

theorem map_toComplex_mul {l : Type*} [Fintype n] (A : Matrix l n 𝕜) (B : Matrix n m 𝕜) :
    (A * B).map (toComplex 𝕜) = A.map (toComplex 𝕜) * B.map (toComplex 𝕜) :=
  Matrix.map_mul

theorem map_toComplex_one [DecidableEq n] : (1 : Matrix n n 𝕜).map (toComplex 𝕜) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- The trace commutes with the entrywise embedding. -/
theorem trace_map_toComplex [Fintype n] (A : Matrix n n 𝕜) :
    (A.map (toComplex 𝕜)).trace = toComplex 𝕜 A.trace :=
  (AddMonoidHom.map_trace (toComplex 𝕜 : 𝕜 →+ ℂ) A).symm

theorem submatrix_map_toComplex {l o : Type*} (A : Matrix m n 𝕜) (e₁ : l → m) (e₂ : o → n) :
    (A.map (toComplex 𝕜)).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map (toComplex 𝕜) :=
  submatrix_map _ e₁ e₂ A

/-- The Kronecker product commutes with the entrywise embedding. -/
theorem kronecker_map_toComplex {p q : Type*} (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    A.map (toComplex 𝕜) ⊗ₖ B.map (toComplex 𝕜) = (A ⊗ₖ B).map (toComplex 𝕜) := by
  ext; simp

/-! ### Vectors -/

theorem star_comp_toComplex (v : n → 𝕜) :
    star (fun i => toComplex 𝕜 (v i)) = fun i => toComplex 𝕜 (star v i) :=
  funext fun i => (map_star (toComplex 𝕜) (v i)).symm

/-- The dot product commutes with the embedding. -/
theorem dotProduct_comp_toComplex [Fintype n] (v w : n → 𝕜) :
    (fun i => toComplex 𝕜 (v i)) ⬝ᵥ (fun i => toComplex 𝕜 (w i)) = toComplex 𝕜 (v ⬝ᵥ w) :=
  (RingHom.map_dotProduct (toComplex 𝕜 : 𝕜 →+* ℂ) v w).symm

/-- The sesquilinear pairing `star v ⬝ᵥ w` commutes with the embedding. -/
theorem star_dotProduct_comp_toComplex [Fintype n] (v w : n → 𝕜) :
    star (fun i => toComplex 𝕜 (v i)) ⬝ᵥ (fun i => toComplex 𝕜 (w i)) =
      toComplex 𝕜 (star v ⬝ᵥ w) := by
  rw [star_comp_toComplex, dotProduct_comp_toComplex]

/-- A unit vector embeds as a unit vector; the normalization `pureState` needs. -/
theorem star_dotProduct_comp_toComplex_eq_one [Fintype n] {v : n → 𝕜} (hv : star v ⬝ᵥ v = 1) :
    star (fun i => toComplex 𝕜 (v i)) ⬝ᵥ (fun i => toComplex 𝕜 (v i)) = 1 := by
  rw [star_dotProduct_comp_toComplex, hv, map_one]

/-- Matrix-vector multiplication commutes with the embedding. -/
theorem mulVec_map_toComplex [Fintype n] (A : Matrix m n 𝕜) (v : n → 𝕜) :
    A.map (toComplex 𝕜) *ᵥ (fun i => toComplex 𝕜 (v i)) = fun i => toComplex 𝕜 ((A *ᵥ v) i) :=
  funext fun i => (RingHom.map_mulVec (toComplex 𝕜 : 𝕜 →+* ℂ) A v i).symm

/-- The outer product commutes with the embedding. -/
theorem vecMulVec_comp_toComplex (v : m → 𝕜) (w : n → 𝕜) :
    vecMulVec (fun i => toComplex 𝕜 (v i)) (fun i => toComplex 𝕜 (w i)) =
      (vecMulVec v w).map (toComplex 𝕜) := by
  ext; simp [vecMulVec_apply]

/-! ### Hermiticity and the spectrum -/

/-- A matrix is Hermitian iff its embedding into `ℂ` is. -/
@[simp] theorem isHermitian_map_toComplex_iff {A : Matrix n n 𝕜} :
    (A.map (toComplex 𝕜)).IsHermitian ↔ A.IsHermitian :=
  isHermitian_map_iff (fun x => map_star (toComplex 𝕜) x) toComplex_injective

theorem isHermitian_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A.map (toComplex 𝕜)).IsHermitian :=
  isHermitian_map_toComplex_iff.2 hA

variable [Fintype n] [DecidableEq n]

/-- **Spectrum transfer**: the eigenvalue multiset of a Hermitian matrix is unchanged by the
embedding into `ℂ`. -/
theorem eigenvalues_multiset_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Finset.univ.val.map (isHermitian_map_toComplex hA).eigenvalues =
      Finset.univ.val.map hA.eigenvalues := by
  have hc : (A.map (toComplex 𝕜)).charpoly = A.charpoly.map (toComplex 𝕜 : 𝕜 →+* ℂ) :=
    charpoly_map A _
  refine Multiset.map_injective (RCLike.ofReal_injective (K := ℂ)) ?_
  rw [Multiset.map_map, Multiset.map_map,
    ← (isHermitian_map_toComplex hA).roots_charpoly_eq_eigenvalues,
    hc, hA.charpoly_eq, Polynomial.map_prod,
    Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- The von Neumann entropy is unchanged by the embedding into `ℂ`. -/
@[simp] theorem vonNeumann_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    vonNeumann (isHermitian_map_toComplex hA) = vonNeumann hA := by
  rw [vonNeumann_eq_H, vonNeumann_eq_H]
  exact H_eq_of_multiset_eq (eigenvalues_multiset_map_toComplex hA)

/-- The Shannon entropy of the spectrum is unchanged by the embedding into `ℂ`. -/
theorem H_eigenvalues_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    H (isHermitian_map_toComplex hA).eigenvalues = H hA.eigenvalues :=
  H_eq_of_multiset_eq (eigenvalues_multiset_map_toComplex hA)

/-- A property holds of every eigenvalue of a Hermitian matrix iff it holds of every
eigenvalue of its embedding into `ℂ`. -/
theorem forall_eigenvalues_map_toComplex_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (p : ℝ → Prop) :
    (∀ i, p ((isHermitian_map_toComplex hA).eigenvalues i)) ↔ ∀ i, p (hA.eigenvalues i) := by
  have h := congrArg (∀ x ∈ ·, p x) (eigenvalues_multiset_map_toComplex hA)
  simp only [Multiset.forall_mem_map_iff, Finset.mem_val, Finset.mem_univ, true_imp_iff] at h
  exact h.to_iff

omit [Fintype n] [DecidableEq n] in
/-- A matrix is positive semidefinite iff its embedding into `ℂ` is. -/
@[simp] theorem posSemidef_map_toComplex_iff [Finite n] {A : Matrix n n 𝕜} :
    (A.map (toComplex 𝕜)).PosSemidef ↔ A.PosSemidef := by
  classical
  have := Fintype.ofFinite n
  by_cases hA : A.IsHermitian
  · rw [(isHermitian_map_toComplex hA).posSemidef_iff_eigenvalues_nonneg,
      hA.posSemidef_iff_eigenvalues_nonneg]
    exact forall_eigenvalues_map_toComplex_iff hA (0 ≤ ·)
  · exact iff_of_false (fun h => hA (isHermitian_map_toComplex_iff.1 h.isHermitian))
      fun h => hA h.isHermitian

omit [Fintype n] [DecidableEq n] in
/-- The Loewner order is reflected and preserved by the embedding into `ℂ`. -/
@[simp] theorem map_toComplex_le_map_toComplex_iff [Finite n] {A B : Matrix n n 𝕜} :
    A.map (toComplex 𝕜) ≤ B.map (toComplex 𝕜) ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← map_toComplex_sub, posSemidef_map_toComplex_iff]

end Matrix

/-! ## Regions: partial trace and tensor constructions -/

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} {S T : Finset σ}

/-- The partial trace commutes with the entrywise embedding. -/
theorem ptrace_map_toComplex [∀ i, Fintype (loc i)] (h : S ⊆ T)
    (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h (M.map (toComplex 𝕜)) = (ptrace h M).map (toComplex 𝕜) := by
  ext x y
  simp [ptrace, map_sum]

/-- Extension by the identity commutes with the entrywise embedding. -/
theorem extendId_map_toComplex [∀ i, DecidableEq (loc i)] (h : S ⊆ T)
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (A.map (toComplex 𝕜)) = (extendId h A).map (toComplex 𝕜) := by
  ext w w'
  simp only [extendId, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

/-- The tensor product of disjoint regions commutes with the entrywise embedding. -/
theorem kronUnion_map_toComplex {A B : Finset σ} (hd : Disjoint A B)
    (M : Matrix (Reg loc A) (Reg loc A) 𝕜) (N : Matrix (Reg loc B) (Reg loc B) 𝕜) :
    kronUnion hd (M.map (toComplex 𝕜)) (N.map (toComplex 𝕜)) =
      (kronUnion hd M N).map (toComplex 𝕜) := by
  ext w w'
  simp [kronUnion]

end Region

end OpenAI

/-! ## States -/

namespace Arealaw

open OpenAI
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

namespace SubState

variable {ι : Type*} [Fintype ι]

/-- A subnormalized state over `𝕜`, viewed over `ℂ` through `OpenAI.toComplex`. -/
noncomputable def toComplex (ρ : SubState ι 𝕜) : SubState ι ℂ where
  M := ρ.M.map (OpenAI.toComplex 𝕜)
  psd := posSemidef_map_toComplex_iff.2 ρ.psd
  tr_le_one := by simpa [trace_map_toComplex] using ρ.tr_le_one

@[simp] theorem toComplex_M (ρ : SubState ι 𝕜) : ρ.toComplex.M = ρ.M.map (OpenAI.toComplex 𝕜) :=
  rfl

theorem toComplex_injective : Function.Injective (toComplex : SubState ι 𝕜 → SubState ι ℂ) :=
  fun _ _ h => SubState.ext (map_toComplex_injective (congrArg SubState.M h))

@[simp] theorem toComplex_complex (ρ : SubState ι ℂ) : ρ.toComplex = ρ :=
  SubState.ext (map_toComplex_complex ρ.M)

/-- **Entropy transfer**: the embedding into `ℂ` preserves the von Neumann entropy. -/
@[simp] theorem entropy_toComplex [DecidableEq ι] (ρ : SubState ι 𝕜) :
    ρ.toComplex.entropy = ρ.entropy :=
  vonNeumann_map_toComplex ρ.psd.isHermitian

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {S T U X Y : Finset σ}

/-- Restriction commutes with the embedding into `ℂ`. -/
theorem toComplex_restrict (h : S ⊆ T) (ρ : SubState (Reg loc T) 𝕜) :
    (ρ.restrict h).toComplex = ρ.toComplex.restrict h :=
  SubState.ext (ptrace_map_toComplex h ρ.M).symm

variable [∀ i, DecidableEq (loc i)]

/-- **Region-entropy transfer**: the embedding into `ℂ` preserves every region entropy. -/
@[simp] theorem regionEntropy_toComplex (ρ : SubState (Reg loc U) 𝕜) (h : X ⊆ U) :
    ρ.toComplex.regionEntropy h = ρ.regionEntropy h := by
  rw [regionEntropy_def, regionEntropy_def, ← toComplex_restrict, entropy_toComplex]

/-- **Mutual-information transfer**: the embedding into `ℂ` preserves mutual information. -/
@[simp] theorem mutualInfo_toComplex (ρ : SubState (Reg loc U) 𝕜) (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.toComplex.mutualInfo hX hY = ρ.mutualInfo hX hY := by
  simp only [mutualInfo_def, regionEntropy_toComplex]

end SubState

namespace MState

variable {ι : Type*} [Fintype ι]

/-- A normalized state over `𝕜`, viewed over `ℂ` through `OpenAI.toComplex`. -/
noncomputable def toComplex (ρ : MState ι 𝕜) : MState ι ℂ :=
  ⟨ρ.toSubState.toComplex, by simpa [trace_map_toComplex] using ρ.tr_eq_one⟩

@[simp] theorem toComplex_M (ρ : MState ι 𝕜) : ρ.toComplex.M = ρ.M.map (OpenAI.toComplex 𝕜) :=
  rfl

@[simp] theorem toSubState_toComplex (ρ : MState ι 𝕜) :
    ρ.toComplex.toSubState = ρ.toSubState.toComplex :=
  rfl

theorem toComplex_injective : Function.Injective (toComplex : MState ι 𝕜 → MState ι ℂ) :=
  fun _ _ h => MState.ext (map_toComplex_injective (congrArg (·.M) h))

@[simp] theorem toComplex_complex (ρ : MState ι ℂ) : ρ.toComplex = ρ :=
  MState.ext (map_toComplex_complex ρ.M)

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)] {S T : Finset σ}

/-- Restriction of a normalized state commutes with the embedding into `ℂ`. -/
theorem toComplex_restrict (h : S ⊆ T) (ρ : MState (Reg loc T) 𝕜) :
    (ρ.restrict h).toComplex = ρ.toComplex.restrict h :=
  MState.ext (ptrace_map_toComplex h ρ.M).symm

end MState

end Arealaw

/-! ## Operator norm and Hamiltonians -/

namespace OpenAI

open Arealaw
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Pure-state transfer**: `|Ω⟩⟨Ω|` over `𝕜`, embedded into `ℂ`, is the pure state of the
embedded vector. -/
theorem pureState_toComplex {ι : Type*} [Fintype ι] (Ω : ι → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) :
    (pureState Ω hΩ).toComplex =
      pureState (fun i => toComplex 𝕜 (Ω i)) (star_dotProduct_comp_toComplex_eq_one hΩ) := by
  ext : 1
  simp only [MState.toComplex_M, pureState, MState.mk'_M, star_comp_toComplex,
    vecMulVec_comp_toComplex]

section OpNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The operator norm of a Hermitian matrix is the largest modulus of an eigenvalue, read as a
supremum in `ℝ≥0∞`. -/
theorem nnnorm_eq_iSup_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (‖A‖₊ : ℝ≥0∞) = ⨆ x ∈ Set.range hA.eigenvalues, (‖x‖₊ : ℝ≥0∞) := by
  have h : (‖A‖₊ : ℝ≥0∞) = spectralRadius 𝕜 A := by
    have hT : IsSelfAdjoint (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := hA.isSelfAdjoint.map _
    rw [spectralRadius, ← AlgEquiv.spectrum_eq (toEuclideanCLM (n := n) (𝕜 := 𝕜)) A]
    exact (ContinuousLinearMap.spectralRadius_eq_nnnorm _ hT).symm
  rw [h, spectralRadius, hA.spectrum_eq_image_range, iSup_image]
  simp

/-- The set of eigenvalues of a Hermitian matrix is unchanged by the embedding into `ℂ`. -/
theorem range_eigenvalues_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Set.range (isHermitian_map_toComplex hA).eigenvalues = Set.range hA.eigenvalues := by
  ext x
  simpa using congrArg (x ∈ ·) (eigenvalues_multiset_map_toComplex hA)

/-- The embedding into `ℂ` preserves the operator norm of a Hermitian matrix. -/
theorem norm_map_toComplex_of_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ‖A.map (toComplex 𝕜)‖ = ‖A‖ := by
  have h := nnnorm_eq_iSup_eigenvalues (isHermitian_map_toComplex hA)
  rw [range_eigenvalues_map_toComplex hA, ← nnnorm_eq_iSup_eigenvalues hA, ENNReal.coe_inj] at h
  exact congrArg NNReal.toReal h

/-- **Operator-norm transfer**: the embedding into `ℂ` preserves the `L²` operator norm. -/
@[simp] theorem norm_map_toComplex (A : Matrix m n 𝕜) : ‖A.map (toComplex 𝕜)‖ = ‖A‖ := by
  classical
  have h := norm_map_toComplex_of_isHermitian (isHermitian_conjTranspose_mul_self A)
  rw [map_toComplex_mul, ← conjTranspose_map_toComplex, l2_opNorm_conjTranspose_mul_self,
    l2_opNorm_conjTranspose_mul_self] at h
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h

end OpNorm

section Vector

variable {ι : Type*}

theorem comp_toComplex_injective :
    Function.Injective (fun (v : ι → 𝕜) (i : ι) => toComplex 𝕜 (v i)) :=
  fun _ _ h => funext fun i => toComplex_injective (congrFun h i)

theorem smul_comp_toComplex (c : 𝕜) (v : ι → 𝕜) :
    toComplex 𝕜 c • (fun i => toComplex 𝕜 (v i)) = fun i => toComplex 𝕜 ((c • v) i) := by
  ext; simp

variable [Fintype ι]

/-- An eigenvector equation transfers along the embedding into `ℂ`, in both directions. -/
theorem mulVec_map_toComplex_eq_smul_iff (A : Matrix ι ι 𝕜) (v : ι → 𝕜) (c : 𝕜) :
    A.map (toComplex 𝕜) *ᵥ (fun i => toComplex 𝕜 (v i)) =
        toComplex 𝕜 c • (fun i => toComplex 𝕜 (v i)) ↔ A *ᵥ v = c • v := by
  rw [mulVec_map_toComplex, smul_comp_toComplex, comp_toComplex_injective.eq_iff]

/-- **Gap transfer**: the global gap holds over `𝕜` iff it holds after embedding into `ℂ`. -/
@[simp] theorem hasGlobalGap_map_toComplex_iff [DecidableEq ι] (H : Matrix ι ι 𝕜) (Ω : ι → 𝕜)
    (E₀ Δ : ℝ) :
    HasGlobalGap (H.map (toComplex 𝕜)) (fun i => toComplex 𝕜 (Ω i)) E₀ Δ ↔
      HasGlobalGap H Ω E₀ Δ := by
  have hΔ : ((Δ : 𝕜) • (1 - vecMulVec Ω (star Ω))).map (toComplex 𝕜) =
      (Δ : ℂ) • (1 - vecMulVec (fun i => toComplex 𝕜 (Ω i)) (star fun i => toComplex 𝕜 (Ω i))) := by
    rw [map_toComplex_smul, toComplex_ofReal, map_toComplex_sub, map_toComplex_one,
      star_comp_toComplex, vecMulVec_comp_toComplex]
  have hE : (H - (E₀ : 𝕜) • 1).map (toComplex 𝕜) = H.map (toComplex 𝕜) - (E₀ : ℂ) • 1 := by
    rw [map_toComplex_sub, map_toComplex_smul, toComplex_ofReal, map_toComplex_one]
  rw [HasGlobalGap, HasGlobalGap, ← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), hΔ, hE]
  -- `HasGlobalGap` over `ℂ` casts through `RCLike.ofReal`, `hΔ` and `hE` through
  -- `Complex.ofReal`; the two agree definitionally.
  rfl

end Vector

section Hamiltonian

variable {q : ℕ}

/-- The Hamiltonian of the embedded interaction is the embedded Hamiltonian. -/
theorem hamiltonian_map_toComplex (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) :
    hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)) = (hamiltonian Λ Φ).map (toComplex 𝕜) := by
  simp only [hamiltonian, map_toComplex_sum, extendId_map_toComplex]

/-- **Admissibility transfer**: an interaction is admissible iff its embedding into `ℂ` is. -/
@[simp] theorem isAdmissible_map_toComplex_iff (Λ : Finset (ℤ × ℤ)) (R : ℕ) (J : ℝ)
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) :
    IsAdmissible Λ R J (fun X => (Φ X).map (toComplex 𝕜)) ↔ IsAdmissible Λ R J Φ := by
  simp only [IsAdmissible, isHermitian_map_toComplex_iff, norm_map_toComplex,
    map_toComplex_eq_zero_iff]

end Hamiltonian

end OpenAI
