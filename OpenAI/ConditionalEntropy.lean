import OpenAI.EntropyMixing
import Arealaw.Bridge.VonNeumann
import Arealaw.EntropyBounds

/-!
# Conditional entropy of positive semidefinite matrices

For a positive semidefinite `A` on `D ⊗ E`, of arbitrary trace, the conditional entropy is
`S(D|E)_A = S(A) - S(tr_D A)`, with `S` the von Neumann entropy `Arealaw.vonNeumann` and
`tr_D` Physlib's `Matrix.traceLeft`.  This file proves the three bipartite facts the
Alicki–Fannes–Winter argument for Lemma 2.1 of [OAI265] uses, writing `η(x) = -x log x`:

* superadditivity, `S(D|E)_A + S(D|E)_B ≤ S(D|E)_{A+B}`;
* the matching upper bound, `S(D|E)_{A+B} ≤ S(D|E)_A + S(D|E)_B + η(tr A) + η(tr B) - η(tr(A+B))`;
* the dimension bound, `|S(D|E)_A| ≤ tr A · log dim D`.

Superadditivity is strong subadditivity for the classical–quantum matrix `⊕ₖ Aₖ` on
`D ⊗ E ⊗ K`, `K` a label register: its entropy is `∑ₖ S(Aₖ)` and that of its `E K` marginal
is `∑ₖ S(tr_D Aₖ)`.  Specialized to a one-dimensional `E` it is concavity of the entropy in
the unnormalized form `S(A) - η(tr A) + S(B) - η(tr B) ≤ S(A+B) - η(tr(A+B))`, and the upper
bound is subadditivity `S(A + B) ≤ S(A) + S(B)` on `D ⊗ E` together with this concavity on
`E`.  The dimension bound combines subadditivity and the Araki–Lieb inequality with
`S(tr_E A) ≤ tr A · log dim D + η(tr A)`.

## Main statements

* `Arealaw.vonNeumann_sub_traceLeft_add_le`: superadditivity; the finite-family form is
  `Arealaw.sum_vonNeumann_sub_traceLeft_le`.
* `Arealaw.vonNeumann_sub_traceLeft_add_le_add`: the upper bound.
* `Arealaw.abs_vonNeumann_sub_traceLeft_le`: the dimension bound.
* `Arealaw.vonNeumann_strong_subadditivity`, `Arealaw.vonNeumann_add_negMulLog_le`,
  `Arealaw.abs_vonNeumann_traceRight_sub_traceLeft_le`: strong subadditivity,
  subadditivity and Araki–Lieb for positive semidefinite matrices of any trace.
* `Arealaw.vonNeumann_blockDiagonal`: the entropy of a block-diagonal matrix is the sum of
  the entropies of its blocks.

## Implementation notes

Physlib proves strong subadditivity (`Sᵥₙ_strong_subadditivity`), subadditivity
(`Sᵥₙ_subadditivity`) and Araki–Lieb (`Sᵥₙ_triangle_subaddivity`) for normalized states over
`ℂ` only.  Their unnormalized forms are therefore proved over `ℂ` first
(`vonNeumann_strong_subadditivity_complex` and its two neighbours): a nonzero positive
semidefinite matrix is `t ρ` with `t > 0` and `ρ` a state, the scaling law
`Arealaw.vonNeumann_smul` moves every term from `ρ` to `t ρ`, and the zero matrix is a
separate case.  They are carried to a general `RCLike` field by the entrywise embedding
`OpenAI.toComplex`, which commutes with both partial traces and preserves positive
semidefiniteness and the entropy.  Everything downstream of these three lemmas is proved
over `𝕜` directly.

The conditional entropy is not given a definition: the statements carry the difference
`S(A) - S(tr_D A)` explicitly, as Lemma 2.1 of [OAI265] does.

The proof structure is ported from QICLean, `QICLean/Entropy/ConditionalEntropy.lean`
(`sum_conditionalEntropy_le`, `sum_vonNeumannEntropy_sub_negMulLog_le`,
`conditionalEntropy_sum_le`, `abs_conditionalEntropy_le_log_card`) and
`QICLean/Entropy/ControlledContinuity.lean`
(`abs_conditionalEntropy_le_re_trace_mul_log_card`) at commit `32a5a1a8` (Apache 2.0),
itself adapted from `openai/math` at commit `adc7f1241b42`, files
`lean/OAI/MathematicalPhysics/PEPSMove/EntropyBounds.lean` (`conditional_superadditive`,
`entropy_homogeneous_concave`, `conditional_add_upper`) and
`lean/OAI/MathematicalPhysics/PEPSMove/PureEntropy.lean` (`conditional_abs_le`).  The
changes: the statements are about `Arealaw.vonNeumann` and Physlib's `traceLeft` over a
general `RCLike` field; strong subadditivity, subadditivity and Araki–Lieb are Physlib's,
extended to unnormalized matrices by scaling, rather than QICLean's; the entropy of a
block-diagonal matrix is computed from its characteristic polynomial; and the dimension
bound is proved for matrices of any trace in one step, without a normalized version.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §2, Lemma 2.1.
* A. Winter, *Tight uniform continuity bounds for quantum entropies*, Commun. Math. Phys. 347
  (2016), Lemma 2.
-/

namespace Arealaw

open Matrix
open scoped ComplexOrder

section Basic

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The entropy depends only on the matrix, not on the Hermiticity proof. -/
theorem vonNeumann_congr {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : vonNeumann hA = vonNeumann hB := by
  subst h; rfl

/-- The zero matrix has zero entropy. -/
theorem vonNeumann_eq_zero_of_eq_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian) (h : A = 0) :
    vonNeumann hA = 0 := by
  rw [vonNeumann_eq_H, (hA.eigenvalues_eq_zero_iff).2 h]
  simp [H]

/-- The scaling law `S(tB) = t S(B) + η(t) Re tr B`, read off a matrix equal to `t • B`. -/
theorem vonNeumann_of_eq_smul {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {t : ℝ} (h : A = t • B) :
    vonNeumann hA = t * vonNeumann hB + Real.negMulLog t * RCLike.re B.trace :=
  (vonNeumann_congr hA (hB.smul_real t) h).trans (vonNeumann_smul hB t)

/-- On a one-dimensional space the entropy is `η(Re tr A)`. -/
theorem vonNeumann_of_unique [Unique n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    vonNeumann hA = Real.negMulLog (RCLike.re A.trace) := by
  rw [vonNeumann_eq_H, H, hA.trace_eq_sum_eigenvalues, Fintype.sum_unique, Fintype.sum_unique,
    RCLike.ofReal_re]

omit [DecidableEq n] in
/-- A nonzero positive semidefinite matrix is a positive multiple of one of unit trace. -/
theorem exists_eq_smul_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h0 : A ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∃ ρ : Matrix n n 𝕜, A = t • ρ ∧ ρ.PosSemidef ∧ RCLike.re ρ.trace = 1 := by
  have htr := RCLike.nonneg_iff.1 hA.trace_nonneg
  have ht : 0 < RCLike.re A.trace := by
    refine htr.1.lt_of_ne fun h => h0 (hA.trace_eq_zero_iff.1 ?_)
    exact RCLike.ext (by simpa using h.symm) (by simpa using htr.2)
  refine ⟨RCLike.re A.trace, ht, (RCLike.re A.trace)⁻¹ • A, ?_, hA.smul (inv_nonneg.2 ht.le), ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  · rw [trace_smul, RCLike.smul_re, inv_mul_cancel₀ ht.ne']

end Basic

/-! ## Block-diagonal matrices -/

section BlockDiagonal

variable {𝕜 : Type*} [RCLike 𝕜] {n o : Type*} [Fintype n] [DecidableEq n] [Fintype o]
  [DecidableEq o]

/-- The characteristic polynomial of a block-diagonal matrix is the product of those of its
blocks. -/
theorem charpoly_blockDiagonal {R : Type*} [CommRing R] (M : o → Matrix n n R) :
    (blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  have h : charmatrix (blockDiagonal M) = blockDiagonal fun k => charmatrix (M k) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst hkl
      by_cases hij : i = j
      · subst hij; simp [blockDiagonal_apply]
      · simp [blockDiagonal_apply, hij]
    · simp [blockDiagonal_apply, hkl]
  rw [charpoly, h, det_blockDiagonal]
  rfl

/-- The eigenvalues of a Hermitian block-diagonal matrix, with multiplicity, are those of its
blocks. -/
theorem eigenvalues_multiset_blockDiagonal {M : o → Matrix n n 𝕜}
    (hM : ∀ k, (M k).IsHermitian) :
    Finset.univ.val.map (isHermitian_blockDiagonal_iff.2 hM).eigenvalues =
      Finset.univ.val.bind fun k => Finset.univ.val.map (hM k).eigenvalues := by
  refine Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_
  rw [Multiset.map_map, Multiset.map_bind,
    ← (isHermitian_blockDiagonal_iff.2 hM).roots_charpoly_eq_eigenvalues,
    charpoly_blockDiagonal, Polynomial.roots_prod]
  · exact Multiset.bind_congr fun k _ => by
      rw [(hM k).roots_charpoly_eq_eigenvalues, Multiset.map_map]
  · exact Finset.prod_ne_zero_iff.2 fun k _ => (Matrix.charpoly_monic _).ne_zero

/-- **Additivity of the entropy over blocks**: `S(⊕ₖ Mₖ) = ∑ₖ S(Mₖ)`. -/
theorem vonNeumann_blockDiagonal {M : o → Matrix n n 𝕜} (hM : ∀ k, (M k).IsHermitian) :
    vonNeumann (isHermitian_blockDiagonal_iff.2 hM) = ∑ k, vonNeumann (hM k) := by
  simp only [vonNeumann_eq_H, H_eq_multiset_sum, eigenvalues_multiset_blockDiagonal hM,
    Multiset.map_bind, Multiset.sum_bind]
  rfl

omit [Fintype n] [DecidableEq n] [Fintype o] in
/-- A block-diagonal matrix with positive semidefinite blocks is positive semidefinite. -/
theorem posSemidef_blockDiagonal [Finite n] [Finite o] {M : o → Matrix n n 𝕜}
    (hM : ∀ k, (M k).PosSemidef) : (blockDiagonal M).PosSemidef := by
  classical
  have := Fintype.ofFinite n
  have := Fintype.ofFinite o
  have hH := isHermitian_blockDiagonal_iff.2 fun k => (hM k).isHermitian
  refine hH.posSemidef_iff_eigenvalues_nonneg.2 fun i => ?_
  have hi : hH.eigenvalues i ∈ Finset.univ.val.map hH.eigenvalues :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  rw [eigenvalues_multiset_blockDiagonal fun k => (hM k).isHermitian] at hi
  obtain ⟨k, -, hk⟩ := Multiset.mem_bind.1 hi
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hk
  exact hj ▸ (hM k).eigenvalues_nonneg j

end BlockDiagonal

/-! ## Partial traces -/

section PartialTrace

variable {R : Type*} {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
@[simp] theorem traceLeft_zero [AddCommMonoid R] :
    (0 : Matrix (m × n) (m × n) R).traceLeft = 0 := by
  ext; simp [traceLeft]

omit [Fintype m] in
@[simp] theorem traceRight_zero [AddCommMonoid R] :
    (0 : Matrix (m × n) (m × n) R).traceRight = 0 := by
  ext; simp [traceRight]

omit [Fintype n] in
/-- Tracing out the first factor commutes with finite sums. -/
theorem traceLeft_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (m × n) (m × n) R) : (∑ k ∈ s, A k).traceLeft = ∑ k ∈ s, (A k).traceLeft := by
  ext; simp only [traceLeft, of_apply, Matrix.sum_apply]; exact Finset.sum_comm

omit [Fintype m] [Fintype n] in
/-- Tracing out the label of a block-diagonal matrix sums its blocks. -/
theorem traceRight_blockDiagonal [AddCommMonoid R] {o : Type*} [Fintype o] [DecidableEq o]
    (M : o → Matrix n n R) : (blockDiagonal M).traceRight = ∑ k, M k := by
  ext; simp [traceRight, blockDiagonal_apply, Matrix.sum_apply]

omit [Fintype n] in
/-- Tracing out the first factor of a block-diagonal matrix acts blockwise. -/
theorem traceLeft_submatrix_blockDiagonal [AddCommMonoid R] {o : Type*} [DecidableEq o]
    (M : o → Matrix (m × n) (m × n) R) :
    ((blockDiagonal M).submatrix (Equiv.prodAssoc m n o).symm
        (Equiv.prodAssoc m n o).symm).traceLeft = blockDiagonal fun k => (M k).traceLeft := by
  ext ⟨j, k⟩ ⟨j', k'⟩
  by_cases h : k = k' <;> simp [traceLeft, blockDiagonal_apply, h]

end PartialTrace

end Arealaw

namespace OpenAI

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
/-- Tracing out the first factor commutes with the entrywise embedding into `ℂ`. -/
theorem traceLeft_map_toComplex (A : Matrix (m × n) (m × n) 𝕜) :
    (A.map (toComplex 𝕜)).traceLeft = A.traceLeft.map (toComplex 𝕜) := by
  ext; simp [traceLeft, map_sum]

omit [Fintype m] in
/-- Tracing out the second factor commutes with the entrywise embedding into `ℂ`. -/
theorem traceRight_map_toComplex (A : Matrix (m × n) (m × n) 𝕜) :
    (A.map (toComplex 𝕜)).traceRight = A.traceRight.map (toComplex 𝕜) := by
  ext; simp [traceRight, map_sum]

omit [Fintype n] in
/-- The real part of the trace is unchanged by the embedding into `ℂ`. -/
theorem re_trace_map_toComplex (A : Matrix m m 𝕜) :
    (A.map (toComplex 𝕜)).trace.re = RCLike.re A.trace := by
  rw [trace_map_toComplex, re_toComplex]

variable [DecidableEq m]

omit [Fintype n] in
/-- The entropy of a complex matrix that is the embedding of one over `𝕜`. -/
theorem vonNeumann_of_eq_map_toComplex {X : Matrix m m ℂ} {Y : Matrix m m 𝕜}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : X = Y.map (toComplex 𝕜)) :
    Arealaw.vonNeumann hX = Arealaw.vonNeumann hY :=
  (Arealaw.vonNeumann_congr hX (isHermitian_map_toComplex hY) h).trans
    (vonNeumann_map_toComplex hY)

end OpenAI

namespace Arealaw

open Matrix
open scoped ComplexOrder

/-! ## Physlib's entropy inequalities, unnormalized -/

section Physlib

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Physlib's `Sᵥₙ` of a state is the `vonNeumann` entropy of its density matrix. -/
theorem Sᵥₙ_eq_vonNeumann (Q : _root_.MState d) {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (h : Q.m = A) : Sᵥₙ Q = vonNeumann hA := by
  subst h
  exact MState.Sᵥₙ_physlibEquiv (MState.physlibEquiv.symm Q)

variable {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
  [Fintype d₃] [DecidableEq d₃]

-- `ℂ` only: Physlib's `Sᵥₙ_strong_subadditivity` is `ℂ`-only; see the implementation notes.
/-- Strong subadditivity `S(ABC) + S(B) ≤ S(AB) + S(BC)` for a positive semidefinite complex
`ω` of any trace. -/
theorem vonNeumann_strong_subadditivity_complex {ω : Matrix (d₁ × d₂ × d₃) (d₁ × d₂ × d₃) ℂ}
    (hω : ω.PosSemidef) :
    vonNeumann hω.isHermitian + vonNeumann hω.isHermitian.traceLeft.traceRight ≤
      vonNeumann (hω.isHermitian.submatrix (Equiv.prodAssoc d₁ d₂ d₃)).traceRight +
        vonNeumann hω.isHermitian.traceLeft := by
  by_cases h0 : ω = 0
  · subst h0
    rw [vonNeumann_eq_zero_of_eq_zero _ rfl, vonNeumann_eq_zero_of_eq_zero _ (by simp),
      vonNeumann_eq_zero_of_eq_zero _ (by simp), vonNeumann_eq_zero_of_eq_zero _ (by simp)]
  obtain ⟨t, ht, ρ, rfl, hρ, hρ1⟩ := exists_eq_smul_of_posSemidef hω h0
  have hssa := Sᵥₙ_strong_subadditivity (MState.physlibEquiv (MState.mk' hρ hρ1))
  dsimp only at hssa
  rw [Sᵥₙ_eq_vonNeumann _ hρ.isHermitian rfl,
    Sᵥₙ_eq_vonNeumann _ hρ.isHermitian.traceLeft.traceRight rfl,
    Sᵥₙ_eq_vonNeumann _ (hρ.isHermitian.submatrix (Equiv.prodAssoc d₁ d₂ d₃)).traceRight rfl,
    Sᵥₙ_eq_vonNeumann _ hρ.isHermitian.traceLeft rfl] at hssa
  rw [vonNeumann_of_eq_smul _ hρ.isHermitian (t := t) rfl,
    vonNeumann_of_eq_smul _ hρ.isHermitian.traceLeft.traceRight (t := t) (by simp),
    vonNeumann_of_eq_smul _ (hρ.isHermitian.submatrix (Equiv.prodAssoc d₁ d₂ d₃)).traceRight
      (t := t) (by simp [submatrix_smul]),
    vonNeumann_of_eq_smul _ hρ.isHermitian.traceLeft (t := t) (by simp)]
  simp only [traceLeft_trace, traceRight_trace, trace_submatrix, hρ1]
  nlinarith

-- `ℂ` only: Physlib's `Sᵥₙ_subadditivity` is `ℂ`-only; see the implementation notes.
/-- Subadditivity `S(AB) + η(tr ω) ≤ S(A) + S(B)` for a positive semidefinite complex `ω`. -/
theorem vonNeumann_add_negMulLog_le_complex {ω : Matrix (d₁ × d₂) (d₁ × d₂) ℂ}
    (hω : ω.PosSemidef) :
    vonNeumann hω.isHermitian + Real.negMulLog (RCLike.re ω.trace) ≤
      vonNeumann hω.isHermitian.traceRight + vonNeumann hω.isHermitian.traceLeft := by
  by_cases h0 : ω = 0
  · subst h0
    rw [vonNeumann_eq_zero_of_eq_zero _ rfl, vonNeumann_eq_zero_of_eq_zero _ (by simp),
      vonNeumann_eq_zero_of_eq_zero _ (by simp)]
    simp
  obtain ⟨t, ht, ρ, rfl, hρ, hρ1⟩ := exists_eq_smul_of_posSemidef hω h0
  have h := Sᵥₙ_subadditivity (MState.physlibEquiv (MState.mk' hρ hρ1))
  rw [Sᵥₙ_eq_vonNeumann _ hρ.isHermitian rfl, Sᵥₙ_eq_vonNeumann _ hρ.isHermitian.traceRight rfl,
    Sᵥₙ_eq_vonNeumann _ hρ.isHermitian.traceLeft rfl] at h
  rw [vonNeumann_of_eq_smul _ hρ.isHermitian (t := t) rfl,
    vonNeumann_of_eq_smul _ hρ.isHermitian.traceRight (t := t) (by simp),
    vonNeumann_of_eq_smul _ hρ.isHermitian.traceLeft (t := t) (by simp)]
  simp only [traceLeft_trace, traceRight_trace, trace_smul, RCLike.smul_re, hρ1, mul_one]
  nlinarith

-- `ℂ` only: Physlib's `Sᵥₙ_triangle_subaddivity` is `ℂ`-only; see the implementation notes.
/-- Araki–Lieb `|S(A) - S(B)| ≤ S(AB) - η(tr ω)` for a positive semidefinite complex `ω`. -/
theorem abs_vonNeumann_traceRight_sub_traceLeft_le_complex {ω : Matrix (d₁ × d₂) (d₁ × d₂) ℂ}
    (hω : ω.PosSemidef) :
    |vonNeumann hω.isHermitian.traceRight - vonNeumann hω.isHermitian.traceLeft| ≤
      vonNeumann hω.isHermitian - Real.negMulLog (RCLike.re ω.trace) := by
  by_cases h0 : ω = 0
  · subst h0
    rw [vonNeumann_eq_zero_of_eq_zero _ rfl, vonNeumann_eq_zero_of_eq_zero _ (by simp),
      vonNeumann_eq_zero_of_eq_zero _ (by simp)]
    simp
  obtain ⟨t, ht, ρ, rfl, hρ, hρ1⟩ := exists_eq_smul_of_posSemidef hω h0
  have h := Sᵥₙ_triangle_subaddivity (MState.physlibEquiv (MState.mk' hρ hρ1))
  rw [Sᵥₙ_eq_vonNeumann _ hρ.isHermitian rfl, Sᵥₙ_eq_vonNeumann _ hρ.isHermitian.traceRight rfl,
    Sᵥₙ_eq_vonNeumann _ hρ.isHermitian.traceLeft rfl] at h
  rw [vonNeumann_of_eq_smul _ hρ.isHermitian (t := t) rfl,
    vonNeumann_of_eq_smul _ hρ.isHermitian.traceRight (t := t) (by simp),
    vonNeumann_of_eq_smul _ hρ.isHermitian.traceLeft (t := t) (by simp)]
  simp only [traceLeft_trace, traceRight_trace, trace_smul, RCLike.smul_re, hρ1, mul_one]
  rw [add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_pos ht, add_sub_cancel_right]
  exact mul_le_mul_of_nonneg_left h ht.le

end Physlib

/-! ## The inequalities over `𝕜` -/

section Transfer

variable {𝕜 : Type*} [RCLike 𝕜]
  {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
  [Fintype d₃] [DecidableEq d₃]

open OpenAI in
/-- **Strong subadditivity, unnormalized**: `S(ABC) + S(B) ≤ S(AB) + S(BC)` for a positive
semidefinite `ω` on `A ⊗ B ⊗ C`. -/
theorem vonNeumann_strong_subadditivity {ω : Matrix (d₁ × d₂ × d₃) (d₁ × d₂ × d₃) 𝕜}
    (hω : ω.PosSemidef) :
    vonNeumann hω.isHermitian + vonNeumann hω.isHermitian.traceLeft.traceRight ≤
      vonNeumann (hω.isHermitian.submatrix (Equiv.prodAssoc d₁ d₂ d₃)).traceRight +
        vonNeumann hω.isHermitian.traceLeft := by
  have h := vonNeumann_strong_subadditivity_complex (posSemidef_map_toComplex_iff.2 hω)
  rwa [vonNeumann_of_eq_map_toComplex _ hω.isHermitian rfl,
    vonNeumann_of_eq_map_toComplex _ hω.isHermitian.traceLeft.traceRight
      (by rw [traceLeft_map_toComplex, traceRight_map_toComplex]),
    vonNeumann_of_eq_map_toComplex _ (hω.isHermitian.submatrix _).traceRight
      (by rw [submatrix_map_toComplex, traceRight_map_toComplex]),
    vonNeumann_of_eq_map_toComplex _ hω.isHermitian.traceLeft (traceLeft_map_toComplex ω)] at h

open OpenAI in
/-- **Subadditivity, unnormalized**: `S(AB) + η(tr ω) ≤ S(A) + S(B)` for positive
semidefinite `ω` on `A ⊗ B`, with `η(x) = -x log x`. -/
theorem vonNeumann_add_negMulLog_le {ω : Matrix (d₁ × d₂) (d₁ × d₂) 𝕜} (hω : ω.PosSemidef) :
    vonNeumann hω.isHermitian + Real.negMulLog (RCLike.re ω.trace) ≤
      vonNeumann hω.isHermitian.traceRight + vonNeumann hω.isHermitian.traceLeft := by
  have h := vonNeumann_add_negMulLog_le_complex (posSemidef_map_toComplex_iff.2 hω)
  rwa [vonNeumann_of_eq_map_toComplex _ hω.isHermitian rfl,
    vonNeumann_of_eq_map_toComplex _ hω.isHermitian.traceRight (traceRight_map_toComplex ω),
    vonNeumann_of_eq_map_toComplex _ hω.isHermitian.traceLeft (traceLeft_map_toComplex ω),
    RCLike.re_to_complex, re_trace_map_toComplex] at h

open OpenAI in
/-- **Araki–Lieb, unnormalized**: `|S(A) - S(B)| ≤ S(AB) - η(tr ω)` for positive
semidefinite `ω` on `A ⊗ B`. -/
theorem abs_vonNeumann_traceRight_sub_traceLeft_le {ω : Matrix (d₁ × d₂) (d₁ × d₂) 𝕜}
    (hω : ω.PosSemidef) :
    |vonNeumann hω.isHermitian.traceRight - vonNeumann hω.isHermitian.traceLeft| ≤
      vonNeumann hω.isHermitian - Real.negMulLog (RCLike.re ω.trace) := by
  have h := abs_vonNeumann_traceRight_sub_traceLeft_le_complex (posSemidef_map_toComplex_iff.2 hω)
  rwa [vonNeumann_of_eq_map_toComplex _ hω.isHermitian rfl,
    vonNeumann_of_eq_map_toComplex _ hω.isHermitian.traceRight (traceRight_map_toComplex ω),
    vonNeumann_of_eq_map_toComplex _ hω.isHermitian.traceLeft (traceLeft_map_toComplex ω),
    RCLike.re_to_complex, re_trace_map_toComplex] at h

end Transfer

/-- **Dimension bound, unnormalized**: `S(X) ≤ tr X · log d + η(tr X)` for positive
semidefinite `X` on a `d`-dimensional space. -/
theorem vonNeumann_le_re_trace_mul_log_card_add {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {X : Matrix n n 𝕜} (hX : X.PosSemidef) :
    vonNeumann hX.isHermitian ≤
      RCLike.re X.trace * Real.log (Fintype.card n) + Real.negMulLog (RCLike.re X.trace) := by
  by_cases h0 : X = 0
  · subst h0
    rw [vonNeumann_eq_zero_of_eq_zero _ rfl]
    simp
  obtain ⟨t, ht, ρ, rfl, hρ, hρ1⟩ := exists_eq_smul_of_posSemidef hX h0
  have h := entropy_le_log_card hρ hρ1
  rw [← vonNeumann_eq_H] at h
  rw [vonNeumann_of_eq_smul _ hρ.isHermitian (t := t) rfl, trace_smul, RCLike.smul_re, hρ1]
  simp only [mul_one]
  nlinarith

/-! ## Conditional entropy -/

section Conditional

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

/-- **Superadditivity of the conditional entropy over a family**:
`∑ₖ S(D|E)_{Aₖ} ≤ S(D|E)_{∑ₖ Aₖ}` for positive semidefinite `Aₖ` on `D ⊗ E`. -/
theorem sum_vonNeumann_sub_traceLeft_le {ι : Type*} [Fintype ι]
    (A : ι → Matrix (m × n) (m × n) 𝕜) (hA : ∀ k, (A k).PosSemidef) :
    ∑ k, (vonNeumann (hA k).isHermitian - vonNeumann (hA k).isHermitian.traceLeft) ≤
      vonNeumann (posSemidef_sum Finset.univ fun k _ => hA k).isHermitian -
        vonNeumann (posSemidef_sum Finset.univ fun k _ => hA k).isHermitian.traceLeft := by
  classical
  have hblock := posSemidef_blockDiagonal hA
  have hω := hblock.submatrix (Equiv.prodAssoc m n ι).symm
  have h := vonNeumann_strong_subadditivity hω
  have e₁ : vonNeumann hω.isHermitian = ∑ k, vonNeumann (hA k).isHermitian := by
    rw [vonNeumann_congr hω.isHermitian (hblock.isHermitian.submatrix _) rfl,
      vonNeumann_submatrix_equiv hblock.isHermitian,
      vonNeumann_congr hblock.isHermitian
        (isHermitian_blockDiagonal_iff.2 fun k => (hA k).isHermitian) rfl,
      vonNeumann_blockDiagonal]
  have e₂ : vonNeumann hω.isHermitian.traceLeft = ∑ k, vonNeumann (hA k).isHermitian.traceLeft := by
    rw [vonNeumann_congr _ (isHermitian_blockDiagonal_iff.2 fun k => (hA k).isHermitian.traceLeft)
      (traceLeft_submatrix_blockDiagonal A), vonNeumann_blockDiagonal]
  have e₃ : vonNeumann hω.isHermitian.traceLeft.traceRight =
      vonNeumann (posSemidef_sum Finset.univ fun k _ => hA k).isHermitian.traceLeft :=
    vonNeumann_congr _ _ (by
      rw [traceLeft_submatrix_blockDiagonal, traceRight_blockDiagonal, traceLeft_sum])
  have e₄ : vonNeumann (hω.isHermitian.submatrix (Equiv.prodAssoc m n ι)).traceRight =
      vonNeumann (posSemidef_sum Finset.univ fun k _ => hA k).isHermitian :=
    vonNeumann_congr _ _ (by
      rw [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, traceRight_blockDiagonal])
  rw [Finset.sum_sub_distrib]
  linarith

/-- **Superadditivity of the conditional entropy**: `S(D|E)_A + S(D|E)_B ≤ S(D|E)_{A+B}` for
positive semidefinite `A, B` on `D ⊗ E`. -/
theorem vonNeumann_sub_traceLeft_add_le {A B : Matrix (m × n) (m × n) 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    (vonNeumann hA.isHermitian - vonNeumann hA.isHermitian.traceLeft) +
        (vonNeumann hB.isHermitian - vonNeumann hB.isHermitian.traceLeft) ≤
      vonNeumann (hA.add hB).isHermitian - vonNeumann (hA.add hB).isHermitian.traceLeft := by
  have hAB : ∀ k, (![A, B] k).PosSemidef := Fin.forall_fin_two.2 ⟨hA, hB⟩
  have h := sum_vonNeumann_sub_traceLeft_le ![A, B] hAB
  have e : ∑ k, ![A, B] k = A + B := by simp [Fin.sum_univ_two]
  rw [vonNeumann_congr _ (hA.add hB).isHermitian e,
    vonNeumann_congr _ (hA.add hB).isHermitian.traceLeft (congrArg traceLeft e),
    Fin.sum_univ_two] at h
  exact h

/-- **Concavity of the entropy, unnormalized**: `(S(A) - η(tr A)) + (S(B) - η(tr B)) ≤
S(A + B) - η(tr(A + B))` for positive semidefinite `A, B`. -/
theorem vonNeumann_sub_negMulLog_add_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    (vonNeumann hA.isHermitian - Real.negMulLog (RCLike.re A.trace)) +
        (vonNeumann hB.isHermitian - Real.negMulLog (RCLike.re B.trace)) ≤
      vonNeumann (hA.add hB).isHermitian - Real.negMulLog (RCLike.re (A + B).trace) := by
  let e : n × Unit ≃ n := Equiv.prodPUnit n
  have key {X Y : Matrix _ _ 𝕜} (hX : X.IsHermitian) (hY : Y.IsHermitian)
      (h : Y = X.submatrix e e) :
      vonNeumann hY - vonNeumann hY.traceLeft =
        vonNeumann hX - Real.negMulLog (RCLike.re X.trace) := by
    subst h
    rw [vonNeumann_submatrix_equiv hX e, vonNeumann_of_unique hY.traceLeft, traceLeft_trace,
      trace_submatrix]
  have h := vonNeumann_sub_traceLeft_add_le (hA.submatrix e) (hB.submatrix e)
  rwa [key hA.isHermitian _ rfl, key hB.isHermitian _ rfl,
    key (hA.add hB).isHermitian ((hA.submatrix e).add (hB.submatrix e)).isHermitian
    (by ext; rfl)] at h

/-- **Upper bound for the conditional entropy of a sum**: `S(D|E)_{A+B} ≤ S(D|E)_A + S(D|E)_B
+ η(tr A) + η(tr B) - η(tr(A + B))` for positive semidefinite `A, B` on `D ⊗ E`, with
`η(x) = -x log x`. -/
theorem vonNeumann_sub_traceLeft_add_le_add {A B : Matrix (m × n) (m × n) 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    vonNeumann (hA.add hB).isHermitian - vonNeumann (hA.add hB).isHermitian.traceLeft ≤
      (vonNeumann hA.isHermitian - vonNeumann hA.isHermitian.traceLeft) +
        (vonNeumann hB.isHermitian - vonNeumann hB.isHermitian.traceLeft) +
        (Real.negMulLog (RCLike.re A.trace) + Real.negMulLog (RCLike.re B.trace) -
          Real.negMulLog (RCLike.re (A + B).trace)) := by
  have hmix := vonNeumann_add_le hA hB
  have hcon := vonNeumann_sub_negMulLog_add_le hA.traceLeft hB.traceLeft
  have htr : RCLike.re (A.traceLeft + B.traceLeft).trace = RCLike.re (A + B).trace := by
    rw [← traceLeft_add, traceLeft_trace]
  rw [vonNeumann_congr (hA.traceLeft.add hB.traceLeft).isHermitian
    (hA.add hB).isHermitian.traceLeft (by rw [traceLeft_add]), htr,
    traceLeft_trace, traceLeft_trace] at hcon
  linarith

/-- **Dimension bound for the conditional entropy**: `|S(D|E)_A| ≤ tr A · log dim D` for
positive semidefinite `A` on `D ⊗ E`; the dimension of `E` does not enter. -/
theorem abs_vonNeumann_sub_traceLeft_le {A : Matrix (m × n) (m × n) 𝕜} (hA : A.PosSemidef) :
    |vonNeumann hA.isHermitian - vonNeumann hA.isHermitian.traceLeft| ≤
      RCLike.re A.trace * Real.log (Fintype.card m) := by
  have hsub := vonNeumann_add_negMulLog_le hA
  have htri := abs_vonNeumann_traceRight_sub_traceLeft_le hA
  have hD := vonNeumann_le_re_trace_mul_log_card_add hA.traceRight
  rw [traceRight_trace] at hD
  rw [abs_le] at htri ⊢
  constructor <;> linarith [htri.1, htri.2]

end Conditional

end Arealaw
