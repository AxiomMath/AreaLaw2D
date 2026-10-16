/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/LatticeAncillaTransport.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations:
* Encodings as in `OpenAI.Amplification.LatticeRestoring`: TNLean's `Site Λ` is
  `↥(Λ : Set (ℤ × ℤ))`, `Configuration Λ q` is `Reg (Qudits q) Λ`, `StateSpace Λ q` is
  `EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and `reducedState Λ q Ω A`,
  `reducedState_isHermitian`, `reducedState_posSemidef`, `regionalEntropy Λ q Ω A`,
  `trace_reducedState` are `FiniteProduct.reducedPure β Ω A`,
  `(FiniteProduct.reducedPure_posSemidef β Ω A).isHermitian`,
  `FiniteProduct.reducedPure_posSemidef`, `FiniteProduct.entropy β Ω A`,
  `FiniteProduct.trace_reducedPure` with `β = fun _ ↦ Fin q`.
* Support.  TNLean's `P ∈ supportedOperators q (S : Set (Site Λ))` for a cut
  `S : Finset (Site Λ)` is `OpenAI.IsSupportedOn (map_embeddingSubtype_subset S) P`, support
  on the region `S.map (Function.Embedding.subtype _) ⊆ Λ`.  TNLean's
  `localLift_eq_kronecker_one_submatrix` and `localLift_mem_supportedOperators` are replaced by
  `OpenAI.isSupportedOn_kronecker_one_submatrix_splitEquiv`, which states the support of
  `K ⊗ 1` in the split coordinates directly; `ancillaPhysical_mem_supportedOperators` is
  renamed `OpenAI.isSupportedOn_ancillaPhysical`.
* TNLean's `l2_opNorm_le_one_of_conjTranspose_mul_self` is `Arealaw`'s, and is not restated;
  `norm_toLp_mulVec_of_conjTranspose_mul_self`, `l2_opNorm_conj_le` and `mulVec_mulVec_eq_conj`
  are stated over `RCLike 𝕜`.  QICLean's `Matrix.l2_opNorm_kronecker_one_le` is
  `Arealaw.l2_opNorm_kronecker_one_le`.  The import of `QICLean.Analysis.RootChannel` is dropped.
-/
import OpenAI.Amplification.AncillaTransport
import OpenAI.Amplification.LatticeRestoring
import OpenAI.MatrixKroneckerContraction

/-!
# The restoring operator with the two ancillary copies as spectators

The restoring estimates of the amplification proof are proved in the coordinates
`((s', e'), (X, Y)), Z'` with the target `X` written in the eigenbasis of `ρ_X`. The
constraint products act on the physical configurations of the finite domain, with the two
ancillary copies `s', e'` of the target as spectators. This module transports the
restoring operator `R₀`, the column operator `B₀` and the vectors `φ`, `η`, `Ω ⊗ |00⟩` to
the coordinates `physical × (s', e')`, with the physical system in its original
coordinates, and restates the three estimates there:

* `‖R₀‖, ‖B₀‖ ≤ exp ((𝓘 + 3w)/2)` with `𝓘 = I_Ω(X : Z')`;
* the column identity `R₀ φ = B₀ (Ω ⊗ ξ)` for the transported blank pair `ξ`, which puts
  `R₀ φ` in the form required by the omission estimate of the local-products lemma;
* the physical ground component of `R₀ φ` has norm at most one;
* `‖((L' ⊗ 1) R₀)^† η - φ‖ ≤ 3 √δ + ‖L'^† Ω - Ω‖` for every physical operator `L'`.

In these coordinates `B₀` is a sum of operators `P ⊗ A` with `P` acting on `S₀ = X ∪ Y`,
and `R₀` a sum of operators `P ⊗ (b ⊗ 1)` with `P` acting on `S₀` and `b` acting on `s'`.
The vector `η` is `Ω` tensored with an ancillary vector, and `φ` is `Ω` with its target
read on `e'` and a blank on the physical target.

## Main definitions

* `OpenAI.restoringEigenbasis`: the eigenvector unitary of `ρ_X`.
* `OpenAI.restoringTransport`: the transport to `physical × (s', e')`.

## Main statements

* `OpenAI.restoringTransport_estimates`: the estimates above.
* `OpenAI.restoringTransport_copy`, `OpenAI.restoringTransport_restored`: the two vectors.
* `OpenAI.restoringTransport_restoringGlobal_eq_sum`,
  `OpenAI.restoringTransport_restoringColumnGlobal_eq_sum`: the supports of `R₀` and `B₀`.

## Implementation notes

A cut `S` of the sites acts through the region `S.map (Function.Embedding.subtype _)` of
`ℤ × ℤ`, which lies in `Λ` by `OpenAI.map_embeddingSubtype_subset`; the supports of the
physical parts of `R₀` and `B₀` are stated on that region, the form taken by the omission and
truncation estimates of the local-products lemma.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 324–447
  and 470–473: `eq:amplification-swapped-state`, `eq:amplification-restored-state`,
  `eq:amplification-restoring-operator`, `eq:amplification-column-operator`,
  `eq:amplification-column-identity`, `eq:amplification-operator-norm`,
  `eq:amplification-adjoint-error` and `eq:amplification-ground-component`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator

namespace OpenAI

open Arealaw

section Isometry

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq m] in
/-- A matrix with `Wᴴ W = 1` preserves Euclidean norms. -/
theorem norm_toLp_mulVec_of_conjTranspose_mul_self {W : Matrix m n 𝕜} (hW : Wᴴ * W = 1)
    (v : n → 𝕜) : ‖WithLp.toLp 2 (W *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  classical
  have hle := l2_opNorm_le_one_of_conjTranspose_mul_self hW
  have hW' : ‖Wᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact hle
  have hA : ‖WithLp.toLp 2 (W *ᵥ v)‖ ≤ ‖W‖ * ‖WithLp.toLp 2 v‖ :=
    W.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have hB : ‖WithLp.toLp 2 (Wᴴ *ᵥ (W *ᵥ v))‖ ≤ ‖Wᴴ‖ * ‖WithLp.toLp 2 (W *ᵥ v)‖ :=
    Wᴴ.l2_opNorm_mulVec (WithLp.toLp 2 (W *ᵥ v))
  have hv : Wᴴ *ᵥ (W *ᵥ v) = v := by rw [mulVec_mulVec, hW, one_mulVec]
  rw [hv] at hB
  apply le_antisymm
  · nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace 𝕜 n), norm_nonneg W]
  · nlinarith [norm_nonneg (WithLp.toLp 2 (W *ᵥ v) : EuclideanSpace 𝕜 m), norm_nonneg Wᴴ]

/-- Conjugation by a matrix with `Wᴴ W = 1` does not increase the operator norm. -/
theorem l2_opNorm_conj_le {W : Matrix m n 𝕜} (hW : Wᴴ * W = 1) (A : Matrix n n 𝕜) :
    ‖W * A * Wᴴ‖ ≤ ‖A‖ := by
  have hle := l2_opNorm_le_one_of_conjTranspose_mul_self hW
  calc ‖W * A * Wᴴ‖ ≤ ‖W * A‖ * ‖Wᴴ‖ := l2_opNorm_mul _ _
    _ ≤ (‖W‖ * ‖A‖) * ‖Wᴴ‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ (1 * ‖A‖) * 1 := by
        rw [l2_opNorm_conjTranspose]
        gcongr
    _ = ‖A‖ := by ring

omit [DecidableEq m] in
/-- Applying an operator and then a matrix with `Wᴴ W = 1` equals applying the conjugated
operator to the transported vector. -/
theorem mulVec_mulVec_eq_conj {W : Matrix m n 𝕜} (hW : Wᴴ * W = 1) (A : Matrix n n 𝕜)
    (v : n → 𝕜) : W *ᵥ (A *ᵥ v) = (W * A * Wᴴ) *ᵥ (W *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (W * A), hW, Matrix.mul_one]

end Isometry

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

set_option hygiene false in
/-- The local level types `Fin q` of the sites of `Λ`. -/
local notation "βΛ" => fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q

/-- **Support in the split coordinates.** An operator `K ⊗ 1` in the coordinates of a cut `S`
of the sites and its complement acts on the region of `S`. -/
theorem isSupportedOn_kronecker_one_submatrix_splitEquiv {𝕜 : Type*} [RCLike 𝕜]
    (S : Finset ↥(Λ : Set (ℤ × ℤ)))
    (K : Matrix (RegionalConfiguration q S) (RegionalConfiguration q S) 𝕜) :
    IsSupportedOn (map_embeddingSubtype_subset (T := Λ) S)
      (((K ⊗ₖ (1 : Matrix (RegionalConfiguration q Sᶜ) (RegionalConfiguration q Sᶜ) 𝕜)).submatrix
        (FiniteProduct.splitEquiv βΛ S) (FiniteProduct.splitEquiv βΛ S) :
          Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜)) := by
  set h := map_embeddingSubtype_subset (T := Λ) S
  let f : Reg (Qudits q) (S.map (Function.Embedding.subtype _)) → RegionalConfiguration q S :=
    fun w v => w ⟨v.1.1, Finset.mem_map_of_mem _ v.2⟩
  refine ⟨K.submatrix f f, ?_⟩
  ext x y
  rw [extendId_apply]
  have hiff : (FiniteProduct.splitEquiv βΛ S x).2 = (FiniteProduct.splitEquiv βΛ S y).2 ↔
      restr (S := Λ \ S.map (Function.Embedding.subtype _)) Finset.sdiff_subset x =
        restr Finset.sdiff_subset y := by
    constructor
    · intro hxy
      funext i
      have hi := Finset.mem_sdiff.1 i.2
      exact congrFun hxy ⟨⟨i.1, hi.1⟩, Finset.mem_compl.2 fun hS =>
        hi.2 (Finset.mem_map_of_mem (Function.Embedding.subtype _) hS)⟩
    · intro hxy
      funext v
      refine congrFun hxy ⟨v.1.1, Finset.mem_sdiff.2 ⟨v.1.2, fun hm => ?_⟩⟩
      obtain ⟨w, hw, hwv⟩ := Finset.mem_map.1 hm
      have : w = v.1 := Subtype.ext hwv
      exact Finset.mem_compl.1 v.2 (this ▸ hw)
  simp only [submatrix_apply, kroneckerMap_apply, one_apply]
  by_cases hxy : (FiniteProduct.splitEquiv βΛ S x).2 = (FiniteProduct.splitEquiv βΛ S y).2
  · rw [if_pos hxy, if_pos (hiff.1 hxy), mul_one]
    rfl
  · rw [if_neg hxy, if_neg (hiff.not.1 hxy), mul_zero]

/-- The physical operator obtained from an operator on `X × Y` acts on `X ∪ Y`.
Source: `09-amplification.tex`, lines 348–364. -/
theorem isSupportedOn_ancillaPhysical (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y)
    (U : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)
    (M : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ) :
    IsSupportedOn (map_embeddingSubtype_subset (T := Λ) (X ∪ Y))
      (ancillaPhysical U (restoringSplit q X Y hXY) M) := by
  set uE := FiniteProduct.unionEquiv βΛ X Y hXY
  have h : ancillaPhysical U (restoringSplit q X Y hXY) M =
      ((((U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) * M *
        (U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y)
          (RegionalConfiguration q Y) ℂ))ᴴ)).submatrix uE uE ⊗ₖ
        (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
          (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)).submatrix
          (FiniteProduct.splitEquiv βΛ (X ∪ Y)) (FiniteProduct.splitEquiv βΛ (X ∪ Y)) := by
    ext c c'
    simp only [ancillaPhysical, submatrix_apply, kroneckerMap_apply]
    rfl
  rw [h]
  exact isSupportedOn_kronecker_one_submatrix_splitEquiv _ _

/-- The eigenvector unitary of the reduced state `ρ_X`, whose columns are the full
eigenbasis `{|x⟩}`. Source: `09-amplification.tex`, lines 324–325. -/
noncomputable abbrev restoringEigenbasis (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X : Finset ↥(Λ : Set (ℤ × ℤ))) :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ :=
  ((FiniteProduct.reducedPure_posSemidef βΛ Ω X).isHermitian.eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)

/-- The eigenvector matrix of `ρ_X` is unitary. -/
theorem restoringEigenbasis_unitary (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X : Finset ↥(Λ : Set (ℤ × ℤ))) :
    restoringEigenbasis Ω X * (restoringEigenbasis Ω X)ᴴ = 1 ∧
      (restoringEigenbasis Ω X)ᴴ * restoringEigenbasis Ω X = 1 := by
  simp only [restoringEigenbasis, ← star_eq_conjTranspose]
  exact ⟨Unitary.coe_mul_star_self _, Unitary.coe_star_mul_self _⟩

/-- The transport from the restoring coordinates `((s', e'), (X, Y)), Z'` to the
coordinates `physical × (s', e')`. Source: `09-amplification.tex`, lines 324–347. -/
noncomputable def restoringTransport (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y) :
    Matrix (Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X))
      (((RegionalConfiguration q X × RegionalConfiguration q X) ×
        (RegionalConfiguration q X × RegionalConfiguration q Y)) ×
          RegionalConfiguration q (X ∪ Y)ᶜ) ℂ :=
  ancillaTransport (restoringEigenbasis Ω X) (restoringSplit q X Y hXY)

/-- The transport is unitary. -/
theorem restoringTransport_unitary (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y) :
    restoringTransport Ω X Y hXY * (restoringTransport Ω X Y hXY)ᴴ = 1 ∧
      (restoringTransport Ω X Y hXY)ᴴ * restoringTransport Ω X Y hXY = 1 :=
  ⟨ancillaTransport_mul_conjTranspose (restoringEigenbasis_unitary Ω X).1
      (restoringEigenbasis_unitary Ω X).2 _,
    conjTranspose_mul_ancillaTransport (restoringEigenbasis_unitary Ω X).1
      (restoringEigenbasis_unitary Ω X).2 _⟩

/-- **The copied vector** `φ` in the coordinates `physical × (s', e')`: its value at a
configuration `c` and ancillary pair `(s, e)` is `|0⟩(s) (U |0⟩)(c_X) Ω(c')`, where `c'`
agrees with `c` off `X` and reads `e` on `X`.
Source: `eq:amplification-swapped-state`, `09-amplification.tex`, lines 334–347. -/
theorem restoringTransport_copy (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y)
    (sBlank xBlank : RegionalConfiguration q X → ℂ) :
    restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp =
      fun c => sBlank c.2.1 * (restoringEigenbasis Ω X *ᵥ xBlank)
        (restoringSplit q X Y hXY c.1).1.1 * Ω ((restoringSplit q X Y hXY).symm
          ((c.2.2, (restoringSplit q X Y hXY c.1).1.2), (restoringSplit q X Y hXY c.1).2)) :=
  ancillaTransport_mulVec_copy (restoringEigenbasis_unitary Ω X).1 _ sBlank xBlank
    (fun c => Ω c)

/-- **The restored vector** `η = Ω ⊗ ∑_x √p_x |x⟩_{s'}|x⟩_{e'}` in the coordinates
`physical × (s', e')`, with `e'` read in the original basis.
Source: `eq:amplification-restored-state`, `09-amplification.tex`, lines 338–341. -/
theorem restoringTransport_restored (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y)
    (p : RegionalConfiguration q X → ℝ) :
    restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp =
      fun c => Ω c.1 * (((1 : Matrix (RegionalConfiguration q X)
        (RegionalConfiguration q X) ℂ) ⊗ₖ restoringEigenbasis Ω X) *ᵥ
          fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0) c.2 :=
  ancillaTransport_mulVec_restored (restoringEigenbasis_unitary Ω X).1 _ p (fun c => Ω c)

/-- **The support of the transported restoring operator**: `R₀` is a sum of operators
`P ⊗ (b ⊗ 1_{e'})` with `P` acting on `X ∪ Y` and `b` acting on `s'`.
Source: `eq:amplification-restoring-operator`, `09-amplification.tex`, lines 350–356. -/
theorem restoringTransport_restoringGlobal_eq_sum (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y)
    (E : Finset (RegionalConfiguration q X))
    (p : RegionalConfiguration q X → ℝ) (sBlank xBlank : RegionalConfiguration q X → ℂ)
    (Q : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ)
    (T : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ) :
    ∃ P : RegionalConfiguration q X → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ,
      (∀ x, IsSupportedOn (map_embeddingSubtype_subset (T := Λ) (X ∪ Y)) (P x)) ∧
      restoringTransport Ω X Y hXY * Entropy.restoringGlobal (Z := RegionalConfiguration q
          (X ∪ Y)ᶜ) E p sBlank xBlank Q T * (restoringTransport Ω X Y hXY)ᴴ =
        ∑ x ∈ E, P x ⊗ₖ (Entropy.basisColumn x sBlank ⊗ₖ
          (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)) := by
  refine ⟨fun x => Entropy.restoringWeight (p x) • ancillaPhysical (restoringEigenbasis Ω X)
    (restoringSplit q X Y hXY) (Q * (Entropy.basisColumn x xBlank ⊗ₖ T)),
    fun x => (isSupportedOn_ancillaPhysical X Y hXY _ _).smul _, ?_⟩
  rw [restoringTransport, ancillaTransport_conj_restoringGlobal
    (restoringEigenbasis_unitary Ω X).1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_kronecker, kronecker_smul]

/-- **The support of the transported column operator**: `B₀` is a sum of operators
`P ⊗ A` with `P` acting on `X ∪ Y` and `A` acting on the ancillas.
Source: `eq:amplification-column-operator`, `09-amplification.tex`, lines 359–364. -/
theorem restoringTransport_restoringColumnGlobal_eq_sum
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y)
    (E : Finset (RegionalConfiguration q X))
    (p : RegionalConfiguration q X → ℝ) (sBlank eBlank : RegionalConfiguration q X → ℂ)
    (Q : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ)
    (T : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ) :
    ∃ (P : RegionalConfiguration q X × RegionalConfiguration q X →
        Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ)
      (A : RegionalConfiguration q X × RegionalConfiguration q X →
        Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
          (RegionalConfiguration q X × RegionalConfiguration q X) ℂ),
      (∀ i, IsSupportedOn (map_embeddingSubtype_subset (T := Λ) (X ∪ Y)) (P i)) ∧
      restoringTransport Ω X Y hXY * Entropy.restoringColumnGlobal (Z := RegionalConfiguration q
          (X ∪ Y)ᶜ) E p sBlank eBlank Q T * (restoringTransport Ω X Y hXY)ᴴ =
        ∑ i ∈ E ×ˢ Finset.univ, P i ⊗ₖ A i := by
  refine ⟨fun i => ancillaPhysical (restoringEigenbasis Ω X) (restoringSplit q X Y hXY)
      (Q * (single i.1 i.2 1 ⊗ₖ T)),
    fun i => ((1 : Matrix _ _ ℂ) ⊗ₖ restoringEigenbasis Ω X) *
      (Entropy.restoringWeight (p i.1) • (Entropy.basisColumn i.1 sBlank ⊗ₖ
        Entropy.basisColumn i.2 eBlank)) * ((1 : Matrix _ _ ℂ) ⊗ₖ restoringEigenbasis Ω X)ᴴ,
    fun i => isSupportedOn_ancillaPhysical X Y hXY _ _, ?_⟩
  rw [restoringTransport, ancillaTransport_conj_restoringColumnGlobal, Finset.sum_product]

/-- **The restoring estimates with the ancillas as spectators.** Let `Ω` be a unit vector,
`X, Y` disjoint regions with `S₀ = X ∪ Y` and `Z' = Λ ∖ S₀`, and `w, δ` real numbers
bounding the failure probabilities of the typical projections of `X`, `Y` and `S₀` by `δ`.
Transport the restoring operator `R₀`, the column operator `B₀`, the copied vector `φ`
and the restored vector `η` to the coordinates `physical × (s', e')`. Then `φ, η` are unit
vectors, `‖R₀‖, ‖B₀‖ ≤ M₀ = exp ((𝓘 + 3w)/2)` with `𝓘 = I_Ω(X : Z')`, `R₀ φ = B₀ (Ω ⊗ ξ)`
for the transported blank pair `ξ`, the physical ground component of `R₀ φ` has norm at
most one, and `‖((L' ⊗ 1) R₀)^† η - φ‖ ≤ 3 √δ + ‖L'^† Ω - Ω‖` for every physical `L'`.
Source: `09-amplification.tex`, lines 324–447 and 470–473. -/
theorem restoringTransport_estimates (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : ‖Ω‖ = 1)
    (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδX : 1 - (FiniteProduct.reducedPure βΛ Ω X * typicalProjection Λ q Ω X w).trace.re ≤ δ)
    (hδY : 1 - (FiniteProduct.reducedPure βΛ Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤ δ)
    (hδS : 1 - (FiniteProduct.reducedPure βΛ Ω (X ∪ Y) *
      typicalProjection Λ q Ω (X ∪ Y) w).trace.re ≤ δ)
    (sBlank xBlank eBlank : RegionalConfiguration q X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (he : ‖WithLp.toLp 2 eBlank‖ = 1) :
    let 𝒲 := restoringTransport Ω X Y hXY
    let p := (FiniteProduct.reducedPure_posSemidef βΛ Ω X).isHermitian.eigenvalues
    let E := Entropy.typicalSet p (FiniteProduct.entropy βΛ Ω X) w
    let T := typicalProjection Λ q Ω Y w
    let Q := restoringCutProjection Ω X Y hXY w
    let ψ := restoringVector Ω X Y hXY
    let I := FiniteProduct.mutualInformation βΛ Ω X (X ∪ Y)ᶜ
    let R := 𝒲 * Entropy.restoringGlobal (Z := RegionalConfiguration q (X ∪ Y)ᶜ) E p sBlank
      xBlank Q T * 𝒲ᴴ
    let B := 𝒲 * Entropy.restoringColumnGlobal (Z := RegionalConfiguration q (X ∪ Y)ᶜ) E p
      sBlank eBlank Q T * 𝒲ᴴ
    let φ := 𝒲 *ᵥ (Entropy.restoringCopy sBlank xBlank ψ).ofLp
    let η := 𝒲 *ᵥ (Entropy.restoringRestored p ψ).ofLp
    ‖WithLp.toLp 2 φ‖ = 1 ∧ ‖WithLp.toLp 2 η‖ = 1 ∧
      ‖R‖ ≤ Real.exp ((I + 3 * w) / 2) ∧ ‖B‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      R *ᵥ φ = B *ᵥ (fun c => Ω c.1 *
        (sBlank c.2.1 * (restoringEigenbasis Ω X *ᵥ eBlank) c.2.2)) ∧
      ‖WithLp.toLp 2 ((vecMulVec Ω.ofLp (star Ω.ofLp) ⊗ₖ
        (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
          (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ (R *ᵥ φ))‖ ≤ 1 ∧
      ∀ L : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ,
        ‖WithLp.toLp 2 ((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
            (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) * R)ᴴ *ᵥ η) -
          WithLp.toLp 2 φ‖ ≤ 3 * √δ + ‖WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp) - Ω‖ := by
  intro 𝒲 p E T Q ψ I R B φ η
  obtain ⟨hU, hU'⟩ := restoringEigenbasis_unitary Ω X
  obtain ⟨-, h𝒲⟩ := restoringTransport_unitary Ω X Y hXY
  set U := restoringEigenbasis Ω X with hUdef
  set rs := restoringSplit q X Y hXY with hrs
  obtain ⟨hψ, hRn, hBn, hground, hadj⟩ := restoringOperator_estimates Ω hΩ X Y hXY w δ hδX hδY
    hδS sBlank xBlank eBlank hs hx he
  -- The rotation `(Uᴴ ⊗ 1) ⊗ 1` relating `ψ` to `Ω`.
  set Uh := (Uᴴ ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) ⊗ₖ
    (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ) (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)
    with hUhdef
  have hUh : Uhᴴ * Uh = 1 := by
    simp only [hUhdef, conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_one,
      ← mul_kronecker_mul, hU, Matrix.one_mul, one_kronecker_one]
  have hUhH : Uhᴴ = (U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y)
      (RegionalConfiguration q Y) ℂ)) ⊗ₖ (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
        (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ) := by
    simp only [hUhdef, conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_one]
  have hψdef : ψ.ofLp = Uh *ᵥ fun i => Ω (rs.symm i) := rfl
  -- The physical operators in the eigenbasis coordinates.
  have hphys (L : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) :
      𝒲 * Entropy.restoringPhysicalLift (Uh * L.submatrix rs.symm rs.symm * Uhᴴ) * 𝒲ᴴ =
        L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
          (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) := by
    rw [hUhH]
    exact ancillaTransport_conj_physicalLift hU rs L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_toLp_mulVec_of_conjTranspose_mul_self h𝒲]
    exact (Entropy.restoringCopy_norm sBlank xBlank hs hx ψ).trans hψ
  · -- `η` is `Ω` tensored with a unit ancillary vector.
    have hη : η = fun c => Ω c.1 * (((1 : Matrix (RegionalConfiguration q X)
        (RegionalConfiguration q X) ℂ) ⊗ₖ U) *ᵥ
          fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0) c.2 :=
      restoringTransport_restored Ω X Y hXY p
    have hp0 : ∀ x, 0 ≤ p x := (FiniteProduct.reducedPure_posSemidef βΛ Ω X).eigenvalues_nonneg
    have hpsum : ∑ x, p x = 1 := by
      have h := (FiniteProduct.reducedPure_posSemidef βΛ Ω X).isHermitian.trace_eq_sum_eigenvalues
      rw [FiniteProduct.trace_reducedPure βΛ Ω hΩ X] at h
      have h' : ((∑ x, p x : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
      exact_mod_cast h'
    have hU1 : ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ U)ᴴ *
        ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ U) = 1 := by
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hU']
      simp
    have hχ : ‖WithLp.toLp 2 (fun a : RegionalConfiguration q X × RegionalConfiguration q X =>
        if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0)‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type]
      rw [← hpsum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [Complex.norm_real, Real.sq_sqrt (hp0 x), abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hη]
    have := EuclideanSpace.norm_vecKron Ω (WithLp.toLp 2 (((1 : Matrix (RegionalConfiguration q X)
      (RegionalConfiguration q X) ℂ) ⊗ₖ U) *ᵥ fun a : RegionalConfiguration q X ×
        RegionalConfiguration q X => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0))
    rw [norm_toLp_mulVec_of_conjTranspose_mul_self hU1, hχ, hΩ, mul_one] at this
    exact this
  · calc ‖R‖ ≤ ‖Entropy.restoringGlobal E p sBlank xBlank Q T‖ := l2_opNorm_conj_le h𝒲 _
      _ ≤ ‖Entropy.restoringOperatorWithAncilla E p sBlank xBlank Q T‖ :=
          l2_opNorm_kronecker_one_le _
      _ ≤ ‖Entropy.restoringOperator E p sBlank xBlank Q T ⊗ₖ
            (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)‖ :=
          norm_submatrix_equiv_le _ _
      _ ≤ ‖Entropy.restoringOperator E p sBlank xBlank Q T‖ := l2_opNorm_kronecker_one_le _
      _ ≤ _ := hRn
  · calc ‖B‖ ≤ ‖Entropy.restoringColumnGlobal E p sBlank eBlank Q T‖ := l2_opNorm_conj_le h𝒲 _
      _ ≤ ‖Entropy.columnOperator E p sBlank eBlank Q T‖ := l2_opNorm_kronecker_one_le _
      _ ≤ _ := hBn
  · have hinit : 𝒲 *ᵥ (Entropy.restoringInitial sBlank eBlank ψ).ofLp =
        fun c => Ω c.1 * (sBlank c.2.1 * (U *ᵥ eBlank) c.2.2) :=
      ancillaTransport_mulVec_initial hU rs sBlank eBlank (fun c => Ω c)
    rw [← hinit, ← mulVec_mulVec_eq_conj h𝒲, ← mulVec_mulVec_eq_conj h𝒲,
      Entropy.restoringGlobal_mulVec_copy E p sBlank xBlank eBlank hx he Q T ψ]
  · have hvec : vecMulVec ψ.ofLp (star ψ.ofLp) =
        Uh * (vecMulVec Ω.ofLp (star Ω.ofLp)).submatrix rs.symm rs.symm * Uhᴴ := by
      have hsub : (vecMulVec Ω.ofLp (star Ω.ofLp)).submatrix rs.symm rs.symm =
          vecMulVec (fun i => Ω (rs.symm i)) (star fun i => Ω (rs.symm i)) := by
        ext i j
        simp [vecMulVec_apply]
      rw [hsub, hψdef, mul_vecMulVec, vecMulVec_mul, star_mulVec]
    have hg := hground
    rw [Entropy.restoringGroundComponent, Entropy.restoringGroundOuterProduct, hvec] at hg
    rw [← norm_toLp_mulVec_of_conjTranspose_mul_self h𝒲] at hg
    rw [← hphys, ← mulVec_mulVec_eq_conj h𝒲, ← mulVec_mulVec_eq_conj h𝒲]
    exact hg
  · intro L
    have h := hadj (Uh * L.submatrix rs.symm rs.symm * Uhᴴ)
    set LG := Uh * L.submatrix rs.symm rs.symm * Uhᴴ with hLG
    set RG := Entropy.restoringGlobal (Z := RegionalConfiguration q (X ∪ Y)ᶜ) E p sBlank xBlank
      Q T
    have key : ∀ {κ : Type} (M : Matrix (((RegionalConfiguration q X ×
        RegionalConfiguration q X) × (RegionalConfiguration q X × RegionalConfiguration q Y)) ×
          RegionalConfiguration q (X ∪ Y)ᶜ) κ ℂ), 𝒲ᴴ * (𝒲 * M) = M := by
      intro κ M
      rw [← Matrix.mul_assoc, h𝒲, Matrix.one_mul]
    have hconj : (L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) * R)ᴴ =
        𝒲 * (Entropy.restoringPhysicalLift LG * RG)ᴴ * 𝒲ᴴ := by
      rw [← hphys L]
      simp only [R, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, key]
      simp only [hLG, Matrix.mul_assoc]
      rfl
    have hleft : ((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) * R)ᴴ *ᵥ η) =
        𝒲 *ᵥ (RGᴴ *ᵥ ((Entropy.restoringPhysicalLift LG)ᴴ *ᵥ
          (Entropy.restoringRestored p ψ).ofLp)) := by
      rw [hconj, ← mulVec_mulVec_eq_conj h𝒲, conjTranspose_mul, ← mulVec_mulVec]
    have hnorm_left : ‖WithLp.toLp 2 ((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
        RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) *
          R)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ =
        ‖WithLp.toLp 2 (RGᴴ *ᵥ ((Entropy.restoringPhysicalLift LG)ᴴ *ᵥ
          (Entropy.restoringRestored p ψ).ofLp)) - Entropy.restoringCopy sBlank xBlank ψ‖ := by
      rw [hleft, ← WithLp.toLp_sub, ← mulVec_sub, norm_toLp_mulVec_of_conjTranspose_mul_self h𝒲,
        WithLp.toLp_sub]
    have hnorm_right : ‖WithLp.toLp 2 (LGᴴ *ᵥ ψ.ofLp) - ψ‖ =
        ‖WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp) - Ω‖ := by
      have hLGH : LGᴴ = Uh * (Lᴴ).submatrix rs.symm rs.symm * Uhᴴ := by
        rw [hLG, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
          conjTranspose_submatrix, Matrix.mul_assoc]
      have hdiff : WithLp.toLp 2 (LGᴴ *ᵥ ψ.ofLp) - ψ = WithLp.toLp 2 (Uh *ᵥ
          ((Lᴴ).submatrix rs.symm rs.symm *ᵥ (fun i => Ω (rs.symm i)) -
            fun i => Ω (rs.symm i))) := by
        rw [hLGH, hψdef, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec (M := Uhᴴ), hUh,
          one_mulVec, mulVec_sub]
        rfl
      rw [hdiff, norm_toLp_mulVec_of_conjTranspose_mul_self hUh, submatrix_mulVec_equiv]
      have hcomp : ((Lᴴ *ᵥ ((fun i => Ω (rs.symm i)) ∘ rs.symm.symm)) ∘ rs.symm -
          fun i => Ω (rs.symm i)) = (Lᴴ *ᵥ Ω.ofLp - Ω.ofLp) ∘ rs.symm := by
        ext i
        simp only [Pi.sub_apply, Function.comp_apply, Equiv.symm_symm]
        congr 2
        ext c
        simp
      rw [hcomp, EuclideanSpace.norm_toLp_comp_equiv, WithLp.toLp_sub]
    rw [hnorm_left, ← hnorm_right]
    exact h

end OpenAI
