/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/AmplificationProofSteps.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations:
* Encodings as in `OpenAI.Amplification.LatticeAncillaSites`: TNLean's `Site Λ` is
  `↥(Λ : Set (ℤ × ℤ))`, `Configuration Λ q` is `Reg (Qudits q) Λ`, `StateSpace Λ q` is
  `EuclideanSpace ℂ (Reg (Qudits q) Λ)`; a physical `P ∈ supportedOperators q (S : Set (Site Λ))`
  is `OpenAI.IsSupportedOn (map_embeddingSubtype_subset S) P`, and an operator `U` on the
  enlarged sites in `supportedOperators q (S : Set (AncillaSites Λ X))` is
  `OpenAI.IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv)`.
* Renamed: `sum_kronecker_submatrix_ancillaSplit_mem_supportedOperators` and
  `block_mem_supportedOperators_of_eq_sum` are
  `OpenAI.isSupportedOn_sum_kronecker_submatrix_ancillaSplit` and
  `OpenAI.isSupportedOn_block_of_eq_sum`; the second is stated for any region `S ⊆ T` of any
  site set and over `RCLike 𝕜`.  Added: `OpenAI.isSupportedOn_sum`, the closure of supported
  operators under finite sums (TNLean's `Submodule.sum_mem`).
* Set disjointness of coerced regions is `Finset` disjointness, as in
  `OpenAI.mutualInformation_le_inv_pow_of_supported_unitary`.
-/
import OpenAI.Amplification.LatticeAncillaSites
import OpenAI.Amplification.SupportedPolarCorrection

/-!
# Steps of the proof of Proposition 10.2 on the enlarged sites

The proof of Proposition 10.2 (`prop:amplification`) works on the physical sites enlarged by
two copies `s', e'` of the target `X`. This module states its last two steps on those sites.

* The polar correction: from the estimates of a good clock realization, stated in the
  coordinates `physical × (s', e')`, some unitary acting on `N ⊔ s'` moves the copied vector
  `φ` to within `a + √(2a + 6ε + 9ε²)` of the restored vector `η`, when the restoring
  operator acts on `N ⊔ s'` and the truncated product acts on the physical region `N`.
* The entropy comparison: if such a unitary moves `φ` to within `C₁ n^(-K/2)` of `η`, then
  every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` in `Ω` with every
  physical set avoiding `N`, where `|X| log q ≤ C₂ n²`.

It also records the supports of the restoring and column operators on these sites.

## Main statements

* `OpenAI.exists_ancilla_unitary_of_good_realization`: the polar correction on the enlarged
  sites.
* `OpenAI.mutualInformation_le_of_ancilla_unitary`: the entropy comparison on the enlarged
  sites.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 330–356 (the
  enlarged sites and the restoring operator), 501–545 (the polar correction) and 547–561
  (the entropy comparison).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix Arealaw
open scoped Kronecker Matrix.Norms.L2Operator

namespace OpenAI

section Sum

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}

/-- Supported operators are closed under finite sums. -/
theorem isSupportedOn_sum (h : S ⊆ T) {κ : Type*} (s : Finset κ)
    {B : κ → Matrix (Reg loc T) (Reg loc T) 𝕜} (hB : ∀ i ∈ s, IsSupportedOn h (B i)) :
    IsSupportedOn h (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSupportedOn_zero h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hB a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hB i (Finset.mem_insert_of_mem hi))

/-- **The blocks of a column operator act on a physical region.** If `B = ∑_i P_i ⊗ A_i` with
every `P_i` acting on a region `S`, then for all ancillary labels `x, y` the block
`u, v ↦ B (u, x) (v, y)` acts on `S`.
Source: `eq:amplification-column-operator`, `09-amplification.tex`, lines 359–364. -/
theorem isSupportedOn_block_of_eq_sum (h : S ⊆ T) {α κ : Type*} (s : Finset κ)
    {P : κ → Matrix (Reg loc T) (Reg loc T) 𝕜} (hP : ∀ i, IsSupportedOn h (P i))
    (A : κ → Matrix α α 𝕜) (x y : α) :
    IsSupportedOn h (Matrix.of fun u v => (∑ i ∈ s, P i ⊗ₖ A i) (u, x) (v, y)) := by
  have hblock : (Matrix.of fun u v => (∑ i ∈ s, P i ⊗ₖ A i) (u, x) (v, y)) =
      ∑ i ∈ s, A i x y • P i := by
    ext u v
    simp only [of_apply, Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hblock]
  exact isSupportedOn_sum h s fun i _ => (hP i).smul _

end Sum

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- **The support of a sum of restoring blocks on the enlarged sites.** A sum of operators
`P_i ⊗ (b_i ⊗ 1_{e'})`, with every `P_i` acting on a physical region `S`, acts on `S ⊔ s'`.
Source: `eq:amplification-restoring-operator`, `09-amplification.tex`, lines 350–356 and
524–525. -/
theorem isSupportedOn_sum_kronecker_submatrix_ancillaSplit {𝕜 : Type*} [RCLike 𝕜]
    {X S : Finset ↥(Λ : Set (ℤ × ℤ))} {κ : Type*} (s : Finset κ)
    {P : κ → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜}
    (hP : ∀ i, IsSupportedOn (map_embeddingSubtype_subset (T := Λ) S) (P i))
    (b : κ → Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) 𝕜) :
    IsSupportedOn (Finset.subset_univ (S.disjSum (Finset.univ.disjSum ∅) :
        Finset (AncillaSites Λ X)))
      (((∑ i ∈ s, P i ⊗ₖ (b i ⊗ₖ
        (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) 𝕜))).submatrix
          (ancillaSplit q X) (ancillaSplit q X)).submatrix univEquiv univEquiv) := by
  have hsum : ((∑ i ∈ s, P i ⊗ₖ (b i ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) 𝕜))).submatrix
        (ancillaSplit q X) (ancillaSplit q X)).submatrix univEquiv univEquiv =
      ∑ i ∈ s, ((P i ⊗ₖ (b i ⊗ₖ
        (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) 𝕜))).submatrix
          (ancillaSplit q X) (ancillaSplit q X)).submatrix univEquiv univEquiv := by
    ext c c'
    simp only [submatrix_apply, Matrix.sum_apply]
  rw [hsum]
  exact isSupportedOn_sum _ s fun i _ =>
    isSupportedOn_kronecker_submatrix_ancillaSplit (hP i) (b i)

/-- **The polar correction on the enlarged sites.** Work in the coordinates
`physical × (s', e')` of the enlarged sites. Let the restoring operator `R₀` act on `N ⊔ s'`
and the truncated product `L'` act on the physical region `N`, and let `D, D_ret` be
physical operators. For unit vectors `φ, η`, suppose that the ground component `g` of
`ζ = R₀ φ` is fixed by `D` with `‖g‖ ≤ 1`, that `‖ζ‖ ≤ M₀`, that the excited component
`‖D (ζ - g)‖`, the omitted events `‖(D - D_ret) ζ‖` and `M₀ ‖D_ret - L'‖` are at most `ε`,
and that the adjoint error of `L' R₀` is at most `a`. Then some unitary acting on `N ⊔ s'`
moves `φ` to within `a + √(2a + 6ε + 9ε²)` of `η`.
Source: `09-amplification.tex`, lines 501–545. -/
theorem exists_ancilla_unitary_of_good_realization {X N : Finset ↥(Λ : Set (ℤ × ℤ))}
    {R₀ : Matrix (Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X))
      (Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X)) ℂ}
    (hR₀ : IsSupportedOn (Finset.subset_univ (N.disjSum (Finset.univ.disjSum ∅) :
        Finset (AncillaSites Λ X)))
      ((R₀.submatrix (ancillaSplit q X) (ancillaSplit q X)).submatrix univEquiv univEquiv))
    {L' D Dret : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ}
    (hL : IsSupportedOn (map_embeddingSubtype_subset (T := Λ) N) L')
    {φ η g : Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ}
    (hφ : ‖WithLp.toLp 2 φ‖ = 1) (hη : ‖WithLp.toLp 2 η‖ = 1) {M₀ ε a : ℝ}
    (hζ : ‖WithLp.toLp 2 (R₀ *ᵥ φ)‖ ≤ M₀)
    (hg : (D ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
      (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ g = g)
    (hgn : ‖WithLp.toLp 2 g‖ ≤ 1)
    (hexc : ‖WithLp.toLp 2 ((D ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ
        (R₀ *ᵥ φ - g))‖ ≤ ε)
    (hret : ‖WithLp.toLp 2 (((D - Dret) ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ
        (R₀ *ᵥ φ))‖ ≤ ε)
    (htrunc : M₀ * ‖Dret - L'‖ ≤ ε)
    (hadj : ‖WithLp.toLp 2 (((L' ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *
        R₀)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ ≤ a) :
    ∃ U : Matrix (AncillaSites Λ X → Fin q) (AncillaSites Λ X → Fin q) ℂ,
      IsSupportedOn (Finset.subset_univ (N.disjSum (Finset.univ.disjSum ∅) :
        Finset (AncillaSites Λ X))) (U.submatrix univEquiv univEquiv) ∧ Uᴴ * U = 1 ∧
      ‖WithLp.toLp 2 (U *ᵥ (φ ∘ ancillaSplit q X)) - WithLp.toLp 2 (η ∘ ancillaSplit q X)‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  set sp := ancillaSplit q X with hspdef
  set I₂ := (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
    (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) with hI₂def
  have hT (A : Matrix (Reg (Qudits q) Λ × (RegionalConfiguration q X ×
      RegionalConfiguration q X)) (Reg (Qudits q) Λ × (RegionalConfiguration q X ×
        RegionalConfiguration q X)) ℂ)
      (v : Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ) :
      A.submatrix sp sp *ᵥ (v ∘ sp) = (A *ᵥ v) ∘ sp := by
    rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hTn (v : Reg (Qudits q) Λ × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ) : ‖WithLp.toLp 2 (v ∘ sp)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv sp v
  have hsubk (A B : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) :
      (A - B) ⊗ₖ I₂ = A ⊗ₖ I₂ - B ⊗ₖ I₂ := by
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  refine exists_supported_unitary_of_good_realization _ hR₀
    (isSupportedOn_kronecker_one_submatrix_ancillaSplit hL)
    (D := (D ⊗ₖ I₂).submatrix sp sp) (Dret := (Dret ⊗ₖ I₂).submatrix sp sp) (g := g ∘ sp)
    (M₀ := M₀) (ε := ε) (a := a)
    (by rw [hTn]; exact hφ) (by rw [hTn]; exact hη) (by rw [hT, hTn]; exact hζ)
    (by rw [hT, hg]) (by rw [hTn]; exact hgn) ?_ ?_ ?_ ?_
  · have hsub : R₀.submatrix sp sp *ᵥ (φ ∘ sp) - g ∘ sp = (R₀ *ᵥ φ - g) ∘ sp := by
      rw [hT]
      rfl
    rw [hsub, hT, hTn]
    exact hexc
  · have hsub : (D ⊗ₖ I₂).submatrix sp sp - (Dret ⊗ₖ I₂).submatrix sp sp =
        ((D - Dret) ⊗ₖ I₂).submatrix sp sp := by
      rw [hsubk]
      rfl
    rw [hT, hsub, hT, hTn]
    exact hret
  · have hsub : (Dret ⊗ₖ I₂).submatrix sp sp - (L' ⊗ₖ I₂).submatrix sp sp =
        ((Dret - L') ⊗ₖ I₂).submatrix sp sp := by
      rw [hsubk]
      rfl
    rw [hsub]
    exact (mul_le_mul_of_nonneg_left ((norm_submatrix_equiv_le _ _).trans
      (l2_opNorm_kronecker_one_le _)) ((norm_nonneg _).trans hζ)).trans htrunc
  · have hprod : (L' ⊗ₖ I₂).submatrix sp sp * R₀.submatrix sp sp =
        ((L' ⊗ₖ I₂) * R₀).submatrix sp sp := by
      rw [submatrix_mul_equiv]
    rw [hprod, conjTranspose_submatrix, hT, ← WithLp.toLp_sub]
    have hcomp : (((L' ⊗ₖ I₂) * R₀)ᴴ *ᵥ η) ∘ sp - φ ∘ sp =
        (((L' ⊗ₖ I₂) * R₀)ᴴ *ᵥ η - φ) ∘ sp := rfl
    rw [hcomp, hTn, WithLp.toLp_sub]
    exact hadj

/-- The copy `e'` of a part of the target is disjoint from every physical region. -/
theorem disjoint_ancillaCopyRegion_ancillaPhysicalRegion {X : Finset ↥(Λ : Set (ℤ × ℤ))}
    (X' : Finset ↥X) (J : Finset ↥(Λ : Set (ℤ × ℤ))) :
    Disjoint (ancillaCopyRegion X') (ancillaPhysicalRegion X J) := by
  rw [Finset.disjoint_left]
  rintro (v | x | x) h1 h2
  · simp only [ancillaCopyRegion, Finset.inl_mem_disjSum, Finset.notMem_empty] at h1
  · simp only [ancillaPhysicalRegion, Finset.inr_mem_disjSum, Finset.notMem_empty] at h2
  · simp only [ancillaPhysicalRegion, Finset.inr_mem_disjSum, Finset.notMem_empty] at h2

/-- The region `N ⊔ s'` of the enlarged sites is disjoint from the copy `e'` of the target
together with any physical region avoiding `N`. -/
theorem disjoint_disjSum_ancillaCopyRegion_union {X N J : Finset ↥(Λ : Set (ℤ × ℤ))}
    (hJ : Disjoint J N) (X' : Finset ↥X) :
    Disjoint (N.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X))
      (ancillaCopyRegion X' ∪ ancillaPhysicalRegion X J) := by
  rw [Finset.disjoint_left]
  rintro (v | x | x) h1 h2
  · simp only [Finset.inl_mem_disjSum] at h1
    simp only [ancillaCopyRegion, ancillaPhysicalRegion, Finset.mem_union,
      Finset.inl_mem_disjSum, Finset.notMem_empty, false_or] at h2
    exact Finset.disjoint_left.mp hJ h2 h1
  · simp only [ancillaCopyRegion, ancillaPhysicalRegion, Finset.mem_union,
      Finset.inr_mem_disjSum, Finset.inl_mem_disjSum, Finset.notMem_empty, or_self] at h2
  · simp only [Finset.inr_mem_disjSum, Finset.notMem_empty] at h1

/-- **The entropy comparison on the enlarged sites.** Let `X, Y` be disjoint physical regions,
let `φ` be the copied vector built from unit blank vectors on `s'` and on the target, and
let `η` be a restored vector, both of unit norm. If a unitary acting on `N ⊔ s'`, with `X ⊆ N`,
moves `φ` to within `C₁ n^(-K/2)` of `η` with `K ≥ 4(M + 2)`, and `|X| log q ≤ C₂ n²`,
then every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` in `Ω` with
every physical set avoiding `N`.
Source: `09-amplification.tex`, lines 547–561. -/
theorem mutualInformation_le_of_ancilla_unitary {Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)}
    (hΩ : ‖Ω‖ = 1) {X Y N J : Finset ↥(Λ : Set (ℤ × ℤ))} (hXY : Disjoint X Y) (hXN : X ⊆ N)
    (hJ : Disjoint J N)
    {sBlank xBlank : RegionalConfiguration q X → ℂ} (hs : ‖WithLp.toLp 2 sBlank‖ = 1)
    (hx : ‖WithLp.toLp 2 xBlank‖ = 1) {p : RegionalConfiguration q X → ℝ}
    (hφ : ‖WithLp.toLp 2 (restoringTransport Ω X Y hXY *ᵥ
      (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp)‖ = 1)
    (hη : ‖WithLp.toLp 2 (restoringTransport Ω X Y hXY *ᵥ
      (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp)‖ = 1)
    {U : Matrix (AncillaSites Λ X → Fin q) (AncillaSites Λ X → Fin q) ℂ}
    (hU : IsSupportedOn (Finset.subset_univ (N.disjSum (Finset.univ.disjSum ∅) :
      Finset (AncillaSites Λ X))) (U.submatrix univEquiv univEquiv)) (hUu : Uᴴ * U = 1)
    {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n) (hK : 4 * (M + 2) ≤ K)
    (hδ : ‖WithLp.toLp 2 (U *ᵥ ((restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp) ∘
          ancillaSplit q X)) -
      WithLp.toLp 2 ((restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp) ∘ ancillaSplit q X)‖ ≤
      C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : (X.card : ℝ) * Real.log q ≤ C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, FiniteProduct.mutualInformation (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω X' J ≤
      8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  intro X' hX'
  set sp := ancillaSplit q X with hspdef
  set φ := restoringTransport Ω X Y hXY *ᵥ
    (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp with hφdef
  set η := restoringTransport Ω X Y hXY *ᵥ
    (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp with hηdef
  set copyAll := ancillaCopyRegion (Finset.univ : Finset ↥X) with hcopyAll
  set physJ := ancillaPhysicalRegion X J with hphysJ
  have hJX : Disjoint J X := Finset.disjoint_of_subset_right hXN hJ
  have hTn (v : Reg (Qudits q) Λ × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ) : ‖WithLp.toLp 2 (v ∘ sp)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv sp v
  have hφform : φ = fun c => sBlank c.2.1 *
      (restoringEigenbasis Ω X *ᵥ xBlank) (restoringSplit q X Y hXY c.1).1.1 *
      Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
        (restoringSplit q X Y hXY c.1).2)) := restoringTransport_copy Ω X Y hXY sBlank xBlank
  have hUx : ‖WithLp.toLp 2 (restoringEigenbasis Ω X *ᵥ xBlank)‖ = 1 := by
    rw [norm_toLp_mulVec_of_conjTranspose_mul_self (restoringEigenbasis_unitary Ω X).2, hx]
  -- `η` is `Ω` tensored with a unit ancillary vector.
  set χ0 : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0
  set χ := ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ
    restoringEigenbasis Ω X) *ᵥ χ0
  have hηform : η = fun c => Ω c.1 * χ c.2 := restoringTransport_restored Ω X Y hXY p
  have hχ : ‖WithLp.toLp 2 χ‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron Ω (WithLp.toLp 2 χ)
    rw [hΩ, one_mul] at h
    rw [← h, ← hη, hηform]
    rfl
  have hprod : FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q)
      (WithLp.toLp 2 (η ∘ sp)) copyAll physJ = 0 := by
    rw [hηform]
    exact mutualInformation_ancillaProduct_copy_eq_zero hΩ hχ _ _
  have hdim' : Real.log (Fintype.card (FiniteProduct.Configuration
      (fun _ : AncillaSites Λ X => Fin q) copyAll)) ≤ C₂ * (n : ℝ) ^ 2 := by
    have hc : copyAll.card = X.card := by
      rw [hcopyAll, ancillaCopyRegion, Finset.card_disjSum, Finset.card_disjSum,
        Finset.card_empty, Finset.card_empty, Finset.card_univ, Fintype.card_coe, zero_add,
        zero_add]
    rw [Fintype.card_pi, Finset.prod_const, Fintype.card_fin, Finset.card_univ,
      Fintype.card_coe, hc, Nat.cast_pow, Real.log_pow]
    exact hdim
  have hfinal := mutualInformation_le_inv_pow_of_supported_unitary (φ := WithLp.toLp 2 (φ ∘ sp))
    (η := WithLp.toLp 2 (η ∘ sp)) (by rw [hTn]; exact hφ) (by rw [hTn]; exact hη)
    (disjoint_ancillaCopyRegion_ancillaPhysicalRegion _ _)
    (disjoint_disjSum_ancillaCopyRegion_union hJ _) hU hUu hprod hn hK hδ hdim'
  -- Back to `Ω` and the part `X'` of the target.
  set X'' : Finset ↥X := X'.subtype (· ∈ X)
  have hX''map : X''.map (Function.Embedding.subtype _) = X' :=
    Finset.subtype_map_of_mem fun x hx => hX' hx
  have hcopy := mutualInformation_ancillaCopy_eq hXY hΩ hs hUx X'' hJX
  rw [hX''map, ← hφform] at hcopy
  rw [← hcopy]
  exact hfinal _ (Finset.disjSum_mono le_rfl (Finset.disjSum_mono le_rfl
    (Finset.subset_univ _)))

end OpenAI
