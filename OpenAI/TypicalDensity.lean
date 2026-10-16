/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Entropy/TypicalDensity.lean` (Apache 2.0), together with the declarations of
`QICLean/Entropy/TypicalSpectrum.lean` it uses. Generalized from `ℂ` to `RCLike 𝕜`; QICLean's
`vonNeumannEntropy ρ hρ` is `Arealaw.vonNeumann hρ` and `Entropy.probabilityEntropy` is
`Arealaw.H`.
-/
import Arealaw.EntropyBounds
import Arealaw.VonNeumann
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Density matrices restricted to selected spectral indices

A finite set of eigenvalue indices determines an orthogonal projection onto the
corresponding eigenvectors. The normalized spectral restriction is the matrix
obtained by retaining these eigenvalues, dividing by their total mass, and
setting the remaining eigenvalues to zero. The matrix acts on the original
Hilbert space. Its rank and von Neumann entropy give the cardinality and entropy
of the selected normalized spectrum.

For the spectrum itself: let `E` be a finite set of indices whose weights lie between
`exp (-S - w)` and `exp (-S + w)`, and let `z` be their total mass. After division
by `z`, the weights form a probability distribution. Both its entropy and the
logarithm of the cardinality of `E` differ from `S` by at most `w + |log z|`.
Weights outside `E` are unrestricted, so zero eigenvalues outside the selected
Schmidt indices cause no difficulty.

## Main definitions

* `Entropy.normalizedRestriction`: a family restricted to `E` and divided by its mass.
* `Matrix.IsHermitian.spectralSelection`: the projection onto selected eigenvectors.
* `Matrix.IsHermitian.normalizedSpectralRestriction`: the normalized selected spectrum.

## Main statements

* `Entropy.typicalSpectrum_entropy_bounds`: the cardinality and entropy estimates for a
  typical set of weights.
* `Matrix.PosSemidef.typicalSpectralRestriction_entropy_bounds`: the rank and von Neumann
  entropy estimates for the normalized typical spectral restriction.

## Implementation notes

`Matrix.vonNeumann_eq_H_of_eq_conj_diagonal` computes the entropy of a unitary conjugate of a
real diagonal matrix through its characteristic polynomial; it replaces QICLean's
`vonNeumannEntropy_units_conj` and `vonNeumannEntropy_diagonal`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
  2026), equations `comparator:typical-set` and `comparator:typical-entropies`,
  `07-comparators.tex`, lines 39–55, at commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix ComplexOrder

open Arealaw

noncomputable section

namespace Entropy

variable {ι : Type*}

/-- A finite family restricted to `E` and divided by its mass.
OpenAI area-law manuscript, `comparator:typical-set`. -/
def normalizedRestriction (p : ι → ℝ) (E : Finset ι) (i : E) : ℝ :=
  p i / ∑ j ∈ E, p j

/-- Restricting to a set of nonzero mass and normalizing gives total weight one. -/
theorem sum_normalizedRestriction {p : ι → ℝ} {E : Finset ι}
    (hz : (∑ j ∈ E, p j) ≠ 0) : ∑ i : E, normalizedRestriction p E i = 1 := by
  classical
  simp only [normalizedRestriction, ← Finset.sum_div]
  rw [Finset.sum_coe_sort]
  exact div_self hz

/-- The number of typical indices has logarithm within `w` of `S + log z`.
OpenAI area-law manuscript, `comparator:typical-entropies`. -/
theorem log_card_typical_centered {p : ι → ℝ} {E : Finset ι} {S w : ℝ}
    (hz : 0 < ∑ i ∈ E, p i)
    (hE : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |Real.log (E.card : ℝ) - S - Real.log (∑ i ∈ E, p i)| ≤ w := by
  classical
  have hne : E.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hz
  have hc : (0 : ℝ) < E.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hlo := Finset.sum_le_sum fun i hi ↦ (hE i hi).1
  have hhi := Finset.sum_le_sum fun i hi ↦ (hE i hi).2
  simp only [Finset.sum_const, nsmul_eq_mul] at hlo hhi
  have hloglo := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlo
  have hloghi := Real.log_le_log hz hhi
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hloglo hloghi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The normalized restriction of positive selected weights is positive. -/
theorem normalizedRestriction_pos {p : ι → ℝ} {E : Finset ι}
    (hz : 0 < ∑ j ∈ E, p j) {i : E} (hi : 0 < p i) :
    0 < normalizedRestriction p E i := div_pos hi hz

/-- The entropy of the normalized typical spectrum is within `w` of `S + log z`.
OpenAI area-law manuscript, `comparator:typical-entropies`. -/
theorem entropy_normalizedRestriction_typical_centered {p : ι → ℝ} {E : Finset ι}
    {S w : ℝ} (hz : 0 < ∑ i ∈ E, p i)
    (hE : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |H (normalizedRestriction p E) - S - Real.log (∑ i ∈ E, p i)| ≤ w := by
  classical
  have hp (i : E) : 0 < p i := (Real.exp_pos _).trans_le (hE i i.property).1
  have hpoint (i : E) :
      S - w + Real.log (∑ j ∈ E, p j) ≤
          -Real.log (normalizedRestriction p E i) ∧
        -Real.log (normalizedRestriction p E i) ≤ S + w + Real.log (∑ j ∈ E, p j) := by
    have hl := Real.log_le_log (Real.exp_pos _) (hE i i.property).1
    have hu := Real.log_le_log (hp i) (hE i i.property).2
    rw [Real.log_exp] at hl hu
    rw [normalizedRestriction, Real.log_div (hp i).ne' hz.ne']
    constructor <;> linarith
  have hlo := Finset.sum_le_sum (s := Finset.univ) fun (i : E) _ ↦
    mul_le_mul_of_nonneg_left (hpoint i).1 (normalizedRestriction_pos hz (hp i)).le
  have hhi := Finset.sum_le_sum (s := Finset.univ) fun (i : E) _ ↦
    mul_le_mul_of_nonneg_left (hpoint i).2 (normalizedRestriction_pos hz (hp i)).le
  have hsum := sum_normalizedRestriction hz.ne'
  have hent : H (normalizedRestriction p E) =
      ∑ i : E, normalizedRestriction p E i * -Real.log (normalizedRestriction p E i) := by
    simp only [H, Real.negMulLog, mul_neg, neg_mul]
  rw [← hent, ← Finset.sum_mul, hsum, one_mul] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The logarithmic cardinality and normalized entropy estimates for a typical
Schmidt set. OpenAI area-law manuscript, `comparator:typical-entropies`.
Only the selected weights occur in the hypotheses; no strict positivity of the
whole marginal spectrum is required. -/
theorem typicalSpectrum_entropy_bounds {p : ι → ℝ} {E : Finset ι} {S w : ℝ}
    (hz : 0 < ∑ i ∈ E, p i)
    (hE : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |Real.log (E.card : ℝ) - S| ≤ w + |Real.log (∑ i ∈ E, p i)| ∧
      |H (normalizedRestriction p E) - S| ≤ w + |Real.log (∑ i ∈ E, p i)| := by
  have htriangle (x z : ℝ) (h : |x - S - z| ≤ w) : |x - S| ≤ w + |z| := by
    calc |x - S| = |(x - S - z) + z| := by congr 1; ring
      _ ≤ |x - S - z| + |z| := abs_add_le _ _
      _ ≤ w + |z| := by linarith
  exact ⟨htriangle _ _ (log_card_typical_centered hz hE),
    htriangle _ _ (entropy_normalizedRestriction_typical_centered hz hE)⟩

end Entropy

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The entropy of a unitary conjugate `U D U⋆` of a real diagonal matrix `D = diag d` is the
Shannon entropy of `d`. -/
theorem vonNeumann_eq_H_of_eq_conj_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (U : unitary (Matrix n n 𝕜)) (d : n → ℝ)
    (h : A = (U : Matrix n n 𝕜) * diagonal (fun i ↦ (d i : 𝕜)) * star (U : Matrix n n 𝕜)) :
    vonNeumann hA = H d := by
  rw [vonNeumann_eq_H]
  refine H_eq_of_multiset_eq (Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_)
  have hchar : A.charpoly = (diagonal fun i ↦ (d i : 𝕜)).charpoly := by
    rw [h, mul_assoc, charpoly_mul_comm, mul_assoc, Unitary.coe_star_mul_self, mul_one]
  have hmap : Finset.univ.val.map (fun i ↦ Polynomial.X - Polynomial.C (d i : 𝕜)) =
      (Finset.univ.val.map fun i ↦ (d i : 𝕜)).map
        (fun a ↦ Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]
    rfl
  rw [Multiset.map_map, ← hA.roots_charpoly_eq_eigenvalues, hchar, charpoly_diagonal,
    Finset.prod_eq_multiset_prod, hmap, Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_map]
  rfl

variable {ρ : Matrix n n 𝕜}

/-- Projection onto a selected family of Hermitian eigenvectors. -/
def IsHermitian.spectralSelection (hρ : ρ.IsHermitian) (E : Finset n) : Matrix n n 𝕜 :=
  (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) hρ.eigenvectorUnitary)
    (diagonal fun i ↦ if i ∈ E then 1 else 0)

/-- The mass carried by the selected eigenvalue indices.
OpenAI area-law manuscript, `comparator:typical-set`. -/
def IsHermitian.spectralRestrictionMass (hρ : ρ.IsHermitian) (E : Finset n) : ℝ :=
  ∑ i ∈ E, hρ.eigenvalues i

/-- The selected normalized spectrum, extended by zero on the other eigenspaces.
OpenAI area-law manuscript, `comparator:typical-set`. -/
def IsHermitian.normalizedSpectralRestriction (hρ : ρ.IsHermitian) (E : Finset n) :
    Matrix n n 𝕜 :=
  (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) hρ.eigenvectorUnitary)
    (diagonal fun i ↦ if i ∈ E then
      ((hρ.eigenvalues i / hρ.spectralRestrictionMass E : ℝ) : 𝕜) else 0)

/-- A spectral selection is an orthogonal projection. -/
theorem IsHermitian.isStarProjection_spectralSelection (hρ : ρ.IsHermitian) (E : Finset n) :
    IsStarProjection (hρ.spectralSelection E) := by
  rw [isStarProjection_iff']
  simp only [spectralSelection, ← map_mul, ← map_star, diagonal_mul_diagonal]
  constructor
  · congr 1
    apply congrArg diagonal
    funext i
    split_ifs <;> simp
  · congr 1
    rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
    apply congrArg diagonal
    funext i
    split_ifs <;> simp_all

/-- The selected projection commutes with the original Hermitian matrix. -/
theorem IsHermitian.commute_spectralSelection (hρ : ρ.IsHermitian) (E : Finset n) :
    Commute (hρ.spectralSelection E) ρ := by
  change hρ.spectralSelection E * ρ = ρ * hρ.spectralSelection E
  conv_lhs => rhs; rw [hρ.spectral_theorem]
  conv_rhs => lhs; rw [hρ.spectral_theorem]
  simp only [spectralSelection, ← map_mul, diagonal_mul_diagonal]
  congr 1
  apply congrArg diagonal
  funext i
  exact mul_comm _ _

/-- A positive-mass spectral restriction of a positive matrix is positive. -/
theorem PosSemidef.normalizedSpectralRestriction_posSemidef (hρ : ρ.PosSemidef)
    (E : Finset n) (hz : 0 < hρ.isHermitian.spectralRestrictionMass E) :
    (hρ.isHermitian.normalizedSpectralRestriction E).PosSemidef := by
  rw [IsHermitian.normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply]
  have hd : (diagonal fun i ↦ if i ∈ E then
      ((hρ.isHermitian.eigenvalues i / hρ.isHermitian.spectralRestrictionMass E : ℝ) : 𝕜)
      else 0).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    change 0 ≤ if i ∈ E then
      ((hρ.isHermitian.eigenvalues i / hρ.isHermitian.spectralRestrictionMass E : ℝ) : 𝕜)
      else 0
    split_ifs
    · exact RCLike.ofReal_nonneg.mpr (div_nonneg (hρ.eigenvalues_nonneg i) hz.le)
    · exact le_rfl
  exact hd.mul_mul_conjTranspose_same _

/-- Normalizing a positive-mass selected spectrum gives trace one. -/
theorem IsHermitian.trace_normalizedSpectralRestriction (hρ : ρ.IsHermitian) (E : Finset n)
    (hz : hρ.spectralRestrictionMass E ≠ 0) :
    (hρ.normalizedSpectralRestriction E).trace = 1 := by
  rw [normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rw [Finset.sum_ite_mem_eq]
  rw [← RCLike.ofReal_sum, ← Finset.sum_div, ← spectralRestrictionMass, div_self hz,
    RCLike.ofReal_one]

/-- A spectral restriction is the normalized compression by its selected projection. -/
theorem IsHermitian.normalizedSpectralRestriction_eq (hρ : ρ.IsHermitian) (E : Finset n) :
    hρ.normalizedSpectralRestriction E = (hρ.spectralRestrictionMass E : 𝕜)⁻¹ •
      (hρ.spectralSelection E * ρ * hρ.spectralSelection E) := by
  conv_rhs => arg 2; lhs; rhs; rw [hρ.spectral_theorem]
  simp only [spectralSelection, normalizedSpectralRestriction, ← map_mul,
    ← map_smul, diagonal_mul_diagonal, ← diagonal_smul]
  congr 1
  apply congrArg diagonal
  funext i
  split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]

/-- For a trace-one positive matrix, a selected spectral mass is at most one. -/
theorem PosSemidef.spectralRestrictionMass_le_one (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (E : Finset n) : hρ.isHermitian.spectralRestrictionMass E ≤ 1 := by
  have hsum : ∑ i, hρ.isHermitian.eigenvalues i = 1 := by
    rw [← re_trace_eq_sum_eigenvalues hρ, htr, RCLike.one_re]
  rw [IsHermitian.spectralRestrictionMass, ← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg E.subset_univ
    (fun i _ _ ↦ hρ.eigenvalues_nonneg i)

/-- The rank of a normalized selected spectrum is the number of its positive indices. -/
theorem IsHermitian.rank_normalizedSpectralRestriction (hρ : ρ.IsHermitian) (E : Finset n)
    (hz : hρ.spectralRestrictionMass E ≠ 0)
    (hpos : ∀ i ∈ E, 0 < hρ.eigenvalues i) :
    (hρ.normalizedSpectralRestriction E).rank = E.card := by
  classical
  rw [normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply,
    ← Unitary.coe_star]
  have hu := (isUnit_iff_isUnit_det _).mp
    (Unitary.isUnit_coe (U := hρ.eigenvectorUnitary))
  have hus := (isUnit_iff_isUnit_det _).mp
    (Unitary.isUnit_coe (U := star hρ.eigenvectorUnitary))
  rw [rank_mul_eq_left_of_isUnit_det _ _ hus,
    rank_mul_eq_right_of_isUnit_det _ _ hu, rank_diagonal]
  have hi (i : n) :
      (if i ∈ E then ((hρ.eigenvalues i / hρ.spectralRestrictionMass E : ℝ) : 𝕜)
        else 0) ≠ 0 ↔ i ∈ E := by
    by_cases he : i ∈ E
    · simp [he, (hpos i he).ne', hz]
    · simp [he]
  exact (Fintype.card_congr (Equiv.subtypeEquivRight hi)).trans (Fintype.card_coe E)

/-- The von Neumann entropy of the actual spectral restriction is the Shannon
entropy of its selected normalized eigenvalues. -/
theorem PosSemidef.entropy_normalizedSpectralRestriction (hρ : ρ.PosSemidef) (E : Finset n)
    (hz : 0 < hρ.isHermitian.spectralRestrictionMass E) :
    vonNeumann (hρ.normalizedSpectralRestriction_posSemidef E hz).isHermitian =
      H (Entropy.normalizedRestriction hρ.isHermitian.eigenvalues E) := by
  let q : n → ℝ := fun i ↦ if i ∈ E then
    hρ.isHermitian.eigenvalues i / hρ.isHermitian.spectralRestrictionMass E else 0
  have heq : hρ.isHermitian.normalizedSpectralRestriction E =
      (hρ.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) * (diagonal fun i ↦ (q i : 𝕜)) *
        star (hρ.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) := by
    rw [IsHermitian.normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply]
    congr 2
    apply congrArg diagonal
    funext i
    by_cases hi : i ∈ E <;> simp [q, hi]
  rw [vonNeumann_eq_H_of_eq_conj_diagonal _ _ q heq]
  simp only [H, Entropy.normalizedRestriction]
  rw [Finset.sum_coe_sort (s := E)
    (f := fun i ↦ Real.negMulLog (hρ.isHermitian.eigenvalues i /
      ∑ j ∈ E, hρ.isHermitian.eigenvalues j))]
  simp [q, apply_ite, IsHermitian.spectralRestrictionMass]

/-- Cardinality and von Neumann entropy estimates for the actual normalized
typical spectral restriction. OpenAI area-law manuscript,
`comparator:typical-entropies`. Only selected positive eigenvalues are required;
the original positive matrix may have a nontrivial kernel. -/
theorem PosSemidef.typicalSpectralRestriction_entropy_bounds (hρ : ρ.PosSemidef)
    (E : Finset n) (w : ℝ) (hz : 0 < hρ.isHermitian.spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-vonNeumann hρ.isHermitian - w) ≤ hρ.isHermitian.eigenvalues i ∧
        hρ.isHermitian.eigenvalues i ≤ Real.exp (-vonNeumann hρ.isHermitian + w)) :
    |Real.log ((hρ.isHermitian.normalizedSpectralRestriction E).rank : ℝ) -
      vonNeumann hρ.isHermitian| ≤
        w + |Real.log (hρ.isHermitian.spectralRestrictionMass E)| ∧
      |vonNeumann (hρ.normalizedSpectralRestriction_posSemidef E hz).isHermitian -
        vonNeumann hρ.isHermitian| ≤
          w + |Real.log (hρ.isHermitian.spectralRestrictionMass E)| := by
  have hpos (i : n) (hi : i ∈ E) : 0 < hρ.isHermitian.eigenvalues i :=
    (Real.exp_pos _).trans_le (hE i hi).1
  rw [hρ.isHermitian.rank_normalizedSpectralRestriction E hz.ne' hpos,
    hρ.entropy_normalizedSpectralRestriction E hz]
  exact Entropy.typicalSpectrum_entropy_bounds hz hE

end Matrix
