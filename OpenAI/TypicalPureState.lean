/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Entropy/TypicalPureState.lean` (Apache 2.0). Adapted: `Matrix.partialTraceRight`/
`partialTraceLeft` are Physlib's `Matrix.traceRight`/`traceLeft` (the private
`partialTraceLeft_complex_smul` is Physlib's `Matrix.traceLeft_smul`); `vonNeumannEntropy ρ hρ`
is `Arealaw.vonNeumann hρ`, with QICLean's scaling, concavity and nonnegativity lemmas replaced
by `Arealaw.vonNeumann_smul`, `Arealaw.sum_vonNeumann_sub_negMulLog_le` and
`Arealaw.entropy_nonneg`. Added here, being absent from the repository:
`Entropy.partialTraceLeft_vecMulVec_eq_map_conj` (from `QICLean/Entropy/Bipartite.lean`).
Physlib's `Matrix.PosSemidef.traceRight` takes `[DecidableEq B]`, so the statements whose
selected mass is that of `traceRight (vecMulVec ψ (star ψ))` keep the source's
`[DecidableEq B]` (`[DecidableEq C]` in the complementary-subsystem section) instead of
omitting it.
-/
import OpenAI.TypicalDensity
import OpenAI.RegionSSA
import OpenAI.PurificationSplitting

/-!
# Typical spectral restrictions of bipartite pure states

Orthogonal projection onto a selected family of marginal eigenvectors,
followed by normalization, gives the typical Schmidt truncation. Both
marginals are computed directly from this vector.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 240–247 and `comparator:post-marginal`,
at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix ComplexOrder InnerProductSpace Kronecker

noncomputable section

namespace Entropy

/-- The second marginal of a pure vector is the complex conjugate of the second
Gram matrix. The conjugation matters even though it does not change entropy. -/
theorem partialTraceLeft_vecMulVec_eq_map_conj {α β : Type*} [Fintype α] (ψ : α × β → ℂ) :
    Matrix.traceLeft (Matrix.vecMulVec ψ (star ψ)) =
      ((Matrix.schmidtCoeffMatrix ψ)ᴴ * Matrix.schmidtCoeffMatrix ψ).map
        (starRingEnd ℂ) := by
  ext i j
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.conjTranspose_apply,
    Matrix.schmidtCoeffMatrix_apply, starRingEnd_apply, star_star]

end Entropy

namespace Matrix

open Arealaw

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
private theorem gram_projection_split (C : Matrix A B ℂ) {P : Matrix A A ℂ}
    (hP : IsStarProjection P) :
    Cᴴ * C = (P * C)ᴴ * (P * C) + ((1 - P) * C)ᴴ * ((1 - P) * C) := by
  rw [conjTranspose_mul, conjTranspose_mul]
  simp only [show Pᴴ = P from hP.isSelfAdjoint,
    show (1 - P)ᴴ = 1 - P from hP.one_sub.isSelfAdjoint,
    Matrix.mul_assoc, ← Matrix.mul_assoc P P C, hP.isIdempotentElem.eq,
    ← Matrix.mul_assoc (1 - P) (1 - P) C, hP.one_sub.isIdempotentElem.eq,
    ← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

/-- Applying a matrix on the first tensor factor of a bipartite vector.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
def leftFilteredVector (P : Matrix A A ℂ) (ψ : EuclideanSpace ℂ (A × B)) :
    EuclideanSpace ℂ (A × B) :=
  WithLp.toLp 2 (fun x ↦ (P * schmidtCoeffMatrix ψ) x.1 x.2)

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem schmidtCoeffMatrix_leftFilteredVector (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    schmidtCoeffMatrix (leftFilteredVector P ψ) = P * schmidtCoeffMatrix ψ := rfl

omit [DecidableEq A] in
/-- The coefficient-matrix action equals the physical action on the first
tensor factor. OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem leftFilteredVector_eq_kronecker (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    leftFilteredVector P ψ = WithLp.toLp 2 ((P ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ ψ) := by
  ext x
  simp [leftFilteredVector, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    schmidtCoeffMatrix_apply]

omit [Fintype B] [DecidableEq B] in
/-- Tracing the first factor removes the cross terms between orthogonal selected
and discarded subspaces. OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_projection_split (ψ : EuclideanSpace ℂ (A × B))
    {P : Matrix A A ℂ} (hP : IsStarProjection P) :
    traceLeft (vecMulVec ψ (star ψ)) =
      traceLeft (vecMulVec (leftFilteredVector P ψ) (star (leftFilteredVector P ψ))) +
      traceLeft (vecMulVec (leftFilteredVector (1 - P) ψ)
        (star (leftFilteredVector (1 - P) ψ))) := by
  simp only [Entropy.partialTraceLeft_vecMulVec_eq_map_conj,
    schmidtCoeffMatrix_leftFilteredVector]
  rw [gram_projection_split (schmidtCoeffMatrix ψ) hP]
  exact Matrix.map_add (starRingEnd ℂ) (starRingEnd ℂ).map_add _ _

omit [DecidableEq A] [DecidableEq B] in
private theorem partialTraceRight_leftFilteredVector (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    traceRight (vecMulVec (leftFilteredVector P ψ) (star (leftFilteredVector P ψ))) =
      P * traceRight (vecMulVec ψ (star ψ)) * Pᴴ := by
  simp only [partialTraceRight_vecMulVec_eq, schmidtCoeffMatrix_leftFilteredVector,
    conjTranspose_mul, Matrix.mul_assoc]

private theorem vonNeumann_nonneg_of_trace_eq_one {R : Matrix B B ℂ} (hR : R.PosSemidef)
    (htr : R.trace = 1) : 0 ≤ vonNeumann hR.isHermitian := by
  rw [vonNeumann_eq_H]
  exact entropy_nonneg hR (by rw [htr, RCLike.one_re])

private theorem entropy_sub_negMulLog_trace_nonneg {R : Matrix B B ℂ} (hR : R.PosSemidef) :
    0 ≤ vonNeumann hR.isHermitian - Real.negMulLog R.trace.re := by
  by_cases ht : R.trace.re = 0
  · have hzero : R = 0 := hR.trace_eq_zero_iff.mp
      (by rw [hR.isHermitian.trace_eq_ofReal_re, ht, Complex.ofReal_zero])
    subst R
    rw [vonNeumann_eq_zero_of_eq_zero _ rfl]
    simp
  · have htpos : 0 < R.trace.re :=
      lt_of_le_of_ne (RCLike.nonneg_iff.mp hR.trace_nonneg).1 (Ne.symm ht)
    let σ := R.trace.re⁻¹ • R
    have hσ : σ.PosSemidef := hR.smul (inv_nonneg.mpr htpos.le)
    have hσtr : σ.trace = 1 := by
      rw [show σ.trace = (R.trace.re⁻¹ : ℂ) * R.trace from by simp [σ, trace_smul]]
      rw [hR.isHermitian.trace_eq_ofReal_re, Complex.ofReal_re,
        inv_mul_cancel₀ (by exact_mod_cast ht)]
    have hback : R.trace.re • σ = R := by simp [σ, smul_smul, ht]
    have hs := vonNeumann_smul hσ.isHermitian R.trace.re
    rw [vonNeumann_congr _ hR.isHermitian hback, hσtr, RCLike.one_re, mul_one] at hs
    linarith [mul_nonneg htpos.le (vonNeumann_nonneg_of_trace_eq_one hσ hσtr)]

private theorem normalized_entropy_le_of_sum {M R : Matrix B B ℂ}
    (hM : M.PosSemidef) (hR : R.PosSemidef) (htr : (M + R).trace = 1)
    (hz : 0 < M.trace.re) :
    M.trace.re * vonNeumann (hM.smul (inv_nonneg.mpr hz.le)).isHermitian ≤
      vonNeumann (hM.add hR).isHermitian := by
  have hc := sum_vonNeumann_sub_negMulLog_le
    (fun b : Bool ↦ cond b M R) (fun b ↦ Bool.rec hR hM b)
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, htr, RCLike.one_re,
    Real.negMulLog_one, sub_zero, RCLike.re_to_complex] at hc
  let σ := M.trace.re⁻¹ • M
  have hσ : σ.PosSemidef := hM.smul (inv_nonneg.mpr hz.le)
  have hσtr : σ.trace = 1 := by
    rw [show σ.trace = (M.trace.re⁻¹ : ℂ) * M.trace from by simp [σ, trace_smul]]
    rw [hM.isHermitian.trace_eq_ofReal_re, Complex.ofReal_re,
      inv_mul_cancel₀ (by exact_mod_cast hz.ne')]
  have hback : M.trace.re • σ = M := by simp [σ, smul_smul, hz.ne']
  have hs := vonNeumann_smul hσ.isHermitian M.trace.re
  rw [vonNeumann_congr _ hM.isHermitian hback, hσtr, RCLike.one_re, mul_one] at hs
  linarith [entropy_sub_negMulLog_trace_nonneg hR]

private theorem trace_spectralCompression {ρ : Matrix A A ℂ} (hρ : ρ.IsHermitian)
    (E : Finset A) (hz : hρ.spectralRestrictionMass E ≠ 0) :
    (hρ.spectralSelection E * ρ * hρ.spectralSelection E).trace =
      (hρ.spectralRestrictionMass E : ℂ) := by
  have h := hρ.trace_normalizedSpectralRestriction E hz
  rw [hρ.normalizedSpectralRestriction_eq, trace_smul, smul_eq_mul] at h
  simpa using (inv_mul_eq_iff_eq_mul₀ (RCLike.ofReal_ne_zero.mpr hz)).mp h

section Typical

variable (ψ : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "ρA" => traceRight (vecMulVec ψ (star ψ))
local notation "hρA" => Matrix.PosSemidef.traceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "PE" => Matrix.IsHermitian.spectralSelection
  (Matrix.PosSemidef.isHermitian hρA) E

/-- The normalized selected Schmidt vector, on the original bipartite space.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
def typicalPureState : EuclideanSpace ℂ (A × B) :=
  (Real.sqrt zE : ℂ)⁻¹ • leftFilteredVector PE ψ

set_option linter.unusedDecidableInType false in
private theorem trace_leftFiltered_spectralSelection (hz : zE ≠ 0) :
    (traceRight (vecMulVec (leftFilteredVector PE ψ)
      (star (leftFilteredVector PE ψ)))).trace = (zE : ℂ) := by
  rw [partialTraceRight_leftFilteredVector,
    show PEᴴ = PE from ((hρA).isHermitian.isStarProjection_spectralSelection E).isSelfAdjoint]
  exact trace_spectralCompression (hρA).isHermitian E hz

private theorem pureMatrix_typicalPureState (hz : 0 < zE) :
    vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E)) =
      (zE : ℂ)⁻¹ • vecMulVec (leftFilteredVector PE ψ) (star (leftFilteredVector PE ψ)) := by
  simp only [typicalPureState, WithLp.ofLp_smul, star_smul,
    Complex.star_def, map_inv₀, Complex.conj_ofReal,
    smul_vecMulVec, vecMulVec_smul, smul_smul]
  rw [← mul_inv, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt hz.le]

/-- The actual first marginal of the selected pure vector is the normalized
spectral restriction. OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem partialTraceRight_typicalPureState (hz : 0 < zE) :
    traceRight (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E))) =
      (hρA).isHermitian.normalizedSpectralRestriction E := by
  rw [pureMatrix_typicalPureState ψ E hz, traceRight_smul,
    partialTraceRight_leftFilteredVector,
    show PEᴴ = PE from ((hρA).isHermitian.isStarProjection_spectralSelection E).isSelfAdjoint,
    (hρA).isHermitian.normalizedSpectralRestriction_eq]
  rfl

/-- A positive-mass typical Schmidt truncation is a unit vector.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_typicalPureState (hz : 0 < zE) : ‖typicalPureState ψ E‖ = 1 := by
  have ht := (hρA).isHermitian.trace_normalizedSpectralRestriction E hz.ne'
  have hs := norm_toLp_sq (typicalPureState ψ E : A × B → ℂ)
  rw [WithLp.toLp_ofLp, ← trace_partialTraceRight_vecMulVec,
    partialTraceRight_typicalPureState ψ E hz, ht, Complex.one_re] at hs
  nlinarith [norm_nonneg (typicalPureState ψ E)]

set_option linter.unusedDecidableInType false in
private theorem star_dotProduct_leftFiltered_spectralSelection (hz : zE ≠ 0) :
    star (ψ : A × B → ℂ) ⬝ᵥ (leftFilteredVector PE ψ : A × B → ℂ) = (zE : ℂ) := by
  rw [star_dotProduct_eq_trace_conjTranspose_mul, schmidtCoeffMatrix_leftFilteredVector]
  rw [← Matrix.mul_assoc, trace_mul_cycle]
  have ht := trace_spectralCompression (hρA).isHermitian E hz
  rw [trace_mul_cycle, ((hρA).isHermitian.isStarProjection_spectralSelection E).isIdempotentElem.eq,
    trace_mul_comm] at ht
  simpa only [partialTraceRight_vecMulVec_eq] using ht

/-- The overlap with the normalized selected vector is the square root of the
selected mass. OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem inner_typicalPureState (hz : 0 < zE) :
    ⟪ψ, typicalPureState ψ E⟫_ℂ = (Real.sqrt zE : ℂ) := by
  rw [typicalPureState, inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, star_dotProduct_leftFiltered_spectralSelection ψ E hz.ne']
  norm_cast
  exact (inv_mul_eq_iff_eq_mul₀ (Real.sqrt_pos.mpr hz).ne').mpr (Real.mul_self_sqrt hz.le).symm

/-- The exact squared vector error of typical Schmidt truncation.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_sub_typicalPureState_sq (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    ‖ψ - typicalPureState ψ E‖ ^ 2 = 2 * (1 - Real.sqrt zE) := by
  rw [@norm_sub_sq ℂ, hψ, norm_typicalPureState ψ E hz,
    inner_typicalPureState ψ E hz, RCLike.re_eq_complex_re, Complex.ofReal_re]
  ring

omit [DecidableEq A] [DecidableEq B] in
private theorem trace_pure_of_norm_one (hψ : ‖ψ‖ = 1) :
    (vecMulVec ψ (star ψ)).trace = 1 := by
  change ⟪ψ, ψ⟫_ℂ = 1
  simp [hψ]

/-- The squared vector error is at most twice the discarded mass.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_sub_typicalPureState_sq_le (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    ‖ψ - typicalPureState ψ E‖ ^ 2 ≤ 2 * (1 - zE) := by
  have hz1 := (hρA).spectralRestrictionMass_le_one
    (by rw [traceRight_trace, trace_pure_of_norm_one ψ hψ]) E
  have hs : zE ≤ Real.sqrt zE :=
    (Real.le_sqrt hz.le hz.le).mpr (by nlinarith)
  linarith [norm_sub_typicalPureState_sq ψ E hψ hz]

local notation "ρB" => traceLeft (vecMulVec ψ (star ψ))
local notation "σB" => traceLeft
  (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E)))
local notation "RB" => traceLeft
  (vecMulVec (leftFilteredVector (1 - PE) ψ) (star (leftFilteredVector (1 - PE) ψ)))
local notation "MB" => traceLeft
  (vecMulVec (leftFilteredVector PE ψ) (star (leftFilteredVector PE ψ)))

/-- The actual complementary marginal is the normalized marginal of the selected
unnormalized vector. OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_typicalPureState (hz : 0 < zE) : σB = zE⁻¹ • MB := by
  change σB = ((zE⁻¹ : ℝ) : ℂ) • MB
  rw [Complex.ofReal_inv, pureMatrix_typicalPureState ψ E hz, traceLeft_smul]

/-- The actual complementary marginal is the sum of the selected and discarded
marginals. OpenAI area-law manuscript, `comparator:post-marginal`. The discarded
term remains unnormalized, so the formula also covers selected mass one. -/
theorem partialTraceLeft_typicalPureState_decomposition (hz : 0 < zE) :
    ρB = zE • σB + RB := by
  change ρB = (zE : ℂ) • σB + RB
  rw [partialTraceLeft_projection_split ψ
    ((hρA).isHermitian.isStarProjection_spectralSelection E),
    pureMatrix_typicalPureState ψ E hz, traceLeft_smul,
    smul_smul, mul_inv_cancel₀ (show (zE : ℂ) ≠ 0 from by exact_mod_cast hz.ne'), one_smul]

/-- The normalized selected complementary marginal is bounded above by the
original marginal divided by the selected mass, in positive-semidefinite order.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_typicalPureState_le (hz : 0 < zE) :
    (zE⁻¹ • ρB - σB).PosSemidef := by
  rw [partialTraceLeft_typicalPureState_decomposition ψ E hz,
    smul_add, smul_smul, inv_mul_cancel₀ hz.ne', one_smul, add_sub_cancel_left]
  exact (posSemidef_vecMulVec_self_star (leftFilteredVector (1 - PE) ψ)).traceLeft.smul
    (inv_nonneg.mpr hz.le)

/-- Entropy of the actual selected complementary marginal is at most the original
entropy divided by the selected mass. OpenAI area-law manuscript,
`comparator:post-marginal`. -/
theorem entropy_partialTraceLeft_typicalPureState_le (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    vonNeumann
        (posSemidef_vecMulVec_self_star (typicalPureState ψ E)).traceLeft.isHermitian ≤
      vonNeumann
        (posSemidef_vecMulVec_self_star ψ).traceLeft.isHermitian / zE := by
  have hsplit := partialTraceLeft_projection_split ψ
    ((hρA).isHermitian.isStarProjection_spectralSelection E)
  have ht : (MB).trace.re = zE := by
    rw [traceLeft_trace, ← traceRight_trace,
      trace_leftFiltered_spectralSelection ψ E hz.ne', Complex.ofReal_re]
  have hc := normalized_entropy_le_of_sum
    (posSemidef_vecMulVec_self_star (leftFilteredVector PE ψ)).traceLeft
    (posSemidef_vecMulVec_self_star (leftFilteredVector (1 - PE) ψ)).traceLeft
    (by rw [← hsplit, traceLeft_trace, trace_pure_of_norm_one ψ hψ])
    (by simpa only [ht] using hz)
  simp only [ht] at hc
  apply (le_div_iff₀ hz).mpr
  rw [mul_comm]
  simpa only [← hsplit, ← partialTraceLeft_typicalPureState ψ E hz] using hc

end Typical

section ComplementarySubsystem

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (ψ : EuclideanSpace ℂ (A × (B × C))) (E : Finset A)

local notation "ρA" => traceRight (vecMulVec ψ (star ψ))
local notation "hρA" => Matrix.PosSemidef.traceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "PE" => Matrix.IsHermitian.spectralSelection
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "ρB" => traceRight (traceLeft (vecMulVec ψ (star ψ)))
local notation "σB" => traceRight (traceLeft
  (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E))))
local notation "RB" => traceRight (traceLeft
  (vecMulVec (leftFilteredVector (1 - PE) ψ) (star (leftFilteredVector (1 - PE) ψ))))
local notation "MB" => traceRight (traceLeft
  (vecMulVec (leftFilteredVector PE ψ) (star (leftFilteredVector PE ψ))))

/-- The actual marginal on any factor of the complement splits into selected and
discarded contributions. OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceRight_partialTraceLeft_typicalPureState_decomposition (hz : 0 < zE) :
    ρB = zE • σB + RB := by
  have hs := congrArg traceRight
    (partialTraceLeft_typicalPureState_decomposition ψ E hz)
  simpa only [traceRight_add, traceRight_smul] using hs

/-- The actual selected marginal on a factor of the complement is bounded by the
original marginal divided by the selected mass, in positive-semidefinite order.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceRight_partialTraceLeft_typicalPureState_le (hz : 0 < zE) :
    (zE⁻¹ • ρB - σB).PosSemidef := by
  rw [partialTraceRight_partialTraceLeft_typicalPureState_decomposition ψ E hz,
    smul_add, smul_smul, inv_mul_cancel₀ hz.ne', one_smul, add_sub_cancel_left]
  have hR := posSemidef_vecMulVec_self_star (leftFilteredVector (1 - PE) ψ)
  exact hR.traceLeft.traceRight.smul (inv_nonneg.mpr hz.le)

/-- Entropy of the actual selected marginal on any factor of the complement is
bounded by the original marginal entropy divided by the selected mass.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem entropy_partialTraceRight_partialTraceLeft_typicalPureState_le
    (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    vonNeumann
        (posSemidef_vecMulVec_self_star
          (typicalPureState ψ E)).traceLeft.traceRight.isHermitian ≤
      vonNeumann
        (posSemidef_vecMulVec_self_star ψ).traceLeft.traceRight.isHermitian / zE := by
  have hsplit := congrArg traceRight (partialTraceLeft_projection_split ψ
    ((hρA).isHermitian.isStarProjection_spectralSelection E))
  simp only [traceRight_add] at hsplit
  have ht : (MB).trace.re = zE := by
    rw [traceRight_trace, traceLeft_trace, ← traceRight_trace,
      trace_leftFiltered_spectralSelection ψ E hz.ne', Complex.ofReal_re]
  have hc := normalized_entropy_le_of_sum
    (posSemidef_vecMulVec_self_star (leftFilteredVector PE ψ)).traceLeft.traceRight
    (posSemidef_vecMulVec_self_star
      (leftFilteredVector (1 - PE) ψ)).traceLeft.traceRight
    (by rw [← hsplit, traceRight_trace, traceLeft_trace,
      trace_pure_of_norm_one ψ hψ])
    (by simpa only [ht] using hz)
  have hn : σB = zE⁻¹ • MB := by
    have hs := congrArg traceRight (partialTraceLeft_typicalPureState ψ E hz)
    simpa only [traceRight_smul] using hs
  simp only [ht] at hc
  apply (le_div_iff₀ hz).mpr
  rw [mul_comm]
  simpa only [← hsplit, ← hn] using hc

end ComplementarySubsystem

end Matrix
