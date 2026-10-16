/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/MarginalTails.lean` (Apache 2.0).  Namespace `TNLean.PEPS.AreaLaw`
renamed to `OpenAI`.  TNLean's `LocalHamiltonian`, `IsGappedGroundState`, `reducedState`,
`regionalEntropy` and cuts of the site subtype become `OpenAI.IsAdmissible`, the eigenvector
equation with `OpenAI.HasGlobalGap`, `MState.restrict` of `OpenAI.pureState`,
`regionEntropy`, and cuts `A ⊆ Λ`, over any `RCLike` field; `cutLogBudget` is renamed
`latticeCutLogBudget`, the name `OpenAI.cutLogBudget` being taken by its general form; the
statements are derived from `OpenAI.marginal_tails`.
-/
import OpenAI.MarginalTails
import OpenAI.ReplicaSupport
import OpenAI.SupportCounting
import OpenAI.SupportedMatrixElements
import OpenAI.TypicalSet

/-!
# Marginal surprisal tails for finite-range lattice Hamiltonians

Lemma 3.1 of [OAI265] holds for any finite tensor product (`OpenAI.marginal_tails`).  This
file instantiates it on a finite domain `Λ ⊂ ℤ²` with local dimension `q`: the terms are the
admissible interactions `Φ X ⊗ 1`, indexed by the admissible supports, and the regional state
of a gapped ground vector satisfies the moment and tail bounds with
`ℬ = 1 + ∑ log² (e q^{|X|})` over the admissible supports `X` that meet both sides of the cut.
At the concentration width `concentrationWidth` the typical part of the marginal spectrum
carries mass at least `1 - (n + 2)^{-M}`.

An operator supported in `S ⊆ T` in the sense of `OpenAI.IsSupportedOn` is supported on the
cut `S` of the site subtype of `T` in the sense of `Entropy.IsSupportedOn`, the support notion
of the replica-transport layer.

## Main definitions

* `OpenAI.latticeCutLogBudget`: the parameter `ℬ_A` of Lemma 3.1 on the lattice.
* `OpenAI.concentrationWidth`: the width at which the marginal tail is `(n + 2)^{-M}`.

## Main statements

* `OpenAI.IsSupportedOn.isSupportedOn_siteConfig`: the two support notions agree.
* `OpenAI.IsAdmissible.log_surprisalMoment_reducedState_le`: eq. (3.1) for the regional state.
* `OpenAI.IsAdmissible.surprisalTail_reducedState_le`: eq. (3.2) for the regional state.
* `OpenAI.IsAdmissible.one_sub_rpow_le_typicalMass_reducedState`: the typical marginal
  spectrum.

## Implementation notes

TNLean's `partialTraceRight_cutVector`, identifying its regional state with the marginal in
cut coordinates, is `OpenAI.ptrace_eq_traceRight_piEquivPiSubtypeProd` here, and is not
restated.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.1, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and the concentration statement
  after it, lines 209–219.
-/

namespace OpenAI

open Arealaw Matrix
open scoped ComplexOrder

/-! ## Supported operators on the site subtype -/

section Support

variable {σ : Type*} [DecidableEq σ] {n : σ → ℕ} {S T : Finset σ}

/-- An operator supported in `S ⊆ T` acts as the identity outside the cut `S` of the sites of
`T`, in the sense of the general marginal-tail lemma. -/
theorem IsSupportedOn.isSupportedOn_siteConfig {h : S ⊆ T}
    {A : Matrix (Reg (fun i => Fin (n i)) T) (Reg (fun i => Fin (n i)) T) ℂ}
    (hA : IsSupportedOn h A) :
    Entropy.IsSupportedOn (n := fun i : T => n i) A (S.subtype (· ∈ T)) := by
  refine ⟨fun w w' hw => ?_, ?_⟩
  · obtain ⟨i, hi, hne⟩ := hw
    exact hA.apply_eq_zero ⟨i, fun hiS => hi (Finset.mem_subtype.2 hiS), hne⟩
  intro w τ w' τ' h1 h2 h3 h4
  obtain ⟨B, rfl⟩ := hA
  have hon : ∀ x y : Reg (fun i => Fin (n i)) T,
      (∀ v ∈ S.subtype (· ∈ T), x v = y v) → restr h x = restr h y := by
    intro x y hxy
    funext j
    exact hxy ⟨j.1, h j.2⟩ (Finset.mem_subtype.2 j.2)
  have hoff : ∀ x y : Reg (fun i => Fin (n i)) T, (∀ v ∉ S.subtype (· ∈ T), x v = y v) →
      restr (S := T \ S) Finset.sdiff_subset x = restr (S := T \ S) Finset.sdiff_subset y := by
    intro x y hxy
    funext j
    have hj : (⟨j.1, (Finset.mem_sdiff.1 j.2).1⟩ : T) ∉ S.subtype (· ∈ T) := by
      rw [Finset.mem_subtype]
      exact (Finset.mem_sdiff.1 j.2).2
    exact hxy _ hj
  rw [extendId_apply, extendId_apply, if_pos (hoff _ _ h3), if_pos (hoff _ _ h4), hon _ _ h1,
    hon _ _ h2]

end Support

/-! ## Lemma 3.1 on the lattice -/

section Lattice

variable {𝕜 : Type*} [RCLike 𝕜] {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}

variable (Λ q R) in
/-- The parameter `ℬ_A = 1 + ∑ log² (e q^{|X|})` of Lemma 3.1 for a cut `A`, the sum running
over the admissible supports `X` of range `R` that meet both `A` and its complement
[OAI265, Lemma 3.1, `02-initial.tex`, lines 47–55]. -/
noncomputable def latticeCutLogBudget (A : Finset (ℤ × ℤ)) : ℝ :=
  cutLogBudget (crossingTerms (fun X : supports Λ R => X.1) A)
    fun X => Fintype.card (Reg (Qudits q) X.1)

variable (Λ q R) in
theorem one_le_latticeCutLogBudget (A : Finset (ℤ × ℤ)) : 1 ≤ latticeCutLogBudget Λ q R A :=
  one_le_cutLogBudget _ _

/-- `OpenAI.marginal_tails` for the terms `Φ X ⊗ 1` of an admissible interaction, indexed by
the admissible supports. -/
private theorem IsAdmissible.marginalTails (hΦ : IsAdmissible Λ R J Φ) (hJ : 0 ≤ J)
    {E₀ Δ : ℝ} {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) (hΔ : 0 < Δ)
    (heig : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) :
    let p := ((pureState Ω hΩ).restrict hA).psd.isHermitian.eigenvalues
    let 𝓑 := latticeCutLogBudget Λ q R A
    (∀ u : ℝ, |u| ≤ (32 * Real.sqrt ((1 + J / Δ) * 𝓑))⁻¹ →
      Real.log (∑ j ∈ Finset.univ.filter (fun j => 0 < p j),
          p j * Real.exp (-u * Real.log (p j))) ≤
        u * (pureState Ω hΩ).regionEntropy hA + 512 * Real.exp 1 * (J / Δ) * 𝓑 * u ^ 2) ∧
    ∀ w : ℝ, 0 ≤ w →
      ∑ j ∈ Finset.univ.filter
          (fun j => 0 < p j ∧ w < |-Real.log (p j) - (pureState Ω hΩ).regionEntropy hA|), p j ≤
        min 1 (2 * Real.exp (Real.exp 1 / 2) *
          Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) * 𝓑))))) := by
  rw [hΦ.hamiltonian_eq_sum_supports] at heig hgap
  exact marginal_tails (𝕜 := 𝕜) (loc := Qudits q) Λ (supports Λ R) (fun X => X.1)
    (fun X => subset_of_mem_supports X.2) (fun X => extendId (subset_of_mem_supports X.2) (Φ X))
    J Δ E₀ Ω hΩ (fun X => isSupportedOn_extendId _ _) hΦ.isHermitian_extendId hJ
    hΦ.norm_extendId_le hΔ heig hgap A hA

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, moment bound.** For a gapped ground
vector `Ω` with gap `Δ > 0` of an admissible interaction with term norms at most `J ≥ 0`, and
any cut `A ⊆ Λ`, the surprisal of the regional state satisfies
`log E e^{uK} ≤ u S(A) + 512 e (J/Δ) ℬ u²` for `|u| ≤ 1/(32 √((1 + J/Δ) ℬ))`
[OAI265, Lemma 3.1, eq. (3.1); `02-initial.tex`, lines 34–63, `eq:initial-tail-mgf`]. -/
theorem IsAdmissible.log_surprisalMoment_reducedState_le (hΦ : IsAdmissible Λ R J Φ)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) (hΔ : 0 < Δ)
    (heig : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) {u : ℝ}
    (hu : |u| ≤ tailRadius (J / Δ) (latticeCutLogBudget Λ q R A)) :
    Real.log (surprisalMoment ((pureState Ω hΩ).restrict hA).psd.isHermitian.eigenvalues u) ≤
      u * (pureState Ω hΩ).regionEntropy hA +
        512 * Real.exp 1 * (J / Δ) * latticeCutLogBudget Λ q R A * u ^ 2 := by
  have key := (hΦ.marginalTails hJ hΩ hΔ heig hgap hA).1 u (by rwa [← one_div])
  rwa [sum_filter_pos_mul_exp_eq_surprisalMoment
    ((pureState Ω hΩ).restrict hA).psd.eigenvalues_nonneg] at key

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, tail bound.** Under the hypotheses of
`IsAdmissible.log_surprisalMoment_reducedState_le`, for every real `w`,
`Pr {|K - S(A)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + J/Δ) ℬ)))}`; for `w < 0` the
right-hand side is `1`.  [OAI265, Lemma 3.1, eq. (3.2); `02-initial.tex`, lines 64–69,
`eq:initial-tail-probability`], where `w ≥ 0`. -/
theorem IsAdmissible.surprisalTail_reducedState_le (hΦ : IsAdmissible Λ R J Φ) (hJ : 0 ≤ J)
    {E₀ Δ : ℝ} {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) (hΔ : 0 < Δ)
    (heig : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) (w : ℝ) :
    surprisalTail ((pureState Ω hΩ).restrict hA).psd.isHermitian.eigenvalues
        ((pureState Ω hΩ).regionEntropy hA) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A))))) := by
  have hp := ((pureState Ω hΩ).restrict hA).psd.eigenvalues_nonneg
  rcases le_or_gt 0 w with hw | hw
  · have key := (hΦ.marginalTails hJ hΩ hΔ heig hgap hA).2 w hw
    rwa [sum_filter_pos_eq_surprisalTail hp] at key
  · have hX : 1 ≤ 2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A)))) := by
      have h1 := Real.one_le_exp (by positivity : 0 ≤ Real.exp 1 / 2)
      have h2 := Real.one_le_exp (neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hw.le
        (by positivity : (0 : ℝ) ≤ 32 * Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A))))
      nlinarith
    rw [min_eq_left hX, ← MState.sum_eigenvalues_eq_one ((pureState Ω hΩ).restrict hA),
      surprisalTail]
    exact Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, hp j]

variable (Λ q R) in
/-- The concentration width `32 √((1 + J/Δ) ℬ_A) (M log (n + 2) + e/2 + log 2)` at which the
marginal tail of Lemma 3.1 drops to `(n + 2)^{-M}`. -/
noncomputable def concentrationWidth (J Δ : ℝ) (A : Finset (ℤ × ℤ)) (n : ℕ) (M : ℝ) : ℝ :=
  32 * Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A) *
    (M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2)

/-- **Typical marginal spectrum.** The positive eigenvalues of the regional state whose
surprisal lies within the concentration width of `S_Ω(A)` carry mass at least
`1 - (n + 2)^{-M}` [OAI265, `02-initial.tex`, lines 209–219, the concentration statement after
Lemma 3.1, before the lattice budget `ℬ_A ≤ C (1 + |∂_Λ A|)` is inserted]. -/
theorem IsAdmissible.one_sub_rpow_le_typicalMass_reducedState (hΦ : IsAdmissible Λ R J Φ)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) (hΔ : 0 < Δ)
    (heig : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) (n : ℕ) (M : ℝ) :
    1 - ((n : ℝ) + 2) ^ (-M) ≤
      Entropy.typicalMass ((pureState Ω hΩ).restrict hA).psd.isHermitian.eigenvalues
        ((pureState Ω hΩ).regionEntropy hA) (concentrationWidth Λ q R J Δ A n M) := by
  have htail := hΦ.surprisalTail_reducedState_le hJ hΩ hΔ heig hgap hA
    (concentrationWidth Λ q R J Δ A n M)
  have hmass := Entropy.one_sub_surprisalTail_le_typicalMass
    ((pureState Ω hΩ).restrict hA).psd.eigenvalues_nonneg
    (MState.sum_eigenvalues_eq_one _) ((pureState Ω hΩ).regionEntropy hA)
    (concentrationWidth Λ q R J Δ A n M)
  set Rr := Real.sqrt ((1 + J / Δ) * latticeCutLogBudget Λ q R A)
  have hB := one_le_latticeCutLogBudget Λ q R A
  have hR : 0 < Rr := Real.sqrt_pos.2 (by
    have : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
    positivity)
  have hexp : 2 * Real.exp (Real.exp 1 / 2) *
      Real.exp (-(concentrationWidth Λ q R J Δ A n M / (32 * Rr))) = ((n : ℝ) + 2) ^ (-M) := by
    have hw : concentrationWidth Λ q R J Δ A n M / (32 * Rr) =
        M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2 := by
      unfold concentrationWidth
      change 32 * Rr * _ / (32 * Rr) = _
      field_simp
    rw [hw, Real.rpow_def_of_pos (by positivity)]
    rw [show -(M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2) =
      Real.log (n + 2) * -M + (-(Real.exp 1 / 2) + -Real.log 2) by ring, Real.exp_add,
      Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log two_pos]
    field_simp
  have h2 := htail.trans (min_le_right _ _)
  rw [hexp] at h2
  linarith

end Lattice

end OpenAI
