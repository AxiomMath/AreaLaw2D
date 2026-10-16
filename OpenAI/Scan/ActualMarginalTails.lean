/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/Scan/ActualMarginalTails.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's encodings, as in
`OpenAI.Scan.ActualEnergyTerms`: `Site Λ` is `↥(Λ : Set (ℤ × ℤ))`, `AdmissibleSupport Λ R` is
`↥(supports Λ R)`, and the bundled `LocalHamiltonian` is an interaction `Φ` with
`hΦ : OpenAI.IsAdmissible Λ R J Φ`. `IsGappedGroundState Λ q H E Ω g` is the three hypotheses
`‖Ω‖ = 1`, `H *ᵥ ofLp Ω = E • ofLp Ω` and `OpenAI.HasGlobalGap H (ofLp Ω) E g`
(`OpenAI.normalized_eigen_hasGlobalGap_iff_euclidean`); in the existential statements the norm
hypothesis is a named witness, because the pure state of `Ωt` needs it. TNLean's
`reducedState Λ q Ωt X` and `regionalEntropy Λ q Ωt X` are the restriction and `regionEntropy`
of `OpenAI.pureState` to `X.map (Function.Embedding.subtype _)`, as in
`OpenAI.Scan.ActualSharpUpper`. The graph budget `cutBudget q S.graph (S.truncationSet L) S.r₀
S.anchor X` is the square-lattice `OpenAI.cutBudget` of the images in `ℤ²` of the truncation set,
the anchors and the cut, the encoding in which `OpenAI.Scan.CollarScan.truncatedEnergyTerm`
truncates. `Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`. The hypothesis
`S.graph = domainGraph Λ` is dropped from the two cutwise theorems, whose proofs no longer use
it; it is kept in the existential theorem. Lemma 3.1 is `OpenAI.marginal_tails` and
Proposition 4.5 is `OpenAI.exists_latticeFiniteSetTruncation`.
-/
import OpenAI.LatticeConstraints
import OpenAI.Scan.ActualEnergyTerms

/-!
# Marginal tails of the actual truncated physical Hamiltonian

The positive terms remain centered at the original unit vector `Ω`. Given a
gapped ground vector `Ωt` of their actual truncated physical sum, every regional
state of that same vector satisfies the supported-family moment and tail bounds.
The term norm bound is one, the gap is `g / 2`, and the resulting parameter is
`2 / g`, where `g = Δ / positiveNormalization 1 (Δ / 2) J`.

The budget is the literal geometric `cutBudget`, with every original admissible
support label retained. No cut containment, history condition, termwise kernel
equation or auxiliary identity extension enters the ground-state hypothesis.
The existential theorem obtains a single truncated ground vector from the original
Hamiltonian's ground-state hypothesis and the source cardinality and radius bounds.
The same witness retains its nonnegative small energy and the phase-adjusted vector
and trace-distance bounds from the original ground vector.
Its truncation constant is chosen before every physical instance and scan, independently
of the scanner's charge-slot constant `S.C₁`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 3.1 (`02-initial.tex`, lines 34–69), applied to the truncation in
`03-quasilocal.tex`, lines 417–426, as in `08-scanner.tex`, lines 400–414.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace OpenAI.Scan.CollarScan

open Arealaw SpectralFilter

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ)
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))

/-- Lemma 3.1 for the actual truncated physical sum, with parameter `1 / (g / 2)`. -/
private theorem marginalTails_truncated (hΦ : IsAdmissible Λ R J Φ)
    (hanchor : ∀ i, (S.anchor i).1 ∈ i.val) (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ}
    {Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)} (hΩt : ‖Ωt‖ = 1)
    (heig : (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
      (e : ℂ) • WithLp.ofLp Ωt)
    (hgap : HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (X : Finset (↥(Λ : Set (ℤ × ℤ)))) :
    let ψ := pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)
    let hX := map_embeddingSubtype_subset (T := Λ) X
    let p := (ψ.restrict hX).psd.isHermitian.eigenvalues
    let ϑ := 1 / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2)
    let 𝓑 := cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
      (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _))
    (∀ u : ℝ, |u| ≤ (32 * Real.sqrt ((1 + ϑ) * 𝓑))⁻¹ →
      Real.log (∑ j ∈ Finset.univ.filter (fun j => 0 < p j),
          p j * Real.exp (-u * Real.log (p j))) ≤
        u * ψ.regionEntropy hX + 512 * Real.exp 1 * ϑ * 𝓑 * u ^ 2) ∧
    ∀ w : ℝ, 0 ≤ w →
      ∑ j ∈ Finset.univ.filter (fun j => 0 < p j ∧ w < |-Real.log (p j) - ψ.regionEntropy hX|),
          p j ≤
        min 1 (2 * Real.exp (Real.exp 1 / 2) *
          Real.exp (-(w / (32 * Real.sqrt ((1 + ϑ) * 𝓑))))) := by
  classical
  intro ψ hX p ϑ 𝓑
  set S₀ := (S.truncationSet L).map (Function.Embedding.subtype (· ∈ (Λ : Set (ℤ × ℤ))))
  have hc := fun i => S.truncatedEnergyTerm_mem_Icc Φ Ω hΦ hΔ hΩ L i
  let anchor : Finset (ℤ × ℤ) → ℤ × ℤ := fun Y =>
    if hY : Y ∈ supports Λ R then (S.anchor ⟨Y, hY⟩).1 else (0, 0)
  have hanchor' : ∀ Y ∈ supports Λ R, anchor Y ∈ Y := fun Y hY => by
    simpa only [anchor, dif_pos hY] using hanchor ⟨Y, hY⟩
  have hai : ∀ i : supports Λ R, anchor i.1 = (S.anchor i).1 := fun i => by
    simp only [anchor, dif_pos i.2]
  have hsupp (i : supports Λ R) :
      IsSupportedOn (designatedSupport_subset Λ S₀ S.r₀ (S.anchor i).1)
        (S.truncatedEnergyTerm Φ Ω J Δ L i) := by
    have hk := positiveConstraint_isSupportedOn_domainComponent (le_refl 1) (half_pos hΔ)
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hΦ anchor hanchor' Ω
      (positiveNormalization 1 (Δ / 2) J) i
    rw [hai] at hk
    exact truncatedConstraint_isSupportedOn Λ S₀ S.r₀ (S.anchor i).1 hk
  have hg : 0 < (Δ / positiveNormalization 1 (Δ / 2) J) / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  have hB : 𝓑 = cutLogBudget
      (crossingTerms (fun i => OpenAI.designatedSupport Λ S₀ S.r₀ (S.anchor i).1)
        (X.map (Function.Embedding.subtype _)))
      (fun i => Fintype.card (Reg (Qudits q) (OpenAI.designatedSupport Λ S₀ S.r₀
        (S.anchor i).1))) :=
    cutBudget_eq_cutLogBudget q Λ S₀ S.r₀ _ _
  rw [hB]
  exact marginal_tails (𝕜 := ℂ) (loc := Qudits q) Λ (supports Λ R)
    (fun i => OpenAI.designatedSupport Λ S₀ S.r₀ (S.anchor i).1)
    (fun i => designatedSupport_subset Λ S₀ S.r₀ (S.anchor i).1)
    (fun i => S.truncatedEnergyTerm Φ Ω J Δ L i) 1 _ e (WithLp.ofLp Ωt)
    (star_dotProduct_self_eq_one_of_norm_eq_one hΩt) hsupp
    (fun i => (Matrix.nonneg_iff_posSemidef.mp (hc i).1).isHermitian) zero_le_one
    (fun i => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hc i).1).mpr (hc i).2) hg heig hgap
    (X.map (Function.Embedding.subtype _)) hX

/-- Lemma 3.1's moment bound for the actual truncated physical sum. The only
ground-state premise concerns the sum, while positivity, Hermitian symmetry,
norm and designated support are derived from the actual terms. The original
vector `Ω` still centers those terms. Source: `08-scanner.tex`, lines 400–414. -/
theorem log_surprisalMoment_truncated_reducedState_le (hΦ : IsAdmissible Λ R J Φ)
    (hanchor : ∀ i, (S.anchor i).1 ∈ i.val) (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ}
    {Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)} (hΩt : ‖Ωt‖ = 1)
    (heig : (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
      (e : ℂ) • WithLp.ofLp Ωt)
    (hgap : HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (X : Finset (↥(Λ : Set (ℤ × ℤ)))) {u : ℝ}
    (hu : |u| ≤ tailRadius (2 / (Δ / positiveNormalization 1 (Δ / 2) J))
      (cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
        (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _)))) :
    Real.log (surprisalMoment
        ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
            (map_embeddingSubtype_subset (T := Λ) X)).psd.isHermitian.eigenvalues u) ≤
      u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) X) +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
          cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
            (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _)) * u ^ 2 := by
  have hθ : (1 : ℝ) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) =
      2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by
    rw [div_div_eq_mul_div, one_mul]
  have key := (S.marginalTails_truncated Φ Ω hΦ hanchor hΔ hΩ L hΩt heig hgap X).1 u
    (by simpa only [hθ, tailRadius, one_div] using hu)
  rwa [hθ, sum_filter_pos_mul_exp_eq_surprisalMoment
    ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
        (map_embeddingSubtype_subset (T := Λ) X)).psd.eigenvalues_nonneg] at key

/-- Lemma 3.1's tail bound for every cut of the same actual truncated ground
vector. The cut may meet retained components outside the truncation set, and
the threshold may be any real number. Source: `08-scanner.tex`, lines 400–414. -/
theorem surprisalTail_truncated_reducedState_le (hΦ : IsAdmissible Λ R J Φ)
    (hanchor : ∀ i, (S.anchor i).1 ∈ i.val) (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ}
    {Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)} (hΩt : ‖Ωt‖ = 1)
    (heig : (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
      (e : ℂ) • WithLp.ofLp Ωt)
    (hgap : HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (X : Finset (↥(Λ : Set (ℤ × ℤ)))) (w : ℝ) :
    surprisalTail
        ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
            (map_embeddingSubtype_subset (T := Λ) X)).psd.isHermitian.eigenvalues
        ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) X)) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
              (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _))))))) := by
  have hθ : (1 : ℝ) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) =
      2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by
    rw [div_div_eq_mul_div, one_mul]
  set ψ := pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
    (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)
  set hX := map_embeddingSubtype_subset (T := Λ) X
  set 𝓑 := cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
    (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _))
  have hp := (ψ.restrict hX).psd.eigenvalues_nonneg
  rcases le_or_gt 0 w with hw | hw
  · have key := (S.marginalTails_truncated Φ Ω hΦ hanchor hΔ hΩ L hΩt heig hgap X).2 w hw
    rw [hθ, sum_filter_pos_eq_surprisalTail hp] at key
    exact key
  · have hg : 0 ≤ 2 / (Δ / positiveNormalization 1 (Δ / 2) J) :=
      (div_pos two_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))).le
    have hX1 : 1 ≤ 2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) * 𝓑)))) := by
      have h1 := Real.one_le_exp (by positivity : 0 ≤ Real.exp 1 / 2)
      have h2 := Real.one_le_exp (neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hw.le
        (by positivity : (0 : ℝ) ≤ 32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) * 𝓑))))
      nlinarith
    rw [min_eq_left hX1, ← MState.sum_eigenvalues_eq_one (ψ.restrict hX), surprisalTail]
    exact Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, hp j]

/-- One physical truncated ground vector satisfies both marginal estimates for every cut.
The constant `Ctr` depends only on `R, J, Δ, C₀` and is independent of the scanner's
charge-slot constant `S.C₁`. The original `Ω` still centers every positive constraint;
only the global projector-gap inequality subtracts the new energy `e`. The same
pair retains `0 ≤ e ≤ ε`, phase-adjusted distance at most `2 * √(ε / g)` from
`Ω`, and trace distance at most `√(2 * ε / g)`, where
`ε = min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)`.

Source: Proposition 4.5 (`03-quasilocal.tex`, lines 405–433 and 457–505), followed by
Lemma 3.1 as used in `08-scanner.tex`, lines 400–414. Empty domains, empty truncation
sets and retained disconnected components are allowed. No auxiliary identity extension
or truncated ground-state hypothesis is used. -/
theorem exists_truncated_reducedState_moment_tail_bounds
    (R : ℕ) {J Δ C₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ →
        ∀ (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)),
        ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        S.graph = (SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
        (∀ i, (S.anchor i).1 ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        ((S.truncationSet L).card : ℝ) ≤ C₀ * (S.n : ℝ) ^ 2 →
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let B : Finset (↥(Λ : Set (ℤ × ℤ))) → ℝ := fun X =>
          cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
            (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _))
        ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1),
          (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
            (e : ℂ) • WithLp.ofLp Ωt ∧
          HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e (g / 2) ∧
          0 ≤ e ∧ e ≤ ε ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
              vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
            Real.sqrt (2 * ε / g) ∧
          (∀ (X : Finset (↥(Λ : Set (ℤ × ℤ)))) (u : ℝ),
            |u| ≤ tailRadius (2 / g) (B X) →
            Real.log (surprisalMoment
                ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                    (map_embeddingSubtype_subset (T := Λ) X)).psd.isHermitian.eigenvalues u) ≤
              u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                  (map_embeddingSubtype_subset (T := Λ) X) +
                512 * Real.exp 1 * (2 / g) * B X * u ^ 2) ∧
          (∀ (X : Finset (↥(Λ : Set (ℤ × ℤ)))) (w : ℝ),
            surprisalTail
                ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                    (map_embeddingSubtype_subset (T := Λ) X)).psd.isHermitian.eigenvalues
                ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                  (map_embeddingSubtype_subset (T := Λ) X)) w ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(w / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) := by
  classical
  obtain ⟨Ctr, hCtr, htr⟩ := exists_latticeFiniteSetTruncation R hJ hΔ hC₀
  refine ⟨Ctr, hCtr, ?_⟩
  intro q _ Λ Φ hΦ S E₀ Ω hΩ heig hgap _ hanchor L hn hr hcard
  have hcard' : (((S.truncationSet L).map
      (Function.Embedding.subtype (· ∈ (Λ : Set (ℤ × ℤ))))).card : ℝ) ≤
      C₀ * (S.n : ℝ) ^ 2 := by
    rwa [Finset.card_map]
  obtain ⟨-, -, -, e, Ωt, hΩt, heigt, he0, he, hgapt, hphase, htrace⟩ :=
    htr Λ Φ hΦ (fun i => (S.anchor i).1) hanchor E₀ Ω hΩ heig hgap (S.n : ℝ)
      (by exact_mod_cast hn) _ hcard'
  have hsum : (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) =
      ∑ i, truncatedConstraint q Λ
        ((S.truncationSet L).map (Function.Embedding.subtype _))
        ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ (S.anchor i).1
        (positiveConstraint (positiveNormalization 1 (Δ / 2) J)
          (centeredFilter 1 (Δ / 2) (hamiltonian Λ Φ) Ω
            (extendId (subset_of_mem_supports i.2) (Φ i)))) := by
    simp only [truncatedEnergyTerm, positiveTerm, hr]
  rw [← hsum] at heigt hgapt
  refine ⟨e, Ωt, hΩt, heigt, hgapt, he0, he, hphase, htrace, ?_, ?_⟩
  · intro X u hu
    exact S.log_surprisalMoment_truncated_reducedState_le Φ Ω hΦ hanchor hΔ hΩ L hΩt heigt
      hgapt X hu
  · intro X w
    exact S.surprisalTail_truncated_reducedState_le Φ Ω hΦ hanchor hΔ hΩ L hΩt heigt hgapt X w

end OpenAI.Scan.CollarScan
