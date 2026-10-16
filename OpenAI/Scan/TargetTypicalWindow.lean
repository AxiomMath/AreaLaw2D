/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/Scan/TargetTypicalWindow.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to the encodings of
`OpenAI.Scan.ActualMarginalTails`: `Site Λ` is `↥(Λ : Set (ℤ × ℤ))`, the bundled
`LocalHamiltonian` is an interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`,
`IsGappedGroundState` is the norm, eigenvector and `OpenAI.HasGlobalGap` conditions (the norm
of the truncated vector a named witness), TNLean's graph `cutBudget` is the square-lattice
`OpenAI.cutBudget` of the images in `ℤ²`, `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, the unordered
`edgeBoundary Λ X` is the ordered `OpenAI.edgeBoundary Λ (X.map (Function.Embedding.subtype _))`,
and `Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`. The cutwise moment and tail
bounds keep the regional states of `OpenAI.pureState` on `Y.map (Function.Embedding.subtype _)`,
as in `OpenAI.Scan.ActualMarginalTails`. The target tail and the target window read TNLean's
`reducedState Λ q Ωt X` and `regionalEntropy Λ q Ωt X` as the finite-product reduction
`FiniteProduct.reducedPure β Ωt X` and its entropy `FiniteProduct.entropy β Ωt X`, the encoding
of `OpenAI.abs_log_card_and_selectedSchmidtEntropy_sub_le` and
`OpenAI.Scan.CollarScan.eventually_actualScan_suppliedPrevector_sharp_upper`, whose typical set
indexes finite-product configurations; the two tails agree by the added
`OpenAI.surprisalTail_restrict_pureState_eq_finiteProduct`. TNLean's `trace_reducedState`
(`ZeroBoundary.lean`) is `FiniteProduct.trace_reducedPure`, and that import is dropped.
-/
import OpenAI.Scan.ActualMarginalTails
import OpenAI.Scan.TargetGeometry
import OpenAI.Scan.DomainFiniteProduct
import OpenAI.TypicalTailScales
import OpenAI.TypicalStateFromTail

/-!
# The target typical window of the actual truncated ground vector

Fixed physical parameters and a target-size coefficient determine the truncation
constant, target-budget constant and threshold before the scale, domain,
Hamiltonian, cut or scanner is chosen. Source ambient rows and clearance give
the compact volume bound and the target's `4n` boundary. The labelled lattice
budget is then at most `C_B * n * (log n)^12`.

One actual truncated physical ground vector retains its quantitative energy,
phase distance, trace distance and every-cut marginal bounds. Its target marginal
has failure mass at most `n^(-100)` at width `n^(3/5)`, hence positive canonical
typical mass and the source exponential eigenvalue window. Original `Ω` centers
the Hamiltonian terms; the entropy of `Ωt` centers this spectral window.
No auxiliary ground-state assertion or comparator construction is made.

## Main statements

* `OpenAI.surprisalTail_restrict_pureState_eq_finiteProduct`: the surprisal tail of a regional
  state of a lattice domain is that of its finite-product reduction.
* `OpenAI.Scan.CollarScan.target_typicalSet_bounds`: a regional tail gives the typical window.
* `OpenAI.Scan.CollarScan.exists_truncated_target_typical_window`: the construction.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 400–414, and `07-comparators.tex`, lines 37–53, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace OpenAI

open Arealaw

/-- The surprisal tail of a Hermitian matrix does not see a relabeling of its index. -/
theorem surprisalTail_eigenvalues_submatrix_equiv {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : m ≃ n)
    (S w : ℝ) :
    surprisalTail (hA.submatrix e).eigenvalues S w = surprisalTail hA.eigenvalues S w := by
  have h := congrArg
    (fun s : Multiset ℝ ↦ (s.map fun x ↦ if w < |-Real.log x - S| then x else 0).sum)
    (eigenvalues_multiset_submatrix_equiv hA e)
  simpa only [surprisalTail, Multiset.map_map, Function.comp_def,
    ← Finset.sum_eq_multiset_sum] using h

/-- The surprisal tail of the regional state of `Ω` on a cut `Q` of a lattice domain, about its
entropy, is that of the finite-product reduced pure state on `Q`. -/
theorem surprisalTail_restrict_pureState_eq_finiteProduct {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ω : EuclideanSpace ℂ (↥(Λ : Set (ℤ × ℤ)) → Fin q))
    (hΩ : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1) (Q : Finset ↥(Λ : Set (ℤ × ℤ))) (w : ℝ) :
    surprisalTail ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ω) hΩ).restrict
        (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues
        ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ω) hΩ).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) Q)) w =
      surprisalTail (FiniteProduct.reducedPure_posSemidef
        (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Q).isHermitian.eigenvalues
        (FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Q) w := by
  classical
  rw [regionalEntropy_eq_finiteProduct Λ q Ω hΩ Q]
  set ρ := (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ω) hΩ).restrict
    (map_embeddingSubtype_subset (T := Λ) Q)
  have hρ : ρ.M.submatrix
      (regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) Q)
        (mem_map_embeddingSubtype_iff Q)).symm
      (regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) Q)
        (mem_map_embeddingSubtype_iff Q)).symm =
      FiniteProduct.reducedPure (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Q :=
    reducedState_eq_finiteProduct Λ q Ω Q
  rw [← surprisalTail_eigenvalues_submatrix_equiv ρ.psd.isHermitian
    (regEquivPiSubtype (loc := Qudits q) (map_embeddingSubtype_subset (T := Λ) Q)
      (mem_map_embeddingSubtype_iff Q)).symm]
  congr 2

end OpenAI

namespace OpenAI.Scan.CollarScan

open Arealaw SpectralFilter SimpleGraph

/-- A regional tail gives a nonempty positive-eigenvalue typical set with
positive mass and the exponential window, including singular marginals.
Source: `07-comparators.tex`, lines 37–53. -/
theorem target_typicalSet_bounds {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1)
    (X : Finset ↥(Λ : Set (ℤ × ℤ))) {w δ : ℝ}
    (htail : surprisalTail (FiniteProduct.reducedPure_posSemidef
        (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωt X).isHermitian.eigenvalues
      (FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωt X) w ≤ δ) (hδ : δ < 1) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q
    let p := (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.eigenvalues
    let E := Entropy.typicalSet p (FiniteProduct.entropy β Ωt X) w
    let z := (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E
    0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
      ∀ i ∈ E, 0 < p i ∧
        Real.exp (-FiniteProduct.entropy β Ωt X - w) ≤ p i ∧
        p i ≤ Real.exp (-FiniteProduct.entropy β Ωt X + w) := by
  classical
  intro β p E z
  obtain ⟨hzδ, hz, hz1, _⟩ :=
    (FiniteProduct.reducedPure_posSemidef β Ωt X).typicalSet_normalizedSpectralRestriction_bounds
      w δ (FiniteProduct.trace_reducedPure β Ωt hΩt X) htail hδ
  refine ⟨sub_pos.mpr hδ, hzδ, hz, hz1, ?_, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro hE
    change 0 < (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass
      E at hz
    rw [hE] at hz
    simp only [Matrix.IsHermitian.spectralRestrictionMass, Finset.sum_empty,
      lt_self_iff_false] at hz
  · intro i hi
    exact ⟨(Entropy.mem_typicalSet.mp hi).1, Entropy.exp_le_of_mem_typicalSet hi⟩

/-- The source target window belongs to the same quantitative actual truncated
ground vector as every-cut moment and tail estimates. The constants and threshold
are independent of all physical and scanner data quantified afterward. The budget
uses the original admissible labels, even for repeated anchors and zero terms.
Only the target's `4n` boundary permits setting the lattice-budget factor to one;
no growing scanner parameter is absorbed into a constant.

Source: `08-scanner.tex`, lines 400–414, and `07-comparators.tex`, lines 37–53.
The floor scale is used literally; neither collar volume, target boundary,
cut budget nor target tail is assumed. -/
theorem exists_truncated_target_typical_window {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr C_B : ℝ, 0 < Ctr ∧ 0 < C_B ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ →
        ∀ (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (F : ScannerExponents)
        (T : Finset (ℤ × ℤ)) (hT : T.Nonempty),
        ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
        (∀ i, (S.anchor i).1 ∈ i.val) → N ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ d : ℕ, 1 ≤ d → d ≤ F.L S.n →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
          ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        let L := F.L S.n
        let X := S.A.filter fun x ↦ x.val ∈ T
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
        let δ := (S.n : ℝ) ^ (-100 : ℝ)
        let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q
        let B : Finset (↥(Λ : Set (ℤ × ℤ))) → ℝ := fun Y =>
          cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
            (fun i => (S.anchor i).1) (Y.map (Function.Embedding.subtype _))
        ((S.truncationSet L).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
        X ⊆ S.truncationSet L ∧
        (edgeBoundary Λ (X.map (Function.Embedding.subtype _))).card ≤ 4 * S.n ∧
        ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1),
          (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
            (e : ℂ) • WithLp.ofLp Ωt ∧
          HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e (g / 2) ∧
          0 ≤ e ∧ e ≤ ε ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
              vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
            Real.sqrt (2 * ε / g) ∧
          (∀ (Y : Finset (↥(Λ : Set (ℤ × ℤ)))) (u : ℝ),
            |u| ≤ tailRadius (2 / g) (B Y) →
            Real.log (surprisalMoment
                ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                    (map_embeddingSubtype_subset (T := Λ) Y)).psd.isHermitian.eigenvalues u) ≤
              u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                  (map_embeddingSubtype_subset (T := Λ) Y) +
                512 * Real.exp 1 * (2 / g) * B Y * u ^ 2) ∧
          (∀ (Y : Finset (↥(Λ : Set (ℤ × ℤ)))) (v : ℝ),
            surprisalTail
                ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                    (map_embeddingSubtype_subset (T := Λ) Y)).psd.isHermitian.eigenvalues
                ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                  (map_embeddingSubtype_subset (T := Λ) Y)) v ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(v / (32 * Real.sqrt ((1 + 2 / g) * B Y)))))) ∧
          B X ≤ C_B * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
          surprisalTail (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.eigenvalues
            (FiniteProduct.entropy β Ωt X) w ≤ δ ∧
          let p := (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.eigenvalues
          let E := Entropy.typicalSet p (FiniteProduct.entropy β Ωt X) w
          let z :=
            (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E
          0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
            ∀ i ∈ E, 0 < p i ∧
              Real.exp (-FiniteProduct.entropy β Ωt X - w) ≤ p i ∧
              p i ≤ Real.exp (-FiniteProduct.entropy β Ωt X + w) := by
  classical
  obtain ⟨Ctr, hCtr, htr⟩ := exists_truncated_reducedState_moment_tail_bounds R hJ hΔ
    (show 0 ≤ C_T + 1 by positivity)
  obtain ⟨C, _, hbudget⟩ := exists_latticeCutBudget_le_log hq R hCtr.le
    (show (0 : ℝ) ≤ 4 by norm_num)
  have hCB : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  obtain ⟨N, hN, hscalar⟩ := Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le) hCB
  refine ⟨Ctr, max 1 C, hCtr, hCB, N, hN, ?_⟩
  intro Λ Φ hΦ S E₀ Ω F T hT hΩ heig hgap hgraph hanchor hn hr hsize hdepth hrows hclear
  have hn2 : 2 ≤ S.n := hN.trans hn
  obtain ⟨hcard, hX, hboundary⟩ := S.source_target_geometry F T hT
    (by omega) hsize hdepth hrows hclear
  refine ⟨hcard, hX, hboundary, ?_⟩
  obtain ⟨e, Ωt, hΩt, heigt, hgapt, he0, he, hphase, htrace, hmoment, htail⟩ :=
    htr Λ Φ hΦ S E₀ Ω hΩ heig hgap hgraph hanchor (F.L S.n) hn2 hr hcard
  set X := S.A.filter fun x ↦ x.val ∈ T
  set B := cutBudget q Λ ((S.truncationSet (F.L S.n)).map (Function.Embedding.subtype _)) S.r₀
    (fun i => (S.anchor i).1) (X.map (Function.Embedding.subtype _))
  have hboundaryR :
      ((edgeBoundary Λ (X.map (Function.Embedding.subtype _))).card : ℝ) ≤ 4 * (S.n : ℝ) := by
    exact_mod_cast hboundary
  have hB : B ≤ max 1 C * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 := by
    have hb := hbudget Λ (fun i => (S.anchor i).1) hanchor
      ((S.truncationSet (F.L S.n)).map (Function.Embedding.subtype _))
      (X.map (Function.Embedding.subtype _)) (Finset.map_subset_map.mpr hX)
      (S.n : ℝ) 1 (by exact_mod_cast hn2) le_rfl
      (by simpa only [mul_one] using hboundaryR)
    simp only [B]
    rw [hr]
    calc
      _ ≤ C * ((S.n : ℝ) * Real.log (S.n : ℝ) ^ 12) := by
        simpa only [mul_one] using hb
      _ ≤ max 1 C * ((S.n : ℝ) * Real.log (S.n : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by ring
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (one_le_cutBudget q Λ _ S.r₀ _ _)
  have htypical : surprisalTail (FiniteProduct.reducedPure_posSemidef
        (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωt X).isHermitian.eigenvalues
      (FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωt X)
        ((S.n : ℝ) ^ ((3 : ℝ) / 5)) ≤ (S.n : ℝ) ^ (-100 : ℝ) := by
    rw [← surprisalTail_restrict_pureState_eq_finiteProduct Ωt
      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)]
    exact (htail X _).trans ((min_le_right _ _).trans (hscalar S.n hn B hBpos hB))
  have hδ : (S.n : ℝ) ^ (-100 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < S.n by omega))
      (by norm_num)
  exact ⟨e, Ωt, hΩt, heigt, hgapt, he0, he, hphase, htrace, hmoment, htail, hB, htypical,
    target_typicalSet_bounds Ωt hΩt X htypical hδ⟩

end OpenAI.Scan.CollarScan
