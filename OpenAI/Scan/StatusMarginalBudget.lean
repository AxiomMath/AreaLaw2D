/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/StatusMarginalBudget.lean` (Apache 2.0); the file is unchanged at
commit 576d1624411e36a16cfc84aba9883f91416bcd32. Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to
`OpenAI.Scan`. The containment lemma, private in the source, is public here. TNLean's graph
`cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Q` is the square-lattice `OpenAI.cutBudget`
of the images in `ℤ²` of the truncation set, the anchors and the cut, as in
`OpenAI.Scan.ActualMarginalTails`; its unordered `edgeBoundary Λ Q` of `Q : Finset (Site Λ)` is
the ordered `OpenAI.edgeBoundary Λ (Q.map (Function.Embedding.subtype _))`, of the same
cardinality; `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`; `cutBudget_compl` and
`edgeBoundary_compl` become `OpenAI.cutBudget_sdiff` and `OpenAI.card_edgeBoundary_sdiff_left`.
The cut-edge bounds are those of `OpenAI.Scan.ScanHistories` and the lattice crossing theorem is
`OpenAI.exists_latticeCutBudget_le_log`.
-/
import OpenAI.LatticeConstraints
import OpenAI.Scan.ScanHistories
import OpenAI.Scan.StatusContainment
import OpenAI.Scan.StatusCutBounds

/-!
# The five physical status regions

The regions are precisely XU, V, Y, U and UY. All except V lie in the
compact truncation set; for V it is the complement that lies there.
The actual cut-edge estimates give the common constant 40, and the lattice
crossing theorem gives a coefficient chosen before all finite domains and
scanners. The factor D is retained. No geometric budget is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32–58 and 400–414; `07-comparators.tex`, lines 70–85,
at `openai/math@adc7f124`.
-/

namespace OpenAI.Scan

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The five physical marginals in the comparator moment assumption.
Coincident regions are allowed, including empty regions. -/
noncomputable def statusMarginalRegions (depth : V → ℤ) (σ : PhysicalPartition V) :
    Finset (Finset V) := by
  classical
  exact {receiving σ false, receiving σ true, middle σ,
    positiveNear depth σ, positiveNearMiddle depth σ}

/-- Every status region, or its complement for the far side, lies in a set containing the
complement of the far side. -/
theorem statusMarginalRegions_containment (depth : V → ℤ)
    (σ : PhysicalPartition V) {S₀ Q : Finset V}
    (hcompact : (receiving σ true)ᶜ ⊆ S₀) (hQ : Q ∈ statusMarginalRegions depth σ) :
    Q ⊆ S₀ ∨ Qᶜ ⊆ S₀ := by
  classical
  have hnear : receiving σ false ⊆ S₀ := by
    intro x hx
    apply hcompact
    have hxσ := (Finset.mem_filter.mp hx).2
    simp [receiving, hxσ]
  have hmiddle : middle σ ⊆ S₀ := by
    intro x hx
    apply hcompact
    have hxσ := (Finset.mem_filter.mp hx).2
    simp [receiving, hxσ]
  simp only [statusMarginalRegions, Finset.mem_insert, Finset.mem_singleton] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hnear
  · exact Or.inr hcompact
  · exact Or.inl hmiddle
  · exact Or.inl ((Finset.filter_subset _ _).trans hnear)
  · exact Or.inl ((Finset.filter_subset _ _).trans (Finset.union_subset hnear hmiddle))

/-- Each of the five status regions has at most `40nD` cut edges. -/
private theorem statusMarginalRegions_boundary {Λ : Finset (ℤ × ℤ)}
    (depth : ↥(Λ : Set (ℤ × ℤ)) → ℤ) (σ : PhysicalPartition ↥(Λ : Set (ℤ × ℤ))) {n D : ℕ}
    (hcuts : (edgeBoundary Λ ((positiveNear depth σ).map
        (Function.Embedding.subtype _))).card ≤ 20 * n * D ∧
      (edgeBoundary Λ ((positiveNearMiddle depth σ).map
        (Function.Embedding.subtype _))).card ≤ 20 * n * D ∧
      (edgeBoundary Λ ((middle σ).map (Function.Embedding.subtype _))).card ≤ 40 * n * D ∧
      (edgeBoundary Λ ((receiving σ false).map
        (Function.Embedding.subtype _))).card ≤ 16 * n * D ∧
      (edgeBoundary Λ ((receiving σ true).map
        (Function.Embedding.subtype _))).card ≤ 16 * n * D)
    {Q : Finset ↥(Λ : Set (ℤ × ℤ))} (hQ : Q ∈ statusMarginalRegions depth σ) :
    (edgeBoundary Λ (Q.map (Function.Embedding.subtype _))).card ≤ 40 * n * D := by
  classical
  simp only [statusMarginalRegions, Finset.mem_insert, Finset.mem_singleton] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl <;> nlinarith [hcuts.1, hcuts.2.1,
    hcuts.2.2.1, hcuts.2.2.2.1, hcuts.2.2.2.2]

namespace CollarScan

open SimpleGraph

/-- A single coefficient bounds all five actual cut budgets, at every completed
and pre-charge status. The lower bound by one also holds when there are no bands.
The literal scale inequalities are geometric premises; no asymptotic premise,
cut-containment certificate or cut-edge estimate is supplied. -/
theorem exists_statusMarginal_cutBudget_le_log {q : ℕ} (hq : 1 ≤ q) (R : ℕ)
    {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hT : T.Nonempty)
        (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R)),
        S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, (S.anchor i).1 ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Cr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
        1 ≤ B ∧ ∀ (k : ℕ) (h : History S.K S.m S.M k) (g : Fin S.K),
          (k ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state h g),
            cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
              (fun i => (S.anchor i).1) (Q.map (Function.Embedding.subtype _)) ≤ B) ∧
          (k + 1 ≤ S.n * S.m →
            ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState h g),
              cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
                (fun i => (S.anchor i).1) (Q.map (Function.Embedding.subtype _)) ≤ B) := by
  classical
  obtain ⟨C, hC, hbudget⟩ := exists_latticeCutBudget_le_log hq R hCr
    (show (0 : ℝ) ≤ 40 by norm_num)
  refine ⟨C + 1, by positivity, ?_⟩
  intro Λ T _ hT S hgraph hdepth hanchor L hn hradius hr hDpos hD hL hrows hclear
  dsimp only
  have hnR : (2 : ℝ) ≤ S.n := by exact_mod_cast hn
  have hDR : (1 : ℝ) ≤ S.D := by exact_mod_cast hDpos
  set S₀ := (S.truncationSet L).map (Function.Embedding.subtype (· ∈ (Λ : Set (ℤ × ℤ))))
  have hbound (Q : Finset (ℤ × ℤ)) (hQ : Q ⊆ S₀)
      (hcut : (edgeBoundary Λ Q).card ≤ 40 * S.n * S.D) :
      cutBudget q Λ S₀ S.r₀ (fun i => (S.anchor i).1) Q ≤
        (C + 1) * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) := by
    rw [hradius]
    refine (hbudget Λ _ hanchor S₀ Q hQ S.n S.D hnR hDR (by exact_mod_cast hcut)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hboundEither (Q : Finset ↥(Λ : Set (ℤ × ℤ)))
      (hQ : Q ⊆ S.truncationSet L ∨ Qᶜ ⊆ S.truncationSet L)
      (hcut : (edgeBoundary Λ (Q.map (Function.Embedding.subtype _))).card ≤ 40 * S.n * S.D) :
      cutBudget q Λ S₀ S.r₀ (fun i => (S.anchor i).1) (Q.map (Function.Embedding.subtype _)) ≤
        (C + 1) * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) := by
    rcases hQ with hQ | hQ
    · exact hbound _ (Finset.map_subset_map.mpr hQ) hcut
    · have h := hbound _ (Finset.map_subset_map.mpr hQ) (by
        rwa [map_subtype_compl, card_edgeBoundary_sdiff_left (map_subtype_subset Λ Q)])
      rwa [map_subtype_compl, cutBudget_sdiff] at h
  refine ⟨(one_le_cutBudget q Λ S₀ S.r₀ _ ∅).trans
    (hbound ∅ (Finset.empty_subset _) (by simp [edgeBoundary])), ?_⟩
  intro k h g
  constructor
  · intro hk Q hQ
    exact hboundEither Q
      (statusMarginalRegions_containment S.depth (S.state h g)
        (S.state_far_compl_subset_truncationSet h g hL) hQ)
      (statusMarginalRegions_boundary S.depth (S.state h g)
        (state_cut_bounds_domainGraph hT S hgraph hdepth h g (by omega) hk
          hr hDpos hD hL hrows hclear) hQ)
  · intro hk Q hQ
    exact hboundEither Q
      (statusMarginalRegions_containment S.depth (S.oldChargeState h g)
        (S.oldChargeState_far_compl_subset_truncationSet h g hL) hQ)
      (statusMarginalRegions_boundary S.depth (S.oldChargeState h g)
        (oldChargeState_cut_bounds_domainGraph hT S hgraph hdepth h g (by omega) hk
          hr hDpos hD hL hrows hclear) hQ)

end CollarScan

end OpenAI.Scan
