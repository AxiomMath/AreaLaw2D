/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/SupportLocalization.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's
domain encoding: TNLean's `Site Λ` and `domainGraph Λ` are `(Λ : Set (ℤ × ℤ))` and
`(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`; the endpoint set
`Geometry.boundaryEndpoints Λ A` of a cut `A` of the sites is the endpoint set
`OpenAI.cutEndpoints Λ (A.map (Function.Embedding.subtype _))` of the same cut read in
`ℤ²` (both are the endpoints of the lattice edges joining `A` to `Λ \ A`), and the crossing
edge is found by `OpenAI.exists_edgeBoundary_of_walk`.
-/
import OpenAI.Scan.AmbientDepth

/-!
# Localization of scan balls inside the fixed cut

A graph ball of radius `r₀` meeting `A ∩ T_L` lies wholly in `A` when the
ambient target is separated from the physical cut endpoints by more than
`2L + 10r₀`. A path between two points of the ball has length at most `2r₀`;
if it leaves `A`, its first crossing produces an actual cut endpoint of
ambient depth at most `L + 2r₀`, contradicting that separation.

This proves the spatial localization step for actual graph balls. Identifying
a splitting truncated designated support with such a ball is a separate
accepted result, `truncationRadius_eq_of_mem_crossingLabels` in
`OpenAI.CrossingBudget`: its hypothesis requires that the crossed compact set lie
inside the truncation set. This module does not identify an arbitrary
truncated support with the fixed-radius ball used by a charge.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 43–48 and 225–233, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI.Scan

open SimpleGraph

/-- A radius-`r₀` graph ball meeting `A ∩ T_L` cannot leave the fixed cut.
The clearance is stated on the actual ambient endpoints of physical cut edges,
exactly as in `scanner:test-geometry`. Source: `08-scanner.tex`, lines 225–233. -/
theorem domainGraph_ball_subset_of_clearance (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset (Λ : Set (ℤ × ℤ))) (L r₀ : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {anchor : (Λ : Set (ℤ × ℤ))}
    (hmeet : ∃ y ∈ A, ambientDepth T hT y.val ≤ L ∧
      ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist anchor y ≤ (r₀ : ℕ∞)) :
    (Finset.univ.filter fun x ↦
      ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist anchor x ≤ (r₀ : ℕ∞)) ⊆
      A := by
  classical
  set G := (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))
  intro x hx
  obtain ⟨y, hyA, hydepth, hy⟩ := hmeet
  have hxball := (Finset.mem_filter.mp hx).2
  by_contra hxA
  have hyx : G.edist y x ≤ ((2 * r₀ : ℕ) : ℕ∞) := by
    calc
      G.edist y x ≤ G.edist y anchor + G.edist anchor x :=
        SimpleGraph.edist_triangle
      _ ≤ (r₀ : ℕ∞) + r₀ :=
        add_le_add (by simpa only [SimpleGraph.edist_comm] using hy) hxball
      _ = ((2 * r₀ : ℕ) : ℕ∞) := by simp [two_mul]
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top (2 * r₀)) hyx)
  have hyA' : (y : ℤ × ℤ) ∈ A.map (Function.Embedding.subtype _) :=
    (Finset.mem_map' (Function.Embedding.subtype _)).mpr hyA
  have hxA' : (x : ℤ × ℤ) ∉ A.map (Function.Embedding.subtype _) :=
    fun h ↦ hxA ((Finset.mem_map' (Function.Embedding.subtype _)).mp h)
  obtain ⟨u, w, hcut, p', hp'⟩ := exists_edgeBoundary_of_walk p hyA' hxA'
  have hyd : G.edist y u ≤ ((2 * r₀ : ℕ) : ℕ∞) := by
    calc
      G.edist y u ≤ p'.length := SimpleGraph.edist_le _
      _ ≤ p.length := by exact_mod_cast hp'
      _ = G.edist y x := hp
      _ ≤ ((2 * r₀ : ℕ) : ℕ∞) := hyx
  have hvariation := abs_ambientDepth_sub_le_domainGraph T hT hyd
  have hz : u.val ∈ cutEndpoints Λ (A.map (Function.Embedding.subtype _)) :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hcut)
  obtain ⟨t, ht, hmin⟩ := T.exists_mem_eq_inf' hT (ambientSupDistance u.val)
  have hseparate := hclear t ht u.val hz
  have hdeep : ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientDepth T hT u.val := by
    rw [ambientDepth, hmin]
    simpa only [ambientSupDistance, abs_sub_comm] using hseparate
  rw [abs_le] at hvariation
  omega

/-- Under the ambient row assumption, every physical depth row of index in `[1, L]` has at
most `n` sites. Source: `08-scanner.tex`, lines 43–48 and 83–87. -/
theorem depthRow_length_le_of_ambientRows {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    {depth : ↥(Λ : Set (ℤ × ℤ)) → ℤ} (hdepth : depth = fun x ↦ ambientDepth T hT x.val)
    {n L : ℕ}
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    {d : ℤ} (hd : d ∈ Finset.Icc (1 : ℤ) L) :
    (depthRow depth d).length ≤ n := by
  obtain ⟨h1, hL⟩ := Finset.mem_Icc.mp hd
  have hb := depthRow_ambientDepth_length_le_of_row_bound T hT
    (Subtype.val : ↥(Λ : Set (ℤ × ℤ)) → ℤ × ℤ) Subtype.val_injective hrows
    (show 1 ≤ d.toNat by omega) (show d.toNat ≤ L by omega)
  simpa only [← hdepth, Int.toNat_of_nonneg (show 0 ≤ d by omega)] using hb

end OpenAI.Scan
