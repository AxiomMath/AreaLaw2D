import OpenAI.Basic

/-!
# Corollary 1.2 from Theorem 1.1

The counting half of Corollary 1.2 [OAI265, §1.1]: on the square lattice every site has at
most four neighbours, so `|∂_in A| ≤ |∂_Λ A| ≤ 4 |∂_in A|` and `|Z_A| ≤ 2 |∂_Λ A| ≤ 4 |Z_A|`.
The vertex-boundary forms `VertexAreaLaw` then follow from the edge form `AreaLaw` of
Theorem 1.1 with the same constant, made nonnegative, and `AreaLawCorollary` follows from
`AreaLaw` at every range.  Corollary 1.2 itself, `area_law_corollary`, is in
`OpenAI.AreaLaw`, which imports the proof of Theorem 1.1.
-/

namespace OpenAI

open Arealaw
open SimpleGraph

section Counting

variable {Λ A : Finset (ℤ × ℤ)}

/-- A finite set of square-lattice edges has at most four times as many edges as initial
endpoints. -/
theorem card_le_four_mul_card_image_fst {s : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    (hs : ∀ p ∈ s, (hasse ℤ □ hasse ℤ).Adj p.1 p.2) : s.card ≤ 4 * (s.image Prod.fst).card := by
  refine Finset.card_le_mul_card_image s 4 fun x _ => ?_
  refine (Finset.card_le_card_of_injOn Prod.snd (t := (s.image Prod.snd).filter
    ((hasse ℤ □ hasse ℤ).Adj x)) (fun p hp => ?_) (fun p hp p' hp' h => ?_)).trans
    (card_neighbors_le_four x _)
  · rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem _ hp.1, hp.2 ▸ hs p hp.1⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    exact Prod.ext (hp.2.trans hp'.2.symm) h

/-- A finite set of square-lattice edges has at most four times as many edges as final
endpoints. -/
theorem card_le_four_mul_card_image_snd {s : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    (hs : ∀ p ∈ s, (hasse ℤ □ hasse ℤ).Adj p.1 p.2) : s.card ≤ 4 * (s.image Prod.snd).card := by
  have h := card_le_four_mul_card_image_fst (s := s.image Prod.swap)
    fun p hp => by
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hp
      exact (hs p' hp').symm
  rwa [Finset.card_image_of_injective _ Prod.swap_injective, Finset.image_image] at h

/-- `|∂_in A| ≤ |∂_Λ A|` [OAI265, proof of Corollary 1.2]. -/
theorem card_innerBoundary_le : (innerBoundary Λ A).card ≤ (edgeBoundary Λ A).card :=
  Finset.card_image_le

/-- `|∂_Λ A| ≤ 4 |∂_in A|` [OAI265, proof of Corollary 1.2]. -/
theorem card_edgeBoundary_le_four_mul_innerBoundary :
    (edgeBoundary Λ A).card ≤ 4 * (innerBoundary Λ A).card :=
  card_le_four_mul_card_image_fst fun _ hp => (mem_edgeBoundary.1 hp).2.2

/-- `|Z_A| ≤ 2 |∂_Λ A|` [OAI265, proof of Corollary 1.2]. -/
theorem card_cutEndpoints_le : (cutEndpoints Λ A).card ≤ 2 * (edgeBoundary Λ A).card :=
  (Finset.card_union_le _ _).trans (by
    rw [two_mul]; exact add_le_add Finset.card_image_le Finset.card_image_le)

/-- The two sides of the cut are disjoint: initial endpoints lie in `A`, final ones off it. -/
theorem disjoint_image_fst_image_snd_edgeBoundary :
    Disjoint ((edgeBoundary Λ A).image Prod.fst) ((edgeBoundary Λ A).image Prod.snd) := by
  simp only [Finset.disjoint_left, Finset.mem_image]
  rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', h⟩
  exact (Finset.mem_sdiff.1 (mem_edgeBoundary.1 hp').2.1).2 (h ▸ (mem_edgeBoundary.1 hp).1)

/-- `2 |∂_Λ A| ≤ 4 |Z_A|` [OAI265, proof of Corollary 1.2], halved. -/
theorem card_edgeBoundary_le_two_mul_cutEndpoints :
    (edgeBoundary Λ A).card ≤ 2 * (cutEndpoints Λ A).card := by
  have hadj : ∀ p ∈ edgeBoundary Λ A, (hasse ℤ □ hasse ℤ).Adj p.1 p.2 :=
    fun _ hp => (mem_edgeBoundary.1 hp).2.2
  have h₁ := card_le_four_mul_card_image_fst hadj
  have h₂ := card_le_four_mul_card_image_snd hadj
  rw [cutEndpoints, Finset.card_union_of_disjoint disjoint_image_fst_image_snd_edgeBoundary]
  omega

end Counting

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}

/-- The vertex-boundary forms of Corollary 1.2 follow from Theorem 1.1 at the same range
[OAI265, §1.1]. -/
theorem vertexAreaLaw_of_areaLaw (h : AreaLaw 𝕜 q R J Δ) : VertexAreaLaw 𝕜 q R J Δ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA => ?_⟩
  have hS := (hC Λ Φ hΦ Ω hΩ E₀ hE hgap A hA).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg _))
  have h0 : (0 : ℝ) ≤ max C 0 := le_max_right C 0
  have hin : ((edgeBoundary Λ A).card : ℝ) ≤ 4 * (innerBoundary Λ A).card := by
    exact_mod_cast card_edgeBoundary_le_four_mul_innerBoundary
  have hZ : ((edgeBoundary Λ A).card : ℝ) ≤ 2 * (cutEndpoints Λ A).card := by
    exact_mod_cast card_edgeBoundary_le_two_mul_cutEndpoints
  exact ⟨hS, by linarith [mul_le_mul_of_nonneg_left hin h0],
    by linarith [mul_le_mul_of_nonneg_left hZ h0]⟩

/-- **Corollary 1.2** from Theorem 1.1 at every range [OAI265, §1.1]. -/
theorem areaLawCorollary_of_areaLaw (h : ∀ R, AreaLaw 𝕜 q R J Δ) : AreaLawCorollary 𝕜 q J Δ :=
  ⟨h 1, fun R => vertexAreaLaw_of_areaLaw (h R)⟩

end OpenAI
