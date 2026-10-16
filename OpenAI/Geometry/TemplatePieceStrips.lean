/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/Geometry/TemplatePolygons.lean`. Apache 2.0.
-/
import OpenAI.Statements
import Mathlib.Analysis.Convex.Combination

/-!
# Template pieces as intersections of four strips

A template piece (`OpenAI.IsTemplatePiece`), a triangle or rectangle all of whose sides have
slope `0`, `∞`, `1` or `-1`, is the set of points at which the four forms `x`, `y`, `x + y` and
`x - y` each lie in a closed interval [OAI265, Definition 9.3].  The inclusion of the hull in
the strips is convexity; the reverse inclusion writes a point satisfying the supporting bounds
in barycentric coordinates (triangles) or in the coordinates of the two orthogonal sides
(rectangles).

## Main statements

* `OpenAI.IsTemplatePiece.exists_four_strip_bounds`: the eight-bound description.

## Implementation notes

TNLean states these facts for its inductive `TemplatePolygon`; here they are derived directly
from the existential witnesses of `OpenAI.IsTemplatePiece`.
-/

namespace OpenAI

namespace TemplatePieceStrips

private def planeDot (u p : ℝ × ℝ) : ℝ := u.1 * p.1 + u.2 * p.2

private def planeCross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

private theorem slope_perpendicular {u : ℝ × ℝ} (hu : HasTemplateSlope u) :
    HasTemplateSlope (-u.2, u.1) := by
  rcases hu with h | h | h | h <;> simp_all [HasTemplateSlope]

private theorem ratio_nonneg_of_between {x d : ℝ}
    (h : min 0 d ≤ x ∧ x ≤ max 0 d) : 0 ≤ x / d := by
  by_cases hd : 0 ≤ d
  · rw [min_eq_left hd, max_eq_right hd] at h
    exact div_nonneg h.1 hd
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [min_eq_right hd', max_eq_left hd'] at h
    exact div_nonneg_of_nonpos h.2 hd'

/-- The supporting bounds of a set `S` in the allowed normal directions. -/
private def NormalBounds (S : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Prop :=
  ∀ u : ℝ × ℝ, HasTemplateSlope u → ∀ l r : ℝ,
    (∀ q ∈ S, l ≤ planeDot u q ∧ planeDot u q ≤ r) → l ≤ planeDot u p ∧ planeDot u p ≤ r

private theorem side_bounds {S : Set (ℝ × ℝ)} {p a b : ℝ × ℝ} (h : NormalBounds S p)
    (hab : HasTemplateSlope (b - a)) {l r : ℝ}
    (hs : ∀ q ∈ S, l ≤ planeCross (b - a) (q - a) ∧ planeCross (b - a) (q - a) ≤ r) :
    l ≤ planeCross (b - a) (p - a) ∧ planeCross (b - a) (p - a) ≤ r := by
  let u : ℝ × ℝ := (-(b.2 - a.2), b.1 - a.1)
  have hu : HasTemplateSlope u := slope_perpendicular hab
  have hp := h u hu (l + planeDot u a) (r + planeDot u a) (by
    intro q hq
    have hq' := hs q hq
    dsimp [u, planeDot, planeCross] at hq' ⊢
    constructor <;> nlinarith only [hq'.1, hq'.2])
  dsimp [u, planeDot, planeCross] at hp ⊢
  constructor <;> nlinarith only [hp.1, hp.2]

private theorem triangle_mem_of_normalBounds (a b c p : ℝ × ℝ)
    (hd : planeCross (b - a) (c - a) ≠ 0)
    (hab : HasTemplateSlope (b - a)) (hbc : HasTemplateSlope (c - b))
    (hca : HasTemplateSlope (a - c)) (h : NormalBounds {a, b, c} p) :
    p ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  let d := planeCross (b - a) (c - a)
  let α := planeCross (a - c) (p - c) / d
  let β := planeCross (b - a) (p - a) / d
  let γ := planeCross (c - b) (p - b) / d
  have hside (x y : ℝ × ℝ) (hxy : HasTemplateSlope (y - x))
      (hv : ∀ q ∈ ({a, b, c} : Set (ℝ × ℝ)),
        planeCross (y - x) (q - x) = 0 ∨ planeCross (y - x) (q - x) = d) :
      0 ≤ planeCross (y - x) (p - x) / d := by
    apply ratio_nonneg_of_between
    apply side_bounds h hxy
    intro q hq
    rcases hv q hq with hq' | hq'
    · rw [hq']
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    · rw [hq']
      exact ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨hα, hβ, hγ⟩ : 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ := by
    refine ⟨hside c a hca ?_, hside a b hab ?_, hside b c hbc ?_⟩ <;> intro q hq <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq <;>
      rcases hq with rfl | rfl | rfl <;> first
        | (left; simp [planeCross]; done) | (left; dsimp [planeCross]; ring1)
        | (right; dsimp [d, planeCross] <;> ring1)
  have hd' : d ≠ 0 := hd
  have hsum : γ + α + β = 1 := by
    dsimp [α, β, γ]
    field_simp [hd']
    dsimp [d, planeCross]
    ring
  have hpoint : γ • a + α • b + β • c = p := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      α, β, γ]
    all_goals
      field_simp [hd']
      dsimp [d, planeCross]
      ring
  apply mem_convexHull_of_exists_fintype ![γ, α, β] ![a, b, c]
  · intro i
    fin_cases i
    · exact hγ
    · exact hα
    · exact hβ
  · simpa [Fin.sum_univ_succ, add_assoc] using hsum
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_succ, add_assoc] using hpoint

private theorem planeDot_self_pos {u : ℝ × ℝ} (hu : u ≠ 0) : 0 < planeDot u u := by
  by_contra h
  have hle : u.1 * u.1 + u.2 * u.2 ≤ 0 := le_of_not_gt h
  have h₁ : u.1 = 0 := by nlinarith [sq_nonneg u.2, sq_nonneg u.1]
  have h₂ : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  exact hu (Prod.ext h₁ h₂)

private theorem planeCross_ne_zero_of_orthogonal {u v : ℝ × ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : planeDot u v = 0) : planeCross u v ≠ 0 := by
  have hpos := mul_pos (planeDot_self_pos hu) (planeDot_self_pos hv)
  have hid : planeCross u v ^ 2 + planeDot u v ^ 2 = planeDot u u * planeDot v v := by
    dsimp [planeCross, planeDot]
    ring
  intro hzero
  rw [hzero, huv] at hid
  have hz : (0 : ℝ) ^ 2 + 0 ^ 2 = 0 := by norm_num
  rw [hz] at hid
  exact (ne_of_gt hpos) hid.symm

private theorem basis_reconstruct (a u v p : ℝ × ℝ) (hd : planeCross u v ≠ 0) :
    a + (planeCross (p - a) v / planeCross u v) • u +
      (planeCross u (p - a) / planeCross u v) • v = p := by
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  all_goals
    field_simp [hd]
    dsimp [planeCross]
    ring

private theorem rectangle_mem_of_normalBounds (a u v p : ℝ × ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : planeDot u v = 0)
    (hus : HasTemplateSlope u) (hvs : HasTemplateSlope v)
    (h : NormalBounds {a, a + u, a + u + v, a + v} p) :
    p ∈ convexHull ℝ ({a, a + u, a + u + v, a + v} : Set (ℝ × ℝ)) := by
  have hu' := planeDot_self_pos hu
  have hv' := planeDot_self_pos hv
  have hd := planeCross_ne_zero_of_orthogonal hu hv huv
  let α := planeCross (p - a) v / planeCross u v
  let β := planeCross u (p - a) / planeCross u v
  have hp : a + α • u + β • v = p := basis_reconstruct a u v p hd
  have hpu : planeDot u (p - a) = α * planeDot u u := by
    rw [← hp]
    dsimp [planeDot] at huv ⊢
    linear_combination β * huv
  have hpv : planeDot v (p - a) = β * planeDot v v := by
    rw [← hp]
    dsimp [planeDot] at huv ⊢
    linear_combination α * huv
  have hU : 0 ≤ planeDot u (p - a) ∧ planeDot u (p - a) ≤ planeDot u u := by
    have hb := h u hus (planeDot u a) (planeDot u a + planeDot u u) (by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        dsimp [planeDot] at * <;> constructor <;> nlinarith only [hu', huv])
    dsimp [planeDot] at hb ⊢
    constructor <;> nlinarith only [hb.1, hb.2]
  have hV : 0 ≤ planeDot v (p - a) ∧ planeDot v (p - a) ≤ planeDot v v := by
    have hb := h v hvs (planeDot v a) (planeDot v a + planeDot v v) (by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        dsimp [planeDot] at * <;> constructor <;> nlinarith only [hv', huv])
    dsimp [planeDot] at hb ⊢
    constructor <;> nlinarith only [hb.1, hb.2]
  rw [hpu] at hU
  rw [hpv] at hV
  have hα₀ : 0 ≤ α := (mul_le_mul_iff_of_pos_right hu').mp (by simpa using hU.1)
  have hα₁ : α ≤ 1 := (mul_le_mul_iff_of_pos_right hu').mp (by simpa using hU.2)
  have hβ₀ : 0 ≤ β := (mul_le_mul_iff_of_pos_right hv').mp (by simpa using hV.1)
  have hβ₁ : β ≤ 1 := (mul_le_mul_iff_of_pos_right hv').mp (by simpa using hV.2)
  have hαc : 0 ≤ 1 - α := sub_nonneg.mpr hα₁
  have hβc : 0 ≤ 1 - β := sub_nonneg.mpr hβ₁
  have hpoint : ((1 - α) * (1 - β)) • a + (α * (1 - β)) • (a + u) +
      (α * β) • (a + u + v) + ((1 - α) * β) • (a + v) = p := by
    rw [← hp]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> ring
  apply mem_convexHull_of_exists_fintype
    ![(1 - α) * (1 - β), α * (1 - β), α * β, (1 - α) * β]
    ![a, a + u, a + u + v, a + v]
  · intro i
    fin_cases i
    · exact mul_nonneg hαc hβc
    · exact mul_nonneg hα₀ hβc
    · exact mul_nonneg hα₀ hβ₀
    · exact mul_nonneg hαc hβ₀
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp
    ring
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_succ, add_assoc] using hpoint

/-- A template piece is the convex hull of a finite nonempty vertex set and contains every
point satisfying the vertices' supporting bounds in the allowed normal directions. -/
private theorem exists_vertices {P : Set (ℝ × ℝ)} (hP : IsTemplatePiece P) :
    ∃ V : Set (ℝ × ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V ∧
      ∀ p, NormalBounds V p → p ∈ P := by
  rcases hP with ⟨a, u, v, hu, hv, huv, hus, hvs, rfl⟩ | ⟨a, b, c, hd, hab, hbc, hca, rfl⟩
  · exact ⟨_, Set.toFinite _, Set.insert_nonempty _ _, rfl,
      fun p h => rectangle_mem_of_normalBounds a u v p hu hv huv hus hvs h⟩
  · exact ⟨_, Set.toFinite _, Set.insert_nonempty _ _, rfl,
      fun p h => triangle_mem_of_normalBounds a b c p hd hab hbc hca h⟩

private theorem finite_form_bounds {S : Set (ℝ × ℝ)} (hs : S.Finite) (hne : S.Nonempty)
    (f : (ℝ × ℝ) → ℝ) : ∃ l r : ℝ,
      (∃ a ∈ S, f a = l) ∧ (∃ b ∈ S, f b = r) ∧ ∀ q ∈ S, l ≤ f q ∧ f q ≤ r := by
  classical
  let V := hs.toFinset.image f
  have hV : V.Nonempty := (hs.toFinset_nonempty.mpr hne).image f
  refine ⟨V.min' hV, V.max' hV, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp (Finset.min'_mem V hV)
    exact ⟨a, hs.mem_toFinset.mp ha, hfa⟩
  · obtain ⟨b, hb, hfb⟩ := Finset.mem_image.mp (Finset.max'_mem V hV)
    exact ⟨b, hs.mem_toFinset.mp hb, hfb⟩
  · intro q hq
    have hq' : f q ∈ V := Finset.mem_image.mpr ⟨q, hs.mem_toFinset.mpr hq, rfl⟩
    exact ⟨Finset.min'_le _ _ hq', Finset.le_max' _ _ hq'⟩

private theorem scaled_between {a b x c l r : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : l ≤ c * a ∧ c * a ≤ r) (hb : l ≤ c * b ∧ c * b ≤ r) :
    l ≤ c * x ∧ c * x ≤ r := by
  by_cases hc : 0 ≤ c
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hx.1 hc),
      (mul_le_mul_of_nonneg_left hx.2 hc).trans hb.2⟩
  · have hc' : c ≤ 0 := le_of_not_ge hc
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hx.2 hc'),
      (mul_le_mul_of_nonpos_left hx.1 hc').trans ha.2⟩

end TemplatePieceStrips

open TemplatePieceStrips in
/-- A template piece is cut out by eight bounds on the four forms `x`, `y`, `x + y` and
`x - y` [OAI265, Definition 9.3]. -/
theorem IsTemplatePiece.exists_four_strip_bounds {P : Set (ℝ × ℝ)} (hP : IsTemplatePiece P) :
    ∃ lx ux ly uy ls us ld ud : ℝ, ∀ p : ℝ × ℝ,
      p ∈ P ↔ (lx ≤ p.1 ∧ p.1 ≤ ux) ∧ (ly ≤ p.2 ∧ p.2 ≤ uy) ∧
        (ls ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ us) ∧ (ld ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ ud) := by
  obtain ⟨V, hf, hn, hPV, hmem⟩ := exists_vertices hP
  obtain ⟨lx, ux, hlx, hux, hx⟩ := finite_form_bounds hf hn (fun q ↦ q.1)
  obtain ⟨ly, uy, hly, huy, hy⟩ := finite_form_bounds hf hn (fun q ↦ q.2)
  obtain ⟨ls, us, hls, hus, hs⟩ := finite_form_bounds hf hn (fun q ↦ q.1 + q.2)
  obtain ⟨ld, ud, hld, hud, hd⟩ := finite_form_bounds hf hn (fun q ↦ q.1 - q.2)
  refine ⟨lx, ux, ly, uy, ls, us, ld, ud, fun p ↦ ?_⟩
  have hhull : ∀ (f : (ℝ × ℝ) → ℝ) (l r : ℝ), (∀ q ∈ V, l ≤ f q ∧ f q ≤ r) →
      (∃ c₁ c₂ : ℝ, ∀ q, f q = c₁ * q.1 + c₂ * q.2) → p ∈ P → l ≤ f p ∧ f p ≤ r := by
    rintro f l r hv ⟨c₁, c₂, hfc⟩ hp
    let g : (ℝ × ℝ) →ₗ[ℝ] ℝ := c₁ • LinearMap.fst ℝ ℝ ℝ + c₂ • LinearMap.snd ℝ ℝ ℝ
    have hc : Convex ℝ {q : ℝ × ℝ | l ≤ f q ∧ f q ≤ r} := by
      have : {q : ℝ × ℝ | l ≤ f q ∧ f q ≤ r} = g ⁻¹' Set.Icc l r := by
        ext q
        simp [g, hfc]
      rw [this]
      exact (convex_Icc l r).linear_preimage g
    rw [hPV] at hp
    exact convexHull_min hv hc hp
  constructor
  · intro hp
    exact ⟨hhull _ lx ux hx ⟨1, 0, fun q => by ring⟩ hp,
      hhull _ ly uy hy ⟨0, 1, fun q => by ring⟩ hp,
      hhull _ ls us hs ⟨1, 1, fun q => by ring⟩ hp,
      hhull _ ld ud hd ⟨1, -1, fun q => by ring⟩ hp⟩
  · rintro ⟨hpx, hpy, hps, hpd⟩
    apply hmem
    intro u hu l r hv
    have transfer (f : (ℝ × ℝ) → ℝ) (lo hi : ℝ)
        (hlo : ∃ a ∈ V, f a = lo) (hhi : ∃ b ∈ V, f b = hi)
        (hfp : lo ≤ f p ∧ f p ≤ hi) (c : ℝ)
        (hfc : ∀ q ∈ V, l ≤ c * f q ∧ c * f q ≤ r) :
        l ≤ c * f p ∧ c * f p ≤ r := by
      obtain ⟨a, ha, hfa⟩ := hlo
      obtain ⟨b, hb, hfb⟩ := hhi
      have ha' := hfc a ha
      have hb' := hfc b hb
      rw [hfa] at ha'
      rw [hfb] at hb'
      exact scaled_between hfp ha' hb'
    have hform : ∀ (f : (ℝ × ℝ) → ℝ) (c : ℝ), (∀ q, planeDot u q = c * f q) →
        ∀ lo hi, (∃ a ∈ V, f a = lo) → (∃ b ∈ V, f b = hi) → lo ≤ f p ∧ f p ≤ hi →
          l ≤ planeDot u p ∧ planeDot u p ≤ r := by
      intro f c hfc lo hi hlo hhi hfp
      rw [hfc]
      exact transfer f lo hi hlo hhi hfp c (fun q hq => by rw [← hfc]; exact hv q hq)
    rcases hu with hu | hu | hu | hu
    · exact hform (fun q ↦ q.1) u.1 (fun q => by simp only [planeDot, hu]; ring)
        lx ux hlx hux hpx
    · exact hform (fun q ↦ q.2) u.2 (fun q => by simp only [planeDot, hu]; ring)
        ly uy hly huy hpy
    · exact hform (fun q ↦ q.1 + q.2) u.1 (fun q => by simp only [planeDot, hu]; ring)
        ls us hls hus hps
    · exact hform (fun q ↦ q.1 - q.2) u.1 (fun q => by simp only [planeDot, hu]; ring)
        ld ud hld hud hpd

end OpenAI
