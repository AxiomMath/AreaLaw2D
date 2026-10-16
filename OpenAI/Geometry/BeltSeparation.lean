import OpenAI.Geometry.Octants
import OpenAI.Geometry.InitialSectorColors
import OpenAI.Geometry.InitialRegionInteriors
import OpenAI.Geometry.InitialRegionRegularity
import OpenAI.Geometry.BeltRunInterfaces
import OpenAI.Geometry.DummyRunInterfaces

/-!
# Birth-template separation for initial belt tiles

Lemma 11.5 of [OAI265, §11, `geometry:birth-separation`, lines 562–660] for initial belt runs:
the closed birth region of a belt run in a fine cell of side `t` is at sup distance at least
`r₀ / 2` from every point of another non-dummy initial region of the same color that keeps
distance at least `r₀` from the nine marks of the cell, for every `r₀ ≤ t / 4096`.

Two points of the two regions closer than `r₀ / 2` are handled in three cases.  Points of two
runs of the same cell are separated by the angular gap at the cell center, since distinct
same-color runs never occupy consecutive fan triangles.  Points near a mark lie in its octant
star of radius `t / 64`, where distinct same-color identifiers occupy non-adjacent octants and
the angular gap applies.  Otherwise the segment between the two points crosses the boundary of
the cell in the interior of one elementary side, away from its endpoints: the crossing point
lies in the fan triangle of that side, the points just beyond it lie in the closed square of the
side's opponent and hence in a single initial region, and that region shares the whole side with
the belt run, so the two colors are opposite (`initialRegionColor_ne_of_segment_subset_inter`).

## Main statements

* `max_dist_le_two_mul_dist_of_mem_cellFanPolygon`: the angular gap between fan triangles with
  no common vertex on the boundary.
* `mem_cellFanPolygon_of_dist_lt`, `mem_cellFanPolygon_of_dist_lt_of_mem_base`: clearance of a
  fan triangle near the boundary of its cell.
* `ball_diff_closure_subset_closure_of_mem_segment`: the square beyond an elementary side.
* `half_le_dist_of_mem_initialBirthRegion_beltRun`: the separation.

## Implementation notes

This replaces the paper's compactness argument over finitely many quarter-mesh patterns by
explicit clearance with constant `1 / 2`.  A fan triangle is handled through the closed octants
about the cell center that make it up (`cellFanOctantSlot`): one octant for half a side, two for
a whole side.
-/

noncomputable section

namespace OpenAI.Geometry

/-! ### Octants of a cell fan -/

/-- The slot of a cell fan whose triangle contains octant `k` about the cell center. -/
def cellFanOctantSlot (split : Fin 4 → Bool) (k : Fin 8) : CellFanSlot split :=
  ⟨⟨(k.val + 1) % 8 / 2, by omega⟩,
    if h : split ⟨(k.val + 1) % 8 / 2, by omega⟩ then ⟨(k.val + 1) % 2, by simp [h]; omega⟩
    else ⟨0, by simp [h]⟩⟩

/-- The tangent parameter of the first endpoint of an elementary side. -/
private def slotLower (split : Fin 4 → Bool) (s : CellFanSlot split) : ℝ :=
  if split s.1 then (s.2.val : ℝ) - 1 else -1

/-- The tangent parameter of the last endpoint of an elementary side. -/
private def slotUpper (split : Fin 4 → Bool) (s : CellFanSlot split) : ℝ :=
  if split s.1 then (s.2.val : ℝ) else 1

private theorem slot_ext {split : Fin 4 → Bool} {s s' : CellFanSlot split}
    (h₁ : s.1 = s'.1) (h₂ : s.2.val = s'.2.val) : s = s' := by
  rcases s with ⟨a, j⟩
  rcases s' with ⟨a', j'⟩
  dsimp only at h₁ h₂
  subst h₁
  exact Sigma.ext rfl (heq_of_eq (Fin.ext h₂))

private theorem slotLower_lt_slotUpper (split : Fin 4 → Bool) (s : CellFanSlot split) :
    -1 ≤ slotLower split s ∧ slotLower split s < slotUpper split s ∧
      slotUpper split s ≤ 1 := by
  rcases s with ⟨side, j⟩
  have hj := j.isLt
  have h0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  unfold slotLower slotUpper
  dsimp only
  split_ifs with hs
  · have hj2 : j.val < 2 := by simpa [hs] using hj
    have h1 : (j.val : ℝ) ≤ 1 := by exact_mod_cast (by omega : j.val ≤ 1)
    exact ⟨by linarith, by linarith, h1⟩
  · norm_num

private theorem sideVector_lineMap (side : Fin 4) (u w θ : ℝ) :
    cellFanSideVector side u + θ • (cellFanSideVector side w - cellFanSideVector side u) =
      cellFanSideVector side (u + θ * (w - u)) := by
  fin_cases side <;> apply Prod.ext <;> simp [cellFanSideVector] <;> ring

private theorem octantRay_eq_sideVector (split : Fin 4 → Bool) (k : Fin 8) :
    (∃ w, slotLower split (cellFanOctantSlot split k) ≤ w ∧
        w ≤ slotUpper split (cellFanOctantSlot split k) ∧
        octantRay k = cellFanSideVector (cellFanOctantSlot split k).1 w) ∧
      ∃ w, slotLower split (cellFanOctantSlot split k) ≤ w ∧
        w ≤ slotUpper split (cellFanOctantSlot split k) ∧
        octantRay (k + 1) = cellFanSideVector (cellFanOctantSlot split k).1 w := by
  refine ⟨⟨if k.val % 2 = 1 then -1 else 0, ?_⟩, ⟨if k.val % 2 = 1 then 0 else 1, ?_⟩⟩ <;>
  fin_cases k <;> simp only [cellFanOctantSlot, slotLower, slotUpper] <;> split_ifs <;>
    simp_all [octantRay, cellFanSideVector]

private theorem octantRay_succ_eq_of_ne (split : Fin 4 → Bool) (k : Fin 8)
    (h : cellFanOctantSlot split (k + 1) ≠ cellFanOctantSlot split k) :
    octantRay (k + 1) = cellFanSideVector (cellFanOctantSlot split k).1
        (slotUpper split (cellFanOctantSlot split k)) ∧
      octantRay (k + 1) = cellFanSideVector (cellFanOctantSlot split (k + 1)).1
        (slotLower split (cellFanOctantSlot split (k + 1))) := by
  cases h0 : split 0 <;> cases h1 : split 1 <;> cases h2 : split 2 <;> cases h3 : split 3 <;>
  fin_cases k <;> simp_all [cellFanOctantSlot, slotLower, slotUpper, octantRay, cellFanSideVector]

private theorem cellFanOctantSlot_fst (split : Fin 4 → Bool) (k : Fin 8) :
    (cellFanOctantSlot split k).1 = ⟨(k.val + 1) % 8 / 2, by omega⟩ := rfl

private theorem cellFanOctantSlot_snd_val (split : Fin 4 → Bool) (k : Fin 8) :
    ((cellFanOctantSlot split k).2 : ℕ) =
      if split ⟨(k.val + 1) % 8 / 2, by omega⟩ then (k.val + 1) % 2 else 0 := by
  by_cases h : split ⟨(k.val + 1) % 8 / 2, by omega⟩ = true <;> simp [cellFanOctantSlot, h]

/-- The octant before the midpoint ray of a side. -/
private def lowOctant (side : Fin 4) : Fin 8 := ⟨(2 * side.val + 7) % 8, by omega⟩

/-- The octant after the midpoint ray of a side. -/
private def highOctant (side : Fin 4) : Fin 8 := ⟨2 * side.val, by omega⟩

private theorem smul_sideVector_mem_lowOctant (side : Fin 4) {μ w : ℝ} (hμ : 0 ≤ μ)
    (hw₁ : -1 ≤ w) (hw₀ : w ≤ 0) : μ • cellFanSideVector side w ∈ octantCone (lowOctant side) := by
  fin_cases side <;>
    simp [lowOctant, octantCone, cellFanSideVector] <;> constructor <;> nlinarith

private theorem smul_sideVector_mem_highOctant (side : Fin 4) {μ w : ℝ} (hμ : 0 ≤ μ)
    (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) : μ • cellFanSideVector side w ∈ octantCone (highOctant side) := by
  fin_cases side <;>
    simp [highOctant, octantCone, cellFanSideVector] <;> constructor <;> nlinarith

private theorem cellFanOctantSlot_lowOctant (split : Fin 4 → Bool) (s : CellFanSlot split)
    (hs : (s.2 : ℕ) = 0) : cellFanOctantSlot split (lowOctant s.1) = s := by
  have hside : (⟨((lowOctant s.1).val + 1) % 8 / 2, by omega⟩ : Fin 4) = s.1 := by
    apply Fin.ext; simp only [lowOctant]; omega
  apply slot_ext
  · rw [cellFanOctantSlot_fst]; exact hside
  · rw [cellFanOctantSlot_snd_val, hside, hs]
    split_ifs
    · simp only [lowOctant]; omega
    · rfl

private theorem cellFanOctantSlot_highOctant (split : Fin 4 → Bool) (s : CellFanSlot split)
    (hs : (s.2 : ℕ) = if split s.1 then 1 else 0) :
    cellFanOctantSlot split (highOctant s.1) = s := by
  have hside : (⟨((highOctant s.1).val + 1) % 8 / 2, by omega⟩ : Fin 4) = s.1 := by
    apply Fin.ext; simp only [highOctant]; omega
  apply slot_ext
  · rw [cellFanOctantSlot_fst]; exact hside
  · rw [cellFanOctantSlot_snd_val, hside, hs]
    split_ifs <;> simp [highOctant]

private theorem exists_octant_of_sideVector (split : Fin 4 → Bool) (s : CellFanSlot split)
    {μ w : ℝ} (hμ : 0 ≤ μ) (hlo : slotLower split s ≤ w) (hhi : w ≤ slotUpper split s) :
    ∃ k, cellFanOctantSlot split k = s ∧ μ • cellFanSideVector s.1 w ∈ octantCone k := by
  obtain ⟨h₁, _, h₂⟩ := slotLower_lt_slotUpper split s
  have hj := s.2.isLt
  unfold slotLower at hlo
  unfold slotUpper at hhi
  by_cases hs : split s.1 = true
  · simp only [hs, if_true] at hlo hhi hj
    have hj' : (s.2 : ℕ) = 0 ∨ (s.2 : ℕ) = 1 := by omega
    rcases hj' with hj' | hj'
    · rw [hj'] at hlo hhi
      exact ⟨lowOctant s.1, cellFanOctantSlot_lowOctant split s hj',
        smul_sideVector_mem_lowOctant s.1 hμ (by simpa using hlo) (by simpa using hhi)⟩
    · rw [hj'] at hlo hhi
      exact ⟨highOctant s.1, cellFanOctantSlot_highOctant split s (by simp [hs, hj']),
        smul_sideVector_mem_highOctant s.1 hμ (by simpa using hlo) (by simpa using hhi)⟩
  · simp only [hs] at hlo hhi hj
    have hj' : (s.2 : ℕ) = 0 := by simpa using hj
    by_cases hw : w ≤ 0
    · exact ⟨lowOctant s.1, cellFanOctantSlot_lowOctant split s hj',
        smul_sideVector_mem_lowOctant s.1 hμ hlo hw⟩
    · exact ⟨highOctant s.1, cellFanOctantSlot_highOctant split s (by simp [hs, hj']),
        smul_sideVector_mem_highOctant s.1 hμ (by linarith) hhi⟩

private theorem cellFanStart_eq_slotLower (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    cellFanStart o ℓ z split s = cellFanCenter o ℓ z +
      ((2 : ℝ) ^ ℓ / 2) • cellFanSideVector s.1 (slotLower split s) :=
  cellFanStart_eq o ℓ z split s

private theorem cellFanEnd_eq_slotUpper (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    cellFanEnd o ℓ z split s = cellFanCenter o ℓ z +
      ((2 : ℝ) ^ ℓ / 2) • cellFanSideVector s.1 (slotUpper split s) :=
  cellFanEnd_eq o ℓ z split s

private theorem cellFanPolygon_region_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    (cellFanPolygon o ℓ z split s).region = convexHull ℝ {cellFanCenter o ℓ z,
      cellFanStart o ℓ z split s, cellFanEnd o ℓ z split s} := rfl

private theorem sidePoint_mem_cellFanPolygon (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) {w : ℝ}
    (hlo : slotLower split s ≤ w) (hhi : w ≤ slotUpper split s) :
    cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • cellFanSideVector s.1 w ∈
      (cellFanPolygon o ℓ z split s).region := by
  obtain ⟨_, hlt, _⟩ := slotLower_lt_slotUpper split s
  have hseg : cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • cellFanSideVector s.1 w ∈
      segment ℝ (cellFanStart o ℓ z split s) (cellFanEnd o ℓ z split s) := by
    rw [segment_eq_image']
    set θ := (w - slotLower split s) / (slotUpper split s - slotLower split s) with hθdef
    have hpos : 0 < slotUpper split s - slotLower split s := by linarith
    refine ⟨θ, ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩, ?_⟩
    have hθ : slotLower split s + θ * (slotUpper split s - slotLower split s) = w := by
      rw [hθdef, div_mul_cancel₀ _ hpos.ne']; ring
    dsimp only
    rw [cellFanStart_eq_slotLower, cellFanEnd_eq_slotUpper, ← hθ, ← sideVector_lineMap]
    module
  rw [cellFanPolygon_region_eq]
  exact segment_subset_convexHull (by simp) (by simp) hseg

/-- Every point of a fan triangle lies in the closed octant, about the cell center, of one of
the octants that make up the triangle. -/
theorem exists_octant_of_mem_cellFanPolygon (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) {x : ℝ × ℝ}
    (hx : x ∈ (cellFanPolygon o ℓ z split s).region) :
    ∃ k, cellFanOctantSlot split k = s ∧ x ∈ octantConeAt (cellFanCenter o ℓ z) k := by
  rw [cellFanPolygon_region_eq, ← convexJoin_singleton_segment, mem_convexJoin] at hx
  obtain ⟨a, ha, e, he, hxe⟩ := hx
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rw [segment_eq_image'] at he hxe
  obtain ⟨θ, hθ, rfl⟩ := he
  obtain ⟨μ, hμ, rfl⟩ := hxe
  have hd : (0 : ℝ) ≤ (2 : ℝ) ^ ℓ / 2 := by positivity
  obtain ⟨h₁, hlt, h₂⟩ := slotLower_lt_slotUpper split s
  obtain ⟨k, hk, hmem⟩ := exists_octant_of_sideVector split s (μ := μ * ((2 : ℝ) ^ ℓ / 2))
    (w := slotLower split s + θ * (slotUpper split s - slotLower split s))
    (mul_nonneg hμ.1 hd) (by nlinarith [hθ.1]) (by nlinarith [hθ.2])
  refine ⟨k, hk, ?_⟩
  simp only [octantConeAt, Set.mem_ofPred_eq]
  convert hmem using 1
  rw [cellFanStart_eq_slotLower, cellFanEnd_eq_slotUpper, ← sideVector_lineMap]
  module

/-- The octant triangle of radius the half-side about the cell center lies in the fan triangle
of its slot. -/
theorem mem_cellFanPolygon_of_mem_octantTriangle (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (k : Fin 8) {x : ℝ × ℝ}
    (hx : x ∈ octantTriangle (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) k) :
    x ∈ (cellFanPolygon o ℓ z split (cellFanOctantSlot split k)).region := by
  rw [octantTriangle_eq_convexHull _ (by positivity)] at hx
  have hconv : Convex ℝ (cellFanPolygon o ℓ z split (cellFanOctantSlot split k)).region := by
    rw [cellFanPolygon_region_eq]; exact convex_convexHull ℝ _
  refine convexHull_min ?_ hconv hx
  intro p hp
  rcases hp with rfl | rfl | rfl
  · rw [cellFanPolygon_region_eq]; exact subset_convexHull ℝ _ (Or.inl rfl)
  · obtain ⟨w, h₁, h₂, h₃⟩ := (octantRay_eq_sideVector split k).1
    rw [h₃]; exact sidePoint_mem_cellFanPolygon o ℓ z split _ h₁ h₂
  · obtain ⟨w, h₁, h₂, h₃⟩ := (octantRay_eq_sideVector split k).2
    rw [h₃]
    exact sidePoint_mem_cellFanPolygon o ℓ z split _ h₁ h₂

/-- The ray between two octants of distinct slots leaves the cell at the common endpoint of
their elementary sides. -/
theorem cellFanCenter_add_octantRay_succ_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (k : Fin 8)
    (h : cellFanOctantSlot split (k + 1) ≠ cellFanOctantSlot split k) :
    cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • octantRay (k + 1) =
        cellFanEnd o ℓ z split (cellFanOctantSlot split k) ∧
      cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • octantRay (k + 1) =
        cellFanStart o ℓ z split (cellFanOctantSlot split (k + 1)) := by
  obtain ⟨h₁, h₂⟩ := octantRay_succ_eq_of_ne split k h
  exact ⟨by rw [cellFanEnd_eq_slotUpper, ← h₁], by rw [cellFanStart_eq_slotLower, ← h₂]⟩

/-- The eight points where the octant rays about the cell center leave the cell are marks of
the cell. -/
theorem cellFanCenter_add_octantRay_mem_beltCellMarks (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (k : Fin 8) :
    cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • octantRay k ∈ beltCellMarks o ℓ z := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (sub_add_cancel k 1).symm⟩
  have hne : cellFanOctantSlot (fun _ ↦ true) (j + 1) ≠ cellFanOctantSlot (fun _ ↦ true) j := by
    intro h
    have h' := congrArg (fun s : CellFanSlot (fun _ : Fin 4 ↦ true) ↦ (s.2 : ℕ)) h
    simp only [cellFanOctantSlot_snd_val, if_true] at h'
    fin_cases j <;> simp at h'
  rw [(cellFanCenter_add_octantRay_succ_eq o ℓ z _ j hne).1]
  exact ((cellFan_vertices_mem_beltCellMarks o ℓ z _).2 _).2

/-- A fan triangle lies in the closed cell, the closed ball of the half-side about the center. -/
theorem cellFanPolygon_subset_closedBall (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    (cellFanPolygon o ℓ z split s).region ⊆
      Metric.closedBall (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) := by
  intro x hx
  rw [closedBall_cellFanCenter_eq_closure_dyadicCell, ← cellFanPolygons_cover o ℓ z split]
  exact Set.mem_iUnion.mpr ⟨s, hx⟩

/-- A point of a fan triangle at the half-side distance from the center lies on its base. -/
theorem mem_segment_of_mem_cellFanPolygon (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) {x : ℝ × ℝ}
    (hx : x ∈ (cellFanPolygon o ℓ z split s).region)
    (hxc : (2 : ℝ) ^ ℓ / 2 ≤ dist x (cellFanCenter o ℓ z)) :
    x ∈ segment ℝ (cellFanStart o ℓ z split s) (cellFanEnd o ℓ z split s) := by
  rw [cellFanPolygon_region_eq, ← convexJoin_singleton_segment, mem_convexJoin] at hx
  obtain ⟨a, ha, e, he, hxe⟩ := hx
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hen := norm_sub_cellFanCenter_of_mem_base o ℓ z split s he
  rw [segment_eq_image'] at hxe
  obtain ⟨μ, hμ, rfl⟩ := hxe
  have hd : (0 : ℝ) < (2 : ℝ) ^ ℓ / 2 := by positivity
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1,
    hen] at hxc
  have hμ1 : μ = 1 := le_antisymm hμ.2 (by nlinarith)
  subst hμ1
  simpa using he

/-- **Clearance at the base, from inside.**  A point on the boundary of the cell, far from the
eight octant marks, near a point of a fan triangle, lies in the same triangle. -/
theorem mem_cellFanPolygon_of_dist_lt (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) {u v : ℝ × ℝ} {d' : ℝ}
    (hu : u ∈ (cellFanPolygon o ℓ z split s).region)
    (hv : v ∈ Metric.closedBall (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2))
    (hvc : (2 : ℝ) ^ ℓ / 2 ≤ dist v (cellFanCenter o ℓ z))
    (hd' : 0 ≤ d') (hd'd : d' ≤ (2 : ℝ) ^ ℓ / 2)
    (hfar : ∀ k, d' ≤ dist v (cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • octantRay k))
    (huv : dist u v < d' / 2) :
    v ∈ (cellFanPolygon o ℓ z split s).region := by
  obtain ⟨k₁, hk₁, hu₁⟩ := exists_octant_of_mem_cellFanPolygon o ℓ z split s hu
  have huB := cellFanPolygon_subset_closedBall o ℓ z split s hu
  obtain ⟨k₂, hv₂⟩ : ∃ k, v ∈ octantTriangle (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) k := by
    rw [← iUnion_octantTriangle] at hv
    exact Set.mem_iUnion.mp hv
  by_cases hs : cellFanOctantSlot split k₂ = s
  · rw [← hs]
    exact mem_cellFanPolygon_of_mem_octantTriangle o ℓ z split k₂ hv₂
  exfalso
  have hne : k₂ ≠ k₁ := fun h ↦ hs (h ▸ hk₁)
  by_cases h₁ : k₂ = k₁ + 1
  · subst h₁
    have := half_le_dist_of_mem_octantTriangle_succ hd' hd'd ⟨hu₁, huB⟩ hv₂.1 hvc (hfar _)
    linarith
  by_cases h₂ : k₁ = k₂ + 1
  · subst h₂
    have := half_le_dist_of_mem_octantTriangle_pred hd' hd'd ⟨hu₁, huB⟩ hv₂.1 hvc (hfar _)
    linarith
  have := max_dist_le_two_mul_dist_of_not_adjacent hne h₁ h₂ hu₁ hv₂.1
  have := le_max_right (dist u (cellFanCenter o ℓ z)) (dist v (cellFanCenter o ℓ z))
  linarith

/-- **Clearance at the base, from outside.**  A point of the closed cell near a point of the base
of a fan triangle, far from the endpoints of that base, lies in the triangle. -/
theorem mem_cellFanPolygon_of_dist_lt_of_mem_base (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) {u v : ℝ × ℝ} {d' : ℝ}
    (hv : v ∈ (cellFanPolygon o ℓ z split s).region)
    (hvc : (2 : ℝ) ^ ℓ / 2 ≤ dist v (cellFanCenter o ℓ z))
    (hu : u ∈ Metric.closedBall (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2))
    (hd' : 0 ≤ d') (hd'd : d' ≤ (2 : ℝ) ^ ℓ / 2)
    (hvs : d' ≤ dist v (cellFanStart o ℓ z split s))
    (hve : d' ≤ dist v (cellFanEnd o ℓ z split s))
    (huv : dist u v < d' / 2) :
    u ∈ (cellFanPolygon o ℓ z split s).region := by
  obtain ⟨k₂, hk₂, hv₂⟩ := exists_octant_of_mem_cellFanPolygon o ℓ z split s hv
  obtain ⟨k₁, hu₁⟩ : ∃ k, u ∈ octantTriangle (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) k := by
    rw [← iUnion_octantTriangle] at hu
    exact Set.mem_iUnion.mp hu
  by_cases hs : cellFanOctantSlot split k₁ = s
  · rw [← hs]
    exact mem_cellFanPolygon_of_mem_octantTriangle o ℓ z split k₁ hu₁
  exfalso
  have hne : k₂ ≠ k₁ := fun h ↦ hs (h ▸ hk₂)
  by_cases h₁ : k₁ = k₂ + 1
  · subst h₁
    have hray := (cellFanCenter_add_octantRay_succ_eq o ℓ z split k₂ (by rw [hk₂]; exact hs)).1
    rw [hk₂] at hray
    have := half_le_dist_of_mem_octantTriangle_pred hd' hd'd hu₁ hv₂ hvc (hray ▸ hve)
    linarith
  by_cases h₂ : k₂ = k₁ + 1
  · subst h₂
    have hray := (cellFanCenter_add_octantRay_succ_eq o ℓ z split k₁
      (by rw [hk₂]; exact fun h ↦ hs h.symm)).2
    rw [hk₂] at hray
    have := half_le_dist_of_mem_octantTriangle_succ hd' hd'd hu₁ hv₂ hvc (hray ▸ hvs)
    linarith
  have := max_dist_le_two_mul_dist_of_not_adjacent hne h₂ h₁ hu₁.1 hv₂
  have := le_max_right (dist u (cellFanCenter o ℓ z)) (dist v (cellFanCenter o ℓ z))
  linarith

/-- **Angular gap between fan triangles.**  Points of two distinct fan triangles whose
elementary sides share no endpoint are at distance at least half the larger of their distances
to the cell center. -/
theorem max_dist_le_two_mul_dist_of_mem_cellFanPolygon (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) {s s' : CellFanSlot split} (hne : s ≠ s')
    (hadj : ¬ (cellFanEnd o ℓ z split s = cellFanStart o ℓ z split s' ∨
      cellFanEnd o ℓ z split s' = cellFanStart o ℓ z split s))
    {x y : ℝ × ℝ} (hx : x ∈ (cellFanPolygon o ℓ z split s).region)
    (hy : y ∈ (cellFanPolygon o ℓ z split s').region) :
    max (dist x (cellFanCenter o ℓ z)) (dist y (cellFanCenter o ℓ z)) ≤ 2 * dist x y := by
  obtain ⟨k, hk, hxk⟩ := exists_octant_of_mem_cellFanPolygon o ℓ z split s hx
  obtain ⟨j, hj, hyj⟩ := exists_octant_of_mem_cellFanPolygon o ℓ z split s' hy
  refine max_dist_le_two_mul_dist_of_not_adjacent ?_ ?_ ?_ hxk hyj
  · rintro rfl; exact hne (hk.symm.trans hj)
  · rintro rfl
    have hray := cellFanCenter_add_octantRay_succ_eq o ℓ z split k
      (by rw [hk, hj]; exact fun h ↦ hne h.symm)
    rw [hk, hj] at hray
    exact hadj (Or.inl (hray.1.symm.trans hray.2))
  · rintro rfl
    have hray := cellFanCenter_add_octantRay_succ_eq o ℓ z split j
      (by rw [hk, hj]; exact hne)
    rw [hk, hj] at hray
    exact hadj (Or.inr (hray.1.symm.trans hray.2))

/-! ### Squares on the far side of an elementary side -/

/-- One-dimensional form of the outward-square argument, for the top side of the first
square: a square `[α₁, β₁] × [α₂, β₂]` with interior disjoint from `[A₁, B₁] × [A₂, B₂]`,
containing the point `(p, B₂)` of the top side and with no corner on the top side near `p`,
contains every point near `(p, B₂)` above the top side. -/
private theorem rect_core {A₁ B₁ A₂ B₂ α₁ β₁ α₂ β₂ m M p ρ : ℝ}
    (hz : B₁ - A₁ = B₂ - A₂) (hQ : α₁ < β₁) (hQsq : β₁ - α₁ = β₂ - α₂) (hρ : 0 < ρ)
    (hm : A₁ ≤ m) (hM : M ≤ B₁) (hpm : m + 2 * ρ ≤ p) (hpM : p + 2 * ρ ≤ M)
    (hpQ : α₁ ≤ p ∧ p ≤ β₁ ∧ α₂ ≤ B₂ ∧ B₂ ≤ β₂)
    (hdisj : ∀ u v, A₁ < u → u < B₁ → A₂ < v → v < B₂ → α₁ < u → u < β₁ → α₂ < v →
      v < β₂ → False)
    (hcorner : ∀ e, (e = α₁ ∨ e = β₁) → α₂ = B₂ → m ≤ e → e ≤ M → e ≤ m ∨ M ≤ e)
    {u v : ℝ} (hu : |u - p| < ρ) (hv : |v - B₂| < ρ)
    (hout : ¬ (A₁ ≤ u ∧ u ≤ B₁ ∧ A₂ ≤ v ∧ v ≤ B₂)) :
    α₁ ≤ u ∧ u ≤ β₁ ∧ α₂ ≤ v ∧ v ≤ β₂ := by
  obtain ⟨hu₁, hu₂⟩ := abs_lt.mp hu
  obtain ⟨hv₁, hv₂⟩ := abs_lt.mp hv
  obtain ⟨hpα, hpβ, hα₂B, hBβ₂⟩ := hpQ
  have hvB : B₂ < v := by
    by_contra hle
    exact hout ⟨by linarith, by linarith, by linarith, not_lt.mp hle⟩
  have hα₂ : α₂ = B₂ := by
    by_contra hne
    have hlt : α₂ < B₂ := lt_of_le_of_ne hα₂B hne
    obtain ⟨u₀, hu₀, hu₀'⟩ : ∃ u₀, max α₁ (p - ρ) < u₀ ∧ u₀ < min β₁ (p + ρ) :=
      exists_between (by
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨hQ, by linarith⟩, by linarith, by linarith⟩)
    obtain ⟨v₀, hv₀, hv₀'⟩ : ∃ v₀, max α₂ (B₂ - ρ) < v₀ ∧ v₀ < B₂ :=
      exists_between (by rw [max_lt_iff]; exact ⟨hlt, by linarith⟩)
    rw [max_lt_iff] at hu₀ hv₀
    rw [lt_min_iff] at hu₀'
    exact hdisj u₀ v₀ (by linarith) (by linarith) (by linarith) hv₀' hu₀.1 hu₀'.1 hv₀.1
      (by linarith)
  have hα₁ : α₁ ≤ p - ρ := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    rcases hcorner α₁ (Or.inl rfl) hα₂ (by linarith) (by linarith) with h | h <;> linarith
  have hβ₁ : p + ρ ≤ β₁ := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    rcases hcorner β₁ (Or.inr rfl) hα₂ (by linarith) (by linarith) with h | h <;> linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem uIcc_margin {a b p ρ : ℝ} (hp : p ∈ Set.uIcc a b) (ha : 2 * ρ ≤ |p - a|)
    (hb : 2 * ρ ≤ |p - b|) : min a b + 2 * ρ ≤ p ∧ p + 2 * ρ ≤ max a b := by
  rw [Set.mem_uIcc] at hp
  rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [abs_of_nonneg (by linarith)] at ha
    rw [abs_of_nonpos (by linarith)] at hb
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> linarith
  · rw [abs_of_nonneg (by linarith)] at hb
    rw [abs_of_nonpos (by linarith)] at ha
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> linarith

private theorem mem_uIcc_of_min_le {a b e : ℝ} (h₁ : min a b ≤ e) (h₂ : e ≤ max a b) :
    e ∈ Set.uIcc a b := by
  rw [Set.mem_uIcc]
  rcases le_total a b with h | h
  · rw [min_eq_left h] at h₁; rw [max_eq_right h] at h₂; exact Or.inl ⟨h₁, h₂⟩
  · rw [min_eq_right h] at h₁; rw [max_eq_left h] at h₂; exact Or.inr ⟨h₁, h₂⟩

private theorem segment_eq_of_snd_eq {a b : ℝ × ℝ} (hab : a.2 = b.2) :
    segment ℝ a b = (fun x : ℝ ↦ (x, a.2)) '' Set.uIcc a.1 b.1 := by
  rw [← segment_eq_uIcc, Prod.image_mk_segment_left]
  congr 1
  exact Prod.ext rfl hab.symm

private theorem segment_eq_of_fst_eq {a b : ℝ × ℝ} (hab : a.1 = b.1) :
    segment ℝ a b = (fun y : ℝ ↦ (a.1, y)) '' Set.uIcc a.2 b.2 := by
  rw [← segment_eq_uIcc, Prod.image_mk_segment_right]
  congr 1
  exact Prod.ext hab.symm rfl

private theorem le_min_or_max_le_of_eq {a b e : ℝ} (h : e = a ∨ e = b) :
    e ≤ min a b ∨ max a b ≤ e := by
  rcases h with h | h <;> rw [h]
  · rcases le_total a b with h' | h'
    · left; rw [min_eq_left h']
    · right; rw [max_eq_left h']
  · rcases le_total a b with h' | h'
    · right; rw [max_eq_right h']
    · left; rw [min_eq_right h']

/-- A corner on a vertical elementary side near no endpoint is impossible: the corner condition
in the coordinate along the side. -/
private theorem corner_vertical {a b : ℝ × ℝ} (hab : a.1 = b.1) {e₁ e : ℝ} (he₁ : e₁ = a.1)
    (h : (e₁, e) ∈ segment ℝ a b → (e₁, e) = a ∨ (e₁, e) = b)
    (he : min a.2 b.2 ≤ e) (he' : e ≤ max a.2 b.2) : e ≤ min a.2 b.2 ∨ max a.2 b.2 ≤ e := by
  apply le_min_or_max_le_of_eq
  have hmem : (e₁, e) ∈ segment ℝ a b := by
    rw [segment_eq_of_fst_eq hab]
    exact ⟨e, mem_uIcc_of_min_le he he', by rw [he₁]⟩
  rcases h hmem with h | h
  · exact Or.inl (congrArg Prod.snd h)
  · exact Or.inr (congrArg Prod.snd h)

/-- The corner condition along a horizontal elementary side. -/
private theorem corner_horizontal {a b : ℝ × ℝ} (hab : a.2 = b.2) {e₂ e : ℝ} (he₂ : e₂ = a.2)
    (h : (e, e₂) ∈ segment ℝ a b → (e, e₂) = a ∨ (e, e₂) = b)
    (he : min a.1 b.1 ≤ e) (he' : e ≤ max a.1 b.1) : e ≤ min a.1 b.1 ∨ max a.1 b.1 ≤ e := by
  apply le_min_or_max_le_of_eq
  have hmem : (e, e₂) ∈ segment ℝ a b := by
    rw [segment_eq_of_snd_eq hab]
    exact ⟨e, mem_uIcc_of_min_le he he', by rw [he₂]⟩
  rcases h hmem with h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)

/-- **Outward square.**  Let a dyadic square `Q` with interior disjoint from a cell contain a
point `p` of an elementary side of the cell, at distance at least `2 ρ` from both endpoints,
and let every corner of `Q` on that side be an endpoint.  Then the points near `p` outside the
closed cell lie in the closed square `Q`. -/
theorem ball_diff_closure_subset_closure_of_mem_segment (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split)
    (hd : Disjoint (dyadicCell o ℓ z) (dyadicCell o j w)) {p : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hp : p ∈ segment ℝ (cellFanStart o ℓ z split s) (cellFanEnd o ℓ z split s))
    (hpQ : p ∈ closure (dyadicCell o j w))
    (hpa : 2 * ρ ≤ dist p (cellFanStart o ℓ z split s))
    (hpb : 2 * ρ ≤ dist p (cellFanEnd o ℓ z split s))
    (hcorner : ∀ ε, dyadicCellCorner o j w ε ∈
        segment ℝ (cellFanStart o ℓ z split s) (cellFanEnd o ℓ z split s) →
      dyadicCellCorner o j w ε = cellFanStart o ℓ z split s ∨
        dyadicCellCorner o j w ε = cellFanEnd o ℓ z split s) :
    Metric.ball p ρ \ closure (dyadicCell o ℓ z) ⊆ closure (dyadicCell o j w) := by
  obtain ⟨-, hgeo⟩ := cellFan_elementary_geometry o ℓ z split s
  have haZ := beltCellMarks_subset_closure_dyadicCell o ℓ z
    ((cellFan_vertices_mem_beltCellMarks o ℓ z split).2 s).1
  have hbZ := beltCellMarks_subset_closure_dyadicCell o ℓ z
    ((cellFan_vertices_mem_beltCellMarks o ℓ z split).2 s).2
  set a := cellFanStart o ℓ z split s with ha_def
  set b := cellFanEnd o ℓ z split s with hb_def
  have hℓ : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hj : (0 : ℝ) < 2 ^ j := by positivity
  set A₁ := o.1 + (2 : ℝ) ^ ℓ * z.1 with hA₁
  set B₁ := o.1 + (2 : ℝ) ^ ℓ * (z.1 + 1) with hB₁
  set A₂ := o.2 + (2 : ℝ) ^ ℓ * z.2 with hA₂
  set B₂ := o.2 + (2 : ℝ) ^ ℓ * (z.2 + 1) with hB₂
  set α₁ := o.1 + (2 : ℝ) ^ j * w.1 with hα₁
  set β₁ := o.1 + (2 : ℝ) ^ j * (w.1 + 1) with hβ₁
  set α₂ := o.2 + (2 : ℝ) ^ j * w.2 with hα₂
  set β₂ := o.2 + (2 : ℝ) ^ j * (w.2 + 1) with hβ₂
  have hz₁ : B₁ - A₁ = 2 ^ ℓ := by rw [hA₁, hB₁]; ring
  have hz₂ : B₂ - A₂ = 2 ^ ℓ := by rw [hA₂, hB₂]; ring
  have hQ₁ : β₁ - α₁ = 2 ^ j := by rw [hα₁, hβ₁]; ring
  have hQ₂ : β₂ - α₂ = 2 ^ j := by rw [hα₂, hβ₂]; ring
  have hcorner' : ∀ e₁ e₂, (e₁ = α₁ ∨ e₁ = β₁) → (e₂ = α₂ ∨ e₂ = β₂) →
      (e₁, e₂) ∈ segment ℝ a b → (e₁, e₂) = a ∨ (e₁, e₂) = b := by
    rintro e₁ e₂ h₁ h₂ hseg
    have hc : ∃ ε, dyadicCellCorner o j w ε = (e₁, e₂) := by
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact ⟨(0, 0), by simp [dyadicCellCorner, hα₁, hα₂]⟩
      · exact ⟨(0, 1), by simp [dyadicCellCorner, hα₁, hβ₂]⟩
      · exact ⟨(1, 0), by simp [dyadicCellCorner, hβ₁, hα₂]⟩
      · exact ⟨(1, 1), by simp [dyadicCellCorner, hβ₁, hβ₂]⟩
    obtain ⟨ε, hε⟩ := hc
    rw [← hε] at hseg ⊢
    exact hcorner ε hseg
  have hdisj : ∀ u v, A₁ < u → u < B₁ → A₂ < v → v < B₂ → α₁ < u → u < β₁ → α₂ < v →
      v < β₂ → False := by
    intro u v h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    exact Set.disjoint_left.mp hd (show (u, v) ∈ dyadicCell o ℓ z from
      ⟨⟨h₁.le, h₂⟩, ⟨h₃.le, h₄⟩⟩) (show (u, v) ∈ dyadicCell o j w from ⟨⟨h₅.le, h₆⟩, ⟨h₇.le, h₈⟩⟩)
  rw [closure_dyadicCell] at haZ hbZ hpQ
  simp only [Set.mem_prod, Set.mem_Icc] at haZ hbZ hpQ
  rintro q ⟨hqball, hqout⟩
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hqball
  rw [closure_dyadicCell] at hqout ⊢
  simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hqout
  simp only [Set.mem_prod, Set.mem_Icc]
  have hc₀₀ : (dyadicCellCorner o ℓ z (0, 0)).1 = A₁ ∧ (dyadicCellCorner o ℓ z (0, 0)).2 = A₂ := by
    simp [dyadicCellCorner, hA₁, hA₂]
  have hc₁₁ : (dyadicCellCorner o ℓ z (1, 1)).1 = B₁ ∧ (dyadicCellCorner o ℓ z (1, 1)).2 = B₂ := by
    simp [dyadicCellCorner, hB₁, hB₂]
  rw [hc₀₀.1, hc₀₀.2, hc₁₁.1, hc₁₁.2] at hgeo
  rcases hgeo with ⟨hab, hside⟩ | ⟨hab, hside⟩
  · -- a vertical side
    rw [segment_eq_of_fst_eq hab] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    simp only at hpa hpb hpQ hqball
    have hda : dist (a.1, y) a = |y - a.2| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
      exact max_eq_right (abs_nonneg _)
    have hdb : dist (a.1, y) b = |y - b.2| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hab, sub_self, abs_zero]
      exact max_eq_right (abs_nonneg _)
    obtain ⟨hm, hM⟩ := uIcc_margin hy (hda ▸ hpa) (hdb ▸ hpb)
    have hmA : A₂ ≤ min a.2 b.2 := le_min haZ.2.1 hbZ.2.1
    have hMB : max a.2 b.2 ≤ B₂ := max_le haZ.2.2 hbZ.2.2
    rcases hside with hL | hR
    · -- the left side
      have h := rect_core (A₁ := A₂) (B₁ := B₂) (A₂ := -B₁) (B₂ := -A₁) (α₁ := α₂) (β₁ := β₂)
        (α₂ := -β₁) (β₂ := -α₁) (m := min a.2 b.2) (M := max a.2 b.2) (p := y) (ρ := ρ)
        (u := q.2) (v := -q.1) (by linarith) (by linarith) (by linarith) hρ hmA hMB hm hM
        ⟨hpQ.2.1, hpQ.2.2, by linarith [hpQ.1.2], by linarith [hpQ.1.1]⟩
        (fun u v h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ↦ hdisj (-v) u (by linarith) (by linarith) h₁ h₂
          (by linarith) (by linarith) h₅ h₆)
        (fun e he hβ h₁ h₂ ↦ corner_vertical hab (e₁ := β₁) (by linarith)
          (hcorner' β₁ e (Or.inr rfl) (he.imp id id)) h₁ h₂)
        hqball.2 (by have := abs_lt.mp hqball.1; rw [abs_lt]; constructor <;> linarith)
        (by intro h; rcases hqout with (h' | h') | h' | h' <;> linarith)
      exact ⟨⟨by linarith, by linarith⟩, h.1, h.2.1⟩
    · -- the right side
      have h := rect_core (A₁ := A₂) (B₁ := B₂) (A₂ := A₁) (B₂ := B₁) (α₁ := α₂) (β₁ := β₂)
        (α₂ := α₁) (β₂ := β₁) (m := min a.2 b.2) (M := max a.2 b.2) (p := y) (ρ := ρ)
        (u := q.2) (v := q.1) (by linarith) (by linarith) (by linarith) hρ hmA hMB hm hM
        ⟨hpQ.2.1, hpQ.2.2, by linarith [hpQ.1.1], by linarith [hpQ.1.2]⟩
        (fun u v h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ↦ hdisj v u h₃ h₄ h₁ h₂ h₇ h₈ h₅ h₆)
        (fun e he hα h₁ h₂ ↦ corner_vertical hab (e₁ := α₁) (by linarith)
          (hcorner' α₁ e (Or.inl rfl) (he.imp id id)) h₁ h₂)
        hqball.2 (by rw [← hR]; exact hqball.1)
        (by intro h; rcases hqout with (h' | h') | h' | h' <;> linarith)
      exact ⟨⟨h.2.2.1, h.2.2.2⟩, h.1, h.2.1⟩
  · -- a horizontal side
    rw [segment_eq_of_snd_eq hab] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    simp only at hpa hpb hpQ hqball
    have hda : dist (x, a.2) a = |x - a.1| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
      exact max_eq_left (abs_nonneg _)
    have hdb : dist (x, a.2) b = |x - b.1| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hab, sub_self, abs_zero]
      exact max_eq_left (abs_nonneg _)
    obtain ⟨hm, hM⟩ := uIcc_margin hx (hda ▸ hpa) (hdb ▸ hpb)
    have hmA : A₁ ≤ min a.1 b.1 := le_min haZ.1.1 hbZ.1.1
    have hMB : max a.1 b.1 ≤ B₁ := max_le haZ.1.2 hbZ.1.2
    rcases hside with hL | hR
    · -- the bottom side
      have h := rect_core (A₁ := A₁) (B₁ := B₁) (A₂ := -B₂) (B₂ := -A₂) (α₁ := α₁) (β₁ := β₁)
        (α₂ := -β₂) (β₂ := -α₂) (m := min a.1 b.1) (M := max a.1 b.1) (p := x) (ρ := ρ)
        (u := q.1) (v := -q.2) (by linarith) (by linarith) (by linarith) hρ hmA hMB hm hM
        ⟨hpQ.1.1, hpQ.1.2, by linarith [hpQ.2.2], by linarith [hpQ.2.1]⟩
        (fun u v h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ↦ hdisj u (-v) h₁ h₂ (by linarith) (by linarith)
          h₅ h₆ (by linarith) (by linarith))
        (fun e he hβ h₁ h₂ ↦ corner_horizontal hab (e₂ := β₂) (by linarith)
          (hcorner' e β₂ he (Or.inr rfl)) h₁ h₂)
        hqball.1 (by have := abs_lt.mp hqball.2; rw [abs_lt]; constructor <;> linarith)
        (by intro h; rcases hqout with (h' | h') | h' | h' <;> linarith)
      exact ⟨⟨h.1, h.2.1⟩, by linarith, by linarith⟩
    · -- the top side
      have h := rect_core (A₁ := A₁) (B₁ := B₁) (A₂ := A₂) (B₂ := B₂) (α₁ := α₁) (β₁ := β₁)
        (α₂ := α₂) (β₂ := β₂) (m := min a.1 b.1) (M := max a.1 b.1) (p := x) (ρ := ρ)
        (u := q.1) (v := q.2) (by linarith) (by linarith) (by linarith) hρ hmA hMB hm hM
        ⟨hpQ.1.1, hpQ.1.2, by linarith [hpQ.2.1], by linarith [hpQ.2.2]⟩
        hdisj
        (fun e he hα h₁ h₂ ↦ corner_horizontal hab (e₂ := α₂) (by linarith)
          (hcorner' e α₂ he (Or.inl rfl)) h₁ h₂)
        hqball.1 (by rw [← hR]; exact hqball.2)
        (by intro h; rcases hqout with (h' | h') | h' | h' <;> linarith)
      exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩

/-! ### Initial regions meeting a belt cell -/

/-- A nonempty open set covered by finitely many closed sets meets the interior of one of
them. -/
private theorem exists_inter_interior_nonempty_of_subset_iUnion {X ι : Type*}
    [TopologicalSpace X] [Finite ι] {F : ι → Set X} (hF : ∀ i, IsClosed (F i)) {V : Set X}
    (hV : IsOpen V) (hne : V.Nonempty) (hcov : V ⊆ ⋃ i, F i) :
    ∃ i, (V ∩ interior (F i)).Nonempty := by
  classical
  cases nonempty_fintype ι
  suffices h : ∀ S : Finset ι, ∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ⋃ i ∈ S, F i →
      ∃ i, (V ∩ interior (F i)).Nonempty from
    h Finset.univ V hV hne (by simpa using hcov)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro V _ hne hcov
    obtain ⟨x, hx⟩ := hne
    simpa using hcov hx
  | insert a S _ ih =>
    intro V hV hne hcov
    by_cases hsub : V ⊆ F a
    · exact ⟨a, by rwa [Set.inter_eq_left.mpr (interior_maximal hsub hV)]⟩
    · obtain ⟨x, hxV, hxa⟩ := Set.not_subset.mp hsub
      obtain ⟨i, hi⟩ := ih (V \ F a) (hV.sdiff (hF a)) ⟨x, hxV, hxa⟩ (by
        intro y hy
        have := hcov hy.1
        simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Set.mem_union] at this
        rcases this with h | h
        · exact absurd h hy.2
        · exact h)
      exact ⟨i, hi.mono (Set.inter_subset_inter_left _ Set.sdiff_subset)⟩

/-- A fan triangle of a belt run lies in its closed birth region. -/
theorem cellFanPolygon_subset_initialBirthRegion (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (hk₀ : k₀ ≤ k) (z : ℤ × ℤ)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    {s : CellFanSlot (fineLayerSplitMask o k₀ k Z C z)} (hs : s ∈ R.supp) :
    (cellFanPolygon o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s).region ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, R⟩)) :=
  fun _ hx ↦ Set.mem_iUnion₂.mpr ⟨s, hs, hx⟩

/-- An initial identifier other than the runs of a belt cell has open region disjoint from the
open cell. -/
theorem initialOpenRegion_inter_interior_closure_eq_empty (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (hk₀ : k₀ ≤ k) (z : ℤ × ℤ)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (i : InitialRegionIndex o k₀ Z C a b hC h₀)
    (hi : ∀ R, i ≠ .inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, R⟩)) :
    initialOpenRegion o k₀ Z C a b hC h₀ i ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z)) = ∅ := by
  by_contra hne
  have hcov := (cellFanPolygons_cover o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)).symm.subset
  obtain ⟨s, hs⟩ := exists_inter_interior_nonempty_of_subset_iUnion
    (fun s ↦ (TemplatePolygon.isCompact_region _).isClosed)
    (isOpen_interior.inter isOpen_interior) (Set.nonempty_iff_ne_empty.mpr hne)
    ((Set.inter_subset_right.trans interior_subset).trans hcov)
  obtain ⟨q, ⟨hqi, -⟩, hqs⟩ := hs
  let R := (cellFanRunGraph o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz)).connectedComponentMk s
  have hsR : s ∈ R.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hqR : q ∈ initialOpenRegion o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, R⟩)) :=
    interior_mono (cellFanPolygon_subset_initialBirthRegion o k₀ Z C a b hC h₀ k hk₀ z hz R
      hsR) hqs
  by_cases hiR : i = .inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, R⟩)
  · exact hi R hiR
  · exact Set.disjoint_left.mp (initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀ hiR)
      hqi hqR
/-- **Birth-template separation**, initial belt runs [OAI265, `geometry:birth-separation`].  A
point of the birth region of a belt run of the fine cell `z` of layer `k`, of side
`t = 2 ^ fineScaleIndex k`, and a point of another non-dummy initial birth region of the same
color at distance at least `r₀` from every mark of the cell are at distance at least `r₀ / 2`,
for every `0 < r₀ ≤ t / 4096`. -/
theorem half_le_dist_of_mem_initialBirthRegion_beltRun (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hZ : Z.Nonempty)
    (k : ℕ) (hk₀ : k₀ ≤ k) (z : ℤ × ℤ)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (Rr : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (i : InitialRegionIndex o k₀ Z C a b hC h₀)
    (hi : i ≠ .inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, Rr⟩)) (hdummy : i ≠ .inl ())
    (hcolor : initialRegionColor o k₀ Z C a b hC h₀ i =
      initialRegionColor o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, Rr⟩)))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ (2 : ℝ) ^ fineScaleIndex k / 4096)
    {x y : ℝ × ℝ}
    (hx : x ∈ initialBirthRegion o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, Rr⟩)))
    (hy : y ∈ initialBirthRegion o k₀ Z C a b hC h₀ i)
    (hyv : ∀ v ∈ beltCellMarks o (fineScaleIndex k) z, r₀ ≤ dist y v) :
    r₀ / 2 ≤ dist x y := by
  classical
  by_contra hlt
  have hxy : dist x y < r₀ / 2 := not_le.mp hlt
  have ht : (0 : ℝ) < 2 ^ fineScaleIndex k := by positivity
  have hk : 50000000 ≤ k := h₀.trans hk₀
  have hzf : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C := Finset.mem_of_mem_filter z hz
  have hcm := (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)).1
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
  -- another run of the same cell: the angular gap at the cell center
  by_cases hrun : ∃ Q, i = .inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, Q⟩)
  · obtain ⟨Q, rfl⟩ := hrun
    obtain ⟨s', hs', hys⟩ := Set.mem_iUnion₂.mp hy
    have hQR : Q ≠ Rr := fun h ↦ hi (by rw [h])
    have hsR := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hs
    have hsQ := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hs'
    have hss' : s ≠ s' := by
      rintro rfl
      exact hQR (hsQ.symm.trans hsR)
    have hfam : beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz s' =
        beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz s := by
      rw [← initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k z hk₀ hz Q s' hs',
        ← initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k z hk₀ hz Rr s hs]
      exact hcolor
    have hadj : ¬ (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s =
          cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s' ∨
        cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s' =
          cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s) :=
      fun hadj ↦ cellFanRun_adjacent_colors_ne o (fineScaleIndex k) z _ _ s s' hadj
        (by rw [hsR, hsQ]; exact hQR.symm) hfam.symm
    have hgap := max_dist_le_two_mul_dist_of_mem_cellFanPolygon o (fineScaleIndex k) z _
      hss' hadj hxs hys
    have := hyv _ hcm
    have := le_max_right (dist x (cellFanCenter o (fineScaleIndex k) z))
      (dist y (cellFanCenter o (fineScaleIndex k) z))
    linarith
  -- both points near a mark: the angular gap in the octant star of the mark
  by_cases hstar : ∃ v ∈ beltCellMarks o (fineScaleIndex k) z,
      dist x v ≤ (2 : ℝ) ^ fineScaleIndex k / 128
  · obtain ⟨v, hv, hxv⟩ := hstar
    let σ := initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hzf hv
    have hdecomp (j : InitialRegionIndex o k₀ Z C a b hC h₀) :
        initialBirthRegion o k₀ Z C a b hC h₀ j ∩
            Metric.closedBall v ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) =
          ⋃ s : {s : CellFanSlot (fun _ : Fin 4 ↦ true) // σ s = j},
            (cellFanPolygon (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
              v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
              (fun _ ↦ true) s.val).region :=
      (Classical.choose_spec (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hzf hv)).1.2 j
    have hr := fineScaleIndex_closed_half_radius_eq k hk
    have hxB : x ∈ Metric.closedBall v ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) := by
      rw [Metric.mem_closedBall]; linarith
    have hyB : y ∈ Metric.closedBall v ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) := by
      rw [Metric.mem_closedBall]
      have := dist_triangle y x v
      rw [dist_comm y x] at this
      linarith
    obtain ⟨⟨t₁, ht₁⟩, hxt⟩ := Set.mem_iUnion.mp ((Set.ext_iff.mp (hdecomp _) x).mp ⟨hx, hxB⟩)
    obtain ⟨⟨t₂, ht₂⟩, hyt⟩ := Set.mem_iUnion.mp ((Set.ext_iff.mp (hdecomp i) y).mp ⟨hy, hyB⟩)
    have hne : t₁ ≠ t₂ := by
      rintro rfl
      exact hi (ht₂.symm.trans ht₁)
    have hadj : ¬ (cellFanEnd (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
            v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
            (fun _ ↦ true) t₁ =
          cellFanStart (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
            v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
            (fun _ ↦ true) t₂ ∨
        cellFanEnd (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
            v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
            (fun _ ↦ true) t₂ =
          cellFanStart (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
            v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
            (fun _ ↦ true) t₁) := by
      intro hadj
      have hiff := initialRegion_sector_assignment_adjacent_colors_eq_iff o k₀ Z C a b hC h₀
        k z v hk₀ hzf hv t₁ t₂ hadj
      have hσ : σ t₁ = σ t₂ := hiff.mp (by
        change initialRegionColor o k₀ Z C a b hC h₀ (σ t₁) =
          initialRegionColor o k₀ Z C a b hC h₀ (σ t₂)
        rw [ht₁, ht₂]
        exact hcolor.symm)
      exact hi (ht₂.symm.trans (hσ.symm.trans ht₁))
    have hcen : cellFanCenter (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
        v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0) = v := by
      apply Prod.ext <;> simp [cellFanCenter]
    have hgap := max_dist_le_two_mul_dist_of_mem_cellFanPolygon _ _ _ _ hne hadj hxt hyt
    rw [hcen] at hgap
    have := hyv v hv
    have := le_max_right (dist x v) (dist y v)
    linarith
  -- otherwise the two points straddle an elementary side
  have hfarx : ∀ v ∈ beltCellMarks o (fineScaleIndex k) z,
      (2 : ℝ) ^ fineScaleIndex k / 128 < dist x v :=
    fun v hv ↦ not_le.mp fun h ↦ hstar ⟨v, hv, h⟩
  have hint := initialOpenRegion_inter_interior_closure_eq_empty o k₀ Z C a b hC h₀ k hk₀ z hz
    i (fun R h ↦ hrun ⟨R, h⟩)
  have hZc := closedBall_cellFanCenter_eq_closure_dyadicCell o (fineScaleIndex k) z
  rw [← hZc, interior_closedBall _ (by positivity)] at hint
  have hreg := initialBirthRegion_eq_closure_initialOpenRegion o k₀ Z C a b hC h₀ i
  have hRz : ∀ q ∈ initialBirthRegion o k₀ Z C a b hC h₀ i,
      q ∉ Metric.ball (cellFanCenter o (fineScaleIndex k) z) ((2 : ℝ) ^ fineScaleIndex k / 2) := by
    intro q hq hqb
    rw [hreg] at hq
    obtain ⟨q', hq'b, hq'i⟩ := mem_closure_iff.mp hq _ Metric.isOpen_ball hqb
    exact (Set.eq_empty_iff_forall_notMem.mp hint) q' ⟨hq'i, hq'b⟩
  have hxZ := cellFanPolygon_subset_closedBall o (fineScaleIndex k) z _ s hxs
  obtain ⟨p, hpseg, hpB, hpball⟩ : ∃ p ∈ segment ℝ x y,
      p ∈ Metric.closedBall (cellFanCenter o (fineScaleIndex k) z)
        ((2 : ℝ) ^ fineScaleIndex k / 2) ∧
      p ∉ Metric.ball (cellFanCenter o (fineScaleIndex k) z) ((2 : ℝ) ^ fineScaleIndex k / 2) := by
    by_cases hxb : x ∈ Metric.ball (cellFanCenter o (fineScaleIndex k) z)
        ((2 : ℝ) ^ fineScaleIndex k / 2)
    · by_contra hnone
      have hsub : segment ℝ x y ⊆ Metric.ball (cellFanCenter o (fineScaleIndex k) z)
          ((2 : ℝ) ^ fineScaleIndex k / 2) ∪ (Metric.closedBall (cellFanCenter o
            (fineScaleIndex k) z) ((2 : ℝ) ^ fineScaleIndex k / 2))ᶜ := by
        intro q hq
        by_cases hqB : q ∈ Metric.closedBall (cellFanCenter o (fineScaleIndex k) z)
            ((2 : ℝ) ^ fineScaleIndex k / 2)
        · exact Or.inl (by_contra fun h ↦ hnone ⟨q, hq, hqB, h⟩)
        · exact Or.inr hqB
      have := (convex_segment x y).isPreconnected.subset_left_of_subset_union
        Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl
        (Set.disjoint_left.mpr fun q hq hq' ↦ hq' (Metric.ball_subset_closedBall hq)) hsub
        ⟨x, left_mem_segment ℝ x y, hxb⟩
      exact hRz y hy (this (right_mem_segment ℝ x y))
    · exact ⟨x, left_mem_segment ℝ x y, hxZ, hxb⟩
  have hpc : (2 : ℝ) ^ fineScaleIndex k / 2 ≤ dist p (cellFanCenter o (fineScaleIndex k) z) := by
    rw [Metric.mem_ball, not_lt] at hpball; exact hpball
  have hsum := dist_add_dist_of_mem_segment hpseg
  have hxp : dist x p < r₀ / 2 := by linarith [dist_nonneg (x := p) (y := y)]
  have hpy : dist p y < r₀ / 2 := by linarith [dist_nonneg (x := x) (y := p)]
  have hpm : ∀ m ∈ beltCellMarks o (fineScaleIndex k) z,
      (2 : ℝ) ^ fineScaleIndex k / 256 ≤ dist p m := by
    intro m hm
    have h₁ := hfarx m hm
    have h₂ := dist_triangle x p m
    linarith
  have hpT := mem_cellFanPolygon_of_dist_lt o (fineScaleIndex k) z _ s
    (d' := (2 : ℝ) ^ fineScaleIndex k / 256) hxs hpB hpc (by positivity) (by linarith)
    (fun j ↦ hpm _ (cellFanCenter_add_octantRay_mem_beltCellMarks o (fineScaleIndex k) z j))
    (by linarith)
  have hpe := mem_segment_of_mem_cellFanPolygon o (fineScaleIndex k) z _ s hpT hpc
  have hmarks := (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)).2 s
  have hps := hpm _ hmarks.1
  have hpe' := hpm _ hmarks.2
  have hρ : (0 : ℝ) < 2 ^ fineScaleIndex k / 1024 := by positivity
  have hab := (cellFan_elementary_geometry o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z) s).1
  -- the region on the far side of the elementary side
  obtain ⟨i', hH, hseg'⟩ : ∃ i' : InitialRegionIndex o k₀ Z C a b hC h₀,
      Metric.ball p ((2 : ℝ) ^ fineScaleIndex k / 1024) \
          closure (dyadicCell o (fineScaleIndex k) z) ⊆
        initialBirthRegion o k₀ Z C a b hC h₀ i' ∧
      segment ℝ (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s)
          (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s) ⊆
        initialBirthRegion o k₀ Z C a b hC h₀ i' := by
    rcases exists_elementarySide_opponent o k₀ k Z C z s hC hk hk₀ hzf with
      hN | ⟨kw, hkw₀, w, hw, hne, hsub⟩
    · have hpN := hN hpe
      rw [dyadicNeighborhood, Finset.closure_biUnion] at hpN
      obtain ⟨w, hw, hpw⟩ := Set.mem_iUnion₂.mp hpN
      have hcellsub : dyadicCell o k₀ w ⊆ dyadicNeighborhood o k₀ Z C :=
        fun q hq ↦ Set.mem_iUnion₂.mpr ⟨w, hw, hq⟩
      have href := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
        (fineScaleIndex k) Z C z (fineScaleIndex_le k) hzf
      have hd := (dyadicNeighborhood_disjoint_later_layer o Z C k₀ k hk₀).symm.mono
        href hcellsub
      refine ⟨.inl (), ?_, hN⟩
      exact (ball_diff_closure_subset_closure_of_mem_segment o (fineScaleIndex k) k₀ z w _ s
        hd hρ hpe hpw (by linarith) (by linarith) (fun ε hε ↦
          dyadicNeighborhood_corner_on_elementarySide o k₀ k Z C z w _ s ε hC hk₀ hzf hw
            hε)).trans (closure_mono hcellsub)
    · have hpw := hsub hpe
      have hd := fineLayer_cells_disjoint o k kw Z C z w hzf hw hne
      have hH := ball_diff_closure_subset_closure_of_mem_segment o (fineScaleIndex k)
        (fineScaleIndex kw) z w _ s hd hρ hpe hpw (by linarith) (by linarith)
        (fun ε hε ↦ fineLayer_corner_on_elementarySide o k₀ k kw Z C z w s ε hC hk hzf hkw₀
          hw hε)
      have hcontact : (segment ℝ
          (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s)
          (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s) ∩
          closure (dyadicCell o (fineScaleIndex kw) w)).Nontrivial :=
        Set.nontrivial_of_mem_mem_ne ⟨left_mem_segment ℝ _ _, hsub (left_mem_segment ℝ _ _)⟩
          ⟨right_mem_segment ℝ _ _, hsub (right_mem_segment ℝ _ _)⟩ hab
      by_cases hwb : w ∈ beltCellIndices (fineLayerIndices o kw (fineScaleIndex kw) Z C)
          (2 ^ (pitchScaleIndex kw - fineScaleIndex kw)) (a kw) (b kw)
      · obtain ⟨j, -, hsj, hej⟩ := fineLayer_elementary_contact_match o k₀ k kw Z C z w hC hk
          hk₀ hkw₀ hzf hw hne s hcontact
        let Rj := (cellFanRunGraph o (fineScaleIndex kw) w (fineLayerSplitMask o k₀ kw Z C w)
          (beltCellFanColor o k₀ Z C a b kw w hC h₀ hkw₀ hwb)).connectedComponentMk j
        have hjR : j ∈ Rj.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
        have hTj := cellFanPolygon_subset_initialBirthRegion o k₀ Z C a b hC h₀ kw hkw₀ w hwb
          Rj hjR
        have hsegj : segment ℝ
            (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s)
            (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s) ⊆
            segment ℝ (cellFanStart o (fineScaleIndex kw) w (fineLayerSplitMask o k₀ kw Z C w) j)
              (cellFanEnd o (fineScaleIndex kw) w (fineLayerSplitMask o k₀ kw Z C w) j) := by
          rw [hsj, hej, segment_symm]
        have hsegT : segment ℝ
            (cellFanStart o (fineScaleIndex kw) w (fineLayerSplitMask o k₀ kw Z C w) j)
            (cellFanEnd o (fineScaleIndex kw) w (fineLayerSplitMask o k₀ kw Z C w) j) ⊆
            (cellFanPolygon o (fineScaleIndex kw) w
              (fineLayerSplitMask o k₀ kw Z C w) j).region := by
          intro q hq
          rw [cellFanPolygon_region_eq]
          exact segment_subset_convexHull (by simp) (by simp) hq
        refine ⟨.inr (.inr ⟨⟨kw, hkw₀⟩, ⟨w, hwb⟩, Rj⟩), ?_, (hsegj.trans hsegT).trans hTj⟩
        intro q hq
        apply hTj
        have hqw := hH hq
        have hZw := closedBall_cellFanCenter_eq_closure_dyadicCell o (fineScaleIndex kw) w
        rw [← hZw] at hqw
        have hpj := hsegj hpe
        have hpcw := norm_sub_cellFanCenter_of_mem_base o (fineScaleIndex kw) w _ j hpj
        have hsw := hsub (left_mem_segment ℝ _ _)
        have hew := hsub (right_mem_segment ℝ _ _)
        rw [← hZw, Metric.mem_closedBall] at hsw hew
        have hlen := dist_add_dist_of_mem_segment hpe
        have hse := dist_triangle (cellFanStart o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) s) (cellFanCenter o (fineScaleIndex kw) w)
          (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s)
        rw [dist_comm (cellFanCenter o (fineScaleIndex kw) w)] at hse
        have hqp : dist q p < (2 : ℝ) ^ fineScaleIndex k / 1024 := hq.1
        refine mem_cellFanPolygon_of_dist_lt_of_mem_base o (fineScaleIndex kw) w _ j
          (d' := (2 : ℝ) ^ fineScaleIndex k / 256) (hsegT hpj) (by rw [dist_eq_norm, hpcw])
          hqw (by positivity) (by rw [dist_comm] at hps; linarith) (by rw [← hej]; exact hpe')
          (by rw [← hsj]; exact hps) (by linarith)
      · obtain ⟨hJ, -, -, -⟩ := beltCellFanColor_nonbelt_opponent o k₀ Z C a b k kw z w hC h₀
          hk₀ hkw₀ hz hw hwb s hcontact
        have hprim := closure_nonbeltCell_subset_primaryBirthRegion o kw (fineScaleIndex kw)
          (pitchScaleIndex kw) Z C (a kw) (b kw) w (fineScaleIndex_le kw)
          ((fineScaleIndex_le kw).trans (le_pitchScaleIndex kw)) hw hwb
        exact ⟨.inr (.inl ⟨⟨kw, hkw₀⟩, ⟨_, hJ⟩⟩), hH.trans hprim, hsub.trans hprim⟩
  -- a point of the open region of `i` beyond the side lies in the open region of `i'`
  have hyp : dist y p < (2 : ℝ) ^ fineScaleIndex k / 1024 := by rw [dist_comm]; linarith
  have hε : 0 < (2 : ℝ) ^ fineScaleIndex k / 1024 - dist y p := by linarith
  obtain ⟨q, hqU, hqZ⟩ : ∃ q ∈ Metric.ball y ((2 : ℝ) ^ fineScaleIndex k / 1024 - dist y p) ∩
      initialOpenRegion o k₀ Z C a b hC h₀ i, q ∉ closure (dyadicCell o (fineScaleIndex k) z) := by
    have hU : (Metric.ball y ((2 : ℝ) ^ fineScaleIndex k / 1024 - dist y p) ∩
        initialOpenRegion o k₀ Z C a b hC h₀ i).Nonempty := by
      have hy' : y ∈ closure (initialOpenRegion o k₀ Z C a b hC h₀ i) := hreg ▸ hy
      exact mem_closure_iff.mp hy' _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    by_contra hall
    have hsub : Metric.ball y ((2 : ℝ) ^ fineScaleIndex k / 1024 - dist y p) ∩
        initialOpenRegion o k₀ Z C a b hC h₀ i ⊆
        frontier (closure (dyadicCell o (fineScaleIndex k) z)) := by
      intro q hq
      have hqZ : q ∈ closure (dyadicCell o (fineScaleIndex k) z) :=
        by_contra fun h ↦ hall ⟨q, hq, h⟩
      rw [isClosed_closure.frontier_eq, ← hZc, interior_closedBall _ (by positivity)]
      rw [← hZc] at hqZ
      exact ⟨hqZ, fun hqi ↦ (Set.eq_empty_iff_forall_notMem.mp hint) q ⟨hq.2, hqi⟩⟩
    have hint' := interior_maximal hsub (Metric.isOpen_ball.inter isOpen_interior)
    rw [interior_frontier isClosed_closure] at hint'
    obtain ⟨q, hq⟩ := hU
    exact hint' hq
  have hqH : q ∈ Metric.ball p ((2 : ℝ) ^ fineScaleIndex k / 1024) \
      closure (dyadicCell o (fineScaleIndex k) z) := by
    refine ⟨?_, hqZ⟩
    rw [Metric.mem_ball]
    have := Metric.mem_ball.mp hqU.1
    have := dist_triangle q y p
    linarith
  have hqi' : q ∈ initialOpenRegion o k₀ Z C a b hC h₀ i' :=
    interior_maximal hH (Metric.isOpen_ball.sdiff isClosed_closure) hqH
  have hii' : i = i' := by
    by_contra h
    exact Set.disjoint_left.mp (initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀ h)
      hqU.2 hqi'
  subst hii'
  have hsegB : segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) s) ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, Rr⟩)) := by
    intro q hq
    apply cellFanPolygon_subset_initialBirthRegion o k₀ Z C a b hC h₀ k hk₀ z hz Rr hs
    rw [cellFanPolygon_region_eq]
    exact segment_subset_convexHull (by simp) (by simp) hq
  exact initialRegionColor_ne_of_segment_subset_inter o k₀ Z C a b hC h₀ i _ hi _ _ hab
    (fun q hq ↦ ⟨hseg' hq, hsegB hq⟩) hcolor

end OpenAI.Geometry
