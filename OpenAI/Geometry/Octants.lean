import OpenAI.Geometry.SimultaneousRepair
import OpenAI.Geometry.TemplatePolygons
import OpenAI.Geometry.DyadicOrigin
import OpenAI.Geometry.DistanceLayers

/-!
# Octant stars in the sup-norm plane

The eight closed octants about a point are the cones between consecutive axis and diagonal
directions.  Intersected with a closed sup-norm ball of radius `d`, octant `k` is the triangle
from the center to a side midpoint and a corner, the all-midpoint fan of the square
[OAI265, §11, `geometry:initial-stars` and the repair step, lines 333–420].

The file supplies the local geometry of one repair: the angular gap between non-adjacent
octants, the clearance across an active ray once the ray-hit point has been trimmed, and the
description of the octants about each of the nine marks of a removal square in terms of the
octants of its center (`childOctant`).

## Main definitions

* `octantCone`, `octantConeAt`, `octantTriangle`: the closed octants and their triangles.
* `octantRay`: the direction separating octant `k - 1` from octant `k`.
* `rayChildOffset`: the child offset at which ray `k` meets the boundary of a removal square.
* `childOctant`: for a child offset and an octant about the child, the octant about the parent
  center and whether the child octant lies inside the removal square.

## Main statements

* `iUnion_octantTriangle`: the eight triangles cover the closed ball.
* `max_dist_le_two_mul_dist_of_not_adjacent`: the angular gap.
* `half_le_dist_of_mem_octantTriangle_succ`, `half_le_dist_of_mem_octantTriangle_pred`: the
  ray-hit clearance.
* `mem_octantConeAt_child_iff`: the child-octant table.
* `octantTriangle_isTemplatePiece`: each triangle is a template piece.

## Implementation notes

Native to this project; the paper's compactness argument over finite local patterns is replaced
by these explicit linear estimates, with constant `1 / 2`.
-/

noncomputable section

namespace OpenAI.Geometry

/-- The closed octant `k` at the origin: the directions between `k π / 4` and
`(k + 1) π / 4`. -/
def octantCone : Fin 8 → Set (ℝ × ℝ)
  | 0 => {p | 0 ≤ p.2 ∧ p.2 ≤ p.1}
  | 1 => {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  | 2 => {p | 0 ≤ -p.1 ∧ -p.1 ≤ p.2}
  | 3 => {p | 0 ≤ p.2 ∧ p.2 ≤ -p.1}
  | 4 => {p | 0 ≤ -p.2 ∧ -p.2 ≤ -p.1}
  | 5 => {p | 0 ≤ -p.1 ∧ -p.1 ≤ -p.2}
  | 6 => {p | 0 ≤ p.1 ∧ p.1 ≤ -p.2}
  | 7 => {p | 0 ≤ -p.2 ∧ -p.2 ≤ p.1}

/-- The closed octant `k` about the point `v`. -/
def octantConeAt (v : ℝ × ℝ) (k : Fin 8) : Set (ℝ × ℝ) :=
  {x | x - v ∈ octantCone k}

/-- The closed triangle of octant `k` about `v` inside the closed sup-norm ball of radius `d`:
the triangle from `v` to `v + d • octantRay k` and `v + d • octantRay (k + 1)`. -/
def octantTriangle (v : ℝ × ℝ) (d : ℝ) (k : Fin 8) : Set (ℝ × ℝ) :=
  octantConeAt v k ∩ Metric.closedBall v d

/-- The direction at angle `k π / 4`, separating octant `k - 1` from octant `k`. -/
def octantRay : Fin 8 → ℝ × ℝ :=
  ![(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]

/-- The child offset in `Fin 3 × Fin 3` (coordinates shifted by one, as in
`repairChildOffset`) at which ray `k` meets the boundary of a removal square. -/
def rayChildOffset : Fin 8 → Fin 3 × Fin 3 :=
  ![(2, 1), (2, 2), (1, 2), (0, 2), (0, 1), (0, 0), (1, 0), (2, 0)]

/-- For the child of offset `o` of a removal square and an octant `j` about that child, the
octant of the removal center containing child octant `j` near the child, and whether it lies
inside the square (`true`) or outside it (`false`).  At the center the octants are unchanged
and inside; at a side midpoint or a corner the eight child octants split into an inside run and
an outside run, read off by rotating the two basic tables for the ray through the child. -/
def childOctant (o : Fin 3 × Fin 3) (j : Fin 8) : Fin 8 × Bool :=
  match o with
  | (1, 1) => (j, true)
  -- axis rays: the child is `v + d • octantRay (2 * i)`
  | (2, 1) => ![(0, false), (0, false), (0, true), (0, true),
                (7, true), (7, true), (7, false), (7, false)] j
  | (1, 2) => ![(1, false), (1, false), (2, false), (2, false),
                (2, true), (2, true), (1, true), (1, true)] j
  | (0, 1) => ![(3, true), (3, true), (3, false), (3, false),
                (4, false), (4, false), (4, true), (4, true)] j
  | (1, 0) => ![(6, true), (6, true), (5, true), (5, true),
                (5, false), (5, false), (6, false), (6, false)] j
  -- diagonal rays: the child is `v + d • octantRay (2 * i + 1)`
  | (2, 2) => ![(0, false), (1, false), (1, false), (1, false),
                (1, true), (0, true), (0, false), (0, false)] j
  | (0, 2) => ![(2, false), (2, false), (2, false), (3, false),
                (3, false), (3, false), (3, true), (2, true)] j
  | (0, 0) => ![(5, true), (4, true), (4, false), (4, false),
                (4, false), (5, false), (5, false), (5, false)] j
  | (2, 0) => ![(7, false), (7, false), (7, true), (6, true),
                (6, false), (6, false), (6, false), (7, false)] j
  | _ => (j, true)

/-! ### Basic structure -/

/-- Every point of the plane lies in some closed octant. -/
private theorem exists_mem_octantCone (p : ℝ × ℝ) : ∃ k, p ∈ octantCone k := by
  rcases le_total 0 p.1 with h1 | h1 <;> rcases le_total 0 p.2 with h2 | h2 <;>
    rcases le_total p.1 p.2 with h3 | h3 <;> rcases le_total (-p.1) p.2 with h4 | h4
  all_goals first
    | (refine ⟨0, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨1, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨2, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨3, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨4, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨5, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨6, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨7, ?_⟩; simp only [octantCone, Set.mem_ofPred_eq]; constructor <;> linarith)

/-- The eight closed octants cover the plane. -/
theorem iUnion_octantCone : ⋃ k, octantCone k = Set.univ := by
  exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.mpr (exists_mem_octantCone p)

/-- The eight octant triangles about `v` cover the closed ball of radius `d`. -/
theorem iUnion_octantTriangle (v : ℝ × ℝ) (d : ℝ) :
    ⋃ k, octantTriangle v d k = Metric.closedBall v d := by
  ext x
  simp only [Set.mem_iUnion, octantTriangle, Set.mem_inter_iff]
  refine ⟨fun ⟨_, _, h⟩ => h, fun h => ?_⟩
  obtain ⟨k, hk⟩ := exists_mem_octantCone (x - v)
  exact ⟨k, hk, h⟩

/-- A point of octant `k` is at distance `‖x - v‖` along a cone, so octant membership is
invariant under positive scaling about the center. -/
theorem mem_octantConeAt_lineMap {v x : ℝ × ℝ} {k : Fin 8} (hx : x ∈ octantConeAt v k)
    {t : ℝ} (ht : 0 ≤ t) : v + t • (x - v) ∈ octantConeAt v k := by
  simp only [octantConeAt, Set.mem_ofPred_eq, add_sub_cancel_left] at hx ⊢
  fin_cases k <;>
    simp only [octantCone, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx ⊢ <;>
    constructor <;> nlinarith [mul_nonneg ht hx.1, mul_nonneg ht (sub_nonneg.mpr hx.2)]

/-- The ray of `octantRay k` lies in both octants it separates. -/
theorem octantRay_mem_octantCone (k : Fin 8) (t : ℝ) (ht : 0 ≤ t) :
    t • octantRay k ∈ octantCone k ∧ t • octantRay k ∈ octantCone (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (sub_add_cancel k 1).symm⟩
  rw [add_sub_cancel_right]
  fin_cases j <;> simp [octantRay, octantCone, ht]

/-- The child of offset `rayChildOffset k` of a removal square of half-side `d` about `v` is the
point `v + d • octantRay k`. -/
theorem repairChildOffset_rayChildOffset (k : Fin 8) :
    repairChildOffset (rayChildOffset k) = octantRay k := by
  fin_cases k <;> simp [repairChildOffset, rayChildOffset, octantRay] <;> norm_num

/-! ### Clearance estimates -/

/-- **Angular gap.**  Points of two non-adjacent octants about `v` are at sup distance at least
half the larger of their distances to `v`. -/
theorem max_dist_le_two_mul_dist_of_not_adjacent {v x y : ℝ × ℝ} {k j : Fin 8}
    (hjk : j ≠ k) (hj : j ≠ k + 1) (hk : k ≠ j + 1)
    (hx : x ∈ octantConeAt v k) (hy : y ∈ octantConeAt v j) :
    max (dist x v) (dist y v) ≤ 2 * dist x y := by
  have hA := abs_le.mp (le_max_left |x.1 - y.1| |x.2 - y.2|)
  have hB := abs_le.mp (le_max_right |x.1 - y.1| |x.2 - y.2|)
  simp only [Prod.dist_eq, Real.dist_eq]
  generalize max |x.1 - y.1| |x.2 - y.2| = M at *
  simp only [octantConeAt, Set.mem_ofPred_eq] at hx hy
  simp only [max_le_iff, abs_le]
  fin_cases k <;> fin_cases j <;> try (simp at hjk hj hk; done)
  all_goals
    simp only [octantCone, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **Ray-hit clearance**, ray after the triangle.  A point of the next octant outside the open
ball of radius `d`, at distance at least `d'` from the point where the separating ray leaves the
square, is at distance at least `d' / 2` from the triangle of octant `k`. -/
theorem half_le_dist_of_mem_octantTriangle_succ {v x y : ℝ × ℝ} {d d' : ℝ} {k : Fin 8}
    (hd' : 0 ≤ d') (hd'd : d' ≤ d) (hx : x ∈ octantTriangle v d k)
    (hy : y ∈ octantConeAt v (k + 1)) (hyv : d ≤ dist y v)
    (hyc : d' ≤ dist y (v + d • octantRay (k + 1))) :
    d' / 2 ≤ dist x y := by
  rw [← not_lt]
  intro hlt
  simp only [octantTriangle, Set.mem_inter_iff, octantConeAt, Set.mem_ofPred_eq,
    Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, max_le_iff, abs_le] at hx
  simp only [octantConeAt, Set.mem_ofPred_eq] at hy
  simp only [Prod.dist_eq, Real.dist_eq, le_max_iff, le_abs, max_lt_iff, abs_lt] at hyv hyc hlt
  fin_cases k <;>
    simp only [octantCone, octantRay, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
      Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Matrix.cons_val, Prod.smul_mk, smul_eq_mul,
      mul_one, mul_zero, mul_neg, Prod.fst_add, Prod.snd_add, add_zero] at hx hy hyc <;>
    casesm* _ ∧ _, _ ∨ _ <;> linarith

/-- **Ray-hit clearance**, ray before the triangle.  The mirror form of
`half_le_dist_of_mem_octantTriangle_succ`: the point lies in octant `k` and the triangle is
that of octant `k + 1`. -/
theorem half_le_dist_of_mem_octantTriangle_pred {v x y : ℝ × ℝ} {d d' : ℝ} {k : Fin 8}
    (hd' : 0 ≤ d') (hd'd : d' ≤ d) (hx : x ∈ octantTriangle v d (k + 1))
    (hy : y ∈ octantConeAt v k) (hyv : d ≤ dist y v)
    (hyc : d' ≤ dist y (v + d • octantRay (k + 1))) :
    d' / 2 ≤ dist x y := by
  rw [← not_lt]
  intro hlt
  simp only [octantTriangle, Set.mem_inter_iff, octantConeAt, Set.mem_ofPred_eq,
    Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, max_le_iff, abs_le] at hx
  simp only [octantConeAt, Set.mem_ofPred_eq] at hy
  simp only [Prod.dist_eq, Real.dist_eq, le_max_iff, le_abs, max_lt_iff, abs_lt] at hyv hyc hlt
  fin_cases k <;>
    simp only [octantCone, octantRay, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
      Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Matrix.cons_val, Prod.smul_mk, smul_eq_mul,
      mul_one, mul_zero, mul_neg, Prod.fst_add, Prod.snd_add, add_zero] at hx hy hyc <;>
    casesm* _ ∧ _, _ ∨ _ <;> linarith

/-! ### The octants about the nine marks of a removal square -/

/-- Closes a goal `∃ j, childOctant o j = (k, b) ∧ q ∈ octantCone j` with concrete `o`, `k`,
`b` and `q`, or refutes the hypotheses, by linear arithmetic. -/
local macro "child_close" : tactic => `(tactic|
  first
    | (exfalso; linarith)
    | (refine ⟨0, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨1, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨2, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨3, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨4, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨5, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨6, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith)
    | (refine ⟨7, ?_, ?_⟩
       · decide
       · simp only [octantCone, Set.mem_ofPred_eq]
         constructor <;> linarith))

/-- Closes a conjunction of two linear inequalities and a sup-norm bound `max |a| |b| ≤ d` or
`d ≤ max |a| |b|`, unfolded to inequalities, by linear arithmetic. -/
local macro "child_close_mpr" : tactic => `(tactic|
  (refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    first
      | linarith
      | (refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
      | (left; left; linarith)
      | (left; right; linarith)
      | (right; left; linarith)
      | (right; right; linarith)))

set_option hygiene false in
/-- The forward direction of `child_iff_aux_00` and its siblings, for the point `q` about the
child: refute every octant `k` that does not meet the child's neighbourhood, then locate `q` in
an octant `j` about the child and close the goal with `child_close`. -/
local macro "child_mp " q:term : tactic => `(tactic|
  (rintro ⟨hk, hb⟩
   obtain ⟨j, hj⟩ := exists_mem_octantCone $q
   fin_cases k <;> cases b <;>
     simp only [octantCone, Set.mem_ofPred_eq, max_le_iff, abs_le, le_max_iff, le_abs, ↓reduceIte,
        Bool.false_eq_true] at hk hb <;>
     casesm* _ ∧ _ <;>
     try (exfalso; linarith)
   all_goals
     try casesm* _ ∨ _
     try (exfalso; linarith)
   all_goals
     fin_cases j <;>
     simp only [octantCone, Set.mem_ofPred_eq] at hj <;>
     casesm* _ ∧ _ <;>
     child_close))

set_option hygiene false in
/-- The reverse direction of `child_iff_aux_00` and its siblings. -/
local macro "child_mpr" : tactic => `(tactic|
  (rintro ⟨j, hj, hjx⟩
   fin_cases k <;> cases b <;> fin_cases j <;> try (exfalso; revert hj; decide)
   all_goals
     simp only [octantCone, Set.mem_ofPred_eq, max_le_iff, abs_le, le_max_iff, le_abs, ↓reduceIte,
        Bool.false_eq_true] at hjx ⊢
     casesm* _ ∧ _
     child_close_mpr))

/-! The child-octant table for each of the nine offsets, in coordinates `(p₁, p₂) = x - v`. -/

private theorem child_iff_aux_00 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁ + d| ≤ R) (h₂ : |p₂ + d| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (0, 0) j = (k, b) ∧ (p₁ + d, p₂ + d) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁ + d, p₂ + d)
  · child_mpr

private theorem child_iff_aux_01 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁ + d| ≤ R) (h₂ : |p₂| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (0, 1) j = (k, b) ∧ (p₁ + d, p₂) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁ + d, p₂)
  · child_mpr

private theorem child_iff_aux_02 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁ + d| ≤ R) (h₂ : |p₂ - d| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (0, 2) j = (k, b) ∧ (p₁ + d, p₂ - d) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁ + d, p₂ - d)
  · child_mpr

private theorem child_iff_aux_10 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁| ≤ R) (h₂ : |p₂ + d| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (1, 0) j = (k, b) ∧ (p₁, p₂ + d) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁, p₂ + d)
  · child_mpr

private theorem child_iff_aux_11 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁| ≤ R) (h₂ : |p₂| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (1, 1) j = (k, b) ∧ (p₁, p₂) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁, p₂)
  · child_mpr

private theorem child_iff_aux_12 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁| ≤ R) (h₂ : |p₂ - d| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (1, 2) j = (k, b) ∧ (p₁, p₂ - d) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁, p₂ - d)
  · child_mpr

private theorem child_iff_aux_20 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁ - d| ≤ R) (h₂ : |p₂ + d| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (2, 0) j = (k, b) ∧ (p₁ - d, p₂ + d) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁ - d, p₂ + d)
  · child_mpr

private theorem child_iff_aux_21 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁ - d| ≤ R) (h₂ : |p₂| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (2, 1) j = (k, b) ∧ (p₁ - d, p₂) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁ - d, p₂)
  · child_mpr

private theorem child_iff_aux_22 {p₁ p₂ d R : ℝ} (hR : 0 ≤ R) (hRd : 2 * R < d)
    (h₁ : |p₁ - d| ≤ R) (h₂ : |p₂ - d| ≤ R) (k : Fin 8) (b : Bool) :
    ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ d else d ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant (2, 2) j = (k, b) ∧ (p₁ - d, p₂ - d) ∈ octantCone j := by
  rw [abs_le] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  constructor
  · child_mp (p₁ - d, p₂ - d)
  · child_mpr

/-- **Child-octant table.**  Near a child `c = v + d • repairChildOffset o` of a removal square
of half-side `d` about `v`, within sup distance `R < d / 2` of `c`, a point lies in octant `k`
about `v` inside the closed square (`b = true`), respectively outside the open square
(`b = false`), exactly when it lies in some octant `j` about `c` with
`childOctant o j = (k, b)`. -/
theorem mem_octantConeAt_child_iff {v x : ℝ × ℝ} {d R : ℝ} (o : Fin 3 × Fin 3)
    (hR : 0 ≤ R) (hRd : 2 * R < d)
    (hx : x ∈ Metric.closedBall (v + d • repairChildOffset o) R) (k : Fin 8) (b : Bool) :
    (x ∈ octantConeAt v k ∧
        (if b then x ∈ Metric.closedBall v d else x ∉ Metric.ball v d)) ↔
      ∃ j, childOctant o j = (k, b) ∧ x ∈ octantConeAt (v + d • repairChildOffset o) j := by
  have hc : ∀ j, x ∈ octantConeAt (v + d • repairChildOffset o) j ↔
      ((x - v).1 - d * (repairChildOffset o).1, (x - v).2 - d * (repairChildOffset o).2) ∈
        octantCone j := by
    intro j
    have e : x - (v + d • repairChildOffset o) =
        ((x - v).1 - d * (repairChildOffset o).1, (x - v).2 - d * (repairChildOffset o).2) := by
      ext <;> simp <;> ring
    rw [octantConeAt, Set.mem_ofPred_eq, e]
  have hif : (if b then x ∈ Metric.closedBall v d else x ∉ Metric.ball v d) ↔
      (if b then max |(x - v).1| |(x - v).2| ≤ d else d ≤ max |(x - v).1| |(x - v).2|) := by
    cases b <;>
      simp only [Metric.mem_closedBall, Metric.mem_ball, not_lt, Prod.dist_eq, Real.dist_eq,
        Prod.fst_sub, Prod.snd_sub, ↓reduceIte, Bool.false_eq_true]
  rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at hx
  obtain ⟨h₁, h₂⟩ := hx
  have e₁ : x.1 - (v + d • repairChildOffset o).1 = (x - v).1 - d * (repairChildOffset o).1 := by
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
    ring
  have e₂ : x.2 - (v + d • repairChildOffset o).2 = (x - v).2 - d * (repairChildOffset o).2 := by
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e₁] at h₁
  rw [e₂] at h₂
  have hv : x ∈ octantConeAt v k ↔ ((x - v).1, (x - v).2) ∈ octantCone k := Iff.rfl
  rw [hv, hif]
  simp only [hc]
  generalize (x - v).1 = p₁ at *
  generalize (x - v).2 = p₂ at *
  obtain ⟨w, hw⟩ : ∃ w, repairChildOffset o = w := ⟨_, rfl⟩
  rw [hw] at h₁ h₂ ⊢
  fin_cases o <;> norm_num [repairChildOffset] at hw <;> subst hw <;>
    simp only [mul_one, mul_zero, mul_neg, sub_zero, sub_neg_eq_add] at h₁ h₂ ⊢
  · exact child_iff_aux_00 hR hRd h₁ h₂ k b
  · exact child_iff_aux_01 hR hRd h₁ h₂ k b
  · exact child_iff_aux_02 hR hRd h₁ h₂ k b
  · exact child_iff_aux_10 hR hRd h₁ h₂ k b
  · exact child_iff_aux_11 hR hRd h₁ h₂ k b
  · exact child_iff_aux_12 hR hRd h₁ h₂ k b
  · exact child_iff_aux_20 hR hRd h₁ h₂ k b
  · exact child_iff_aux_21 hR hRd h₁ h₂ k b
  · exact child_iff_aux_22 hR hRd h₁ h₂ k b

/-- Consecutive octants about a child come from the same parent octant on opposite sides of
the square, or from adjacent parent octants on the same side. -/
theorem childOctant_succ (o : Fin 3 × Fin 3) (j : Fin 8) :
    childOctant o (j + 1) = childOctant o j ∨
      ((childOctant o (j + 1)).1 = (childOctant o j).1 ∧
        (childOctant o (j + 1)).2 ≠ (childOctant o j).2) ∨
      ((childOctant o (j + 1)).2 = (childOctant o j).2 ∧
        ((childOctant o (j + 1)).1 = (childOctant o j).1 + 1 ∨
          (childOctant o j).1 = (childOctant o (j + 1)).1 + 1)) := by
  revert o j
  decide

/-! ### Templates and lattice points -/

/-- Each closed octant about a point is convex. -/
private theorem convex_octantConeAt (v : ℝ × ℝ) (k : Fin 8) : Convex ℝ (octantConeAt v k) := by
  intro x hx y hy a b ha hb hab
  have e : a • x + b • y - v = a • (x - v) + b • (y - v) := by
    calc a • x + b • y - v = a • x + b • y - (a + b) • v := by rw [hab, one_smul]
      _ = a • (x - v) + b • (y - v) := by rw [add_smul, smul_sub, smul_sub]; abel
  simp only [octantConeAt, Set.mem_ofPred_eq] at hx hy ⊢
  rw [e]
  generalize x - v = p at *
  generalize y - v = q at *
  fin_cases k <;>
    simp only [octantCone, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hx hy ⊢ <;>
    obtain ⟨hx₁, hx₂⟩ := hx <;> obtain ⟨hy₁, hy₂⟩ := hy <;>
    constructor <;>
    nlinarith [mul_nonneg ha hx₁, mul_nonneg hb hy₁, mul_nonneg ha (sub_nonneg.2 hx₂),
      mul_nonneg hb (sub_nonneg.2 hy₂)]

/-- A point of octant `k` in the closed sup-norm ball of radius `d` is a combination
`α • octantRay k + β • octantRay (k + 1)` with `α, β ≥ 0` and `α + β ≤ d`. -/
private theorem exists_eq_smul_octantRay_add_smul {p : ℝ × ℝ} {d : ℝ} {k : Fin 8}
    (hp : p ∈ octantCone k) (hd : max |p.1| |p.2| ≤ d) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ d ∧ p = α • octantRay k + β • octantRay (k + 1) := by
  rw [max_le_iff, abs_le, abs_le] at hd
  obtain ⟨⟨h₃, h₄⟩, h₅, h₆⟩ := hd
  refine ⟨p.1 * (octantRay (k + 1)).2 - p.2 * (octantRay (k + 1)).1,
    (octantRay k).1 * p.2 - (octantRay k).2 * p.1, ?_, ?_, ?_, Prod.ext ?_ ?_⟩ <;>
    fin_cases k <;> simp only [octantCone, Set.mem_ofPred_eq] at hp <;>
    obtain ⟨h₁, h₂⟩ := hp <;> simp [octantRay] <;> linarith

/-- Consecutive rays form a positively oriented unimodular pair. -/
private theorem octantRay_cross (k : Fin 8) :
    (octantRay k).1 * (octantRay (k + 1)).2 - (octantRay k).2 * (octantRay (k + 1)).1 = 1 := by
  fin_cases k <;> simp [octantRay]

/-- The point at parameter `d ≥ 0` along a ray is at sup distance `d` from the center. -/
private theorem dist_add_smul_octantRay (v : ℝ × ℝ) {d : ℝ} (hd : 0 ≤ d) (k : Fin 8) :
    dist (v + d • octantRay k) v = d := by
  fin_cases k <;> simp [octantRay, abs_of_nonneg hd, hd]

/-- An octant triangle is the convex hull of the center and the two points where its bounding
rays leave the square. -/
theorem octantTriangle_eq_convexHull (v : ℝ × ℝ) {d : ℝ} (hd : 0 ≤ d) (k : Fin 8) :
    octantTriangle v d k =
      convexHull ℝ {v, v + d • octantRay k, v + d • octantRay (k + 1)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxd⟩
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, ← Prod.fst_sub,
      ← Prod.snd_sub] at hxd
    obtain ⟨α, β, hα, hβ, hαβ, hp⟩ := exists_eq_smul_octantRay_add_smul hx hxd
    have hx₂ : x = v + (α • octantRay k + β • octantRay (k + 1)) := by rw [← hp]; abel
    rcases hd.eq_or_lt with rfl | hd'
    · have hα0 : α = 0 := by linarith
      have hβ0 : β = 0 := by linarith
      rw [hx₂, hα0, hβ0, zero_smul, zero_smul, add_zero, add_zero]
      exact subset_convexHull ℝ _ (by simp)
    · have hx' : x = ∑ i, ![1 - (α + β) / d, α / d, β / d] i •
          ![v, v + d • octantRay k, v + d • octantRay (k + 1)] i := by
        rw [hx₂]
        ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring
      rw [hx']
      refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_
        (fun i _ => subset_convexHull ℝ _ ?_)
      · fin_cases i
        · exact sub_nonneg.2 ((div_le_one hd').2 hαβ)
        · exact div_nonneg hα hd
        · exact div_nonneg hβ hd
      · simp [Fin.sum_univ_three]
        field_simp
        ring
      · fin_cases i <;> simp
  · refine convexHull_min ?_ ((convex_octantConeAt v k).inter (convex_closedBall v d))
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨⟨?_, Metric.mem_closedBall_self hd⟩, ⟨?_, (dist_add_smul_octantRay v hd k).le⟩,
      ⟨?_, (dist_add_smul_octantRay v hd (k + 1)).le⟩⟩
    · simpa [octantConeAt] using (octantRay_mem_octantCone k 0 le_rfl).1
    · simpa [octantConeAt] using (octantRay_mem_octantCone k d hd).1
    · simpa [octantConeAt] using (octantRay_mem_octantCone (k + 1) d hd).2

/-- An octant triangle of positive radius is a template piece of sup-norm diameter at most its
radius. -/
theorem octantTriangle_isTemplatePiece (v : ℝ × ℝ) {d : ℝ} (hd : 0 < d) (k : Fin 8) :
    OpenAI.IsTemplatePiece (octantTriangle v d k) ∧
      Metric.ediam (octantTriangle v d k) ≤ ENNReal.ofReal d := by
  refine ⟨Or.inr ⟨v, v + d • octantRay k, v + d • octantRay (k + 1), ?_, ?_, ?_, ?_,
    octantTriangle_eq_convexHull v hd.le k⟩, ?_⟩
  · have h := octantRay_cross k
    simp only [add_sub_cancel_left, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have e : d * (octantRay k).1 * (d * (octantRay (k + 1)).2) -
        d * (octantRay k).2 * (d * (octantRay (k + 1)).1) = d ^ 2 := by
      linear_combination d ^ 2 * h
    rw [e]
    positivity
  · fin_cases k <;> simp [HasTemplateSlope, octantRay]
  · fin_cases k <;> simp [HasTemplateSlope, octantRay]
  · fin_cases k <;> simp [HasTemplateSlope, octantRay]
  · refine Metric.ediam_le fun x hx y hy => ?_
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hx, hxd⟩ := hx
    obtain ⟨hy, hyd⟩ := hy
    simp only [octantConeAt, Set.mem_ofPred_eq] at hx hy
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff, abs_le,
      abs_le] at hxd hyd
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff, abs_le, abs_le]
    fin_cases k <;>
      simp only [octantCone, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub] at hx hy <;>
      casesm* _ ∧ _ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- No lattice point lies on a ray through a point of the translated mesh
`dyadicOrigin + ℤ²`, so a lattice point lies in at most one octant about such a point. -/
theorem eq_of_integerPoint_mem_octantConeAt {a : ℤ × ℤ} {z : ℤ × ℤ} {k j : Fin 8}
    (hk : integerPoint z ∈ octantConeAt (dyadicOrigin + integerPoint a) k)
    (hj : integerPoint z ∈ octantConeAt (dyadicOrigin + integerPoint a) j) : k = j := by
  have e1 := (dyadicOrigin_supporting_lines_avoid_lattice z a.1).1
  have e2 := (dyadicOrigin_supporting_lines_avoid_lattice z a.2).2.1
  have e3 := (dyadicOrigin_supporting_lines_avoid_lattice z (a.1 + a.2)).2.2.1
  have e4 := (dyadicOrigin_supporting_lines_avoid_lattice z (a.1 - a.2)).2.2.2
  push_cast at e3 e4
  simp only [octantConeAt, Set.mem_ofPred_eq, integerPoint] at hk hj
  fin_cases k <;> fin_cases j <;>
    simp only [octantCone, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add,
      Prod.snd_add] at hk hj <;>
    first
      | rfl
      | exfalso
        first
          | exact e1 (by linarith)
          | exact e2 (by linarith)
          | exact e3 (by linarith)
          | exact e4 (by linarith)

/-- No lattice point lies on the boundary of an integer-radius sup-norm square centered on the
translated mesh `dyadicOrigin + ℤ²`. -/
theorem dist_integerPoint_ne_natCast (a z : ℤ × ℤ) (n : ℕ) :
    dist (integerPoint z) (dyadicOrigin + integerPoint a) ≠ n := by
  intro h
  simp only [Prod.dist_eq, Real.dist_eq, integerPoint, Prod.fst_add, Prod.snd_add] at h
  rcases max_choice |(z.1 : ℝ) - (dyadicOrigin.1 + a.1)| |(z.2 : ℝ) - (dyadicOrigin.2 + a.2)|
    with hm | hm <;> rw [hm, abs_eq (Nat.cast_nonneg n)] at h
  · rcases h with h | h
    · exact (dyadicOrigin_nonintegral (z.1 - a.1 - n)).1 (by push_cast; linarith)
    · exact (dyadicOrigin_nonintegral (z.1 - a.1 + n)).1 (by push_cast; linarith)
  · rcases h with h | h
    · exact (dyadicOrigin_nonintegral (z.2 - a.2 - n)).2.1 (by push_cast; linarith)
    · exact (dyadicOrigin_nonintegral (z.2 - a.2 + n)).2.1 (by push_cast; linarith)

end OpenAI.Geometry
