import AreaLaw.S11_Geometry.Layers
import AreaLaw.S11_Geometry.RepairScales
import OpenAI.Statements

/-! # §11.5 Removing point contacts at successively smaller scales

The local geometry of one point contact: the eight octants of a star, the octants about the
nine child marks of a removal square, the angular gap and ray-hit clearance, octant triangles
as template pieces, and lattice sites off rays and square boundaries.

Digest `digest/11-geometry.md` D11.14, D11.15, D11.16, D11.18 -/

open Metric Set

namespace AreaLaw.Geometry

/-! ## Octant stars -/

/-- D11.13. The closed octant `k` at the origin: directions between `kπ/4` and `(k+1)π/4`. -/
def octantCone : Fin 8 → Set (ℝ × ℝ)
  | 0 => {p | 0 ≤ p.2 ∧ p.2 ≤ p.1}
  | 1 => {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  | 2 => {p | 0 ≤ -p.1 ∧ -p.1 ≤ p.2}
  | 3 => {p | 0 ≤ p.2 ∧ p.2 ≤ -p.1}
  | 4 => {p | 0 ≤ -p.2 ∧ -p.2 ≤ -p.1}
  | 5 => {p | 0 ≤ -p.1 ∧ -p.1 ≤ -p.2}
  | 6 => {p | 0 ≤ p.1 ∧ p.1 ≤ -p.2}
  | 7 => {p | 0 ≤ -p.2 ∧ -p.2 ≤ p.1}

/-- The closed octant `k` about `v`. -/
def octantConeAt (v : ℝ × ℝ) (k : Fin 8) : Set (ℝ × ℝ) := {x | x - v ∈ octantCone k}

/-- The triangle of octant `k` about `v` in the closed sup-ball of radius `r`. -/
def octantTriangle (v : ℝ × ℝ) (r : ℝ) (k : Fin 8) : Set (ℝ × ℝ) :=
  octantConeAt v k ∩ closedBall v r

/-- The ray at angle `kπ/4`, between octants `k - 1` and `k`. -/
def octantRay : Fin 8 → ℝ × ℝ :=
  ![(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]

/-- D11.14. The nine child marks of `Q_v` sit at `v + d(S) • childOffset o`: centre, corners
and side midpoints. -/
def childOffset (o : Fin 3 × Fin 3) : ℝ × ℝ := ((o.1 : ℝ) - 1, (o.2 : ℝ) - 1)

/-- The child offset at which ray `k` leaves the removal square. -/
def rayChildOffset : Fin 8 → Fin 3 × Fin 3 :=
  ![(2, 1), (2, 2), (1, 2), (0, 2), (0, 1), (0, 0), (1, 0), (2, 0)]

/-- D11.15.3. For the child at offset `o` and an octant `j` about it: the octant about the
centre containing it near the child, and whether it lies inside `Q_v` (`true`). -/
def childOctant (o : Fin 3 × Fin 3) (j : Fin 8) : Fin 8 × Bool :=
  match o with
  | (1, 1) => (j, true)
  | (2, 1) => ![(0, false), (0, false), (0, true), (0, true),
                (7, true), (7, true), (7, false), (7, false)] j
  | (1, 2) => ![(1, false), (1, false), (2, false), (2, false),
                (2, true), (2, true), (1, true), (1, true)] j
  | (0, 1) => ![(3, true), (3, true), (3, false), (3, false),
                (4, false), (4, false), (4, true), (4, true)] j
  | (1, 0) => ![(6, true), (6, true), (5, true), (5, true),
                (5, false), (5, false), (6, false), (6, false)] j
  | (2, 2) => ![(0, false), (1, false), (1, false), (1, false),
                (1, true), (0, true), (0, false), (0, false)] j
  | (0, 2) => ![(2, false), (2, false), (2, false), (3, false),
                (3, false), (3, false), (3, true), (2, true)] j
  | (0, 0) => ![(5, true), (4, true), (4, false), (4, false),
                (4, false), (5, false), (5, false), (5, false)] j
  | (2, 0) => ![(7, false), (7, false), (7, true), (6, true),
                (6, false), (6, false), (6, false), (7, false)] j
  | _ => (j, true)

lemma exists_mem_octantCone (p : ℝ × ℝ) : ∃ k, p ∈ octantCone k := by
  rcases le_total 0 p.1 with h1 | h1 <;> rcases le_total 0 p.2 with h2 | h2 <;>
    rcases le_total p.1 p.2 with h3 | h3 <;> rcases le_total (-p.1) p.2 with h4 | h4
  all_goals first
    | (refine ⟨0, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨1, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨2, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨3, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨4, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨5, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨6, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨7, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)

/-- D11.14. The eight octant triangles about `v` cover the closed square. -/
theorem iUnion_octantTriangle (v : ℝ × ℝ) (r : ℝ) : ⋃ k, octantTriangle v r k = closedBall v r :=
  Subset.antisymm (iUnion_subset fun _ => inter_subset_right) fun x hx =>
    let ⟨k, hk⟩ := exists_mem_octantCone (x - v); mem_iUnion.2 ⟨k, hk, hx⟩

lemma octantRay_mem_octantCone (k : Fin 8) {t : ℝ} (ht : 0 ≤ t) :
    t • octantRay k ∈ octantCone k ∧ t • octantRay k ∈ octantCone (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (sub_add_cancel k 1).symm⟩
  rw [add_sub_cancel_right]
  fin_cases j <;> simp [octantRay, octantCone, ht]

lemma childOffset_rayChildOffset (k : Fin 8) : childOffset (rayChildOffset k) = octantRay k := by
  fin_cases k <;> simp [childOffset, rayChildOffset, octantRay] <;> norm_num

lemma norm_childOffset_le (o : Fin 3 × Fin 3) : ‖childOffset o‖ ≤ 1 := by
  obtain ⟨i, j⟩ := o
  rw [Prod.norm_def]
  fin_cases i <;> fin_cases j <;> norm_num [childOffset]

lemma one_le_norm_childOffset_sub {o o' : Fin 3 × Fin 3} (ho : o ≠ o') :
    1 ≤ ‖childOffset o - childOffset o'‖ := by
  obtain ⟨i, j⟩ := o
  obtain ⟨i', j'⟩ := o'
  rw [Prod.norm_def]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    first | exact absurd rfl ho | norm_num [childOffset]

/-- D11.18.5 (angular gap). Points of two non-adjacent octants about `v` are at sup distance
at least half the larger of their distances to `v`. -/
theorem max_dist_le_two_mul_dist_of_not_adjacent {v x y : ℝ × ℝ} {k j : Fin 8}
    (hjk : j ≠ k) (hj : j ≠ k + 1) (hk : k ≠ j + 1)
    (hx : x ∈ octantConeAt v k) (hy : y ∈ octantConeAt v j) :
    max (dist x v) (dist y v) ≤ 2 * dist x y := by
  have hA := abs_le.mp (le_max_left |x.1 - y.1| |x.2 - y.2|)
  have hB := abs_le.mp (le_max_right |x.1 - y.1| |x.2 - y.2|)
  simp only [Prod.dist_eq, Real.dist_eq]
  generalize max |x.1 - y.1| |x.2 - y.2| = M at *
  simp only [octantConeAt, mem_ofPred_eq] at hx hy
  simp only [max_le_iff, abs_le]
  fin_cases k <;> fin_cases j <;> try (simp at hjk hj hk; done)
  all_goals
    simp only [octantCone, mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- D11.18.5 (ray-hit clearance). A point of octant `k + 1` outside the open square of radius
`r`, at distance `≥ r'` from the point where ray `k + 1` leaves it, is at distance `≥ r'/2`
from the triangle of octant `k`; and symmetrically with the roles of `k`, `k + 1` swapped. -/
theorem half_le_dist_of_mem_octantTriangle {v x y : ℝ × ℝ} {r r' : ℝ} {k : Fin 8}
    (hr'r : r' ≤ r) (hyv : r ≤ dist y v)
    (hyc : r' ≤ dist y (v + r • octantRay (k + 1))) :
    (x ∈ octantTriangle v r k → y ∈ octantConeAt v (k + 1) → r' / 2 ≤ dist x y) ∧
    (x ∈ octantTriangle v r (k + 1) → y ∈ octantConeAt v k → r' / 2 ≤ dist x y) := by
  constructor <;> intro hx hy <;> rw [← not_lt] <;> intro hlt <;>
  simp only [octantTriangle, mem_inter_iff, octantConeAt, mem_ofPred_eq,
    mem_closedBall, Prod.dist_eq, Real.dist_eq, max_le_iff, abs_le] at hx hy <;>
  simp only [Prod.dist_eq, Real.dist_eq, le_max_iff, le_abs, max_lt_iff, abs_lt] at hyv hyc hlt <;>
  fin_cases k <;>
    simp only [octantCone, octantRay, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
      mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Matrix.cons_val, Prod.smul_mk, smul_eq_mul,
      mul_one, mul_zero, mul_neg, Prod.fst_add, Prod.snd_add, add_zero] at hx hy hyc <;>
    casesm* _ ∧ _, _ ∨ _ <;> linarith

/-! ### The octants about the nine child marks -/

local macro "child_close" : tactic => `(tactic|
  first
    | (exfalso; linarith)
    | (refine ⟨0, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨1, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨2, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨3, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨4, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨5, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨6, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨7, by decide, ?_⟩; simp only [octantCone, mem_ofPred_eq]; constructor <;> linarith))

set_option hygiene false in
local macro "child_iff " q:term : tactic => `(tactic|
  (rw [abs_le] at h₁ h₂
   obtain ⟨h₁, h₁'⟩ := h₁
   obtain ⟨h₂, h₂'⟩ := h₂
   constructor
   · rintro ⟨hk, hb⟩
     obtain ⟨j, hj⟩ := exists_mem_octantCone $q
     fin_cases k <;> cases b <;>
       simp only [octantCone, mem_ofPred_eq, max_le_iff, abs_le, le_max_iff, le_abs, ↓reduceIte,
          Bool.false_eq_true] at hk hb <;>
       casesm* _ ∧ _ <;>
       try (exfalso; linarith)
     all_goals
       try casesm* _ ∨ _
       try (exfalso; linarith)
     all_goals
       fin_cases j <;>
       simp only [octantCone, mem_ofPred_eq] at hj <;>
       casesm* _ ∧ _ <;>
       child_close
   · rintro ⟨j, hj, hjx⟩
     fin_cases k <;> cases b <;> fin_cases j <;> try (exfalso; revert hj; decide)
     all_goals
       simp only [octantCone, mem_ofPred_eq, max_le_iff, abs_le, le_max_iff, le_abs, ↓reduceIte,
          Bool.false_eq_true] at hjx ⊢
       casesm* _ ∧ _
       refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
         first
           | linarith
           | (refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
           | (left; left; linarith)
           | (left; right; linarith)
           | (right; left; linarith)
           | (right; right; linarith)))

/-- The child-octant table in coordinates `(p₁, p₂) = x - v`. -/
abbrev ChildIff (o : Fin 3 × Fin 3) : Prop :=
  ∀ {p₁ p₂ r ρ : ℝ}, 0 ≤ ρ → 2 * ρ < r → |p₁ - (childOffset o).1 * r| ≤ ρ →
    |p₂ - (childOffset o).2 * r| ≤ ρ → ∀ (k : Fin 8) (b : Bool), ((p₁, p₂) ∈ octantCone k ∧
        (if b then max |p₁| |p₂| ≤ r else r ≤ max |p₁| |p₂|)) ↔
      ∃ j, childOctant o j = (k, b) ∧
        (p₁ - (childOffset o).1 * r, p₂ - (childOffset o).2 * r) ∈ octantCone j

lemma childIff_00 : ChildIff (0, 0) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (0, 0) = (-1, -1) by norm_num [childOffset]] at *
  simp only [neg_mul, one_mul, sub_neg_eq_add] at *
  child_iff (p₁ + r, p₂ + r)
lemma childIff_01 : ChildIff (0, 1) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (0, 1) = (-1, 0) by norm_num [childOffset]] at *
  simp only [neg_mul, one_mul, zero_mul, sub_zero, sub_neg_eq_add] at *
  child_iff (p₁ + r, p₂)
lemma childIff_02 : ChildIff (0, 2) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (0, 2) = (-1, 1) by norm_num [childOffset]] at *
  simp only [neg_mul, one_mul, sub_neg_eq_add] at *
  child_iff (p₁ + r, p₂ - r)
lemma childIff_10 : ChildIff (1, 0) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (1, 0) = (0, -1) by norm_num [childOffset]] at *
  simp only [neg_mul, one_mul, zero_mul, sub_zero, sub_neg_eq_add] at *
  child_iff (p₁, p₂ + r)
lemma childIff_11 : ChildIff (1, 1) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (1, 1) = (0, 0) by norm_num [childOffset]] at *
  simp only [zero_mul, sub_zero] at *
  child_iff (p₁, p₂)
lemma childIff_12 : ChildIff (1, 2) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (1, 2) = (0, 1) by norm_num [childOffset]] at *
  simp only [one_mul, zero_mul, sub_zero] at *
  child_iff (p₁, p₂ - r)
lemma childIff_20 : ChildIff (2, 0) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (2, 0) = (1, -1) by norm_num [childOffset]] at *
  simp only [neg_mul, one_mul, sub_neg_eq_add] at *
  child_iff (p₁ - r, p₂ + r)
lemma childIff_21 : ChildIff (2, 1) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (2, 1) = (1, 0) by norm_num [childOffset]] at *
  simp only [one_mul, zero_mul, sub_zero] at *
  child_iff (p₁ - r, p₂)
lemma childIff_22 : ChildIff (2, 2) := by
  intro p₁ p₂ r ρ hρ hρr h₁ h₂ k b
  rw [show childOffset (2, 2) = (1, 1) by norm_num [childOffset]] at *
  simp only [one_mul] at *
  child_iff (p₁ - r, p₂ - r)

/-- D11.15.3. Near the child `c = v + r • childOffset o` of `Q_v = v + [-r, r]²`, within
sup-distance `ρ < r/2` of `c`, a point lies in octant `k` about `v` inside the closed square
(`b = true`), resp. outside the open square (`b = false`), iff it lies in an octant `j` about
`c` with `childOctant o j = (k, b)`. -/
theorem mem_octantConeAt_child_iff {v x : ℝ × ℝ} {r ρ : ℝ} (o : Fin 3 × Fin 3)
    (hρ : 0 ≤ ρ) (hρr : 2 * ρ < r) (hx : x ∈ closedBall (v + r • childOffset o) ρ)
    (k : Fin 8) (b : Bool) :
    (x ∈ octantConeAt v k ∧ (if b then x ∈ closedBall v r else x ∉ ball v r)) ↔
      ∃ j, childOctant o j = (k, b) ∧ x ∈ octantConeAt (v + r • childOffset o) j := by
  have e : ∀ j, x ∈ octantConeAt (v + r • childOffset o) j ↔
      ((x - v).1 - (childOffset o).1 * r, (x - v).2 - (childOffset o).2 * r) ∈ octantCone j :=
    fun j => by
      simp only [octantConeAt, mem_ofPred_eq]
      convert Iff.rfl using 2; ext <;> simp <;> ring
  have hif : (if b then x ∈ closedBall v r else x ∉ ball v r) ↔
      (if b then max |(x - v).1| |(x - v).2| ≤ r else r ≤ max |(x - v).1| |(x - v).2|) := by
    cases b <;> simp only [mem_closedBall, mem_ball, not_lt, Prod.dist_eq, Real.dist_eq,
      Prod.fst_sub, Prod.snd_sub, ↓reduceIte, Bool.false_eq_true]
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hx
  obtain ⟨h₁, h₂⟩ := hx
  rw [show x.1 - (v + r • childOffset o).1 = (x - v).1 - (childOffset o).1 * r by simp; ring]
    at h₁
  rw [show x.2 - (v + r • childOffset o).2 = (x - v).2 - (childOffset o).2 * r by simp; ring]
    at h₂
  rw [show x ∈ octantConeAt v k ↔ ((x - v).1, (x - v).2) ∈ octantCone k from Iff.rfl, hif]
  simp only [e]
  obtain ⟨i, j⟩ := o
  fin_cases i <;> fin_cases j
  exacts [childIff_00 hρ hρr h₁ h₂ k b, childIff_01 hρ hρr h₁ h₂ k b,
    childIff_02 hρ hρr h₁ h₂ k b, childIff_10 hρ hρr h₁ h₂ k b, childIff_11 hρ hρr h₁ h₂ k b,
    childIff_12 hρ hρr h₁ h₂ k b, childIff_20 hρ hρr h₁ h₂ k b, childIff_21 hρ hρr h₁ h₂ k b,
    childIff_22 hρ hρr h₁ h₂ k b]

/-- D11.15.2. Consecutive octants about a child come from one parent octant on opposite sides
of `∂Q_v`, or from adjacent parent octants on the same side. -/
lemma childOctant_succ (o : Fin 3 × Fin 3) (j : Fin 8) :
    childOctant o (j + 1) = childOctant o j ∨
      ((childOctant o (j + 1)).1 = (childOctant o j).1 ∧
        (childOctant o (j + 1)).2 ≠ (childOctant o j).2) ∨
      ((childOctant o (j + 1)).2 = (childOctant o j).2 ∧
        ((childOctant o (j + 1)).1 = (childOctant o j).1 + 1 ∨
          (childOctant o j).1 = (childOctant o (j + 1)).1 + 1)) := by
  revert o j; decide


/-! ### Octant triangles are template pieces -/

lemma convex_octantConeAt (v : ℝ × ℝ) (k : Fin 8) : Convex ℝ (octantConeAt v k) := by
  intro x hx y hy a b ha hb hab
  have e : a • x + b • y - v = a • (x - v) + b • (y - v) := by
    calc a • x + b • y - v = a • x + b • y - (a + b) • v := by rw [hab, one_smul]
      _ = _ := by rw [add_smul, smul_sub, smul_sub]; abel
  simp only [octantConeAt, mem_ofPred_eq] at hx hy ⊢
  rw [e]
  generalize x - v = p at *
  generalize y - v = q at *
  fin_cases k <;>
    simp only [octantCone, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hx hy ⊢ <;>
    obtain ⟨hx₁, hx₂⟩ := hx <;> obtain ⟨hy₁, hy₂⟩ := hy <;>
    constructor <;>
    nlinarith [mul_nonneg ha hx₁, mul_nonneg hb hy₁, mul_nonneg ha (sub_nonneg.2 hx₂),
      mul_nonneg hb (sub_nonneg.2 hy₂)]

lemma exists_eq_smul_octantRay_add_smul {p : ℝ × ℝ} {r : ℝ} {k : Fin 8}
    (hp : p ∈ octantCone k) (hr : max |p.1| |p.2| ≤ r) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ r ∧ p = α • octantRay k + β • octantRay (k + 1) := by
  rw [max_le_iff, abs_le, abs_le] at hr
  obtain ⟨⟨h₃, h₄⟩, h₅, h₆⟩ := hr
  refine ⟨p.1 * (octantRay (k + 1)).2 - p.2 * (octantRay (k + 1)).1,
    (octantRay k).1 * p.2 - (octantRay k).2 * p.1, ?_, ?_, ?_, Prod.ext ?_ ?_⟩ <;>
    fin_cases k <;> simp only [octantCone, mem_ofPred_eq] at hp <;>
    obtain ⟨h₁, h₂⟩ := hp <;> simp [octantRay] <;> linarith

lemma dist_add_smul_octantRay (v : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) (k : Fin 8) :
    dist (v + r • octantRay k) v = r := by
  fin_cases k <;> simp [octantRay, abs_of_nonneg hr, hr]

lemma octantTriangle_eq_convexHull (v : ℝ × ℝ) {r : ℝ} (hr : 0 < r) (k : Fin 8) :
    octantTriangle v r k = convexHull ℝ {v, v + r • octantRay k, v + r • octantRay (k + 1)} := by
  refine Subset.antisymm (fun x ⟨hx, hxr⟩ => ?_) (convexHull_min ?_
    ((convex_octantConeAt v k).inter (convex_closedBall v r)))
  · rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, ← Prod.fst_sub,
      ← Prod.snd_sub] at hxr
    obtain ⟨α, β, hα, hβ, hαβ, hp⟩ := exists_eq_smul_octantRay_add_smul hx hxr
    have hx' : x = ∑ i, ![1 - (α + β) / r, α / r, β / r] i •
        ![v, v + r • octantRay k, v + r • octantRay (k + 1)] i := by
      rw [show x = v + (α • octantRay k + β • octantRay (k + 1)) by rw [← hp]; abel]
      ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring
    rw [hx']
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_
      (fun i _ => subset_convexHull ℝ _ ?_)
    · fin_cases i
      exacts [sub_nonneg.2 ((div_le_one hr).2 hαβ), div_nonneg hα hr.le, div_nonneg hβ hr.le]
    · simp [Fin.sum_univ_three]; field_simp; ring
    · fin_cases i <;> simp
  · simp only [insert_subset_iff, singleton_subset_iff]
    refine ⟨⟨?_, mem_closedBall_self hr.le⟩, ⟨?_, (dist_add_smul_octantRay v hr.le k).le⟩,
      ⟨?_, (dist_add_smul_octantRay v hr.le (k + 1)).le⟩⟩
    · simpa [octantConeAt] using (octantRay_mem_octantCone k le_rfl).1
    · simpa [octantConeAt] using (octantRay_mem_octantCone k hr.le).1
    · simpa [octantConeAt] using (octantRay_mem_octantCone (k + 1) hr.le).2

/-- D11.14. A sector of `Q_v` is a union of the triangles centre–corner/midpoint; each such
triangle is a template piece of sup-diameter at most the halfside, so replacement birth
regions keep the finite description.
2D only: planar triangles with sides of slope `0, ∞, ±1`. -/
theorem octantTriangle_isTemplatePiece (v : ℝ × ℝ) {r : ℝ} (hr : 0 < r) (k : Fin 8) :
    OpenAI.IsTemplatePiece (octantTriangle v r k) ∧
      ediam (octantTriangle v r k) ≤ ENNReal.ofReal r := by
  refine ⟨Or.inr ⟨v, v + r • octantRay k, v + r • octantRay (k + 1), ?_, ?_, ?_, ?_,
    octantTriangle_eq_convexHull v hr k⟩, ediam_le fun x ⟨hx, hxr⟩ y ⟨hy, hyr⟩ => ?_⟩
  · have h : (octantRay k).1 * (octantRay (k + 1)).2 -
        (octantRay k).2 * (octantRay (k + 1)).1 = 1 := by fin_cases k <;> simp [octantRay]
    simp only [add_sub_cancel_left, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [show r * (octantRay k).1 * (r * (octantRay (k + 1)).2) -
        r * (octantRay k).2 * (r * (octantRay (k + 1)).1) = r ^ 2 by linear_combination r ^ 2 * h]
    positivity
  all_goals try (fin_cases k <;> simp [OpenAI.HasTemplateSlope, octantRay])
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [octantConeAt, mem_ofPred_eq] at hx hy
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff, abs_le,
    abs_le] at hxr hyr
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff, abs_le, abs_le]
  fin_cases k <;>
    simp only [octantCone, mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub] at hx hy <;>
    casesm* _ ∧ _ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### Lattice sites avoid rays and square boundaries -/

/-- The lattice site `z ∈ ℤ²` as a point of the plane. -/
def latticePoint (z : ℤ × ℤ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

/-- D11.5. The origin `o` has `o₁, o₂, o₁ + o₂, o₁ - o₂` irrational. -/
def IsIrrationalOrigin (o : ℝ × ℝ) : Prop :=
  Irrational o.1 ∧ Irrational o.2 ∧ Irrational (o.1 + o.2) ∧ Irrational (o.1 - o.2)

/-- D11.5. `o = (√2, √3)` is an irrational origin. -/
lemma isIrrationalOrigin_o₂ : IsIrrationalOrigin (o₂ 0, o₂ 1) :=
  ⟨o₂_irrational.1 0, o₂_irrational.1 1, (o₂_irrational.2 0 1 (by decide)).1,
    (o₂_irrational.2 0 1 (by decide)).2⟩

/-- D11.16.3. A lattice site lies in at most one closed octant about a point of `o + ℤ²`. -/
theorem eq_of_latticePoint_mem_octantConeAt {o : ℝ × ℝ} (ho : IsIrrationalOrigin o)
    {a z : ℤ × ℤ} {k j : Fin 8} (hk : latticePoint z ∈ octantConeAt (o + latticePoint a) k)
    (hj : latticePoint z ∈ octantConeAt (o + latticePoint a) j) : k = j := by
  obtain ⟨h1, h2, h3, h4⟩ := ho
  have e1 := h1.ne_int (z.1 - a.1)
  have e2 := h2.ne_int (z.2 - a.2)
  have e3 := h3.ne_int (z.1 + z.2 - a.1 - a.2)
  have e4 := h4.ne_int (z.1 - z.2 - a.1 + a.2)
  push_cast at e1 e2 e3 e4
  simp only [octantConeAt, mem_ofPred_eq, latticePoint] at hk hj
  fin_cases k <;> fin_cases j <;>
    simp only [octantCone, mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add,
      Prod.snd_add] at hk hj <;>
    first
      | rfl
      | exfalso
        first
          | exact e1 (by linarith)
          | exact e2 (by linarith)
          | exact e3 (by linarith)
          | exact e4 (by linarith)

/-- D11.16.2–3. No lattice site lies on the boundary of an integer-halfside square centred in
`o + ℤ²`. -/
theorem dist_latticePoint_ne_natCast {o : ℝ × ℝ} (ho : IsIrrationalOrigin o) (a z : ℤ × ℤ)
    (n : ℕ) : dist (latticePoint z) (o + latticePoint a) ≠ n := by
  intro h
  simp only [Prod.dist_eq, Real.dist_eq, latticePoint, Prod.fst_add, Prod.snd_add] at h
  rcases max_choice |(z.1 : ℝ) - (o.1 + a.1)| |(z.2 : ℝ) - (o.2 + a.2)| with hm | hm <;>
    rw [hm, abs_eq (Nat.cast_nonneg n)] at h
  · rcases h with h | h
    · exact ho.1.ne_int (z.1 - a.1 - n) (by push_cast; linarith)
    · exact ho.1.ne_int (z.1 - a.1 + n) (by push_cast; linarith)
  · rcases h with h | h
    · exact ho.2.1.ne_int (z.2 - a.2 - n) (by push_cast; linarith)
    · exact ho.2.1.ne_int (z.2 - a.2 + n) (by push_cast; linarith)

end AreaLaw.Geometry
