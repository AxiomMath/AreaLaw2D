import AreaLawRefactored.S11_Geometry.Repairs

/-! # §11.5 Removing point contacts at successively smaller scales: the recursion

The repair rule run over abstract initial marks, the uniform repair induction (Lemma 11.4), the
lattice partition after repair, the replacement half of Lemma 11.5 and the replacement half of
the descendant count.

Digest `digest/11-geometry.md` D11.14, D11.15, D11.16, D11.18, D11.19 -/

open Metric Set Real

namespace AreaLaw.Geometry

/-! ## D11.14 The repair rule -/

/-- D11.14. A mark: its initial mark `root` and the child offsets leading to it, newest first;
the generation is the length of the path. -/
structure Mark (M₀ : Type*) where
  /-- The initial mark it descends from. -/
  root : M₀
  /-- The child offsets, newest first. -/
  path : List (Fin 3 × Fin 3)

namespace Mark

variable {M₀ : Type*}

/-- The generation of a mark. -/
def gen (m : Mark M₀) : ℕ := m.path.length

/-- The child of `m` at offset `o` of `Q_v`. -/
def child (m : Mark M₀) (o : Fin 3 × Fin 3) : Mark M₀ := ⟨m.root, o :: m.path⟩

/-- The descendant of `m` along the further offsets `q`, newest first. -/
def descend (m : Mark M₀) (q : List (Fin 3 × Fin 3)) : Mark M₀ := ⟨m.root, q ++ m.path⟩

@[simp] lemma gen_child (m : Mark M₀) (o : Fin 3 × Fin 3) : (m.child o).gen = m.gen + 1 := by
  simp [gen, child]

end Mark

/-- D11.14. The repair data, the output of Lemma 11.3: initial marks `M₀` with positions `v₀`,
scales `S₀` and the tile identifiers `oct₀` of the eight octants of their stars; initial tile
identifiers `I` with labels `label₀` and closed birth regions `birth₀`; the stopping scale `S_*`
and the star constant `a₀`. -/
structure Repair (I M₀ : Type*) where
  /-- Position of an initial mark. -/
  v₀ : M₀ → ℝ × ℝ
  /-- Scale of an initial mark. -/
  S₀ : M₀ → ℝ
  /-- The initial identifier of each octant of an initial star. -/
  oct₀ : M₀ → Fin 8 → I
  /-- Label of an initial identifier. -/
  label₀ : I → Fin 2
  /-- Closed birth region of an initial identifier. -/
  birth₀ : I → Set (ℝ × ℝ)
  /-- The stopping scale `S_*`. -/
  S_star : ℝ
  /-- The star constant `a₀`. -/
  a₀ : ℝ

/-- D11.14. Tile identifiers: the initial ones, and the replacement `repl m a` filling the
sectors of `Q_v` (`v` the position of `m`) whose exterior identifier is `a`. -/
inductive TileId (I M₀ : Type*) where
  | init : I → TileId I M₀
  | repl : Mark M₀ → TileId I M₀ → TileId I M₀

/-- The generation of birth: replacements at the mark `m` are born at generation `m.gen + 1`. -/
def TileId.birthGen {I M₀ : Type*} : TileId I M₀ → ℕ
  | .init _ => 0
  | .repl m _ => m.gen + 1

namespace Repair

variable {I M₀ : Type*} (R : Repair I M₀)

/-- D11.14. The scale of a mark: `S_{j+1} = d(S_j)` along the path. -/
noncomputable def S (m : Mark M₀) : ℝ := d^[m.gen] (R.S₀ m.root)

/-- Position of the mark with root `r` and path `p`. -/
noncomputable def pathPos (r : M₀) : List (Fin 3 × Fin 3) → ℝ × ℝ
  | [] => R.v₀ r
  | o :: p => pathPos r p + d (d^[p.length] (R.S₀ r)) • childOffset o

/-- D11.14. The position `v` of a mark. -/
noncomputable def v (m : Mark M₀) : ℝ × ℝ := R.pathPos m.root m.path

/-- D11.14. The active marks: initial marks, and children of marks `(v, S)` with
`d(S) ≥ S_*`. -/
def IsMark (m : Mark M₀) : Prop := m.path = [] ∨ R.S_star ≤ R.S m

/-- D11.14. A mark is nonterminal when `d(S) ≥ S_*`. -/
def IsNonterminal (m : Mark M₀) : Prop := R.S_star ≤ d (R.S m)

/-- D11.14. The label: a replacement has the label opposite to its exterior sector. -/
def label : TileId I M₀ → Fin 2
  | .init i => R.label₀ i
  | .repl _ a => label a + 1

/-- The identifiers in the octants of the star of the mark with root `r` and path `p`. -/
def markOctPath (r : M₀) : List (Fin 3 × Fin 3) → Fin 8 → TileId I M₀
  | [], k => .init (R.oct₀ r k)
  | o :: p, j =>
      if (childOctant o j).2 then .repl ⟨r, p⟩ (markOctPath r p (childOctant o j).1)
      else markOctPath r p (childOctant o j).1

/-- D11.14. The identifier of octant `k` of the star of `m`, at the generation of `m`. -/
def markOct (m : Mark M₀) : Fin 8 → TileId I M₀ := R.markOctPath m.root m.path

/-- D11.14. Fix `S_*` so large that for all `S ≥ S_*`, `d(S) = 2^{⌊ρ₀ log₂ S⌋}` satisfies
`½S^{ρ₀} ≤ d(S) ≤ S^{ρ₀}`, `d(S) ≤ (a₀/1000)S`. Take `k₀` with all initial mark scales `≥ S_*`.
At every generation, simultaneously at every active mark `(v, S)`:
1. remove the closed square `Q_v = v + [−d(S), d(S)]²` from every old tile identifier;
2. if `d(S) < S_*`: leave the interior unassigned; terminal exceptional square;
3. else continue the incident active rays through `Q_v` to its centre; in each sector the new
region gets the label opposite to the corresponding exterior sector, with a new identifier per
sector (no rays: one opposite-label square); mark centre, corners and side midpoints of `Q_v`,
all at scale `d(S)`, for the next generation.
A sector of angle `> π` is a union of `≤ 8` of the triangles centre–corner/midpoint, so
replacement birth regions keep the finite description. Every old ray meets `∂Q_v` at a corner or
side midpoint.
2D only: eight rays and nine child marks of a planar point contact. -/
def birthRegion : TileId I M₀ → Set (ℝ × ℝ)
  | .init i => R.birth₀ i
  | .repl m a => {x | R.IsMark m ∧ R.IsNonterminal m ∧
      ∃ k, R.markOct m k = a ∧ x ∈ octantTriangle (R.v m) (d (R.S m)) k}

/-- D11.14. The region of an identifier just before the removals of generation `g`. -/
def currentRegion (g : ℕ) (a : TileId I M₀) : Set (ℝ × ℝ) :=
  R.birthRegion a \ ⋃ (m : Mark M₀) (_ : R.IsMark m ∧ a.birthGen ≤ m.gen ∧ m.gen < g),
    ball (R.v m) (d (R.S m))

/-- D11.14. The final region: the birth region minus every later removal square. -/
def finalRegion (a : TileId I M₀) : Set (ℝ × ℝ) :=
  R.birthRegion a \ ⋃ (m : Mark M₀) (_ : R.IsMark m ∧ a.birthGen ≤ m.gen),
    ball (R.v m) (d (R.S m))

/-- D11.13, D11.14. The hypotheses of the repair, i.e. the output of Lemma 11.3 and the choice of
`S_*`: `0 < a₀ < ½`; `S_* ≥ 2` with `d(S) ≤ (a₀/1000)S` for `S ≥ S_*`; initial scales `≥ S_*`;
distinct initial marks `‖v − w‖_∞ ≥ a₀ max(S_v, S_w)`; in `v + [−a₀S, a₀S]²` every initial
birth region is the union of its octants; consecutive distinct octant identifiers have opposite
labels. -/
structure Hyp : Prop where
  a₀_pos : 0 < R.a₀
  a₀_lt : R.a₀ < 1 / 2
  two_le_S_star : 2 ≤ R.S_star
  margin : ∀ S, R.S_star ≤ S → d S ≤ R.a₀ / 1000 * S
  S_star_le_S₀ : ∀ r, R.S_star ≤ R.S₀ r
  sep₀ : ∀ r r', r ≠ r' → R.a₀ * max (R.S₀ r) (R.S₀ r') ≤ dist (R.v₀ r) (R.v₀ r')
  star₀ : ∀ r i, R.birth₀ i ∩ closedBall (R.v₀ r) (R.a₀ * R.S₀ r) =
    ⋃ (k : Fin 8) (_ : R.oct₀ r k = i), octantConeAt (R.v₀ r) k ∩
      closedBall (R.v₀ r) (R.a₀ * R.S₀ r)
  label₀_ne : ∀ r (k : Fin 8), R.oct₀ r k ≠ R.oct₀ r (k + 1) →
    R.label₀ (R.oct₀ r k) ≠ R.label₀ (R.oct₀ r (k + 1))

variable {R}

@[simp] lemma S_child (m : Mark M₀) (o : Fin 3 × Fin 3) : R.S (m.child o) = d (R.S m) := by
  simp [S, Mark.child, Mark.gen, Function.iterate_succ_apply']

@[simp] lemma v_child (m : Mark M₀) (o : Fin 3 × Fin 3) :
    R.v (m.child o) = R.v m + d (R.S m) • childOffset o := rfl

@[simp] lemma markOct_child (m : Mark M₀) (o : Fin 3 × Fin 3) (j : Fin 8) :
    R.markOct (m.child o) j = if (childOctant o j).2 then .repl m (R.markOct m (childOctant o j).1)
      else R.markOct m (childOctant o j).1 := rfl

lemma dist_v_child_le (R : Repair I M₀) (m : Mark M₀) (o : Fin 3 × Fin 3) :
    dist (R.v (m.child o)) (R.v m) ≤ d (R.S m) := by
  rw [v_child, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_of_nonneg (d_pos _).le]
  exact mul_le_of_le_one_right (d_pos _).le (norm_childOffset_le o)

lemma d_le_dist_v_child (R : Repair I M₀) (m : Mark M₀) {o o' : Fin 3 × Fin 3} (ho : o ≠ o') :
    d (R.S m) ≤ dist (R.v (m.child o)) (R.v (m.child o')) := by
  rw [v_child, v_child, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    norm_of_nonneg (d_pos _).le]
  exact le_mul_of_one_le_right (d_pos _).le (one_le_norm_childOffset_sub ho)

namespace Hyp

variable (hR : R.Hyp)
include hR

lemma S_pos (m : Mark M₀) : 0 < R.S m := by
  unfold S
  rcases Nat.eq_zero_or_eq_succ_pred m.gen with h | h
  · rw [h]; exact lt_of_lt_of_le (by linarith [hR.two_le_S_star]) (hR.S_star_le_S₀ m.root)
  · rw [h, Function.iterate_succ_apply']; exact d_pos _

lemma S_star_le_S {m : Mark M₀} (hm : R.IsMark m) : R.S_star ≤ R.S m := by
  rcases hm with h | h
  · simpa [S, Mark.gen, h] using hR.S_star_le_S₀ m.root
  · exact h

lemma d_le {m : Mark M₀} (hm : R.IsMark m) : d (R.S m) ≤ R.a₀ / 1000 * R.S m :=
  hR.margin _ (hR.S_star_le_S hm)

/-- D11.16.2. `d(S)` is a power of two, in particular an integer. -/
lemma exists_d_eq_pow {m : Mark M₀} (hm : R.IsMark m) : ∃ n : ℕ, d (R.S m) = 2 ^ n :=
  ⟨_, d_eq_two_pow (by linarith [hR.S_star_le_S hm, hR.two_le_S_star])⟩

lemma isMark_child_iff (m : Mark M₀) (o : Fin 3 × Fin 3) :
    R.IsMark (m.child o) ↔ R.IsMark m ∧ R.IsNonterminal m := by
  have hc : R.IsMark (m.child o) ↔ R.IsNonterminal m := by
    unfold IsMark IsNonterminal; rw [S_child]; simp [Mark.child]
  rw [hc]
  refine ⟨fun h => ⟨Or.inr ?_, h⟩, fun h => h.2⟩
  have hS := hR.S_pos m
  have h1 := (step_11_14_1 hS).2
  rcases le_or_gt (R.S m) 1 with h2 | h2
  · have h3 : R.S m ^ ρ₀ ≤ 1 := rpow_le_one hS.le h2 ρ₀_pos.le
    have h4 : R.S_star ≤ d (R.S m) := h
    linarith [hR.two_le_S_star]
  · calc R.S_star ≤ R.S m ^ ρ₀ := h.trans h1
      _ ≤ R.S m ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le h2.le eq_exponent_gaps.2.2.2.2.2.le
      _ = R.S m := rpow_one _

/-- D11.15.4. Distinct active marks of one generation have `‖v − w‖_∞ ≥ a₀ max(S, T)`. -/
theorem step_11_15_4 {m m' : Mark M₀} (hm : R.IsMark m) (hm' : R.IsMark m') (hne : m ≠ m')
    (hgen : m.gen = m'.gen) : R.a₀ * max (R.S m) (R.S m') ≤ dist (R.v m) (R.v m') := by
  obtain ⟨r, p⟩ := m
  obtain ⟨r', p'⟩ := m'
  induction p generalizing r' p' with
  | nil =>
    obtain rfl : p' = [] := List.eq_nil_of_length_eq_zero (by simpa [Mark.gen] using hgen.symm)
    exact hR.sep₀ r r' fun h => hne (h ▸ rfl)
  | cons o p ih =>
    obtain _ | ⟨o', p'⟩ := p'
    · simp [Mark.gen] at hgen
    change R.IsMark ((⟨r, p⟩ : Mark M₀).child o) at hm
    change R.IsMark ((⟨r', p'⟩ : Mark M₀).child o') at hm'
    change R.a₀ * max (R.S ((⟨r, p⟩ : Mark M₀).child o)) (R.S ((⟨r', p'⟩ : Mark M₀).child o')) ≤
      dist (R.v ((⟨r, p⟩ : Mark M₀).child o)) (R.v ((⟨r', p'⟩ : Mark M₀).child o'))
    obtain ⟨hP, -⟩ := (hR.isMark_child_iff _ o).1 hm
    obtain ⟨hP', -⟩ := (hR.isMark_child_iff _ o').1 hm'
    rw [S_child, S_child]
    have ha₀ := hR.a₀_pos
    have ha₁ := hR.a₀_lt
    have h0 := d_pos (R.S ⟨r, p⟩)
    have h0' := d_pos (R.S ⟨r', p'⟩)
    by_cases hPP : (⟨r, p⟩ : Mark M₀) = ⟨r', p'⟩
    · obtain ⟨rfl, rfl⟩ : r = r' ∧ p = p' := by simpa using hPP
      have := R.d_le_dist_v_child ⟨r, p⟩ (o := o) (o' := o') fun h => hne (h ▸ rfl)
      rw [max_self]; nlinarith
    · have hIH := ih hP r' p' hP' hPP (by simpa [Mark.gen] using hgen)
      have h4 := dist_triangle4 (R.v ⟨r, p⟩) (R.v (Mark.child ⟨r, p⟩ o))
        (R.v (Mark.child ⟨r', p'⟩ o')) (R.v ⟨r', p'⟩)
      rw [dist_comm (R.v ⟨r, p⟩) (R.v (Mark.child ⟨r, p⟩ o))] at h4
      set M := max (R.S ⟨r, p⟩) (R.S ⟨r', p'⟩)
      have hd := (hR.d_le hP).trans (mul_le_mul_of_nonneg_left
        (le_max_left _ _ : R.S ⟨r, p⟩ ≤ M) (by positivity))
      have hd' := (hR.d_le hP').trans (mul_le_mul_of_nonneg_left
        (le_max_right _ _ : R.S ⟨r', p'⟩ ≤ M) (by positivity))
      have hmax := max_le hd hd'
      have hm0 := le_max_left (d (R.S ⟨r, p⟩)) (d (R.S ⟨r', p'⟩))
      have hX : R.a₀ / 1000 * M = R.a₀ * M / 1000 := by ring
      have : R.a₀ * max (d (R.S ⟨r, p⟩)) (d (R.S ⟨r', p'⟩)) ≤
          max (d (R.S ⟨r, p⟩)) (d (R.S ⟨r', p'⟩)) := by nlinarith
      linarith [R.dist_v_child_le ⟨r, p⟩ o, R.dist_v_child_le ⟨r', p'⟩ o']

/-- D11.15.1. The star of a child of `m` lies in the star of `m`, and misses the closed removal
square of every other active mark of the generation of `m`. -/
theorem step_11_15_1 {m : Mark M₀} {o : Fin 3 × Fin 3} (hc : R.IsMark (m.child o)) {x : ℝ × ℝ}
    (hx : x ∈ closedBall (R.v (m.child o)) (R.a₀ * R.S (m.child o))) :
    x ∈ closedBall (R.v m) (R.a₀ * R.S m) ∧ ∀ m', R.IsMark m' → m' ≠ m → m'.gen = m.gen →
      d (R.S m') < dist x (R.v m') := by
  obtain ⟨hm, -⟩ := (hR.isMark_child_iff m o).1 hc
  rw [S_child, mem_closedBall] at hx
  have h1 := R.dist_v_child_le m o
  have h2 := hR.d_le hm
  have h3 := hR.S_star_le_S hm
  have h4 := hR.two_le_S_star
  have h5 := hR.a₀_pos
  have h6 := hR.a₀_lt
  have h7 := d_pos (R.S m)
  have h8 : R.a₀ * d (R.S m) ≤ 1 / 2 * d (R.S m) := by nlinarith
  have ht := dist_triangle x (R.v (m.child o)) (R.v m)
  refine ⟨by rw [mem_closedBall]; nlinarith, fun m' hm' hne hgen => ?_⟩
  have h0 := hR.step_11_15_4 hm hm' hne.symm hgen.symm
  have h2' := hR.d_le hm'
  have hM := le_max_left (R.S m) (R.S m')
  have hM' := le_max_right (R.S m) (R.S m')
  have h10 := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ R.a₀ / 1000)
  have h11 := mul_le_mul_of_nonneg_left hM' (by positivity : 0 ≤ R.a₀ / 1000)
  have ht1 := dist_triangle (R.v m) x (R.v m')
  rw [dist_comm] at ht
  nlinarith

end Hyp

lemma birthGen_markOct_le (m : Mark M₀) (k : Fin 8) : (R.markOct m k).birthGen ≤ m.gen := by
  obtain ⟨r, p⟩ := m
  simp only [markOct, Mark.gen]
  induction p generalizing k with
  | nil => simp [markOctPath, TileId.birthGen]
  | cons o p ih =>
    simp only [markOctPath]
    split_ifs
    · simp [TileId.birthGen, Mark.gen]
    · exact (ih _).trans (by simp)

lemma mem_currentRegion {g : ℕ} {a : TileId I M₀} {x : ℝ × ℝ} :
    x ∈ R.currentRegion g a ↔ x ∈ R.birthRegion a ∧ ∀ m, R.IsMark m → a.birthGen ≤ m.gen →
      m.gen < g → d (R.S m) ≤ dist x (R.v m) := by
  simp [currentRegion]

lemma finalRegion_subset_currentRegion (g : ℕ) (a : TileId I M₀) :
    R.finalRegion a ⊆ R.currentRegion g a := fun _ hx =>
  ⟨hx.1, fun h => hx.2 (by simp only [mem_iUnion] at h ⊢; tauto)⟩

lemma le_dist_of_mem_finalRegion {a : TileId I M₀} {m : Mark M₀} (hm : R.IsMark m)
    (hgen : a.birthGen ≤ m.gen) {y : ℝ × ℝ} (hy : y ∈ R.finalRegion a) :
    d (R.S m) ≤ dist y (R.v m) :=
  not_lt.1 fun h => hy.2 (mem_iUnion₂.2 ⟨m, ⟨hm, hgen⟩, mem_ball.2 h⟩)

lemma birthRegion_repl_subset (m : Mark M₀) (a : TileId I M₀) :
    R.birthRegion (.repl m a) ⊆ closedBall (R.v m) (d (R.S m)) := fun _ ⟨_, _, _, _, hx⟩ => hx.2

lemma markOct_child_eq_iff {m : Mark M₀} {a : TileId I M₀} (ha : a.birthGen ≤ m.gen)
    (o : Fin 3 × Fin 3) (j : Fin 8) : R.markOct (m.child o) j = a ↔
      (childOctant o j).2 = false ∧ R.markOct m (childOctant o j).1 = a := by
  rw [markOct_child]
  split_ifs with h
  · simp only [h, Bool.true_eq_false, false_and, iff_false]
    rintro rfl
    simp [TileId.birthGen] at ha
  · simp [h]

lemma markOct_child_eq_repl_iff {m m' : Mark M₀} (hgen : m'.gen = m.gen) (a : TileId I M₀)
    (o : Fin 3 × Fin 3) (j : Fin 8) : R.markOct (m.child o) j = .repl m' a ↔
      (childOctant o j).2 = true ∧ m = m' ∧ R.markOct m (childOctant o j).1 = a := by
  rw [markOct_child]
  split_ifs with h
  · simp [h]
  · simp only [h, Bool.false_eq_true, false_and, iff_false]
    intro he
    have := R.birthGen_markOct_le m (childOctant o j).1
    rw [he, TileId.birthGen] at this
    omega

lemma inter_eq_iUnion_iff {α ι : Type*} {A B : Set α} {P : ι → Prop} {C : ι → Set α} :
    A ∩ B = ⋃ (k) (_ : P k), C k ∩ B ↔ ∀ x ∈ B, (x ∈ A ↔ ∃ k, P k ∧ x ∈ C k) := by
  simp only [Set.ext_iff, mem_inter_iff, mem_iUnion, exists_prop]
  exact ⟨fun h x hx => by simpa [hx] using h x,
    fun h x => by by_cases hx : x ∈ B <;> simp [hx, h]⟩

lemma exists_childOctant_iff {o : Fin 3 × Fin 3} {b : Bool} {P Q : Fin 8 → Prop} :
    (∃ k, P k ∧ ∃ j, childOctant o j = (k, b) ∧ Q j) ↔
      ∃ j, ((childOctant o j).2 = b ∧ P (childOctant o j).1) ∧ Q j :=
  ⟨fun ⟨_, hk, j, hj, hq⟩ => ⟨j, ⟨by simp [hj], by simpa [hj] using hk⟩, hq⟩,
    fun ⟨j, ⟨hb, hk⟩, hq⟩ => ⟨_, hk, j, Prod.ext rfl hb, hq⟩⟩

namespace Hyp

variable (hR : R.Hyp)
include hR

/-- D11.15.3, the induction step: the star of a child of `m` is read off the star of `m`
through `childOctant`. -/
theorem step_11_15_3 {m : Mark M₀} {o : Fin 3 × Fin 3} (hc : R.IsMark (m.child o))
    (ih : ∀ a : TileId I M₀, a.birthGen ≤ m.gen →
      R.currentRegion m.gen a ∩ closedBall (R.v m) (R.a₀ * R.S m) =
        ⋃ (k : Fin 8) (_ : R.markOct m k = a),
          octantConeAt (R.v m) k ∩ closedBall (R.v m) (R.a₀ * R.S m))
    {a : TileId I M₀} (ha : a.birthGen ≤ (m.child o).gen) :
    R.currentRegion (m.child o).gen a ∩ closedBall (R.v (m.child o)) (R.a₀ * R.S (m.child o)) =
      ⋃ (k : Fin 8) (_ : R.markOct (m.child o) k = a), octantConeAt (R.v (m.child o)) k ∩
        closedBall (R.v (m.child o)) (R.a₀ * R.S (m.child o)) := by
  obtain ⟨hm, hnt⟩ := (hR.isMark_child_iff m o).1 hc
  have hd : 2 ≤ d (R.S m) := hR.two_le_S_star.trans hnt
  have ha0 := hR.a₀_pos
  have ha1 := hR.a₀_lt
  rw [inter_eq_iUnion_iff]
  intro x hx
  obtain ⟨hxm, sep⟩ := hR.step_11_15_1 hc hx
  rw [S_child, v_child] at hx
  have child := fun k b => mem_octantConeAt_child_iff o (by positivity) (by nlinarith) hx k b
  rw [v_child]
  rw [Mark.gen_child] at ha ⊢
  rcases Nat.le_succ_iff.1 ha with ha | ha
  · calc x ∈ R.currentRegion (m.gen + 1) a ↔
          x ∈ R.currentRegion m.gen a ∧ d (R.S m) ≤ dist x (R.v m) := by
          simp only [mem_currentRegion]
          refine ⟨fun ⟨hb, h⟩ => ⟨⟨hb, fun m' hm' h1 h2 => h m' hm' h1 (by omega)⟩,
            h m hm ha (by omega)⟩, fun ⟨⟨hb, h⟩, hmd⟩ => ⟨hb, fun m' hm' h1 h2 => ?_⟩⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
          · exact h m' hm' h1 h2
          · by_cases hne : m' = m
            · exact hne ▸ hmd
            · exact (sep m' hm' hne h2).le
      _ ↔ ∃ k, R.markOct m k = a ∧ ∃ j, childOctant o j = (k, false) ∧
            x ∈ octantConeAt (R.v m + d (R.S m) • childOffset o) j := by
          rw [(inter_eq_iUnion_iff.1 (ih a ha)) x hxm]
          refine ⟨fun ⟨⟨k, hk, hxk⟩, h⟩ => ⟨k, hk, (child k false).1 ⟨hxk, by simpa using h⟩⟩,
            fun ⟨k, hk, hj⟩ => ?_⟩
          obtain ⟨hxk, h⟩ := (child k false).2 hj
          exact ⟨⟨k, hk, hxk⟩, by simpa using h⟩
      _ ↔ _ := by rw [exists_childOctant_iff]; simp only [R.markOct_child_eq_iff ha]
  · obtain _ | ⟨m'', a''⟩ := a
    · simp [TileId.birthGen] at ha
    replace ha : m''.gen = m.gen := by simp only [TileId.birthGen] at ha; omega
    have hcur : x ∈ R.currentRegion (m.gen + 1) (.repl m'' a'') ↔
        x ∈ R.birthRegion (.repl m'' a'') := by
      rw [mem_currentRegion]
      exact ⟨And.left, fun h => ⟨h, fun m' _ h1 h2 => by simp only [TileId.birthGen] at h1; omega⟩⟩
    rw [hcur]
    simp only [R.markOct_child_eq_repl_iff ha]
    by_cases hne : m'' = m
    · subst hne
      calc x ∈ R.birthRegion (.repl m'' a'') ↔ ∃ k, R.markOct m'' k = a'' ∧
            ∃ j, childOctant o j = (k, true) ∧
              x ∈ octantConeAt (R.v m'' + d (R.S m'') • childOffset o) j := by
            simp only [birthRegion, mem_ofPred_eq, hm, hnt, true_and]
            exact exists_congr fun k => and_congr_right fun _ => child k true
        _ ↔ _ := by rw [exists_childOctant_iff]; simp
    · refine ⟨fun ⟨hm'', _, k, _, hxk⟩ => ?_, fun ⟨j, ⟨_, h, _⟩, _⟩ => absurd h.symm hne⟩
      linarith [sep m'' hm'' hne ha, mem_closedBall.1 hxk.2]

/-- D11.15.2. Across every active ray of the star of an active mark the labels are opposite. -/
theorem step_11_15_2 {m : Mark M₀} (hm : R.IsMark m) (k : Fin 8)
    (hk : R.markOct m k ≠ R.markOct m (k + 1)) :
    R.label (R.markOct m k) ≠ R.label (R.markOct m (k + 1)) := by
  have hne : ∀ a : Fin 2, a ≠ a + 1 := by decide
  obtain ⟨r, p⟩ := m
  induction p generalizing k with
  | nil => exact hR.label₀_ne r k fun h => hk (by simp [markOct, markOctPath, h])
  | cons o p ih =>
    have ih' := fun k => ih k ((hR.isMark_child_iff ⟨r, p⟩ o).1 hm).1
    change R.markOct ((⟨r, p⟩ : Mark M₀).child o) k ≠
      R.markOct ((⟨r, p⟩ : Mark M₀).child o) (k + 1) at hk
    change R.label (R.markOct ((⟨r, p⟩ : Mark M₀).child o) k) ≠
      R.label (R.markOct ((⟨r, p⟩ : Mark M₀).child o) (k + 1))
    have key := childOctant_succ o k
    rw [markOct_child, markOct_child] at hk ⊢
    revert key hk
    generalize childOctant o k = c₁
    generalize childOctant o (k + 1) = c₂
    obtain ⟨k₁, _ | _⟩ := c₁ <;> obtain ⟨k₂, _ | _⟩ := c₂ <;> intro hk key <;>
      simp only [Prod.mk.injEq, and_true, true_and, and_false, false_and, or_false, false_or,
        ne_eq, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false,
        ite_true, ite_false, label, TileId.repl.injEq] at key hk ⊢
    · rcases key with rfl | rfl | rfl
      exacts [absurd rfl hk, ih' k₁ hk, fun h => ih' k₂ (Ne.symm hk) h.symm]
    · exact key ▸ hne _
    · exact key ▸ (hne _).symm
    · rcases key with rfl | rfl | rfl
      exacts [absurd rfl hk, fun h => ih' k₁ hk (add_right_cancel h),
        fun h => ih' k₂ (Ne.symm hk) (add_right_cancel h).symm]

/-- D11.15.3 (uniform isolated star). At every active mark `(v, S)`, in `v + [−a₀S, a₀S]²` every
identifier present at its generation occupies exactly its octants of the star of `m`. -/
theorem star {m : Mark M₀} (hm : R.IsMark m) {a : TileId I M₀} (ha : a.birthGen ≤ m.gen) :
    R.currentRegion m.gen a ∩ closedBall (R.v m) (R.a₀ * R.S m) =
      ⋃ (k : Fin 8) (_ : R.markOct m k = a),
        octantConeAt (R.v m) k ∩ closedBall (R.v m) (R.a₀ * R.S m) := by
  obtain ⟨r, p⟩ := m
  induction p generalizing a with
  | nil =>
    obtain ⟨i⟩ | ⟨m', _⟩ := a
    · have hcur : R.currentRegion 0 (.init i) = R.birth₀ i := by
        ext x; simp [mem_currentRegion, birthRegion]
      change R.currentRegion 0 _ ∩ closedBall (R.v₀ r) (R.a₀ * R.S₀ r) =
        ⋃ (k : Fin 8) (_ : TileId.init (R.oct₀ r k) = .init i),
          octantConeAt (R.v₀ r) k ∩ closedBall (R.v₀ r) (R.a₀ * R.S₀ r)
      simp only [hcur, hR.star₀ r i, TileId.init.injEq]
    · simp [TileId.birthGen, Mark.gen] at ha
  | cons o p ih =>
    exact hR.step_11_15_3 (m := ⟨r, p⟩) hm
      (fun a ha => ih ((hR.isMark_child_iff ⟨r, p⟩ o).1 hm).1 ha) ha

/-- D11.15.5. The star of an active mark misses the removal square of every terminal active mark
of an earlier generation. -/
theorem step_11_15_5 {m : Mark M₀} (hm : R.IsMark m) {m' : Mark M₀} (hm' : R.IsMark m')
    (hgen : m'.gen < m.gen) (ht : ¬R.IsNonterminal m') :
    Disjoint (closedBall (R.v m) (R.a₀ * R.S m)) (ball (R.v m') (d (R.S m'))) := by
  obtain ⟨r, p⟩ := m
  induction p with
  | nil => simp [Mark.gen] at hgen
  | cons o p ih =>
    change R.IsMark ((⟨r, p⟩ : Mark M₀).child o) at hm
    change Disjoint (closedBall (R.v ((⟨r, p⟩ : Mark M₀).child o))
      (R.a₀ * R.S ((⟨r, p⟩ : Mark M₀).child o))) _
    obtain ⟨hP, hnt⟩ := (hR.isMark_child_iff _ o).1 hm
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨hxP, sep⟩ := hR.step_11_15_1 hm hx
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show m'.gen < p.length + 1 from hgen) with h | h
    · exact Set.disjoint_left.1 (ih hP h) hxP hx'
    · exact (sep m' hm' (fun e => ht (e ▸ hnt)) h).not_ge (mem_ball'.1 hx' |>.le.trans_eq'
        (dist_comm _ _))

/-- D11.15.6 (displacement). A descendant mark together with its removal square stays within
sup-distance `2d(S)` of its ancestor `(v, S)`. -/
theorem step_11_15_6_marks {m : Mark M₀} (q : List (Fin 3 × Fin 3))
    (hq : R.IsMark (m.descend q)) :
    dist (R.v (m.descend q)) (R.v m) + d (R.S (m.descend q)) ≤ 2 * d (R.S m) := by
  have ha₁ := hR.a₀_lt
  have key : ∀ q : List (Fin 3 × Fin 3), R.IsMark (m.descend q) →
      dist (R.v (m.descend q)) (R.v m) + 2 * d (R.S (m.descend q)) ≤ 2 * d (R.S m) := by
    intro q
    induction q with
    | nil => intro _; simp [Mark.descend]
    | cons o q ih =>
      intro h
      change R.IsMark ((m.descend q).child o) at h
      change dist (R.v ((m.descend q).child o)) (R.v m) +
        2 * d (R.S ((m.descend q).child o)) ≤ _
      have h2 := hR.d_le h
      rw [S_child] at h2 ⊢
      have := d_pos (R.S (m.descend q))
      have : R.a₀ / 1000 * d (R.S (m.descend q)) ≤ d (R.S (m.descend q)) / 2 := by nlinarith
      linarith [ih ((hR.isMark_child_iff _ o).1 h).1, R.dist_v_child_le (m.descend q) o,
        dist_triangle (R.v ((m.descend q).child o)) (R.v (m.descend q)) (R.v m)]
  linarith [key q hq, d_pos (R.S (m.descend q))]

/-- D11.15.7 (termination). The generations of the marks descended from an initial mark are
bounded. -/
theorem step_11_15_7 (r : M₀) : ∃ N : ℕ, ∀ m : Mark M₀, R.IsMark m → m.root = r → m.gen ≤ N := by
  obtain ⟨C, -, hC⟩ := (step_11_19_1 (by linarith [hR.two_le_S_star] : 1 < R.S_star)).2
  refine ⟨⌈C + C * log (log (exp (exp 1) + R.S₀ r))⌉₊, fun m hm hr => ?_⟩
  have h := hC _ (lt_of_lt_of_le (by linarith [hR.two_le_S_star]) (hR.S_star_le_S₀ r)) m.gen
    (hr ▸ hR.S_star_le_S hm)
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- D11.15 **Lemma 11.4** (uniform repair induction). For sufficiently small fixed `a₀` and
corresponding `S_*`, at every generation every active mark `(v, S)` has a terminal-square-free
isolated star `v + [−a₀S, a₀S]²` with the properties of Lemma 11.3. Distinct active marks
satisfy the same separation inequality. The simultaneous removal squares are disjoint. Each
replacement has opposite labels across every positive-length interface of distinct identifiers;
its same-label contacts with old remnants or peer replacements occur only at marks of the next
generation. Every descendant mark and every descendant birth region of `(v, S)` lies within
sup-distance `2d(S)` of `v`. Each branch terminates after finitely many generations.
2D only: nine child marks, eight rays, finite planar line arrangement. -/
theorem lemma_11_4 :
    (∀ m : Mark M₀, R.IsMark m → (∀ a : TileId I M₀, a.birthGen ≤ m.gen →
        R.currentRegion m.gen a ∩ closedBall (R.v m) (R.a₀ * R.S m) =
          ⋃ (k : Fin 8) (_ : R.markOct m k = a),
            octantConeAt (R.v m) k ∩ closedBall (R.v m) (R.a₀ * R.S m)) ∧
      (∀ m', R.IsMark m' → m'.gen < m.gen → ¬R.IsNonterminal m' →
        Disjoint (closedBall (R.v m) (R.a₀ * R.S m)) (ball (R.v m') (d (R.S m')))) ∧
      ∀ k : Fin 8, R.markOct m k ≠ R.markOct m (k + 1) →
        R.label (R.markOct m k) ≠ R.label (R.markOct m (k + 1))) ∧
    (∀ m m' : Mark M₀, R.IsMark m → R.IsMark m' → m ≠ m' → m.gen = m'.gen →
      R.a₀ * max (R.S m) (R.S m') ≤ dist (R.v m) (R.v m') ∧
        Disjoint (closedBall (R.v m) (d (R.S m))) (closedBall (R.v m') (d (R.S m')))) ∧
    (∀ (m : Mark M₀) (a : TileId I M₀), R.label (.repl m a) ≠ R.label a) ∧
    (∀ (m : Mark M₀) (q : List (Fin 3 × Fin 3)), R.IsMark (m.descend q) →
      dist (R.v (m.descend q)) (R.v m) + d (R.S (m.descend q)) ≤ 2 * d (R.S m) ∧
        ∀ a : TileId I M₀, R.birthRegion (.repl (m.descend q) a) ⊆
          closedBall (R.v m) (2 * d (R.S m))) ∧
    ∀ r : M₀, ∃ N : ℕ, ∀ m : Mark M₀, R.IsMark m → m.root = r → m.gen ≤ N := by
  refine ⟨fun m hm => ⟨fun a => hR.star hm, fun m' => hR.step_11_15_5 hm,
    hR.step_11_15_2 hm⟩, fun m m' hm hm' hne hgen => ?_, fun m a => ?_,
    fun m q hq => ⟨hR.step_11_15_6_marks q hq, fun a x hx => ?_⟩, hR.step_11_15_7⟩
  · -- D11.15.1, D11.15.4
    have h := hR.step_11_15_4 hm hm' hne hgen
    refine ⟨h, closedBall_disjoint_closedBall ?_⟩
    have := hR.a₀_pos
    nlinarith [hR.d_le hm, hR.d_le hm', le_max_left (R.S m) (R.S m'),
      le_max_right (R.S m) (R.S m'), hR.S_pos m, hR.S_pos m', hR.a₀_lt]
  · -- D11.15.2
    simp only [label]
    generalize R.label a = c
    revert c; decide
  · -- D11.15.6
    rw [mem_closedBall]
    linarith [hR.step_11_15_6_marks q hq, mem_closedBall.1 (R.birthRegion_repl_subset _ a hx),
      dist_triangle x (R.v (m.descend q)) (R.v m)]

end Hyp

/-- The marks of root `r` and generation `≤ G`, as images of offset lists. -/
noncomputable def marksUpTo (r : M₀) (G : ℕ) : Finset (Mark M₀) := by
  classical
  exact (Finset.range (G + 1)).biUnion fun j =>
    (Finset.univ : Finset (Fin j → Fin 3 × Fin 3)).image fun f => ⟨r, List.ofFn f⟩

lemma mem_marksUpTo {r : M₀} {G : ℕ} {m : Mark M₀} (hr : m.root = r) (hG : m.gen ≤ G) :
    m ∈ marksUpTo r G := by
  classical
  obtain ⟨r', p⟩ := m
  obtain rfl : r' = r := hr
  simp only [marksUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨p.length, Nat.lt_succ_of_le hG, p.get, by rw [List.ofFn_get]⟩

/-- D11.19.2. At most nine children per mark: `≤ ∑_{j ≤ G} 9^j` marks of generation `≤ G`. -/
lemma card_marksUpTo_le (r : M₀) (G : ℕ) :
    ((marksUpTo r G).card : ℝ) ≤ ∑ j ∈ Finset.range (G + 1), (9 : ℝ) ^ j := by
  classical
  have h : (marksUpTo r G).card ≤ ∑ j ∈ Finset.range (G + 1), 9 ^ j := by
    unfold marksUpTo
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ =>
      Finset.card_image_le.trans (by simp))
  exact_mod_cast h

/-- D11.16. The lattice hypotheses: `o₁, o₂, o₁ ± o₂` irrational, initial marks in `o + ℤ²`, and
the initial birth regions partition `ℤ²`. -/
structure LatticeHyp (R : Repair I M₀) (o : ℝ × ℝ) : Prop where
  origin : IsIrrationalOrigin o
  v₀_mem : ∀ r, ∃ a : ℤ × ℤ, R.v₀ r = o + latticePoint a
  birth₀_unique : ∀ (z : ℤ × ℤ) (i j : I), latticePoint z ∈ R.birth₀ i →
    latticePoint z ∈ R.birth₀ j → i = j
  birth₀_cover : ∀ z : ℤ × ℤ, ∃ i, latticePoint z ∈ R.birth₀ i

namespace Hyp

variable (hR : R.Hyp)
include hR

/-- D11.15.7. Finitely many initial marks create finitely many marks. -/
theorem finite_isMark [Finite M₀] : {m : Mark M₀ | R.IsMark m}.Finite := by
  rw [show {m : Mark M₀ | R.IsMark m} = ⋃ r, {m | R.IsMark m ∧ m.root = r} by ext; simp]
  refine finite_iUnion fun r => ?_
  obtain ⟨N, hN⟩ := hR.step_11_15_7 r
  exact (marksUpTo r N).finite_toSet.subset fun m hm => mem_marksUpTo hm.2 (hN m hm.1 hm.2)

/-- D11.19.2 (`geometry:descendant-count`), replacement half. At most nine children per mark,
so the marks descended from an initial mark of scale `S` number
`≤ ∑_{j ≤ depth} 9^j ≤ C (log(S+2))^C`.
2D only: at most nine children per mark (centre, corners and side midpoints of `Q_v`). -/
theorem step_11_19_marks : ∃ C : ℝ, 0 < C ∧ ∀ r : M₀,
    ({m : Mark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ) ≤ C * log (R.S₀ r + 2) ^ C := by
  classical
  obtain ⟨C, hC, hcount⟩ := step_11_19_2 (by linarith [hR.two_le_S_star] : 1 < R.S_star)
  refine ⟨C, hC, fun r => ?_⟩
  obtain ⟨N, hN⟩ := hR.step_11_15_7 r
  have hP0 : R.S_star ≤ d^[0] (R.S₀ r) := hR.S_star_le_S₀ r
  have hsub : {m : Mark M₀ | R.IsMark m ∧ m.root = r} ⊆
      ↑(marksUpTo r (Nat.findGreatest (fun j => R.S_star ≤ d^[j] (R.S₀ r)) N)) := by
    rintro m ⟨hm, hr⟩
    refine mem_marksUpTo hr (Nat.le_findGreatest (hN m hm hr) ?_)
    simpa [S, hr] using hR.S_star_le_S hm
  calc ({m : Mark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ)
      ≤ (marksUpTo r (Nat.findGreatest (fun j => R.S_star ≤ d^[j] (R.S₀ r)) N)).card := by
        rw [← ncard_coe_finset]; exact_mod_cast ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ _ := card_marksUpTo_le r _
    _ ≤ C * log (R.S₀ r + 2) ^ C := hcount _ (by linarith [hR.two_le_S_star, hR.S_star_le_S₀ r]) _
        (Nat.findGreatest_spec (P := fun j => R.S_star ≤ d^[j] (R.S₀ r)) (Nat.zero_le N)
          hP0)

variable {o : ℝ × ℝ} (hL : R.LatticeHyp o)
include hL

/-- D11.16.1–2. Every active mark lies in `o + ℤ²`. -/
lemma exists_v_eq {m : Mark M₀} (hm : R.IsMark m) : ∃ a : ℤ × ℤ, R.v m = o + latticePoint a := by
  obtain ⟨r, p⟩ := m
  induction p with
  | nil => exact hL.v₀_mem r
  | cons e p ih =>
    change R.IsMark ((⟨r, p⟩ : Mark M₀).child e) at hm
    change ∃ a : ℤ × ℤ, R.v ((⟨r, p⟩ : Mark M₀).child e) = o + latticePoint a
    obtain ⟨hm', -⟩ := (hR.isMark_child_iff _ e).1 hm
    obtain ⟨a, ha⟩ := ih hm'
    obtain ⟨n, hn⟩ := hR.exists_d_eq_pow hm'
    refine ⟨a + (2 ^ n * ((e.1 : ℤ) - 1), 2 ^ n * ((e.2 : ℤ) - 1)), ?_⟩
    rw [v_child, ha, hn]
    ext <;> simp [latticePoint, childOffset] <;> ring

/-- D11.16.3. A lattice site in a closed removal square lies in the open one. -/
lemma latticePoint_mem_ball_iff {m : Mark M₀} (hm : R.IsMark m) (z : ℤ × ℤ) :
    latticePoint z ∈ ball (R.v m) (d (R.S m)) ↔
      latticePoint z ∈ closedBall (R.v m) (d (R.S m)) := by
  refine ⟨fun h => ball_subset_closedBall h, fun h => mem_ball.2 (lt_of_le_of_ne h ?_)⟩
  obtain ⟨a, ha⟩ := hR.exists_v_eq hL hm
  obtain ⟨n, hn⟩ := hR.exists_d_eq_pow hm
  rw [hn, ha]
  exact_mod_cast dist_latticePoint_ne_natCast hL.origin a z (2 ^ n)

/-- D11.16 (after repair), uniqueness: a lattice site lies in the final region of at most one
identifier. -/
theorem step_11_16_unique {z : ℤ × ℤ} {a b : TileId I M₀}
    (ha : latticePoint z ∈ R.finalRegion a) (hb : latticePoint z ∈ R.finalRegion b) : a = b := by
  have hball : ∀ {m : Mark M₀} {c : TileId I M₀}, latticePoint z ∈ R.finalRegion (.repl m c) →
      R.IsMark m ∧ dist (latticePoint z) (R.v m) < d (R.S m) := fun {m c} h =>
    ⟨h.1.1, mem_ball.1 ((hR.latticePoint_mem_ball_iff hL h.1.1 z).2
      (R.birthRegion_repl_subset m c h.1))⟩
  have hcross : ∀ {m : Mark M₀} {c e : TileId I M₀}, latticePoint z ∈ R.finalRegion (.repl m c) →
      e.birthGen ≤ m.gen → latticePoint z ∉ R.finalRegion e := fun h hg he =>
    (R.le_dist_of_mem_finalRegion (hball h).1 hg he).not_gt (hball h).2
  obtain ⟨i⟩ | ⟨m₁, c₁⟩ := a <;> obtain ⟨j⟩ | ⟨m₂, c₂⟩ := b
  · exact congrArg _ (hL.birth₀_unique z i j ha.1 hb.1)
  · exact absurd ha (hcross hb (Nat.zero_le _))
  · exact absurd hb (hcross ha (Nat.zero_le _))
  rcases lt_trichotomy m₁.gen m₂.gen with hlt | heq | hgt
  · exact absurd ha (hcross hb hlt)
  · by_cases hm : m₁ = m₂
    · subst hm
      obtain ⟨hm₁, -, k₁, hk₁, hz₁⟩ := ha.1
      obtain ⟨-, -, k₂, hk₂, hz₂⟩ := hb.1
      obtain ⟨p, hp⟩ := hR.exists_v_eq hL hm₁
      rw [hp] at hz₁ hz₂
      rw [← hk₁, ← hk₂, eq_of_latticePoint_mem_octantConeAt hL.origin hz₁.1 hz₂.1]
    · obtain ⟨hm₁, hd₁⟩ := hball ha
      obtain ⟨hm₂, hd₂⟩ := hball hb
      have := hR.step_11_15_4 hm₁ hm₂ hm heq
      have := hR.a₀_pos
      nlinarith [hR.d_le hm₁, hR.d_le hm₂, hR.S_pos m₁, hR.S_pos m₂,
        dist_triangle_left (R.v m₁) (R.v m₂) (latticePoint z), le_max_left (R.S m₁) (R.S m₂),
        le_max_right (R.S m₁) (R.S m₂)]
  · exact absurd hb (hcross ha hgt)

/-- D11.16 (after repair), coverage: a lattice site lies in a final region or in the open square
of a terminal mark. -/
theorem step_11_16_cover [Finite M₀] (z : ℤ × ℤ) :
    (∃ a : TileId I M₀, latticePoint z ∈ R.finalRegion a) ∨
      ∃ m : Mark M₀, R.IsMark m ∧ ¬R.IsNonterminal m ∧
        latticePoint z ∈ ball (R.v m) (d (R.S m)) := by
  set T := {m : Mark M₀ | R.IsMark m ∧ latticePoint z ∈ ball (R.v m) (d (R.S m))}
  rcases T.eq_empty_or_nonempty with hempty | hne
  · obtain ⟨i, hi⟩ := hL.birth₀_cover z
    refine Or.inl ⟨.init i, hi, ?_⟩
    simp only [mem_iUnion, not_exists]
    intro m hm hz
    have : m ∈ T := ⟨hm.1, hz⟩
    simp [hempty] at this
  obtain ⟨m, hmT, hmax⟩ :=
    (hR.finite_isMark.subset fun m hm => hm.1).exists_maximalFor Mark.gen T hne
  by_cases hnt : R.IsNonterminal m
  · have hz : latticePoint z ∈ ⋃ k, octantTriangle (R.v m) (d (R.S m)) k := by
      rw [iUnion_octantTriangle]; exact ball_subset_closedBall hmT.2
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    refine Or.inl ⟨.repl m (R.markOct m k), ⟨hmT.1, hnt, k, rfl, hk⟩, ?_⟩
    simp only [mem_iUnion, not_exists]
    intro m' hm' hz
    have := hmax ⟨hm'.1, hz⟩ (le_trans (Nat.le_succ _) hm'.2)
    simp only [TileId.birthGen] at hm'
    omega
  · exact Or.inr ⟨m, hmT.1, hnt, hmT.2⟩

omit hL in
/-- D11.18 **Lemma 11.5**, replacement half (`geometry:birth-separation`). The birth region of
a replacement created in `Q_v` of halfside `u = d(S)` is at sup-distance `≥ d(u)/2` from the final
region of every other identifier of the same label born no later than it.
2D only: angular gap `π/4` across the eight rays at a planar point contact. -/
theorem step_11_18_replacement {m : Mark M₀} (hm : R.IsMark m) (hnt : R.IsNonterminal m)
    {c a : TileId I M₀} (ha : a ≠ .repl m c) (hlabel : R.label a = R.label (.repl m c))
    (hgen : a.birthGen ≤ m.gen + 1) {x y : ℝ × ℝ} (hx : x ∈ R.birthRegion (.repl m c))
    (hy : y ∈ R.finalRegion a) : d (d (R.S m)) / 2 ≤ dist x y := by
  have hd2 : 2 ≤ d (R.S m) := hR.two_le_S_star.trans hnt
  have hdd : d (d (R.S m)) ≤ d (R.S m) := by nlinarith [hR.margin _ hnt, hR.a₀_lt, hR.a₀_pos]
  have hdS := hR.d_le hm
  have hfar : ∀ e, d (d (R.S m)) ≤ dist y (R.v m + d (R.S m) • childOffset e) := fun e => by
    simpa using R.le_dist_of_mem_finalRegion ((hR.isMark_child_iff m e).2 ⟨hm, hnt⟩)
      (by simpa using hgen) hy
  have hcenter : d (d (R.S m)) ≤ dist y (R.v m) := by
    simpa [show childOffset (1, 1) = 0 by ext <;> simp [childOffset]] using hfar (1, 1)
  obtain ⟨-, -, k, hk, hxk⟩ := hx
  have hxv : dist x (R.v m) ≤ d (R.S m) := hxk.2
  -- D11.18.5: the angular gap across non-adjacent octants
  have hgap : ∀ j, j ≠ k → j ≠ k + 1 → k ≠ j + 1 → y ∈ octantConeAt (R.v m) j →
      d (d (R.S m)) / 2 ≤ dist x y := fun j h1 h2 h3 hyj => by
    linarith [max_dist_le_two_mul_dist_of_not_adjacent h1 h2 h3 hxk.1 hyj,
      le_max_right (dist x (R.v m)) (dist y (R.v m))]
  rcases Nat.lt_or_ge a.birthGen (m.gen + 1) with hlt | hge
  · have hag : a.birthGen ≤ m.gen := Nat.lt_succ_iff.mp hlt
    by_cases hyS : y ∈ closedBall (R.v m) (R.a₀ * R.S m)
    · have hcur : y ∈ R.currentRegion m.gen a ∩ closedBall (R.v m) (R.a₀ * R.S m) :=
        ⟨R.finalRegion_subset_currentRegion _ _ hy, hyS⟩
      rw [hR.star hm hag] at hcur
      obtain ⟨j, hj, hyj, -⟩ := mem_iUnion₂.1 hcur
      have hyd := R.le_dist_of_mem_finalRegion hm hag hy
      have hjk : j ≠ k := by
        rintro rfl
        rw [← hj, hk] at hlabel
        simp [label] at hlabel
      by_cases h2 : j = k + 1
      · subst h2
        have := hfar (rayChildOffset (k + 1))
        rw [childOffset_rayChildOffset] at this
        exact (half_le_dist_of_mem_octantTriangle hdd hyd this).1 hxk hyj
      by_cases h3 : k = j + 1
      · subst h3
        have := hfar (rayChildOffset (j + 1))
        rw [childOffset_rayChildOffset] at this
        exact (half_le_dist_of_mem_octantTriangle hdd hyd this).2 hxk hyj
      exact hgap j hjk h2 h3 hyj
    · have hyv : R.a₀ * R.S m < dist y (R.v m) := by simpa using hyS
      nlinarith [hR.a₀_pos, dist_comm x y, dist_triangle_left y (R.v m) x]
  · obtain ⟨i⟩ | ⟨m'', c''⟩ := a
    · simp [TileId.birthGen] at hge
    have hag : m''.gen = m.gen := by simp only [TileId.birthGen] at hgen hge; omega
    obtain ⟨hm'', -, j, hj, hyj⟩ := hy.1
    by_cases hmm : m'' = m
    · subst hmm
      have hne : c'' ≠ c := by rintro rfl; exact ha rfl
      have hl : R.label c'' = R.label c := by simpa [label] using hlabel
      have hjk : j ≠ k := by rintro rfl; exact hne (hj.symm.trans hk)
      have h2 : j ≠ k + 1 := by
        rintro rfl
        exact hR.step_11_15_2 hm'' k (by rw [hk, hj]; exact hne.symm) (by rw [hk, hj, hl])
      have h3 : k ≠ j + 1 := by
        rintro rfl
        exact hR.step_11_15_2 hm'' j (by rw [hk, hj]; exact hne) (by rw [hk, hj, hl])
      exact hgap j hjk h2 h3 hyj.1
    · have hsep := hR.step_11_15_4 hm hm'' (Ne.symm hmm) hag.symm
      have htri := dist_triangle4 (R.v m) x y (R.v m'')
      rw [dist_comm (R.v m) x] at htri
      have h1 := mul_le_mul_of_nonneg_left (le_max_left (R.S m) (R.S m''))
        (by linarith [hR.a₀_pos] : 0 ≤ R.a₀ / 1000)
      have h2 := mul_le_mul_of_nonneg_left (le_max_right (R.S m) (R.S m''))
        (by linarith [hR.a₀_pos] : 0 ≤ R.a₀ / 1000)
      linarith [hR.d_le hm'', mem_closedBall.1 hyj.2]

end Hyp

end Repair

end AreaLaw.Geometry
