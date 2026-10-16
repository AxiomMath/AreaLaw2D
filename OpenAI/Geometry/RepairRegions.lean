import OpenAI.Geometry.RepairTree

/-!
# Regions of the recursive repair

The repair of [OAI265, §11, lines 372–541], run simultaneously at every mark of a generation:
the open removal square of every mark is deleted from every older identifier, and a
nonterminal mark's square is refilled octant by octant.  The inner part of octant `k` receives
the identifier `repl m old`, where `old` occupies octant `k` outside the square, with the
opposite label.  Octants with the same outer identifier therefore share one new identifier, so
equal-label runs are merged without an explicit enumeration of sectors.

An identifier's birth region is fixed when it is created; its final region is the birth region
minus every removal square of its own or a later generation.

## Main definitions

* `RepairId`: initial identifiers and replacements `repl m old`.
* `RepairSetup.label`, `RepairId.birthGen`: labels and generations of birth.
* `RepairSetup.markOct`: the identifier occupying each octant of a mark's star.
* `RepairSetup.birthRegion`, `RepairSetup.currentRegion`, `RepairSetup.finalRegion`.
* `RepairSetup.Hyp`: `TreeHyp` together with octant stars at the initial marks.

## Main statements

* `RepairSetup.Hyp.currentRegion_inter_closedBall`: **uniform repair induction**: at every
  mark the regions present at its generation form an octant star of radius `a₀` times its
  scale (`geometry:repair-induction`).
* `RepairSetup.Hyp.label_markOct_ne`: consecutive distinct octant identifiers have opposite
  labels.

## Implementation notes

The removal squares are deleted as open sup-norm balls, so that birth, current and final
regions are closed; the paper deletes closed squares and keeps open actual regions.  No lattice
point lies on the boundary of a removal square (`dist_integerPoint_ne_natCast`), so the lattice
sets are the same.
-/

noncomputable section

namespace OpenAI.Geometry

/-- Identifiers of the repair: the initial ones, and the replacement `repl m old` filling the
octants of the removal square of `m` whose outer identifier is `old`. -/
inductive RepairId (I M₀ : Type*) where
  | init : I → RepairId I M₀
  | repl : RepairMark M₀ → RepairId I M₀ → RepairId I M₀

namespace RepairId

variable {I M₀ : Type*}

/-- The generation of birth: initial identifiers are born before generation zero, the
replacements of a mark of generation `g` at generation `g + 1`. -/
def birthGen : RepairId I M₀ → ℕ
  | .init _ => 0
  | .repl m _ => m.gen + 1

end RepairId

namespace RepairSetup

variable {I M₀ : Type*} (R : RepairSetup I M₀)

/-- The family label: a replacement has the label opposite to its outer identifier. -/
def label : RepairId I M₀ → Fin 2
  | .init i => R.label₀ i
  | .repl _ old => label old + 1

/-- The identifiers in the octants of the mark with root `r` and offsets `p`: initial octant
identifiers at an initial mark, and at a child the identifier read off `childOctant`. -/
def markOctPath (r : M₀) : List (Fin 3 × Fin 3) → Fin 8 → RepairId I M₀
  | [], k => .init (R.oct₀ r k)
  | o :: p, j =>
      if (childOctant o j).2 then .repl ⟨r, p⟩ (markOctPath r p (childOctant o j).1)
      else markOctPath r p (childOctant o j).1

/-- The identifier occupying octant `k` of the star of the mark `m` at its generation. -/
def markOct (m : RepairMark M₀) : Fin 8 → RepairId I M₀ :=
  R.markOctPath m.root m.path

/-- The closed birth region: the initial region, or the union of the inner octant triangles of
a nonterminal mark whose outer identifier is `old`. -/
def birthRegion : RepairId I M₀ → Set (ℝ × ℝ)
  | .init i => R.birth₀ i
  | .repl m old => {x | R.IsMark m ∧ R.IsNonterminal m ∧
      ∃ k, R.markOct m k = old ∧ x ∈ octantTriangle (R.markPos m) (R.markRadius m) k}

/-- The region of an identifier just before the removals of generation `g`: its birth region
minus the removal squares of the generations from its birth up to `g - 1`. -/
def currentRegion (g : ℕ) (a : RepairId I M₀) : Set (ℝ × ℝ) :=
  R.birthRegion a \ ⋃ (m : RepairMark M₀) (_ : R.IsMark m ∧ a.birthGen ≤ m.gen ∧ m.gen < g),
    Metric.ball (R.markPos m) (R.markRadius m)

/-- The final region of an identifier: its birth region minus every removal square of its own
or a later generation, terminal squares included. -/
def finalRegion (a : RepairId I M₀) : Set (ℝ × ℝ) :=
  R.birthRegion a \ ⋃ (m : RepairMark M₀) (_ : R.IsMark m ∧ a.birthGen ≤ m.gen),
    Metric.ball (R.markPos m) (R.markRadius m)

/-- The hypotheses of the repair induction: `TreeHyp`, an octant star of radius `a₀ S` at every
initial mark of scale `S` in which every initial birth region is the union of its octants, and
opposite labels across every active ray of an initial star (`geometry:initial-stars`). -/
structure Hyp : Prop where
  tree : R.TreeHyp
  star₀ : ∀ r i, R.birth₀ i ∩ Metric.closedBall (R.pos₀ r) (R.a₀ * R.scale₀ r) =
    ⋃ (k : Fin 8) (_ : R.oct₀ r k = i),
      octantConeAt (R.pos₀ r) k ∩ Metric.closedBall (R.pos₀ r) (R.a₀ * R.scale₀ r)
  label₀_ne : ∀ r (k : Fin 8), R.oct₀ r k ≠ R.oct₀ r (k + 1) →
    R.label₀ (R.oct₀ r k) ≠ R.label₀ (R.oct₀ r (k + 1))

@[simp] theorem markOct_child (m : RepairMark M₀) (o : Fin 3 × Fin 3) (j : Fin 8) :
    R.markOct (m.child o) j =
      if (childOctant o j).2 then .repl m (R.markOct m (childOctant o j).1)
      else R.markOct m (childOctant o j).1 :=
  rfl

/-- Every identifier in the star of a mark was born no later than the mark's generation. -/
theorem birthGen_markOct_le (m : RepairMark M₀) (k : Fin 8) :
    (R.markOct m k).birthGen ≤ m.gen := by
  obtain ⟨r, p⟩ := m
  simp only [markOct, RepairMark.gen]
  induction p generalizing k with
  | nil => simp [markOctPath, RepairId.birthGen]
  | cons o p ih =>
    simp only [markOctPath]
    split_ifs
    · simp [RepairId.birthGen, RepairMark.gen]
    · exact (ih _).trans (by simp)

/-- A point lies in the current region before generation `g` when it lies in the birth region
and outside the removal squares of the generations from birth up to `g - 1`. -/
theorem mem_currentRegion {g : ℕ} {a : RepairId I M₀} {x : ℝ × ℝ} :
    x ∈ R.currentRegion g a ↔ x ∈ R.birthRegion a ∧
      ∀ m, R.IsMark m → a.birthGen ≤ m.gen → m.gen < g → R.markRadius m ≤ dist x (R.markPos m) := by
  simp only [currentRegion, Set.mem_sdiff, Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt,
    exists_prop, not_and, and_imp]

theorem finalRegion_subset_currentRegion (g : ℕ) (a : RepairId I M₀) :
    R.finalRegion a ⊆ R.currentRegion g a := by
  intro x hx
  refine ⟨hx.1, fun h => hx.2 ?_⟩
  simp only [Set.mem_iUnion] at h ⊢
  obtain ⟨m, ⟨hm, h1, -⟩, h⟩ := h
  exact ⟨m, ⟨hm, h1⟩, h⟩

theorem finalRegion_subset_birthRegion (a : RepairId I M₀) :
    R.finalRegion a ⊆ R.birthRegion a :=
  Set.sdiff_subset

/-- The final region of an identifier avoids the open removal square of every mark of its own
or a later generation. -/
theorem le_dist_of_mem_finalRegion {a : RepairId I M₀} {m : RepairMark M₀} (hm : R.IsMark m)
    (hgen : a.birthGen ≤ m.gen) {y : ℝ × ℝ} (hy : y ∈ R.finalRegion a) :
    R.markRadius m ≤ dist y (R.markPos m) := by
  by_contra h
  exact hy.2 (Set.mem_iUnion₂.2 ⟨m, ⟨hm, hgen⟩, Metric.mem_ball.2 (not_le.1 h)⟩)

theorem birthRegion_repl_subset (m : RepairMark M₀) (old : RepairId I M₀) :
    R.birthRegion (.repl m old) ⊆ Metric.closedBall (R.markPos m) (R.markRadius m) := by
  rintro x ⟨-, -, k, -, hx⟩
  exact hx.2

/-- An identifier born no later than generation `m.gen` occupies an octant of a child of `m`
exactly when that octant lies outside the removal square, in an octant of `m` it occupies. -/
theorem markOct_child_eq_iff_of_birthGen_le {m : RepairMark M₀} {a : RepairId I M₀}
    (ha : a.birthGen ≤ m.gen) (o : Fin 3 × Fin 3) (j : Fin 8) :
    R.markOct (m.child o) j = a ↔
      (childOctant o j).2 = false ∧ R.markOct m (childOctant o j).1 = a := by
  rw [markOct_child]
  split_ifs with h
  · simp only [h, Bool.true_eq_false, false_and, iff_false]
    rintro rfl
    simp [RepairId.birthGen] at ha
  · simp [h]

/-- The replacement `repl m' old` occupies an octant of a child of `m` exactly when `m' = m` and
the octant lies inside the removal square, in an octant of `m` occupied by `old`. -/
theorem markOct_child_eq_repl_iff {m m' : RepairMark M₀} (hgen : m'.gen = m.gen)
    (old : RepairId I M₀) (o : Fin 3 × Fin 3) (j : Fin 8) :
    R.markOct (m.child o) j = .repl m' old ↔
      (childOctant o j).2 = true ∧ m = m' ∧ R.markOct m (childOctant o j).1 = old := by
  rw [markOct_child]
  split_ifs with h
  · simp [h]
  · simp only [h, Bool.false_eq_true, false_and, iff_false]
    intro he
    have := R.birthGen_markOct_le m (childOctant o j).1
    rw [he] at this
    simp only [RepairId.birthGen] at this
    omega

private theorem inter_eq_iUnion_iff {α ι : Type*} {A B : Set α} {P : ι → Prop}
    {C : ι → Set α} :
    A ∩ B = ⋃ (k) (_ : P k), C k ∩ B ↔ ∀ x ∈ B, (x ∈ A ↔ ∃ k, P k ∧ x ∈ C k) := by
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · intro h x hx
    simpa [hx] using h x
  · intro h x
    by_cases hx : x ∈ B
    · simpa [hx] using h x hx
    · simp [hx]

private theorem exists_childOctant_iff {o : Fin 3 × Fin 3} {b : Bool} {P Q : Fin 8 → Prop} :
    (∃ k, P k ∧ ∃ j, childOctant o j = (k, b) ∧ Q j) ↔
      ∃ j, ((childOctant o j).2 = b ∧ P (childOctant o j).1) ∧ Q j := by
  constructor
  · rintro ⟨k, hk, j, hj, hq⟩
    exact ⟨j, ⟨by simp [hj], by simpa [hj] using hk⟩, hq⟩
  · rintro ⟨j, ⟨hb, hk⟩, hq⟩
    exact ⟨_, hk, j, Prod.ext rfl hb, hq⟩

namespace TreeHyp

variable {R}

/-- The star ball of a child of `m` lies in the star ball of `m`. -/
theorem mem_closedBall_of_mem_closedBall_child (hR : R.TreeHyp) {m : RepairMark M₀}
    {o : Fin 3 × Fin 3} (hc : R.IsMark (m.child o)) {x : ℝ × ℝ}
    (hx : x ∈ Metric.closedBall (R.markPos (m.child o)) (R.a₀ * R.markScale (m.child o))) :
    x ∈ Metric.closedBall (R.markPos m) (R.a₀ * R.markScale m) := by
  obtain ⟨hm, -⟩ := (hR.isMark_child_iff m o).1 hc
  rw [markScale_child, Metric.mem_closedBall] at hx
  rw [Metric.mem_closedBall]
  have h1 := hR.dist_markPos_child_le hm o
  have h2 := hR.markRadius_le hm
  have h3 := hR.Sstar_le_markScale hm
  have h4 := hR.two_le_Sstar
  have h5 := hR.a₀_pos
  have h6 := hR.a₀_lt
  have h7 : 0 ≤ R.markRadius m := (repairHalfSide_pos _).le
  have h8 : R.a₀ * R.markRadius m ≤ 1 / 2 * R.markRadius m :=
    mul_le_mul_of_nonneg_right h6.le h7
  have h9 : 0 < R.a₀ * R.markScale m := mul_pos h5 (by linarith)
  calc dist x (R.markPos m) ≤ dist x (R.markPos (m.child o)) + dist (R.markPos (m.child o))
        (R.markPos m) := dist_triangle _ _ _
    _ ≤ R.a₀ * R.markScale m := by nlinarith

/-- The star ball of a child of `m` misses the closed removal square of every other mark of
the generation of `m`. -/
theorem markRadius_lt_dist_of_mem_closedBall_child (hR : R.TreeHyp) {m m' : RepairMark M₀}
    {o : Fin 3 × Fin 3} (hc : R.IsMark (m.child o)) (hm' : R.IsMark m') (hne : m' ≠ m)
    (hgen : m'.gen = m.gen) {x : ℝ × ℝ}
    (hx : x ∈ Metric.closedBall (R.markPos (m.child o)) (R.a₀ * R.markScale (m.child o))) :
    R.markRadius m' < dist x (R.markPos m') := by
  obtain ⟨hm, -⟩ := (hR.isMark_child_iff m o).1 hc
  rw [markScale_child, Metric.mem_closedBall] at hx
  have h0 := hR.dist_markPos_of_gen_eq hm hm' hne.symm hgen.symm
  have h1 := hR.dist_markPos_child_le hm o
  have h2 := hR.markRadius_le hm
  have h2' := hR.markRadius_le hm'
  have h3 := hR.Sstar_le_markScale hm
  have h4 := hR.two_le_Sstar
  have h5 := hR.a₀_pos
  have h6 := hR.a₀_lt
  have h7 : 0 ≤ R.markRadius m := (repairHalfSide_pos _).le
  have h8 : R.a₀ * R.markRadius m ≤ 1 / 2 * R.markRadius m :=
    mul_le_mul_of_nonneg_right h6.le h7
  set M := max (R.markScale m) (R.markScale m')
  have hM : R.markScale m ≤ M := le_max_left _ _
  have hM' : R.markScale m' ≤ M := le_max_right _ _
  have h9 : 0 < R.a₀ * M := by nlinarith
  have h10 : R.a₀ / 1000 * R.markScale m ≤ R.a₀ / 1000 * M :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have h11 : R.a₀ / 1000 * R.markScale m' ≤ R.a₀ / 1000 * M :=
    mul_le_mul_of_nonneg_left hM' (by positivity)
  have ht1 := dist_triangle (R.markPos m) x (R.markPos m')
  have ht2 := dist_triangle x (R.markPos (m.child o)) (R.markPos m)
  rw [dist_comm] at ht2
  linarith

end TreeHyp

namespace Hyp

variable {R}

/-- The induction step of `currentRegion_inter_closedBall`: the star of a child of `m` is read
off the star of `m` through `childOctant`. -/
theorem currentRegion_child_inter_closedBall (hR : R.Hyp) {m : RepairMark M₀}
    {o : Fin 3 × Fin 3} (hc : R.IsMark (m.child o))
    (ih : ∀ a : RepairId I M₀, a.birthGen ≤ m.gen →
      R.currentRegion m.gen a ∩ Metric.closedBall (R.markPos m) (R.a₀ * R.markScale m) =
        ⋃ (k : Fin 8) (_ : R.markOct m k = a),
          octantConeAt (R.markPos m) k ∩ Metric.closedBall (R.markPos m) (R.a₀ * R.markScale m))
    {a : RepairId I M₀} (ha : a.birthGen ≤ (m.child o).gen) :
    R.currentRegion (m.child o).gen a ∩
        Metric.closedBall (R.markPos (m.child o)) (R.a₀ * R.markScale (m.child o)) =
      ⋃ (k : Fin 8) (_ : R.markOct (m.child o) k = a),
        octantConeAt (R.markPos (m.child o)) k ∩
          Metric.closedBall (R.markPos (m.child o)) (R.a₀ * R.markScale (m.child o)) := by
  obtain ⟨hm, hnt⟩ := (hR.tree.isMark_child_iff m o).1 hc
  have hd : 2 ≤ R.markRadius m := hR.tree.two_le_Sstar.trans hnt
  have ha0 := hR.tree.a₀_pos
  have ha1 := hR.tree.a₀_lt
  have hRd : 2 * (R.a₀ * R.markRadius m) < R.markRadius m := by nlinarith
  have hR0 : 0 ≤ R.a₀ * R.markRadius m := by positivity
  rw [inter_eq_iUnion_iff]
  intro x hx
  have hx' := hx
  rw [markScale_child, markPos_child] at hx'
  have hxm := hR.tree.mem_closedBall_of_mem_closedBall_child hc hx
  have sep := fun m' (hm' : R.IsMark m') hne hgen =>
    hR.tree.markRadius_lt_dist_of_mem_closedBall_child hc hm' hne hgen hx
  have child := fun k b => mem_octantConeAt_child_iff o hR0 hRd hx' k b
  rw [markPos_child]
  rw [RepairMark.gen_child] at ha ⊢
  rcases Nat.le_succ_iff.1 ha with ha | ha
  · have hih := (inter_eq_iUnion_iff.1 (ih a ha)) x hxm
    calc x ∈ R.currentRegion (m.gen + 1) a ↔
          x ∈ R.currentRegion m.gen a ∧ R.markRadius m ≤ dist x (R.markPos m) := by
          simp only [mem_currentRegion]
          constructor
          · rintro ⟨hb, h⟩
            exact ⟨⟨hb, fun m' hm' h1 h2 => h m' hm' h1 (by omega)⟩, h m hm ha (by omega)⟩
          · rintro ⟨⟨hb, h⟩, hmd⟩
            refine ⟨hb, fun m' hm' h1 h2 => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
            · exact h m' hm' h1 h2
            · by_cases hne : m' = m
              · subst hne
                exact hmd
              · exact (sep m' hm' hne h2).le
      _ ↔ ∃ k, R.markOct m k = a ∧ ∃ j, childOctant o j = (k, false) ∧
            x ∈ octantConeAt (R.markPos m + R.markRadius m • repairChildOffset o) j := by
          rw [hih]
          constructor
          · rintro ⟨⟨k, hk, hxk⟩, h⟩
            refine ⟨k, hk, (child k false).1 ⟨hxk, ?_⟩⟩
            simpa [Metric.mem_ball] using h
          · rintro ⟨k, hk, hj⟩
            obtain ⟨hxk, h⟩ := (child k false).2 hj
            refine ⟨⟨k, hk, hxk⟩, ?_⟩
            simpa [Metric.mem_ball] using h
      _ ↔ _ := by
          rw [exists_childOctant_iff]
          simp only [R.markOct_child_eq_iff_of_birthGen_le ha]
  · cases a with
    | init i => simp [RepairId.birthGen] at ha
    | repl m'' old =>
      replace ha : m''.gen = m.gen := by
        simp only [RepairId.birthGen] at ha
        omega
      have hcur : x ∈ R.currentRegion (m.gen + 1) (.repl m'' old) ↔
          x ∈ R.birthRegion (.repl m'' old) := by
        rw [mem_currentRegion]
        refine ⟨And.left, fun h => ⟨h, fun m' _ h1 h2 => ?_⟩⟩
        simp only [RepairId.birthGen] at h1
        omega
      rw [hcur]
      simp only [R.markOct_child_eq_repl_iff ha]
      by_cases hne : m'' = m
      · subst hne
        calc x ∈ R.birthRegion (.repl m'' old) ↔ ∃ k, R.markOct m'' k = old ∧
              ∃ j, childOctant o j = (k, true) ∧
                x ∈ octantConeAt (R.markPos m'' + R.markRadius m'' • repairChildOffset o) j := by
              simp only [birthRegion, Set.mem_ofPred_eq, hm, hnt, true_and]
              refine exists_congr fun k => and_congr_right fun _ => ?_
              rw [← child k true]
              rfl
          _ ↔ _ := by
              rw [exists_childOctant_iff]
              simp
      · constructor
        · rintro ⟨hm'', -, k, -, hxk⟩
          have := sep m'' hm'' hne ha
          have := hxk.2
          rw [Metric.mem_closedBall] at this
          linarith
        · rintro ⟨j, ⟨-, h, -⟩, -⟩
          exact absurd h.symm hne

/-- **Uniform repair induction** [OAI265, `geometry:repair-induction`].  At every mark `m`, in
the closed sup-norm ball of radius `a₀` times its scale, every identifier present before the
removals of generation `m.gen` occupies exactly the octants of `m` assigned to it.  In
particular no earlier removal square, terminal or not, meets the star. -/
theorem currentRegion_inter_closedBall (hR : R.Hyp) {m : RepairMark M₀} (hm : R.IsMark m)
    {a : RepairId I M₀} (ha : a.birthGen ≤ m.gen) :
    R.currentRegion m.gen a ∩ Metric.closedBall (R.markPos m) (R.a₀ * R.markScale m) =
      ⋃ (k : Fin 8) (_ : R.markOct m k = a),
        octantConeAt (R.markPos m) k ∩ Metric.closedBall (R.markPos m) (R.a₀ * R.markScale m) := by
  obtain ⟨r, p⟩ := m
  induction p generalizing a with
  | nil =>
    cases a with
    | repl m' old => simp [RepairId.birthGen, RepairMark.gen] at ha
    | init i =>
      have hcur : R.currentRegion 0 (.init i) = R.birth₀ i := by
        ext x
        simp [mem_currentRegion, birthRegion]
      change R.currentRegion 0 _ ∩ Metric.closedBall (R.pos₀ r) (R.a₀ * R.scale₀ r) =
        ⋃ (k : Fin 8) (_ : RepairId.init (R.oct₀ r k) = .init i),
          octantConeAt (R.pos₀ r) k ∩ Metric.closedBall (R.pos₀ r) (R.a₀ * R.scale₀ r)
      rw [hcur, hR.star₀ r i]
      simp only [RepairId.init.injEq]
  | cons o p ih =>
    exact currentRegion_child_inter_closedBall hR (m := ⟨r, p⟩) (o := o) hm
      (fun a ha => ih ((hR.tree.isMark_child_iff ⟨r, p⟩ o).1 hm).1 ha) ha

private theorem fin_two_ne_add_one (a : Fin 2) : a ≠ a + 1 := by
  revert a
  decide

/-- Across every active ray of the star of a mark the labels are opposite. -/
theorem label_markOct_ne (hR : R.Hyp) {m : RepairMark M₀} (hm : R.IsMark m) (k : Fin 8)
    (hk : R.markOct m k ≠ R.markOct m (k + 1)) :
    R.label (R.markOct m k) ≠ R.label (R.markOct m (k + 1)) := by
  obtain ⟨r, p⟩ := m
  induction p generalizing k with
  | nil =>
    exact hR.label₀_ne r k fun h => hk (by simp [markOct, markOctPath, h])
  | cons o p ih =>
    have hm' := ((hR.tree.isMark_child_iff ⟨r, p⟩ o).1 hm).1
    have ih' := fun k => ih k hm'
    change R.markOct ((⟨r, p⟩ : RepairMark M₀).child o) k ≠
      R.markOct ((⟨r, p⟩ : RepairMark M₀).child o) (k + 1) at hk
    change R.label (R.markOct ((⟨r, p⟩ : RepairMark M₀).child o) k) ≠
      R.label (R.markOct ((⟨r, p⟩ : RepairMark M₀).child o) (k + 1))
    have key := childOctant_succ o k
    rw [markOct_child, markOct_child] at hk ⊢
    revert key hk
    generalize childOctant o k = c₁
    generalize childOctant o (k + 1) = c₂
    obtain ⟨k₁, b₁⟩ := c₁
    obtain ⟨k₂, b₂⟩ := c₂
    intro hk key
    cases b₁ <;> cases b₂ <;> simp only [Prod.mk.injEq, and_true, true_and, and_false,
      false_and, or_false, false_or, ne_eq, not_true_eq_false, not_false_eq_true,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
      label, RepairId.repl.injEq] at key hk ⊢
    · rcases key with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact ih' k₁ hk
      · exact fun h => ih' k₂ (Ne.symm hk) h.symm
    · subst key
      exact fin_two_ne_add_one _
    · subst key
      exact (fin_two_ne_add_one _).symm
    · rcases key with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact fun h => ih' k₁ hk (add_right_cancel h)
      · exact fun h => ih' k₂ (Ne.symm hk) (add_right_cancel h).symm

end Hyp

end RepairSetup

end OpenAI.Geometry
