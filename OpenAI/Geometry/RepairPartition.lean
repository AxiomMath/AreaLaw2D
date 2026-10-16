import OpenAI.Geometry.RepairRegions

/-!
# The lattice partition left by the repair

On lattice points the final regions of the repair are pairwise disjoint, and every lattice
point lies in some final region or in the open square of a terminal mark
[OAI265, §11, lines 545–559 and 668–688].  Lattice points avoid every removal-square boundary
and every ray, because initial marks lie on the translated mesh `dyadicOrigin + ℤ²` and removal
half-sides are integers.

## Main definitions

* `RepairSetup.LatticeHyp`: initial marks on the translated mesh, and the initial birth regions
  partition the lattice.

## Main statements

* `RepairSetup.LatticeHyp.eq_of_mem_finalRegion`: disjointness on lattice points.
* `RepairSetup.LatticeHyp.exists_mem_finalRegion_or_terminal`: coverage.
* `RepairSetup.Hyp.birthRegion_repl_subset_closedBall_root`: every replacement lies within
  twice the removal half-side of its initial mark.
-/

noncomputable section

namespace OpenAI.Geometry

namespace RepairSetup

variable {I M₀ : Type*} (R : RepairSetup I M₀)

/-- Lattice hypotheses: initial marks on the translated mesh, and each lattice point in exactly
one initial birth region. -/
structure LatticeHyp : Prop where
  hyp : R.Hyp
  pos₀_mem : ∀ r, ∃ a : ℤ × ℤ, R.pos₀ r = dyadicOrigin + integerPoint a
  birth₀_unique : ∀ (z : ℤ × ℤ) (i j : I), integerPoint z ∈ R.birth₀ i →
    integerPoint z ∈ R.birth₀ j → i = j
  birth₀_cover : ∀ z : ℤ × ℤ, ∃ i, integerPoint z ∈ R.birth₀ i

namespace LatticeHyp

variable {R}

/-- Every mark lies on the translated mesh. -/
theorem exists_markPos_eq (hR : R.LatticeHyp) {m : RepairMark M₀} (hm : R.IsMark m) :
    ∃ a : ℤ × ℤ, R.markPos m = dyadicOrigin + integerPoint a := by
  obtain ⟨r, p⟩ := m
  induction p with
  | nil => exact hR.pos₀_mem r
  | cons o p ih =>
    have hc : (⟨r, o :: p⟩ : RepairMark M₀) = (⟨r, p⟩ : RepairMark M₀).child o := rfl
    rw [hc] at hm ⊢
    obtain ⟨hm', -⟩ := (hR.hyp.tree.isMark_child_iff _ o).mp hm
    obtain ⟨a, ha⟩ := ih hm'
    obtain ⟨n, hn⟩ := hR.hyp.tree.exists_markRadius_eq_pow hm'
    refine ⟨a + (2 ^ n * ((o.1.val : ℤ) - 1), 2 ^ n * ((o.2.val : ℤ) - 1)), ?_⟩
    rw [R.markPos_child, ha, hn]
    ext <;> simp [integerPoint, repairChildOffset] <;> ring

/-- A lattice point lies in the open removal square of a mark exactly when it lies in the
closed one. -/
theorem integerPoint_mem_ball_iff (hR : R.LatticeHyp) {m : RepairMark M₀} (hm : R.IsMark m)
    (z : ℤ × ℤ) :
    integerPoint z ∈ Metric.ball (R.markPos m) (R.markRadius m) ↔
      integerPoint z ∈ Metric.closedBall (R.markPos m) (R.markRadius m) := by
  refine ⟨fun h => Metric.ball_subset_closedBall h, fun h => ?_⟩
  obtain ⟨a, ha⟩ := hR.exists_markPos_eq hm
  obtain ⟨n, hn⟩ := hR.hyp.tree.exists_markRadius_eq_pow hm
  rw [Metric.mem_closedBall] at h
  rw [Metric.mem_ball]
  refine lt_of_le_of_ne h ?_
  have := dist_integerPoint_ne_natCast a z (2 ^ n)
  rw [hn, ha]
  simpa using this

/-- **Disjointness.**  A lattice point lies in the final region of at most one identifier. -/
theorem eq_of_mem_finalRegion (hR : R.LatticeHyp) {z : ℤ × ℤ} {a b : RepairId I M₀}
    (ha : integerPoint z ∈ R.finalRegion a) (hb : integerPoint z ∈ R.finalRegion b) :
    a = b := by
  have hT := hR.hyp.tree
  -- a lattice point of a replacement region lies in the open square of its mark
  have hball : ∀ {m : RepairMark M₀} {old : RepairId I M₀},
      integerPoint z ∈ R.finalRegion (.repl m old) →
        R.IsMark m ∧ dist (integerPoint z) (R.markPos m) < R.markRadius m := by
    intro m old h
    have hb := R.finalRegion_subset_birthRegion _ h
    have hm : R.IsMark m := hb.1
    have hc := R.birthRegion_repl_subset m old hb
    exact ⟨hm, Metric.mem_ball.mp ((hR.integerPoint_mem_ball_iff hm z).mpr hc)⟩
  -- a lattice point of a replacement region is not in the final region of anything born no
  -- later than its mark
  have hcross : ∀ {m : RepairMark M₀} {old c : RepairId I M₀},
      integerPoint z ∈ R.finalRegion (.repl m old) → c.birthGen ≤ m.gen →
        integerPoint z ∉ R.finalRegion c := by
    intro m old c h hg hc
    obtain ⟨hm, hd⟩ := hball h
    exact (R.le_dist_of_mem_finalRegion hm hg hc).not_gt hd
  cases a with
  | init i =>
    cases b with
    | init j =>
      exact congrArg _ (hR.birth₀_unique z i j (R.finalRegion_subset_birthRegion _ ha)
        (R.finalRegion_subset_birthRegion _ hb))
    | repl m old => exact absurd ha (hcross hb (Nat.zero_le _))
  | repl m₁ old₁ =>
    cases b with
    | init j => exact absurd hb (hcross ha (Nat.zero_le _))
    | repl m₂ old₂ =>
      rcases lt_trichotomy m₁.gen m₂.gen with hlt | heq | hgt
      · exact absurd ha (hcross hb hlt)
      · by_cases hm : m₁ = m₂
        · subst hm
          obtain ⟨hm₁, -, k₁, hk₁, hz₁⟩ := R.finalRegion_subset_birthRegion _ ha
          obtain ⟨-, -, k₂, hk₂, hz₂⟩ := R.finalRegion_subset_birthRegion _ hb
          obtain ⟨p, hp⟩ := hR.exists_markPos_eq hm₁
          rw [hp] at hz₁ hz₂
          have hk := eq_of_integerPoint_mem_octantConeAt hz₁.1 hz₂.1
          rw [← hk₁, ← hk₂, hk]
        · exfalso
          obtain ⟨hm₁, hd₁⟩ := hball ha
          obtain ⟨hm₂, hd₂⟩ := hball hb
          have hsep := hT.dist_markPos_of_gen_eq hm₁ hm₂ hm heq
          have hr₁ := hT.markRadius_le hm₁
          have hr₂ := hT.markRadius_le hm₂
          have hs₁ := hT.Sstar_le_markScale hm₁
          have hs₂ := hT.Sstar_le_markScale hm₂
          have htri := dist_triangle_left (R.markPos m₁) (R.markPos m₂) (integerPoint z)
          have hmax₁ := le_max_left (R.markScale m₁) (R.markScale m₂)
          have hmax₂ := le_max_right (R.markScale m₁) (R.markScale m₂)
          have ha₀ := hT.a₀_pos
          have h2 := hT.two_le_Sstar
          nlinarith
      · exact absurd hb (hcross ha hgt)

/-- **Coverage.**  Every lattice point lies in a final region, or in the open removal square of
a terminal mark. -/
theorem exists_mem_finalRegion_or_terminal (hR : R.LatticeHyp) [Finite M₀] (z : ℤ × ℤ) :
    (∃ a : RepairId I M₀, integerPoint z ∈ R.finalRegion a) ∨
      ∃ m : RepairMark M₀, R.IsMark m ∧ ¬ R.IsNonterminal m ∧
        integerPoint z ∈ Metric.ball (R.markPos m) (R.markRadius m) := by
  set S := {m : RepairMark M₀ | R.IsMark m ∧
    integerPoint z ∈ Metric.ball (R.markPos m) (R.markRadius m)} with hS
  have hfin : S.Finite := hR.hyp.tree.finite_isMark.subset fun m hm => hm.1
  rcases S.eq_empty_or_nonempty with hempty | hne
  · obtain ⟨i, hi⟩ := hR.birth₀_cover z
    refine Or.inl ⟨.init i, hi, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro m hm hz
    have : m ∈ S := ⟨hm.1, hz⟩
    simp [hempty] at this
  · obtain ⟨m, hmS, hmax⟩ := hfin.exists_maximalFor RepairMark.gen S hne
    by_cases hnt : R.IsNonterminal m
    · left
      have hcb : integerPoint z ∈ Metric.closedBall (R.markPos m) (R.markRadius m) :=
        Metric.ball_subset_closedBall hmS.2
      rw [← iUnion_octantTriangle] at hcb
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hcb
      refine ⟨.repl m (R.markOct m k), ⟨hmS.1, hnt, k, rfl, hk⟩, ?_⟩
      simp only [Set.mem_iUnion, not_exists]
      intro m' hm' hz
      have hle := hmax ⟨hm'.1, hz⟩ (le_trans (Nat.le_succ _) hm'.2)
      simp only [RepairId.birthGen] at hm'
      omega
    · exact Or.inr ⟨m, hmS.1, hnt, hmS.2⟩

end LatticeHyp

namespace Hyp

variable {R}

/-- Every replacement birth region lies within twice the removal half-side of its initial
mark (`geometry:repair-induction`, descendant bound). -/
theorem birthRegion_repl_subset_closedBall_root (hR : R.Hyp) (m : RepairMark M₀)
    (old : RepairId I M₀) :
    R.birthRegion (.repl m old) ⊆
      Metric.closedBall (R.pos₀ m.root) (2 * repairHalfSide (R.scale₀ m.root)) := by
  intro x hx
  have hm : R.IsMark m := hx.1
  have hxm := Metric.mem_closedBall.mp (R.birthRegion_repl_subset m old hx)
  set r₀ : RepairMark M₀ := ⟨m.root, []⟩
  have hr₀ : R.IsMark r₀ := Or.inl rfl
  have hdesc : r₀.descend m.path = m := by
    simp [r₀, RepairMark.descend]
  have h := hR.tree.dist_markPos_descendant_add_markRadius_le hr₀ m.path (by rw [hdesc]; exact hm)
  rw [hdesc] at h
  have hpos : R.markPos r₀ = R.pos₀ m.root := rfl
  have hrad : R.markRadius r₀ = repairHalfSide (R.scale₀ m.root) := rfl
  rw [hpos, hrad] at h
  rw [Metric.mem_closedBall]
  linarith [dist_triangle x (R.markPos m) (R.pos₀ m.root)]

end Hyp

end RepairSetup

end OpenAI.Geometry
