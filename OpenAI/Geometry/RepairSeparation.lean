import OpenAI.Geometry.RepairRegions

/-!
# Birth-template separation for replacements

Lemma 11.5 of [OAI265, §11, `geometry:birth-separation`, lines 562–660] for replacement tiles:
the whole closed birth region of a replacement created in the removal square of half-side `u`
is at sup distance at least `d(u) / 2` from the final region of every other identifier of the
same label born no later than it.

Inside the star of the mark, an older same-label identifier occupies outer octants and a peer
of the same mark occupies inner octants, never adjacent to the new identifier's octants except
across an active ray; the angular gap and the ray-hit clearance of `OpenAI.Geometry.Octants`,
together with the next generation's removal squares at the center and the ray-hit points, give
the bound.  Outside the star the distance exceeds the star radius minus the removal half-side.

## Implementation notes

The paper's compactness argument over finitely many rescaled patterns is replaced by the
explicit constant `1 / 2`.
-/

noncomputable section

namespace OpenAI.Geometry

namespace RepairSetup.Hyp

variable {I M₀ : Type*} {R : RepairSetup I M₀}

/-- **Birth-template separation**, replacements [OAI265, `geometry:birth-separation`].  The
birth region of the replacement `repl m old` of a nonterminal mark is at sup distance at least
`d(d(S)) / 2` from the final region of every other identifier with the same label born no later
than generation `m.gen + 1`. -/
theorem half_le_dist_of_mem_birthRegion_repl (hR : R.Hyp) {m : RepairMark M₀}
    (hm : R.IsMark m) (hnt : R.IsNonterminal m) {old a : RepairId I M₀}
    (ha : a ≠ .repl m old) (hlabel : R.label a = R.label (.repl m old))
    (hgen : a.birthGen ≤ m.gen + 1) {x y : ℝ × ℝ}
    (hx : x ∈ R.birthRegion (.repl m old)) (hy : y ∈ R.finalRegion a) :
    repairHalfSide (R.markRadius m) / 2 ≤ dist x y := by
  set v := R.markPos m with hv
  set d := R.markRadius m with hd
  set d' := repairHalfSide d with hd'
  have hT := hR.tree
  have hd2 : 2 ≤ d := hT.two_le_Sstar.trans hnt
  have hd'pos : 0 ≤ d' := by
    rw [hd', repairHalfSide]; positivity
  have hd'd : d' ≤ d := by
    have h1 := hT.margin d hnt
    have h2 := hT.a₀_lt
    nlinarith
  have hdS : d ≤ R.a₀ / 1000 * R.markScale m := hT.markRadius_le hm
  -- children of `m` are marks of removal half-side `d'`
  have hchild : ∀ o, R.IsMark (m.child o) := fun o =>
    (hT.isMark_child_iff m o).2 ⟨hm, hnt⟩
  have hradchild : ∀ o, R.markRadius (m.child o) = d' := fun o => by
    rw [RepairSetup.markRadius, RepairSetup.markScale_child]
  have hfar : ∀ o, d' ≤ dist y (v + d • repairChildOffset o) := fun o => by
    have := R.le_dist_of_mem_finalRegion (hchild o)
      (by simpa using hgen) hy
    rwa [hradchild, RepairSetup.markPos_child] at this
  have hcenter : d' ≤ dist y v := by
    have h0 : repairChildOffset (1, 1) = 0 := by
      ext <;> simp [repairChildOffset]
    simpa [h0] using hfar (1, 1)
  obtain ⟨-, -, k, hk, hxk⟩ := hx
  have hxv : dist x v ≤ d := hxk.2
  -- the angular gap, once `y` is at distance at least `d'` from `v`
  have hgap : ∀ j, j ≠ k → j ≠ k + 1 → k ≠ j + 1 → y ∈ octantConeAt v j →
      d' / 2 ≤ dist x y := fun j h1 h2 h3 hyj => by
    have := max_dist_le_two_mul_dist_of_not_adjacent h1 h2 h3 hxk.1 hyj
    have := le_max_right (dist x v) (dist y v)
    linarith
  rcases Nat.lt_or_ge a.birthGen (m.gen + 1) with hlt | hge
  · have hag : a.birthGen ≤ m.gen := Nat.lt_succ_iff.mp hlt
    by_cases hyS : y ∈ Metric.closedBall v (R.a₀ * R.markScale m)
    · have hcur : y ∈ R.currentRegion m.gen a ∩ Metric.closedBall v (R.a₀ * R.markScale m) :=
        ⟨R.finalRegion_subset_currentRegion _ _ hy, hyS⟩
      rw [hR.currentRegion_inter_closedBall hm hag] at hcur
      simp only [Set.mem_iUnion] at hcur
      obtain ⟨j, hj, hyj, -⟩ := hcur
      have hyd : d ≤ dist y v := R.le_dist_of_mem_finalRegion hm hag hy
      have hne : a ≠ old := by
        rintro rfl
        simp [RepairSetup.label] at hlabel
      have hjk : j ≠ k := by
        rintro rfl
        exact hne (hj.symm.trans hk)
      by_cases h2 : j = k + 1
      · subst h2
        have := hfar (rayChildOffset (k + 1))
        rw [repairChildOffset_rayChildOffset] at this
        exact half_le_dist_of_mem_octantTriangle_succ hd'pos hd'd hxk hyj hyd this
      by_cases h3 : k = j + 1
      · subst h3
        have := hfar (rayChildOffset (j + 1))
        rw [repairChildOffset_rayChildOffset] at this
        exact half_le_dist_of_mem_octantTriangle_pred hd'pos hd'd hxk hyj hyd this
      exact hgap j hjk h2 h3 hyj
    · have hyv : R.a₀ * R.markScale m < dist y v := by
        simpa [Metric.mem_closedBall] using hyS
      have := dist_triangle_left y v x
      rw [dist_comm] at this
      have : d' / 2 ≤ d := by linarith
      nlinarith [hT.a₀_pos, dist_comm x y, dist_triangle_left y v x]
  · have hag : a.birthGen = m.gen + 1 := le_antisymm hgen hge
    have hyb := R.finalRegion_subset_birthRegion a hy
    cases a with
    | init i => simp [RepairId.birthGen] at hag
    | repl m'' old'' =>
      simp only [RepairId.birthGen, Nat.add_right_cancel_iff] at hag
      obtain ⟨hm'', -, j, hj, hyj⟩ := hyb
      by_cases hmm : m'' = m
      · subst hmm
        have hne : old'' ≠ old := by
          rintro rfl; exact ha rfl
        have hl : R.label old'' = R.label old := by
          simpa [RepairSetup.label] using hlabel
        have hjk : j ≠ k := by
          rintro rfl; exact hne (hj.symm.trans hk)
        have h2 : j ≠ k + 1 := by
          rintro rfl
          have hne' : R.markOct m'' k ≠ R.markOct m'' (k + 1) := by
            rw [hk, hj]; exact hne.symm
          exact hR.label_markOct_ne hm'' k hne' (by rw [hk, hj, hl])
        have h3 : k ≠ j + 1 := by
          rintro rfl
          have hne' : R.markOct m'' j ≠ R.markOct m'' (j + 1) := by
            rw [hk, hj]; exact hne
          exact hR.label_markOct_ne hm'' j hne' (by rw [hk, hj, hl])
        exact hgap j hjk h2 h3 hyj.1
      · have hsep := hT.dist_markPos_of_gen_eq hm hm'' (Ne.symm hmm) hag.symm
        have hd'' : R.markRadius m'' ≤ R.a₀ / 1000 * R.markScale m'' := hT.markRadius_le hm''
        have hyv'' : dist y (R.markPos m'') ≤ R.markRadius m'' := hyj.2
        have htri := dist_triangle4 v x y (R.markPos m'')
        have hmax1 := le_max_left (R.markScale m) (R.markScale m'')
        have hmax2 := le_max_right (R.markScale m) (R.markScale m'')
        have ha0 := hT.a₀_pos
        rw [dist_comm v x] at htri
        nlinarith

end RepairSetup.Hyp

end OpenAI.Geometry
