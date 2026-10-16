import OpenAI.Geometry.Octants
import OpenAI.Geometry.RepairDepth

/-!
# The tree of repair marks

The recursive repair of [OAI265, §11, lines 372–541] starts from finitely many initial marks,
each with a position and a scale.  A nonterminal mark `(v, S)` has removal half-side
`d(S) = repairHalfSide S` and nine children: the center, corners and side midpoints of its
removal square, all of scale `d(S)`.  A mark is terminal once `d(S) < S_*`.

A mark is recorded by its initial ancestor and the list of child offsets leading to it, newest
first, so positions and scales are computed by recursion on the list and a mark's generation is
the length of its list.

## Main definitions

* `RepairSetup`: the initial marks, their octant identifiers and the initial regions.
* `RepairMark`, `RepairMark.gen`, `RepairMark.child`: marks, generations and children.
* `RepairSetup.markScale`, `RepairSetup.markRadius`, `RepairSetup.markPos`.
* `RepairSetup.IsMark`: the marks actually created.
* `RepairSetup.TreeHyp`: the separation and scale hypotheses on the initial marks.

## Main statements

* `RepairSetup.TreeHyp.dist_markPos_of_gen_eq`: marks of one generation stay separated
  (`geometry:repair-induction`, separation invariant).
* `RepairSetup.TreeHyp.dist_markPos_descendant_add_markRadius_le`: descendants stay within
  twice the removal half-side.
* `RepairSetup.TreeHyp.finite_isMark`, `RepairSetup.TreeHyp.exists_ncard_isMark_root_le`:
  finiteness and the descendant count (`geometry:descendant-count`).
-/

noncomputable section

namespace OpenAI.Geometry

/-- A repair mark: an initial mark `root` and the child offsets leading from it, newest first. -/
structure RepairMark (M₀ : Type*) where
  /-- The initial ancestor. -/
  root : M₀
  /-- The offsets of the successive children, newest first. -/
  path : List (Fin 3 × Fin 3)

namespace RepairMark

variable {M₀ : Type*}

/-- The generation of a mark: initial marks have generation zero. -/
def gen (m : RepairMark M₀) : ℕ := m.path.length

/-- The child of `m` at offset `o` of its removal square. -/
def child (m : RepairMark M₀) (o : Fin 3 × Fin 3) : RepairMark M₀ := ⟨m.root, o :: m.path⟩

/-- The descendant of `m` along the further offsets `q`, newest first. -/
def descend (m : RepairMark M₀) (q : List (Fin 3 × Fin 3)) : RepairMark M₀ :=
  ⟨m.root, q ++ m.path⟩

@[simp] theorem gen_child (m : RepairMark M₀) (o : Fin 3 × Fin 3) :
    (m.child o).gen = m.gen + 1 := by
  simp [gen, child]

@[simp] theorem gen_descend (m : RepairMark M₀) (q : List (Fin 3 × Fin 3)) :
    (m.descend q).gen = q.length + m.gen := by
  simp [gen, descend]

end RepairMark

/-- The centered offsets of the nine children have sup norm at most one. -/
theorem norm_repairChildOffset_le (o : Fin 3 × Fin 3) : ‖repairChildOffset o‖ ≤ 1 := by
  obtain ⟨i, j⟩ := o
  rw [Prod.norm_def]
  fin_cases i <;> fin_cases j <;> norm_num [repairChildOffset]

private theorem one_le_abs_sub_of_ne {i j : Fin 3} (h : i ≠ j) :
    1 ≤ |((i.val : ℝ) - 1) - ((j.val : ℝ) - 1)| := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | norm_num

/-- Distinct centered offsets are at sup distance at least one. -/
theorem one_le_norm_repairChildOffset_sub {o o' : Fin 3 × Fin 3} (ho : o ≠ o') :
    1 ≤ ‖repairChildOffset o - repairChildOffset o'‖ := by
  obtain ⟨i, j⟩ := o
  obtain ⟨i', j'⟩ := o'
  rw [Prod.norm_def]
  simp only [repairChildOffset, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  by_cases hi : i = i'
  · subst hi
    have hj : j ≠ j' := fun h => ho (by rw [h])
    exact (one_le_abs_sub_of_ne hj).trans (le_max_right _ _)
  · exact (one_le_abs_sub_of_ne hi).trans (le_max_left _ _)

/-- The data of a repair: initial marks `M₀` with positions, scales and the initial identifiers
of their eight octants, initial identifiers `I` with labels and closed birth regions, the
stopping scale `Sstar` and the isolation constant `a₀`. -/
structure RepairSetup (I M₀ : Type*) where
  /-- Position of an initial mark. -/
  pos₀ : M₀ → ℝ × ℝ
  /-- Scale of an initial mark. -/
  scale₀ : M₀ → ℝ
  /-- The initial identifier occupying each octant of an initial mark's star. -/
  oct₀ : M₀ → Fin 8 → I
  /-- Family label of an initial identifier. -/
  label₀ : I → Fin 2
  /-- Closed birth region of an initial identifier. -/
  birth₀ : I → Set (ℝ × ℝ)
  /-- The stopping scale `S_*`. -/
  Sstar : ℝ
  /-- The isolation constant: an initial mark of scale `S` has an octant star of radius
  `a₀ * S`. -/
  a₀ : ℝ

namespace RepairSetup

variable {I M₀ : Type*} (R : RepairSetup I M₀)

/-- The scale of a mark: the initial scale halved by `repairHalfSide` once per generation. -/
def markScale (m : RepairMark M₀) : ℝ :=
  repairHalfSide^[m.gen] (R.scale₀ m.root)

/-- The removal half-side `d(S)` of a mark of scale `S`. -/
def markRadius (m : RepairMark M₀) : ℝ :=
  repairHalfSide (R.markScale m)

/-- Position of the mark with root `r` and offsets `p`, newest first. -/
def pathPos (r : M₀) : List (Fin 3 × Fin 3) → ℝ × ℝ
  | [] => R.pos₀ r
  | o :: p => pathPos r p +
      repairHalfSide (repairHalfSide^[p.length] (R.scale₀ r)) • repairChildOffset o

/-- The position of a mark. -/
def markPos (m : RepairMark M₀) : ℝ × ℝ :=
  R.pathPos m.root m.path

/-- The marks actually created: initial marks, and children of nonterminal marks, i.e. those
whose scale is at least `Sstar`. -/
def IsMark (m : RepairMark M₀) : Prop :=
  m.path = [] ∨ R.Sstar ≤ R.markScale m

/-- A mark is nonterminal when its removal half-side is at least the stopping scale. -/
def IsNonterminal (m : RepairMark M₀) : Prop :=
  R.Sstar ≤ R.markRadius m

@[simp] theorem markScale_child (m : RepairMark M₀) (o : Fin 3 × Fin 3) :
    R.markScale (m.child o) = R.markRadius m := by
  simp [markScale, markRadius, RepairMark.child, RepairMark.gen, Function.iterate_succ_apply']

@[simp] theorem markPos_child (m : RepairMark M₀) (o : Fin 3 × Fin 3) :
    R.markPos (m.child o) = R.markPos m + R.markRadius m • repairChildOffset o := by
  rfl

/-- The hypotheses on the initial marks used by the repair induction: a small isolation
constant, a stopping scale beyond which `d(S) ≤ (a₀ / 1000) S`, initial scales at least the
stopping scale, and initial marks separated by `a₀` times the larger scale
(`geometry:initial-stars` and `geometry:trim-margins`). -/
structure TreeHyp : Prop where
  a₀_pos : 0 < R.a₀
  a₀_lt : R.a₀ < 1 / 2
  two_le_Sstar : 2 ≤ R.Sstar
  margin : ∀ S, R.Sstar ≤ S → repairHalfSide S ≤ R.a₀ / 1000 * S
  Sstar_le_scale₀ : ∀ r, R.Sstar ≤ R.scale₀ r
  sep₀ : ∀ r r', r ≠ r' → R.a₀ * max (R.scale₀ r) (R.scale₀ r') ≤ dist (R.pos₀ r) (R.pos₀ r')

namespace TreeHyp

variable {R}

theorem markScale_pos (hR : R.TreeHyp) (m : RepairMark M₀) : 0 < R.markScale m := by
  unfold markScale
  rcases Nat.eq_zero_or_eq_succ_pred m.gen with h | h
  · rw [h]
    exact lt_of_lt_of_le (by linarith [hR.two_le_Sstar]) (hR.Sstar_le_scale₀ m.root)
  · rw [h, Function.iterate_succ_apply']
    exact repairHalfSide_pos _

private theorem le_of_le_repairHalfSide {S T : ℝ} (hS : 0 < S) (hT : 2 ≤ T)
    (h : T ≤ repairHalfSide S) : T ≤ S := by
  by_cases h1 : 1 < S
  · exact h.trans (repairHalfSide_lt_self h1).le
  · have : repairHalfSide S ≤ 1 :=
      (repairHalfSide_le_rpow hS).trans
        (Real.rpow_le_one hS.le (not_lt.mp h1) rho_pos_lt_one.1.le)
    linarith

theorem Sstar_le_markScale (hR : R.TreeHyp) {m : RepairMark M₀} (hm : R.IsMark m) :
    R.Sstar ≤ R.markScale m := by
  rcases hm with h | h
  · have : m.gen = 0 := by simp [RepairMark.gen, h]
    rw [markScale, this, Function.iterate_zero_apply]
    exact hR.Sstar_le_scale₀ _
  · exact h

theorem markRadius_le (hR : R.TreeHyp) {m : RepairMark M₀} (hm : R.IsMark m) :
    R.markRadius m ≤ R.a₀ / 1000 * R.markScale m := by
  exact hR.margin _ (hR.Sstar_le_markScale hm)

/-- The removal half-side of a mark is a power of two, in particular a positive integer. -/
theorem exists_markRadius_eq_pow (hR : R.TreeHyp) {m : RepairMark M₀} (hm : R.IsMark m) :
    ∃ n : ℕ, R.markRadius m = 2 ^ n := by
  have hS : 1 ≤ R.markScale m := by linarith [hR.Sstar_le_markScale hm, hR.two_le_Sstar]
  have h0 : 0 ≤ ⌊(Exponents.rho : ℝ) * Real.logb 2 (R.markScale m)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg rho_pos_lt_one.1.le (Real.logb_nonneg (by norm_num) hS))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
  exact ⟨n, by rw [markRadius, repairHalfSide, hn, zpow_natCast]⟩

theorem isMark_child_iff (hR : R.TreeHyp) (m : RepairMark M₀) (o : Fin 3 × Fin 3) :
    R.IsMark (m.child o) ↔ R.IsMark m ∧ R.IsNonterminal m := by
  have hc : R.IsMark (m.child o) ↔ R.IsNonterminal m := by
    unfold IsMark IsNonterminal
    rw [markScale_child]
    simp [RepairMark.child]
  rw [hc]
  refine ⟨fun h => ⟨Or.inr ?_, h⟩, fun h => h.2⟩
  exact le_of_le_repairHalfSide (hR.markScale_pos m) hR.two_le_Sstar h

/-- A child is at sup distance at most the removal half-side from its parent. -/
theorem dist_markPos_child_le (hR : R.TreeHyp) {m : RepairMark M₀} (hm : R.IsMark m)
    (o : Fin 3 × Fin 3) :
    dist (R.markPos (m.child o)) (R.markPos m) ≤ R.markRadius m := by
  have h0 : 0 < R.markRadius m := repairHalfSide_pos _
  rw [markPos_child, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos h0]
  exact mul_le_of_le_one_right (repairHalfSide_pos _).le (norm_repairChildOffset_le o)

/-- Distinct children of one mark are at sup distance at least its removal half-side. -/
theorem markRadius_le_dist_markPos_child (hR : R.TreeHyp) {m : RepairMark M₀}
    (hm : R.IsMark m) {o o' : Fin 3 × Fin 3} (ho : o ≠ o') :
    R.markRadius m ≤ dist (R.markPos (m.child o)) (R.markPos (m.child o')) := by
  have h0 : 0 < R.markRadius m := repairHalfSide_pos _
  rw [markPos_child, markPos_child, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos h0]
  exact le_mul_of_one_le_right (repairHalfSide_pos _).le (one_le_norm_repairChildOffset_sub ho)

/-- **Separation invariant.**  Distinct marks of one generation are at sup distance at least
`a₀` times the larger scale. -/
theorem dist_markPos_of_gen_eq (hR : R.TreeHyp) {m m' : RepairMark M₀} (hm : R.IsMark m)
    (hm' : R.IsMark m') (hne : m ≠ m') (hgen : m.gen = m'.gen) :
    R.a₀ * max (R.markScale m) (R.markScale m') ≤ dist (R.markPos m) (R.markPos m') := by
  obtain ⟨n, hn⟩ : ∃ n, m.gen = n := ⟨_, rfl⟩
  induction n generalizing m m' with
  | zero =>
    obtain ⟨r, p⟩ := m
    obtain ⟨r', p'⟩ := m'
    have hp : p = [] := List.eq_nil_of_length_eq_zero hn
    have hp' : p' = [] := List.eq_nil_of_length_eq_zero (by
      change p.length = p'.length at hgen
      change p.length = 0 at hn
      omega)
    subst hp hp'
    have hr : r ≠ r' := fun h => hne (by rw [h])
    exact hR.sep₀ r r' hr
  | succ n ih =>
    obtain ⟨r, _ | ⟨o, p⟩⟩ := m
    · simp [RepairMark.gen] at hn
    obtain ⟨r', _ | ⟨o', p'⟩⟩ := m'
    · simp [RepairMark.gen] at hgen
    change R.IsMark (RepairMark.child ⟨r, p⟩ o) at hm
    change R.IsMark (RepairMark.child ⟨r', p'⟩ o') at hm'
    change RepairMark.child ⟨r, p⟩ o ≠ RepairMark.child ⟨r', p'⟩ o' at hne
    change (RepairMark.child ⟨r, p⟩ o).gen = (RepairMark.child ⟨r', p'⟩ o').gen at hgen
    change (RepairMark.child ⟨r, p⟩ o).gen = n + 1 at hn
    change R.a₀ * max (R.markScale (RepairMark.child ⟨r, p⟩ o))
        (R.markScale (RepairMark.child ⟨r', p'⟩ o')) ≤
      dist (R.markPos (RepairMark.child ⟨r, p⟩ o)) (R.markPos (RepairMark.child ⟨r', p'⟩ o'))
    set P : RepairMark M₀ := ⟨r, p⟩
    set P' : RepairMark M₀ := ⟨r', p'⟩
    rw [RepairMark.gen_child, RepairMark.gen_child] at hgen
    rw [RepairMark.gen_child] at hn
    have hgen' : P.gen = P'.gen := by omega
    have hn' : P.gen = n := by omega
    obtain ⟨hP, -⟩ := (hR.isMark_child_iff P o).1 hm
    obtain ⟨hP', -⟩ := (hR.isMark_child_iff P' o').1 hm'
    have ha₀ := hR.a₀_pos
    have ha₁ := hR.a₀_lt
    rw [markScale_child, markScale_child]
    by_cases hPP : P = P'
    · rw [← hPP] at hne ⊢
      have ho : o ≠ o' := fun h => hne (by rw [h])
      have hd := hR.markRadius_le_dist_markPos_child hP ho
      rw [max_self]
      have : 0 < R.markRadius P := repairHalfSide_pos _
      nlinarith
    · have hIH := ih hP hP' hPP hgen' hn'
      have h1 := hR.dist_markPos_child_le hP o
      have h2 := hR.dist_markPos_child_le hP' o'
      have h4 := dist_triangle4 (R.markPos P) (R.markPos (P.child o))
        (R.markPos (P'.child o')) (R.markPos P')
      rw [dist_comm (R.markPos P) (R.markPos (P.child o))] at h4
      set M := max (R.markScale P) (R.markScale P')
      have hSM : R.markScale P ≤ M := le_max_left _ _
      have hSM' : R.markScale P' ≤ M := le_max_right _ _
      have hd : R.markRadius P ≤ R.a₀ / 1000 * M :=
        (hR.markRadius_le hP).trans (mul_le_mul_of_nonneg_left hSM (by positivity))
      have hd' : R.markRadius P' ≤ R.a₀ / 1000 * M :=
        (hR.markRadius_le hP').trans (mul_le_mul_of_nonneg_left hSM' (by positivity))
      have hmax : max (R.markRadius P) (R.markRadius P') ≤ R.a₀ / 1000 * M := max_le hd hd'
      have hmax0 : 0 ≤ max (R.markRadius P) (R.markRadius P') :=
        (repairHalfSide_pos _).le.trans (le_max_left _ _)
      have hX : R.a₀ / 1000 * M = R.a₀ * M / 1000 := by ring
      have hXp : 0 ≤ R.a₀ * M := by
        have := (hR.markScale_pos P).trans_le hSM
        positivity
      have hamax : R.a₀ * max (R.markRadius P) (R.markRadius P') ≤
          max (R.markRadius P) (R.markRadius P') := by nlinarith
      linarith

/-- **Descendant displacement.**  A descendant mark together with its removal square stays
within twice the removal half-side of its ancestor. -/
theorem dist_markPos_descendant_add_markRadius_le (hR : R.TreeHyp) {m : RepairMark M₀}
    (hm : R.IsMark m) (q : List (Fin 3 × Fin 3)) (hq : R.IsMark (m.descend q)) :
    dist (R.markPos (m.descend q)) (R.markPos m) + R.markRadius (m.descend q) ≤
      2 * R.markRadius m := by
  have ha₁ := hR.a₀_lt
  have key : ∀ q : List (Fin 3 × Fin 3), R.IsMark (m.descend q) →
      dist (R.markPos (m.descend q)) (R.markPos m) + 2 * R.markRadius (m.descend q) ≤
        2 * R.markRadius m := by
    intro q
    induction q with
    | nil => intro _; simp [RepairMark.descend]
    | cons o q ih =>
      intro h
      have hchild : m.descend (o :: q) = (m.descend q).child o := rfl
      rw [hchild] at h ⊢
      obtain ⟨hq', -⟩ := (hR.isMark_child_iff _ o).1 h
      have h1 := hR.dist_markPos_child_le hq' o
      have h2 := hR.markRadius_le h
      rw [markScale_child] at h2
      have h3 := dist_triangle (R.markPos ((m.descend q).child o)) (R.markPos (m.descend q))
        (R.markPos m)
      have h0 : 0 < R.markRadius (m.descend q) := repairHalfSide_pos _
      have h5 : R.a₀ / 1000 * R.markRadius (m.descend q) ≤ R.markRadius (m.descend q) / 2 := by
        nlinarith
      linarith [ih hq']
  have := key q hq
  have : 0 < R.markRadius (m.descend q) := repairHalfSide_pos _
  linarith

/-- The generations of the marks with a given root are bounded. -/
theorem exists_gen_le (hR : R.TreeHyp) (r : M₀) :
    ∃ N : ℕ, ∀ m : RepairMark M₀, R.IsMark m → m.root = r → m.gen ≤ N := by
  obtain ⟨C, -, hC⟩ := exists_repair_depth_bound (by linarith [hR.two_le_Sstar] : 1 < R.Sstar)
  have hS : 0 < R.scale₀ r :=
    lt_of_lt_of_le (by linarith [hR.two_le_Sstar]) (hR.Sstar_le_scale₀ r)
  refine ⟨⌈C + C * Real.log (Real.log (Real.exp (Real.exp 1) + R.scale₀ r))⌉₊,
    fun m hm hr => ?_⟩
  have h := hC _ hS m.gen (hr ▸ hR.Sstar_le_markScale hm)
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- The marks with a given root and generation at most `G`, as images of offset lists. -/
private def marksUpTo (r : M₀) (G : ℕ) : Finset (RepairMark M₀) := by
  classical
  exact (Finset.range (G + 1)).biUnion fun j =>
    (Finset.univ : Finset (Fin j → Fin 3 × Fin 3)).image fun f => ⟨r, List.ofFn f⟩

private theorem mem_marksUpTo {r : M₀} {G : ℕ} {m : RepairMark M₀} (hr : m.root = r)
    (hG : m.gen ≤ G) : m ∈ marksUpTo r G := by
  classical
  obtain ⟨r', p⟩ := m
  change r' = r at hr
  subst hr
  simp only [marksUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨p.length, Nat.lt_succ_of_le hG, p.get, by rw [List.ofFn_get]⟩

private theorem card_marksUpTo_le (r : M₀) (G : ℕ) :
    ((marksUpTo r G).card : ℝ) ≤ ∑ j ∈ Finset.range (G + 1), (9 : ℝ) ^ j := by
  classical
  have h : (marksUpTo r G).card ≤ ∑ j ∈ Finset.range (G + 1), 9 ^ j := by
    unfold marksUpTo
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
    refine Finset.card_image_le.trans ?_
    simp
  exact_mod_cast h

/-- Only finitely many marks are created from finitely many initial marks. -/
theorem finite_isMark (hR : R.TreeHyp) [Finite M₀] : {m : RepairMark M₀ | R.IsMark m}.Finite := by
  have : {m : RepairMark M₀ | R.IsMark m} = ⋃ r, {m | R.IsMark m ∧ m.root = r} := by
    ext m; simp
  rw [this]
  refine Set.finite_iUnion fun r => ?_
  obtain ⟨N, hN⟩ := hR.exists_gen_le r
  exact (marksUpTo r N).finite_toSet.subset fun m hm => mem_marksUpTo hm.2 (hN m hm.1 hm.2)

/-- **Descendant count.**  The marks with a given root number at most `∑_{j ≤ G} 9 ^ j`, where
`G` is a generation still at or above the stopping scale. -/
theorem exists_ncard_isMark_root_le (hR : R.TreeHyp) (r : M₀) :
    ∃ G : ℕ, (G = 0 ∨ R.Sstar ≤ repairHalfSide^[G] (R.scale₀ r)) ∧
      ({m : RepairMark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ) ≤
        ∑ j ∈ Finset.range (G + 1), (9 : ℝ) ^ j := by
  classical
  obtain ⟨N, hN⟩ := hR.exists_gen_le r
  let P : ℕ → Prop := fun j => R.Sstar ≤ repairHalfSide^[j] (R.scale₀ r)
  have hP0 : P 0 := hR.Sstar_le_scale₀ r
  refine ⟨Nat.findGreatest P N, Or.inr (Nat.findGreatest_spec (Nat.zero_le N) hP0), ?_⟩
  have hsub : {m : RepairMark M₀ | R.IsMark m ∧ m.root = r} ⊆
      ↑(marksUpTo r (Nat.findGreatest P N)) := by
    rintro m ⟨hm, hr⟩
    refine mem_marksUpTo hr (Nat.le_findGreatest (hN m hm hr) ?_)
    have := hR.Sstar_le_markScale hm
    rw [markScale, hr] at this
    exact this
  calc ({m : RepairMark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ)
      ≤ ((↑(marksUpTo r (Nat.findGreatest P N)) : Set (RepairMark M₀)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ _ := by rw [Set.ncard_coe_finset]; exact card_marksUpTo_le r _

end TreeHyp

end RepairSetup

end OpenAI.Geometry
