import AreaLawRefactored.S09_Scanner.Histories.Rounds

/-!
# §9.1 Lemma 9.1 (1), (2): splitting supports, prefixes, cuts, counts (D9.8.1–9)

Digest `digest/09-scanner.md` D9.8.1–D9.8.9, paper `paper/sections/08-scanner.tex` 223–300.
Graph-level (Map.md, Dimension: `any d`).
-/

open scoped Matrix
open Finset Arealaw

namespace AreaLaw.Scanner

universe u

open Transport (MeanTree)
open Comparators (physReg Site)

namespace Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ)

/-! ## D9.8.1–4 Splitting supports (item 1) -/

theorem exists_walk_of_mem_ball {x y : σ} {ρ : ℕ} (h : y ∈ GraphDomain.ball S.G S.Λ x ρ) :
    ∃ (hy : y ∈ S.Λ) (hx : x ∈ S.Λ) (p : (S.G.induce (S.Λ : Set σ)).Walk ⟨y, hy⟩ ⟨x, hx⟩),
      p.length ≤ ρ := by
  obtain ⟨hy, hd⟩ := (GraphDomain.mem_ball S.G).1 h
  unfold GraphDomain.domainEDist at hd
  split_ifs at hd with hxy
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top ρ) hd)
    have h2 : (p.length : ℕ∞) ≤ ρ := hp ▸ hd
    exact ⟨hxy.1, hxy.2, p, by exact_mod_cast h2⟩
  · simp at hd

theorem mem_up {Q : Finset S.Λ} {x : S.Λ} (hx : x ∈ Q) : x.1 ∈ up Q :=
  Finset.mem_map_of_mem _ hx

theorem init_near {g r : ℕ} {x : S.Λ} (hA : x.1 ∈ S.A) (hd : S.dep x ≤ S.lo g r) :
    S.init g r x = some false := by
  simp [init, hA, hd]

theorem init_far {g r : ℕ} {x : S.Λ} (hd : x.1 ∈ S.A → S.hi g r < S.dep x) :
    S.init g r x = some true := by
  have := S.hi_eq g r
  by_cases hA : x.1 ∈ S.A
  · have := hd hA
    simp only [init, hA, not_true_eq_false, if_false]
    rw [if_neg (by omega), if_pos this]
  · simp [init, hA]

theorem part_contains (s : S.St) (g : Fin S.K) (Q : Finset S.Λ) :
    (S.Γ.part s g).Contains (physReg Q) ↔ Q ⊆ S.X ∪ S.U (S.leafState s g) ∨
      Q ⊆ middle (S.leafState s g) ∨ Q ⊆ side (S.leafState s g) true :=
  contains_physReg

theorem part_splitsToP (s : S.St) (g : Fin S.K) (Q : Finset S.Λ) :
    (S.Γ.part s g).SplitsToP (physReg Q) ↔ (Q ∩ middle (S.leafState s g)).Nonempty ∧
      (Q ∩ (S.X ∪ S.U (S.leafState s g))).Nonempty ∧ Disjoint Q (side (S.leafState s g) true) :=
  splitsToP_physReg

theorem part_splitsToF (s : S.St) (g : Fin S.K) (Q : Finset S.Λ) :
    (S.Γ.part s g).SplitsToF (physReg Q) ↔ (Q ∩ middle (S.leafState s g)).Nonempty ∧
      (Q ∩ side (S.leafState s g) true).Nonempty ∧ Disjoint Q (S.X ∪ S.U (S.leafState s g)) :=
  splitsToF_physReg

theorem leafState_X_union_U (s : S.St) (g : Fin S.K) :
    S.X ∪ S.U (S.leafState s g) = side (S.leafState s g) false := by
  obtain ⟨t, h, -, hs⟩ := S.exists_leafState s
  rw [hs]
  exact S.X_union_U (S.X_subset_side h g)

theorem Xt_eq_ball (i : S.Term) {x : S.Λ} (hx : x ∈ S.Xt i) (hx₀ : x.1 ∈ S.S₀) :
    S.Xt i = S.ball i := by
  unfold Xt GraphDomain.truncatedSupport at hx ⊢
  have h2 : GraphDomain.setDist S.G S.Λ S.S₀ (S.a i) ≤
      GraphDomain.domainEDist S.G S.Λ (S.a i) x := Finset.inf_le hx₀
  split_ifs at hx ⊢ with hd
  · exfalso
    rw [mem_subtype] at hx
    rw [hd] at h2
    exact (mem_filter.1 hx).2 (top_le_iff.1 h2)
  · rw [mem_subtype] at hx
    have h1 := ((GraphDomain.mem_ball S.G).1 hx).2
    rw [S.domainEDist_comm] at h2
    have h3 := h2.trans h1
    rw [← ENat.natCast_toNat hd] at h3
    have h4 : (GraphDomain.setDist S.G S.Λ S.S₀ (S.a i)).toNat ≤
        GraphDomain.radius S.r₀ (GraphDomain.setDist S.G S.Λ S.S₀ (S.a i)).toNat := by
      exact_mod_cast h3
    have h5 : GraphDomain.radius S.r₀ (GraphDomain.setDist S.G S.Λ S.S₀ (S.a i)).toNat =
        S.r₀ := by
      unfold GraphDomain.radius at h4 ⊢
      rcases le_total S.r₀ ((GraphDomain.setDist S.G S.Λ S.S₀ (S.a i)).toNat / 2) with h6 | h6
      · rw [max_eq_right h6] at h4 ⊢; omega
      · exact max_eq_left h6
    rw [h5]
    rfl

section Supports

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

theorem Hyp.hi_add_lt_lo {g g' : ℕ} (hg : g < g') {r : ℕ} (hr : r < S.m) (r' : ℕ) :
    S.hi g r + 2 * S.r₀ < S.lo g' r' := by
  have h1 : 8 * (g + 1) * S.m ≤ 8 * g' * S.m := Nat.mul_le_mul_right _ (by omega)
  have h2 : 8 * (g + 1) * S.m = 8 * g * S.m + 8 * S.m := by ring
  have := H.m_ge
  have := H.r₀_le
  simp only [hi, lo]
  omega

/-- D9.28.2. Sites outside `S₀` are on the far side of every band at all times. -/
theorem Hyp.far_of_not_mem_S₀ {t : ℕ} (h : S.Hist t) (g : Fin S.K) {x : S.Λ}
    (hx : x.1 ∉ S.S₀) : S.stateAt t h g x = some true := by
  apply S.stateAt_of_init
  apply S.init_far
  intro hA
  have := H.hi_add_le g (S.offset t h g)
  simp only [S₀, mem_filter, not_and, not_le] at hx
  have := hx hA
  omega

/-- D9.8.2. A graph `r₀`-ball meeting `S₀` lies in `A` (clearance `dist(T, Z) > 2L + 10 r₀`). -/
theorem Hyp.up_ball_subset_A (i : S.Term) {x : S.Λ} (hx : x ∈ S.ball i) (hx₀ : x.1 ∈ S.S₀) :
    up (S.ball i) ⊆ S.A := by
  intro y hy
  obtain ⟨y, hyb, rfl⟩ := Finset.mem_map.1 hy
  by_contra hyA
  obtain ⟨hx', ha, p₁, hp₁⟩ := S.exists_walk_of_mem_ball (mem_subtype.1 hx)
  obtain ⟨hy', ha', p₂, hp₂⟩ := S.exists_walk_of_mem_ball (mem_subtype.1 hyb)
  have hxA : x.1 ∈ S.A := (mem_filter.1 hx₀).1
  have hxL := (mem_filter.1 hx₀).2
  obtain ⟨z, hz, p', hp'⟩ := GraphDomain.exists_cutEndpoints_of_walk S.G
    (p₁.append p₂.reverse) (D := S.A) (by simp only [hxA, true_iff]; exact hyA)
  have h1 := S.dep_le_walk H.hlip p'.reverse
  have hcl := H.tg.clearance z hz
  simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_append] at h1 hp'
  omega

/-- D9.8.3. At times `t ≤ 2nm` a ball in `A` never meets both sides of a band (the fronts plus
leads are `≥ 2m > 2 r₀` apart). -/
theorem Hyp.not_near_far {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) (i : S.Term)
    (hA : up (S.ball i) ⊆ S.A) {x y : S.Λ} (hx : x ∈ S.ball i) (hy : y ∈ S.ball i)
    (hxn : S.stateAt t h g x = some false) (hyf : S.stateAt t h g y = some true) : False := by
  have h1 := H.near_dep_le ht h g hxn (hA (S.mem_up hx))
  have h2 := H.far_dep_ge ht h g hyf (hA (S.mem_up hy))
  have h3 := (S.dep_le_of_mem_ball H.hlip (mem_subtype.1 hx)).2
  have h4 := (S.dep_le_of_mem_ball H.hlip (mem_subtype.1 hy)).1
  have := S.hi_eq g (S.offset t h g)
  have := H.m_ge
  omega

/-- D9.8.4. A ball in `A` meeting the middle of band `g` lies on one side of every other band
(windows of consecutive bands are `≥ 3m - O(r₀)` apart). -/
theorem Hyp.ball_side_of_middle {t t' : ℕ} (h : S.Hist t) (h' : S.Hist t') {g g' : Fin S.K}
    (hg : g ≠ g') (i : S.Term) (hA : up (S.ball i) ⊆ S.A) {y : S.Λ} (hy : y ∈ S.ball i)
    (hym : S.stateAt t h g y = none) :
    S.ball i ⊆ side (S.stateAt t' h' g') false ∨ S.ball i ⊆ side (S.stateAt t' h' g') true := by
  have hinit : S.init g (S.offset t h g) y = none := by
    rcases hi : S.init g (S.offset t h g) y with _ | b
    · rfl
    · rw [S.stateAt_of_init h g hi] at hym; cases hym
  obtain ⟨-, hlo, hhi⟩ := S.init_eq_none hinit
  have hy1 := (S.dep_le_of_mem_ball H.hlip (mem_subtype.1 hy)).1
  have hy2 := (S.dep_le_of_mem_ball H.hlip (mem_subtype.1 hy)).2
  rcases lt_or_gt_of_ne hg with hlt | hlt
  · left
    have := H.hi_add_lt_lo hlt (S.offset t h g).2 (S.offset t' h' g')
    intro x hx
    have := (S.dep_le_of_mem_ball H.hlip (mem_subtype.1 hx)).1
    rw [mem_side]
    exact S.stateAt_of_init h' g' (S.init_near (hA (S.mem_up hx)) (by omega))
  · right
    have := H.hi_add_lt_lo hlt (S.offset t' h' g').2 (S.offset t h g)
    intro x hx
    have := (S.dep_le_of_mem_ball H.hlip (mem_subtype.1 hx)).2
    rw [mem_side]
    exact S.stateAt_of_init h' g' (S.init_far fun _ => by omega)

/-- D9.8.1–4. In a band at time `t ≤ 2nm` a designated support lies in one part, or it is the
`r₀`-ball, lies in `A`, meets `Y` and exactly one side. -/
theorem Hyp.classify {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) (i : S.Term) :
    (S.Xt i ⊆ side (S.stateAt t h g) false ∨ S.Xt i ⊆ middle (S.stateAt t h g) ∨
      S.Xt i ⊆ side (S.stateAt t h g) true) ∨
    (S.Xt i = S.ball i ∧ up (S.Xt i) ⊆ S.A ∧ (S.Xt i ∩ middle (S.stateAt t h g)).Nonempty ∧
      (((S.Xt i ∩ side (S.stateAt t h g) false).Nonempty ∧
        Disjoint (S.Xt i) (side (S.stateAt t h g) true)) ∨
       ((S.Xt i ∩ side (S.stateAt t h g) true).Nonempty ∧
        Disjoint (S.Xt i) (side (S.stateAt t h g) false)))) := by
  set st := S.stateAt t h g
  by_cases hS : ∃ x ∈ S.Xt i, x.1 ∈ S.S₀
  swap
  · simp only [not_exists, not_and] at hS
    exact Or.inl (Or.inr (Or.inr fun x hx => mem_side.2 (H.far_of_not_mem_S₀ h g (hS x hx))))
  obtain ⟨x₀, hx₀, hx₀S⟩ := hS
  have hball := S.Xt_eq_ball i hx₀ hx₀S
  have hA := H.up_ball_subset_A i (hball ▸ hx₀) hx₀S
  rw [hball]
  have hnf : ¬ ((S.ball i ∩ side st false).Nonempty ∧ (S.ball i ∩ side st true).Nonempty) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rw [mem_inter, mem_side] at hx hy
    exact H.not_near_far ht h g i hA hx.1 hy.1 hx.2 hy.2
  have hdisj : ∀ b, ¬ (S.ball i ∩ side st b).Nonempty → Disjoint (S.ball i) (side st b) :=
    fun b hb => Finset.disjoint_iff_inter_eq_empty.2 (Finset.not_nonempty_iff_eq_empty.1 hb)
  have hsub : ∀ x ∈ S.ball i, st x = some false ∨ st x = none ∨ st x = some true := by
    intro x _
    rcases st x with _ | _ | _ <;> simp
  by_cases hm : (S.ball i ∩ middle st).Nonempty
  · by_cases hn : (S.ball i ∩ side st false).Nonempty
    · exact Or.inr ⟨rfl, hA, hm, Or.inl ⟨hn, hdisj true fun hf => hnf ⟨hn, hf⟩⟩⟩
    · by_cases hf : (S.ball i ∩ side st true).Nonempty
      · exact Or.inr ⟨rfl, hA, hm, Or.inr ⟨hf, hdisj false hn⟩⟩
      · refine Or.inl (Or.inr (Or.inl fun x hx => ?_))
        rcases hsub x hx with h1 | h1 | h1
        · exact absurd ⟨x, mem_inter.2 ⟨hx, mem_side.2 h1⟩⟩ hn
        · exact mem_middle.2 h1
        · exact absurd ⟨x, mem_inter.2 ⟨hx, mem_side.2 h1⟩⟩ hf
  · refine Or.inl ?_
    by_cases hn : (S.ball i ∩ side st false).Nonempty
    · refine Or.inl fun x hx => ?_
      rcases hsub x hx with h1 | h1 | h1
      · exact mem_side.2 h1
      · exact absurd ⟨x, mem_inter.2 ⟨hx, mem_middle.2 h1⟩⟩ hm
      · exact absurd ⟨hn, ⟨x, mem_inter.2 ⟨hx, mem_side.2 h1⟩⟩⟩ hnf
    · refine Or.inr (Or.inr fun x hx => ?_)
      rcases hsub x hx with h1 | h1 | h1
      · exact absurd ⟨x, mem_inter.2 ⟨hx, mem_side.2 h1⟩⟩ hn
      · exact absurd ⟨x, mem_inter.2 ⟨hx, mem_middle.2 h1⟩⟩ hm
      · exact mem_side.2 h1

theorem Hyp.classify_leaf (s : S.St) (g : Fin S.K) (i : S.Term) :
    (S.Γ.part s g).Contains (physReg (S.Xt i)) ∨
    (S.Xt i = S.ball i ∧ up (S.Xt i) ⊆ S.A ∧ (S.Xt i ∩ middle (S.leafState s g)).Nonempty ∧
      ((S.Γ.part s g).SplitsToP (physReg (S.Xt i)) ∨
        (S.Γ.part s g).SplitsToF (physReg (S.Xt i)))) := by
  obtain ⟨t, h, ht, hs⟩ := S.exists_leafState s
  rw [S.part_contains, S.part_splitsToP, S.part_splitsToF, S.leafState_X_union_U, hs]
  rcases H.classify ht h g i with h1 | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h2, h3, h4.imp (fun h5 => ⟨h3, h5.1, h5.2⟩) (fun h5 => ⟨h3, h5.1, h5.2⟩)⟩

/-- **Lemma 9.1 (1).** -/
theorem Hyp.item1 : S.Item1 where
  ball_of_split s g i hs := by
    rcases H.classify_leaf s g i with h1 | h1
    · exact absurd h1 hs
    · exact ⟨h1.1, h1.2.1⟩
  supportCompatible t nl E hE j i g := by
    rw [hE i]
    simp only [S.round_leafPart]
    rcases H.classify_leaf ⟨t, j⟩ g i with h1 | ⟨hb, hA, ⟨y, hy⟩, hsp⟩
    · exact Or.inl h1
    · refine Or.inr ⟨hsp, fun g' hg' => ?_⟩
      obtain ⟨t', h', -, hs⟩ := S.exists_leafState (⟨t, j⟩ : S.St)
      rw [S.part_contains, S.leafState_X_union_U]
      rw [hs] at hy ⊢
      rw [hb] at hy ⊢
      rw [mem_inter, mem_middle] at hy
      rw [hb] at hA
      rcases H.ball_side_of_middle h' h' (Ne.symm hg') i hA hy.1 hy.2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inr h2)
  move_ball t h c g := by
    change ∃ x : σ, (S.toMove (S.step g (S.offset t h g) t (c g) (S.stateAt t h g))).subsystem ⊆ _
    rcases hs : S.step g (S.offset t h g) t (c g) (S.stateAt t h g) with _ | ⟨b, x⟩
    · exact ⟨S.a ∅, Finset.empty_subset _⟩
    · have hx : ∃ z : σ, x ⊆ (GraphDomain.ball S.G S.Λ z S.r₀).subtype (· ∈ S.Λ) := by
        rcases S.step_eq_some hs with ⟨-, y, -, rfl⟩ | ⟨-, i, -, rfl, -⟩
        · refine ⟨y.1, fun z hz => ?_⟩
          rw [mem_singleton] at hz
          subst hz
          rw [mem_subtype, GraphDomain.mem_ball]
          refine ⟨z.2, ?_⟩
          rw [GraphDomain.domainEDist_eq S.G z z]
          simp
        · exact ⟨S.a i, inter_subset_left⟩
      obtain ⟨z, hz⟩ := hx
      refine ⟨z, ?_⟩
      cases b <;> exact physReg_subset_iff.2 hz
  admissible := S.round_isAdmissible
  crossBand nl _ d _ τ hτ k t := S.round_crossBandCommute nl d τ hτ k t
  far s g x hx := by
    obtain ⟨t, h, -, hs⟩ := S.exists_leafState s
    change x ∈ side (S.leafState s g) true
    rw [hs, mem_side]
    exact H.far_of_not_mem_S₀ h g (by simpa using (mem_sdiff.1 (mem_subtype.1 hx)).2)

end Supports

/-! ## D9.8.5–8 Prefixes, cuts, counts (item 2) -/

theorem mem_take_row {j k : ℕ} {x : S.Λ} :
    x ∈ (S.row j).take k ↔ S.dep x = j ∧ S.idx x < k := by
  constructor
  · intro h
    have hx : S.dep x = j := S.mem_row.1 (List.mem_of_mem_take h)
    refine ⟨hx, ?_⟩
    have h1 := List.idxOf_append_of_mem (l₂ := (S.row j).drop k) h
    rw [List.take_append_drop] at h1
    unfold idx
    rw [hx, h1]
    exact (List.idxOf_lt_length_of_mem h).trans_le (List.length_take_le _ _)
  · rintro ⟨rfl, hk⟩
    rw [List.mem_iff_getElem?]
    exact ⟨S.idx x, by rw [List.getElem?_take]; simp [hk, S.row_idx]⟩

theorem mem_pre {j k : ℕ} (hj : 1 ≤ j) {x : S.Λ} :
    x ∈ S.pre j k ↔ x.1 ∈ S.A ∧ 0 < S.dep x ∧ (S.dep x < j ∨ (S.dep x = j ∧ S.idx x < k)) := by
  simp only [pre, mem_union, mem_filter, mem_univ, true_and, List.mem_toFinset, S.mem_take_row]
  constructor
  · rintro (⟨hA, h0, hj'⟩ | ⟨⟨hd, hk⟩, hA⟩)
    · exact ⟨hA, h0, Or.inl hj'⟩
    · exact ⟨hA, by omega, Or.inr ⟨hd, hk⟩⟩
  · rintro ⟨hA, h0, hj' | hj'⟩
    · exact Or.inl ⟨hA, h0, hj'⟩
    · exact Or.inr ⟨hj', hA⟩

theorem mem_prefixes {B : Finset S.Λ} :
    B ∈ S.prefixes ↔ ∃ j k, 1 ≤ j ∧ j ≤ S.L ∧ k ≤ S.n ∧ B = S.pre j k := by
  simp only [prefixes, mem_image, mem_product, mem_Icc, mem_range, Prod.exists]
  constructor
  · rintro ⟨j, k, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨j, k, h1, h2, by omega, rfl⟩
  · rintro ⟨j, k, h1, h2, h3, rfl⟩
    exact ⟨j, k, ⟨⟨h1, h2⟩, by omega⟩, rfl⟩

theorem prefixes_nested : ∀ B ∈ S.prefixes, ∀ B' ∈ S.prefixes, B ⊆ B' ∨ B' ⊆ B := by
  intro B hB B' hB'
  obtain ⟨j, k, hj, -, -, rfl⟩ := S.mem_prefixes.1 hB
  obtain ⟨j', k', hj', -, -, rfl⟩ := S.mem_prefixes.1 hB'
  have key : ∀ j k j' k', 1 ≤ j → 1 ≤ j' → (j < j' ∨ (j = j' ∧ k ≤ k')) →
      S.pre j k ⊆ S.pre j' k' := by
    intro j k j' k' hj hj' hlt x hx
    rw [S.mem_pre hj] at hx
    rw [S.mem_pre hj']
    refine ⟨hx.1, hx.2.1, ?_⟩
    omega
  rcases lt_trichotomy j j' with h | rfl | h
  · exact Or.inl (key _ _ _ _ hj hj' (Or.inl h))
  · rcases le_total k k' with h | h
    · exact Or.inl (key _ _ _ _ hj hj (Or.inr ⟨rfl, h⟩))
    · exact Or.inr (key _ _ _ _ hj hj (Or.inr ⟨rfl, h⟩))
  · exact Or.inr (key _ _ _ _ hj' hj (Or.inl h))

theorem prefixes_disjoint : ∀ B ∈ S.prefixes, Disjoint B S.X := by
  intro B hB
  obtain ⟨j, k, hj, -, -, rfl⟩ := S.mem_prefixes.1 hB
  rw [Finset.disjoint_left]
  intro x hx hxX
  have h1 := ((S.mem_pre hj).1 hx).2.1
  simp only [X, mem_subtype, mem_filter] at hxX
  omega

theorem prefixes_rows : ∀ B ∈ S.prefixes, ∃ j, 1 ≤ j ∧ j ≤ S.L ∧
    (S.A.filter fun x => 0 < S.dep x ∧ S.dep x < j).subtype (· ∈ S.Λ) ⊆ B ∧
    B ⊆ (S.A.filter fun x => 0 < S.dep x ∧ S.dep x ≤ j).subtype (· ∈ S.Λ) := by
  intro B hB
  obtain ⟨j, k, hj, hjL, -, rfl⟩ := S.mem_prefixes.1 hB
  refine ⟨j, hj, hjL, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [mem_subtype, mem_filter] at hx
    exact (S.mem_pre hj).2 ⟨hx.1, hx.2.1, Or.inl hx.2.2⟩
  · rw [S.mem_pre hj] at hx
    simp only [mem_subtype, mem_filter]
    exact ⟨hx.1, hx.2.1, by omega⟩

theorem mem_A_of_ne_far {t : ℕ} (h : S.Hist t) (g : Fin S.K) {x : S.Λ}
    (hx : S.stateAt t h g x ≠ some true) : x.1 ∈ S.A :=
  (S.mem_A_of_init_ne fun h1 => hx (S.stateAt_of_init h g h1)).1

section Prefixes

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

theorem Hyp.card_window {j₀ c : ℕ} (h1 : 1 ≤ j₀) (h2 : j₀ + c ≤ S.L) :
    #(univ.filter fun x : S.Λ => j₀ ≤ S.dep x ∧ S.dep x ≤ j₀ + c) ≤ (c + 1) * S.n := by
  calc #(univ.filter fun x : S.Λ => j₀ ≤ S.dep x ∧ S.dep x ≤ j₀ + c)
      ≤ #((Icc j₀ (j₀ + c)).biUnion fun j => univ.filter fun x : S.Λ => S.dep x = j) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp only [mem_biUnion, mem_Icc, mem_filter, mem_univ, true_and]
        exact ⟨S.dep x, hx, rfl⟩
    _ ≤ ∑ j ∈ Icc j₀ (j₀ + c), #(univ.filter fun x : S.Λ => S.dep x = j) := card_biUnion_le
    _ ≤ ∑ _j ∈ Icc j₀ (j₀ + c), S.n := by
        apply sum_le_sum
        intro j hj
        rw [mem_Icc] at hj
        rw [← Finset.length_toList]
        exact H.length_row_le (by omega) (by omega)
    _ = (c + 1) * S.n := by
        rw [sum_const, Nat.card_Icc, smul_eq_mul]
        congr 1
        omega

/-- Depths of a set of depths `W ⊆ [1, L]` hold at most `|W| n` sites. -/
theorem Hyp.card_depths (W : Finset ℕ) (hW : ∀ j ∈ W, 1 ≤ j ∧ j ≤ S.L) :
    #(univ.filter fun x : S.Λ => S.dep x ∈ W) ≤ #W * S.n := by
  calc #(univ.filter fun x : S.Λ => S.dep x ∈ W)
      ≤ #(W.biUnion fun j => univ.filter fun x : S.Λ => S.dep x = j) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp only [mem_biUnion, mem_filter, mem_univ, true_and]
        exact ⟨S.dep x, hx, rfl⟩
    _ ≤ ∑ j ∈ W, #(univ.filter fun x : S.Λ => S.dep x = j) := card_biUnion_le
    _ ≤ ∑ _j ∈ W, S.n := by
        apply sum_le_sum
        intro j hj
        rw [← Finset.length_toList]
        exact H.length_row_le (hW j hj).1 (hW j hj).2
    _ = #W * S.n := by rw [sum_const, smul_eq_mul]

theorem Hyp.near_of_dep_lt {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {y : S.Λ}
    (hA : y.1 ∈ S.A)
    (hy : S.dep y < S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n) :
    S.stateAt t h g y = some false := by
  by_cases hlo : S.dep y ≤ S.lo g (S.offset t h g)
  · exact S.stateAt_of_init h g (S.init_near hA hlo)
  have hdiv := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hidx := H.idx_lt (y := y) (by omega) (by omega)
  have h1 : S.n * (S.dep y - S.lo g (S.offset t h g) - 1 + 1) ≤
      S.n * (sideFills (fills t) false / S.n) := Nat.mul_le_mul_left _ (by omega)
  have h2 := Nat.mul_div_le (sideFills (fills t) false) S.n
  have h3 : S.n * (S.dep y - S.lo g (S.offset t h g) - 1 + 1) =
      S.n * (S.dep y - S.lo g (S.offset t h g) - 1) + S.n := by ring
  exact H.consumed_near ht h g hA (by omega) (by omega) (by omega)

/-- D9.8.5. The near sandwich: `pre(j_P, t_P mod n) ⊆ U ⊆ pre(j_P, ·) ∪ (rows j_P … j_P + D + r₀)`.
-/
theorem Hyp.U_sandwich {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) :
    S.pre (S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n)
        (sideFills (fills t) false % S.n) ⊆ S.U (S.stateAt t h g) ∧
      S.U (S.stateAt t h g) \ S.pre (S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n)
        (sideFills (fills t) false % S.n) ⊆
      univ.filter fun x : S.Λ =>
        S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n ≤ S.dep x ∧
        S.dep x ≤ S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n +
          (S.D + S.r₀) := by
  have hdiv := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hn := H.n_pos
  have hm := H.m_ge
  have := int_div_nonneg (sideFills (fills t) false) S.n
  constructor
  · intro x hx
    rw [S.mem_pre (by omega)] at hx
    obtain ⟨hA, h0, hx | ⟨hx, hk⟩⟩ := hx
    · refine mem_sdiff.2 ⟨mem_side.2 (H.near_of_dep_lt ht h g hA hx), fun hX => ?_⟩
      simp only [X, mem_subtype, mem_filter] at hX
      omega
    · refine mem_sdiff.2 ⟨mem_side.2 ?_, fun hX => ?_⟩
      · have h1 := Nat.div_add_mod (sideFills (fills t) false) S.n
        refine H.consumed_near ht h g hA (by omega) (by omega) ?_
        have : S.dep x - S.lo g (S.offset t h g) - 1 = (sideFills (fills t) false) / S.n := by omega
        rw [this]
        have := Nat.mod_lt (sideFills (fills t) false) hn
        omega
      · simp only [X, mem_subtype, mem_filter] at hX
        omega
  · intro x hx
    obtain ⟨hxU, hxB⟩ := mem_sdiff.1 hx
    obtain ⟨hxn, hxX⟩ := mem_sdiff.1 hxU
    rw [mem_side] at hxn
    have hA := S.mem_A_of_ne_far h g (by rw [hxn]; simp)
    have hlead := S.lead H.hlip t h g false x hxn hA
    rw [odep_false, front_false] at hlead
    push_cast at hlead
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨?_, by omega⟩
    by_contra hc
    apply hxB
    rw [S.mem_pre (by omega)]
    refine ⟨hA, ?_, Or.inl (by omega)⟩
    by_contra h0
    apply hxX
    simp only [X, mem_subtype, mem_filter]
    exact ⟨hA, by omega⟩

/-- D9.8.5. The far sandwich: `pre(j_F) ⊇ U Y ⊇ pre(j_F) \ (rows j_F - D - r₀ … j_F)`, `j_F` the
far front row, the assigned far part a suffix of the slot order. -/
theorem Hyp.UY_sandwich {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) :
    S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) ⊆
        S.pre (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n)
          (S.n - sideFills (fills t) true % S.n) ∧
      S.pre (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n)
          (S.n - sideFills (fills t) true % S.n) \
        (S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g)) ⊆
      univ.filter fun x : S.Λ =>
        S.hi g (S.offset t h g) - sideFills (fills t) true / S.n - (S.D + S.r₀) ≤ S.dep x ∧
        S.dep x ≤ S.hi g (S.offset t h g) - sideFills (fills t) true / S.n - (S.D + S.r₀) +
          (S.D + S.r₀) := by
  have hdiv := S.sideFills_div_le ht true
  have hdivP := S.sideFills_div_le ht false
  have := int_div_nonneg (sideFills (fills t) false) S.n
  have := int_div_nonneg (sideFills (fills t) true) S.n
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hn := H.n_pos
  have hm := H.m_ge
  have hj₂ : 1 ≤ S.hi g (S.offset t h g) - (sideFills (fills t) true) / S.n := by
    have := S.lo_ge g (S.offset t h g); omega
  constructor
  · intro x hx
    rw [S.mem_pre hj₂]
    rcases mem_union.1 hx with hxU | hxm
    · obtain ⟨hxn, hxX⟩ := mem_sdiff.1 hxU
      rw [mem_side] at hxn
      have hA := S.mem_A_of_ne_far h g (by rw [hxn]; simp)
      have hlead := S.lead H.hlip t h g false x hxn hA
      rw [odep_false, front_false] at hlead
      push_cast at hlead
      refine ⟨hA, ?_, Or.inl (by omega)⟩
      by_contra h0
      apply hxX
      simp only [X, mem_subtype, mem_filter]
      exact ⟨hA, by omega⟩
    · rw [mem_middle] at hxm
      obtain ⟨hA, hlo, hhi'⟩ := H.middle_bounds ht h g hxm
      refine ⟨hA, by omega, ?_⟩
      rcases lt_or_eq_of_le (show S.dep x ≤ S.hi g (S.offset t h g) -
          (sideFills (fills t) true) / S.n by omega) with hlt | heq
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, ?_⟩
        by_contra hk
        have h1 := Nat.div_add_mod (sideFills (fills t) true) S.n
        have hidx := H.idx_lt (y := x) (by omega) (by omega)
        have := H.consumed_far ht h g hA (by omega) (by omega) (by omega)
          (by
            have e : S.hi g (S.offset t h g) - S.dep x = (sideFills (fills t) true) / S.n := by
              omega
            rw [e]
            omega)
        rw [this] at hxm
        cases hxm
  · intro x hx
    obtain ⟨hxB, hxU⟩ := mem_sdiff.1 hx
    rw [S.mem_pre hj₂] at hxB
    obtain ⟨hA, h0, hxj⟩ := hxB
    have hnX : x ∉ S.X := by
      simp only [X, mem_subtype, mem_filter]
      omega
    have hfar : S.stateAt t h g x = some true := by
      rcases hst : S.stateAt t h g x with _ | _ | _
      · exact absurd (mem_union_right _ (mem_middle.2 hst)) hxU
      · exact absurd (mem_union_left _ (mem_sdiff.2 ⟨mem_side.2 hst, hnX⟩)) hxU
      · rfl
    have hlead := S.lead H.hlip t h g true x hfar hA
    rw [odep_true, front_true] at hlead
    simp only [mem_filter, mem_univ, true_and]
    omega

/-! ### D9.8.7 Cuts -/

omit H in
theorem mem_cutEndpoints {x y : σ} (hx : x ∈ S.A) (hy : y ∈ S.Λ) (hyA : y ∉ S.A)
    (hadj : S.G.Adj x y) : x ∈ GraphDomain.cutEndpoints S.G S.Λ S.A :=
  mem_union_left _ (mem_image.2 ⟨(x, y), (SimpleGraph.mem_interedges_iff S.G).2
    ⟨hx, mem_sdiff.2 ⟨hy, hyA⟩, hadj⟩, rfl⟩)

/-- A region whose boundary sites (sites with a neighbour outside) have depths in `W ⊆ [1, L]`
has a cut of at most `|W| n V(1)` edges (D9.8.7). -/
theorem Hyp.card_edgeBoundary_le (Q : Finset S.Λ) (W : Finset ℕ)
    (hW : ∀ j ∈ W, 1 ≤ j ∧ j ≤ S.L)
    (hQ : ∀ x ∈ Q, ∀ y : S.Λ, S.G.Adj x y → y ∉ Q → S.dep x ∈ W) :
    #(GraphDomain.edgeBoundary S.G S.Λ (up Q)) ≤ #W * S.n * V 1 := by
  have hsub : GraphDomain.edgeBoundary S.G S.Λ (up Q) ⊆
      (up (Q.filter fun x : S.Λ => S.dep x ∈ W)).biUnion
        fun x => ({x} : Finset σ) ×ˢ GraphDomain.ball S.G S.Λ x 1 := by
    intro e he
    rw [GraphDomain.edgeBoundary, SimpleGraph.mem_interedges_iff] at he
    obtain ⟨h1, h2, h3⟩ := he
    obtain ⟨x, hxQ, hx⟩ := Finset.mem_map.1 h1
    obtain ⟨hyΛ, hyQ⟩ := mem_sdiff.1 h2
    have hyQ' : (⟨e.2, hyΛ⟩ : S.Λ) ∉ Q := fun h => hyQ (Finset.mem_map.2 ⟨_, h, rfl⟩)
    rw [← hx] at h3
    rw [mem_biUnion]
    refine ⟨x.1, Finset.mem_map_of_mem _ (mem_filter.2 ⟨hxQ, hQ x hxQ ⟨e.2, hyΛ⟩ h3 hyQ'⟩), ?_⟩
    rw [mem_product, mem_singleton]
    refine ⟨hx.symm, ?_⟩
    rw [GraphDomain.mem_ball]
    refine ⟨hyΛ, ?_⟩
    rw [GraphDomain.domainEDist_eq S.G ⟨e.2, hyΛ⟩ x]
    exact SimpleGraph.edist_le_one_iff_adj_or_eq.2 (Or.inl h3.symm)
  calc #(GraphDomain.edgeBoundary S.G S.Λ (up Q))
      ≤ #((up (Q.filter fun x : S.Λ => S.dep x ∈ W)).biUnion
        fun x => ({x} : Finset σ) ×ˢ GraphDomain.ball S.G S.Λ x 1) := card_le_card hsub
    _ ≤ ∑ x ∈ up (Q.filter fun x : S.Λ => S.dep x ∈ W),
          #(({x} : Finset σ) ×ˢ GraphDomain.ball S.G S.Λ x 1) := card_biUnion_le
    _ ≤ ∑ _x ∈ up (Q.filter fun x : S.Λ => S.dep x ∈ W), V 1 := by
        apply sum_le_sum
        intro x _
        rw [card_product, card_singleton, one_mul]
        exact H.hV _ _ _
    _ = #(Q.filter fun x : S.Λ => S.dep x ∈ W) * V 1 := by
        rw [sum_const, smul_eq_mul, up, card_map]
    _ ≤ #W * S.n * V 1 := by
        apply Nat.mul_le_mul_right
        refine (card_le_card fun x hx => ?_).trans (H.card_depths W hW)
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact hx.2

omit H in
theorem card_edgeBoundary_sdiff {P Q : Finset σ} (hQ : Q ⊆ S.Λ) :
    #(GraphDomain.edgeBoundary S.G S.Λ (Q \ P)) ≤
      #(GraphDomain.edgeBoundary S.G S.Λ Q) + #(GraphDomain.edgeBoundary S.G S.Λ P) := by
  have hsub : GraphDomain.edgeBoundary S.G S.Λ (Q \ P) ⊆
      GraphDomain.edgeBoundary S.G S.Λ Q ∪
        (GraphDomain.edgeBoundary S.G S.Λ P).image Prod.swap := by
    rintro ⟨x, y⟩ he
    rw [GraphDomain.edgeBoundary, SimpleGraph.mk_mem_interedges_iff] at he
    obtain ⟨h1, h2, h3⟩ := he
    obtain ⟨hxQ, hxP⟩ := mem_sdiff.1 h1
    obtain ⟨hyΛ, hy⟩ := mem_sdiff.1 h2
    by_cases hyQ : y ∈ Q
    · have hyP : y ∈ P := by
        by_contra hyP
        exact hy (mem_sdiff.2 ⟨hyQ, hyP⟩)
      refine mem_union_right _ (mem_image.2 ⟨(y, x), ?_, rfl⟩)
      rw [GraphDomain.edgeBoundary, SimpleGraph.mk_mem_interedges_iff]
      exact ⟨hyP, mem_sdiff.2 ⟨hQ hxQ, hxP⟩, h3.symm⟩
    · refine mem_union_left _ ?_
      rw [GraphDomain.edgeBoundary, SimpleGraph.mk_mem_interedges_iff]
      exact ⟨hxQ, mem_sdiff.2 ⟨hyΛ, hyQ⟩, h3⟩
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left card_image_le _))

/-- D9.8.7. The boundary of the near side lies in the rows `j_P - 1, …, j_P + D + r₀`. -/
theorem Hyp.bdry_near {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {x y : S.Λ}
    (hx : S.stateAt t h g x = some false) (hadj : S.G.Adj x y)
    (hy : S.stateAt t h g y ≠ some false) :
    S.lo g (S.offset t h g) + sideFills (fills t) false / S.n ≤ S.dep x ∧
      S.dep x ≤ S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n +
        (S.D + S.r₀) := by
  have hA := S.mem_A_of_ne_far h g (by rw [hx]; simp)
  have hlead := S.lead H.hlip t h g false x hx hA
  rw [odep_false, front_false] at hlead
  have hlead' : S.dep x ≤ S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n +
      S.D + S.r₀ := by exact_mod_cast hlead
  have hdiv := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hm := H.m_ge
  have hyA : y.1 ∈ S.A := by
    by_contra hyA
    have := H.tg.clearance _ (mem_cutEndpoints hA y.2 hyA hadj)
    clear hlead
    generalize sideFills (fills t) false / S.n = q at *
    omega
  have hy' : ¬ S.dep y < S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n :=
    fun hlt => hy (H.near_of_dep_lt ht h g hyA hlt)
  have := H.hlip _ _ hadj.symm
  clear hlead
  generalize sideFills (fills t) false / S.n = q at *
  omega

/-- D9.8.7. The boundary of `X U Y` (the complement of the far side) lies in the rows
`j_F - D - r₀ - 1, …, j_F`. -/
theorem Hyp.bdry_notFar {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {x y : S.Λ}
    (hx : S.stateAt t h g x ≠ some true) (hadj : S.G.Adj x y)
    (hy : S.stateAt t h g y = some true) :
    S.hi g (S.offset t h g) - sideFills (fills t) true / S.n - (S.D + S.r₀) - 1 ≤ S.dep x ∧
      S.dep x + sideFills (fills t) true / S.n ≤ S.hi g (S.offset t h g) := by
  have hA := S.mem_A_of_ne_far h g hx
  have hdiv := S.sideFills_div_le ht true
  have hdivP := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hm := H.m_ge
  have hup : S.dep x + sideFills (fills t) true / S.n ≤ S.hi g (S.offset t h g) := by
    rcases hst : S.stateAt t h g x with _ | _ | _
    · exact (H.middle_bounds ht h g hst).2.2
    · have := H.near_dep_le ht h g hst hA
      generalize sideFills (fills t) true / S.n = q at *
      generalize sideFills (fills t) false / S.n = q' at *
      omega
    · exact absurd hst hx
  have hyA : y.1 ∈ S.A := by
    by_contra hyA
    have := H.tg.clearance _ (mem_cutEndpoints hA y.2 hyA hadj)
    generalize sideFills (fills t) true / S.n = q at *
    omega
  have hlead := S.lead H.hlip t h g true y hy hyA
  rw [odep_true, front_true] at hlead
  have := H.hlip _ _ hadj.symm
  refine ⟨?_, hup⟩
  generalize sideFills (fills t) true / S.n = q at *
  omega

omit [DecidableEq σ] [DecidableRel S.G.Adj] H in
theorem window_card_le {a c : ℕ} : #(insert 1 (Icc a (a + c))) ≤ c + 2 :=
  (card_insert_le _ _).trans (by rw [Nat.card_Icc]; omega)

/-- D9.8.7. The cuts of `X U`, `X U Y`, `Y`, `U`, `U Y` have at most `2 (D + r₀ + 3) n V(1)`
edges, and these regions lie in `S₀`. -/
theorem Hyp.cut {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) (Q : Finset S.Λ)
    (hQ : Q ∈ ({S.X ∪ S.U (S.stateAt t h g), S.X ∪ S.U (S.stateAt t h g) ∪
      middle (S.stateAt t h g), middle (S.stateAt t h g), S.U (S.stateAt t h g),
      S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g)} : Finset (Finset S.Λ))) :
    #(GraphDomain.edgeBoundary S.G S.Λ (up Q)) ≤ 2 * (S.D + S.r₀ + 3) * S.n * V 1 ∧
      up Q ⊆ S.S₀ := by
  have hdiv := S.sideFills_div_le ht true
  have hdivP := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hlo := S.lo_ge g (S.offset t h g)
  have hm := H.m_ge
  have hXU := S.X_union_U (S.X_subset_side h g)
  have hW₁ : ∀ j ∈ insert 1 (Icc (S.lo g (S.offset t h g) + sideFills (fills t) false / S.n)
      (S.lo g (S.offset t h g) + sideFills (fills t) false / S.n + (S.D + S.r₀ + 1))),
      1 ≤ j ∧ j ≤ S.L := by
    intro j hj
    rw [mem_insert, mem_Icc] at hj
    generalize sideFills (fills t) false / S.n = q at *
    omega
  have hW₂ : ∀ j ∈ insert 1 (Icc (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n -
      (S.D + S.r₀) - 1) (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n -
        (S.D + S.r₀) - 1 + (S.D + S.r₀ + 1))), 1 ≤ j ∧ j ≤ S.L := by
    intro j hj
    rw [mem_insert, mem_Icc] at hj
    generalize sideFills (fills t) true / S.n = q at *
    omega
  have hnear : ∀ x ∈ side (S.stateAt t h g) false, ∀ y : S.Λ, S.G.Adj x y →
      y ∉ side (S.stateAt t h g) false →
      S.dep x ∈ insert 1 (Icc (S.lo g (S.offset t h g) + sideFills (fills t) false / S.n)
        (S.lo g (S.offset t h g) + sideFills (fills t) false / S.n + (S.D + S.r₀ + 1))) := by
    intro x hx y hadj hy
    have := H.bdry_near ht h g (mem_side.1 hx) hadj (fun h' => hy (mem_side.2 h'))
    rw [mem_insert, mem_Icc]
    generalize sideFills (fills t) false / S.n = q at *
    omega
  have hnf : ∀ x : S.Λ, S.stateAt t h g x ≠ some true ↔
      x ∈ S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) := by
    intro x
    rw [hXU, mem_union, mem_side, mem_middle]
    rcases S.stateAt t h g x with _ | _ | _ <;> simp
  have hfar : ∀ x ∈ S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g), ∀ y : S.Λ,
      S.G.Adj x y → y ∉ S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) →
      S.dep x ∈ insert 1 (Icc (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n -
        (S.D + S.r₀) - 1) (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n -
          (S.D + S.r₀) - 1 + (S.D + S.r₀ + 1))) := by
    intro x hx y hadj hy
    have hyf : S.stateAt t h g y = some true := by
      by_contra hc
      exact hy ((hnf y).1 hc)
    have := H.bdry_notFar ht h g ((hnf x).2 hx) hadj hyf
    rw [mem_insert, mem_Icc]
    generalize sideFills (fills t) true / S.n = q at *
    omega
  have hXdep : ∀ x ∈ S.X, S.dep x = 0 := fun x hx => by
    simp only [X, mem_subtype, mem_filter] at hx
    exact hx.2
  have hnotX : ∀ x : S.Λ, x.1 ∈ S.A → x ∉ S.X → 1 ≤ S.dep x := fun x hA hx => by
    by_contra h0
    exact hx (by simp only [X, mem_subtype, mem_filter]; exact ⟨hA, by omega⟩)
  have hS₀ : ∀ x : S.Λ, S.stateAt t h g x ≠ some true → x.1 ∈ S.S₀ := by
    intro x hx
    have hA := S.mem_A_of_ne_far h g hx
    refine mem_filter.2 ⟨hA, ?_⟩
    rcases hst : S.stateAt t h g x with _ | _ | _
    · have := (H.middle_bounds ht h g hst).2.2
      generalize sideFills (fills t) true / S.n = q at *
      omega
    · have := H.near_dep_le ht h g hst hA
      generalize sideFills (fills t) false / S.n = q at *
      omega
    · exact absurd hst hx
  have hupS₀ : ∀ Q : Finset S.Λ, Q ⊆ S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) →
      up Q ⊆ S.S₀ := by
    intro Q hQ x hx
    obtain ⟨x, hxQ, rfl⟩ := Finset.mem_map.1 hx
    exact hS₀ x ((hnf x).2 (hQ hxQ))
  have hc1 : #(insert 1 (Icc (S.lo g (S.offset t h g) + sideFills (fills t) false / S.n)
      (S.lo g (S.offset t h g) + sideFills (fills t) false / S.n + (S.D + S.r₀ + 1)))) ≤
      S.D + S.r₀ + 3 := window_card_le
  have hc2 : #(insert 1 (Icc (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n -
      (S.D + S.r₀) - 1) (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n -
        (S.D + S.r₀) - 1 + (S.D + S.r₀ + 1)))) ≤ S.D + S.r₀ + 3 := window_card_le
  have hbXU : #(GraphDomain.edgeBoundary S.G S.Λ (up (S.X ∪ S.U (S.stateAt t h g)))) ≤
      (S.D + S.r₀ + 3) * S.n * V 1 := by
    rw [hXU]
    exact (H.card_edgeBoundary_le _ _ hW₁ hnear).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc1))
  have hbXUY : #(GraphDomain.edgeBoundary S.G S.Λ
      (up (S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g)))) ≤
      (S.D + S.r₀ + 3) * S.n * V 1 :=
    (H.card_edgeBoundary_le _ _ hW₂ hfar).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc2))
  have hsubXU : S.X ∪ S.U (S.stateAt t h g) ⊆
      S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) := subset_union_left
  have h2 : (S.D + S.r₀ + 3) * S.n * V 1 ≤ 2 * (S.D + S.r₀ + 3) * S.n * V 1 := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    omega
  simp only [mem_insert, mem_singleton] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨hbXU.trans h2, hupS₀ _ hsubXU⟩
  · exact ⟨hbXUY.trans h2, hupS₀ _ subset_rfl⟩
  · -- `Y = X U Y \ X U`
    have hY : up (middle (S.stateAt t h g)) =
        up (S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g)) \
          up (S.X ∪ S.U (S.stateAt t h g)) := by
      rw [up, up, up, ← Finset.map_sdiff]
      congr 1
      ext x
      rw [hXU, mem_sdiff, mem_union, mem_side, mem_middle]
      rcases S.stateAt t h g x with _ | _ | _ <;> simp
    refine ⟨?_, hupS₀ _ subset_union_right⟩
    rw [hY]
    refine (card_edgeBoundary_sdiff (up_subset _)).trans ?_
    have := Nat.add_le_add hbXUY hbXU
    calc _ ≤ (S.D + S.r₀ + 3) * S.n * V 1 + (S.D + S.r₀ + 3) * S.n * V 1 := this
      _ = 2 * (S.D + S.r₀ + 3) * S.n * V 1 := by ring
  · -- `U = X U \ X`
    refine ⟨(H.card_edgeBoundary_le _ _ hW₁ fun x hx y hadj hy => ?_).trans ?_,
      hupS₀ _ (fun x hx => mem_union_left _ (mem_union_right _ hx))⟩
    · rw [U, mem_sdiff] at hx
      by_cases hyn : y ∈ side (S.stateAt t h g) false
      · have hyX : y ∈ S.X := by
          by_contra hyX
          exact hy (mem_sdiff.2 ⟨hyn, hyX⟩)
        have := H.hlip _ _ hadj
        have := hXdep y hyX
        have := hnotX x (S.mem_A_of_ne_far h g (by rw [mem_side.1 hx.1]; simp)) hx.2
        rw [mem_insert]
        exact Or.inl (by omega)
      · exact hnear x hx.1 y hadj hyn
    · exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc1)).trans h2
  · -- `U Y = X U Y \ X`
    have hsub : S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) ⊆
        S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) := by
      intro x hx
      rcases mem_union.1 hx with hx | hx
      · exact mem_union_left _ (mem_union_right _ hx)
      · exact mem_union_right _ hx
    refine ⟨(H.card_edgeBoundary_le _ _ hW₂ fun x hx y hadj hy => ?_).trans ?_, hupS₀ _ hsub⟩
    · have hxnX : x ∉ S.X := by
        rcases mem_union.1 hx with hx | hx
        · exact (mem_sdiff.1 hx).2
        · intro hX
          have h1 := S.stateAt_X h g hX
          rw [mem_middle.1 hx] at h1
          cases h1
      have hxnf : S.stateAt t h g x ≠ some true := (hnf x).2 (hsub hx)
      by_cases hyX : y ∈ S.X
      · have := H.hlip _ _ hadj
        have := hXdep y hyX
        have := hnotX x (S.mem_A_of_ne_far h g hxnf) hxnX
        rw [mem_insert]
        exact Or.inl (by omega)
      · refine hfar x (hsub hx) y hadj fun hy' => hy ?_
        rw [← hnf] at hy'
        rcases hst : S.stateAt t h g y with _ | _ | _
        · exact mem_union_right _ (mem_middle.2 hst)
        · exact mem_union_left _ (mem_sdiff.2 ⟨mem_side.2 hst, hyX⟩)
        · exact absurd hst hy'
    · exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc2)).trans h2

/-! ### D9.8.8 Count of split terms -/

omit [DecidableRel S.G.Adj] H in
theorem card_filter_Λ (p : σ → Prop) [DecidablePred p] :
    #(S.Λ.filter p) = #(univ.filter fun x : S.Λ => p x.1) := by
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ S.Λ))]
  congr 1
  ext x
  simp [and_comm]

/-- At most `μ_R` labelled terms share an anchor (D2.8): terms with anchors in a window of
`c + 1` rows number at most `μ_R (c + 1) n`. -/
theorem Hyp.card_terms_window (j₀ c : ℕ) (h1 : 1 ≤ j₀) (h2 : j₀ + c ≤ S.L) :
    #(univ.filter fun i : S.Term => j₀ ≤ S.dep (S.a i) ∧ S.dep (S.a i) ≤ j₀ + c) ≤
      AreaLaw.μ V S.R * ((c + 1) * S.n) := by
  refine (card_le_mul_card_image_of_maps_to (f := fun i : S.Term => S.a i)
    (t := S.Λ.filter fun x => j₀ ≤ S.dep x ∧ S.dep x ≤ j₀ + c) ?_ (AreaLaw.μ V S.R) ?_).trans ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    exact mem_filter.2 ⟨((GraphDomain.mem_supports S.G).1 i.2).1 (H.anchor i.1 i.2), hi⟩
  · intro x _
    refine le_trans (card_le_card_of_injOn (fun i : S.Term => i.1)
      (t := (GraphDomain.supports S.G S.Λ S.R).filter fun Y => S.a Y = x) ?_
      Subtype.val_injective.injOn) ((step_2_8 S.G V H.hV S.Λ S.R x).2.1 S.a H.anchor)
    intro i hi
    simp only [coe_filter, Set.mem_ofPred_eq, mem_filter, mem_univ, true_and] at hi ⊢
    exact ⟨i.2, hi.2⟩
  · apply Nat.mul_le_mul_left
    rw [S.card_filter_Λ]
    exact H.card_window h1 h2

/-- D9.8.8. A term split in band `g` at time `t ≤ 2nm` has its anchor at oriented depth in
`[j - r₀, j + D + 2 r₀]` on its splitting side. -/
theorem Hyp.split_anchor {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) (i : S.Term)
    (hs : ¬ (S.Xt i ⊆ side (S.stateAt t h g) false ∨ S.Xt i ⊆ middle (S.stateAt t h g) ∨
      S.Xt i ⊆ side (S.stateAt t h g) true)) :
    ∃ b : Bool, S.front g (S.offset t h g) t b - S.r₀ ≤ S.odep b (S.a i) ∧
      S.odep b (S.a i) ≤ S.front g (S.offset t h g) t b + S.D + 2 * S.r₀ := by
  rcases H.classify ht h g i with hc | ⟨hb, hA, ⟨y, hy⟩, hsplit⟩
  · exact absurd hc hs
  rw [mem_inter, mem_middle] at hy
  obtain ⟨-, hmP, hmF⟩ := H.middle_bounds ht h g hy.2
  have hyb : y.1 ∈ GraphDomain.ball S.G S.Λ (S.a i) S.r₀ := by
    have := hy.1
    rw [hb] at this
    exact mem_subtype.1 this
  rcases hsplit with ⟨⟨x, hx⟩, -⟩ | ⟨⟨x, hx⟩, -⟩
  · refine ⟨false, ?_, ?_⟩
    · have h1 := (S.odep_le_of_mem_ball H.hlip hyb false).1
      rw [front_false]
      simp only [odep_false] at h1 ⊢
      have : ((S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n : ℕ) : ℤ) ≤
        S.dep y := by exact_mod_cast hmP
      omega
    · rw [mem_inter, mem_side] at hx
      have hxA := hA (S.mem_up hx.1)
      have hxb : x.1 ∈ GraphDomain.ball S.G S.Λ (S.a i) S.r₀ := by
        have := hx.1
        rw [hb] at this
        exact mem_subtype.1 this
      have h1 := (S.odep_le_of_mem_ball H.hlip hxb false).2
      have h2 := S.lead H.hlip t h g false x hx.2 hxA
      omega
  · refine ⟨true, ?_, ?_⟩
    · have h1 := (S.odep_le_of_mem_ball H.hlip hyb true).1
      rw [front_true]
      simp only [odep_true] at h1 ⊢
      have : (S.dep y : ℤ) + ((sideFills (fills t) true / S.n : ℕ) : ℤ) ≤
        S.hi g (S.offset t h g) := by exact_mod_cast hmF
      omega
    · rw [mem_inter, mem_side] at hx
      have hxA := hA (S.mem_up hx.1)
      have hxb : x.1 ∈ GraphDomain.ball S.G S.Λ (S.a i) S.r₀ := by
        have := hx.1
        rw [hb] at this
        exact mem_subtype.1 this
      have h1 := (S.odep_le_of_mem_ball H.hlip hxb true).2
      have h2 := S.lead H.hlip t h g true x hx.2 hxA
      omega

/-- Terms with anchors in the oriented window `[j - r₀, j + D + 2 r₀]` of one side of one band
number at most `μ_R (D + 3 r₀ + 1) n`. -/
theorem Hyp.card_window_terms {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) (b : Bool) :
    #(univ.filter fun i : S.Term => S.front g (S.offset t h g) t b - S.r₀ ≤ S.odep b (S.a i) ∧
      S.odep b (S.a i) ≤ S.front g (S.offset t h g) t b + S.D + 2 * S.r₀) ≤
      AreaLaw.μ V S.R * ((S.D + 3 * S.r₀ + 1) * S.n) := by
  have hdiv := S.sideFills_div_le ht true
  have hdivP := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hlo := S.lo_ge g (S.offset t h g)
  have hm := H.m_ge
  have hr := H.r₀_le
  cases b
  · obtain ⟨q, hq⟩ : ∃ q, sideFills (fills t) false / S.n = q := ⟨_, rfl⟩
    rw [hq] at hdivP
    refine (card_le_card fun i hi => ?_).trans (H.card_terms_window
      (S.lo g (S.offset t h g) + 1 + q - S.r₀) (S.D + 3 * S.r₀) (by omega) (by omega))
    simp only [mem_filter, mem_univ, true_and, front_false, odep_false, hq] at hi ⊢
    push_cast at hi
    omega
  · obtain ⟨q, hq⟩ : ∃ q, sideFills (fills t) true / S.n = q := ⟨_, rfl⟩
    rw [hq] at hdiv
    refine (card_le_card fun i hi => ?_).trans (H.card_terms_window
      (S.hi g (S.offset t h g) - q - (S.D + 2 * S.r₀)) (S.D + 3 * S.r₀) (by omega) (by omega))
    simp only [mem_filter, mem_univ, true_and, front_true, odep_true, hq] at hi ⊢
    omega

open Classical in
/-- D9.8.8. At most `2 μ_R K (D + 3 r₀ + 1) n` terms split in any joint status. -/
theorem Hyp.splitCount (s : S.St) :
    #(univ.filter fun i : S.Term => ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) ≤
      S.K * (2 * (AreaLaw.μ V S.R * ((S.D + 3 * S.r₀ + 1) * S.n))) := by
  obtain ⟨t, h, ht, hs⟩ := S.exists_leafState s
  calc #(univ.filter fun i : S.Term => ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i)))
      ≤ #((univ : Finset (Fin S.K)).biUnion fun g => (univ : Finset Bool).biUnion fun b =>
          univ.filter fun i : S.Term => S.front g (S.offset t h g) t b - S.r₀ ≤
            S.odep b (S.a i) ∧
            S.odep b (S.a i) ≤ S.front g (S.offset t h g) t b + S.D + 2 * S.r₀) := by
        apply card_le_card
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        obtain ⟨g, hg⟩ := hi
        rw [S.part_contains, S.leafState_X_union_U, hs] at hg
        obtain ⟨b, hb⟩ := H.split_anchor ht h g i hg
        simp only [mem_biUnion, mem_univ, true_and, mem_filter]
        exact ⟨g, b, hb⟩
    _ ≤ ∑ g : Fin S.K, #((univ : Finset Bool).biUnion fun b =>
          univ.filter fun i : S.Term => S.front g (S.offset t h g) t b - S.r₀ ≤
            S.odep b (S.a i) ∧
            S.odep b (S.a i) ≤ S.front g (S.offset t h g) t b + S.D + 2 * S.r₀) :=
        card_biUnion_le
    _ ≤ ∑ _g : Fin S.K, 2 * (AreaLaw.μ V S.R * ((S.D + 3 * S.r₀ + 1) * S.n)) := by
        apply sum_le_sum
        intro g _
        refine card_biUnion_le.trans ?_
        rw [Fintype.sum_bool]
        have h1 := H.card_window_terms ht h g true
        have h2 := H.card_window_terms ht h g false
        omega
    _ = S.K * (2 * (AreaLaw.μ V S.R * ((S.D + 3 * S.r₀ + 1) * S.n))) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- The constant of Lemma 9.1 (2), (3). -/
def C₂ (V : ℕ → ℕ) (R : ℕ) : ℝ := 8 * (V 1 + 1) * (AreaLaw.μ V R + 1)

omit [DecidableEq σ] [DecidableRel S.G.Adj] H in
theorem C₂_ge (V : ℕ → ℕ) (R : ℕ) : 8 ≤ C₂ V R ∧ 8 * (V 1 : ℝ) ≤ C₂ V R ∧
    8 * (AreaLaw.μ V R : ℝ) ≤ C₂ V R := by
  unfold C₂
  have h1 : (0 : ℝ) ≤ V 1 := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ AreaLaw.μ V R := Nat.cast_nonneg _
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Lemma 9.1 (2).** -/
theorem Hyp.item2 : S.Item2 (C₂ V S.R) where
  lead t _ h g b x hx hA := S.lead H.hlip t h g b x hx hA
  nested := S.prefixes_nested
  disjoint := S.prefixes_disjoint
  rows := S.prefixes_rows
  matched s g Q hQ := by
    obtain ⟨t, h, ht, hs⟩ := S.exists_leafState s
    change Q ∈ ({S.U (S.leafState s g), S.U (S.leafState s g) ∪ middle (S.leafState s g)} :
      Finset (Finset S.Λ)) at hQ
    rw [hs] at hQ
    have hdiv := S.sideFills_div_le ht true
    have hdivP := S.sideFills_div_le ht false
    have hL := H.hi_add_le g (S.offset t h g)
    have hhi := S.hi_eq g (S.offset t h g)
    have hlo := S.lo_ge g (S.offset t h g)
    have hm := H.m_ge
    have hn := H.n_pos
    have hD := H.D_pos
    have hr := H.r₀_le
    have hC := (C₂_ge V S.R).1
    have := int_div_nonneg (sideFills (fills t) false) S.n
    have := int_div_nonneg (sideFills (fills t) true) S.n
    have hreal : ∀ k : ℕ, k ≤ (S.D + S.r₀ + 1) * S.n → (k : ℝ) ≤ C₂ V S.R * S.n * S.D := by
      intro k hk
      have hDr : S.D + S.r₀ + 1 ≤ 2 * S.D := by omega
      have h1 : k ≤ 2 * S.D * S.n := hk.trans (Nat.mul_le_mul_right _ hDr)
      have h2 : (k : ℝ) ≤ 2 * S.D * S.n := by exact_mod_cast h1
      have h3 : (0 : ℝ) ≤ S.n * S.D := by positivity
      nlinarith
    simp only [mem_insert, mem_singleton] at hQ
    rcases hQ with rfl | rfl
    · refine ⟨S.pre (S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n)
        (sideFills (fills t) false % S.n), S.mem_prefixes.2 ⟨_, _, by omega, by omega,
          (Nat.mod_lt _ hn).le, rfl⟩, Or.inr ⟨(H.U_sandwich ht h g).1, hreal _ ?_⟩⟩
      refine (card_le_card (H.U_sandwich ht h g).2).trans ?_
      exact H.card_window (by omega) (by omega)
    · refine ⟨S.pre (S.hi g (S.offset t h g) - sideFills (fills t) true / S.n)
        (S.n - sideFills (fills t) true % S.n), S.mem_prefixes.2 ⟨_, _, by omega, by omega,
          by omega, rfl⟩, Or.inl ⟨(H.UY_sandwich ht h g).1, hreal _ ?_⟩⟩
      refine (card_le_card (H.UY_sandwich ht h g).2).trans ?_
      exact H.card_window (by omega) (by omega)
  cut s g Q hQ := by
    obtain ⟨t, h, ht, hs⟩ := S.exists_leafState s
    change Q ∈ ({S.X ∪ S.U (S.leafState s g), S.X ∪ S.U (S.leafState s g) ∪
      middle (S.leafState s g), middle (S.leafState s g), S.U (S.leafState s g),
      S.U (S.leafState s g) ∪ middle (S.leafState s g)} : Finset (Finset S.Λ)) at hQ
    rw [hs] at hQ
    obtain ⟨h1, h2⟩ := H.cut ht h g Q hQ
    refine ⟨?_, h2⟩
    have hD := H.D_pos
    have hr := H.r₀_le
    have hC := (C₂_ge V S.R).2.1
    have h3 : #(GraphDomain.edgeBoundary S.G S.Λ (up Q)) ≤ 8 * S.D * S.n * V 1 :=
      h1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
    have h4 : (#(GraphDomain.edgeBoundary S.G S.Λ (up Q)) : ℝ) ≤ 8 * S.D * S.n * V 1 := by
      exact_mod_cast h3
    have h5 : (0 : ℝ) ≤ S.n * S.D := by positivity
    nlinarith
  splitCount s := by
    classical
    have h1 := H.splitCount s
    have hD := H.D_pos
    have hr := H.r₀_le
    have hC := (C₂_ge V S.R).2.2
    have h3 : #(univ.filter fun i : S.Term =>
        ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) ≤
        8 * AreaLaw.μ V S.R * (S.K * S.n * S.D) := by
      refine h1.trans ?_
      have : S.D + 3 * S.r₀ + 1 ≤ 4 * S.D := by omega
      calc S.K * (2 * (AreaLaw.μ V S.R * ((S.D + 3 * S.r₀ + 1) * S.n)))
          ≤ S.K * (2 * (AreaLaw.μ V S.R * ((4 * S.D) * S.n))) := by gcongr
        _ = 8 * AreaLaw.μ V S.R * (S.K * S.n * S.D) := by ring
    have h4 : (#(univ.filter fun i : S.Term =>
        ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) : ℝ) ≤
        8 * AreaLaw.μ V S.R * (S.K * S.n * S.D) := by exact_mod_cast h3
    have h5 : (0 : ℝ) ≤ S.K * S.n * S.D := by positivity
    nlinarith

end Prefixes

end Scan

end AreaLaw.Scanner
