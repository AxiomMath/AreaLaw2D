import AreaLaw.S09_Scanner.Scan

/-!
# §9.1 Lemma 9.1, the rounds of the scan and their kinematics (D9.7, D9.8.3, D9.8.4)

Digest `digest/09-scanner.md` D9.7, D9.8, paper `paper/sections/08-scanner.tex` 137–338.
Graph-level (Map.md, Dimension: `any d`). The rounds of the scan are admissible rounds of §7
with commuting bands (D9.7, D9.8.10); every assigned site lies within `D + r₀` of its front
(D9.8.3); fill slots are consumed by their own side and middle sites lie between the fronts
(D9.8.4, D9.5 Output), under the standing hypotheses `Scan.Hyp`.
-/

open scoped Matrix
open Finset Arealaw

namespace AreaLaw.Scanner

universe u

open Transport (MeanTree)
open Comparators (physReg Site)

/-! ## Physical regions as tensor factors -/

section PhysReg

variable {τ : Type*} {Q P Y F : Finset τ}

@[simp] theorem phys_mem_physReg {v : τ} : Site.phys v ∈ physReg Q ↔ v ∈ Q :=
  Finset.mem_map' ⟨Site.phys, fun _ _ h => Site.phys.inj h⟩

@[simp] theorem C_not_mem_physReg : Site.C ∉ physReg Q := by simp [physReg]

@[simp] theorem R_not_mem_physReg : Site.R ∉ physReg Q := by simp [physReg]

theorem physReg_subset_iff : physReg Q ⊆ physReg P ↔ Q ⊆ P := Finset.map_subset_map

theorem physReg_nonempty : (physReg Q).Nonempty ↔ Q.Nonempty := Finset.map_nonempty

theorem disjoint_physReg_iff : Disjoint (physReg Q) (physReg P) ↔ Disjoint Q P :=
  Finset.disjoint_map _

variable [DecidableEq τ]

theorem physReg_union (A B : Finset τ) : physReg (A ∪ B) = physReg A ∪ physReg B :=
  Finset.map_union _ _

theorem physReg_inter (A B : Finset τ) : physReg (A ∩ B) = physReg A ∩ physReg B :=
  Finset.map_inter _ _

theorem physReg_sdiff (A B : Finset τ) : physReg (A \ B) = physReg A \ physReg B :=
  Finset.map_sdiff _ _

theorem physReg_subset_insert_C : physReg Q ⊆ insert Site.C (physReg P) ↔ Q ⊆ P := by
  rw [subset_insert_iff_of_notMem C_not_mem_physReg]
  exact Finset.map_subset_map

theorem physReg_subset_insert_R : physReg Q ⊆ insert Site.R (physReg P) ↔ Q ⊆ P := by
  rw [subset_insert_iff_of_notMem R_not_mem_physReg]
  exact Finset.map_subset_map

theorem physReg_inter_insert_C : physReg Q ∩ insert Site.C (physReg P) = physReg (Q ∩ P) := by
  rw [inter_insert_of_notMem C_not_mem_physReg, physReg_inter]

theorem physReg_inter_insert_R : physReg Q ∩ insert Site.R (physReg P) = physReg (Q ∩ P) := by
  rw [inter_insert_of_notMem R_not_mem_physReg, physReg_inter]

/-- `Contains` on a partition `(C P, Y, R F)` of physical regions. -/
theorem contains_physReg :
    (⟨insert Site.C (physReg P), physReg Y, insert Site.R (physReg F)⟩ :
      Transport.PYF (Site τ)).Contains (physReg Q) ↔ Q ⊆ P ∨ Q ⊆ Y ∨ Q ⊆ F := by
  change physReg Q ⊆ _ ∨ physReg Q ⊆ physReg Y ∨ physReg Q ⊆ _ ↔ _
  rw [physReg_subset_insert_C, physReg_subset_insert_R, physReg_subset_iff]

theorem disjoint_physReg_insert_R : Disjoint (physReg Q) (insert Site.R (physReg P)) ↔
    Disjoint Q P := by
  rw [Finset.disjoint_insert_right, disjoint_physReg_iff]
  simp

theorem disjoint_physReg_insert_C : Disjoint (physReg Q) (insert Site.C (physReg P)) ↔
    Disjoint Q P := by
  rw [Finset.disjoint_insert_right, disjoint_physReg_iff]
  simp

theorem splitsToP_physReg :
    (⟨insert Site.C (physReg P), physReg Y, insert Site.R (physReg F)⟩ :
      Transport.PYF (Site τ)).SplitsToP (physReg Q) ↔
      (Q ∩ Y).Nonempty ∧ (Q ∩ P).Nonempty ∧ Disjoint Q F := by
  change (physReg Q ∩ physReg Y).Nonempty ∧ (physReg Q ∩ insert Site.C (physReg P)).Nonempty ∧
    Disjoint (physReg Q) (insert Site.R (physReg F)) ↔ _
  rw [← physReg_inter, physReg_inter_insert_C, physReg_nonempty, physReg_nonempty,
    disjoint_physReg_insert_R]

theorem splitsToF_physReg :
    (⟨insert Site.C (physReg P), physReg Y, insert Site.R (physReg F)⟩ :
      Transport.PYF (Site τ)).SplitsToF (physReg Q) ↔
      (Q ∩ Y).Nonempty ∧ (Q ∩ F).Nonempty ∧ Disjoint Q P := by
  change (physReg Q ∩ physReg Y).Nonempty ∧ (physReg Q ∩ insert Site.R (physReg F)).Nonempty ∧
    Disjoint (physReg Q) (insert Site.C (physReg P)) ↔ _
  rw [← physReg_inter, physReg_inter_insert_R, physReg_nonempty, physReg_nonempty,
    disjoint_physReg_insert_C]

end PhysReg

/-! ## Mean-tree weights -/

namespace Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ)

/-! ## The rounds of the scan as rounds of §7 -/

variable {S} in
@[simp] theorem mem_side {st : S.State} {b : Bool} {x : S.Λ} : x ∈ side st b ↔ st x = some b := by
  simp [side]

variable {S} in
@[simp] theorem mem_middle {st : S.State} {x : S.Λ} : x ∈ middle st ↔ st x = none := by
  simp [middle]

variable {S} in
theorem applyStep_some_apply {st : S.State} {b : Bool} {x : Finset S.Λ} {y : S.Λ} :
    applyStep (some (b, x)) st y = if y ∈ x then some b else st y := rfl

theorem X_subset_side {t : ℕ} (h : S.Hist t) (g : Fin S.K) :
    S.X ⊆ side (S.stateAt t h g) false := fun x hx => by
  simp [side, S.stateAt_X h g hx]

theorem X_union_U {st : S.State} (hX : S.X ⊆ side st false) : S.X ∪ S.U st = side st false := by
  ext x
  have := @hX x
  simp only [U, mem_union, mem_sdiff]
  tauto

theorem stateAt_ext (t : ℕ) (h : S.Hist t) (c : S.Ch t) (g : Fin S.K) :
    S.stateAt (t + 1) (S.ext t h c) g =
      applyStep (S.step g (S.offset t h g) t (c g) (S.stateAt t h g)) (S.stateAt t h g) := rfl

theorem offset_ext (t : ℕ) (h : S.Hist t) (c : S.Ch t) :
    S.offset (t + 1) (S.ext t h c) = S.offset t h := rfl

theorem ext_inj {t : ℕ} {h h' : S.Hist t} {c c' : S.Ch t} (he : S.ext t h c = S.ext t h' c') :
    h = h' ∧ c = c' :=
  Prod.mk.inj he

/-- A transition is the §7 move of its middle part (D9.7). -/
theorem toMove_apply (st : S.State) (hX : S.X ⊆ side st false) (mv : Option (Bool × Finset S.Λ))
    (hmv : ∀ b x, mv = some (b, x) → x ⊆ middle st) :
    (S.toMove mv).apply ⟨insert Site.C (physReg (S.X ∪ S.U st)), physReg (middle st),
        insert Site.R (physReg (side st true))⟩ =
      ⟨insert Site.C (physReg (S.X ∪ S.U (applyStep mv st))), physReg (middle (applyStep mv st)),
        insert Site.R (physReg (side (applyStep mv st) true))⟩ := by
  rcases mv with _ | ⟨b, x⟩
  · rfl
  have hx := hmv b x rfl
  have hxn : ∀ y ∈ x, st y = none := fun y hy => mem_middle.1 (hx hy)
  have hX' : S.X ⊆ side (applyStep (some (b, x)) st) false := fun y hy => by
    have h1 := mem_side.1 (hX hy)
    rw [mem_side, applyStep_some_apply, if_neg fun hyx => by simp [hxn y hyx] at h1, h1]
  rw [X_union_U S hX, X_union_U S hX']
  have hmid : middle (applyStep (some (b, x)) st) = middle st \ x := by
    ext y
    rw [mem_middle, applyStep_some_apply, mem_sdiff, mem_middle]
    by_cases hy : y ∈ x <;> simp [hy]
  have hside : ∀ b', side (applyStep (some (b, x)) st) b' =
      if b' = b then side st b' ∪ x else side st b' := by
    intro b'
    ext y
    rw [mem_side, applyStep_some_apply]
    by_cases hy : y ∈ x
    · split_ifs with hb
      · simp [hy, hb]
      · simp [hxn y hy, Ne.symm hb]
    · split_ifs <;> simp [hy]
  cases b
  · simp only [toMove, Transport.Move.apply, hside, hmid, if_true, Bool.true_eq_false, if_false,
      physReg_union, physReg_sdiff, insert_union]
  · simp only [toMove, Transport.Move.apply, hside, hmid, if_true, Bool.false_eq_true, if_false,
      physReg_union, physReg_sdiff, insert_union]

/-- D9.7. The partitions at the terminal leaves of round `t` are the statuses of `Γ`. -/
theorem round_leafPart (t : Fin S.T) (j : Transport.Round.Leaf (S.Hist t) (fun _ => S.Ch t))
    (g : Fin S.K) : (S.round t).leafPart j g = S.Γ.part ⟨t, j⟩ g := by
  obtain ⟨h, _ | c⟩ := j
  · rfl
  · exact S.toMove_apply _ (S.X_subset_side h g) _ fun b x hbx => S.step_subset_middle hbx

/-- D9.7. Consecutive rounds are chained: the old partitions of round `t + 1` are the new ones
of round `t`. -/
theorem round_old_succ (t : Fin S.T) (ht : t.1 + 1 < S.T) (h : S.Hist t) (c : S.Ch t)
    (g : Fin S.K) :
    (S.round ⟨t + 1, ht⟩).old (S.ext t h c) g = (S.round t).new h c g :=
  (S.round_leafPart t ⟨h, some c⟩ g).symm

/-- D9.7. The history tree of round `t + 1` is that of round `t` with the choice trees
attached. -/
theorem round_histTree_succ (t : Fin S.T) (ht : t.1 + 1 < S.T) :
    (S.round ⟨t + 1, ht⟩).histTree =
      (S.round t).histTree.bind fun h => ((S.round t).choiceTree h).map (S.ext t h) := rfl

theorem weight_histTree_ext (t : ℕ) (h : S.Hist t) (c : S.Ch t) :
    (S.histTree (t + 1)).weight (S.ext t h c) =
      (S.histTree t).weight h * (uniformTree (S.Ch t)).weight c := by
  rw [histTree, MeanTree.weight_bind_of_forall_ne _ (h₀ := h)]
  · rw [MeanTree.weight_map_apply _ (fun a b hab => (S.ext_inj hab).2)]
  · intro h' hh'
    exact MeanTree.weight_map_of_forall_ne _ fun c' hc' => hh' (S.ext_inj hc').1

theorem histTree_weight_pos : ∀ (t : ℕ) (h : S.Hist t), 0 < (S.histTree t).weight h
  | 0, h => by
    rw [histTree, weight_uniformTree]
    exact one_div_pos.2 (by exact_mod_cast Fintype.card_pos)
  | t + 1, h => by
    obtain ⟨h₀, c⟩ := h
    rw [show (⟨h₀, c⟩ : S.Hist t × S.Ch t) = S.ext t h₀ c from rfl, weight_histTree_ext,
      weight_uniformTree]
    exact mul_pos (histTree_weight_pos t h₀) (one_div_pos.2 (by exact_mod_cast Fintype.card_pos))

theorem histTree_nodup : ∀ t : ℕ, (S.histTree t).labels.Nodup
  | 0 => nodup_uniformTree _
  | t + 1 => by
    rw [histTree, labels_bind, List.nodup_flatMap]
    refine ⟨fun h _ => ?_, (histTree_nodup t).imp fun {h h'} hne => ?_⟩
    · rw [labels_map]
      exact (nodup_uniformTree _).map fun a b hab => (S.ext_inj hab).2
    · simp only [Function.onFun]
      rw [labels_map, labels_map, List.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨c', -, hc'⟩ := List.mem_map.1 hx'
      exact hne (S.ext_inj hc').1.symm

/-- D9.7. Every round of the scan satisfies the standing hypotheses of D7.9. -/
theorem round_isAdmissible (t : Fin S.T) : (S.round t).IsAdmissible where
  histWeight_pos h := S.histTree_weight_pos t h
  choiceWeight_pos h c := by
    change 0 < (uniformTree (S.Ch t)).weight c
    rw [weight_uniformTree]
    exact one_div_pos.2 (by exact_mod_cast Fintype.card_pos)
  hist_nodup := S.histTree_nodup t
  choice_nodup _ := nodup_uniformTree _
  old_isPartition h g := Comparators.Upper.isPartition_part S.Γ _ g
  move_subset h c g := by
    change (S.toMove (S.step g (S.offset t h g) t (c g) (S.stateAt t h g))).subsystem ⊆
      physReg (middle (S.stateAt t h g))
    rcases hs : S.step g (S.offset t h g) t (c g) (S.stateAt t h g) with _ | ⟨_ | _, x⟩
    · exact Finset.empty_subset _
    · exact Finset.map_subset_map.2 (S.step_subset_middle hs)
    · exact Finset.map_subset_map.2 (S.step_subset_middle hs)

/-- D9.8.10. Cross-band commutation at every round (`comparator:nesting`, D8.1 Output (ii)). -/
theorem round_crossBandCommute (nl : S.Λ → ℕ) [∀ v, NeZero (nl v)] (d : ℕ) [NeZero d] (τ : ℝ)
    (hτ : 0 ≤ τ) (k : ℕ) (t : Fin S.T) :
    (S.round t).CrossBandCommute (Comparators.dims nl d) τ k := by
  intro j j' g g' hgg'
  rw [S.round_leafPart, S.round_leafPart]
  exact (Comparators.step_8_1 S.Γ).2 nl d τ hτ k _ _ g g' hgg'

/-! ## D9.5 Fronts -/

theorem sideFills_le (f : ℕ) (b : Bool) : sideFills f b ≤ f := by
  unfold sideFills; split_ifs <;> omega

theorem sideFills_mono {f f' : ℕ} (h : f ≤ f') (b : Bool) : sideFills f b ≤ sideFills f' b := by
  unfold sideFills; split_ifs <;> omega

theorem fills_mono {t t' : ℕ} (h : t ≤ t') : fills t ≤ fills t' := by
  unfold fills; omega

theorem front_false (g r t : ℕ) :
    S.front g r t false = ((S.lo g r + 1 + sideFills (fills t) false / S.n : ℕ) : ℤ) := rfl

theorem front_true (g r t : ℕ) :
    S.front g r t true = -(S.hi g r : ℤ) + ((sideFills (fills t) true / S.n : ℕ) : ℤ) := rfl

theorem front_mono (g r : ℕ) {t t' : ℕ} (h : t ≤ t') (b : Bool) :
    S.front g r t b ≤ S.front g r t' b := by
  have := Nat.div_le_div_right (c := S.n) (sideFills_mono (fills_mono h) b)
  cases b
  · rw [front_false, front_false]; push_cast; omega
  · rw [front_true, front_true]; omega

theorem odep_false (x : σ) : S.odep false x = S.dep x := rfl

theorem odep_true (x : σ) : S.odep true x = -(S.dep x : ℤ) := rfl

theorem T_eq : S.T = 2 * (S.n * S.m) := by simp only [T, Nat.mul_assoc]

/-- Before any round `t ≤ 2nm` each side has received at most `nm` fills. -/
theorem sideFills_div_le {t : ℕ} (ht : t ≤ S.T) (b : Bool) :
    sideFills (fills t) b / S.n ≤ S.m := by
  apply Nat.div_le_of_le_mul
  have h1 := sideFills_le (fills t) b
  have h2 : fills t ≤ S.n * S.m := by
    have := S.T_eq; unfold fills; omega
  linarith [Nat.mul_comm S.n S.m]

theorem int_div_nonneg (a n : ℕ) : (0 : ℤ) ≤ (a : ℤ) / (n : ℤ) :=
  Int.ediv_nonneg (by positivity) (by positivity)

/-! ## D9.1 Depth along the graph -/

theorem domainEDist_comm (x y : σ) :
    GraphDomain.domainEDist S.G S.Λ x y = GraphDomain.domainEDist S.G S.Λ y x := by
  unfold GraphDomain.domainEDist
  by_cases hx : x ∈ S.Λ <;> by_cases hy : y ∈ S.Λ <;> simp only [hx, hy, and_self, dif_pos,
    and_false, false_and, dif_neg, not_false_eq_true]
  exact SimpleGraph.edist_comm

section Lipschitz

variable (hlip : ∀ x y, S.G.Adj x y → S.dep x ≤ S.dep y + 1)
include hlip

theorem dep_le_walk {u v : S.Λ} (p : (S.G.induce (S.Λ : Set σ)).Walk u v) :
    S.dep u ≤ S.dep v + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hadj p ih =>
    have h1 : S.dep a.1 ≤ S.dep b.1 + 1 := hlip _ _ hadj
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- D9.1 Output. `d_Λ` dominates the depth difference (edges change the depth by `≤ 1`). -/
theorem dep_le_of_domainEDist {x y : σ} {ρ : ℕ} (h : GraphDomain.domainEDist S.G S.Λ x y ≤ ρ) :
    S.dep x ≤ S.dep y + ρ := by
  unfold GraphDomain.domainEDist at h
  split_ifs at h with hxy
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top ρ) h)
    have h1 := S.dep_le_walk hlip p
    have h2 : (p.length : ℕ∞) ≤ ρ := hp ▸ h
    have h3 : p.length ≤ ρ := by exact_mod_cast h2
    change S.dep x ≤ S.dep y + p.length at h1
    omega
  · simp at h

theorem dep_le_of_mem_ball {x y : σ} {ρ : ℕ} (h : y ∈ GraphDomain.ball S.G S.Λ x ρ) :
    S.dep y ≤ S.dep x + ρ ∧ S.dep x ≤ S.dep y + ρ := by
  have h' := ((GraphDomain.mem_ball S.G).1 h).2
  exact ⟨S.dep_le_of_domainEDist hlip h',
    S.dep_le_of_domainEDist hlip ((S.domainEDist_comm x y).trans_le h')⟩

theorem odep_le_of_mem_ball {x y : σ} {ρ : ℕ} (h : y ∈ GraphDomain.ball S.G S.Λ x ρ)
    (b : Bool) : S.odep b y ≤ S.odep b x + ρ ∧ S.odep b x ≤ S.odep b y + ρ := by
  have := S.dep_le_of_mem_ball hlip h
  cases b
  · rw [odep_false, odep_false]; omega
  · rw [odep_true, odep_true]; omega

end Lipschitz

/-! ## D9.5, D9.6 The transitions -/

theorem mem_row {j : ℕ} {y : S.Λ} : y ∈ S.row j ↔ S.dep y = j := by
  simp [row]

theorem fillSlot_spec {g r : ℕ} {b : Bool} {w : ℕ} {y : S.Λ} (h : S.fillSlot g r b w = some y) :
    y.1 ∈ S.A ∧ S.dep y = if b then S.hi g r - w / S.n else S.lo g r + 1 + w / S.n := by
  unfold fillSlot at h
  rw [Option.filter_eq_some_iff] at h
  refine ⟨by simpa using h.2, ?_⟩
  cases b
  · simpa [mem_row] using S.mem_row.1 (List.mem_of_getElem? (by simpa using h.1))
  · simpa [mem_row] using S.mem_row.1 (List.mem_of_getElem? (by simpa using h.1))

theorem odep_fillSlot {g r t : ℕ} {b : Bool} {y : S.Λ}
    (h : S.fillSlot g r b (sideFills (fills t) b) = some y) :
    S.odep b y = S.front g r t b ∨ (b = true ∧ S.odep b y ≤ S.front g r t b) := by
  have h1 := (S.fillSlot_spec h).2
  cases b
  · left; simp only [if_false, Bool.false_eq_true] at h1; rw [odep_false, front_false, h1]
  · right; refine ⟨rfl, ?_⟩
    simp only [if_true] at h1
    rw [odep_true, front_true, h1]
    omega

theorem mem_chargeList {g r t : ℕ} {b : Bool} {i : S.Term} :
    i ∈ S.chargeList g r t b ↔
      S.front g r t b - S.r₀ ≤ S.odep b (S.a i) ∧ S.odep b (S.a i) ≤ S.front g r t b + S.D := by
  simp [chargeList]

theorem fills_of_even {t : ℕ} (ht : t % 2 = 0) : fills t = t / 2 := by
  unfold fills; omega

theorem step_eq_some {g r t v : ℕ} {st : S.State} {b : Bool} {x : Finset S.Λ}
    (h : S.step g r t v st = some (b, x)) :
    (t % 2 = 0 ∧ ∃ y, S.fillSlot g r b (sideFills (fills t) b) = some y ∧ x = {y}) ∨
    (t % 2 = 1 ∧ ∃ i ∈ S.chargeList g r t b, x = S.ball i ∩ middle st ∧
      (S.ball i ∩ side st b).Nonempty) := by
  unfold step at h
  split_ifs at h with ht
  · left
    refine ⟨ht, ?_⟩
    unfold fillStep at h
    rcases hs : S.fillSlot g r (decide (t / 2 % 2 = 1)) (sideFills (t / 2) (decide (t / 2 % 2 = 1)))
      with _ | y <;> rw [hs] at h
    · simp at h
    · simp only [Option.bind_some] at h
      split_ifs at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨y, by rw [fills_of_even ht]; exact hs, rfl⟩
  · right
    refine ⟨by omega, ?_⟩
    unfold chargeStep at h
    rcases hs : (S.chargeList g r t (decide (S.M ≤ v)))[v % S.M]? with _ | i <;> rw [hs] at h
    · simp at h
    · simp only [Option.bind_some] at h
      split_ifs at h with hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨i, List.mem_of_getElem? hs, rfl, hc.1⟩

/-- D9.8.3 (item 2, first claim). Every assigned site of `A` has oriented depth `≤ j + D + r₀`
on its side: a fill assigns a site at the front, a charge the sites of an `r₀`-ball around an
anchor of oriented depth `≤ j + D`; the front never decreases. -/
theorem lead (hlip : ∀ x y, S.G.Adj x y → S.dep x ≤ S.dep y + 1) :
    ∀ (t : ℕ) (h : S.Hist t) (g : Fin S.K) (b : Bool) (x : S.Λ), S.stateAt t h g x = some b →
      x.1 ∈ S.A → S.odep b x ≤ S.front g (S.offset t h g) t b + S.D + S.r₀
  | 0, h, g, b, x, hx, hA => by
    change S.init g (h g) x = some b at hx
    change S.odep b x ≤ S.front g (h g) 0 b + S.D + S.r₀
    simp only [init, hA, not_true_eq_false, if_false] at hx
    have hf0 : sideFills (fills 0) false / S.n = 0 ∧ sideFills (fills 0) true / S.n = 0 := by
      simp [fills, sideFills]
    split_ifs at hx with h1 h2 <;> cases hx
    · rw [odep_false, front_false, hf0.1]; push_cast; omega
    · rw [odep_true, front_true, hf0.2]; push_cast; omega
  | t + 1, h, g, b, x, hx, hA => by
    obtain ⟨h₀, c⟩ := h
    change S.stateAt (t + 1) (S.ext t h₀ c) g x = some b at hx
    change S.odep b x ≤ S.front g (S.offset t h₀ g) (t + 1) b + S.D + S.r₀
    rw [stateAt_ext] at hx
    have hmono := S.front_mono g (S.offset t h₀ g) (by omega : t ≤ t + 1) b
    by_cases h0 : S.stateAt t h₀ g x = none
    · rcases hs : S.step g (S.offset t h₀ g) t (c g) (S.stateAt t h₀ g) with _ | ⟨b', x'⟩
      · rw [hs] at hx; simp [applyStep, h0] at hx
      · rw [hs, applyStep_some_apply] at hx
        split_ifs at hx with hxx
        · cases hx
          rcases S.step_eq_some hs with ⟨-, y, hy, rfl⟩ | ⟨-, i, hi, rfl, -⟩
          · rw [mem_singleton] at hxx
            subst hxx
            rcases S.odep_fillSlot hy with h1 | ⟨-, h1⟩ <;> omega
          · have hwin := (S.mem_chargeList.1 hi).2
            have hball := (S.odep_le_of_mem_ball hlip
              (mem_subtype.1 (mem_inter.1 hxx).1 : x.1 ∈ _) b).1
            omega
        · rw [h0] at hx; cases hx
    · rw [S.applyStep_step_of_ne_none h0] at hx
      have := lead hlip t h₀ g b x hx hA
      omega

/-! ## The standing hypotheses -/

section Hyp

variable [DecidableRel S.G.Adj]

/-- The standing hypotheses of Lemma 9.1 on a scan: `scanner:test-geometry` (D9.3), ball growth,
anchors, and the scale relations of D9.2–D9.6 used in D9.8 (`2r₀ ≤ D`, `4(D + r₀ + 1) ≤ m`,
`8Km ≤ L`, the charge lists fit into `M` slots). -/
structure Hyp (V : ℕ → ℕ) (CT : ℝ) : Prop where
  tg : TestGeometry S.G S.Λ S.A S.dep CT S.n S.L S.r₀
  hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(GraphDomain.ball S.G Λ x r) ≤ V r
  hA : S.A ⊆ S.Λ
  anchor : ∀ Y ∈ GraphDomain.supports S.G S.Λ S.R, S.a Y ∈ Y
  n_pos : 0 < S.n
  D_pos : 0 < S.D
  r₀_le : 2 * S.r₀ ≤ S.D
  m_ge : 4 * (S.D + S.r₀ + 1) ≤ S.m
  KL : 8 * S.K * S.m ≤ S.L
  M_ge : AreaLaw.μ V S.R * (S.n * (S.D + S.r₀ + 1)) ≤ S.M

variable {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

theorem Hyp.hlip : ∀ x y, S.G.Adj x y → S.dep x ≤ S.dep y + 1 := H.tg.lipschitz

theorem Hyp.hi_add_le (g : Fin S.K) (r : Fin S.m) : S.hi g r + 2 * S.m ≤ S.L := by
  have h1 : 8 * ((g : ℕ) + 1) * S.m ≤ 8 * S.K * S.m :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ g.2)
  have h2 : 8 * ((g : ℕ) + 1) * S.m = 8 * g * S.m + 8 * S.m := by ring
  have := H.KL
  have := r.2
  simp only [hi]
  omega

end Hyp

theorem lo_ge (g r : ℕ) : S.m ≤ S.lo g r := by simp only [lo]; omega

theorem hi_eq (g r : ℕ) : S.hi g r = S.lo g r + 4 * S.m := by simp only [hi, lo]; omega

theorem init_eq_none {g r : ℕ} {y : S.Λ} (hy : S.init g r y = none) :
    y.1 ∈ S.A ∧ S.lo g r < S.dep y ∧ S.dep y ≤ S.hi g r := by
  simp only [init] at hy
  split_ifs at hy with h1 h2 h3
  simp_all

/-! ## Rows -/

theorem length_row (j : ℕ) : (S.row j).length = #(S.Λ.filter fun x => S.dep x = j) := by
  rw [row, Finset.length_toList, ← Finset.card_map (Function.Embedding.subtype (· ∈ S.Λ))]
  congr 1
  ext x
  simp [and_comm]

/-- The slot of a site in its row. -/
noncomputable def idx (y : S.Λ) : ℕ := (S.row (S.dep y)).idxOf y

theorem row_idx (y : S.Λ) : (S.row (S.dep y))[S.idx y]? = some y :=
  List.getElem?_idxOf (S.mem_row.2 rfl)

section HypRows

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

theorem Hyp.length_row_le {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ S.L) : (S.row j).length ≤ S.n :=
  (S.length_row j).trans_le (H.tg.card_row j h1 h2)

theorem Hyp.idx_lt {y : S.Λ} (h1 : 1 ≤ S.dep y) (h2 : S.dep y ≤ S.L) : S.idx y < S.n :=
  (List.idxOf_lt_length_of_mem (S.mem_row.2 rfl)).trans_le (H.length_row_le h1 h2)

theorem Hyp.fillSlot_near {g r : ℕ} {y : S.Λ} (hA : y.1 ∈ S.A) (hlo : S.lo g r + 1 ≤ S.dep y)
    (hL : S.dep y ≤ S.L) :
    S.fillSlot g r false (S.n * (S.dep y - S.lo g r - 1) + S.idx y) = some y := by
  have hi := H.idx_lt (y := y) (by omega) hL
  have hn := H.n_pos
  have h1 : (S.n * (S.dep y - S.lo g r - 1) + S.idx y) / S.n = S.dep y - S.lo g r - 1 := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hi, add_zero]
  have h2 : (S.n * (S.dep y - S.lo g r - 1) + S.idx y) % S.n = S.idx y := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have h3 : S.lo g r + 1 + (S.dep y - S.lo g r - 1) = S.dep y := by omega
  simp only [fillSlot, Bool.false_eq_true, if_false, h1, h2, h3, row_idx]
  simp [hA]

theorem Hyp.fillSlot_far {g r : ℕ} {y : S.Λ} (hA : y.1 ∈ S.A) (h1 : 1 ≤ S.dep y)
    (hhi : S.dep y ≤ S.hi g r) (hL : S.dep y ≤ S.L) :
    S.fillSlot g r true (S.n * (S.hi g r - S.dep y) + (S.n - 1 - S.idx y)) = some y := by
  have hi := H.idx_lt (y := y) h1 hL
  have hn := H.n_pos
  have hlt : S.n - 1 - S.idx y < S.n := by omega
  have e1 : (S.n * (S.hi g r - S.dep y) + (S.n - 1 - S.idx y)) / S.n = S.hi g r - S.dep y := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hlt, add_zero]
  have e2 : (S.n * (S.hi g r - S.dep y) + (S.n - 1 - S.idx y)) % S.n = S.n - 1 - S.idx y := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have e3 : S.hi g r - (S.hi g r - S.dep y) = S.dep y := by omega
  have e4 : S.n - 1 - (S.n - 1 - S.idx y) = S.idx y := by omega
  simp only [fillSlot, if_true, e1, e2, e3, e4, row_idx]
  simp [hA]

/-- Before round `t ≤ 2nm`, near-side `A`-sites have depth `≤ lo + 1 + m + D + r₀`. -/
theorem Hyp.near_dep_le {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {x : S.Λ}
    (hx : S.stateAt t h g x = some false) (hA : x.1 ∈ S.A) :
    S.dep x ≤ S.lo g (S.offset t h g) + 1 + S.m + S.D + S.r₀ := by
  have h1 := S.lead H.hlip t h g false x hx hA
  have h2 := S.sideFills_div_le ht false
  rw [odep_false, front_false] at h1
  push_cast at h1
  omega

/-- Before round `t ≤ 2nm`, far-side `A`-sites have depth `≥ hi - m - D - r₀`. -/
theorem Hyp.far_dep_ge {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {x : S.Λ}
    (hx : S.stateAt t h g x = some true) (hA : x.1 ∈ S.A) :
    S.hi g (S.offset t h g) ≤ S.dep x + S.m + S.D + S.r₀ := by
  have h1 := S.lead H.hlip t h g true x hx hA
  have h2 := S.sideFills_div_le ht true
  rw [odep_true, front_true] at h1
  omega

/-- D9.8.4. A fill slot is never consumed by the opposite side: consumed slots are assigned to
the consuming side. -/
theorem Hyp.consumed : ∀ (t : ℕ), t ≤ S.T → ∀ (h : S.Hist t) (g : Fin S.K) (u : ℕ), 2 * u < t →
    ∀ y : S.Λ, S.fillSlot g (S.offset t h g) (decide (u % 2 = 1))
      (sideFills u (decide (u % 2 = 1))) = some y →
    S.stateAt t h g y = some (decide (u % 2 = 1))
  | 0, _, _, _, u, hu, _, _ => absurd hu (by omega)
  | t + 1, ht, h, g, u, hu, y, hy => by
    obtain ⟨h₀, c⟩ := h
    change S.fillSlot g (S.offset t h₀ g) _ _ = _ at hy
    change S.stateAt (t + 1) (S.ext t h₀ c) g y = _
    rw [stateAt_ext]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | hu'
    · have h1 := Hyp.consumed t (by omega) h₀ g u hu' y hy
      rw [S.applyStep_step_of_ne_none (by rw [h1]; simp), h1]
    · have ht2 : t % 2 = 0 := by omega
      have htu : t / 2 = u := by omega
      by_cases hst : S.stateAt t h₀ g y = none
      · have hstep : S.step g (S.offset t h₀ g) t (c g) (S.stateAt t h₀ g) =
            some (decide (u % 2 = 1), {y}) := by
          simp only [step, ht2, if_true, fillStep, htu, hy, Option.bind_some, hst]
        rw [hstep, applyStep_some_apply, if_pos (mem_singleton_self y)]
      · rw [S.applyStep_step_of_ne_none hst]
        obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 hst
        rw [hb']
        have hspec := S.fillSlot_spec hy
        have hu2 : sideFills u (decide (u % 2 = 1)) / S.n ≤ S.m := by
          apply Nat.div_le_of_le_mul
          have := sideFills_le u (decide (u % 2 = 1))
          have := S.T_eq
          nlinarith
        have hhi := S.hi_eq g (S.offset t h₀ g)
        have hm := H.m_ge
        cases hb : decide (u % 2 = 1) <;> rw [hb] at hspec hu2 <;>
          simp only [Bool.false_eq_true, if_false, if_true] at hspec <;> cases b'
        all_goals first
          | rfl
          | (have := H.far_dep_ge (by omega) h₀ g hb' hspec.1; omega)
          | (have := H.near_dep_le (by omega) h₀ g hb' hspec.1; omega)

theorem Hyp.consumed_near {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {y : S.Λ}
    (hA : y.1 ∈ S.A) (hlo : S.lo g (S.offset t h g) + 1 ≤ S.dep y) (hL : S.dep y ≤ S.L)
    (hw : S.n * (S.dep y - S.lo g (S.offset t h g) - 1) + S.idx y < sideFills (fills t) false) :
    S.stateAt t h g y = some false := by
  set w := S.n * (S.dep y - S.lo g (S.offset t h g) - 1) + S.idx y
  have h1 : decide ((2 * w) % 2 = 1) = false := by simp
  have h2 : sideFills (2 * w) false = w := by
    simp only [sideFills, Bool.false_eq_true, ↓reduceIte]; omega
  unfold sideFills fills at hw
  simp only [Bool.false_eq_true, ↓reduceIte] at hw
  have := H.consumed t ht h g (2 * w) (by omega) y
    (by rw [h1, h2]; exact H.fillSlot_near hA hlo hL)
  rwa [h1] at this

theorem Hyp.consumed_far {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {y : S.Λ}
    (hA : y.1 ∈ S.A) (h1 : 1 ≤ S.dep y) (hhi : S.dep y ≤ S.hi g (S.offset t h g))
    (hL : S.dep y ≤ S.L)
    (hw : S.n * (S.hi g (S.offset t h g) - S.dep y) + (S.n - 1 - S.idx y) <
      sideFills (fills t) true) :
    S.stateAt t h g y = some true := by
  set w := S.n * (S.hi g (S.offset t h g) - S.dep y) + (S.n - 1 - S.idx y)
  have e1 : decide ((2 * w + 1) % 2 = 1) = true := by simp
  have e2 : sideFills (2 * w + 1) true = w := by simp only [sideFills, ↓reduceIte]; omega
  unfold sideFills fills at hw
  simp only [↓reduceIte] at hw
  have := H.consumed t ht h g (2 * w + 1) (by omega) y
    (by rw [e1, e2]; exact H.fillSlot_far hA h1 hhi hL)
  rwa [e1] at this

/-- D9.5 Output. Every site of oriented depth `< j` is assigned: middle sites lie between the two
fronts. -/
theorem Hyp.middle_bounds {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K) {y : S.Λ}
    (hy : S.stateAt t h g y = none) :
    y.1 ∈ S.A ∧ S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n ≤ S.dep y ∧
      S.dep y + sideFills (fills t) true / S.n ≤ S.hi g (S.offset t h g) := by
  have hinit : S.init g (S.offset t h g) y = none := by
    rcases hi : S.init g (S.offset t h g) y with _ | b
    · rfl
    · rw [S.stateAt_of_init h g hi] at hy; cases hy
  obtain ⟨hA, hlo, hhi⟩ := S.init_eq_none hinit
  have hL := H.hi_add_le g (S.offset t h g)
  have hn := H.n_pos
  have hidx := H.idx_lt (y := y) (by omega) (by omega)
  refine ⟨hA, ?_, ?_⟩
  · by_contra hc
    have h1 : S.n * (S.dep y - S.lo g (S.offset t h g) - 1 + 1) ≤
        S.n * (sideFills (fills t) false / S.n) := Nat.mul_le_mul_left _ (by omega)
    have h2 := Nat.mul_div_le (sideFills (fills t) false) S.n
    have h3 : S.n * (S.dep y - S.lo g (S.offset t h g) - 1 + 1) =
        S.n * (S.dep y - S.lo g (S.offset t h g) - 1) + S.n := by ring
    rw [H.consumed_near ht h g hA (by omega) (by omega) (by omega)] at hy
    cases hy
  · by_contra hc
    have h1 : S.n * (S.hi g (S.offset t h g) - S.dep y + 1) ≤
        S.n * (sideFills (fills t) true / S.n) := Nat.mul_le_mul_left _ (by omega)
    have h2 := Nat.mul_div_le (sideFills (fills t) true) S.n
    have h3 : S.n * (S.hi g (S.offset t h g) - S.dep y + 1) =
        S.n * (S.hi g (S.offset t h g) - S.dep y) + S.n := by ring
    rw [H.consumed_far ht h g hA (by omega) hhi (by omega) (by omega)] at hy
    cases hy

end HypRows

end Scan

end AreaLaw.Scanner
