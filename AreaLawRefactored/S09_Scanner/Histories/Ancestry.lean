import AreaLawRefactored.S09_Scanner.Histories.Dilution

/-!
# §9.1 Lemma 9.1 (4): charge ancestry and the bad-history tail (D9.8.12–15)

Digest `digest/09-scanner.md` D9.8.12–D9.8.15. A site of a side lying more than `D/2` beyond the
front was assigned by a chain of charges, each ball meeting the previous one, whose depth gain
`2 r₀` per charge must beat the advance of the front (D9.8.12, D9.8.13). The chains are counted
by their charge times and their terms (D9.8.14); each prescribed chain has classical probability
`(2 M)^{-length}`, and the union over chains is `exp(-n^{κ - o(1)})` (D9.8.15).
-/

open scoped Matrix
open Finset Arealaw

namespace AreaLaw.Scanner

universe u

open Transport (MeanTree)
open Comparators (physReg Site)

theorem List.zip_fun {α β : Type*} : ∀ {ts : List α} {Ys : List β} (_ : ts.Nodup) {s : α}
    {Y Y' : β}, (s, Y) ∈ ts.zip Ys → (s, Y') ∈ ts.zip Ys → Y = Y'
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | a :: ts, b :: Ys, hts, s, Y, Y', h1, h2 => by
    rw [List.zip_cons_cons, List.mem_cons] at h1 h2
    rw [List.nodup_cons] at hts
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · simp only [Prod.mk.injEq] at h1 h2; rw [h1.2, h2.2]
    · simp only [Prod.mk.injEq] at h1; exact absurd (h1.1 ▸ List.of_mem_zip h2).1 hts.1
    · simp only [Prod.mk.injEq] at h2; exact absurd (h2.1 ▸ List.of_mem_zip h1).1 hts.1
    · exact List.zip_fun hts.2 h1 h2

theorem List.exists_mem_zip {α β : Type*} : ∀ {ts : List α} {Ys : List β},
    ts.length = Ys.length → ∀ {s : α}, s ∈ ts → ∃ Y, (s, Y) ∈ ts.zip Ys
  | [], _, _, _, h => by simp at h
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: ts, b :: Ys, hl, s, h => by
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨b, by simp⟩
    · obtain ⟨Y, hY⟩ := List.exists_mem_zip (by simpa using hl) h
      exact ⟨Y, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hY⟩

namespace Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ)

/-! ## The recorded choices -/

/-- The value of the band-`g` choice of round `s` recorded in a history before round `t`. -/
def chVal : (t : ℕ) → S.Hist t → ℕ → Fin S.K → ℕ
  | 0, _, _, _ => 0
  | t + 1, h, s, g => if s = t then (h.2 g : ℕ) else chVal t h.1 s g

theorem chVal_ext (t : ℕ) (h : S.Hist t) (c : S.Ch t) (s : ℕ) (g : Fin S.K) :
    S.chVal (t + 1) (S.ext t h c) s g = if s = t then (c g : ℕ) else S.chVal t h s g := rfl

/-- D9.6. The band-`g` slot value `v` of round `s` (offset `r`) selects the term `Y` on side `b`.
-/
def Sel (g : Fin S.K) (r s v : ℕ) (b : Bool) (Y : S.Term) : Prop :=
  v < 2 * S.M ∧ decide (S.M ≤ v) = b ∧ (S.chargeList g r s b)[v % S.M]? = some Y

theorem Sel_unique {g : Fin S.K} {r s v v' : ℕ} {b : Bool} {Y : S.Term} (h1 : S.Sel g r s v b Y)
    (h2 : S.Sel g r s v' b Y) : v = v' := by
  obtain ⟨hv, hb, hl⟩ := h1
  obtain ⟨hv', hb', hl'⟩ := h2
  have hk : v % S.M = v' % S.M := by
    rw [List.getElem?_eq_some_iff] at hl hl'
    obtain ⟨h1, h2⟩ := hl
    obtain ⟨h1', h2'⟩ := hl'
    exact ((S.chargeList_nodup _ _ _ _).getElem_inj_iff).1 (h2.trans h2'.symm)
  have hM := S.M_pos
  rw [← hb'] at hb
  by_cases h : S.M ≤ v
  · have h' : S.M ≤ v' := by simpa [h] using hb
    have e1 : v % S.M = v - S.M := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    have e2 : v' % S.M = v' - S.M := by
      rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
    omega
  · have h' : ¬ S.M ≤ v' := by simpa [h] using hb
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hk
    exact hk

/-! ## D9.8.14 Chains of terms -/

/-- The terms whose `r₀`-ball contains the site `z`. -/
noncomputable def nearTerms (z : S.Λ) : Finset S.Term := univ.filter fun Y => z ∈ S.ball Y

/-- D9.8.14. The linked term sequences of length `ℓ` from a site `z`: a term whose ball contains
`z`, a site of that ball, and a linked sequence from it. -/
noncomputable def LL : S.Λ → ℕ → Finset (List S.Term)
  | _, 0 => {[]}
  | z, ℓ + 1 => (S.nearTerms z).biUnion fun Y => (S.ball Y).biUnion fun z' =>
      (LL z' ℓ).image (Y :: ·)

theorem mem_LL_succ {z z' : S.Λ} {ℓ : ℕ} {Y : S.Term} {Ys : List S.Term} (hz : z ∈ S.ball Y)
    (hz' : z' ∈ S.ball Y) (hYs : Ys ∈ S.LL z' ℓ) : Y :: Ys ∈ S.LL z (ℓ + 1) := by
  simp only [LL, mem_biUnion, mem_image]
  exact ⟨Y, by simp [nearTerms, hz], z', hz', Ys, hYs, rfl⟩

theorem length_of_mem_LL : ∀ {z : S.Λ} {ℓ : ℕ} {Ys : List S.Term}, Ys ∈ S.LL z ℓ → Ys.length = ℓ
  | _, 0, Ys, h => by simp [LL] at h; simp [h]
  | z, ℓ + 1, Ys, h => by
    simp only [LL, mem_biUnion, mem_image] at h
    obtain ⟨Y, -, z', -, Ys', hYs', rfl⟩ := h
    simp [length_of_mem_LL hYs']

section Counting

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

theorem Hyp.card_ball (Y : S.Term) : #(S.ball Y) ≤ V S.r₀ :=
  (card_le_card_of_injOn (fun x : S.Λ => x.1) (fun _ hx => mem_subtype.1 hx)
    Subtype.val_injective.injOn).trans (H.hV _ _ _)

/-- D2.8. At most `μ_R V(r₀)` terms have a given site in their `r₀`-ball. -/
theorem Hyp.card_nearTerms (z : S.Λ) : #(S.nearTerms z) ≤ AreaLaw.μ V S.R * V S.r₀ := by
  refine (card_le_mul_card_image_of_maps_to (f := fun i : S.Term => S.a i)
    (t := GraphDomain.ball S.G S.Λ z S.r₀) ?_ (AreaLaw.μ V S.R) ?_).trans
      (Nat.mul_le_mul_left _ (H.hV _ _ _))
  · intro Y hY
    simp only [nearTerms, mem_filter, mem_univ, true_and, ball, mem_subtype] at hY
    have h := (GraphDomain.mem_ball S.G).1 hY
    rw [GraphDomain.mem_ball]
    refine ⟨((GraphDomain.mem_supports S.G).1 Y.2).1 (H.anchor Y.1 Y.2), ?_⟩
    rw [S.domainEDist_comm]
    exact h.2
  · intro x _
    refine le_trans (card_le_card_of_injOn (fun i : S.Term => i.1)
      (t := (GraphDomain.supports S.G S.Λ S.R).filter fun Y => S.a Y = x) ?_
      Subtype.val_injective.injOn) ((step_2_8 S.G V H.hV S.Λ S.R x).2.1 S.a H.anchor)
    intro i hi
    simp only [coe_filter] at hi ⊢
    exact ⟨i.2, hi.2⟩

/-- D9.8.14. `#{linked sequences of length ℓ} ≤ (μ_R V(r₀)²)^ℓ`. -/
theorem Hyp.card_LL : ∀ (z : S.Λ) (ℓ : ℕ),
    #(S.LL z ℓ) ≤ (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ
  | _, 0 => by simp [LL]
  | z, ℓ + 1 => by
    simp only [LL]
    calc #((S.nearTerms z).biUnion fun Y => (S.ball Y).biUnion fun z' =>
            (S.LL z' ℓ).image (Y :: ·))
        ≤ ∑ Y ∈ S.nearTerms z, #((S.ball Y).biUnion fun z' => (S.LL z' ℓ).image (Y :: ·)) :=
          card_biUnion_le
      _ ≤ ∑ _Y ∈ S.nearTerms z, V S.r₀ * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ := by
          refine sum_le_sum fun Y _ => card_biUnion_le.trans ?_
          calc ∑ z' ∈ S.ball Y, #((S.LL z' ℓ).image (Y :: ·))
              ≤ ∑ _z' ∈ S.ball Y, (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ :=
                sum_le_sum fun z' _ => card_image_le.trans (Hyp.card_LL z' ℓ)
            _ ≤ V S.r₀ * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ := by
                rw [sum_const, smul_eq_mul]
                exact Nat.mul_le_mul_right _ (H.card_ball Y)
      _ ≤ (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ (ℓ + 1) := by
          rw [sum_const, smul_eq_mul, pow_succ]
          calc #(S.nearTerms z) * (V S.r₀ * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ)
              ≤ (AreaLaw.μ V S.R * V S.r₀) * (V S.r₀ * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ) :=
                Nat.mul_le_mul_right _ (H.card_nearTerms z)
            _ = (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) ^ ℓ * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) :=
                by ring

end Counting

/-! ## D9.8.12 The ancestry chain -/

theorem chargeStep_spec {g r t v : ℕ} {st : S.State} {b : Bool} {x : Finset S.Λ}
    (h : S.chargeStep g r t v st = some (b, x)) :
    ∃ Y, (S.chargeList g r t b)[v % S.M]? = some Y ∧ b = decide (S.M ≤ v) ∧
      x = S.ball Y ∩ middle st ∧ (S.ball Y ∩ side st b).Nonempty := by
  unfold chargeStep at h
  rcases hs : (S.chargeList g r t (decide (S.M ≤ v)))[v % S.M]? with _ | Y <;> rw [hs] at h
  · simp at h
  · simp only [Option.bind_some] at h
    split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨Y, hs, rfl, rfl, hc.1⟩

theorem odep_init_lt {g r : ℕ} {x : S.Λ} {b : Bool} (hx : S.init g r x = some b)
    (hA : x.1 ∈ S.A) : S.odep b x < S.front g r 0 b := by
  simp only [init, hA, not_true_eq_false, if_false] at hx
  have hf0 : sideFills (fills 0) false / S.n = 0 ∧ sideFills (fills 0) true / S.n = 0 := by
    simp [fills, sideFills]
  split_ifs at hx with h1 h2 <;> cases hx
  · rw [odep_false, front_false, hf0.1]; push_cast; omega
  · rw [odep_true, front_true, hf0.2]; push_cast; omega

section Chain

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

/-- D9.8.12 (ancestry inequality). An assigned site `x ∈ A` of side `b` before round `t` has a
chain of charges at rounds `t > s₁ > ⋯ > s_ℓ ≥ t₁` selecting linked terms `Y₁, …, Y_ℓ` on side
`b` (each ball meeting the next, the first containing `x`), and
`λ_b(x) ≤ j_b(t₁) + 2 r₀ ℓ`. -/
theorem Hyp.chain : ∀ (t : ℕ) (h : S.Hist t) (g : Fin S.K) (b : Bool) (x : S.Λ),
    S.stateAt t h g x = some b → x.1 ∈ S.A →
    ∃ (ts : List ℕ) (Ys : List S.Term) (t₁ : ℕ), ts.length = Ys.length ∧
      Ys ∈ S.LL x Ys.length ∧ t₁ ≤ t ∧ ts.Pairwise (· > ·) ∧
      (∀ s ∈ ts, t₁ ≤ s ∧ s < t ∧ s % 2 = 1) ∧
      (∀ p ∈ ts.zip Ys, S.Sel g (S.offset t h g) p.1 (S.chVal t h p.1 g) b p.2) ∧
      S.odep b x ≤ S.front g (S.offset t h g) t₁ b + 2 * S.r₀ * Ys.length
  | 0, h, g, b, x, hx, hA => by
    have h1 := S.odep_init_lt (r := (h g : ℕ)) hx hA
    refine ⟨[], [], 0, rfl, by simp [LL], le_rfl, List.Pairwise.nil, by simp, by simp, ?_⟩
    change S.odep b x ≤ S.front g (h g) 0 b + 2 * S.r₀ * ([] : List S.Term).length
    simp only [List.length_nil, CharP.cast_eq_zero, mul_zero, add_zero]
    exact h1.le
  | t + 1, h, g, b, x, hx, hA => by
    obtain ⟨h₀, c⟩ := h
    change S.stateAt (t + 1) (S.ext t h₀ c) g x = some b at hx
    change ∃ (ts : List ℕ) (Ys : List S.Term) (t₁ : ℕ), ts.length = Ys.length ∧
      Ys ∈ S.LL x Ys.length ∧ t₁ ≤ t + 1 ∧ ts.Pairwise (· > ·) ∧
      (∀ s ∈ ts, t₁ ≤ s ∧ s < t + 1 ∧ s % 2 = 1) ∧
      (∀ p ∈ ts.zip Ys, S.Sel g (S.offset t h₀ g) p.1 (S.chVal (t + 1) (S.ext t h₀ c) p.1 g) b
        p.2) ∧
      S.odep b x ≤ S.front g (S.offset t h₀ g) t₁ b + 2 * S.r₀ * Ys.length
    rw [stateAt_ext] at hx
    by_cases h0 : S.stateAt t h₀ g x = none
    · rcases hs : S.step g (S.offset t h₀ g) t (c g) (S.stateAt t h₀ g) with _ | ⟨b', x'⟩
      · rw [hs] at hx; simp [applyStep, h0] at hx
      rw [hs, applyStep_some_apply] at hx
      split_ifs at hx with hxx
      swap
      · rw [h0] at hx; cases hx
      cases hx
      unfold step at hs
      split_ifs at hs with ht2
      · -- a fill: the site is at the front
        have hs' : S.step g (S.offset t h₀ g) t (c g) (S.stateAt t h₀ g) = some (b, x') := by
          unfold step; rw [if_pos ht2]; exact hs
        rcases S.step_eq_some hs' with ⟨-, y, hy, rfl⟩ | ⟨h1, -⟩
        · rw [mem_singleton] at hxx
          subst hxx
          refine ⟨[], [], t, rfl, by simp [LL], by omega, List.Pairwise.nil, by simp, by simp, ?_⟩
          rcases S.odep_fillSlot hy with h1 | ⟨-, h1⟩ <;> simp <;> omega
        · omega
      · -- a charge: the ball meets the side; follow a previously assigned site of the ball
        obtain ⟨Y, hsel, hb, rfl, ⟨z, hz⟩⟩ := S.chargeStep_spec hs
        rw [mem_inter, mem_side] at hz
        rw [mem_inter, mem_middle] at hxx
        have hxS₀ : x.1 ∈ S.S₀ := by
          have hinit : S.init g (S.offset t h₀ g) x = none := by
            rcases hi : S.init g (S.offset t h₀ g) x with _ | b''
            · rfl
            · rw [S.stateAt_of_init h₀ g hi] at h0; cases h0
          obtain ⟨hA', -, hhi⟩ := S.init_eq_none hinit
          have := H.hi_add_le g (S.offset t h₀ g)
          exact mem_filter.2 ⟨hA', by omega⟩
        have hAb := H.up_ball_subset_A Y hxx.1 hxS₀
        have hzA := hAb (S.mem_up hz.1)
        obtain ⟨ts, Ys, t₁, hl, hLL, ht₁, hsort, hts, hsel', hdep⟩ :=
          Hyp.chain t h₀ g b z hz.2 hzA
        have hct : S.c t = 2 * S.M := S.c_of_odd (by omega)
        have hv : ((c g : ℕ)) < 2 * S.M := hct ▸ (c g).2
        refine ⟨t :: ts, Y :: Ys, t₁, by simp [hl], ?_, by omega, ?_, ?_, ?_, ?_⟩
        · exact S.mem_LL_succ hxx.1 hz.1 hLL
        · rw [List.pairwise_cons]
          exact ⟨fun s hs => (hts s hs).2.1, hsort⟩
        · intro s hs
          rw [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact ⟨by omega, by omega, by omega⟩
          · have := hts s hs
            exact ⟨this.1, by omega, this.2.2⟩
        · intro p hp
          rw [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · refine ⟨?_, ?_, ?_⟩
            · simp only [chVal_ext, if_true]; exact hv
            · simp only [chVal_ext, if_true]; exact hb.symm
            · simp only [chVal_ext, if_true]; exact hsel
          · have hlt := (hts p.1 (List.of_mem_zip hp).1).2.1
            simp only [chVal_ext, if_neg (show p.1 ≠ t by omega)]
            exact hsel' p hp
        · have hxb : x.1 ∈ GraphDomain.ball S.G S.Λ (S.a Y) S.r₀ := mem_subtype.1 hxx.1
          have hzb : z.1 ∈ GraphDomain.ball S.G S.Λ (S.a Y) S.r₀ := mem_subtype.1 hz.1
          have h1 := (S.odep_le_of_mem_ball H.hlip hxb b).1
          have h2 := (S.odep_le_of_mem_ball H.hlip hzb b).2
          simp only [List.length_cons]
          push_cast
          linarith
    · rw [S.applyStep_step_of_ne_none h0] at hx
      obtain ⟨ts, Ys, t₁, hl, hLL, ht₁, hsort, hts, hsel', hdep⟩ := Hyp.chain t h₀ g b x hx hA
      refine ⟨ts, Ys, t₁, hl, hLL, by omega, hsort, fun s hs => ?_, fun p hp => ?_, hdep⟩
      · have := hts s hs
        exact ⟨this.1, by omega, this.2.2⟩
      · have hlt := (hts p.1 (List.of_mem_zip hp).1).2.1
        simp only [chVal_ext, if_neg (show p.1 ≠ t by omega)]
        exact hsel' p hp

end Chain

/-! ## D9.8.14 The probability of a prescribed chain -/

open Classical in
/-- The indicator `1_p ∈ {0, 1}` of a proposition. -/
noncomputable def ind (p : Prop) : ℝ := if p then 1 else 0

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by unfold ind; split_ifs <;> norm_num

theorem ind_pos {p : Prop} (hp : p) : ind p = 1 := by unfold ind; rw [if_pos hp]

theorem ind_neg {p : Prop} (hp : ¬ p) : ind p = 0 := by unfold ind; rw [if_neg hp]

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by unfold ind; split_ifs <;> norm_num

open Classical in
/-- D9.8.14. Prescribing (by predicates allowing at most one slot value each) the band-`g`
choices at distinct charge rounds `s ∈ T_s` has classical probability `≤ (2M)^{-|T_s|}`: the
choices are uniform and independent across rounds. -/
theorem prob_sel (g : Fin S.K) (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ s r v v', v < 2 * S.M → v' < 2 * S.M → P s r v → P s r v' → v = v') :
    ∀ (t : ℕ) (Ts : Finset ℕ), (∀ s ∈ Ts, s < t ∧ s % 2 = 1) →
      ∑ h, (S.histTree t).weight h * ∏ s ∈ Ts, ind (P s (S.offset t h g) (S.chVal t h s g)) ≤
          (1 / (2 * S.M)) ^ #Ts
  | 0, Ts, hTs => by
    have : Ts = ∅ := eq_empty_of_forall_notMem fun s hs => by have := hTs s hs; omega
    subst this
    simp only [prod_empty, mul_one, card_empty, pow_zero]
    exact (MeanTree.sum_weight _).le
  | t + 1, Ts, hTs => by
    rw [S.sum_histTree_succ]
    simp_rw [chVal_ext, offset_ext]
    have hw0 : ∀ h, 0 ≤ (S.histTree t).weight h := fun h => MeanTree.weight_nonneg _ _
    by_cases ht : t ∈ Ts
    · have hodd := (hTs t ht).2
      have hct : S.c t = 2 * S.M := S.c_of_odd hodd
      have hM : (0 : ℝ) < 2 * S.M := by have := S.M_pos; positivity
      have hcoord : ∀ r : ℕ, ∑ c : S.Ch t, (uniformTree (S.Ch t)).weight c *
          ind (P t r (c g)) ≤ 1 / (2 * S.M) := by
        intro r
        rw [← sum_fiberwise univ (fun c : S.Ch t => c g)]
        have e : ∀ v : Fin (S.c t), ∑ c ∈ univ.filter (fun c : S.Ch t => c g = v),
            (uniformTree (S.Ch t)).weight c * ind (P t r (c g)) = ind (P t r v) / S.c t := by
          intro v
          rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], ← sum_mul,
            S.sum_choice_apply]
          ring
        simp_rw [e, ← sum_div]
        have hcard : ∑ v : Fin (S.c t), ind (P t r v) ≤ 1 := by
          classical
          have h1 : ∑ v : Fin (S.c t), ind (P t r v) =
              #(univ.filter fun v : Fin (S.c t) => P t r v) := by
            rw [← sum_boole]
            exact sum_congr rfl fun v _ => rfl
          rw [h1]
          have h2 : #(univ.filter fun v : Fin (S.c t) => P t r v) ≤ 1 := by
            refine card_le_one.2 fun v hv v' hv' => Fin.ext ?_
            simp only [mem_filter, mem_univ, true_and] at hv hv'
            exact hP t r v v' (hct ▸ v.2) (hct ▸ v'.2) hv hv'
          exact_mod_cast h2
        have hc0 : (0 : ℝ) < S.c t := by exact_mod_cast S.c_pos t
        calc (∑ v : Fin (S.c t), ind (P t r v)) / (S.c t : ℝ) ≤ 1 / (S.c t : ℝ) :=
              div_le_div_of_nonneg_right hcard hc0.le
          _ = 1 / (2 * S.M) := by rw [hct]; push_cast; ring
      have key : ∀ h : S.Hist t, ∑ c : S.Ch t, (uniformTree (S.Ch t)).weight c *
          ∏ s ∈ Ts, ind (P s (S.offset t h g) (if s = t then (c g : ℕ) else S.chVal t h s g)) ≤
          1 / (2 * S.M) * ∏ s ∈ Ts.erase t, ind (P s (S.offset t h g) (S.chVal t h s g)) := by
        intro h
        have e : ∀ c : S.Ch t, ∏ s ∈ Ts, ind (P s (S.offset t h g)
            (if s = t then (c g : ℕ) else S.chVal t h s g)) =
            ind (P t (S.offset t h g) (c g)) * ∏ s ∈ Ts.erase t,
              ind (P s (S.offset t h g) (S.chVal t h s g)) := by
          intro c
          rw [← Finset.mul_prod_erase Ts _ ht, if_pos rfl]
          congr 1
          refine prod_congr rfl fun s hs => ?_
          rw [if_neg (ne_of_mem_erase hs)]
        simp_rw [e, ← mul_assoc, ← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hcoord _) (prod_nonneg fun s _ => ind_nonneg _)
      have ih := prob_sel g P hP t (Ts.erase t) fun s hs =>
        ⟨by have := (hTs s (mem_of_mem_erase hs)).1; have := ne_of_mem_erase hs; omega,
          (hTs s (mem_of_mem_erase hs)).2⟩
      calc _ ≤ ∑ h, (S.histTree t).weight h * (1 / (2 * S.M) * ∏ s ∈ Ts.erase t,
              ind (P s (S.offset t h g) (S.chVal t h s g))) :=
            sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (key h) (hw0 h)
        _ = 1 / (2 * S.M) * ∑ h, (S.histTree t).weight h * ∏ s ∈ Ts.erase t,
              ind (P s (S.offset t h g) (S.chVal t h s g)) := by
            rw [mul_sum]
            exact sum_congr rfl fun h _ => by ring
        _ ≤ 1 / (2 * S.M) * (1 / (2 * S.M)) ^ #(Ts.erase t) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (1 / (2 * S.M)) ^ #Ts := by
            rw [card_erase_of_mem ht, ← pow_succ']
            congr 1
            have := card_pos.2 ⟨t, ht⟩
            omega
    · have e : ∀ (h : S.Hist t) (c : S.Ch t), ∏ s ∈ Ts, ind (P s (S.offset t h g)
          (if s = t then (c g : ℕ) else S.chVal t h s g)) =
          ∏ s ∈ Ts, ind (P s (S.offset t h g) (S.chVal t h s g)) :=
        fun h c => prod_congr rfl fun s hs => by rw [if_neg fun e : s = t => ht (e ▸ hs)]
      simp_rw [e, ← Finset.sum_mul, MeanTree.sum_weight, one_mul]
      exact prob_sel g P hP t Ts fun s hs =>
        ⟨by have := (hTs s hs).1; have : s ≠ t := fun e => ht (e ▸ hs); omega, (hTs s hs).2⟩

/-! ## D9.8.13 The time window -/

theorem front_gap (g r : ℕ) {t₁ t : ℕ} (h : t₁ ≤ t) (b : Bool) (hn : 0 < S.n) :
    ((t : ℤ) - t₁) < 4 * S.n * (S.front g r t b - S.front g r t₁ b + 3) := by
  have h1 : t - t₁ ≤ 4 * (sideFills (fills t) b - sideFills (fills t₁) b) + 6 := by
    unfold sideFills fills
    split_ifs <;> omega
  have h2 := sideFills_mono (fills_mono h) b
  have h3 := Nat.div_add_mod (sideFills (fills t) b) S.n
  have h4 := Nat.mod_lt (sideFills (fills t) b) hn
  have h5 := Nat.mul_div_le (sideFills (fills t₁) b) S.n
  have h6 := Nat.div_le_div_right (c := S.n) h2
  have hfront : S.front g r t b - S.front g r t₁ b =
      ((sideFills (fills t) b / S.n : ℕ) : ℤ) - ((sideFills (fills t₁) b / S.n : ℕ) : ℤ) := by
    cases b
    · rw [front_false, front_false]; push_cast; ring
    · rw [front_true, front_true]; ring
  rw [hfront]
  have h7 : (S.n : ℤ) * ((sideFills (fills t) b / S.n : ℕ) : ℤ) +
      ((sideFills (fills t) b % S.n : ℕ) : ℤ) = (sideFills (fills t) b : ℤ) := by
    exact_mod_cast h3
  have h8 : (S.n : ℤ) * ((sideFills (fills t₁) b / S.n : ℕ) : ℤ) ≤
      (sideFills (fills t₁) b : ℤ) := by
    exact_mod_cast h5
  have h9 : ((sideFills (fills t) b % S.n : ℕ) : ℤ) < S.n := by exact_mod_cast h4
  have h10 : ((t : ℤ) - t₁) ≤ 4 * ((sideFills (fills t) b : ℤ) - sideFills (fills t₁) b) + 6 := by
    have := h1
    have h11 : ((sideFills (fills t) b - sideFills (fills t₁) b : ℕ) : ℤ) =
        (sideFills (fills t) b : ℤ) - sideFills (fills t₁) b := by
      push_cast [h2]; ring
    have : ((t - t₁ : ℕ) : ℤ) ≤
        4 * ((sideFills (fills t) b - sideFills (fills t₁) b : ℕ) : ℤ) + 6 := by
      exact_mod_cast this
    push_cast [h] at this
    linarith
  have hn' : (1 : ℤ) ≤ S.n := by exact_mod_cast hn
  nlinarith

/-! ## D9.8.15 The union over chains -/

/-- D9.8.13. The time window `4 n (2 r₀ ℓ + 3)` of a chain of `ℓ` charges. -/
def W (ℓ : ℕ) : ℕ := 4 * S.n * (2 * S.r₀ * ℓ + 3)

/-- D9.8.14. The decreasing lists of `ℓ` charge times in the window before round `t`. -/
noncomputable def TL (t ℓ : ℕ) : Finset (List ℕ) :=
  (powersetCard ℓ ((Ico (t - S.W ℓ) t).filter fun s => s % 2 = 1)).image
    fun T => T.sort (· ≥ ·)

/-- D9.8.15. The possible bad sites of band `g` (initially in the middle of band `g`). -/
noncomputable def Eg (g : Fin S.K) : Finset S.Λ :=
  univ.filter fun x => 8 * g * S.m + S.m < S.dep x ∧ S.dep x ≤ 8 * g * S.m + 6 * S.m

/-- D9.8.13. The chain lengths beating the lead `D/2`. -/
def Lset : Finset ℕ := (range (S.T + 1)).filter fun ℓ => S.D / 2 < 2 * S.r₀ * ℓ

/-- D9.8.14. The history `h` realizes the chain of charge times `ts` and terms `Ys` in band `g`
on side `b`. -/
def Ev (t : ℕ) (g : Fin S.K) (b : Bool) (h : S.Hist t) (ts : List ℕ) (Ys : List S.Term) :
    Prop :=
  ∀ p ∈ ts.zip Ys, S.Sel g (S.offset t h g) p.1 (S.chVal t h p.1 g) b p.2

open Classical in
/-- D9.8.14. A prescribed chain of `ℓ` charges has probability `≤ (2M)^{-ℓ}`. -/
theorem prob_chain (t : ℕ) (g : Fin S.K) (b : Bool) (x : S.Λ) (ℓ : ℕ) {ts : List ℕ}
    (hts : ts ∈ S.TL t ℓ) {Ys : List S.Term} (hYs : Ys ∈ S.LL x ℓ) :
    ∑ h, (S.histTree t).weight h * ind (S.Ev t g b h ts Ys) ≤ (1 / (2 * S.M)) ^ ℓ := by
  rw [TL, mem_image] at hts
  obtain ⟨T, hT, rfl⟩ := hts
  rw [mem_powersetCard] at hT
  have hnd := Finset.sort_nodup T (· ≥ ·)
  have hlen : (T.sort (· ≥ ·)).length = Ys.length := by
    rw [Finset.length_sort, S.length_of_mem_LL hYs, hT.2]
  have hP : ∀ s r v v', v < 2 * S.M → v' < 2 * S.M →
      (∃ Y, (s, Y) ∈ (T.sort (· ≥ ·)).zip Ys ∧ S.Sel g r s v b Y) →
      (∃ Y, (s, Y) ∈ (T.sort (· ≥ ·)).zip Ys ∧ S.Sel g r s v' b Y) → v = v' := by
    rintro s r v v' - - ⟨Y, hY, hS⟩ ⟨Y', hY', hS'⟩
    rw [List.zip_fun hnd hY hY'] at hS
    exact S.Sel_unique hS hS'
  have hTs : ∀ s ∈ T, s < t ∧ s % 2 = 1 := by
    intro s hs
    have := hT.1 hs
    rw [mem_filter, mem_Ico] at this
    exact ⟨this.1.2, this.2⟩
  have h1 := S.prob_sel g (fun s r v => ∃ Y, (s, Y) ∈ (T.sort (· ≥ ·)).zip Ys ∧
    S.Sel g r s v b Y) hP t T hTs
  rw [hT.2] at h1
  refine le_trans (sum_le_sum fun h _ => mul_le_mul_of_nonneg_left ?_
    (MeanTree.weight_nonneg _ h)) h1
  by_cases hev : S.Ev t g b h (T.sort (· ≥ ·)) Ys
  · rw [ind_pos hev]
    refine le_of_eq (prod_eq_one fun s hs => ind_pos ?_).symm
    have hs' : s ∈ T.sort (· ≥ ·) := (Finset.mem_sort _).2 hs
    obtain ⟨Y, hY⟩ := List.exists_mem_zip hlen hs'
    exact ⟨Y, hY, hev _ hY⟩
  · rw [ind_neg hev]
    exact prod_nonneg fun s _ => ind_nonneg _

section Union

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

/-- D9.8.12, D9.8.13. A history with a site of side `b` of band `g` beyond the front plus
`D/2` realizes a chain of `ℓ` charges, `D/2 < 2 r₀ ℓ`, in the time window of `ℓ`. -/
theorem Hyp.exists_chain (t : Fin S.T) (g : Fin S.K) (b : Bool) (h : S.Hist t)
    (hb : ∃ x : S.Λ, x.1 ∈ S.A ∧ S.stateAt t h g x = some b ∧
      S.front g (S.offset t h g) t b + (S.D / 2 : ℕ) < S.odep b x) :
    ∃ x ∈ S.Eg g, ∃ ℓ ∈ S.Lset, ∃ ts ∈ S.TL t ℓ, ∃ Ys ∈ S.LL x ℓ, S.Ev t g b h ts Ys := by
  have hT := t.2
  have hn := H.n_pos
  obtain ⟨x, hA, hst, hbad⟩ := hb
  have hinit : S.init g (S.offset t h g) x = none := by
    rcases hi : S.init g (S.offset t h g) x with _ | b'
    · rfl
    · have h1 := S.stateAt_of_init h g hi
      rw [hst] at h1
      cases h1
      have h2 := S.odep_init_lt hi hA
      have h3 := S.front_mono g (S.offset t h g) (Nat.zero_le t) b
      omega
  obtain ⟨-, hlo, hhi⟩ := S.init_eq_none hinit
  have hr := (S.offset t h g).2
  obtain ⟨ts, Ys, t₁, hl, hLL, ht₁, hsort, hts, hsel, hdep⟩ := H.chain t h g b x hst hA
  have hmono := S.front_mono g (S.offset t h g) ht₁ b
  have hgap := S.front_gap g (S.offset t h g) ht₁ b hn
  have hlen : S.D / 2 < 2 * S.r₀ * Ys.length := by
    have : ((S.D / 2 : ℕ) : ℤ) < 2 * S.r₀ * Ys.length := by linarith
    exact_mod_cast this
  have hnd : ts.Nodup := hsort.imp ne_of_gt
  have hsub : ts.toFinset ⊆ (Ico (t - S.W Ys.length) t).filter fun s => s % 2 = 1 := by
    intro s hs
    rw [List.mem_toFinset] at hs
    obtain ⟨h1, h2, h3⟩ := hts s hs
    have hW : (t : ℤ) - t₁ < S.W Ys.length := by
      unfold W
      push_cast
      have : S.front g (S.offset t h g) t b - S.front g (S.offset t h g) t₁ b <
          2 * S.r₀ * Ys.length := by linarith
      nlinarith
    rw [mem_filter, mem_Ico]
    refine ⟨⟨?_, h2⟩, h3⟩
    omega
  have hcard : #ts.toFinset = Ys.length := by rw [List.toFinset_card_of_nodup hnd, hl]
  refine ⟨x, ?_, Ys.length, ?_, ts, ?_, Ys, hLL, hsel⟩
  · simp only [Eg, mem_filter, mem_univ, true_and]
    simp only [lo, hi] at hlo hhi
    omega
  · rw [Lset, mem_filter, mem_range]
    refine ⟨?_, hlen⟩
    have h1 : #ts.toFinset ≤ t := (card_le_card (hsub.trans (filter_subset _ _))).trans
      (by rw [Nat.card_Ico]; omega)
    omega
  · rw [TL, mem_image]
    exact ⟨ts.toFinset, mem_powersetCard.2 ⟨hsub, hcard⟩,
      (List.toFinset_sort (· ≥ ·) hnd).2 (hsort.imp le_of_lt)⟩

open Classical in
/-- D9.8.12–14. The weight of the histories with a site of side `b` of band `g` beyond the front
plus `D/2` is at most the sum over chains of their probabilities. -/
theorem Hyp.bad_le (t : Fin S.T) (g : Fin S.K) (b : Bool) :
    ∑ h ∈ univ.filter (fun h : S.Hist t => ∃ x : S.Λ, x.1 ∈ S.A ∧ S.stateAt t h g x = some b ∧
        S.front g (S.offset t h g) t b + (S.D / 2 : ℕ) < S.odep b x), (S.histTree t).weight h ≤
      ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, (#(S.TL t ℓ) : ℝ) * #(S.LL x ℓ) * (1 / (2 * S.M)) ^ ℓ := by
  have hw0 : ∀ h, 0 ≤ (S.histTree t).weight h := fun h => MeanTree.weight_nonneg _ _
  calc ∑ h ∈ univ.filter (fun h : S.Hist t => ∃ x : S.Λ, x.1 ∈ S.A ∧
          S.stateAt t h g x = some b ∧ S.front g (S.offset t h g) t b + (S.D / 2 : ℕ) <
            S.odep b x), (S.histTree t).weight h
      ≤ ∑ h, (S.histTree t).weight h * ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, ∑ ts ∈ S.TL t ℓ,
          ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys) := by
        rw [sum_filter]
        refine sum_le_sum fun h _ => ?_
        have hnn : 0 ≤ ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, ∑ ts ∈ S.TL t ℓ,
            ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys) :=
          sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
            sum_nonneg fun _ _ => ind_nonneg _
        split_ifs with hb
        · obtain ⟨x, hx, ℓ, hℓ, ts, hts, Ys, hYs, hev⟩ := H.exists_chain t g b h hb
          have h1 : (1 : ℝ) ≤ ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, ∑ ts ∈ S.TL t ℓ,
              ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys) := by
            calc (1 : ℝ) = ind (S.Ev t g b h ts Ys) := (ind_pos hev).symm
              _ ≤ ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys) :=
                  single_le_sum (f := fun Ys => ind (S.Ev t g b h ts Ys))
                    (fun _ _ => ind_nonneg _) hYs
              _ ≤ ∑ ts ∈ S.TL t ℓ, ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys) :=
                  single_le_sum (f := fun ts => ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys))
                    (fun _ _ => sum_nonneg fun _ _ => ind_nonneg _) hts
              _ ≤ ∑ ℓ ∈ S.Lset, ∑ ts ∈ S.TL t ℓ, ∑ Ys ∈ S.LL x ℓ,
                    ind (S.Ev t g b h ts Ys) :=
                  single_le_sum (f := fun ℓ => ∑ ts ∈ S.TL t ℓ, ∑ Ys ∈ S.LL x ℓ,
                    ind (S.Ev t g b h ts Ys))
                    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => ind_nonneg _) hℓ
              _ ≤ _ :=
                  single_le_sum (f := fun x => ∑ ℓ ∈ S.Lset, ∑ ts ∈ S.TL t ℓ,
                    ∑ Ys ∈ S.LL x ℓ, ind (S.Ev t g b h ts Ys))
                    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg
                      fun _ _ => ind_nonneg _) hx
          nlinarith [hw0 h]
        · exact mul_nonneg (hw0 h) hnn
    _ = ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, ∑ ts ∈ S.TL t ℓ, ∑ Ys ∈ S.LL x ℓ,
          ∑ h, (S.histTree t).weight h * ind (S.Ev t g b h ts Ys) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ℓ _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ts _ => ?_
        rw [sum_comm]
    _ ≤ ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, ∑ _ts ∈ S.TL t ℓ, ∑ _Ys ∈ S.LL x ℓ,
          (1 / (2 * S.M) : ℝ) ^ ℓ :=
        sum_le_sum fun x _ => sum_le_sum fun ℓ _ => sum_le_sum fun ts hts =>
          sum_le_sum fun Ys hYs => S.prob_chain t g b x ℓ hts hYs
    _ = ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, (#(S.TL t ℓ) : ℝ) * #(S.LL x ℓ) *
          (1 / (2 * S.M)) ^ ℓ := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun ℓ _ => ?_
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring

omit [DecidableRel S.G.Adj] H in
/-- `C(W, ℓ) ≤ (e W / ℓ)^ℓ`. -/
theorem choose_le_pow (W ℓ : ℕ) (hℓ : 0 < ℓ) :
    (W.choose ℓ : ℝ) ≤ (Real.exp 1 * W / ℓ) ^ ℓ := by
  have h1 := Nat.choose_le_pow_div (α := ℝ) ℓ W
  have h2 := Real.pow_div_factorial_le_exp (ℓ : ℝ) (Nat.cast_nonneg _) ℓ
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hf : (0 : ℝ) < ℓ.factorial := by exact_mod_cast Nat.factorial_pos ℓ
  calc (W.choose ℓ : ℝ) ≤ (W : ℝ) ^ ℓ / ℓ.factorial := h1
    _ = ((W : ℝ) / ℓ) ^ ℓ * ((ℓ : ℝ) ^ ℓ / ℓ.factorial) := by
        rw [div_pow]; field_simp
    _ ≤ ((W : ℝ) / ℓ) ^ ℓ * Real.exp ℓ := by gcongr
    _ = (Real.exp 1 * W / ℓ) ^ ℓ := by
        rw [← Real.exp_one_pow, ← mul_pow]
        ring

open Classical in
/-- D9.8.15. The weight of the old histories of round `t` that are not good is at most
`2 K · 5 m n · (2nm + 1) · ρ^{⌊D/2⌋ / (2 r₀ + 1)}`, `ρ = e · 4 n (2 r₀ + 3) · μ_R V(r₀)² / (2M)`
(for `ρ ≤ 1`). -/
theorem Hyp.tail_le (t : Fin S.T)
    (hρ : Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3)) * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) /
      (2 * S.M) ≤ 1) :
    ∑ h ∈ univ.filter (fun h => ¬ S.Good t h), (S.histTree t).weight h ≤
      2 * S.K * (5 * S.m * S.n) * (S.T + 1) *
        (Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3)) * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) /
          (2 * S.M)) ^ ((S.D / 2) / (2 * S.r₀ + 1)) := by
  set ρ := Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3)) * (AreaLaw.μ V S.R * V S.r₀ * V S.r₀) /
    (2 * S.M) with hρdef
  have hM : (0 : ℝ) < 2 * S.M := by have := S.M_pos; positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hw0 : ∀ h, 0 ≤ (S.histTree t).weight h := fun h => MeanTree.weight_nonneg _ _
  let Bad : Fin S.K → Bool → S.Hist t → Prop := fun g b h => ∃ x : S.Λ, x.1 ∈ S.A ∧
    S.stateAt t h g x = some b ∧ S.front g (S.offset t h g) t b + (S.D / 2 : ℕ) < S.odep b x
  -- a not-good history is bad in some band and side
  have hnot : ∀ h, ¬ S.Good t h → ∃ g b, Bad g b h := by
    intro h hh
    simp only [Good, not_forall, not_le, exists_prop] at hh
    obtain ⟨g, b, x, hx, hA, hlt⟩ := hh
    exact ⟨g, b, x, hA, hx, hlt⟩
  -- each term of the union over chains is `≤ ρ^ℓ ≤ ρ^{ℓ₀}`
  have hterm : ∀ (x : S.Λ), ∀ ℓ ∈ S.Lset,
      (#(S.TL t ℓ) : ℝ) * #(S.LL x ℓ) * (1 / (2 * S.M)) ^ ℓ ≤
        ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) := by
    intro x ℓ hℓ
    rw [Lset, mem_filter, mem_range] at hℓ
    have hℓ1 : 0 < ℓ := by
      rcases Nat.eq_zero_or_pos ℓ with h0 | h0
      · rw [h0] at hℓ; omega
      · exact h0
    have hℓ0 : (S.D / 2) / (2 * S.r₀ + 1) ≤ ℓ := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      nlinarith [hℓ.2]
    have hTL : (#(S.TL t ℓ) : ℝ) ≤ (Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3))) ^ ℓ := by
      have h1 : #(S.TL t ℓ) ≤ (S.W ℓ).choose ℓ := by
        refine card_image_le.trans ?_
        rw [card_powersetCard]
        apply Nat.choose_le_choose
        refine (card_filter_le _ _).trans ?_
        rw [Nat.card_Ico]
        omega
      have h2 := choose_le_pow (S.W ℓ) ℓ hℓ1
      have h3 : Real.exp 1 * (S.W ℓ : ℝ) / ℓ ≤ Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3)) := by
        rw [div_le_iff₀ (by exact_mod_cast hℓ1)]
        unfold W
        push_cast
        have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
        have he : 0 < Real.exp 1 := Real.exp_pos 1
        nlinarith [mul_pos he (show (0 : ℝ) < 4 * S.n by have := H.n_pos; positivity)]
      calc (#(S.TL t ℓ) : ℝ) ≤ ((S.W ℓ).choose ℓ : ℝ) := by exact_mod_cast h1
        _ ≤ (Real.exp 1 * S.W ℓ / ℓ) ^ ℓ := h2
        _ ≤ (Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3))) ^ ℓ :=
            pow_le_pow_left₀ (by positivity) h3 ℓ
    have hLL : (#(S.LL x ℓ) : ℝ) ≤ (AreaLaw.μ V S.R * V S.r₀ * V S.r₀ : ℕ) ^ ℓ := by
      exact_mod_cast H.card_LL x ℓ
    calc (#(S.TL t ℓ) : ℝ) * #(S.LL x ℓ) * (1 / (2 * S.M)) ^ ℓ
        ≤ (Real.exp 1 * (4 * S.n * (2 * S.r₀ + 3))) ^ ℓ *
            (AreaLaw.μ V S.R * V S.r₀ * V S.r₀ : ℕ) ^ ℓ * (1 / (2 * S.M)) ^ ℓ := by
          gcongr
      _ = ρ ^ ℓ := by
          rw [hρdef, ← mul_pow, ← mul_pow]
          congr 1
          push_cast
          ring
      _ ≤ ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) := pow_le_pow_of_le_one hρ0 hρ hℓ0
  have hbad : ∀ g b, ∑ h ∈ univ.filter (Bad g b), (S.histTree t).weight h ≤
      (5 * S.m * S.n) * (S.T + 1) * ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) := by
    intro g b
    refine (H.bad_le t g b).trans ?_
    have hEg : #(S.Eg g) ≤ 5 * S.m * S.n := by
      have hm := S.m_pos
      have h1 : 8 * ((g : ℕ) + 1) * S.m ≤ 8 * S.K * S.m :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ g.2)
      have h2 : 8 * ((g : ℕ) + 1) * S.m = 8 * g * S.m + 8 * S.m := by ring
      have h3 := H.KL
      have := H.card_window (j₀ := 8 * g * S.m + S.m + 1) (c := 5 * S.m - 1) (by omega)
        (by omega)
      refine (card_le_card fun x hx => ?_).trans (this.trans (by
        rw [show 5 * S.m - 1 + 1 = 5 * S.m by omega]))
      simp only [Eg, mem_filter, mem_univ, true_and] at hx ⊢
      omega
    have hL : #S.Lset ≤ S.T + 1 := (card_filter_le _ _).trans (by rw [card_range])
    have hEg' : (#(S.Eg g) : ℝ) ≤ (5 * S.m * S.n : ℕ) := by exact_mod_cast hEg
    have hL' : (#S.Lset : ℝ) ≤ (S.T + 1 : ℕ) := by exact_mod_cast hL
    calc ∑ x ∈ S.Eg g, ∑ ℓ ∈ S.Lset, (#(S.TL t ℓ) : ℝ) * #(S.LL x ℓ) * (1 / (2 * S.M)) ^ ℓ
        ≤ ∑ _x ∈ S.Eg g, ∑ _ℓ ∈ S.Lset, ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) :=
          sum_le_sum fun x _ => sum_le_sum fun ℓ hℓ => hterm x ℓ hℓ
      _ = #(S.Eg g) * (#S.Lset * ρ ^ ((S.D / 2) / (2 * S.r₀ + 1))) := by
          rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ (5 * S.m * S.n : ℕ) * ((S.T + 1 : ℕ) * ρ ^ ((S.D / 2) / (2 * S.r₀ + 1))) := by
          gcongr
      _ = (5 * S.m * S.n) * (S.T + 1) * ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) := by
          push_cast; ring
  calc ∑ h ∈ univ.filter (fun h => ¬ S.Good t h), (S.histTree t).weight h
      ≤ ∑ h, (S.histTree t).weight h * ∑ g : Fin S.K, ∑ b : Bool, ind (Bad g b h) := by
        rw [sum_filter]
        refine sum_le_sum fun h _ => ?_
        by_cases hh : S.Good t h
        · rw [if_neg (not_not.2 hh)]
          exact mul_nonneg (hw0 h) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => ind_nonneg _)
        · rw [if_pos hh]
          obtain ⟨g, b, hgb⟩ := hnot h hh
          have h1 : (1 : ℝ) ≤ ∑ g : Fin S.K, ∑ b : Bool, ind (Bad g b h) :=
            calc (1 : ℝ) = ind (Bad g b h) := (ind_pos hgb).symm
              _ ≤ ∑ b' : Bool, ind (Bad g b' h) :=
                  single_le_sum (f := fun b' => ind (Bad g b' h)) (fun _ _ => ind_nonneg _)
                    (mem_univ b)
              _ ≤ _ := single_le_sum (f := fun g' => ∑ b' : Bool, ind (Bad g' b' h))
                  (fun _ _ => sum_nonneg fun _ _ => ind_nonneg _) (mem_univ g)
          nlinarith [hw0 h]
    _ = ∑ g : Fin S.K, ∑ b : Bool, ∑ h ∈ univ.filter (Bad g b), (S.histTree t).weight h := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun g _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun b _ => ?_
        rw [sum_filter]
        refine sum_congr rfl fun h _ => ?_
        unfold ind
        split_ifs <;> ring
    _ ≤ ∑ _g : Fin S.K, ∑ _b : Bool,
          (5 * S.m * S.n) * (S.T + 1) * ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) :=
        sum_le_sum fun g _ => sum_le_sum fun b _ => hbad g b
    _ = 2 * S.K * (5 * S.m * S.n) * (S.T + 1) * ρ ^ ((S.D / 2) / (2 * S.r₀ + 1)) := by
        rw [sum_const, sum_const, card_univ, card_univ, Fintype.card_bool, Fintype.card_fin,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

end Union

end Scan

end AreaLaw.Scanner
