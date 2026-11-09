import AreaLaw.S09_Scanner.Histories.Geometry

/-!
# §9.1 Lemma 9.1 (3), (4): dilution by offsets and availability (D9.8.11, D9.8.16)

Digest `digest/09-scanner.md` D9.8.11, D9.8.16, paper `paper/sections/08-scanner.tex` 300–338.
The classical path probabilities of the history tree: uniform offsets and uniform independent
choices. Graph-level (Map.md, Dimension: `any d`).
-/

open scoped Matrix
open Finset Arealaw

namespace AreaLaw.Scanner

universe u

open Transport (MeanTree)
open Comparators (physReg Site)

namespace Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ)

/-! ## Classical path probabilities of the history tree -/

/-- The functions `Fin K → Fin m` with a prescribed value at `g` are `m^{K-1}` of `m^K`. -/
theorem card_filter_apply_eq {K m : ℕ} (g : Fin K) (a : Fin m) :
    #(univ.filter fun r : Fin K → Fin m => r g = a) * m = m ^ K := by
  have e : {r : Fin K → Fin m // r g = a} ≃ ({i // i ≠ g} → Fin m) :=
    { toFun := fun r i => r.1 i
      invFun := fun r' => ⟨fun i => if h : i = g then a else r' ⟨i, h⟩, by simp⟩
      left_inv := fun r => by
        ext i
        by_cases h : i = g
        · subst h; simp [r.2]
        · simp [h]
      right_inv := fun r' => by
        funext i
        simp [i.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  have : Fintype.card {i // i ≠ g} = K - 1 := by simp
  rw [this, ← pow_succ]
  congr 1
  have := g.2
  omega

/-- The uniform weight of a coordinate value: `∑_r w_r φ(r_g) = m⁻¹ ∑_a φ(a)`. -/
theorem sum_uniform_apply {K m : ℕ} [Nonempty (Fin K → Fin m)] (hm : 0 < m) (g : Fin K)
    (φ : Fin m → ℝ) :
    ∑ r : Fin K → Fin m, (uniformTree (Fin K → Fin m)).weight r * φ (r g) =
      (∑ a, φ a) / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp_rw [weight_uniformTree, Fintype.card_fun, Fintype.card_fin]
  rw [← Finset.mul_sum, ← sum_fiberwise univ (fun r : Fin K → Fin m => r g) (fun r => φ (r g))]
  have h1 : ∀ a : Fin m, ∑ r ∈ univ.filter (fun r : Fin K → Fin m => r g = a), φ (r g) =
      #(univ.filter fun r : Fin K → Fin m => r g = a) * φ a := by
    intro a
    rw [sum_congr rfl fun r hr => by rw [(mem_filter.1 hr).2], sum_const, nsmul_eq_mul]
  have h2 : ∀ a : Fin m, (#(univ.filter fun r : Fin K → Fin m => r g = a) : ℝ) =
      (m : ℝ) ^ K / m := by
    intro a
    rw [eq_div_iff hm']
    exact_mod_cast card_filter_apply_eq g a
  simp_rw [h1, h2, ← Finset.mul_sum]
  push_cast
  field_simp

theorem sum_histTree_succ (t : ℕ) (F : S.Hist (t + 1) → ℝ) :
    ∑ h', (S.histTree (t + 1)).weight h' * F h' =
      ∑ h, (S.histTree t).weight h * ∑ c, (uniformTree (S.Ch t)).weight c * F (S.ext t h c) := by
  change ∑ p : S.Hist t × S.Ch t, (S.histTree (t + 1)).weight (S.ext t p.1 p.2) *
    F (S.ext t p.1 p.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [weight_histTree_ext, Finset.mul_sum, mul_assoc]

/-- D9.7. The history tree samples every offset uniformly: `∑_h w_h φ(r_g(h)) = m⁻¹ ∑_a φ(a)`. -/
theorem sum_histTree_offset : ∀ (t : ℕ) (g : Fin S.K) (φ : Fin S.m → ℝ),
    ∑ h, (S.histTree t).weight h * φ (S.offset t h g) = (∑ a, φ a) / S.m
  | 0, g, φ => by
    have : Nonempty (Fin S.m) := ⟨⟨0, S.m_pos⟩⟩
    change ∑ r : Fin S.K → Fin S.m, (uniformTree (Fin S.K → Fin S.m)).weight r * φ (r g) = _
    exact sum_uniform_apply S.m_pos g φ
  | t + 1, g, φ => by
    rw [S.sum_histTree_succ]
    simp_rw [offset_ext, ← Finset.sum_mul, MeanTree.sum_weight, one_mul]
    exact sum_histTree_offset t g φ

/-- D7.9 (`transport:terminal-weights`). Summing the terminal weights over the old and new leaves
of a history gives its weight. -/
theorem sum_tree_leaf (t : Fin S.T) (p : unitInterval) (F : S.Hist t → ℝ) :
    ∑ j : Transport.Round.Leaf (S.Hist t) (fun _ => S.Ch t), ((S.round t).tree p).weight j *
      F j.1 = ∑ h, (S.histTree t).weight h * F h := by
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_option, (S.round t).weight_tree_old]
  simp_rw [(S.round t).weight_tree_new]
  have h1 : ∑ c : S.Ch t, (p : ℝ) * (S.round t).histTree.weight h *
      ((S.round t).choiceTree h).weight c * F h =
      (p : ℝ) * (S.round t).histTree.weight h * F h *
        ∑ c : S.Ch t, ((S.round t).choiceTree h).weight c := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun c _ => by ring
  rw [h1, MeanTree.sum_weight]
  change (1 - (p : ℝ)) * (S.histTree t).weight h * F h +
    (p : ℝ) * (S.histTree t).weight h * F h * 1 = _
  ring

/-! ## D9.8.11 Dilution by offsets (item 3) -/

theorem front_succ_le (g r t : ℕ) (b : Bool) : S.front g r (t + 1) b ≤ S.front g r t b + 1 := by
  have h1 : sideFills (fills (t + 1)) b ≤ sideFills (fills t) b + 1 := by
    unfold sideFills fills; split_ifs <;> omega
  have h2 : sideFills (fills (t + 1)) b / S.n ≤ sideFills (fills t) b / S.n + 1 := by
    rcases Nat.eq_zero_or_pos S.n with hn | hn
    · simp [hn]
    · calc sideFills (fills (t + 1)) b / S.n ≤ (sideFills (fills t) b + S.n) / S.n :=
            Nat.div_le_div_right (by omega)
        _ = sideFills (fills t) b / S.n + 1 := Nat.add_div_right _ hn
  cases b
  · rw [front_false, front_false]; push_cast; omega
  · rw [front_true, front_true]; omega

/-- D9.8.11. For fixed `t`, `b`, `d` the offsets `a` of band `g` putting the oriented depth `d`
in the window `[j - r₀, j + D + 2 r₀ + 1]` form an interval of `≤ D + 3 r₀ + 2` values. -/
theorem card_offsets (g : Fin S.K) (t : ℕ) (b : Bool) (d : ℤ) :
    #(univ.filter fun a : Fin S.m => S.front g a t b - S.r₀ ≤ d ∧
      d ≤ S.front g a t b + S.D + 2 * S.r₀ + 1) ≤ S.D + 3 * S.r₀ + 2 := by
  obtain ⟨q, hq⟩ : ∃ q, sideFills (fills t) b / S.n = q := ⟨_, rfl⟩
  cases b
  · refine (card_le_card_of_injOn (fun a : Fin S.m => (a : ℤ))
      (t := Icc (d - S.D - 2 * S.r₀ - 1 - (8 * g * S.m + S.m + 1 + q))
        (d + S.r₀ - (8 * g * S.m + S.m + 1 + q))) ?_ ?_).trans ?_
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, front_false, lo, hq] at ha
      simp only [coe_Icc, Set.mem_Icc]
      push_cast at ha
      constructor <;> linarith [ha.1, ha.2]
    · intro a _ a' _ h
      exact Fin.ext (by exact_mod_cast (show ((a : ℕ) : ℤ) = (a' : ℕ) from h))
    · rw [Int.card_Icc]
      omega
  · refine (card_le_card_of_injOn (fun a : Fin S.m => (a : ℤ))
      (t := Icc (-d - (8 * g * S.m + 5 * S.m) + q - S.r₀) (-d - (8 * g * S.m + 5 * S.m) + q + S.D
        + 2 * S.r₀ + 1)) ?_ ?_).trans ?_
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, front_true, hi, hq] at ha
      simp only [coe_Icc, Set.mem_Icc]
      push_cast at ha
      constructor <;> linarith [ha.1, ha.2]
    · intro a _ a' _ h
      exact Fin.ext (by exact_mod_cast (show ((a : ℕ) : ℤ) = (a' : ℕ) from h))
    · rw [Int.card_Icc]
      omega

section Dilution

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

/-- D9.8.11. The windows of distinct bands are disjoint: an oriented anchor depth in the window
of band `g` (for any offset) determines `g = ⌊dep / 8m⌋`. -/
theorem Hyp.band_of_window {t : ℕ} (ht : t ≤ S.T) {g : Fin S.K} {b : Bool} {a : Fin S.m}
    {x : σ} (hc : S.front g a t b - S.r₀ ≤ S.odep b x ∧
      S.odep b x ≤ S.front g a t b + S.D + 2 * S.r₀ + 1) :
    (g : ℕ) = S.dep x / (8 * S.m) := by
  have hm := H.m_ge
  have ha := a.2
  have hdiv := S.sideFills_div_le ht b
  obtain ⟨q, hq⟩ : ∃ q, sideFills (fills t) b / S.n = q := ⟨_, rfl⟩
  rw [hq] at hdiv
  have key : 8 * g * S.m ≤ S.dep x ∧ S.dep x < 8 * g * S.m + 8 * S.m := by
    cases b
    · simp only [front_false, lo, odep_false, hq] at hc
      push_cast at hc
      constructor
      · have : (8 * g * S.m : ℤ) ≤ S.dep x := by linarith [hc.1]
        exact_mod_cast this
      · have : (S.dep x : ℤ) < 8 * g * S.m + 8 * S.m := by
          have : (S.D : ℤ) + 2 * S.r₀ + 1 + S.m + 1 + q < 6 * S.m := by
            have h1 : (q : ℤ) ≤ S.m := by exact_mod_cast hdiv
            have h2 : 4 * ((S.D : ℤ) + S.r₀ + 1) ≤ S.m := by exact_mod_cast hm
            have h3 : (a : ℤ) < S.m := by exact_mod_cast ha
            nlinarith
          linarith [hc.2]
        exact_mod_cast this
    · simp only [front_true, hi, odep_true, hq] at hc
      push_cast at hc
      have h1 : (q : ℤ) ≤ S.m := by exact_mod_cast hdiv
      have h2 : 4 * ((S.D : ℤ) + S.r₀ + 1) ≤ S.m := by exact_mod_cast hm
      have h3 : (a : ℤ) < S.m := by exact_mod_cast ha
      have h4 : (0 : ℤ) ≤ a := by positivity
      constructor
      · have : (8 * g * S.m : ℤ) ≤ S.dep x := by linarith [hc.2]
        exact_mod_cast this
      · have : (S.dep x : ℤ) < 8 * g * S.m + 8 * S.m := by linarith [hc.1]
        exact_mod_cast this
  have hm0 : 0 < 8 * S.m := by have := S.m_pos; omega
  symm
  apply Nat.div_eq_of_lt_le
  · linarith [key.1]
  · nlinarith [key.2]

open Classical in
/-- **Lemma 9.1 (3)** (D9.8.11). -/
theorem Hyp.item3 : S.Item3 (C₂ V S.R) := by
  intro t nl E hE i p
  have hT := t.2
  -- the split event is confined to an event about the offset of one band
  have key : ∀ j ∈ (S.round t).splitLeaves E i, ∃ g : Fin S.K, ∃ b : Bool,
      S.front g (S.offset t j.1 g) t b - S.r₀ ≤ S.odep b (S.a i) ∧
        S.odep b (S.a i) ≤ S.front g (S.offset t j.1 g) t b + S.D + 2 * S.r₀ + 1 := by
    intro j hj
    simp only [Transport.Round.splitLeaves, mem_filter, mem_univ, true_and] at hj
    obtain ⟨g, hg⟩ := hj
    refine ⟨g, ?_⟩
    rw [hE i, S.round_leafPart, S.part_contains, S.leafState_X_union_U] at hg
    obtain ⟨h, _ | c⟩ := j
    · obtain ⟨b, hb⟩ := H.split_anchor hT.le h g i hg
      exact ⟨b, hb.1, by linarith [hb.2]⟩
    · obtain ⟨b, hb⟩ := H.split_anchor (t := t.1 + 1) hT (S.ext t h c) g i hg
      have h1 := S.front_mono g (S.offset t h g) (by omega : t.1 ≤ t.1 + 1) b
      have h2 := S.front_succ_le g (S.offset t h g) t b
      rw [offset_ext] at hb
      exact ⟨b, by dsimp only; linarith [hb.1], by dsimp only; linarith [hb.2]⟩
  set Gs : Finset (Fin S.K) := univ.filter fun g => (g : ℕ) = S.dep (S.a i) / (8 * S.m)
  have hGs : #Gs ≤ 1 := card_le_one.2 fun g hg g' hg' => Fin.ext (by
    simp only [Gs, mem_filter, mem_univ, true_and] at hg hg'
    omega)
  have hw0 : ∀ j, 0 ≤ ((S.round t).tree p).weight j := fun j => MeanTree.weight_nonneg _ _
  have hm0 : (0 : ℝ) < S.m := by exact_mod_cast S.m_pos
  let ind : Fin S.K → Bool → ℕ → ℝ := fun g b a =>
    if S.front g a t b - S.r₀ ≤ S.odep b (S.a i) ∧
      S.odep b (S.a i) ≤ S.front g a t b + S.D + 2 * S.r₀ + 1 then 1 else 0
  have hind0 : ∀ g b a, 0 ≤ ind g b a := fun g b a => by
    simp only [ind]; split_ifs <;> norm_num
  calc (S.round t).splitWeight E i p
      = ∑ j ∈ (S.round t).splitLeaves E i, ((S.round t).tree p).weight j := rfl
    _ ≤ ∑ j ∈ (S.round t).splitLeaves E i, ((S.round t).tree p).weight j *
          ∑ g ∈ Gs, ∑ b, ind g b (S.offset t j.1 g) := by
        refine sum_le_sum fun j hj => ?_
        obtain ⟨g, b, hc⟩ := key j hj
        have hg : g ∈ Gs := by
          simp only [Gs, mem_filter, mem_univ, true_and]
          exact H.band_of_window hT.le hc
        have h1 : ind g b (S.offset t j.1 g) = 1 := by simp only [ind]; rw [if_pos hc]
        have h2 : (1 : ℝ) ≤ ∑ g ∈ Gs, ∑ b, ind g b (S.offset t j.1 g) := by
          calc (1 : ℝ) = ind g b (S.offset t j.1 g) := h1.symm
            _ ≤ ∑ b', ind g b' (S.offset t j.1 g) :=
                single_le_sum (f := fun b' => ind g b' (S.offset t j.1 g))
                  (fun b' _ => hind0 _ _ _) (mem_univ b)
            _ ≤ ∑ g' ∈ Gs, ∑ b', ind g' b' (S.offset t j.1 g') :=
                single_le_sum (f := fun g' => ∑ b', ind g' b' (S.offset t j.1 g'))
                  (fun g' _ => sum_nonneg fun b' _ => hind0 _ _ _) hg
        nlinarith [hw0 j]
    _ ≤ ∑ j, ((S.round t).tree p).weight j * ∑ g ∈ Gs, ∑ b, ind g b (S.offset t j.1 g) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ =>
          mul_nonneg (hw0 j) (sum_nonneg fun g _ => sum_nonneg fun b _ => hind0 _ _ _)
    _ = ∑ g ∈ Gs, ∑ b, ∑ h, (S.histTree t).weight h * ind g b (S.offset t h g) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun g _ => ?_
        rw [Finset.sum_comm]
        refine sum_congr rfl fun b _ => ?_
        exact S.sum_tree_leaf t p (fun h => ind g b (S.offset t h g))
    _ = ∑ g ∈ Gs, ∑ b, (∑ a : Fin S.m, ind g b a) / S.m := by
        refine sum_congr rfl fun g _ => sum_congr rfl fun b _ => ?_
        exact S.sum_histTree_offset t g (fun a => ind g b a)
    _ ≤ ∑ g ∈ Gs, ∑ _b : Bool, ((S.D + 3 * S.r₀ + 2 : ℕ) : ℝ) / S.m := by
        refine sum_le_sum fun g _ => sum_le_sum fun b _ => ?_
        apply div_le_div_of_nonneg_right _ hm0.le
        simp only [ind]
        rw [Finset.sum_boole]
        exact_mod_cast S.card_offsets g t b (S.odep b (S.a i))
    _ ≤ C₂ V S.R * S.D / S.m := by
        rw [sum_const, sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul, nsmul_eq_mul]
        have hD := H.D_pos
        have hr := H.r₀_le
        have h1 : ((S.D + 3 * S.r₀ + 2 : ℕ) : ℝ) ≤ 4 * S.D := by
          exact_mod_cast (by omega : S.D + 3 * S.r₀ + 2 ≤ 4 * S.D)
        have h2 : (#Gs : ℝ) ≤ 1 := by exact_mod_cast hGs
        have hC := (C₂_ge V S.R).1
        have hD' : (0 : ℝ) ≤ S.D := Nat.cast_nonneg _
        have hinv : (0 : ℝ) ≤ (S.m : ℝ)⁻¹ := inv_nonneg.2 hm0.le
        simp only [div_eq_mul_inv]
        have hc0 : (0 : ℝ) ≤ ((S.D + 3 * S.r₀ + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
        have e1 : (#Gs : ℝ) * ((2 : ℕ) * (((S.D + 3 * S.r₀ + 2 : ℕ) : ℝ) * (S.m : ℝ)⁻¹)) ≤
            1 * ((2 : ℕ) * (((S.D + 3 * S.r₀ + 2 : ℕ) : ℝ) * (S.m : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
        have e2 : ((S.D + 3 * S.r₀ + 2 : ℕ) : ℝ) * (S.m : ℝ)⁻¹ ≤ 4 * S.D * (S.m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hinv
        have e3 : 8 * (S.D : ℝ) * (S.m : ℝ)⁻¹ ≤ C₂ V S.R * S.D * (S.m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hD') hinv
        push_cast at e1 e2 ⊢
        linarith

end Dilution

/-! ## D9.8.16 Availability (item 4) -/

theorem chargeList_nodup (g r t : ℕ) (b : Bool) : (S.chargeList g r t b).Nodup :=
  (Finset.nodup_toList _).filter _

theorem length_chargeList (g r t : ℕ) (b : Bool) :
    (S.chargeList g r t b).length = #(univ.filter fun i : S.Term =>
      S.front g r t b - S.r₀ ≤ S.odep b (S.a i) ∧ S.odep b (S.a i) ≤ S.front g r t b + S.D) := by
  rw [← List.toFinset_card_of_nodup (S.chargeList_nodup g r t b)]
  congr 1
  ext i
  simp [chargeList]

theorem c_of_odd {t : ℕ} (ht : t % 2 = 1) : S.c t = 2 * S.M := by
  simp [c, ht]

/-- A band coordinate of the uniform choice tree takes each value with weight `1/c`. -/
theorem sum_choice_apply (t : ℕ) (g : Fin S.K) (v : Fin (S.c t)) :
    ∑ c ∈ univ.filter (fun c : S.Ch t => c g = v), (uniformTree (S.Ch t)).weight c =
      1 / S.c t := by
  have hc : (S.c t : ℝ) ≠ 0 := by exact_mod_cast (S.c_pos t).ne'
  simp_rw [weight_uniformTree, Fintype.card_fun, Fintype.card_fin]
  rw [sum_const, nsmul_eq_mul]
  have h1 : (#(univ.filter fun c : S.Ch t => c g = v) : ℝ) * S.c t = (S.c t : ℝ) ^ S.K := by
    exact_mod_cast card_filter_apply_eq g v
  have h2 : (S.c t : ℝ) ^ S.K ≠ 0 := pow_ne_zero _ hc
  field_simp
  push_cast at h1 ⊢
  linarith [h1]

section Availability

variable [DecidableRel S.G.Adj] {S} {V : ℕ → ℕ} {CT : ℝ} (H : S.Hyp V CT)
include H

/-- D9.6. The charge lists fit into `M` slots: anchors at oriented depth `[j - r₀, j + D]`
occupy `D + r₀ + 1` rows of `≤ n` sites, each anchoring `≤ μ_R` terms. -/
theorem Hyp.length_chargeList_le {t : ℕ} (ht : t ≤ S.T) (h : S.Hist t) (g : Fin S.K)
    (b : Bool) : (S.chargeList g (S.offset t h g) t b).length ≤ S.M := by
  rw [length_chargeList]
  refine le_trans ?_ H.M_ge
  have hdiv := S.sideFills_div_le ht true
  have hdivP := S.sideFills_div_le ht false
  have hL := H.hi_add_le g (S.offset t h g)
  have hhi := S.hi_eq g (S.offset t h g)
  have hlo := S.lo_ge g (S.offset t h g)
  have hm := H.m_ge
  have e : AreaLaw.μ V S.R * ((S.D + S.r₀ + 1) * S.n) =
      AreaLaw.μ V S.R * (S.n * (S.D + S.r₀ + 1)) := by ring
  rw [← e]
  cases b
  · obtain ⟨q, hq⟩ : ∃ q, sideFills (fills t) false / S.n = q := ⟨_, rfl⟩
    rw [hq] at hdivP
    refine (card_le_card fun i hi => ?_).trans (H.card_terms_window
      (S.lo g (S.offset t h g) + 1 + q - S.r₀) (S.D + S.r₀) (by omega) (by omega))
    simp only [mem_filter, mem_univ, true_and, front_false, odep_false, hq] at hi ⊢
    push_cast at hi
    omega
  · obtain ⟨q, hq⟩ : ∃ q, sideFills (fills t) true / S.n = q := ⟨_, rfl⟩
    rw [hq] at hdiv
    refine (card_le_card fun i hi => ?_).trans (H.card_terms_window
      (S.hi g (S.offset t h g) - q - S.D) (S.D + S.r₀) (by omega) (by omega))
    simp only [mem_filter, mem_univ, true_and, front_true, odep_true, hq] at hi ⊢
    omega

/-- D9.8.16. On a good old history at a charge round, a term split in band `g` is in the charge
list of its splitting side, at a slot `v < 2M` that selects it. -/
theorem Hyp.exists_slot {t : Fin S.T} (h : S.Hist t) (hgood : S.Good t h) (g : Fin S.K)
    (i : S.Term) (hi : ¬ ((S.round t).old h g).Contains (physReg (S.Xt i))) :
    ∃ v : ℕ, v < 2 * S.M ∧
      (S.chargeList g (S.offset t h g) t (decide (S.M ≤ v)))[v % S.M]? = some i ∧
      (decide (S.M ≤ v) = false ↔ ((S.round t).old h g).SplitsToP (physReg (S.Xt i))) ∧
      (S.ball i ∩ side (S.stateAt t h g) (decide (S.M ≤ v))).Nonempty ∧
      (S.ball i ∩ middle (S.stateAt t h g)).Nonempty ∧ S.Xt i = S.ball i := by
  have hT := t.2
  rcases H.classify_leaf (⟨t, ⟨h, none⟩⟩ : S.St) g i with hc | ⟨hb, hA, hmid, hsp⟩
  · exact absurd hc hi
  change (S.Xt i ∩ middle (S.stateAt t h g)).Nonempty at hmid
  obtain ⟨y, hy⟩ := hmid
  rw [mem_inter, mem_middle] at hy
  obtain ⟨-, hmP, hmF⟩ := H.middle_bounds hT.le h g hy.2
  have hyb : y.1 ∈ GraphDomain.ball S.G S.Λ (S.a i) S.r₀ := by
    have := hy.1
    rw [hb] at this
    exact mem_subtype.1 this
  -- the splitting side `b`, a site `x` of the ball on it
  obtain ⟨b, hbP, x, hx⟩ : ∃ b : Bool, (b = false ↔ ((S.round t).old h g).SplitsToP
      (physReg (S.Xt i))) ∧ ∃ x ∈ S.Xt i, S.stateAt t h g x = some b := by
    rcases hsp with hP | hF
    · refine ⟨false, iff_of_true rfl hP, ?_⟩
      have := ((S.part_splitsToP _ _ _).1 hP).2.1
      rw [S.leafState_X_union_U] at this
      obtain ⟨x, hx⟩ := this
      exact ⟨x, (mem_inter.1 hx).1, mem_side.1 (mem_inter.1 hx).2⟩
    · refine ⟨true, ⟨fun h' => (by cases h'), fun hP => ?_⟩, ?_⟩
      · have h1 := ((S.part_splitsToP _ _ _).1 hP).2.2
        have h2 := ((S.part_splitsToF _ _ _).1 hF).2.1
        obtain ⟨z, hz⟩ := h2
        exact (Finset.disjoint_left.1 h1 (mem_inter.1 hz).1 (mem_inter.1 hz).2).elim
      · have := ((S.part_splitsToF _ _ _).1 hF).2.1
        obtain ⟨x, hx⟩ := this
        exact ⟨x, (mem_inter.1 hx).1, mem_side.1 (mem_inter.1 hx).2⟩
  have hxb : x.1 ∈ GraphDomain.ball S.G S.Λ (S.a i) S.r₀ := by
    have := hx.1
    rw [hb] at this
    exact mem_subtype.1 this
  have hxA := hA (S.mem_up hx.1)
  -- the anchor is in the list of side `b`
  have hgd := hgood g b x hx.2 hxA
  have hr := H.r₀_le
  have hmem : i ∈ S.chargeList g (S.offset t h g) t b := by
    rw [mem_chargeList]
    have h1 := (S.odep_le_of_mem_ball H.hlip hyb b).1
    have h2 := (S.odep_le_of_mem_ball H.hlip hxb b).2
    have h3 : (S.D / 2 : ℕ) + S.r₀ ≤ S.D := by omega
    have h3' : ((S.D / 2 : ℕ) : ℤ) + S.r₀ ≤ S.D := by exact_mod_cast h3
    cases b
    · simp only [front_false, odep_false] at h1 h2 hgd ⊢
      have : ((S.lo g (S.offset t h g) + 1 + sideFills (fills t) false / S.n : ℕ) : ℤ) ≤
        S.dep y := by exact_mod_cast hmP
      constructor <;> omega
    · simp only [front_true, odep_true] at h1 h2 hgd ⊢
      have : (S.dep y : ℤ) + ((sideFills (fills t) true / S.n : ℕ) : ℤ) ≤
        S.hi g (S.offset t h g) := by exact_mod_cast hmF
      constructor <;> omega
  set k := (S.chargeList g (S.offset t h g) t b).idxOf i
  have hk : k < S.M :=
    (List.idxOf_lt_length_of_mem hmem).trans_le (H.length_chargeList_le hT.le h g b)
  have hM := S.M_pos
  have e1 : decide (S.M ≤ (if b then S.M else 0) + k) = b := by
    cases b
    · simp only [Bool.false_eq_true, if_false, zero_add, decide_eq_false_iff_not, not_le]
      exact hk
    · simp
  refine ⟨(if b then S.M else 0) + k, by split_ifs <;> omega, ?_, ?_, ?_, ?_, hb⟩
  · have e2 : ((if b then S.M else 0) + k) % S.M = k := by
      cases b
      · simp [Nat.mod_eq_of_lt hk]
      · simp [Nat.add_mod_left, Nat.mod_eq_of_lt hk]
    rw [e1, e2]
    exact List.getElem?_idxOf hmem
  · rw [e1]
    exact hbP
  · rw [e1]
    exact ⟨x, mem_inter.2 ⟨hb ▸ hx.1, mem_side.2 hx.2⟩⟩
  · exact ⟨y, mem_inter.2 ⟨hb ▸ hy.1, mem_middle.2 hy.2⟩⟩

open Classical in
/-- **Lemma 9.1 (4), availability** (D9.8.16). -/
theorem Hyp.item4 (c₁ : ℝ) (hcM : c₁ * (2 * S.M) ≤ S.n * S.D) : S.Item4 c₁ := by
  intro t ht2 h hgood g
  have hcT := S.c_of_odd ht2
  have hslot := fun i hi => H.exists_slot h hgood g i hi
  choose! vf hvf using hslot
  refine ⟨fun i => ⟨vf i % S.c t, Nat.mod_lt _ (S.c_pos t)⟩, ?_, ?_⟩
  · intro i i' hi hi' hv
    have h1 := (hvf i hi).1
    have h2 := (hvf i' hi').1
    have hv' : vf i % S.c t = vf i' % S.c t := congrArg Fin.val hv
    rw [hcT, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv'
    have e1 := (hvf i hi).2.1
    have e2 := (hvf i' hi').2.1
    rw [hv'] at e1
    rw [e1] at e2
    exact Option.some.inj e2
  · intro i hi
    obtain ⟨hlt, hsel, hside, hP, hY, hb⟩ := hvf i hi
    have hmod : vf i % S.c t = vf i := by rw [hcT]; exact Nat.mod_eq_of_lt hlt
    -- the move of every choice with this slot in band `g`
    have hmove : ∀ c : S.Ch t, c g = ⟨vf i % S.c t, Nat.mod_lt _ (S.c_pos t)⟩ →
        (S.round t).move h c g =
          (if ((S.round t).old h g).SplitsToP (physReg (S.Xt i)) then
            Transport.Move.toP (physReg (S.Xt i) ∩ ((S.round t).old h g).Y)
          else Transport.Move.toF (physReg (S.Xt i) ∩ ((S.round t).old h g).Y)) := by
      intro c hc
      have hcv : (c g : ℕ) = vf i := by rw [hc]; exact hmod
      have hstep : S.step g (S.offset t h g) t (c g) (S.stateAt t h g) =
          some (decide (S.M ≤ vf i), S.ball i ∩ middle (S.stateAt t h g)) := by
        simp only [step, show (t : ℕ) % 2 ≠ 0 by omega, if_false, chargeStep, hcv, hsel,
          Option.bind_some]
        rw [if_pos ⟨hP, hY⟩]
      change S.toMove (S.step g (S.offset t h g) t (c g) (S.stateAt t h g)) = _
      rw [hstep]
      change _ = if ((S.round t).old h g).SplitsToP (physReg (S.Xt i)) then
        Transport.Move.toP (physReg (S.Xt i) ∩ physReg (middle (S.stateAt t h g)))
      else Transport.Move.toF (physReg (S.Xt i) ∩ physReg (middle (S.stateAt t h g)))
      rw [← physReg_inter, hb]
      rw [hb] at hside
      cases hd : decide (S.M ≤ vf i)
      · rw [if_pos (hside.1 hd)]; rfl
      · rw [if_neg fun hP' => by have := hside.2 hP'; rw [hd] at this; cases this]; rfl
    refine ⟨?_, fun c hc => ⟨hmove c hc, fun nl θ => ?_⟩⟩
    · change c₁ / (S.n * S.D) ≤ ∑ c ∈ univ.filter (fun c : S.Ch t => c g = _),
        (uniformTree (S.Ch t)).weight c
      rw [sum_choice_apply, hcT]
      have hn : (0 : ℝ) < S.n := by exact_mod_cast H.n_pos
      have hD : (0 : ℝ) < S.D := by exact_mod_cast H.D_pos
      have hM : (0 : ℝ) < 2 * S.M := by have := S.M_pos; positivity
      rw [div_le_div_iff₀ (mul_pos hn hD) (by push_cast; exact hM)]
      push_cast
      linarith
    · change Transport.Round.moveEta ((S.round t).old h g) ((S.round t).move h c g) θ = _
      rw [hmove c hc]
      unfold Transport.Round.splitBandEta
      split_ifs <;> simp only [Transport.Round.moveEta, Finset.sdiff_inter_self_right]

end Availability

end Scan

end AreaLaw.Scanner
