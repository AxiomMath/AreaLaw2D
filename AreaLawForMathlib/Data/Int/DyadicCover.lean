import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Maximal dyadic covers of finite subsets of `ℤ × ℤ`

Extends `Mathlib/Data/Int/Interval.lean`. The dyadic square of side `2^k` and index `z` is the
integer rectangle `[2^k z, 2^k z + (2^k - 1, 2^k - 1)]`, the sites `p` with `p / 2^k = z`.
For a finite `Y ⊆ ℤ × ℤ` and a cap `K`, the maximal dyadic squares of side at most `2^K`
contained in `Y` partition `Y` (`Finset.biUnion_dyadicCover`,
`Finset.pairwiseDisjoint_dyadicCover`);
below the cap the parent of each is *mixed* (meets `Y` and its complement), so there are at most
four squares of side `2^k` per mixed square of side `2^(k+1)` (`Finset.card_dyadicCover_lt`).
-/

open Finset

namespace Int

/-- The dyadic square of side `2^k` with index `z`. -/
noncomputable def dyadicSquare (k : ℕ) (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Icc (2 ^ k * z.1, 2 ^ k * z.2) (2 ^ k * z.1 + (2 ^ k - 1), 2 ^ k * z.2 + (2 ^ k - 1))

/-- The index of the dyadic square of side `2^k` containing `p`. -/
def dyadicIndex (k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1 / 2 ^ k, p.2 / 2 ^ k)

variable {k l : ℕ} {z : ℤ × ℤ} {p q : ℤ × ℤ}

theorem ediv_eq_iff_le_le {a b u : ℤ} (hu : 0 < u) :
    a / u = b ↔ u * b ≤ a ∧ a ≤ u * b + (u - 1) := by
  rw [le_antisymm_iff, ← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hu, Int.le_ediv_iff_mul_le hu]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem mem_dyadicSquare : p ∈ dyadicSquare k z ↔ dyadicIndex k p = z := by
  have hu : (0 : ℤ) < 2 ^ k := by positivity
  simp only [dyadicSquare, dyadicIndex, mem_Icc, Prod.le_def, Prod.ext_iff, ediv_eq_iff_le_le hu]
  tauto

theorem mem_dyadicSquare_self (k : ℕ) (p : ℤ × ℤ) : p ∈ dyadicSquare k (dyadicIndex k p) :=
  mem_dyadicSquare.2 rfl

theorem dyadicIndex_zero (p : ℤ × ℤ) : dyadicIndex 0 p = p := by simp [dyadicIndex]

theorem dyadicIndex_add (k l : ℕ) (p : ℤ × ℤ) :
    dyadicIndex (k + l) p = dyadicIndex l (dyadicIndex k p) := by
  have : (0 : ℤ) ≤ 2 ^ k := by positivity
  simp only [dyadicIndex, pow_add, Int.ediv_ediv_of_nonneg this]

/-- Dyadic nesting: a square of side `2^k` sharing a site `p` with a square of side `2^l ≥ 2^k`
lies inside it. -/
theorem dyadicSquare_subset_of_mem (hkl : k ≤ l) (hp : p ∈ dyadicSquare k z) {w : ℤ × ℤ}
    (hq : p ∈ dyadicSquare l w) : dyadicSquare k z ⊆ dyadicSquare l w := by
  intro x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [mem_dyadicSquare] at hp hq hx ⊢
  rw [dyadicIndex_add, hx, ← hp, ← dyadicIndex_add, hq]

theorem card_dyadicSquare (k : ℕ) (z : ℤ × ℤ) : #(dyadicSquare k z) = 4 ^ k := by
  have h (a : ℤ) : (2 ^ k * a + (2 ^ k - 1) + 1 - 2 ^ k * a).toNat = 2 ^ k := by
    rw [show 2 ^ k * a + (2 ^ k - 1) + 1 - 2 ^ k * a = ((2 ^ k : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [dyadicSquare, Icc_prod_def, Finset.card_product, Int.card_Icc, Int.card_Icc]
  simp only [h, ← mul_pow]
  norm_num

theorem dyadicSquare_zero (p : ℤ × ℤ) : dyadicSquare 0 p = {p} := by
  ext q; rw [mem_dyadicSquare, dyadicIndex_zero, mem_singleton]

end Int

open Int

namespace Finset

variable (Y : Finset (ℤ × ℤ)) (K : ℕ)

/-- The level of the maximal dyadic square of side at most `2^K` around `p` contained in `Y`. -/
noncomputable def dyadicLevel (p : ℤ × ℤ) : ℕ :=
  Nat.findGreatest (fun k => dyadicSquare k (dyadicIndex k p) ⊆ Y) K

/-- The maximal dyadic squares of side at most `2^K` contained in `Y`, indexed by
`(level, index)`. -/
noncomputable def dyadicCover : Finset (ℕ × (ℤ × ℤ)) :=
  Y.image fun p => (dyadicLevel Y K p, dyadicIndex (dyadicLevel Y K p) p)

/-- The indices of the dyadic squares of side `2^k` meeting `Y` and its complement. -/
noncomputable def mixedIndices (k : ℕ) : Finset (ℤ × ℤ) :=
  (Y.image (dyadicIndex k)).filter fun z => ¬dyadicSquare k z ⊆ Y

variable {Y K}

theorem mem_mixedIndices {k : ℕ} {z : ℤ × ℤ} :
    z ∈ mixedIndices Y k ↔ (∃ p ∈ Y, p ∈ dyadicSquare k z) ∧ ∃ q ∉ Y, q ∈ dyadicSquare k z := by
  simp only [mixedIndices, mem_filter, mem_image, not_subset, mem_dyadicSquare]
  tauto

theorem dyadicLevel_le (p : ℤ × ℤ) : dyadicLevel Y K p ≤ K := Nat.findGreatest_le K

theorem dyadicSquare_dyadicLevel_subset {p : ℤ × ℤ} (hp : p ∈ Y) :
    dyadicSquare (dyadicLevel Y K p) (dyadicIndex (dyadicLevel Y K p) p) ⊆ Y :=
  Nat.findGreatest_spec (P := fun k => dyadicSquare k (dyadicIndex k p) ⊆ Y) (Nat.zero_le K)
    (by rw [dyadicIndex_zero, dyadicSquare_zero]; exact singleton_subset_iff.2 hp)

theorem le_dyadicLevel {p : ℤ × ℤ} {k : ℕ} (hk : k ≤ K) (h : dyadicSquare k (dyadicIndex k p) ⊆ Y) :
    k ≤ dyadicLevel Y K p :=
  Nat.le_findGreatest hk h

theorem mem_dyadicCover {c : ℕ × (ℤ × ℤ)} (hc : c ∈ dyadicCover Y K) :
    c.1 ≤ K ∧ dyadicSquare c.1 c.2 ⊆ Y := by
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
  exact ⟨dyadicLevel_le p, dyadicSquare_dyadicLevel_subset hp⟩

/-- The maximal squares cover `Y`. -/
theorem biUnion_dyadicCover : (dyadicCover Y K).biUnion (fun c => dyadicSquare c.1 c.2) = Y := by
  apply Subset.antisymm (biUnion_subset.2 fun c hc => (mem_dyadicCover hc).2)
  intro p hp
  exact mem_biUnion.2 ⟨_, mem_image_of_mem _ hp, mem_dyadicSquare_self _ _⟩

/-- Distinct maximal squares are disjoint. -/
theorem pairwiseDisjoint_dyadicCover :
    (dyadicCover Y K : Set (ℕ × (ℤ × ℤ))).PairwiseDisjoint (fun c => dyadicSquare c.1 c.2) := by
  -- if two maximal squares share a site, the smaller lies in the larger, so their levels agree
  have key : ∀ p ∈ Y, ∀ p' ∈ Y, ∀ x, x ∈ dyadicSquare (dyadicLevel Y K p)
      (dyadicIndex (dyadicLevel Y K p) p) → x ∈ dyadicSquare (dyadicLevel Y K p')
      (dyadicIndex (dyadicLevel Y K p') p') → dyadicLevel Y K p ≤ dyadicLevel Y K p' →
      dyadicLevel Y K p' ≤ dyadicLevel Y K p := by
    intro p hp p' hp' x hx hx' hle
    have hsub := dyadicSquare_subset_of_mem hle hx hx'
    have hpp : p ∈ dyadicSquare (dyadicLevel Y K p') (dyadicIndex (dyadicLevel Y K p') p') :=
      hsub (mem_dyadicSquare_self _ _)
    rw [mem_dyadicSquare] at hpp
    refine le_dyadicLevel (dyadicLevel_le p') ?_
    rw [hpp]; exact dyadicSquare_dyadicLevel_subset hp'
  rintro c hc c' hc' hne
  obtain ⟨p, hp, rfl⟩ := mem_image.1 (mem_coe.1 hc)
  obtain ⟨p', hp', rfl⟩ := mem_image.1 (mem_coe.1 hc')
  refine disjoint_left.2 fun x hx hx' => hne ?_
  have hlev : dyadicLevel Y K p = dyadicLevel Y K p' := by
    rcases le_total (dyadicLevel Y K p) (dyadicLevel Y K p') with h | h
    · exact le_antisymm h (key p hp p' hp' x hx hx' h)
    · exact (le_antisymm h (key p' hp' p hp x hx' hx h)).symm
  simp only at hx hx'
  rw [mem_dyadicSquare] at hx hx'
  rw [hlev] at hx ⊢
  rw [← hx, ← hx']

/-- At the cap: the squares of side `2^K` are disjoint inside `Y`. -/
theorem card_dyadicCover_eq_mul_le :
    #((dyadicCover Y K).filter (·.1 = K)) * 4 ^ K ≤ #Y := by
  have hd := (pairwiseDisjoint_dyadicCover (Y := Y) (K := K)).subset
    (coe_subset.2 (filter_subset (·.1 = K) _))
  calc #((dyadicCover Y K).filter (·.1 = K)) * 4 ^ K
      = ∑ c ∈ (dyadicCover Y K).filter (·.1 = K), #(dyadicSquare c.1 c.2) := by
        rw [sum_congr rfl fun c hc => by rw [card_dyadicSquare, (mem_filter.1 hc).2], sum_const,
          smul_eq_mul]
    _ = #(((dyadicCover Y K).filter (·.1 = K)).biUnion fun c => dyadicSquare c.1 c.2) :=
        (card_biUnion hd).symm
    _ ≤ #Y := card_le_card (biUnion_subset.2 fun c hc => (mem_dyadicCover (mem_filter.1 hc).1).2)

/-- Below the cap the parent of a maximal square of side `2^k` is mixed, and a square has four
children: `N_k ≤ 4 #mixed_{k+1}`. -/
theorem card_dyadicCover_lt {k : ℕ} (hk : k < K) :
    #((dyadicCover Y K).filter (·.1 = k)) ≤ 4 * #(mixedIndices Y (k + 1)) := by
  set s := (dyadicCover Y K).filter (·.1 = k)
  have hmaps : ∀ c ∈ s, dyadicIndex 1 c.2 ∈ mixedIndices Y (k + 1) := by
    intro c hc
    obtain ⟨hc1, hck⟩ := mem_filter.1 hc
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hc1
    simp only at hck ⊢
    subst hck
    have hidx : dyadicIndex 1 (dyadicIndex (dyadicLevel Y K p) p) =
        dyadicIndex (dyadicLevel Y K p + 1) p := (dyadicIndex_add _ _ _).symm
    rw [hidx, mem_mixedIndices]
    refine ⟨⟨p, hp, mem_dyadicSquare_self _ _⟩, ?_⟩
    by_contra h
    push Not at h
    have := le_dyadicLevel (Y := Y) (K := K) (p := p) (k := dyadicLevel Y K p + 1)
      (by simpa using hk) fun x hx => by_contra fun hxY => (h x hxY) hx |>.elim
    omega
  calc #s ≤ 4 * #(s.image fun c => dyadicIndex 1 c.2) := by
        refine card_le_mul_card_image _ _ fun w _ => ?_
        refine (card_le_card_of_injOn (fun c => c.2) (t := dyadicSquare 1 w) ?_ ?_).trans
          (card_dyadicSquare 1 w).le
        · intro c hc
          exact mem_dyadicSquare.2 (mem_filter.1 hc).2
        · intro c hc c' hc' h
          have h1 := (mem_filter.1 (mem_filter.1 hc).1).2
          have h2 := (mem_filter.1 (mem_filter.1 hc').1).2
          exact Prod.ext (h1.trans h2.symm) h
    _ ≤ 4 * #(mixedIndices Y (k + 1)) :=
        Nat.mul_le_mul_left _ (card_le_card fun w hw => by
          obtain ⟨c, hc, rfl⟩ := mem_image.1 hw; exact hmaps c hc)

/-- A square mixed for `Y \ W` is mixed for `Y` or for `W`. -/
theorem mixedIndices_sdiff_subset (Y W : Finset (ℤ × ℤ)) (k : ℕ) :
    mixedIndices (Y \ W) k ⊆ mixedIndices Y k ∪ mixedIndices W k := by
  intro z hz
  rw [mem_mixedIndices] at hz
  obtain ⟨⟨p, hp, hpz⟩, q, hq, hqz⟩ := hz
  rw [mem_sdiff] at hp
  rw [mem_union, mem_mixedIndices, mem_mixedIndices]
  by_cases hqY : q ∈ Y
  · exact Or.inr ⟨⟨q, by simpa [hqY] using hq, hqz⟩, p, hp.2, hpz⟩
  · exact Or.inl ⟨⟨p, hp.1, hpz⟩, q, hqY, hqz⟩

/-- A square mixed for a union is mixed for one of its members. -/
theorem mixedIndices_biUnion_subset {ι : Type*} (s : Finset ι) (Y : ι → Finset (ℤ × ℤ)) (k : ℕ) :
    mixedIndices (s.biUnion Y) k ⊆ s.biUnion fun i => mixedIndices (Y i) k := by
  intro z hz
  rw [mem_mixedIndices] at hz
  obtain ⟨⟨p, hp, hpz⟩, q, hq, hqz⟩ := hz
  obtain ⟨i, hi, hpi⟩ := mem_biUnion.1 hp
  exact mem_biUnion.2 ⟨i, hi, mem_mixedIndices.2 ⟨⟨p, hpi, hpz⟩, q,
    fun h => hq (mem_biUnion.2 ⟨i, hi, h⟩), hqz⟩⟩

end Finset
