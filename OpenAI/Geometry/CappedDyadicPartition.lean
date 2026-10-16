/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/Geometry/CappedDyadicPartition.lean`,
`TNLean/PEPS/AreaLaw/Geometry/MixedDyadicSquares.lean`,
`TNLean/PEPS/AreaLaw/Geometry/CappedDyadicPartitionByScale.lean` and
`TNLean/PEPS/AreaLaw/Geometry/LatticeDyadicRect.lean`. Apache 2.0.
-/
import Mathlib.Data.Nat.Find
import OpenAI.Geometry.DyadicRefinement
import OpenAI.Geometry.DyadicWeightedSum

/-!
# Capped maximal dyadic partitions of a finite lattice set

The lattice sites of the origin-zero dyadic square of side `2^k` and index `z` are the integer
rectangle `[2^k z, 2^k z + (2^k - 1, 2^k - 1)]`.  For a finite set `S ⊂ ℤ²` and a cap `K`, the
contained squares of side at most `2^K` whose parent is not contained, together with the
contained squares of side exactly `2^K`, partition `S` [OAI265, Lemma 9.4]: a single site is a
contained square, and dyadic nesting makes distinct maximal squares disjoint.  Below the cap the
parent of a selected square contains a site of `S` and a site outside, so there are at most four
selected squares of side `2^k` per mixed square of side `2^(k+1)`.  A square mixed for a union is
mixed for one of the constituents, and one mixed for a difference is mixed for one of the two
sets.

## Main definitions

* `OpenAI.Geometry.latticeDyadicCell`: the sites of a dyadic square.
* `OpenAI.Geometry.cappedDyadicPartition`: the capped maximal contained squares of a set.
* `OpenAI.Geometry.mixedDyadicIndices`: the squares meeting a set and its complement.

## Main statements

* `OpenAI.Geometry.biUnion_cappedDyadicPartition`,
  `OpenAI.Geometry.pairwiseDisjoint_cappedDyadicPartition`: the selected squares partition `S`.
* `OpenAI.Geometry.card_cappedDyadicPartition_below_cap_le`: four selected squares per mixed
  parent.
* `OpenAI.Geometry.sum_rpow_cappedDyadicPartition_le`: the dyadic moment of order `1 + e`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §9.3, proof of Lemma 9.4.
-/

open scoped BigOperators

namespace OpenAI.Geometry

/-! ## Lattice dyadic squares -/

/-- The lattice sites of the origin-zero dyadic square of side `2^k` with index `z`. -/
def latticeDyadicCell (k : ℕ) (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  dyadicRefinement {z} k

/-- Integer ancestry agrees with the real floor-index convention, including negative
coordinates. -/
theorem dyadicAncestor_eq_cellIndex (k : ℕ) (x : ℤ × ℤ) :
    dyadicAncestor k x = dyadicCellIndex (0, 0) k (x.1, x.2) := by
  simpa [dyadicCellIndex] using
    dyadicCellIndex_of_le (0, 0) 0 k (x.1, x.2) (Nat.zero_le k)

@[simp] theorem mem_latticeDyadicCell (k : ℕ) (z x : ℤ × ℤ) :
    x ∈ latticeDyadicCell k z ↔ dyadicAncestor k x = z := by
  simp [latticeDyadicCell, mem_dyadicRefinement_iff]

/-- A side-`2^k` square has `4^k` lattice sites. -/
@[simp] theorem card_latticeDyadicCell (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicCell k z).card = 4 ^ k := by
  simp [latticeDyadicCell, card_dyadicRefinement]

theorem latticeDyadicCell_nonempty (k : ℕ) (z : ℤ × ℤ) : (latticeDyadicCell k z).Nonempty := by
  rw [← Finset.card_pos, card_latticeDyadicCell]
  positivity

@[simp] theorem latticeDyadicCell_zero (z : ℤ × ℤ) : latticeDyadicCell 0 z = {z} := by
  ext x
  simp [dyadicAncestor]

theorem dyadicAncestor_succ (k : ℕ) (x : ℤ × ℤ) :
    dyadicAncestor (k + 1) x = dyadicParent (dyadicAncestor k x) := by
  simp only [dyadicAncestor_eq_cellIndex, dyadicCellIndex_succ]

theorem dyadicAncestor_sub_dyadicAncestor (k l : ℕ) (x : ℤ × ℤ) (h : k ≤ l) :
    dyadicAncestor (l - k) (dyadicAncestor k x) = dyadicAncestor l x := by
  rw [dyadicAncestor_eq_cellIndex k, dyadicAncestor_eq_cellIndex l]
  exact dyadicCellIndex_of_le _ _ _ _ h

/-- Intersecting dyadic squares are nested in the order of their scales. -/
theorem latticeDyadicCell_subset_of_common_mem {k l : ℕ} {u v x : ℤ × ℤ} (hkl : k ≤ l)
    (hx : x ∈ latticeDyadicCell k u) (hy : x ∈ latticeDyadicCell l v) :
    latticeDyadicCell k u ⊆ latticeDyadicCell l v := by
  simp only [Finset.subset_iff, mem_latticeDyadicCell] at hx hy ⊢
  intro y hyu
  rw [← dyadicAncestor_sub_dyadicAncestor k l y hkl, hyu, ← hx,
    dyadicAncestor_sub_dyadicAncestor k l x hkl, hy]

/-- Every lattice square is contained in its parent. -/
theorem latticeDyadicCell_subset_parent (k : ℕ) (z : ℤ × ℤ) :
    latticeDyadicCell k z ⊆ latticeDyadicCell (k + 1) (dyadicParent z) := by
  intro x hx
  rw [mem_latticeDyadicCell, dyadicAncestor_succ, (mem_latticeDyadicCell k z x).mp hx]

/-- Membership in a dyadic square in coordinates. -/
theorem mem_latticeDyadicCell_iff_bounds (k : ℕ) (z x : ℤ × ℤ) :
    x ∈ latticeDyadicCell k z ↔
      z.1 * 2 ^ k ≤ x.1 ∧ x.1 < z.1 * 2 ^ k + 2 ^ k ∧
      z.2 * 2 ^ k ≤ x.2 ∧ x.2 < z.2 * 2 ^ k + 2 ^ k := by
  rcases z with ⟨a, b⟩
  rw [mem_latticeDyadicCell]
  simp only [dyadicAncestor, Prod.mk.injEq,
    Int.ediv_eq_iff_of_pos (show (0 : ℤ) < 2 ^ k by positivity)]
  tauto

/-- A dyadic square is the integer rectangle `[2^k z, 2^k z + (2^k - 1, 2^k - 1)]`. -/
theorem latticeDyadicCell_eq_Icc (k : ℕ) (z : ℤ × ℤ) :
    latticeDyadicCell k z = Finset.Icc (z.1 * 2 ^ k, z.2 * 2 ^ k)
      (z.1 * 2 ^ k + 2 ^ k - 1, z.2 * 2 ^ k + 2 ^ k - 1) := by
  ext x
  rw [mem_latticeDyadicCell_iff_bounds, Finset.mem_Icc, Prod.le_def, Prod.le_def]
  dsimp only
  omega

theorem isIntRect_latticeDyadicCell (k : ℕ) (z : ℤ × ℤ) : IsIntRect (latticeDyadicCell k z) := by
  rw [latticeDyadicCell_eq_Icc]
  have : (0 : ℤ) < 2 ^ k := by positivity
  exact isIntRect_Icc (Prod.le_def.2 ⟨by dsimp only; omega, by dsimp only; omega⟩)

/-- A dyadic square of side `2^k` has size `2^k`. -/
@[simp] theorem boxSize_latticeDyadicCell (k : ℕ) (z : ℤ × ℤ) :
    boxSize (latticeDyadicCell k z) = 2 ^ k := by
  have h : (0 : ℤ) < 2 ^ k := by positivity
  rw [latticeDyadicCell_eq_Icc, boxSize_Icc (Prod.le_def.2 ⟨by dsimp only; omega,
    by dsimp only; omega⟩)]
  dsimp only
  have : z.1 * 2 ^ k + 2 ^ k - 1 + 1 - z.1 * 2 ^ k = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
  have h' : z.2 * 2 ^ k + 2 ^ k - 1 + 1 - z.2 * 2 ^ k = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [this, h', Int.toNat_natCast, max_self]

/-! ## The capped partition -/

/-- The contained dyadic squares of side at most `2^K` whose parent is not contained, together
with the contained squares of side `2^K`, indexed by `(k, z)`. -/
def cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) : Finset (ℕ × (ℤ × ℤ)) :=
  ((Finset.range (K + 1)).biUnion fun k ↦
    (S.image (dyadicAncestor k)).image (Prod.mk k)).filter fun c ↦
      latticeDyadicCell c.1 c.2 ⊆ S ∧
        (c.1 = K ∨ ¬latticeDyadicCell (c.1 + 1) (dyadicParent c.2) ⊆ S)

theorem mem_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K k : ℕ) (z : ℤ × ℤ) :
    (k, z) ∈ cappedDyadicPartition S K ↔
      k ≤ K ∧ latticeDyadicCell k z ⊆ S ∧
        (k = K ∨ ¬latticeDyadicCell (k + 1) (dyadicParent z) ⊆ S) := by
  constructor
  · intro h
    obtain ⟨h, hs, hp⟩ := Finset.mem_filter.mp h
    obtain ⟨l, hl, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    have hlk : l = k := congrArg Prod.fst he
    subst l
    exact ⟨by simpa [Nat.lt_succ_iff] using hl, hs, hp⟩
  · rintro ⟨hk, hs, hp⟩
    obtain ⟨x, hx⟩ := latticeDyadicCell_nonempty k z
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨k, ?_, ?_⟩, hs, hp⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_image.mpr ⟨z, Finset.mem_image.mpr
        ⟨x, hs hx, (mem_latticeDyadicCell k z x).mp hx⟩, rfl⟩

/-- Every site of `S` lies in a selected square: take its largest contained scale up to the
cap. -/
theorem exists_mem_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) {x : ℤ × ℤ}
    (hx : x ∈ S) : ∃ c ∈ cappedDyadicPartition S K, x ∈ latticeDyadicCell c.1 c.2 := by
  let P : ℕ → Prop := fun k ↦ latticeDyadicCell k (dyadicAncestor k x) ⊆ S
  have hzero : P 0 := by simpa [P, dyadicAncestor] using hx
  let k := Nat.findGreatest P K
  have hk : k ≤ K := Nat.findGreatest_le K
  have hs : P k := Nat.findGreatest_spec (Nat.zero_le K) hzero
  refine ⟨(k, dyadicAncestor k x), ?_, by simp⟩
  rw [mem_cappedDyadicPartition]
  refine ⟨hk, hs, ?_⟩
  by_cases he : k = K
  · exact Or.inl he
  · right
    have hp : ¬P (k + 1) :=
      Nat.findGreatest_is_greatest (n := K) (Nat.lt_succ_self k) (by omega)
    simpa only [P, dyadicAncestor_succ] using hp

/-- The selected squares cover exactly `S`. -/
theorem biUnion_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    (cappedDyadicPartition S K).biUnion (fun c ↦ latticeDyadicCell c.1 c.2) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨k, z⟩, hc, hx⟩ := Finset.mem_biUnion.mp hx
    exact ((mem_cappedDyadicPartition S K k z).mp hc).2.1 hx
  · exact fun hx ↦ Finset.mem_biUnion.mpr (exists_mem_cappedDyadicPartition S K hx)

private theorem selected_scale_eq_of_le {S : Finset (ℤ × ℤ)} {K k l : ℕ} {u v x : ℤ × ℤ}
    (hu : (k, u) ∈ cappedDyadicPartition S K) (hv : (l, v) ∈ cappedDyadicPartition S K)
    (hx : x ∈ latticeDyadicCell k u) (hy : x ∈ latticeDyadicCell l v) (hkl : k ≤ l) :
    k = l := by
  obtain ⟨hk, _, hp⟩ := (mem_cappedDyadicPartition S K k u).mp hu
  obtain ⟨hl, hs, _⟩ := (mem_cappedDyadicPartition S K l v).mp hv
  by_contra hne
  have hparent := latticeDyadicCell_subset_parent k u hx
  have hsub := latticeDyadicCell_subset_of_common_mem (by omega : k + 1 ≤ l) hparent hy
  rcases hp with hp | hp
  · omega
  · exact hp (hsub.trans hs)

/-- Distinct selected squares are disjoint, including at unequal scales. -/
theorem pairwiseDisjoint_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    (cappedDyadicPartition S K : Set (ℕ × (ℤ × ℤ))).PairwiseDisjoint
      (fun c ↦ latticeDyadicCell c.1 c.2) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hk : a.1 = b.1 := by
    rcases le_total a.1 b.1 with h | h
    · exact selected_scale_eq_of_le ha hb hxa hxb h
    · exact (selected_scale_eq_of_le hb ha hxb hxa h).symm
  have hz : a.2 = b.2 := by
    rw [mem_latticeDyadicCell] at hxa hxb
    rw [hk] at hxa
    exact hxa.symm.trans hxb
  exact hab (Prod.ext hk hz)

/-- The areas `4^k` of the selected squares sum to `|S|`. -/
theorem sum_pow_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    ∑ c ∈ cappedDyadicPartition S K, 4 ^ c.1 = S.card := by
  have := Finset.card_biUnion (pairwiseDisjoint_cappedDyadicPartition S K)
  rw [biUnion_cappedDyadicPartition] at this
  simpa using this.symm

/-- The cap-scale squares have total area at most `|S|`. -/
theorem card_cappedDyadicPartition_at_cap_le (S : Finset (ℤ × ℤ)) (K : ℕ) :
    4 ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card ≤ S.card := by
  calc
    _ = ∑ _c ∈ (cappedDyadicPartition S K).filter (fun c ↦ c.1 = K), 4 ^ K := by
      simp [Nat.mul_comm]
    _ = ∑ c ∈ (cappedDyadicPartition S K).filter (fun c ↦ c.1 = K), 4 ^ c.1 :=
      Finset.sum_congr rfl fun c hc ↦ by rw [(Finset.mem_filter.mp hc).2]
    _ ≤ ∑ c ∈ cappedDyadicPartition S K, 4 ^ c.1 :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = S.card := sum_pow_cappedDyadicPartition S K

/-! ## Mixed squares -/

/-- The indices of the side-`2^k` squares containing a site of `S` and a site outside `S`. -/
def mixedDyadicIndices (S : Finset (ℤ × ℤ)) (k : ℕ) : Finset (ℤ × ℤ) :=
  (S.image (dyadicAncestor k)).filter fun z ↦ ¬latticeDyadicCell k z ⊆ S

theorem mem_mixedDyadicIndices (S : Finset (ℤ × ℤ)) (k : ℕ) (z : ℤ × ℤ) :
    z ∈ mixedDyadicIndices S k ↔
      (∃ x ∈ latticeDyadicCell k z, x ∈ S) ∧ ∃ y ∈ latticeDyadicCell k z, y ∉ S := by
  simp only [mixedDyadicIndices, Finset.mem_filter, Finset.mem_image,
    Finset.subset_iff, not_forall, mem_latticeDyadicCell]
  aesop

/-- Below the cap, every selected square has a mixed parent. -/
theorem parent_mem_mixedDyadicIndices {S : Finset (ℤ × ℤ)} {K k : ℕ} {z : ℤ × ℤ}
    (hz : (k, z) ∈ cappedDyadicPartition S K) (hk : k < K) :
    dyadicParent z ∈ mixedDyadicIndices S (k + 1) := by
  obtain ⟨_, hs, hp⟩ := (mem_cappedDyadicPartition S K k z).mp hz
  have hp' : ¬latticeDyadicCell (k + 1) (dyadicParent z) ⊆ S := hp.resolve_left (by omega)
  obtain ⟨x, hx⟩ := latticeDyadicCell_nonempty k z
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hs hx, ?_⟩, hp'⟩
  exact (mem_latticeDyadicCell _ _ _).mp (latticeDyadicCell_subset_parent k z hx)

/-- There are at most four selected squares of side `2^k` per mixed square of side `2^(k+1)`,
below the cap. -/
theorem card_cappedDyadicPartition_below_cap_le (S : Finset (ℤ × ℤ)) (K k : ℕ) (hk : k < K) :
    ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card ≤
      4 * (mixedDyadicIndices S (k + 1)).card := by
  have hinj : Set.InjOn Prod.snd
      (↑((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)) : Set (ℕ × (ℤ × ℤ))) := by
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  have hsub : ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).image Prod.snd ⊆
      dyadicRefinement (mixedDyadicIndices S (k + 1)) 1 := by
    rintro z hz
    obtain ⟨⟨l, u⟩, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hu, hscale⟩ := Finset.mem_filter.mp hu
    dsimp at hscale ⊢
    subst l
    rw [mem_dyadicRefinement_iff]
    simpa [dyadicAncestor, dyadicParent] using parent_mem_mixedDyadicIndices hu hk
  calc
    _ = (((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).image Prod.snd).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (dyadicRefinement (mixedDyadicIndices S (k + 1)) 1).card := Finset.card_le_card hsub
    _ = _ := by simp [card_dyadicRefinement]

/-- A square mixed for a finite union is mixed for one of its constituents. -/
theorem card_mixedDyadicIndices_biUnion_le {ι : Type*} (I : Finset ι)
    (S : ι → Finset (ℤ × ℤ)) (k : ℕ) :
    (mixedDyadicIndices (I.biUnion S) k).card ≤ ∑ i ∈ I, (mixedDyadicIndices (S i) k).card := by
  classical
  refine (Finset.card_le_card fun z hz => ?_).trans Finset.card_biUnion_le
  obtain ⟨⟨x, hx, hxin⟩, y, hy, hyout⟩ := (mem_mixedDyadicIndices _ _ _).mp hz
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxin
  exact Finset.mem_biUnion.mpr ⟨i, hi, (mem_mixedDyadicIndices _ _ _).mpr
    ⟨⟨x, hx, hxi⟩, y, hy, fun h ↦ hyout (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)⟩⟩

/-- A square mixed for a difference is mixed for one of the two sets. -/
theorem card_mixedDyadicIndices_sdiff_le (S U : Finset (ℤ × ℤ)) (k : ℕ) :
    (mixedDyadicIndices (S \ U) k).card ≤
      (mixedDyadicIndices S k).card + (mixedDyadicIndices U k).card := by
  refine (Finset.card_le_card fun z hz => ?_).trans (Finset.card_union_le _ _)
  obtain ⟨⟨x, hx, hxin⟩, y, hy, hyout⟩ := (mem_mixedDyadicIndices _ _ _).mp hz
  obtain ⟨hxS, hxU⟩ := Finset.mem_sdiff.mp hxin
  by_cases hyS : y ∈ S
  · have hyU : y ∈ U := by
      by_contra h
      exact hyout (Finset.mem_sdiff.mpr ⟨hyS, h⟩)
    exact Finset.mem_union_right _ ((mem_mixedDyadicIndices _ _ _).mpr
      ⟨⟨y, hy, hyU⟩, x, hx, hxU⟩)
  · exact Finset.mem_union_left _ ((mem_mixedDyadicIndices _ _ _).mpr
      ⟨⟨x, hx, hxS⟩, y, hy, hyS⟩)

/-! ## Summation by scale -/

/-- A weight depending only on the scale sums over the selected squares by counting the squares
at each scale. -/
theorem sum_cappedDyadicPartition_by_scale (S : Finset (ℤ × ℤ)) (K : ℕ) (f : ℕ → ℝ) :
    (∑ c ∈ cappedDyadicPartition S K, f c.1) =
      ∑ k ∈ Finset.range (K + 1),
        (((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card : ℝ) * f k := by
  have hmap : ∀ c ∈ cappedDyadicPartition S K, c.1 ∈ Finset.range (K + 1) :=
    fun c hc ↦ Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((mem_cappedDyadicPartition S K c.1 c.2).mp hc).1)
  have h := Finset.sum_fiberwise_of_maps_to' (g := Prod.fst)
    (s := cappedDyadicPartition S K) (t := Finset.range (K + 1)) hmap f
  simpa only [Finset.sum_const, nsmul_eq_mul] using h.symm

/-- **The dyadic moment of a capped partition.**  If the cap-scale squares have total side at
most `A` and the squares at each lower scale total side at most `B`, then
`∑ (side)^{1+e} ≤ (A + B / (2^e - 1)) L^e` for every `L ≥ 2^K`. -/
theorem sum_rpow_cappedDyadicPartition_le (S : Finset (ℤ × ℤ)) (K : ℕ) {L e A B : ℝ}
    (he : 0 < e) (hB : 0 ≤ B) (hlo : 2 ^ K ≤ L)
    (hcap : (2 : ℝ) ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card ≤ A)
    (hsmall : ∀ k < K,
      (2 : ℝ) ^ k * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card ≤ B) :
    ∑ c ∈ cappedDyadicPartition S K, ((2 : ℝ) ^ c.1) ^ (1 + e) ≤
      (A + B / ((2 : ℝ) ^ e - 1)) * L ^ e := by
  rw [sum_cappedDyadicPartition_by_scale S K fun k ↦ ((2 : ℝ) ^ k) ^ (1 + e)]
  have hA : 0 ≤ A := le_trans (by positivity) hcap
  have hden : 0 < (2 : ℝ) ^ e - 1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) he)
  exact (sum_weighted_dyadic_rpow_le _ K he hB hcap hsmall).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hlo he.le) (by positivity))

end OpenAI.Geometry
