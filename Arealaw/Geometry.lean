import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Nat.Dist
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Lattice.Nat

/-!
# Ring and line geometry of the chain

The ordered layer above `Finset σ` that Brandão–Horodecki's statements quantify over: the
cyclic site distance `ringDist` on `Fin n`, the minimal pairwise distance `regionDist` over an
arbitrary site metric, the paper's `separation`, and intervals of the line and arcs of the ring.

`ringDist` is ours because Mathlib's cyclic magnitude, `ZMod.valMinAbs`, lives on `ZMod n` and
the chain's sites are `Fin n` throughout; the line distance is `Nat.dist ↑i ↑j` and needs no
definition of its own.  An interval is an ℕ-window clipped to the chain, *not* a `Finset.Ico`
of `Fin`-valued endpoints, which cannot express suffixes `[a, n)` or the full line;
`interval_eq_Ico` bridges the two when both endpoints lie on the chain.
-/

namespace Arealaw

/-! ## Site distance on the ring -/

variable {n : ℕ}

/-- The cyclic distance between two sites of the ring `Fin n`: the shorter of the two
ways around. -/
def ringDist (i j : Fin n) : ℕ := min ((j - i : Fin n) : ℕ) ((i - j : Fin n) : ℕ)

theorem ringDist_comm (i j : Fin n) : ringDist i j = ringDist j i := min_comm _ _

/-- **Definiteness of the ring distance.** -/
@[simp] theorem ringDist_eq_zero_iff {i j : Fin n} : ringDist i j = 0 ↔ i = j := by
  have := i.neZero
  simp [ringDist, sub_eq_zero, eq_comm]

@[simp] theorem ringDist_self (i : Fin n) : ringDist i i = 0 := ringDist_eq_zero_iff.mpr rfl

/-- **Rotation invariance of the ring distance.** -/
@[simp] theorem ringDist_add_right (i j k : Fin n) : ringDist (i + k) (j + k) = ringDist i j := by
  have := i.neZero
  simp [ringDist]

/-- **Cut invariance of the ring distance**: cutting the ring open at `k`, the
relabelling `i ↦ i - k`, leaves distances alone. -/
@[simp] theorem ringDist_sub_right (i j k : Fin n) : ringDist (i - k) (j - k) = ringDist i j := by
  have := i.neZero
  simp [ringDist]

/-! ## Distance between regions -/

section Region

variable {σ : Type*}

/-- The minimal pairwise distance between two regions over a site metric `d`. -/
noncomputable def regionDist (d : σ → σ → ℕ) (X Y : Finset σ) : ℕ := sInf (Set.image2 d X Y)

variable {d : σ → σ → ℕ} {X Y X' Y' : Finset σ}

theorem regionDist_le_of_mem {i j : σ} (hi : i ∈ X) (hj : j ∈ Y) : regionDist d X Y ≤ d i j :=
  Nat.sInf_le <| Set.mem_image2_of_mem hi hj

/-- On nonempty regions the minimal distance is attained. -/
theorem exists_regionDist_eq (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ i ∈ X, ∃ j ∈ Y, d i j = regionDist d X Y :=
  Nat.sInf_mem <| hX.to_set.image2 hY.to_set

/-- Nonemptiness is necessary: an empty region has `regionDist = 0` yet satisfies the
hypothesis for every `k`. -/
theorem le_regionDist (hX : X.Nonempty) (hY : Y.Nonempty) {k : ℕ}
    (h : ∀ i ∈ X, ∀ j ∈ Y, k ≤ d i j) : k ≤ regionDist d X Y :=
  le_csInf (hX.to_set.image2 hY.to_set) fun _ ⟨i, hi, j, hj, hij⟩ => hij ▸ h i hi j hj

theorem regionDist_comm (hd : ∀ i j, d i j = d j i) : regionDist d X Y = regionDist d Y X :=
  congrArg sInf <| (Set.image2_swap d _ _).trans <| Set.image2_congr' fun i j => hd j i

@[simp] theorem regionDist_empty_left : regionDist d ∅ Y = 0 := by simp [regionDist]

@[simp] theorem regionDist_empty_right : regionDist d X ∅ = 0 := by simp [regionDist]

/-- Shrinking the regions can only increase their distance. -/
theorem regionDist_le_regionDist (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty) : regionDist d X Y ≤ regionDist d X' Y' :=
  le_regionDist hX' hY' fun _ hi _ hj => regionDist_le_of_mem (hX hi) (hY hj)

@[simp] theorem regionDist_singleton (i j : σ) : regionDist d {i} {j} = d i j := by
  simp [regionDist]

/-! ## Separation -/

/-- The number of sites strictly between two regions, truncated, so adjacent or
overlapping regions have separation `0`. -/
noncomputable def separation (d : σ → σ → ℕ) (X Y : Finset σ) : ℕ := regionDist d X Y - 1

theorem lt_separation_iff {l : ℕ} : l < separation d X Y ↔ l + 1 < regionDist d X Y :=
  Nat.lt_sub_iff_add_lt

@[simp] theorem separation_singleton (i j : σ) : separation d {i} {j} = d i j - 1 := by
  simp [separation]

/-- Positive separation forces disjointness.  Reflexivity of the site metric is necessary:
an overlap is seen only through the vanishing distance of a site to itself. -/
theorem disjoint_of_lt_separation (hrefl : ∀ i, d i i = 0) {l : ℕ} (h : l < separation d X Y) :
    Disjoint X Y := by
  grind [separation, regionDist_le_of_mem, Finset.disjoint_left]

end Region

/-! ## Intervals of the line and arcs of the ring -/

/-- The sites of the chain in the ℕ-window `[a, b)`. -/
def interval (a b : ℕ) : Finset (Fin n) := {i | a ≤ (i : ℕ) ∧ (i : ℕ) < b}

@[simp] theorem mem_interval {a b : ℕ} {i : Fin n} :
    i ∈ interval a b ↔ a ≤ (i : ℕ) ∧ (i : ℕ) < b := by simp [interval]

@[simp] theorem interval_self (a : ℕ) : interval (n := n) a a = ∅ := by simp [interval]

@[simp] theorem interval_zero_eq_univ : interval (n := n) 0 n = Finset.univ := by simp [interval]

/-- With both endpoints on the chain, an interval is the `Fin`-interval `Finset.Ico a b`. -/
theorem interval_eq_Ico (a b : Fin n) : interval (a : ℕ) b = Finset.Ico a b := by
  ext i
  simp

/-- The window `[a, b)` holds at most `b - a` sites of the chain. -/
theorem card_interval_le (a b : ℕ) : (interval (n := n) a b).card ≤ b - a :=
  (Finset.card_le_card_of_injOn Fin.val (by simp [Set.MapsTo]) Fin.val_injective.injOn).trans_eq
    (Nat.card_Ico a b)

/-- A region of the chain is an interval of the line if it is some ℕ-window. -/
def IsInterval (A : Finset (Fin n)) : Prop := ∃ a b : ℕ, A = interval a b

theorem isInterval_interval (a b : ℕ) : IsInterval (interval (n := n) a b) := ⟨a, b, rfl⟩

section Arc

variable [NeZero n]

/-- A region of the ring is an arc if cutting the ring open at some site makes it an
interval of the line.  Cutting at `s` is the relabelling `i ↦ i - s`. -/
def IsArc (A : Finset (Fin n)) : Prop := ∃ s : Fin n, IsInterval (A.image (Equiv.subRight s))

/-- **Interval-to-arc transfer**: every interval of the line is an arc of the ring, cut
at `0`. -/
theorem IsInterval.isArc {A : Finset (Fin n)} (h : IsInterval A) : IsArc A :=
  ⟨0, by simpa [Equiv.subRight] using h⟩

end Arc

end Arealaw
