import Mathlib.Algebra.Order.Floor.Div
import OpenAI.Rectangles

/-!
# Partitioning a rectangle into chunks

Cut each axis of an integer rectangle `Q = [a, b]` into chunks of `r` sites, the last chunk
being shorter if `r` does not divide the side length.  A side of `w` sites has `⌈w / r⌉`
chunks.  The products of the chunks are the children of `Q`: rectangles of size at most `r`,
pairwise disjoint, covering `Q`.  If `size Q ≤ M r` there are at most `M` chunks along each
axis.  A child whose padding `Q₀^{+C r}` meets another child is within `C` chunk positions of
it along each axis, and a child at least `C` positions from the first chunk and `C + 2` from
the last one along both axes has its padding inside `Q`.  Children of a safe rectangle are
safe.  This is the decomposition of a safe parent in the scale recurrence of Proposition 3.3.

## Main definitions

* `OpenAI.numChunksX`, `OpenAI.numChunksY`: the number of chunks along each axis.
* `OpenAI.rectChild`: the child at chunk position `(i, j)`.

## Main statements

* `OpenAI.numChunksX_le`, `OpenAI.numChunksY_le`: at most `M` chunks per axis.
* `OpenAI.isIntRect_rectChild`, `OpenAI.boxSize_rectChild_le`, `OpenAI.rectChild_subset`:
  children are rectangles of size at most `r` inside the parent.
* `OpenAI.biUnion_rectChild`, `OpenAI.disjoint_rectChild`: the children partition the parent.
* `OpenAI.le_add_of_mem_rectChild_of_mem_ambientDilation`: padded children meet only nearby
  children.
* `OpenAI.ambientDilation_rectChild_subset`: interior children have their padding inside the
  parent.

## Implementation notes

The child at a position is defined for every `(i, j) : ℕ × ℕ`, empty outside the grid, so its
membership and containment lemmas carry no side condition on the position; only
`isIntRect_rectChild` and the covering need the position, or every site, to be on the grid.
`rectChild` is `noncomputable` because the interval `Finset.Icc` on `ℤ × ℤ` is built from a
classical order instance.

Ported from TNLean (`LionSR/TNLean`, commit `f4c2d204`, Apache 2.0),
`TNLean/PEPS/AreaLaw/SafeBoxChildren.lean`.  TNLean's structure `IntRect` becomes
`Finset.Icc a b`, its `dilate` our `ambientDilation`, and its `size` our `boxSize`.  TNLean
counts `(w - 1) / r + 1` chunks of a side of `w ≥ 1` sites and clamps an off-grid child to a
one-site rectangle; we count `w ⌈/⌉ r`, equal for `w ≥ 1` and `r ≥ 1`, and let off-grid
children be empty.  TNLean's `width`, `height` and `size_le_of_subset` are `boxSize_Icc` and
`boxSize_mono` here, and its `IsSafe.mono` is `IsSafe.subset`, which needs `D₀ ≥ 0` because our
`D₀` is real.  The covering and disjointness statements `biUnion_rectChild` and
`disjoint_rectChild` are new, as is `isIntRect_rectChild`, needed since being a rectangle is a
property of a `Finset` here rather than a type.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.3, proof of Proposition 3.3.
-/

namespace OpenAI

/-! ## Chunks -/

section Chunks

variable (a b : ℤ × ℤ) (r : ℕ)

/-- The number of horizontal chunks of `r` sites of the rectangle `[a, b]`: `⌈w / r⌉` for a side
of `w` sites. -/
def numChunksX : ℕ := (b.1 + 1 - a.1).toNat ⌈/⌉ r

/-- The number of vertical chunks of `r` sites of the rectangle `[a, b]`. -/
def numChunksY : ℕ := (b.2 + 1 - a.2).toNat ⌈/⌉ r

/-- The child of `[a, b]` at chunk position `(i, j)`: the product of the `i`-th horizontal and
the `j`-th vertical chunk of `r` sites, the last chunks being cut off by `[a, b]`. -/
noncomputable def rectChild (i j : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (a.1 + i * r, a.2 + j * r)
    (min (a.1 + i * r + r - 1) b.1, min (a.2 + j * r + r - 1) b.2)

variable {a b r} {i j i' j' M C : ℕ} {p : ℤ × ℤ}

/-- A position `i` is on a grid of `w ⌈/⌉ r` chunks iff its chunk starts before offset `w`. -/
theorem lt_ceilDiv_iff (hr : 1 ≤ r) {w : ℕ} : i < w ⌈/⌉ r ↔ i * r < w := by
  rw [← not_le, ceilDiv_le_iff_le_mul (by omega), not_le, mul_comm]

theorem lt_numChunksX_iff (hr : 1 ≤ r) : i < numChunksX a b r ↔ a.1 + i * r ≤ b.1 := by
  rw [numChunksX, lt_ceilDiv_iff hr]
  omega

theorem lt_numChunksY_iff (hr : 1 ≤ r) : j < numChunksY a b r ↔ a.2 + j * r ≤ b.2 := by
  rw [numChunksY, lt_ceilDiv_iff hr]
  omega

/-- A side of at most `M r` sites has at most `M` chunks of `r` sites. -/
theorem ceilDiv_le_of_le_mul (hr : 1 ≤ r) {w : ℕ} (hw : w ≤ M * r) : w ⌈/⌉ r ≤ M := by
  rw [ceilDiv_le_iff_le_mul (by omega), mul_comm]
  exact hw

theorem numChunksX_le (hab : a ≤ b) (hr : 1 ≤ r) (hQ : boxSize (Finset.Icc a b) ≤ M * r) :
    numChunksX a b r ≤ M := by
  rw [boxSize_Icc hab] at hQ
  exact ceilDiv_le_of_le_mul hr ((le_max_left _ _).trans hQ)

theorem numChunksY_le (hab : a ≤ b) (hr : 1 ≤ r) (hQ : boxSize (Finset.Icc a b) ≤ M * r) :
    numChunksY a b r ≤ M := by
  rw [boxSize_Icc hab] at hQ
  exact ceilDiv_le_of_le_mul hr ((le_max_right _ _).trans hQ)

theorem mem_rectChild :
    p ∈ rectChild a b r i j ↔
      a.1 + i * r ≤ p.1 ∧ p.1 < a.1 + i * r + r ∧ p.1 ≤ b.1 ∧
        a.2 + j * r ≤ p.2 ∧ p.2 < a.2 + j * r + r ∧ p.2 ≤ b.2 := by
  simp only [rectChild, Finset.mem_Icc, Prod.le_def, le_min_iff]
  omega

/-- Children lie in the parent. -/
theorem rectChild_subset : rectChild a b r i j ⊆ Finset.Icc a b := by
  intro p hp
  rw [mem_rectChild] at hp
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
  have : (0 : ℤ) ≤ i * r := by positivity
  have : (0 : ℤ) ≤ j * r := by positivity
  omega

/-- A child at a position on the grid is a rectangle. -/
theorem isIntRect_rectChild (hr : 1 ≤ r) (hi : i < numChunksX a b r)
    (hj : j < numChunksY a b r) : IsIntRect (rectChild a b r i j) := by
  rw [lt_numChunksX_iff hr] at hi
  rw [lt_numChunksY_iff hr] at hj
  refine isIntRect_Icc (Prod.le_def.2 ⟨le_min ?_ hi, le_min ?_ hj⟩) <;> simp only <;> omega

/-- Children have size at most `r`. -/
theorem boxSize_rectChild_le : boxSize (rectChild a b r i j) ≤ r := by
  by_cases h : (a.1 + i * r, a.2 + j * r) ≤
      (min (a.1 + i * r + r - 1) b.1, min (a.2 + j * r + r - 1) b.2)
  · rw [rectChild, boxSize_Icc h]
    simp only
    omega
  · rw [rectChild, Finset.Icc_eq_empty h]
    simp [boxSize]

/-- Every site of the parent lies in the child at its chunk position. -/
theorem exists_mem_rectChild (hr : 1 ≤ r) (hp : p ∈ Finset.Icc a b) :
    ∃ i < numChunksX a b r, ∃ j < numChunksY a b r, p ∈ rectChild a b r i j := by
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def] at hp
  set s := (p.1 - a.1).toNat
  set t := (p.2 - a.2).toNat
  have h1 : ((s / r : ℕ) : ℤ) * r ≤ s := by exact_mod_cast Nat.div_mul_le_self s r
  have h2 : (s : ℤ) < ((s / r : ℕ) : ℤ) * r + r := by
    exact_mod_cast Nat.lt_div_mul_add (a := s) (b := r) (by omega)
  have h3 : ((t / r : ℕ) : ℤ) * r ≤ t := by exact_mod_cast Nat.div_mul_le_self t r
  have h4 : (t : ℤ) < ((t / r : ℕ) : ℤ) * r + r := by
    exact_mod_cast Nat.lt_div_mul_add (a := t) (b := r) (by omega)
  have hs : (s : ℤ) = p.1 - a.1 := by omega
  have ht : (t : ℤ) = p.2 - a.2 := by omega
  refine ⟨s / r, (lt_numChunksX_iff hr).2 (by omega), t / r, (lt_numChunksY_iff hr).2 (by omega),
    mem_rectChild.2 (by omega)⟩

/-- A site in two children determines the chunk position. -/
theorem eq_of_mem_rectChild (hp : p ∈ rectChild a b r i j) (hp' : p ∈ rectChild a b r i' j') :
    i = i' ∧ j = j' := by
  rw [mem_rectChild] at hp hp'
  have key : ∀ {k k' : ℕ} {x : ℤ}, (k : ℤ) * r ≤ x → x < k * r + r → (k' : ℤ) * r ≤ x →
      x < k' * r + r → k = k' := by
    intro k k' x h1 h2 h3 h4
    have hk : (k : ℤ) * r < (k' + 1) * r := by linarith
    have hk' : (k' : ℤ) * r < (k + 1) * r := by linarith
    have := lt_of_mul_lt_mul_right hk (Nat.cast_nonneg r)
    have := lt_of_mul_lt_mul_right hk' (Nat.cast_nonneg r)
    omega
  exact ⟨key (x := p.1 - a.1) (by linarith) (by linarith) (by linarith) (by linarith),
    key (x := p.2 - a.2) (by linarith) (by linarith) (by linarith) (by linarith)⟩

/-- Children at distinct positions are disjoint. -/
theorem disjoint_rectChild (h : (i, j) ≠ (i', j')) :
    Disjoint (rectChild a b r i j) (rectChild a b r i' j') :=
  Finset.disjoint_left.2 fun _ hp hp' => h <| by
    obtain ⟨rfl, rfl⟩ := eq_of_mem_rectChild hp hp'
    rfl

/-- **The children cover the parent.** -/
theorem biUnion_rectChild (hr : 1 ≤ r) :
    (Finset.range (numChunksX a b r) ×ˢ Finset.range (numChunksY a b r)).biUnion
      (fun ij => rectChild a b r ij.1 ij.2) = Finset.Icc a b := by
  refine subset_antisymm (Finset.biUnion_subset.2 fun _ _ => rectChild_subset) fun p hp => ?_
  obtain ⟨i, hi, j, hj, h⟩ := exists_mem_rectChild hr hp
  exact Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_product.2
    ⟨Finset.mem_range.2 hi, Finset.mem_range.2 hj⟩, h⟩

/-- **Neighbours of a padded child.**  If a site of the child at `(i', j')` lies in the padding
`C r` of the child at `(i, j)`, the positions differ by at most `C` along each axis. -/
theorem le_add_of_mem_rectChild_of_mem_ambientDilation (hp : p ∈ rectChild a b r i' j')
    (hp' : p ∈ ambientDilation (rectChild a b r i j) (C * r)) :
    i' ≤ i + C ∧ i ≤ i' + C ∧ j' ≤ j + C ∧ j ≤ j' + C := by
  obtain ⟨x, hx, h1, h2⟩ := mem_ambientDilation.1 hp'
  rw [mem_rectChild] at hp hx
  rw [abs_le] at h1 h2
  push_cast at h1 h2
  have key : ∀ {k k' : ℕ} {y z : ℤ}, (k : ℤ) * r ≤ y → y < k * r + r → (k' : ℤ) * r ≤ z →
      z < k' * r + r → y - z ≤ C * r → k ≤ k' + C := by
    intro k k' y z h1 h2 h3 h4 h5
    have hk : (k : ℤ) * r < (k' + C + 1) * r := by linarith
    have := lt_of_mul_lt_mul_right hk (Nat.cast_nonneg r)
    omega
  exact ⟨key (y := p.1 - a.1) (z := x.1 - a.1) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith),
    key (y := x.1 - a.1) (z := p.1 - a.1) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith),
    key (y := p.2 - a.2) (z := x.2 - a.2) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith),
    key (y := x.2 - a.2) (z := p.2 - a.2) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)⟩

/-- **Interior children.**  A child at least `C` chunk positions from the first chunk and
`C + 2` from the last one along both axes has its padding `C r` inside the parent. -/
theorem ambientDilation_rectChild_subset (hr : 1 ≤ r) (hi : i + C + 2 ≤ numChunksX a b r)
    (hj : j + C + 2 ≤ numChunksY a b r) (hiC : C ≤ i) (hjC : C ≤ j) :
    ambientDilation (rectChild a b r i j) (C * r) ⊆ Finset.Icc a b := by
  intro p hp
  obtain ⟨x, hx, h1, h2⟩ := mem_ambientDilation.1 hp
  rw [mem_rectChild] at hx
  rw [abs_le] at h1 h2
  push_cast at h1 h2
  have hx1 := (lt_numChunksX_iff hr).1 (show i + C + 1 < numChunksX a b r by omega)
  have hy1 := (lt_numChunksY_iff hr).1 (show j + C + 1 < numChunksY a b r by omega)
  push_cast at hx1 hy1
  have hCi : (C : ℤ) * r ≤ i * r := by exact_mod_cast Nat.mul_le_mul_right r hiC
  have hCj : (C : ℤ) * r ≤ j * r := by exact_mod_cast Nat.mul_le_mul_right r hjC
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- Children of a safe rectangle are safe, for `D₀ ≥ 0`. -/
theorem IsSafe.rectChild {D₀ : ℝ} {Λ A : Finset (ℤ × ℤ)} (hs : IsSafe D₀ Λ A (Finset.Icc a b))
    (hD₀ : 0 ≤ D₀) : IsSafe D₀ Λ A (rectChild a b r i j) :=
  hs.subset hD₀ rectChild_subset

end Chunks

end OpenAI
