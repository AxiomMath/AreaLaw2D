import OpenAI.Basic
import OpenAI.Bridges

/-!
# Safe integer rectangles around a cut

The lattice geometry of §3.2 of [OAI265], used by Lemma 3.2 and Proposition 3.3.  An integer
rectangle `Q = [a, b] ⊂ ℤ²` has side lengths `bᵢ + 1 - aᵢ` and size the larger of the two; its
ambient dilation `Q^{+j}` is the rectangle `[a - (j, j), b + (j, j)]`, of size `size Q + 2j`.
Ambient distances are those of the sup metric on `ℤ × ℤ`, so `Q` is safe for a cut `A` exactly
when every site of `Q` is at sup-distance more than `D₀ · size Q` from every endpoint of a
crossing edge.

A nearest-neighbour step moves the sup-distance by one, so a walk of length `k` in the domain
moves it by at most `k`, and a walk from `A` to `Λ \ A` meets an endpoint of a crossing edge no
further along than its own length.  Hence, for `R < D₀`, an admissible support of range `R`
with a site of `A` in a safe rectangle lies wholly in `A`.  A support meeting
`A ∩ T^{+d}` with `T^{+d}` inside a safe rectangle then lies in `A ∩ T^{+(d+R)}`: two contours
`A ∩ T^{+d}` and `A ∩ T^{+d'}` with `d + R ≤ d'` are never split by the same support, and a
support split by `A ∩ T^{+d}` meets the layer `T^{+d} \ T^{+(d-R)}`.  For a rectangle the
layer `Q^{+d} \ Q^{+(d-k)}` has at most `4 k (size Q + 2d)` sites.

## Main statements

* `boxSize_Icc`, `ambientDilation_Icc`, `boxSize_ambientDilation`: sides, dilations and sizes
  of rectangles.
* `isSafe_iff`: safety in pointwise form; `IsSafe.of_le`, `IsSafe.subset`: monotonicity.
* `dist_le_length_of_walk`, `exists_mem_cutEndpoints_dist_le_of_walk`: walks against the sup
  metric and the cut.
* `subset_of_isSafe`, `subset_inter_ambientDilation_of_isSafe`, `not_splits_two_contours`,
  `mem_sdiff_ambientDilation_of_isSafe`: admissible supports near a safe rectangle.
* `card_ambientDilation_sdiff_le`: the boundary-layer count.

## Implementation notes

The ambient sup-distance is Mathlib's `dist` on `ℤ × ℤ` (the product metric is the sup
metric); `dist_eq_max_abs` gives its integer form, so no distance is defined here.

Adapted from TNLean (`LionSR/TNLean`, commit `f4c2d204`, Apache 2.0),
`PEPS/AreaLaw/BufferedRectangles.lean` and `exists_edgeBoundary_of_walk` of
`PEPS/AreaLaw/FiniteDomain.lean`.  TNLean's structure `IntRect`, its sites `Site Λ` and its
`Sym2` edge boundary are replaced by `Finset.Icc a b`, sites `ℤ × ℤ` and the ordered
`edgeBoundary`; its safety condition, a quantified inequality with `D₀ : ℕ`, is our
`ENNReal` inequality `IsSafe` with `D₀ : ℝ`, related by `isSafe_iff`.  The support lemmas hold
for any finite set `T` in place of TNLean's rectangle `Q₀`, need `T^{+d} ⊆ Q` rather than
`T^{+d'} ⊆ Q`, and the layer has width `R` rather than `R + 1`.  TNLean's count of split
supports (`card_crossingTerms_rectRegion_le`) is not ported.
-/

namespace OpenAI

open SimpleGraph
open scoped Pointwise

/-! ## Integer rectangles -/

section Rect

variable {a b : ℤ × ℤ} {Q T : Finset (ℤ × ℤ)}

theorem isIntRect_Icc (h : a ≤ b) : IsIntRect (Finset.Icc a b) := ⟨a, b, h, rfl⟩

theorem IsIntRect.nonempty (hQ : IsIntRect Q) : Q.Nonempty := by
  obtain ⟨a, b, h, rfl⟩ := hQ
  exact Finset.nonempty_Icc.2 h

theorem image_fst_Icc (h : a ≤ b) : (Finset.Icc a b).image Prod.fst = Finset.Icc a.1 b.1 := by
  rw [Finset.Icc_prod_def]
  exact Finset.product_image_fst (Finset.nonempty_Icc.2 h.2)

theorem image_snd_Icc (h : a ≤ b) : (Finset.Icc a b).image Prod.snd = Finset.Icc a.2 b.2 := by
  rw [Finset.Icc_prod_def]
  exact Finset.product_image_snd (Finset.nonempty_Icc.2 h.1)

/-- The size of the rectangle `[a, b]` is its longer side, counted in sites. -/
theorem boxSize_Icc (h : a ≤ b) :
    boxSize (Finset.Icc a b) = max (b.1 + 1 - a.1).toNat (b.2 + 1 - a.2).toNat := by
  rw [boxSize, image_fst_Icc h, image_snd_Icc h, Int.card_Icc, Int.card_Icc]

theorem card_Icc_eq_mul (a b : ℤ × ℤ) :
    (Finset.Icc a b).card = (b.1 + 1 - a.1).toNat * (b.2 + 1 - a.2).toNat := by
  rw [Finset.card_Icc_prod, Int.card_Icc, Int.card_Icc]

theorem boxSize_pos_iff : 0 < boxSize Q ↔ Q.Nonempty := by
  refine ⟨fun h => ?_, fun h => lt_max_of_lt_left (Finset.card_pos.2 (h.image _))⟩
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  simp [boxSize] at h

theorem IsIntRect.one_le_boxSize (hQ : IsIntRect Q) : 1 ≤ boxSize Q :=
  boxSize_pos_iff.2 hQ.nonempty

theorem boxSize_mono (h : Q ⊆ T) : boxSize Q ≤ boxSize T :=
  max_le_max (Finset.card_le_card (Finset.image_subset_image h))
    (Finset.card_le_card (Finset.image_subset_image h))

/-- A set of sites has at most `size Q ^ 2` elements. -/
theorem card_le_boxSize_sq (Q : Finset (ℤ × ℤ)) : Q.card ≤ boxSize Q ^ 2 :=
  (Finset.card_le_card Finset.subset_product).trans <| by
    rw [Finset.card_product, sq]
    exact Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)

/-- Two sites of a rectangle differ by less than its size in each coordinate. -/
theorem IsIntRect.abs_sub_lt_boxSize (hQ : IsIntRect Q) {x y : ℤ × ℤ} (hx : x ∈ Q)
    (hy : y ∈ Q) : |x.1 - y.1| < boxSize Q ∧ |x.2 - y.2| < boxSize Q := by
  obtain ⟨a, b, h, rfl⟩ := hQ
  rw [Finset.mem_Icc] at hx hy
  rw [boxSize_Icc h, abs_lt, abs_lt]
  have := h.1; have := h.2; have := hx.1.1; have := hx.1.2; have := hx.2.1; have := hx.2.2
  have := hy.1.1; have := hy.1.2; have := hy.2.1; have := hy.2.2
  omega

end Rect

/-! ## Ambient dilations -/

section Dilation

variable {a b : ℤ × ℤ} {Q T T' : Finset (ℤ × ℤ)} {j k : ℕ} {x y : ℤ × ℤ}

theorem mem_ambientDilation :
    y ∈ ambientDilation T j ↔ ∃ x ∈ T, |y.1 - x.1| ≤ j ∧ |y.2 - x.2| ≤ j := by
  simp only [ambientDilation, Finset.mem_add, Finset.mem_Icc]
  constructor
  · rintro ⟨x, hx, z, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    refine ⟨x, hx, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, abs_le] <;> omega
  · rintro ⟨x, hx, h1, h2⟩
    rw [abs_le] at h1 h2
    exact ⟨x, hx, y - x, ⟨⟨by simp; omega, by simp; omega⟩, by simp; omega, by simp; omega⟩,
      add_sub_cancel x y⟩

theorem subset_ambientDilation (T : Finset (ℤ × ℤ)) (j : ℕ) : T ⊆ ambientDilation T j :=
  Finset.subset_add_left T (by simp [Finset.mem_Icc, Prod.le_def])

@[simp] theorem ambientDilation_zero (T : Finset (ℤ × ℤ)) : ambientDilation T 0 = T := by
  simp [ambientDilation, Prod.mk_zero_zero, Finset.singleton_zero]

theorem ambientDilation_mono (T : Finset (ℤ × ℤ)) : Monotone (ambientDilation T) :=
  fun j k h => Finset.add_subset_add_left <| Finset.Icc_subset_Icc
    (by simp [Prod.le_def]; omega) (by simp [Prod.le_def]; omega)

theorem ambientDilation_mono_left (h : T ⊆ T') (j : ℕ) :
    ambientDilation T j ⊆ ambientDilation T' j :=
  Finset.add_subset_add_right h

/-- The dilation of the rectangle `[a, b]` by `j` is the rectangle `[a - (j, j), b + (j, j)]`. -/
theorem ambientDilation_Icc (h : a ≤ b) (j : ℕ) :
    ambientDilation (Finset.Icc a b) j = Finset.Icc (a.1 - j, a.2 - j) (b.1 + j, b.2 + j) := by
  ext y
  rw [mem_ambientDilation, Finset.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
  have := h.1; have := h.2
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    rw [Finset.mem_Icc] at hx
    rw [abs_le] at h1 h2
    have := hx.1.1; have := hx.1.2; have := hx.2.1; have := hx.2.2
    omega
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨(max a.1 (min b.1 y.1), max a.2 (min b.2 y.2)), ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
      omega
    · rw [abs_le]; omega
    · rw [abs_le]; omega

theorem isIntRect_ambientDilation (hQ : IsIntRect Q) (j : ℕ) :
    IsIntRect (ambientDilation Q j) := by
  obtain ⟨a, b, h, rfl⟩ := hQ
  rw [ambientDilation_Icc h]
  exact isIntRect_Icc (Prod.mk_le_mk.2 ⟨by have := h.1; omega, by have := h.2; omega⟩)

theorem ambientDilation_ambientDilation (T : Finset (ℤ × ℤ)) (j k : ℕ) :
    ambientDilation (ambientDilation T j) k = ambientDilation T (j + k) := by
  have hj : (-(j : ℤ), -(j : ℤ)) ≤ ((j : ℤ), (j : ℤ)) := Prod.mk_le_mk.2 ⟨by omega, by omega⟩
  have hbox : Finset.Icc (-(j : ℤ), -(j : ℤ)) ((j : ℤ), (j : ℤ)) +
      Finset.Icc (-(k : ℤ), -(k : ℤ)) ((k : ℤ), (k : ℤ)) =
        Finset.Icc (-((j + k : ℕ) : ℤ), -((j + k : ℕ) : ℤ))
          (((j + k : ℕ) : ℤ), ((j + k : ℕ) : ℤ)) := by
    have := ambientDilation_Icc hj k
    rw [ambientDilation] at this
    rw [this]
    push_cast
    ring_nf
  rw [ambientDilation, ambientDilation, add_assoc, hbox, ambientDilation]

/-- A site at sup-distance at most `k` from `T^{+j}` lies in `T^{+(j+k)}`. -/
theorem mem_ambientDilation_add (hy : y ∈ ambientDilation T j) {y' : ℤ × ℤ}
    (h1 : |y'.1 - y.1| ≤ k) (h2 : |y'.2 - y.2| ≤ k) : y' ∈ ambientDilation T (j + k) := by
  rw [← ambientDilation_ambientDilation]
  exact mem_ambientDilation.2 ⟨y, hy, h1, h2⟩

/-- The size of a rectangle grows by `2j` under dilation by `j`. -/
theorem IsIntRect.boxSize_ambientDilation (hQ : IsIntRect Q) (j : ℕ) :
    boxSize (ambientDilation Q j) = boxSize Q + 2 * j := by
  obtain ⟨a, b, h, rfl⟩ := hQ
  have h' : (a.1 - j, a.2 - j) ≤ (b.1 + j, b.2 + j) :=
    Prod.mk_le_mk.2 ⟨by have := h.1; omega, by have := h.2; omega⟩
  rw [ambientDilation_Icc h, boxSize_Icc h', boxSize_Icc h]
  have := h.1; have := h.2
  simp only
  omega

/-- **Boundary layer.**  For `k ≤ d` the layer `Q^{+d} \ Q^{+(d-k)}` of a rectangle has at most
`4 k (size Q + 2d)` sites. -/
theorem IsIntRect.card_ambientDilation_sdiff_le (hQ : IsIntRect Q) {d k : ℕ} (hk : k ≤ d) :
    (ambientDilation Q d \ ambientDilation Q (d - k)).card ≤ 4 * k * (boxSize Q + 2 * d) := by
  rw [Finset.card_sdiff_of_subset (ambientDilation_mono Q (Nat.sub_le d k))]
  obtain ⟨a, b, h, rfl⟩ := hQ
  rw [ambientDilation_Icc h, ambientDilation_Icc h, card_Icc_eq_mul, card_Icc_eq_mul,
    boxSize_Icc h]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel]
  have := h.1; have := h.2
  set w := (b.1 + 1 - a.1).toNat
  set v := (b.2 + 1 - a.2).toNat
  have e1 : (b.1 + ((e + k : ℕ) : ℤ) + 1 - (a.1 - ((e + k : ℕ) : ℤ))).toNat =
      w + 2 * e + 2 * k := by
    omega
  have e2 : (b.2 + ((e + k : ℕ) : ℤ) + 1 - (a.2 - ((e + k : ℕ) : ℤ))).toNat =
      v + 2 * e + 2 * k := by
    omega
  have e3 : (b.1 + (e : ℤ) + 1 - (a.1 - (e : ℤ))).toNat = w + 2 * e := by omega
  have e4 : (b.2 + (e : ℤ) + 1 - (a.2 - (e : ℤ))).toNat = v + 2 * e := by omega
  simp only
  rw [e1, e2, e3, e4, Nat.sub_le_iff_le_add]
  have hw : w ≤ max w v := le_max_left _ _
  have hv : v ≤ max w v := le_max_right _ _
  nlinarith

end Dilation

/-! ## The sup metric and the lattice graph -/

section Metric

variable {Λ A X : Finset (ℤ × ℤ)} {R : ℕ} {x y : ℤ × ℤ}

/-- The ambient distance on `ℤ × ℤ` is the sup-distance of the coordinates. -/
theorem dist_eq_max_abs (x y : ℤ × ℤ) :
    dist x y = ((max |x.1 - y.1| |x.2 - y.2| : ℤ) : ℝ) := by
  rw [Prod.dist_eq, Int.dist_eq, Int.dist_eq]
  push_cast
  rfl

theorem dist_le_natCast_iff {k : ℕ} :
    dist x y ≤ k ↔ |x.1 - y.1| ≤ k ∧ |x.2 - y.2| ≤ k := by
  rw [dist_eq_max_abs, ← Int.cast_natCast (R := ℝ), Int.cast_le, max_le_iff]

/-- Adjacent sites of the square lattice are at sup-distance one. -/
theorem dist_eq_one_of_adj (h : (hasse ℤ □ hasse ℤ).Adj x y) : dist x y = 1 := by
  rw [squareLattice_adj_iff] at h
  rw [dist_eq_max_abs, Int.cast_eq_one]
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp [h1, ← h2]

/-- A walk of length `k` in an induced subgraph of the square lattice moves the sup-distance by
at most `k`. -/
theorem dist_le_length_of_walk {s : Set (ℤ × ℤ)} {u v : s}
    (p : ((hasse ℤ □ hasse ℤ).induce s).Walk u v) : dist (u : ℤ × ℤ) v ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Nat.cast_add_one, add_comm]
    exact (dist_triangle _ _ _).trans
      (add_le_add (dist_eq_one_of_adj (induce_adj.1 h)).le ih)

theorem dist_le_of_domainEDist_le {k : ℕ} (h : domainEDist Λ x y ≤ k) : dist x y ≤ k := by
  by_cases hxy : x ∈ Λ ∧ y ∈ Λ
  · rw [domainEDist, dif_pos hxy] at h
    obtain ⟨p, hp⟩ := (exists_walk_length_le_iff_edist_le _).2 h
    exact (dist_le_length_of_walk p).trans (by exact_mod_cast hp)
  · rw [domainEDist, dif_neg hxy] at h
    exact absurd h (by simp)

/-- Two sites of an admissible support of range `R` are at sup-distance at most `R`. -/
theorem dist_le_of_mem_supports (hX : X ∈ supports Λ R) (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ R :=
  dist_le_of_domainEDist_le (domainEDiam_le_iff.1 (mem_supports_iff.1 hX).2.2 x hx y hy)

/-- A walk in the induced graph on `Λ` from a site of `A` to a site off `A` crosses an edge
`(u, v)` of the cut `∂_Λ A`, and its initial segment reaches `u` in at most as many steps. -/
theorem exists_edgeBoundary_of_walk {u v : (Λ : Set (ℤ × ℤ))}
    (p : ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).Walk u v) (hu : (u : ℤ × ℤ) ∈ A)
    (hv : (v : ℤ × ℤ) ∉ A) :
    ∃ u' v' : (Λ : Set (ℤ × ℤ)), ((u' : ℤ × ℤ), (v' : ℤ × ℤ)) ∈ edgeBoundary Λ A ∧
      ∃ p' : ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).Walk u u', p'.length ≤ p.length := by
  classical
  obtain ⟨d, hd, h1, h2⟩ := p.exists_boundary_dart {z | (z : ℤ × ℤ) ∈ A} hu hv
  have hs := p.dart_fst_mem_support_of_mem_darts hd
  exact ⟨d.fst, d.snd, mem_edgeBoundary.2 ⟨h1, Finset.mem_sdiff.2 ⟨d.snd.2, h2⟩,
    induce_adj.1 d.adj⟩, p.takeUntil _ hs, p.length_takeUntil_le_length hs⟩

/-- A walk in the induced graph on `Λ` from a site of `A` to a site off `A` passes within its
length, in sup-distance, of an endpoint of a crossing edge. -/
theorem exists_mem_cutEndpoints_dist_le_of_walk {u v : (Λ : Set (ℤ × ℤ))}
    (p : ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).Walk u v) (hu : (u : ℤ × ℤ) ∈ A)
    (hv : (v : ℤ × ℤ) ∉ A) :
    ∃ z ∈ cutEndpoints Λ A, dist (u : ℤ × ℤ) z ≤ p.length := by
  obtain ⟨u', v', he, p', hp'⟩ := exists_edgeBoundary_of_walk p hu hv
  exact ⟨u', Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst he),
    (dist_le_length_of_walk p').trans (by exact_mod_cast hp')⟩

end Metric

/-! ## Ambient distances and safety -/

section Safety

variable {D₀ D₀' : ℝ} {Λ A Q Q' T Z X : Finset (ℤ × ℤ)} {R : ℕ}

theorem ambientEDist_eq_inf (T Z : Finset (ℤ × ℤ)) :
    ambientEDist T Z = T.inf fun x => Z.inf fun z => edist x z := by
  simp only [ambientEDist, Metric.infEDist, Finset.inf_eq_iInf, Finset.mem_coe]

theorem le_ambientEDist_iff {c : ENNReal} :
    c ≤ ambientEDist T Z ↔ ∀ x ∈ T, ∀ z ∈ Z, c ≤ edist x z := by
  simp only [ambientEDist_eq_inf, Finset.le_inf_iff]

theorem lt_ambientEDist_iff {c : ENNReal} (hc : c < ⊤) :
    c < ambientEDist T Z ↔ ∀ x ∈ T, ∀ z ∈ Z, c < edist x z := by
  simp only [ambientEDist_eq_inf, Finset.lt_inf_iff hc]

@[simp] theorem ambientEDist_empty_right (T : Finset (ℤ × ℤ)) : ambientEDist T ∅ = ⊤ := by
  simp [ambientEDist_eq_inf]

theorem ambientEDist_anti_left (h : T ⊆ Q) (Z : Finset (ℤ × ℤ)) :
    ambientEDist Q Z ≤ ambientEDist T Z := by
  rw [ambientEDist_eq_inf, ambientEDist_eq_inf]
  exact Finset.inf_mono h

theorem IsSafe.lt_dist (hs : IsSafe D₀ Λ A Q) {x z : ℤ × ℤ} (hx : x ∈ Q)
    (hz : z ∈ cutEndpoints Λ A) : D₀ * boxSize Q < dist x z := by
  have := (lt_ambientEDist_iff ENNReal.ofReal_lt_top).1 hs x hx z hz
  rw [edist_dist] at this
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1

/-- **Safety, pointwise.**  For `D₀ ≥ 0`, a set `Q` is safe for the cut `A` iff every site of
`Q` is at sup-distance more than `D₀ · size Q` from every endpoint of a crossing edge.  For
`D₀ < 0` the right-hand side admits a crossing endpoint inside `Q`, which `IsSafe` excludes. -/
theorem isSafe_iff (hD₀ : 0 ≤ D₀) :
    IsSafe D₀ Λ A Q ↔ ∀ x ∈ Q, ∀ z ∈ cutEndpoints Λ A, D₀ * boxSize Q < dist x z := by
  refine ⟨fun hs x hx z hz => hs.lt_dist hx hz, fun h => ?_⟩
  refine (lt_ambientEDist_iff ENNReal.ofReal_lt_top).2 fun x hx z hz => ?_
  have hxz := h x hx z hz
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff']
  exact ⟨hxz, (mul_nonneg hD₀ (Nat.cast_nonneg _)).trans_lt hxz⟩

theorem isSafe_of_edgeBoundary_eq_empty (h : edgeBoundary Λ A = ∅) : IsSafe D₀ Λ A Q := by
  simp [IsSafe, cutEndpoints, h]

/-- Safety for `D₀` implies safety for every smaller `D₀'`. -/
theorem IsSafe.of_le (hs : IsSafe D₀ Λ A Q) (hD : D₀' ≤ D₀) : IsSafe D₀' Λ A Q :=
  (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg _))).trans_lt hs

/-- A subset of a safe set is safe, for `D₀ ≥ 0`. -/
theorem IsSafe.subset (hs : IsSafe D₀ Λ A Q) (hD₀ : 0 ≤ D₀) (h : Q' ⊆ Q) : IsSafe D₀ Λ A Q' :=
  ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Nat.cast_le.2 (boxSize_mono h)) hD₀)).trans_lt hs).trans_le (ambientEDist_anti_left h _)

/-! ### Admissible supports near a safe set -/

/-- **Supports near a safe set stay in the cut.**  If `Q` is safe and `R < D₀`, an admissible
support of range `R` with a site of `A` in `Q` lies in `A`: otherwise a walk of length at most
`R` from that site leaves `A` and passes within sup-distance `R` of an endpoint of a crossing
edge. -/
theorem subset_of_isSafe (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀) (hX : X ∈ supports Λ R)
    {v : ℤ × ℤ} (hvX : v ∈ X) (hvA : v ∈ A) (hvQ : v ∈ Q) : X ⊆ A := by
  intro w hwX
  by_contra hwA
  obtain ⟨hXΛ, -, hw⟩ := mem_supports_iff_walk.1 hX
  obtain ⟨p, hp⟩ := hw v hvX w hwX
  obtain ⟨z, hz, hdist⟩ := exists_mem_cutEndpoints_dist_le_of_walk p hvA hwA
  have hlt := hs.lt_dist hvQ hz
  have hsize : (1 : ℝ) ≤ boxSize Q := by exact_mod_cast boxSize_pos_iff.2 ⟨v, hvQ⟩
  have hD₀ : 0 < D₀ := (Nat.cast_nonneg R).trans_lt hR
  have hlen : (p.length : ℝ) ≤ R := by exact_mod_cast hp
  nlinarith

/-- **A support meeting a contour stays within range of it.**  If `T^{+d}` lies in a safe set
`Q` and `R < D₀`, an admissible support of range `R` meeting `A ∩ T^{+d}` lies in
`A ∩ T^{+d'}` for every `d' ≥ d + R`. -/
theorem subset_inter_ambientDilation_of_isSafe (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀)
    {d d' : ℕ} (hdd : d + R ≤ d') (hQ : ambientDilation T d ⊆ Q) (hX : X ∈ supports Λ R)
    {v : ℤ × ℤ} (hvX : v ∈ X) (hv : v ∈ A ∩ ambientDilation T d) :
    X ⊆ A ∩ ambientDilation T d' := by
  rw [Finset.mem_inter] at hv
  intro w hwX
  refine Finset.mem_inter.2 ⟨subset_of_isSafe hs hR hX hvX hv.1 (hQ hv.2) hwX, ?_⟩
  obtain ⟨h1, h2⟩ := dist_le_natCast_iff.1 (dist_le_of_mem_supports hX hwX hvX)
  exact ambientDilation_mono T hdd (mem_ambientDilation_add hv.2 h1 h2)

/-- **Single split.**  If `T^{+d}` lies in a safe set, `R < D₀` and `d + R ≤ d'`, no admissible
support of range `R` is split by both contours `A ∩ T^{+d}` and `A ∩ T^{+d'}`: one meeting the
first lies inside the second. -/
theorem not_splits_two_contours (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀) {d d' : ℕ}
    (hdd : d + R ≤ d') (hQ : ambientDilation T d ⊆ Q) (hX : X ∈ supports Λ R) {v w : ℤ × ℤ}
    (hvX : v ∈ X) (hv : v ∈ A ∩ ambientDilation T d) (hwX : w ∈ X)
    (hw : w ∉ A ∩ ambientDilation T d') : False :=
  hw (subset_inter_ambientDilation_of_isSafe hs hR hdd hQ hX hvX hv hwX)

/-- **Split supports meet the boundary layer.**  If `T^{+d}` lies in a safe set and `R < D₀`, an
admissible support of range `R` split by `A ∩ T^{+d}` has its sites in `A ∩ T^{+d}` in the layer
`T^{+d} \ T^{+k}`, for every `k ≤ d - R`. -/
theorem mem_sdiff_ambientDilation_of_isSafe (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀)
    {d k : ℕ} (hk : k + R ≤ d) (hQ : ambientDilation T d ⊆ Q) (hX : X ∈ supports Λ R)
    {v w : ℤ × ℤ} (hvX : v ∈ X) (hv : v ∈ A ∩ ambientDilation T d) (hwX : w ∈ X)
    (hw : w ∉ A ∩ ambientDilation T d) : v ∈ ambientDilation T d \ ambientDilation T k := by
  refine Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hv).2, fun hvk => ?_⟩
  have hvk' : v ∈ A ∩ ambientDilation T k := Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hv).1, hvk⟩
  exact not_splits_two_contours hs hR hk ((ambientDilation_mono T (by omega)).trans hQ) hX hvX
    hvk' hwX hw

end Safety

end OpenAI
