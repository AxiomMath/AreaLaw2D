import OpenAI.Geometry.CappedDyadicPartition
import OpenAI.Geometry.QuotientIntervals
import OpenAI.Geometry.TemplateCollar

/-!
# Mixed dyadic squares of a template

A set of lattice sites has *Lipschitz rows* if, from any of its sites `p`, every row between `p`
and another site carries a site at horizontal distance at most the vertical distance to `p`.
The lattice points of a template piece have Lipschitz rows, and the property survives integer
sup-norm dilation.  For a set whose rows are integer intervals, with Lipschitz rows and
coordinates varying by at most `m`, the dyadic squares of side `u` meeting the set and its
complement number `O((m + u) / u)` [OAI265, eq. (9.11)]: inside a row band of `u` consecutive
rows all meeting the set, both row endpoints move by less than `u`, so a mixed square of the band
lies within three square columns of an endpoint of the band's first row, and only the two bands
holding the extreme rows can contain a row missing the set.  Summing over the pieces bounds the
mixed squares of a template and of its dilations.

## Main definitions

* `OpenAI.HasLipschitzRows`: the row condition above.

## Main statements

* `OpenAI.IsOctagonallyConvex.hasLipschitzRows`, `OpenAI.HasLipschitzRows.ambientDilation`.
* `OpenAI.card_mixedDyadicIndices_le`: the mixed-square count of one set.
* `OpenAI.IsTemplate.card_mixedDyadicIndices_ambientDilation_le`: the count for a dilated
  template.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §9.3, proof of Lemma 9.4.
-/

open OpenAI.Geometry

namespace OpenAI

/-- A set of sites has *Lipschitz rows* if for every site `p`, every row `z` between the rows of
`p` and of another site, and every `d ≥ |z - p.2|`, the row `z` has a site at horizontal
distance at most `d` from `p`. -/
def HasLipschitzRows (D : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ D, ∀ r ∈ D, ∀ z d : ℤ, min p.2 r.2 ≤ z → z ≤ max p.2 r.2 → z - d ≤ p.2 → p.2 ≤ z + d →
    ∃ w, (w, z) ∈ D ∧ p.1 - d ≤ w ∧ w ≤ p.1 + d

/-- An octagonally convex set meets every horizontal line between two of its sites. -/
theorem IsOctagonallyConvex.exists_snd_eq {Q : Set (ℤ × ℤ)} (hQ : IsOctagonallyConvex Q)
    {p r : ℤ × ℤ} (hp : p ∈ Q) (hr : r ∈ Q) {t : ℤ} (h₁ : min p.2 r.2 ≤ t)
    (h₂ : t ≤ max p.2 r.2) : ∃ w, (w, t) ∈ Q := by
  have hQ' := hQ.preimage_swap
  rcases le_total p.2 r.2 with h | h
  · obtain ⟨q, hq, hqt, -⟩ := hQ'.exists_fst_eq (p := p.swap) (r := r.swap)
      (by simpa using hp) (by simpa using hr) (t := t) (by simp; omega) (by simp; omega)
    exact ⟨q.2, by rw [← hqt]; exact hq⟩
  · obtain ⟨q, hq, hqt, -⟩ := hQ'.exists_fst_eq (p := r.swap) (r := p.swap)
      (by simpa using hr) (by simpa using hp) (t := t) (by simp; omega) (by simp; omega)
    exact ⟨q.2, by rw [← hqt]; exact hq⟩

/-- An octagonally convex set has Lipschitz rows: clamp a site of the target row into the
window `[p.1 - d, p.1 + d]`. -/
theorem IsOctagonallyConvex.hasLipschitzRows {Q : Set (ℤ × ℤ)} (hQ : IsOctagonallyConvex Q) :
    HasLipschitzRows Q := by
  intro p hp r hr z d h₁ h₂ h₃ h₄
  obtain ⟨a, ha⟩ := hQ.exists_snd_eq hp hr h₁ h₂
  refine ⟨max (p.1 - d) (min a (p.1 + d)), ?_, by omega, by omega⟩
  exact hQ p hp (a, z) ha _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega)

/-- Integer sup-norm dilation preserves Lipschitz rows. -/
theorem HasLipschitzRows.ambientDilation {Q : Finset (ℤ × ℤ)}
    (hQ : HasLipschitzRows (Q : Set (ℤ × ℤ))) (j : ℕ) :
    HasLipschitzRows (ambientDilation Q j : Set (ℤ × ℤ)) := by
  intro p hp r hr z d h₁ h₂ h₃ h₄
  obtain ⟨s, hs, hs₁, hs₂⟩ := mem_ambientDilation.1 (Finset.mem_coe.1 hp)
  obtain ⟨t, ht, ht₁, ht₂⟩ := mem_ambientDilation.1 (Finset.mem_coe.1 hr)
  rw [abs_le] at hs₁ hs₂ ht₁ ht₂
  obtain ⟨a, ha, ha₁, ha₂⟩ := hQ s hs t ht (max (z - j) (min s.2 (z + j))) d (by omega)
    (by omega) (by omega) (by omega)
  refine ⟨max (a - j) (min p.1 (a + j)), mem_ambientDilation.2 ⟨_, ha, ?_, ?_⟩, by omega,
    by omega⟩ <;> rw [abs_le] <;> dsimp only <;> omega

private theorem mem_Icc_ediv_of_mul {a u z : ℤ} (hu : 0 < u) (h₁ : a - 2 * u ≤ z * u)
    (h₂ : z * u ≤ a + 2 * u) : z ∈ Finset.Icc (a / u - 3) (a / u + 3) := by
  have hlo := Int.ediv_mul_le a (ne_of_gt hu)
  have hhi := Int.lt_ediv_add_one_mul_self a hu
  rw [Finset.mem_Icc]
  constructor
  · by_contra hz
    have : z + 3 ≤ a / u := by omega
    nlinarith
  · by_contra hz
    have : a / u + 4 ≤ z := by omega
    nlinarith

/-- **Mixed squares of a set with interval rows and Lipschitz rows** [OAI265, eq. (9.11)].  If
the rows of `D` are integer intervals, `D` has Lipschitz rows and its coordinates vary by at
most `m`, then at most `16 (m + 2u) / u` dyadic squares of side `u = 2^k` meet both `D` and its
complement. -/
theorem card_mixedDyadicIndices_le {D : Finset (ℤ × ℤ)}
    (hrow : ∀ x ∈ D, ∀ x' ∈ D, x.2 = x'.2 → ∀ t, x.1 ≤ t → t ≤ x'.1 → (t, x.2) ∈ D)
    (hlip : HasLipschitzRows (D : Set (ℤ × ℤ))) {m : ℕ}
    (hd : ∀ x ∈ D, ∀ x' ∈ D, x.1 - x'.1 ≤ m ∧ x.2 - x'.2 ≤ m) (k : ℕ) :
    2 ^ k * (mixedDyadicIndices D k).card ≤ 16 * (m + 2 * 2 ^ k) := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp [mixedDyadicIndices]
  set u : ℤ := 2 ^ k with hu_def
  have hu : 0 < u := by positivity
  have hxs : (D.image Prod.fst).Nonempty := hD.image _
  have hys : (D.image Prod.snd).Nonempty := hD.image _
  set x₀ := (D.image Prod.fst).min' hxs
  set x₁ := (D.image Prod.fst).max' hxs
  set y₀ := (D.image Prod.snd).min' hys
  set y₁ := (D.image Prod.snd).max' hys
  obtain ⟨p₀, hp₀, hp₀y⟩ := Finset.mem_image.1 ((D.image Prod.snd).min'_mem hys)
  obtain ⟨p₁, hp₁, hp₁y⟩ := Finset.mem_image.1 ((D.image Prod.snd).max'_mem hys)
  obtain ⟨q₀, hq₀, hq₀x⟩ := Finset.mem_image.1 ((D.image Prod.fst).min'_mem hxs)
  obtain ⟨q₁, hq₁, hq₁x⟩ := Finset.mem_image.1 ((D.image Prod.fst).max'_mem hxs)
  have hx₀ : ∀ x ∈ D, x₀ ≤ x.1 :=
    fun x hx => (D.image Prod.fst).min'_le _ (Finset.mem_image_of_mem _ hx)
  have hx₁ : ∀ x ∈ D, x.1 ≤ x₁ :=
    fun x hx => (D.image Prod.fst).le_max' _ (Finset.mem_image_of_mem _ hx)
  have hy₀ : ∀ x ∈ D, y₀ ≤ x.2 :=
    fun x hx => (D.image Prod.snd).min'_le _ (Finset.mem_image_of_mem _ hx)
  have hy₁ : ∀ x ∈ D, x.2 ≤ y₁ :=
    fun x hx => (D.image Prod.snd).le_max' _ (Finset.mem_image_of_mem _ hx)
  have hxm : x₁ - x₀ ≤ m := by
    have := (hd q₁ hq₁ q₀ hq₀).1
    rw [hq₀x, hq₁x] at this
    exact this
  have hym : y₁ - y₀ ≤ m := by
    have := (hd p₁ hp₁ p₀ hp₀).2
    rw [hp₀y, hp₁y] at this
    exact this
  -- every row strictly between the extreme rows meets `D`
  have hrowne : ∀ y, y₀ ≤ y → y ≤ y₁ → ∃ w, (w, y) ∈ D := by
    intro y h₁ h₂
    obtain ⟨w, hw, -⟩ := hlip p₀ hp₀ p₁ hp₁ y (y₁ - y₀) (by rw [hp₀y]; omega)
      (by rw [hp₁y]; omega) (by rw [hp₀y]; omega) (by rw [hp₀y]; omega)
    exact ⟨w, hw⟩
  let R : ℤ → Finset ℤ := fun b => (D.filter fun x => x.2 = b * u).image Prod.fst
  let l : ℤ → ℤ := fun b => if h : (R b).Nonempty then (R b).min' h else 0
  let v : ℤ → ℤ := fun b => if h : (R b).Nonempty then (R b).max' h else 0
  let cols : ℤ → Finset ℤ := fun b =>
    Finset.Icc (l b / u - 3) (l b / u + 3) ∪ Finset.Icc (v b / u - 3) (v b / u + 3)
  have hcols (b : ℤ) : (cols b).card ≤ 14 := by
    refine (Finset.card_union_le _ _).trans ?_
    simp only [Int.card_Icc]
    omega
  let X := Finset.Icc (x₀ / u) (x₁ / u)
  let Y := Finset.Icc (y₀ / u) (y₁ / u)
  have hcover : mixedDyadicIndices D k ⊆
      X ×ˢ ({y₀ / u, y₁ / u} : Finset ℤ) ∪ Y.biUnion fun b => cols b ×ˢ {b} := by
    intro z hz
    obtain ⟨⟨x, hxc, hxD⟩, y, hyc, hyD⟩ := (mem_mixedDyadicIndices _ _ _).1 hz
    have hxz := (mem_latticeDyadicCell k z x).1 hxc
    have hxB := (mem_latticeDyadicCell_iff_bounds k z x).1 hxc
    have hyB := (mem_latticeDyadicCell_iff_bounds k z y).1 hyc
    simp only [dyadicAncestor, Prod.ext_iff] at hxz
    rw [← hu_def] at hxz hxB hyB
    have hzX : z.1 ∈ X := by
      rw [← hxz.1]
      exact Finset.mem_Icc.2 ⟨Int.ediv_le_ediv hu (hx₀ x hxD), Int.ediv_le_ediv hu (hx₁ x hxD)⟩
    have hzY : z.2 ∈ Y := by
      rw [← hxz.2]
      exact Finset.mem_Icc.2 ⟨Int.ediv_le_ediv hu (hy₀ x hxD), Int.ediv_le_ediv hu (hy₁ x hxD)⟩
    by_cases hedge : z.2 = y₀ / u ∨ z.2 = y₁ / u
    · refine Finset.mem_union_left _ (Finset.mem_product.2 ⟨hzX, ?_⟩)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hedge
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z.2, hzY,
      Finset.mem_product.2 ⟨?_, Finset.mem_singleton_self _⟩⟩)
    have hzY' := Finset.mem_Icc.1 hzY
    have hlo : y₀ < z.2 * u := by
      have := Int.lt_ediv_add_one_mul_self y₀ hu
      have h' : y₀ / u + 1 ≤ z.2 := by omega
      nlinarith
    have hhi : z.2 * u + u ≤ y₁ := by
      have := Int.ediv_mul_le y₁ (ne_of_gt hu)
      have h' : z.2 + 1 ≤ y₁ / u := by omega
      nlinarith
    -- the first row of the band
    obtain ⟨w₀, hw₀⟩ := hrowne (z.2 * u) (by omega) (by omega)
    have hR : (R z.2).Nonempty := ⟨w₀, Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨hw₀, rfl⟩, rfl⟩⟩
    have hl : l z.2 = (R z.2).min' hR := dif_pos hR
    have hv : v z.2 = (R z.2).max' hR := dif_pos hR
    have hmemR : ∀ w, w ∈ R z.2 ↔ (w, z.2 * u) ∈ D := by
      intro w
      simp only [R, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
        rwa [← hx2]
      · intro h
        exact ⟨_, ⟨h, rfl⟩, rfl⟩
    have hlD : (l z.2, z.2 * u) ∈ D := by rw [hl]; exact (hmemR _).1 (Finset.min'_mem _ _)
    have hvD : (v z.2, z.2 * u) ∈ D := by rw [hv]; exact (hmemR _).1 (Finset.max'_mem _ _)
    -- a site of the first row near `x`
    obtain ⟨w, hw, hw₁, hw₂⟩ := hlip x hxD _ hlD (z.2 * u) (u - 1) (by dsimp only; omega)
      (by dsimp only; omega) (by omega) (by omega)
    have hlw : l z.2 ≤ w := by rw [hl]; exact Finset.min'_le _ _ ((hmemR w).2 hw)
    have hwv : w ≤ v z.2 := by rw [hv]; exact Finset.le_max' _ _ ((hmemR w).2 hw)
    -- the row of `y` and its sites near the endpoints of the first row
    obtain ⟨c, hc⟩ := hrowne y.2 (by omega) (by omega)
    obtain ⟨l', hl'D, hl'₁, hl'₂⟩ := hlip _ hlD _ hc y.2 (u - 1) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    obtain ⟨v', hv'D, hv'₁, hv'₂⟩ := hlip _ hvD _ hc y.2 (u - 1) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    dsimp only at hl'₁ hl'₂ hv'₁ hv'₂
    have hout : y.1 < l' ∨ v' < y.1 := by
      by_contra h
      exact hyD (hrow _ hl'D _ hv'D rfl y.1 (by dsimp only; omega) (by dsimp only; omega))
    rcases hout with h | h
    · exact Finset.mem_union_left _ (mem_Icc_ediv_of_mul hu (by omega) (by omega))
    · exact Finset.mem_union_right _ (mem_Icc_ediv_of_mul hu (by omega) (by omega))
  have hcount : (mixedDyadicIndices D k).card ≤ 2 * X.card + 14 * Y.card := by
    calc _ ≤ _ := Finset.card_le_card hcover
      _ ≤ (X ×ˢ ({y₀ / u, y₁ / u} : Finset ℤ)).card + (Y.biUnion fun b => cols b ×ˢ {b}).card :=
          Finset.card_union_le _ _
      _ ≤ X.card * 2 + ∑ _b ∈ Y, 14 := by
          refine Nat.add_le_add ?_ (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun b _ => ?_))
          · rw [Finset.card_product]
            exact Nat.mul_le_mul_left _ (Finset.card_le_two)
          · rw [Finset.card_product, Finset.card_singleton, mul_one]
            exact hcols b
      _ = 2 * X.card + 14 * Y.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hX : u * (X.card : ℤ) ≤ m + 2 * u :=
    (quotient_interval_card x₀ x₁ u hu ((hx₀ q₀ hq₀).trans (hx₁ q₀ hq₀))).trans (by omega)
  have hY : u * (Y.card : ℤ) ≤ m + 2 * u :=
    (quotient_interval_card y₀ y₁ u hu ((hy₀ p₀ hp₀).trans (hy₁ p₀ hp₀))).trans (by omega)
  have hcountZ : ((mixedDyadicIndices D k).card : ℤ) ≤ 2 * (X.card : ℤ) + 14 * (Y.card : ℤ) := by
    exact_mod_cast hcount
  have hfinal : u * ((mixedDyadicIndices D k).card : ℤ) ≤ 16 * ((m : ℤ) + 2 * u) := by
    nlinarith
  rw [hu_def] at hfinal
  exact_mod_cast hfinal

/-- Dilation distributes over finite unions. -/
theorem ambientDilation_biUnion {ι : Type*} (s : Finset ι)
    (Q : ι → Finset (ℤ × ℤ)) (j : ℕ) :
    ambientDilation (s.biUnion Q) j = s.biUnion fun i => ambientDilation (Q i) j := by
  ext x
  simp only [mem_ambientDilation, Finset.mem_biUnion]
  constructor
  · rintro ⟨y, ⟨i, hi, hy⟩, h⟩
    exact ⟨i, hi, y, hy, h⟩
  · rintro ⟨i, hi, y, hy, h⟩
    exact ⟨y, ⟨i, hi, hy⟩, h⟩

/-- The dyadic squares of side `u = 2^k` mixed for the dilation `Q_j` of an octagonally convex
set whose coordinates vary by at most `s` number at most `16 (s + 2j + 2u) / u`. -/
theorem IsOctagonallyConvex.card_mixedDyadicIndices_ambientDilation_le {Q : Finset (ℤ × ℤ)}
    (hQ : IsOctagonallyConvex (Q : Set (ℤ × ℤ))) {s : ℕ}
    (hd : ∀ x ∈ Q, ∀ x' ∈ Q, x.1 - x'.1 ≤ s ∧ x.2 - x'.2 ≤ s) (j k : ℕ) :
    2 ^ k * (mixedDyadicIndices (ambientDilation Q j) k).card ≤ 16 * (s + 2 * j + 2 * 2 ^ k) := by
  refine card_mixedDyadicIndices_le
    (fun x hx x' hx' h t h₁ h₂ => hQ.mk_mem_ambientDilation_of_snd_eq hx hx' h h₁ h₂)
    (hQ.hasLipschitzRows.ambientDilation j) (fun x hx x' hx' => ?_) k
  obtain ⟨p, hp, hp₁, hp₂⟩ := mem_ambientDilation.1 hx
  obtain ⟨r, hr, hr₁, hr₂⟩ := mem_ambientDilation.1 hx'
  have h := hd p hp r hr
  rw [abs_le] at hp₁ hp₂ hr₁ hr₂
  push_cast
  omega

variable {Ctpl : ℝ} {n s₀ : ℕ} {T : Finset (ℤ × ℤ)}

private theorem natCast_le_of_one_le {N₀ : ℕ} (hC : 1 ≤ Ctpl) (h : Ctpl * N₀ * (s₀ + 1) ≤ n) :
    N₀ * (s₀ + 1) ≤ n := by
  have : ((N₀ * (s₀ + 1) : ℕ) : ℝ) ≤ n := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 hC) (by positivity : (0 : ℝ) ≤ N₀ * (s₀ + 1))]
  exact_mod_cast this

/-- **Mixed squares of a dilated template** [OAI265, proof of Lemma 9.4].  For a template with
`C_tpl ≥ 1`, `j ≤ s₀` and `u = 2^k ≤ a (s₀ + 1)`, at most `16 (3 + 2a) n / u` dyadic squares of
side `u` are mixed for `T_j`. -/
theorem IsTemplate.card_mixedDyadicIndices_ambientDilation_le (hT : IsTemplate Ctpl n s₀ T)
    (hC : 1 ≤ Ctpl) {j : ℕ} (hj : j ≤ s₀) {k a : ℕ} (hk : 2 ^ k ≤ a * (s₀ + 1)) :
    2 ^ k * (mixedDyadicIndices (ambientDilation T j) k).card ≤ 16 * (3 + 2 * a) * n := by
  classical
  obtain ⟨N₀, Q, rfl, hconv, hd, hscale⟩ := hT.exists_pieces
  have hN := natCast_le_of_one_le hC hscale
  rw [ambientDilation_biUnion]
  calc _ ≤ 2 ^ k * ∑ i, (mixedDyadicIndices (ambientDilation (Q i) j) k).card :=
        Nat.mul_le_mul_left _ (card_mixedDyadicIndices_biUnion_le _ _ k)
    _ = ∑ i, 2 ^ k * (mixedDyadicIndices (ambientDilation (Q i) j) k).card := Finset.mul_sum ..
    _ ≤ ∑ _i : Fin N₀, 16 * (s₀ + 2 * j + 2 * 2 ^ k) := Finset.sum_le_sum fun i _ =>
        (hconv i).card_mixedDyadicIndices_ambientDilation_le (hd i) j k
    _ = N₀ * (16 * (s₀ + 2 * j + 2 * 2 ^ k)) := by simp
    _ ≤ N₀ * (16 * ((3 + 2 * a) * (s₀ + 1))) := by
        gcongr
        nlinarith
    _ = 16 * (3 + 2 * a) * (N₀ * (s₀ + 1)) := by ring
    _ ≤ 16 * (3 + 2 * a) * n := Nat.mul_le_mul_left _ hN

/-- A template with `C_tpl ≥ 1` has at most `n (s₀ + 1)` sites. -/
theorem IsTemplate.card_le (hT : IsTemplate Ctpl n s₀ T) (hC : 1 ≤ Ctpl) :
    T.card ≤ n * (s₀ + 1) := by
  classical
  obtain ⟨N₀, Q, rfl, -, hd, hscale⟩ := hT.exists_pieces
  have hN := natCast_le_of_one_le hC hscale
  have hQ (i : Fin N₀) : (Q i).card ≤ (s₀ + 1) * (s₀ + 1) := by
    refine (Finset.card_le_card (fun x hx => Finset.mem_product.2
      ⟨Finset.mem_image_of_mem Prod.fst hx, Finset.mem_image_of_mem Prod.snd hx⟩)).trans ?_
    rw [Finset.card_product]
    exact Nat.mul_le_mul
      (card_le_of_forall_sub_le fun a ha b hb => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
        exact (hd i x hx y hy).1)
      (card_le_of_forall_sub_le fun a ha b hb => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
        exact (hd i x hx y hy).2)
  calc _ ≤ ∑ i, (Q i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin N₀, (s₀ + 1) * (s₀ + 1) := Finset.sum_le_sum fun i _ => hQ i
    _ = N₀ * (s₀ + 1) * (s₀ + 1) := by simp [mul_assoc]
    _ ≤ n * (s₀ + 1) := Nat.mul_le_mul_right _ hN

end OpenAI
