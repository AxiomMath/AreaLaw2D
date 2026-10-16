import OpenAI.Scan.SourceScan
import OpenAI.Geometry.TemplateCollar
import OpenAI.Geometry.TemplateMixedSquares

/-!
# The test geometry of a separated template

The scale and clearance conditions of eq. (9.2) for a template separated from the cut
[OAI265, Lemma 9.4 and the proof of Proposition 9.6].

The depth layer `T_d \ T_{d-1}` is bounded piece by piece.  A row of the dilation of an
octagonally convex set is an integer interval, and one more unit of dilation moves its endpoints
by at most two, so every row already met by `Q_{d-1}` acquires at most four sites of the layer;
only the two extreme rows of `Q_d` are new, each of length `O(s₀ + d)`.

## Main statements

* `OpenAI.IsOctagonallyConvex.card_ambientDilation_succ_sdiff_le`: the layer of one piece.
* `OpenAI.IsTemplate.card_ambientDilation_sdiff_le`: the layer bound of eq. (9.10).
* `OpenAI.Scan.isTemplate_test_geometry`: eq. (9.2) for a separated template.
-/

namespace OpenAI

section Layers

variable {Q : Finset (ℤ × ℤ)}

/-- On one row, a site is determined by its first coordinate. -/
theorem injOn_fst_filter_snd_eq (D : Finset (ℤ × ℤ)) (y : ℤ) :
    Set.InjOn Prod.fst ((D.filter fun x => x.2 = y : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  intro x hx x' hx' h
  exact Prod.ext h (((Finset.mem_filter.1 hx).2).trans (Finset.mem_filter.1 hx').2.symm)

/-- A set whose first coordinates vary by at most `m` has at most `m + 1` sites on each row. -/
theorem card_filter_snd_eq_le {D : Finset (ℤ × ℤ)} {m : ℕ}
    (hd : ∀ x ∈ D, ∀ x' ∈ D, x.1 - x'.1 ≤ m) (y : ℤ) :
    (D.filter fun x => x.2 = y).card ≤ m + 1 := by
  rw [← Finset.card_image_of_injOn (injOn_fst_filter_snd_eq D y)]
  refine card_le_of_forall_sub_le fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hb
  exact hd x (Finset.mem_filter.1 hx).1 x' (Finset.mem_filter.1 hx').1

/-- For an octagonally convex `Q`, a site of `Q_{r+1}` on a row met by `Q_r` lies within two
of a site of `Q_r` on that row. -/
theorem IsOctagonallyConvex.exists_mem_ambientDilation_near
    (hQ : IsOctagonallyConvex (Q : Set (ℤ × ℤ))) {r : ℕ} {x p : ℤ × ℤ}
    (hx : x ∈ ambientDilation Q (r + 1)) (hp : p ∈ ambientDilation Q r) (hpx : p.2 = x.2) :
    ∃ w : ℤ, (w, x.2) ∈ ambientDilation Q r ∧ x.1 - 2 ≤ w ∧ w ≤ x.1 + 2 := by
  obtain ⟨q, hq, hq₁, hq₂⟩ := mem_ambientDilation.1 hx
  obtain ⟨q', hq', hq'₁, hq'₂⟩ := mem_ambientDilation.1 hp
  rw [abs_le] at hq₁ hq₂ hq'₁ hq'₂
  push_cast at hq₁ hq₂
  obtain ⟨w, hw, hw₁, hw₂⟩ := hQ.hasLipschitzRows q hq q' hq'
    (max (x.2 - r) (min q.2 (x.2 + r))) 1 (by omega) (by omega) (by omega) (by omega)
  refine ⟨max (w - r) (min x.1 (w + r)), mem_ambientDilation.2 ⟨_, hw, ?_, ?_⟩, by omega,
    by omega⟩ <;> rw [abs_le] <;> dsimp only <;> omega

/-- For an octagonally convex `Q`, every row met by `Q_r` carries at most four sites of the
layer `Q_{r+1} \ Q_r`. -/
theorem IsOctagonallyConvex.card_filter_sdiff_snd_eq_le_four
    (hQ : IsOctagonallyConvex (Q : Set (ℤ × ℤ))) (r : ℕ) {p : ℤ × ℤ}
    (hp : p ∈ ambientDilation Q r) :
    ((ambientDilation Q (r + 1) \ ambientDilation Q r).filter fun x => x.2 = p.2).card ≤ 4 := by
  classical
  set R := ((ambientDilation Q r).filter fun x => x.2 = p.2).image Prod.fst with hRdef
  have hR : R.Nonempty := ⟨p.1, Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, rfl⟩, rfl⟩⟩
  have hmemR (t : ℤ) (ht : t ∈ R) : (t, p.2) ∈ ambientDilation Q r := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hx, hx2⟩ := Finset.mem_filter.1 hx
    rw [← hx2]
    exact hx
  have hl := hmemR _ (R.min'_mem hR)
  have hu := hmemR _ (R.max'_mem hR)
  have hsub : (((ambientDilation Q (r + 1) \ ambientDilation Q r).filter
      fun x => x.2 = p.2).image Prod.fst) ⊆
      Finset.Icc (R.min' hR - 2) (R.min' hR - 1) ∪ Finset.Icc (R.max' hR + 1) (R.max' hR + 2) := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hx, hx2⟩ := Finset.mem_filter.1 hx
    obtain ⟨hxn, hxo⟩ := Finset.mem_sdiff.1 hx
    obtain ⟨w, hw, hw₁, hw₂⟩ := hQ.exists_mem_ambientDilation_near hxn hp hx2.symm
    have hwR : w ∈ R := Finset.mem_image.2 ⟨(w, x.2), Finset.mem_filter.2 ⟨hw, hx2⟩, rfl⟩
    have h₁ := R.min'_le w hwR
    have h₂ := R.le_max' w hwR
    have hout : ¬ (R.min' hR ≤ x.1 ∧ x.1 ≤ R.max' hR) := by
      rintro ⟨h₃, h₄⟩
      apply hxo
      have := hQ.mk_mem_ambientDilation_of_snd_eq hl hu rfl h₃ h₄
      rw [← hx2] at this
      simpa using this
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [← Finset.card_image_of_injOn (injOn_fst_filter_snd_eq _ _)]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  simp only [Int.card_Icc]
  omega

/-- **The layer of one piece** [OAI265, proof of Lemma 9.4].  For an octagonally convex `Q`
whose coordinates vary by at most `s`, the layer `Q_{r+1} \ Q_r` has at most
`6 s + 12 r + 10` sites. -/
theorem IsOctagonallyConvex.card_ambientDilation_succ_sdiff_le
    (hQ : IsOctagonallyConvex (Q : Set (ℤ × ℤ))) {s : ℕ}
    (hd : ∀ x ∈ Q, ∀ x' ∈ Q, x.1 - x'.1 ≤ s ∧ x.2 - x'.2 ≤ s) (r : ℕ) :
    (ambientDilation Q (r + 1) \ ambientDilation Q r).card ≤ 6 * s + 12 * r + 10 := by
  classical
  rcases Q.eq_empty_or_nonempty with rfl | hne
  · simp [ambientDilation]
  have hY : (Q.image Prod.snd).Nonempty := hne.image _
  obtain ⟨qa, hqa, hqa2⟩ := Finset.mem_image.1 ((Q.image Prod.snd).min'_mem hY)
  obtain ⟨qb, hqb, hqb2⟩ := Finset.mem_image.1 ((Q.image Prod.snd).max'_mem hY)
  set a := (Q.image Prod.snd).min' hY
  set b := (Q.image Prod.snd).max' hY
  have hab : b - a ≤ s := by have := (hd qb hqb qa hqa).2; omega
  have hlo (q : ℤ × ℤ) (hq : q ∈ Q) : a ≤ q.2 :=
    (Q.image Prod.snd).min'_le _ (Finset.mem_image_of_mem _ hq)
  have hhi (q : ℤ × ℤ) (hq : q ∈ Q) : q.2 ≤ b :=
    (Q.image Prod.snd).le_max' _ (Finset.mem_image_of_mem _ hq)
  set S := ambientDilation Q (r + 1) \ ambientDilation Q r
  have hband (x : ℤ × ℤ) (hx : x ∈ S) : a - (r + 1 : ℕ) ≤ x.2 ∧ x.2 ≤ b + (r + 1 : ℕ) := by
    obtain ⟨q, hq, -, h2⟩ := mem_ambientDilation.1 (Finset.mem_sdiff.1 hx).1
    rw [abs_le] at h2
    have := hlo q hq
    have := hhi q hq
    omega
  have hmid (y : ℤ) (hy : y ∈ Finset.Icc (a - r) (b + r)) :
      (S.filter fun x => x.2 = y).card ≤ 4 := by
    rw [Finset.mem_Icc] at hy
    have hqa' : qa ∈ (Q : Set (ℤ × ℤ)) := Finset.mem_coe.2 hqa
    have hqb' : qb ∈ (Q : Set (ℤ × ℤ)) := Finset.mem_coe.2 hqb
    obtain ⟨w, hw⟩ := hQ.exists_snd_eq hqa' hqb' (t := max a (min y b)) (by omega) (by omega)
    have hp : (w, y) ∈ ambientDilation Q r :=
      mem_ambientDilation.2 ⟨_, hw, by simp, by rw [abs_le]; dsimp only; omega⟩
    exact hQ.card_filter_sdiff_snd_eq_le_four r hp
  have hend (y : ℤ) : (S.filter fun x => x.2 = y).card ≤ s + 2 * (r + 1) + 1 := by
    refine card_filter_snd_eq_le (fun x hx x' hx' => ?_) y
    obtain ⟨p, hp, hp₁, -⟩ := mem_ambientDilation.1 (Finset.mem_sdiff.1 hx).1
    obtain ⟨p', hp', hp'₁, -⟩ := mem_ambientDilation.1 (Finset.mem_sdiff.1 hx').1
    have := (hd p hp p' hp').1
    rw [abs_le] at hp₁ hp'₁
    push_cast at hp₁ hp'₁ ⊢
    omega
  have hsub : S ⊆ (((Finset.Icc (a - r) (b + r)).biUnion fun y => S.filter fun x => x.2 = y) ∪
      S.filter fun x => x.2 = a - (r + 1 : ℕ)) ∪ S.filter fun x => x.2 = b + (r + 1 : ℕ) := by
    intro x hx
    have := hband x hx
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
    push_cast at this ⊢
    by_cases h : a - r ≤ x.2 ∧ x.2 ≤ b + r
    · exact Or.inl (Or.inl ⟨h, hx, rfl⟩)
    · rcases (show x.2 = a - (r + 1) ∨ x.2 = b + (r + 1) by omega) with h' | h'
      · exact Or.inl (Or.inr ⟨hx, h'⟩)
      · exact Or.inr ⟨hx, h'⟩
  have hrows : (Finset.Icc (a - r) (b + r)).card ≤ s + 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  have hbi := Finset.card_biUnion_le_card_mul (Finset.Icc (a - r) (b + r))
    (fun y => S.filter fun x => x.2 = y) 4 hmid
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (((Finset.Icc (a - r) (b + r)).biUnion fun y =>
      S.filter fun x => x.2 = y) ∪ S.filter fun x => x.2 = a - (r + 1 : ℕ))
    (S.filter fun x => x.2 = b + (r + 1 : ℕ))
  have h₃ := Finset.card_union_le ((Finset.Icc (a - r) (b + r)).biUnion fun y =>
      S.filter fun x => x.2 = y) (S.filter fun x => x.2 = a - (r + 1 : ℕ))
  have h₄ := hend (a - (r + 1 : ℕ))
  have h₅ := hend (b + (r + 1 : ℕ))
  have h₆ : (Finset.Icc (a - r) (b + r)).card * 4 ≤ (s + 2 * r + 1) * 4 :=
    Nat.mul_le_mul_right 4 hrows
  omega

end Layers

section Template

variable {Ctpl : ℝ} {n s₀ : ℕ} {T : Finset (ℤ × ℤ)}

/-- **The layer bound of Lemma 9.4** [OAI265, eq. (9.10)].  For a template with `C_tpl ≥ 24`,
each depth layer `T_d \ T_{d-1}` with `1 ≤ d ≤ s₀` has at most `n` sites. -/
theorem IsTemplate.card_ambientDilation_sdiff_le (hT : IsTemplate Ctpl n s₀ T) (hC : 24 ≤ Ctpl)
    {d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s₀) :
    (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n := by
  classical
  obtain ⟨N₀, Q, rfl, hconv, hdQ, hscale⟩ := hT.exists_pieces
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, ambientDilation_biUnion, ambientDilation_biUnion]
  have hsub : (Finset.univ.biUnion fun i => ambientDilation (Q i) (r + 1)) \
      (Finset.univ.biUnion fun i => ambientDilation (Q i) r) ⊆
      Finset.univ.biUnion fun i => ambientDilation (Q i) (r + 1) \ ambientDilation (Q i) r := by
    intro x hx
    obtain ⟨hx, hxo⟩ := Finset.mem_sdiff.1 hx
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_sdiff.2 ⟨hi, fun h =>
      hxo (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)⟩⟩
  have hscale' : 24 * N₀ * (s₀ + 1) ≤ n := by
    have : (24 : ℝ) * N₀ * (s₀ + 1) ≤ n :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))
        (by positivity)).trans hscale
    exact_mod_cast this
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i, (ambientDilation (Q i) (r + 1) \ ambientDilation (Q i) r).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin N₀, (6 * s₀ + 12 * r + 10) := Finset.sum_le_sum fun i _ =>
        (hconv i).card_ambientDilation_succ_sdiff_le (hdQ i) r
    _ = N₀ * (6 * s₀ + 12 * r + 10) := by simp
    _ ≤ N₀ * (24 * (s₀ + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 24 * N₀ * (s₀ + 1) := by ring
    _ ≤ n := hscale'

end Template

end OpenAI

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- **The test geometry of a separated template** [OAI265, Lemma 9.4, eq. (9.10), and the proof
of Proposition 9.6, lines 833–836].  For `C_tpl` large, every template `T` with parameters
`(n, s₀)` separated from the cut at `D₀ ≥ 10`, with `L = ⌊n^{1-10⁻⁵}⌋ ≤ s₀` and `n` large,
has `|T| ≤ 4n²`, at most `n` sites in each depth layer `T_d \ T_{d-1}` with `1 ≤ d ≤ L`, and
`dist_∞(T, Z_A) > 2L + 10 r₀`. -/
theorem isTemplate_test_geometry {Ctr : ℝ} (hCtr : 0 ≤ Ctr) :
    ∃ Ctpl₀ : ℝ, 24 ≤ Ctpl₀ ∧ ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∃ N : ℕ,
      ∀ (D₀ : ℝ), 10 ≤ D₀ → ∀ (n s₀ : ℕ) (Λ A T : Finset (ℤ × ℤ)),
      IsTemplate Ctpl n s₀ T → IsSeparatedFromCut D₀ s₀ Λ A T → collarWidth n ≤ s₀ →
      N ≤ n →
      (T.card : ℝ) ≤ 4 * (n : ℝ) ^ 2 ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ collarWidth n →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) ∧
      ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * collarWidth n + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) <
          ambientSupDistance t z := by
  refine ⟨24, le_rfl, fun Ctpl hC => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_const_mul_roundedLogRadius_le_rpow hCtr
    (ε := 1 - 1 / 100000) (by norm_num) 10)
  refine ⟨N, fun D₀ hD₀ n s₀ Λ A T hT hsep hL hn => ⟨?_, fun d hd hdL =>
    hT.card_ambientDilation_sdiff_le hC hd (hdL.trans hL), fun t ht z hz => ?_⟩⟩
  · have h₁ := hT.card_le (by linarith)
    have h₂ := hT.twentyFour_mul_add_one_le hC
    have : T.card ≤ 4 * n ^ 2 :=
      calc T.card ≤ n * (s₀ + 1) := h₁
        _ ≤ n * n := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 4 * n ^ 2 := by nlinarith
    exact_mod_cast this
  · have hr : 10 * roundedLogRadius Ctr n ≤ collarWidth n := by
      unfold collarWidth
      exact Nat.le_floor (by exact_mod_cast hN n hn)
    have h := (lt_ambientEDist_iff ENNReal.ofReal_lt_top).1 hsep t ht z hz
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff', dist_eq_max_abs] at h
    have hsum : ((2 * collarWidth n + 10 * roundedLogRadius Ctr n : ℕ) : ℝ) ≤ 3 * s₀ := by
      exact_mod_cast (show 2 * collarWidth n + 10 * roundedLogRadius Ctr n ≤ 3 * s₀ by omega)
    have hD : (3 * s₀ : ℝ) ≤ 4 * D₀ * s₀ := by
      have : (0 : ℝ) ≤ s₀ := Nat.cast_nonneg _
      nlinarith
    have : ((2 * collarWidth n + 10 * roundedLogRadius Ctr n : ℕ) : ℝ) <
        ((ambientSupDistance t z : ℤ) : ℝ) := by
      unfold ambientSupDistance
      linarith [h.1]
    exact_mod_cast this

end OpenAI.Scan
