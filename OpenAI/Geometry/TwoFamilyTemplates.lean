import OpenAI.Geometry.RepairRegions
import OpenAI.Geometry.InitialRegions
import OpenAI.Geometry.PrimaryFragments

/-!
# Birth templates of the two-family decomposition

The ambient lattice template of a birth region is its set of lattice points
[OAI265, §11, lines 189–194 and 690–735].  This file checks Definition 9.3 (`OpenAI.IsTemplate`)
for the three classes of tiles of Proposition 11.2:

* a primary of layer `k` is a union of at most `(2 ^ (p - k) + 2) ^ 2` closed rectangles of
  diameter at most `2 ^ k`, with total diameter at most the pitch `2 ^ p`;
* a belt run of a fine cell of side `t` is a union of at most eight fan triangles of diameter at
  most `t`;
* a replacement of removal half-side `u` is a union of at most eight octant triangles of
  diameter at most `u ≤ 2 u`.

## Main definitions

* `latticeTemplate`: the lattice points of a bounded planar set, as a finite set.

## Main statements

* `mem_latticeTemplate`: a bounded set has finitely many lattice points.
* `isTemplate_latticeTemplate_of_eq_biUnion`: the lattice points of a finite union of template
  pieces with the counting and diameter bounds form a template.
* `isTemplate_primary`, `isTemplate_beltRun`, `isTemplate_repl`.
-/

noncomputable section

namespace OpenAI.Geometry

open scoped Classical in
/-- The lattice points of a planar set, as a finite set when there are finitely many; the
ambient lattice template of a birth region. -/
def latticeTemplate (B : Set (ℝ × ℝ)) : Finset (ℤ × ℤ) :=
  if h : (integerPoint ⁻¹' B).Finite then h.toFinset else ∅

/-- A bounded set has finitely many lattice points, and these form its lattice template. -/
theorem mem_latticeTemplate {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B) {z : ℤ × ℤ} :
    z ∈ latticeTemplate B ↔ integerPoint z ∈ B := by
  have hfin : (integerPoint ⁻¹' B).Finite := by
    have hpre : Bornology.IsBounded (integerPoint ⁻¹' B) :=
      (Isometry.of_dist_eq dist_integerPoint).antilipschitz.isBounded_preimage hB
    simpa using Metric.finite_isBounded_inter_isClosed (s := Set.univ)
      (isDiscrete_univ_iff.mpr inferInstance) hpre isClosed_univ
  classical
  rw [latticeTemplate, dif_pos hfin, Set.Finite.mem_toFinset, Set.mem_preimage]

/-- Lattice templates are monotone below a bounded set. -/
theorem latticeTemplate_mono {B B' : Set (ℝ × ℝ)} (hB' : Bornology.IsBounded B')
    (h : B ⊆ B') : latticeTemplate B ⊆ latticeTemplate B' := by
  intro z hz
  rw [mem_latticeTemplate hB']
  classical
  unfold latticeTemplate at hz
  split_ifs at hz with hfin
  · exact h ((Set.Finite.mem_toFinset hfin).mp hz)
  · simp at hz

/-- The lattice template of a bounded set is the preimage of the set under the lattice
embedding. -/
theorem coe_latticeTemplate {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B) :
    (latticeTemplate B : Set (ℤ × ℤ)) = integerPoint ⁻¹' B := by
  ext z
  rw [Finset.mem_coe, mem_latticeTemplate hB, Set.mem_preimage]

/-- A set whose points are pairwise at sup distance at most `s` has extended diameter at most
`s`. -/
theorem ediam_le_natCast_of_dist_le {P : Set (ℝ × ℝ)} {s : ℕ}
    (h : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ s) : Metric.ediam P ≤ (s : ENNReal) := by
  refine Metric.ediam_le fun x hx y hy ↦ ?_
  rw [edist_dist, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- A closed axis-parallel rectangle with nondegenerate sides is a template piece. -/
theorem isTemplatePiece_Icc_prod_Icc {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    OpenAI.IsTemplatePiece (Set.Icc a b ×ˢ Set.Icc c d) := by
  refine Or.inl ⟨(a, c), (b - a, 0), (0, d - c), ?_, ?_, by simp, Or.inl rfl, Or.inr (Or.inl rfl),
    ?_⟩
  · simp [Prod.ext_iff, sub_eq_zero, hab.ne']
  · simp [Prod.ext_iff, sub_eq_zero, hcd.ne']
  have hset : ({(a, c), (a, c) + (b - a, 0), (a, c) + (b - a, 0) + (0, d - c),
      (a, c) + (0, d - c)} : Set (ℝ × ℝ)) = ({a, b} : Set ℝ) ×ˢ ({c, d} : Set ℝ) := by
    ext ⟨x, y⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk_add_mk, Set.mem_prod,
      Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
    · rintro ⟨rfl | rfl, rfl | rfl⟩ <;> simp
  rw [hset, convexHull_prod, convexHull_pair, convexHull_pair, segment_eq_Icc hab.le,
    segment_eq_Icc hcd.le]

/-- A nonempty intersection of a half-open and an open interval has nondegenerate closure. -/
theorem max_lt_min_of_Ico_inter_Ioo_nonempty {a b c d : ℝ}
    (h : (Set.Ico a b ∩ Set.Ioo c d).Nonempty) : max a c < min b d := by
  obtain ⟨x, hx⟩ := h
  exact (max_le hx.1.1 hx.2.1.le).trans_lt (lt_min hx.1.2 hx.2.2)

/-- The lattice points of a finite union of template pieces form a template, given the counting
bound `max C_tpl 0 · N · (s₀ + 1) ≤ n` for an upper bound `N` on the number of pieces and the
diameter bound `n` on the union. -/
theorem isTemplate_latticeTemplate_of_eq_biUnion {ι : Type*} {B : Set (ℝ × ℝ)} (S : Finset ι)
    (P : ι → Set (ℝ × ℝ)) (hBP : B = ⋃ i ∈ S, P i) {Ctpl : ℝ} {n s₀ N : ℕ} (hn : 1 ≤ n)
    (hs₀ : 1 ≤ s₀) (hT : (latticeTemplate B).Nonempty)
    (hP : ∀ i ∈ S, OpenAI.IsTemplatePiece (P i) ∧ Metric.ediam (P i) ≤ (s₀ : ENNReal))
    (hSN : S.card ≤ N) (hN : max Ctpl 0 * N * ((s₀ : ℝ) + 1) ≤ n)
    (hD : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ n) :
    OpenAI.IsTemplate Ctpl n s₀ (latticeTemplate B) := by
  have hB : Bornology.IsBounded B := Metric.isBounded_iff.mpr ⟨n, hD⟩
  have hS : S.Nonempty := by
    obtain ⟨z, hz⟩ := hT
    rw [mem_latticeTemplate hB, hBP, Set.mem_iUnion₂] at hz
    obtain ⟨i, hi, -⟩ := hz
    exact ⟨i, hi⟩
  let e := S.equivFin
  refine ⟨hn, hs₀, hT, S.card, fun i ↦ P (e.symm i), hS.card_pos, fun i ↦ hP _ (e.symm i).2, ?_,
    ?_, ?_⟩
  · rw [coe_latticeTemplate hB, hBP]
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hz⟩
      exact ⟨e ⟨i, hi⟩, by simpa [integerPoint] using hz⟩
    · rintro ⟨i, hz⟩
      exact ⟨_, (e.symm i).2, hz⟩
  · have hmax : 0 ≤ max Ctpl 0 := le_max_right _ _
    have hs : (0 : ℝ) ≤ s₀ + 1 := by positivity
    calc Ctpl * (S.card : ℝ) * (s₀ + 1) ≤ max Ctpl 0 * S.card * (s₀ + 1) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max Ctpl 0 * N * (s₀ + 1) := by gcongr
      _ ≤ n := hN
  · refine Metric.ediam_le fun z hz w hw ↦ ?_
    rw [Finset.mem_coe, mem_latticeTemplate hB] at hz hw
    rw [edist_dist, ← dist_integerPoint, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hD _ hz _ hw)

/-- **Primary templates** [OAI265, `geometry:primary-pieces` and `geometry:primary-scale`]. -/
theorem isTemplate_primary (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ)
    (j : ℤ × ℤ) (hkp : k ≤ p) (Ctpl : ℝ) (n : ℕ)
    (hn : max Ctpl 0 * (2 ^ (p - k) + 2) ^ 2 * ((2 : ℝ) ^ k + 1) ≤ n)
    (hpn : (2 : ℝ) ^ p ≤ n)
    (hT : (latticeTemplate (primaryBirthRegion o k ℓ p Z C a b j)).Nonempty) :
    OpenAI.IsTemplate Ctpl n (2 ^ k) (latticeTemplate (primaryBirthRegion o k ℓ p Z C a b j)) := by
  have hn1 : 1 ≤ n := by exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hpn
  refine isTemplate_latticeTemplate_of_eq_biUnion (primaryFragmentIndices o k ℓ p Z C a b j)
    (primaryFragment o k ℓ p a b j) (primaryBirthRegion_eq_iUnion_primaryFragment o k ℓ p Z C a b j)
    (N := (2 ^ (p - k) + 2) ^ 2) hn1 Nat.one_le_two_pow hT ?_
    (card_primaryFragmentIndices_le o k ℓ p Z C a b j hkp) (by push_cast; exact hn)
    fun x hx y hy ↦ (primaryBirthRegion_dist_le o k ℓ p Z C a b j x y hx hy).trans hpn
  intro z hz
  have hne : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty := by
    simp only [primaryFragmentIndices, Finset.mem_filter] at hz
    exact hz.2
  refine ⟨?_, ediam_le_natCast_of_dist_le fun x hx y hy ↦ ?_⟩
  · rw [primaryFragment_eq_closedRectangle o k ℓ p a b j z hne]
    change (Set.Ico _ _ ×ˢ Set.Ico _ _ ∩ Set.Ioo _ _ ×ˢ Set.Ioo _ _).Nonempty at hne
    rw [Set.prod_inter_prod, Set.prod_nonempty_iff] at hne
    exact isTemplatePiece_Icc_prod_Icc (max_lt_min_of_Ico_inter_Ioo_nonempty hne.1)
      (max_lt_min_of_Ico_inter_Ioo_nonempty hne.2)
  · push_cast
    exact primaryFragment_dist_le o k ℓ p a b j z x y hx hy

/-- **Belt-run templates** [OAI265, §11, lines 703–707]. -/
theorem isTemplate_beltRun (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (split : Fin 4 → Bool)
    (family : CellFanSlot split → Fin 2) (R : CellFanRun o ℓ z split family) (Ctpl : ℝ)
    (n : ℕ) (hn : max Ctpl 0 * 8 * ((2 : ℝ) ^ ℓ + 1) ≤ n) (htn : (2 : ℝ) ^ ℓ ≤ n)
    (hT : (latticeTemplate (cellFanRunRegion o ℓ z split family R)).Nonempty) :
    OpenAI.IsTemplate Ctpl n (2 ^ ℓ) (latticeTemplate (cellFanRunRegion o ℓ z split family R)) := by
  classical
  have hn1 : 1 ≤ n := by exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans htn
  have hcell (i : CellFanSlot split) :
      (cellFanPolygon o ℓ z split i).region ⊆ closure (dyadicCell o ℓ z) := by
    rw [← cellFanPolygons_cover o ℓ z split]
    exact Set.subset_iUnion (fun i ↦ (cellFanPolygon o ℓ z split i).region) i
  have hdist : ∀ x ∈ closure (dyadicCell o ℓ z), ∀ y ∈ closure (dyadicCell o ℓ z),
      dist x y ≤ (2 : ℝ) ^ ℓ := fun x hx y hy ↦ by
    simpa using dyadicCell_dist_le o ℓ z z 0 x y hx hy (by simp)
  refine isTemplate_latticeTemplate_of_eq_biUnion (Finset.univ.filter (· ∈ R.supp))
    (fun i ↦ (cellFanPolygon o ℓ z split i).region) ?_ (N := 8) hn1 Nat.one_le_two_pow hT
    (fun i _ ↦ ⟨cellFanPolygon_isTemplatePiece o ℓ z split i,
      ediam_le_natCast_of_dist_le fun x hx y hy ↦ by
        push_cast
        exact hdist x (hcell i hx) y (hcell i hy)⟩)
    ((Finset.card_filter_le _ _).trans
      (by rw [Finset.card_univ]; exact (card_cellFanSlot_bounds split).2))
    (by push_cast; exact hn) ?_
  · simp [cellFanRunRegion]
  · intro x hx y hy
    simp only [cellFanRunRegion, Set.mem_iUnion] at hx hy
    obtain ⟨i, -, hx⟩ := hx
    obtain ⟨j, -, hy⟩ := hy
    exact (hdist x (hcell i hx) y (hcell j hy)).trans htn

/-- **Replacement templates** [OAI265, §11, lines 707–712]. -/
theorem isTemplate_repl {I M₀ : Type*} (R : RepairSetup I M₀) (m : RepairMark M₀)
    (old : RepairId I M₀) (u : ℕ) (hu : R.markRadius m = u) (hu1 : 1 ≤ u) (Ctpl : ℝ) (n : ℕ)
    (hn : max Ctpl 0 * 8 * (2 * (u : ℝ) + 1) ≤ n) (hun : 2 * (u : ℝ) ≤ n)
    (hT : (latticeTemplate (R.birthRegion (.repl m old))).Nonempty) :
    OpenAI.IsTemplate Ctpl n (2 * u) (latticeTemplate (R.birthRegion (.repl m old))) := by
  classical
  have hu0 : 0 < R.markRadius m := by rw [hu]; exact_mod_cast hu1
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
  have hB : Bornology.IsBounded (R.birthRegion (.repl m old)) :=
    Metric.isBounded_closedBall.subset (R.birthRegion_repl_subset m old)
  obtain ⟨w, hw⟩ := id hT
  rw [mem_latticeTemplate hB] at hw
  obtain ⟨hmark, hnt, -⟩ := hw
  refine isTemplate_latticeTemplate_of_eq_biUnion (Finset.univ.filter (R.markOct m · = old))
    (octantTriangle (R.markPos m) (R.markRadius m)) ?_ (N := 8) hn1 (by omega) hT
    (fun k _ ↦ ⟨(octantTriangle_isTemplatePiece _ hu0 k).1,
      (octantTriangle_isTemplatePiece _ hu0 k).2.trans ?_⟩)
    ((Finset.card_filter_le _ _).trans (by simp)) (by push_cast; exact hn) ?_
  · ext x
    simp [RepairSetup.birthRegion, hmark, hnt]
  · rw [hu, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith
  · intro x hx y hy
    have hx' := R.birthRegion_repl_subset m old hx
    have hy' := R.birthRegion_repl_subset m old hy
    rw [Metric.mem_closedBall, hu] at hx' hy'
    linarith [dist_triangle_right x y (R.markPos m)]

end OpenAI.Geometry
