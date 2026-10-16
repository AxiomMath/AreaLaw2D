import OpenAI.Geometry.InitialRepairSetup
import OpenAI.Geometry.RepairSeparation
import OpenAI.Geometry.BeltSeparation
import OpenAI.Geometry.TwoFamilyTemplates
import OpenAI.Geometry.TwoFamilyScales
import OpenAI.Geometry.TwoFamilyCounting
import OpenAI.Geometry.AmbientDistanceBridge
import OpenAI.Geometry.LocalLayers
import OpenAI.Geometry.LayerPartition

/-!
# Two families with separated birth templates

Proposition 11.2 of [OAI265, §11.2, eqs. (11.3) and (11.4)].  The construction: the dummy
neighborhood, the primaries and the belt runs of the initial configuration
(`OpenAI.Geometry.InitialRegions`), repaired at the marks of the belt cells
(`OpenAI.Geometry.RepairRegions`).  The tiles are the identifiers whose final region meets `A`,
ordered primaries, then belt runs, then replacements by generation; `X i` is the final region
on `A`, `T i` the lattice template of the birth region, and `D` the rest of `A`, in the dummy
or in terminal squares.

## Main statements

* `OpenAI.two_family_decomposition`: Proposition 11.2.

## Implementation notes

The constants are fixed in `OpenAI.Geometry.TwoFamilyAssembly.Consts` before the cut, and the
cut-dependent choices (belt shifts, the marks and their assigned cells) in
`OpenAI.Geometry.TwoFamilyAssembly.Data`.  The ordering of the tiles is any enumeration along
which the rank `0` (primaries), `1` (belt runs), `g + 2` (replacements of a mark of generation
`g`) is nondecreasing, so earlier tiles of a replacement are born no later than it.
-/

noncomputable section

open scoped Fin.NatCast

namespace OpenAI.Geometry

/-! ### Generic lemmas -/

/-- A finite set has an enumeration along which a natural-number rank is nondecreasing. -/
theorem exists_equiv_fin_rank_monotone {α : Type*} (s : Finset α) (r : α → ℕ) :
    ∃ (m : ℕ) (e : Fin m ≃ s), ∀ i j, i < j → r (e i) ≤ r (e j) := by
  classical
  let L := s.attach.toList.mergeSort (fun a b => decide (r a ≤ r b))
  have hnd : L.Nodup := List.nodup_mergeSort.2 (Finset.nodup_toList _)
  have hmem : ∀ x, x ∈ L := fun x =>
    List.mem_mergeSort.2 (Finset.mem_toList.2 (Finset.mem_attach _ _))
  have hsort := List.pairwise_mergeSort (le := fun a b : s => decide (r a ≤ r b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) s.attach.toList
  refine ⟨L.length, List.Nodup.getEquivOfForallMemList L hnd hmem, fun i j hij => ?_⟩
  have := List.pairwise_iff_get.1 hsort i j hij
  exact of_decide_eq_true this

/-- A strict pointwise lower bound `c'` on lattice distances bounds the ambient distance from
below by every `c < c'`. -/
theorem ofReal_lt_ambientEDist_of_le_dist {c c' : ℝ} (hc' : 0 < c') (hc : c < c')
    {T Z : Finset (ℤ × ℤ)}
    (h : ∀ x ∈ T, ∀ z ∈ Z, c' ≤ dist (integerPoint x) (integerPoint z)) :
    ENNReal.ofReal c < OpenAI.ambientEDist T Z :=
  (ENNReal.ofReal_le_ofReal (le_max_left c 0)).trans_lt
    (ofReal_lt_ambientEDist_of_integerPoint_dist (le_max_right _ _) fun x hx z hz =>
      (max_lt hc hc').trans_le (h x hx z hz))

theorem repairHalfSide_le_self {S : ℝ} (hS : 1 ≤ S) : repairHalfSide S ≤ S :=
  (repairHalfSide_le_rpow (by linarith)).trans <|
    (Real.rpow_le_rpow_of_exponent_le hS rho_pos_lt_one.2.le).trans_eq (Real.rpow_one S)

theorem sum_half_pow_le_two (F : Finset ℕ) : ∑ k ∈ F, (1 / 2 : ℝ) ^ k ≤ 2 :=
  (Finset.sum_le_sum_of_subset_of_nonneg
    (fun k hk => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)))
    fun _ _ _ => by positivity).trans (sum_geometric_two_le _)

theorem isBounded_closure_dyadicCell (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    Bornology.IsBounded (closure (dyadicCell o ℓ z)) := by
  rw [closure_dyadicCell]
  exact (Metric.isBounded_Icc _ _).prod (Metric.isBounded_Icc _ _)

theorem isBounded_closure_dyadicNeighborhood (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) : Bornology.IsBounded (closure (dyadicNeighborhood o k Z C)) :=
  Bornology.IsBounded.closure <| (Bornology.isBounded_biUnion_finset _).2 fun z _ =>
    (isBounded_closure_dyadicCell o k z).subset subset_closure

theorem cellFanRunRegion_subset_closure_dyadicCell (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (R : CellFanRun o ℓ z split family) :
    cellFanRunRegion o ℓ z split family R ⊆ closure (dyadicCell o ℓ z) := by
  rw [← cellFanRunRegions_cover o ℓ z split family]
  exact Set.subset_iUnion (fun R => cellFanRunRegion o ℓ z split family R) R

theorem closure_dyadicCell_subset_closure_dyadicLayer (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) {z : ℤ × ℤ}
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    closure (dyadicCell o (fineScaleIndex k) z) ⊆ closure (dyadicLayer o k Z C) :=
  closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k _ Z C z
    (fineScaleIndex_le k) hz)

theorem mem_closure_dyadicLayer_of_mem_beltCellMarks (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) {z : ℤ × ℤ} {x : ℝ × ℝ}
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hx : x ∈ beltCellMarks o (fineScaleIndex k) z) : x ∈ closure (dyadicLayer o k Z C) :=
  closure_dyadicCell_subset_closure_dyadicLayer o k Z C hz
    (beltCellMarks_subset_closure_dyadicCell o _ z hx)

/-- A mark shared by fine cells of two late layers sees fine sides within a factor two. -/
theorem fineScale_le_two_mul_of_mem_beltCellMarks (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) {z w : ℤ × ℤ} {x : ℝ × ℝ} (hC : 2 ≤ C)
    (hk : 50000000 ≤ k) (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hxz : x ∈ beltCellMarks o (fineScaleIndex k) z)
    (hxw : x ∈ beltCellMarks o (fineScaleIndex h) w) :
    (2 : ℝ) ^ fineScaleIndex k ≤ 2 * (2 : ℝ) ^ fineScaleIndex h := by
  have hkh := (dyadicLayer_nearby_indices o k h Z C x x hC hk
    (mem_closure_dyadicLayer_of_mem_beltCellMarks o k Z C hz hxz)
    (mem_closure_dyadicLayer_of_mem_beltCellMarks o h Z C hw hxw)
    (by rw [dist_self]; positivity)).2
  have h1 := fineScaleIndex_mono hkh
  have h2 := fineScaleIndex_succ h
  have h3 : fineScaleIndex k ≤ fineScaleIndex h + 1 := by omega
  calc (2 : ℝ) ^ fineScaleIndex k ≤ 2 ^ (fineScaleIndex h + 1) :=
        pow_le_pow_right₀ (by norm_num) h3
    _ = 2 * 2 ^ fineScaleIndex h := by rw [pow_succ]; ring

/-- The removal half-side of a mark is at most twice that of its initial ancestor. -/
theorem RepairSetup.TreeHyp.markRadius_le_two_mul_root {I M₀ : Type*} {R : RepairSetup I M₀}
    (hR : R.TreeHyp) {m : RepairMark M₀} (hm : R.IsMark m) :
    R.markRadius m ≤ 2 * repairHalfSide (R.scale₀ m.root) := by
  set r₀ : RepairMark M₀ := ⟨m.root, []⟩
  have hdesc : r₀.descend m.path = m := by simp [r₀, RepairMark.descend]
  have h := hR.dist_markPos_descendant_add_markRadius_le (m := r₀) (Or.inl rfl) m.path
    (by rw [hdesc]; exact hm)
  rw [hdesc] at h
  have : R.markRadius r₀ = repairHalfSide (R.scale₀ m.root) := rfl
  linarith [dist_nonneg (x := R.markPos m) (y := R.markPos r₀)]

namespace TwoFamilyAssembly

/-- The constants of Proposition 11.2, fixed before the cut: `C₀, C_P, C_B, S_*, k₀` of
`exists_twoFamily_constants`, the mark-count constant `K` of `exists_ncard_isMark_le`, and a
bound `B₀` on the dyadic sums `∑ 2 ^ (-δ₀ k / 2)`. -/
structure Consts (D₀ Ctpl : ℝ) (nStar : ℕ) where
  /-- The layer constant: layer `k` lies at distance `C₀ 2 ^ k` from the cut. -/
  C₀ : ℕ
  /-- The scale multiplier of primaries. -/
  CP : ℝ
  /-- The scale multiplier of belt runs and replacements. -/
  CB : ℝ
  /-- The stopping scale of the repair. -/
  Sstar : ℝ
  /-- The lowest layer. -/
  k₀ : ℕ
  one_le_nStar : 1 ≤ nStar
  two_le_C₀ : 2 ≤ C₀
  four_mul_D₀_add_two_le : 4 * D₀ + 2 ≤ (C₀ : ℝ)
  le_k₀ : 50000000 ≤ k₀
  two_le_Sstar : 2 ≤ Sstar
  CB_pos : 0 < CB
  margin : ∀ S, Sstar ≤ S → repairHalfSide S ≤ 1 / 64 / 1000 * S
  fine : ∀ k, k₀ ≤ k → 2 * Sstar ≤ (2 : ℝ) ^ fineScaleIndex k
  tile : ∀ u : ℝ, Sstar ≤ u →
    nStar ≤ tileScanScale CB u ∧
    max Ctpl 0 * 8 * (2 * u + 1) ≤ tileScanScale CB u ∧
    2 * u ≤ tileScanScale CB u ∧
    (collarWidth (tileScanScale CB u) : ℝ) ≤ u ∧
    2 * (tileScanScale CB u : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < repairHalfSide (u / 2) / 2
  primary : ∀ k, k₀ ≤ k →
    nStar ≤ primaryScanScale CP k ∧
    max Ctpl 0 * (2 ^ (pitchScaleIndex k - k) + 2) ^ 2 * ((2 : ℝ) ^ k + 1) ≤
      primaryScanScale CP k ∧
    (2 : ℝ) ^ pitchScaleIndex k ≤ primaryScanScale CP k ∧
    collarWidth (primaryScanScale CP k) ≤ 2 ^ k ∧
    2 * (primaryScanScale CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) <
      (2 : ℝ) ^ fineScaleIndex k ∧
    2 * (primaryScanScale CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) <
      ((C₀ : ℝ) - 1) / 2 * (2 : ℝ) ^ k
  /-- The constant of the total repair count. -/
  K : ℝ
  K_pos : 0 < K
  ncard_isMark_le : ∀ {I M₀ : Type} [Finite M₀] (R : RepairSetup I M₀),
    R.Sstar = Sstar → R.TreeHyp → ∀ (layer : M₀ → ℕ) (B : ℝ),
      (∀ r, R.scale₀ r ≤ 1 * 2 ^ layer r) →
      (∀ k, ({r | layer r = k}.ncard : ℝ) ≤
        B * (2 : ℝ) ^ (-((Exponents.geometryDelta : ℝ) / 2) * k)) →
      ({m : RepairMark M₀ | R.IsMark m}.ncard : ℝ) ≤ K * B
  /-- A bound on the dyadic sums `∑ 2 ^ (-δ₀ k / 2)`. -/
  B₀ : ℝ
  B₀_pos : 0 < B₀
  sum_le_B₀ : ∀ F : Finset ℕ,
    ∑ k ∈ F, (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) ≤ B₀

variable {D₀ Ctpl : ℝ} {nStar : ℕ}

theorem nonempty_consts (D₀ Ctpl : ℝ) (nStar : ℕ) (hn : 1 ≤ nStar) :
    Nonempty (Consts D₀ Ctpl nStar) := by
  obtain ⟨C₀, CP, CB, Sstar, k₀, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_twoFamily_constants D₀ Ctpl nStar
  have hδ : 0 < (Exponents.geometryDelta : ℝ) / 2 := by norm_num [Exponents.geometryDelta]
  obtain ⟨K, hK, hKm⟩ := exists_ncard_isMark_le Sstar 1 _ (by linarith) one_pos hδ
  obtain ⟨B₀, hB₀, hsum⟩ := exists_uniform_polynomial_dyadic_sum_bound 0
  exact ⟨⟨C₀, CP, CB, Sstar, k₀, hn, h1, h2, h3, h4, h5, h6, h7, h8, h9, K, hK, hKm, B₀, hB₀,
    fun F => by simpa using hsum F⟩⟩

/-- The constant of Proposition 11.2: dummy sites, terminal squares, and the weights of
primaries, belt runs and replacements. -/
def Consts.C (κ : Consts D₀ Ctpl nStar) : ℝ :=
  (2 * κ.C₀ + 1) ^ 2 * (2 * ((2 : ℝ) ^ κ.k₀ + 1) ^ 2 + 576 * κ.K * (2 * κ.Sstar + 1) ^ 2 +
    64 + 512 * κ.B₀ + 4608 * κ.K)

/-- The selected belt cells of layer `k`. -/
abbrev beltCells (Z : Finset (ℤ × ℤ)) (C₀ : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))) (k : ℕ) :
    Finset (ℤ × ℤ) :=
  beltCellIndices (fineLayerIndices dyadicOrigin k (fineScaleIndex k) Z C₀)
    (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)

/-- The cut-dependent data: the cut, the sparse belt shifts, the deduplicated marks with an
assigned cell realizing the least incident side, and the separation of the marks. -/
structure Data (κ : Consts D₀ Ctpl nStar) where
  /-- The domain. -/
  Λ : Finset (ℤ × ℤ)
  /-- The cut. -/
  A : Finset (ℤ × ℤ)
  b_pos : 0 < (edgeBoundary Λ A).card
  /-- The horizontal belt residue of each layer. -/
  a : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))
  /-- The vertical belt residue of each layer. -/
  b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))
  card_beltCells_le : ∀ k, ((beltCells (cutEndpoints Λ A) κ.C₀ a b k).card : ℝ) ≤
    64 * (2 * (κ.C₀ : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
      (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)
  /-- The initial marks: the marks of the selected belt cells from layer `k₀` on. -/
  M : Finset (ℝ × ℝ)
  mem_M : ∀ x, x ∈ M ↔ ∃ k, κ.k₀ ≤ k ∧
    x ∈ beltMarks dyadicOrigin (fineScaleIndex k) (beltCells (cutEndpoints Λ A) κ.C₀ a b k)
  /-- The layer of the cell assigned to a mark. -/
  kOf : M → ℕ
  /-- The cell assigned to a mark, realizing its least incident side. -/
  zOf : M → ℤ × ℤ
  k₀_le_kOf : ∀ v, κ.k₀ ≤ kOf v
  zOf_mem : ∀ v, zOf v ∈ beltCells (cutEndpoints Λ A) κ.C₀ a b (kOf v)
  mem_beltCellMarks : ∀ v, v.val ∈ beltCellMarks dyadicOrigin (fineScaleIndex (kOf v)) (zOf v)
  sep : ∀ v w : M, v ≠ w →
    max ((2 : ℝ) ^ fineScaleIndex (kOf v)) ((2 : ℝ) ^ fineScaleIndex (kOf w)) / 4 ≤
      dist v.val w.val

theorem exists_data (κ : Consts D₀ Ctpl nStar) (Λ A : Finset (ℤ × ℤ))
    (hb : 0 < (edgeBoundary Λ A).card) : ∃ d : Data κ, d.Λ = Λ ∧ d.A = A := by
  obtain ⟨Bm, -, hmarks⟩ := exists_uniform_separated_initial_marks
  obtain ⟨a, b, hcells, -, M, hM, -, S, hS, -, hsep⟩ :=
    hmarks dyadicOrigin Λ A κ.C₀ κ.k₀ κ.two_le_C₀ κ.le_k₀
  have hS' := fun v => (hS v).2
  choose kOf zOf hkOf hzOf hvOf hSeq using hS'
  refine ⟨⟨Λ, A, hb, a, b, hcells, M, hM, kOf, zOf, hkOf, hzOf, hvOf, fun v w hvw => ?_⟩,
    rfl, rfl⟩
  have := hsep v w hvw
  rwa [hSeq v, hSeq w] at this

namespace Data

variable {κ : Consts D₀ Ctpl nStar} (d : Data κ)

/-- The cut endpoints. -/
abbrev Z : Finset (ℤ × ℤ) := cutEndpoints d.Λ d.A

/-- The initial identifiers. -/
abbrev I : Type :=
  InitialRegionIndex dyadicOrigin κ.k₀ d.Z κ.C₀ d.a d.b κ.two_le_C₀ κ.le_k₀

theorem mem_fineLayerIndices_zOf (v : d.M) :
    d.zOf v ∈ fineLayerIndices dyadicOrigin (d.kOf v) (fineScaleIndex (d.kOf v)) d.Z κ.C₀ :=
  (Finset.mem_filter.1 (d.zOf_mem v)).1

/-- The repair data of the initial configuration. -/
def R : RepairSetup d.I d.M :=
  initialRepairSetup κ.k₀ d.Z κ.C₀ d.a d.b κ.two_le_C₀ κ.le_k₀ d.M d.kOf d.zOf d.k₀_le_kOf
    d.mem_fineLayerIndices_zOf d.mem_beltCellMarks κ.Sstar

theorem Z_nonempty : d.Z.Nonempty := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 d.b_pos
  exact ⟨e.1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)⟩

theorem latticeHyp : d.R.LatticeHyp :=
  initialRepairSetup_latticeHyp _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.Z_nonempty κ.two_le_Sstar
    κ.margin (fun v => by have := κ.fine _ (d.k₀_le_kOf v); linarith [κ.two_le_Sstar]) d.sep

theorem mem_M_of_mem_beltCellMarks {k : ℕ} (hk : κ.k₀ ≤ k) {z : ℤ × ℤ}
    (hz : z ∈ beltCells d.Z κ.C₀ d.a d.b k) {v : ℝ × ℝ}
    (hv : v ∈ beltCellMarks dyadicOrigin (fineScaleIndex k) z) : v ∈ d.M :=
  (d.mem_M v).2 ⟨k, hk, Finset.mem_biUnion.2 ⟨z, hz, hv⟩⟩

/-! ### Tiles -/

/-- The tiles: non-dummy identifiers whose final region contains a site of `A`. -/
def IsTile (a : RepairId d.I d.M) : Prop :=
  a ≠ .init (.inl ()) ∧ ∃ z ∈ d.A, integerPoint z ∈ d.R.finalRegion a

theorem finite_isTile : {a | d.IsTile a}.Finite := by
  classical
  have h : ∀ z : ℤ × ℤ, {a : RepairId d.I d.M | integerPoint z ∈ d.R.finalRegion a}.Finite :=
    fun z => Set.Subsingleton.finite fun a ha b hb => d.latticeHyp.eq_of_mem_finalRegion ha hb
  refine (d.A.finite_toSet.biUnion fun z _ => h z).subset ?_
  rintro a ⟨-, z, hz, hza⟩
  exact Set.mem_biUnion hz hza

/-- The tiles, as a finite set. -/
def tiles : Finset (RepairId d.I d.M) := d.finite_isTile.toFinset

theorem mem_tiles {a : RepairId d.I d.M} : a ∈ d.tiles ↔ d.IsTile a :=
  d.finite_isTile.mem_toFinset

/-- The rank of an identifier in the order of the tiles. -/
def rank : RepairId d.I d.M → ℕ
  | .init (.inr (.inr _)) => 1
  | .init _ => 0
  | .repl m _ => m.gen + 2

/-- The scanner scale `n` of an identifier. -/
def scanScale : RepairId d.I d.M → ℕ
  | .init (.inl _) => 1
  | .init (.inr (.inl ⟨k, _⟩)) => primaryScanScale κ.CP k.val
  | .init (.inr (.inr ⟨k, _, _⟩)) => tileScanScale κ.CB ((2 : ℝ) ^ fineScaleIndex k.val)
  | .repl m _ => tileScanScale κ.CB (d.R.markRadius m)

/-- The piece scale `s₀` of an identifier. -/
def pieceScale : RepairId d.I d.M → ℕ
  | .init (.inl _) => 1
  | .init (.inr (.inl ⟨k, _⟩)) => 2 ^ k.val
  | .init (.inr (.inr ⟨k, _, _⟩)) => 2 ^ fineScaleIndex k.val
  | .repl m _ => 2 * ⌊d.R.markRadius m⌋₊

/-- The distance from the birth template of an identifier to every earlier tile of its family:
the belt width or the nonadjacent-layer gap for primaries, `d(t / 2) / 2` for belt runs of fine
side `t`, and `d(u) / 2` for replacements of removal half-side `u`. -/
def clearance : RepairId d.I d.M → ℝ
  | .init (.inl _) => 1
  | .init (.inr (.inl ⟨k, _⟩)) =>
      min ((2 : ℝ) ^ fineScaleIndex k.val) (((κ.C₀ : ℝ) - 1) / 2 * 2 ^ k.val)
  | .init (.inr (.inr ⟨k, _, _⟩)) => repairHalfSide ((2 : ℝ) ^ fineScaleIndex k.val / 2) / 2
  | .repl m _ => repairHalfSide (d.R.markRadius m) / 2

/-- The lattice template of the birth region. -/
def template (a : RepairId d.I d.M) : Finset (ℤ × ℤ) := latticeTemplate (d.R.birthRegion a)

theorem isBounded_birthRegion : ∀ a : RepairId d.I d.M, Bornology.IsBounded (d.R.birthRegion a)
  | .init (.inl _) => isBounded_closure_dyadicNeighborhood _ _ _ _
  | .init (.inr (.inl ⟨_, _⟩)) => Metric.isBounded_iff.2
      ⟨_, fun x hx y hy => primaryBirthRegion_dist_le _ _ _ _ _ _ _ _ _ x y hx hy⟩
  | .init (.inr (.inr ⟨_, _, _⟩)) =>
      (isBounded_closure_dyadicCell _ _ _).subset
        (cellFanRunRegion_subset_closure_dyadicCell _ _ _ _ _ _)
  | .repl m old => Metric.isBounded_closedBall.subset (d.R.birthRegion_repl_subset m old)

theorem mem_template {a : RepairId d.I d.M} {z : ℤ × ℤ} :
    z ∈ d.template a ↔ integerPoint z ∈ d.R.birthRegion a :=
  mem_latticeTemplate (d.isBounded_birthRegion a)

theorem mem_template_of_mem_finalRegion {a : RepairId d.I d.M} {z : ℤ × ℤ}
    (hz : integerPoint z ∈ d.R.finalRegion a) : z ∈ d.template a :=
  d.mem_template.2 (d.R.finalRegion_subset_birthRegion a hz)

/-- The conditions of Proposition 11.2 on a single tile, other than the clearance from earlier
tiles, together with the comparison of `2 n ^ β` with `clearance`. -/
def TileSpec (a : RepairId d.I d.M) : Prop :=
  nStar ≤ d.scanScale a ∧
    OpenAI.IsTemplate Ctpl (d.scanScale a) (d.pieceScale a) (d.template a) ∧
    OpenAI.IsSeparatedFromCut D₀ (d.pieceScale a) d.Λ d.A (d.template a) ∧
    collarWidth (d.scanScale a) ≤ d.pieceScale a ∧
    ENNReal.ofReal (2 * (d.scanScale a : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
      OpenAI.ambientEDist (d.template a) d.Z ∧
    2 * (d.scanScale a : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < d.clearance a

theorem tileSpec {a : RepairId d.I d.M} (ha : d.IsTile a) : d.TileSpec a := by
  obtain ⟨hdummy, z₀, -, hz₀⟩ := ha
  have hT : (d.template a).Nonempty := ⟨z₀, d.mem_template_of_mem_finalRegion hz₀⟩
  have hC0 : (2 : ℝ) ≤ κ.C₀ := by exact_mod_cast κ.two_le_C₀
  have hD := κ.four_mul_D₀_add_two_le
  have hS2 := κ.two_le_Sstar
  rcases a with (⟨⟨⟩⟩ | ⟨⟨k, hk⟩, ⟨J, hJ⟩⟩ | ⟨⟨k, hk⟩, ⟨z, hz⟩, Rr⟩) | ⟨m, old⟩
  · exact absurd rfl hdummy
  · -- a primary of layer `k`
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := κ.primary k hk
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hc' : (0 : ℝ) < κ.C₀ * 2 ^ k := mul_pos (by linarith) hpow
    have hdist : ∀ x ∈ d.template (.init (.inr (.inl ⟨⟨k, hk⟩, ⟨J, hJ⟩⟩))), ∀ y ∈ d.Z,
        (κ.C₀ : ℝ) * 2 ^ k ≤ dist (integerPoint x) (integerPoint y) := fun x hx y hy =>
      dyadicLayer_dist_lower _ _ _ _ _ (closure_mono Set.inter_subset_left
        (d.mem_template.1 hx)) y hy
    have hβ : 0 ≤ 2 * (primaryScanScale κ.CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) := by positivity
    refine ⟨h1, ?_, ?_, h4, ?_, lt_min h5 h6⟩
    · exact isTemplate_primary _ _ _ _ _ _ _ _ _ (le_pitchScaleIndex k) Ctpl _ h2 h3 hT
    · refine ofReal_lt_ambientEDist_of_le_dist hc' ?_ hdist
      change 4 * D₀ * ((2 ^ k : ℕ) : ℝ) < _
      push_cast
      nlinarith
    · refine ofReal_lt_ambientEDist_of_le_dist hc' ?_ hdist
      change 2 * (primaryScanScale κ.CP k : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < _
      nlinarith
  · -- a belt run of the fine cell `z` of layer `k`, of side `2 ^ fineScaleIndex k`
    have hz' : z ∈ fineLayerIndices dyadicOrigin k (fineScaleIndex k) d.Z κ.C₀ :=
      (Finset.mem_filter.1 hz).1
    have hfine : 2 * κ.Sstar ≤ (2 : ℝ) ^ fineScaleIndex k := κ.fine k hk
    have hSu : κ.Sstar ≤ (2 : ℝ) ^ fineScaleIndex k := by linarith
    obtain ⟨h1, h2, h3, h4, h5⟩ := κ.tile _ hSu
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hc' : (0 : ℝ) < κ.C₀ * 2 ^ k := mul_pos (by linarith) hpow
    have huk : (2 : ℝ) ^ fineScaleIndex k ≤ 2 ^ k :=
      pow_le_pow_right₀ (by norm_num) (fineScaleIndex_le k)
    have hdist : ∀ x ∈ d.template (.init (.inr (.inr ⟨⟨k, hk⟩, ⟨z, hz⟩, Rr⟩))), ∀ y ∈ d.Z,
        (κ.C₀ : ℝ) * 2 ^ k ≤ dist (integerPoint x) (integerPoint y) := fun x hx y hy =>
      dyadicLayer_dist_lower _ _ _ _ _ (closure_dyadicCell_subset_closure_dyadicLayer _ _ _ _ hz'
        (cellFanRunRegion_subset_closure_dyadicCell _ _ _ _ _ _ (d.mem_template.1 hx))) y hy
    have hhalf : repairHalfSide ((2 : ℝ) ^ fineScaleIndex k / 2) ≤
        (2 : ℝ) ^ fineScaleIndex k / 2 := repairHalfSide_le_self (by linarith)
    have hβ : 0 ≤ 2 * (tileScanScale κ.CB ((2 : ℝ) ^ fineScaleIndex k) : ℝ) ^
        (1 - (2 / 1000000 : ℝ)) := by positivity
    have hmax : 0 ≤ max Ctpl 0 * 8 := mul_nonneg (le_max_right _ _) (by norm_num)
    refine ⟨h1, ?_, ?_, ?_, ?_, h5⟩
    · exact isTemplate_beltRun _ _ _ _ _ Rr Ctpl _
        ((mul_le_mul_of_nonneg_left (by linarith) hmax).trans h2)
        (by
          change (2 : ℝ) ^ fineScaleIndex k ≤ (tileScanScale κ.CB ((2 : ℝ) ^ fineScaleIndex k) : ℝ)
          linarith) hT
    · refine ofReal_lt_ambientEDist_of_le_dist hc' ?_ hdist
      change 4 * D₀ * ((2 ^ fineScaleIndex k : ℕ) : ℝ) < _
      push_cast
      rcases le_or_gt 0 D₀ with h0 | h0 <;> nlinarith
    · change collarWidth (tileScanScale κ.CB ((2 : ℝ) ^ fineScaleIndex k)) ≤ 2 ^ fineScaleIndex k
      exact_mod_cast h4
    · refine ofReal_lt_ambientEDist_of_le_dist hc' ?_ hdist
      change 2 * (tileScanScale κ.CB ((2 : ℝ) ^ fineScaleIndex k) : ℝ) ^
        (1 - (2 / 1000000 : ℝ)) < _
      nlinarith
  · -- a replacement at the mark `m`, of removal half-side `d.R.markRadius m`
    have hR := d.latticeHyp
    obtain ⟨hm, hnt, -⟩ := d.R.finalRegion_subset_birthRegion _ hz₀
    have hSu : κ.Sstar ≤ d.R.markRadius m := hnt
    obtain ⟨h1, h2, h3, h4, h5⟩ := κ.tile _ hSu
    obtain ⟨p, hp⟩ := hR.hyp.tree.exists_markRadius_eq_pow hm
    have hfl : ⌊(2 : ℝ) ^ p⌋₊ = 2 ^ p := by
      rw [show (2 : ℝ) ^ p = ((2 ^ p : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
    have huN : ((⌊d.R.markRadius m⌋₊ : ℕ) : ℝ) = d.R.markRadius m := by
      rw [hp, hfl]; push_cast; rfl
    have hu1 : 1 ≤ ⌊d.R.markRadius m⌋₊ := by
      have : ((1 : ℕ) : ℝ) ≤ ⌊d.R.markRadius m⌋₊ := by rw [huN]; push_cast; linarith
      exact_mod_cast this
    -- the initial mark at the root, in the closed layer `d.kOf m.root`
    have hSvS : κ.Sstar ≤ (2 : ℝ) ^ fineScaleIndex (d.kOf m.root) := by
      have := κ.fine _ (d.k₀_le_kOf m.root); linarith
    have hdSv : repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf m.root)) ≤
        1 / 64 / 1000 * (2 : ℝ) ^ fineScaleIndex (d.kOf m.root) := κ.margin _ hSvS
    have hSvk : (2 : ℝ) ^ fineScaleIndex (d.kOf m.root) ≤ 2 ^ d.kOf m.root :=
      pow_le_pow_right₀ (by norm_num) (fineScaleIndex_le _)
    have hu2 : d.R.markRadius m ≤ 2 * repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf m.root)) :=
      hR.hyp.tree.markRadius_le_two_mul_root hm
    have hvlayer : m.root.val ∈ closure (dyadicLayer dyadicOrigin (d.kOf m.root) d.Z κ.C₀) :=
      mem_closure_dyadicLayer_of_mem_beltCellMarks _ _ _ _ (d.mem_fineLayerIndices_zOf m.root)
        (d.mem_beltCellMarks m.root)
    have hpow : (0 : ℝ) < 2 ^ d.kOf m.root := by positivity
    have hdist : ∀ x ∈ d.template (.repl m old), ∀ y ∈ d.Z,
        (κ.C₀ : ℝ) * 2 ^ d.kOf m.root -
            2 * repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf m.root)) ≤
          dist (integerPoint x) (integerPoint y) := by
      intro x hx y hy
      have e1 := dyadicLayer_dist_lower _ _ _ _ _ hvlayer y hy
      have e2 : dist (integerPoint x) m.root.val ≤
          2 * repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf m.root)) :=
        Metric.mem_closedBall.1 (hR.hyp.birthRegion_repl_subset_closedBall_root m old
          (d.mem_template.1 hx))
      have e3 := dist_triangle m.root.val (integerPoint x) (integerPoint y)
      rw [dist_comm] at e2
      linarith
    have hhalf : repairHalfSide (d.R.markRadius m / 2) ≤ d.R.markRadius m / 2 :=
      repairHalfSide_le_self (by linarith)
    have hβ : 0 ≤ 2 * (tileScanScale κ.CB (d.R.markRadius m) : ℝ) ^
        (1 - (2 / 1000000 : ℝ)) := by positivity
    have hd0 : 0 < repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf m.root)) :=
      repairHalfSide_pos _
    have hc' : 0 < (κ.C₀ : ℝ) * 2 ^ d.kOf m.root -
        2 * repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf m.root)) := by nlinarith
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
    · exact isTemplate_repl d.R m old ⌊d.R.markRadius m⌋₊ huN.symm hu1 Ctpl _
        (by rw [huN]; exact h2) (by rw [huN]; exact h3) hT
    · refine ofReal_lt_ambientEDist_of_le_dist hc' ?_ hdist
      change 4 * D₀ * ((2 * ⌊d.R.markRadius m⌋₊ : ℕ) : ℝ) < _
      push_cast
      rw [huN]
      rcases le_or_gt 0 D₀ with h0 | h0 <;> nlinarith
    · change collarWidth (tileScanScale κ.CB (d.R.markRadius m)) ≤ 2 * ⌊d.R.markRadius m⌋₊
      have : (collarWidth (tileScanScale κ.CB (d.R.markRadius m)) : ℝ) ≤
          ((2 * ⌊d.R.markRadius m⌋₊ : ℕ) : ℝ) := by
        push_cast; rw [huN]; linarith
      exact_mod_cast this
    · refine ofReal_lt_ambientEDist_of_le_dist hc' ?_ hdist
      change 2 * (tileScanScale κ.CB (d.R.markRadius m) : ℝ) ^ (1 - (2 / 1000000 : ℝ)) < _
      nlinarith
    · change 2 * (tileScanScale κ.CB (d.R.markRadius m) : ℝ) ^ (1 - (2 / 1000000 : ℝ)) <
        repairHalfSide (d.R.markRadius m) / 2
      have : repairHalfSide (d.R.markRadius m / 2) ≤ repairHalfSide (d.R.markRadius m) :=
        repairHalfSide_le_repairHalfSide (by linarith) (by linarith)
      linarith

/-! ### Clearance from earlier tiles of the same family -/

/-- **Birth-template clearance** [OAI265, `geometry:birth-separation`].  The birth template of a
tile is at distance at least its `clearance` from the final region of every other tile of the
same label and no larger rank. -/
theorem clearance_le_dist {a b : RepairId d.I d.M} (ha : d.IsTile a) (hb : d.IsTile b)
    (hab : b ≠ a) (hrank : d.rank b ≤ d.rank a) (hlabel : d.R.label b = d.R.label a)
    {x y : ℤ × ℤ} (hx : x ∈ d.template a) (hy : integerPoint y ∈ d.R.finalRegion b) :
    d.clearance a ≤ dist (integerPoint x) (integerPoint y) := by
  have hR := d.latticeHyp
  have hxb := d.mem_template.1 hx
  have hyb := d.R.finalRegion_subset_birthRegion b hy
  have hC0 : (2 : ℝ) ≤ κ.C₀ := by exact_mod_cast κ.two_le_C₀
  rcases a with (⟨⟨⟩⟩ | ⟨⟨k, hk⟩, ⟨J, hJ⟩⟩ | ⟨⟨k, hk⟩, ⟨z, hz⟩, Rr⟩) | ⟨m, old⟩
  · exact absurd rfl ha.1
  · -- `a` is a primary; then so is `b`
    rcases b with (⟨⟨⟩⟩ | ⟨⟨h, hh⟩, ⟨J', hJ'⟩⟩ | ⟨⟨h, hh⟩, _, _⟩) | ⟨m', old'⟩
    · exact absurd rfl hb.1
    · have hx' : integerPoint x ∈ closure (dyadicLayer dyadicOrigin k d.Z κ.C₀) :=
        closure_mono Set.inter_subset_left hxb
      have hy' : integerPoint y ∈ closure (dyadicLayer dyadicOrigin h d.Z κ.C₀) :=
        closure_mono Set.inter_subset_left hyb
      have hpar : h % 2 = k % 2 := by
        have h' : ((h : ℕ) : Fin 2) = ((k : ℕ) : Fin 2) := hlabel
        have := congrArg Fin.val h'
        simpa only [Fin.val_natCast] using this
      have hC1 : (0 : ℝ) ≤ ((κ.C₀ : ℝ) - 1) / 2 := by linarith
      rcases lt_trichotomy k h with hkh | rfl | hkh
      · have := dyadicLayer_dist_nonadjacent _ _ _ _ _ _ _ (by omega) hx' hy'
        refine (min_le_right _ _).trans (le_trans ?_ this)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hkh.le) hC1
      · have hJJ : J ≠ J' := by
          rintro rfl
          exact hab rfl
        exact (min_le_left _ _).trans
          (primaryBirthRegion_dist_separation _ _ _ _ _ _ _ _ _ _ hJJ _ _ hxb hyb)
      · have := dyadicLayer_dist_nonadjacent _ _ _ _ _ _ _ (by omega) hy' hx'
        rw [dist_comm] at this
        exact (min_le_right _ _).trans this
    · have : 1 ≤ 0 := hrank
      omega
    · have : m'.gen + 2 ≤ 0 := hrank
      omega
  · -- `a` is a belt run; then `b` is initial
    rcases b with i | ⟨m', old'⟩
    · have hz' : z ∈ fineLayerIndices dyadicOrigin k (fineScaleIndex k) d.Z κ.C₀ :=
        (Finset.mem_filter.1 hz).1
      have hfine : 2 * κ.Sstar ≤ (2 : ℝ) ^ fineScaleIndex k := κ.fine k hk
      have hS2 := κ.two_le_Sstar
      have hr₀t : repairHalfSide ((2 : ℝ) ^ fineScaleIndex k / 2) ≤
          (2 : ℝ) ^ fineScaleIndex k / 4096 := by
        have := κ.margin ((2 : ℝ) ^ fineScaleIndex k / 2) (by linarith)
        linarith
      have hyv : ∀ v ∈ beltCellMarks dyadicOrigin (fineScaleIndex k) z,
          repairHalfSide ((2 : ℝ) ^ fineScaleIndex k / 2) ≤ dist (integerPoint y) v := by
        intro v hv
        have hvM := d.mem_M_of_mem_beltCellMarks hk hz hv
        have h1 := d.R.le_dist_of_mem_finalRegion (m := ⟨⟨v, hvM⟩, []⟩) (Or.inl rfl)
          (le_of_eq rfl) hy
        have h2 := fineScale_le_two_mul_of_mem_beltCellMarks dyadicOrigin k (d.kOf ⟨v, hvM⟩)
          d.Z κ.C₀ κ.two_le_C₀ (κ.le_k₀.trans hk) hz' (d.mem_fineLayerIndices_zOf ⟨v, hvM⟩) hv
          (d.mem_beltCellMarks ⟨v, hvM⟩)
        calc repairHalfSide ((2 : ℝ) ^ fineScaleIndex k / 2)
            ≤ repairHalfSide ((2 : ℝ) ^ fineScaleIndex (d.kOf ⟨v, hvM⟩)) :=
              repairHalfSide_le_repairHalfSide (by positivity) (by linarith)
          _ ≤ dist (integerPoint y) v := h1
      exact half_le_dist_of_mem_initialBirthRegion_beltRun dyadicOrigin κ.k₀ d.Z κ.C₀ d.a d.b
        κ.two_le_C₀ κ.le_k₀ d.Z_nonempty k hk z hz Rr i (fun h => hab (congrArg _ h))
        (fun h => hb.1 (congrArg _ h)) hlabel (repairHalfSide_pos _) hr₀t hxb hyb hyv
    · have : m'.gen + 2 ≤ 1 := hrank
      omega
  · -- `a` is a replacement
    have hgen : b.birthGen ≤ m.gen + 1 := by
      cases b with
      | init i => exact Nat.zero_le _
      | repl m' old' =>
        have : m'.gen + 2 ≤ m.gen + 2 := hrank
        change m'.gen + 1 ≤ m.gen + 1
        omega
    exact hR.hyp.half_le_dist_of_mem_birthRegion_repl hxb.1 hxb.2.1 hab hlabel hgen hxb hy

/-! ### Counting -/

/-- The marks of the repair, as a finite set. -/
def marks : Finset (RepairMark d.M) := d.latticeHyp.hyp.tree.finite_isMark.toFinset

theorem mem_marks {m : RepairMark d.M} : m ∈ d.marks ↔ d.R.IsMark m :=
  d.latticeHyp.hyp.tree.finite_isMark.mem_toFinset

/-- **Total repairs** [OAI265, `geometry:total-repairs`]. -/
theorem card_marks_le : (d.marks.card : ℝ) ≤
    κ.K * (576 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card) := by
  have hT := d.latticeHyp.hyp.tree
  have h := κ.ncard_isMark_le d.R rfl hT d.kOf
    (576 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card) ?_ ?_
  · rwa [Set.ncard_eq_toFinset_card _ hT.finite_isMark] at h
  · intro r
    rw [one_mul]
    exact pow_le_pow_right₀ (by norm_num) (fineScaleIndex_le _)
  · intro k
    have hsub : {r : d.M | d.kOf r = k}.ncard ≤
        (beltMarks dyadicOrigin (fineScaleIndex k) (beltCells d.Z κ.C₀ d.a d.b k)).card := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
        (Finset.finite_toSet _)
      rintro r rfl
      exact Finset.mem_biUnion.2 ⟨d.zOf r, d.zOf_mem r, d.mem_beltCellMarks r⟩
    have h9 := card_beltMarks_le dyadicOrigin (fineScaleIndex k) (beltCells d.Z κ.C₀ d.a d.b k)
    have hc := d.card_beltCells_le k
    have hexp : (2 : ℝ) ^ (-((Exponents.geometryDelta : ℝ) / 2) * k) =
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
      congr 1; ring
    rw [hexp]
    calc ({r : d.M | d.kOf r = k}.ncard : ℝ)
        ≤ 9 * ((beltCells d.Z κ.C₀ d.a d.b k).card : ℝ) := by
          exact_mod_cast hsub.trans h9
      _ ≤ 9 * (64 * (2 * (κ.C₀ : ℝ) + 1) ^ 2 * (edgeBoundary d.Λ d.A).card *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) := by gcongr
      _ = _ := by ring

/-- **Bad sites** [OAI265, `geometry:bad-sites`]: a set of sites each in the closed dummy
neighborhood or in a terminal removal square has at most `C b` elements. -/
theorem card_le_of_subset_exceptional (D : Finset (ℤ × ℤ))
    (hD : ∀ z ∈ D, integerPoint z ∈ closure (dyadicNeighborhood dyadicOrigin κ.k₀ d.Z κ.C₀) ∨
      ∃ m ∈ d.marks, ¬ d.R.IsNonterminal m ∧
        integerPoint z ∈ Metric.closedBall (d.R.markPos m) (d.R.markRadius m)) :
    (D.card : ℝ) ≤ κ.C * (edgeBoundary d.Λ d.A).card := by
  classical
  have hsub : D ⊆ latticeTemplate (closure (dyadicNeighborhood dyadicOrigin κ.k₀ d.Z κ.C₀)) ∪
      (d.marks.filter fun m => ¬ d.R.IsNonterminal m).biUnion fun m =>
        latticeTemplate (Metric.closedBall (d.R.markPos m) (d.R.markRadius m)) := by
    intro z hz
    rcases hD z hz with h | ⟨m, hm, hnt, hball⟩
    · exact Finset.mem_union_left _
        ((mem_latticeTemplate (isBounded_closure_dyadicNeighborhood _ _ _ _)).2 h)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, Finset.mem_filter.2 ⟨hm, hnt⟩,
        (mem_latticeTemplate Metric.isBounded_closedBall).2 hball⟩)
  have hS2 := κ.two_le_Sstar
  have hQ : (((d.marks.filter fun m => ¬ d.R.IsNonterminal m).biUnion fun m =>
        latticeTemplate (Metric.closedBall (d.R.markPos m) (d.R.markRadius m))).card : ℝ) ≤
      d.marks.card * (2 * κ.Sstar + 1) ^ 2 := by
    calc _ ≤ ∑ m ∈ d.marks.filter (fun m => ¬ d.R.IsNonterminal m),
          ((latticeTemplate (Metric.closedBall (d.R.markPos m) (d.R.markRadius m))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ m ∈ d.marks.filter (fun m => ¬ d.R.IsNonterminal m), (2 * κ.Sstar + 1) ^ 2 := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hnt := (Finset.mem_filter.1 hm).2
          have hρ : d.R.markRadius m < κ.Sstar := lt_of_not_ge hnt
          have hρ0 : 0 ≤ d.R.markRadius m := (repairHalfSide_pos _).le
          exact (card_latticeTemplate_closedBall_le _ hρ0).trans
            (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      _ = (d.marks.filter fun m => ¬ d.R.IsNonterminal m).card * (2 * κ.Sstar + 1) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ d.marks.card * (2 * κ.Sstar + 1) ^ 2 := by
          gcongr; exact Finset.filter_subset _ _
  have hN := card_latticeTemplate_closure_dyadicNeighborhood_le dyadicOrigin κ.k₀ d.Z κ.C₀
  have hZ : (d.Z.card : ℝ) ≤ 2 * (edgeBoundary d.Λ d.A).card := by
    exact_mod_cast card_cutEndpoints_le d.Λ d.A
  have hM := d.card_marks_le
  have hK := κ.K_pos
  have hB := κ.B₀_pos
  have hb0 : (0 : ℝ) ≤ (edgeBoundary d.Λ d.A).card := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (2 * κ.C₀ + 1) ^ 2 := by positivity
  have hk0 : (0 : ℝ) ≤ ((2 : ℝ) ^ κ.k₀ + 1) ^ 2 := by positivity
  have hs0 : (0 : ℝ) ≤ (2 * κ.Sstar + 1) ^ 2 := by positivity
  have hN' : ((latticeTemplate (closure (dyadicNeighborhood dyadicOrigin κ.k₀ d.Z κ.C₀))).card :
      ℝ) ≤ (2 * κ.C₀ + 1) ^ 2 * (2 * (edgeBoundary d.Λ d.A).card) *
        ((2 : ℝ) ^ κ.k₀ + 1) ^ 2 := hN.trans (by gcongr)
  have hQ' := hQ.trans (mul_le_mul_of_nonneg_right hM hs0)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : (D.card : ℝ) ≤
      ((latticeTemplate (closure (dyadicNeighborhood dyadicOrigin κ.k₀ d.Z κ.C₀))).card : ℝ) +
        (((d.marks.filter fun m => ¬ d.R.IsNonterminal m).biUnion fun m =>
          latticeTemplate (Metric.closedBall (d.R.markPos m) (d.R.markRadius m))).card : ℝ) := by
    exact_mod_cast hcard
  unfold Consts.C
  nlinarith [mul_nonneg (mul_nonneg hc0 hb0) (by positivity : (0 : ℝ) ≤
    64 + 512 * κ.B₀ + 4608 * κ.K)]

/-- Primaries. -/
def IsPrimary : RepairId d.I d.M → Prop
  | .init (.inr (.inl _)) => True
  | _ => False

/-- Belt runs. -/
def IsRun : RepairId d.I d.M → Prop
  | .init (.inr (.inr _)) => True
  | _ => False

/-- The layer of a primary or a belt run. -/
def layer : RepairId d.I d.M → ℕ
  | .init (.inr (.inl ⟨k, _⟩)) => k.val
  | .init (.inr (.inr ⟨k, _, _⟩)) => k.val
  | _ => 0

/-- The pitch index of a primary. -/
def pitchIndex : RepairId d.I d.M → ℤ × ℤ
  | .init (.inr (.inl ⟨_, J⟩)) => J.val
  | _ => 0

/-- The fine cell of a belt run. -/
def cell : RepairId d.I d.M → ℤ × ℤ
  | .init (.inr (.inr ⟨_, z, _⟩)) => z.val
  | _ => 0

/-- The mark of a replacement. -/
def markOf : RepairId d.I d.M → Option (RepairMark d.M)
  | .repl m _ => some m
  | _ => none

theorem one_le_scanScale {a : RepairId d.I d.M} (ha : d.IsTile a) : 1 ≤ d.scanScale a :=
  κ.one_le_nStar.trans (d.tileSpec ha).1

theorem inv_scanScale_pow_le_one {a : RepairId d.I d.M} (ha : d.IsTile a) :
    ((d.scanScale a : ℝ) ^ 100)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast d.one_le_scanScale ha))

/-- Primaries of layer `k` have weight at most `2 ^ (-k)`, and number at most
`32 (2 C₀ + 1) ^ 2 b` per layer. -/
theorem sum_primary_le (S : Finset (RepairId d.I d.M)) (hS : ∀ a ∈ S, d.IsPrimary a) :
    ∑ a ∈ S, ((d.scanScale a : ℝ) ^ 100)⁻¹ ≤
      64 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card := by
  classical
  have hw : ∀ a ∈ S, ((d.scanScale a : ℝ) ^ 100)⁻¹ ≤ (1 / 2 : ℝ) ^ d.layer a := by
    intro a ha
    have hP := hS a ha
    rcases a with (⟨⟨⟩⟩ | ⟨⟨k, hk⟩, ⟨J, hJ⟩⟩ | _) | _
    all_goals try exact False.elim hP
    change ((primaryScanScale κ.CP k : ℝ) ^ 100)⁻¹ ≤ (1 / 2 : ℝ) ^ k
    have h3 := (κ.primary k hk).2.2.1
    have hn : (2 : ℝ) ^ k ≤ primaryScanScale κ.CP k :=
      (pow_le_pow_right₀ (by norm_num) (le_pitchScaleIndex k)).trans h3
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hn1 : (1 : ℝ) ≤ primaryScanScale κ.CP k := h1.trans hn
    rw [one_div_pow, one_div]
    exact inv_anti₀ (by positivity) (hn.trans (le_self_pow₀ hn1 (by norm_num)))
  have hfib : ∀ k, ((S.filter (d.layer · = k)).card) ≤
      32 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card := by
    intro k
    refine le_trans ?_ (card_primaryPitchIndices_boundary_le dyadicOrigin k (fineScaleIndex k)
      (pitchScaleIndex k) d.Λ d.A κ.C₀ (d.a k).val (d.b k).val (le_pitchScaleIndex k))
    refine Finset.card_le_card_of_injOn d.pitchIndex ?_ ?_
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      obtain ⟨ha, hl⟩ := ha
      have hP := hS a ha
      rcases a with (⟨⟨⟩⟩ | ⟨⟨k', hk'⟩, ⟨J, hJ⟩⟩ | _) | _
      all_goals try exact False.elim hP
      change k' = k at hl
      subst hl
      exact hJ
    · intro a ha a' ha' h
      rw [Finset.mem_coe, Finset.mem_filter] at ha ha'
      obtain ⟨ha, hl⟩ := ha
      obtain ⟨ha', hl'⟩ := ha'
      have hP := hS a ha
      have hP' := hS a' ha'
      rcases a with (⟨⟨⟩⟩ | ⟨⟨k₁, hk₁⟩, ⟨J₁, hJ₁⟩⟩ | _) | _
      all_goals try exact False.elim hP
      rcases a' with (⟨⟨⟩⟩ | ⟨⟨k₂, hk₂⟩, ⟨J₂, hJ₂⟩⟩ | _) | _
      all_goals try exact False.elim hP'
      change k₁ = k at hl
      change k₂ = k at hl'
      change J₁ = J₂ at h
      subst hl hl' h
      rfl
  calc ∑ a ∈ S, ((d.scanScale a : ℝ) ^ 100)⁻¹ ≤ ∑ a ∈ S, (1 / 2 : ℝ) ^ d.layer a :=
        Finset.sum_le_sum hw
    _ = ∑ k ∈ S.image d.layer, (S.filter (d.layer · = k)).card • (1 / 2 : ℝ) ^ k :=
        Finset.sum_comp _ _
    _ ≤ ∑ k ∈ S.image d.layer,
        (32 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card : ℝ) * (1 / 2 : ℝ) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [nsmul_eq_mul]
        gcongr
        exact_mod_cast hfib k
    _ = (32 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card : ℝ) *
        ∑ k ∈ S.image d.layer, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ (32 * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card : ℝ) * 2 := by
        gcongr; exact sum_half_pow_le_two _
    _ = _ := by ring

/-- At most eight belt runs per selected belt cell. -/
theorem card_run_le (S : Finset (RepairId d.I d.M)) (hS : ∀ a ∈ S, d.IsRun a) :
    ((S.card : ℕ) : ℝ) ≤ 512 * κ.B₀ * (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card := by
  classical
  have hcell : ∀ k, ∀ z ∈ (S.filter (d.layer · = k)).image d.cell,
      ((S.filter (d.layer · = k)).filter (d.cell · = z)).card ≤ 8 := by
    intro k z hz
    obtain ⟨a₀, ha₀, hza₀⟩ := Finset.mem_image.1 hz
    rw [Finset.mem_filter] at ha₀
    obtain ⟨ha₀, hl₀⟩ := ha₀
    have hP₀ := hS a₀ ha₀
    rcases a₀ with (⟨⟨⟩⟩ | _ | ⟨⟨k', hk'⟩, ⟨z', hz'⟩, Rr₀⟩) | _
    all_goals try exact False.elim hP₀
    change k' = k at hl₀
    change z' = z at hza₀
    subst hl₀ hza₀
    calc _ ≤ ((Finset.univ : Finset (type_of% Rr₀)).image fun Rr =>
          (RepairId.init (.inr (.inr ⟨⟨k', hk'⟩, ⟨z', hz'⟩, Rr⟩)) : RepairId d.I d.M)).card := by
          refine Finset.card_le_card fun a ha => ?_
          rw [Finset.mem_filter, Finset.mem_filter] at ha
          obtain ⟨⟨ha, hl⟩, hc⟩ := ha
          have hP := hS a ha
          rcases a with (⟨⟨⟩⟩ | _ | ⟨⟨k'', hk''⟩, ⟨z'', hz''⟩, Rr⟩) | _
          all_goals try exact False.elim hP
          change k'' = k' at hl
          change z'' = z' at hc
          subst hl hc
          exact Finset.mem_image.2 ⟨Rr, Finset.mem_univ _, rfl⟩
      _ ≤ (Finset.univ : Finset (type_of% Rr₀)).card := Finset.card_image_le
      _ = Fintype.card (type_of% Rr₀) := Finset.card_univ
      _ ≤ Fintype.card (CellFanSlot (fineLayerSplitMask dyadicOrigin κ.k₀ k' d.Z κ.C₀ z')) :=
          Fintype.card_le_of_surjective
            (cellFanRunGraph dyadicOrigin (fineScaleIndex k') z' _ _).connectedComponentMk
            fun c => Quot.exists_rep c
      _ ≤ 8 := (card_cellFanSlot_bounds _).2
  have hlayer : ∀ k, ((S.filter (d.layer · = k)).card : ℝ) ≤
      8 * ((beltCells d.Z κ.C₀ d.a d.b k).card : ℝ) := by
    intro k
    have h1 := Finset.card_le_mul_card_image (S.filter (d.layer · = k)) 8 (hcell k)
    have h2 : (S.filter (d.layer · = k)).image d.cell ⊆ beltCells d.Z κ.C₀ d.a d.b k := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_filter] at ha
      obtain ⟨ha, hl⟩ := ha
      have hP := hS a ha
      rcases a with (⟨⟨⟩⟩ | _ | ⟨⟨k', hk'⟩, ⟨z', hz'⟩, Rr⟩) | _
      all_goals try exact False.elim hP
      change k' = k at hl
      subst hl
      exact hz'
    have h3 := Finset.card_le_card h2
    exact_mod_cast h1.trans (Nat.mul_le_mul_left 8 h3)
  have hb0 : (0 : ℝ) ≤ (edgeBoundary d.Λ d.A).card := Nat.cast_nonneg _
  calc ((S.card : ℕ) : ℝ) = ∑ k ∈ S.image d.layer, ((S.filter (d.layer · = k)).card : ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image d.layer S
    _ ≤ ∑ k ∈ S.image d.layer, 8 * (64 * (2 * (κ.C₀ : ℝ) + 1) ^ 2 *
        (edgeBoundary d.Λ d.A).card * (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) :=
        Finset.sum_le_sum fun k _ => (hlayer k).trans (by gcongr; exact d.card_beltCells_le k)
    _ = 512 * (2 * (κ.C₀ : ℝ) + 1) ^ 2 * (edgeBoundary d.Λ d.A).card *
        ∑ k ∈ S.image d.layer, (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 512 * (2 * (κ.C₀ : ℝ) + 1) ^ 2 * (edgeBoundary d.Λ d.A).card * κ.B₀ := by
        gcongr; exact κ.sum_le_B₀ _
    _ = _ := by ring

/-- At most eight replacements per mark. -/
theorem card_repl_le (S : Finset (RepairId d.I d.M))
    (hS : ∀ a ∈ S, d.IsTile a ∧ ¬ d.IsPrimary a ∧ ¬ d.IsRun a) :
    ((S.card : ℕ) : ℝ) ≤ 8 * (d.marks.card : ℝ) := by
  classical
  have hfib : ∀ o ∈ S.image d.markOf, (S.filter (d.markOf · = o)).card ≤ 8 := by
    intro o _
    rcases o with _ | m
    · refine (Finset.card_eq_zero.2 ?_).le.trans (Nat.zero_le _)
      refine Finset.filter_eq_empty_iff.2 ?_
      intro a ha h
      obtain ⟨⟨hdummy, -⟩, hP, hR⟩ := hS a ha
      rcases a with (⟨⟨⟩⟩ | _ | _) | _
      · exact hdummy rfl
      · exact hP trivial
      · exact hR trivial
      · exact Option.some_ne_none _ h
    · calc _ ≤ ((Finset.univ : Finset (Fin 8)).image fun k =>
            (RepairId.repl m (d.R.markOct m k) : RepairId d.I d.M)).card := by
            refine Finset.card_le_card fun a ha => ?_
            obtain ⟨ha, hm⟩ := Finset.mem_filter.1 ha
            obtain ⟨⟨hdummy, z, -, hz⟩, hP, hR⟩ := hS a ha
            rcases a with (⟨⟨⟩⟩ | _ | _) | ⟨m', old⟩
            · exact absurd rfl hdummy
            · exact False.elim (hP trivial)
            · exact False.elim (hR trivial)
            · change some m' = some m at hm
              cases Option.some_injective _ hm
              obtain ⟨-, -, k, hk, -⟩ := d.R.finalRegion_subset_birthRegion _ hz
              exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [hk]⟩
        _ ≤ (Finset.univ : Finset (Fin 8)).card := Finset.card_image_le
        _ = 8 := by simp
  have h1 := Finset.card_le_mul_card_image S 8 hfib
  have h2 : S.image d.markOf ⊆ d.marks.image some := by
    intro o ho
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ho
    obtain ⟨⟨hdummy, z, -, hz⟩, hP, hR⟩ := hS a ha
    rcases a with (⟨⟨⟩⟩ | _ | _) | ⟨m', old⟩
    · exact absurd rfl hdummy
    · exact False.elim (hP trivial)
    · exact False.elim (hR trivial)
    · obtain ⟨hm, -⟩ := d.R.finalRegion_subset_birthRegion _ hz
      exact Finset.mem_image.2 ⟨m', d.mem_marks.2 hm, rfl⟩
  have h3 := (Finset.card_le_card h2).trans Finset.card_image_le
  exact_mod_cast h1.trans (Nat.mul_le_mul_left 8 h3)

/-- **Scanner weights**: `∑ n ^ (-100) ≤ C b`. -/
theorem sum_le : ∑ a ∈ d.tiles, ((d.scanScale a : ℝ) ^ 100)⁻¹ ≤
    κ.C * (edgeBoundary d.Λ d.A).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not d.tiles d.IsPrimary]
  have hP := d.sum_primary_le (d.tiles.filter d.IsPrimary) fun a ha => (Finset.mem_filter.1 ha).2
  have hsub : d.tiles.filter (fun a => ¬ d.IsPrimary a) ⊆ d.tiles.filter d.IsRun ∪
      d.tiles.filter fun a => ¬ d.IsPrimary a ∧ ¬ d.IsRun a := by
    intro a ha
    obtain ⟨ha, hP⟩ := Finset.mem_filter.1 ha
    by_cases hR : d.IsRun a
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha, hR⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha, hP, hR⟩)
  have hrest : ∑ a ∈ d.tiles.filter (fun a => ¬ d.IsPrimary a), ((d.scanScale a : ℝ) ^ 100)⁻¹ ≤
      (((d.tiles.filter d.IsRun).card : ℕ) : ℝ) +
        (((d.tiles.filter fun a => ¬ d.IsPrimary a ∧ ¬ d.IsRun a).card : ℕ) : ℝ) := by
    calc _ ≤ ∑ a ∈ d.tiles.filter (fun a => ¬ d.IsPrimary a), (1 : ℝ) :=
          Finset.sum_le_sum fun a ha =>
            d.inv_scanScale_pow_le_one (d.mem_tiles.1 (Finset.mem_filter.1 ha).1)
      _ = (((d.tiles.filter fun a => ¬ d.IsPrimary a).card : ℕ) : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hB := d.card_run_le (d.tiles.filter d.IsRun) fun a ha => (Finset.mem_filter.1 ha).2
  have hRp := d.card_repl_le (d.tiles.filter fun a => ¬ d.IsPrimary a ∧ ¬ d.IsRun a)
    fun a ha => ⟨d.mem_tiles.1 (Finset.mem_filter.1 ha).1, (Finset.mem_filter.1 ha).2⟩
  have hM := d.card_marks_le
  have hb0 : (0 : ℝ) ≤ (edgeBoundary d.Λ d.A).card := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (2 * κ.C₀ + 1) ^ 2 := by positivity
  have hK := κ.K_pos
  have hrest0 : (0 : ℝ) ≤ (2 * κ.C₀ + 1) ^ 2 * (edgeBoundary d.Λ d.A).card *
      (2 * ((2 : ℝ) ^ κ.k₀ + 1) ^ 2 + 576 * κ.K * (2 * κ.Sstar + 1) ^ 2) := by
    have := κ.two_le_Sstar
    positivity
  unfold Consts.C
  nlinarith

/-! ### Assembly -/

/-- Proposition 11.2 for the cut-dependent data `d`. -/
theorem decomposition : ∃ (D : Finset (ℤ × ℤ)) (m : ℕ) (X : Fin m → Finset (ℤ × ℤ))
    (f : Fin m → Fin 2) (T : Fin m → Finset (ℤ × ℤ)) (n s : Fin m → ℕ),
    d.A = D ∪ Finset.univ.biUnion X ∧ (∀ i, Disjoint D (X i)) ∧
    Pairwise (Function.onFun Disjoint X) ∧
    (D.card : ℝ) ≤ κ.C * (edgeBoundary d.Λ d.A).card ∧
    (∀ i, (X i).Nonempty ∧ X i ⊆ d.A ∩ T i ∧ nStar ≤ n i ∧
      OpenAI.IsTemplate Ctpl (n i) (s i) (T i) ∧
      OpenAI.IsSeparatedFromCut D₀ (s i) d.Λ d.A (T i) ∧
      collarWidth (n i) ≤ s i ∧
      ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
        OpenAI.ambientEDist (T i) (cutEndpoints d.Λ d.A) ∧
      ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
        OpenAI.ambientEDist (T i) ((Finset.univ.filter fun j => j < i ∧ f j = f i).biUnion X)) ∧
    ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ κ.C * (edgeBoundary d.Λ d.A).card := by
  classical
  obtain ⟨m, e, he⟩ := exists_equiv_fin_rank_monotone d.tiles d.rank
  have htile : ∀ i, d.IsTile (e i).val := fun i => d.mem_tiles.1 (e i).2
  have hinj : ∀ i j, (e i).val = (e j).val → i = j := fun i j h => e.injective (Subtype.ext h)
  obtain ⟨X, hX⟩ : ∃ X : Fin m → Finset (ℤ × ℤ),
      X = fun i => d.A.filter fun z => integerPoint z ∈ d.R.finalRegion (e i).val := ⟨_, rfl⟩
  have hmemX : ∀ i z, z ∈ X i ↔ z ∈ d.A ∧ integerPoint z ∈ d.R.finalRegion (e i).val := by
    intro i z; rw [hX, Finset.mem_filter]
  have hXA : Finset.univ.biUnion X ⊆ d.A := by
    intro z hz
    obtain ⟨i, -, hzi⟩ := Finset.mem_biUnion.1 hz
    exact ((hmemX i z).1 hzi).1
  refine ⟨d.A \ Finset.univ.biUnion X, m, X, fun i => d.R.label (e i).val,
    fun i => d.template (e i).val, fun i => d.scanScale (e i).val,
    fun i => d.pieceScale (e i).val, (Finset.sdiff_union_of_subset hXA).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.disjoint_left.2 fun z hz hzX =>
      (Finset.mem_sdiff.1 hz).2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hzX⟩)
  · intro i j hij
    exact Finset.disjoint_left.2 fun z hzi hzj => hij (hinj i j
      (d.latticeHyp.eq_of_mem_finalRegion ((hmemX i z).1 hzi).2 ((hmemX j z).1 hzj).2))
  · refine d.card_le_of_subset_exceptional _ fun z hz => ?_
    obtain ⟨hzA, hzX⟩ := Finset.mem_sdiff.1 hz
    rcases d.latticeHyp.exists_mem_finalRegion_or_terminal z with ⟨a, ha⟩ | ⟨m, hm, hnt, hball⟩
    · left
      by_cases hdummy : a = .init (.inl ())
      · subst hdummy
        exact d.R.finalRegion_subset_birthRegion _ ha
      · exfalso
        have hat : a ∈ d.tiles := d.mem_tiles.2 ⟨hdummy, z, hzA, ha⟩
        refine hzX (Finset.mem_biUnion.2 ⟨e.symm ⟨a, hat⟩, Finset.mem_univ _, ?_⟩)
        rw [hmemX, Equiv.apply_symm_apply]
        exact ⟨hzA, ha⟩
    · exact Or.inr ⟨m, d.mem_marks.2 hm, hnt, Metric.ball_subset_closedBall hball⟩
  · intro i
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := d.tileSpec (htile i)
    obtain ⟨-, z, hzA, hz⟩ := htile i
    refine ⟨⟨z, (hmemX i z).2 ⟨hzA, hz⟩⟩, fun y hy => ?_, h1, h2, h3, h4, h5, ?_⟩
    · obtain ⟨hyA, hy⟩ := (hmemX i y).1 hy
      exact Finset.mem_inter.2 ⟨hyA, d.mem_template_of_mem_finalRegion hy⟩
    · have hβ : (0 : ℝ) ≤ 2 * (d.scanScale (e i).val : ℝ) ^ (1 - (2 / 1000000 : ℝ)) := by
        positivity
      refine ofReal_lt_ambientEDist_of_le_dist (hβ.trans_lt h6) h6 fun x hx y hy => ?_
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hji, hf⟩ := (Finset.mem_filter.1 hj).2
      exact d.clearance_le_dist (htile i) (htile j) (fun h => hji.ne (hinj j i h)) (he j i hji)
        hf hx ((hmemX j y).1 hyj).2
  · calc ∑ i, ((d.scanScale (e i).val : ℝ) ^ 100)⁻¹ =
          ∑ a ∈ d.tiles, ((d.scanScale a : ℝ) ^ 100)⁻¹ := by
          rw [← Finset.sum_coe_sort d.tiles]
          exact Equiv.sum_comp e (fun a => ((d.scanScale a.val : ℝ) ^ 100)⁻¹)
      _ ≤ _ := d.sum_le

end Data

end TwoFamilyAssembly

end OpenAI.Geometry

namespace OpenAI

/-- **Proposition 11.2** [OAI265, §11.2]. -/
theorem two_family_decomposition : TwoFamilyDecomposition := by
  intro D₀ Ctpl nStar hnStar
  obtain ⟨κ⟩ := Geometry.TwoFamilyAssembly.nonempty_consts D₀ Ctpl nStar hnStar
  refine ⟨κ.C, fun Λ A _ hb => ?_⟩
  obtain ⟨d, rfl, rfl⟩ := Geometry.TwoFamilyAssembly.exists_data κ Λ A hb
  exact d.decomposition

end OpenAI
