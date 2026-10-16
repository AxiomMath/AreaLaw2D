import OpenAI.Geometry.RepairPartition
import OpenAI.Geometry.InitialSectorColors
import OpenAI.Geometry.InitialLatticePartition
import OpenAI.Geometry.InitialMarkFamily
import OpenAI.Geometry.CellFanCycle

/-!
# The initial configuration as repair data

The initial identifiers (dummy, primaries and belt runs) and the deduplicated marks of the
selected belt cells form a `RepairSetup` satisfying `RepairSetup.LatticeHyp`
[OAI265, §11, `geometry:initial-stars`, lines 325–370].  Each mark is assigned a belt cell
realizing its least incident side `t`; the initial octant star of the mark is the ported sector
assignment of that cell, of radius `t / 64`, so the isolation constant is `a₀ = 1 / 64`.

## Main definitions

* `octantSlot`: the all-midpoint fan slot of an octant.
* `initialRepairSetup`: the repair data of the initial configuration.

## Main statements

* `cellFanPolygon_octantSlot`: the all-midpoint fan triangles are the octant triangles.
* `initialRepairSetup_latticeHyp`: the initial configuration satisfies the lattice hypotheses
  of the repair.
-/

noncomputable section

namespace OpenAI.Geometry

/-- The all-midpoint fan slot occupying octant `k`: slot `(side, segment)` is octant
`2 * side + segment - 1`. -/
def octantSlot (k : Fin 8) : CellFanSlot (fun _ : Fin 4 ↦ true) :=
  ⟨⟨(k.val + 1) % 8 / 2, by omega⟩, ⟨(k.val + 1) % 2, by simp; omega⟩⟩

theorem octantSlot_bijective : Function.Bijective octantSlot := by
  decide

/-- The all-midpoint fan triangle of slot `octantSlot k` of the square of half-side `r`
centered at `c` is the octant triangle `k` about `c`. -/
theorem cellFanPolygon_octantSlot (c : ℝ × ℝ) (ℓ : ℕ) (k : Fin 8) :
    (cellFanPolygon (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0)
      (fun _ ↦ true) (octantSlot k)).region = octantTriangle c ((2 : ℝ) ^ ℓ / 2) k := by
  rw [octantTriangle_eq_convexHull c (by positivity) k]
  change convexHull ℝ {cellFanCenter _ ℓ (0, 0), cellFanStart _ ℓ (0, 0) _ (octantSlot k),
    cellFanEnd _ ℓ (0, 0) _ (octantSlot k)} = _
  have hc : cellFanCenter (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0) = c := by
    ext <;> simp [cellFanCenter]
  rw [cellFanStart_eq, cellFanEnd_eq, hc]
  fin_cases k <;> simp [octantSlot, cellFanSideVector, octantRay]

/-- Consecutive octants are consecutive fan slots. -/
theorem cellFanNext_octantSlot (k : Fin 8) : cellFanNext (octantSlot k) = octantSlot (k + 1) := by
  revert k
  decide

/-- A mark of a dyadic cell of side at least two lies on the integer translate of the origin. -/
theorem exists_eq_add_integerPoint_of_mem_beltCellMarks {o v : ℝ × ℝ} {ℓ : ℕ} {z : ℤ × ℤ}
    (hℓ : 1 ≤ ℓ) (hv : v ∈ beltCellMarks o ℓ z) :
    ∃ a : ℤ × ℤ, v = o + integerPoint a := by
  classical
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨(2 ^ ℓ * z.1 + 2 ^ (ℓ - 1) * p.1.val, 2 ^ ℓ * z.2 + 2 ^ (ℓ - 1) * p.2.val), ?_⟩
  have h2 : (2 : ℝ) ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  ext <;> simp [integerPoint, h2] <;> ring

section

variable (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
  (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
  (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
  (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
  (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)

/-- Within distance one sixty-fourth of the fine-cell side of a mark, an initial birth region
is the union of the octants that the sector assignment gives to it. -/
theorem initialBirthRegion_inter_closedBall_eq_iUnion_octantConeAt
    (i : InitialRegionIndex o k₀ Z C a b hC h₀) :
    initialBirthRegion o k₀ Z C a b hC h₀ i ∩
        Metric.closedBall v (1 / 64 * (2 : ℝ) ^ fineScaleIndex k) =
      ⋃ (j : Fin 8) (_ : initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
          (octantSlot j) = i),
        octantConeAt v j ∩ Metric.closedBall v (1 / 64 * (2 : ℝ) ^ fineScaleIndex k) := by
  have hspec := (Classical.choose_spec
    (exists_unique_initialRegion_sector_assignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.2 i
  have hr : (2 : ℝ) ^ (fineScaleIndex k - 5) / 2 = 1 / 64 * (2 : ℝ) ^ fineScaleIndex k := by
    have := fineScaleIndex_closed_half_radius_eq k (h₀.trans hk₀)
    linarith
  change _ ∩ Metric.closedBall v ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) = _ at hspec
  rw [← hr]
  refine hspec.trans ?_
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨s, hs⟩, hx⟩
    obtain ⟨j, rfl⟩ := octantSlot_bijective.2 s
    rw [cellFanPolygon_octantSlot] at hx
    exact ⟨j, hs, hx⟩
  · rintro ⟨j, hj, hx⟩
    refine ⟨⟨octantSlot j, hj⟩, ?_⟩
    change x ∈ (cellFanPolygon _ _ _ _ (octantSlot j)).region
    rw [cellFanPolygon_octantSlot]
    exact hx

/-- Distinct identifiers of consecutive octants about a mark have distinct colors. -/
theorem initialRegionColor_initialSectorAssignment_ne (j : Fin 8)
    (hne : initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv (octantSlot j) ≠
      initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv (octantSlot (j + 1))) :
    initialRegionColor o k₀ Z C a b hC h₀
        (initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv (octantSlot j)) ≠
      initialRegionColor o k₀ Z C a b hC h₀
        (initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv (octantSlot (j + 1))) :=
  fun h ↦ hne ((initialRegion_sector_assignment_adjacent_colors_eq_iff o k₀ Z C a b hC h₀
    k z v hk₀ hz hv (octantSlot j) (octantSlot (j + 1)) (Or.inl (by
      rw [← cellFanNext_octantSlot]
      exact cellFanEnd_eq_cellFanStart_next _ _ _ _))).mp h)

end

section

variable (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
  (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (M : Finset (ℝ × ℝ))
  (kOf : M → ℕ) (zOf : M → ℤ × ℤ) (hkOf : ∀ v, k₀ ≤ kOf v)
  (hzOf : ∀ v, zOf v ∈ fineLayerIndices dyadicOrigin (kOf v) (fineScaleIndex (kOf v)) Z C)
  (hvOf : ∀ v, v.val ∈ beltCellMarks dyadicOrigin (fineScaleIndex (kOf v)) (zOf v))
  (Sstar : ℝ)

/-- The repair data of the initial configuration: initial identifiers with their colors and
birth regions, the marks `M` at their assigned cells `(kOf v, zOf v)` with scale the cell side,
octant identifiers from the sector assignment of that cell, and `a₀ = 1 / 64`. -/
def initialRepairSetup :
    RepairSetup (InitialRegionIndex dyadicOrigin k₀ Z C a b hC h₀) M where
  pos₀ v := v.val
  scale₀ v := (2 : ℝ) ^ fineScaleIndex (kOf v)
  oct₀ v k := initialSectorAssignment dyadicOrigin k₀ Z C a b hC h₀ (kOf v) (zOf v) v.val
    (hkOf v) (hzOf v) (hvOf v) (octantSlot k)
  label₀ := initialRegionColor dyadicOrigin k₀ Z C a b hC h₀
  birth₀ := initialBirthRegion dyadicOrigin k₀ Z C a b hC h₀
  Sstar := Sstar
  a₀ := 1 / 64

/-- The initial configuration satisfies the lattice hypotheses of the repair, given a stopping
scale with the trim margins, mark scales above it, and marks separated by a quarter of the
larger scale. -/
theorem initialRepairSetup_latticeHyp (hZ : Z.Nonempty) (hSstar : 2 ≤ Sstar)
    (hmargin : ∀ S, Sstar ≤ S → repairHalfSide S ≤ 1 / 64 / 1000 * S)
    (hscale : ∀ v, Sstar ≤ (2 : ℝ) ^ fineScaleIndex (kOf v))
    (hsep : ∀ v w : M, v ≠ w →
      max ((2 : ℝ) ^ fineScaleIndex (kOf v)) ((2 : ℝ) ^ fineScaleIndex (kOf w)) / 4 ≤
        dist v.val w.val) :
    (initialRepairSetup k₀ Z C a b hC h₀ M kOf zOf hkOf hzOf hvOf Sstar).LatticeHyp := by
  have hlat (z : ℤ × ℤ) := exists_unique_initialOpenRegion_integerPoint k₀ Z C a b hC h₀ hZ z
  have hmem := initialBirthRegion_lattice_mem_iff_initialOpenRegion k₀ Z C a b hC h₀
  refine ⟨⟨⟨show (0 : ℝ) < 1 / 64 by norm_num, show (1 / 64 : ℝ) < 1 / 2 by norm_num,
    hSstar, hmargin, hscale, fun v w hvw ↦ ?_⟩,
    fun v i ↦ ?_, fun v j ↦ ?_⟩, fun v ↦ ?_, fun z i j hi hj ↦ ?_, fun z ↦ ?_⟩
  · have hmax : 0 ≤ max ((2 : ℝ) ^ fineScaleIndex (kOf v)) ((2 : ℝ) ^ fineScaleIndex (kOf w)) :=
      le_max_of_le_left (by positivity)
    change 1 / 64 * max ((2 : ℝ) ^ fineScaleIndex (kOf v)) ((2 : ℝ) ^ fineScaleIndex (kOf w)) ≤
      dist v.val w.val
    linarith [hsep v w hvw]
  · exact initialBirthRegion_inter_closedBall_eq_iUnion_octantConeAt dyadicOrigin k₀ Z C a b hC h₀
      (kOf v) (zOf v) v.val (hkOf v) (hzOf v) (hvOf v) i
  · exact initialRegionColor_initialSectorAssignment_ne dyadicOrigin k₀ Z C a b hC h₀
      (kOf v) (zOf v) v.val (hkOf v) (hzOf v) (hvOf v) j
  · have hf : 1 ≤ fineScaleIndex (kOf v) := by
      by_contra hf
      have h0 : fineScaleIndex (kOf v) = 0 := by omega
      have := hscale v
      rw [h0, pow_zero] at this
      linarith
    exact exists_eq_add_integerPoint_of_mem_beltCellMarks hf (hvOf v)
  · exact (hlat z).unique ((hmem i z).mp hi) ((hmem j z).mp hj)
  · obtain ⟨i, hi, -⟩ := hlat z
    exact ⟨i, (hmem i z).mpr hi⟩

end

end OpenAI.Geometry
