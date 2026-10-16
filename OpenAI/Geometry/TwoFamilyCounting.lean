import OpenAI.Geometry.RepairTree
import OpenAI.Geometry.TwoFamilyTemplates
import OpenAI.Geometry.CellCounting
import OpenAI.Geometry.PolynomialBudget
import OpenAI.Geometry.DyadicClosure

/-!
# Counting exceptional sites and repair tiles

The counts behind `|D| ≤ C b` and `∑ n_i ^ {-100} ≤ C b` in Proposition 11.2
[OAI265, §11, `geometry:descendant-count`, `geometry:total-repairs` and `geometry:bad-sites`,
lines 664–688]: a closed sup-norm ball and the dummy neighborhood contain boundedly many lattice
points, and the marks of the repair number at most a constant times any bound on the initial
marks per layer that decays geometrically in the layer.

## Main statements

* `card_latticeTemplate_closedBall_le`, `card_latticeTemplate_closure_dyadicNeighborhood_le`.
* `exists_ncard_isMark_le`: the total number of repair marks (`geometry:total-repairs`).

## Implementation notes

The total is bounded by summing the layer form `C (k + 1) ^ C` of the descendant count against
the initial marks of layer `k`, at most `B 2 ^ (-δ k)`; the resulting series
`∑ (k + 1) ^ C 2 ^ (-δ k)` converges for every `δ > 0` (`summable_rpow_mul_two_rpow_neg`), so
`K` is `C` times one more than its sum.
-/

noncomputable section

namespace OpenAI.Geometry

/-- The integers in `[a, b]` number at most `b - a + 1`. -/
theorem card_Icc_ceil_floor_le {a b : ℝ} (h : a ≤ b) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b - a + 1 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le b
  have h2 := Int.le_ceil a
  have : ((⌊b⌋ + 1 - ⌈a⌉).toNat : ℝ) = (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℤ) : ℝ) := rfl
  rw [this, Int.toNat_of_nonneg]
  · push_cast; linarith
  · have : (⌈a⌉ : ℝ) < ⌊b⌋ + 2 := by linarith [Int.ceil_lt_add_one a, Int.lt_floor_add_one b]
    have : ⌈a⌉ < ⌊b⌋ + 2 := by exact_mod_cast this
    omega

/-- A closed sup-norm ball of radius `ρ` contains at most `(2 ρ + 1) ^ 2` lattice points. -/
theorem card_latticeTemplate_closedBall_le (v : ℝ × ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((latticeTemplate (Metric.closedBall v ρ)).card : ℝ) ≤ (2 * ρ + 1) ^ 2 := by
  have hsub : latticeTemplate (Metric.closedBall v ρ) ⊆
      Finset.Icc ⌈v.1 - ρ⌉ ⌊v.1 + ρ⌋ ×ˢ Finset.Icc ⌈v.2 - ρ⌉ ⌊v.2 + ρ⌋ := by
    intro z hz
    rw [mem_latticeTemplate Metric.isBounded_closedBall, Metric.mem_closedBall,
      Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le] at hz
    simp only [integerPoint] at hz
    simp only [Finset.mem_product, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  calc ((latticeTemplate (Metric.closedBall v ρ)).card : ℝ)
      ≤ ((Finset.Icc ⌈v.1 - ρ⌉ ⌊v.1 + ρ⌋ ×ˢ Finset.Icc ⌈v.2 - ρ⌉ ⌊v.2 + ρ⌋).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((Finset.Icc ⌈v.1 - ρ⌉ ⌊v.1 + ρ⌋).card : ℝ) * (Finset.Icc ⌈v.2 - ρ⌉ ⌊v.2 + ρ⌋).card := by
        rw [Finset.card_product]; push_cast; ring
    _ ≤ (v.1 + ρ - (v.1 - ρ) + 1) * (v.2 + ρ - (v.2 - ρ) + 1) := by
        exact mul_le_mul (card_Icc_ceil_floor_le (by linarith))
          (card_Icc_ceil_floor_le (by linarith)) (Nat.cast_nonneg _) (by linarith)
    _ = (2 * ρ + 1) ^ 2 := by ring

/-- A closed dyadic cell of side `2 ^ k` lies in the sup-norm ball of radius `2 ^ k / 2` about
its center. -/
theorem closure_dyadicCell_subset_closedBall (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    closure (dyadicCell o k z) ⊆ Metric.closedBall
      (o.1 + (2 : ℝ) ^ k * (z.1 + 1 / 2), o.2 + (2 : ℝ) ^ k * (z.2 + 1 / 2)) ((2 : ℝ) ^ k / 2) := by
  rw [closure_dyadicCell]
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le,
    abs_le]
  dsimp only at hx1 hx2 hy1 hy2 ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- A closed dyadic cell of side `2 ^ k` contains at most `(2 ^ k + 1) ^ 2` lattice points. -/
theorem card_latticeTemplate_closure_dyadicCell_le (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    ((latticeTemplate (closure (dyadicCell o k z))).card : ℝ) ≤ ((2 : ℝ) ^ k + 1) ^ 2 := by
  calc ((latticeTemplate (closure (dyadicCell o k z))).card : ℝ)
      ≤ ((latticeTemplate (Metric.closedBall
          (o.1 + (2 : ℝ) ^ k * (z.1 + 1 / 2), o.2 + (2 : ℝ) ^ k * (z.2 + 1 / 2))
          ((2 : ℝ) ^ k / 2))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (latticeTemplate_mono Metric.isBounded_closedBall
          (closure_dyadicCell_subset_closedBall o k z))
    _ ≤ (2 * ((2 : ℝ) ^ k / 2) + 1) ^ 2 := card_latticeTemplate_closedBall_le _ (by positivity)
    _ = ((2 : ℝ) ^ k + 1) ^ 2 := by ring

/-- The closed dummy neighborhood `N_k` contains at most `(2 C + 1) ^ 2 |Z| (2 ^ k + 1) ^ 2`
lattice points (`geometry:bad-sites`). -/
theorem card_latticeTemplate_closure_dyadicNeighborhood_le (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    ((latticeTemplate (closure (dyadicNeighborhood o k Z C))).card : ℝ) ≤
      (2 * C + 1) ^ 2 * Z.card * ((2 : ℝ) ^ k + 1) ^ 2 := by
  set A := ambientDilation (occupiedCellIndices o k Z) C
  have hU : closure (dyadicNeighborhood o k Z C) = ⋃ z ∈ A, closure (dyadicCell o k z) := by
    rw [dyadicNeighborhood, Finset.closure_biUnion]
  have hbdd : ∀ z, Bornology.IsBounded (closure (dyadicCell o k z)) := fun z =>
    Metric.isBounded_closedBall.subset (closure_dyadicCell_subset_closedBall o k z)
  have hsub : latticeTemplate (closure (dyadicNeighborhood o k Z C)) ⊆
      A.biUnion fun z => latticeTemplate (closure (dyadicCell o k z)) := by
    intro p hp
    rw [hU, mem_latticeTemplate ((Bornology.isBounded_biUnion_finset A).mpr fun z _ => hbdd z)]
      at hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    exact Finset.mem_biUnion.mpr ⟨z, hz, (mem_latticeTemplate (hbdd z)).mpr hpz⟩
  have hA : (A.card : ℝ) ≤ (2 * C + 1) ^ 2 * Z.card := by
    have h1 := card_ambientDilation_le (occupiedCellIndices o k Z) C
    have h2 : (occupiedCellIndices o k Z).card ≤ Z.card := Finset.card_image_le
    have : A.card ≤ (2 * C + 1) ^ 2 * Z.card := h1.trans (Nat.mul_le_mul_left _ h2)
    exact_mod_cast this
  calc ((latticeTemplate (closure (dyadicNeighborhood o k Z C))).card : ℝ)
      ≤ ((A.biUnion fun z => latticeTemplate (closure (dyadicCell o k z))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ z ∈ A, ((latticeTemplate (closure (dyadicCell o k z))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ A, ((2 : ℝ) ^ k + 1) ^ 2 :=
        Finset.sum_le_sum fun z _ => card_latticeTemplate_closure_dyadicCell_le o k z
    _ = A.card * ((2 : ℝ) ^ k + 1) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * C + 1) ^ 2 * Z.card * ((2 : ℝ) ^ k + 1) ^ 2 := by gcongr

/-- A real power of `k + 1` against a geometric decay `2 ^ (-δ k)` is summable. -/
theorem summable_rpow_mul_two_rpow_neg (p : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ p * (2 : ℝ) ^ (-δ * k) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (-δ) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := hr ▸ Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, p ≤ N := ⟨⌈p⌉₊, Nat.le_ceil p⟩
  have hg0 : Summable fun k : ℕ => (k : ℝ) ^ N * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one N
      (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  have hg1 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ N * r ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr hg0
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hg1.mul_left r⁻¹)
  · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)
  have hk : (1 : ℝ) ≤ k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have e1 : (2 : ℝ) ^ (-δ * k) = r ^ k := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have e2 : r⁻¹ * (((k + 1 : ℕ) : ℝ) ^ N * r ^ (k + 1)) = ((k : ℝ) + 1) ^ N * r ^ k := by
    rw [pow_succ]; push_cast; field_simp
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0.le _)
  calc ((k : ℝ) + 1) ^ p ≤ ((k : ℝ) + 1) ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk hN
    _ = ((k : ℝ) + 1) ^ N := Real.rpow_natCast _ _

/-- **Total repairs** [OAI265, `geometry:descendant-count` and `geometry:total-repairs`].  If each
initial mark of layer `k` has scale at most `M_b 2 ^ k` and layer `k` carries at most
`B 2 ^ (-δ k)` initial marks, the repair creates at most `K B` marks, with `K` depending only on
`S_*`, `M_b` and `δ`. -/
theorem exists_ncard_isMark_le (Sstar Mb δ : ℝ) (hS : 1 < Sstar) (hMb : 0 < Mb) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {I M₀ : Type} [Finite M₀] (R : RepairSetup I M₀),
      R.Sstar = Sstar → R.TreeHyp → ∀ (layer : M₀ → ℕ) (B : ℝ),
        (∀ r, R.scale₀ r ≤ Mb * 2 ^ layer r) →
        (∀ k, ({r | layer r = k}.ncard : ℝ) ≤ B * (2 : ℝ) ^ (-δ * k)) →
        ({m : RepairMark M₀ | R.IsMark m}.ncard : ℝ) ≤ K * B := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_repair_descendant_count_layer_bound hS hMb
  have hsum := summable_rpow_mul_two_rpow_neg C hδ
  set T := ∑' k : ℕ, ((k : ℝ) + 1) ^ C * (2 : ℝ) ^ (-δ * k)
  have hw : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) ^ C * (2 : ℝ) ^ (-δ * k) := fun k => by positivity
  have hT : 0 ≤ T := tsum_nonneg hw
  refine ⟨C * (T + 1), by positivity, ?_⟩
  intro I M₀ _ R hRS hR layer B hscale hlayer
  have hB : 0 ≤ B := by
    have := (Nat.cast_nonneg _).trans (hlayer 0)
    simpa using this
  have : Fintype M₀ := Fintype.ofFinite M₀
  have hroot : ∀ r, ({m : RepairMark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ) ≤
      C * ((layer r : ℝ) + 1) ^ C := by
    intro r
    obtain ⟨G, hG, hle⟩ := hR.exists_ncard_isMark_root_le r
    have hS0 : 0 < R.scale₀ r := by linarith [hR.Sstar_le_scale₀ r, hR.two_le_Sstar]
    refine hle.trans (hcount (layer r) _ hS0 (hscale r) G ?_)
    rcases hG with rfl | hG
    · simpa [← hRS] using hR.Sstar_le_scale₀ r
    · rwa [← hRS]
  have hfin := hR.finite_isMark
  set F := hfin.toFinset
  have hF : F = Finset.univ.biUnion fun r => F.filter (fun m => m.root = r) := by
    ext m; simp
  have hFr : ∀ r, ((F.filter fun m => m.root = r).card : ℝ) =
      ({m : RepairMark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ) := by
    intro r
    rw [← Set.ncard_coe_finset]
    congr 2
    ext m
    simp [F]
  have hfib : ∀ k : ℕ, ((Finset.univ.filter fun r => layer r = k).card : ℝ) ≤
      B * (2 : ℝ) ^ (-δ * k) := by
    intro k
    rw [← Set.ncard_coe_finset]
    simpa using hlayer k
  calc ({m : RepairMark M₀ | R.IsMark m}.ncard : ℝ) = F.card := by
        rw [Set.ncard_eq_toFinset_card _ hfin]
    _ ≤ ∑ r, ((F.filter fun m => m.root = r).card : ℝ) := by
        conv_lhs => rw [hF]
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ r, C * ((layer r : ℝ) + 1) ^ C :=
        Finset.sum_le_sum fun r _ => (hFr r).le.trans (hroot r)
    _ = ∑ k ∈ Finset.univ.image layer,
          ∑ r ∈ Finset.univ.filter (fun r => layer r = k), C * ((layer r : ℝ) + 1) ^ C :=
        (Finset.sum_fiberwise_of_maps_to
          (fun r _ => Finset.mem_image_of_mem _ (Finset.mem_univ r)) _).symm
    _ = ∑ k ∈ Finset.univ.image layer,
          ((Finset.univ.filter fun r => layer r = k).card : ℝ) * (C * ((k : ℝ) + 1) ^ C) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => C * ((k : ℝ) + 1) ^ C)
          (fun r hr => by rw [(Finset.mem_filter.mp hr).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.univ.image layer, B * (2 : ℝ) ^ (-δ * k) * (C * ((k : ℝ) + 1) ^ C) :=
        Finset.sum_le_sum fun k _ => by gcongr; exact hfib k
    _ = C * B * ∑ k ∈ Finset.univ.image layer, ((k : ℝ) + 1) ^ C * (2 : ℝ) ^ (-δ * k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ C * B * T := by
        gcongr
        exact hsum.sum_le_tsum _ fun k _ => hw k
    _ ≤ C * (T + 1) * B := by nlinarith

end OpenAI.Geometry
