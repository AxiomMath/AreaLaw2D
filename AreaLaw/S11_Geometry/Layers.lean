import AreaLaw.S11_Geometry.Exponents
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Real

/-!
# §11.3 Layers

The translated dyadic grid, the neighbourhoods `N_k` and layers `D_k` around a finite endpoint
set `Z`, the separation of non-adjacent layers, and the irrational origin that keeps lattice
sites off every supporting line. Everything is stated on `Fin d → ℝ` with its sup metric.

Digest `digest/11-geometry.md` D11.5–D11.7, D11.16.
-/

open Set Metric

namespace AreaLaw

namespace Geometry

variable {d : ℕ}

/-! ## D11.5 Origin and dyadic cells -/

/-- D11.5. `o = (√2, √3)`. -/
noncomputable def o₂ : Fin 2 → ℝ := ![√2, √3]

/-- D11.5. For `r = 2^k`: half-open cells `C_{k,z} = o + r(z + [0,1)^d)`, `z ∈ ℤ^d`, nested
(`C_{k+1,z'} = ⋃_{e ∈ {0,1}^d} C_{k,2z'+e}`). Half-open cells fix indices; closures fix birth
regions. The integer `C₀` is a parameter of the later declarations. -/
def cell (o : Fin d → ℝ) (k : ℕ) (z : Fin d → ℤ) : Set (Fin d → ℝ) :=
  univ.pi fun i ↦ Ico (o i + 2 ^ k * z i) (o i + 2 ^ k * (z i + 1))

/-- The index of the cell `C_{k,z}` containing `x`. -/
noncomputable def cellIndex (o : Fin d → ℝ) (k : ℕ) (x : Fin d → ℝ) : Fin d → ℤ :=
  fun i ↦ ⌊(x i - o i) / 2 ^ k⌋

theorem mem_cell_iff {o : Fin d → ℝ} {k : ℕ} {z : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ cell o k z ↔ cellIndex o k x = z := by
  have hr : (0 : ℝ) < 2 ^ k := by positivity
  simp only [cell, mem_univ_pi, mem_Ico, funext_iff, cellIndex, Int.floor_eq_iff,
    le_div_iff₀ hr, div_lt_iff₀ hr]
  exact forall_congr' fun i ↦ by constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem cellIndex_succ (o : Fin d → ℝ) (k : ℕ) (x : Fin d → ℝ) :
    cellIndex o (k + 1) x = fun i ↦ cellIndex o k x i / 2 := by
  funext i
  simp only [cellIndex, pow_succ, ← div_div]
  exact_mod_cast Int.floor_div_natCast ((x i - o i) / 2 ^ k) 2

theorem closure_cell (o : Fin d → ℝ) (k : ℕ) (z : Fin d → ℤ) :
    closure (cell o k z) = univ.pi fun i ↦ Icc (o i + 2 ^ k * z i) (o i + 2 ^ k * (z i + 1)) := by
  rw [cell, closure_pi_set]
  congr! with i
  exact closure_Ico (by have : (0 : ℝ) < 2 ^ k := (by positivity); linarith)

/-- D11.5 (nesting). `C_{k+1,z'} = ⋃_{e ∈ {0,1}^d} C_{k,2z'+e}`. -/
theorem cell_succ (o : Fin d → ℝ) (k : ℕ) (z' : Fin d → ℤ) :
    cell o (k + 1) z' = ⋃ e : Fin d → Fin 2, cell o k (fun i ↦ 2 * z' i + e i) := by
  ext x
  simp only [mem_iUnion, mem_cell_iff, cellIndex_succ, funext_iff]
  refine ⟨fun h ↦ ⟨fun i ↦ ⟨(cellIndex o k x i % 2).toNat, by omega⟩, fun i ↦ ?_⟩,
    fun ⟨e, he⟩ i ↦ ?_⟩
  · have := h i; simp only; omega
  · have := he i; have := (e i).2; omega

/-- Two closed cell intervals: points differ by at most `(|u-v|+1)r` and at least `(|u-v|-1)r`. -/
theorem abs_sub_bounds {a r x y : ℝ} {u v : ℤ} (hr : 0 < r)
    (hx : x ∈ Icc (a + r * u) (a + r * (u + 1))) (hy : y ∈ Icc (a + r * v) (a + r * (v + 1))) :
    |x - y| ≤ (|(u : ℝ) - v| + 1) * r ∧ (|(u : ℝ) - v| - 1) * r ≤ |x - y| := by
  obtain ⟨hx₁, hx₂⟩ := hx; obtain ⟨hy₁, hy₂⟩ := hy
  rcases le_total (u : ℝ) v with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h)]
    constructor
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_sub_comm]; exact (by nlinarith : _ ≤ y - x).trans (le_abs_self _)
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    constructor
    · rw [abs_le]; constructor <;> nlinarith
    · exact (by nlinarith : _ ≤ x - y).trans (le_abs_self _)

/-! ## D11.6 Neighbourhoods and layers -/

/-- D11.6. `𝒵_k = {z : C_{k,z} ∩ Z ≠ ∅}`. -/
noncomputable def 𝒵 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (k : ℕ) : Finset (Fin d → ℤ) :=
  Z.image (cellIndex o k)

/-- D11.6. The indices `z` with `dist_∞(z, 𝒵_k) ≤ C₀`. -/
noncomputable def NIndex (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ : ℕ) (k : ℕ) :
    Finset (Fin d → ℤ) :=
  (𝒵 o Z k).biUnion fun v ↦ Finset.Icc (v - fun _ ↦ (C₀ : ℤ)) (v + fun _ ↦ (C₀ : ℤ))

/-- D11.6. `N_k = ⋃_{dist_∞(z,𝒵_k) ≤ C₀} C_{k,z}`. -/
def N (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ : ℕ) (k : ℕ) : Set (Fin d → ℝ) :=
  ⋃ z ∈ NIndex o Z C₀ k, cell o k z

/-- D11.6. The layer `D_k = N_{k+1} \ N_k`. -/
def D (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ : ℕ) (k : ℕ) : Set (Fin d → ℝ) :=
  N o Z C₀ (k + 1) \ N o Z C₀ k

/-- D11.6. The indices of the `r`-cells of `D_k`: children of `N_{k+1}`-indices not in `N_k`. -/
noncomputable def DIndex (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ : ℕ) (k : ℕ) :
    Finset (Fin d → ℤ) :=
  (NIndex o Z C₀ (k + 1)).biUnion (fun w ↦ Finset.Icc (fun i ↦ 2 * w i) (fun i ↦ 2 * w i + 1))
    \ NIndex o Z C₀ k

/-- D11.6.3. The number of layer cells per endpoint, `2^d (2C₀+1)^d`. -/
def layerCount (d C₀ : ℕ) : ℕ := 2 ^ d * (2 * C₀ + 1) ^ d

/-- D11.6.3 at `d = 2`: `4(2C₀+1)²`. -/
theorem layerCount_two (C₀ : ℕ) : layerCount 2 C₀ = 4 * (2 * C₀ + 1) ^ 2 := by
  simp [layerCount]

theorem mem_NIndex_iff {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ} {z : Fin d → ℤ} :
    z ∈ NIndex o Z C₀ k ↔ ∃ w ∈ Z, ∀ i, |z i - cellIndex o k w i| ≤ C₀ := by
  simp only [NIndex, 𝒵, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc, Pi.le_def,
    Pi.sub_apply, Pi.add_apply, abs_le]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, h₁, h₂⟩
    exact ⟨w, hw, fun i ↦ ⟨by linarith [h₁ i], by linarith [h₂ i]⟩⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, fun i ↦ by linarith [(h i).1], fun i ↦ by linarith [(h i).2]⟩

theorem mem_N_iff {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ} {x : Fin d → ℝ} :
    x ∈ N o Z C₀ k ↔ cellIndex o k x ∈ NIndex o Z C₀ k := by
  simp [N, mem_cell_iff]

theorem D_eq_iUnion (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) :
    D o Z C₀ k = ⋃ z ∈ DIndex o Z C₀ k, cell o k z := by
  ext x
  simp only [D, mem_sdiff, mem_N_iff, mem_iUnion, mem_cell_iff, exists_prop, DIndex,
    Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_Icc, Pi.le_def, cellIndex_succ]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, ⟨⟨_, h₁, fun i ↦ by omega, fun i ↦ by omega⟩, h₂⟩, rfl⟩
  · rintro ⟨_, ⟨⟨w, hw, h₁, h₂⟩, h₃⟩, rfl⟩
    refine ⟨?_, h₃⟩
    convert hw using 1
    funext i; have := h₁ i; have := h₂ i; omega

/-- D11.6.3. `N_{k+1}` has `≤ (2C₀+1)^d|Z|` cells, each with `2^d` children. -/
theorem step_11_6_3 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) :
    (DIndex o Z C₀ k).card ≤ layerCount d C₀ * Z.card := by
  have hI (a b : Fin d → ℤ) (n : ℕ) (h : ∀ i, b i + 1 - a i = n) :
      (Finset.Icc a b).card = n ^ d := by
    simp [Pi.card_Icc, Int.card_Icc, h]
  calc (DIndex o Z C₀ k).card
      ≤ ∑ w ∈ NIndex o Z C₀ (k + 1), 2 ^ d :=
        (Finset.card_le_card Finset.sdiff_subset).trans <| Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun w _ ↦ (hI _ _ 2 fun i ↦ by simp; ring).le)
    _ ≤ 2 ^ d * ∑ v ∈ 𝒵 o Z (k + 1), (2 * C₀ + 1) ^ d := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        refine Nat.mul_le_mul_left _ (Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun v _ ↦ (hI _ _ (2 * C₀ + 1) fun i ↦ ?_).le))
        simp; ring
    _ ≤ layerCount d C₀ * Z.card := by
        rw [Finset.sum_const, smul_eq_mul, layerCount, mul_assoc, mul_comm (Finset.card _)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ Finset.card_image_le)

/-- D11.6.2. For fixed `x` and large `k`, `x` and some `w ∈ Z` lie in cells whose indices differ
by `≤ 1`. -/
theorem step_11_6_2 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (hZ : Z.Nonempty) (C₀ : ℕ)
    (hC₀ : 2 ≤ C₀) (x : Fin d → ℝ) : ∃ k, x ∈ N o Z C₀ k := by
  obtain ⟨w, hw⟩ := hZ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - o‖ + ‖w - o‖) (by norm_num : (1 : ℝ) < 2)
  have hr : (0 : ℝ) < 2 ^ k := by positivity
  have hf (y : Fin d → ℝ) (hy : ‖y - o‖ < 2 ^ k) (i : Fin d) :
      -1 ≤ cellIndex o k y i ∧ cellIndex o k y i ≤ 0 := by
    have := abs_lt.1 ((norm_le_pi_norm (y - o) i).trans_lt hy)
    simp only [Pi.sub_apply] at this
    refine ⟨Int.le_floor.2 ?_, Int.lt_add_one_iff.1 (Int.floor_lt.2 ?_)⟩
    · rw [le_div_iff₀ hr]; push_cast; linarith
    · rw [div_lt_iff₀ hr]; push_cast; linarith
  refine ⟨k, mem_N_iff.2 (mem_NIndex_iff.2 ⟨w, hw, fun i ↦ ?_⟩)⟩
  have := hf x (by linarith [norm_nonneg (w - o)]) i
  have := hf w (by linarith [norm_nonneg (x - o)]) i
  rw [abs_le]; constructor <;> omega

/-- D11.6.4. A point of `closure D_k` is at sup distance `≥ C₀r` from every `w ∈ Z`. -/
theorem step_11_6_4 {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ closure (D o Z C₀ k)) {w : Fin d → ℝ} (hw : w ∈ Z) :
    C₀ * 2 ^ k ≤ dist x w := by
  rw [D_eq_iUnion, Finset.closure_biUnion] at hx
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 hx
  have hu : u ∉ NIndex o Z C₀ k := (Finset.mem_sdiff.1 hu).2
  -- some coordinate differs from the endpoint-occupied index by `≥ C₀ + 1`
  obtain ⟨i, hi⟩ : ∃ i, (C₀ : ℤ) + 1 ≤ |u i - cellIndex o k w i| := by
    by_contra! h
    exact hu (mem_NIndex_iff.2 ⟨w, hw, fun i ↦ by have := h i; omega⟩)
  have hw' : w ∈ closure (cell o k (cellIndex o k w)) := subset_closure (mem_cell_iff.2 rfl)
  rw [closure_cell, mem_univ_pi] at hxu hw'
  have hi : (C₀ : ℝ) + 1 ≤ |(u i : ℝ) - cellIndex o k w i| := by exact_mod_cast hi
  -- cells whose indices differ by `m` in one coordinate have closures at distance `≥ (m-1)r`
  have := (abs_sub_bounds (by positivity) (hxu i) (hw' i)).2
  calc (C₀ : ℝ) * 2 ^ k ≤ |x i - w i| := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) k]
    _ ≤ dist x w := by rw [← Real.dist_eq]; exact dist_le_pi_dist x w i

/-- D11.6.5. A point of `closure D_k` is within `2(C₀+1)r` of some `w ∈ Z`. -/
theorem step_11_6_5 {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ closure (D o Z C₀ k)) : ∃ w ∈ Z, dist x w ≤ 2 * (C₀ + 1) * 2 ^ k := by
  have hx : x ∈ closure (N o Z C₀ (k + 1)) := closure_mono sdiff_subset hx
  rw [N, Finset.closure_biUnion] at hx
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 hx
  obtain ⟨w, hw, huw⟩ := mem_NIndex_iff.1 hu
  have hw' : w ∈ closure (cell o (k + 1) (cellIndex o (k + 1) w)) :=
    subset_closure (mem_cell_iff.2 rfl)
  rw [closure_cell, mem_univ_pi] at hxu hw'
  refine ⟨w, hw, (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_⟩
  have := (abs_sub_bounds (by positivity) (hxu i) (hw' i)).1
  have h : |(u i : ℝ) - cellIndex o (k + 1) w i| ≤ C₀ := by exact_mod_cast huw i
  rw [Real.dist_eq]
  calc |x i - w i| ≤ (|(u i : ℝ) - cellIndex o (k + 1) w i| + 1) * 2 ^ (k + 1) := this
    _ ≤ (C₀ + 1) * 2 ^ (k + 1) := by gcongr
    _ = 2 * (C₀ + 1) * 2 ^ k := by ring

/-- D11.6 (geometry:layer-distance). `𝒵_k = {z : C_{k,z} ∩ Z ≠ ∅}`,
`N_k = ⋃_{dist_∞(z,𝒵_k) ≤ C₀} C_{k,z}` (index distance in sup norm). Then
- `N_k ⊆ N_{k+1}`, `⋃_k N_k = ℝ^d`;
- `D_k = N_{k+1} \ N_k` is a union of `r`-cells, at most `2^d(2C₀+1)^d|Z|` of them
  (`4(2C₀+1)²|Z|` at `d = 2`, `layerCount_two`);
- `C₀r ≤ dist_∞(x,Z) ≤ 2(C₀+1)r` for `x ∈ closure D_k`. -/
theorem step_11_6 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (hZ : Z.Nonempty) (C₀ : ℕ)
    (hC₀ : 2 ≤ C₀) :
    (∀ k, N o Z C₀ k ⊆ N o Z C₀ (k + 1)) ∧ (⋃ k, N o Z C₀ k) = univ ∧
      (∀ k, D o Z C₀ k = ⋃ z ∈ DIndex o Z C₀ k, cell o k z ∧
        (DIndex o Z C₀ k).card ≤ layerCount d C₀ * Z.card) ∧
      ∀ k, ∀ x ∈ closure (D o Z C₀ k),
        C₀ * 2 ^ k ≤ infDist x Z ∧ infDist x Z ≤ 2 * (C₀ + 1) * 2 ^ k := by
  refine ⟨fun k x hx ↦ ?_, eq_univ_of_forall fun x ↦ mem_iUnion.2 (step_11_6_2 o Z hZ C₀ hC₀ x),
    fun k ↦ ⟨D_eq_iUnion o Z C₀ k, step_11_6_3 o Z C₀ k⟩, fun k x hx ↦ ?_⟩
  · -- D11.6.1: parents of indices within `C₀` of an occupied index are within `C₀` of its parent
    obtain ⟨w, hw, h⟩ := mem_NIndex_iff.1 (mem_N_iff.1 hx)
    refine mem_N_iff.2 (mem_NIndex_iff.2 ⟨w, hw, fun i ↦ ?_⟩)
    have := abs_le.1 (h i)
    simp only [cellIndex_succ, abs_le]; omega
  · obtain ⟨w, hw, hxw⟩ := step_11_6_5 hx
    exact ⟨(le_infDist ⟨w, hw⟩).2 fun y hy ↦ step_11_6_4 hx hy, -- D11.6.4
      (infDist_le_dist_of_mem hw).trans hxw⟩ -- D11.6.5

/-! ## D11.7 Non-adjacent layers -/

/-- D11.7 (geometry:nonadjacent). For `h ≥ k+2`:
`dist_∞(closure D_k, closure D_h) ≥ C₀2^h − 2(C₀+1)2^k ≥ (C₀−1)/2·2^h`. -/
theorem step_11_7 {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k h : ℕ} (hkh : k + 2 ≤ h)
    {x y : Fin d → ℝ} (hx : x ∈ closure (D o Z C₀ k)) (hy : y ∈ closure (D o Z C₀ h)) :
    C₀ * 2 ^ h - 2 * (C₀ + 1) * 2 ^ k ≤ dist x y ∧
      ((C₀ : ℝ) - 1) / 2 * 2 ^ h ≤ C₀ * 2 ^ h - 2 * (C₀ + 1) * 2 ^ k := by
  obtain ⟨w, hw, hxw⟩ := step_11_6_5 hx
  -- D11.7.1: `x ↦ dist_∞(x, Z)` is 1-Lipschitz
  have h₁ : infDist y Z ≤ infDist x Z + dist y x := infDist_le_infDist_add_dist
  have h₂ : C₀ * 2 ^ h ≤ infDist y Z := (le_infDist ⟨w, hw⟩).2 fun z hz ↦ step_11_6_4 hy hz
  have h₃ : infDist x Z ≤ 2 * (C₀ + 1) * 2 ^ k := (infDist_le_dist_of_mem hw).trans hxw
  -- D11.7.2: `2^k ≤ 2^(h-2)`
  have h₄ : 4 * (2 : ℝ) ^ k ≤ 2 ^ h := by
    calc 4 * (2 : ℝ) ^ k = 2 ^ (k + 2) := by ring
      _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hkh
  exact ⟨by rw [dist_comm] at h₁; linarith,
    by nlinarith [mul_le_mul_of_nonneg_left h₄ (by positivity : (0 : ℝ) ≤ C₀ + 1)]⟩

/-! ## D11.16 Edges avoid lattice sites -/

/-- D11.16. Every supporting line of every edge has equation `x_i = o_i + m`,
`x_i + x_j = o_i + o_j + m` or `x_i − x_j = o_i − o_j + m`, `m ∈ ℤ`. None contains a point of
`ℤ^d`. (Hypothesis: `o_i`, `o_i ± o_j` irrational for `i ≠ j`; `o₂_irrational` at `d = 2`.) -/
theorem step_11_16 {o : Fin d → ℝ} (ho : ∀ i, Irrational (o i))
    (ho' : ∀ i j, i ≠ j → Irrational (o i + o j) ∧ Irrational (o i - o j))
    (z : Fin d → ℤ) (m : ℤ) (i : Fin d) :
    (z i : ℝ) ≠ o i + m ∧ ∀ j, i ≠ j →
      (z i : ℝ) + z j ≠ o i + o j + m ∧ (z i : ℝ) - z j ≠ o i - o j + m := by
  -- D11.16.3: irrationality of `o_i`, `o_i ± o_j` excludes lattice points
  refine ⟨fun h ↦ (ho i).ne_int (z i - m) (by push_cast; linarith), fun j hij ↦
    ⟨fun h ↦ (ho' i j hij).1.ne_int (z i + z j - m) (by push_cast; linarith),
      fun h ↦ (ho' i j hij).2.ne_int (z i - z j - m) (by push_cast; linarith)⟩⟩

/-- D11.5. `o₂ = (√2, √3)` has `o_1, o_2, o_1 + o_2, o_1 − o_2` irrational. -/
theorem o₂_irrational :
    (∀ i, Irrational (o₂ i)) ∧
      ∀ i j, i ≠ j → Irrational (o₂ i + o₂ j) ∧ Irrational (o₂ i - o₂ j) := by
  have h₂ : Irrational √2 := by simpa using Nat.prime_two.irrational_sqrt
  have h₃ : Irrational √3 := by simpa using Nat.prime_three.irrational_sqrt
  have h₆ : Irrational √6 := irrational_sqrt_natCast_iff.2 (by
    rintro ⟨r, hr⟩
    have : r ≤ 3 := by nlinarith
    interval_cases r <;> norm_num at hr)
  have hsq : √2 * √3 = √6 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hp : Irrational (√2 + √3) := by
    refine Irrational.of_pow 2 ?_
    have : (√2 + √3) ^ 2 = 5 + 2 * √6 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [this]; exact_mod_cast (h₆.natCast_mul two_ne_zero).natCast_add 5
  have hm : Irrational (√2 - √3) := by
    refine Irrational.of_pow 2 ?_
    have : (√2 - √3) ^ 2 = 5 - 2 * √6 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [this]; exact_mod_cast (h₆.natCast_mul two_ne_zero).natCast_sub 5
  refine ⟨fun i ↦ by fin_cases i <;> simpa [o₂], fun i j hij ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all [o₂, add_comm]
  · simpa [neg_sub] using hm.neg

end Geometry

end AreaLaw
