import AreaLawRefactored.S11_Geometry.Templates

/-! # §11.4 Filling the belts

The initial configuration of tiles in the plane `ℝ × ℝ`: the dummy tile `N_{k₀}`, the primary
tiles and the belt fans of the layers `k₀ ≤ k < K`, and an exterior tile outside `N_K`. Every
point gets one raw piece (`piece`) and one tile identifier (`tile`); birth regions are formed from
these in `InitialStars.lean`. The fan of a belt cell is the all-midpoint fan: its eight triangles
are the octant triangles about the cell centre (D11.11.2).

Digest `digest/11-geometry.md` D11.11, D11.12 -/

open Set Metric

namespace AreaLaw.Geometry

noncomputable section

/-- D11.13. The star constant `a₀ = 1/64` of the initial stars. -/
noncomputable def starA₀ : ℝ := 1 / 64

/-- D11.14. The stopping scale `S_*` for `a₀ = 1/64`: both trim margins hold above it. -/
noncomputable def Sstar : ℝ := max 4 ((1000 / starA₀) ^ (1 - ρ₀)⁻¹)

/-- The parity `k mod 2` as a label. -/
def par (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt _ two_pos⟩

lemma par_succ (k : ℕ) : par (k + 1) = par k + 1 := by
  apply Fin.ext; simp only [par, Fin.val_add]; omega

lemma ne_add_one (c : Fin 2) : c ≠ c + 1 := by fin_cases c <;> decide

/-- The point `x ∈ ℝ × ℝ` in `Fin 2 → ℝ`, where layers and cells live. -/
def pt (x : ℝ × ℝ) : Fin 2 → ℝ := plane.symm x

/-- The four forms `x₁ - o₁`, `x₂ - o₂`, their sum and difference, `o = (√2, √3)`. -/
def f₀ (x : ℝ × ℝ) : ℝ := x.1 - o₂ 0
/-- The second coordinate form. -/
def f₁ (x : ℝ × ℝ) : ℝ := x.2 - o₂ 1
/-- The diagonal form `x₁ + x₂ - o₁ - o₂`. -/
def fp (x : ℝ × ℝ) : ℝ := f₀ x + f₁ x
/-- The diagonal form `x₁ - x₂ - o₁ + o₂`. -/
def fm (x : ℝ × ℝ) : ℝ := f₀ x - f₁ x

/-! ## Same side of every grid line of mesh `u` -/

/-- `F` and `F'` lie on the same side of every point of the grid `uℤ`. -/
def SB (u F F' : ℝ) : Prop := ∀ n : ℤ, (n * u ≤ F ↔ n * u ≤ F')

lemma le_iff_le_floor {u F : ℝ} (hu : 0 < u) (n : ℤ) : n * u ≤ F ↔ n ≤ ⌊F / u⌋ := by
  rw [Int.le_floor, le_div_iff₀ hu]

lemma sb_iff {u F F' : ℝ} (hu : 0 < u) : SB u F F' ↔ ⌊F / u⌋ = ⌊F' / u⌋ := by
  simp only [SB, le_iff_le_floor hu]
  exact ⟨fun h ↦ le_antisymm ((h _).1 le_rfl) ((h _).2 le_rfl), fun h n ↦ by rw [h]⟩

lemma sb_symm {u F F' : ℝ} (h : SB u F F') : SB u F' F := fun n ↦ (h n).symm

lemma sb_pow {p r : ℕ} {F F' : ℝ} (h : SB (2 ^ p) F F') (hpr : p ≤ r) : SB (2 ^ r) F F' := by
  intro n
  have : (n : ℝ) * 2 ^ r = ((n * 2 ^ (r - p) : ℤ) : ℝ) * 2 ^ p := by
    push_cast; rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hpr]
  rw [this]; exact h _

/-- Two reals in one interval `[mu, (m+1)u)` are on the same side of every grid point. -/
lemma sb_of_mem {u F F' : ℝ} (hu : 0 < u) (m : ℤ) (h₁ : m * u ≤ F) (h₂ : F < (m + 1) * u)
    (h₁' : m * u ≤ F') (h₂' : F' < (m + 1) * u) : SB u F F' := by
  intro n
  rcases le_or_gt n m with h | h
  · have : (n : ℝ) * u ≤ m * u := by gcongr
    exact ⟨fun _ ↦ this.trans h₁', fun _ ↦ this.trans h₁⟩
  · have : ((m : ℝ) + 1) * u ≤ n * u := by gcongr; exact_mod_cast h
    exact ⟨fun h' ↦ absurd (h'.trans_lt h₂) this.not_gt,
      fun h' ↦ absurd (h'.trans_lt h₂') this.not_gt⟩

/-- Near a grid point `nu`, the side of every grid point is the sign of the offset. -/
lemma sb_of_near {u e e' : ℝ} (n : ℤ) (he : |e| < u) (he' : |e'| < u) (hs : 0 ≤ e ↔ 0 ≤ e') :
    SB u (n * u + e) (n * u + e') := by
  have hu : 0 < u := (abs_nonneg e).trans_lt he
  rw [abs_lt] at he he'
  by_cases h : 0 ≤ e
  · exact sb_of_mem hu n (by linarith) (by linarith) (by linarith [hs.1 h]) (by linarith)
  · exact sb_of_mem hu (n - 1) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith [not_le.1 (mt hs.2 h)])

lemma abs_sub_lt_of_sb {u F F' : ℝ} (hu : 0 < u) (h : SB u F F') : |F - F'| < u := by
  have h₁ := (le_iff_le_floor hu ⌊F / u⌋).2 le_rfl
  have h₂ := (h ⌊F / u⌋).1 h₁
  have h₃ : F < (⌊F / u⌋ + 1) * u := by
    rw [← div_lt_iff₀ hu]; exact Int.lt_floor_add_one _
  have h₄ : F' < (⌊F / u⌋ + 1) * u := by
    by_contra h'; push Not at h'
    have := (h (⌊F / u⌋ + 1)).2 (by push_cast; exact h')
    push_cast at this; linarith
  rw [abs_lt]; constructor <;> nlinarith

/-- `F` lies in the grid cell just above the grid point `Xu`, `F'` in the one just below. -/
def Adj (u F F' : ℝ) : Prop :=
  ∃ X : ℤ, X * u ≤ F ∧ F < (X + 1) * u ∧ (X - 1) * u ≤ F' ∧ F' < X * u

lemma adj_of_near {u e e' : ℝ} (n : ℤ) (he : 0 ≤ e) (he₁ : e < u) (he' : e' < 0)
    (he'₁ : -u ≤ e') : Adj u (n * u + e) (n * u + e') :=
  ⟨n, by linarith, by linarith, by linarith, by linarith⟩

lemma abs_sub_lt_of_adj {u F F' : ℝ} (h : Adj u F F') : |F - F'| < 2 * u := by
  obtain ⟨X, h₁, h₂, h₃, h₄⟩ := h
  rw [abs_lt]; constructor <;> nlinarith

/-- The two points agree on the axis grid lines of mesh `2^p`. -/
def AxSim (p : ℕ) (x x' : ℝ × ℝ) : Prop := SB (2 ^ p) (f₀ x) (f₀ x') ∧ SB (2 ^ p) (f₁ x) (f₁ x')

/-- The two points agree on all grid lines of mesh `2^p` of the four slopes. -/
def Sim (p : ℕ) (x x' : ℝ × ℝ) : Prop :=
  AxSim p x x' ∧ SB (2 ^ p) (fp x) (fp x') ∧ SB (2 ^ p) (fm x) (fm x')

/-- Crossing a vertical grid line of mesh `2^p`: `x` just right of it, `x'` just left. -/
def CrossX (p : ℕ) (x x' : ℝ × ℝ) : Prop :=
  Adj (2 ^ p) (f₀ x) (f₀ x') ∧ SB (2 ^ p) (f₁ x) (f₁ x') ∧ SB (2 ^ p) (fp x) (fp x') ∧
    SB (2 ^ p) (fm x) (fm x')

/-- Crossing a horizontal grid line of mesh `2^p`: `x` just above it, `x'` just below. -/
def CrossY (p : ℕ) (x x' : ℝ × ℝ) : Prop :=
  SB (2 ^ p) (f₀ x) (f₀ x') ∧ Adj (2 ^ p) (f₁ x) (f₁ x') ∧ SB (2 ^ p) (fp x) (fp x') ∧
    SB (2 ^ p) (fm x) (fm x')

lemma cellIndex_pt (k : ℕ) (x : ℝ × ℝ) :
    cellIndex o₂ k (pt x) = ![⌊f₀ x / 2 ^ k⌋, ⌊f₁ x / 2 ^ k⌋] := by
  funext i; fin_cases i <;> rfl

lemma cellIndex_eq_of_axSim {p r : ℕ} {x x' : ℝ × ℝ} (h : AxSim p x x') (hpr : p ≤ r) :
    cellIndex o₂ r (pt x) = cellIndex o₂ r (pt x') := by
  rw [cellIndex_pt, cellIndex_pt, (sb_iff (by positivity)).1 (sb_pow h.1 hpr),
    (sb_iff (by positivity)).1 (sb_pow h.2 hpr)]

lemma dist_lt_of_abs {x x' : ℝ × ℝ} {r : ℝ} (h₀ : |f₀ x - f₀ x'| < r)
    (h₁ : |f₁ x - f₁ x'| < r) : dist x x' < r := by
  simp only [f₀, f₁, sub_sub_sub_cancel_right] at h₀ h₁
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_lt h₀ h₁

lemma dist_pt (x x' : ℝ × ℝ) : dist (pt x) (pt x') = dist x x' := plane.symm.dist_eq x x'

/-! ## Scale facts -/

lemma floor_zeta_mono {k k' : ℕ} (h : k ≤ k') : ⌊ζ * k⌋₊ ≤ ⌊ζ * k'⌋₊ := by
  have : 0 ≤ ζ := by simp only [ζ, δ₀]; norm_num
  exact Nat.floor_le_floor (by gcongr)

lemma floor_zeta_le (k : ℕ) : ⌊ζ * k⌋₊ ≤ k := by
  have : ζ < 1 := eq_exponent_gaps.2.1
  exact Nat.floor_le_of_le (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

lemma floor_zeta_lt {k : ℕ} (hk : 1 ≤ k) : ⌊ζ * k⌋₊ < k := by
  have : ζ < 1 := eq_exponent_gaps.2.1
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact (Nat.floor_lt (by simp only [ζ, δ₀]; positivity)).2 (by nlinarith)

lemma floor_zeta_succ (k : ℕ) : ⌊ζ * (k + 1 : ℕ)⌋₊ ≤ ⌊ζ * k⌋₊ + 1 := by
  rcases (step_11_8.1 k).2.2 with h | h <;> unfold t at h
  · rw [Nat.pow_right_injective le_rfl h]; omega
  · rw [← pow_succ'] at h; rw [Nat.pow_right_injective le_rfl h]

lemma t_eq (k : ℕ) : (t k : ℝ) = 2 ^ ⌊ζ * k⌋₊ := by simp [t]

/-! ## D11.11 The configuration -/

/-- D11.8, D11.11. The data of the initial configuration: the endpoint set `Z`, the integer `C₀`,
the dummy layer `k₀` and the last layer `K > k₀`, and the residue classes `a k` (one per
coordinate) of the belt cells of layer `k`. `k₀` is large: `S_* ≤ t_{k₀}`. -/
structure Layout where
  /-- The endpoints of the cut edges. -/
  Z : Finset (Fin 2 → ℝ)
  /-- The neighbourhood constant. -/
  C₀ : ℕ
  /-- The dummy layer. -/
  k₀ : ℕ
  /-- Outside `N_K` lies one exterior tile. -/
  K : ℕ
  /-- The residue classes of the belt cells. -/
  a : ℕ → Fin 2 → ℤ
  Z_nonempty : Z.Nonempty
  two_le_C₀ : 2 ≤ C₀
  lt_K : k₀ < K
  Sstar_le : Sstar ≤ t k₀

/-- D11.11. The raw pieces of the plane: the dummy tile `N_{k₀}`, the exterior tile outside
`N_K`, the primary `j` of layer `k`, and the belt cell `w` of layer `k`. -/
inductive Piece
  | dummy
  | exterior
  | primary (k : ℕ) (j : Fin 2 → ℤ)
  | belt (k : ℕ) (w : Fin 2 → ℤ)

/-- D11.11.4. The initial tile identifiers: dummy, exterior, primaries, and `belt k w c`, the
union of the triangles of the fan of the belt cell `w` with label `c`. -/
inductive InitId
  | dummy
  | exterior
  | primary (k : ℕ) (j : Fin 2 → ℤ)
  | belt (k : ℕ) (w : Fin 2 → ℤ) (c : Fin 2)

/-- The index of the fine cell of layer `k` containing `x`. -/
def fineIdx (k : ℕ) (x : ℝ × ℝ) : Fin 2 → ℤ := cellIndex o₂ ⌊ζ * k⌋₊ (pt x)

/-- Half the fine side of layer `k`, `t_k / 2`. -/
def hs (k : ℕ) : ℝ := 2 ^ (⌊ζ * k⌋₊ - 1)

lemma hs_pos (k : ℕ) : 0 < hs k := by unfold hs; positivity

lemma two_pow_eq {k : ℕ} (hq : 1 ≤ ⌊ζ * k⌋₊) : (2 : ℝ) ^ ⌊ζ * k⌋₊ = 2 * hs k := by
  unfold hs; rw [← pow_succ']; congr 1; omega

/-! The fan of the fine cell `w` of layer `k`, centre `c = o + (t_k/2)(2w+1)`: the side tests
`x_1 + x_2 ≥ c_1 + c_2`, `x_1 - x_2 ≥ c_1 - c_2`, `x_1 ≥ c_1`, `x_2 ≥ c_2`. -/

/-- `x₁ + x₂ ≥ c₁ + c₂`. -/
def Ap (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Prop := ((2 * (w 0 + w 1 + 1) : ℤ) : ℝ) * hs k ≤ fp x
/-- `x₁ - x₂ ≥ c₁ - c₂`. -/
def Am (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Prop := ((2 * (w 0 - w 1) : ℤ) : ℝ) * hs k ≤ fm x
/-- `x₁ ≥ c₁`. -/
def A0 (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Prop := ((2 * w 0 + 1 : ℤ) : ℝ) * hs k ≤ f₀ x
/-- `x₂ ≥ c₂`. -/
def A1 (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Prop := ((2 * w 1 + 1 : ℤ) : ℝ) * hs k ≤ f₁ x

noncomputable instance (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Decidable (Ap k w x) := by
  unfold Ap; infer_instance
noncomputable instance (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Decidable (Am k w x) := by
  unfold Am; infer_instance
noncomputable instance (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Decidable (A0 k w x) := by
  unfold A0; infer_instance
noncomputable instance (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Decidable (A1 k w x) := by
  unfold A1; infer_instance

/-- D11.11.2. The triangle of the fan of `w` containing `x`: `(i, s, h)` is the triangle whose
outer half-side lies on the side `x_i = c_i ± t/2` (sign `s`), in the half `h` of that side. The
eight triangles are the octant triangles about the centre. -/
def tri (k : ℕ) (w : Fin 2 → ℤ) (x : ℝ × ℝ) : Bool × Bool × Bool :=
  (decide ¬(Ap k w x ↔ Am k w x), decide (Ap k w x),
    if (Ap k w x ↔ Am k w x) then decide (A1 k w x) else decide (A0 k w x))

/-- D11.11.1. The test point facing the outer half-side of the triangle `b` of the fan of `w`:
at distance `t/8` beyond the half-side, at its midpoint. -/
def testPt (k : ℕ) (w : Fin 2 → ℤ) (b : Bool × Bool × Bool) : ℝ × ℝ :=
  if b.1 then
    (o₂ 0 + hs k * (2 * w 0 + 1 + (if b.2.2 then 1 else -1) / 2),
      o₂ 1 + hs k * (2 * w 1 + 1 + (if b.2.1 then 1 else -1) * 5 / 4))
  else
    (o₂ 0 + hs k * (2 * w 0 + 1 + (if b.2.1 then 1 else -1) * 5 / 4),
      o₂ 1 + hs k * (2 * w 1 + 1 + (if b.2.2 then 1 else -1) / 2))

lemma fine_bounds {k : ℕ} {x : ℝ × ℝ} {w : Fin 2 → ℤ} (hw : fineIdx k x = w)
    (hq : 1 ≤ ⌊ζ * k⌋₊) :
    2 * w 0 * hs k ≤ f₀ x ∧ f₀ x < (2 * w 0 + 2) * hs k ∧ 2 * w 1 * hs k ≤ f₁ x ∧
      f₁ x < (2 * w 1 + 2) * hs k := by
  subst hw
  have h2 := two_pow_eq hq
  have hpos : (0 : ℝ) < 2 ^ ⌊ζ * k⌋₊ := by positivity
  simp only [fineIdx, cellIndex_pt, Matrix.cons_val_zero, Matrix.cons_val_one]
  have a0 := Int.floor_le (f₀ x / 2 ^ ⌊ζ * k⌋₊)
  have b0 := Int.lt_floor_add_one (f₀ x / 2 ^ ⌊ζ * k⌋₊)
  have a1 := Int.floor_le (f₁ x / 2 ^ ⌊ζ * k⌋₊)
  have b1 := Int.lt_floor_add_one (f₁ x / 2 ^ ⌊ζ * k⌋₊)
  rw [le_div_iff₀ hpos] at a0 a1; rw [div_lt_iff₀ hpos] at b0 b1
  generalize ⌊f₀ x / 2 ^ ⌊ζ * k⌋₊⌋ = n₀ at *
  generalize ⌊f₁ x / 2 ^ ⌊ζ * k⌋₊⌋ = n₁ at *
  rw [h2] at a0 a1 b0 b1
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma fineIdx_eq_of_bounds {k : ℕ} {x : ℝ × ℝ} {w : Fin 2 → ℤ} (hq : 1 ≤ ⌊ζ * k⌋₊)
    (h₀ : 2 * w 0 * hs k ≤ f₀ x) (h₀' : f₀ x < (2 * w 0 + 2) * hs k)
    (h₁ : 2 * w 1 * hs k ≤ f₁ x) (h₁' : f₁ x < (2 * w 1 + 2) * hs k) : fineIdx k x = w := by
  have h2 := two_pow_eq hq
  have hpos : (0 : ℝ) < 2 ^ ⌊ζ * k⌋₊ := by positivity
  funext i; fin_cases i <;>
    simp only [fineIdx, cellIndex_pt, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one] <;>
    rw [Int.floor_eq_iff, le_div_iff₀ hpos, div_lt_iff₀ hpos, h2] <;>
    constructor <;> linarith

lemma axSim_of_cellIndex {r : ℕ} {x x' : ℝ × ℝ}
    (h : cellIndex o₂ r (pt x) = cellIndex o₂ r (pt x')) : AxSim r x x' := by
  rw [cellIndex_pt, cellIndex_pt] at h
  have h0 := congrFun h 0; have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact ⟨(sb_iff (by positivity)).2 h0, (sb_iff (by positivity)).2 h1⟩

lemma ediv_sub_one {n m : ℤ} (hm : 0 < m) (h : ¬ m ∣ n) : (n - 1) / m = n / m := by
  have h1 : n = n % m + n / m * m := by rw [Int.emod_def]; ring
  have h2 := Int.emod_nonneg n hm.ne'
  have h3 := Int.emod_lt_of_pos n hm
  have h4 : n % m ≠ 0 := fun h' ↦ h (Int.dvd_of_emod_eq_zero h')
  conv_lhs => rw [h1, show n % m + n / m * m - 1 = (n % m - 1) + n / m * m by ring]
  rw [Int.add_mul_ediv_right _ _ hm.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]

namespace Layout

variable (L : Layout)

lemma N_mono {k k' : ℕ} (h : k ≤ k') : N o₂ L.Z L.C₀ k ⊆ N o₂ L.Z L.C₀ k' :=
  monotone_nat_of_le_succ (step_11_6 o₂ L.Z L.Z_nonempty L.C₀ L.two_le_C₀).1 h

lemma exists_mem_N (x : ℝ × ℝ) : ∃ k, pt x ∈ N o₂ L.Z L.C₀ k :=
  step_11_6_2 o₂ L.Z L.Z_nonempty L.C₀ L.two_le_C₀ _

open Classical in
/-- The least `k` with `x ∈ N_k`; `x ∈ D_{lev x - 1}`. -/
def lev (x : ℝ × ℝ) : ℕ := Nat.find (L.exists_mem_N x)

variable {L}

lemma mem_N_iff_lev {x : ℝ × ℝ} {k : ℕ} : pt x ∈ N o₂ L.Z L.C₀ k ↔ L.lev x ≤ k := by
  classical
  exact ⟨fun h ↦ Nat.find_min' _ h, fun h ↦ L.N_mono h (Nat.find_spec (L.exists_mem_N x))⟩

lemma mem_D_lev {x : ℝ × ℝ} {k : ℕ} (h : L.lev x = k + 1) : pt x ∈ D o₂ L.Z L.C₀ k :=
  ⟨mem_N_iff_lev.2 h.le, fun h' ↦ by have := mem_N_iff_lev.1 h'; omega⟩

lemma two_le_floor {k : ℕ} (hk : L.k₀ ≤ k) : 2 ≤ ⌊ζ * k⌋₊ := by
  have h4 : (4 : ℝ) ≤ 2 ^ ⌊ζ * L.k₀⌋₊ :=
    (le_max_left _ _).trans (L.Sstar_le.trans (t_eq _).le)
  by_contra h; push Not at h
  have : ⌊ζ * L.k₀⌋₊ ≤ 1 := by have := floor_zeta_mono hk; omega
  have : (2 : ℝ) ^ ⌊ζ * L.k₀⌋₊ ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) this
  linarith

/-- A point of `N_k` is within `(C₀+1)2^k` of some endpoint. -/
lemma N_dist {k : ℕ} {y : Fin 2 → ℝ} (hy : y ∈ N o₂ L.Z L.C₀ k) :
    ∃ z ∈ L.Z, dist y z ≤ (L.C₀ + 1) * 2 ^ k := by
  obtain ⟨z, hz, h⟩ := mem_NIndex_iff.1 (mem_N_iff.1 hy)
  have hy' : y ∈ closure (cell o₂ k (cellIndex o₂ k y)) := subset_closure (mem_cell_iff.2 rfl)
  have hz' : z ∈ closure (cell o₂ k (cellIndex o₂ k z)) := subset_closure (mem_cell_iff.2 rfl)
  rw [closure_cell, mem_univ_pi] at hy' hz'
  refine ⟨z, hz, (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_⟩
  have := (abs_sub_bounds (by positivity) (hy' i) (hz' i)).1
  have h' : |(cellIndex o₂ k y i : ℝ) - cellIndex o₂ k z i| ≤ L.C₀ := by exact_mod_cast h i
  rw [Real.dist_eq]
  calc |y i - z i| ≤ (|(cellIndex o₂ k y i : ℝ) - cellIndex o₂ k z i| + 1) * 2 ^ k := this
    _ ≤ (L.C₀ + 1) * 2 ^ k := by gcongr

/-- D11.7. A point of `N_m` and a point of `closure D_h`, `h > m`, are `2^m` apart. -/
lemma two_pow_le_dist {x x' : ℝ × ℝ} {m h : ℕ} (hx : pt x ∈ N o₂ L.Z L.C₀ m)
    (hx' : pt x' ∈ closure (D o₂ L.Z L.C₀ h)) (hmh : m + 1 ≤ h) : (2 : ℝ) ^ m ≤ dist x x' := by
  obtain ⟨z, hz, hxz⟩ := L.N_dist hx
  have h₁ := step_11_6_4 hx' hz
  have h₂ : (2 : ℝ) * 2 ^ m ≤ 2 ^ h := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hmh
  have h₃ := dist_triangle (pt x') (pt x) z
  rw [dist_pt, dist_comm x' x] at h₃
  have hC : (2 : ℝ) ≤ L.C₀ := by exact_mod_cast L.two_le_C₀
  have := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg L.C₀ : (0 : ℝ) ≤ L.C₀)
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]

lemma far {x x' : ℝ × ℝ} {m h p : ℕ} (hx : pt x ∈ N o₂ L.Z L.C₀ m)
    (hx' : pt x' ∈ closure (D o₂ L.Z L.C₀ h)) (hmh : m + 1 ≤ h) (hpm : p + 1 ≤ m)
    (hd : dist x x' < 2 ^ (p + 1)) : False := by
  have := L.two_pow_le_dist hx hx' hmh
  have : (2 : ℝ) ^ (p + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hpm
  linarith

lemma lev_ge {x x' : ℝ × ℝ} {k : ℕ} (hx : pt x ∈ closure (D o₂ L.Z L.C₀ k)) (hk : 1 ≤ k)
    (hd : dist x x' < 2 ^ (k - 1)) : k ≤ L.lev x' := by
  by_contra h; push Not at h
  have := L.two_pow_le_dist (mem_N_iff_lev.2 (by omega : L.lev x' ≤ k - 1)) hx (by omega)
  rw [dist_comm] at this; linarith

variable (L)

/-- The layer index governing the local mesh at `x`: `k₀` on the dummy tile, `K` outside `N_K`,
`k` on `D_k`. -/
def lay (x : ℝ × ℝ) : ℕ :=
  if L.lev x ≤ L.k₀ then L.k₀ else if L.K < L.lev x then L.K else L.lev x - 1

/-- The pitch index of the fine cell `w` of layer `k`. -/
def pitchIdx (k : ℕ) (w : Fin 2 → ℤ) : Fin 2 → ℤ := fun i ↦ (w i - L.a k i) / (s k / t k : ℕ)

open Classical in
/-- D11.11. The raw piece containing `x`. -/
def piece (x : ℝ × ℝ) : Piece :=
  if L.lev x ≤ L.k₀ then .dummy else if L.K < L.lev x then .exterior else
    if IsBeltCell (L.lev x - 1) (L.a (L.lev x - 1)) (fineIdx (L.lev x - 1) x) then
      .belt (L.lev x - 1) (fineIdx (L.lev x - 1) x)
    else .primary (L.lev x - 1) (L.pitchIdx (L.lev x - 1) (fineIdx (L.lev x - 1) x))

/-- D11.11.3. The label of a non-belt piece: `(k₀ - 1) mod 2`, `K mod 2`, `k mod 2`. -/
def plabel : Piece → Fin 2
  | .dummy => par (L.k₀ + 1)
  | .exterior => par L.K
  | .primary k _ => par k
  | .belt _ _ => 0

/-- D11.11.3. The label of a triangle facing the piece `P` across its outer half-side, on the side
`x_i = c_i + t/2` (`s`) or `x_i = c_i - t/2` (`¬s`): opposite to a dummy, exterior or primary
tile; facing a belt cell, `0` on the left/bottom and `1` on the right/top. -/
def gLab (s : Bool) : Piece → Fin 2
  | .belt _ _ => if s then 0 else 1
  | P => L.plabel P + 1

/-- D11.11.3. The label of the triangle `b` of the fan of `w`. -/
def lab (k : ℕ) (w : Fin 2 → ℤ) (b : Bool × Bool × Bool) : Fin 2 :=
  L.gLab b.2.1 (L.piece (testPt k w b))

/-- D11.11.4. The tile identifier of `x`. -/
def tile (x : ℝ × ℝ) : InitId :=
  match L.piece x with
  | .dummy => .dummy
  | .exterior => .exterior
  | .primary k j => .primary k j
  | .belt k w => .belt k w (L.lab k w (tri k w x))

/-- D11.11.3. The labels of the identifiers. -/
def label : InitId → Fin 2
  | .dummy => par (L.k₀ + 1)
  | .exterior => par L.K
  | .primary k _ => par k
  | .belt _ _ c => c

variable {L}

lemma piece_belt {x : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} (h : L.piece x = .belt k w) :
    L.lev x = k + 1 ∧ L.k₀ ≤ k ∧ k < L.K ∧ fineIdx k x = w ∧ IsBeltCell k (L.a k) w := by
  unfold piece at h
  split_ifs at h with h1 h2 h3
  cases h
  exact ⟨by omega, by omega, by omega, rfl, h3⟩

lemma piece_primary {x : ℝ × ℝ} {k : ℕ} {j : Fin 2 → ℤ} (h : L.piece x = .primary k j) :
    L.lev x = k + 1 ∧ L.k₀ ≤ k ∧ k < L.K ∧ ¬ IsBeltCell k (L.a k) (fineIdx k x) ∧
      j = L.pitchIdx k (fineIdx k x) := by
  unfold piece at h
  split_ifs at h with h1 h2 h3
  cases h
  exact ⟨by omega, by omega, by omega, h3, rfl⟩

lemma piece_dummy {x : ℝ × ℝ} (h : L.piece x = .dummy) : L.lev x ≤ L.k₀ := by
  unfold piece at h
  split_ifs at h with h1
  exact h1

lemma piece_exterior {x : ℝ × ℝ} (h : L.piece x = .exterior) : L.K < L.lev x := by
  unfold piece at h
  split_ifs at h with h1 h2
  exact h2

lemma lay_eq {x : ℝ × ℝ} {k : ℕ} (h : L.lev x = k + 1) (hk : L.k₀ ≤ k) (hK : k < L.K) :
    L.lay x = k := by
  unfold lay; split_ifs <;> omega

lemma lay_ge {x : ℝ × ℝ} {k : ℕ} (h : k ≤ L.lev x) (hk : k ≤ L.K + 1) : k - 1 ≤ L.lay x := by
  unfold lay; split_ifs <;> omega

lemma k₀_le_lay (x : ℝ × ℝ) : L.k₀ ≤ L.lay x := by
  have := L.lt_K; unfold lay; split_ifs <;> omega

/-! ## Constancy of pieces and identifiers between grid lines -/

lemma lev_le_iff {p k : ℕ} {x x' : ℝ × ℝ} (h : AxSim p x x') (hk : p ≤ k) :
    L.lev x ≤ k ↔ L.lev x' ≤ k := by
  rw [← mem_N_iff_lev, ← mem_N_iff_lev, mem_N_iff, mem_N_iff, cellIndex_eq_of_axSim h hk]

lemma lev_eq_of_axSim {p : ℕ} {x x' : ℝ × ℝ} (h : AxSim p x x') (hp : p + 1 ≤ L.lev x) :
    L.lev x' = L.lev x := by
  have h1 := (lev_le_iff (L := L) h (le_of_lt hp)).1 le_rfl
  have h2 := mt (lev_le_iff (L := L) h (show p ≤ L.lev x - 1 by omega)).2 (by omega)
  omega

/-- The piece of `x` is constant across grid cells of mesh `2^p` for `2^p ≤ t_{lay x}`. -/
lemma piece_eq_of_axSim {p : ℕ} {x x' : ℝ × ℝ} (h : AxSim p x x')
    (hp : p ≤ ⌊ζ * L.lay x⌋₊) : L.piece x = L.piece x' := by
  have hpl : p ≤ L.lay x := hp.trans (floor_zeta_le _)
  have hK := L.lt_K
  by_cases h1 : L.lev x ≤ L.k₀
  · have hl : L.lay x = L.k₀ := by simp [lay, h1]
    have h1' := (lev_le_iff (L := L) h (by omega)).1 h1
    simp [piece, h1, h1']
  by_cases h2 : L.K < L.lev x
  · have hl : L.lay x = L.K := by simp [lay, h1, h2]
    have h2' : L.K < L.lev x' := by
      have := mt (lev_le_iff (L := L) h (show p ≤ L.K by omega)).2 (by omega); omega
    have h1' : ¬ L.lev x' ≤ L.k₀ := by omega
    simp [piece, h1, h2, h1', h2']
  · have hl : L.lay x = L.lev x - 1 := by simp [lay, h1, h2]
    have he := lev_eq_of_axSim (L := L) h (by omega)
    have hf : fineIdx (L.lev x - 1) x = fineIdx (L.lev x - 1) x' :=
      cellIndex_eq_of_axSim h (by rw [hl] at hp; exact hp)
    simp only [piece, he, h1, h2, if_false, hf]

lemma tri_eq_of_sim {p k : ℕ} {w : Fin 2 → ℤ} {x x' : ℝ × ℝ} (h : Sim p x x')
    (hp : p + 1 ≤ ⌊ζ * k⌋₊) : tri k w x = tri k w x' := by
  have hp' : p ≤ ⌊ζ * k⌋₊ - 1 := by omega
  have hAp : Ap k w x ↔ Ap k w x' := sb_pow h.2.1 hp' _
  have hAm : Am k w x ↔ Am k w x' := sb_pow h.2.2 hp' _
  have hA0 : A0 k w x ↔ A0 k w x' := sb_pow h.1.1 hp' _
  have hA1 : A1 k w x ↔ A1 k w x' := sb_pow h.1.2 hp' _
  unfold tri
  by_cases a : Ap k w x <;> by_cases b : Am k w x <;> by_cases c : A0 k w x <;>
    by_cases e : A1 k w x <;>
    simp_all

/-- The identifier of `x` is constant across grid cells of mesh `2^p` for `2^p < t_{lay x}`. -/
lemma tile_eq_of_sim {p : ℕ} {x x' : ℝ × ℝ} (h : Sim p x x')
    (hp : p + 1 ≤ ⌊ζ * L.lay x⌋₊) : L.tile x = L.tile x' := by
  have hP := piece_eq_of_axSim (L := L) h.1 (by omega)
  unfold tile; rw [← hP]
  rcases hx : L.piece x with _ | _ | ⟨k, j⟩ | ⟨k, w⟩
  · rfl
  · rfl
  · rfl
  · obtain ⟨hl, hk, hK, -⟩ := piece_belt hx
    simp only [tri_eq_of_sim h (by rwa [lay_eq hl hk hK] at hp)]

end Layout

/-! ## D11.11.1 Facing regions -/

namespace Layout

variable {L : Layout}

lemma piece_of_fineIdx {x x' : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} (hx : L.piece x = .belt k w)
    (h : fineIdx k x' = w) : L.piece x' = .belt k w := by
  obtain ⟨hl, hk, hK, hw, hb⟩ := piece_belt hx
  have hc : cellIndex o₂ k (pt x) = cellIndex o₂ k (pt x') := by
    rw [cellIndex_eq_fine o₂ k (pt x), cellIndex_eq_fine o₂ k (pt x')]
    simp only [fineIdx] at h hw
    rw [h, hw]
  have he := lev_eq_of_axSim (L := L) (axSim_of_cellIndex hc) (by omega)
  simp only [piece, he, hl, show ¬ k + 1 ≤ L.k₀ by omega, show ¬ L.K < k + 1 by omega, if_false,
    Nat.add_sub_cancel, h, hb, if_true]

lemma dist_lt_of_crossX {p : ℕ} {x x' : ℝ × ℝ} (h : CrossX p x x') : dist x x' < 2 ^ (p + 1) := by
  have := abs_sub_lt_of_adj h.1
  have := abs_sub_lt_of_sb (by positivity) h.2.1
  refine dist_lt_of_abs ?_ ?_ <;> rw [pow_succ] <;> linarith [pow_pos (two_pos : (0 : ℝ) < 2) p]

lemma dist_lt_of_crossY {p : ℕ} {x x' : ℝ × ℝ} (h : CrossY p x x') : dist x x' < 2 ^ (p + 1) := by
  have := abs_sub_lt_of_sb (by positivity) h.1
  have := abs_sub_lt_of_adj h.2.1
  refine dist_lt_of_abs ?_ ?_ <;> rw [pow_succ] <;> linarith [pow_pos (two_pos : (0 : ℝ) < 2) p]

/-- The grid point of mesh `2^p` between two adjacent grid cells is the cell side `2 w hs`. -/
lemma grid_eq {p k : ℕ} {X n : ℤ} {F F' : ℝ} (hp : p + 1 ≤ ⌊ζ * k⌋₊) (_h₁ : X * 2 ^ p ≤ F)
    (h₂ : F < (X + 1) * 2 ^ p) (h₃ : (X - 1) * 2 ^ p ≤ F') (_h₄ : F' < X * 2 ^ p)
    (hlo : F' < n * hs k) (hhi : n * hs k ≤ F) : (X : ℝ) * 2 ^ p = n * hs k := by
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  have hu0 : (0 : ℝ) < 2 ^ p := by positivity
  have key : ((n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) : ℤ) : ℝ) * 2 ^ p = n * hs k := by
    push_cast; rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]; rfl
  have i₁ : X - 1 < n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) := by
    have : ((X : ℝ) - 1) * 2 ^ p < ((n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) : ℤ) : ℝ) * 2 ^ p := by
      rw [key]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hu0.le
  have i₂ : n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) < X + 1 := by
    have : ((n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) : ℤ) : ℝ) * 2 ^ p < ((X : ℝ) + 1) * 2 ^ p := by
      rw [key]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hu0.le
  have hXN : X = n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) := by
    generalize n * 2 ^ (⌊ζ * k⌋₊ - 1 - p) = N at i₁ i₂ ⊢; omega
  rw [hXN]; exact key

private lemma facing_left {p k : ℕ} {w : Fin 2 → ℤ} {x x' : ℝ × ℝ}
    (hx : L.piece x = .belt k w) (hx' : L.piece x' ≠ .belt k w) (hp : p + 1 ≤ ⌊ζ * k⌋₊)
    (hc : CrossX p x x') :
    tri k w x = (false, false, decide (A1 k w x)) ∧
      AxSim (⌊ζ * k⌋₊ - 1) x' (testPt k w (tri k w x)) := by
  obtain ⟨-, -, -, hw, -⟩ := piece_belt hx
  obtain ⟨⟨X, h₁, h₂, h₃, h₄⟩, c₁, cp, cm⟩ := hc
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  obtain ⟨b₀, b₀', b₁, b₁'⟩ := fine_bounds hw hq
  have hpH : p ≤ ⌊ζ * k⌋₊ - 1 := by omega
  have hu : (2 : ℝ) ^ p ≤ hs k := pow_le_pow_right₀ (by norm_num) hpH
  have hH0 := hs_pos k
  have r₁ : SB (hs k) (f₁ x) (f₁ x') := sb_pow c₁ hpH
  have e₁ : 2 * w 1 * hs k ≤ f₁ x' := by
    have := (r₁ (2 * w 1)).1 (by push_cast; linarith); push_cast at this; linarith
  have e₂ : f₁ x' < (2 * w 1 + 2) * hs k := by
    by_contra h; push Not at h
    have := (r₁ (2 * w 1 + 2)).2 (by push_cast; linarith); push_cast at this; linarith
  have hlt : f₀ x' < 2 * w 0 * hs k := by
    by_contra h; push Not at h
    exact hx' (piece_of_fineIdx hx (fineIdx_eq_of_bounds hq h (by linarith) e₁ e₂))
  have hX := grid_eq (n := 2 * w 0) hp h₁ h₂ h₃ h₄ (by push_cast; linarith) (by push_cast; linarith)
  push_cast at hX
  have hA : ¬ Ap k w x := by
    rw [show Ap k w x ↔ Ap k w x' from sb_pow cp hpH _]; unfold Ap fp; push_cast; intro h; linarith
  have hM : ¬ Am k w x := by
    rw [show Am k w x ↔ Am k w x' from sb_pow cm hpH _]; unfold Am fm; push_cast; intro h; linarith
  have htri : tri k w x = (false, false, decide (A1 k w x)) := by
    simp only [tri, hA, hM, iff_self, not_true_eq_false, decide_false, if_true]
  refine ⟨htri, ?_, ?_⟩ <;> rw [htri] <;> change SB (hs k) _ _
  · refine sb_of_mem hH0 (2 * w 0 - 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
      simp only [testPt, f₀, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left] <;> push_cast <;>
      linarith
  · have t1 : A1 k w x ↔ A1 k w x' := r₁ _
    by_cases hA1 : A1 k w x
    · have h' := t1.1 hA1; unfold A1 at h'; push_cast at h'
      refine sb_of_mem hH0 (2 * w 1 + 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₁, hA1, decide_true, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_left] <;> push_cast <;> linarith
    · have h' := mt t1.2 hA1; unfold A1 at h'; push_cast at h'; push Not at h'
      refine sb_of_mem hH0 (2 * w 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₁, hA1, decide_false, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_left] <;> push_cast <;> linarith

private lemma facing_right {p k : ℕ} {w : Fin 2 → ℤ} {x x' : ℝ × ℝ}
    (hx : L.piece x = .belt k w) (hx' : L.piece x' ≠ .belt k w) (hp : p + 1 ≤ ⌊ζ * k⌋₊)
    (hc : CrossX p x' x) :
    tri k w x = (false, true, decide (A1 k w x)) ∧
      AxSim (⌊ζ * k⌋₊ - 1) x' (testPt k w (tri k w x)) := by
  obtain ⟨-, -, -, hw, -⟩ := piece_belt hx
  obtain ⟨⟨X, h₁, h₂, h₃, h₄⟩, c₁, cp, cm⟩ := hc
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  obtain ⟨b₀, b₀', b₁, b₁'⟩ := fine_bounds hw hq
  have hpH : p ≤ ⌊ζ * k⌋₊ - 1 := by omega
  have hu : (2 : ℝ) ^ p ≤ hs k := pow_le_pow_right₀ (by norm_num) hpH
  have hH0 := hs_pos k
  have r₁ : SB (hs k) (f₁ x) (f₁ x') := sb_symm (sb_pow c₁ hpH)
  have e₁ : 2 * w 1 * hs k ≤ f₁ x' := by
    have := (r₁ (2 * w 1)).1 (by push_cast; linarith); push_cast at this; linarith
  have e₂ : f₁ x' < (2 * w 1 + 2) * hs k := by
    by_contra h; push Not at h
    have := (r₁ (2 * w 1 + 2)).2 (by push_cast; linarith); push_cast at this; linarith
  have hgt : (2 * w 0 + 2) * hs k ≤ f₀ x' := by
    by_contra h; push Not at h
    exact hx' (piece_of_fineIdx hx (fineIdx_eq_of_bounds hq (by linarith) h e₁ e₂))
  have hX := grid_eq (n := 2 * w 0 + 2) hp h₁ h₂ h₃ h₄ (by push_cast; linarith)
    (by push_cast; linarith)
  push_cast at hX
  have hA : Ap k w x := by
    rw [show Ap k w x ↔ Ap k w x' from sb_pow (sb_symm cp) hpH _]; unfold Ap fp; push_cast; linarith
  have hM : Am k w x := by
    rw [show Am k w x ↔ Am k w x' from sb_pow (sb_symm cm) hpH _]; unfold Am fm; push_cast; linarith
  have htri : tri k w x = (false, true, decide (A1 k w x)) := by
    simp only [tri, hA, hM, iff_self, not_true_eq_false, decide_false, decide_true, if_true]
  refine ⟨htri, ?_, ?_⟩ <;> rw [htri] <;> change SB (hs k) _ _
  · refine sb_of_mem hH0 (2 * w 0 + 2) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
      simp only [testPt, f₀, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left] <;>
      push_cast <;> linarith
  · have t1 : A1 k w x ↔ A1 k w x' := r₁ _
    by_cases hA1 : A1 k w x
    · have h' := t1.1 hA1; unfold A1 at h'; push_cast at h'
      refine sb_of_mem hH0 (2 * w 1 + 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₁, hA1, decide_true, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_left] <;> push_cast <;> linarith
    · have h' := mt t1.2 hA1; unfold A1 at h'; push_cast at h'; push Not at h'
      refine sb_of_mem hH0 (2 * w 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₁, hA1, decide_false, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_left] <;> push_cast <;> linarith

private lemma facing_down {p k : ℕ} {w : Fin 2 → ℤ} {x x' : ℝ × ℝ}
    (hx : L.piece x = .belt k w) (hx' : L.piece x' ≠ .belt k w) (hp : p + 1 ≤ ⌊ζ * k⌋₊)
    (hc : CrossY p x x') :
    tri k w x = (true, false, decide (A0 k w x)) ∧
      AxSim (⌊ζ * k⌋₊ - 1) x' (testPt k w (tri k w x)) := by
  obtain ⟨-, -, -, hw, -⟩ := piece_belt hx
  obtain ⟨c₀, ⟨X, h₁, h₂, h₃, h₄⟩, cp, cm⟩ := hc
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  obtain ⟨b₀, b₀', b₁, b₁'⟩ := fine_bounds hw hq
  have hpH : p ≤ ⌊ζ * k⌋₊ - 1 := by omega
  have hu : (2 : ℝ) ^ p ≤ hs k := pow_le_pow_right₀ (by norm_num) hpH
  have hH0 := hs_pos k
  have r₀ : SB (hs k) (f₀ x) (f₀ x') := sb_pow c₀ hpH
  have e₁ : 2 * w 0 * hs k ≤ f₀ x' := by
    have := (r₀ (2 * w 0)).1 (by push_cast; linarith); push_cast at this; linarith
  have e₂ : f₀ x' < (2 * w 0 + 2) * hs k := by
    by_contra h; push Not at h
    have := (r₀ (2 * w 0 + 2)).2 (by push_cast; linarith); push_cast at this; linarith
  have hlt : f₁ x' < 2 * w 1 * hs k := by
    by_contra h; push Not at h
    exact hx' (piece_of_fineIdx hx (fineIdx_eq_of_bounds hq e₁ e₂ h (by linarith)))
  have hX := grid_eq (n := 2 * w 1) hp h₁ h₂ h₃ h₄ (by push_cast; linarith) (by push_cast; linarith)
  push_cast at hX
  have hA : ¬ Ap k w x := by
    rw [show Ap k w x ↔ Ap k w x' from sb_pow cp hpH _]; unfold Ap fp; push_cast; intro h; linarith
  have hM : Am k w x := by
    rw [show Am k w x ↔ Am k w x' from sb_pow cm hpH _]; unfold Am fm; push_cast; linarith
  have htri : tri k w x = (true, false, decide (A0 k w x)) := by
    simp only [tri, hA, hM, false_iff, not_true_eq_false, not_false_eq_true, decide_false,
      decide_true, if_false]
  refine ⟨htri, ?_, ?_⟩ <;> rw [htri] <;> change SB (hs k) _ _
  · have t0 : A0 k w x ↔ A0 k w x' := r₀ _
    by_cases hA0 : A0 k w x
    · have h' := t0.1 hA0; unfold A0 at h'; push_cast at h'
      refine sb_of_mem hH0 (2 * w 0 + 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₀, hA0, decide_true, ↓reduceIte, add_sub_cancel_left] <;>
        push_cast <;> linarith
    · have h' := mt t0.2 hA0; unfold A0 at h'; push_cast at h'; push Not at h'
      refine sb_of_mem hH0 (2 * w 0) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₀, hA0, decide_false, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_left] <;> push_cast <;> linarith
  · refine sb_of_mem hH0 (2 * w 1 - 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
      simp only [testPt, f₁, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left] <;>
      push_cast <;> linarith

private lemma facing_up {p k : ℕ} {w : Fin 2 → ℤ} {x x' : ℝ × ℝ}
    (hx : L.piece x = .belt k w) (hx' : L.piece x' ≠ .belt k w) (hp : p + 1 ≤ ⌊ζ * k⌋₊)
    (hc : CrossY p x' x) :
    tri k w x = (true, true, decide (A0 k w x)) ∧
      AxSim (⌊ζ * k⌋₊ - 1) x' (testPt k w (tri k w x)) := by
  obtain ⟨-, -, -, hw, -⟩ := piece_belt hx
  obtain ⟨c₀, ⟨X, h₁, h₂, h₃, h₄⟩, cp, cm⟩ := hc
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  obtain ⟨b₀, b₀', b₁, b₁'⟩ := fine_bounds hw hq
  have hpH : p ≤ ⌊ζ * k⌋₊ - 1 := by omega
  have hu : (2 : ℝ) ^ p ≤ hs k := pow_le_pow_right₀ (by norm_num) hpH
  have hH0 := hs_pos k
  have r₀ : SB (hs k) (f₀ x) (f₀ x') := sb_symm (sb_pow c₀ hpH)
  have e₁ : 2 * w 0 * hs k ≤ f₀ x' := by
    have := (r₀ (2 * w 0)).1 (by push_cast; linarith); push_cast at this; linarith
  have e₂ : f₀ x' < (2 * w 0 + 2) * hs k := by
    by_contra h; push Not at h
    have := (r₀ (2 * w 0 + 2)).2 (by push_cast; linarith); push_cast at this; linarith
  have hgt : (2 * w 1 + 2) * hs k ≤ f₁ x' := by
    by_contra h; push Not at h
    exact hx' (piece_of_fineIdx hx (fineIdx_eq_of_bounds hq e₁ e₂ (by linarith) h))
  have hX := grid_eq (n := 2 * w 1 + 2) hp h₁ h₂ h₃ h₄ (by push_cast; linarith)
    (by push_cast; linarith)
  push_cast at hX
  have hA : Ap k w x := by
    rw [show Ap k w x ↔ Ap k w x' from sb_pow (sb_symm cp) hpH _]; unfold Ap fp; push_cast; linarith
  have hM : ¬ Am k w x := by
    rw [show Am k w x ↔ Am k w x' from sb_pow (sb_symm cm) hpH _]
    unfold Am fm; push_cast; intro h; linarith
  have htri : tri k w x = (true, true, decide (A0 k w x)) := by
    simp only [tri, hA, hM, iff_false, not_true_eq_false, not_false_eq_true, decide_true,
      if_false]
  refine ⟨htri, ?_, ?_⟩ <;> rw [htri] <;> change SB (hs k) _ _
  · have t0 : A0 k w x ↔ A0 k w x' := r₀ _
    by_cases hA0 : A0 k w x
    · have h' := t0.1 hA0; unfold A0 at h'; push_cast at h'
      refine sb_of_mem hH0 (2 * w 0 + 1) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₀, hA0, decide_true, ↓reduceIte, add_sub_cancel_left] <;>
        push_cast <;> linarith
    · have h' := mt t0.2 hA0; unfold A0 at h'; push_cast at h'; push Not at h'
      refine sb_of_mem hH0 (2 * w 0) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
        simp only [testPt, f₀, hA0, decide_false, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_left] <;> push_cast <;> linarith
  · refine sb_of_mem hH0 (2 * w 1 + 2) (by push_cast; linarith) (by push_cast; linarith) ?_ ?_ <;>
      simp only [testPt, f₁, ↓reduceIte, add_sub_cancel_left] <;>
      push_cast <;> linarith

end Layout

/-! ## D11.11.2 The fan -/

/-- The open octant `k` at the origin. -/
def openCone : Fin 8 → Set (ℝ × ℝ)
  | 0 => {p | 0 < p.2 ∧ p.2 < p.1}
  | 1 => {p | 0 < p.1 ∧ p.1 < p.2}
  | 2 => {p | 0 < -p.1 ∧ -p.1 < p.2}
  | 3 => {p | 0 < p.2 ∧ p.2 < -p.1}
  | 4 => {p | 0 < -p.2 ∧ -p.2 < -p.1}
  | 5 => {p | 0 < -p.1 ∧ -p.1 < -p.2}
  | 6 => {p | 0 < p.1 ∧ p.1 < -p.2}
  | 7 => {p | 0 < -p.2 ∧ -p.2 < p.1}

/-- The centre `o + (t_k/2)(2w + 1)` of the fine cell `w` of layer `k`. -/
def centre (k : ℕ) (w : Fin 2 → ℤ) : ℝ × ℝ :=
  (o₂ 0 + (2 * w 0 + 1) * hs k, o₂ 1 + (2 * w 1 + 1) * hs k)

/-- The triangle of the fan containing the open octant `j` about the centre. -/
def triTable : Fin 8 → Bool × Bool × Bool :=
  ![(false, true, true), (true, true, true), (true, true, false), (false, false, true),
    (false, false, false), (true, false, false), (true, false, true), (false, true, false)]

/-- D11.11.2. Fan. Join the cell centre to the endpoints of its elementary segments: `≤ 8`
triangles; edges have slopes `0, ∞, 1, -1`. Each triangle has exactly one outer segment. Here the
fan is the all-midpoint fan: its triangles are the eight octant triangles about the centre. -/
theorem step_11_11_2 {k : ℕ} {w : Fin 2 → ℤ} {x : ℝ × ℝ} {j : Fin 8}
    (h : x - centre k w ∈ openCone j) : tri k w x = triTable j := by
  have e₀ : (x - centre k w).1 = f₀ x - ((2 * w 0 + 1 : ℤ) : ℝ) * hs k := by
    simp only [centre, f₀, Prod.fst_sub]; push_cast; ring
  have e₁ : (x - centre k w).2 = f₁ x - ((2 * w 1 + 1 : ℤ) : ℝ) * hs k := by
    simp only [centre, f₁, Prod.snd_sub]; push_cast; ring
  unfold tri
  by_cases a : Ap k w x <;> by_cases b : Am k w x <;> by_cases c : A0 k w x <;>
    by_cases d : A1 k w x <;>
    simp only [a, b, c, d, iff_self, iff_true, iff_false, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false, ↓reduceIte] <;>
    unfold Ap Am A0 A1 fp fm at * <;> push_cast at * <;>
    fin_cases j <;> simp only [openCone, mem_ofPred_eq, triTable, Fin.reduceFinMk,
      Matrix.cons_val] at h ⊢ <;> rw [e₀, e₁] at h <;> first | rfl | (exfalso; linarith [h.1, h.2])

/-! ## D11.11.3–5 Labels across interfaces -/

namespace Layout

variable {L : Layout}

lemma label_tile_belt {x : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} (hx : L.piece x = .belt k w) :
    L.label (L.tile x) = L.lab k w (tri k w x) := by
  simp only [tile, hx, label]

lemma label_tile_nb {x : ℝ × ℝ} (hb : ∀ k w, L.piece x ≠ .belt k w) :
    L.label (L.tile x) = L.plabel (L.piece x) := by
  unfold tile
  rcases h : L.piece x with _ | _ | ⟨k, j⟩ | ⟨k, w⟩
  · rfl
  · rfl
  · rfl
  · exact absurd h (hb k w)

lemma label_ne_of_piece_eq {x x' : ℝ × ℝ} (hP : L.piece x = L.piece x')
    (hne : L.tile x ≠ L.tile x') : L.label (L.tile x) ≠ L.label (L.tile x') := by
  unfold tile at *
  rw [← hP] at hne ⊢
  rcases h : L.piece x with _ | _ | ⟨k, j⟩ | ⟨k, w⟩ <;>
    simp only [h, ne_eq, not_true_eq_false] at hne ⊢
  simpa [label] using hne

/-- Points near a point of `D_k` lie in layers `≥ k - 1`, whose meshes are `≥ t_k/2`. -/
lemma lay_near {x x' : ℝ × ℝ} {k : ℕ} (hx : pt x ∈ closure (D o₂ L.Z L.C₀ k)) (hk : L.k₀ ≤ k)
    (hK : k ≤ L.K) (hd : dist x x' < 2 ^ ⌊ζ * k⌋₊) : ⌊ζ * k⌋₊ - 1 ≤ ⌊ζ * L.lay x'⌋₊ := by
  have h2 := L.two_le_floor hk
  have hk1 : 1 ≤ k := by have := floor_zeta_le k; omega
  have hlt := floor_zeta_lt hk1
  have hd' : dist x x' < 2 ^ (k - 1) :=
    hd.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have h3 := lev_ge hx hk1 hd'
  have h4 := lay_ge (L := L) h3 (by omega)
  have h5 := floor_zeta_mono h4
  have h6 := floor_zeta_succ (k - 1)
  rw [Nat.sub_add_cancel hk1] at h6
  omega

lemma lab_eq {x x' : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} (hx : L.piece x = .belt k w)
    (hlay : ⌊ζ * k⌋₊ - 1 ≤ ⌊ζ * L.lay x'⌋₊)
    (hax : AxSim (⌊ζ * k⌋₊ - 1) x' (testPt k w (tri k w x))) :
    L.label (L.tile x) = L.gLab (tri k w x).2.1 (L.piece x') := by
  rw [label_tile_belt hx, lab, piece_eq_of_axSim hax hlay]

lemma belt_lay {x : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} (hx : L.piece x = .belt k w) :
    L.lay x = k ∧ pt x ∈ closure (D o₂ L.Z L.C₀ k) ∧ L.k₀ ≤ k ∧ k ≤ L.K := by
  obtain ⟨hl, hk, hK, -⟩ := piece_belt hx
  exact ⟨lay_eq hl hk hK, subset_closure (mem_D_lev hl), hk, hK.le⟩

/-- D11.11.1. Along a segment of a belt-cell side the opposing region is one primary, the dummy
tile, or one elementary segment of another belt cell. -/
theorem step_11_11_1 {p : ℕ} {x x' : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ}
    (hx : L.piece x = .belt k w) (hne : L.piece x ≠ L.piece x') (hp : p + 1 ≤ ⌊ζ * L.lay x⌋₊) :
    (CrossX p x x' → L.label (L.tile x) = L.gLab false (L.piece x')) ∧
    (CrossX p x' x → L.label (L.tile x) = L.gLab true (L.piece x')) ∧
    (CrossY p x x' → L.label (L.tile x) = L.gLab false (L.piece x')) ∧
    (CrossY p x' x → L.label (L.tile x) = L.gLab true (L.piece x')) := by
  obtain ⟨hl, hD, hk, hK⟩ := belt_lay hx
  rw [hl] at hp
  have hx' : L.piece x' ≠ .belt k w := fun h ↦ hne (hx.trans h.symm)
  have hpq : (2 : ℝ) ^ (p + 1) ≤ 2 ^ ⌊ζ * k⌋₊ := pow_le_pow_right₀ (by norm_num) hp
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_, fun hc ↦ ?_, fun hc ↦ ?_⟩
  · obtain ⟨h1, h2⟩ := facing_left hx hx' hp hc
    rw [lab_eq hx (lay_near hD hk hK ((dist_lt_of_crossX hc).trans_le hpq)) h2, h1]
  · obtain ⟨h1, h2⟩ := facing_right hx hx' hp hc
    have hd : dist x x' < 2 ^ ⌊ζ * k⌋₊ := by
      rw [dist_comm]; exact (dist_lt_of_crossX hc).trans_le hpq
    rw [lab_eq hx (lay_near hD hk hK hd) h2, h1]
  · obtain ⟨h1, h2⟩ := facing_down hx hx' hp hc
    rw [lab_eq hx (lay_near hD hk hK ((dist_lt_of_crossY hc).trans_le hpq)) h2, h1]
  · obtain ⟨h1, h2⟩ := facing_up hx hx' hp hc
    have hd : dist x x' < 2 ^ ⌊ζ * k⌋₊ := by
      rw [dist_comm]; exact (dist_lt_of_crossY hc).trans_le hpq
    rw [lab_eq hx (lay_near hD hk hK hd) h2, h1]

/-- Two adjacent non-belt fine cells of one layer lie in one pitch interior. -/
lemma pitch_eq {k : ℕ} {w w' : Fin 2 → ℤ} (hb : ¬ IsBeltCell k (L.a k) w) (i : Fin 2)
    (hi : w' i + 1 = w i)
    (hj : ∀ j, j ≠ i → w' j = w j) : L.pitchIdx k w = L.pitchIdx k w' := by
  have hm : (0 : ℤ) < ((s k / t k : ℕ) : ℤ) := by exact_mod_cast (scale_facts k).2.2.2.2.2.2.2
  funext j
  by_cases h : j = i
  · subst h
    simp only [pitchIdx]
    rw [show w' j = w j - 1 by omega, sub_right_comm, ediv_sub_one hm]
    exact fun hd ↦ hb ⟨j, (Int.modEq_of_dvd hd).symm⟩
  · simp only [pitchIdx, hj j h]

lemma pitch_eq_x {p k : ℕ} {j j' : Fin 2 → ℤ} {x x' : ℝ × ℝ} (hc : CrossX p x x')
    (hx : L.piece x = .primary k j) (hx' : L.piece x' = .primary k j')
    (hp : p + 1 ≤ ⌊ζ * k⌋₊) : j = j' := by
  obtain ⟨-, -, -, hb, rfl⟩ := piece_primary hx
  obtain ⟨-, -, -, -, rfl⟩ := piece_primary hx'
  obtain ⟨⟨X, h₁, h₂, h₃, h₄⟩, c₁, -, -⟩ := hc
  have hpos : (0 : ℝ) < 2 ^ ⌊ζ * k⌋₊ := by positivity
  have hu : (2 : ℝ) ^ p * 2 ≤ 2 ^ ⌊ζ * k⌋₊ := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hp
  have row : fineIdx k x' 1 = fineIdx k x 1 := by
    simp only [fineIdx, cellIndex_pt, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact ((sb_iff hpos).1 (sb_pow c₁ (by omega))).symm
  have a := Int.floor_mono (div_le_div_of_nonneg_right (show f₀ x' ≤ f₀ x by linarith) hpos.le)
  have b : ⌊f₀ x / 2 ^ ⌊ζ * k⌋₊⌋ - 1 ≤ ⌊f₀ x' / 2 ^ ⌊ζ * k⌋₊⌋ := by
    rw [Int.le_floor]; push_cast
    have := Int.floor_le (f₀ x / 2 ^ ⌊ζ * k⌋₊)
    have : f₀ x / 2 ^ ⌊ζ * k⌋₊ - 1 < f₀ x' / 2 ^ ⌊ζ * k⌋₊ := by
      rw [div_sub_one hpos.ne', div_lt_div_iff_of_pos_right hpos]; linarith
    linarith
  have col : fineIdx k x' 0 = fineIdx k x 0 ∨ fineIdx k x' 0 + 1 = fineIdx k x 0 := by
    simp only [fineIdx, cellIndex_pt, Matrix.cons_val_zero]; omega
  rcases col with h | h
  · congr 1; funext i; fin_cases i
    · exact h.symm
    · exact row.symm
  · exact pitch_eq hb 0 h fun j hj ↦ by
      fin_cases j <;> first | exact absurd rfl hj | exact row

lemma pitch_eq_y {p k : ℕ} {j j' : Fin 2 → ℤ} {x x' : ℝ × ℝ} (hc : CrossY p x x')
    (hx : L.piece x = .primary k j) (hx' : L.piece x' = .primary k j')
    (hp : p + 1 ≤ ⌊ζ * k⌋₊) : j = j' := by
  obtain ⟨-, -, -, hb, rfl⟩ := piece_primary hx
  obtain ⟨-, -, -, -, rfl⟩ := piece_primary hx'
  obtain ⟨c₀, ⟨X, h₁, h₂, h₃, h₄⟩, -, -⟩ := hc
  have hpos : (0 : ℝ) < 2 ^ ⌊ζ * k⌋₊ := by positivity
  have hu : (2 : ℝ) ^ p * 2 ≤ 2 ^ ⌊ζ * k⌋₊ := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hp
  have row : fineIdx k x' 0 = fineIdx k x 0 := by
    simp only [fineIdx, cellIndex_pt, Matrix.cons_val_zero]
    exact ((sb_iff hpos).1 (sb_pow c₀ (by omega))).symm
  have a := Int.floor_mono (div_le_div_of_nonneg_right (show f₁ x' ≤ f₁ x by linarith) hpos.le)
  have b : ⌊f₁ x / 2 ^ ⌊ζ * k⌋₊⌋ - 1 ≤ ⌊f₁ x' / 2 ^ ⌊ζ * k⌋₊⌋ := by
    rw [Int.le_floor]; push_cast
    have := Int.floor_le (f₁ x / 2 ^ ⌊ζ * k⌋₊)
    have : f₁ x / 2 ^ ⌊ζ * k⌋₊ - 1 < f₁ x' / 2 ^ ⌊ζ * k⌋₊ := by
      rw [div_sub_one hpos.ne', div_lt_div_iff_of_pos_right hpos]; linarith
    linarith
  have col : fineIdx k x' 1 = fineIdx k x 1 ∨ fineIdx k x' 1 + 1 = fineIdx k x 1 := by
    simp only [fineIdx, cellIndex_pt, Matrix.cons_val_one, Matrix.cons_val_zero]; omega
  rcases col with h | h
  · congr 1; funext i; fin_cases i
    · exact row.symm
    · exact h.symm
  · exact pitch_eq hb 1 h fun j hj ↦ by
      fin_cases j <;> first | exact absurd rfl hj | exact row

lemma lay_dummy {x : ℝ × ℝ} (h : L.piece x = .dummy) : L.lay x = L.k₀ := by
  simp [lay, piece_dummy h]

lemma lay_exterior {x : ℝ × ℝ} (h : L.piece x = .exterior) : L.lay x = L.K := by
  have := piece_exterior h; have := L.lt_K
  unfold lay; split_ifs <;> omega

/-- D11.11.5. Distinct non-belt pieces meeting across a grid line finer than both local meshes
have opposite labels: adjacent layers, or the dummy (exterior) tile and layer `k₀` (`K - 1`). -/
lemma nonbelt_ne {p : ℕ} {x x' : ℝ × ℝ} (hP : L.piece x ≠ L.piece x')
    (hb : ∀ k w, L.piece x ≠ .belt k w) (hb' : ∀ k w, L.piece x' ≠ .belt k w)
    (hd : dist x x' < 2 ^ (p + 1)) (hp : p + 1 ≤ ⌊ζ * L.lay x⌋₊)
    (hp' : p + 1 ≤ ⌊ζ * L.lay x'⌋₊)
    (hpitch : ∀ k j j', L.piece x = .primary k j → L.piece x' = .primary k j' → j = j') :
    L.plabel (L.piece x) ≠ L.plabel (L.piece x') := by
  have fl := floor_zeta_le (L.lay x)
  have fl' := floor_zeta_le (L.lay x')
  have hK := L.lt_K
  have hd' : dist x' x < 2 ^ (p + 1) := by rwa [dist_comm]
  rcases hx : L.piece x with _ | _ | ⟨k, j⟩ | ⟨k, w⟩ <;>
    rcases hx' : L.piece x' with _ | _ | ⟨k', j'⟩ | ⟨k', w'⟩
  all_goals first
    | exact absurd hx (hb _ _) | exact absurd hx' (hb' _ _)
    | exact absurd (hx.trans hx'.symm) hP | skip
  · -- dummy, exterior
    have h1 := piece_dummy hx; have h2 := piece_exterior hx'; have := lay_dummy hx
    exact (L.far (mem_N_iff_lev.2 h1) (subset_closure (mem_D_lev (k := L.lev x' - 1)
      (by omega))) (by omega) (by omega) hd).elim
  · -- dummy, primary
    have h1 := piece_dummy hx; have := lay_dummy hx
    obtain ⟨h2, hk', -⟩ := piece_primary hx'
    rcases (show k' = L.k₀ ∨ L.k₀ + 1 ≤ k' by omega) with rfl | h
    · simp only [plabel, par_succ]; exact (ne_add_one _).symm
    · exact (L.far (mem_N_iff_lev.2 h1) (subset_closure (mem_D_lev h2)) h (by omega) hd).elim
  · -- exterior, dummy
    have h1 := piece_dummy hx'; have h2 := piece_exterior hx; have := lay_dummy hx'
    exact (L.far (mem_N_iff_lev.2 h1) (subset_closure (mem_D_lev (k := L.lev x - 1)
      (by omega))) (by omega) (by omega) hd').elim
  · -- exterior, primary
    have h1 := piece_exterior hx
    obtain ⟨h2, hk', hK', -⟩ := piece_primary hx'
    have := lay_eq h2 hk' hK'
    rcases (show k' + 1 = L.K ∨ k' + 2 ≤ L.K by omega) with h | h
    · simp only [plabel]; rw [← h, par_succ]; exact (ne_add_one _).symm
    · exact (L.far (mem_N_iff_lev.2 h2.le) (subset_closure (mem_D_lev (k := L.lev x - 1)
        (by omega))) (by omega) (by omega) hd').elim
  · -- primary, dummy
    have h1 := piece_dummy hx'; have := lay_dummy hx'
    obtain ⟨h2, hk, -⟩ := piece_primary hx
    rcases (show k = L.k₀ ∨ L.k₀ + 1 ≤ k by omega) with rfl | h
    · simp only [plabel, par_succ]; exact ne_add_one _
    · exact (L.far (mem_N_iff_lev.2 h1) (subset_closure (mem_D_lev h2)) h (by omega) hd').elim
  · -- primary, exterior
    have h1 := piece_exterior hx'
    obtain ⟨h2, hk, hK', -⟩ := piece_primary hx
    have := lay_eq h2 hk hK'
    rcases (show k + 1 = L.K ∨ k + 2 ≤ L.K by omega) with h | h
    · simp only [plabel]; rw [← h, par_succ]; exact ne_add_one _
    · exact (L.far (mem_N_iff_lev.2 h2.le) (subset_closure (mem_D_lev (k := L.lev x' - 1)
        (by omega))) (by omega) (by omega) hd).elim
  · -- primary, primary
    obtain ⟨h2, hk, hK', -⟩ := piece_primary hx
    obtain ⟨h2', hk', hK'', -⟩ := piece_primary hx'
    have := lay_eq h2 hk hK'; have := lay_eq h2' hk' hK''
    rcases (show k = k' ∨ k' = k + 1 ∨ k = k' + 1 ∨ k + 2 ≤ k' ∨ k' + 2 ≤ k by omega) with
      rfl | rfl | rfl | h | h
    · exact absurd (hx.trans ((congrArg (Piece.primary k) (hpitch _ _ _ hx hx')).trans hx'.symm)) hP
    · simp only [plabel, par_succ]; exact ne_add_one _
    · simp only [plabel, par_succ]; exact (ne_add_one _).symm
    · exact (L.far (mem_N_iff_lev.2 h2.le) (subset_closure (mem_D_lev h2')) (by omega)
        (by omega) hd).elim
    · exact (L.far (mem_N_iff_lev.2 h2'.le) (subset_closure (mem_D_lev h2)) (by omega)
        (by omega) hd').elim

/-- The interface lemma across one grid line, given the facing labels of both sides. -/
lemma interface {p : ℕ} {x x' : ℝ × ℝ} {s : Bool} (hd : dist x x' < 2 ^ (p + 1))
    (hp : p + 1 ≤ ⌊ζ * L.lay x⌋₊) (hp' : p + 1 ≤ ⌊ζ * L.lay x'⌋₊) (hne : L.tile x ≠ L.tile x')
    (hb : ∀ k w, L.piece x = .belt k w → L.piece x ≠ L.piece x' →
      L.label (L.tile x) = L.gLab s (L.piece x'))
    (hb' : ∀ k w, L.piece x' = .belt k w → L.piece x ≠ L.piece x' →
      L.label (L.tile x') = L.gLab (!s) (L.piece x))
    (hpitch : ∀ k j j', L.piece x = .primary k j → L.piece x' = .primary k j' → j = j') :
    L.label (L.tile x) ≠ L.label (L.tile x') := by
  by_cases hP : L.piece x = L.piece x'
  · exact label_ne_of_piece_eq hP hne
  by_cases e : ∃ k w, L.piece x = .belt k w
  · obtain ⟨k, w, hx⟩ := e
    rw [hb k w hx hP]
    by_cases e' : ∃ k w, L.piece x' = .belt k w
    · obtain ⟨k', w', hx'⟩ := e'
      rw [hb' k' w' hx' hP, hx, hx']; cases s <;> simp [gLab]
    · push Not at e'
      rw [label_tile_nb e']
      rcases hx' : L.piece x' with _ | _ | ⟨k', j'⟩ | ⟨k', w'⟩
      · exact (ne_add_one _).symm
      · exact (ne_add_one _).symm
      · exact (ne_add_one _).symm
      · exact absurd hx' (e' _ _)
  · push Not at e
    rw [label_tile_nb e]
    by_cases e' : ∃ k w, L.piece x' = .belt k w
    · obtain ⟨k', w', hx'⟩ := e'
      rw [hb' k' w' hx' hP]
      rcases hx : L.piece x with _ | _ | ⟨k, j⟩ | ⟨k, w⟩
      · exact ne_add_one _
      · exact ne_add_one _
      · exact ne_add_one _
      · exact absurd hx (e _ _)
    · push Not at e'
      rw [label_tile_nb e']
      exact nonbelt_ne hP e e' hd hp hp' hpitch

lemma lay_primary {x : ℝ × ℝ} {k : ℕ} {j : Fin 2 → ℤ} (h : L.piece x = .primary k j) :
    L.lay x = k := by
  obtain ⟨hl, hk, hK, -⟩ := piece_primary h; exact lay_eq hl hk hK

/-- D11.11. Belt cells get tile identifiers and labels such that every positive-length interface
between distinct identifiers joins opposite labels. Hence a same-label contact between distinct
tiles is a single point and involves a belt cell.
2D only: planar fans of eight triangles and the four slopes of the plane. -/
theorem step_11_11 {p : ℕ} {x x' : ℝ × ℝ}
    (hc : CrossX p x x' ∨ CrossY p x x' ∨ AxSim p x x') (hp : p + 1 ≤ ⌊ζ * L.lay x⌋₊)
    (hp' : p + 1 ≤ ⌊ζ * L.lay x'⌋₊) (hne : L.tile x ≠ L.tile x') :
    L.label (L.tile x) ≠ L.label (L.tile x') := by
  rcases hc with hc | hc | hc
  · -- D11.11.5: across a vertical cell side
    refine interface (s := false) (dist_lt_of_crossX hc) hp hp' hne
      (fun k w hx hP ↦ (step_11_11_1 hx hP hp).1 hc)
      (fun k w hx hP ↦ (step_11_11_1 hx (Ne.symm hP) hp').2.1 hc)
      fun k j j' hx hx' ↦ pitch_eq_x hc hx hx' (by rwa [lay_primary hx] at hp)
  · -- D11.11.5: across a horizontal cell side
    refine interface (s := false) (dist_lt_of_crossY hc) hp hp' hne
      (fun k w hx hP ↦ (step_11_11_1 hx hP hp).2.2.1 hc)
      (fun k w hx hP ↦ (step_11_11_1 hx (Ne.symm hP) hp').2.2.2 hc)
      fun k j j' hx hx' ↦ pitch_eq_y hc hx hx' (by rwa [lay_primary hx] at hp)
  · -- D11.11.5: inside a fan, equal-label triangles are merged
    exact label_ne_of_piece_eq (piece_eq_of_axSim hc (by omega)) hne

end Layout

/-! ## D11.12 Initial marks -/

/-- D11.12. The marks of the fine cell `w` of layer `k`, as lattice offsets from `o`: centre,
corners and side midpoints `t_k w + (t_k/2) e`, `e ∈ {0,1,2}²`. -/
def markInt (k : ℕ) (w : Fin 2 → ℤ) (e : Fin 3 × Fin 3) : ℤ × ℤ :=
  (2 ^ ⌊ζ * k⌋₊ * w 0 + 2 ^ (⌊ζ * k⌋₊ - 1) * (e.1 : ℕ),
    2 ^ ⌊ζ * k⌋₊ * w 1 + 2 ^ (⌊ζ * k⌋₊ - 1) * (e.2 : ℕ))

/-- D11.12. The mark `o + t_k w + (t_k/2) e` of the fine cell `w` of layer `k`. -/
def markPos (k : ℕ) (w : Fin 2 → ℤ) (e : Fin 3 × Fin 3) : ℝ × ℝ :=
  (o₂ 0, o₂ 1) + latticePoint (markInt k w e)

lemma f_markPos (k : ℕ) (w : Fin 2 → ℤ) (e : Fin 3 × Fin 3) :
    f₀ (markPos k w e) = (markInt k w e).1 ∧ f₁ (markPos k w e) = (markInt k w e).2 := by
  simp [f₀, f₁, markPos, latticePoint]

/-- The marks of layer `k` lie on the mesh `2^r ℤ²` for every `r < ⌊ζk⌋`. -/
lemma markInt_eq {k r : ℕ} (hr : r + 1 ≤ ⌊ζ * k⌋₊) (w : Fin 2 → ℤ) (e : Fin 3 × Fin 3) :
    (markInt k w e).1 = (2 * w 0 + (e.1 : ℕ)) * 2 ^ (⌊ζ * k⌋₊ - 1 - r) * 2 ^ r ∧
      (markInt k w e).2 = (2 * w 1 + (e.2 : ℕ)) * 2 ^ (⌊ζ * k⌋₊ - 1 - r) * 2 ^ r := by
  obtain ⟨n, hn⟩ : ∃ n, ⌊ζ * k⌋₊ = n + r + 1 := ⟨⌊ζ * k⌋₊ - r - 1, by omega⟩
  simp only [markInt, hn, Nat.add_sub_cancel]
  constructor <;> ring

namespace Layout

variable (L : Layout)

open Classical in
/-- D11.12. The initial marks: centre, four corners and four side midpoints of every belt cell
(midpoints even when the fan omits them), deduplicated. -/
def marks : Finset (ℝ × ℝ) :=
  (Finset.Ico L.k₀ L.K).biUnion fun k ↦ (beltIndex o₂ L.Z L.C₀ k (L.a k)).biUnion fun w ↦
    Finset.univ.image (markPos k w)

/-- D11.12. `v` is a mark of a belt cell of layer `k`. -/
def Marks (v : ℝ × ℝ) (k : ℕ) : Prop :=
  L.k₀ ≤ k ∧ k < L.K ∧ ∃ w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k), ∃ e, markPos k w e = v

variable {L}

lemma mem_marks {v : ℝ × ℝ} : v ∈ L.marks ↔ ∃ k, L.Marks v k := by
  classical
  simp only [marks, Marks, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image,
    Finset.mem_univ, true_and, and_assoc]

variable (L)

open Classical in
/-- D11.12. The layer of the smallest belt cell marking `v`. -/
def markLayer (v : L.marks) : ℕ := Nat.find (mem_marks.1 v.2)

/-- D11.12. The scale `S_v` of a mark: the smallest side `t_k` of a belt cell that marked it. -/
def markScale (v : L.marks) : ℝ := t (L.markLayer v)

lemma marks_markLayer (v : L.marks) : L.Marks v.1 (L.markLayer v) := by
  classical
  exact Nat.find_spec (mem_marks.1 v.2)

/-- D11.12. `S_v` is the smallest side of a belt cell marking `v`. -/
lemma markScale_le (v : L.marks) {k : ℕ} (hk : L.Marks v.1 k) : L.markScale v ≤ t k := by
  classical
  have : L.markLayer v ≤ k := Nat.find_min' _ hk
  rw [markScale, t_eq, t_eq]
  exact pow_le_pow_right₀ (by norm_num) (floor_zeta_mono this)

/-- D11.12. Mark centre, four corners and four side midpoints of every belt cell (midpoints even
when the fan omits them). Deduplicate; mark `v` gets scale `S_v` = smallest side of a belt cell
that marked it. At most `9×`(number of belt cells) initial marks.
2D only: the nine marks of a planar square. -/
theorem step_11_12 :
    L.marks.card ≤ 9 * ∑ k ∈ Finset.Ico L.k₀ L.K, (beltIndex o₂ L.Z L.C₀ k (L.a k)).card := by
  classical
  unfold marks
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rw [mul_comm]
  exact Finset.card_biUnion_le_card_mul _ _ _ fun w _ ↦ Finset.card_image_le.trans (by simp)

end Layout

end

end AreaLaw.Geometry
