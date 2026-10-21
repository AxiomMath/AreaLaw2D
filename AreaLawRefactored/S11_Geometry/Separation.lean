import AreaLawRefactored.S11_Geometry.TileShapes

/-! # §11.6 Separation from earlier actual regions

The order of the tile identifiers (D11.17) and Lemma 11.5 (D11.18): the closed birth region of
an initial belt tile, or of a replacement tile, is far from the final actual region of every
earlier or peer identifier of the same label.

Digest `digest/11-geometry.md` D11.17, D11.18 -/

open Set Metric Filter Topology

namespace AreaLaw.Geometry

noncomputable section

/-! ## D11.17 The order of the tile identifiers -/

namespace Layout

variable (L : Layout)

/-- D11.17. Order: all primaries first, all initial belt tiles second, then replacement tiles by
generation of birth; ties arbitrary. Dummy tile excluded. Primaries already have the required
same-label separation among themselves (D11.10, D11.7). Lemma 11.5 covers all other
identifiers. Here: rank `0` for primaries, `1` for initial belt tiles, `g + 2` for the
replacements born at the marks of generation `g`.
2D only: the identifiers are those of the planar initial configuration and its planar repair. -/
def rank : TileId InitId L.marks → ℕ
  | .init (.primary _ _) => 0
  | .init (.belt _ _ _) => 1
  | .init .dummy => 0
  | .init .exterior => 0
  | .repl m _ => m.gen + 2

/-- D11.17. The identifiers in the order: all but the dummy and the exterior tile. -/
def Ordered : TileId InitId L.marks → Prop
  | .init .dummy => False
  | .init .exterior => False
  | _ => True

/-- D11.17. The order of the identifiers: by rank, ties broken by a fixed well-order. -/
@[instance_reducible] def order : LinearOrder (TileId InitId L.marks) :=
  LinearOrder.lift' (fun a ↦ toLex (L.rank a, embeddingToCardinal a))
    fun _ _ h ↦ embeddingToCardinal.injective (congrArg Prod.snd (toLex.injective h))

/-- D11.17. The order on the identifiers in the order. -/
@[instance_reducible] def orderedOrder : LinearOrder {a // L.Ordered a} :=
  @Subtype.instLinearOrder _ L.order _

variable {L}

theorem order_lt_of_rank_lt {a b : TileId InitId L.marks} (h : L.rank a < L.rank b) :
    L.order.lt a b :=
  Prod.Lex.left _ _ h

lemma birthGen_le_of_rank_le {a : TileId InitId L.marks} {m : Mark L.marks}
    {c : TileId InitId L.marks} (h : L.rank a ≤ L.rank (.repl m c)) : a.birthGen ≤ m.gen + 1 := by
  rcases a with _ | ⟨m', _⟩
  · exact Nat.zero_le _
  · simp only [rank] at h; simp only [TileId.birthGen]; omega

end Layout

/-! ## D11.18 Grid points near two close points -/

lemma exists_line {u F F' : ℝ} (hu : 0 < u) (hF : |F - F'| < u) (h : ¬ SB u F F') :
    ∃ n : ℤ, |F - n * u| ≤ |F - F'| ∧ (Adj u F F' ∨ Adj u F' F) := by
  rw [sb_iff hu] at h
  have a₀ := Int.floor_le (F / u)
  have b₀ := Int.lt_floor_add_one (F / u)
  have a₁ := Int.floor_le (F' / u)
  have b₁ := Int.lt_floor_add_one (F' / u)
  rw [le_div_iff₀ hu] at a₀ a₁
  rw [div_lt_iff₀ hu] at b₀ b₁
  generalize ⌊F / u⌋ = a at *
  generalize ⌊F' / u⌋ = b at *
  rw [abs_lt] at hF
  have h₁ : (a : ℝ) < b + 2 := by
    by_contra hc; push Not at hc; nlinarith [mul_le_mul_of_nonneg_right hc hu.le]
  have h₂ : (b : ℝ) < a + 2 := by
    by_contra hc; push Not at hc; nlinarith [mul_le_mul_of_nonneg_right hc hu.le]
  have h₁' : a < b + 2 := by exact_mod_cast h₁
  have h₂' : b < a + 2 := by exact_mod_cast h₂
  rcases (by omega : a = b + 1 ∨ b = a + 1) with e | e
  · have e' : (a : ℝ) = b + 1 := by exact_mod_cast e
    have c₁ : F' < a * u := by rw [e']; exact b₁
    refine ⟨a, ?_, Or.inl ⟨a, a₀, b₀, by rw [e']; linarith, c₁⟩⟩
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · have e' : (b : ℝ) = a + 1 := by exact_mod_cast e
    have c₁ : F < b * u := by rw [e']; exact b₀
    refine ⟨b, ?_, Or.inr ⟨b, a₁, b₁, by rw [e']; linarith, c₁⟩⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

lemma dist_le_of_f {x : ℝ × ℝ} {A B r : ℝ} (h₀ : |f₀ x - A| ≤ r) (h₁ : |f₁ x - B| ≤ r) :
    dist x (o₂ 0 + A, o₂ 1 + B) ≤ r := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le ?_ ?_
  · rw [show x.1 - (o₂ 0 + A) = f₀ x - A by unfold f₀; ring]; exact h₀
  · rw [show x.2 - (o₂ 1 + B) = f₁ x - B by unfold f₁; ring]; exact h₁

lemma exists_mesh_pt {x : ℝ × ℝ} {p : ℕ} (n₀ n₁ : ℤ) {r : ℝ} (h₀ : |f₀ x - n₀ * 2 ^ p| ≤ r)
    (h₁ : |f₁ x - n₁ * 2 ^ p| ≤ r) :
    ∃ P : ℝ × ℝ, (∃ n₀ n₁ : ℤ, f₀ P = n₀ * 2 ^ p ∧ f₁ P = n₁ * 2 ^ p) ∧ dist x P ≤ r :=
  ⟨(o₂ 0 + n₀ * 2 ^ p, o₂ 1 + n₁ * 2 ^ p), ⟨n₀, n₁, by simp [f₀], by simp [f₁]⟩,
    dist_le_of_f h₀ h₁⟩

/-- D11.18.3. Two close points separated by more than one grid line of mesh `2^p`: two of the
lines, one axis-parallel, meet at a point of the mesh `2^p` near the points. -/
lemma exists_mesh_near {p : ℕ} {x y : ℝ × ℝ} (hd : dist x y < 2 ^ p / 4)
    (hc : ¬ (CrossX p x y ∨ CrossX p y x ∨ CrossY p x y ∨ CrossY p y x ∨ AxSim p x y)) :
    ∃ P : ℝ × ℝ, (∃ n₀ n₁ : ℤ, f₀ P = n₀ * 2 ^ p ∧ f₁ P = n₁ * 2 ^ p) ∧
      dist x P ≤ 3 * dist x y := by
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  obtain ⟨d₀, d₁⟩ := abs_sub_le_dist x y
  have dp : |fp x - fp y| ≤ 2 * dist x y := by
    rw [show fp x - fp y = (f₀ x - f₀ y) + (f₁ x - f₁ y) by unfold fp; ring]
    linarith [abs_add_le (f₀ x - f₀ y) (f₁ x - f₁ y)]
  have dm : |fm x - fm y| ≤ 2 * dist x y := by
    rw [show fm x - fm y = (f₀ x - f₀ y) - (f₁ x - f₁ y) by unfold fm; ring]
    linarith [abs_sub (f₀ x - f₀ y) (f₁ x - f₁ y)]
  have hD := dist_nonneg (x := x) (y := y)
  by_cases e₀ : SB (2 ^ p) (f₀ x) (f₀ y)
  · have e₁ : ¬ SB (2 ^ p) (f₁ x) (f₁ y) := fun e₁ ↦ hc (Or.inr (Or.inr (Or.inr (Or.inr ⟨e₀, e₁⟩))))
    obtain ⟨n₁, hn₁, ha⟩ := exists_line hu (by linarith) e₁
    by_cases ep : SB (2 ^ p) (fp x) (fp y)
    · by_cases em : SB (2 ^ p) (fm x) (fm y)
      · exfalso
        rcases ha with ha | ha
        · exact hc (Or.inr (Or.inr (Or.inl ⟨e₀, ha, ep, em⟩)))
        · exact hc (Or.inr (Or.inr (Or.inr (Or.inl ⟨sb_symm e₀, ha, sb_symm ep, sb_symm em⟩))))
      · obtain ⟨nm, hnm, -⟩ := exists_line hu (by linarith) em
        refine exists_mesh_pt (nm + n₁) n₁ ?_ (by linarith)
        rw [show f₀ x - ((nm + n₁ : ℤ) : ℝ) * 2 ^ p =
          (fm x - nm * 2 ^ p) + (f₁ x - n₁ * 2 ^ p) by unfold fm; push_cast; ring]
        linarith [abs_add_le (fm x - nm * 2 ^ p) (f₁ x - n₁ * 2 ^ p)]
    · obtain ⟨np, hnp, -⟩ := exists_line hu (by linarith) ep
      refine exists_mesh_pt (np - n₁) n₁ ?_ (by linarith)
      rw [show f₀ x - ((np - n₁ : ℤ) : ℝ) * 2 ^ p =
        (fp x - np * 2 ^ p) - (f₁ x - n₁ * 2 ^ p) by unfold fp; push_cast; ring]
      linarith [abs_sub (fp x - np * 2 ^ p) (f₁ x - n₁ * 2 ^ p)]
  · obtain ⟨n₀, hn₀, ha⟩ := exists_line hu (by linarith) e₀
    by_cases e₁ : SB (2 ^ p) (f₁ x) (f₁ y)
    · by_cases ep : SB (2 ^ p) (fp x) (fp y)
      · by_cases em : SB (2 ^ p) (fm x) (fm y)
        · exfalso
          rcases ha with ha | ha
          · exact hc (Or.inl ⟨ha, e₁, ep, em⟩)
          · exact hc (Or.inr (Or.inl ⟨ha, sb_symm e₁, sb_symm ep, sb_symm em⟩))
        · obtain ⟨nm, hnm, -⟩ := exists_line hu (by linarith) em
          refine exists_mesh_pt n₀ (n₀ - nm) (by linarith) ?_
          rw [show f₁ x - ((n₀ - nm : ℤ) : ℝ) * 2 ^ p =
            (f₀ x - n₀ * 2 ^ p) - (fm x - nm * 2 ^ p) by unfold fm; push_cast; ring]
          linarith [abs_sub (f₀ x - n₀ * 2 ^ p) (fm x - nm * 2 ^ p)]
      · obtain ⟨np, hnp, -⟩ := exists_line hu (by linarith) ep
        refine exists_mesh_pt n₀ (np - n₀) (by linarith) ?_
        rw [show f₁ x - ((np - n₀ : ℤ) : ℝ) * 2 ^ p =
          (fp x - np * 2 ^ p) - (f₀ x - n₀ * 2 ^ p) by unfold fp; push_cast; ring]
        linarith [abs_sub (fp x - np * 2 ^ p) (f₀ x - n₀ * 2 ^ p)]
    · obtain ⟨n₁, hn₁, -⟩ := exists_line hu (by linarith) e₁
      exact exists_mesh_pt n₀ n₁ (by linarith) (by linarith)

/-! ## D11.18 The star at a grid point -/

lemma test_iff {u θ F₀ F₁ F₂ : ℝ} (hu : 0 < u) {a b : ℤ} (hθ : θ = a * u) (hF : F₀ = b * u)
    (hab : a ≠ b) (h₁ : |F₁ - F₀| < u) (h₂ : |F₂ - F₀| < u) : θ ≤ F₁ ↔ θ ≤ F₂ := by
  rw [abs_lt] at h₁ h₂
  rcases lt_or_gt_of_ne hab with h | h
  · have := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show a + 1 ≤ b by omega) : (a : ℝ) + 1 ≤ b) hu.le
    constructor <;> intro _ <;> linarith
  · have := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show b + 1 ≤ a by omega) : (b : ℝ) + 1 ≤ a) hu.le
    constructor <;> intro _ <;> linarith

lemma mesh_mem {u F : ℝ} (hu : 0 < u) {a b n : ℤ} (h₁ : a * u ≤ F) (h₂ : F < b * u)
    (h : |F - n * u| < u) : a ≤ n ∧ n ≤ b := by
  rw [abs_lt] at h
  have e₁ : (a : ℝ) < n + 1 := lt_of_mul_lt_mul_right (by linarith) hu.le
  have e₂ : (n : ℝ) - 1 < b := lt_of_mul_lt_mul_right (by linarith) hu.le
  have : a < n + 1 := by exact_mod_cast e₁
  have : n - 1 < b := by exact_mod_cast e₂
  omega

lemma tri_eq_of_iff {k : ℕ} {w : Fin 2 → ℤ} {x x' : ℝ × ℝ} (hAp : Ap k w x ↔ Ap k w x')
    (hAm : Am k w x ↔ Am k w x') (hA0 : A0 k w x ↔ A0 k w x') (hA1 : A1 k w x ↔ A1 k w x') :
    tri k w x = tri k w x' := by
  unfold tri
  by_cases a : Ap k w x <;> by_cases b : Am k w x <;> by_cases c : A0 k w x <;>
    by_cases e : A1 k w x <;> simp_all

/-- The sample point of the open octant `r` about a point `P` of the mesh `2^p`. -/
def smp (P : ℝ × ℝ) (p : ℕ) (r : Fin 8) : ℝ × ℝ := P + ((2 : ℝ) ^ p / 16) • octDir r

lemma dist_smp (P : ℝ × ℝ) (p : ℕ) (r : Fin 8) : dist (smp P p r) P = 2 ^ p / 8 := by
  rw [smp, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_octDir, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  ring

lemma axSim_smp {P : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ P = n₀ * 2 ^ p)
    (h₁ : f₁ P = n₁ * 2 ^ p) {r : Fin 8} (hr : r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6) :
    AxSim p (smp P p r) (smp P p (r + 1)) := by
  have hδ : (0 : ℝ) < 2 ^ p / 16 := by positivity
  have hδu : 2 ^ p / 16 * 3 < (2 : ℝ) ^ p := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) p]
  simp only [smp, AxSim, f₀_add, f₁_add, h₀, h₁]
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp only [octDir, Fin.isValue, Fin.reduceAdd, Matrix.cons_val] <;>
    exact ⟨sb_dir hδ hδu _ (by norm_num [abs_le]) (by norm_num [abs_le]) (by norm_num),
      sb_dir hδ hδu _ (by norm_num [abs_le]) (by norm_num [abs_le]) (by norm_num)⟩

namespace Layout

variable {L : Layout}

/-- D11.18.2. Near a point `P` of the mesh `2^p` whose surroundings have mesh `≥ 2^{p+1}`, the
identifier is constant on each open octant about `P`. -/
lemma tile_eq_smp {P : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ P = n₀ * 2 ^ p)
    (h₁ : f₁ P = n₁ * 2 ^ p) (hlay : ∀ y, dist y P < 2 ^ p / 2 → p + 1 ≤ ⌊ζ * L.lay y⌋₊)
    {r : Fin 8} {y : ℝ × ℝ} (hy : y - P ∈ openCone r) (hd : dist y P < 2 ^ p / 2) :
    L.tile y = L.tile (smp P p r) := by
  have hs : smp P p r - P ∈ openCone r := by
    rw [smp, add_sub_cancel_left]; exact smul_octDir_mem (by positivity) r
  have hds : dist (smp P p r) P < 2 ^ p / 2 := by
    rw [dist_smp]; linarith [pow_pos (two_pos : (0 : ℝ) < 2) p]
  exact tile_eq_of_sim (sim_of_sector h₀ h₁ hy hs hd hds) (hlay y hd)

/-- D11.18.3. Consecutive octants about a mesh point with distinct identifiers have opposite
labels (`step_11_11`). -/
lemma label_ne_smp {P : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ P = n₀ * 2 ^ p)
    (h₁ : f₁ P = n₁ * 2 ^ p) (hlay : ∀ y, dist y P < 2 ^ p / 2 → p + 1 ≤ ⌊ζ * L.lay y⌋₊)
    (r : Fin 8) (h : L.tile (smp P p r) ≠ L.tile (smp P p (r + 1))) :
    L.label (L.tile (smp P p r)) ≠ L.label (L.tile (smp P p (r + 1))) := by
  have hδ : (0 : ℝ) < 2 ^ p / 16 := by positivity
  have hδu : 2 ^ p / 16 * 3 < (2 : ℝ) ^ p := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) p]
  have hl (r' : Fin 8) : p + 1 ≤ ⌊ζ * L.lay (smp P p r')⌋₊ :=
    hlay _ (by rw [dist_smp]; linarith [pow_pos (two_pos : (0 : ℝ) < 2) p])
  rcases oct_cross h₀ h₁ hδ hδu r with hc | hc | hc | hc | hc
  · exact step_11_11 (Or.inl hc) (hl r) (hl (r + 1)) h
  · exact (step_11_11 (Or.inl hc) (hl (r + 1)) (hl r) (Ne.symm h)).symm
  · exact step_11_11 (Or.inr (Or.inl hc)) (hl r) (hl (r + 1)) h
  · exact (step_11_11 (Or.inr (Or.inl hc)) (hl (r + 1)) (hl r) (Ne.symm h)).symm
  · exact step_11_11 (Or.inr (Or.inr hc)) (hl r) (hl (r + 1)) h

lemma exists_belt_of_tile_ne {s s' : ℝ × ℝ} (hP : L.piece s = L.piece s')
    (hne : L.tile s ≠ L.tile s') : ∃ k w, L.piece s = .belt k w := by
  unfold tile at hne
  rw [← hP] at hne
  rcases h : L.piece s with _ | _ | ⟨k, j⟩ | ⟨k, w⟩
  · simp [h] at hne
  · simp [h] at hne
  · simp [h] at hne
  · exact ⟨k, w, rfl⟩

/-! ## D11.18 The cell of a belt piece seen from a grid point -/

/-- A point `P` of the mesh `2^p` near a point of the belt cell `w` of layer `k`
(`2^{p+1} ≤ t_k`) lies in the closed cell: `P = c_w + (A, B) 2^p` with `|A|, |B| ≤ H`,
`t_k/2 = H 2^p`. -/
lemma near_centre {P : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ P = n₀ * 2 ^ p)
    (h₁ : f₁ P = n₁ * 2 ^ p) {s : ℝ × ℝ} (hds : dist s P < 2 ^ p / 2) {k : ℕ}
    {w : Fin 2 → ℤ} (hps : L.piece s = .belt k w) (hpk : p + 1 ≤ ⌊ζ * k⌋₊) :
    ∃ A B H : ℤ, 0 < H ∧ f₀ P = (2 * w 0 + 1) * hs k + A * 2 ^ p ∧
      f₁ P = (2 * w 1 + 1) * hs k + B * 2 ^ p ∧ hs k = H * 2 ^ p ∧
      -H ≤ A ∧ A ≤ H ∧ -H ≤ B ∧ B ≤ H := by
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  have hH : hs k = ((2 ^ (⌊ζ * k⌋₊ - 1 - p) : ℤ) : ℝ) * 2 ^ p := by
    rw [hs]; push_cast; rw [← pow_add]; congr 1; omega
  set H : ℤ := 2 ^ (⌊ζ * k⌋₊ - 1 - p)
  have hH0 : 0 < H := by positivity
  obtain ⟨a₀, b₀, a₁, b₁⟩ := fine_bounds (piece_belt hps).2.2.2.1 hq
  obtain ⟨d₀, d₁⟩ := abs_sub_le_dist s P
  rw [h₀] at d₀
  rw [h₁] at d₁
  obtain ⟨m₀, m₀'⟩ := mesh_mem hu (F := f₀ s) (a := 2 * w 0 * H) (b := (2 * w 0 + 2) * H)
    (n := n₀)
    (by push_cast; linarith [show (2 * (w 0 : ℝ) * H) * 2 ^ p = 2 * w 0 * hs k by rw [hH]; ring])
    (by push_cast
        linarith [show (2 * (w 0 : ℝ) + 2) * H * 2 ^ p = (2 * w 0 + 2) * hs k by rw [hH]; ring])
    (by linarith)
  obtain ⟨m₁, m₁'⟩ := mesh_mem hu (F := f₁ s) (a := 2 * w 1 * H) (b := (2 * w 1 + 2) * H)
    (n := n₁)
    (by push_cast; linarith [show (2 * (w 1 : ℝ) * H) * 2 ^ p = 2 * w 1 * hs k by rw [hH]; ring])
    (by push_cast
        linarith [show (2 * (w 1 : ℝ) + 2) * H * 2 ^ p = (2 * w 1 + 2) * hs k by rw [hH]; ring])
    (by linarith)
  refine ⟨n₀ - (2 * w 0 + 1) * H, n₁ - (2 * w 1 + 1) * H, H, hH0, ?_, ?_, hH, ?_, ?_, ?_, ?_⟩
  · rw [h₀, hH]; push_cast; ring
  · rw [h₁, hH]; push_cast; ring
  all_goals linarith

/-- All points near an interior grid point of a belt cell lie in its piece. -/
lemma piece_near {P : ℝ × ℝ} {p k : ℕ} {w : Fin 2 → ℤ} {s : ℝ × ℝ}
    (hps : L.piece s = .belt k w) (hq : 1 ≤ ⌊ζ * k⌋₊) {A B H : ℤ}
    (hA : f₀ P = (2 * w 0 + 1) * hs k + A * 2 ^ p) (hB : f₁ P = (2 * w 1 + 1) * hs k + B * 2 ^ p)
    (hH : hs k = H * 2 ^ p) (hint : -(H - 1) ≤ A ∧ A ≤ H - 1 ∧ -(H - 1) ≤ B ∧ B ≤ H - 1) :
    ∀ y, dist y P < 2 ^ p / 2 → L.piece y = .belt k w := by
  intro y hy
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  obtain ⟨d₀, d₁⟩ := abs_sub_le_dist y P
  rw [abs_le] at d₀ d₁
  obtain ⟨i₁, i₂, i₃, i₄⟩ := hint
  have c₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₁ : ((-(H - 1) : ℤ) : ℝ) ≤ A) hu.le
  have c₂ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₂ : (A : ℝ) ≤ ((H - 1 : ℤ) : ℝ)) hu.le
  have c₃ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₃ : ((-(H - 1) : ℤ) : ℝ) ≤ B) hu.le
  have c₄ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₄ : (B : ℝ) ≤ ((H - 1 : ℤ) : ℝ)) hu.le
  push_cast at c₁ c₂ c₃ c₄
  refine piece_of_fineIdx hps (fineIdx_eq_of_bounds hq ?_ ?_ ?_ ?_) <;> linarith

lemma eq_markPos {k : ℕ} (hq : 1 ≤ ⌊ζ * k⌋₊) {w : Fin 2 → ℤ} {P : ℝ × ℝ} {e : Fin 3 × Fin 3}
    (h₀ : f₀ P = (2 * w 0 + (e.1 : ℕ)) * hs k) (h₁ : f₁ P = (2 * w 1 + (e.2 : ℕ)) * hs k) :
    markPos k w e = P := by
  obtain ⟨g₀, g₁⟩ := f_markPos k w e
  have e₂ := two_pow_eq hq
  have e₁ : (2 : ℝ) ^ (⌊ζ * k⌋₊ - 1) = hs k := rfl
  simp only [markInt] at g₀ g₁
  push_cast at g₀ g₁
  rw [e₂, e₁] at g₀ g₁
  refine Prod.ext ?_ ?_
  · have : f₀ (markPos k w e) = f₀ P := by rw [g₀, h₀]; ring
    simpa [f₀] using this
  · have : f₁ (markPos k w e) = f₁ P := by rw [g₁, h₁]; ring
    simpa [f₁] using this

/-- A grid point of a closed belt cell at the centre, a corner or a side midpoint is a mark. -/
lemma mem_marks_of {P : ℝ × ℝ} {p k : ℕ} {w : Fin 2 → ℤ} {s : ℝ × ℝ}
    (hps : L.piece s = .belt k w) (hq : 1 ≤ ⌊ζ * k⌋₊) {A B H : ℤ}
    (hA : f₀ P = (2 * w 0 + 1) * hs k + A * 2 ^ p) (hB : f₁ P = (2 * w 1 + 1) * hs k + B * 2 ^ p)
    (hH : hs k = H * 2 ^ p) (hA' : A = -H ∨ A = 0 ∨ A = H) (hB' : B = -H ∨ B = 0 ∨ B = H) :
    P ∈ L.marks := by
  have pick (X : ℤ) (hX : X = -H ∨ X = 0 ∨ X = H) :
      ∃ e : Fin 3, (X : ℝ) * 2 ^ p = ((e : ℕ) - 1 : ℝ) * hs k := by
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by rw [hH]; norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by rw [hH]; norm_num⟩
  obtain ⟨e₁, he₁⟩ := pick A hA'
  obtain ⟨e₂, he₂⟩ := pick B hB'
  have hP : markPos k w (e₁, e₂) = P :=
    eq_markPos hq (by rw [hA, he₁]; ring) (by rw [hB, he₂]; ring)
  rw [← hP]
  exact mem_marks.2 ⟨k, (piece_belt hps).2.1, (piece_belt hps).2.2.1, w,
    mem_beltIndex_of_piece hps, (e₁, e₂), rfl⟩

/-- D11.18.3. Two points near a grid point `P`, in one belt piece with distinct identifiers:
`P` lies on one of the four lines of the fan through the centre, hence is a mark of the cell,
or the whole neighbourhood of `P` lies in the cell. -/
theorem mark_or_cell {P : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ P = n₀ * 2 ^ p)
    (h₁ : f₁ P = n₁ * 2 ^ p) {s s' : ℝ × ℝ} (hds : dist s P < 2 ^ p / 2)
    (hds' : dist s' P < 2 ^ p / 2) {k : ℕ} {w : Fin 2 → ℤ} (hps : L.piece s = .belt k w)
    (hps' : L.piece s' = .belt k w) (hpk : p + 1 ≤ ⌊ζ * k⌋₊) (hne : L.tile s ≠ L.tile s') :
    P ∈ L.marks ∨ ∀ y, dist y P < 2 ^ p / 2 → L.piece y = .belt k w := by
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  obtain ⟨A, B, H, hH0, hA, hB, hH, a₁, a₂, b₁, b₂⟩ := near_centre h₀ h₁ hds hps hpk
  by_cases hint : -(H - 1) ≤ A ∧ A ≤ H - 1 ∧ -(H - 1) ≤ B ∧ B ≤ H - 1
  · exact Or.inr (piece_near hps hq hA hB hH hint)
  left
  have hline : A = 0 ∨ B = 0 ∨ A + B = 0 ∨ A = B := by
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨c₀, c₁, c₂, c₃⟩ := hc
    obtain ⟨d₀, d₁⟩ := abs_sub_le_dist s P
    obtain ⟨d₀', d₁'⟩ := abs_sub_le_dist s' P
    have dp (z : ℝ × ℝ) (hz : dist z P < 2 ^ p / 2) : |fp z - fp P| < 2 ^ p := by
      obtain ⟨e₀, e₁⟩ := abs_sub_le_dist z P
      rw [show fp z - fp P = (f₀ z - f₀ P) + (f₁ z - f₁ P) by unfold fp; ring]
      linarith [abs_add_le (f₀ z - f₀ P) (f₁ z - f₁ P)]
    have dm (z : ℝ × ℝ) (hz : dist z P < 2 ^ p / 2) : |fm z - fm P| < 2 ^ p := by
      obtain ⟨e₀, e₁⟩ := abs_sub_le_dist z P
      rw [show fm z - fm P = (f₀ z - f₀ P) - (f₁ z - f₁ P) by unfold fm; ring]
      linarith [abs_sub (f₀ z - f₀ P) (f₁ z - f₁ P)]
    have tp : Ap k w s ↔ Ap k w s' :=
      test_iff (F₀ := fp P) hu (a := 2 * (w 0 + w 1 + 1) * H)
        (b := 2 * (w 0 + w 1 + 1) * H + A + B)
        (by rw [hH]; push_cast; ring) (by unfold fp; rw [hA, hB, hH]; push_cast; ring)
        (fun e ↦ c₂ (by linarith)) (dp s hds) (dp s' hds')
    have tm : Am k w s ↔ Am k w s' :=
      test_iff (F₀ := fm P) hu (a := 2 * (w 0 - w 1) * H) (b := 2 * (w 0 - w 1) * H + A - B)
        (by rw [hH]; push_cast; ring) (by unfold fm; rw [hA, hB, hH]; push_cast; ring)
        (fun e ↦ c₃ (by linarith)) (dm s hds) (dm s' hds')
    have t₀ : A0 k w s ↔ A0 k w s' :=
      test_iff (F₀ := f₀ P) hu (a := (2 * w 0 + 1) * H) (b := (2 * w 0 + 1) * H + A)
        (by rw [hH]; push_cast; ring) (by rw [hA, hH]; push_cast; ring)
        (fun e ↦ c₀ (by linarith)) (by linarith) (by linarith)
    have t₁ : A1 k w s ↔ A1 k w s' :=
      test_iff (F₀ := f₁ P) hu (a := (2 * w 1 + 1) * H) (b := (2 * w 1 + 1) * H + B)
        (by rw [hH]; push_cast; ring) (by rw [hB, hH]; push_cast; ring)
        (fun e ↦ c₁ (by linarith)) (by linarith) (by linarith)
    apply hne
    simp only [tile, hps, hps', tri_eq_of_iff tp tm t₀ t₁]
  exact mem_marks_of hps hq hA hB hH (by omega) (by omega)

lemma piece_smp {P : ℝ × ℝ} {p k : ℕ} {w : Fin 2 → ℤ} {s : ℝ × ℝ}
    (hps : L.piece s = .belt k w) (hq : 1 ≤ ⌊ζ * k⌋₊) (r : Fin 8)
    (h : 2 * w 0 * hs k ≤ f₀ P + 2 ^ p / 16 * (octDir r).1 ∧
      f₀ P + 2 ^ p / 16 * (octDir r).1 < (2 * w 0 + 2) * hs k ∧
      2 * w 1 * hs k ≤ f₁ P + 2 ^ p / 16 * (octDir r).2 ∧
      f₁ P + 2 ^ p / 16 * (octDir r).2 < (2 * w 1 + 2) * hs k) :
    L.piece (smp P p r) = .belt k w := by
  obtain ⟨h₀, h₀', h₁, h₁'⟩ := h
  exact piece_of_fineIdx hps (fineIdx_eq_of_bounds hq (by rwa [smp, f₀_add])
    (by rwa [smp, f₀_add]) (by rwa [smp, f₁_add]) (by rwa [smp, f₁_add]))

end Layout

/-! ## D11.18 Labels around a grid point -/

lemma cyc {α : Type*} (ℓ : α → Fin 2) {A B C D : α} (h₂ : B ≠ C → ℓ B ≠ ℓ C)
    (h₃ : C ≠ D → ℓ C ≠ ℓ D) (h₄ : D ≠ A → ℓ D ≠ ℓ A) (hAB : A = B) {x y : α}
    (hx : x = A ∨ x = B ∨ x = C ∨ x = D) (hy : y = A ∨ y = B ∨ y = C ∨ y = D)
    (hl : ℓ x = ℓ y) : x = y := by
  subst hAB
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (by_contra hne
       first
       | exact h₂ hne hl
       | exact h₂ (Ne.symm hne) hl.symm
       | exact h₃ hne hl
       | exact h₃ (Ne.symm hne) hl.symm
       | exact h₄ hne hl
       | exact h₄ (Ne.symm hne) hl.symm)

/-- D11.18.3. Around a point, with labels alternating across every active ray, two distinct
identifiers of the same label need an active diagonal ray or all four axis rays active. -/
lemma comb {α : Type*} (g : Fin 8 → α) (ℓ : α → Fin 2)
    (halt : ∀ r, g r ≠ g (r + 1) → ℓ (g r) ≠ ℓ (g (r + 1))) {a b : Fin 8} (hab : g a ≠ g b)
    (hl : ℓ (g a) = ℓ (g b)) :
    g 0 ≠ g 1 ∨ g 2 ≠ g 3 ∨ g 4 ≠ g 5 ∨ g 6 ≠ g 7 ∨
      (g 1 ≠ g 2 ∧ g 3 ≠ g 4 ∧ g 5 ≠ g 6 ∧ g 7 ≠ g 0) := by
  by_contra h
  simp only [not_or, not_and, not_not, ne_eq] at h
  obtain ⟨e₀, e₂, e₄, e₆, h⟩ := h
  have h1 : g 1 ≠ g 2 → ℓ (g 1) ≠ ℓ (g 2) := halt 1
  have h3 : g 3 ≠ g 4 → ℓ (g 3) ≠ ℓ (g 4) := halt 3
  have h5 : g 5 ≠ g 6 → ℓ (g 5) ≠ ℓ (g 6) := halt 5
  have h7 : g 7 ≠ g 0 → ℓ (g 7) ≠ ℓ (g 0) := halt 7
  rw [← e₀] at h1 h
  rw [← e₂] at h3 h
  rw [← e₄] at h5 h
  rw [← e₆] at h7 h
  have mem (r : Fin 8) : g r = g 0 ∨ g r = g 2 ∨ g r = g 4 ∨ g r = g 6 := by
    fin_cases r <;> simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, ← e₀, ← e₂, ← e₄,
      ← e₆, true_or, or_true]
  have rot (x : α) (hx : x = g 0 ∨ x = g 2 ∨ x = g 4 ∨ x = g 6) :
      (x = g 2 ∨ x = g 4 ∨ x = g 6 ∨ x = g 0) ∧ (x = g 4 ∨ x = g 6 ∨ x = g 0 ∨ x = g 2) ∧
        (x = g 6 ∨ x = g 0 ∨ x = g 2 ∨ x = g 4) := by
    rcases hx with hx | hx | hx | hx <;> simp [hx]
  by_cases c₁ : g 0 = g 2
  · exact hab (cyc ℓ h3 h5 h7 c₁ (mem a) (mem b) hl)
  by_cases c₂ : g 2 = g 4
  · exact hab (cyc ℓ h5 h7 h1 c₂ (rot _ (mem a)).1 (rot _ (mem b)).1 hl)
  by_cases c₃ : g 4 = g 6
  · exact hab (cyc ℓ h7 h1 h3 c₃ (rot _ (mem a)).2.1 (rot _ (mem b)).2.1 hl)
  · exact hab (cyc ℓ h1 h3 h5 (h c₁ c₂ c₃) (rot _ (mem a)).2.2 (rot _ (mem b)).2.2 hl)

namespace Layout

variable {L : Layout}

/-- D11.18.3. Contacts. Two distinct identifiers of the same label in octants about a point `P`
of the mesh `2^p`, one of them a belt tile: `P` is a mark. -/
theorem mem_marks_of_contact {P : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ P = n₀ * 2 ^ p)
    (h₁ : f₁ P = n₁ * 2 ^ p) (hlay : ∀ y, dist y P < 2 ^ p / 2 → p + 1 ≤ ⌊ζ * L.lay y⌋₊)
    {k : ℕ} {w : Fin 2 → ℤ} {c : Fin 2} {a b : Fin 8}
    (ha : L.tile (smp P p a) = .belt k w c) (hb : L.tile (smp P p b) ≠ .belt k w c)
    (hl : L.label (L.tile (smp P p b)) = c) : P ∈ L.marks := by
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  have hd (r : Fin 8) : dist (smp P p r) P < 2 ^ p / 2 := by rw [dist_smp]; linarith
  -- an identifier of label `c` in the cell of the belt tile is the belt tile itself
  have hcell (k' : ℕ) (w' : Fin 2 → ℤ)
      (hall : ∀ y, dist y P < 2 ^ p / 2 → L.piece y = .belt k' w') : False := by
    obtain ⟨hpa, -⟩ := tile_eq_belt_iff.1 ha
    rw [hall _ (hd a)] at hpa
    cases hpa
    have hpb := hall _ (hd b)
    apply hb
    rw [tile_eq_belt_iff]
    refine ⟨hpb, ?_⟩
    rw [← hl]
    simp only [tile, hpb, label]
  have ipc (r r' : Fin 8) (hP : L.piece (smp P p r) = L.piece (smp P p r'))
      (hne : L.tile (smp P p r) ≠ L.tile (smp P p r')) : P ∈ L.marks := by
    obtain ⟨k', w', hk'⟩ := exists_belt_of_tile_ne hP hne
    have hpk : p + 1 ≤ ⌊ζ * k'⌋₊ := by
      have := hlay _ (hd r); rwa [(belt_lay hk').1] at this
    rcases mark_or_cell h₀ h₁ (hd r) (hd r') hk' (hP.symm.trans hk') hpk hne with hm | hall
    · exact hm
    · exact (hcell k' w' hall).elim
  have hdiag (r : Fin 8) (hr : r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6)
      (hne : L.tile (smp P p r) ≠ L.tile (smp P p (r + 1))) : P ∈ L.marks :=
    ipc r (r + 1) (piece_eq_of_axSim (axSim_smp h₀ h₁ hr) (by have := hlay _ (hd r); omega)) hne
  have hab : L.tile (smp P p a) ≠ L.tile (smp P p b) := fun e ↦ hb (e ▸ ha)
  have hlab : L.label (L.tile (smp P p a)) = L.label (L.tile (smp P p b)) := by
    rw [hl, ha]; rfl
  rcases comb (fun r ↦ L.tile (smp P p r)) L.label (label_ne_smp h₀ h₁ hlay) hab hlab with
    h | h | h | h | ⟨g₁, g₃, g₅, g₇⟩
  · exact hdiag 0 (Or.inl rfl) h
  · exact hdiag 2 (Or.inr (Or.inl rfl)) h
  · exact hdiag 4 (Or.inr (Or.inr (Or.inl rfl))) h
  · exact hdiag 6 (Or.inr (Or.inr (Or.inr rfl))) h
  -- all four axis rays are active: `P` is in the closed cell of the belt tile
  obtain ⟨hpa, -⟩ := tile_eq_belt_iff.1 ha
  have hpk : p + 1 ≤ ⌊ζ * k⌋₊ := by have := hlay _ (hd a); rwa [(belt_lay hpa).1] at this
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by omega
  obtain ⟨A, B, H, hH0, hA, hB, hH, a₁, a₂, b₁, b₂⟩ := near_centre h₀ h₁ (hd a) hpa hpk
  by_cases hint : -(H - 1) ≤ A ∧ A ≤ H - 1 ∧ -(H - 1) ≤ B ∧ B ≤ H - 1
  · exact (hcell k w (piece_near hpa hq hA hB hH hint)).elim
  by_cases hcorner : (A = -H ∨ A = H) ∧ (B = -H ∨ B = H)
  · exact mem_marks_of hpa hq hA hB hH (by omega) (by omega)
  -- on a side of the cell the two octants across the inward axis ray lie in the cell
  have hH1 := mul_le_mul_of_nonneg_right (by exact_mod_cast hH0 : (1 : ℝ) ≤ H) hu.le
  rcases (by omega : (A = H ∧ -(H - 1) ≤ B ∧ B ≤ H - 1) ∨ (A = -H ∧ -(H - 1) ≤ B ∧ B ≤ H - 1) ∨
      (B = H ∧ -(H - 1) ≤ A ∧ A ≤ H - 1) ∨ (B = -H ∧ -(H - 1) ≤ A ∧ A ≤ H - 1)) with
    ⟨e, i₁, i₂⟩ | ⟨e, i₁, i₂⟩ | ⟨e, i₁, i₂⟩ | ⟨e, i₁, i₂⟩
  · have eA : (A : ℝ) * 2 ^ p = hs k := by rw [e, hH]
    have c₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₁ : ((-(H - 1) : ℤ) : ℝ) ≤ B) hu.le
    have c₂ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₂ : (B : ℝ) ≤ ((H - 1 : ℤ) : ℝ)) hu.le
    push_cast at c₁ c₂
    exact ipc 3 4
      ((piece_smp (P := P) (p := p) hpa hq 3 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).trans
        (piece_smp (P := P) (p := p) hpa hq 4 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).symm) g₃
  · have eA : (A : ℝ) * 2 ^ p = -hs k := by rw [e, hH]; push_cast; ring
    have c₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₁ : ((-(H - 1) : ℤ) : ℝ) ≤ B) hu.le
    have c₂ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₂ : (B : ℝ) ≤ ((H - 1 : ℤ) : ℝ)) hu.le
    push_cast at c₁ c₂
    exact ipc 7 0
      ((piece_smp (P := P) (p := p) hpa hq 7 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).trans
        (piece_smp (P := P) (p := p) hpa hq 0 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).symm) g₇
  · have eB : (B : ℝ) * 2 ^ p = hs k := by rw [e, hH]
    have c₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₁ : ((-(H - 1) : ℤ) : ℝ) ≤ A) hu.le
    have c₂ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₂ : (A : ℝ) ≤ ((H - 1 : ℤ) : ℝ)) hu.le
    push_cast at c₁ c₂
    exact ipc 5 6
      ((piece_smp (P := P) (p := p) hpa hq 5 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).trans
        (piece_smp (P := P) (p := p) hpa hq 6 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).symm) g₅
  · have eB : (B : ℝ) * 2 ^ p = -hs k := by rw [e, hH]; push_cast; ring
    have c₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₁ : ((-(H - 1) : ℤ) : ℝ) ≤ A) hu.le
    have c₂ := mul_le_mul_of_nonneg_right (by exact_mod_cast i₂ : (A : ℝ) ≤ ((H - 1 : ℤ) : ℝ)) hu.le
    push_cast at c₁ c₂
    exact ipc 1 2
      ((piece_smp (P := P) (p := p) hpa hq 1 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).trans
        (piece_smp (P := P) (p := p) hpa hq 2 (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [octDir, Fin.isValue, Matrix.cons_val] <;>
            linarith)).symm) g₁

/-! ## D11.18 Lemma 11.5 -/

lemma ρ₀_le_one : ρ₀ ≤ 1 := by norm_num [ρ₀, β]

/-- D11.18 **Lemma 11.5**, belt half (`geometry:birth-separation`). The closed birth region of
the initial belt tile `(k, w, c)`, of side scale `u = t_k`, is at sup-distance `≥ u^{ρ₀}/128`
from the final actual region of every other initial identifier of label `c`.
2D only: angular gap `π/4` across the eight rays at a planar point contact. -/
theorem step_11_18_belt {k : ℕ} {w : Fin 2 → ℤ} {c : Fin 2} {b : InitId}
    (hb : b ≠ .belt k w c) (hl : L.label b = c) {x y : ℝ × ℝ}
    (hx : x ∈ L.repair.birthRegion (.init (.belt k w c)))
    (hy : y ∈ L.repair.finalRegion (.init b)) : (t k : ℝ) ^ ρ₀ / 128 ≤ dist x y := by
  have hu1 : (1 : ℝ) ≤ t k := by rw [t_eq]; exact one_le_pow₀ (by norm_num)
  have hρu : (t k : ℝ) ^ ρ₀ ≤ t k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hu1 ρ₀_le_one
  have hρ0 : 0 ≤ (t k : ℝ) ^ ρ₀ := by positivity
  -- D11.18.7: pairs at distance `≥ u/128`
  by_cases hfar : (t k : ℝ) / 128 ≤ dist x y
  · linarith
  push Not at hfar
  -- D11.18.1: points of the two tiles next to `x` and `y`
  have hx' : x ∈ closure (interior {z | L.tile z = .belt k w c}) := hx
  have hy' : y ∈ closure (interior {z | L.tile z = b}) :=
    L.repair.finalRegion_subset_birthRegion _ hy
  obtain ⟨X, hX, hxX⟩ := Metric.mem_closure_iff.1 hx' ((t k : ℝ) / 128) (by positivity)
  obtain ⟨Y, hY, hyY⟩ := Metric.mem_closure_iff.1 hy' ((t k : ℝ) / 128) (by positivity)
  have hXt : L.tile X = .belt k w c := interior_subset (s := {z | L.tile z = .belt k w c}) hX
  have hYt : L.tile Y = b := interior_subset (s := {z | L.tile z = b}) hY
  obtain ⟨hpX, -⟩ := tile_eq_belt_iff.1 hXt
  obtain ⟨-, hD, hk, hK⟩ := belt_lay hpX
  obtain ⟨p, hp⟩ : ∃ p, ⌊ζ * k⌋₊ = p + 2 :=
    ⟨_, (Nat.sub_add_cancel (L.two_le_floor hk)).symm⟩
  have hu : (t k : ℝ) = 4 * 2 ^ p := by rw [t_eq, hp, pow_add]; ring
  have hv : (0 : ℝ) < 2 ^ p := by positivity
  -- D11.18.2: around the belt cell all meshes are `≥ t_k/2`
  have hlayX (z : ℝ × ℝ) (hz : dist X z < 4 * 2 ^ p) : p + 1 ≤ ⌊ζ * L.lay z⌋₊ := by
    have := lay_near hD hk hK (x' := z)
      (by rw [hp, pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num]; linarith)
    omega
  have hXY : dist X Y < 3 * 2 ^ p / 32 := by
    have := dist_triangle4 X x y Y
    rw [dist_comm X x] at this
    linarith
  -- D11.18.3: no positive-length interface between the two tiles
  have hne : L.tile X ≠ L.tile Y := by rw [hXt, hYt]; exact Ne.symm hb
  have hlab : L.label (L.tile X) = L.label (L.tile Y) := by rw [hXt, hYt, hl]; rfl
  have lX := hlayX X (by rw [dist_self]; positivity)
  have lY := hlayX Y (by linarith)
  have hc : ¬ (CrossX p X Y ∨ CrossX p Y X ∨ CrossY p X Y ∨ CrossY p Y X ∨ AxSim p X Y) := by
    rintro (h | h | h | h | h)
    · exact step_11_11 (Or.inl h) lX lY hne hlab
    · exact step_11_11 (Or.inl h) lY lX hne.symm hlab.symm
    · exact step_11_11 (Or.inr (Or.inl h)) lX lY hne hlab
    · exact step_11_11 (Or.inr (Or.inl h)) lY lX hne.symm hlab.symm
    · exact step_11_11 (Or.inr (Or.inr h)) lX lY hne hlab
  obtain ⟨P, ⟨n₀, n₁, h₀, h₁⟩, hXP⟩ := exists_mesh_near (by linarith) hc
  have hlay (z : ℝ × ℝ) (hz : dist z P < 2 ^ p / 2) : p + 1 ≤ ⌊ζ * L.lay z⌋₊ :=
    hlayX z (by linarith [dist_triangle X P z, dist_comm P z])
  -- D11.18.5: the star about the grid point `P`
  have hρ : (3 * 2 ^ p / 8 : ℝ) < 2 ^ p / 2 := by linarith
  have hxP : dist x P ≤ 3 * 2 ^ p / 8 := by linarith [dist_triangle x X P]
  have hyP : dist y P ≤ 3 * 2 ^ p / 8 := by
    linarith [dist_triangle y x P, dist_comm x y, dist_triangle x X P]
  have hF (r : Fin 8) (z : ℝ × ℝ) (hz : z - P ∈ openCone r) (hzd : dist z P < 2 ^ p / 2) :
      L.tile z = L.tile (smp P p r) := tile_eq_smp h₀ h₁ hlay hz hzd
  have hxs : x ∈ closure (interior {z | L.tile z = .belt k w c}) ∩
      closedBall P (3 * 2 ^ p / 8) := ⟨hx', mem_closedBall.2 hxP⟩
  have hys : y ∈ closure (interior {z | L.tile z = b}) ∩ closedBall P (3 * 2 ^ p / 8) :=
    ⟨hy', mem_closedBall.2 hyP⟩
  rw [star_of_const L.tile P hρ (fun r ↦ L.tile (smp P p r)) hF] at hxs hys
  simp only [mem_iUnion] at hxs hys
  obtain ⟨rx, hrx, hxr, -⟩ := hxs
  obtain ⟨ry, hry, hyr, -⟩ := hys
  -- D11.18.3: the contact point is a mark
  have hPm : P ∈ L.marks :=
    mem_marks_of_contact h₀ h₁ hlay hrx (by rw [hry]; exact hb) (by rw [hry]; exact hl)
  -- D11.18.5: the angular gap
  have halt := label_ne_smp h₀ h₁ hlay
  have hcx : L.label (L.tile (smp P p rx)) = c := by rw [hrx]; rfl
  have hcy : L.label (L.tile (smp P p ry)) = c := by rw [hry]; exact hl
  have hjk : ry ≠ rx := by rintro rfl; exact hb (hry.symm.trans hrx)
  have hj : ry ≠ rx + 1 := by
    rintro rfl
    exact halt rx (by rw [hrx, hry]; exact Ne.symm hb) (hcx.trans hcy.symm)
  have hk' : rx ≠ ry + 1 := by
    rintro rfl
    exact halt ry (by rw [hrx, hry]; exact hb) (hcy.trans hcx.symm)
  have hgap := max_dist_le_two_mul_dist_of_not_adjacent hjk hj hk' hxr hyr
  -- D11.18.6: the trim at the mark removes the open square of radius `d(S_v)`
  have htrim : d (L.markScale ⟨P, hPm⟩) ≤ dist y P :=
    L.repair.le_dist_of_mem_finalRegion (m := ⟨⟨P, hPm⟩, []⟩) (Or.inl rfl) (Nat.zero_le _) hy
  have hml : k ≤ L.markLayer ⟨P, hPm⟩ + 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, -, -, hDv, -, -, -⟩ := L.mark_facts ⟨P, hPm⟩
    have h7 := step_11_7 (by omega : L.markLayer ⟨P, hPm⟩ + 2 ≤ k) hDv hD
    rw [dist_pt] at h7
    have h7' : ((L.C₀ : ℝ) - 1) / 2 * 2 ^ k ≤ dist P X := h7.2.trans h7.1
    have hC : (2 : ℝ) ≤ L.C₀ := by exact_mod_cast L.two_le_C₀
    have htk : (t k : ℝ) ≤ 2 ^ k := (scale_facts k).2.2.2.1
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ (L.C₀ - 1) / 2 by linarith)
      (pow_pos (two_pos : (0 : ℝ) < 2) k).le
    linarith [dist_comm P X]
  have hS : (t k : ℝ) / 2 ≤ L.markScale ⟨P, hPm⟩ := by
    have := floor_zeta_le k
    have h1 : (t (k - 1) : ℝ) ≤ L.markScale ⟨P, hPm⟩ := t_le_t (by omega)
    have h2 := floor_zeta_succ (k - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h2
    have h3 : (t k : ℝ) ≤ 2 * t (k - 1) := by
      rw [t_eq, t_eq]
      calc (2 : ℝ) ^ ⌊ζ * k⌋₊ ≤ 2 ^ (⌊ζ * ↑(k - 1)⌋₊ + 1) := pow_le_pow_right₀ (by norm_num) h2
        _ = 2 * 2 ^ ⌊ζ * ↑(k - 1)⌋₊ := by ring
    linarith
  -- D11.18.7: combine
  have hS0 : 0 < L.markScale ⟨P, hPm⟩ := by linarith
  have hd1 := (step_11_14_1 hS0).1
  have hpow : ((t k : ℝ) / 2) ^ ρ₀ ≤ L.markScale ⟨P, hPm⟩ ^ ρ₀ :=
    Real.rpow_le_rpow (by positivity) hS ρ₀_pos.le
  have hhalf : (t k : ℝ) ^ ρ₀ / 2 ≤ ((t k : ℝ) / 2) ^ ρ₀ := by
    rw [Real.div_rpow (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ ρ₀ ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ρ₀_le_one
    exact div_le_div_of_nonneg_left hρ0 (by positivity) this
  have := le_max_right (dist x P) (dist y P)
  linarith

/-- D11.18 **Lemma 11.5** (`geometry:birth-separation`). There is a fixed `c₁ > 0` such that:
let `𝓑` be the closed birth region of an initial belt tile of side scale `u = t_k`, or of a
replacement tile whose removal square has halfside `u`. Then `dist_∞` from `𝓑` to the final
actual region of every earlier or peer identifier of the same label is `≥ c₁ u^{ρ₀}`. Peer =
another initial belt tile, resp. another replacement born in the same generation.
2D only: angular gap `π/4` across the eight rays at a planar point contact. -/
theorem lemma_11_5 : ∃ c₁ : ℝ, 0 < c₁ ∧
    (∀ (k : ℕ) (w : Fin 2 → ℤ) (c : Fin 2) (b : InitId),
      L.rank (.init b) ≤ L.rank (.init (.belt k w c)) → b ≠ .belt k w c →
      L.repair.label (.init b) = L.repair.label (.init (.belt k w c)) →
      ∀ x ∈ L.repair.birthRegion (.init (.belt k w c)), ∀ y ∈ L.repair.finalRegion (.init b),
        c₁ * (t k : ℝ) ^ ρ₀ ≤ dist x y) ∧
    (∀ (m : Mark L.marks) (c a : TileId InitId L.marks), L.repair.IsMark m →
      L.repair.IsNonterminal m → L.rank a ≤ L.rank (.repl m c) → a ≠ .repl m c →
      L.repair.label a = L.repair.label (.repl m c) →
      ∀ x ∈ L.repair.birthRegion (.repl m c), ∀ y ∈ L.repair.finalRegion a,
        c₁ * d (L.repair.S m) ^ ρ₀ ≤ dist x y) := by
  refine ⟨1 / 128, by norm_num, fun k w c b _ hb hl x hx y hy ↦ ?_,
    fun m c a hm hnt hr ha hl x hx y hy ↦ ?_⟩
  · -- D11.18.1–7 for the belt tile
    have := step_11_18_belt hb hl hx hy
    linarith
  · -- D11.18 for the replacement: `d(d(S))/2 > d(S)^{ρ₀}/4`
    have h := L.lemma_11_3.1.step_11_18_replacement hm hnt ha hl (birthGen_le_of_rank_le hr)
      hx hy
    have h₂ := (step_11_14_1 (d_pos (L.repair.S m))).1
    have : 0 ≤ d (L.repair.S m) ^ ρ₀ := Real.rpow_nonneg (d_pos _).le _
    linarith

end Layout

end

end AreaLaw.Geometry
