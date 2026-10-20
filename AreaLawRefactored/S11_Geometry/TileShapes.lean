import AreaLawRefactored.S11_Geometry.InitialStars

/-! # Birth regions of the initial tiles

Birth region, actual region and template of a tile, and the explicit birth regions of the
initial tiles of `Layout.repair`: a belt tile is a union of octant triangles of the fan of its
cell, a primary has the lattice sites of the birth region of D11.10, the dummy tile lies in
`closure N_{k₀}` and the exterior tile outside `N_K`.

Digest `digest/11-geometry.md` D11.3, D11.11 -/

open Set Metric Filter Topology

namespace AreaLaw.Geometry

noncomputable section

/-! ## D11.3 Birth region, actual region, template -/

namespace Repair

variable {I M₀ : Type*} (R : Repair I M₀)

/-- D11.3. Birth region of a tile: bounded closed planar region assigned at creation. Later
steps only delete points. Actual region: interior of the birth region remaining after all
deletions. Pieces with one tile identifier form one region; neither birth nor actual region need
be connected. Ambient lattice template `T = birth region ∩ ℤ²`.
2D only: planar regions and their lattice sites in `ℤ²`. -/
def template (a : TileId I M₀) : Set (ℤ × ℤ) := latticePoint ⁻¹' R.birthRegion a

lemma finalRegion_subset_birthRegion (a : TileId I M₀) : R.finalRegion a ⊆ R.birthRegion a :=
  sdiff_subset

end Repair

/-! ## Cells of the initial configuration -/

namespace Layout

variable {L : Layout}

lemma lev_eq_of_mem_D {x : ℝ × ℝ} {k : ℕ} (h : pt x ∈ D o₂ L.Z L.C₀ k) : L.lev x = k + 1 := by
  have h₁ := mem_N_iff_lev.1 h.1
  have h₂ : ¬ L.lev x ≤ k := fun h' ↦ h.2 (mem_N_iff_lev.2 h')
  omega

lemma cell_subset_D {k : ℕ} {w : Fin 2 → ℤ} (hf : w ∈ fineIndex o₂ L.Z L.C₀ k) :
    cell o₂ ⌊ζ * k⌋₊ w ⊆ D o₂ L.Z L.C₀ k := by
  intro y hy
  rw [D_eq_iUnion]
  refine mem_iUnion₂.2 ⟨_, mem_fineIndex_iff.1 hf, ?_⟩
  rw [mem_cell_iff, cellIndex_eq_fine, mem_cell_iff.1 hy]

/-- Every point of a belt cell of `D_k`, `k₀ ≤ k < K`, lies in its belt piece. -/
lemma piece_of_mem_beltIndex {k : ℕ} {w : Fin 2 → ℤ} (hw : w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k))
    (hk : L.k₀ ≤ k) (hK : k < L.K) {x : ℝ × ℝ} (hx : fineIdx k x = w) :
    L.piece x = .belt k w := by
  obtain ⟨hf, hb⟩ := Finset.mem_filter.1 hw
  have hl : L.lev x = k + 1 := lev_eq_of_mem_D (cell_subset_D hf (mem_cell_iff.2 hx))
  simp only [piece, hl, show ¬ k + 1 ≤ L.k₀ by omega, show ¬ L.K < k + 1 by omega, if_false,
    Nat.add_sub_cancel, hx, hb, if_true]

lemma mem_beltIndex_of_piece {x : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} (h : L.piece x = .belt k w) :
    w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k) := by
  obtain ⟨hl, -, -, hw, hb⟩ := piece_belt h
  refine Finset.mem_filter.2 ⟨mem_fineIndex_iff.2 ?_, hb⟩
  have hD := mem_D_lev hl
  rw [D_eq_iUnion] at hD
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hD
  rw [mem_cell_iff, cellIndex_eq_fine] at hxz
  subst hw
  convert hz using 1
  rw [← hxz]; rfl

lemma tile_eq_belt_iff {x : ℝ × ℝ} {k : ℕ} {w : Fin 2 → ℤ} {c : Fin 2} :
    L.tile x = .belt k w c ↔ L.piece x = .belt k w ∧ L.lab k w (tri k w x) = c := by
  unfold tile
  rcases h : L.piece x with _ | _ | ⟨k', j⟩ | ⟨k', w'⟩
  · simp
  · simp
  · simp
  · constructor
    · intro he; cases he; exact ⟨rfl, rfl⟩
    · rintro ⟨he, rfl⟩; cases he; rfl

lemma piece_of_tile_dummy {x : ℝ × ℝ} (h : L.tile x = .dummy) : L.piece x = .dummy := by
  unfold tile at h
  rcases hp : L.piece x with _ | _ | ⟨k', j⟩ | ⟨k', w'⟩ <;> simp_all

lemma piece_of_tile_exterior {x : ℝ × ℝ} (h : L.tile x = .exterior) : L.piece x = .exterior := by
  unfold tile at h
  rcases hp : L.piece x with _ | _ | ⟨k', j⟩ | ⟨k', w'⟩ <;> simp_all

lemma piece_of_tile_primary {x : ℝ × ℝ} {k : ℕ} {j : Fin 2 → ℤ}
    (h : L.tile x = .primary k j) : L.piece x = .primary k j := by
  unfold tile at h
  rcases hp : L.piece x with _ | _ | ⟨k', j'⟩ | ⟨k', w'⟩ <;> simp_all

/-- A fine cell of layer `k` is the closed sup-ball of radius `t_k/2` about its centre. -/
lemma mem_closedBall_centre {k : ℕ} {w : Fin 2 → ℤ} {x : ℝ × ℝ} (hq : 1 ≤ ⌊ζ * k⌋₊)
    (hx : fineIdx k x = w) : x ∈ closedBall (centre k w) (hs k) := by
  obtain ⟨a₀, b₀, a₁, b₁⟩ := fine_bounds hx hq
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff, abs_le, abs_le]
  simp only [centre]
  unfold f₀ f₁ at *
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma fineIdx_of_dist_lt {k : ℕ} {w : Fin 2 → ℤ} {x : ℝ × ℝ} (hq : 1 ≤ ⌊ζ * k⌋₊)
    (hx : dist x (centre k w) < hs k) : fineIdx k x = w := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt] at hx
  simp only [centre] at hx
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hx
  refine fineIdx_eq_of_bounds hq ?_ ?_ ?_ ?_ <;> simp only [f₀, f₁] <;> linarith

lemma smul_mem_octantCone {c : ℝ} (hc : 0 ≤ c) {k : Fin 8} {p : ℝ × ℝ} (hp : p ∈ octantCone k) :
    c • p ∈ octantCone k := by
  fin_cases k <;>
    simp only [octantCone, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hp ⊢ <;>
    constructor <;> nlinarith [hp.1, hp.2]

/-- A closed octant triangle is the closure of the open octant inside the open ball. -/
lemma octantTriangle_subset_closure (v : ℝ × ℝ) {r : ℝ} (hr : 0 < r) (k : Fin 8) :
    octantTriangle v r k ⊆ closure ({y | y - v ∈ openCone k} ∩ ball v r) := by
  intro x ⟨hxk, hxr⟩
  have hxv : ‖x - v‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hxr
  rw [Metric.mem_closure_iff]
  intro ε hε
  set τ := min (1 / 2) (ε / (4 * r)) with hτ
  have hτ₀ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ₁ : τ ≤ 1 / 2 := min_le_left _ _
  have hτε : τ * (4 * r) ≤ ε := by
    have := min_le_right (1 / 2) (ε / (4 * r)); rw [← hτ] at this
    calc τ * (4 * r) ≤ ε / (4 * r) * (4 * r) := by gcongr
      _ = ε := by field_simp
  have hn : ‖(τ * (r / 4)) • octDir k‖ = τ * r / 2 := by
    rw [norm_smul, norm_octDir, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
  have hn' : ‖(1 - τ) • (x - v)‖ ≤ (1 - τ) * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]; gcongr; linarith
  refine ⟨v + ((1 - τ) • (x - v) + (τ * (r / 4)) • octDir k), ⟨?_, ?_⟩, ?_⟩
  · change v + _ - v ∈ openCone k
    rw [add_sub_cancel_left]
    exact add_mem_openCone (smul_mem_octantCone (by linarith) hxk)
      (smul_octDir_mem (by positivity) k)
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖(1 - τ) • (x - v) + (τ * (r / 4)) • octDir k‖
        ≤ ‖(1 - τ) • (x - v)‖ + ‖(τ * (r / 4)) • octDir k‖ := norm_add_le _ _
      _ < r := by rw [hn]; nlinarith
  · rw [dist_eq_norm]
    have : x - (v + ((1 - τ) • (x - v) + (τ * (r / 4)) • octDir k)) =
        τ • (x - v) - (τ * (r / 4)) • octDir k := by
      rw [sub_smul, one_smul]; abel
    rw [this]
    calc ‖τ • (x - v) - (τ * (r / 4)) • octDir k‖
        ≤ ‖τ • (x - v)‖ + ‖(τ * (r / 4)) • octDir k‖ := norm_sub_le _ _
      _ < ε := by
        rw [hn, norm_smul, Real.norm_eq_abs, abs_of_pos hτ₀]
        nlinarith [mul_le_mul_of_nonneg_left hxv hτ₀.le]

/-! ## D11.11 The initial birth regions -/

/-- D11.3, D11.11. The birth region of the belt tile `(k, w, c)` of a belt cell `w` of `D_k`,
`k₀ ≤ k < K`: the union of the octant triangles of the fan of `w` with label `c`, at most eight
triangles in the closed ball of radius `t_k/2` about the centre of `w`. -/
theorem birth₀_belt {k : ℕ} {w : Fin 2 → ℤ} (hw : w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k))
    (hk : L.k₀ ≤ k) (hK : k < L.K) (c : Fin 2) :
    L.repair.birth₀ (.belt k w c) =
      ⋃ (j : Fin 8) (_ : L.lab k w (triTable j) = c), octantTriangle (centre k w) (hs k) j := by
  have hq : 1 ≤ ⌊ζ * k⌋₊ := by have := L.two_le_floor hk; omega
  change closure (interior {x | L.tile x = .belt k w c}) = _
  have hU : IsClosed (⋃ (j : Fin 8) (_ : L.lab k w (triTable j) = c),
      octantTriangle (centre k w) (hs k) j) :=
    isClosed_iUnion_of_finite fun j ↦ isClosed_iUnion_of_finite fun _ ↦
      (isClosed_octantConeAt _ j).inter isClosed_closedBall
  refine Subset.antisymm (fun x hx ↦ ?_) (iUnion₂_subset fun j hj ↦ ?_)
  · rw [← hU.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (by positivity)
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
    obtain ⟨z, j, hz, hzy⟩ := exists_near_openCone (centre k w) y (lt_min hη (half_pos hε))
    have hzT : L.tile z = .belt k w c :=
      interior_subset (s := {x | L.tile x = .belt k w c})
        (hball (mem_ball.2 (hzy.trans_le (min_le_left _ _))))
    obtain ⟨hp, hl⟩ := tile_eq_belt_iff.1 hzT
    rw [step_11_11_2 hz] at hl
    refine ⟨z, mem_iUnion₂.2 ⟨j, hl, openCone_subset j hz,
      mem_closedBall_centre hq (piece_belt hp).2.2.2.1⟩, ?_⟩
    have := hzy.trans_le (min_le_right _ _)
    rw [dist_comm] at this
    linarith [dist_triangle x y z]
  · refine (octantTriangle_subset_closure _ (hs_pos k) j).trans (closure_mono ?_)
    refine interior_maximal (fun y ⟨hy, hd⟩ ↦ ?_)
      (((isOpen_openCone j).preimage (continuous_id.sub continuous_const)).inter isOpen_ball)
    have hp := piece_of_mem_beltIndex hw hk hK (fineIdx_of_dist_lt hq (mem_ball.1 hd))
    exact tile_eq_belt_iff.2 ⟨hp, by rw [step_11_11_2 hy, hj]⟩

/-- D11.3, D11.11. The birth region of a belt tile lies in the closed cell. -/
lemma birth₀_belt_subset {k : ℕ} {w : Fin 2 → ℤ} (hw : w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k))
    (hk : L.k₀ ≤ k) (hK : k < L.K) (c : Fin 2) :
    L.repair.birth₀ (.belt k w c) ⊆ closedBall (centre k w) (hs k) := by
  rw [birth₀_belt hw hk hK]
  exact iUnion₂_subset fun _ _ ↦ inter_subset_right

/-- D11.3, D11.11. The birth region of the dummy tile lies in `closure N_{k₀}`. -/
theorem birth₀_dummy_subset :
    L.repair.birth₀ .dummy ⊆ plane '' closure (N o₂ L.Z L.C₀ L.k₀) := by
  change closure (interior {x | L.tile x = .dummy}) ⊆ _
  have h := plane.toHomeomorph.image_closure (N o₂ L.Z L.C₀ L.k₀)
  rw [IsometryEquiv.coe_toHomeomorph] at h
  rw [h]
  refine closure_mono (interior_subset.trans fun x hx ↦ ⟨pt x, ?_, plane.apply_symm_apply x⟩)
  exact mem_N_iff_lev.2 (piece_dummy (piece_of_tile_dummy hx))

/-- D11.3, D11.11. The birth region of the exterior tile lies outside the interior of `N_K`. -/
theorem birth₀_exterior_subset :
    L.repair.birth₀ .exterior ⊆ (plane '' interior (N o₂ L.Z L.C₀ L.K))ᶜ := by
  change closure (interior {x | L.tile x = .exterior}) ⊆ _
  have hc : IsClosed (plane '' interior (N o₂ L.Z L.C₀ L.K))ᶜ := by
    refine IsOpen.isClosed_compl ?_
    rw [← IsometryEquiv.coe_toHomeomorph]
    exact plane.toHomeomorph.isOpenMap _ isOpen_interior
  refine closure_minimal (interior_subset.trans fun x hx ⟨y, hy, hyx⟩ ↦ ?_) hc
  subst hyx
  have h₁ := piece_exterior (piece_of_tile_exterior hx)
  have h₂ : pt (plane y) ∈ N o₂ L.Z L.C₀ L.K := by
    rw [show pt (plane y) = y from plane.symm_apply_apply y]; exact interior_subset hy
  exact absurd (mem_N_iff_lev.1 h₂) (by omega)

/-! ## D11.11 The lattice sites of a primary -/

lemma latticePoint_mem_birth₀ {z : ℤ × ℤ} {i : InitId} :
    latticePoint z ∈ L.repair.birth₀ i ↔ L.tile (latticePoint z) = i := by
  refine ⟨fun h ↦ (L.eq_of_mem_birth h).symm, fun h ↦ ?_⟩
  subst h
  exact subset_closure (mem_interior_iff_mem_nhds.2 (L.tile_nhds z))

/-- The coordinates of a lattice site, measured from `o`, are not integers. -/
lemma pt_latticePoint_ne (z : ℤ × ℤ) (i : Fin 2) (n : ℤ) : pt (latticePoint z) i - o₂ i ≠ n := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, pt (latticePoint z) i = m := by
    fin_cases i
    exacts [⟨z.1, rfl⟩, ⟨z.2, rfl⟩]
  rw [hm] at h
  exact (o₂_irrational.1 i).ne_int (m - n) (by push_cast; linarith)

lemma pitch_real {T y : ℝ} {w N M : ℤ} (hT : 0 < T) (h₁ : T * w ≤ y) (h₂ : y < T * (w + 1))
    (hy : ∀ n : ℤ, y ≠ T * n) :
    (T * N + T < y ∧ y < T * N + T * M) ↔ (N + 1 ≤ w ∧ w ≤ N + M - 1) := by
  constructor
  · rintro ⟨h₃, h₄⟩
    have e₁ : (N : ℝ) + 1 < w + 1 := by
      by_contra h; push Not at h; nlinarith [mul_le_mul_of_nonneg_left h hT.le]
    have e₂ : (w : ℝ) < N + M := by
      by_contra h; push Not at h; nlinarith [mul_le_mul_of_nonneg_left h hT.le]
    have e₁' : N + 1 < w + 1 := by exact_mod_cast e₁
    have e₂' : w < N + M := by exact_mod_cast e₂
    omega
  · rintro ⟨h₃, h₄⟩
    have e₁ : (N : ℝ) + 1 ≤ w := by exact_mod_cast h₃
    have e₂ : (w : ℝ) + 1 ≤ N + M := by exact_mod_cast (by omega : w + 1 ≤ N + M)
    refine ⟨lt_of_le_of_ne ?_ fun e ↦ hy (N + 1) (by push_cast; linarith), ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left e₁ hT.le]
    · nlinarith [mul_le_mul_of_nonneg_left e₂ hT.le]

lemma pitch_int {w a j m : ℤ} (hm : 0 < m) :
    (a + m * j + 1 ≤ w ∧ w ≤ a + m * j + m - 1) ↔ (¬ w ≡ a [ZMOD m] ∧ (w - a) / m = j) := by
  have hdiv : (w - a) / m = j ↔ m * j ≤ w - a ∧ w - a ≤ m * j + m - 1 := by
    rw [le_antisymm_iff, ← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hm,
      Int.le_ediv_iff_mul_le hm]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hdiv, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun ⟨c, hc⟩ ↦ ?_, by constructor <;> linarith⟩
    have h₃ : m * j < m * (-c) := by linarith
    have h₄ : m * (-c) < m * (j + 1) := by linarith
    have := lt_of_mul_lt_mul_left h₃ hm.le
    have := lt_of_mul_lt_mul_left h₄ hm.le
    omega
  · rintro ⟨hnd, h₁, h₂⟩
    refine ⟨?_, by linarith⟩
    by_contra h
    refine hnd ⟨-j, ?_⟩
    rw [mul_neg]
    generalize m * j = M at *
    omega

/-- D11.3, D11.10, D11.11. The template of the primary `(k, j)`, `k₀ ≤ k < K`: the lattice
sites of its birth region are those of the birth region of the primary `j` of layer `k`
(D11.10), as in `step_11_21`. -/
theorem template_primary {k : ℕ} (hk : L.k₀ ≤ k) (hK : k < L.K) (j : Fin 2 → ℤ) :
    L.repair.template (.init (.primary k j)) =
      latticePoint ⁻¹' (plane '' birthRegion o₂ L.Z L.C₀ k (L.a k) j) := by
  ext z
  change latticePoint z ∈ L.repair.birth₀ (.primary k j) ↔ _
  rw [latticePoint_mem_birth₀, mem_preimage, ← IsometryEquiv.preimage_symm, mem_preimage,
    birthRegion_eq]
  change _ ↔ pt (latticePoint z) ∈ closure (primary o₂ L.Z L.C₀ k (L.a k) j)
  set x := latticePoint z with hx
  -- a lattice site of `closure D_k` lies in `D_k`
  have hD : pt x ∈ closure (D o₂ L.Z L.C₀ k) → pt x ∈ D o₂ L.Z L.C₀ k := by
    rw [D_eq_iUnion, Finset.closure_biUnion]
    intro h
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 h
    refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
    rw [closure_cell, mem_univ_pi] at hxy
    intro i _
    obtain ⟨h₁, h₂⟩ := hxy i
    refine ⟨h₁, lt_of_le_of_ne h₂ fun e ↦ pt_latticePoint_ne z i (2 ^ k * (y i + 1)) ?_⟩
    rw [e]; push_cast; ring
  -- a lattice site of the closed pitch box lies in the open one
  have hP : pt x ∈ closure (pitchInterior o₂ k (L.a k) j) →
      pt x ∈ pitchInterior o₂ k (L.a k) j := by
    intro h i _
    obtain ⟨h₁, h₂⟩ := closure_pitchInterior_subset o₂ k (L.a k) j h i trivial
    refine ⟨lt_of_le_of_ne h₁ fun e ↦ pt_latticePoint_ne z i
        (t k * L.a k i + s k * j i + t k) ?_, lt_of_le_of_ne h₂ fun e ↦ pt_latticePoint_ne z i
        (t k * L.a k i + s k * j i + s k) ?_⟩
    · rw [← e]; push_cast; ring
    · rw [e]; push_cast; ring
  rw [show pt x ∈ closure (primary o₂ L.Z L.C₀ k (L.a k) j) ↔
      pt x ∈ D o₂ L.Z L.C₀ k ∧ pt x ∈ pitchInterior o₂ k (L.a k) j from
    ⟨fun h ↦ ⟨hD (closure_mono inter_subset_left h), hP (closure_mono inter_subset_right h)⟩,
      fun h ↦ subset_closure h⟩]
  rw [show L.tile x = .primary k j ↔ L.piece x = .primary k j from
    ⟨piece_of_tile_primary, fun h ↦ by simp only [tile, h]⟩]
  set w := fineIdx k x with hw
  have hm : (0 : ℤ) < (s k / t k : ℕ) := by exact_mod_cast (scale_facts k).2.2.2.2.2.2.2
  have ht : (0 : ℝ) < t k := (scale_facts k).2.2.1
  have hs : (s k : ℝ) = ((s k / t k : ℕ) : ℝ) * t k := by
    rw [(scale_facts k).2.2.2.2.2.2.1, div_mul_cancel₀ _ ht.ne']
  have hcell : pt x ∈ cell o₂ ⌊ζ * k⌋₊ w := mem_cell_iff.2 rfl
  have hpi : ∀ i, pt x i ∈ Ioo (o₂ i + t k * L.a k i + s k * j i + t k)
      (o₂ i + t k * L.a k i + s k * j i + s k) ↔
      (¬ w i ≡ L.a k i [ZMOD (s k / t k : ℕ)] ∧ (w i - L.a k i) / (s k / t k : ℕ) = j i) := by
    intro i
    obtain ⟨h₁, h₂⟩ := hcell i trivial
    rw [← pitch_int hm, ← pitch_real (T := t k) (y := pt x i - o₂ i) ht
      (by rw [t_eq]; linarith) (by rw [t_eq]; linarith)
      (fun n ↦ by have := pt_latticePoint_ne z i (t k * n); push_cast at this; exact this)]
    simp only [mem_Ioo, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [hs]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hpitch : pt x ∈ pitchInterior o₂ k (L.a k) j ↔
      ¬ IsBeltCell k (L.a k) w ∧ L.pitchIdx k w = j := by
    simp only [pitchInterior, mem_univ_pi, IsBeltCell, not_exists, Layout.pitchIdx, funext_iff,
      hpi]
    exact ⟨fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩, fun h i ↦ ⟨h.1 i, h.2 i⟩⟩
  constructor
  · intro h
    obtain ⟨hl, -, -, hb, hj⟩ := piece_primary h
    exact ⟨mem_D_lev hl, hpitch.2 ⟨hb, hj.symm⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨hb, hj⟩ := hpitch.1 h₂
    have hl := lev_eq_of_mem_D h₁
    simp only [piece, hl, show ¬ k + 1 ≤ L.k₀ by omega, show ¬ L.K < k + 1 by omega, if_false,
      Nat.add_sub_cancel, ← hw, hb, hj]

end Layout

end

end AreaLaw.Geometry
