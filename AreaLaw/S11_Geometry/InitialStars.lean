import AreaLaw.S11_Geometry.BeltFans
import AreaLaw.S11_Geometry.RepairRegions

/-! # §11.4 Isolated stars of the initial mesh

Lemma 11.3: near every initial mark the initial tiles form a star of octants with alternating
labels across every active ray. The initial configuration of `BeltFans.lean` is packaged as the
repair data `Repair` of §11.5, with the hypotheses `Repair.Hyp` and `Repair.LatticeHyp`. Birth
regions are the closures of the interiors of the tiles.

Digest `digest/11-geometry.md` D11.13 -/

open Set Metric Filter Topology

namespace AreaLaw.Geometry

noncomputable section

/-! ## Open octants -/

/-- A direction inside the open octant `k`. -/
def octDir : Fin 8 → ℝ × ℝ :=
  ![(2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), (-1, -2), (1, -2), (2, -1)]

lemma isOpen_openCone (k : Fin 8) : IsOpen (openCone k) := by
  fin_cases k <;> simp only [openCone] <;> rw [ofPred_and] <;>
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))

lemma isClosed_octantConeAt (v : ℝ × ℝ) (k : Fin 8) : IsClosed (octantConeAt v k) := by
  have : IsClosed (octantCone k) := by
    fin_cases k <;> simp only [octantCone] <;> rw [ofPred_and] <;>
      exact (isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))
  exact this.preimage (continuous_id.sub continuous_const)

lemma openCone_subset (k : Fin 8) : openCone k ⊆ octantCone k := by
  intro p hp
  fin_cases k <;> simp only [openCone, octantCone, mem_ofPred_eq] at hp ⊢ <;>
    constructor <;> linarith [hp.1, hp.2]

lemma add_mem_openCone {k : Fin 8} {p q : ℝ × ℝ} (hp : p ∈ octantCone k)
    (hq : q ∈ openCone k) : p + q ∈ openCone k := by
  fin_cases k <;>
    simp only [octantCone, openCone, mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at hp hq ⊢ <;>
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]

lemma smul_octDir_mem {c : ℝ} (hc : 0 < c) (k : Fin 8) : c • octDir k ∈ openCone k := by
  fin_cases k <;>
    simp only [openCone, octDir, Fin.reduceFinMk, Matrix.cons_val, mem_ofPred_eq,
      Prod.smul_mk, smul_eq_mul] <;>
    constructor <;> linarith

lemma norm_octDir (k : Fin 8) : ‖octDir k‖ = 2 := by
  fin_cases k <;> simp [octDir, Prod.norm_def]

lemma openCone_signs {k : Fin 8} {p q : ℝ × ℝ} (hp : p ∈ openCone k) (hq : q ∈ openCone k) :
    (0 ≤ p.1 ↔ 0 ≤ q.1) ∧ (0 ≤ p.2 ↔ 0 ≤ q.2) ∧ (0 ≤ p.1 + p.2 ↔ 0 ≤ q.1 + q.2) ∧
      (0 ≤ p.1 - p.2 ↔ 0 ≤ q.1 - q.2) := by
  fin_cases k <;> simp only [openCone, mem_ofPred_eq] at hp hq <;>
    refine ⟨⟨fun _ ↦ ?_, fun _ ↦ ?_⟩, ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩, ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩,
      ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩⟩ <;> linarith [hp.1, hp.2, hq.1, hq.2]

lemma exists_openCone {p : ℝ × ℝ} (h₁ : p.1 ≠ 0) (h₂ : p.2 ≠ 0) (h₃ : p.1 + p.2 ≠ 0)
    (h₄ : p.1 - p.2 ≠ 0) : ∃ k, p ∈ openCone k := by
  rcases h₁.lt_or_gt with h₁ | h₁ <;> rcases h₂.lt_or_gt with h₂ | h₂ <;>
    rcases h₃.lt_or_gt with h₃ | h₃ <;> rcases h₄.lt_or_gt with h₄ | h₄ <;>
    first
    | (exfalso; linarith)
    | (refine ⟨0, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨1, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨2, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨3, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨4, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨5, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨6, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)
    | (refine ⟨7, ?_⟩; simp only [openCone, mem_ofPred_eq]; constructor <;> linarith)

/-- Every ball meets the union of the open octants about `v`. -/
lemma exists_near_openCone (v y : ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z k, z - v ∈ openCone k ∧ dist z y < δ := by
  obtain ⟨c, ⟨hc0, hcδ⟩, hcB⟩ := ((Set.Ioo_infinite (by linarith : (0 : ℝ) < δ / 4)).sdiff
    (Set.toFinite ({-(y - v).1, -(y - v).2 / 3, -((y - v).1 + (y - v).2) / 4,
      ((y - v).1 - (y - v).2) / 2} : Set ℝ))).nonempty
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hcB
  obtain ⟨n₁, n₂, n₃, n₄⟩ := hcB
  obtain ⟨k, hk⟩ := exists_openCone (p := y - v + (c, 3 * c))
    (fun h ↦ n₁ (by simp only [Prod.fst_add] at h; linarith))
    (fun h ↦ n₂ (by simp only [Prod.snd_add] at h; linarith))
    (fun h ↦ n₃ (by simp only [Prod.fst_add, Prod.snd_add] at h; linarith))
    (fun h ↦ n₄ (by simp only [Prod.fst_add, Prod.snd_add] at h; linarith))
  refine ⟨y + (c, 3 * c), k, by rwa [add_sub_right_comm], ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hc0, abs_of_pos (by linarith : 0 < 3 * c)]
  exact max_lt (by linarith) (by linarith)

/-- A star from constancy on open octants: if `F` is constant on each open octant about `v`
inside the ball of radius `ρ' > ρ`, the closure of the interior of each fibre of `F` meets the
closed ball of radius `ρ` in the union of the corresponding closed octants. -/
theorem star_of_const {I : Type*} (F : ℝ × ℝ → I) (v : ℝ × ℝ) {ρ ρ' : ℝ} (hρ : ρ < ρ')
    (g : Fin 8 → I) (hF : ∀ k y, y - v ∈ openCone k → dist y v < ρ' → F y = g k) (i : I) :
    closure (interior {x | F x = i}) ∩ closedBall v ρ =
      ⋃ (k : Fin 8) (_ : g k = i), octantConeAt v k ∩ closedBall v ρ := by
  ext x
  simp only [mem_inter_iff, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hx, hxv⟩
    have hxv' : dist x v ≤ ρ := mem_closedBall.1 hxv
    have hU : x ∈ closure (⋃ k ∈ {k | g k = i}, {y | y - v ∈ openCone k}) := by
      rw [Metric.mem_closure_iff] at hx ⊢
      intro ε hε
      have hε' : 0 < min ε (ρ' - ρ) / 2 := by have := sub_pos.2 hρ; positivity
      obtain ⟨y, hy, hxy⟩ := hx _ hε'
      obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
      obtain ⟨z, k, hz, hzy⟩ := exists_near_openCone v y (lt_min hη hε')
      have hzy₁ := hzy.trans_le (min_le_left _ _)
      have hzy₂ := hzy.trans_le (min_le_right _ _)
      have hzF : F z = i := interior_subset (s := {x | F x = i}) (hball (mem_ball.2 hzy₁))
      have hm₁ := min_le_left ε (ρ' - ρ)
      have hm₂ := min_le_right ε (ρ' - ρ)
      have t₁ := dist_triangle z y v
      have t₂ := dist_triangle y x v
      have t₃ := dist_triangle x y z
      rw [dist_comm y x] at t₂
      rw [dist_comm y z] at t₃
      have hzv : dist z v < ρ' := by linarith
      exact ⟨z, mem_iUnion₂.2 ⟨k, (hF k z hz hzv).symm.trans hzF, hz⟩, by linarith⟩
    rw [(Set.toFinite _).closure_biUnion] at hU
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hU
    exact ⟨k, hk, closure_minimal (s := {y | y - v ∈ openCone k}) (t := octantConeAt v k)
      (fun y hy ↦ openCone_subset k hy) (isClosed_octantConeAt v k) hxk, hxv⟩
  · rintro ⟨k, hk, hxk, hxv⟩
    refine ⟨?_, hxv⟩
    have hopen : IsOpen ({y | y - v ∈ openCone k} ∩ ball v ρ') :=
      ((isOpen_openCone k).preimage (continuous_id.sub continuous_const)).inter isOpen_ball
    have hsub : {y | y - v ∈ openCone k} ∩ ball v ρ' ⊆ interior {x | F x = i} :=
      interior_maximal (fun y hy ↦ (hF k y hy.1 hy.2).trans hk) hopen
    refine closure_mono hsub (Metric.mem_closure_iff.2 fun ε hε ↦ ?_)
    have hc : 0 < min ε (ρ' - ρ) / 4 := by have := sub_pos.2 hρ; positivity
    have hm₁ := min_le_left ε (ρ' - ρ)
    have hm₂ := min_le_right ε (ρ' - ρ)
    have hn : ‖(min ε (ρ' - ρ) / 4) • octDir k‖ = 2 * (min ε (ρ' - ρ) / 4) := by
      rw [norm_smul, norm_octDir, Real.norm_eq_abs, abs_of_pos hc]; ring
    have hxv' : dist x v ≤ ρ := mem_closedBall.1 hxv
    refine ⟨x + (min ε (ρ' - ρ) / 4) • octDir k, ⟨?_, ?_⟩, ?_⟩
    · change x + _ - v ∈ openCone k
      rw [add_sub_right_comm]; exact add_mem_openCone hxk (smul_octDir_mem hc k)
    · rw [mem_ball]
      calc dist (x + (min ε (ρ' - ρ) / 4) • octDir k) v
          ≤ dist x v + ‖(min ε (ρ' - ρ) / 4) • octDir k‖ := by
            rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
        _ < ρ' := by linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, hn]; linarith

/-! ## Grid structure near a point -/

lemma f₀_add (v d : ℝ × ℝ) (δ : ℝ) : f₀ (v + δ • d) = f₀ v + δ * d.1 := by
  simp only [f₀, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
lemma f₁_add (v d : ℝ × ℝ) (δ : ℝ) : f₁ (v + δ • d) = f₁ v + δ * d.2 := by
  simp only [f₁, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
lemma fp_add (v d : ℝ × ℝ) (δ : ℝ) : fp (v + δ • d) = fp v + δ * (d.1 + d.2) := by
  simp only [fp, f₀_add, f₁_add]; ring
lemma fm_add (v d : ℝ × ℝ) (δ : ℝ) : fm (v + δ • d) = fm v + δ * (d.1 - d.2) := by
  simp only [fm, f₀_add, f₁_add]; ring

lemma abs_sub_le_dist (y v : ℝ × ℝ) :
    |f₀ y - f₀ v| ≤ dist y v ∧ |f₁ y - f₁ v| ≤ dist y v := by
  simp only [f₀, f₁, sub_sub_sub_cancel_right, Prod.dist_eq, Real.dist_eq]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- Two points of one open octant about a point `v` of the mesh `2^p ℤ²`, within `2^p / 2` of
`v`, lie on the same side of every grid line of mesh `2^p` of the four slopes. -/
lemma sim_of_sector {v y y' : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} (h₀ : f₀ v = n₀ * 2 ^ p)
    (h₁ : f₁ v = n₁ * 2 ^ p) {k : Fin 8} (hy : y - v ∈ openCone k) (hy' : y' - v ∈ openCone k)
    (hd : dist y v < 2 ^ p / 2) (hd' : dist y' v < 2 ^ p / 2) : Sim p y y' := by
  obtain ⟨s₀, s₁, s₂, s₃⟩ := openCone_signs hy hy'
  obtain ⟨a₀, a₁⟩ := abs_sub_le_dist y v
  obtain ⟨b₀, b₁⟩ := abs_sub_le_dist y' v
  simp only [Prod.fst_sub, Prod.snd_sub] at s₀ s₁ s₂ s₃
  have e₀ (z : ℝ × ℝ) : f₀ z = n₀ * 2 ^ p + (z.1 - v.1) := by
    unfold f₀ at h₀ ⊢; linarith
  have e₁ (z : ℝ × ℝ) : f₁ z = n₁ * 2 ^ p + (z.2 - v.2) := by
    unfold f₁ at h₁ ⊢; linarith
  have g₀ (z : ℝ × ℝ) : f₀ z - f₀ v = z.1 - v.1 := by simp [f₀]
  have g₁ (z : ℝ × ℝ) : f₁ z - f₁ v = z.2 - v.2 := by simp [f₁]
  rw [g₀] at a₀ b₀; rw [g₁] at a₁ b₁
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e₀, e₀]; exact sb_of_near n₀ (by linarith) (by linarith) s₀
  · rw [e₁, e₁]; exact sb_of_near n₁ (by linarith) (by linarith) s₁
  · have (z : ℝ × ℝ) : fp z = ((n₀ + n₁ : ℤ) : ℝ) * 2 ^ p + ((z.1 - v.1) + (z.2 - v.2)) := by
      unfold fp; rw [e₀, e₁]; push_cast; ring
    rw [this, this]
    exact sb_of_near _ ((abs_add_le _ _).trans_lt (by linarith))
      ((abs_add_le _ _).trans_lt (by linarith)) s₂
  · have (z : ℝ × ℝ) : fm z = ((n₀ - n₁ : ℤ) : ℝ) * 2 ^ p + ((z.1 - v.1) - (z.2 - v.2)) := by
      unfold fm; rw [e₀, e₁]; push_cast; ring
    rw [this, this]
    exact sb_of_near _ ((abs_sub _ _).trans_lt (by linarith))
      ((abs_sub _ _).trans_lt (by linarith)) s₃

section dirs

variable {p : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδu : δ * 3 < 2 ^ p)
include hδ hδu

lemma sb_dir (n : ℤ) {c c' : ℝ} (hc : |c| ≤ 3) (hc' : |c'| ≤ 3) (hs : 0 ≤ c ↔ 0 ≤ c') :
    SB (2 ^ p) (n * 2 ^ p + δ * c) (n * 2 ^ p + δ * c') := by
  refine sb_of_near n ?_ ?_ ?_
  · rw [abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg c]
  · rw [abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg c']
  · rw [mul_nonneg_iff_of_pos_left hδ, mul_nonneg_iff_of_pos_left hδ]; exact hs

lemma adj_dir (n : ℤ) {c c' : ℝ} (hc : 0 < c) (hc3 : c ≤ 3) (hc' : c' < 0) (hc'3 : -3 ≤ c') :
    Adj (2 ^ p) (n * 2 ^ p + δ * c) (n * 2 ^ p + δ * c') :=
  adj_of_near n (by positivity) (by nlinarith) (by nlinarith) (by nlinarith)

end dirs

/-- Sample points of consecutive octants about a mesh point: they are separated by exactly one
grid line, the active ray between the octants. -/
lemma oct_cross {v : ℝ × ℝ} {p : ℕ} {n₀ n₁ : ℤ} {δ : ℝ} (h₀ : f₀ v = n₀ * 2 ^ p)
    (h₁ : f₁ v = n₁ * 2 ^ p) (hδ : 0 < δ) (hδu : δ * 3 < 2 ^ p) (k : Fin 8) :
    CrossX p (v + δ • octDir k) (v + δ • octDir (k + 1)) ∨
    CrossX p (v + δ • octDir (k + 1)) (v + δ • octDir k) ∨
    CrossY p (v + δ • octDir k) (v + δ • octDir (k + 1)) ∨
    CrossY p (v + δ • octDir (k + 1)) (v + δ • octDir k) ∨
    AxSim p (v + δ • octDir k) (v + δ • octDir (k + 1)) := by
  have hp : fp v = ((n₀ + n₁ : ℤ) : ℝ) * 2 ^ p := by unfold fp; rw [h₀, h₁]; push_cast; ring
  have hm : fm v = ((n₀ - n₁ : ℤ) : ℝ) * 2 ^ p := by unfold fm; rw [h₀, h₁]; push_cast; ring
  simp only [CrossX, CrossY, AxSim, f₀_add, f₁_add, fp_add, fm_add, h₀, h₁, hp, hm]
  fin_cases k <;>
    simp only [octDir, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, Matrix.cons_val] <;>
    first
    | (refine Or.inl ⟨adj_dir hδ hδu _ ?_ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_,
        sb_dir hδ hδu _ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_⟩ <;> norm_num [abs_le] <;> done)
    | (refine Or.inr <| Or.inl ⟨adj_dir hδ hδu _ ?_ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_,
        sb_dir hδ hδu _ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_⟩ <;> norm_num [abs_le] <;> done)
    | (refine Or.inr <| Or.inr <| Or.inl ⟨sb_dir hδ hδu _ ?_ ?_ ?_, adj_dir hδ hδu _ ?_ ?_ ?_ ?_,
        sb_dir hδ hδu _ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_⟩ <;> norm_num [abs_le] <;> done)
    | (refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨sb_dir hδ hδu _ ?_ ?_ ?_,
        adj_dir hδ hδu _ ?_ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_, sb_dir hδ hδu _ ?_ ?_ ?_⟩ <;>
        norm_num [abs_le] <;> done)
    | (refine Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨sb_dir hδ hδu _ ?_ ?_ ?_,
        sb_dir hδ hδu _ ?_ ?_ ?_⟩ <;> norm_num [abs_le])

/-- At a lattice site the four forms are irrational, so nearby points agree on all unit grid
lines. -/
lemma eventually_sim_lattice (z : ℤ × ℤ) :
    ∀ᶠ y in 𝓝 (latticePoint z), Sim 0 (latticePoint z) y := by
  obtain ⟨i₀, i₁, i₂, i₃⟩ := isIrrationalOrigin_o₂
  have key (F : ℝ × ℝ → ℝ) (hF : Continuous F) (h : Irrational (F (latticePoint z))) :
      ∀ᶠ y in 𝓝 (latticePoint z), SB (2 ^ 0) (F (latticePoint z)) (F y) := by
    have h₁ : (⌊F (latticePoint z)⌋ : ℝ) < F (latticePoint z) :=
      lt_of_le_of_ne (Int.floor_le _) (fun e ↦ h.ne_int _ e.symm)
    have h₂ := Int.lt_floor_add_one (F (latticePoint z))
    filter_upwards [hF.continuousAt.eventually (Ioo_mem_nhds h₁ h₂)] with y hy
    rw [pow_zero]
    exact sb_of_mem one_pos ⌊F (latticePoint z)⌋ (by rw [mul_one]; exact h₁.le)
      (by rw [mul_one]; exact h₂) (by rw [mul_one]; exact hy.1.le) (by rw [mul_one]; exact hy.2)
  have c₀ : Continuous f₀ := by unfold f₀; fun_prop
  have c₁ : Continuous f₁ := by unfold f₁; fun_prop
  have r₀ : f₀ (latticePoint z) = (z.1 : ℝ) - o₂ 0 := rfl
  have r₁ : f₁ (latticePoint z) = (z.2 : ℝ) - o₂ 1 := rfl
  have j₀ : Irrational (f₀ (latticePoint z)) := by rw [r₀]; exact Irrational.intCast_sub i₀ _
  have j₁ : Irrational (f₁ (latticePoint z)) := by rw [r₁]; exact Irrational.intCast_sub i₁ _
  have j₂ : Irrational (fp (latticePoint z)) := by
    rw [fp, r₀, r₁, show (z.1 : ℝ) - o₂ 0 + (z.2 - o₂ 1) = ((z.1 + z.2 : ℤ) : ℝ) -
      (o₂ 0 + o₂ 1) by push_cast; ring]
    exact Irrational.intCast_sub i₂ _
  have j₃ : Irrational (fm (latticePoint z)) := by
    rw [fm, r₀, r₁, show (z.1 : ℝ) - o₂ 0 - (z.2 - o₂ 1) = ((z.1 - z.2 : ℤ) : ℝ) -
      (o₂ 0 - o₂ 1) by push_cast; ring]
    exact Irrational.intCast_sub i₃ _
  filter_upwards [key f₀ c₀ j₀, key f₁ c₁ j₁, key fp (by unfold fp; fun_prop) j₂,
    key fm (by unfold fm; fun_prop) j₃] with y h₀ h₁ h₂ h₃
  exact ⟨⟨h₀, h₁⟩, h₂, h₃⟩

/-! ## D11.13 The initial stars -/

/-- D11.13. The sample point of octant `k` of the star at `v` of scale `S`. -/
def octPt (v : ℝ × ℝ) (S : ℝ) (k : Fin 8) : ℝ × ℝ := v + (S / 256) • octDir k

lemma dist_octPt (v : ℝ × ℝ) {S : ℝ} (hS : 0 ≤ S) (k : Fin 8) :
    dist (octPt v S k) v = S / 256 * 2 := by
  rw [octPt, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_octDir, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

lemma gap_of_ne {F F' u : ℝ} {B B' : ℤ} (hu : 0 < u) (hF : F = B * u) (hF' : F' = B' * u)
    (h : F ≠ F') : u ≤ |F - F'| := by
  have hB : B ≠ B' := fun e ↦ h (by rw [hF, hF', e])
  have : (1 : ℝ) ≤ |(B : ℝ) - B'| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hB)
  rw [hF, hF', ← sub_mul, abs_mul, abs_of_pos hu]; nlinarith

namespace Layout

variable {L : Layout}

lemma t_le_t {k k' : ℕ} (h : k ≤ k') : (t k : ℝ) ≤ t k' := by
  rw [t_eq, t_eq]; exact pow_le_pow_right₀ (by norm_num) (floor_zeta_mono h)

/-- The marks of a belt cell of layer `k` lie in `closure D_k`. -/
lemma mark_mem_closure {k : ℕ} {w : Fin 2 → ℤ} (hw : w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k))
    (hk : L.k₀ ≤ k) (e : Fin 3 × Fin 3) : pt (markPos k w e) ∈ closure (D o₂ L.Z L.C₀ k) := by
  have hf : w ∈ fineIndex o₂ L.Z L.C₀ k := (Finset.mem_filter.1 hw).1
  have hsub : cell o₂ ⌊ζ * k⌋₊ w ⊆ D o₂ L.Z L.C₀ k := by
    intro y hy
    rw [D_eq_iUnion]
    refine mem_iUnion₂.2 ⟨_, mem_fineIndex_iff.1 hf, ?_⟩
    rw [mem_cell_iff, cellIndex_eq_fine, mem_cell_iff.1 hy]
  refine closure_mono hsub ?_
  have hq := L.two_le_floor hk
  have hH : (2 : ℝ) ^ ⌊ζ * k⌋₊ = 2 * hs k := two_pow_eq (by omega)
  have hH' : (2 : ℝ) ^ (⌊ζ * k⌋₊ - 1) = hs k := rfl
  have h₁ : ((e.1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 e.1.2
  have h₂ : ((e.2 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 e.2.2
  have a₁ := mul_le_mul_of_nonneg_left h₁ (hs_pos k).le
  have a₂ := mul_le_mul_of_nonneg_left h₂ (hs_pos k).le
  have b₁ := mul_nonneg (hs_pos k).le (Nat.cast_nonneg (e.1 : ℕ) : (0 : ℝ) ≤ (e.1 : ℕ))
  have b₂ := mul_nonneg (hs_pos k).le (Nat.cast_nonneg (e.2 : ℕ) : (0 : ℝ) ≤ (e.2 : ℕ))
  rw [closure_cell, mem_univ_pi]
  intro i; fin_cases i
  · change _ ≤ (markPos k w e).1 ∧ (markPos k w e).1 ≤ _
    simp only [markPos, markInt, latticePoint, Prod.fst_add, Fin.zero_eta, Fin.isValue]
    push_cast; rw [hH, hH']
    constructor <;> nlinarith
  · change _ ≤ (markPos k w e).2 ∧ (markPos k w e).2 ≤ _
    simp only [markPos, markInt, latticePoint, Prod.snd_add, Fin.mk_one, Fin.isValue]
    push_cast; rw [hH, hH']
    constructor <;> nlinarith

variable (L)

/-- The local data at a mark `v` of layer `k = markLayer v`: `v` lies on the mesh `(t_k/4)ℤ²`
and in `closure D_k`. -/
lemma mark_facts (v : L.marks) : ∃ n₀ n₁ : ℤ,
    f₀ v.1 = n₀ * 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) ∧ f₁ v.1 = n₁ * 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) ∧
      pt v.1 ∈ closure (D o₂ L.Z L.C₀ (L.markLayer v)) ∧ L.k₀ ≤ L.markLayer v ∧
      L.markLayer v < L.K ∧ 2 ≤ ⌊ζ * L.markLayer v⌋₊ := by
  obtain ⟨hk, hK, w, hw, e, he⟩ := L.marks_markLayer v
  have hq := L.two_le_floor hk
  obtain ⟨h0, h1⟩ := markInt_eq (k := L.markLayer v) (r := ⌊ζ * L.markLayer v⌋₊ - 2) (by omega)
    w e
  obtain ⟨g0, g1⟩ := f_markPos (L.markLayer v) w e
  rw [he] at g0 g1
  refine ⟨(2 * w 0 + (e.1 : ℕ)) * 2 ^ (⌊ζ * L.markLayer v⌋₊ - 1 - (⌊ζ * L.markLayer v⌋₊ - 2)),
    (2 * w 1 + (e.2 : ℕ)) * 2 ^ (⌊ζ * L.markLayer v⌋₊ - 1 - (⌊ζ * L.markLayer v⌋₊ - 2)),
    ?_, ?_, he ▸ mark_mem_closure hw hk e, hk, hK, hq⟩
  · rw [g0, h0]; push_cast; ring
  · rw [g1, h1]; push_cast; ring

lemma markScale_eq (v : L.marks) :
    L.markScale v = 4 * 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) := by
  obtain ⟨-, -, -, -, -, -, hq⟩ := L.mark_facts v
  rw [markScale, t_eq, show ⌊ζ * L.markLayer v⌋₊ = ⌊ζ * L.markLayer v⌋₊ - 2 + 2 by omega,
    pow_add, Nat.add_sub_cancel]
  ring

/-- D11.13.1–3. In the open octants about a mark `v` of layer `k`, within `t_k/8`, the identifier
is constant: only layers `k-1, k, k+1` occur and all their edges lie on lines of the mesh
`(t_k/4)ℤ²` with the four slopes, none of which crosses an open octant near `v`. -/
theorem step_11_13_3 (v : L.marks) {k : Fin 8} {y y' : ℝ × ℝ} (hy : y - v.1 ∈ openCone k)
    (hy' : y' - v.1 ∈ openCone k) (hd : dist y v.1 < 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) / 2)
    (hd' : dist y' v.1 < 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) / 2) : L.tile y = L.tile y' := by
  obtain ⟨n₀, n₁, h₀, h₁, hD, hk, hK, hq⟩ := L.mark_facts v
  -- D11.13.2: the two points agree on the grid lines of mesh `t_k/4`
  refine tile_eq_of_sim (sim_of_sector h₀ h₁ hy hy' hd hd') ?_
  -- D11.13.1: only the layers `≥ k - 1` occur near `v`
  have h2 : (2 : ℝ) ^ (⌊ζ * L.markLayer v⌋₊ - 2) ≤ 2 ^ ⌊ζ * L.markLayer v⌋₊ :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have := lay_near (x' := y) hD hk hK.le (by
    rw [dist_comm]; linarith [pow_pos (two_pos : (0 : ℝ) < 2) (⌊ζ * L.markLayer v⌋₊ - 2)])
  omega

lemma octPt_facts (v : L.marks) (k : Fin 8) :
    octPt v.1 (L.markScale v) k - v.1 ∈ openCone k ∧
      dist (octPt v.1 (L.markScale v) k) v.1 < 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) / 2 ∧
      dist v.1 (octPt v.1 (L.markScale v) k) < 2 ^ ⌊ζ * L.markLayer v⌋₊ := by
  obtain ⟨-, -, -, -, -, -, hq⟩ := L.mark_facts v
  have hS := L.markScale_eq v
  have hu : (0 : ℝ) < 2 ^ (⌊ζ * L.markLayer v⌋₊ - 2) := by positivity
  have h2 : (2 : ℝ) ^ (⌊ζ * L.markLayer v⌋₊ - 2) ≤ 2 ^ ⌊ζ * L.markLayer v⌋₊ :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hd := dist_octPt v.1 (by rw [hS]; positivity : 0 ≤ L.markScale v) k
  refine ⟨?_, ?_, ?_⟩
  · rw [octPt, add_sub_cancel_left]; exact smul_octDir_mem (by rw [hS]; positivity) k
  · rw [hd, hS]; linarith
  · rw [dist_comm, hd, hS]; linarith


/-- D11.13. The initial configuration as repair data: the initial marks with their scales `S_v`,
the identifiers of their octants (read off at a sample point of each octant), the labels, the
birth regions (closures of the interiors of the tiles), `S_*` and `a₀ = 1/64`. -/
def repair : Repair InitId L.marks where
  v₀ v := v.1
  S₀ := L.markScale
  oct₀ v k := L.tile (octPt v.1 (L.markScale v) k)
  label₀ := L.label
  birth₀ i := closure (interior {x | L.tile x = i})
  stopScale := L.stopScale
  a₀ := starA₀

/-- D11.13.4. Distinct marks `v, w` satisfy `‖v - w‖_∞ ≥ a₀ max(S_v, S_w)`: marks of layers
`k ≤ k' ≤ k + 1` lie on the mesh `(t_k/2)ℤ²`, `t_{k'} ≤ 2t_k`, and marks of layers `k + 2 ≤ k'`
are separated by D11.7. -/
theorem step_11_13_4 (r r' : L.marks) (h : r ≠ r') :
    starA₀ * max (L.markScale r) (L.markScale r') ≤ dist r.1 r'.1 := by
  wlog hle : L.markLayer r ≤ L.markLayer r' generalizing r r'
  · rw [max_comm, dist_comm]; exact this r' r (Ne.symm h) (by omega)
  obtain ⟨hk, hK, w, hw, e, he⟩ := L.marks_markLayer r
  obtain ⟨hk', hK', w', hw', e', he'⟩ := L.marks_markLayer r'
  have hmax : max (L.markScale r) (L.markScale r') = t (L.markLayer r') :=
    max_eq_right (t_le_t hle)
  rw [hmax]
  have ht0 : (0 : ℝ) ≤ t (L.markLayer r') := by rw [t_eq]; positivity
  rcases (show L.markLayer r' ≤ L.markLayer r + 1 ∨ L.markLayer r + 2 ≤ L.markLayer r' by
    omega) with h₁ | h₁
  · have hq := L.two_le_floor hk
    have hqq := floor_zeta_mono hle
    have hq1 : ⌊ζ * L.markLayer r'⌋₊ ≤ ⌊ζ * L.markLayer r⌋₊ + 1 :=
      (floor_zeta_mono h₁).trans (floor_zeta_succ _)
    have hu : (0 : ℝ) < 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1) := by positivity
    have ht : (t (L.markLayer r') : ℝ) ≤ 4 * 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1) := by
      rw [t_eq]
      calc (2 : ℝ) ^ ⌊ζ * L.markLayer r'⌋₊ ≤ 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1 + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4 * 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1) := by rw [pow_add]; ring
    have hne : r.1 ≠ r'.1 := fun e ↦ h (Subtype.ext e)
    obtain ⟨d₀, d₁⟩ := abs_sub_le_dist r.1 r'.1
    have F (k₁ : ℕ) (w₁ : Fin 2 → ℤ) (e₁ : Fin 3 × Fin 3) (r₁ : L.marks)
        (he₁ : markPos k₁ w₁ e₁ = r₁.1) (hk₁ : ⌊ζ * L.markLayer r⌋₊ - 1 + 1 ≤ ⌊ζ * k₁⌋₊) :
        f₀ r₁.1 = (((2 * w₁ 0 + (e₁.1 : ℕ)) * 2 ^ (⌊ζ * k₁⌋₊ - 1 - (⌊ζ * L.markLayer r⌋₊ - 1)) :
          ℤ) : ℝ) * 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1) ∧
        f₁ r₁.1 = (((2 * w₁ 1 + (e₁.2 : ℕ)) * 2 ^ (⌊ζ * k₁⌋₊ - 1 - (⌊ζ * L.markLayer r⌋₊ - 1)) :
          ℤ) : ℝ) * 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1) := by
      obtain ⟨b₀, b₁⟩ := markInt_eq hk₁ w₁ e₁
      obtain ⟨c₀, c₁⟩ := f_markPos k₁ w₁ e₁
      rw [he₁] at c₀ c₁
      rw [c₀, c₁, b₀, b₁]; constructor <;> norm_cast
    obtain ⟨F₀, F₁⟩ := F _ w e r he (by omega)
    obtain ⟨F₀', F₁'⟩ := F _ w' e' r' he' (by omega)
    have hgap : (2 : ℝ) ^ (⌊ζ * L.markLayer r⌋₊ - 1) ≤ dist r.1 r'.1 := by
      by_cases e₀ : f₀ r.1 = f₀ r'.1
      · have e₁ : f₁ r.1 ≠ f₁ r'.1 := fun e₁ ↦ hne (Prod.ext
          (by unfold f₀ at e₀; linarith) (by unfold f₁ at e₁; linarith))
        exact le_trans (gap_of_ne hu F₁ F₁' e₁) d₁
      · exact le_trans (gap_of_ne hu F₀ F₀' e₀) d₀
    calc starA₀ * t (L.markLayer r') ≤ starA₀ * (4 * 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1)) :=
          mul_le_mul_of_nonneg_left ht (by norm_num [starA₀])
      _ ≤ 2 ^ (⌊ζ * L.markLayer r⌋₊ - 1) := by norm_num [starA₀]; linarith
      _ ≤ dist r.1 r'.1 := hgap
  · -- D11.7: marks of non-adjacent layers are far apart
    have h7 := step_11_7 h₁ (he ▸ mark_mem_closure hw hk e) (he' ▸ mark_mem_closure hw' hk' e')
    rw [dist_pt] at h7
    have hC : (2 : ℝ) ≤ L.C₀ := by exact_mod_cast L.two_le_C₀
    have ht : (t (L.markLayer r') : ℝ) ≤ 2 ^ L.markLayer r' := by
      rw [t_eq]; exact pow_le_pow_right₀ (by norm_num) (floor_zeta_le _)
    have h2 : (0 : ℝ) < 2 ^ L.markLayer r' := by positivity
    have : (2 : ℝ) ^ L.markLayer r' / 2 ≤ (L.C₀ - 1) / 2 * 2 ^ L.markLayer r' := by nlinarith
    calc starA₀ * t (L.markLayer r') ≤ 2 ^ L.markLayer r' / 2 := by
          norm_num [starA₀]; linarith
      _ ≤ dist r.1 r'.1 := by linarith [h7.1, h7.2]

/-- D11.13.5. Consecutive octants about a mark with distinct identifiers have opposite labels:
their sample points lie on either side of one active ray, a grid line of mesh `t_k/4`, and the
point-contact property `step_11_11` applies. -/
theorem step_11_13_5 (r : L.marks) (k : Fin 8)
    (h : L.repair.oct₀ r k ≠ L.repair.oct₀ r (k + 1)) :
    L.repair.label₀ (L.repair.oct₀ r k) ≠ L.repair.label₀ (L.repair.oct₀ r (k + 1)) := by
  change L.tile _ ≠ L.tile _ at h
  change L.label (L.tile _) ≠ L.label (L.tile _)
  obtain ⟨n₀, n₁, h₀, h₁, hD, hk, hK, hq⟩ := L.mark_facts r
  have hS := L.markScale_eq r
  have hu : (0 : ℝ) < 2 ^ (⌊ζ * L.markLayer r⌋₊ - 2) := by positivity
  have hδ : 0 < L.markScale r / 256 := by rw [hS]; positivity
  have hδu : L.markScale r / 256 * 3 < 2 ^ (⌊ζ * L.markLayer r⌋₊ - 2) := by rw [hS]; linarith
  have hlay (j : Fin 8) :
      ⌊ζ * L.markLayer r⌋₊ - 2 + 1 ≤ ⌊ζ * L.lay (octPt r.1 (L.markScale r) j)⌋₊ := by
    have := lay_near hD hk hK.le (L.octPt_facts r j).2.2
    omega
  rcases oct_cross h₀ h₁ hδ hδu k with hc | hc | hc | hc | hc
  · exact step_11_11 (Or.inl hc) (hlay k) (hlay (k + 1)) h
  · exact (step_11_11 (Or.inl hc) (hlay (k + 1)) (hlay k) (Ne.symm h)).symm
  · exact step_11_11 (Or.inr (Or.inl hc)) (hlay k) (hlay (k + 1)) h
  · exact (step_11_11 (Or.inr (Or.inl hc)) (hlay (k + 1)) (hlay k) (Ne.symm h)).symm
  · exact step_11_11 (Or.inr (Or.inr hc)) (hlay k) (hlay (k + 1)) h

/-- Near a lattice site the identifier is constant. -/
lemma tile_nhds (z : ℤ × ℤ) :
    {x | L.tile x = L.tile (latticePoint z)} ∈ 𝓝 (latticePoint z) := by
  have h1 : 0 + 1 ≤ ⌊ζ * L.lay (latticePoint z)⌋₊ := by
    have := L.two_le_floor (le_refl L.k₀)
    have := floor_zeta_mono (L.k₀_le_lay (latticePoint z))
    omega
  filter_upwards [eventually_sim_lattice z] with y hy
  exact (tile_eq_of_sim hy h1).symm

lemma eq_of_mem_birth {z : ℤ × ℤ} {i : InitId}
    (h : latticePoint z ∈ closure (interior {x | L.tile x = i})) :
    i = L.tile (latticePoint z) := by
  obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff_nhds.1 h _ (L.tile_nhds z)
  exact (interior_subset (s := {x | L.tile x = i}) hy₂ : L.tile y = i).symm.trans hy₁

/-- D11.13 (Lemma 11.3, `geometry:initial-stars`). There is an absolute `a₀ > 0`, independent of
the layer and of the shifts, such that for `k₀` large:
1. distinct marks `v,w`: `‖v-w‖_∞ ≥ a₀ max(S_v,S_w)`;
2. in `v+[-a₀S_v,a₀S_v]²` all active boundaries are straight rays from `v` in the eight axis
and diagonal directions; each sector between consecutive active rays has one tile identifier and
consecutive sectors have opposite labels; with no active ray the square lies in one tile.
Active boundary = interface of distinct identifiers (merged seams are not boundaries).
2D only: eight octant rays of a planar star and the irrational planar origin. -/
theorem lemma_11_3 : L.repair.Hyp ∧ L.repair.LatticeHyp (o₂ 0, o₂ 1) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨isIrrationalOrigin_o₂, ?_, ?_, ?_⟩⟩
  · change (0 : ℝ) < starA₀; norm_num [starA₀]
  · change starA₀ < 1 / 2; norm_num [starA₀]
  · change (2 : ℝ) ≤ L.stopScale
    exact ((by norm_num : (2 : ℝ) ≤ 4).trans (le_max_left _ _)).trans L.Sstar_le
  · intro S hS
    exact (eq_trim_margins (by norm_num [starA₀] : (0 : ℝ) < starA₀)
      (((show (1000 / starA₀) ^ (1 - ρ₀)⁻¹ ≤ Sstar from le_max_right _ _).trans L.Sstar_le).trans
        hS)).2.2
  · exact fun r ↦ L.stopScale_le.trans (t_le_t (L.marks_markLayer r).1)
  · -- D11.13.4
    exact L.step_11_13_4
  · -- D11.13.1–3: the star
    intro r i
    obtain ⟨-, -, -, -, -, -, hq⟩ := L.mark_facts r
    have hS := L.markScale_eq r
    have hu : (0 : ℝ) < 2 ^ (⌊ζ * L.markLayer r⌋₊ - 2) := by positivity
    refine star_of_const L.tile r.1 (ρ' := 2 ^ (⌊ζ * L.markLayer r⌋₊ - 2) / 2) ?_ _
      (fun k y hy hd ↦ L.step_11_13_3 r hy (L.octPt_facts r k).1 hd (L.octPt_facts r k).2.1) i
    change starA₀ * L.markScale r < _
    rw [hS]; norm_num [starA₀]; linarith
  · -- D11.13.5
    exact L.step_11_13_5
  · intro r
    obtain ⟨-, -, w, -, e, he⟩ := L.marks_markLayer r
    exact ⟨markInt _ w e, he.symm⟩
  · intro z i j hi hj
    exact (L.eq_of_mem_birth hi).trans (L.eq_of_mem_birth hj).symm
  · intro z
    exact ⟨L.tile (latticePoint z), subset_closure (mem_interior_iff_mem_nhds.2 (L.tile_nhds z))⟩

end Layout

end

end AreaLaw.Geometry
