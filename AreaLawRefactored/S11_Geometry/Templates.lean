import AreaLawRefactored.S11_Geometry.Primaries
import AreaLawRefactored.S11_Geometry.Repairs

/-! # §11.7 Exceptional sites and templates

The exceptional set of dummy and terminal sites is bounded, and primaries, belt tiles and
replacements give templates of Definition 9.3 (`OpenAI.IsTemplate`) separated from the cut
(`OpenAI.IsSeparatedFromCut`). Counts and distances are stated on `Fin d → ℝ`; templates are
planar, and the plane `Fin 2 → ℝ` is identified with `ℝ × ℝ` once, by `plane`.

Digest `digest/11-geometry.md` D11.20–D11.23 -/

open Set Metric Filter Topology OpenAI

namespace AreaLaw.Geometry

variable {d : ℕ}

/-! ## The plane and the lattice -/

/-- The plane `Fin 2 → ℝ` as `ℝ × ℝ`, `x ↦ (x 0, x 1)`: an isometry of the sup metrics. -/
def plane : (Fin 2 → ℝ) ≃ᵢ ℝ × ℝ := IsometryEquiv.piFinTwo fun _ ↦ ℝ

/-- The lattice `Fin 2 → ℤ` as `ℤ × ℤ`, `z ↦ (z 0, z 1)`: an isometry of the sup metrics. -/
def lattice : (Fin 2 → ℤ) ≃ᵢ ℤ × ℤ := IsometryEquiv.piFinTwo fun _ ↦ ℤ

/-- The lattice site `z ∈ ℤ^d` as a point of `ℝ^d`. -/
def latticeSite (z : Fin d → ℤ) : Fin d → ℝ := fun i ↦ z i

theorem isometry_latticeSite : Isometry (latticeSite (d := d)) :=
  Isometry.piMap (fun _ ↦ ((↑) : ℤ → ℝ)) fun _ ↦ Real.isometry_intCast

theorem plane_latticeSite (z : Fin 2 → ℤ) : plane (latticeSite z) = latticePoint (lattice z) :=
  rfl

theorem isometry_latticePoint : Isometry latticePoint :=
  Real.isometry_intCast.prodMap Real.isometry_intCast

/-- The site `z ∈ ℤ × ℤ` as a point of `Fin 2 → ℝ`. -/
theorem isometry_plane_symm_latticePoint :
    Isometry fun z : ℤ × ℤ ↦ plane.symm (latticePoint z) :=
  plane.symm.isometry.comp isometry_latticePoint

open Classical in
/-- The cut endpoints `Z = Z_A ⊂ ℤ²` as points of `Fin 2 → ℝ`, the endpoint set of §11.3. -/
noncomputable def cutSites (Λ A : Finset (ℤ × ℤ)) : Finset (Fin 2 → ℝ) :=
  (cutEndpoints Λ A).image fun z ↦ plane.symm (latticePoint z)

/-- A closed box `∏ [l_i, u_i]` of `Fin 2 → ℝ` is the rectangle `[l₀,u₀] × [l₁,u₁]`. -/
theorem plane_image_pi_Icc (l u : Fin 2 → ℝ) :
    plane '' univ.pi (fun i ↦ Icc (l i) (u i)) = Icc (l 0) (u 0) ×ˢ Icc (l 1) (u 1) := by
  rw [← IsometryEquiv.preimage_symm]
  ext p
  simp only [mem_preimage, mem_univ_pi, mem_prod, Fin.forall_fin_two]
  rfl

/-- An axis-parallel closed rectangle with nonempty interior is a template piece; its
sup-diameter is at most `s` when both sides are. -/
theorem isTemplatePiece_Icc_prod_Icc {a b c e : ℝ} (hab : a < b) (hce : c < e) {s : ℕ}
    (hs : b - a ≤ s ∧ e - c ≤ s) :
    IsTemplatePiece (Icc a b ×ˢ Icc c e) ∧ ediam (Icc a b ×ˢ Icc c e) ≤ s := by
  refine ⟨Or.inl ⟨(a, c), (b - a, 0), (0, e - c), ?_, ?_, by simp, Or.inl rfl,
    Or.inr (Or.inl rfl), ?_⟩, ediam_le fun x hx y hy ↦ ?_⟩
  · simp [Prod.ext_iff, sub_eq_zero, hab.ne']
  · simp [Prod.ext_iff, sub_eq_zero, hce.ne']
  · have : ({(a, c), (a, c) + (b - a, 0), (a, c) + (b - a, 0) + (0, e - c),
        (a, c) + (0, e - c)} : Set (ℝ × ℝ)) = ({a, b} : Set ℝ) ×ˢ ({c, e} : Set ℝ) := by
      ext ⟨x, y⟩
      simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_add_mk, mem_prod, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
      · rintro ⟨rfl | rfl, rfl | rfl⟩ <;> simp
    rw [this, convexHull_prod, convexHull_pair, convexHull_pair, segment_eq_Icc hab.le,
      segment_eq_Icc hce.le]
  · obtain ⟨⟨hx₁, hx₂⟩, hx₃, hx₄⟩ := hx
    obtain ⟨⟨hy₁, hy₂⟩, hy₃, hy₄⟩ := hy
    rw [edist_dist, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff, abs_le, abs_le]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- `dist_∞(T, Z) ≥ c' > c ≥ 0` pointwise gives the frozen clearance `c < dist_∞(T, Z)`. -/
theorem ofReal_lt_ambientEDist {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c < c') {T Z : Finset (ℤ × ℤ)}
    (h : ∀ x ∈ T, ∀ z ∈ Z, c' ≤ dist x z) : ENNReal.ofReal c < ambientEDist T Z :=
  ((ENNReal.ofReal_lt_ofReal_iff (hc.trans_lt hcc')).2 hcc').trans_le <|
    le_iInf₂ fun x hx ↦ le_infEDist.2 fun z hz ↦ by
      rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (h x hx z hz)

/-! ## D11.20 Bounded exceptional set -/

/-- Lattice sites in a closed box of side `L` starting at `c`: at most `(L+1)^d`. -/
theorem card_le_of_mem_box {T : Finset (Fin d → ℤ)} {c : Fin d → ℝ} {L : ℕ}
    (hT : ∀ z ∈ T, ∀ i, c i ≤ z i ∧ (z i : ℝ) ≤ c i + L) : T.card ≤ (L + 1) ^ d := by
  let l : Fin d → ℤ := fun i ↦ ⌈c i⌉
  calc T.card ≤ (Finset.Icc l (l + fun _ ↦ (L : ℤ))).card :=
        Finset.card_le_card fun z hz ↦ Finset.mem_Icc.2 ⟨fun i ↦ Int.ceil_le.2 (hT z hz i).1,
          fun i ↦ by
            have : (z i : ℝ) ≤ (⌈c i⌉ + L : ℤ) := by
              push_cast; linarith [Int.le_ceil (c i), (hT z hz i).2]
            exact_mod_cast this⟩
    _ = (L + 1) ^ d := by simp [Pi.card_Icc, Int.card_Icc, add_sub_right_comm]

/-- D11.20.1. A terminal square of halfside `≤ S_*` (centre `c`) holds `≤ (2S_*+1)^d` lattice
sites; `J` such squares hold `≤ |J|(2S_*+1)^d`. -/
theorem step_11_20_1 (S : ℕ) (J : Finset (Fin d → ℝ)) {T : Finset (Fin d → ℤ)}
    (hT : ∀ z ∈ T, ∃ c ∈ J, dist (latticeSite z) c ≤ S) : T.card ≤ J.card * (2 * S + 1) ^ d := by
  classical
  have hsq (c : Fin d → ℝ) : (T.filter fun z ↦ dist (latticeSite z) c ≤ S).card ≤
      (2 * S + 1) ^ d :=
    card_le_of_mem_box (c := fun i ↦ c i - S) fun z hz i ↦ by
      have := abs_le.1 (((dist_le_pi_dist _ _ i).trans (Finset.mem_filter.1 hz).2).trans_eq'
        (Real.dist_eq _ _).symm)
      simp only [latticeSite] at this
      push_cast; constructor <;> linarith
  calc T.card ≤ (J.biUnion fun c ↦ T.filter fun z ↦ dist (latticeSite z) c ≤ S).card :=
        Finset.card_le_card fun z hz ↦ by
          obtain ⟨c, hc, h⟩ := hT z hz
          exact Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_filter.2 ⟨hz, h⟩⟩
    _ ≤ ∑ c ∈ J, (2 * S + 1) ^ d := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun c _ ↦ hsq c)
    _ = J.card * (2 * S + 1) ^ d := by rw [Finset.sum_const, smul_eq_mul]

/-- D11.20.2. The dummy region `closure N_{k₀}`: `≤ (2C₀+1)^d|Z|` cells of side `2^{k₀}`, so
`≤ (2C₀+1)^d (2^{k₀}+1)^d |Z|` lattice sites. -/
theorem step_11_20_2 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k₀ : ℕ)
    {T : Finset (Fin d → ℤ)} (hT : ∀ z ∈ T, latticeSite z ∈ closure (N o Z C₀ k₀)) :
    T.card ≤ (2 * C₀ + 1) ^ d * (2 ^ k₀ + 1) ^ d * Z.card := by
  classical
  have hcell (w : Fin d → ℤ) : (T.filter fun z ↦ latticeSite z ∈ closure (cell o k₀ w)).card ≤
      (2 ^ k₀ + 1) ^ d :=
    card_le_of_mem_box (c := fun i ↦ o i + 2 ^ k₀ * w i) fun z hz i ↦ by
      have h := (Finset.mem_filter.1 hz).2
      rw [closure_cell, mem_univ_pi] at h
      obtain ⟨h₁, h₂⟩ := h i
      simp only [latticeSite] at h₁ h₂
      push_cast; constructor <;> linarith
  have hN : (NIndex o Z C₀ k₀).card ≤ (2 * C₀ + 1) ^ d * Z.card :=
    Finset.card_biUnion_le.trans <| (Finset.sum_le_sum fun v _ ↦ (by
      rw [Pi.card_Icc, Finset.prod_congr rfl (g := fun _ ↦ 2 * C₀ + 1) fun i _ ↦ by
        simp only [Pi.sub_apply, Pi.add_apply, Int.card_Icc]; omega]
      simp :
        (Finset.Icc (v - fun _ ↦ (C₀ : ℤ)) (v + fun _ ↦ (C₀ : ℤ))).card ≤ (2 * C₀ + 1) ^ d)).trans
      (by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left _ Finset.card_image_le)
  calc T.card ≤ ((NIndex o Z C₀ k₀).biUnion fun w ↦
        T.filter fun z ↦ latticeSite z ∈ closure (cell o k₀ w)).card :=
        Finset.card_le_card fun z hz ↦ by
          have := hT z hz
          rw [N, Finset.closure_biUnion] at this
          obtain ⟨w, hw, h⟩ := mem_iUnion₂.1 this
          exact Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_filter.2 ⟨hz, h⟩⟩
    _ ≤ ∑ w ∈ NIndex o Z C₀ k₀, (2 ^ k₀ + 1) ^ d :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ ↦ hcell w)
    _ ≤ (2 * C₀ + 1) ^ d * (2 ^ k₀ + 1) ^ d * Z.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_right_comm]
        exact Nat.mul_le_mul_right _ hN

open Classical in
/-- D11.20 (`geometry:bad-sites`). `D` := sites of `A` that remain in the dummy region
`closure N_{k₀}` or lie in terminal squares (halfside `≤ S_*`, centres `J`). With `|Z| ≤ 2b`
and `|J| ≤ C'b` (D11.19), `|D| ≤ Cb`, `C = C'(2S_*+1)^d + 2(2C₀+1)^d(2^{k₀}+1)^d`. -/
theorem step_11_20 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k₀ S : ℕ)
    (J : Finset (Fin d → ℝ)) {b C' : ℕ} (hZ : Z.card ≤ 2 * b) (hJ : J.card ≤ C' * b)
    (A : Finset (Fin d → ℤ)) :
    (A.filter fun z ↦ latticeSite z ∈ closure (N o Z C₀ k₀) ∨
        ∃ c ∈ J, dist (latticeSite z) c ≤ S).card ≤
      (C' * (2 * S + 1) ^ d + 2 * (2 * C₀ + 1) ^ d * (2 ^ k₀ + 1) ^ d) * b := by
  rw [Finset.filter_or]
  -- D11.20.3: count ambient sites of `A`; intersecting with `A` only reduces the count
  calc _ ≤ (A.filter fun z ↦ latticeSite z ∈ closure (N o Z C₀ k₀)).card +
        (A.filter fun z ↦ ∃ c ∈ J, dist (latticeSite z) c ≤ S).card := Finset.card_union_le _ _
    _ ≤ (2 * C₀ + 1) ^ d * (2 ^ k₀ + 1) ^ d * Z.card + J.card * (2 * S + 1) ^ d :=
        add_le_add (step_11_20_2 o Z C₀ k₀ fun z hz ↦ (Finset.mem_filter.1 hz).2) -- D11.20.2
          (step_11_20_1 S J fun z hz ↦ (Finset.mem_filter.1 hz).2) -- D11.20.1
    _ ≤ _ := by
        have := Nat.mul_le_mul_left ((2 * C₀ + 1) ^ d * (2 ^ k₀ + 1) ^ d) hZ
        have := Nat.mul_le_mul_right ((2 * S + 1) ^ d) hJ
        nlinarith

/-! ## D11.21–D11.22 Templates of primaries, belt tiles and replacements -/

/-- D11.21.2, D11.22.1–2. The lattice sites `T` of a finite union `⋃_{i∈S} P_i` of template
pieces of sup-diameter `≤ s₀` form a template when `C_tpl |S| (s₀+1) ≤ n` and the union has
sup-diameter `≤ n`. -/
theorem isTemplate_of_biUnion {ι : Type*} (S : Finset ι) (P : ι → Set (ℝ × ℝ))
    {T : Finset (ℤ × ℤ)} (hT : (T : Set (ℤ × ℤ)) = latticePoint ⁻¹' ⋃ i ∈ S, P i)
    (hne : T.Nonempty) {Ctpl : ℝ} {n s₀ : ℕ} (hn : 1 ≤ n) (hs₀ : 1 ≤ s₀)
    (hP : ∀ i ∈ S, IsTemplatePiece (P i) ∧ ediam (P i) ≤ s₀)
    (hN : Ctpl * S.card * (s₀ + 1) ≤ n)
    (hD : ∀ x ∈ ⋃ i ∈ S, P i, ∀ y ∈ ⋃ i ∈ S, P i, dist x y ≤ n) :
    IsTemplate Ctpl n s₀ T := by
  have hmem (z : ℤ × ℤ) (hz : z ∈ T) : latticePoint z ∈ ⋃ i ∈ S, P i := by
    have := Finset.mem_coe.2 hz; rwa [hT] at this
  obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (hmem _ hne.choose_spec)
  let e := S.equivFin
  refine ⟨hn, hs₀, hne, S.card, fun i ↦ P (e.symm i), Finset.card_pos.2 ⟨i, hi⟩,
    fun i ↦ hP _ (e.symm i).2, ?_, hN, ediam_le fun z hz w hw ↦ ?_⟩
  · rw [hT]
    ext z
    simp only [mem_preimage, mem_iUnion]
    exact ⟨fun ⟨i, hi, h⟩ ↦ ⟨e ⟨i, hi⟩, by rw [Equiv.symm_apply_apply]; exact h⟩,
      fun ⟨i, h⟩ ↦ ⟨_, (e.symm i).2, h⟩⟩
  · rw [← isometry_latticePoint.edist_eq, edist_dist, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hD _ (hmem z hz) _ (hmem w hw))

/-- D11.10. A nonempty fragment `closure (C_{k,z} ∩ P_j)` is a closed box `∏ [l_i, u_i]` with
`l_i < u_i ≤ l_i + r`. -/
theorem closure_fragment_eq_pi {o : Fin d → ℝ} {k : ℕ} {a j z : Fin d → ℤ}
    (h : (cell o k z ∩ pitchInterior o k a j).Nonempty) :
    ∃ l u : Fin d → ℝ, closure (cell o k z ∩ pitchInterior o k a j) =
        univ.pi (fun i ↦ Icc (l i) (u i)) ∧ ∀ i, l i < u i ∧ u i - l i ≤ 2 ^ k := by
  rw [cell, pitchInterior, ← pi_inter_distrib] at h ⊢
  refine ⟨fun i ↦ max (o i + 2 ^ k * z i) (o i + t k * a i + s k * j i + t k),
    fun i ↦ min (o i + 2 ^ k * (z i + 1)) (o i + t k * a i + s k * j i + s k), ?_, fun i ↦ ?_⟩
  · rw [closure_pi_set]
    exact pi_congr rfl fun i _ ↦ closure_Ico_inter_Ioo (univ_pi_nonempty_iff.1 h i)
  · obtain ⟨y, ⟨h₁, h₂⟩, h₃, h₄⟩ := univ_pi_nonempty_iff.1 h i
    refine ⟨(max_le h₁ h₃.le).trans_lt (lt_min h₂ h₄), ?_⟩
    have := min_le_left (o i + 2 ^ k * (z i + 1)) (o i + t k * a i + s k * j i + s k)
    have := le_max_left (o i + 2 ^ k * z i) (o i + t k * a i + s k * j i + t k)
    have e : (2 : ℝ) ^ k * (z i + 1) = 2 ^ k * z i + 2 ^ k := by ring
    linarith

/-- D11.21.3. Separation: on `closure D_k`, `dist_∞(·, Z) ≥ C₀r > 4D₀r = 4D₀s₀` because
`C₀ > 100(D₀+1)`. -/
theorem step_11_21_3 {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ} {D₀ : ℝ}
    (hD₀ : 0 ≤ D₀) (hC₀ : 100 * (D₀ + 1) < C₀) :
    4 * D₀ * 2 ^ k < C₀ * 2 ^ k ∧ ∀ x ∈ closure (D o Z C₀ k), ∀ w ∈ Z, C₀ * 2 ^ k ≤ dist x w :=
  ⟨mul_lt_mul_of_pos_right (by linarith) (by positivity), fun _ hx _ hw ↦ step_11_6_4 hx hw⟩

/-- D11.21 (`geometry:primary-scale`). For a primary `j` in layer `k`: `s₀ = r = 2^k`,
`n = ⌈C_P r^{1+2δ₀}⌉`, `T = 𝓑 ∩ ℤ²` for the birth region `𝓑`, `Z = Z_A`. For `C_P ≥ 18 C_tpl`
and `C_P ≥ 1`, `T` is a template (`N₀ ≤ 9r^{2δ₀}`, `n ≥ C_tpl N₀(s₀+1)`,
`diam_∞ T ≤ s_k ≤ n`), and for `C₀ > 100(D₀+1)` it is separated from the cut.
2D only: templates are planar (Definition 9.3, `OpenAI.IsTemplate`). -/
theorem step_11_21 (o : Fin 2 → ℝ) (Λ A : Finset (ℤ × ℤ)) (C₀ k : ℕ) (a j : Fin 2 → ℤ)
    {T : Finset (ℤ × ℤ)}
    (hT : (T : Set (ℤ × ℤ)) = latticePoint ⁻¹' (plane '' birthRegion o (cutSites Λ A) C₀ k a j))
    (hne : T.Nonempty) {CP Ctpl D₀ : ℝ} (hCtpl : 0 ≤ Ctpl) (hCP : 18 * Ctpl ≤ CP) (hCP1 : 1 ≤ CP)
    (hD₀ : 0 ≤ D₀) (hC₀ : 100 * (D₀ + 1) < C₀) :
    IsTemplate Ctpl (primaryScale CP k) (2 ^ k) T ∧ IsSeparatedFromCut D₀ (2 ^ k) Λ A T := by
  classical
  set Z := cutSites Λ A
  set F := fragmentIndex o Z C₀ k a j
  have hB : plane '' birthRegion o Z C₀ k a j =
      ⋃ z ∈ F, plane '' closure (cell o k z ∩ pitchInterior o k a j) := by
    simp only [birthRegion, image_iUnion₂, F]
  -- D11.21.1: `N₀ ≤ (s_k/r+2)² ≤ 9r^{2δ₀}`
  have hN₀ := step_11_21_1 k (C := 1) (N₀ := F.card) zero_le_one (by
    have hdiv : ((s k / 2 ^ k : ℕ) : ℝ) = s k / 2 ^ k := by
      rw [Nat.cast_div (step_11_8.1 k).2.1 (by positivity)]; push_cast; rfl
    calc (F.card : ℝ) ≤ ((s k / 2 ^ k + 2) ^ 2 : ℕ) := by exact_mod_cast step_11_10_2 o Z C₀ k a j
      _ = 1 * ((s k : ℝ) / 2 ^ k + 2) ^ 2 := by rw [Nat.cast_pow, Nat.cast_add, hdiv]; norm_num)
  -- D11.21.2: `C_tpl N₀ (s₀+1) ≤ n` and `s_k ≤ n`
  obtain ⟨hn, hsn⟩ := step_11_21_2 k zero_le_one hCtpl hN₀.2.2 (by linarith) hCP1
  have hbdd : Bornology.IsBounded (birthRegion o Z C₀ k a j) := by
    rw [birthRegion_eq]
    exact (isBounded_Icc _ _).subset (((closure_mono inter_subset_right).trans
      (closure_pitchInterior_subset o k a j)).trans (pi_univ_Icc _ _).subset)
  refine ⟨isTemplate_of_biUnion F _ (hB ▸ hT) hne ((show 1 ≤ s k from Nat.one_le_two_pow).trans hsn)
    Nat.one_le_two_pow (fun z hz ↦ ?_) (by push_cast; exact hn) ?_, ?_⟩
  · obtain ⟨l, u, heq, hlu⟩ := closure_fragment_eq_pi (Finset.mem_filter.1 hz).2
    rw [heq, plane_image_pi_Icc]
    exact isTemplatePiece_Icc_prod_Icc (hlu 0).1 (hlu 1).1
      ⟨by push_cast; exact (hlu 0).2, by push_cast; exact (hlu 1).2⟩
  · -- D11.21.2: `diam_∞ T ≤ s_k ≤ n`
    rw [← hB]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [plane.dist_eq]
    exact (dist_le_diam_of_mem hbdd hx hy).trans
      (((step_11_10 o Z C₀ k a).2.1 j).2.2.2.trans (by exact_mod_cast hsn))
  · -- D11.21.3: `T ⊆ closure D_k`, so `dist_∞(T, Z) ≥ C₀r > 4D₀s₀`
    have h := step_11_21_3 (o := o) (Z := Z) (k := k) hD₀ hC₀
    refine ofReal_lt_ambientEDist (c' := C₀ * 2 ^ k)
      (mul_nonneg (mul_nonneg (by norm_num) hD₀) (Nat.cast_nonneg _)) (by exact_mod_cast h.1)
      fun x hx w hw ↦ ?_
    have hx : plane.symm (latticePoint x) ∈ closure (D o Z C₀ k) := by
      have := Finset.mem_coe.2 hx
      rw [hT, ← IsometryEquiv.preimage_symm, birthRegion_eq] at this
      exact closure_mono inter_subset_left this
    rw [← isometry_plane_symm_latticePoint.dist_eq]
    exact h.2 _ hx _ (Finset.mem_image_of_mem _ hw)

/-- D11.22 (belt tiles and replacements). A union of `N₀ ≤ 8` template pieces of
sup-diameter `≤ s₀ ≤ 2u` inside a square of side `2u` (`u ≥ 1`; belt tile `s₀ = u`,
replacement `s₀ = 2u`) has lattice sites forming a template with `n = ⌈C_B u⌉`, for
`C_B ≥ 24 C_tpl` and `C_B ≥ 2`.
2D only: belt and replacement pieces are planar fan triangles. -/
theorem step_11_22 {CB Ctpl : ℝ} (hCtpl : 0 ≤ Ctpl) (hCB : 24 * Ctpl ≤ CB) (hCB2 : 2 ≤ CB)
    {u s₀ N₀ : ℕ} (hu : 1 ≤ u) (hs₀1 : 1 ≤ s₀) (hs₀ : s₀ ≤ 2 * u) (hN₀ : N₀ ≤ 8)
    (P : Fin N₀ → Set (ℝ × ℝ)) (hP : ∀ i, IsTemplatePiece (P i) ∧ ediam (P i) ≤ s₀)
    (c : ℝ × ℝ) (hc : ∀ i, P i ⊆ closedBall c u) {T : Finset (ℤ × ℤ)}
    (hT : (T : Set (ℤ × ℤ)) = latticePoint ⁻¹' ⋃ i, P i) (hne : T.Nonempty) :
    IsTemplate Ctpl (beltScale CB u) s₀ T := by
  have hn := step_11_22_2 hCB2 u
  refine isTemplate_of_biUnion Finset.univ P (by simpa using hT) hne (by omega) hs₀1
    (fun i _ ↦ hP i) ?_ ?_
  · -- D11.22.1
    rw [Finset.card_univ, Fintype.card_fin]
    exact step_11_22_1 hCtpl hCB hu hN₀ hs₀
  · -- D11.22.2
    intro x hx y hy
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion] at hx hy
    obtain ⟨i, hx⟩ := hx
    obtain ⟨i', hy⟩ := hy
    calc dist x y ≤ dist x c + dist y c := dist_triangle_right x y c
      _ ≤ 2 * u := by linarith [mem_closedBall.1 (hc i hx), mem_closedBall.1 (hc i' hy)]
      _ ≤ beltScale CB u := by exact_mod_cast hn

/-! ## D11.23 Cut clearance of belt and replacement templates -/

/-- D11.23. For all large `k` (`r = 2^k`): a point within `2d(S) ≤ 2t_k^{ρ₀}` of a mark in
`closure D_k` has `dist_∞(·, Z) ≥ (C₀−1)r`, and `(C₀−1)r` exceeds both `4D₀s₀` for side scales
`s₀ ≤ 2t_k` and `2n^β` for scanner scales `n ≤ ⌈C_B t_k⌉`. -/
theorem step_11_23 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) {C₀ : ℕ} (hC₀ : 1 < C₀)
    {D₀ CB : ℝ} (hD₀ : 0 ≤ D₀) (hCB : 0 ≤ CB) :
    ∀ᶠ k in atTop, (∀ m ∈ closure (D o Z C₀ k), ∀ x : Fin d → ℝ,
        dist x m ≤ 2 * (t k : ℝ) ^ ρ₀ → ∀ w ∈ Z, (C₀ - 1) * 2 ^ k ≤ dist x w) ∧
      (∀ s₀ : ℕ, s₀ ≤ 2 * t k → 4 * D₀ * s₀ < (C₀ - 1) * 2 ^ k) ∧
      ∀ n : ℕ, n ≤ beltScale CB (t k) → 2 * (n : ℝ) ^ β < (C₀ - 1) * 2 ^ k := by
  obtain ⟨-, -, -, -, hβρ, hρ1⟩ := eq_exponent_gaps
  have hβ0 : 0 ≤ β := by simp only [β]; norm_num
  have hC : (0 : ℝ) < C₀ - 1 := by
    have : (1 : ℝ) < C₀ := by exact_mod_cast hC₀
    linarith
  -- `t_k = o(r)` (D11.8) and `1 = o(r)`
  have ht := step_11_8.2.1
  have hr := tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2))
  have e₁ := (ht.eventually (gt_mem_nhds (half_pos one_pos)))
  have e₂ := ((ht.const_mul (8 * D₀)).eventually (gt_mem_nhds (by rw [mul_zero]; exact hC)))
  have e₃ := (((ht.const_mul (2 * CB)).add (hr.const_mul 4)).eventually
    (gt_mem_nhds (by rw [mul_zero, mul_zero, add_zero]; exact hC)))
  filter_upwards [e₁, e₂, e₃] with k h₁ h₂ h₃
  simp only [Function.comp] at h₃
  have hr0 : (0 : ℝ) < 2 ^ k := by positivity
  have ht1 : (1 : ℝ) ≤ t k := by unfold t; exact_mod_cast Nat.one_le_two_pow
  rw [div_lt_iff₀ hr0] at h₁
  rw [← mul_div_assoc, div_lt_iff₀ hr0] at h₂
  rw [show 2 * CB * (t k / 2 ^ k) + 4 * ((2 : ℝ) ^ k)⁻¹ = (2 * CB * t k + 4) / 2 ^ k by ring,
    div_lt_iff₀ hr0] at h₃
  have hC' : ((C₀ : ℝ) - 1) * 2 ^ k = C₀ * 2 ^ k - 2 ^ k := by ring
  refine ⟨fun m hm x hxm w hw ↦ ?_, fun s₀ hs₀ ↦ ?_, fun n hn ↦ ?_⟩
  · -- D11.23.1: `dist_∞(m, Z) ≥ C₀r` on `closure D_k`
    have h₄ := step_11_6_4 hm hw
    -- D11.23.2–3: `2t_k^{ρ₀} ≤ 2t_k ≤ r`
    have h₅ : (t k : ℝ) ^ ρ₀ ≤ t k := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 hρ1.le
    linarith [dist_triangle m x w, dist_comm x m]
  · -- D11.23.4: `4D₀s₀ ≤ 8D₀t_k < (C₀−1)r`
    have : (s₀ : ℝ) ≤ 2 * t k := by exact_mod_cast hs₀
    calc 4 * D₀ * s₀ ≤ 4 * D₀ * (2 * t k) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = 8 * D₀ * t k := by ring
      _ < _ := h₂
  · -- D11.23.4: `2n^β ≤ 2(n+1) ≤ 2C_B t_k + 4 < (C₀−1)r`
    have hpow : (n : ℝ) ^ β ≤ 1 + n := by
      rcases le_total (n : ℝ) 1 with h | h
      · linarith [Real.rpow_le_one (Nat.cast_nonneg n) h hβ0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · linarith [(Real.rpow_le_rpow_of_exponent_le h (hβρ.trans hρ1).le).trans_eq
          (Real.rpow_one _)]
    have : (n : ℝ) < CB * t k + 1 :=
      (Nat.cast_le.2 hn).trans_lt (Nat.ceil_lt_add_one (by positivity))
    linarith

/-- D11.23 (Output; Definition 9.3). With `Z = Z_A`, for all large `k`: a template `T` whose
sites lie within `2t_k^{ρ₀}` of marks in `closure D_k`, with side scale `s₀ ≤ 2t_k` and scanner
scale `n ≤ ⌈C_B t_k⌉`, is separated from the cut and has `dist_∞(T, Z) > 2n^β`.
2D only: the frozen clearance `OpenAI.ambientEDist` is on `ℤ × ℤ`. -/
theorem step_11_23_planar (o : Fin 2 → ℝ) (Λ A : Finset (ℤ × ℤ)) {C₀ : ℕ} (hC₀ : 1 < C₀)
    {D₀ CB : ℝ} (hD₀ : 0 ≤ D₀) (hCB : 0 ≤ CB) :
    ∀ᶠ k in atTop, ∀ (T : Finset (ℤ × ℤ)) (s₀ n : ℕ), s₀ ≤ 2 * t k → n ≤ beltScale CB (t k) →
      (∀ x ∈ T, ∃ m ∈ closure (D o (cutSites Λ A) C₀ k),
        dist (plane.symm (latticePoint x)) m ≤ 2 * (t k : ℝ) ^ ρ₀) →
      IsSeparatedFromCut D₀ s₀ Λ A T ∧
        ENNReal.ofReal (2 * (n : ℝ) ^ β) < ambientEDist T (cutEndpoints Λ A) := by
  filter_upwards [step_11_23 o (cutSites Λ A) hC₀ hD₀ hCB] with k ⟨hcl, hs, hn⟩ T s₀ n hs₀ hn₀ hT
  have h : ∀ x ∈ T, ∀ w ∈ cutEndpoints Λ A, (C₀ - 1) * 2 ^ k ≤ dist x w := fun x hx w hw ↦ by
    obtain ⟨m, hm, hxm⟩ := hT x hx
    rw [← isometry_plane_symm_latticePoint.dist_eq]
    exact hcl m hm _ hxm _ (Finset.mem_image_of_mem _ hw)
  exact ⟨ofReal_lt_ambientEDist (mul_nonneg (mul_nonneg (by norm_num) hD₀) (Nat.cast_nonneg _))
    (hs s₀ hs₀) h, ofReal_lt_ambientEDist (by positivity) (hn n hn₀) h⟩

end AreaLaw.Geometry
