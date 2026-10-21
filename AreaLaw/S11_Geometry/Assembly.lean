import AreaLaw.S11_Geometry.Counting

/-! # §11.7 Conclusion of Proposition 11.2

The order of the thresholds (D11.24), the verification of the clauses of Proposition 11.2 for
every retained identifier (D11.25.1–3), and the assembly (D11.25, D11.4).

Digest `digest/11-geometry.md` D11.4, D11.24, D11.25 -/

open Set Metric Filter Topology OpenAI

namespace AreaLaw.Geometry

noncomputable section

/-! ## Templates, cuts and the truncation layer -/

lemma isTemplate_of_le {Ctpl Ctpl' : ℝ} (h : Ctpl ≤ Ctpl') {n s : ℕ} {T : Finset (ℤ × ℤ)}
    (hT : IsTemplate Ctpl' n s T) : IsTemplate Ctpl n s T := by
  obtain ⟨h1, h2, h3, N₀, P, hN, hP, hTe, hn, hd⟩ := hT
  exact ⟨h1, h2, h3, N₀, P, hN, hP, hTe, le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)) (by positivity)) hn, hd⟩

lemma isSeparatedFromCut_of_le {D₀ D₀' : ℝ} (h : D₀ ≤ D₀') {s : ℕ} {Λ A T : Finset (ℤ × ℤ)}
    (hT : IsSeparatedFromCut D₀' s Λ A T) : IsSeparatedFromCut D₀ s Λ A T :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by gcongr)) hT

/-- `|Z| ≤ 2b`. -/
lemma card_cutSites_le (Λ A : Finset (ℤ × ℤ)) :
    (cutSites Λ A).card ≤ 2 * (edgeBoundary Λ A).card := by
  have h₁ := Finset.card_image_le (s := edgeBoundary Λ A) (f := Prod.fst)
  have h₂ := Finset.card_image_le (s := edgeBoundary Λ A) (f := Prod.snd)
  have h₃ := Finset.card_union_le ((edgeBoundary Λ A).image Prod.fst)
    ((edgeBoundary Λ A).image Prod.snd)
  unfold cutSites cutEndpoints
  exact Finset.card_image_le.trans (by omega)

lemma cutSites_nonempty {Λ A : Finset (ℤ × ℤ)} (hb : 0 < (edgeBoundary Λ A).card) :
    (cutSites Λ A).Nonempty := by
  unfold cutSites cutEndpoints
  exact (((Finset.card_pos.1 hb).image Prod.fst).mono Finset.subset_union_left).image _

lemma pt_mem_of_mem_image {B : Set (Fin 2 → ℝ)} {x : ℝ × ℝ} (h : x ∈ plane '' B) : pt x ∈ B := by
  obtain ⟨y, hy, rfl⟩ := h
  simpa [pt] using hy

lemma dist_pt_latticePoint (x y : ℤ × ℤ) :
    dist (pt (latticePoint x)) (pt (latticePoint y)) = dist x y :=
  isometry_plane_symm_latticePoint.dist_eq x y

/-- The lattice sites of a bounded planar set are finitely many. -/
lemma finite_preimage_latticePoint {S : Set (ℝ × ℝ)} (hS : Bornology.IsBounded S) :
    (latticePoint ⁻¹' S).Finite :=
  (isometry_latticePoint.antilipschitz.isBounded_preimage hS).isCompact_closure.finite_of_discrete
    |>.subset subset_closure

/-- D11.23.1. A lattice site within `δ` of a point of `closure D_k` is at sup-distance
`≥ C₀ 2^k - δ` from every cut endpoint. -/
lemma le_dist_cut {Λ A : Finset (ℤ × ℤ)} {C₀ k : ℕ} {m : Fin 2 → ℝ}
    (hm : m ∈ closure (D o₂ (cutSites Λ A) C₀ k)) {x : ℤ × ℤ} {δ : ℝ}
    (hx : dist (pt (latticePoint x)) m ≤ δ) {w : ℤ × ℤ} (hw : w ∈ cutEndpoints Λ A) :
    C₀ * 2 ^ k - δ ≤ dist x w := by
  have h : (C₀ : ℝ) * 2 ^ k ≤ dist m (pt (latticePoint w)) :=
    step_11_6_4 hm (Finset.mem_image_of_mem (fun z ↦ plane.symm (latticePoint z)) hw)
  rw [← dist_pt_latticePoint]
  linarith [dist_triangle m (pt (latticePoint x)) (pt (latticePoint w)),
    dist_comm m (pt (latticePoint x))]

/-- D11.16.3. A lattice site of `N_k` lies in its interior: lattice sites avoid cell edges. -/
lemma mem_interior_N {Z : Finset (Fin 2 → ℝ)} {C₀ k : ℕ} {z : ℤ × ℤ}
    (h : pt (latticePoint z) ∈ N o₂ Z C₀ k) : pt (latticePoint z) ∈ interior (N o₂ Z C₀ k) := by
  set x := pt (latticePoint z)
  set c := cellIndex o₂ k x
  have hU : IsOpen (univ.pi fun i ↦ Ioo (o₂ i + 2 ^ k * c i) (o₂ i + 2 ^ k * (c i + 1))) :=
    isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hc : x ∈ cell o₂ k c := mem_cell_iff.2 rfl
  have hxU : x ∈ univ.pi fun i ↦ Ioo (o₂ i + 2 ^ k * c i) (o₂ i + 2 ^ k * (c i + 1)) := by
    intro i _
    obtain ⟨h₁, h₂⟩ := hc i trivial
    refine ⟨lt_of_le_of_ne h₁ fun e ↦ Layout.pt_latticePoint_ne z i (2 ^ k * c i) ?_, h₂⟩
    change x i - o₂ i = _
    rw [← e]; push_cast; ring
  refine interior_maximal (fun y hy ↦ mem_N_iff.2 ?_) hU hxU
  rw [show cellIndex o₂ k y = c from mem_cell_iff.1 fun i _ ↦ Ioo_subset_Ico_self (hy i trivial)]
  exact mem_N_iff.1 h

/-- The truncation layer: some `K > k₀` has every site of `Λ` inside `N_K`. -/
lemma exists_K (Z : Finset (Fin 2 → ℝ)) (hZ : Z.Nonempty) {C₀ : ℕ} (hC₀ : 2 ≤ C₀) (k₀ : ℕ)
    (Λ : Finset (ℤ × ℤ)) :
    ∃ K, k₀ < K ∧ ∀ z ∈ Λ, pt (latticePoint z) ∈ interior (N o₂ Z C₀ K) := by
  choose f hf using fun z : ℤ × ℤ ↦ step_11_6_2 o₂ Z hZ C₀ hC₀ (pt (latticePoint z))
  have hmono : Monotone (N o₂ Z C₀) := monotone_nat_of_le_succ (step_11_6 o₂ Z hZ C₀ hC₀).1
  refine ⟨k₀ + 1 + Λ.sup f, by omega, fun z hz ↦ mem_interior_N (hmono ?_ (hf z))⟩
  have := Finset.le_sup (f := f) hz
  omega

/-! ## Scales -/

lemma primaryScale_ge {CP : ℝ} (hCP : 1 ≤ CP) (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) ≤ primaryScale CP k ∧ 2 ^ k ≤ primaryScale CP k := by
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hδ : 0 ≤ δ₀ := by norm_num [δ₀]
  have e : ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) ≤ primaryScale CP k :=
    (le_mul_of_one_le_left (by positivity) hCP).trans (Nat.le_ceil _)
  have e' : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) := by
    simpa using Real.rpow_le_rpow_of_exponent_le h1 (by linarith : (1 : ℝ) ≤ 1 + 2 * δ₀)
  exact ⟨e, by exact_mod_cast e'.trans e⟩

lemma rpow_β_le {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ^ β ≤ n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa using Real.rpow_le_rpow_of_exponent_le this (show β ≤ 1 by norm_num [β])

lemma beltScale_lt {CB : ℝ} (hCB : 0 ≤ CB) (u : ℕ) : (beltScale CB u : ℝ) < CB * u + 1 :=
  Nat.ceil_lt_add_one (by positivity)

lemma one_le_t (k : ℕ) : (1 : ℝ) ≤ t k := by rw [t_eq]; exact one_le_pow₀ (by norm_num)

namespace Layout

variable (L : Layout)

/-! ## D11.24 Order of thresholds -/

/-- D11.24 (`geometry:fine-clearance`). Fix in this order: (i) `C₀, C_P, C_B` and the absolute
isolation constant `a₀`; (ii) increase `S_*` until `trim-margins` holds, all belt and replacement
scanner scales are `≥ n_*`, and `c₁u^{ρ₀} > 2⌈C_B u⌉^β` (`u ≥ S_*`); (iii) increase `k₀` so that
initial belt scales exceed `S_*`, primary scales exceed `n_*`, and all large-scale inequalities
used hold: for primaries the same-layer gap `t_k > 2n^β`, non-adjacent-layer gaps, and
`geometry:primary-limits`. Here `a₀ = 1/64` and `c₁ = 1/128`; `S_* ≥ Sstar` and `S_* ≤ t_{k₀}`
are fields of the layout. -/
structure Thresholds (D₀ Ctpl : ℝ) (nStar : ℕ) (CP CB : ℝ) : Prop where
  D₀_nonneg : 0 ≤ D₀
  Ctpl_nonneg : 0 ≤ Ctpl
  CP_ge : 18 * Ctpl ≤ CP
  one_le_CP : 1 ≤ CP
  CB_ge : 24 * Ctpl ≤ CB
  two_le_CB : 2 ≤ CB
  C₀_gt : 100 * (D₀ + 1) < L.C₀
  C₀_gt' : 4 * CB + 16 * D₀ + 8 < L.C₀
  nStar_le : (nStar : ℝ) ≤ L.stopScale
  fine : ∀ u : ℕ, L.stopScale ≤ u →
    2 * (beltScale CB u : ℝ) ^ β < 1 / 128 * (u : ℝ) ^ ρ₀ ∧ collarWidth (beltScale CB u) ≤ u
  layer : ∀ k, L.k₀ ≤ k → nStar ≤ 2 ^ k ∧ (primaryScale CP k : ℝ) ^ β ≤ 1 / 4 * t k ∧
    collarWidth (primaryScale CP k) ≤ 2 ^ k

/-! ## Scales and templates of the identifiers -/

/-- D11.22. The removal halfside `u = d(S)` of a mark, an integer. -/
def half (m : Mark L.marks) : ℕ := ⌊d (L.repair.S m)⌋₊

/-- D11.21, D11.22. The scanner scale `n` of an identifier: `⌈C_P r^{1+2δ₀}⌉` for a primary,
`⌈C_B t_k⌉` for a belt tile, `⌈C_B u⌉` for a replacement of removal halfside `u`. -/
def scale (CP CB : ℝ) : TileId InitId L.marks → ℕ
  | .init (.primary k _) => primaryScale CP k
  | .init (.belt k _ _) => beltScale CB (t k)
  | .init .dummy => 1
  | .init .exterior => 1
  | .repl m _ => beltScale CB (L.half m)

/-- D11.21, D11.22. The side scale `s₀` of an identifier: `r = 2^k` for a primary, `t_k` for a
belt tile, `2u` for a replacement. -/
def side : TileId InitId L.marks → ℕ
  | .init (.primary k _) => 2 ^ k
  | .init (.belt k _ _) => t k
  | .init .dummy => 1
  | .init .exterior => 1
  | .repl m _ => 2 * L.half m

open Classical in
/-- D11.3. The template `T = birth region ∩ ℤ²` of an identifier, as a finite set. -/
def tmpl (a : TileId InitId L.marks) : Finset (ℤ × ℤ) :=
  if h : (L.repair.template a).Finite then h.toFinset else ∅

variable {L}

lemma coe_tmpl {a : TileId InitId L.marks} (h : (L.repair.template a).Finite) :
    (L.tmpl a : Set (ℤ × ℤ)) = L.repair.template a := by
  rw [tmpl, dif_pos h, Set.Finite.coe_toFinset]

lemma mem_tmpl {a : TileId InitId L.marks} (h : (L.repair.template a).Finite) {x : ℤ × ℤ} :
    x ∈ L.tmpl a ↔ latticePoint x ∈ L.repair.birthRegion a := by
  rw [← Finset.mem_coe, coe_tmpl h]; rfl

/-- D11.25. The clauses of Proposition 11.2 for one template `T` of scales `(n, s₀)`. -/
def Clauses (Ctpl D₀ : ℝ) (nStar : ℕ) (Λ A : Finset (ℤ × ℤ)) (n s : ℕ) (T : Finset (ℤ × ℤ)) :
    Prop :=
  nStar ≤ n ∧ IsTemplate Ctpl n s T ∧ IsSeparatedFromCut D₀ s Λ A T ∧ collarWidth n ≤ s ∧
    ENNReal.ofReal (2 * (n : ℝ) ^ β) < ambientEDist T (cutEndpoints Λ A)

variable {D₀ Ctpl : ℝ} {nStar : ℕ} {CP CB : ℝ} (hT : L.Thresholds D₀ Ctpl nStar CP CB)
  {Λ A : Finset (ℤ × ℤ)} (hZ : L.Z = cutSites Λ A)
include hT hZ

/-! ## D11.25.1–3 Primaries -/

/-- D11.21, D11.25.2. A primary `(k, j)` with a lattice site in its birth region: `k₀ ≤ k < K`,
the primary is nonempty, and its template satisfies the clauses of Proposition 11.2
(`n = ⌈C_P r^{1+2δ₀}⌉`, `s₀ = r = 2^k`). -/
theorem step_11_25_2_primary {k : ℕ} {j : Fin 2 → ℤ} {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion (.init (.primary k j))) :
    (k ∈ Finset.Ico L.k₀ L.K ∧ j ∈ primaries o₂ L.Z L.C₀ k (L.a k)) ∧
      (L.repair.template (.init (.primary k j))).Finite ∧
      Clauses Ctpl D₀ nStar Λ A (primaryScale CP k) (2 ^ k) (L.tmpl (.init (.primary k j))) := by
  have htile : L.tile (latticePoint z) = .primary k j := latticePoint_mem_birth₀.1 hz
  obtain ⟨-, hk, hK, -, -⟩ := piece_primary (piece_of_tile_primary htile)
  have htpl := template_primary hk hK j
  have hbdd : Bornology.IsBounded (plane '' birthRegion o₂ L.Z L.C₀ k (L.a k) j) := by
    refine plane.isometry.lipschitz.isBounded_image ?_
    rw [birthRegion_eq]
    exact (isBounded_Icc _ _).subset (((closure_mono inter_subset_right).trans
      (closure_pitchInterior_subset o₂ k (L.a k) j)).trans (pi_univ_Icc _ _).subset)
  have hfin : (L.repair.template (.init (.primary k j))).Finite :=
    htpl ▸ finite_preimage_latticePoint hbdd
  have hT' : (L.tmpl (.init (.primary k j)) : Set (ℤ × ℤ)) =
      latticePoint ⁻¹' (plane '' birthRegion o₂ (cutSites Λ A) L.C₀ k (L.a k) j) := by
    rw [coe_tmpl hfin, htpl, hZ]
  have hzT : z ∈ L.tmpl (.init (.primary k j)) := (mem_tmpl hfin).2 hz
  -- the points of the template lie in the birth region of D11.10
  have hpt : ∀ x ∈ L.tmpl (.init (.primary k j)),
      pt (latticePoint x) ∈ birthRegion o₂ L.Z L.C₀ k (L.a k) j := fun x hx ↦ by
    have : x ∈ (L.tmpl (.init (.primary k j)) : Set (ℤ × ℤ)) := hx
    rw [coe_tmpl hfin, htpl] at this
    exact pt_mem_of_mem_image this
  have hjP : j ∈ primaries o₂ L.Z L.C₀ k (L.a k) := by
    have := hpt z hzT
    rw [birthRegion_eq] at this
    exact closure_nonempty_iff.1 ⟨_, this⟩
  obtain ⟨hn₀, hβ, hcol⟩ := hT.layer k hk
  -- D11.21
  obtain ⟨htmp, hsep⟩ := step_11_21 o₂ Λ A L.C₀ k (L.a k) j hT' ⟨z, hzT⟩ hT.Ctpl_nonneg hT.CP_ge
    hT.one_le_CP hT.D₀_nonneg hT.C₀_gt
  refine ⟨⟨Finset.mem_Ico.2 ⟨hk, hK⟩, hjP⟩, hfin, hn₀.trans (primaryScale_ge hT.one_le_CP k).2,
    htmp, hsep, hcol, ?_⟩
  -- D11.25.2: `dist_∞(T, Z) ≥ C₀r > 2n^β`, with `n^β ≤ t_k/4 ≤ r/4`
  have htr : (t k : ℝ) ≤ 2 ^ k := (scale_facts k).2.2.2.1
  have hC : (1 : ℝ) ≤ L.C₀ := by linarith [hT.C₀_gt, hT.D₀_nonneg]
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  refine ofReal_lt_ambientEDist (c' := L.C₀ * 2 ^ k) (by positivity) (by nlinarith)
    fun x hx w hw ↦ ?_
  have hm : pt (latticePoint x) ∈ closure (D o₂ (cutSites Λ A) L.C₀ k) := by
    have := hpt x hx
    rw [birthRegion_eq, ← hZ] at *
    exact closure_mono inter_subset_left this
  simpa using le_dist_cut hm (le_of_eq (dist_self _)) hw

/-- D11.25.3 (ordered clearance), primaries. Earlier same-label primaries are `≥ t_k > 2n^β`
away in the same layer (D11.10, D11.21); in other layers they are in layers differing by `≥ 2`,
at distance `≥ (C₀-1)/2 · 2^{max(h,k)} > 2n^β` (D11.7). -/
theorem step_11_25_3_primary {k : ℕ} {j : Fin 2 → ℤ} {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion (.init (.primary k j))) :
    ∃ c', 2 * (primaryScale CP k : ℝ) ^ β < c' ∧ ∀ b, L.Ordered b → b ≠ .init (.primary k j) →
      L.rank b ≤ L.rank (.init (.primary k j)) →
      L.repair.label b = L.repair.label (.init (.primary k j)) →
      ∀ x ∈ L.tmpl (.init (.primary k j)), ∀ y : ℤ × ℤ, latticePoint y ∈ L.repair.finalRegion b →
        c' ≤ dist x y := by
  obtain ⟨⟨hkI, -⟩, hfin, -⟩ := step_11_25_2_primary hT hZ hz
  obtain ⟨hk, -⟩ := Finset.mem_Ico.1 hkI
  have ht0 : (0 : ℝ) < t k := (scale_facts k).2.2.1
  have htr : (t k : ℝ) ≤ 2 ^ k := (scale_facts k).2.2.2.1
  have hC : (3 : ℝ) ≤ L.C₀ := by linarith [hT.C₀_gt, hT.D₀_nonneg]
  refine ⟨t k, by linarith [(hT.layer k hk).2.1], fun b hbo hb hr hl x hx y hy ↦ ?_⟩
  have hx' : pt (latticePoint x) ∈ birthRegion o₂ L.Z L.C₀ k (L.a k) j := by
    have : x ∈ (L.tmpl (.init (.primary k j)) : Set (ℤ × ℤ)) := hx
    rw [coe_tmpl hfin, template_primary hk (Finset.mem_Ico.1 hkI).2 j] at this
    exact pt_mem_of_mem_image this
  rw [← dist_pt_latticePoint]
  rcases b with ((_ | _ | ⟨k', j'⟩ | ⟨k', w, c⟩) | ⟨m, c⟩)
  · exact hbo.elim
  · exact hbo.elim
  · -- an earlier primary `(k', j')` of the same label
    have hyb := L.repair.finalRegion_subset_birthRegion _ hy
    have htile : L.tile (latticePoint y) = .primary k' j' := latticePoint_mem_birth₀.1 hyb
    obtain ⟨-, hk', hK', -, -⟩ := piece_primary (piece_of_tile_primary htile)
    have hy' : pt (latticePoint y) ∈ birthRegion o₂ L.Z L.C₀ k' (L.a k') j' := by
      have : y ∈ L.repair.template (.init (.primary k' j')) := hyb
      rw [template_primary hk' hK' j'] at this
      exact pt_mem_of_mem_image this
    have hl' : Geometry.label k' = Geometry.label k := by
      have : (par k').val = (par k).val := congrArg Fin.val hl
      simpa [par, Geometry.label] using this
    have hpow : ∀ {h : ℕ}, k ≤ h → (t k : ℝ) ≤ ((L.C₀ : ℝ) - 1) / 2 * 2 ^ h := fun {h} hh ↦ by
      have : (2 : ℝ) ^ k ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hh
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) h]
    rcases lt_trichotomy k k' with h | rfl | h
    · exact (hpow h.le).trans
        ((step_11_10 o₂ L.Z L.C₀ k (L.a k)).2.2.2.2 k' h hl' (L.a k') j j' _ hx' _ hy')
    · have hjj : j ≠ j' := fun e ↦ hb (by rw [e])
      exact (step_11_10 o₂ L.Z L.C₀ k (L.a k)).2.2.1 j j' hjj _ hx' _ hy'
    · rw [dist_comm]
      exact (hpow le_rfl).trans
        ((step_11_10 o₂ L.Z L.C₀ k' (L.a k')).2.2.2.2 k h hl'.symm (L.a k) j' j _ hy' _ hx')
  · exact absurd hr (by simp [Layout.rank])
  · exact absurd hr (by simp [Layout.rank])

/-! ## D11.25.1–3 Belt tiles -/

/-- D11.22, D11.23, D11.25.2. A belt tile `(k, w, c)` with a lattice site in its birth region:
`k₀ ≤ k < K`, `w` is a belt cell, and its template satisfies the clauses of Proposition 11.2
(`n = ⌈C_B t_k⌉`, `s₀ = t_k`). -/
theorem step_11_25_2_belt {k : ℕ} {w : Fin 2 → ℤ} {c : Fin 2} {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion (.init (.belt k w c))) :
    (k ∈ Finset.Ico L.k₀ L.K ∧ w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k)) ∧
      (L.repair.template (.init (.belt k w c))).Finite ∧
      Clauses Ctpl D₀ nStar Λ A (beltScale CB (t k)) (t k) (L.tmpl (.init (.belt k w c))) := by
  classical
  have hlay : ∀ {x : ℝ × ℝ}, x ∈ L.repair.birth₀ (.belt k w c) → ∀ x' : ℤ × ℤ,
      x = latticePoint x' → pt x ∈ D o₂ L.Z L.C₀ k := by
    rintro x hx x' rfl
    exact mem_D_lev (piece_belt (tile_eq_belt_iff.1 (latticePoint_mem_birth₀.1 hx)).1).1
  have hp := (tile_eq_belt_iff.1 (latticePoint_mem_birth₀.1 hz)).1
  obtain ⟨-, hk, hK, -, -⟩ := piece_belt hp
  have hw := mem_beltIndex_of_piece hp
  have hB := birth₀_belt hw hk hK c
  have hsub := birth₀_belt_subset hw hk hK c
  have hfin : (L.repair.template (.init (.belt k w c))).Finite :=
    finite_preimage_latticePoint (isBounded_closedBall.subset hsub)
  set S := Finset.univ.filter fun j : Fin 8 ↦ L.lab k w (triTable j) = c
  have hTe : (L.tmpl (.init (.belt k w c)) : Set (ℤ × ℤ)) =
      latticePoint ⁻¹' ⋃ i ∈ S, octantTriangle (centre k w) (hs k) i := by
    rw [coe_tmpl hfin]
    change latticePoint ⁻¹' L.repair.birth₀ _ = _
    rw [hB]
    congr 1
    ext x
    simp [S]
  have hzT : z ∈ L.tmpl (.init (.belt k w c)) := (mem_tmpl hfin).2 hz
  have ht1 := one_le_t k
  have ht1' : 1 ≤ t k := by exact_mod_cast ht1
  have htr : (t k : ℝ) ≤ 2 ^ k := (scale_facts k).2.2.2.1
  have hn2 : 2 * t k ≤ beltScale CB (t k) := step_11_22_2 hT.two_le_CB (t k)
  have hn2' : 2 * (t k : ℝ) ≤ beltScale CB (t k) := by exact_mod_cast hn2
  have hhs : hs k ≤ t k := by
    rw [t_eq]; exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hSk : L.stopScale ≤ t k := L.stopScale_le.trans (Layout.t_le_t hk)
  -- D11.22: the template
  have htmp : IsTemplate Ctpl (beltScale CB (t k)) (t k) (L.tmpl (.init (.belt k w c))) := by
    refine isTemplate_of_biUnion S _ hTe ⟨z, hzT⟩ (by omega) ht1' (fun i _ ↦ ?_) ?_ ?_
    · obtain ⟨h₁, h₂⟩ := octantTriangle_isTemplatePiece (centre k w) (hs_pos k) i
      refine ⟨h₁, h₂.trans ?_⟩
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hhs
    · -- D11.22.1
      exact step_11_22_1 hT.Ctpl_nonneg hT.CB_ge ht1' ((Finset.card_filter_le _ _).trans
        (by simp)) (by omega)
    · -- D11.22.2
      intro x hx y hy
      simp only [mem_iUnion] at hx hy
      obtain ⟨i, -, hx⟩ := hx
      obtain ⟨i', -, hy⟩ := hy
      linarith [dist_triangle_right x y (centre k w), mem_closedBall.1 hx.2,
        mem_closedBall.1 hy.2]
  -- D11.23: `dist_∞(T, Z) ≥ C₀r`
  have hcut : ∀ x ∈ L.tmpl (.init (.belt k w c)), ∀ v ∈ cutEndpoints Λ A,
      (L.C₀ : ℝ) * 2 ^ k ≤ dist x v := by
    intro x hx v hv
    have hm : pt (latticePoint x) ∈ closure (D o₂ (cutSites Λ A) L.C₀ k) :=
      hZ ▸ subset_closure (hlay ((mem_tmpl hfin).1 hx) x rfl)
    simpa using le_dist_cut hm (le_of_eq (dist_self _)) hv
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hD₀ := hT.D₀_nonneg
  have hC := hT.C₀_gt'
  have hCB := hT.two_le_CB
  have hnb := beltScale_lt (by linarith) (t k) (CB := CB)
  refine ⟨⟨Finset.mem_Ico.2 ⟨hk, hK⟩, hw⟩, hfin, ?_, htmp, ?_, (hT.fine _ hSk).2, ?_⟩
  · have : (nStar : ℝ) ≤ beltScale CB (t k) := by linarith [hT.nStar_le]
    exact_mod_cast this
  · exact ofReal_lt_ambientEDist (by positivity) (c' := L.C₀ * 2 ^ k) (by nlinarith) hcut
  · have hβ := rpow_β_le (n := beltScale CB (t k)) (by omega)
    exact ofReal_lt_ambientEDist (by positivity) (c' := L.C₀ * 2 ^ k) (by nlinarith) hcut

/-- D11.25.3 (ordered clearance), belt tiles: Lemma 11.5 (`c₁ = 1/128`) and `fine-clearance`. -/
theorem step_11_25_3_belt {k : ℕ} {w : Fin 2 → ℤ} {c : Fin 2} {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion (.init (.belt k w c))) :
    ∃ c', 2 * (beltScale CB (t k) : ℝ) ^ β < c' ∧ ∀ b, L.Ordered b → b ≠ .init (.belt k w c) →
      L.rank b ≤ L.rank (.init (.belt k w c)) →
      L.repair.label b = L.repair.label (.init (.belt k w c)) →
      ∀ x ∈ L.tmpl (.init (.belt k w c)), ∀ y : ℤ × ℤ, latticePoint y ∈ L.repair.finalRegion b →
        c' ≤ dist x y := by
  obtain ⟨⟨hkI, -⟩, hfin, -⟩ := step_11_25_2_belt hT hZ hz
  have hSk : L.stopScale ≤ t k := L.stopScale_le.trans (Layout.t_le_t (Finset.mem_Ico.1 hkI).1)
  refine ⟨1 / 128 * (t k : ℝ) ^ ρ₀, (hT.fine _ hSk).1, fun b _ hb hr hl x hx y hy ↦ ?_⟩
  rcases b with b' | ⟨m, c'⟩
  · -- D11.18: Lemma 11.5, belt half
    have h := step_11_18_belt (k := k) (w := w) (c := c) (b := b') (fun e ↦ hb (by rw [e])) hl
      ((mem_tmpl hfin).1 hx) hy
    rw [← isometry_latticePoint.dist_eq]
    linarith
  · exact absurd hr (by simp [Layout.rank])

/-! ## D11.25.1–3 Replacements -/

omit hT hZ in
lemma half_eq {m : Mark L.marks} (hm : L.repair.IsMark m) :
    (L.half m : ℝ) = d (L.repair.S m) := by
  obtain ⟨n, hn⟩ := L.lemma_11_3.1.exists_d_eq_pow hm
  rw [half, hn, show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]

omit hT hZ in
/-- D11.15.6. The removal square of a mark lies within `2d(S_v)` of its initial mark `v`, and
`d(S_v) ≤ t_k`, `k` the layer of `v`. -/
lemma repl_near {m : Mark L.marks} (hm : L.repair.IsMark m) (c : TileId InitId L.marks) :
    d (L.repair.S m) ≤ 2 * t (L.markLayer m.root) ∧
      L.repair.birthRegion (.repl m c) ⊆ closedBall m.root.1 (2 * t (L.markLayer m.root)) := by
  have hR := L.lemma_11_3.1
  have hdesc : (⟨m.root, []⟩ : Mark L.marks).descend m.path = m := by
    obtain ⟨r, p⟩ := m; simp [Mark.descend]
  have hm' : L.repair.IsMark ((⟨m.root, []⟩ : Mark L.marks).descend m.path) := by
    rw [hdesc]; exact hm
  obtain ⟨h₁, h₂⟩ := (hR.lemma_11_4).2.2.2.1 ⟨m.root, []⟩ m.path hm'
  rw [hdesc] at h₁ h₂
  have hS0 : L.repair.S ⟨m.root, []⟩ = t (L.markLayer m.root) := rfl
  have hv0 : L.repair.v ⟨m.root, []⟩ = m.root.1 := rfl
  rw [hS0, hv0] at h₁ h₂
  have ht0 : (0 : ℝ) < t (L.markLayer m.root) := (scale_facts _).2.2.1
  have hd : d (t (L.markLayer m.root)) ≤ t (L.markLayer m.root) := by
    have := (step_11_14_1 ht0).2
    have h1 := one_le_t (L.markLayer m.root)
    have : (t (L.markLayer m.root) : ℝ) ^ ρ₀ ≤ t (L.markLayer m.root) := by
      simpa using Real.rpow_le_rpow_of_exponent_le h1 ρ₀_le_one
    linarith
  refine ⟨by linarith [dist_nonneg (x := L.repair.v m) (y := m.root.1)], ?_⟩
  exact (h₂ c).trans (closedBall_subset_closedBall (by linarith))

/-- D11.22, D11.23, D11.25.2. A replacement `repl m c` with a lattice site in its birth region:
`m` is an active mark, `c` an identifier of its star, and its template satisfies the clauses of
Proposition 11.2 (`n = ⌈C_B u⌉`, `s₀ = 2u`, `u = d(S)` the removal halfside). -/
theorem step_11_25_2_repl {m : Mark L.marks} {c : TileId InitId L.marks} {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion (.repl m c)) :
    (L.repair.IsMark m ∧ ∃ i, L.repair.markOct m i = c) ∧
      (L.repair.template (.repl m c)).Finite ∧
      Clauses Ctpl D₀ nStar Λ A (beltScale CB (L.half m)) (2 * L.half m) (L.tmpl (.repl m c)) := by
  classical
  obtain ⟨hm, hnt, i, hi, -⟩ := id hz
  have hu := half_eq hm
  have hSu : L.stopScale ≤ L.half m := by rw [hu]; exact hnt
  have hu1 : (1 : ℝ) ≤ L.half m := by
    linarith [((by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _)).trans L.Sstar_le]
  have hu1' : 1 ≤ L.half m := by exact_mod_cast hu1
  set S := Finset.univ.filter fun i : Fin 8 ↦ L.repair.markOct m i = c
  have hB : L.repair.birthRegion (.repl m c) =
      ⋃ i ∈ S, octantTriangle (L.repair.v m) (d (L.repair.S m)) i := by
    ext x
    simp only [Repair.birthRegion, mem_ofPred_eq, mem_iUnion, Finset.mem_filter, S,
      Finset.mem_univ, true_and, exists_prop]
    exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨hm, hnt, h⟩⟩
  have hsub := L.repair.birthRegion_repl_subset m c
  have hfin : (L.repair.template (.repl m c)).Finite :=
    finite_preimage_latticePoint (isBounded_closedBall.subset hsub)
  have hTe : (L.tmpl (.repl m c) : Set (ℤ × ℤ)) =
      latticePoint ⁻¹' ⋃ i ∈ S, octantTriangle (L.repair.v m) (d (L.repair.S m)) i := by
    rw [coe_tmpl hfin, ← hB]; rfl
  have hzT : z ∈ L.tmpl (.repl m c) :=
    (mem_tmpl hfin).2 hz
  have hn2 : 2 * L.half m ≤ beltScale CB (L.half m) := step_11_22_2 hT.two_le_CB _
  have hn2' : 2 * (L.half m : ℝ) ≤ beltScale CB (L.half m) := by exact_mod_cast hn2
  -- D11.22: the template
  have htmp : IsTemplate Ctpl (beltScale CB (L.half m)) (2 * L.half m) (L.tmpl (.repl m c)) := by
    refine isTemplate_of_biUnion S _ hTe ⟨z, hzT⟩ (by omega) (by omega) (fun i _ ↦ ?_) ?_ ?_
    · obtain ⟨h₁, h₂⟩ := octantTriangle_isTemplatePiece (L.repair.v m) (d_pos _) i
      refine ⟨h₁, h₂.trans ?_⟩
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by push_cast; linarith)
    · -- D11.22.1
      exact step_11_22_1 hT.Ctpl_nonneg hT.CB_ge hu1' ((Finset.card_filter_le _ _).trans
        (by simp)) le_rfl
    · -- D11.22.2
      intro x hx y hy
      simp only [mem_iUnion] at hx hy
      obtain ⟨i, -, hx⟩ := hx
      obtain ⟨i', -, hy⟩ := hy
      linarith [dist_triangle_right x y (L.repair.v m), mem_closedBall.1 hx.2,
        mem_closedBall.1 hy.2]
  -- D11.23: within `2t_k` of the initial mark, so `dist_∞(T, Z) ≥ (C₀-2)r`
  set k := L.markLayer m.root
  obtain ⟨-, -, -, -, hDk, -, -, -⟩ := L.mark_facts m.root
  obtain ⟨hdk, hnear⟩ := repl_near hm c
  have htr : (t k : ℝ) ≤ 2 ^ k := (scale_facts k).2.2.2.1
  have hcut : ∀ x ∈ L.tmpl (.repl m c), ∀ v ∈ cutEndpoints Λ A,
      ((L.C₀ : ℝ) - 2) * 2 ^ k ≤ dist x v := by
    intro x hx v hv
    have hx' := mem_closedBall.1 (hnear ((mem_tmpl hfin).1 hx))
    have h := le_dist_cut (hZ ▸ hDk : pt m.root.1 ∈ closure (D o₂ (cutSites Λ A) L.C₀ k))
      (x := x) (δ := 2 * 2 ^ k) (by rw [dist_pt]; linarith) hv
    linarith
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hD₀ := hT.D₀_nonneg
  have hC := hT.C₀_gt'
  have hCB := hT.two_le_CB
  have hnb := beltScale_lt (by linarith) (L.half m) (CB := CB)
  have hu2 : (L.half m : ℝ) ≤ 2 * 2 ^ k := by linarith
  refine ⟨⟨hm, i, hi⟩, hfin, ?_, htmp, ?_, (hT.fine _ hSu).2.trans (by omega), ?_⟩
  · have : (nStar : ℝ) ≤ beltScale CB (L.half m) := by linarith [hT.nStar_le]
    exact_mod_cast this
  · refine ofReal_lt_ambientEDist (by positivity) (c' := (L.C₀ - 2) * 2 ^ k) ?_ hcut
    push_cast
    nlinarith
  · have hβ := rpow_β_le (n := beltScale CB (L.half m)) (by omega)
    refine ofReal_lt_ambientEDist (by positivity) (c' := (L.C₀ - 2) * 2 ^ k) ?_ hcut
    nlinarith

/-- D11.25.3 (ordered clearance), replacements: Lemma 11.5 (`c₁ = 1/128`) and
`fine-clearance`. -/
theorem step_11_25_3_repl {m : Mark L.marks} {c : TileId InitId L.marks} {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion (.repl m c)) :
    ∃ c', 2 * (beltScale CB (L.half m) : ℝ) ^ β < c' ∧ ∀ b, L.Ordered b → b ≠ .repl m c →
      L.rank b ≤ L.rank (.repl m c) → L.repair.label b = L.repair.label (.repl m c) →
      ∀ x ∈ L.tmpl (.repl m c), ∀ y : ℤ × ℤ, latticePoint y ∈ L.repair.finalRegion b →
        c' ≤ dist x y := by
  obtain ⟨⟨hm, -⟩, hfin, -⟩ := step_11_25_2_repl hT hZ hz
  have hnt : L.repair.IsNonterminal m := hz.2.1
  have hu := half_eq hm
  have hSu : L.stopScale ≤ L.half m := by rw [hu]; exact hnt
  refine ⟨1 / 128 * (L.half m : ℝ) ^ ρ₀, (hT.fine _ hSu).1, fun b _ hb hr hl x hx y hy ↦ ?_⟩
  -- D11.18: Lemma 11.5, replacement half, `d(d(S))/2 > d(S)^{ρ₀}/4`
  have h := L.lemma_11_3.1.step_11_18_replacement hm hnt hb hl (birthGen_le_of_rank_le hr)
    ((mem_tmpl hfin).1 hx) hy
  have h₂ := (step_11_14_1 (d_pos (L.repair.S m))).1
  have : 0 ≤ d (L.repair.S m) ^ ρ₀ := Real.rpow_nonneg (d_pos _).le _
  rw [← isometry_latticePoint.dist_eq, hu]
  linarith

/-! ## D11.25.1–3 All identifiers -/

/-- D11.25.1–2. Every identifier in the order whose final region holds a lattice site is
retainable, its template is finite, and it satisfies the clauses of Proposition 11.2. -/
theorem step_11_25_2 {a : TileId InitId L.marks} (ha : L.Ordered a) {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion a) :
    L.Retainable a ∧ (L.repair.template a).Finite ∧
      Clauses Ctpl D₀ nStar Λ A (L.scale CP CB a) (L.side a) (L.tmpl a) := by
  rcases a with ((_ | _ | ⟨k, j⟩ | ⟨k, w, c⟩) | ⟨m, c⟩)
  · exact ha.elim
  · exact ha.elim
  · exact step_11_25_2_primary hT hZ hz
  · obtain ⟨h₁, h₂, h₃⟩ := step_11_25_2_belt hT hZ hz
    exact ⟨h₁, h₂, h₃⟩
  · exact step_11_25_2_repl hT hZ hz

/-- D11.25.3 (`geometry:ordered-clearance`). For every identifier in the order whose final
region holds a lattice site, the template is farther than `2n^β` from the final regions of all
earlier (lower-rank or peer) identifiers of the same label. -/
theorem step_11_25_3 {a : TileId InitId L.marks} (ha : L.Ordered a) {z : ℤ × ℤ}
    (hz : latticePoint z ∈ L.repair.birthRegion a) :
    ∃ c', 2 * (L.scale CP CB a : ℝ) ^ β < c' ∧ ∀ b, L.Ordered b → b ≠ a → L.rank b ≤ L.rank a →
      L.repair.label b = L.repair.label a →
      ∀ x ∈ L.tmpl a, ∀ y : ℤ × ℤ, latticePoint y ∈ L.repair.finalRegion b → c' ≤ dist x y := by
  rcases a with ((_ | _ | ⟨k, j⟩ | ⟨k, w, c⟩) | ⟨m, c⟩)
  · exact ha.elim
  · exact ha.elim
  · exact step_11_25_3_primary hT hZ hz
  · exact step_11_25_3_belt hT hZ hz
  · exact step_11_25_3_repl hT hZ hz


/-! ## D11.25 Conclusion -/

/-- D11.25 (Conclusion of Proposition 11.2). Retain the identifiers whose final actual regions
meet `A`; `X_i` = those intersections, in the order of D11.17. All assertions of
Proposition 11.2 hold; here with the counts `|D| ≤ C₁ b` (D11.20) and `∑ n_i^{-100} ≤ C₂ b`
(D11.25.4) as hypotheses.
2D only: the identifiers, regions and templates of the planar construction. -/
theorem step_11_25 (hA : A ⊆ Λ)
    (hΛ : ∀ z ∈ Λ, pt (latticePoint z) ∈ interior (N o₂ L.Z L.C₀ L.K)) {C₁ C₂ b : ℝ}
    (hDc : ∀ D : Finset (ℤ × ℤ), (∀ z ∈ D, pt (latticePoint z) ∈ closure (N o₂ L.Z L.C₀ L.k₀) ∨
        ∃ m, L.repair.IsMark m ∧ ¬ L.repair.IsNonterminal m ∧
          latticePoint z ∈ ball (L.repair.v m) (d (L.repair.S m))) → (D.card : ℝ) ≤ C₁ * b)
    (hSc : ∀ (F : Finset (TileId InitId L.marks)) (n : TileId InitId L.marks → ℕ),
      (∀ a ∈ F, L.Retainable a ∧ 1 ≤ n a) →
      (∀ k j, TileId.init (.primary k j) ∈ F →
        ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) ≤ n (.init (.primary k j))) →
      ∑ a ∈ F, ((n a : ℝ) ^ 100)⁻¹ ≤ C₂ * b) :
    ∃ (D : Finset (ℤ × ℤ)) (m : ℕ) (X : Fin m → Finset (ℤ × ℤ)) (f : Fin m → Fin 2)
      (T : Fin m → Finset (ℤ × ℤ)) (n s : Fin m → ℕ),
      A = D ∪ Finset.univ.biUnion X ∧ (∀ i, Disjoint D (X i)) ∧
      Pairwise (Function.onFun Disjoint X) ∧ (D.card : ℝ) ≤ C₁ * b ∧
      (∀ i, (X i).Nonempty ∧ X i ⊆ A ∩ T i ∧ nStar ≤ n i ∧
        IsTemplate Ctpl (n i) (s i) (T i) ∧ IsSeparatedFromCut D₀ (s i) Λ A (T i) ∧
        collarWidth (n i) ≤ s i ∧
        ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
          ambientEDist (T i) (cutEndpoints Λ A) ∧
        ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
          ambientEDist (T i) ((Finset.univ.filter fun j => j < i ∧ f j = f i).biUnion X)) ∧
      ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C₂ * b := by
  classical
  have hR := L.lemma_11_3.1
  have hL := L.lemma_11_3.2
  -- D11.25.1: the retained identifiers, finitely many (one per site of `A` at most, D11.16)
  let g : ℤ × ℤ → TileId InitId L.marks := fun z ↦
    if h : ∃ a, latticePoint z ∈ L.repair.finalRegion a then h.choose else .init .dummy
  let F := (A.image g).filter fun a ↦
    L.Ordered a ∧ ∃ z ∈ A, latticePoint z ∈ L.repair.finalRegion a
  have hmemF : ∀ a, a ∈ F ↔ L.Ordered a ∧ ∃ z ∈ A, latticePoint z ∈ L.repair.finalRegion a := by
    intro a
    refine ⟨fun h ↦ (Finset.mem_filter.1 h).2, fun ⟨ho, z, hz, hza⟩ ↦
      Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨z, hz, ?_⟩, ho, z, hz, hza⟩⟩
    have h : ∃ a, latticePoint z ∈ L.repair.finalRegion a := ⟨a, hza⟩
    simp only [g, dif_pos h]
    exact hR.step_11_16_unique hL h.choose_spec hza
  -- D11.17: the order
  let _ : LinearOrder (TileId InitId L.marks) := L.order
  let e := F.orderIsoOfFin rfl
  let ids : Fin F.card → TileId InitId L.marks := fun i ↦ (e i).1
  have hinj : ∀ i j, ids i = ids j → i = j := fun i j h ↦ e.injective (Subtype.ext h)
  have hmono : ∀ i j, i < j → L.rank (ids i) ≤ L.rank (ids j) := by
    intro i j hij
    by_contra h
    push Not at h
    exact lt_asymm (order_lt_of_rank_lt h : ids j < ids i) (e.strictMono hij)
  have hord : ∀ i, L.Ordered (ids i) := fun i ↦ ((hmemF _).1 (e i).2).1
  have hspec : ∀ i, ∃ z ∈ A, latticePoint z ∈ L.repair.finalRegion (ids i) :=
    fun i ↦ ((hmemF _).1 (e i).2).2
  let X : Fin F.card → Finset (ℤ × ℤ) := fun i ↦
    A.filter fun z ↦ latticePoint z ∈ L.repair.finalRegion (ids i)
  have hmemX : ∀ i z, z ∈ X i ↔ z ∈ A ∧ latticePoint z ∈ L.repair.finalRegion (ids i) :=
    fun i z ↦ Finset.mem_filter
  have hXA : Finset.univ.biUnion X ⊆ A := fun z hz ↦ by
    obtain ⟨i, -, hzi⟩ := Finset.mem_biUnion.1 hz
    exact ((hmemX i z).1 hzi).1
  refine ⟨A \ Finset.univ.biUnion X, F.card, X, fun i ↦ L.repair.label (ids i),
    fun i ↦ L.tmpl (ids i), fun i ↦ L.scale CP CB (ids i), fun i ↦ L.side (ids i),
    (Finset.sdiff_union_of_subset hXA).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.disjoint_left.2 fun z hz hzX ↦
      (Finset.mem_sdiff.1 hz).2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hzX⟩)
  · intro i j hij
    exact Finset.disjoint_left.2 fun z hzi hzj ↦ hij (hinj i j
      (hR.step_11_16_unique hL ((hmemX i z).1 hzi).2 ((hmemX j z).1 hzj).2))
  · -- D11.20: the remaining sites are dummy sites or in terminal squares (D11.16)
    refine hDc _ fun z hz ↦ ?_
    obtain ⟨hzA, hzX⟩ := Finset.mem_sdiff.1 hz
    rcases hR.step_11_16_cover hL z with ⟨a, ha⟩ | ⟨m, hm, hnt, hball⟩
    · left
      by_cases ho : L.Ordered a
      · exfalso
        have haF : a ∈ F := (hmemF a).2 ⟨ho, z, hzA, ha⟩
        refine hzX (Finset.mem_biUnion.2 ⟨e.symm ⟨a, haF⟩, Finset.mem_univ _,
          (hmemX _ z).2 ⟨hzA, ?_⟩⟩)
        rw [show ids (e.symm ⟨a, haF⟩) = a from congrArg Subtype.val (e.apply_symm_apply _)]
        exact ha
      · have hb := L.repair.finalRegion_subset_birthRegion _ ha
        rcases a with ((_ | _ | _ | _) | _)
        · exact pt_mem_of_mem_image (birth₀_dummy_subset hb)
        · exact (birth₀_exterior_subset hb ⟨_, hΛ z (hA hzA), plane.apply_symm_apply _⟩).elim
        all_goals exact (ho trivial).elim
    · exact Or.inr ⟨m, hm, hnt, hball⟩
  · intro i
    obtain ⟨z, hzA, hz⟩ := hspec i
    have hzb := L.repair.finalRegion_subset_birthRegion _ hz
    obtain ⟨-, hfin, hn, htmp, hsep, hcol, hcut⟩ := step_11_25_2 hT hZ (hord i) hzb
    obtain ⟨c', hc', hsep'⟩ := step_11_25_3 hT hZ (hord i) hzb
    refine ⟨⟨z, (hmemX i z).2 ⟨hzA, hz⟩⟩, fun y hy ↦ ?_, hn, htmp, hsep, hcol, hcut, ?_⟩
    · obtain ⟨hyA, hy⟩ := (hmemX i y).1 hy
      exact Finset.mem_inter.2
        ⟨hyA, (mem_tmpl hfin).2 (L.repair.finalRegion_subset_birthRegion _ hy)⟩
    · -- D11.25.3: restricting an older actual region to `A` keeps the lower bounds
      refine ofReal_lt_ambientEDist (by positivity) hc' fun x hx y hy ↦ ?_
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hji, hf⟩ := (Finset.mem_filter.1 hj).2
      exact hsep' (ids j) (hord j) (fun h ↦ hji.ne (hinj j i h)) (hmono j i hji) hf x hx y
        ((hmemX j y).1 hyj).2
  · -- D11.25.4
    have hF : ∀ a ∈ F, L.Retainable a ∧ 1 ≤ L.scale CP CB a := by
      intro a ha
      obtain ⟨ho, z, -, hz⟩ := (hmemF a).1 ha
      obtain ⟨hret, -, -, htmp, -⟩ :=
        step_11_25_2 hT hZ ho (L.repair.finalRegion_subset_birthRegion _ hz)
      exact ⟨hret, htmp.1⟩
    calc ∑ i, ((L.scale CP CB (ids i) : ℝ) ^ 100)⁻¹ =
          ∑ a ∈ F, ((L.scale CP CB a : ℝ) ^ 100)⁻¹ := by
          rw [← Finset.sum_coe_sort F]
          exact Equiv.sum_comp e.toEquiv (fun a : F ↦ ((L.scale CP CB a.1 : ℝ) ^ 100)⁻¹)
      _ ≤ C₂ * b := hSc F _ hF fun k j _ ↦ (primaryScale_ge hT.one_le_CP k).1

end Layout

/-! ## D11.4 Proposition 11.2 -/

/-- D11.4 **Proposition 11.2** (two families with separated birth templates). Fix `D₀, C_tpl` of
Def 9.3 and a threshold `n_* ≥ 1`. There is `C` (depending on these and `n_*` only) such that:
for every finite induced subgraph `Λ` of `ℤ²`, `A ⊆ Λ`, `b = |∂_Λ A| > 0`, `Z` = endpoints of
cut edges, there are `D ⊆ A`, a finite ordered collection of disjoint nonempty `X_i ⊆ A`, labels
`f_i ∈ {0,1}`, ambient templates `T_i ⊂ ℤ²`, integers `n_i ≥ n_*` with
1. `A = D ∪̇ ⋃_i X_i`, `|D| ≤ Cb`.
2. `X_i ⊆ A ∩ T_i`; `T_i` is a template of Def 9.3 (union of `N_i` lattice samples of closed
   convex rectangles/triangles with side slopes `0, ∞, 1, -1`, each of sup-diameter `≤ s_i`)
   with `diam_∞ T_i ≤ n_i`, `n_i ≥ C_tpl N_i(s_i+1)`, `dist_∞(T_i, Z) > 4D₀s_i`; and
   `L_i = ⌊n_i^{1-ℓ}⌋ ≤ s_i`.
3. `dist_∞(T_i, Z) > 2n_i^β` (`geometry:cut-clearance`) and
   `dist_∞(T_i, ⋃_{j<i, f_j=f_i} X_j) > 2n_i^β` (`geometry:ordered-clearance`); distance to `∅`
   is `∞`.
4. `∑_i n_i^{-100} ≤ Cb`.
2D only: planar layers, belts, stars and templates (Definition 9.3 is planar). -/
theorem prop_11_2 : TwoFamilyDecomposition := by
  intro D₀ Ctpl nStar _
  -- D11.24 (i): `C₀, C_P, C_B`; `a₀ = 1/64`, `c₁ = 1/128`
  set D₀' := max D₀ 0
  set Ctpl' := max Ctpl 0
  set CP : ℝ := max (18 * Ctpl') 1
  set CB : ℝ := max (24 * Ctpl') 2
  set C₀ : ℕ := ⌈100 * (D₀' + 1) + 4 * CB + 16 * D₀' + 8⌉₊ + 1
  have hD₀' : 0 ≤ D₀' := le_max_right _ _
  have hCtpl' : 0 ≤ Ctpl' := le_max_right _ _
  have hCP0 : 0 ≤ CP := zero_le_one.trans (le_max_right _ _)
  have hCB2 : 2 ≤ CB := le_max_right _ _
  have hCB0 : 0 ≤ CB := by linarith
  have hC₀ : 100 * (D₀' + 1) + 4 * CB + 16 * D₀' + 8 < (C₀ : ℝ) := by
    have := Nat.le_ceil (100 * (D₀' + 1) + 4 * CB + 16 * D₀' + 8)
    push_cast [C₀]; linarith
  have hC₀2 : 2 ≤ C₀ := by
    have : (2 : ℝ) < C₀ := by linarith
    exact_mod_cast this.le
  -- D11.24 (ii): `S_*` with the trim margins, `n_*` and `fine-clearance`
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    ((step_11_24 hCB0 (c₁ := 1 / 128) (by norm_num)).and (step_11_22_3 hCB0 one_pos))
  set S_star : ℝ := max (max Sstar nStar) N₁
  have hSstar : Sstar ≤ S_star := (le_max_left _ _).trans (le_max_left _ _)
  have h4 : (4 : ℝ) ≤ Sstar := le_max_left _ _
  have hS1 : 1 < S_star := by linarith
  -- D11.24 (iii): `k₀` with `t_{k₀} ≥ S_*`, `2^k ≥ n_*` and the primary limits
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt S_star (by norm_num : (1 : ℝ) < 2)
  have hζ : 0 < ζ := by norm_num [ζ, δ₀]
  have ht : ∀ᶠ k : ℕ in atTop, S_star ≤ t k := by
    filter_upwards [eventually_ge_atTop ⌈(n₀ : ℝ) / ζ⌉₊] with k hk
    have h1 : (n₀ : ℝ) ≤ ζ * k := by
      have := Nat.ceil_le.1 hk
      rw [div_le_iff₀ hζ] at this
      linarith
    rw [t_eq]
    exact hn₀.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_floor h1))
  have hpr := step_11_21_4 hCP0 (c := 1 / 4) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (((hpr.2.1.and hpr.2.2.2).and ht).and (eventually_ge_atTop nStar))
  -- the counting constants (D11.19, D11.20, D11.25.4)
  obtain ⟨C₁, hC₁0, hC₁⟩ := step_11_20_count C₀ k₀ hS1
  obtain ⟨C₂, hC₂0, hC₂⟩ := step_11_25_4_count C₀ hS1
  refine ⟨C₁ + 2 * C₂, fun Λ A hA hb ↦ ?_⟩
  have hZne := cutSites_nonempty hb
  obtain ⟨K, hK, hΛ⟩ := exists_K (cutSites Λ A) hZne hC₀2 k₀ Λ
  -- the layout: `Z = Z_A`, the shifts of D11.9, the truncation layer `K`
  let L : Layout :=
    { Z := cutSites Λ A, C₀ := C₀, k₀ := k₀, K := K
      a := fun k ↦ (step_11_9 o₂ (cutSites Λ A) C₀ k).choose
      Z_nonempty := hZne, two_le_C₀ := hC₀2, lt_K := hK, stopScale := S_star
      Sstar_le := hSstar, stopScale_le := (hk₀ k₀ le_rfl).1.2 }
  have hsp : L.BeltSparse := fun k ↦ (step_11_9 o₂ (cutSites Λ A) C₀ k).choose_spec.1.trans
    (step_11_9 o₂ (cutSites Λ A) C₀ k).choose_spec.2
  have hT : L.Thresholds D₀' Ctpl' nStar CP CB :=
    { D₀_nonneg := hD₀', Ctpl_nonneg := hCtpl', CP_ge := le_max_left _ _
      one_le_CP := le_max_right _ _, CB_ge := le_max_left _ _, two_le_CB := hCB2
      C₀_gt := by change _ < (C₀ : ℝ); linarith
      C₀_gt' := by change _ < (C₀ : ℝ); linarith
      nStar_le := (le_max_right _ _).trans (le_max_left _ _)
      fine := fun u hu ↦ by
        have hN : N₁ ≤ u := by
          exact_mod_cast (le_max_right _ _ : (N₁ : ℝ) ≤ S_star).trans hu
        obtain ⟨h₁, h₂⟩ := hN₁ u hN
        refine ⟨h₁, ?_⟩
        change ⌊(beltScale CB u : ℝ) ^ (1 - ℓ)⌋₊ ≤ u
        rw [one_mul] at h₂
        exact_mod_cast h₂
      layer := fun k hk ↦ by
        obtain ⟨⟨⟨h₁, h₂⟩, -⟩, h₃⟩ := hk₀ k hk
        exact ⟨h₃.trans Nat.lt_two_pow_self.le, h₁, h₂⟩ }
  have hZb : (cutSites Λ A).card ≤ 2 * (edgeBoundary Λ A).card := card_cutSites_le Λ A
  have hZb' : ((cutSites Λ A).card : ℝ) ≤ 2 * (edgeBoundary Λ A).card := by exact_mod_cast hZb
  have hb0 : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  -- D11.25
  obtain ⟨D, m, X, f, T, n, s, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    Layout.step_11_25 hT (Λ := Λ) (A := A) rfl hA hΛ (C₁ := C₁) (C₂ := 2 * C₂)
      (b := (edgeBoundary Λ A).card) (fun D hD ↦ hC₁ L rfl rfl rfl hsp _ hZb D hD)
      (fun F n hF hFp ↦ (hC₂ L rfl rfl hsp F n hF hFp).trans (by
        change C₂ * ((cutSites Λ A).card : ℝ) ≤ _
        nlinarith))
  refine ⟨D, m, X, f, T, n, s, h₁, h₂, h₃, h₄.trans (by nlinarith), fun i ↦ ?_,
    h₆.trans (by nlinarith)⟩
  obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩ := h₅ i
  exact ⟨g₁, g₂, g₃, isTemplate_of_le (le_max_left _ _) g₄,
    isSeparatedFromCut_of_le (le_max_left _ _) g₅, g₆, g₇, g₈⟩

end

end AreaLaw.Geometry
