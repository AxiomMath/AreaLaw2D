import AreaLaw.S11_Geometry.Layers
import AreaLaw.S11_Geometry.Scales
import Mathlib.Combinatorics.Pigeonhole

/-!
# §11.3 Belt cells and primary tiles

In the layer `D_k` (cell side `r = 2^k`): fine cells of side `t_k`, belt cells selected by one
residue class mod `s_k/t_k` per coordinate, the open pitch interiors between the belt strips,
and the primary tiles, the fragments of `D_k` in one pitch interior. Everything is stated on
`Fin d → ℝ` with its sup metric; counts are in terms of the endpoint set `Z`, `|Z| ≤ 2b`.

Digest `digest/11-geometry.md` D11.8–D11.10.

Some declarations here come from the v1 file `OpenAI/Geometry/PrimaryRegions.lean`, whose header
records it as ported or adapted from `LionSR/TNLean` (see `NOTICE`).
-/

open Set Metric

namespace AreaLaw

namespace Geometry

variable {d : ℕ}

/-! ## D11.8 Fine cells, belt cells, pitch interiors, primary tiles -/

/-- D11.8. Fine cells of layer `k`: side `t_k = 2^⌊ζk⌋`, origin `o`. -/
def fineCell (o : Fin d → ℝ) (k : ℕ) (w : Fin d → ℤ) : Set (Fin d → ℝ) :=
  cell o ⌊ζ * k⌋₊ w

/-- D11.8. The fine cells of `D_k`: the `(r/t_k)^d` fine cells of each `r`-cell of `D_k`. -/
noncomputable def fineIndex (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) :
    Finset (Fin d → ℤ) :=
  (DIndex o Z C₀ k).biUnion fun z ↦ Finset.Icc (fun i ↦ (2 ^ k / t k : ℕ) * z i)
    (fun i ↦ (2 ^ k / t k : ℕ) * z i + (2 ^ k / t k : ℕ) - 1)

/-- D11.8. For residue classes `a_i` mod `s_k/t_k` (one per coordinate), the fine cell `w` is a
belt cell if some index `w_i` lies in its class. -/
def IsBeltCell (k : ℕ) (a w : Fin d → ℤ) : Prop :=
  ∃ i, w i ≡ a i [ZMOD (s k / t k : ℕ)]

noncomputable instance (k : ℕ) (a : Fin d → ℤ) : DecidablePred (IsBeltCell k a) :=
  fun _ ↦ by unfold IsBeltCell; infer_instance

/-- D11.8. The belt cells in `D_k`. -/
noncomputable def beltIndex (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ)
    (a : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (fineIndex o Z C₀ k).filter (IsBeltCell k a)

/-- D11.8. The open pitch interior `j`: the cube of side `s_k − t_k` between successive strips. -/
def pitchInterior (o : Fin d → ℝ) (k : ℕ) (a j : Fin d → ℤ) : Set (Fin d → ℝ) :=
  univ.pi fun i ↦ Ioo (o i + t k * a i + s k * j i + t k) (o i + t k * a i + s k * j i + s k)

/-- D11.8. The primary tile `j` of layer `k`: all fragments of `D_k` in the pitch interior `j`. -/
def primary (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a j : Fin d → ℤ) :
    Set (Fin d → ℝ) :=
  D o Z C₀ k ∩ pitchInterior o k a j

/-- D11.8. The primaries of layer `k`: the pitch interiors meeting `D_k`. -/
def primaries (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a : Fin d → ℤ) :
    Set (Fin d → ℤ) :=
  {j | (primary o Z C₀ k a j).Nonempty}

/-- D11.8. The label of a primary of layer `k`, `k mod 2`. -/
def label (k : ℕ) : ℕ := k % 2

open Classical in
/-- D11.10. The `r`-cells of `D_k` meeting the pitch interior `j`. -/
noncomputable def fragmentIndex (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ)
    (a j : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (DIndex o Z C₀ k).filter fun z ↦ (cell o k z ∩ pitchInterior o k a j).Nonempty

/-- D11.10. The birth region of the primary `j`: the closures of (pitch interior ∩ `r`-cell of
`D_k`). -/
def birthRegion (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a j : Fin d → ℤ) :
    Set (Fin d → ℝ) :=
  ⋃ z ∈ fragmentIndex o Z C₀ k a j, closure (cell o k z ∩ pitchInterior o k a j)

/-! ## Scale bookkeeping -/

/-- `⌊ζk⌋ ≤ k`, `0 < t_k ≤ r ≤ s_k`, `r/t_k = 2^{k-⌊ζk⌋}` and the exact quotients. -/
theorem scale_facts (k : ℕ) :
    ⌊ζ * k⌋₊ ≤ k ∧ 2 ^ k / t k = 2 ^ (k - ⌊ζ * k⌋₊) ∧ (0 : ℝ) < t k ∧ (t k : ℝ) ≤ 2 ^ k ∧
      (2 : ℝ) ^ k ≤ s k ∧ ((2 ^ k / t k : ℕ) : ℝ) = (2 : ℝ) ^ k / (t k : ℝ) ∧
      ((s k / t k : ℕ) : ℝ) = s k / t k ∧ 0 < s k / t k := by
  obtain ⟨htr, hrs, -⟩ := (step_11_8.1 k)
  have ht : 0 < t k := by unfold t; positivity
  have hs : 0 < s k := by unfold s; positivity
  have hℓ : ⌊ζ * k⌋₊ ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 htr
  have hts : t k ≤ s k := Nat.le_of_dvd hs (htr.trans hrs)
  have htr' : t k ≤ 2 ^ k := Nat.le_of_dvd (by positivity) htr
  have hrs' : 2 ^ k ≤ s k := Nat.le_of_dvd hs hrs
  refine ⟨hℓ, Nat.pow_div hℓ two_pos, by exact_mod_cast ht, by exact_mod_cast htr',
    by exact_mod_cast hrs', ?_, ?_, Nat.div_pos hts ht⟩
  · rw [Nat.cast_div htr (by exact_mod_cast ht.ne')]; push_cast; rfl
  · exact Nat.cast_div (htr.trans hrs) (by exact_mod_cast ht.ne')

/-- The index of an `r`-cell from the index of a fine cell: `z_i = ⌊w_i / (r/t_k)⌋`. -/
theorem cellIndex_eq_fine (o : Fin d → ℝ) (k : ℕ) (x : Fin d → ℝ) :
    cellIndex o k x = fun i ↦ cellIndex o ⌊ζ * k⌋₊ x i / (2 ^ k / t k : ℕ) := by
  obtain ⟨hℓ, hR, -⟩ := scale_facts k
  funext i
  have : (x i - o i) / 2 ^ k = (x i - o i) / 2 ^ ⌊ζ * k⌋₊ / ((2 ^ k / t k : ℕ) : ℝ) := by
    rw [hR, div_div]; push_cast; rw [← pow_add, Nat.add_sub_cancel' hℓ]
  simp only [cellIndex, this]
  exact_mod_cast Int.floor_div_natCast _ _

private theorem ediv_eq_iff {R z w : ℤ} (hR : 0 < R) :
    w / R = z ↔ R * z ≤ w ∧ w ≤ R * z + R - 1 := by
  rw [le_antisymm_iff, ← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hR, Int.le_ediv_iff_mul_le hR]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem mem_fineIndex_iff {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ}
    {w : Fin d → ℤ} :
    w ∈ fineIndex o Z C₀ k ↔ (fun i ↦ w i / (2 ^ k / t k : ℕ)) ∈ DIndex o Z C₀ k := by
  have hR : (0 : ℤ) < (2 ^ k / t k : ℕ) := by
    have := (scale_facts k).2.1; rw [this]; positivity
  simp only [fineIndex, Finset.mem_biUnion, Finset.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨z, hz, h₁, h₂⟩
    convert hz using 1
    exact funext fun i ↦ (ediv_eq_iff hR).2 ⟨h₁ i, h₂ i⟩
  · exact fun h ↦ ⟨_, h, fun i ↦ ((ediv_eq_iff hR).1 rfl).1, fun i ↦ ((ediv_eq_iff hR).1 rfl).2⟩

/-- D11.8. Belt cells are disjoint from the pitch interiors: these are the cubes between
successive strips. -/
theorem disjoint_fineCell_pitchInterior {o : Fin d → ℝ} {k : ℕ} {a w : Fin d → ℤ}
    (hw : IsBeltCell k a w) (j : Fin d → ℤ) :
    Disjoint (fineCell o k w) (pitchInterior o k a j) := by
  obtain ⟨-, -, ht, -, -, -, hm, -⟩ := scale_facts k
  obtain ⟨i, hi⟩ := hw
  -- the strip of coordinate `i`: `w_i = a_i + (s_k/t_k) q`
  obtain ⟨q, hq⟩ := hi.symm.dvd
  have hw : (t k : ℝ) * w i = t k * a i + s k * q := by
    rw [show (w i : ℝ) = a i + ((s k / t k : ℕ) : ℤ) * q by exact_mod_cast (by omega),
      Int.cast_natCast, hm]
    field_simp
  have hts : (t k : ℝ) ≤ s k := (scale_facts k).2.2.2.1.trans (scale_facts k).2.2.2.2.1
  rw [Set.disjoint_left]
  intro x hx hp
  have hx := hx i trivial
  have hp := hp i trivial
  rw [show (2 : ℝ) ^ ⌊ζ * k⌋₊ = t k by simp [t]] at hx
  obtain ⟨hx₁, hx₂⟩ := hx; obtain ⟨hp₁, hp₂⟩ := hp
  rcases (show q + 1 ≤ j i ∨ q = j i ∨ j i + 1 ≤ q by omega) with h | h | h
  · have h : (q : ℝ) + 1 ≤ j i := by exact_mod_cast h
    nlinarith
  · subst h; nlinarith
  · have h : (j i : ℝ) + 1 ≤ q := by exact_mod_cast h
    nlinarith

/-! ## D11.9 Few belt cells -/

/-- D11.9.1. `D_k` is the union of its fine cells, and it has `≤ (r/t_k)^d·layerCount d C₀·|Z|`
of them, independent of the shift. -/
theorem step_11_9_1 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) :
    D o Z C₀ k = ⋃ w ∈ fineIndex o Z C₀ k, fineCell o k w ∧
      (fineIndex o Z C₀ k).card ≤ (2 ^ k / t k) ^ d * (layerCount d C₀ * Z.card) := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [D_eq_iUnion, mem_iUnion, mem_cell_iff, fineCell, exists_prop, exists_eq_right',
      mem_fineIndex_iff, cellIndex_eq_fine o k x]
  · -- each `r`-cell is a union of `(r/t_k)^d` fine cells
    calc (fineIndex o Z C₀ k).card ≤ ∑ z ∈ DIndex o Z C₀ k, (2 ^ k / t k) ^ d :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun z _ ↦ by
            simp only [Pi.card_Icc, Int.card_Icc, sub_add_cancel, add_sub_cancel_left,
              Int.toNat_natCast, Finset.prod_const, Finset.card_univ, Fintype.card_fin, le_refl])
      _ ≤ (2 ^ k / t k) ^ d * (layerCount d C₀ * Z.card) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left _ (step_11_6_3 o Z C₀ k)

/-- D11.9.2. Choosing the residue class of each coordinate to be a least-occupied one, a fixed
finite set `F` of fine cells has at most a `d/m` share of belt cells. -/
theorem step_11_9_2 (F : Finset (Fin d → ℤ)) {m : ℕ} (hm : 0 < m) :
    ∃ a : Fin d → ℤ, m * (F.filter fun w ↦ ∃ i, w i ≡ a i [ZMOD m]).card ≤ d * F.card := by
  -- per coordinate, some class `y ∈ [0, m)` holds at most `|F|/m` of the cells
  have h (i : Fin d) : ∃ y, m * (F.filter fun w ↦ w i ≡ y [ZMOD m]).card ≤ F.card := by
    obtain ⟨y, hy, hF⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (s := F)
      (t := Finset.Ico (0 : ℤ) m) (f := fun w ↦ w i % m) (n := F.card / m + 1)
      (by simpa using Nat.lt_mul_div_succ F.card hm)
    obtain ⟨hy₀, hy₁⟩ := Finset.mem_Ico.1 hy
    refine ⟨y, (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ ?_)).trans (Nat.mul_div_le _ _)⟩
    convert hF using 4
    simp [Int.ModEq, Int.emod_eq_of_lt hy₀ hy₁]
  choose a ha using h
  refine ⟨a, ?_⟩
  -- the belt cells are the union over the coordinates
  calc m * (F.filter fun w ↦ ∃ i, w i ≡ a i [ZMOD m]).card
      ≤ m * ∑ i, (F.filter fun w ↦ w i ≡ a i [ZMOD m]).card := by
        refine Nat.mul_le_mul_left _ ((Finset.card_le_card ?_).trans Finset.card_biUnion_le)
        intro w hw
        obtain ⟨hwF, i, hi⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨hwF, hi⟩⟩
    _ ≤ ∑ _i : Fin d, F.card := by rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ ↦ ha i
    _ = d * F.card := by simp

/-- D11.9.3. Some shift achieves at most the mean:
`(s_k/t_k)·#{belt cells in D_k} ≤ d·(r/t_k)^d·layerCount d C₀·|Z|`. -/
theorem step_11_9_3 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) :
    ∃ a : Fin d → ℤ, (s k / t k) * (beltIndex o Z C₀ k a).card ≤
      d * ((2 ^ k / t k) ^ d * (layerCount d C₀ * Z.card)) := by
  obtain ⟨a, ha⟩ := step_11_9_2 (fineIndex o Z C₀ k) (scale_facts k).2.2.2.2.2.2.2
  exact ⟨a, ha.trans (Nat.mul_le_mul_left _ (step_11_9_1 o Z C₀ k).2)⟩

/-- D11.9 (geometry:belt-count). The residue classes can be chosen, layer by layer, with
`#{belt cells in D_k} ≤ C|Z| r²/(s_k t_k) ≤ C|Z| 2^{−kδ₀/2}` (`|Z| ≤ 2b`), here with
`C = 2·layerCount 2 C₀` and `4C`.
2D only: the decay `r^d/(t_k^{d-1}s_k) → 0` of `step_11_9_3` needs `ζ > 1 − δ₀/(d−1)`. -/
theorem step_11_9 (o : Fin 2 → ℝ) (Z : Finset (Fin 2 → ℝ)) (C₀ k : ℕ) :
    ∃ a : Fin 2 → ℤ,
      ((beltIndex o Z C₀ k a).card : ℝ) ≤
        2 * layerCount 2 C₀ * Z.card * (((2 : ℝ) ^ k) ^ 2 / (s k * t k)) ∧
      2 * layerCount 2 C₀ * Z.card * (((2 : ℝ) ^ k) ^ 2 / (s k * t k)) ≤
        8 * layerCount 2 C₀ * Z.card * (2 : ℝ) ^ (-(k * δ₀ / 2)) := by
  obtain ⟨-, -, ht, -, -, hR, hm, -⟩ := scale_facts k
  obtain ⟨a, ha⟩ := step_11_9_3 o Z C₀ k
  refine ⟨a, ?_, ?_⟩
  · -- D11.9.3: the mean is `2|Z|·layerCount·(r/t_k)²/(s_k/t_k) = 2|Z|·layerCount·r²/(s_k t_k)`
    have ha : ((s k / t k : ℕ) : ℝ) * (beltIndex o Z C₀ k a).card ≤
        2 * (((2 ^ k / t k : ℕ) : ℝ) ^ 2 * (layerCount 2 C₀ * Z.card)) := by exact_mod_cast ha
    rw [hm, hR] at ha
    have hs : (0 : ℝ) < s k := by unfold s; positivity
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    field_simp at ha
    nlinarith
  · -- D11.9.4
    have := step_11_9_4 k
    rw [show (8 : ℝ) * layerCount 2 C₀ * Z.card * 2 ^ (-(k * δ₀ / 2)) =
      2 * layerCount 2 C₀ * Z.card * (4 * 2 ^ (-(k * δ₀ / 2))) by ring]
    gcongr

/-! ## D11.10 Primary tiles -/

/-- A point of the pitch interior `j` has pitch index `j_i = ⌊(x_i − o_i − t_k a_i)/s_k⌋`. -/
theorem pitchIndex_eq {o : Fin d → ℝ} {k : ℕ} {a j : Fin d → ℤ} {x : Fin d → ℝ}
    (hx : x ∈ pitchInterior o k a j) (i : Fin d) :
    j i = ⌊(x i - o i - t k * a i) / s k⌋ := by
  have hs : (0 : ℝ) < s k := by unfold s; positivity
  have ht := (scale_facts k).2.2.1
  obtain ⟨h₁, h₂⟩ := hx i trivial
  rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]
  constructor <;> nlinarith

theorem closure_pitchInterior_subset (o : Fin d → ℝ) (k : ℕ) (a j : Fin d → ℤ) :
    closure (pitchInterior o k a j) ⊆
      univ.pi fun i ↦
        Icc (o i + t k * a i + s k * j i + t k) (o i + t k * a i + s k * j i + s k) :=
  closure_minimal (fun _ hx i _ ↦ Ioo_subset_Icc_self (hx i trivial))
    (isClosed_set_pi fun _ _ ↦ isClosed_Icc)

theorem diam_le_of_subset_pi_Icc {S : Set (Fin d → ℝ)} {c : Fin d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hS : S ⊆ univ.pi fun i ↦ Icc (c i) (c i + L)) : diam S ≤ L :=
  diam_le_of_forall_dist_le hL fun x hx y hy ↦ (dist_pi_le_iff hL).2 fun i ↦ by
    obtain ⟨hx₁, hx₂⟩ := hS hx i trivial
    obtain ⟨hy₁, hy₂⟩ := hS hy i trivial
    rw [Real.dist_eq, abs_le]; constructor <;> linarith

theorem closure_Ico_inter_Ioo {a b c e : ℝ} (h : (Ico a b ∩ Ioo c e).Nonempty) :
    closure (Ico a b ∩ Ioo c e) = Icc (max a c) (min b e) := by
  obtain ⟨y, ⟨hay, hyb⟩, hcy, hye⟩ := h
  have hlt : max a c < min b e := (max_le hay hcy.le).trans_lt (lt_min hyb hye)
  refine (closure_minimal ?_ isClosed_Icc).antisymm ?_
  · rintro x ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨max_le h₁ h₃.le, le_min h₂.le h₄.le⟩
  · rw [← closure_Ioo hlt.ne]
    exact closure_mono fun x ⟨h₁, h₂⟩ ↦ ⟨⟨(le_max_left _ _).trans h₁.le,
      h₂.trans_le (min_le_left _ _)⟩, (le_max_right _ _).trans_lt h₁,
      h₂.trans_le (min_le_right _ _)⟩

/-- D11.10.1. Each `r`-cell (`r ≤ s_k`) meets `≤ 2^d` pitch interiors, so there are
`≤ 2^d·layerCount d C₀·|Z|` primaries. -/
theorem step_11_10_1 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a : Fin d → ℤ) :
    (primaries o Z C₀ k a).Finite ∧
      (primaries o Z C₀ k a).ncard ≤ 2 ^ d * (layerCount d C₀ * Z.card) := by
  obtain ⟨-, -, ht, -, hrs, -⟩ := scale_facts k
  have hs : (0 : ℝ) < s k := by unfold s; positivity
  let p (z : Fin d → ℤ) : Fin d → ℤ := fun i ↦ ⌊((2 : ℝ) ^ k * z i - t k * a i) / s k⌋
  have hsub : primaries o Z C₀ k a ⊆
      ↑((DIndex o Z C₀ k).biUnion fun z ↦ Finset.Icc (p z) (p z + 1)) := by
    rintro j ⟨x, hxD, hxP⟩
    rw [D_eq_iUnion] at hxD
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxD
    refine Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_Icc.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩⟩ <;>
      obtain ⟨h₁, h₂⟩ := hxz i trivial <;> rw [pitchIndex_eq hxP i]
    · exact Int.floor_mono (by gcongr; linarith)
    · rw [Pi.add_apply, Pi.one_apply, ← Int.floor_add_one]
      exact Int.floor_mono (by rw [div_add_one hs.ne', div_le_div_iff_of_pos_right hs]; linarith)
  refine ⟨(Finset.finite_toSet _).subset hsub,
    (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_⟩
  rw [Set.ncard_coe_finset]
  calc _ ≤ ∑ z ∈ DIndex o Z C₀ k, 2 ^ d := Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun z _ ↦ by simp [Pi.card_Icc, Int.card_Icc, add_assoc])
    _ ≤ 2 ^ d * (layerCount d C₀ * Z.card) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        exact Nat.mul_le_mul_left _ (step_11_6_3 o Z C₀ k)

/-- D11.10.2. A cube of side `s_k` meets `≤ (s_k/r+2)^d` cells of side `r`: the primary `j` has
`≤ (s_k/r+2)^d` fragments. -/
theorem step_11_10_2 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a j : Fin d → ℤ) :
    (fragmentIndex o Z C₀ k a j).card ≤ (s k / 2 ^ k + 2) ^ d := by
  classical
  obtain ⟨-, -, ht, -, -, -⟩ := scale_facts k
  obtain ⟨N, hN, hN'⟩ : ∃ N : ℕ, s k / 2 ^ k = N ∧ (N : ℝ) * 2 ^ k = s k :=
    ⟨_, rfl, by exact_mod_cast Nat.div_mul_cancel (step_11_8.1 k).2.1⟩
  rw [hN]
  let q : Fin d → ℤ := fun i ↦ ⌊(t k * a i + s k * j i) / (2 : ℝ) ^ k⌋
  have hsub : fragmentIndex o Z C₀ k a j ⊆ Finset.Icc q (q + fun _ ↦ (N : ℤ)) := by
    intro z hz
    obtain ⟨-, x, hxz, hxP⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_Icc.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;>
      obtain ⟨h₁, h₂⟩ := hxz i trivial <;> obtain ⟨h₃, h₄⟩ := hxP i trivial
    · rw [Int.floor_le_iff, div_lt_iff₀ (by positivity)]; nlinarith
    · rw [Pi.add_apply, ← sub_le_iff_le_add, Int.le_floor, le_div_iff₀ (by positivity)]
      push_cast; nlinarith
  calc _ ≤ (Finset.Icc q (q + fun _ ↦ (N : ℤ))).card := Finset.card_le_card hsub
    _ = (N + 1) ^ d := by simp [Pi.card_Icc, Int.card_Icc, add_sub_right_comm]
    _ ≤ (N + 2) ^ d := by gcongr; omega

/-- D11.10. A nonempty fragment `closure (C_{k,z} ∩ P_j)` is a closed rectangle of sup-diameter
`≤ r`. -/
theorem closure_fragment {o : Fin d → ℝ} {k : ℕ} {a j z : Fin d → ℤ}
    (h : (cell o k z ∩ pitchInterior o k a j).Nonempty) :
    ∃ l u : Fin d → ℝ,
      closure (cell o k z ∩ pitchInterior o k a j) = univ.pi (fun i ↦ Icc (l i) (u i)) ∧
        diam (closure (cell o k z ∩ pitchInterior o k a j)) ≤ 2 ^ k := by
  refine ⟨fun i ↦ max (o i + 2 ^ k * z i) (o i + t k * a i + s k * j i + t k),
    fun i ↦ min (o i + 2 ^ k * (z i + 1)) (o i + t k * a i + s k * j i + s k), ?_,
    diam_le_of_subset_pi_Icc (by positivity)
    (((closure_mono inter_subset_left).trans (closure_cell o k z).subset).trans
      fun x hx i _ ↦ ⟨(hx i trivial).1, by linarith [(hx i trivial).2]⟩)⟩
  rw [cell, pitchInterior, ← pi_inter_distrib] at h ⊢
  rw [closure_pi_set]
  exact pi_congr rfl fun i _ ↦ closure_Ico_inter_Ioo (univ_pi_nonempty_iff.1 h i)

/-- D11.10. The birth region of the primary `j` is the closure of the primary tile. -/
theorem birthRegion_eq (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a j : Fin d → ℤ) :
    birthRegion o Z C₀ k a j = closure (primary o Z C₀ k a j) := by
  have : birthRegion o Z C₀ k a j =
      ⋃ z ∈ DIndex o Z C₀ k, closure (cell o k z ∩ pitchInterior o k a j) := by
    ext x
    simp only [birthRegion, fragmentIndex, mem_iUnion, Finset.mem_filter, exists_prop]
    exact ⟨fun ⟨z, ⟨hz, _⟩, hx⟩ ↦ ⟨z, hz, hx⟩,
      fun ⟨z, hz, hx⟩ ↦ ⟨z, ⟨hz, closure_nonempty_iff.1 ⟨x, hx⟩⟩, hx⟩⟩
  rw [this, primary, D_eq_iUnion, iUnion₂_inter, Finset.closure_biUnion]

/-- D11.10.3. Different pitch interiors are separated by a strip of width `t_k`. -/
theorem step_11_10_3 {o : Fin d → ℝ} {Z : Finset (Fin d → ℝ)} {C₀ k : ℕ} {a j j' : Fin d → ℤ}
    (hj : j ≠ j') {x y : Fin d → ℝ} (hx : x ∈ birthRegion o Z C₀ k a j)
    (hy : y ∈ birthRegion o Z C₀ k a j') : (t k : ℝ) ≤ dist x y := by
  have hs : (0 : ℝ) ≤ s k := by positivity
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ j' i := by by_contra! h; exact hj (funext h)
  rw [birthRegion_eq] at hx hy
  obtain ⟨hx₁, hx₂⟩ := closure_pitchInterior_subset o k a j
    (closure_mono inter_subset_right hx) i trivial
  obtain ⟨hy₁, hy₂⟩ := closure_pitchInterior_subset o k a j'
    (closure_mono inter_subset_right hy) i trivial
  refine le_trans ?_ (dist_le_pi_dist x y i)
  rw [Real.dist_eq]
  rcases hi.lt_or_gt with h | h
  · have h : (j i : ℝ) + 1 ≤ j' i := by exact_mod_cast h
    rw [abs_sub_comm]
    exact le_trans (by nlinarith [mul_le_mul_of_nonneg_left h hs]) (le_abs_self _)
  · have h : (j' i : ℝ) + 1 ≤ j i := by exact_mod_cast h
    exact le_trans (by nlinarith [mul_le_mul_of_nonneg_left h hs]) (le_abs_self _)

/-- D11.10 (geometry:primary-pieces).
- At most `2^d·layerCount d C₀·|Z|` primaries per layer (`≤ Cb`, `|Z| ≤ 2b`).
- Birth region of a primary = closures of (pitch interior ∩ `r`-cell of `D_k`): at most
  `(s_k/r+2)^d` closed rectangles of sup-diameter `≤ r`; total sup-diameter `≤ s_k`.
- Distinct primaries of one layer are at distance `≥ t_k` (separated by a belt strip).
- Primaries of adjacent layers have opposite labels; same-label primaries of different layers
  satisfy D11.7. -/
theorem step_11_10 (o : Fin d → ℝ) (Z : Finset (Fin d → ℝ)) (C₀ k : ℕ) (a : Fin d → ℤ) :
    ((primaries o Z C₀ k a).Finite ∧
      (primaries o Z C₀ k a).ncard ≤ 2 ^ d * (layerCount d C₀ * Z.card)) ∧
    (∀ j, birthRegion o Z C₀ k a j = closure (primary o Z C₀ k a j) ∧
      (fragmentIndex o Z C₀ k a j).card ≤ (s k / 2 ^ k + 2) ^ d ∧
      (∀ z ∈ fragmentIndex o Z C₀ k a j, ∃ l u : Fin d → ℝ,
        closure (cell o k z ∩ pitchInterior o k a j) = univ.pi (fun i ↦ Icc (l i) (u i)) ∧
        diam (closure (cell o k z ∩ pitchInterior o k a j)) ≤ 2 ^ k) ∧
      diam (birthRegion o Z C₀ k a j) ≤ s k) ∧
    (∀ j j', j ≠ j' → ∀ x ∈ birthRegion o Z C₀ k a j, ∀ y ∈ birthRegion o Z C₀ k a j',
      (t k : ℝ) ≤ dist x y) ∧
    label (k + 1) ≠ label k ∧
    ∀ h, k < h → label h = label k → ∀ a' j j' : Fin d → ℤ,
      ∀ x ∈ birthRegion o Z C₀ k a j, ∀ y ∈ birthRegion o Z C₀ h a' j',
        ((C₀ : ℝ) - 1) / 2 * 2 ^ h ≤ dist x y := by
  classical
  have ht : (0 : ℝ) ≤ t k := (scale_facts k).2.2.1.le
  refine ⟨step_11_10_1 o Z C₀ k a, fun j ↦ ⟨birthRegion_eq o Z C₀ k a j, step_11_10_2 o Z C₀ k a j,
    fun z hz ↦ closure_fragment (Finset.mem_filter.1 hz).2, ?_⟩,
    fun j j' hj x hx y hy ↦ step_11_10_3 hj hx hy, by simp only [label]; omega,
    fun h hkh hl a' j j' x hx y hy ↦ ?_⟩
  · -- the birth region lies in the closed cube of side `s_k`
    rw [birthRegion_eq]
    exact diam_le_of_subset_pi_Icc (by positivity)
      (((closure_mono inter_subset_right).trans (closure_pitchInterior_subset o k a j)).trans
        fun x hx i _ ↦ ⟨by linarith [(hx i trivial).1], (hx i trivial).2⟩)
  · -- same labels in different layers: `h ≥ k + 2`, D11.7
    rw [birthRegion_eq] at hx hy
    have hkh : k + 2 ≤ h := by simp only [label] at hl; omega
    have := step_11_7 hkh (closure_mono inter_subset_left hx) (closure_mono inter_subset_left hy)
    linarith [this.1, this.2]

end Geometry

end AreaLaw
