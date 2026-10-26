import AreaLaw.S03_InitialBox.MarginalTails

/-!
# §3.2 An entropy discount from a buffer

Digest `digest/03-initial-box.md` (D3.3–D3.14), paper `paper/sections/02-initial.tex`,
lines 219–586.

Some declarations here come from the v1 files `OpenAI/Geometry/TemplateCollar.lean`,
`OpenAI/LogClipping.lean`, `OpenAI/Rectangles.lean`, whose header records them as ported or adapted
from `LionSR/QICLean` and `LionSR/TNLean` (see `NOTICE`).
-/

namespace AreaLaw

open Arealaw OpenAI Finset

/-! ## D3.3 Safe rectangles, size, buffers

D3.3. An integer rectangle is `OpenAI.IsIntRect Q` (`Q = [a, b]`), its size `OpenAI.boxSize Q`,
`Q` is safe iff `OpenAI.IsSafe D₀ Λ A Q`: `dist_∞(Q, Z_A) > D₀ size(Q)`, `dist_∞(Q, ∅) = ∞`;
`Q^{+d}` is `OpenAI.ambientDilation Q d`. These are frozen in `OpenAI/Statements.lean`. -/

section D33

variable {a b : ℤ × ℤ} {Q T : Finset (ℤ × ℤ)} {D₀ : ℝ} {Λ A : Finset (ℤ × ℤ)}

theorem boxSize_Icc (h : a ≤ b) :
    boxSize (Icc a b) = max (b.1 + 1 - a.1).toNat (b.2 + 1 - a.2).toNat := by
  rw [boxSize, Icc_prod_def, product_image_fst (nonempty_Icc.2 h.2),
    product_image_snd (nonempty_Icc.2 h.1), Int.card_Icc, Int.card_Icc]

theorem boxSize_mono (h : Q ⊆ T) : boxSize Q ≤ boxSize T :=
  max_le_max (card_le_card (image_subset_image h)) (card_le_card (image_subset_image h))

theorem card_le_boxSize_sq (Q : Finset (ℤ × ℤ)) : #Q ≤ boxSize Q ^ 2 :=
  (card_le_card subset_product).trans <| by
    rw [card_product, sq]
    exact Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)

theorem mem_ambientDilation {y : ℤ × ℤ} {j : ℕ} :
    y ∈ ambientDilation T j ↔ ∃ x ∈ T, |y.1 - x.1| ≤ j ∧ |y.2 - x.2| ≤ j := by
  simp only [ambientDilation, mem_add, mem_Icc]
  constructor
  · rintro ⟨x, hx, z, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    refine ⟨x, hx, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, abs_le] <;> omega
  · rintro ⟨x, hx, h1, h2⟩
    rw [abs_le] at h1 h2
    exact ⟨x, hx, y - x, ⟨⟨by simp; omega, by simp; omega⟩, by simp; omega, by simp; omega⟩,
      add_sub_cancel x y⟩

/-- A subset of a safe set is safe (`D₀ ≥ 0`). -/
theorem IsSafe.subset' (hs : IsSafe D₀ Λ A Q) (hD₀ : 0 ≤ D₀) (h : T ⊆ Q) : IsSafe D₀ Λ A T :=
  ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Nat.cast_le.2 (boxSize_mono h)) hD₀)).trans_lt hs).trans_le
      (by simp only [ambientEDist]; exact biInf_mono fun x hx => h hx)

end D33

/-! ## D3.5–D3.6 parameters `m`, `d_j` and harmonic weights -/

section D36

/-- D3.5. `m = ⌊(C_pad - 1) r / D⌋`. -/
def m (Cpad r D : ℕ) : ℕ := (Cpad - 1) * r / D

/-- D3.5. `d_j = r + j D`. -/
def d (r D j : ℕ) : ℕ := r + j * D

/-- D3.6. `Z_r = ∑_{j=1}^m 1/(r + d_j)`. -/
noncomputable def harmonicSum (Cpad r D : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (m Cpad r D), 1 / ((r + d r D j : ℕ) : ℝ)

/-- D3.6. `a_j = 2 / (Z_r (r + d_j))`. -/
noncomputable def a (Cpad r D j : ℕ) : ℝ := 2 / (harmonicSum Cpad r D * (r + d r D j : ℕ))

/-- D3.6. `ℰ = ∑_j (r + d_j) a_j²`. -/
noncomputable def ℰ (Cpad r D : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (m Cpad r D), ((r + d r D j : ℕ) : ℝ) * a Cpad r D j ^ 2

variable {Cpad r D : ℕ}

/-- D3.6 (eq:initial-harmonic-weights, eq:initial-harmonic-lower). `∑_j a_j = 2`, `ℰ = 4/Z_r`,
`ℰ = min{∑_j (r + d_j) b_j² : ∑_j b_j = 2}`, and `Z_r ≥ (1/D) log((C_pad + 1)/(2 + D))`. -/
theorem eq_initial_harmonic_weights (hD : 0 < D) (hC : D + 1 < Cpad) (hr : 1 ≤ r) :
    ∑ j ∈ Icc 1 (m Cpad r D), a Cpad r D j = 2 ∧ ℰ Cpad r D = 4 / harmonicSum Cpad r D ∧
    (∀ b : ℕ → ℝ, ∑ j ∈ Icc 1 (m Cpad r D), b j = 2 →
      ℰ Cpad r D ≤ ∑ j ∈ Icc 1 (m Cpad r D), ((r + d r D j : ℕ) : ℝ) * b j ^ 2) ∧
    1 / D * Real.log ((Cpad + 1) / (2 + D)) ≤ harmonicSum Cpad r D := by
  have hm : 1 ≤ m Cpad r D := (Nat.le_div_iff_mul_le hD).2 (by
    rw [one_mul]; exact (show D ≤ Cpad - 1 by omega).trans (Nat.le_mul_of_pos_right _ hr))
  have hc : ∀ j, (0 : ℝ) < ((r + d r D j : ℕ) : ℝ) := fun j => by unfold d; positivity
  have hZ : 0 < harmonicSum Cpad r D :=
    sum_pos (fun j _ => one_div_pos.2 (hc j)) ⟨1, mem_Icc.2 ⟨le_rfl, hm⟩⟩
  -- D3.6.1
  have ha : ∀ j, a Cpad r D j = 2 / harmonicSum Cpad r D * (1 / ((r + d r D j : ℕ) : ℝ)) :=
    fun j => by
    simp only [a]; field_simp
  have hE : ∀ j, ((r + d r D j : ℕ) : ℝ) * a Cpad r D j ^ 2 =
      4 / harmonicSum Cpad r D ^ 2 * (1 / ((r + d r D j : ℕ) : ℝ)) := fun j => by
    simp only [a]; field_simp [(hc j).ne']; ring
  have h1 : ∑ j ∈ Icc 1 (m Cpad r D), a Cpad r D j = 2 := by
    simp only [ha, ← mul_sum]; rw [← harmonicSum]; field_simp
  have h2 : ℰ Cpad r D = 4 / harmonicSum Cpad r D := by
    simp only [ℰ, hE, ← mul_sum]; rw [← harmonicSum]; field_simp
  refine ⟨h1, h2, fun b hb => ?_, ?_⟩
  · -- D3.6.1: Cauchy–Schwarz, `4 = (∑ b)² ≤ (∑ (r + d_j) b_j²)(∑ 1/(r + d_j))`
    have := sq_sum_div_le_sum_sq_div (Icc 1 (m Cpad r D)) b fun j _ => one_div_pos.2 (hc j)
    rw [hb, ← harmonicSum] at this
    simp only [div_div_eq_mul_div, div_one] at this
    rw [h2]
    exact (by norm_num : (4 : ℝ) = 2 ^ 2) ▸ this.trans_eq (sum_congr rfl fun _ _ => mul_comm _ _)
  · -- D3.6.2: `1/(2r + jD) ≥ (1/D) log((2r + (j+1)D)/(2r + jD))`, telescoped
    set f : ℕ → ℝ := fun j => Real.log (2 * r + j * D)
    have hstep : ∀ j, f (j + 1) - f j ≤ D * (1 / ((r + d r D j : ℕ) : ℝ)) := fun j => by
      have hp : (0 : ℝ) < 2 * r + j * D := by positivity
      simp only [f, d]
      rw [← Real.log_div (by positivity) hp.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans_eq ?_
      push_cast; field_simp; ring
    have htele : ∀ n, ∑ j ∈ Icc 1 n, (f (j + 1) - f j) = f (n + 1) - f 1 := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [sum_Icc_succ_top (by omega), ih]; ring
    have hsum := (htele (m Cpad r D)).symm.le.trans (sum_le_sum fun j _ => hstep j)
    rw [← mul_sum, ← harmonicSum] at hsum
    have hmr : (Cpad + 1 : ℝ) * r ≤ 2 * r + (m Cpad r D + 1 : ℕ) * D := by
      unfold m
      have h' : (((Cpad - 1) * r : ℕ) : ℝ) < (((Cpad - 1) * r / D * D + D : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_div_mul_add (a := (Cpad - 1) * r) hD
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Cpad)] at h'
      push_cast at h' ⊢; nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ hsum
    simp only [f, Nat.cast_one, one_mul]
    rw [← Real.log_div (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have h4 : (2 * r + D : ℝ) ≤ (2 + D) * r := by nlinarith
    push_cast at hmr ⊢
    nlinarith [mul_le_mul_of_nonneg_right hmr (by positivity : (0 : ℝ) ≤ 2 + D),
      mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ Cpad + 1)]

end D36

/-! ## D3.5 Nested regions, locality, single split, contour budget -/

section D35

open SimpleGraph

variable {Λ A Q X : Finset (ℤ × ℤ)} {R : ℕ} {D₀ : ℝ}

/-- D3.5. `X_0 = A ∩ Q₀`, `X_j = A ∩ Q₀^{+d_j}` for `j ≥ 1`. -/
noncomputable def bufferRegion (A Q₀ : Finset (ℤ × ℤ)) (r D j : ℕ) : Finset (ℤ × ℤ) :=
  if j = 0 then A ∩ Q₀ else A ∩ ambientDilation Q₀ (d r D j)

/-- The dilation radius of `X_j`: `0` for `j = 0`, `d_j` otherwise. -/
def rad (r D j : ℕ) : ℕ := if j = 0 then 0 else d r D j

theorem rad_add_le {r D i j : ℕ} (h : i < j) : rad r D i + D ≤ rad r D j := by
  have := Nat.mul_le_mul_right D (show i + 1 ≤ j by omega)
  simp only [rad, d, add_mul, one_mul] at *
  split_ifs <;> omega

theorem rad_le_d (r D j : ℕ) : rad r D j ≤ d r D j := by
  unfold rad; split_ifs <;> omega

/-- Two sites of a support are at `ℓ¹`-distance at most `R`. -/
theorem l1_le_of_mem_supports (hX : X ∈ supports Λ R) {s t : ℤ × ℤ} (hs : s ∈ X) (ht : t ∈ X) :
    (s.1 - t.1).natAbs + (s.2 - t.2).natAbs ≤ R := by
  have hΛ := (mem_supports.1 hX).1
  have hd := domainEDist_le_of_mem_supports hX hs ht
  rw [domainEDist_eq ⟨s, hΛ hs⟩ ⟨t, hΛ ht⟩] at hd
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (hd.trans_lt (ENat.natCast_lt_top R)).ne
  exact (natAbs_add_natAbs_le_length p).trans (ENat.natCast_le_natCast.1 (hp ▸ hd))

/-- A site of a safe `Q` is at `ℓ¹`-distance more than `R < D₀` from every endpoint of `∂_Λ A`. -/
theorem IsSafe.not_near (hs : IsSafe D₀ Λ A Q) (hRD₀ : (R : ℝ) < D₀) {x z : ℤ × ℤ} (hx : x ∈ Q)
    (hz : z ∈ cutEndpoints Λ A) (h : (x.1 - z.1).natAbs + (x.2 - z.2).natAbs ≤ R) : False := by
  have hQ : (1 : ℝ) ≤ boxSize Q := by
    exact_mod_cast le_max_of_le_left (card_pos.2 ⟨x.1, mem_image_of_mem _ hx⟩)
  have h1 : ambientEDist Q (cutEndpoints Λ A) ≤ edist x z :=
    (iInf₂_le x hx).trans (Metric.infEDist_le_edist_of_mem (by simpa using hz))
  have h2 : edist x z ≤ ENNReal.ofReal R := by
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Prod.dist_eq, Int.dist_eq, Int.dist_eq]
    have h3 : |x.1 - z.1| ≤ (R : ℤ) := abs_le.2 ⟨by omega, by omega⟩
    have h4 : |x.2 - z.2| ≤ (R : ℤ) := abs_le.2 ⟨by omega, by omega⟩
    exact max_le (by exact_mod_cast h3) (by exact_mod_cast h4)
  have := (hs.trans_le (h1.trans h2))
  rw [ENNReal.ofReal_lt_ofReal_iff'] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) R]

/-- D3.5.2. A support meeting `A` inside a safe `Q` lies in `A` (`R < D₀`). -/
theorem subset_of_isSafe (hs : IsSafe D₀ Λ A Q) (hRD₀ : (R : ℝ) < D₀) (hX : X ∈ supports Λ R)
    {x : ℤ × ℤ} (hxX : x ∈ X) (hxA : x ∈ A) (hxQ : x ∈ Q) : X ⊆ A := by
  intro y hy
  by_contra hyA
  have hΛ := (mem_supports.1 hX).1
  have hd := domainEDist_le_of_mem_supports hX hxX hy
  rw [domainEDist_eq ⟨x, hΛ hxX⟩ ⟨y, hΛ hy⟩] at hd
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (hd.trans_lt (ENat.natCast_lt_top R)).ne
  obtain ⟨z, hz, p', hp'⟩ := exists_cutEndpoints_of_walk (D := A) p (by simp [hxA, hyA])
  exact IsSafe.not_near hs hRD₀ hxQ hz ((natAbs_add_natAbs_le_length p').trans
    (hp'.trans (ENat.natCast_le_natCast.1 (hp ▸ hd))))

theorem mem_ambientDilation_Icc {a b y : ℤ × ℤ} (hab : a ≤ b) {e : ℕ} :
    y ∈ ambientDilation (Icc a b) e ↔
      a.1 - e ≤ y.1 ∧ y.1 ≤ b.1 + e ∧ a.2 - e ≤ y.2 ∧ y.2 ≤ b.2 + e := by
  have := Prod.le_def.1 hab
  rw [mem_ambientDilation]
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    rw [mem_Icc, Prod.le_def, Prod.le_def] at hx
    rw [abs_le] at h1 h2
    omega
  · intro h
    refine ⟨(max a.1 (min b.1 y.1), max a.2 (min b.2 y.2)), ?_, abs_le.2 ⟨?_, ?_⟩,
      abs_le.2 ⟨?_, ?_⟩⟩
    · rw [mem_Icc, Prod.le_def, Prod.le_def]; dsimp only; omega
    all_goals dsimp only; omega

theorem mem_bufferRegion {A : Finset (ℤ × ℤ)} {a b y : ℤ × ℤ} (hab : a ≤ b) {r D j : ℕ} :
    y ∈ bufferRegion A (Icc a b) r D j ↔ y ∈ A ∧ a.1 - rad r D j ≤ y.1 ∧ y.1 ≤ b.1 + rad r D j ∧
      a.2 - rad r D j ≤ y.2 ∧ y.2 ≤ b.2 + rad r D j := by
  unfold bufferRegion rad
  split_ifs
  · simp [mem_Icc, Prod.le_def]; omega
  · rw [mem_inter, mem_ambientDilation_Icc hab]

/-- D3.5.3. If no edge of `∂_Λ A` starts in `Y = A ∩ [a,b]^{+ρ}`, then every edge of `∂_Λ Y`
leaves the ambient rectangle `[a,b]^{+ρ}`, so `|∂_Λ Y|` is at most its perimeter. -/
theorem card_edgeBoundary_inter_le {a b : ℤ × ℤ} (hab : a ≤ b) {ρ : ℕ}
    (h : ∀ e ∈ edgeBoundary Λ A, e.1 ∉ A ∩ ambientDilation (Icc a b) ρ) :
    #(edgeBoundary Λ (A ∩ ambientDilation (Icc a b) ρ)) ≤
      2 * (b.1 + 1 - a.1 + 2 * ρ).toNat + 2 * (b.2 + 1 - a.2 + 2 * ρ).toNat := by
  set Y := A ∩ ambientDilation (Icc a b) ρ
  set I₁ := Icc (a.1 - ρ) (b.1 + ρ)
  set I₂ := Icc (a.2 - ρ) (b.2 + ρ)
  set P := ({a.1 - ρ - 1} ×ˢ I₂ ∪ {b.1 + ρ + 1} ×ˢ I₂) ∪ (I₁ ×ˢ {a.2 - ρ - 1} ∪ I₁ ×ˢ {b.2 + ρ + 1})
  have hP : #P ≤ 2 * (b.1 + 1 - a.1 + 2 * ρ).toNat + 2 * (b.2 + 1 - a.2 + 2 * ρ).toNat := by
    refine (card_union_le _ _).trans
      ((add_le_add (card_union_le _ _) (card_union_le _ _)).trans ?_)
    simp only [card_product, card_singleton, I₁, I₂, Int.card_Icc]
    omega
  -- D3.5.3: the coordinates of an edge of `∂_Λ Y`
  have hE : ∀ e ∈ edgeBoundary Λ Y, (a.1 - ρ ≤ e.1.1 ∧ e.1.1 ≤ b.1 + ρ ∧ a.2 - ρ ≤ e.1.2 ∧
      e.1.2 ≤ b.2 + ρ) ∧ ¬(a.1 - ρ ≤ e.2.1 ∧ e.2.1 ≤ b.1 + ρ ∧ a.2 - ρ ≤ e.2.2 ∧
      e.2.2 ≤ b.2 + ρ) ∧ ((e.1.1 + 1 = e.2.1 ∨ e.2.1 + 1 = e.1.1) ∧ e.1.2 = e.2.2 ∨
      (e.1.2 + 1 = e.2.2 ∨ e.2.2 + 1 = e.1.2) ∧ e.1.1 = e.2.1) := by
    rintro ⟨x, y⟩ he
    obtain ⟨hx, hy, hadj⟩ := (mk_mem_interedges_iff _).1 he
    have hyA : y ∈ A := by
      by_contra hyA
      exact h (x, y) ((mk_mem_interedges_iff _).2 ⟨(mem_inter.1 hx).1,
        mem_sdiff.2 ⟨(mem_sdiff.1 hy).1, hyA⟩, hadj⟩) hx
    have hy' : y ∉ ambientDilation (Icc a b) ρ := fun h' =>
      (mem_sdiff.1 hy).2 (mem_inter.2 ⟨hyA, h'⟩)
    rw [mem_inter, mem_ambientDilation_Icc hab] at hx
    rw [mem_ambientDilation_Icc hab] at hy'
    simp only [boxProd_adj, hasse_adj, Order.covBy_iff_add_one_eq] at hadj
    exact ⟨hx.2, hy', hadj⟩
  refine (card_le_card_of_injOn Prod.snd (fun e he => ?_) fun e he e' he' hee => ?_).trans hP
  · have := hE e he
    simp only [P, coe_union, Set.mem_union, coe_product, coe_singleton, Set.mem_prod,
      Set.mem_singleton_iff, coe_Icc, Set.mem_Icc, I₁, I₂]
    omega
  · have h1 := hE e he
    have h2 := hE e' he'
    have h3 := congrArg Prod.fst hee
    have h4 := congrArg Prod.snd hee
    exact Prod.ext (Prod.ext (by omega) (by omega)) hee

theorem rad_mono {r D i j : ℕ} (h : i ≤ j) : rad r D i ≤ rad r D j := by
  rcases h.lt_or_eq with h | rfl
  · exact (Nat.le_add_right _ _).trans (rad_add_le h)
  · exact le_rfl

theorem ambientDilation_mono' {T : Finset (ℤ × ℤ)} {i j : ℕ} (h : i ≤ j) :
    ambientDilation T i ⊆ ambientDilation T j := fun y hy => by
  obtain ⟨x, hx, h1, h2⟩ := mem_ambientDilation.1 hy
  have : (i : ℤ) ≤ j := by exact_mod_cast h
  exact mem_ambientDilation.2 ⟨x, hx, h1.trans this, h2.trans this⟩

variable {a b : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {r D Cpad : ℕ}

/-- D3.5.1. `d_m ≤ C_pad r`. -/
theorem d_m_le (hC : D + 1 < Cpad) : d r D (m Cpad r D) ≤ Cpad * r := by
  have h1 : m Cpad r D * D ≤ (Cpad - 1) * r := Nat.div_mul_le_self _ _
  have h2 : (Cpad - 1) * r + r = Cpad * r := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  unfold d; omega

/-- D3.5.1. `X_j ⊆ Q₀^{+d_m} ⊆ Q` for `j ≤ m`. -/
theorem bufferRegion_subset (hab : a ≤ b) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) {j : ℕ} (hj : j ≤ m Cpad r D) :
    bufferRegion A (Icc a b) r D j ⊆ ambientDilation (Icc a b) (d r D (m Cpad r D)) ∧
      ambientDilation (Icc a b) (d r D (m Cpad r D)) ⊆ Q := by
  refine ⟨fun y hy => ?_, (ambientDilation_mono' (d_m_le hC)).trans hQ₀Q⟩
  have h1 := rad_le_d r D j
  have h2 : d r D j ≤ d r D (m Cpad r D) := by unfold d; gcongr
  rw [mem_bufferRegion hab] at hy
  rw [mem_ambientDilation_Icc hab]
  omega

/-- D3.5.1 (a). `1 ≤ m`, `m D ≤ C_pad r`, `X_0 ⊆ X_1 ⊆ ⋯`, `Q₀^{+d_m} ⊆ Q`. -/
theorem step_3_5_1 (hab : a ≤ b) (hr : 1 ≤ r) (hD : 0 < D) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) :
    1 ≤ m Cpad r D ∧ m Cpad r D * D ≤ Cpad * r ∧
      (∀ i j, i ≤ j → bufferRegion A (Icc a b) r D i ⊆ bufferRegion A (Icc a b) r D j) ∧
      ambientDilation (Icc a b) (d r D (m Cpad r D)) ⊆ Q := by
  refine ⟨?_, ?_, fun i j hij y hy => ?_, (bufferRegion_subset (A := A) hab hC hQ₀Q le_rfl).2⟩
  · have : D ≤ (Cpad - 1) * r :=
      (show D ≤ Cpad - 1 by omega).trans (Nat.le_mul_of_pos_right _ hr)
    exact (Nat.le_div_iff_mul_le hD).2 (by simpa using this)
  · have := d_m_le (r := r) hC; unfold d at this; omega
  · have := rad_mono (r := r) (D := D) hij
    rw [mem_bufferRegion hab] at hy ⊢
    exact ⟨hy.1, by omega⟩

/-- D3.5.2 (b). Every support meeting some `X_j` lies in `A`; no edge of `∂_Λ A` is incident
with any `X_j`. -/
theorem step_3_5_2 (hab : a ≤ b) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    (∀ j ≤ m Cpad r D, ∀ X ∈ supports Λ R, (X ∩ bufferRegion A (Icc a b) r D j).Nonempty → X ⊆ A) ∧
      ∀ j ≤ m Cpad r D, ∀ e ∈ edgeBoundary Λ A,
        e.1 ∉ bufferRegion A (Icc a b) r D j ∧ e.2 ∉ bufferRegion A (Icc a b) r D j := by
  have hQ' : ∀ j ≤ m Cpad r D, bufferRegion A (Icc a b) r D j ⊆ Q := fun j hj =>
    (bufferRegion_subset (A := A) hab hC hQ₀Q hj).1.trans
      (bufferRegion_subset (A := A) hab hC hQ₀Q hj).2
  refine ⟨fun j hj X hX ⟨x, hx⟩ => ?_, fun j hj e he => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
  · exact subset_of_isSafe hs hRD₀ hX (mem_inter.1 hx).1
      ((mem_bufferRegion hab).1 (mem_inter.1 hx).2).1 (hQ' j hj (mem_inter.1 hx).2)
  · exact IsSafe.not_near hs hRD₀ (hQ' j hj h1) (mem_union_left _ (mem_image_of_mem _ he))
      (by simp)
  · rcases e with ⟨x, y⟩
    exact (mem_sdiff.1 ((mk_mem_interedges_iff _).1 he).2.1).2 ((mem_bufferRegion hab).1 h2).1

/-- D3.5.3 (c). `|∂_Λ X_j| ≤ 4 (r + 2 d_j)` for `1 ≤ j ≤ m`. -/
theorem step_3_5_3 (hab : a ≤ b) (hQ₀r : boxSize (Icc a b) ≤ r) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    ∀ j, 1 ≤ j → j ≤ m Cpad r D →
      #(edgeBoundary Λ (bufferRegion A (Icc a b) r D j)) ≤ 4 * (r + 2 * d r D j) := by
  intro j hj1 hjm
  have hX : bufferRegion A (Icc a b) r D j = A ∩ ambientDilation (Icc a b) (d r D j) :=
    if_neg (by omega)
  have hb := (step_3_5_2 hab hC hQ₀Q hs hRD₀).2 j hjm
  rw [hX] at hb ⊢
  refine (card_edgeBoundary_inter_le hab fun e he => (hb e he).1).trans ?_
  rw [boxSize_Icc hab] at hQ₀r
  have h1 := (le_max_left _ _).trans hQ₀r
  have h2 := (le_max_right _ _).trans hQ₀r
  omega

/-- D3.5.4 (d). A support split by `X_j` (`j ≤ m`) is disjoint from `X_i` for `i < j` and
contained in `X_i` for every `i > j`. -/
theorem step_3_5_4 (hab : a ≤ b) (hD : 2 * R + 2 < D) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    ∀ X ∈ supports Λ R, ∀ j ≤ m Cpad r D, (X ∩ bufferRegion A (Icc a b) r D j).Nonempty →
      (X \ bufferRegion A (Icc a b) r D j).Nonempty →
      (∀ i < j, Disjoint X (bufferRegion A (Icc a b) r D i)) ∧
        ∀ i, j < i → X ⊆ bufferRegion A (Icc a b) r D i := by
  intro X hX j hj ⟨p, hp⟩ ⟨p', hp'⟩
  have hXA := (step_3_5_2 hab hC hQ₀Q hs hRD₀).1 j hj X hX ⟨p, hp⟩
  rw [mem_inter, mem_bufferRegion hab] at hp
  rw [mem_sdiff, mem_bufferRegion hab] at hp'
  refine ⟨fun i hi => disjoint_left.2 fun s hs hsi => hp'.2 ?_, fun i hi s hs => ?_⟩
  · have := l1_le_of_mem_supports hX hs hp'.1
    have := rad_add_le (r := r) (D := D) hi
    rw [mem_bufferRegion hab] at hsi
    exact ⟨hXA hp'.1, by omega⟩
  · have := l1_le_of_mem_supports hX hs hp.1
    have := rad_add_le (r := r) (D := D) hi
    rw [mem_bufferRegion hab]
    exact ⟨hXA hs, by omega⟩

/-- D3.5.5. `C₂ = 1 + 16 v_R μ_R (1 + v_R log q)²`. -/
noncomputable def C₂ (q R : ℕ) : ℝ := 1 + 16 * v 2 R * μ (v 2) R * (1 + v 2 R * Real.log q) ^ 2

/-- D3.5.5 (e). For `1 ≤ j ≤ m`: `#{split by X_j} ≤ 16 v_R μ_R (r + d_j)` and
`𝓑_j ≤ C₂ (r + d_j)`. -/
theorem step_3_5_5 {q : ℕ} (hq : 1 ≤ q) (hab : a ≤ b) (hr : 1 ≤ r)
    (hQ₀r : boxSize (Icc a b) ≤ r) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    ∀ j, 1 ≤ j → j ≤ m Cpad r D →
      (#{X ∈ supports Λ R | (X ∩ bufferRegion A (Icc a b) r D j).Nonempty ∧
          (X \ bufferRegion A (Icc a b) r D j).Nonempty} : ℝ) ≤
          16 * v 2 R * μ (v 2) R * (r + d r D j) ∧
        1 + ∑ X ∈ supports Λ R with (X ∩ bufferRegion A (Icc a b) r D j).Nonempty ∧
          (X \ bufferRegion A (Icc a b) r D j).Nonempty,
          Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
          C₂ q R * (r + d r D j) := by
  intro j hj1 hjm
  have hc := step_3_5_3 hab hQ₀r hC hQ₀Q hs hRD₀ j hj1 hjm
  have hcR : (#(edgeBoundary Λ (bufferRegion A (Icc a b) r D j)) : ℝ) ≤ 4 * (r + 2 * d r D j) := by
    exact_mod_cast hc
  have hrd : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) ≤ d r D j := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have h1 : (#{X ∈ supports Λ R | (X ∩ bufferRegion A (Icc a b) r D j).Nonempty ∧
        (X \ bufferRegion A (Icc a b) r D j).Nonempty} : ℝ) ≤
        2 * v 2 R * μ (v 2) R * #(edgeBoundary Λ (bufferRegion A (Icc a b) r D j)) := by
      exact_mod_cast eq_crossing_count squareLattice (v 2) eq_ball_count_two Λ _ R
    have hK : (0 : ℝ) ≤ v 2 R * μ (v 2) R := by positivity
    nlinarith
  · have h1 := step_3_2_3' Λ (bufferRegion A (Icc a b) r D j) R q hq
    have hK : (0 : ℝ) ≤ 2 * v 2 R * μ (v 2) R * (1 + v 2 R * Real.log q) ^ 2 := by positivity
    unfold C₂
    nlinarith [mul_le_mul_of_nonneg_left hcR hK, mul_nonneg hK hd0]

end D35

/-- D3.5. Let `D > 2R + 2`, `C_pad > D + 1`, `m = ⌊(C_pad - 1) r / D⌋`, `d_j = r + jD`,
`X_0 = A ∩ Q₀`, `X_j = A ∩ Q₀^{+d_j}`. Then (a) `1 ≤ m`, `m D ≤ C_pad r`,
`X_0 ⊆ X_1 ⊆ ⋯ ⊆ X_m`, `Q₀^{+d_m} ⊆ Q`; (b) every support meeting some `X_j` lies in `A`, and
no edge of `∂_Λ A` is incident with any `X_j`; (c) `|∂_Λ X_j| ≤ 4 (r + 2 d_j)`; (d) a support
split by `X_j` is disjoint from `X_i` for `i < j` and contained in `X_i` for every `i > j`;
(e) `#{supports split by X_j} ≤ 16 v_R μ_R (r + d_j)` and `𝓑_j ≤ C₂ (r + d_j)`. -/
theorem step_3_5 {q R : ℕ} {D₀ : ℝ} {Λ A Q Q₀ : Finset (ℤ × ℤ)} {r D Cpad : ℕ} (hq : 1 ≤ q)
    (_hA : A ⊆ Λ) (_hQ : IsIntRect Q) (hs : IsSafe D₀ Λ A Q) (hRD₀ : (R : ℝ) < D₀) (hr : 1 ≤ r)
    (hQ₀ : IsIntRect Q₀) (hQ₀r : boxSize Q₀ ≤ r) (hD : 2 * R + 2 < D) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation Q₀ (Cpad * r) ⊆ Q) :
    (1 ≤ m Cpad r D ∧ m Cpad r D * D ≤ Cpad * r ∧
      (∀ i j, i ≤ j → bufferRegion A Q₀ r D i ⊆ bufferRegion A Q₀ r D j) ∧
      ambientDilation Q₀ (d r D (m Cpad r D)) ⊆ Q) ∧
    ((∀ j ≤ m Cpad r D, ∀ X ∈ supports Λ R, (X ∩ bufferRegion A Q₀ r D j).Nonempty → X ⊆ A) ∧
      ∀ j ≤ m Cpad r D, ∀ e ∈ edgeBoundary Λ A,
        e.1 ∉ bufferRegion A Q₀ r D j ∧ e.2 ∉ bufferRegion A Q₀ r D j) ∧
    (∀ j, 1 ≤ j → j ≤ m Cpad r D →
      #(edgeBoundary Λ (bufferRegion A Q₀ r D j)) ≤ 4 * (r + 2 * d r D j)) ∧
    (∀ X ∈ supports Λ R, ∀ j ≤ m Cpad r D, (X ∩ bufferRegion A Q₀ r D j).Nonempty →
      (X \ bufferRegion A Q₀ r D j).Nonempty →
      (∀ i < j, Disjoint X (bufferRegion A Q₀ r D i)) ∧
        ∀ i, j < i → X ⊆ bufferRegion A Q₀ r D i) ∧
    ∀ j, 1 ≤ j → j ≤ m Cpad r D →
      (#{X ∈ supports Λ R | (X ∩ bufferRegion A Q₀ r D j).Nonempty ∧
          (X \ bufferRegion A Q₀ r D j).Nonempty} : ℝ)
          ≤ 16 * v 2 R * μ (v 2) R * (r + d r D j) ∧
        1 + ∑ X ∈ supports Λ R with (X ∩ bufferRegion A Q₀ r D j).Nonempty ∧
          (X \ bufferRegion A Q₀ r D j).Nonempty,
          Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
          C₂ q R * (r + d r D j) := by
  obtain ⟨a, b, hab, rfl⟩ := hQ₀
  exact ⟨step_3_5_1 hab hr (by omega) hC hQ₀Q, step_3_5_2 hab hC hQ₀Q hs hRD₀,
    step_3_5_3 hab hQ₀r hC hQ₀Q hs hRD₀, step_3_5_4 hab hD hC hQ₀Q hs hRD₀,
    step_3_5_5 hq hab hr hQ₀r hC hQ₀Q hs hRD₀⟩

/-! ## D3.8 Clipping bounds log-ratios of filter eigenvalues (D3.8.2–D3.8.3) -/

section D38

variable {ι : Type*} [Fintype ι]

/-- D3.8.2. KKT with floor: `x_i ≥ f > 0`, some coordinate free (`x_{i₀} > f`), `p_i ≥ 0`,
`∑_i p_i = 1`, and `p_k / x_k ≤ p_i / x_i` whenever `x_i > f`. Then `x_i = max {f, p_i/λ}` for
some `λ > 0`. -/
theorem step_3_8_2 {x p : ι → ℝ} {f : ℝ} (hf : 0 < f) (hx : ∀ i, f ≤ x i)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) {i₀ : ι} (hi₀ : f < x i₀)
    (hopt : ∀ i k, f < x i → p k / x k ≤ p i / x i) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ i, x i = max f (p i / lam) := by
  have hxpos : ∀ i, 0 < x i := fun i => hf.trans_le (hx i)
  -- D3.8.2: `p_i / x_i = λ` on free coordinates, `≤ λ` on floored ones
  have hle : ∀ k, p k / x k ≤ p i₀ / x i₀ := fun k => hopt i₀ k hi₀
  -- D3.8.2: `λ > 0`, as `∑ p = 1`
  have hlam : 0 < p i₀ / x i₀ := by
    by_contra h
    have h0 : ∀ k, p k = 0 := fun k => le_antisymm (by
      simpa using (div_le_iff₀ (hxpos k)).1 ((hle k).trans (not_lt.1 h))) (hp k)
    simp [h0] at hs
  refine ⟨p i₀ / x i₀, hlam, fun i => ?_⟩
  -- D3.8.3: hence `x_i = max {f, p_i/λ}`
  have := hle i
  rw [div_le_iff₀ (hxpos i)] at this
  rcases (hx i).eq_or_lt with h | h
  · rw [← h, max_eq_left]
    rw [div_le_iff₀ hlam]; rw [← h] at this; linarith
  · have he := le_antisymm (hle i) (hopt i i₀ h)
    rw [div_eq_iff (hxpos i).ne'] at he
    have hx' : p i / (p i₀ / x i₀) = x i := by rw [he, mul_div_cancel_left₀ _ hlam.ne']
    rw [hx', max_eq_right h.le]

/-- D3.8.3. If `x_i = max {f, p_i/λ}` and `l_i = x_i^{a/2}` (`f, λ > 0`, `a ≥ 0`), then for
`p_i, p_k > 0`: `|log (l_i/l_k)| ≤ (a/2) |log (p_i/p_k)|`. -/
theorem step_3_8_3 {f lam a p₁ p₂ : ℝ} (hf : 0 < f) (hlam : 0 < lam) (ha : 0 ≤ a)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    |Real.log (max f (p₁ / lam) ^ (a / 2) / max f (p₂ / lam) ^ (a / 2))| ≤
      a / 2 * |Real.log (p₁ / p₂)| := by
  have h1 : 0 < max f (p₁ / lam) := lt_max_of_lt_left hf
  have h2 : 0 < max f (p₂ / lam) := lt_max_of_lt_left hf
  have hlog : ∀ y, 0 < y → Real.log (max f y) = max (Real.log f) (Real.log y) := fun y hy => by
    rcases le_total f y with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log hf h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log hy h)]
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow h1, Real.log_rpow h2, ← mul_sub,
    abs_mul, abs_of_nonneg (by linarith : 0 ≤ a / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  -- D3.8.3: `s ↦ log max {f, e^s}` is 1-Lipschitz
  rw [hlog _ (by positivity), hlog _ (by positivity), max_comm (Real.log f),
    max_comm (Real.log f), Real.log_div hp₁.ne' hp₂.ne']
  refine (abs_max_sub_max_le_abs _ _ _).trans_eq ?_
  rw [Real.log_div hp₁.ne' hlam.ne', Real.log_div hp₂.ne' hlam.ne']
  ring_nf

end D38

/-! ## D3.9 The optimized vector has small excitation energy (D3.9.4) -/

section D39

/-- `cosh s - 1 ≤ ½ s² cosh s` (termwise Taylor). -/
theorem cosh_sub_one_le (s : ℝ) : Real.cosh s - 1 ≤ s ^ 2 / 2 * Real.cosh s := by
  have h1 : HasSum (fun k : ℕ => s ^ (2 * (k + 1)) / (2 * (k + 1)).factorial)
      (Real.cosh s - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cosh s)
  refine hasSum_le (fun k => ?_) h1 ((Real.hasSum_cosh s).mul_left (s ^ 2 / 2))
  have hf : (2 : ℝ) * (2 * k).factorial ≤ (2 * (k + 1)).factorial := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hF := (Nat.cast_pos (α := ℝ)).2 (Nat.factorial_pos (2 * k))
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    nlinarith [mul_nonneg hk hF.le, mul_nonneg (mul_nonneg hk hk) hF.le]
  have h0 : 0 ≤ s ^ 2 * s ^ (2 * k) := by rw [pow_mul]; positivity
  calc s ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)
      = s ^ 2 * s ^ (2 * k) / ((2 * (k + 1)).factorial : ℝ) := by ring_nf
    _ ≤ s ^ 2 * s ^ (2 * k) / (2 * (2 * k).factorial) :=
        div_le_div_of_nonneg_left h0 (by positivity) hf
    _ = _ := by ring

/-- D3.9.4. For `p_i, p_k > 0`, `0 ≤ a_j ≤ ½` and `|log (l_i/l_k)| ≤ (a_j/2) |log (p_i/p_k)|`
(D3.8): `√(p_i p_k) (cosh log (l_i/l_k) - 1) ≤ (8/e²) a_j² (p_i + p_k)`. -/
theorem step_3_9_4 {a p₁ p₂ t : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (ht : |t| ≤ a / 2 * |Real.log (p₁ / p₂)|) :
    √(p₁ * p₂) * (Real.cosh t - 1) ≤ 8 / Real.exp 2 * a ^ 2 * (p₁ + p₂) := by
  set z := Real.log (p₁ / p₂) / 2
  set w := (Real.log p₁ + Real.log p₂) / 2
  have hlz : Real.log (p₁ / p₂) = Real.log p₁ - Real.log p₂ := Real.log_div hp₁.ne' hp₂.ne'
  have hp1 : p₁ = Real.exp (w + z) := by
    rw [show w + z = Real.log p₁ by simp only [w, z, hlz]; ring, Real.exp_log hp₁]
  have hp2 : p₂ = Real.exp (w - z) := by
    rw [show w - z = Real.log p₂ by simp only [w, z, hlz]; ring, Real.exp_log hp₂]
  -- D3.9.4: `√(p_i p_k) = (p_i + p_k) / (2 cosh z)`
  have hsq : √(p₁ * p₂) = Real.exp w := by
    rw [hp1, hp2, ← Real.exp_add, show w + z + (w - z) = w + w by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos w).le]
  have hsum : p₁ + p₂ = 2 * Real.exp w * Real.cosh z := by
    rw [hp1, hp2, Real.cosh_eq, Real.exp_add, Real.exp_sub, Real.exp_neg]; field_simp
  -- D3.9.4: `cosh log(l_i/l_k) ≤ cosh(a_j z) ≤ cosh(z/2)`
  have hat : |t| ≤ |a * z| := by
    rw [abs_mul, abs_of_nonneg ha, abs_div, abs_two]; linarith
  have hc1 : Real.cosh t - 1 ≤ (a * z) ^ 2 / 2 * Real.cosh (z / 2) := by
    refine (sub_le_sub_right (Real.cosh_le_cosh.2 hat) 1).trans ((cosh_sub_one_le _).trans ?_)
    gcongr
    rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg ha, abs_div z 2, abs_two]
    nlinarith [abs_nonneg z]
  -- D3.9.4: `z² cosh(z/2) / cosh z ≤ 2 z² e^{-|z|/2} ≤ 32/e²`
  have hch : Real.cosh (z / 2) ≤ Real.exp (|z| / 2) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (z / 2) ≤ Real.exp (|z| / 2) :=
      Real.exp_le_exp.2 (by linarith [le_abs_self z])
    have h2 : Real.exp (-(z / 2)) ≤ Real.exp (|z| / 2) :=
      Real.exp_le_exp.2 (by linarith [neg_abs_le z])
    linarith
  have hcz : Real.exp |z| ≤ 2 * Real.cosh z := by
    rw [← Real.cosh_abs, Real.cosh_eq]; nlinarith [Real.exp_pos (-|z|)]
  have hez : Real.exp 2 * z ^ 2 ≤ 16 * Real.exp (|z| / 2) := by
    have := Real.add_one_le_exp (|z| / 4 - 1)
    have h4 : Real.exp (|z| / 2) = (Real.exp 1 * Real.exp (|z| / 4 - 1)) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h4, show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num,
      ← sq_abs z]
    have he := Real.exp_pos 1
    have hu : Real.exp 1 * (|z| / 4) ≤ Real.exp 1 * Real.exp (|z| / 4 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) he.le
    nlinarith [pow_le_pow_left₀ (by positivity) hu 2]
  have hE2 := Real.exp_pos 2
  have hw := Real.exp_pos w
  have hcpos : 0 < Real.cosh z := Real.cosh_pos z
  rw [hsq, hsum]
  calc Real.exp w * (Real.cosh t - 1)
      ≤ Real.exp w * ((a * z) ^ 2 / 2 * Real.exp (|z| / 2)) := by
        gcongr; exact hc1.trans (by gcongr)
    _ = Real.exp w * a ^ 2 / 2 * (Real.exp 2 * z ^ 2) * Real.exp (|z| / 2) / Real.exp 2 := by
        field_simp
    _ ≤ Real.exp w * a ^ 2 / 2 * (16 * Real.exp (|z| / 2)) * Real.exp (|z| / 2) /
        Real.exp 2 := by gcongr
    _ = 8 * Real.exp w * a ^ 2 * Real.exp |z| / Real.exp 2 := by
        rw [← show Real.exp (|z| / 2) * Real.exp (|z| / 2) = Real.exp |z| by
          rw [← Real.exp_add]; ring_nf]
        ring
    _ ≤ 8 * Real.exp w * a ^ 2 * (2 * Real.cosh z) / Real.exp 2 := by gcongr
    _ = _ := by ring

end D39

/-! ## D3.10 Final choice of `C_pad` -/

section D310

/-- D3.10 (eq:initial-weight-range), with the last sentence of D3.6. For `D ≥ 1`, `C` (the
constant of D3.9), `Δ > 0`, `J ≥ 0` there is an integer `C_pad > D + 1` such that for all `r ≥ 1`,
`1 ≤ j ≤ m`: (i) `C ℰ / Δ ≤ 1/4`; (ii) `a_j ≤ ½`;
(iii) `a_j / (1 - a_j) ≤ 1 / (32 √((1 + J/Δ) C₂ (r + d_j)))` (`𝓑_j ≤ C₂ (r + d_j)`, D3.5(e)). -/
theorem eq_initial_weight_range (q R D : ℕ) (hD : 0 < D) {C J Δ : ℝ} (hΔ : 0 < Δ)
    (hJ : 0 ≤ J) :
    ∃ Cpad : ℕ, D + 1 < Cpad ∧ ∀ r, 1 ≤ r → C * ℰ Cpad r D / Δ ≤ 1 / 4 ∧
      ∀ j ∈ Icc 1 (m Cpad r D), a Cpad r D j ≤ 1 / 2 ∧
        a Cpad r D j / (1 - a Cpad r D j) ≤
          1 / (32 * √((1 + J / Δ) * (C₂ q R * (r + d r D j)))) := by
  set K := (1 + J / Δ) * C₂ q R
  have hC₂ : 1 ≤ C₂ q R := by
    unfold C₂
    have : (0 : ℝ) ≤ 16 * v 2 R * μ (v 2) R * (1 + v 2 R * Real.log q) ^ 2 := by positivity
    linarith
  have hK : 0 < K := mul_pos (by positivity) (by linarith)
  set L₀ := max 4 (max (16 * C * D / Δ) (128 * D * √K))
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨⌈(2 + D) * Real.exp L₀⌉₊ + D + 2, by omega, fun r hr => ?_⟩
  set Cpad := ⌈(2 + D) * Real.exp L₀⌉₊ + D + 2
  -- D3.10.1: `log ((C_pad + 1)/(2 + D)) ≥ L₀`
  have hL : L₀ ≤ Real.log ((Cpad + 1) / (2 + D)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity), mul_comm]
    have := Nat.le_ceil ((2 + D) * Real.exp L₀)
    simp only [Cpad]; push_cast; linarith
  obtain ⟨-, hE, -, hZ⟩ := eq_initial_harmonic_weights hD (by omega : D + 1 < Cpad) hr
  have hL₀ : 4 ≤ L₀ := le_max_left _ _
  have hZ' : L₀ / D ≤ harmonicSum Cpad r D := by
    refine le_trans ?_ hZ; rw [one_div_mul_eq_div]; gcongr
  have hZpos : 0 < harmonicSum Cpad r D := lt_of_lt_of_le (by positivity) hZ'
  have hDZ : L₀ ≤ D * harmonicSum Cpad r D := by rwa [div_le_iff₀ (by positivity), mul_comm] at hZ'
  refine ⟨?_, fun j hj => ?_⟩
  · -- D3.10.1 (i): `C ℰ / Δ ≤ 4 C D / (L₀ Δ) ≤ 1/4`
    rw [hE, div_le_iff₀ hΔ]
    have h1 : 16 * C * D / Δ ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hΔ] at h1
    rw [mul_div_assoc', div_le_iff₀ hZpos]
    nlinarith
  · have hs : (2 : ℝ) ≤ ((r + d r D j : ℕ) : ℝ) := by
      have : 2 ≤ r + d r D j := by unfold d; omega
      exact_mod_cast this
    have hs' : ((r + d r D j : ℕ) : ℝ) = r + d r D j := by push_cast; ring
    have hDs : (D : ℝ) + 2 ≤ ((r + d r D j : ℕ) : ℝ) := by
      have : D + 2 ≤ r + d r D j := by
        unfold d; have := Nat.le_mul_of_pos_left D (show 0 < j by simp at hj; omega); omega
      exact_mod_cast this
    have hZs : 0 < harmonicSum Cpad r D * ((r + d r D j : ℕ) : ℝ) := by positivity
    -- D3.6.3 (ii): `a_j ≤ 2 / (Z_r (D + 2)) ≤ ½`
    have ha2 : a Cpad r D j ≤ 1 / 2 := by
      rw [a, div_le_div_iff₀ hZs (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left hDs hZpos.le]
    refine ⟨ha2, ?_⟩
    -- D3.10.2 (iii): `a_j/(1 - a_j) ≤ 2 a_j = 4/(Z_r (r + d_j)) ≤ 1/(32 √K (r + d_j))`
    have ha0 : 0 < a Cpad r D j := div_pos two_pos hZs
    have h1 : a Cpad r D j / (1 - a Cpad r D j) ≤ 2 * a Cpad r D j := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    refine h1.trans ?_
    have h128 : 128 * D * √K ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
    have hsq : √(K * ((r + d r D j : ℕ) : ℝ)) ≤ √K * ((r + d r D j : ℕ) : ℝ) := by
      rw [Real.sqrt_mul hK.le]; gcongr
      exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hKZ : 128 * √K ≤ harmonicSum Cpad r D :=
      le_of_mul_le_mul_left (by linarith [h128.trans hDZ] :
        (D : ℝ) * (128 * √K) ≤ D * harmonicSum Cpad r D) (by positivity)
    rw [show (1 + J / Δ) * (C₂ q R * (r + d r D j)) = K * ((r + d r D j : ℕ) : ℝ) by
      rw [hs']; ring, a, mul_div_assoc', le_div_iff₀ (by positivity), div_mul_eq_mul_div,
      div_le_iff₀ hZs]
    nlinarith [mul_le_mul_of_nonneg_right hKZ (by positivity : (0 : ℝ) ≤ ((r + d r D j : ℕ) : ℝ))]

end D310

/-! ## D3.11 First norm comparison (D3.11.4–D3.11.5, scalar part) -/

section D311

/-- D3.11.4 (scalar part). For `0 < a_j ≤ ½`, `u = -a_j/(1 - a_j)`, `ϑ, 𝓑_j ≥ 0`: Lemma 3.1 at
`u`, `log Tr ρ^{1/(1-a_j)} ≤ u S + 512 e ϑ 𝓑_j u²`, gives
`(1 - a_j) log Tr ρ^{1/(1-a_j)} ≤ -a_j S + 1024 e ϑ 𝓑_j a_j²`. -/
theorem step_3_11_4 {a S ϑ 𝓑 M : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hϑ : 0 ≤ ϑ) (h𝓑 : 0 ≤ 𝓑)
    (hM : M ≤ -a / (1 - a) * S + 512 * Real.exp 1 * ϑ * 𝓑 * (-a / (1 - a)) ^ 2) :
    (1 - a) * M ≤ -a * S + 1024 * Real.exp 1 * ϑ * 𝓑 * a ^ 2 := by
  have h1 : 0 < 1 - a := by linarith
  have hK : 0 ≤ 512 * Real.exp 1 * ϑ * 𝓑 * a ^ 2 := by positivity
  calc (1 - a) * M
      ≤ (1 - a) * (-a / (1 - a) * S + 512 * Real.exp 1 * ϑ * 𝓑 * (-a / (1 - a)) ^ 2) :=
        mul_le_mul_of_nonneg_left hM h1.le
    _ = -a * S + 512 * Real.exp 1 * ϑ * 𝓑 * a ^ 2 / (1 - a) := by field_simp
    _ ≤ -a * S + 512 * Real.exp 1 * ϑ * 𝓑 * a ^ 2 * 2 := by
        gcongr; rw [div_le_iff₀ h1]; nlinarith
    _ = _ := by ring

/-- `-log (1 - v) ≤ 2 v` for `0 ≤ v ≤ ½`. -/
theorem neg_two_mul_le_log_one_sub {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2) :
    -(2 * v) ≤ Real.log (1 - v) := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + 2 * v)
  have h2 : 0 ≤ Real.log ((1 - v) * (1 + 2 * v)) := Real.log_nonneg (by nlinarith)
  rw [Real.log_mul (by linarith) (by linarith)] at h2
  linarith

/-- D3.11.5. `N_0 = 1`, `N_j > 0`, `√(1 - v) N_j ≤ x_j N_{j-1}` (D3.11.2) with `0 ≤ v ≤ ¼`,
`x_j = ‖L_j Ω‖ > 0` and `2 log x_j ≤ -a_j S(X_j) + c_j` (D3.11.3–D3.11.4). Then
`-2 log N_m ≥ ∑_j (a_j S(X_j) - c_j) - 2 m v`. -/
theorem step_3_11_5 {m : ℕ} {N x a S c : ℕ → ℝ} {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 4)
    (hN0 : N 0 = 1) (hN : ∀ j, 0 < N j) (hx : ∀ j ∈ Icc 1 m, 0 < x j)
    (htel : ∀ j ∈ Icc 1 m, √(1 - v) * N j ≤ x j * N (j - 1))
    (hlog : ∀ j ∈ Icc 1 m, 2 * Real.log (x j) ≤ -(a j * S j) + c j) :
    ∑ j ∈ Icc 1 m, (a j * S j - c j) - 2 * m * v ≤ -2 * Real.log (N m) := by
  have hv' := neg_two_mul_le_log_one_sub hv0 (by linarith)
  induction m with
  | zero => simp [hN0]
  | succ k ih =>
    have hk : k + 1 ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, le_rfl⟩
    have hmono : ∀ j ∈ Icc 1 k, j ∈ Icc 1 (k + 1) := fun j hj =>
      mem_Icc.2 ⟨(mem_Icc.1 hj).1, (mem_Icc.1 hj).2.trans (Nat.le_succ k)⟩
    have ih := ih (fun j hj => hx j (hmono j hj)) (fun j hj => htel j (hmono j hj))
      (fun j hj => hlog j (hmono j hj))
    -- D3.11.5: `log N_j ≤ log x_j + log N_{j-1} - ½ log(1 - v)`
    have h1 := htel (k + 1) hk
    simp only [Nat.add_sub_cancel] at h1
    have hs : 0 < √(1 - v) := Real.sqrt_pos.2 (by linarith)
    have h2 := Real.log_le_log (by have := hN (k + 1); positivity) h1
    rw [Real.log_mul hs.ne' (hN _).ne', Real.log_mul (hx _ hk).ne' (hN _).ne',
      Real.log_sqrt (by linarith)] at h2
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    nlinarith [hlog (k + 1) hk]

end D311

/-! ## D3.14 Conclusion of Lemma 3.2 -/

section D314

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ}

/-- SSA (D2.2 item 2) for nested conditioning sets: `T ⊆ T'` gives `S(X | T') ≤ S(X | T)`. -/
theorem condEntropy_anti (ρ : Arealaw.MState (Reg loc U) ℂ) {X T T' : Finset σ} (hX : X ⊆ U)
    (hT' : T' ⊆ U) (hXT : Disjoint X T') (h : T ⊆ T') :
    ρ.regionEntropy (union_subset hX hT') - ρ.regionEntropy hT' ≤
      ρ.regionEntropy (union_subset hX (h.trans hT')) - ρ.regionEntropy (h.trans hT') := by
  have := ρ.regionEntropy_union_sub_le (hXT.mono_right h) (hXT.mono_right sdiff_subset)
    disjoint_sdiff hX (h.trans hT') (sdiff_subset.trans hT')
  simp only [union_sdiff_of_subset h] at this
  convert this using 2

/-- D3.14.1–D3.14.4. From `∑_j a_j S(X_j) - E ≤ S(X) + ∑_j a_j S(T_j)` with `X_j = X ⊔ T_j`,
`T_j ⊆ T_m ⊆ T`, `a_j > 0`, `∑_j a_j = 2`: `S(X | T) ≤ ½ S(X) + ½ E`. -/
theorem step_3_14 (ρ : Arealaw.MState (Reg loc U) ℂ) {X T : Finset σ} {m : ℕ}
    (Tj : ℕ → Finset σ) (hX : X ⊆ U) (hT : T ⊆ U) (hXT : Disjoint X T) (hTT : ∀ j, Tj j ⊆ T)
    (hmono : ∀ j ∈ Icc 1 m, Tj j ⊆ Tj m) (a : ℕ → ℝ) (ha : ∀ j ∈ Icc 1 m, 0 < a j)
    (hsum : ∑ j ∈ Icc 1 m, a j = 2) {E : ℝ}
    (h : ∑ j ∈ Icc 1 m, a j * ρ.regionEntropy (union_subset hX ((hTT j).trans hT)) - E ≤
      ρ.regionEntropy hX + ∑ j ∈ Icc 1 m, a j * ρ.regionEntropy ((hTT j).trans hT)) :
    ρ.regionEntropy (union_subset hX hT) - ρ.regionEntropy hT ≤ ρ.regionEntropy hX / 2 + E / 2 := by
  obtain ⟨f, hf⟩ : ∃ f : Finset σ → ℝ, ∀ A (h : A ⊆ U), ρ.regionEntropy h = f A :=
    ⟨fun A => if h : A ⊆ U then ρ.regionEntropy h else 0, fun A h => (dif_pos h).symm⟩
  -- D3.14.3–D3.14.4: `S(X|T) ≤ S(X|T_m) ≤ S(X|T_j)` (SSA)
  have key : ∀ j ∈ Icc 1 m, a j * (f (X ∪ T) - f T) ≤ a j * f (X ∪ Tj j) - a j * f (Tj j) := by
    intro j hj
    have h1 := condEntropy_anti ρ hX hT hXT (hTT m)
    have h2 := condEntropy_anti ρ hX ((hTT m).trans hT) (hXT.mono_right (hTT m)) (hmono j hj)
    simp only [hf] at h1 h2
    nlinarith [ha j hj]
  -- D3.14.1–D3.14.2: `∑_j a_j S(X|T_j) ≤ S(X) + E`, and `∑_j a_j = 2`
  have := sum_le_sum key
  rw [← sum_mul, hsum, sum_sub_distrib] at this
  simp only [hf] at h ⊢
  linarith

/-- D3.14.5. `m + 1 ≤ (C_pad/D + 1) r` (`r ≥ 1`) and `ℰ = 4/Z_r ≤ 4D / log((C_pad + 1)/(2 + D))`
(D3.6), so the error `½ C (m + 1) ℰ` is at most `C_buf r`,
`C_buf = C (C_pad/D + 1) · 2D / log((C_pad + 1)/(2 + D))`. -/
theorem step_3_14_5 {Cpad r D : ℕ} (hD : 0 < D) (hC : D + 1 < Cpad) (hr : 1 ≤ r) {C : ℝ}
    (hC0 : 0 ≤ C) :
    C * (m Cpad r D + 1) * ℰ Cpad r D / 2 ≤
      C * (Cpad / D + 1) * (2 * D / Real.log ((Cpad + 1) / (2 + D))) * r := by
  obtain ⟨-, hE, -, hZ⟩ := eq_initial_harmonic_weights hD hC hr
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL : 0 < Real.log ((Cpad + 1) / (2 + D)) := Real.log_pos (by
    rw [one_lt_div (by positivity)]; exact_mod_cast (by omega : 2 + D < Cpad + 1))
  -- D3.14.5: `m + 1 ≤ (C_pad/D + 1) r`
  have hm : (m Cpad r D : ℝ) + 1 ≤ (Cpad / D + 1) * r := by
    have h1 : (m Cpad r D * D : ℝ) ≤ Cpad * r := by
      have := Nat.div_mul_le_self ((Cpad - 1) * r) D
      have h2 : (Cpad - 1) * r ≤ Cpad * r := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      exact_mod_cast this.trans h2
    have h3 : (m Cpad r D : ℝ) ≤ Cpad * r / D := by rw [le_div_iff₀ hD']; exact h1
    calc (m Cpad r D : ℝ) + 1 ≤ Cpad * r / D + r := by linarith
      _ = _ := by ring
  -- D3.6: `ℰ ≤ 4 D / log((C_pad + 1)/(2 + D))`
  have hE' : ℰ Cpad r D ≤ 4 * D / Real.log ((Cpad + 1) / (2 + D)) := by
    rw [hE, div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hZ) hL]
    rw [one_div_mul_eq_div, div_le_iff₀ hD'] at hZ; linarith
  have hE0 : 0 ≤ ℰ Cpad r D := by unfold ℰ; positivity
  calc C * (m Cpad r D + 1) * ℰ Cpad r D / 2
      ≤ C * ((Cpad / D + 1) * r) * (4 * D / Real.log ((Cpad + 1) / (2 + D))) / 2 := by gcongr
    _ = _ := by ring

end D314


end AreaLaw
