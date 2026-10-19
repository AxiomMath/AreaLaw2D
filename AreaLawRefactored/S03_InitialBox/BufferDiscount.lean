import AreaLawRefactored.S02_Preliminaries

/-!
# §3.2 An entropy discount from a buffer

Digest `digest/03-initial-box.md` (D3.2–D3.14), paper `paper/sections/02-initial.tex`,
lines 202–586.
-/

namespace AreaLaw

open Arealaw OpenAI Finset

/-! ## D3.2 Lattice specialization of Lemma 3.1: the budget `𝓑` -/

/-- D3.2. `C₁ = max {1, 2 v_R μ_R (1 + v_R log q)²}`. -/
noncomputable def C₁ (q R : ℕ) : ℝ := max 1 (2 * v R * μ R * (1 + v R * Real.log q) ^ 2)

/-- D3.2.2. For a support `X`: `log (e q^{|X|})² ≤ (1 + v_R log q)²`. -/
theorem log_sq_le_of_mem_supports {Λ X : Finset (ℤ × ℤ)} {R q : ℕ} (hq : 1 ≤ q)
    (hX : X ∈ supports Λ R) :
    Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤ (1 + v R * Real.log q) ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hc : (Fintype.card (Reg (Qudits q) X) : ℝ) = (q : ℝ) ^ #X := by
    simp [Reg, Fintype.card_pi]
  have hv : (#X : ℝ) ≤ v R := by exact_mod_cast (step_2_8 Λ R 0).2.2.2 X hX
  rw [hc, Real.log_mul (Real.exp_pos 1).ne' (pow_pos hq' _).ne', Real.log_exp, Real.log_pow]
  exact pow_le_pow_left₀ (by positivity) (by gcongr) 2

/-- D3.2.1–D3.2.3. `𝓑 ≤ 1 + 2 v_R μ_R (1 + v_R log q)² |∂_Λ B|`. -/
theorem step_3_2_3' (Λ B : Finset (ℤ × ℤ)) (R q : ℕ) (hq : 1 ≤ q) :
    1 + ∑ X ∈ supports Λ R with (X ∩ B).Nonempty ∧ (X \ B).Nonempty,
        Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
      1 + 2 * v R * μ R * (1 + v R * Real.log q) ^ 2 * #(edgeBoundary Λ B) := by
  -- D3.2.2
  have h1 := sum_le_card_nsmul {X ∈ supports Λ R | (X ∩ B).Nonempty ∧ (X \ B).Nonempty}
    (fun X => Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2) _ fun X hX =>
    log_sq_le_of_mem_supports (Λ := Λ) (R := R) hq (mem_filter.1 hX).1
  -- D3.2.1
  have h2 : (#{X ∈ supports Λ R | (X ∩ B).Nonempty ∧ (X \ B).Nonempty} : ℝ) ≤
      2 * v R * μ R * #(edgeBoundary Λ B) := by exact_mod_cast eq_crossing_count Λ B R
  rw [nsmul_eq_mul] at h1
  nlinarith [sq_nonneg (1 + v R * Real.log q)]

/-- D3.2.1–D3.2.3. `𝓑 ≤ C₁ (1 + |∂_Λ B|)`. -/
theorem step_3_2_3 (Λ B : Finset (ℤ × ℤ)) (R q : ℕ) (hq : 1 ≤ q) :
    1 + ∑ X ∈ supports Λ R with (X ∩ B).Nonempty ∧ (X \ B).Nonempty,
        Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
      C₁ q R * (1 + #(edgeBoundary Λ B)) := by
  have hb : (0 : ℝ) ≤ #(edgeBoundary Λ B) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ C₁ q R := le_max_left _ _
  have h2 := le_max_right 1 (2 * v R * μ R * (1 + v R * Real.log q) ^ 2)
  refine (step_3_2_3' Λ B R q hq).trans ?_
  rw [mul_add, mul_one]
  gcongr
  exact h2

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
noncomputable def Z_r (Cpad r D : ℕ) : ℝ := ∑ j ∈ Icc 1 (m Cpad r D), 1 / ((r + d r D j : ℕ) : ℝ)

/-- D3.6. `a_j = 2 / (Z_r (r + d_j))`. -/
noncomputable def a (Cpad r D j : ℕ) : ℝ := 2 / (Z_r Cpad r D * (r + d r D j : ℕ))

/-- D3.6. `ℰ = ∑_j (r + d_j) a_j²`. -/
noncomputable def ℰ (Cpad r D : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (m Cpad r D), ((r + d r D j : ℕ) : ℝ) * a Cpad r D j ^ 2

variable {Cpad r D : ℕ}

/-- D3.6 (eq:initial-harmonic-weights, eq:initial-harmonic-lower). `∑_j a_j = 2`, `ℰ = 4/Z_r`,
`ℰ = min{∑_j (r + d_j) b_j² : ∑_j b_j = 2}`, and `Z_r ≥ (1/D) log((C_pad + 1)/(2 + D))`. -/
theorem eq_initial_harmonic_weights (hD : 0 < D) (hC : D + 1 < Cpad) (hr : 1 ≤ r) :
    ∑ j ∈ Icc 1 (m Cpad r D), a Cpad r D j = 2 ∧ ℰ Cpad r D = 4 / Z_r Cpad r D ∧
    (∀ b : ℕ → ℝ, ∑ j ∈ Icc 1 (m Cpad r D), b j = 2 →
      ℰ Cpad r D ≤ ∑ j ∈ Icc 1 (m Cpad r D), ((r + d r D j : ℕ) : ℝ) * b j ^ 2) ∧
    1 / D * Real.log ((Cpad + 1) / (2 + D)) ≤ Z_r Cpad r D := by
  have hm : 1 ≤ m Cpad r D := (Nat.le_div_iff_mul_le hD).2 (by
    rw [one_mul]; exact (show D ≤ Cpad - 1 by omega).trans (Nat.le_mul_of_pos_right _ hr))
  have hc : ∀ j, (0 : ℝ) < ((r + d r D j : ℕ) : ℝ) := fun j => by unfold d; positivity
  have hZ : 0 < Z_r Cpad r D :=
    sum_pos (fun j _ => one_div_pos.2 (hc j)) ⟨1, mem_Icc.2 ⟨le_rfl, hm⟩⟩
  -- D3.6.1
  have ha : ∀ j, a Cpad r D j = 2 / Z_r Cpad r D * (1 / ((r + d r D j : ℕ) : ℝ)) := fun j => by
    simp only [a]; field_simp
  have hE : ∀ j, ((r + d r D j : ℕ) : ℝ) * a Cpad r D j ^ 2 =
      4 / Z_r Cpad r D ^ 2 * (1 / ((r + d r D j : ℕ) : ℝ)) := fun j => by
    simp only [a]; field_simp [(hc j).ne']; ring
  have h1 : ∑ j ∈ Icc 1 (m Cpad r D), a Cpad r D j = 2 := by
    simp only [ha, ← mul_sum]; rw [← Z_r]; field_simp
  have h2 : ℰ Cpad r D = 4 / Z_r Cpad r D := by
    simp only [ℰ, hE, ← mul_sum]; rw [← Z_r]; field_simp
  refine ⟨h1, h2, fun b hb => ?_, ?_⟩
  · -- D3.6.1: Cauchy–Schwarz, `4 = (∑ b)² ≤ (∑ (r + d_j) b_j²)(∑ 1/(r + d_j))`
    have := sq_sum_div_le_sum_sq_div (Icc 1 (m Cpad r D)) b fun j _ => one_div_pos.2 (hc j)
    rw [hb, ← Z_r] at this
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
    rw [← mul_sum, ← Z_r] at hsum
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
noncomputable def X_j (A Q₀ : Finset (ℤ × ℤ)) (r D j : ℕ) : Finset (ℤ × ℤ) :=
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

theorem mem_X_j {A : Finset (ℤ × ℤ)} {a b y : ℤ × ℤ} (hab : a ≤ b) {r D j : ℕ} :
    y ∈ X_j A (Icc a b) r D j ↔ y ∈ A ∧ a.1 - rad r D j ≤ y.1 ∧ y.1 ≤ b.1 + rad r D j ∧
      a.2 - rad r D j ≤ y.2 ∧ y.2 ≤ b.2 + rad r D j := by
  unfold X_j rad
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
theorem X_j_subset (hab : a ≤ b) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) {j : ℕ} (hj : j ≤ m Cpad r D) :
    X_j A (Icc a b) r D j ⊆ ambientDilation (Icc a b) (d r D (m Cpad r D)) ∧
      ambientDilation (Icc a b) (d r D (m Cpad r D)) ⊆ Q := by
  refine ⟨fun y hy => ?_, (ambientDilation_mono' (d_m_le hC)).trans hQ₀Q⟩
  have h1 := rad_le_d r D j
  have h2 : d r D j ≤ d r D (m Cpad r D) := by unfold d; gcongr
  rw [mem_X_j hab] at hy
  rw [mem_ambientDilation_Icc hab]
  omega

/-- D3.5.1 (a). `1 ≤ m`, `m D ≤ C_pad r`, `X_0 ⊆ X_1 ⊆ ⋯`, `Q₀^{+d_m} ⊆ Q`. -/
theorem step_3_5_1 (hab : a ≤ b) (hr : 1 ≤ r) (hD : 0 < D) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) :
    1 ≤ m Cpad r D ∧ m Cpad r D * D ≤ Cpad * r ∧
      (∀ i j, i ≤ j → X_j A (Icc a b) r D i ⊆ X_j A (Icc a b) r D j) ∧
      ambientDilation (Icc a b) (d r D (m Cpad r D)) ⊆ Q := by
  refine ⟨?_, ?_, fun i j hij y hy => ?_, (X_j_subset (A := A) hab hC hQ₀Q le_rfl).2⟩
  · have : D ≤ (Cpad - 1) * r :=
      (show D ≤ Cpad - 1 by omega).trans (Nat.le_mul_of_pos_right _ hr)
    exact (Nat.le_div_iff_mul_le hD).2 (by simpa using this)
  · have := d_m_le (r := r) hC; unfold d at this; omega
  · have := rad_mono (r := r) (D := D) hij
    rw [mem_X_j hab] at hy ⊢
    exact ⟨hy.1, by omega⟩

/-- D3.5.2 (b). Every support meeting some `X_j` lies in `A`; no edge of `∂_Λ A` is incident
with any `X_j`. -/
theorem step_3_5_2 (hab : a ≤ b) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    (∀ j ≤ m Cpad r D, ∀ X ∈ supports Λ R, (X ∩ X_j A (Icc a b) r D j).Nonempty → X ⊆ A) ∧
      ∀ j ≤ m Cpad r D, ∀ e ∈ edgeBoundary Λ A,
        e.1 ∉ X_j A (Icc a b) r D j ∧ e.2 ∉ X_j A (Icc a b) r D j := by
  have hQ' : ∀ j ≤ m Cpad r D, X_j A (Icc a b) r D j ⊆ Q := fun j hj =>
    (X_j_subset (A := A) hab hC hQ₀Q hj).1.trans (X_j_subset (A := A) hab hC hQ₀Q hj).2
  refine ⟨fun j hj X hX ⟨x, hx⟩ => ?_, fun j hj e he => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
  · exact subset_of_isSafe hs hRD₀ hX (mem_inter.1 hx).1
      ((mem_X_j hab).1 (mem_inter.1 hx).2).1 (hQ' j hj (mem_inter.1 hx).2)
  · exact IsSafe.not_near hs hRD₀ (hQ' j hj h1) (mem_union_left _ (mem_image_of_mem _ he))
      (by simp)
  · rcases e with ⟨x, y⟩
    exact (mem_sdiff.1 ((mk_mem_interedges_iff _).1 he).2.1).2 ((mem_X_j hab).1 h2).1

/-- D3.5.3 (c). `|∂_Λ X_j| ≤ 4 (r + 2 d_j)` for `1 ≤ j ≤ m`. -/
theorem step_3_5_3 (hab : a ≤ b) (hQ₀r : boxSize (Icc a b) ≤ r) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    ∀ j, 1 ≤ j → j ≤ m Cpad r D →
      #(edgeBoundary Λ (X_j A (Icc a b) r D j)) ≤ 4 * (r + 2 * d r D j) := by
  intro j hj1 hjm
  have hX : X_j A (Icc a b) r D j = A ∩ ambientDilation (Icc a b) (d r D j) :=
    if_neg (by omega)
  have hb := (step_3_5_2 hab hC hQ₀Q hs hRD₀).2 j hjm
  rw [hX] at hb ⊢
  refine (card_edgeBoundary_inter_le hab fun e he => (hb e he).1).trans ?_
  rw [boxSize_Icc hab] at hQ₀r
  have h1 := (le_max_left _ _).trans hQ₀r
  have h2 := (le_max_right _ _).trans hQ₀r
  omega

/-- D3.5.4 (d). A support split by `X_j` is disjoint from `X_i` for `i < j` and contained in
`X_i` for `j < i ≤ m`. -/
theorem step_3_5_4 (hab : a ≤ b) (hD : 2 * R + 2 < D) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    ∀ X ∈ supports Λ R, ∀ j ≤ m Cpad r D, (X ∩ X_j A (Icc a b) r D j).Nonempty →
      (X \ X_j A (Icc a b) r D j).Nonempty →
      (∀ i < j, Disjoint X (X_j A (Icc a b) r D i)) ∧
        ∀ i, j < i → i ≤ m Cpad r D → X ⊆ X_j A (Icc a b) r D i := by
  intro X hX j hj ⟨p, hp⟩ ⟨p', hp'⟩
  have hXA := (step_3_5_2 hab hC hQ₀Q hs hRD₀).1 j hj X hX ⟨p, hp⟩
  rw [mem_inter, mem_X_j hab] at hp
  rw [mem_sdiff, mem_X_j hab] at hp'
  refine ⟨fun i hi => disjoint_left.2 fun s hs hsi => hp'.2 ?_, fun i hi _ s hs => ?_⟩
  · have := l1_le_of_mem_supports hX hs hp'.1
    have := rad_add_le (r := r) (D := D) hi
    rw [mem_X_j hab] at hsi
    exact ⟨hXA hp'.1, by omega⟩
  · have := l1_le_of_mem_supports hX hs hp.1
    have := rad_add_le (r := r) (D := D) hi
    rw [mem_X_j hab]
    exact ⟨hXA hs, by omega⟩

/-- D3.5.5. `C₂ = 1 + 16 v_R μ_R (1 + v_R log q)²`. -/
noncomputable def C₂ (q R : ℕ) : ℝ := 1 + 16 * v R * μ R * (1 + v R * Real.log q) ^ 2

/-- D3.5.5 (e). For `1 ≤ j ≤ m`: `#{split by X_j} ≤ 16 v_R μ_R (r + d_j)` and
`𝓑_j ≤ C₂ (r + d_j)`. -/
theorem step_3_5_5 {q : ℕ} (hq : 1 ≤ q) (hab : a ≤ b) (hr : 1 ≤ r)
    (hQ₀r : boxSize (Icc a b) ≤ r) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation (Icc a b) (Cpad * r) ⊆ Q) (hs : IsSafe D₀ Λ A Q)
    (hRD₀ : (R : ℝ) < D₀) :
    ∀ j, 1 ≤ j → j ≤ m Cpad r D →
      (#{X ∈ supports Λ R | (X ∩ X_j A (Icc a b) r D j).Nonempty ∧
          (X \ X_j A (Icc a b) r D j).Nonempty} : ℝ) ≤ 16 * v R * μ R * (r + d r D j) ∧
        1 + ∑ X ∈ supports Λ R with (X ∩ X_j A (Icc a b) r D j).Nonempty ∧
          (X \ X_j A (Icc a b) r D j).Nonempty,
          Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
          C₂ q R * (r + d r D j) := by
  intro j hj1 hjm
  have hc := step_3_5_3 hab hQ₀r hC hQ₀Q hs hRD₀ j hj1 hjm
  have hcR : (#(edgeBoundary Λ (X_j A (Icc a b) r D j)) : ℝ) ≤ 4 * (r + 2 * d r D j) := by
    exact_mod_cast hc
  have hrd : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) ≤ d r D j := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have h1 : (#{X ∈ supports Λ R | (X ∩ X_j A (Icc a b) r D j).Nonempty ∧
        (X \ X_j A (Icc a b) r D j).Nonempty} : ℝ) ≤
        2 * v R * μ R * #(edgeBoundary Λ (X_j A (Icc a b) r D j)) := by
      exact_mod_cast eq_crossing_count Λ _ R
    have hK : (0 : ℝ) ≤ v R * μ R := by positivity
    nlinarith
  · have h1 := step_3_2_3' Λ (X_j A (Icc a b) r D j) R q hq
    have hK : (0 : ℝ) ≤ 2 * v R * μ R * (1 + v R * Real.log q) ^ 2 := by positivity
    unfold C₂
    nlinarith [mul_le_mul_of_nonneg_left hcR hK, mul_nonneg hK hd0]

end D35

/-- D3.5. Let `D > 2R + 2`, `C_pad > D + 1`, `m = ⌊(C_pad - 1) r / D⌋`, `d_j = r + jD`,
`X_0 = A ∩ Q₀`, `X_j = A ∩ Q₀^{+d_j}`. Then (a) `1 ≤ m`, `m D ≤ C_pad r`,
`X_0 ⊆ X_1 ⊆ ⋯ ⊆ X_m`, `Q₀^{+d_m} ⊆ Q`; (b) every support meeting some `X_j` lies in `A`, and
no edge of `∂_Λ A` is incident with any `X_j`; (c) `|∂_Λ X_j| ≤ 4 (r + 2 d_j)`; (d) a support
split by `X_j` is disjoint from `X_i` for `i < j` and contained in `X_i` for `j < i ≤ m`;
(e) `#{supports split by X_j} ≤ 16 v_R μ_R (r + d_j)` and `𝓑_j ≤ C₂ (r + d_j)`. -/
theorem step_3_5 {q R : ℕ} {D₀ : ℝ} {Λ A Q Q₀ : Finset (ℤ × ℤ)} {r D Cpad : ℕ} (hq : 1 ≤ q)
    (_hA : A ⊆ Λ) (_hQ : IsIntRect Q) (hs : IsSafe D₀ Λ A Q) (hRD₀ : (R : ℝ) < D₀) (hr : 1 ≤ r)
    (hQ₀ : IsIntRect Q₀) (hQ₀r : boxSize Q₀ ≤ r) (hD : 2 * R + 2 < D) (hC : D + 1 < Cpad)
    (hQ₀Q : ambientDilation Q₀ (Cpad * r) ⊆ Q) :
    (1 ≤ m Cpad r D ∧ m Cpad r D * D ≤ Cpad * r ∧
      (∀ i j, i ≤ j → X_j A Q₀ r D i ⊆ X_j A Q₀ r D j) ∧
      ambientDilation Q₀ (d r D (m Cpad r D)) ⊆ Q) ∧
    ((∀ j ≤ m Cpad r D, ∀ X ∈ supports Λ R, (X ∩ X_j A Q₀ r D j).Nonempty → X ⊆ A) ∧
      ∀ j ≤ m Cpad r D, ∀ e ∈ edgeBoundary Λ A,
        e.1 ∉ X_j A Q₀ r D j ∧ e.2 ∉ X_j A Q₀ r D j) ∧
    (∀ j, 1 ≤ j → j ≤ m Cpad r D → #(edgeBoundary Λ (X_j A Q₀ r D j)) ≤ 4 * (r + 2 * d r D j)) ∧
    (∀ X ∈ supports Λ R, ∀ j ≤ m Cpad r D, (X ∩ X_j A Q₀ r D j).Nonempty →
      (X \ X_j A Q₀ r D j).Nonempty →
      (∀ i < j, Disjoint X (X_j A Q₀ r D i)) ∧
        ∀ i, j < i → i ≤ m Cpad r D → X ⊆ X_j A Q₀ r D i) ∧
    ∀ j, 1 ≤ j → j ≤ m Cpad r D →
      (#{X ∈ supports Λ R | (X ∩ X_j A Q₀ r D j).Nonempty ∧ (X \ X_j A Q₀ r D j).Nonempty} : ℝ)
          ≤ 16 * v R * μ R * (r + d r D j) ∧
        1 + ∑ X ∈ supports Λ R with (X ∩ X_j A Q₀ r D j).Nonempty ∧
          (X \ X_j A Q₀ r D j).Nonempty,
          Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
          C₂ q R * (r + d r D j) := by
  obtain ⟨a, b, hab, rfl⟩ := hQ₀
  exact ⟨step_3_5_1 hab hr (by omega) hC hQ₀Q, step_3_5_2 hab hC hQ₀Q hs hRD₀,
    step_3_5_3 hab hQ₀r hC hQ₀Q hs hRD₀, step_3_5_4 hab hD hC hQ₀Q hs hRD₀,
    step_3_5_5 hq hab hr hQ₀r hC hQ₀Q hs hRD₀⟩

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

end D314


end AreaLaw
