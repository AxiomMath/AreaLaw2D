import AreaLawRefactored.S02_Preliminaries

/-!
# §3 Marginal tails and an initial box estimate

Digest `digest/03-initial-box.md`, paper `paper/sections/02-initial.tex`.
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

/-! ## D3.16.1 Children of a parent rectangle -/

section Children

variable (a b : ℤ × ℤ) (r : ℕ)

/-- D3.16.1. Number of chunks of `r` sites along the first axis of `[a, b]`. -/
def nChunks₁ : ℕ := (b.1 + 1 - a.1).toNat ⌈/⌉ r

/-- D3.16.1. Number of chunks of `r` sites along the second axis of `[a, b]`. -/
def nChunks₂ : ℕ := (b.2 + 1 - a.2).toNat ⌈/⌉ r

/-- D3.16.1. The child `Q_{(i,j)}` of `[a, b]`: product of the `i`-th and `j`-th chunks. -/
noncomputable def child (i j : ℕ) : Finset (ℤ × ℤ) :=
  Icc (a.1 + i * r, a.2 + j * r) (min (a.1 + i * r + r - 1) b.1, min (a.2 + j * r + r - 1) b.2)

variable {a b r} {i j i' j' M C : ℕ} {p : ℤ × ℤ}

theorem lt_nChunks₁_iff (hr : 1 ≤ r) : i < nChunks₁ a b r ↔ a.1 + i * r ≤ b.1 := by
  rw [nChunks₁, ← not_le, ceilDiv_le_iff_le_mul (by omega), not_le, mul_comm]; omega

theorem lt_nChunks₂_iff (hr : 1 ≤ r) : j < nChunks₂ a b r ↔ a.2 + j * r ≤ b.2 := by
  rw [nChunks₂, ← not_le, ceilDiv_le_iff_le_mul (by omega), not_le, mul_comm]; omega

theorem nChunks_le (hab : a ≤ b) (hr : 1 ≤ r) (hQ : boxSize (Icc a b) ≤ M * r) :
    nChunks₁ a b r ≤ M ∧ nChunks₂ a b r ≤ M := by
  rw [boxSize_Icc hab] at hQ
  rw [nChunks₁, nChunks₂, ceilDiv_le_iff_le_mul (by omega), ceilDiv_le_iff_le_mul (by omega)]
  simp only [mul_comm r M]
  exact ⟨(le_max_left _ _).trans hQ, (le_max_right _ _).trans hQ⟩

theorem mem_child : p ∈ child a b r i j ↔ a.1 + i * r ≤ p.1 ∧ p.1 < a.1 + i * r + r ∧
    p.1 ≤ b.1 ∧ a.2 + j * r ≤ p.2 ∧ p.2 < a.2 + j * r + r ∧ p.2 ≤ b.2 := by
  simp only [child, mem_Icc, Prod.le_def, le_min_iff]; omega

theorem child_subset : child a b r i j ⊆ Icc a b := fun p hp => by
  rw [mem_child] at hp
  have : (0 : ℤ) ≤ i * r := by positivity
  have : (0 : ℤ) ≤ j * r := by positivity
  rw [mem_Icc, Prod.le_def, Prod.le_def]; omega

theorem isIntRect_child (hr : 1 ≤ r) (hi : i < nChunks₁ a b r) (hj : j < nChunks₂ a b r) :
    IsIntRect (child a b r i j) := by
  rw [lt_nChunks₁_iff hr] at hi
  rw [lt_nChunks₂_iff hr] at hj
  exact ⟨_, _, Prod.le_def.2 ⟨le_min (by omega) hi, le_min (by omega) hj⟩, rfl⟩

theorem boxSize_child_le : boxSize (child a b r i j) ≤ r := by
  by_cases h : (a.1 + i * r, a.2 + j * r) ≤
      (min (a.1 + i * r + r - 1) b.1, min (a.2 + j * r + r - 1) b.2)
  · rw [child, boxSize_Icc h]; simp only; omega
  · rw [child, Icc_eq_empty h]; simp [boxSize]

theorem exists_mem_child (hr : 1 ≤ r) (hp : p ∈ Icc a b) :
    ∃ i < nChunks₁ a b r, ∃ j < nChunks₂ a b r, p ∈ child a b r i j := by
  rw [mem_Icc, Prod.le_def, Prod.le_def] at hp
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = p.1 - a.1 := ⟨(p.1 - a.1).toNat, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = p.2 - a.2 := ⟨(p.2 - a.2).toNat, by omega⟩
  have h1 : ((s / r : ℕ) : ℤ) * r ≤ s := by exact_mod_cast Nat.div_mul_le_self s r
  have h2 : (s : ℤ) < ((s / r : ℕ) : ℤ) * r + r := by
    exact_mod_cast Nat.lt_div_mul_add (a := s) (b := r) (by omega)
  have h3 : ((t / r : ℕ) : ℤ) * r ≤ t := by exact_mod_cast Nat.div_mul_le_self t r
  have h4 : (t : ℤ) < ((t / r : ℕ) : ℤ) * r + r := by
    exact_mod_cast Nat.lt_div_mul_add (a := t) (b := r) (by omega)
  exact ⟨s / r, (lt_nChunks₁_iff hr).2 (by omega), t / r, (lt_nChunks₂_iff hr).2 (by omega),
    mem_child.2 (by omega)⟩

/-- Chunk positions of a site in a padded child `Q_{(i,j)}^{+Cr}` differ from `(i, j)` by at most
`C` along each axis. -/
theorem le_add_of_mem_child (hp : p ∈ child a b r i' j')
    (hp' : p ∈ ambientDilation (child a b r i j) (C * r)) :
    i' ≤ i + C ∧ i ≤ i' + C ∧ j' ≤ j + C ∧ j ≤ j' + C := by
  obtain ⟨x, hx, h1, h2⟩ := mem_ambientDilation.1 hp'
  rw [mem_child] at hp hx
  rw [abs_le] at h1 h2
  push_cast at h1 h2
  have key : ∀ {k k' : ℕ} {y z : ℤ}, (k : ℤ) * r ≤ y → y < k * r + r → (k' : ℤ) * r ≤ z →
      z < k' * r + r → y - z ≤ C * r → k ≤ k' + C := fun {k k' _ _} h1 h2 h3 h4 h5 => by
    have := lt_of_mul_lt_mul_right (show (k : ℤ) * r < (k' + C + 1) * r by linarith)
      (Nat.cast_nonneg r)
    omega
  exact ⟨key (y := p.1 - a.1) (z := x.1 - a.1) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith),
    key (y := x.1 - a.1) (z := p.1 - a.1) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith),
    key (y := p.2 - a.2) (z := x.2 - a.2) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith),
    key (y := x.2 - a.2) (z := p.2 - a.2) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)⟩

theorem eq_of_mem_child (hp : p ∈ child a b r i j) (hp' : p ∈ child a b r i' j') :
    i = i' ∧ j = j' := by
  have h := le_add_of_mem_child (C := 0) hp' (mem_ambientDilation.2 ⟨p, hp, by simp, by simp⟩)
  omega

/-- D3.16.2. A child `C` positions from the first and `C + 2` from the last chunk along both
axes is interior: `Q_i^{+Cr} ⊆ Q`. -/
theorem ambientDilation_child_subset (hr : 1 ≤ r) (hi : i + C + 2 ≤ nChunks₁ a b r)
    (hj : j + C + 2 ≤ nChunks₂ a b r) (hiC : C ≤ i) (hjC : C ≤ j) :
    ambientDilation (child a b r i j) (C * r) ⊆ Icc a b := fun p hp => by
  obtain ⟨x, hx, h1, h2⟩ := mem_ambientDilation.1 hp
  rw [mem_child] at hx
  rw [abs_le] at h1 h2
  push_cast at h1 h2
  have hx1 := (lt_nChunks₁_iff hr).1 (show i + C + 1 < nChunks₁ a b r by omega)
  have hy1 := (lt_nChunks₂_iff hr).1 (show j + C + 1 < nChunks₂ a b r by omega)
  push_cast at hx1 hy1
  have hCi : (C : ℤ) * r ≤ i * r := by exact_mod_cast Nat.mul_le_mul_right r hiC
  have hCj : (C : ℤ) * r ≤ j * r := by exact_mod_cast Nat.mul_le_mul_right r hjC
  rw [mem_Icc, Prod.le_def, Prod.le_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- D3.16.2. At most `2(C + 2)` positions of `[0, n)` violate `C ≤ a ∧ a + C + 2 ≤ n`. -/
theorem card_not_interior_le (n C : ℕ) :
    #((univ : Finset (Fin n)).filter fun a => ¬(C ≤ a.val ∧ a.val + C + 2 ≤ n)) ≤ 2 * (C + 2) := by
  have hsub : ((univ : Finset (Fin n)).filter
      fun a => ¬(C ≤ a.val ∧ a.val + C + 2 ≤ n)).map Fin.valEmbedding ⊆
      range C ∪ Ico (n - (C + 1)) n := by
    intro x hx
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [mem_union, mem_range, mem_Ico]
    have := a.isLt
    omega
  have := (card_le_card hsub).trans (card_union_le _ _)
  simp only [card_map, card_range, Nat.card_Ico] at this
  omega

end Children

/-! ## D3.15 `F_box(r)` -/

section D315

open Matrix

variable (q R : ℕ) (J Δ : ℝ)

/-- The values `S_Ω(A ∩ Q)` whose supremum is `F_box(r)` (D3.15). -/
def boxEntropies (r : ℕ) : Set ℝ :=
  {s | ∃ D₀ : ℝ, 2 * R + 10 < D₀ ∧ ∃ (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
    IsAdmissible Λ R J Φ ∧ ∃ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
    hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω ∧ HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ ∧
    ∃ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)), IsIntRect Q ∧ IsSafe D₀ Λ A Q ∧
      boxSize Q ≤ r ∧ s = (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ Q ⊆ Λ)}

/-- D3.15. For an integer `r ≥ 1`, `F_box(r) = sup S_Ω(A ∩ Q)`, sup over admissible `H` (unique
ground vector, gap `Δ`), domains `Λ`, cuts `A ⊆ Λ`, safe integer rectangles `Q` of size `≤ r`;
`q, R, J, Δ` fixed. `F_box` nondecreasing, `0 ≤ F_box(r) ≤ r² log q`. -/
noncomputable def F_box (r : ℕ) : ℝ := sSup (boxEntropies q R J Δ r)

variable {q R J Δ}

theorem le_of_mem_boxEntropies {r : ℕ} {s : ℝ} (hs : s ∈ boxEntropies q R J Δ r) :
    0 ≤ s ∧ s ≤ (r : ℝ) ^ 2 * Real.log q := by
  obtain ⟨-, -, Λ, Φ, -, Ω, hΩ, -, -, -, A, hA, Q, -, -, hQ, rfl⟩ := hs
  refine ⟨SubState.regionEntropy_nonneg _ _, ?_⟩
  have h := ((pureState Ω hΩ).restrict (inter_subset_left.trans hA : A ∩ Q ⊆ Λ)).entropy_le_log_card
  rw [card_reg_const (fun _ => Fintype.card_fin q), Nat.cast_pow, Real.log_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg q))
  exact_mod_cast (card_le_card inter_subset_right).trans
    ((card_le_boxSize_sq Q).trans (Nat.pow_le_pow_left hQ 2))

theorem F_box_nonneg (r : ℕ) : 0 ≤ F_box q R J Δ r :=
  Real.sSup_nonneg fun _ hs => (le_of_mem_boxEntropies hs).1

theorem le_F_box {D₀ : ℝ} (hD₀ : 2 * R + 10 < D₀) {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ}
    (hΦ : IsAdmissible Λ R J Φ) {Ω : Reg (Qudits q) Λ → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1) {E₀ : ℝ}
    (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) {Q : Finset (ℤ × ℤ)} (hQ : IsIntRect Q)
    (hs : IsSafe D₀ Λ A Q) {r : ℕ} (hr : boxSize Q ≤ r) :
    (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤ F_box q R J Δ r :=
  le_csSup ⟨_, fun _ hs => (le_of_mem_boxEntropies hs).2⟩
    ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hr, rfl⟩

theorem F_box_mono : Monotone (F_box q R J Δ) := by
  intro r r' hrr
  refine Real.sSup_le (fun s hs => ?_) (F_box_nonneg r')
  obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hQr, rfl⟩ := hs
  exact le_F_box hD₀ hΦ hΩ hE hgap hA hQ hs (hQr.trans hrr)

end D315

/-! ## D3.16.6–D3.16.8 Solving the recursion -/

section Recursion

variable {F : ℕ → ℝ} {M : ℕ} {lam K : ℝ}

/-- D3.16.6. `f_{j+1} ≤ λ f_j + K M^j` gives `f_j ≤ λ^j f_0 + K (λ^j - M^j)/(λ - M)`. -/
theorem step_3_16_6 (hM : 1 ≤ M) (hlam : (M : ℝ) < lam)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r) (j : ℕ) :
    F (M ^ j) ≤ lam ^ j * F 1 + K / (lam - M) * (lam ^ j - (M : ℝ) ^ j) := by
  have hlM : 0 < lam - M := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hrec (M ^ j) (Nat.one_le_pow _ _ hM)
    rw [show M * M ^ j = M ^ (j + 1) by ring] at h1
    calc F (M ^ (j + 1)) ≤ lam * (lam ^ j * F 1 + K / (lam - M) * (lam ^ j - (M : ℝ) ^ j)) +
          K * ((M ^ j : ℕ) : ℝ) :=
        h1.trans (by gcongr; linarith [(Nat.cast_nonneg M).trans_lt hlam])
      _ = _ := by push_cast; field_simp; ring

/-- D3.16.6–D3.16.8. `F` nondecreasing, `M ≥ 2`, `M < λ`, `K ≥ 0`, `F(Mr) ≤ λ F(r) + K r`:
`F(r) ≤ C r^{log_M λ}` for `r ≥ 1`. -/
theorem step_3_16_8 (hF : Monotone F) (hM : 2 ≤ M) (hlam : (M : ℝ) < lam) (hK : 0 ≤ K)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r) :
    ∃ C, ∀ r, 1 ≤ r → F r ≤ C * (r : ℝ) ^ (Real.log lam / Real.log M) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hlM : 0 < lam - M := by linarith
  set e := Real.log lam / Real.log M
  set B := |F 1| + K / (lam - M)
  -- D3.16.6
  have hpow (j : ℕ) : F (M ^ j) ≤ B * lam ^ j := by
    have h := step_3_16_6 (by omega) hlam hrec j
    have : 0 ≤ K / (lam - M) * (M : ℝ) ^ j := by positivity
    have := le_abs_self (F 1)
    have : 0 ≤ lam ^ j := pow_nonneg (by linarith) j
    nlinarith
  -- D3.16.7: `λ^j = (M^j)^{1+e₀}`
  have hrpow (j : ℕ) : lam ^ j = ((M : ℝ) ^ j) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by positivity)]
    simp only [e]
    field_simp [(Real.log_pos hM1).ne']
  -- D3.16.8: `M^{j-1} < r ≤ M^j`
  refine ⟨B * (M : ℝ) ^ e, fun r hr => ?_⟩
  set j := Nat.clog M r
  have hjr : ((M : ℝ) ^ j) ≤ M * r := by
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · have := Nat.pow_pred_clog_lt_self (b := M) (by omega) h1
      have h2 : M ^ j = M * M ^ (j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.clog_pos (by omega) h1)]
      exact_mod_cast h2 ▸ Nat.mul_le_mul_left _ this.le
    · obtain rfl : r = 1 := le_antisymm h1 hr
      simp [j]; linarith
  have : 0 ≤ B := by positivity
  have : 0 ≤ e := div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg hM1.le)
  calc F r ≤ B * ((M : ℝ) ^ j) ^ e := hrpow j ▸ (hF (Nat.le_pow_clog (by omega) r)).trans (hpow j)
    _ ≤ B * ((M : ℝ) * r) ^ e := by gcongr
    _ = B * (M : ℝ) ^ e * (r : ℝ) ^ e := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

end Recursion

end AreaLaw
