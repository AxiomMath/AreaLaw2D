import AreaLaw.S03_InitialBox.Lemma32

/-!
# §3 Marginal tails and an initial box estimate

Digest `digest/03-initial-box.md`, paper `paper/sections/02-initial.tex`. Lemma 3.1 (§3.1) is
in `S03_InitialBox/MarginalTails.lean`, Lemma 3.2 (§3.2) in `S03_InitialBox/BufferDiscount.lean`,
`Filters.lean`, `ZeroFloorPinning.lean`, `ThreeLines.lean`, `TrialNorm.lean`, `Lemma32.lean`;
this file is §3.3: `F_box` (D3.15) and Proposition 3.3 (D3.16).
-/

namespace AreaLaw

open Arealaw OpenAI Finset

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
noncomputable def boxEntropySup (r : ℕ) : ℝ := sSup (boxEntropies q R J Δ r)

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

theorem boxEntropySup_nonneg (r : ℕ) : 0 ≤ boxEntropySup q R J Δ r :=
  Real.sSup_nonneg fun _ hs => (le_of_mem_boxEntropies hs).1

theorem le_boxEntropySup {D₀ : ℝ} (hD₀ : 2 * R + 10 < D₀) {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ}
    (hΦ : IsAdmissible Λ R J Φ) {Ω : Reg (Qudits q) Λ → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1) {E₀ : ℝ}
    (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) {Q : Finset (ℤ × ℤ)} (hQ : IsIntRect Q)
    (hs : IsSafe D₀ Λ A Q) {r : ℕ} (hr : boxSize Q ≤ r) :
    (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤
      boxEntropySup q R J Δ r :=
  le_csSup ⟨_, fun _ hs => (le_of_mem_boxEntropies hs).2⟩
    ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hr, rfl⟩

theorem boxEntropySup_mono : Monotone (boxEntropySup q R J Δ) := by
  intro r r' hrr
  refine Real.sSup_le (fun s hs => ?_) (boxEntropySup_nonneg r')
  obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hQr, rfl⟩ := hs
  exact le_boxEntropySup hD₀ hΦ hΩ hE hgap hA hQ hs (hQr.trans hrr)

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

/-! ## D3.16 Proposition 3.3 -/

section D316

open Matrix

/-- D3.16.3. `p₀ = (2 C_pad + 5)⁻²`. -/
noncomputable def p₀ (Cpad : ℕ) : ℝ := 1 / (2 * Cpad + 5 : ℝ) ^ 2

/-- D3.16.2. `B_M = 4 (C_pad + 2) M`. -/
def noninteriorBound (Cpad M : ℕ) : ℕ := 4 * (Cpad + 2) * M

/-- Telescoping chain rule along an order `π` of the children (child `i` sits at position `π i`). -/
theorem step_3_16_3_chain {σ : Type*} [DecidableEq σ] {n : ℕ} (X : Fin n → Finset σ)
    (F : Finset σ → ℝ) (π : Equiv.Perm (Fin n)) :
    F (univ.biUnion X) - F ∅ = ∑ i, (F (X i ∪ (univ.filter fun j => π j < π i).biUnion X) -
      F ((univ.filter fun j => π j < π i).biUnion X)) := by
  set W : ℕ → Finset σ := fun k => (univ.filter fun j => (π j : ℕ) < k).biUnion X
  have h0 : W 0 = ∅ := by simp [W]
  have hn : W n = univ.biUnion X := by simp [W]
  have hs : ∀ i, W (π i + 1) = X i ∪ (univ.filter fun j => π j < π i).biUnion X := by
    intro i
    simp only [W]
    rw [← biUnion_insert]
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (π.injective (Fin.ext h))
    · rintro (rfl | h)
      · omega
      · exact Nat.lt_succ_of_lt h
  have hl : ∀ i, W (π i) = (univ.filter fun j => π j < π i).biUnion X := by
    intro i; simp [W]
  rw [← h0, ← hn, ← Finset.sum_range_sub (fun k => F (W k)),
    ← Fin.sum_univ_eq_sum_range (fun k => F (W (k + 1)) - F (W k)), ← Equiv.sum_comp π]
  simp only [hs, hl]

/-- Exactly a `1/(#N+1)` fraction of the orders put child `i` after all of `N ∌ i`. -/
theorem step_3_16_3_count {n : ℕ} (i : Fin n) (N : Finset (Fin n)) (hi : i ∉ N) :
    #(univ.filter fun π : Equiv.Perm (Fin n) => ∀ j ∈ N, π j < π i) * (#N + 1) = n.factorial := by
  set S := insert i N
  set W : Fin n → Finset (Equiv.Perm (Fin n)) :=
    fun k => univ.filter fun π => ∀ j ∈ S, j ≠ k → π j < π k
  have hWi : W i = univ.filter fun π : Equiv.Perm (Fin n) => ∀ j ∈ N, π j < π i := by
    ext π
    simp only [W, S, mem_filter, mem_univ, true_and, forall_mem_insert, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, true_and]
    exact ⟨fun h j hj => h j hj (fun e => hi (e ▸ hj)), fun h j hj _ => h j hj⟩
  have hmap : ∀ k ∈ S, ∀ l ∈ S, ∀ π ∈ W k, π * Equiv.swap k l ∈ W l := by
    intro k hk l hl π hπ
    simp only [W, mem_filter, mem_univ, true_and, Equiv.Perm.mul_apply] at hπ ⊢
    intro j hj hjl
    rw [Equiv.swap_apply_right]
    by_cases hjk : j = k
    · subst hjk; rw [Equiv.swap_apply_left]; exact hπ l hl (Ne.symm hjl)
    · rw [Equiv.swap_apply_of_ne_of_ne hjk hjl]; exact hπ j hj hjk
  have hcard : ∀ k ∈ S, #(W k) = #(W i) := by
    intro k hk
    refine card_nbij' (· * Equiv.swap k i) (· * Equiv.swap i k)
      (fun π hπ => hmap k hk i (mem_insert_self _ _) π hπ)
      (fun π hπ => hmap i (mem_insert_self _ _) k hk π hπ) ?_ ?_
    · intro π _; simp [mul_assoc, Equiv.swap_comm k i]
    · intro π _; simp [mul_assoc, Equiv.swap_comm k i]
  have hcover : (univ : Finset (Equiv.Perm (Fin n))) = S.biUnion W := by
    ext π
    simp only [mem_univ, mem_biUnion, true_iff]
    obtain ⟨k, hk, hmax⟩ := S.exists_max_image (fun j => π j) ⟨i, mem_insert_self _ _⟩
    refine ⟨k, hk, ?_⟩
    simp only [W, mem_filter, mem_univ, true_and]
    exact fun j hj hjk => lt_of_le_of_ne (hmax j hj) (fun e => hjk (π.injective e))
  have hdisjW : (S : Set (Fin n)).PairwiseDisjoint W := by
    intro k hk l hl hkl
    rw [Function.onFun, Finset.disjoint_left]
    intro π h1 h2
    simp only [W, mem_filter, mem_univ, true_and] at h1 h2
    exact lt_asymm (h1 l (mem_coe.1 hl) (Ne.symm hkl)) (h2 k (mem_coe.1 hk) hkl)
  have := congrArg Finset.card hcover
  rw [card_univ, Fintype.card_perm, Fintype.card_fin, card_biUnion hdisjW, sum_congr rfl hcard,
    sum_const, smul_eq_mul, card_insert_of_notMem hi, hWi] at this
  rw [this, mul_comm]

/-- D3.16.3–D3.16.4. Children `X i` (pairwise disjoint), an interior set `G`, for interior `i` a
neighbour set `Nb i ∌ i` with `#(Nb i) + 1 ≤ P` whose children cover the buffer `T i`, and the
buffer discount `S(X i | T i) ≤ S(X i)/2 + c`. Averaging the chain rule over all orders of the
children: `S(⋃ X) ≤ ∑ S(X i) - (1/(2P)) ∑_{i ∈ G} S(X i) + #G c`. -/
theorem step_3_16_4 {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {U : Finset σ} (ρ : Arealaw.MState (Reg loc U) ℂ) {n : ℕ}
    (X : Fin n → Finset σ) (hX : ∀ i, X i ⊆ U) (hdisj : Pairwise fun i j => Disjoint (X i) (X j))
    (G : Finset (Fin n)) (Nb : Fin n → Finset (Fin n)) (T : Fin n → Finset σ)
    (hT : ∀ i, T i ⊆ U) (P : ℕ) (hNb : ∀ i ∈ G, i ∉ Nb i ∧ #(Nb i) + 1 ≤ P)
    (hTN : ∀ i ∈ G, T i ⊆ (Nb i).biUnion X) {c : ℝ} (hc : 0 ≤ c)
    (hbuf : ∀ i ∈ G, ρ.regionEntropy (union_subset (hX i) (hT i)) - ρ.regionEntropy (hT i) ≤
      ρ.regionEntropy (hX i) / 2 + c) :
    ρ.regionEntropy (biUnion_subset.2 fun i _ => hX i : univ.biUnion X ⊆ U) ≤
      ∑ i, ρ.regionEntropy (hX i) - 1 / (2 * P) * ∑ i ∈ G, ρ.regionEntropy (hX i) + #G * c := by
  obtain ⟨f, hf⟩ : ∃ f : Finset σ → ℝ, ∀ A (h : A ⊆ U), ρ.regionEntropy h = f A :=
    ⟨fun A => if h : A ⊆ U then ρ.regionEntropy h else 0, fun A h => (dif_pos h).symm⟩
  have hfnn : ∀ A, A ⊆ U → 0 ≤ f A := fun A h => hf A h ▸ SubState.regionEntropy_nonneg _ _
  have hf0 : f ∅ = 0 := by rw [← hf ∅ (empty_subset U)]; exact MState.regionEntropy_empty ρ
  simp only [hf] at hbuf ⊢
  set Y : Equiv.Perm (Fin n) → Fin n → Finset σ :=
    fun π i => (univ.filter fun j => π j < π i).biUnion X
  set E : Fin n → Finset (Equiv.Perm (Fin n)) :=
    fun i => univ.filter fun π => ∀ j ∈ Nb i, π j < π i
  have hY : ∀ π i, Y π i ⊆ U := fun π i => biUnion_subset.2 fun j _ => hX j
  have hXY : ∀ π i, Disjoint (X i) (Y π i) := fun π i =>
    disjoint_biUnion_right _ _ _ |>.2 fun j hj => hdisj fun e => by simp [e] at hj
  -- D3.16.3: the chain rule along every order `π`
  have hchain : ∀ π, f (univ.biUnion X) = ∑ i, (f (X i ∪ Y π i) - f (Y π i)) := fun π => by
    simpa [hf0] using step_3_16_3_chain X f π
  -- D3.16.3: each conditional term is at most `S(X i)`, and discounted when `π ∈ E i`
  have hterm : ∀ π i, f (X i ∪ Y π i) - f (Y π i) ≤
      f (X i) - if i ∈ G ∧ π ∈ E i then f (X i) / 2 - c else 0 := by
    intro π i
    split_ifs with h
    · obtain ⟨hi, hπ⟩ := h
      have hTY : T i ⊆ Y π i := (hTN i hi).trans (biUnion_subset_biUnion_of_subset_left _
        fun j hj => by simp only [E, mem_filter] at hπ; simpa using hπ.2 j hj)
      have := ρ.regionEntropy_union_sub_le ((hXY π i).mono_right hTY)
        ((hXY π i).mono_right sdiff_subset) disjoint_sdiff (hX i) (hT i)
        (sdiff_subset.trans (hY π i))
      simp only [hf, union_sdiff_of_subset hTY] at this
      linarith [hbuf i hi]
    · have := Arealaw.regionEntropy_union_le ρ (hXY π i) (hX i) (hY π i)
      simp only [hf] at this
      linarith
  -- D3.16.4: average over orders, using `#E i ≥ n!/P`
  have hsum : ∀ i, ∑ π, (f (X i ∪ Y π i) - f (Y π i)) ≤ n.factorial * f (X i) -
      if i ∈ G then n.factorial * (f (X i) / (2 * P) - c) else 0 := by
    intro i
    refine (sum_le_sum fun π _ => hterm π i).trans ?_
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    split_ifs with hi
    · simp only [hi, true_and]
      rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
      have hcnt := step_3_16_3_count i (Nb i) (hNb i hi).1
      have hP := (hNb i hi).2
      have ha := hfnn (X i) (hX i)
      have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
      have h1 : (n.factorial : ℝ) ≤ P * #(E i) := by
        rw [← hcnt]; push_cast; nlinarith [(show ((#(Nb i) : ℝ) + 1) ≤ P by exact_mod_cast hP)]
      have h2 : (#(E i) : ℝ) ≤ n.factorial := by
        rw [← hcnt]; push_cast; nlinarith
      have h3 : (n.factorial : ℝ) * (f (X i) / (2 * P)) ≤ #(E i) * (f (X i) / 2) := by
        rw [show (n.factorial : ℝ) * (f (X i) / (2 * P)) = n.factorial / P * (f (X i) / 2) by
          field_simp]
        exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hPpos).2 (by linarith)) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right h2 hc]
    · simp [hi]
  have htot : (n.factorial : ℝ) * f (univ.biUnion X) ≤
      n.factorial * (∑ i, f (X i) - 1 / (2 * P) * ∑ i ∈ G, f (X i) + #G * c) := by
    calc (n.factorial : ℝ) * f (univ.biUnion X)
        = ∑ π : Equiv.Perm (Fin n), f (univ.biUnion X) := by simp [card_univ, Fintype.card_perm]
      _ = ∑ i, ∑ π, (f (X i ∪ Y π i) - f (Y π i)) := by
        rw [sum_congr rfl fun π _ => hchain π, sum_comm]
      _ ≤ ∑ i, (n.factorial * f (X i) - if i ∈ G then n.factorial * (f (X i) / (2 * P) - c)
          else 0) := sum_le_sum fun i _ => hsum i
      _ = _ := by
        rw [sum_sub_distrib, sum_ite_mem, univ_inter, ← mul_sum, ← mul_sum, sum_sub_distrib,
          sum_const, nsmul_eq_mul, ← sum_div]
        ring
  exact le_of_mul_le_mul_left htot (by positivity)

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  {Λ A : Finset (ℤ × ℤ)} {a b : ℤ × ℤ}

/-- Positions within `C` of a position: at most `2C + 1` of them on an axis of `n` chunks. -/
theorem card_near_le (n i C : ℕ) :
    #((univ : Finset (Fin n)).filter fun i' : Fin n => i'.val ≤ i + C ∧ i ≤ i'.val + C) ≤
      2 * C + 1 := by
  have h := card_le_card (show ((univ : Finset (Fin n)).filter
      fun i' : Fin n => i'.val ≤ i + C ∧ i ≤ i'.val + C).map Fin.valEmbedding ⊆
        Icc (i - C) (i + C) by
    intro x hx
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [mem_Icc]; omega)
  simp only [card_map, Nat.card_Icc] at h
  omega

/-- D3.16.1–D3.16.4 for one safe parent `Q = [a, b]` of size `≤ M r`: if `F` bounds `S(A ∩ Q₀)`
for the rectangles `Q₀ ⊆ Q` of size `≤ r` and the buffer discount of Lemma 3.2 holds in `Q`,
then `S(A ∩ Q) ≤ [(1 - p₀/2) M² + (p₀/2) B_M] F + C_buf M² r`. -/
theorem step_3_16_3 (ρ : Arealaw.MState (Reg loc Λ) ℂ) (hA : A ⊆ Λ) (hab : a ≤ b) {M r : ℕ}
    (hr : 1 ≤ r) (hQr : boxSize (Icc a b) ≤ M * r) {F : ℝ}
    (hF : ∀ Q₀, IsIntRect Q₀ → Q₀ ⊆ Icc a b → boxSize Q₀ ≤ r →
      ρ.regionEntropy (inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) ≤ F)
    {Cpad : ℕ} {Cbuf : ℝ} (hCbuf : 0 ≤ Cbuf)
    (hbuf : ∀ Q₀, IsIntRect Q₀ → boxSize Q₀ ≤ r → ambientDilation Q₀ (Cpad * r) ⊆ Icc a b →
      ρ.regionEntropy ((union_subset (inter_subset_left.trans hA)
            (sdiff_subset.trans (inter_subset_left.trans hA))) :
            A ∩ Q₀ ∪ (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) -
        ρ.regionEntropy (sdiff_subset.trans (inter_subset_left.trans hA) :
            (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) ≤
      ρ.regionEntropy (inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) / 2 + Cbuf * r) :
    ρ.regionEntropy (inter_subset_left.trans hA : A ∩ Icc a b ⊆ Λ) ≤
      ((1 - p₀ Cpad / 2) * M ^ 2 + p₀ Cpad / 2 * noninteriorBound Cpad M) * F +
        Cbuf * M ^ 2 * r := by
  classical
  set nx := nChunks₁ a b r
  set ny := nChunks₂ a b r
  obtain ⟨hnx, hny⟩ := nChunks_le hab hr hQr
  set e : Fin nx × Fin ny ≃ Fin (nx * ny) := finProdFinEquiv
  set ch : Fin (nx * ny) → Finset (ℤ × ℤ) := fun k => child a b r (e.symm k).1 (e.symm k).2
  set X : Fin (nx * ny) → Finset (ℤ × ℤ) := fun k => A ∩ ch k
  set T : Fin (nx * ny) → Finset (ℤ × ℤ) := fun k => (A ∩ ambientDilation (ch k) (Cpad * r)) \ X k
  have hX : ∀ k, X k ⊆ Λ := fun _ => inter_subset_left.trans hA
  have hT : ∀ k, T k ⊆ Λ := fun _ => sdiff_subset.trans (inter_subset_left.trans hA)
  set G := (univ : Finset (Fin (nx * ny))).filter fun k =>
    (Cpad ≤ ((e.symm k).1 : ℕ) ∧ ((e.symm k).1 : ℕ) + Cpad + 2 ≤ nx) ∧
      (Cpad ≤ ((e.symm k).2 : ℕ) ∧ ((e.symm k).2 : ℕ) + Cpad + 2 ≤ ny)
  set near : Fin (nx * ny) → Fin (nx * ny) → Prop := fun k k' =>
    ((e.symm k').1 : ℕ) ≤ (e.symm k).1 + Cpad ∧ ((e.symm k).1 : ℕ) ≤ (e.symm k').1 + Cpad ∧
      ((e.symm k').2 : ℕ) ≤ (e.symm k).2 + Cpad ∧ ((e.symm k).2 : ℕ) ≤ (e.symm k').2 + Cpad
  set Nb : Fin (nx * ny) → Finset (Fin (nx * ny)) := fun k =>
    univ.filter fun k' => k' ≠ k ∧ near k k'
  -- D3.16.1: the children partition `A ∩ Q`
  have hunion : univ.biUnion X = A ∩ Icc a b := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and, X, ch, mem_inter]
    refine ⟨fun ⟨k, hxA, hx⟩ => ⟨hxA, child_subset hx⟩, fun ⟨hxA, hx⟩ => ?_⟩
    obtain ⟨i, hi, j, hj, hij⟩ := exists_mem_child hr hx
    exact ⟨e (⟨i, hi⟩, ⟨j, hj⟩), hxA, by simpa using hij⟩
  have hpos : ∀ {k k' : Fin (nx * ny)} {x}, x ∈ ch k → x ∈ ch k' → k = k' := fun hx hx' => by
    obtain ⟨h1, h2⟩ := eq_of_mem_child hx hx'
    exact e.symm.injective (Prod.ext (Fin.ext h1) (Fin.ext h2))
  have hdisj : Pairwise fun k k' => Disjoint (X k) (X k') := fun k k' hkk =>
    disjoint_left.2 fun x hx hx' => hkk (hpos (mem_inter.1 hx).2 (mem_inter.1 hx').2)
  -- D3.16.3: an interior child has at most `(2 C_pad + 1)² - 1` neighbours
  have hNb : ∀ k ∈ G, k ∉ Nb k ∧ #(Nb k) + 1 ≤ (2 * Cpad + 5) ^ 2 := by
    refine fun k _ => ⟨by simp [Nb], ?_⟩
    have h1 : insert k (Nb k) ⊆ univ.filter (near k) := by
      intro k' hk'
      rcases mem_insert.1 hk' with rfl | hk'
      · simp [near]
      · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hk').2.2⟩
    have h2 : #(univ.filter (near k)) ≤ (2 * Cpad + 1) * (2 * Cpad + 1) := by
      rw [← card_map e.symm.toEmbedding]
      refine (card_le_card fun ij hij => ?_).trans ((card_product _ _).le.trans
        (Nat.mul_le_mul (card_near_le nx (e.symm k).1 Cpad) (card_near_le ny (e.symm k).2 Cpad)))
      obtain ⟨k', hk', rfl⟩ := mem_map.1 hij
      simp only [near, mem_filter, mem_univ, true_and] at hk'
      simp only [Equiv.toEmbedding_apply, mem_product, mem_filter, mem_univ, true_and]
      omega
    have := (card_insert_of_notMem (show k ∉ Nb k by simp [Nb])).symm.trans_le
      ((card_le_card h1).trans h2)
    nlinarith
  -- D3.16.3: the buffer `T_i` of an interior child lies in its neighbours
  have hTN : ∀ k ∈ G, T k ⊆ (Nb k).biUnion X := by
    intro k hk x hx
    simp only [G, mem_filter, mem_univ, true_and] at hk
    simp only [T, X, mem_sdiff, mem_inter] at hx
    obtain ⟨⟨hxA, hxd⟩, hxk⟩ := hx
    obtain ⟨i', hi', j', hj', hij⟩ := exists_mem_child hr
      (ambientDilation_child_subset hr hk.1.2 hk.2.2 hk.1.1 hk.2.1 hxd)
    have hij' : x ∈ ch (e (⟨i', hi'⟩, ⟨j', hj'⟩)) := by simpa [ch] using hij
    refine mem_biUnion.2 ⟨e (⟨i', hi'⟩, ⟨j', hj'⟩), mem_filter.2 ⟨mem_univ _,
      fun h => hxk ⟨hxA, h ▸ hij'⟩, ?_⟩, mem_inter.2 ⟨hxA, hij'⟩⟩
    have := le_add_of_mem_child hij hxd
    simp only [near, Equiv.symm_apply_apply]
    omega
  -- D3.16.3: Lemma 3.2 for interior children
  have hbuf' : ∀ k ∈ G, ρ.regionEntropy (union_subset (hX k) (hT k)) - ρ.regionEntropy (hT k) ≤
      ρ.regionEntropy (hX k) / 2 + Cbuf * r := fun k hk => by
    simp only [G, mem_filter, mem_univ, true_and] at hk
    exact hbuf _ (isIntRect_child hr (e.symm k).1.isLt (e.symm k).2.isLt) boxSize_child_le
      (ambientDilation_child_subset hr hk.1.2 hk.2.2 hk.1.1 hk.2.1)
  have key := step_3_16_4 ρ X hX hdisj G Nb T hT _ hNb hTN (by positivity) hbuf'
  rw [ρ.toSubState.regionEntropy_congr hunion _ (inter_subset_left.trans hA)] at key
  -- D3.16.4: noninterior children number at most `B_M`
  have hXF : ∀ k, ρ.regionEntropy (hX k) ≤ F := fun k =>
    hF _ (isIntRect_child hr (e.symm k).1.isLt (e.symm k).2.isLt) child_subset boxSize_child_le
  have hF0 : 0 ≤ F := (SubState.regionEntropy_nonneg _ _).trans (hF (Icc a a) ⟨a, a, le_rfl, rfl⟩
    (Icc_subset_Icc_right hab)
    (by rw [boxSize_Icc le_rfl]; simpa only [add_sub_cancel_left, Int.toNat_one, max_self]))
  have hbad : #(univ \ G) ≤ noninteriorBound Cpad M := by
    have hsub : (univ \ G).map e.symm.toEmbedding ⊆
        (univ.filter fun i : Fin nx => ¬(Cpad ≤ i.val ∧ i.val + Cpad + 2 ≤ nx)) ×ˢ univ ∪
          univ ×ˢ univ.filter fun j : Fin ny => ¬(Cpad ≤ j.val ∧ j.val + Cpad + 2 ≤ ny) := by
      intro ij hij
      obtain ⟨k, hk, rfl⟩ := mem_map.1 hij
      simp only [G, mem_sdiff, mem_univ, mem_filter, true_and, not_and_or] at hk
      simp only [Equiv.toEmbedding_apply, mem_union, mem_product, mem_filter, mem_univ,
        true_and, and_true]
      tauto
    rw [← card_map e.symm.toEmbedding]
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    rw [card_product, card_product, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
      noninteriorBound]
    have := Nat.mul_le_mul (card_not_interior_le nx Cpad) hny
    have := Nat.mul_le_mul hnx (card_not_interior_le ny Cpad)
    nlinarith
  have hcard : (#G : ℝ) + #(univ \ G) ≤ M ^ 2 := by
    have h := card_sdiff_add_card_eq_card (subset_univ G)
    rw [card_univ, Fintype.card_fin] at h
    have h' : #(univ \ G) + #G ≤ M ^ 2 := h.trans_le (by rw [sq]; exact Nat.mul_le_mul hnx hny)
    have : ((#(univ \ G) + #G : ℕ) : ℝ) ≤ (M ^ 2 : ℕ) := by exact_mod_cast h'
    push_cast at this
    linarith
  have hp : 0 ≤ p₀ Cpad ∧ p₀ Cpad ≤ 1 := ⟨by unfold p₀; positivity, by
    unfold p₀; rw [div_le_one (by positivity)]; nlinarith [(Cpad.cast_nonneg : (0:ℝ) ≤ Cpad)]⟩
  have hP : (((2 * Cpad + 5) ^ 2 : ℕ) : ℝ) = (2 * Cpad + 5 : ℝ) ^ 2 := by push_cast; ring
  rw [← sum_sdiff (subset_univ G), hP] at key
  have hg := sum_le_card_nsmul G _ _ fun k _ => hXF k
  have hb := sum_le_card_nsmul (univ \ G) _ _ fun k _ => hXF k
  rw [nsmul_eq_mul] at hg hb
  have hbad' : (#(univ \ G) : ℝ) ≤ noninteriorBound Cpad M := by exact_mod_cast hbad
  have h1 : (1 - p₀ Cpad / 2) * ∑ k ∈ G, ρ.regionEntropy (hX k) ≤ (1 - p₀ Cpad / 2) * (#G * F) :=
    mul_le_mul_of_nonneg_left hg (by linarith)
  have h2 : (#G : ℝ) * (Cbuf * r) ≤ M ^ 2 * (Cbuf * r) :=
    mul_le_mul_of_nonneg_right (by linarith [(#(univ \ G)).cast_nonneg (α := ℝ)]) (by positivity)
  have hc1 : (1 - p₀ Cpad / 2) * (#G + #(univ \ G)) ≤ (1 - p₀ Cpad / 2) * M ^ 2 :=
    mul_le_mul_of_nonneg_left hcard (by linarith)
  have hc2 : p₀ Cpad / 2 * #(univ \ G) ≤ p₀ Cpad / 2 * noninteriorBound Cpad M :=
    mul_le_mul_of_nonneg_left hbad' (by linarith)
  have h3 : (1 - p₀ Cpad / 2) * (#G * F) + #(univ \ G) * F ≤
      ((1 - p₀ Cpad / 2) * M ^ 2 + p₀ Cpad / 2 * noninteriorBound Cpad M) * F := by
    rw [show (1 - p₀ Cpad / 2) * (#G * F) + #(univ \ G) * F = ((1 - p₀ Cpad / 2) *
      (#G + #(univ \ G)) + p₀ Cpad / 2 * #(univ \ G)) * F by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) hF0
  have hpe : 1 / (2 * (2 * (Cpad : ℝ) + 5) ^ 2) = p₀ Cpad / 2 := by
    unfold p₀; rw [div_div, mul_comm]
  rw [hpe] at key
  linarith

/-- D3.16 (Proposition 3.3, prop:initial-box). There are `C < ∞` and `e₀ ∈ (0, 1)`, depending
only on `q, R, J, Δ`, with `F_box(r) ≤ C r^{1+e₀}` (`r ≥ 1`). -/
theorem prop_3_3 {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    InitialBoxEstimate ℂ q R J Δ := by
  obtain ⟨Cpad, -, Cbuf, hbuf⟩ := lemma_3_2 (R := R) hq hJ hΔ
  set c := max Cbuf 0
  set p := p₀ Cpad
  have hp : 0 < p ∧ p ≤ 1 / 25 := ⟨by simp only [p, p₀]; positivity, by
    simp only [p, p₀]; gcongr; nlinarith [(Cpad.cast_nonneg : (0 : ℝ) ≤ Cpad)]⟩
  -- D3.16.4 (eq:initial-box-recursion)
  have hrec : ∀ M r, 1 ≤ r → boxEntropySup q R J Δ (M * r) ≤
      ((1 - p / 2) * M ^ 2 + p / 2 * noninteriorBound Cpad M) * boxEntropySup q R J Δ r +
        c * M ^ 2 * r := by
    refine fun M r hr => Real.sSup_le (fun s hs => ?_) (add_nonneg (mul_nonneg (add_nonneg
      (mul_nonneg (by linarith) (by positivity)) (mul_nonneg (by linarith) (by positivity)))
      (boxEntropySup_nonneg r)) (by positivity))
    obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, ⟨a, b, hab, rfl⟩, hs, hQr, rfl⟩ := hs
    have hD₀' : 0 ≤ D₀ := by linarith [(by positivity : (0 : ℝ) ≤ 2 * R + 10)]
    exact step_3_16_3 (pureState Ω hΩ) hA hab hr (hQr.trans (by rw [mul_comm]))
      (fun Q₀ hQ₀ hsub hsz =>
        le_boxEntropySup hD₀ hΦ hΩ hE hgap hA hQ₀ (IsSafe.subset' hs hD₀' hsub) hsz)
      (le_max_right _ _) fun Q₀ hQ₀ hsz hdil =>
        (hbuf D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA _ ⟨a, b, hab, rfl⟩ hs r hr Q₀
        hQ₀ hsz hdil).trans (by gcongr; exact le_max_left _ _)
  -- D3.16.5: `M = 16(C_pad + 2)`, `λ = (1 - p₀/4) M²`, `M < λ < M²`
  set M : ℕ := 16 * (Cpad + 2)
  set lam : ℝ := (1 - p / 4) * M ^ 2
  have hM : (32 : ℝ) ≤ M := by
    simp only [M]; push_cast; linarith [(Cpad.cast_nonneg : (0 : ℝ) ≤ Cpad)]
  have hBM : (noninteriorBound Cpad M : ℝ) ≤ M ^ 2 / 4 := by
    simp only [noninteriorBound, M]; push_cast; nlinarith [(Cpad.cast_nonneg : (0 : ℝ) ≤ Cpad)]
  have hMlam : (M : ℝ) < lam := by simp only [lam]; nlinarith
  have hlamM : lam < (M : ℝ) ^ 2 := by
    have : 0 < (M : ℝ) ^ 2 := by positivity
    simp only [lam]; nlinarith [hp.1]
  have hrec' : ∀ r, 1 ≤ r →
      boxEntropySup q R J Δ (M * r) ≤ lam * boxEntropySup q R J Δ r + c * M ^ 2 * r := by
    refine fun r hr => (hrec M r hr).trans ?_
    have := boxEntropySup_nonneg (q := q) (R := R) (J := J) (Δ := Δ) r
    gcongr
    simp only [lam]; nlinarith
  -- D3.16.6–D3.16.8
  obtain ⟨C, hC⟩ := step_3_16_8 boxEntropySup_mono (by omega) hMlam (by positivity) hrec'
  -- D3.16.7: `1 + e₀ = log_M λ ∈ (1, 2)`
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have h1 : Real.log M < Real.log lam := Real.log_lt_log (by linarith) hMlam
  have h2 : Real.log lam < 2 * Real.log M := by
    have := Real.log_lt_log (by linarith) hlamM
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  refine ⟨C, Real.log lam / Real.log M - 1, by rw [sub_pos, one_lt_div hlogM]; exact h1,
    by rw [sub_lt_iff_lt_add, div_lt_iff₀ hlogM]; linarith,
    fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q r hr hQ hs hQr => ?_⟩
  rw [add_sub_cancel]
  exact (le_boxEntropySup hD₀ hΦ hΩ hE hgap hA hQ hs hQr).trans (hC r hr)

end D316

end AreaLaw
