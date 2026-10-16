import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith

import Arealaw.Geometry
import Arealaw.Subadditivity

/-!
# The saturation ladder

Machinery for `Arealaw.lemma16` (Brandão–Horodecki, Saturation of Mutual Information): a
multiplicative descent engine, a window of admissible region positions, a positional maximum
of region entropies, and the one-step quartering recurrence that drives them.

The proof of `lemma16` negates the conclusion and derives a contradiction.  Over a geometric
ladder of `~2/ε` nested scales the failure of saturation forces the maximum region entropy
below zero, against `entropy ≥ 0`.

## Main definitions

* `positions`, `placement`: the window of admissible start positions near the marked site.
* `regionEntropy₂`, `M`: region entropy in bits, and its maximum over the positions of a
  given scale.

## Main statements

* `descend_add`, `descend_add_nonneg_bound`, `rescale_step`: additive telescoping, its
  contradiction, and the rescaling that turns the `×4` recurrence into a constant-loss one.
* `region_step`, `per_position`, `M_recursion`: the one quartering step, on a region, on a
  position, and lifted to the maximum.
* `lt_mutualInfo₂_interval_of_neg`: the negated conclusion, specialized to one region and
  translated into the nats/`interval` language `M_recursion` consumes.

## Implementation notes

`M` is a *maximum* over positions, following the paper; the descent is then a choice-free
inequality on that maximum.  Region sizes are powers of four because a quarter of a size-`4q`
region is a size-`q` region.  The size-`m` region at position `p` is the ℕ-window
`interval p (p + m)`, so position arithmetic stays in `ℕ`; `interval_eq_Ico` bridges to
`Finset.Ico`, where the quartering lemmas live.  Everything is pinned to `ℂ`/`Qubits`,
inherited from the region entropy API.
-/

namespace Arealaw.Ladder

/-! ## The descent engine -/

/-- Telescoping a per-step loss: a sequence obeying `f (k + 1) ≤ f k - c` for its first `K`
steps satisfies `f K ≤ f 0 - K * c`. -/
theorem descend_add (f : ℕ → ℝ) (c : ℝ) :
    ∀ K, (∀ k, k < K → f (k + 1) ≤ f k - c) → f K ≤ f 0 - K * c := by
  intro K
  induction K <;> grind

/-- A sequence pinned by `f 0 ≤ D` above and `0 ≤ f K` below cannot lose `c` at each of `K`
steps once `D < K * c`. -/
theorem descend_add_nonneg_bound (f : ℕ → ℝ) (c D : ℝ) (K : ℕ)
    (hstep : ∀ k, k < K → f (k + 1) ≤ f k - c) (h0 : f 0 ≤ D) (hK : 0 ≤ f K)
    (hD : D < (K : ℝ) * c) : False := by
  linarith [descend_add f c K hstep]

/-- A `×4` recurrence rescales to a constant-loss one: dividing `M (k+1) ≤ 4·M k − d·4^k`
through by `4^(k+1)` turns the geometric deficit `d·4^k` into the constant loss `d / 4`, so
`M k / 4^k` is the sequence the additive descent runs on. -/
theorem rescale_step {M : ℕ → ℝ} {d : ℝ} {k : ℕ}
    (h : M (k + 1) ≤ 4 * M k - d * 4 ^ k) :
    M (k + 1) / 4 ^ (k + 1) ≤ M k / 4 ^ k - d / 4 := by
  rw [pow_succ]
  field_simp
  linarith

/-! ## The position window -/

/-- Start positions `p` in the window `[o, o+W)` where a size-`m` region `[p, p+m)` fits. -/
def positions (o W m : ℕ) : Finset ℕ :=
  (Finset.range (o + W + 1)).filter (fun p => o ≤ p ∧ p + m ≤ o + W)

/-- Membership in the position window, unfolded to its two bounds. -/
theorem mem_positions {o W m p : ℕ} : p ∈ positions o W m ↔ o ≤ p ∧ p + m ≤ o + W := by
  simp only [positions, Finset.mem_filter, Finset.mem_range]
  omega

/-- The window holds at least one size-`m` region once `m` fits inside it. -/
theorem positions_nonempty (o W m : ℕ) (hW : m ≤ W) : (positions o W m).Nonempty :=
  ⟨o, mem_positions.mpr ⟨le_refl o, by omega⟩⟩

/-- The four quarters of a size-`4q` region are size-`q` regions in the same window. -/
theorem positions_nest (o W q p : ℕ) (hp : p ∈ positions o W (4 * q)) :
    p ∈ positions o W q ∧ p + q ∈ positions o W q ∧
      p + 2 * q ∈ positions o W q ∧ p + 3 * q ∈ positions o W q := by
  grind [mem_positions]

/-- A window that fits inside `[0, N)` keeps every region's far endpoint below `N`. -/
theorem add_mul_lt_of_mem_positions {o W q N : ℕ} (hW : o + W < N) (p : ℕ)
    (hp : p ∈ positions o W (4 * q)) : p + 4 * q < N := by
  rw [mem_positions] at hp
  omega

/-- A window of width `W` fits inside `[0, N)` near `s` so that for every region `[p, p+F)`
in it the midpoint quantity `a + d = 2p + F` stays within `4W` of `2s`. -/
theorem placement (s N W : ℕ) (hN : 2 * W + 1 ≤ N) (hs : s < N) :
    ∃ o, o + W < N ∧ ∀ p F : ℕ, o ≤ p → p + F ≤ o + W →
      |((2 * p + F : ℕ) : ℤ) - 2 * (s : ℤ)| ≤ 4 * W :=
  ⟨min s (N - 1 - W), by omega, fun p F _ _ => abs_le.2 (by omega)⟩

/-! ## Entropy budgets -/

variable {n : ℕ}

/-- Region bit-entropy of `X` as a region of the whole `n`-qubit chain: the shared
`SubState.regionEntropy₂` specialized to `Finset.univ` and indexed by a bare `Finset (Fin n)`. -/
noncomputable def regionEntropy₂ (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (X : Finset (Fin n)) : ℝ :=
  ρ.toSubState.regionEntropy₂ (Finset.subset_univ X)

/-- Region bit-entropy is nonnegative. -/
theorem regionEntropy₂_nonneg (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (X : Finset (Fin n)) : 0 ≤ regionEntropy₂ ρ X :=
  ρ.toSubState.regionEntropy₂_nonneg _

/-- **Entropy budget**: a region of `|X|` qubits carries at most `|X|` bits. -/
theorem regionEntropy₂_le_card (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (X : Finset (Fin n)) : regionEntropy₂ ρ X ≤ (X.card : ℝ) :=
  (div_le_iff₀ (Real.log_pos one_lt_two)).2 <|
    (ρ.restrict (Finset.subset_univ X)).entropy_le_log_card.trans_eq <| by simp

/-- **Subadditivity** in bits: `S₂(X ∪ Y) ≤ S₂(X) + S₂(Y)` for disjoint regions. -/
theorem regionEntropy₂_union_le (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    {X Y : Finset (Fin n)} (hd : Disjoint X Y) :
    regionEntropy₂ ρ (X ∪ Y) ≤ regionEntropy₂ ρ X + regionEntropy₂ ρ Y :=
  Arealaw.regionEntropy₂_union_le ρ hd (Finset.subset_univ X) (Finset.subset_univ Y)

/-- `mutualInfo₂` as the three-term combination of region bit-entropies. -/
theorem mutualInfo₂_eq (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (X Y : Finset (Fin n)) :
    ρ.toSubState.mutualInfo₂ (Finset.subset_univ X) (Finset.subset_univ Y)
      = regionEntropy₂ ρ X + regionEntropy₂ ρ Y - regionEntropy₂ ρ (X ∪ Y) :=
  ρ.toSubState.mutualInfo₂_eq (Finset.subset_univ X) (Finset.subset_univ Y)

/-! ## The positional maximum -/

/-- Maximum region bit-entropy over start positions `P` for size-`m` regions (`0` if `P`
empty). -/
noncomputable def M (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (P : Finset ℕ) (m : ℕ) : ℝ :=
  if h : P.Nonempty then P.sup' h (fun p => regionEntropy₂ ρ (interval p (p + m))) else 0

/-- The positional maximum is nonnegative. -/
theorem M_nonneg (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (P : Finset ℕ) (m : ℕ) : 0 ≤ M ρ P m := by
  unfold M
  exact dite_nonneg (fun ⟨_, hp⟩ ↦ Finset.le_sup'_of_le _ hp (regionEntropy₂_nonneg ρ _))
    fun _ ↦ le_rfl

/-- Bit-entropy budget for a size-`m` region: `S₂([p, p+m)) ≤ m`. -/
theorem regionEntropy₂_interval_le (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (p m : ℕ) : regionEntropy₂ ρ (interval p (p + m)) ≤ (m : ℝ) :=
  (regionEntropy₂_le_card ρ _).trans <| by
    exact_mod_cast (card_interval_le p (p + m)).trans_eq (Nat.add_sub_cancel_left p m)

/-- Budget for the positional max: `M ρ P m ≤ m`. -/
theorem M_le (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (P : Finset ℕ) (m : ℕ) : M ρ P m ≤ (m : ℝ) := by
  unfold M
  split_ifs
  exacts [Finset.sup'_le _ _ fun p _ ↦ regionEntropy₂_interval_le ρ p m, m.cast_nonneg]

/-- Every candidate region's bit-entropy is ≤ the max `M`. -/
theorem le_M (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (Q : Finset ℕ) (m p : ℕ) (hp : p ∈ Q) :
    regionEntropy₂ ρ (interval p (p + m)) ≤ M ρ Q m := by
  rw [M, dif_pos ⟨p, hp⟩]
  apply Finset.le_sup' _ hp

/-- A `Fin`-interval of length `q` starting in `Q` has bit-entropy at most `M ρ Q q`. -/
theorem regionEntropy₂_Ico_le_M (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (Q : Finset ℕ) (q : ℕ) {a b : Fin n} (hab : b.val = a.val + q) (ha : a.val ∈ Q) :
    regionEntropy₂ ρ (Finset.Ico a b) ≤ M ρ Q q := by
  simpa [← hab, interval_eq_Ico] using le_M ρ Q q _ ha

/-! ## The quartering step -/

/-- **One quartering step, on a region.**  If saturation fails at the region `[a,d)` with
centre `[b,c)` and borders `[a,b) ∪ [c,d)`, then subadditivity splits its entropy below the
sum of its four quarters' entropies, less the cutoff `cc`. -/
theorem region_step (ρ : MState (Reg (Qubits n) Finset.univ) ℂ) (a b e c d : Fin n) (hab : a ≤ b)
    (hbe : b ≤ e) (hec : e ≤ c) (hcd : c ≤ d) (cc : ℝ)
    (hsat : cc < ρ.toSubState.mutualInfo₂ (Finset.subset_univ (Finset.Ico b c))
              (Finset.subset_univ (Finset.Ico a b ∪ Finset.Ico c d))) :
    regionEntropy₂ ρ (Finset.Ico a d) ≤ regionEntropy₂ ρ (Finset.Ico a b)
      + regionEntropy₂ ρ (Finset.Ico b e) + regionEntropy₂ ρ (Finset.Ico e c)
      + regionEntropy₂ ρ (Finset.Ico c d) - cc := by
  have hbc : b ≤ c := hbe.trans hec
  rw [mutualInfo₂_eq, Finset.union_left_comm, Finset.Ico_union_Ico_eq_Ico hbc hcd,
    Finset.Ico_union_Ico_eq_Ico hab (hbc.trans hcd), ← Finset.Ico_union_Ico_eq_Ico hbe hec] at hsat
  linarith [regionEntropy₂_union_le ρ (Finset.Ico_disjoint_Ico_consecutive b e c),
    regionEntropy₂_union_le ρ <|
      (Finset.Ico_disjoint_Ico_consecutive a b d).mono_right (Finset.Ico_subset_Ico_left hbc)]

/-- Per-position bound: one region's entropy ≤ 4·M − cc, given saturation fails there. -/
theorem per_position (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (Q : Finset ℕ) (q : ℕ) (cc : ℝ) (a b e c d : Fin n)
    (hab : a ≤ b) (hbe : b ≤ e) (hec : e ≤ c) (hcd : c ≤ d)
    (hq1 : b.val = a.val + q) (hq2 : e.val = b.val + q)
    (hq3 : c.val = e.val + q) (hq4 : d.val = c.val + q)
    (hQa : a.val ∈ Q) (hQb : b.val ∈ Q) (hQe : e.val ∈ Q) (hQc : c.val ∈ Q)
    (hsat : cc < ρ.toSubState.mutualInfo₂ (Finset.subset_univ (Finset.Ico b c))
              (Finset.subset_univ (Finset.Ico a b ∪ Finset.Ico c d))) :
    regionEntropy₂ ρ (Finset.Ico a d) ≤ 4 * M ρ Q q - cc := by
  linarith [region_step ρ a b e c d hab hbe hec hcd cc hsat,
    regionEntropy₂_Ico_le_M ρ Q q hq1 hQa, regionEntropy₂_Ico_le_M ρ Q q hq2 hQb,
    regionEntropy₂_Ico_le_M ρ Q q hq3 hQe, regionEntropy₂_Ico_le_M ρ Q q hq4 hQc]

/-- **One quartering step, lifted to the maximum.**  The maximum region bit-entropy at one
scale is at most four times the maximum at the next scale down, less the cutoff `cc`. -/
theorem M_recursion (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (P Q : Finset ℕ) (q : ℕ) (cc : ℝ) (hPne : P.Nonempty)
    (hnest : ∀ p ∈ P, p ∈ Q ∧ p + q ∈ Q ∧ p + 2 * q ∈ Q ∧ p + 3 * q ∈ Q)
    (hbnd : ∀ p ∈ P, p + 4 * q < n)
    (hsat : ∀ p ∈ P, cc < ρ.toSubState.mutualInfo₂
              (Finset.subset_univ (interval (p + q) (p + 3 * q)))
              (Finset.subset_univ (interval p (p + q) ∪ interval (p + 3 * q) (p + 4 * q)))) :
    M ρ P (4 * q) ≤ 4 * M ρ Q q - cc := by
  rw [M, dif_pos hPne]
  refine Finset.sup'_le _ _ fun p hp => ?_
  have := hbnd p hp
  have h := per_position ρ Q q cc ⟨p, by omega⟩ ⟨p + q, by omega⟩ ⟨p + 2 * q, by omega⟩
    ⟨p + 3 * q, by omega⟩ ⟨p + 4 * q, by omega⟩
  simp only [← interval_eq_Ico] at h
  grind [hnest p hp, hsat p hp]

/-! ## Wiring the negation -/

/-- The per-scale cutoff `ε·(2·l₀·4^k)` is `d·4^k` for the constant `d = 2ε·l₀`, the form
`rescale_step` divides down into the constant per-step loss the additive descent runs on. -/
theorem cost_eq (ε : ℝ) (l₀ k : ℕ) :
    ε * (2 * ((l₀ * 4 ^ k : ℕ) : ℝ)) = (2 * ε * (l₀ : ℝ)) * (4 : ℝ) ^ k := by
  push_cast
  ring

/-- Per-position wiring: the negation, applied to the region at `p`, yields the interval-form
saturation bound that `M_recursion` consumes. -/
theorem lt_mutualInfo₂_interval_of_neg (ρ : MState (Reg (Qubits n) Finset.univ) ℂ) (s : Fin n)
    (l₀ : ℕ) (ε : ℝ) (B : ℕ)
    (hneg : ∀ (l : ℕ) (a b c d : Fin n), l₀ ≤ l → l ≤ l₀ * B →
        (Finset.Ico a d).card = 2 * l → (Finset.Ico b c).card = l →
        (Finset.Ico a b).card = (Finset.Ico c d).card →
        |((a : ℕ) + (d : ℕ) : ℤ) - 2 * (s : ℕ)| ≤ 4 * l₀ * B →
        ε * l < ρ.toSubState.mutualInfo₂ (Finset.subset_univ (Finset.Ico b c))
          (Finset.subset_univ (Finset.Ico a b ∪ Finset.Ico c d)))
    (p q : ℕ) (hbnd : p + 4 * q < n)
    (hr1 : l₀ ≤ 2 * q) (hr2 : 2 * q ≤ l₀ * B)
    (hcenter : |((2 * p + 4 * q : ℕ) : ℤ) - 2 * (s : ℕ)| ≤ 4 * (l₀ * B)) :
    ε * (2 * q) < ρ.toSubState.mutualInfo₂
      (Finset.subset_univ (interval (p + q) (p + 3 * q)))
      (Finset.subset_univ (interval p (p + q) ∪ interval (p + 3 * q) (p + 4 * q))) := by
  have h := hneg (2 * q) ⟨p, by omega⟩ ⟨p + q, by omega⟩ ⟨p + 3 * q, by omega⟩
    ⟨p + 4 * q, by omega⟩ hr1 hr2 (by simp; omega) (by simp; omega) (by simp; omega)
    (by push_cast at hcenter ⊢; rwa [mul_assoc, ← add_assoc, ← two_mul])
  simp only [← interval_eq_Ico] at h
  exact_mod_cast h

end Arealaw.Ladder
