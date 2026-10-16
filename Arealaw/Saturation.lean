import Arealaw.Ladder
import Arealaw.Subadditivity
import Mathlib.Order.Interval.Finset.Fin

/-!
# Saturation of mutual information

Brandão–Horodecki's Lemma 16: near any site of a qubit chain there is a region whose centre
and borders share little mutual information, at a scale bounded by `scaleBound ε`.

`lemma16` negates the conclusion and, through the ladder machinery of `Arealaw.Ladder`,
derives a contradiction: over `~2/ε` scales of quartering the failure of saturation drives
the maximum region entropy below its `entropy ≥ 0` floor.

## Main definitions

* `scaleBound`: the scale within which `lemma16` finds its region.
* `Unsaturated`: the negated conclusion, the hypothesis the descent runs on.

## Main statements

* `lemma16`: the saturation lemma.

## Implementation notes

Pinned to `ℂ`, inherited from `Arealaw.Subadditivity`.  The `+ 1` in `scaleBound` supplies the
strict margin that turns `entropy ≥ 0` into a genuine contradiction.
-/

namespace Arealaw

open Ladder

/-- `exp(O(1/ε))`: the scale `4 ^ (⌈2/ε⌉₊ + 1)` within which `lemma16` finds its region. -/
noncomputable def scaleBound (ε : ℝ) : ℕ := 4 ^ (⌈2 / ε⌉₊ + 1)

/-- The negation of `lemma16`'s conclusion at the site `s`: *every* admissible region near
`s` has its centre and borders sharing more than `ε` bits per site of a half. -/
def Unsaturated {n : ℕ} (ρ : MState (Reg (Qubits n) Finset.univ) ℂ) (s : Fin n) (l₀ : ℕ) (ε : ℝ) :
    Prop :=
  ∀ (l : ℕ) (a b c d : Fin n), l₀ ≤ l → l ≤ l₀ * scaleBound ε → (Finset.Ico a d).card = 2 * l →
    (Finset.Ico b c).card = l → (Finset.Ico a b).card = (Finset.Ico c d).card →
    |((a : ℕ) + (d : ℕ) : ℤ) - 2 * (s : ℕ)| ≤ 4 * l₀ * scaleBound ε →
    ε * l < ρ.toSubState.mutualInfo₂ (Finset.subset_univ (Finset.Ico b c))
      (Finset.subset_univ (Finset.Ico a b ∪ Finset.Ico c d))

private lemma lt_ceil_succ_mul_deficit {l₀ : ℕ} (hl₀ : 0 < l₀) {ε : ℝ} (hε : 0 < ε) :
    (l₀ : ℝ) < ((⌈2 / ε⌉₊ + 1 : ℕ) : ℝ) * (ε * l₀ / 2) := by
  have := (div_lt_iff₀ hε).mp ((Nat.le_ceil (2 / ε)).trans_lt (lt_add_one _))
  push_cast
  nlinarith [Nat.cast_pos (α := ℝ).mpr hl₀]

private lemma four_mul_pow_le_scaleBound (l₀ : ℕ) {ε : ℝ} {k : ℕ} (hk : k < ⌈2 / ε⌉₊ + 1) :
    4 * (l₀ * 4 ^ k) ≤ l₀ * scaleBound ε := by
  rw [scaleBound, ← mul_left_comm, ← pow_succ']
  gcongr <;> omega

private lemma rescaled_maxEntropy_step {n : ℕ} (ρ : MState (Reg (Qubits n) Finset.univ) ℂ)
    (s : Fin n) (l₀ : ℕ) (ε : ℝ) (hcon : Unsaturated ρ s l₀ ε) {o : ℕ}
    (hob : o + l₀ * scaleBound ε < n)
    (hoc : ∀ p F : ℕ, o ≤ p → p + F ≤ o + l₀ * scaleBound ε →
      |((2 * p + F : ℕ) : ℤ) - 2 * (s : ℤ)| ≤ 4 * ((l₀ * scaleBound ε : ℕ) : ℤ)) {k : ℕ}
    (hk : k < ⌈2 / ε⌉₊ + 1) :
    M ρ (positions o (l₀ * scaleBound ε) (l₀ * 4 ^ (k + 1))) (l₀ * 4 ^ (k + 1)) / 4 ^ (k + 1) ≤
      M ρ (positions o (l₀ * scaleBound ε) (l₀ * 4 ^ k)) (l₀ * 4 ^ k) / 4 ^ k - ε * l₀ / 2 := by
  -- the `×4` recurrence, divided down by `rescale_step`
  refine (rescale_step (d := 2 * ε * l₀)
    (M := fun k => M ρ (positions o (l₀ * scaleBound ε) (l₀ * 4 ^ k)) (l₀ * 4 ^ k)) ?_).trans_eq
    (by ring)
  have hW := four_mul_pow_le_scaleBound l₀ (ε := ε) hk
  rw [pow_succ', mul_left_comm, ← cost_eq]
  refine M_recursion ρ _ _ _ _ (positions_nonempty o _ _ hW) (positions_nest o _ _)
    (add_mul_lt_of_mem_positions hob) fun p hp => lt_mutualInfo₂_interval_of_neg ρ s l₀ ε _ hcon
      p _ (add_mul_lt_of_mem_positions hob p hp) ?_ (by omega)
      ((mem_positions.mp hp).elim (hoc p _))
  exact (Nat.le_mul_of_pos_right l₀ (by positivity)).trans (Nat.le_mul_of_pos_left _ two_pos)

/-- **Saturation of Mutual Information** (Brandão–Horodecki, Lemma 16).  Near any site `s` of
a qubit chain there is a region `[a,d)` of `2l` sites, at a scale `l₀ ≤ l ≤ l₀·scaleBound ε`
and centred on `s` to within `4·l₀·scaleBound ε`, whose centre `[b,c)` and borders
`[a,b) ∪ [c,d)` share at most `ε·l` bits of mutual information.

`hn` guards against small `n`: the lemma fails at `n = 1`, `l₀ = 1`, where no such region fits. -/
theorem lemma16 (l₀ : ℕ) (hl₀ : 0 < l₀) (ε : ℝ) (hε : 0 < ε) {n : ℕ}
    (ρ : MState (Reg (Qubits n) Finset.univ) ℂ) (s : Fin n)
    (hn : 2 * l₀ * scaleBound ε + 1 ≤ n) :
    ∃ (l : ℕ) (a b c d : Fin n), l₀ ≤ l ∧ l ≤ l₀ * scaleBound ε ∧
      (Finset.Ico a d).card = 2 * l ∧ (Finset.Ico b c).card = l ∧
      (Finset.Ico a b).card = (Finset.Ico c d).card ∧
      |((a : ℕ) + (d : ℕ) : ℤ) - 2 * (s : ℕ)| ≤ 4 * l₀ * scaleBound ε ∧
      ρ.toSubState.mutualInfo₂ (Finset.subset_univ (Finset.Ico b c))
        (Finset.subset_univ (Finset.Ico a b ∪ Finset.Ico c d)) ≤ ε * l := by
  by_contra! hcon : Unsaturated ρ s l₀ ε
  obtain ⟨o, hob, hoc⟩ := placement s.val n (l₀ * scaleBound ε) (by rwa [← mul_assoc]) s.isLt
  -- The rescaled max entropy `M k / 4^k` loses `ε·l₀/2` per scale; fed to the additive engine.
  exact descend_add_nonneg_bound
    (fun k => M ρ (positions o (l₀ * scaleBound ε) (l₀ * 4 ^ k)) (l₀ * 4 ^ k) / 4 ^ k)
    (ε * l₀ / 2) l₀ (⌈2 / ε⌉₊ + 1)
    (fun k hk => rescaled_maxEntropy_step ρ s l₀ ε hcon hob hoc hk) (by simpa using M_le ρ _ _)
    (div_nonneg (M_nonneg ρ _ _) (by positivity)) (lt_ceil_succ_mul_deficit hl₀ hε)

end Arealaw
