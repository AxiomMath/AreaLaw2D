import OpenAI.RegionEntropy
import OpenAI.RegionSSA

/-!
# The entropy chain rule averaged over rotated color orders

Let `X_i`, `i ∈ ι`, be pairwise disjoint regions of a state `ρ`, colored by `col : ι → Fin N`,
and let `O_i` be the union of the regions whose color differs from that of `i`.  Ordering the
indices by color, rotated by `k`, and then by a fixed enumeration, the chain rule writes
`S(⋃ X_i)` as the sum of the conditional entropies `S(X_i | X_{<i})`.  Each term is at most
`S(X_i)`, and in the rotation that puts the color of `i` last, the predecessors of `i` contain
`O_i`, so the term of `i` is at most `S(X_i | O_i)`.  Summing over the `N` rotations gives
`N S(⋃ X_i) ≤ (N - 1) ∑ S(X_i) + ∑ S(X_i | O_i)`.

With buffers `T_i ⊆ O_i` satisfying `S(X_i | T_i) ≤ S(X_i)/2 + β` for the indices of a set
`good`, this reads `S(⋃ X_i) ≤ ∑ S(X_i) - (2N)⁻¹ ∑_{i ∈ good} S(X_i) + |good| β / N`, the
expected chain rule in the proof of Proposition 3.3 of [OAI265].

## Main statements

* `OpenAI.mul_regionEntropy_biUnion_le_rotations`: the chain rule summed over the rotations.
* `OpenAI.regionEntropy_biUnion_le_rotations`: the buffered form used for Proposition 3.3.

## Implementation notes

The source orders the children uniformly at random; each child satisfying the buffer bound is
last among its neighbors with probability at least `1/N`.  The `N` cyclic rotations of the
colors are a deterministic replacement: each index is last among the other colors in exactly
one of them.  The chain rule for each rotation is `Arealaw.SubState.regionEntropy_union_biUnion`
for the order on `ι` lifted from the lexicographic key `(col i + k, e i)`, with `e` an
enumeration of `ι`.  Conditioning is lowered by
`Arealaw.SubState.regionEntropy_union_sub_le_of_subset`, so the file is native over any
`RCLike` field.

Ported from TNLean, `TNLean/PEPS/AreaLaw/RotatedChainRule.lean` (theorems
`sum_sub_filter_key_eq`, `regionalEntropy_cond_anti`, `regionalEntropy_biUnion_le_rotations`)
at commit `f4c2d204` (Apache 2.0).  The changes: the regions are `Finset`s of a general site
type `σ` with local spaces `loc`, the state is an `Arealaw.MState` over `𝕜` rather than a unit
vector over `ℂ`, and the entropies are `Arealaw.SubState.regionEntropy`; the colors take values
in `Fin N` rather than in `ℕ` below `N`; the region-containment facts that TNLean's region type
carries (`X_i, T_i ⊆ Λ`) are hypotheses; the telescoping lemma and the monotonicity of the
conditional entropy are replaced by the project's chain identity and its consequence of strong
subadditivity; and the summed form over the rotations, without buffers, is stated separately.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.3 (proof of Proposition 3.3).
-/

namespace OpenAI

open Arealaw

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U : Finset σ}

/-- **The chain rule summed over rotated color orders.** For pairwise disjoint regions `X_i`
colored by `col : ι → Fin N`, with `O_i` the union of the regions of the colors other than
that of `i`, `N S(⋃ X_i) ≤ (N - 1) ∑ S(X_i) + ∑ S(X_i | O_i)`. -/
theorem mul_regionEntropy_biUnion_le_rotations (ρ : MState (Reg loc U) 𝕜) {ι : Type*}
    [Fintype ι] (Xs : ι → Finset σ) (hX : ∀ i, Xs i ⊆ U)
    (hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j)) {N : ℕ} (col : ι → Fin N) :
    (N : ℝ) * ρ.regionEntropy (Finset.biUnion_subset.2 fun i _ ↦ hX i :
        Finset.univ.biUnion Xs ⊆ U) ≤
      ((N : ℝ) - 1) * ∑ i, ρ.regionEntropy (hX i) +
        ∑ i, (ρ.regionEntropy (Finset.union_subset (hX i)
            (Finset.biUnion_subset.2 fun j _ ↦ hX j) :
              Xs i ∪ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs ⊆ U) -
          ρ.regionEntropy (Finset.biUnion_subset.2 fun j _ ↦ hX j :
            (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs ⊆ U)) := by
  classical
  set S : ∀ Y : Finset σ, Y ⊆ U → ℝ := fun _ h ↦ ρ.regionEntropy h with hS
  have hB : ∀ s : Finset ι, s.biUnion Xs ⊆ U := fun s ↦ Finset.biUnion_subset.2 fun j _ ↦ hX j
  have hdisjB : ∀ (s : Finset ι) i, i ∉ s → Disjoint (Xs i) (s.biUnion Xs) := fun s i hi ↦
    (Finset.disjoint_biUnion_right _ _ _).2 fun j hj ↦ hdisj fun h ↦ hi (h ▸ hj)
  -- conditioning on a region of the other children lowers the entropy below `S(X_i)`
  have hterm : ∀ (s : Finset ι) i, i ∉ s →
      S (Xs i ∪ s.biUnion Xs) (Finset.union_subset (hX i) (hB s)) - S (s.biUnion Xs) (hB s) ≤
        S (Xs i) (hX i) := fun s i hi ↦ by
    have h := ρ.toSubState.regionEntropy_union_sub_le_of_subset (Finset.empty_subset _)
      (hdisjB s i hi) (hX i) (hB s)
    rw [MState.regionEntropy_empty, sub_zero,
      ρ.regionEntropy_congr (Finset.union_empty (Xs i)) _ (hX i)] at h
    exact h
  rcases N with _ | n
  · have : IsEmpty ι := ⟨fun i ↦ (col i).elim0⟩
    simp
  set e := Fintype.equivFin ι
  set κ : Fin (n + 1) → ι → Lex (Fin (n + 1) × Fin (Fintype.card ι)) :=
    fun k i ↦ toLex (col i + k, e i)
  have hκ : ∀ k, Function.Injective (κ k) := fun k i j h ↦
    e.injective (congrArg (fun p ↦ (ofLex p).2) h)
  set pre : Fin (n + 1) → ι → Finset ι := fun k i ↦ Finset.univ.filter fun j ↦ κ k j < κ k i
  have hpre : ∀ k i, i ∉ pre k i := fun k i ↦ by simp [pre]
  set term : Fin (n + 1) → ι → ℝ := fun k i ↦
    S (Xs i ∪ (pre k i).biUnion Xs) (Finset.union_subset (hX i) (hB _)) -
      S ((pre k i).biUnion Xs) (hB _)
  -- the chain rule for each rotation
  have hchain : ∀ k, S (Finset.univ.biUnion Xs) (hB _) = ∑ i, term k i := by
    intro k
    let _ : LinearOrder ι := LinearOrder.lift' (κ k) (hκ k)
    have h := ρ.toSubState.regionEntropy_union_biUnion (Finset.empty_subset U) Finset.univ hX
    have hfil : ∀ i, (Finset.univ.filter (· < i)) = pre k i := fun i ↦ by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, pre]; rfl
    rw [ρ.regionEntropy_congr (Finset.empty_union _) _ (hB _), MState.regionEntropy_empty,
      zero_add, Finset.sum_congr rfl fun i _ ↦ ρ.toSubState.mutualInfo_congr rfl
        (by rw [Finset.empty_union, hfil i]) _ _ (hX i) (hB (pre k i)), ← Finset.sum_sub_distrib]
      at h
    rw [show S (Finset.univ.biUnion Xs) (hB _) = _ from h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [term, hS, SubState.mutualInfo_def]
    ring
  -- in the rotation putting the color of `i` last, the other colors precede `i`
  have hlast : ∀ i, term (Fin.last n - col i) i ≤
      S (Xs i ∪ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs)
          (Finset.union_subset (hX i) (hB _)) -
        S ((Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs) (hB _) := fun i ↦ by
    have hsub : Finset.univ.filter (fun j ↦ col j ≠ col i) ⊆ pre (Fin.last n - col i) i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pre, κ] at hj ⊢
      refine Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)
      change col j + (Fin.last n - col i) < col i + (Fin.last n - col i)
      rw [add_sub_cancel]
      exact lt_of_le_of_ne (Fin.le_last _)
        fun h ↦ hj (add_right_cancel (h.trans (add_sub_cancel (col i) _).symm))
    exact ρ.toSubState.regionEntropy_union_sub_le_of_subset
      (Finset.biUnion_subset_biUnion_of_subset_left _ hsub) (hdisjB _ i (hpre _ i)) (hX i)
      (hB _)
  have hbound : ∀ i, ∑ k, term k i ≤ (n : ℝ) * S (Xs i) (hX i) +
      (S (Xs i ∪ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs)
          (Finset.union_subset (hX i) (hB _)) -
        S ((Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs) (hB _)) := fun i ↦ by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.last n - col i))]
    have hrest : ∑ k ∈ Finset.univ.erase (Fin.last n - col i), term k i ≤
        (n : ℝ) * S (Xs i) (hX i) := by
      refine (Finset.sum_le_sum fun k _ ↦ hterm (pre k i) i (hpre k i)).trans_eq ?_
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.add_sub_cancel]
    linarith [hlast i]
  calc ((n + 1 : ℕ) : ℝ) * S (Finset.univ.biUnion Xs) (hB _)
      = ∑ k : Fin (n + 1), S (Finset.univ.biUnion Xs) (hB _) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ i, ∑ k, term k i := by
        rw [Finset.sum_congr rfl fun k _ ↦ hchain k, Finset.sum_comm]
    _ ≤ _ := (Finset.sum_le_sum fun i _ ↦ hbound i).trans_eq (by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        push_cast
        ring)

/-- **The chain rule averaged over rotated color orders**, with buffers.  Let `X_i` be pairwise
disjoint regions colored by `col : ι → Fin N`.  Suppose every `i ∈ good` has a buffer `T_i`
inside the union of the regions of the other colors, with `S(X_i | T_i) ≤ S(X_i)/2 + β`.  Then
`S(⋃ X_i) ≤ ∑ S(X_i) - (2N)⁻¹ ∑_{i ∈ good} S(X_i) + |good| β / N`. -/
theorem regionEntropy_biUnion_le_rotations (ρ : MState (Reg loc U) 𝕜) {ι : Type*} [Fintype ι]
    (Xs : ι → Finset σ) (hX : ∀ i, Xs i ⊆ U)
    (hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j)) {N : ℕ} (col : ι → Fin N)
    (good : Finset ι) (T : ι → Finset σ) (hTU : ∀ i, T i ⊆ U) (β : ℝ)
    (hT : ∀ i ∈ good, T i ⊆ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs)
    (hbuf : ∀ i ∈ good, ρ.regionEntropy (Finset.union_subset (hX i) (hTU i)) -
      ρ.regionEntropy (hTU i) ≤ ρ.regionEntropy (hX i) / 2 + β) :
    ρ.regionEntropy (Finset.biUnion_subset.2 fun i _ ↦ hX i : Finset.univ.biUnion Xs ⊆ U) ≤
      ∑ i, ρ.regionEntropy (hX i) - (∑ i ∈ good, ρ.regionEntropy (hX i)) / (2 * N) +
        good.card * β / N := by
  classical
  rcases N with _ | n
  · have : IsEmpty ι := ⟨fun i ↦ (col i).elim0⟩
    rw [Finset.eq_empty_of_isEmpty good, ρ.regionEntropy_congr
      (by rw [Finset.univ_eq_empty, Finset.biUnion_empty]) _ (Finset.empty_subset U)]
    simp
  have hB : ∀ s : Finset ι, s.biUnion Xs ⊆ U := fun s ↦ Finset.biUnion_subset.2 fun j _ ↦ hX j
  have hO : ∀ i, Disjoint (Xs i) ((Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs) :=
    fun i ↦ (Finset.disjoint_biUnion_right _ _ _).2 fun j hj ↦
      hdisj fun h ↦ (Finset.mem_filter.1 hj).2 (h ▸ rfl)
  have hc : ∀ i, ρ.regionEntropy (Finset.union_subset (hX i) (hB _) :
        Xs i ∪ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs ⊆ U) -
      ρ.regionEntropy (hB (Finset.univ.filter fun j ↦ col j ≠ col i)) ≤
        ρ.regionEntropy (hX i) - if i ∈ good then ρ.regionEntropy (hX i) / 2 - β else 0 := by
    intro i
    split_ifs with hi
    · have h := ρ.toSubState.regionEntropy_union_sub_le_of_subset (hT i hi) (hO i) (hX i) (hB _)
      rw [ρ.regionEntropy_congr rfl _ (Finset.union_subset (hX i) (hTU i)),
        ρ.regionEntropy_congr rfl _ (hTU i)] at h
      linarith [hbuf i hi]
    · have h := ρ.toSubState.regionEntropy_union_sub_le_of_subset (Finset.empty_subset _)
        (hO i) (hX i) (hB _)
      rw [MState.regionEntropy_empty, sub_zero,
        ρ.regionEntropy_congr (Finset.union_empty (Xs i)) _ (hX i)] at h
      linarith
  have key := (mul_regionEntropy_biUnion_le_rotations ρ Xs hX hdisj col).trans
    (add_le_add_right (Finset.sum_le_sum fun i _ ↦ hc i) _)
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at key
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have key' : ρ.regionEntropy (hB Finset.univ) ≤ ((((n + 1 : ℕ) : ℝ) - 1) *
      ∑ i, ρ.regionEntropy (hX i) + (∑ i, ρ.regionEntropy (hX i) -
        ((∑ i ∈ good, ρ.regionEntropy (hX i)) / 2 - good.card * β))) / ((n + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hN]
    linarith
  refine key'.trans_eq ?_
  field_simp
  ring

end OpenAI
