import OpenAI.BoxEntropy
import OpenAI.BufferDiscount
import OpenAI.ChildColoring
import OpenAI.HarmonicWeights
import OpenAI.RotatedChainRule
import OpenAI.SafeBoxChildren

/-!
# The initial safe-box estimate

Proposition 3.3 of [OAI265] bounds the safe-box entropy by `F_box(r) ≤ C r^{1 + e₀}` with
`e₀ ∈ (0, 1)`, the constants depending only on `q, R, J, Δ`.  Here it is derived from the
buffer discount of Lemma 3.2.

A safe parent `Q` of size at most `M r` is cut into at most `M²` children of size at most `r`,
safe as well.  With `P = 2 C_pad + 1`, colour the child at chunk position `(i, j)` by
`(i mod P) P + (j mod P)`, one of `N = P²` colours; the padding `Q₀^{+C_pad r}` of a child meets
only children of other colours.  A child at least `C_pad` positions from the first chunk and
`C_pad + 2` from the last along both axes has its padding inside `Q`, so the buffer discount
applies to it; at most `2 (2 C_pad + 1) M` children are not of this kind.  The chain rule
averaged over the `N` cyclic rotations of the colours then gives, with `p = 1/(2N)`,
`S(A ∩ Q) ≤ ((1 - p) M² + p · 2 (2 C_pad + 1) M) F_box(r) + C_buf M² r`.  For
`M = 8 (C_pad + 1)` the coefficient is at most `λ = (1 - p/2) M²`, and `M < λ < M²`, so the
scale recurrence `F_box(M r) ≤ λ F_box(r) + C_buf M² r` gives
`F_box(r) ≤ C r^{log λ / log M}` with exponent `1 + e₀`, `e₀ = log λ / log M - 1 ∈ (0, 1)`.

## Main statements

* `OpenAI.regionEntropy_inter_le_of_children`: the estimate for one safe parent.
* `OpenAI.boxEntropy_le_of_scale`: the scale recurrence, eq. (3.20) of [OAI265].
* `OpenAI.initial_box_estimate_of_bufferDiscount`: Lemma 3.2 implies Proposition 3.3.

## Implementation notes

The paper averages the chain rule over a uniformly random order of the children, under which
each interior child comes last among its neighbours with probability at least `1/N`.  The `N`
cyclic rotations of the colours replace the random order: each child comes after all children
of the other colours in exactly one of them, which gives the same frequency `1/N`.

The one-parent estimate is stated for an arbitrary state and an arbitrary bound `F` on the
entropies of the sub-rectangles of size at most `r`; the Hamiltonian enters only through
`F = F_box(r)` and the buffer discount.  `BufferDiscount` does not assert `C_buf ≥ 0`, which
the averaging needs (the discount is applied to at most `M²` of the children), so the proof uses
`max C_buf 0`.

Ported from TNLean (`LionSR/TNLean`, commit `f4c2d204`, Apache 2.0),
`TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean` (`regionalEntropy_rectRegion_le_of_children`,
`boxEntropy_le_of_scale`, `exists_boxEntropy_le_rpow_fixed`).  TNLean works at one natural
`D₀` and reaches the others by monotonicity in `D₀`; here `D₀` is real and `F_box` is a
supremum over every `D₀ > 2R + 10` as well, so no monotonicity in `D₀` is used.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.3, Proposition 3.3 and its proof.
-/

namespace OpenAI

open Arealaw Matrix
open scoped MatrixOrder

section Parent

variable {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {Λ : Finset (ℤ × ℤ)}

/-- **One safe parent** [OAI265, §3.3].  Let `Q` be a rectangle of size at most `M r`, and `F`
a bound on `S(A ∩ Q₀)` for every rectangle `Q₀ ⊆ Q` of size at most `r`.  If every rectangle
`Q₀` of size at most `r` with `Q₀^{+C_pad r} ⊆ Q` satisfies the buffer discount
`S(X | T) ≤ S(X)/2 + C_buf r` for `X = A ∩ Q₀` and `T = (A ∩ Q₀^{+C_pad r}) \ X`, with
`C_buf ≥ 0`, then, for `p = 1/(2 (2 C_pad + 1)²)`,
`S(A ∩ Q) ≤ ((1 - p) M² + p · 2 (2 C_pad + 1) M) F + C_buf M² r`. -/
theorem regionEntropy_inter_le_of_children (ρ : MState (Reg loc Λ) 𝕜) {A Q : Finset (ℤ × ℤ)}
    (hA : A ⊆ Λ) (hQ : IsIntRect Q) {M r : ℕ} (hr : 1 ≤ r) (hQr : boxSize Q ≤ M * r) {F : ℝ}
    (hF : ∀ Q₀, IsIntRect Q₀ → Q₀ ⊆ Q → boxSize Q₀ ≤ r →
      ρ.regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) ≤ F)
    {Cpad : ℕ} {Cbuf : ℝ} (hCbuf : 0 ≤ Cbuf)
    (hbuf : ∀ Q₀, IsIntRect Q₀ → boxSize Q₀ ≤ r → ambientDilation Q₀ (Cpad * r) ⊆ Q →
      ρ.regionEntropy
          ((Finset.union_subset (Finset.inter_subset_left.trans hA)
            (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA))) :
            A ∩ Q₀ ∪ (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) -
        ρ.regionEntropy
          (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA) :
            (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) ≤
      ρ.regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) / 2 + Cbuf * r) :
    ρ.regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤
      ((1 - 1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2)) * (M : ℝ) ^ 2 +
        1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2) * (2 * (2 * Cpad + 1) * M)) * F +
          Cbuf * M ^ 2 * r := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hQ
  set P : ℕ := 2 * Cpad + 1 with hPdef
  set N : ℕ := P ^ 2 with hNdef
  set nx := numChunksX a b r
  set ny := numChunksY a b r
  have hnx : nx ≤ M := numChunksX_le hab hr hQr
  have hny : ny ≤ M := numChunksY_le hab hr hQr
  have hP : 0 < P := by omega
  have hX : ∀ i : Fin nx × Fin ny, A ∩ rectChild a b r i.1 i.2 ⊆ Λ := fun _ ↦
    Finset.inter_subset_left.trans hA
  set Xs : Fin nx × Fin ny → Finset (ℤ × ℤ) := fun i ↦ A ∩ rectChild a b r i.1 i.2
  set T : Fin nx × Fin ny → Finset (ℤ × ℤ) := fun i ↦
    (A ∩ ambientDilation (rectChild a b r i.1 i.2) (Cpad * r)) \ Xs i
  have hTU : ∀ i, T i ⊆ Λ := fun _ ↦ Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA)
  set col : Fin nx × Fin ny → Fin N := fun i ↦ ⟨((i.1 : ℕ) % P) * P + (i.2 : ℕ) % P, by
    have h1 := Nat.mod_lt (i.1 : ℕ) hP
    have h2 := Nat.mod_lt (i.2 : ℕ) hP
    simp only [hNdef, sq]
    nlinarith⟩
  set good : Finset (Fin nx × Fin ny) := Finset.univ.filter fun i ↦
    (Cpad ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) + Cpad + 2 ≤ nx) ∧ (Cpad ≤ (i.2 : ℕ) ∧ (i.2 : ℕ) + Cpad + 2 ≤ ny)
  -- the children partition `A ∩ Q`
  have hunion : Finset.univ.biUnion Xs = A ∩ Finset.Icc a b := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Xs, Finset.mem_inter]
    constructor
    · rintro ⟨i, hxA, hx⟩
      exact ⟨hxA, rectChild_subset hx⟩
    · rintro ⟨hxA, hx⟩
      obtain ⟨i, hi, j, hj, hij⟩ := exists_mem_rectChild hr hx
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), hxA, hij⟩
  have hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j) := by
    intro i j hij
    refine Finset.disjoint_left.2 fun x hxi hxj ↦ hij ?_
    obtain ⟨h1, h2⟩ := eq_of_mem_rectChild (Finset.mem_inter.1 hxi).2 (Finset.mem_inter.1 hxj).2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  -- buffers of interior children lie in children of other colours
  have hT : ∀ i ∈ good, T i ⊆ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs := by
    intro i hi x hx
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [T, Xs, Finset.mem_sdiff, Finset.mem_inter] at hx
    obtain ⟨⟨hxA, hxd⟩, hxi⟩ := hx
    have hxQ := ambientDilation_rectChild_subset hr hi.1.2 hi.2.2 hi.1.1 hi.2.1 hxd
    obtain ⟨i', hi', j', hj', hij'⟩ := exists_mem_rectChild hr hxQ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(⟨i', hi'⟩, ⟨j', hj'⟩), fun hc ↦ ?_, Finset.mem_inter.2 ⟨hxA, hij'⟩⟩
    obtain ⟨d1, d2, d3, d4⟩ := le_add_of_mem_rectChild_of_mem_ambientDilation hij' hxd
    obtain ⟨e1, e2⟩ := eq_of_color_eq (P := P) (C := Cpad) (by omega)
      (congrArg Fin.val hc) d2 d1 d4 d3
    subst e1 e2
    exact hxi ⟨hxA, hij'⟩
  have hbuf' : ∀ i ∈ good, ρ.regionEntropy (Finset.union_subset (hX i) (hTU i)) -
      ρ.regionEntropy (hTU i) ≤ ρ.regionEntropy (hX i) / 2 + Cbuf * r := by
    intro i hi
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hbuf _ (isIntRect_rectChild hr i.1.isLt i.2.isLt) boxSize_rectChild_le
      (ambientDilation_rectChild_subset hr hi.1.2 hi.2.2 hi.1.1 hi.2.1)
  have key := regionEntropy_biUnion_le_rotations ρ Xs hX hdisj col good T hTU (Cbuf * r) hT hbuf'
  rw [ρ.toSubState.regionEntropy_congr hunion _ (Finset.inter_subset_left.trans hA)] at key
  -- bounds on the children
  have hXF : ∀ i, ρ.regionEntropy (hX i) ≤ F := fun i ↦
    hF _ (isIntRect_rectChild hr i.1.isLt i.2.isLt) rectChild_subset boxSize_rectChild_le
  have hF0 : 0 ≤ F := by
    refine (SubState.regionEntropy_nonneg _ (Finset.inter_subset_left.trans hA :
      A ∩ Finset.Icc a a ⊆ Λ)).trans (hF _ (isIntRect_Icc le_rfl)
      (Finset.Icc_subset_Icc_right hab) ?_)
    rw [boxSize_Icc le_rfl]
    simp only [add_sub_cancel_left, Int.toNat_one, max_self]
    exact hr
  have hcard : (Finset.univ : Finset (Fin nx × Fin ny)).card ≤ M ^ 2 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, sq]
    exact Nat.mul_le_mul hnx hny
  have hbad : (Finset.univ \ good).card ≤ 2 * (2 * Cpad + 1) * M := by
    have hsub' : Finset.univ \ good ⊆
        ((Finset.univ : Finset (Fin nx)).filter
            fun a : Fin nx ↦ ¬ (Cpad ≤ a.val ∧ a.val + Cpad + 2 ≤ nx)) ×ˢ Finset.univ ∪
          Finset.univ ×ˢ ((Finset.univ : Finset (Fin ny)).filter
            fun b : Fin ny ↦ ¬ (Cpad ≤ b.val ∧ b.val + Cpad + 2 ≤ ny)) := by
      intro i hi
      simp only [good, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and,
        not_and_or] at hi
      rcases hi with hi | hi
      · exact Finset.mem_union_left _ (Finset.mem_product.2
          ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩, Finset.mem_univ _⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.2
          ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩⟩)
    have h1 := card_filter_not_interior_le nx Cpad
    have h2 := card_filter_not_interior_le ny Cpad
    refine (Finset.card_le_card hsub').trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
    have := Nat.mul_le_mul h1 hny
    have := Nat.mul_le_mul hnx h2
    nlinarith
  -- assemble
  have hNR : (N : ℝ) = (2 * (Cpad : ℝ) + 1) ^ 2 := by simp [hNdef, hPdef]
  set p : ℝ := 1 / (2 * (N : ℝ)) with hp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_pow _ _ hP
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    linarith
  have hsplit : ∑ i, ρ.regionEntropy (hX i) - (∑ i ∈ good, ρ.regionEntropy (hX i)) / (2 * N) =
      (1 - p) * ∑ i ∈ good, ρ.regionEntropy (hX i) +
        ∑ i ∈ Finset.univ \ good, ρ.regionEntropy (hX i) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ good), hp]
    field_simp
    ring
  have hg : ∑ i ∈ good, ρ.regionEntropy (hX i) ≤ good.card * F := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ hXF i
  have hb : ∑ i ∈ Finset.univ \ good, ρ.regionEntropy (hX i) ≤
      (Finset.univ \ good).card * F := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ hXF i
  have hgb : (good.card : ℝ) + (Finset.univ \ good).card ≤ M ^ 2 := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good)
    have : (((Finset.univ \ good).card + good.card : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
      rw [h1]
      exact_mod_cast hcard
    push_cast at this
    linarith
  have hbad' : ((Finset.univ \ good).card : ℝ) ≤ 2 * (2 * Cpad + 1) * M := by
    exact_mod_cast hbad
  have hgood' : (good.card : ℝ) * (Cbuf * r) / N ≤ Cbuf * M ^ 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    have hgM : (good.card : ℝ) ≤ M ^ 2 := by
      have : (0 : ℝ) ≤ (Finset.univ \ good).card := Nat.cast_nonneg _
      linarith
    have h0 : 0 ≤ Cbuf * r := by positivity
    calc (good.card : ℝ) * (Cbuf * r) ≤ M ^ 2 * (Cbuf * r) :=
          mul_le_mul_of_nonneg_right hgM h0
      _ ≤ M ^ 2 * (Cbuf * r) * N := le_mul_of_one_le_right (by positivity) hN1
      _ = Cbuf * M ^ 2 * r * N := by ring
  have hfinal : (1 - p) * (good.card * F) + (Finset.univ \ good).card * F ≤
      ((1 - p) * M ^ 2 + p * (2 * (2 * Cpad + 1) * M)) * F := by
    have : (1 - p) * (good.card * F) + (Finset.univ \ good).card * F =
        ((1 - p) * (good.card + (Finset.univ \ good).card) +
          p * (Finset.univ \ good).card) * F := by ring
    rw [this]
    gcongr
  rw [hsplit] at key
  have := mul_le_mul_of_nonneg_left hg (by linarith : 0 ≤ 1 - p)
  have hpe : p = 1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2) := by rw [hp, hNR]
  rw [← hpe]
  linarith

end Parent

section Recurrence

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}

/-- **The scale recurrence** [OAI265, eq. (3.20)].  If the buffer discount of Lemma 3.2 holds
with constants `C_pad` and `C_buf ≥ 0`, then for `M ≥ 0`, `r ≥ 1` and
`p = 1/(2 (2 C_pad + 1)²)`,
`F_box(M r) ≤ ((1 - p) M² + p · 2 (2 C_pad + 1) M) F_box(r) + C_buf M² r`. -/
theorem boxEntropy_le_of_scale {Cpad : ℕ} {Cbuf : ℝ} (hCbuf : 0 ≤ Cbuf)
    (hbuf : ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
      ∀ Λ : Finset (ℤ × ℤ),
      ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
        IsAdmissible Λ R J Φ →
      ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)), IsIntRect Q → IsSafe D₀ Λ A Q →
      ∀ (r : ℕ), 1 ≤ r → ∀ Q₀ : Finset (ℤ × ℤ), IsIntRect Q₀ → boxSize Q₀ ≤ r →
        ambientDilation Q₀ (Cpad * r) ⊆ Q →
        (pureState Ω hΩ).regionEntropy
            ((Finset.union_subset (Finset.inter_subset_left.trans hA)
              (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA))) :
              A ∩ Q₀ ∪ (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) -
          (pureState Ω hΩ).regionEntropy
            (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA) :
              (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) ≤
        (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) / 2 +
          Cbuf * r)
    (M : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    boxEntropy 𝕜 q R J Δ (M * r) ≤
      ((1 - 1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2)) * (M : ℝ) ^ 2 +
        1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2) * (2 * (2 * Cpad + 1) * M)) *
          boxEntropy 𝕜 q R J Δ r + Cbuf * M ^ 2 * r := by
  refine Real.sSup_le (fun s hs => ?_) ?_
  · obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hQr, rfl⟩ := hs
    have hD₀' : 0 ≤ D₀ := by
      have : (0 : ℝ) ≤ 2 * R + 10 := by positivity
      linarith
    exact regionEntropy_inter_le_of_children (pureState Ω hΩ) hA hQ hr hQr
      (fun Q₀ hQ₀ hsub hsz => regionEntropy_le_boxEntropy hD₀ hΦ hΩ hE hgap hA hQ₀
        (hs.subset hD₀' hsub) hsz) hCbuf (hbuf D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hs r hr)
  · have hF := boxEntropy_nonneg (𝕜 := 𝕜) (q := q) (R := R) (J := J) (Δ := Δ) r
    have hN : (1 : ℝ) ≤ (2 * (Cpad : ℝ) + 1) ^ 2 :=
      one_le_pow₀ (by linarith [Cpad.cast_nonneg (α := ℝ)])
    have hp1 : 1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have : (0 : ℝ) ≤ 1 - 1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2) := by linarith
    positivity

/-- **Lemma 3.2 implies Proposition 3.3** [OAI265, §3.3]: the buffer discount gives
constants `C` and `e₀ ∈ (0, 1)` with `S_Ω(A ∩ Q) ≤ C r^{1 + e₀}` for every safe rectangle `Q`
of size at most `r`, uniformly in `D₀ > 2R + 10`. -/
theorem initial_box_estimate_of_bufferDiscount (h : BufferDiscount 𝕜 q R J Δ) :
    InitialBoxEstimate 𝕜 q R J Δ := by
  obtain ⟨Cpad, hCpad, Cbuf, hbuf⟩ := h
  set Cb : ℝ := max Cbuf 0
  have hCb : 0 ≤ Cb := le_max_right _ _
  set p : ℝ := 1 / (2 * (2 * (Cpad : ℝ) + 1) ^ 2) with hp
  set M : ℕ := 8 * (Cpad + 1) with hMdef
  set lam : ℝ := (1 - p / 2) * M ^ 2 with hlam
  have hC1 : (1 : ℝ) ≤ Cpad := by exact_mod_cast hCpad
  have hN1 : (1 : ℝ) ≤ (2 * (Cpad : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 / 2 := by
    rw [hp, div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have hM : 2 ≤ M := by omega
  have hM' : (16 : ℝ) ≤ M := by
    rw [hMdef]
    push_cast
    linarith
  have hp34 : (3 / 4 : ℝ) ≤ 1 - p / 2 := by linarith
  have hMlam : (M : ℝ) < lam := by
    have h1 : (12 : ℝ) ≤ (1 - p / 2) * M := by nlinarith
    have h2 : (12 : ℝ) * M ≤ (1 - p / 2) * M * M :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : lam = (1 - p / 2) * M * M := by rw [hlam]; ring
    rw [h3]
    linarith
  have hlamM2 : lam < (M : ℝ) ^ 2 := by
    have : 0 < (M : ℝ) ^ 2 := by positivity
    rw [hlam]
    nlinarith
  have hrec : ∀ r, 1 ≤ r → boxEntropy 𝕜 q R J Δ (M * r) ≤
      lam * boxEntropy 𝕜 q R J Δ r + Cb * M ^ 2 * r := by
    intro r hr
    refine (boxEntropy_le_of_scale hCb (fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hs r hr Q₀
      hQ₀ hsz hdil => (hbuf D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hs r hr Q₀ hQ₀ hsz hdil).trans
        (by gcongr; exact le_max_left _ _)) M hr).trans ?_
    have hF0 := boxEntropy_nonneg (𝕜 := 𝕜) (q := q) (R := R) (J := J) (Δ := Δ) r
    gcongr
    -- `(1 - p) M² + p · 2 (2 C_pad + 1) M ≤ (1 - p/2) M²` since `2 (2 C_pad + 1) ≤ M/2`
    have hB : 2 * (2 * (Cpad : ℝ) + 1) * M ≤ (M : ℝ) ^ 2 / 2 := by
      have : 2 * (2 * (Cpad : ℝ) + 1) ≤ M / 2 := by
        rw [hMdef]
        push_cast
        linarith
      nlinarith
    rw [← hp, hlam]
    nlinarith
  obtain ⟨C, hC⟩ := exists_le_mul_rpow_of_scale_recurrence boxEntropy_mono hM hMlam
    (by positivity) hrec
  have hexp := one_lt_log_div_log_lt_two (by exact_mod_cast hM) hMlam hlamM2
  refine ⟨C, Real.log lam / Real.log M - 1, by linarith [hexp.1], by linarith [hexp.2],
    fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q r hr hQ hs hQr => ?_⟩
  rw [add_sub_cancel]
  exact (regionEntropy_le_boxEntropy hD₀ hΦ hΩ hE hgap hA hQ hs hQr).trans (hC r hr)

end Recurrence

/-- **Proposition 3.3** [OAI265, §3.3, eq. (3.21)]: for a gapped ground vector of an admissible
Hamiltonian, the entropy of a cut inside a safe rectangle of size at most `r` is at most
`C r^{1 + e₀}`, with `e₀ ∈ (0, 1)` and `C` depending only on `q, R, J, Δ`. -/
theorem initial_box_estimate {𝕜 : Type*} [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q)
    (hJ : 0 < J) (hΔ : 0 < Δ) : InitialBoxEstimate 𝕜 q R J Δ :=
  initial_box_estimate_of_bufferDiscount (buffer_discount q R J Δ hq hJ hΔ)

end OpenAI
