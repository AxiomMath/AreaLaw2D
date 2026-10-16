import OpenAI.Rectangles
import OpenAI.RegionLift

/-!
# Counting admissible supports

Counting facts about the admissible supports `supports Λ R` of eq. (1.1) of [OAI265], used in
the proof of Lemma 3.2.  Two sites of a support of range `R` are at sup-distance at most `R`,
so a support containing `a` lies in the box `[a - (R, R), a + (R, R)]` of `(2R + 1)²` sites.
Hence a support has at most `(2R + 1)²` sites, and at most `2 ^ (2R + 1)²` supports contain a
given site.

An admissible Hamiltonian is the sum, over the supports, of its terms extended by the identity;
each term is supported on its support, Hermitian, and of operator norm at most `J`.  The
supports split by a contour `A ∩ T^{+d}`, with `T^{+d}` inside a safe rectangle and `R ≤ d`,
all meet the layer `T^{+d} \ T^{+(d-R)}`, so for a rectangle `T` there are at most
`8 R 2^{(2R+1)²} (size T + d)` of them.  Contours whose dilation parameters differ by at least
`R` are never split by the same support.

## Main statements

* `subset_Icc_of_mem_supports`, `card_le_of_mem_supports`, `card_filter_mem_supports_le`: the
  box around a site, the size of a support, and the number of supports containing a site.
* `IsAdmissible.hamiltonian_eq_sum_supports`: the Hamiltonian as a sum over the supports, with
  `IsAdmissible.isHermitian_extendId` and `IsAdmissible.norm_extendId_le` for its terms.
* `card_crossingTerms_le_of_isSafe`, `IsIntRect.card_crossingTerms_le_of_isSafe`: the number of
  supports split by a contour near a cut.
* `eq_of_mem_crossingTerms_of_isSafe`, `eq_of_splits_of_isSafe`: a support is split by at most
  one contour of a family spaced by at least `R`.

## Implementation notes

The terms are indexed by the subtype of `supports Λ R`, with support map `Subtype.val`, so that
they form a family over a `Fintype` as `crossingTerms` requires.  Each term `Φ X ⊗ 1` is
supported on `X` by `isSupportedOn_extendId`.

The per-site count follows the sup-norm box rather than the `ℓ¹` diamond of TNLean
(`LionSR/TNLean`, commit `f4c2d204`, Apache 2.0, `card_admissibleSupport_containing_le` of
`PEPS/AreaLaw/BufferedRectangles.lean`), which gives `2 ^ (2R(R+1))`.  The crossing count
adapts `card_crossingTerms_rectRegion_le` of the same file, with a layer of width `R` rather
than `R + 1`, and the single-split lemma the `hsingle` step of
`PEPS/AreaLaw/InitialBuffer.lean`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §1.1 and §3.2.
-/

namespace OpenAI

open Arealaw Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Supports in a box -/

section Box

variable {Λ X : Finset (ℤ × ℤ)} {R : ℕ}

theorem subset_of_mem_supports (hX : X ∈ supports Λ R) : X ⊆ Λ :=
  (mem_supports_iff.1 hX).1

/-- A support of range `R` containing `a` lies in the box `[a - (R, R), a + (R, R)]`. -/
theorem subset_Icc_of_mem_supports (hX : X ∈ supports Λ R) {a : ℤ × ℤ} (ha : a ∈ X) :
    X ⊆ Finset.Icc (a - ((R : ℤ), (R : ℤ))) (a + ((R : ℤ), (R : ℤ))) := by
  intro x hx
  obtain ⟨h1, h2⟩ := dist_le_natCast_iff.1 (dist_le_of_mem_supports hX hx ha)
  rw [abs_le] at h1 h2
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  omega

theorem card_Icc_sub_add (a : ℤ × ℤ) (R : ℕ) :
    (Finset.Icc (a - ((R : ℤ), (R : ℤ))) (a + ((R : ℤ), (R : ℤ)))).card = (2 * R + 1) ^ 2 := by
  rw [card_Icc_eq_mul, sq]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  congr 1 <;> omega

/-- A support of range `R` has at most `(2R + 1)²` sites. -/
theorem card_le_of_mem_supports (hX : X ∈ supports Λ R) : X.card ≤ (2 * R + 1) ^ 2 := by
  obtain ⟨a, ha⟩ := (mem_supports_iff.1 hX).2.1
  exact (Finset.card_le_card (subset_Icc_of_mem_supports hX ha)).trans
    (card_Icc_sub_add a R).le

/-- The configurations of a support of range `R` number at most `q ^ (2R + 1)²`. -/
theorem card_reg_le_of_mem_supports {q : ℕ} (hX : X ∈ supports Λ R) :
    Fintype.card (Reg (Qudits q) X) ≤ q ^ (2 * R + 1) ^ 2 := by
  simp only [card_reg (loc := Qudits q), Fintype.card_fin, Finset.prod_const]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [zero_pow (Finset.card_ne_zero.2 (mem_supports_iff.1 hX).2.1)]
    exact Nat.zero_le _
  · exact Nat.pow_le_pow_right hq (card_le_of_mem_supports hX)

/-- At most `2 ^ (2R + 1)²` supports of range `R` contain a given site. -/
theorem card_filter_mem_supports_le (Λ : Finset (ℤ × ℤ)) (R : ℕ) (a : ℤ × ℤ) :
    ((supports Λ R).filter fun X => a ∈ X).card ≤ 2 ^ (2 * R + 1) ^ 2 := by
  have hsub : ((supports Λ R).filter fun X => a ∈ X) ⊆
      (Finset.Icc (a - ((R : ℤ), (R : ℤ))) (a + ((R : ℤ), (R : ℤ)))).powerset := by
    intro X hX
    rw [Finset.mem_filter] at hX
    exact Finset.mem_powerset.2 (subset_Icc_of_mem_supports hX.1 hX.2)
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_powerset, card_Icc_sub_add])

end Box

/-! ## The Hamiltonian as a sum over supports -/

section Hamiltonian

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J : ℝ} {Λ : Finset (ℤ × ℤ)}
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}

/-- **The Hamiltonian over its supports.**  For an admissible interaction, `H` is the sum of
the terms `Φ X ⊗ 1` over the admissible supports `X`. -/
theorem IsAdmissible.hamiltonian_eq_sum_supports (hΦ : IsAdmissible Λ R J Φ) :
    hamiltonian Λ Φ =
      ∑ X : supports Λ R, extendId (subset_of_mem_supports X.2) (Φ X) := by
  have hsub : supports Λ R ⊆ Λ.powerset := Finset.filter_subset _ _
  rw [hamiltonian_eq_sum_powerset, ← Finset.sum_subset hsub fun X hX hXs => ?_,
    ← Finset.sum_coe_sort]
  · exact Finset.sum_congr rfl fun X _ => dif_pos (subset_of_mem_supports X.2)
  · rw [Finset.mem_powerset] at hX
    rw [dif_pos hX, (hΦ X hX).2.2 hXs, extendId_zero]

theorem IsAdmissible.isHermitian_extendId (hΦ : IsAdmissible Λ R J Φ) (X : supports Λ R) :
    (extendId (subset_of_mem_supports X.2) (Φ X)).IsHermitian :=
  Arealaw.isHermitian_extendId _ (hΦ X.1 (subset_of_mem_supports X.2)).1

theorem IsAdmissible.norm_extendId_le (hΦ : IsAdmissible Λ R J Φ) (X : supports Λ R) :
    ‖extendId (subset_of_mem_supports X.2) (Φ X)‖ ≤ J :=
  (l2_opNorm_extendId_le _ _).trans (hΦ X.1 (subset_of_mem_supports X.2)).2.1

/-- The total norm of the Hamiltonian terms whose supports contain one site is bounded by
`2^((2R+1)^2) J`. -/
theorem IsAdmissible.sum_norm_extendId_containing_le (hΦ : IsAdmissible Λ R J Φ)
    (hJ : 0 ≤ J) (x : Λ) :
    ∑ X ∈ Finset.univ.filter (fun X : supports Λ R => x.1 ∈ X.1),
        ‖extendId (subset_of_mem_supports X.2) (Φ X)‖ ≤
      2 ^ (2 * R + 1) ^ 2 * J := by
  classical
  let s := Finset.univ.filter (fun X : supports Λ R => x.1 ∈ X.1)
  have hcard : s.card ≤ ((supports Λ R).filter fun X => x.1 ∈ X).card := by
    refine Finset.card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
    intro X hX
    change X ∈ s at hX
    change X.1 ∈ (supports Λ R).filter fun Y => x.1 ∈ Y
    exact Finset.mem_filter.2 ⟨X.2, (Finset.mem_filter.1 hX).2⟩
  have hcard' : s.card ≤ 2 ^ (2 * R + 1) ^ 2 :=
    hcard.trans (card_filter_mem_supports_le Λ R x.1)
  calc
    ∑ X ∈ s, ‖extendId (subset_of_mem_supports X.2) (Φ X)‖ ≤ s.card • J :=
      Finset.sum_le_card_nsmul _ _ _ fun X _ => hΦ.norm_extendId_le X
    _ = (s.card : ℝ) * J := by rw [nsmul_eq_mul]
    _ ≤ 2 ^ (2 * R + 1) ^ 2 * J := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') hJ

end Hamiltonian

/-! ## Supports split by a contour -/

section Crossing

variable {D₀ : ℝ} {Λ A Q T : Finset (ℤ × ℤ)} {R : ℕ}

/-- If every support split by `B` has a site in `L`, at most `2 ^ (2R + 1)² |L|` supports are
split by `B`. -/
theorem card_crossingTerms_le_of_forall {B L : Finset (ℤ × ℤ)}
    (h : ∀ X ∈ supports Λ R, (X ∩ B).Nonempty → (X \ B).Nonempty → ∃ v ∈ X, v ∈ L) :
    (crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) B).card ≤
      2 ^ (2 * R + 1) ^ 2 * L.card := by
  classical
  have hmaps : Set.MapsTo (fun X : supports Λ R => (X : Finset (ℤ × ℤ)))
      (crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) B)
      (L.biUnion fun v => (supports Λ R).filter fun X => v ∈ X) := by
    intro X hX
    obtain ⟨h1, h2⟩ := mem_crossingTerms.1 hX
    obtain ⟨v, hvX, hvL⟩ := h X.1 X.2 h1 h2
    exact Finset.mem_biUnion.2 ⟨v, hvL, Finset.mem_filter.2 ⟨X.2, hvX⟩⟩
  refine (Finset.card_le_card_of_injOn _ hmaps Subtype.val_injective.injOn).trans ?_
  rw [mul_comm]
  exact Finset.card_biUnion_le_card_mul _ _ _ fun v _ => card_filter_mem_supports_le Λ R v

/-- **Crossing count.**  If `T^{+d}` lies in a safe set `Q`, `R < D₀` and `R ≤ d`, at most
`2 ^ (2R + 1)² |T^{+d} \ T^{+(d-R)}|` admissible supports of range `R` are split by the contour
`A ∩ T^{+d}`. -/
theorem card_crossingTerms_le_of_isSafe (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀) {d : ℕ}
    (hd : R ≤ d) (hQ : ambientDilation T d ⊆ Q) :
    (crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ)))
        (A ∩ ambientDilation T d)).card ≤
      2 ^ (2 * R + 1) ^ 2 * (ambientDilation T d \ ambientDilation T (d - R)).card := by
  refine card_crossingTerms_le_of_forall fun X hX ⟨v, hv⟩ ⟨w, hw⟩ => ?_
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_sdiff] at hw
  exact ⟨v, hv.1, mem_sdiff_ambientDilation_of_isSafe hs hR (by omega) hQ hX hv.1 hv.2 hw.1 hw.2⟩

/-- **Crossing count for a rectangle** [OAI265, §3.2]: if `T` is an integer rectangle, `T^{+d}`
lies in a safe set `Q`, `R < D₀` and `R ≤ d`, at most `8 R 2^{(2R+1)²} (size T + d)` admissible
supports of range `R` are split by `A ∩ T^{+d}`. -/
theorem IsIntRect.card_crossingTerms_le_of_isSafe (hT : IsIntRect T) (hs : IsSafe D₀ Λ A Q)
    (hR : (R : ℝ) < D₀) {d : ℕ} (hd : R ≤ d) (hQ : ambientDilation T d ⊆ Q) :
    (crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ)))
        (A ∩ ambientDilation T d)).card ≤
      8 * R * 2 ^ (2 * R + 1) ^ 2 * (boxSize T + d) := by
  refine (OpenAI.card_crossingTerms_le_of_isSafe hs hR hd hQ).trans ?_
  have hlayer := hT.card_ambientDilation_sdiff_le hd
  calc 2 ^ (2 * R + 1) ^ 2 * (ambientDilation T d \ ambientDilation T (d - R)).card
      ≤ 2 ^ (2 * R + 1) ^ 2 * (4 * R * (boxSize T + 2 * d)) := Nat.mul_le_mul_left _ hlayer
    _ ≤ 2 ^ (2 * R + 1) ^ 2 * (4 * R * (2 * (boxSize T + d))) := by gcongr; omega
    _ = 8 * R * 2 ^ (2 * R + 1) ^ 2 * (boxSize T + d) := by ring

/-! ## A single split per support -/

/-- **Single split for a family of contours.**  Let `B j = A ∩ T^{+d_j}` for `j < m`, with
`T^{+d_j}` in a safe set `Q`, `R < D₀`, and `d_j + R ≤ d_{j'}` for `j < j' < m`, and let
`B j ⊇ Λ` for `j ≥ m`.  Then an admissible support of range `R` is split by at most one
`B j`. -/
theorem eq_of_mem_crossingTerms_of_isSafe (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀)
    {m : ℕ} {d : ℕ → ℕ} (hd : ∀ j j', j < j' → j' < m → d j + R ≤ d j')
    (hQ : ∀ j < m, ambientDilation T (d j) ⊆ Q) {B : ℕ → Finset (ℤ × ℤ)}
    (hB : ∀ j < m, B j = A ∩ ambientDilation T (d j)) (hBm : ∀ j, m ≤ j → Λ ⊆ B j)
    {X : supports Λ R} {j j' : ℕ}
    (hj : X ∈ crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) (B j))
    (hj' : X ∈ crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) (B j')) :
    j = j' := by
  have hlt : ∀ k, X ∈ crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) (B k) →
      k < m := by
    intro k hk
    by_contra hkm
    obtain ⟨-, w, hw⟩ := mem_crossingTerms.1 hk
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (hBm k (not_lt.1 hkm) (subset_of_mem_supports X.2 hw.1))
  have key : ∀ k k', k < k' → k' < m →
      X ∈ crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) (B k) →
      X ∈ crossingTerms (fun X : supports Λ R => (X : Finset (ℤ × ℤ))) (B k') → False := by
    intro k k' hkk hk' h1 h2
    obtain ⟨⟨v, hv⟩, -⟩ := mem_crossingTerms.1 h1
    obtain ⟨-, ⟨w, hw⟩⟩ := mem_crossingTerms.1 h2
    rw [Finset.mem_inter, hB k (hkk.trans hk')] at hv
    rw [Finset.mem_sdiff, hB k' hk'] at hw
    exact not_splits_two_contours hs hR (hd k k' hkk hk') (hQ k (hkk.trans hk')) X.2 hv.1 hv.2
      hw.1 hw.2
  rcases lt_trichotomy j j' with h | h | h
  · exact (key j j' h (hlt j' hj') hj hj').elim
  · exact h
  · exact (key j' j h (hlt j hj) hj' hj).elim

/-- `eq_of_mem_crossingTerms_of_isSafe` with splitting written through witnesses, the form of
the single-split hypothesis of the buffer discount. -/
theorem eq_of_splits_of_isSafe (hs : IsSafe D₀ Λ A Q) (hR : (R : ℝ) < D₀)
    {m : ℕ} {d : ℕ → ℕ} (hd : ∀ j j', j < j' → j' < m → d j + R ≤ d j')
    (hQ : ∀ j < m, ambientDilation T (d j) ⊆ Q) {B : ℕ → Finset (ℤ × ℤ)}
    (hB : ∀ j < m, B j = A ∩ ambientDilation T (d j)) (hBm : ∀ j, m ≤ j → Λ ⊆ B j)
    (X : supports Λ R) (j j' : ℕ)
    (hj : (∃ v ∈ (X : Finset (ℤ × ℤ)), v ∈ B j) ∧ ∃ v ∈ (X : Finset (ℤ × ℤ)), v ∉ B j)
    (hj' : (∃ v ∈ (X : Finset (ℤ × ℤ)), v ∈ B j') ∧ ∃ v ∈ (X : Finset (ℤ × ℤ)), v ∉ B j') :
    j = j' := by
  refine eq_of_mem_crossingTerms_of_isSafe hs hR hd hQ hB hBm (X := X) ?_ ?_
  · obtain ⟨⟨v, hv, hvB⟩, w, hw, hwB⟩ := hj
    exact mem_crossingTerms.2 ⟨⟨v, Finset.mem_inter.2 ⟨hv, hvB⟩⟩,
      ⟨w, Finset.mem_sdiff.2 ⟨hw, hwB⟩⟩⟩
  · obtain ⟨⟨v, hv, hvB⟩, w, hw, hwB⟩ := hj'
    exact mem_crossingTerms.2 ⟨⟨v, Finset.mem_inter.2 ⟨hv, hvB⟩⟩,
      ⟨w, Finset.mem_sdiff.2 ⟨hw, hwB⟩⟩⟩

end Crossing

end OpenAI
