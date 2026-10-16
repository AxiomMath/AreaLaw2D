import OpenAI.BufferDiscountCore
import OpenAI.SupportCounting
import OpenAI.HarmonicWeights
import OpenAI.Embedding

/-!
# Conditional entropy in a buffered rectangle

Lemma 3.2 of [OAI265]: for a gapped ground vector `Ω` of an admissible Hamiltonian of range
`R`, a cut `A`, a safe rectangle `Q` and a rectangle `Q₀` of size at most `r` whose dilation
`Q₀^{+C_pad r}` lies in `Q`, the region `X = A ∩ Q₀` and its buffer
`T = (A ∩ Q₀^{+C_pad r}) \ X` satisfy `S(X | T) ≤ S(X)/2 + C_buf r`, with `C_pad` and `C_buf`
depending only on `q`, `R`, `J`, `Δ`.

The finite-dimensional argument is `OpenAI.two_mul_condEntropy_le`.  This file supplies its
lattice hypotheses: the nested contours `X ∪ T_j = A ∩ Q₀^{+d_j}`, `d_j = r + (j+1)(R+1)` for
`j < m = ⌊(C_pad - 1) r/(R+1)⌋`; the single-split property of safe rectangles; the crossing
counts `≤ K (r + d_j)`, `K = 8 R 2^{(2R+1)²}`, hence cut parameters `𝓑_j ≤ K' (r + d_j)`; the
harmonic weights `a_j = 2/(Z (r + d_j))` of total mass two and quadratic cost `4/Z`; and a
padding `C_pad` making `Z` large uniformly in `r`.

## Main definitions

* `OpenAI.bufferCrossConst`, `OpenAI.bufferBudgetConst`: the constants `K` and `K'`.

## Main statements

* `OpenAI.condEntropy_le_initialBuffer_of_constants`: the discount at explicit constants, for
  any real `D₀ > R`.
* `OpenAI.bufferDiscount_of_complex`: Lemma 3.2 over `ℂ` gives it over every `RCLike` field.
* `OpenAI.buffer_discount`: **Lemma 3.2** of [OAI265], eq. (3.9).

## Implementation notes

Ported from TNLean (LionSR/TNLean), `TNLean/PEPS/AreaLaw/InitialBuffer.lean` at commit
`f4c2d204` (Apache 2.0), written there from the proof of Lemma 3.2 of [OAI265].  Changes: the
namespace is `OpenAI`; the region model is `Reg (Qudits q) Λ` with the regions as subsets of
`Λ`, so TNLean's `rectRegion A Q₀` is `A ∩ Q₀` and its `Q₀.dilate d` is
`OpenAI.ambientDilation Q₀ d`, and the contours beyond the last one are `Λ \ X` rather than the
complement of `X` in the site type; the terms are indexed by the admissible supports
`↥(supports Λ R)`; the safety parameter `D₀` is real, and only `R < D₀` is used.

The constants differ from TNLean's through the support counts of `OpenAI.SupportCounting`,
which bound a support by the sup-norm box: a support has at most `v = (2R+1)²` sites, hence
dimension at most `q^v`, and at most `K (size Q₀ + d)` supports, `K = 8 R 2^{(2R+1)²}`, are
split by `A ∩ Q₀^{+d}`.  With `K' = 1 + K log² (e q^v)` and
`Z_min = max (4, 32 K q^{2v} J/Δ, 128 √((1 + J/Δ) K'))`, the constants of `OpenAI.buffer_discount`
are
`C_pad = ⌈(R + 3) e^{(R+1) Z_min}⌉₊ + R + 3` and `C_buf = (1024 e (J/Δ) K' + C_pad)/2`.

The discount is proved over `ℂ`, because the filter argument behind
`OpenAI.two_mul_condEntropy_le` is complex (`OpenAI.bufferDiscount_complex`).
`OpenAI.bufferDiscount_of_complex` transfers it to a general `RCLike` field along
`OpenAI.toComplex`, which preserves admissibility, the eigenvector equation, the gap and every
region entropy.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.2, Lemma 3.2 and eq. (3.9).
-/

namespace OpenAI

open Arealaw Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Shifting the index of a finite sum from `0, …, m-1` to `1, …, m`. -/
theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ j ∈ Finset.range m, f (j + 1) = ∑ j ∈ Finset.Icc 1 m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-! ## Supports and cut parameters -/

section Supports

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ}

/-- A region of qudits of positive dimension has at least one configuration. -/
theorem one_le_card_reg_qudits (hq : 1 ≤ q) (X : Finset (ℤ × ℤ)) :
    1 ≤ Fintype.card (Reg (Qudits q) X) := by
  simp only [card_reg (loc := Qudits q), Fintype.card_fin, Finset.prod_const]
  exact Nat.one_le_pow _ _ hq

/-- The cut parameter grows at most linearly with the number of crossing supports:
`𝓑 ≤ 1 + |𝒞| log² (e q^{(2R+1)²})`. -/
theorem cutLogBudget_le_card (hq : 1 ≤ q) (Cr : Finset (supports Λ R)) :
    cutLogBudget Cr (fun X ↦ Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ)))) ≤
      1 + Cr.card * Real.log (Real.exp 1 * (q : ℝ) ^ (2 * R + 1) ^ 2) ^ 2 := by
  have hbound : ∀ X ∈ Cr,
      Real.log (Real.exp 1 * (Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) : ℝ)) ^ 2 ≤
        Real.log (Real.exp 1 * (q : ℝ) ^ (2 * R + 1) ^ 2) ^ 2 := by
    intro X _
    have h1 : (1 : ℝ) ≤ Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) := by
      exact_mod_cast one_le_card_reg_qudits hq _
    have h2 : (Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ))) : ℝ) ≤
        (q : ℝ) ^ (2 * R + 1) ^ 2 := by
      exact_mod_cast card_reg_le_of_mem_supports X.2
    have he : 1 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hl : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) (X : Finset (ℤ × ℤ)))) :=
      Real.log_nonneg (by nlinarith)
    have := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le)
    exact pow_le_pow_left₀ hl this 2
  have hsum := Finset.sum_le_card_nsmul Cr _ _ hbound
  rw [nsmul_eq_mul] at hsum
  rw [cutLogBudget]
  linarith

end Supports

/-! ## Scalar estimates for the harmonic weights -/

/-- A weight `a = 2/(Z c)` with `Z ≥ 4` and `c ≥ 1` satisfies `a ≤ 1/2`. -/
theorem harmonic_weight_le_half {Z c : ℝ} (hZ : 4 ≤ Z) (hc : 1 ≤ c) : 2 / (Z * c) ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (by positivity) two_pos]
  nlinarith

/-- A weight `a = 2/(Z c)` with `Z ≥ 4` and `c ≥ 1` satisfies `a/(1-a) ≤ 2a = 4/(Z c)`. -/
theorem harmonic_weight_ratio_le {Z c : ℝ} (hZ : 4 ≤ Z) (hc : 1 ≤ c) :
    2 / (Z * c) / (1 - 2 / (Z * c)) ≤ 4 / (Z * c) := by
  have ha := harmonic_weight_le_half hZ hc
  have ha0 : 0 < 2 / (Z * c) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have : 4 / (Z * c) = 2 * (2 / (Z * c)) := by ring
  rw [this]
  nlinarith

/-- **The admissible tail range**: if `𝓑 ≤ K' c` with `c ≥ 1` and `Z ≥ 128 √((1 + ϑ) K')`, then
`4/(Z c) ≤ 1/(32 √((1 + ϑ) 𝓑))`. -/
theorem le_tailRadius_of_le {Z c ϑ K' B : ℝ} (hZ : 128 * Real.sqrt ((1 + ϑ) * K') ≤ Z)
    (hZ0 : 0 < Z) (hc : 1 ≤ c) (hϑ : 0 ≤ ϑ) (hB1 : 1 ≤ B) (hB : B ≤ K' * c) :
    4 / (Z * c) ≤ tailRadius ϑ B := by
  have hK' : 0 ≤ K' := by nlinarith
  rw [tailRadius, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : Real.sqrt ((1 + ϑ) * B) ≤ Real.sqrt ((1 + ϑ) * K') * c := by
    calc Real.sqrt ((1 + ϑ) * B) ≤ Real.sqrt ((1 + ϑ) * K' * c) :=
          Real.sqrt_le_sqrt (by rw [mul_assoc]; gcongr)
      _ = Real.sqrt ((1 + ϑ) * K') * Real.sqrt c := Real.sqrt_mul (by positivity) _
      _ ≤ Real.sqrt ((1 + ϑ) * K') * c := by
          gcongr
          calc Real.sqrt c ≤ Real.sqrt (c * c) := Real.sqrt_le_sqrt (by nlinarith)
            _ = c := Real.sqrt_mul_self (by linarith)
  have := mul_le_mul_of_nonneg_right hZ (by linarith : (0 : ℝ) ≤ c)
  nlinarith [Real.sqrt_nonneg ((1 + ϑ) * K')]

/-! ## The constants -/

/-- The constant `K = 8 R 2^{(2R+1)²}` of the crossing count. -/
noncomputable def bufferCrossConst (R : ℕ) : ℝ :=
  8 * R * 2 ^ (2 * R + 1) ^ 2

/-- The constant `K' = 1 + K log² (e q^{(2R+1)²})` bounding the cut parameters
`𝓑_j ≤ K' (r + d_j)`. -/
noncomputable def bufferBudgetConst (q R : ℕ) : ℝ :=
  1 + bufferCrossConst R * Real.log (Real.exp 1 * (q : ℝ) ^ (2 * R + 1) ^ 2) ^ 2

theorem bufferCrossConst_nonneg (R : ℕ) : 0 ≤ bufferCrossConst R := by
  unfold bufferCrossConst; positivity

theorem one_le_bufferBudgetConst (q R : ℕ) : 1 ≤ bufferBudgetConst q R := by
  unfold bufferBudgetConst
  have := mul_nonneg (bufferCrossConst_nonneg R)
    (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ (2 * R + 1) ^ 2)))
  linarith

/-! ## The discount at fixed constants -/

/-- **Lemma 3.2 at explicit constants.** Let `Z_min ≥ 4` dominate the energy and tail
thresholds, and let the padding `C_pad > R + 2` satisfy `(R + 3) e^{(R+1) Z_min} ≤ C_pad + 1`.
Then for a gapped ground vector, a set `Q` safe at a real `D₀ > R`, `r ≥ 1` and a rectangle
`Q₀` of size at most `r` with `Q₀^{+C_pad r} ⊆ Q`,
`S(X | T) ≤ S(X)/2 + (1024 e (J/Δ) K' + C_pad) r / 2` for `X = A ∩ Q₀` and
`T = (A ∩ Q₀^{+C_pad r}) \ X`. -/
theorem condEntropy_le_initialBuffer_of_constants {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) {Zmin : ℝ} (hZ4 : 4 ≤ Zmin)
    (hZE : 32 * bufferCrossConst R * (q : ℝ) ^ (2 * (2 * R + 1) ^ 2) * J / Δ ≤ Zmin)
    (hZT : 128 * Real.sqrt ((1 + J / Δ) * bufferBudgetConst q R) ≤ Zmin) {Cpad : ℕ}
    (hCR : R + 2 < Cpad)
    (hCZ : (2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin) ≤ Cpad + 1)
    {D₀ : ℝ} (hRD₀ : (R : ℝ) < D₀) {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ}
    (hΦ : IsAdmissible Λ R J Φ) {Ω : Reg (Qudits q) Λ → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1) {E₀ : ℝ}
    (heig : hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) {Q : Finset (ℤ × ℤ)} (hsafe : IsSafe D₀ Λ A Q) {r : ℕ}
    (hr : 1 ≤ r) {Q₀ : Finset (ℤ × ℤ)} (hQ₀ : IsIntRect Q₀) (hQ₀r : boxSize Q₀ ≤ r)
    (hpad : ambientDilation Q₀ (Cpad * r) ⊆ Q) :
    (pureState Ω hΩ).regionEntropy
        ((Finset.union_subset (Finset.inter_subset_left.trans hA)
          (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA))) :
          A ∩ Q₀ ∪ (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) -
      (pureState Ω hΩ).regionEntropy
        (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA) :
          (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) ≤
    (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) / 2 +
      (1024 * Real.exp 1 * (J / Δ) * bufferBudgetConst q R + Cpad) / 2 * r := by
  set K := bufferCrossConst R
  set K' := bufferBudgetConst q R
  set v : ℕ := (2 * R + 1) ^ 2
  have hK : 0 ≤ K := bufferCrossConst_nonneg R
  have hK' : 1 ≤ K' := one_le_bufferBudgetConst q R
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  -- the terms, and the ground vector as a unit vector of `EuclideanSpace`
  set S : supports Λ R → Finset (ℤ × ℤ) := fun X ↦ X.1
  have hSU : ∀ i, S i ⊆ Λ := fun X ↦ subset_of_mem_supports X.2
  set h : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X ↦ extendId (hSU X) (Φ X)
  have hsupp : ∀ i, IsSupportedOn (hSU i) (h i) := fun X ↦ isSupportedOn_extendId _ _
  have hH : hamiltonian Λ Φ = ∑ X, h X := hΦ.hamiltonian_eq_sum_supports
  obtain ⟨hn, heu, hpsd⟩ :=
    (normalized_eigen_hasGlobalGap_iff_euclidean _ _ _ _).1 ⟨hΩ, heig, hgap⟩
  set Ω' : EuclideanSpace ℂ (Reg (Qudits q) Λ) := WithLp.toLp 2 Ω
  have heig' : toEuclideanLin (∑ X, h X) Ω' = (E₀ : ℂ) • Ω' := by
    rw [← hH, ← coe_toEuclideanCLM_eq_toEuclideanLin]; exact heu
  have hgap' : ((∑ X, h X) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω') (star (WithLp.ofLp Ω')))).PosSemidef := by
    rw [← hH]; exact hpsd
  -- the contours
  set D : ℕ := R + 1 with hDdef
  set m : ℕ := (Cpad - 1) * r / D
  set d : ℕ → ℕ := fun j ↦ r + (j + 1) * D
  set c : ℕ → ℝ := fun j ↦ 2 * r + (j + 1) * D
  set X : Finset (ℤ × ℤ) := A ∩ Q₀
  have hXU : X ⊆ Λ := Finset.inter_subset_left.trans hA
  set T : ℕ → Finset (ℤ × ℤ) := fun j ↦
    if j < m then (A ∩ ambientDilation Q₀ (d j)) \ X else Λ \ X
  have hTU : ∀ j, T j ⊆ Λ := fun j ↦ by
    simp only [T]; split_ifs
    · exact Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA)
    · exact Finset.sdiff_subset
  set Tbuf : Finset (ℤ × ℤ) := (A ∩ ambientDilation Q₀ (Cpad * r)) \ X
  have hTbufU : Tbuf ⊆ Λ := Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA)
  have hD : 0 < D := Nat.succ_pos R
  have hm1 : 1 ≤ m := by
    refine (Nat.le_div_iff_mul_le hD).mpr ?_
    have : D ≤ Cpad - 1 := by omega
    nlinarith
  have hmD : m * D ≤ (Cpad - 1) * r := Nat.div_mul_le_self _ _
  have hdle : ∀ j < m, d j ≤ Cpad * r := by
    intro j hj
    have : (j + 1) * D ≤ m * D := Nat.mul_le_mul_right _ hj
    have : (Cpad - 1) * r + r = Cpad * r := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    simp only [d]; omega
  have hc : ∀ j, (d j : ℝ) + r = c j := fun j ↦ by simp only [d, c]; push_cast; ring
  have hc1 : ∀ j, (1 : ℝ) ≤ c j := fun j ↦ by
    simp only [c]
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ (j + 1) * D := by positivity
    linarith
  have hcpos : ∀ j, 0 < c j := fun j ↦ lt_of_lt_of_le one_pos (hc1 j)
  have hXd : ∀ j, X ⊆ A ∩ ambientDilation Q₀ (d j) := fun j ↦
    Finset.inter_subset_inter le_rfl (subset_ambientDilation Q₀ (d j))
  have hXT : ∀ j < m, X ∪ T j = A ∩ ambientDilation Q₀ (d j) := fun j hj ↦ by
    simp only [T, hj, ↓reduceIte]
    exact Finset.union_sdiff_of_subset (hXd j)
  have hXT' : ∀ j, m ≤ j → X ∪ T j = Λ := fun j hj ↦ by
    simp only [T, not_lt.mpr hj, ↓reduceIte]
    exact Finset.union_sdiff_of_subset hXU
  -- the harmonic weights
  set Z : ℝ := ∑ i ∈ Finset.range m, 1 / c i
  set a : ℕ → ℝ := harmonicWeight (Finset.range m) c
  have hrange : (Finset.range m).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hZ : Zmin ≤ Z := by
    have hlow := log_div_le_sum_inv_contour_of_le (r := r) (D := D) (P := Cpad)
      (by exact_mod_cast hr) (by exact_mod_cast hD) (by exact_mod_cast (by omega : 1 ≤ Cpad))
      (m := m) (by
        have h1 := Nat.lt_mul_div_succ ((Cpad - 1) * r) hD
        have h3 : (((Cpad - 1) * r : ℕ) : ℝ) ≤ D * (m + 1) := by
          exact_mod_cast h1.le
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one] at h3
        linarith)
    have hsum : ∑ j ∈ Finset.Icc 1 m, 1 / (2 * (r : ℝ) + j * D) = Z := by
      rw [← sum_range_succ_eq_sum_Icc (fun j : ℕ ↦ 1 / (2 * (r : ℝ) + j * D))]
      simp only [Z, c]; push_cast; rfl
    rw [hsum] at hlow
    refine le_trans ?_ hlow
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    rw [le_div_iff₀ hDpos]
    have := Real.log_le_log (by positivity) hCZ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at this
    rw [Real.log_div (by positivity) (by positivity)]
    linarith
  have hZpos : 0 < Z := by linarith
  have ha_eq : ∀ j, a j = 2 / (Z * c j) := fun j ↦ rfl
  have hZ4' : 4 ≤ Z := hZ4.trans hZ
  have ha0 : ∀ j, 0 < a j := fun j ↦ by
    rw [ha_eq]; exact div_pos two_pos (mul_pos hZpos (hcpos j))
  have ha2 : ∀ j, a j ≤ 1 / 2 := fun j ↦ by
    rw [ha_eq]; exact harmonic_weight_le_half hZ4' (hc1 j)
  have hmass : ∑ j ∈ Finset.range m, a j = 2 :=
    sum_harmonicWeight hrange fun j _ ↦ hcpos j
  have hcost : ∑ j ∈ Finset.range m, c j * a j ^ 2 = 4 / Z :=
    sum_mul_harmonicWeight_sq hrange fun j _ ↦ hcpos j
  have hcost1 : 4 / Z ≤ 1 := by rw [div_le_one hZpos]; linarith
  -- crossing budgets
  have hcross : ∀ j < m, ((crossingTerms S (X ∪ T j)).card : ℝ) ≤ K * c j := fun j hj ↦ by
    rw [hXT j hj]
    have hdR : R ≤ d j := by
      have : D ≤ (j + 1) * D := Nat.le_mul_of_pos_left D (by omega)
      simp only [d]; omega
    have hQ : ambientDilation Q₀ (d j) ⊆ Q :=
      (ambientDilation_mono Q₀ (hdle j hj)).trans hpad
    have := hQ₀.card_crossingTerms_le_of_isSafe hsafe hRD₀ hdR hQ
    have h' : ((crossingTerms S (A ∩ ambientDilation Q₀ (d j))).card : ℝ) ≤
        K * ((boxSize Q₀ : ℝ) + d j) := by
      simp only [K, bufferCrossConst]; exact_mod_cast this
    refine h'.trans (mul_le_mul_of_nonneg_left ?_ hK)
    have : (boxSize Q₀ : ℝ) ≤ r := by exact_mod_cast hQ₀r
    linarith [hc j]
  have hB : ∀ j < m, cutLogBudget (crossingTerms S (X ∪ T j))
      (fun i ↦ Fintype.card (Reg (Qudits q) (S i))) ≤ K' * c j := fun j hj ↦ by
    refine (cutLogBudget_le_card hq _).trans ?_
    have := mul_le_mul_of_nonneg_right (hcross j hj)
      (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ v)))
    have hKL := mul_nonneg hK (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ v)))
    simp only [K', bufferBudgetConst]
    nlinarith [hc1 j]
  -- the hypotheses of the finite-dimensional discount
  have hT : ∀ i j, i ≤ j → T i ⊆ T j := by
    intro i j hij
    by_cases hj : j < m
    · have hi : i < m := lt_of_le_of_lt hij hj
      simp only [T, hi, hj, ↓reduceIte]
      exact Finset.sdiff_subset_sdiff (Finset.inter_subset_inter le_rfl
        (ambientDilation_mono Q₀ (Nat.add_le_add_left (Nat.mul_le_mul_right _
          (Nat.succ_le_succ hij)) r))) le_rfl
    · simp only [T, hj, ↓reduceIte]
      split_ifs
      · exact Finset.sdiff_subset_sdiff (Finset.inter_subset_left.trans hA) le_rfl
      · exact le_rfl
  have hdisj : ∀ j, Disjoint X (T j) := fun j ↦ by
    simp only [T]; split_ifs <;> exact Finset.disjoint_sdiff
  have hsingle : ∀ i j j', ((∃ v ∈ S i, v ∈ X ∪ T j) ∧ ∃ v ∈ S i, v ∉ X ∪ T j) →
      ((∃ v ∈ S i, v ∈ X ∪ T j') ∧ ∃ v ∈ S i, v ∉ X ∪ T j') → j = j' := by
    refine eq_of_splits_of_isSafe hsafe hRD₀ (m := m) (d := d) (fun k k' hkk _ ↦ ?_)
      (fun k hk ↦ (ambientDilation_mono Q₀ (hdle k hk)).trans hpad) hXT
      (fun k hk ↦ (hXT' k hk).ge)
    have : (k + 1) * D + D ≤ (k' + 1) * D := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    simp only [d]; omega
  have hE : ∑ j ∈ Finset.range m, 4 * a j ^ 2 *
      ∑ i ∈ crossingTerms S (X ∪ T j), Fintype.card (Reg (Qudits q) (S i)) ^ 2 * J ≤
        Δ / 2 := by
    have hqJ : 0 ≤ (q : ℝ) ^ (2 * v) * J := by positivity
    have hterm : ∀ j ∈ Finset.range m, 4 * a j ^ 2 *
        ∑ i ∈ crossingTerms S (X ∪ T j), (Fintype.card (Reg (Qudits q) (S i)) : ℝ) ^ 2 * J ≤
        4 * K * ((q : ℝ) ^ (2 * v) * J) * (c j * a j ^ 2) := by
      intro j hj
      have hj := Finset.mem_range.mp hj
      have hsum : ∑ i ∈ crossingTerms S (X ∪ T j),
          (Fintype.card (Reg (Qudits q) (S i)) : ℝ) ^ 2 * J ≤
          (crossingTerms S (X ∪ T j)).card * ((q : ℝ) ^ (2 * v) * J) := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
        have h2 : (Fintype.card (Reg (Qudits q) (S i)) : ℝ) ≤ (q : ℝ) ^ v := by
          exact_mod_cast card_reg_le_of_mem_supports i.2
        have h0 : (0 : ℝ) ≤ Fintype.card (Reg (Qudits q) (S i)) := by positivity
        calc (Fintype.card (Reg (Qudits q) (S i)) : ℝ) ^ 2 * J ≤
            ((q : ℝ) ^ v) ^ 2 * J := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 2) hJ
          _ = (q : ℝ) ^ (2 * v) * J := by rw [← pow_mul, mul_comm v 2]
      calc 4 * a j ^ 2 * ∑ i ∈ crossingTerms S (X ∪ T j),
            (Fintype.card (Reg (Qudits q) (S i)) : ℝ) ^ 2 * J
          ≤ 4 * a j ^ 2 * ((crossingTerms S (X ∪ T j)).card *
              ((q : ℝ) ^ (2 * v) * J)) := by gcongr
        _ ≤ 4 * a j ^ 2 * (K * c j * ((q : ℝ) ^ (2 * v) * J)) := by
            gcongr; exact hcross j hj
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, hcost]
    have hnum : 0 ≤ 4 * K * ((q : ℝ) ^ (2 * v) * J) := by positivity
    have h1 : 32 * K * (q : ℝ) ^ (2 * v) * J ≤ Zmin * Δ := (div_le_iff₀ hΔ).mp hZE
    rw [mul_div_assoc', div_le_div_iff₀ hZpos two_pos]
    nlinarith
  have hu : ∀ j < m, a j / (1 - a j) ≤ tailRadius (J / Δ)
      (cutLogBudget (crossingTerms S (X ∪ T j))
        fun i ↦ Fintype.card (Reg (Qudits q) (S i))) := fun j hj ↦ by
    rw [ha_eq]
    exact (harmonic_weight_ratio_le hZ4' (hc1 j)).trans
      (le_tailRadius_of_le (hZT.trans hZ) hZpos (hc1 j) hϑ
        (one_le_cutLogBudget _ _) (hB j hj))
  have hTbuf : ∀ j < m, T j ⊆ Tbuf := fun j hj ↦ by
    simp only [T, hj, ↓reduceIte, Tbuf]
    exact Finset.sdiff_subset_sdiff
      (Finset.inter_subset_inter le_rfl (ambientDilation_mono Q₀ (hdle j hj))) le_rfl
  -- the finite-dimensional discount
  have key := two_mul_condEntropy_le hXU T hTU hT hdisj a ha0 ha2 hn h S hSU hsupp
    (fun X ↦ hΦ.isHermitian_extendId X) hJ (fun X ↦ hΦ.norm_extendId_le X) hsingle hΔ heig'
    hgap' (by linarith) hE hu hmass hTbufU Finset.disjoint_sdiff hTbuf
  -- the error terms
  have herr : ∑ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
      cutLogBudget (crossingTerms S (X ∪ T j)) (fun i ↦ Fintype.card (Reg (Qudits q) (S i))) *
        a j ^ 2 ≤ 1024 * Real.exp 1 * (J / Δ) * K' := by
    have h0 : 0 ≤ 1024 * Real.exp 1 * (J / Δ) := by positivity
    have hterm : ∀ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
        cutLogBudget (crossingTerms S (X ∪ T j))
          (fun i ↦ Fintype.card (Reg (Qudits q) (S i))) * a j ^ 2 ≤
        1024 * Real.exp 1 * (J / Δ) * K' * (c j * a j ^ 2) := by
      intro j hj
      have := hB j (Finset.mem_range.mp hj)
      calc _ = 1024 * Real.exp 1 * (J / Δ) * (cutLogBudget (crossingTerms S (X ∪ T j))
              (fun i ↦ Fintype.card (Reg (Qudits q) (S i))) * a j ^ 2) := by ring
        _ ≤ 1024 * Real.exp 1 * (J / Δ) * (K' * c j * a j ^ 2) := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, hcost]
    have h0' : 0 ≤ 1024 * Real.exp 1 * (J / Δ) * K' := by positivity
    calc 1024 * Real.exp 1 * (J / Δ) * K' * (4 / Z) ≤ 1024 * Real.exp 1 * (J / Δ) * K' * 1 :=
          mul_le_mul_of_nonneg_left hcost1 h0'
      _ = _ := mul_one _
  have hmr : (m : ℝ) ≤ Cpad * r := by
    have : m * D ≤ Cpad * r := hmD.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    have : m ≤ Cpad * r := le_trans (Nat.le_mul_of_pos_right m hD) this
    exact_mod_cast this
  have hlog : -((m : ℝ) * Real.log (1 - Δ / 2 / Δ)) ≤ Cpad * r := by
    have h12 : 1 - Δ / 2 / Δ = (2 : ℝ)⁻¹ := by field_simp; norm_num
    rw [h12, Real.log_inv, mul_neg, neg_neg]
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  -- conclusion
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hE1 : 0 ≤ 1024 * Real.exp 1 * (J / Δ) * K' := by positivity
  have hE1r : 1024 * Real.exp 1 * (J / Δ) * K' ≤ 1024 * Real.exp 1 * (J / Δ) * K' * r :=
    le_mul_of_one_le_right hE1 hr1
  have key' : 2 * ((pureState Ω hΩ).regionEntropy (Finset.union_subset hXU hTbufU) -
      (pureState Ω hΩ).regionEntropy hTbufU) ≤ (pureState Ω hΩ).regionEntropy hXU +
      ∑ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
        cutLogBudget (crossingTerms S (X ∪ T j)) (fun i ↦ Fintype.card (Reg (Qudits q) (S i))) *
          a j ^ 2 - m * Real.log (1 - Δ / 2 / Δ) := key
  rw [sub_eq_add_neg] at key'
  have := add_le_add herr hlog
  linarith

/-! ## Transfer from `ℂ` -/

section Transfer

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Embedding a unit vector into `ℂ` preserves every region entropy of its pure state. -/
theorem regionEntropy_pureState_toComplex {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U Y : Finset σ} (Ω : Reg loc U → 𝕜)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hY : Y ⊆ U) :
    (pureState (fun x ↦ toComplex 𝕜 (Ω x)) (star_dotProduct_comp_toComplex_eq_one hΩ)).regionEntropy
      hY = (pureState Ω hΩ).regionEntropy hY := by
  rw [← pureState_toComplex]
  exact SubState.regionEntropy_toComplex _ hY

variable {q R : ℕ} {J Δ : ℝ}

/-- Lemma 3.2 over `ℂ` implies Lemma 3.2 over any `RCLike` field, with the same constants. -/
theorem bufferDiscount_of_complex (h : BufferDiscount ℂ q R J Δ) : BufferDiscount 𝕜 q R J Δ := by
  obtain ⟨Cpad, hCpad, Cbuf, H⟩ := h
  refine ⟨Cpad, hCpad, Cbuf,
    fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ heig hgap A hA Q hQ hsafe r hr Q₀ hQ₀ hQ₀r hpad ↦ ?_⟩
  have hΦC : IsAdmissible Λ R J fun X ↦ (Φ X).map (toComplex 𝕜) :=
    (isAdmissible_map_toComplex_iff Λ R J Φ).2 hΦ
  have heigC : hamiltonian Λ (fun X ↦ (Φ X).map (toComplex 𝕜)) *ᵥ
      (fun x ↦ toComplex 𝕜 (Ω x)) = (E₀ : ℂ) • fun x ↦ toComplex 𝕜 (Ω x) := by
    have h1 := (mulVec_map_toComplex_eq_smul_iff (hamiltonian Λ Φ) Ω (E₀ : 𝕜)).2 heig
    rw [toComplex_ofReal] at h1
    rw [hamiltonian_map_toComplex]
    exact h1
  have hgapC : HasGlobalGap (hamiltonian Λ fun X ↦ (Φ X).map (toComplex 𝕜))
      (fun x ↦ toComplex 𝕜 (Ω x)) E₀ Δ := by
    rw [hamiltonian_map_toComplex, hasGlobalGap_map_toComplex_iff]
    exact hgap
  have key := H D₀ hD₀ Λ _ hΦC _ (star_dotProduct_comp_toComplex_eq_one hΩ) E₀ heigC hgapC A hA
    Q hQ hsafe r hr Q₀ hQ₀ hQ₀r hpad
  rwa [regionEntropy_pureState_toComplex, regionEntropy_pureState_toComplex,
    regionEntropy_pureState_toComplex] at key

end Transfer

/-! ## Lemma 3.2 -/

/-- Lemma 3.2 over `ℂ`. -/
theorem bufferDiscount_complex (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    BufferDiscount ℂ q R J Δ := by
  set Zmin : ℝ := max 4 (max
    (32 * bufferCrossConst R * (q : ℝ) ^ (2 * (2 * R + 1) ^ 2) * J / Δ)
    (128 * Real.sqrt ((1 + J / Δ) * bufferBudgetConst q R)))
  set Cpad : ℕ := ⌈(2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin)⌉₊ + R + 3
    with hCpad
  have hCZ : (2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin) ≤ Cpad + 1 := by
    have := Nat.le_ceil ((2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin))
    have h0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    rw [hCpad]
    push_cast at this ⊢
    linarith
  have hCR : R + 2 < Cpad := by rw [hCpad]; omega
  refine ⟨Cpad, by omega, (1024 * Real.exp 1 * (J / Δ) * bufferBudgetConst q R + Cpad) / 2,
    fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ heig hgap A hA Q _ hsafe r hr Q₀ hQ₀ hQ₀r hpad ↦ ?_⟩
  have hRD₀ : (R : ℝ) < D₀ := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  exact condEntropy_le_initialBuffer_of_constants hq hJ.le hΔ (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    hCR hCZ hRD₀ hΦ hΩ heig hgap hA hsafe hr hQ₀ hQ₀r hpad

/-- **Lemma 3.2** [OAI265, §3.2, eq. (3.9)]: for `q ≥ 1`, `J > 0` and `Δ > 0` there are an
integer `C_pad ≥ 1` and a constant `C_buf` with `S(X | T) ≤ S(X)/2 + C_buf r` for every
buffered rectangle of every safe rectangle. -/
theorem buffer_discount {𝕜 : Type*} [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) : BufferDiscount 𝕜 q R J Δ :=
  bufferDiscount_of_complex (bufferDiscount_complex q R J Δ hq hJ hΔ)

end OpenAI
