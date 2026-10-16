import OpenAI.BoxEntropy
import OpenAI.RegionEntropy
import OpenAI.Geometry.TemplateMixedSquares

/-!
# Template entropies from the safe-box entropy

The entropy half of Lemma 9.4 [OAI265, §9.3, eq. (9.12)]: if `F_box(r) ≤ C_e r^{1+e}` at every
scale, a template `T` separated from the cut has core entropy `S_Ω(A ∩ T) ≤ C'_e n s₀^e` and
shell entropies `S_Ω(A ∩ (T_j \ T)) ≤ C'_e n L^e` for `j ≤ L ≤ s₀`.  Each set is partitioned
into maximal contained dyadic squares, capped at a scale comparable to `s₀` resp. `j`.  Below
the cap the parent of a square is mixed, so there are `O(n / u)` squares of side `u`; every
square lies in `T_j` with side at most `2 s₀`, hence is safe, and subadditivity of entropy with
`F_box(u) ≤ C_e u^{1+e}` gives a geometric sum `C n ∑_{u ≤ L dyadic} u^e ≤ C' n L^e`.

## Main statements

* `OpenAI.IsSeparatedFromCut.isSafe`: sets near a separated template are safe.
* `OpenAI.regionEntropy_inter_le_sum_cappedDyadicPartition`: subadditivity over a capped
  dyadic partition.
* `OpenAI.templateEntropy_le_of_boxEntropy_le`: Lemma 9.4, entropy bounds.

## Implementation notes

For the shell `T_j \ T` the cap is the least power of two `2^K > 2j`, at most `4L`, rather than
the largest power of two not exceeding `L`: a square of side `2^K` contained in `T_j` meets `T`,
so no square of the shell partition reaches the cap and the bound `|T_j \ T| ≤ C n j` of the
paper is not needed.  The squares then have side at most `2j ≤ 2 s₀`, still safe.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §9.3, Lemma 9.4 and its proof.
-/

open OpenAI.Geometry

namespace OpenAI

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder

/-- A set inside the dilation `T_j` of a template separated from the cut at `D₀ ≥ 0` is safe
whenever `D₀ size(Q) + j ≤ 4 D₀ s₀`. -/
theorem IsSeparatedFromCut.isSafe {D₀ : ℝ} {s₀ : ℕ} {Λ A T Q : Finset (ℤ × ℤ)}
    (hsep : IsSeparatedFromCut D₀ s₀ Λ A T) (hD₀ : 0 ≤ D₀) {j : ℕ}
    (hQ : Q ⊆ ambientDilation T j) (h : D₀ * boxSize Q + j ≤ 4 * D₀ * s₀) :
    IsSafe D₀ Λ A Q := by
  refine (isSafe_iff hD₀).2 fun x hx z hz => ?_
  obtain ⟨t, ht, h₁, h₂⟩ := mem_ambientDilation.1 (hQ hx)
  have hlt := (lt_ambientEDist_iff ENNReal.ofReal_lt_top).1 hsep t ht z hz
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff'] at hlt
  have hd : dist t x ≤ j := dist_le_natCast_iff.2 ⟨by rwa [abs_sub_comm], by rwa [abs_sub_comm]⟩
  linarith [hlt.1, dist_triangle t x z]

/-- **Subadditivity over a capped dyadic partition**: `S(A ∩ S) ≤ ∑_Q S(A ∩ Q)` over the
squares `Q` of the capped maximal dyadic partition of `S`. -/
theorem regionEntropy_inter_le_sum_cappedDyadicPartition {𝕜 : Type*} [RCLike 𝕜]
    {loc : ℤ × ℤ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
    {U : Finset (ℤ × ℤ)} (ρ : MState (Reg loc U) 𝕜) {A : Finset (ℤ × ℤ)} (hA : A ⊆ U)
    (S : Finset (ℤ × ℤ)) (K : ℕ) :
    ρ.regionEntropy (Finset.inter_subset_left.trans hA : A ∩ S ⊆ U) ≤
      ∑ c ∈ cappedDyadicPartition S K,
        ρ.regionEntropy
          (Finset.inter_subset_left.trans hA : A ∩ latticeDyadicCell c.1 c.2 ⊆ U) := by
  have h := ρ.regionEntropy_union_biUnion_le (Finset.empty_subset U) (cappedDyadicPartition S K)
    (X := fun c => A ∩ latticeDyadicCell c.1 c.2) (fun _ => Finset.inter_subset_left.trans hA)
    (fun _ _ => Finset.disjoint_empty_left _)
    ((pairwiseDisjoint_cappedDyadicPartition S K).mono fun _ => Finset.inter_subset_right)
  rw [MState.regionEntropy_empty, zero_add] at h
  refine le_of_eq_of_le (ρ.regionEntropy_congr ?_ _ _) h
  rw [Finset.empty_union, ← Finset.inter_biUnion, biUnion_cappedDyadicPartition]

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}

/-- **Lemma 9.4, entropy bounds** [OAI265, §9.3, eq. (9.12)].  There is a universal template
constant `C_tpl₀` such that, if `F_box(r) ≤ C_e r^{1+e}` for every integer `r ≥ 1`, with
`0 < e < 1`, then some `C'_e` gives, for every `C_tpl ≥ C_tpl₀`, every `D₀ > 2R + 10`, every
admissible Hamiltonian with gapped ground vector `Ω`, every cut `A ⊆ Λ` and every template `T`
with parameters `(n, s₀)` separated from `A`: `S_Ω(A ∩ T) ≤ C'_e n s₀^e`, and
`S_Ω(A ∩ (T_j \ T)) ≤ C'_e n L^e` whenever `1 ≤ L ≤ s₀` and `j ≤ L`. -/
theorem templateEntropy_le_of_boxEntropy_le :
    ∃ Ctpl₀ : ℝ, ∀ Ce e : ℝ, 0 < e → e < 1 →
      (∀ r : ℕ, 1 ≤ r → boxEntropy 𝕜 q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) →
    ∃ C' : ℝ, ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s₀ : ℕ),
      IsTemplate Ctpl n s₀ T → IsSeparatedFromCut D₀ s₀ Λ A T →
      (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ) ≤
          C' * n * (s₀ : ℝ) ^ e ∧
      ∀ L j : ℕ, 1 ≤ L → L ≤ s₀ → j ≤ L →
        (pureState Ω hΩ).regionEntropy
            (Finset.inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
          C' * n * (L : ℝ) ^ e := by
  classical
  refine ⟨1, fun Ce e he he₁ hF => ?_⟩
  have hCe : 0 ≤ Ce := by
    have := (boxEntropy_nonneg (𝕜 := 𝕜) (q := q) (R := R) (J := J) (Δ := Δ) 1).trans
      (hF 1 le_rfl)
    simpa using this
  have hγ : 0 < (2 : ℝ) ^ e - 1 := sub_pos.2 (Real.one_lt_rpow (by norm_num) he)
  refine ⟨Ce * (2 + 160 / ((2 : ℝ) ^ e - 1)) + Ce * (2816 / ((2 : ℝ) ^ e - 1)),
    fun Ctpl hCtpl D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hT hsep => ?_⟩
  have hD₀' : 1 ≤ D₀ := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  have hs₀ : 1 ≤ s₀ := hT.2.1
  -- the entropy of a safe capped partition
  have key : ∀ (S : Finset (ℤ × ℤ)) (K : ℕ),
      (∀ c ∈ cappedDyadicPartition S K, IsSafe D₀ Λ A (latticeDyadicCell c.1 c.2)) →
      (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ S ⊆ Λ) ≤
        Ce * ∑ c ∈ cappedDyadicPartition S K, ((2 : ℝ) ^ c.1) ^ (1 + e) := by
    intro S K hsafe
    refine (regionEntropy_inter_le_sum_cappedDyadicPartition _ hA S K).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    refine (regionEntropy_le_boxEntropy hD₀ hΦ hΩ hE hgap hA (isIntRect_latticeDyadicCell c.1 c.2)
      (hsafe c hc) (boxSize_latticeDyadicCell c.1 c.2).le).trans ?_
    have := hF (2 ^ c.1) Nat.one_le_two_pow
    simpa using this
  have hmem : ∀ {S : Finset (ℤ × ℤ)} {K : ℕ} {c : ℕ × (ℤ × ℤ)},
      c ∈ cappedDyadicPartition S K → c.1 ≤ K ∧ latticeDyadicCell c.1 c.2 ⊆ S := by
    intro S K c hc
    obtain ⟨h₁, h₂, -⟩ := (mem_cappedDyadicPartition _ _ _ _).1 hc
    exact ⟨h₁, h₂⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · -- the core `A ∩ T`, capped at the largest power of two not exceeding `s₀`
    set K := Nat.log 2 s₀
    have hK₁ : 2 ^ K ≤ s₀ := Nat.pow_log_le_self 2 (by omega)
    have hK₂ : s₀ < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) s₀
    have hcapN : 2 ^ K * ((cappedDyadicPartition T K).filter (fun c ↦ c.1 = K)).card ≤ 2 * n := by
      have h : 2 ^ K * (2 ^ K * ((cappedDyadicPartition T K).filter (fun c ↦ c.1 = K)).card) ≤
          2 ^ K * (2 * n) := by
        calc _ = 4 ^ K * ((cappedDyadicPartition T K).filter (fun c ↦ c.1 = K)).card := by
              rw [← mul_assoc, ← mul_pow]
              norm_num
          _ ≤ T.card := card_cappedDyadicPartition_at_cap_le T K
          _ ≤ n * (s₀ + 1) := hT.card_le hCtpl
          _ ≤ n * 2 ^ (K + 1) := Nat.mul_le_mul_left _ hK₂
          _ = 2 ^ K * (2 * n) := by ring
      exact Nat.le_of_mul_le_mul_left h (by positivity)
    have hsmallN : ∀ k < K,
        2 ^ k * ((cappedDyadicPartition T K).filter (fun c ↦ c.1 = k)).card ≤ 160 * n := by
      intro k hk
      have h₁ := card_cappedDyadicPartition_below_cap_le T K k hk
      have h₂ := hT.card_mixedDyadicIndices_ambientDilation_le hCtpl (Nat.zero_le s₀)
        (k := k + 1) (a := 1) (by
          have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show k + 1 ≤ K by omega)
          omega)
      rw [ambientDilation_zero] at h₂
      calc _ ≤ 2 ^ k * (4 * (mixedDyadicIndices T (k + 1)).card) := Nat.mul_le_mul_left _ h₁
        _ = 2 * (2 ^ (k + 1) * (mixedDyadicIndices T (k + 1)).card) := by ring
        _ ≤ 2 * (16 * (3 + 2 * 1) * n) := Nat.mul_le_mul_left _ h₂
        _ = 160 * n := by ring
    have hsum := sum_rpow_cappedDyadicPartition_le T K (L := (s₀ : ℝ)) (A := 2 * n)
      (B := 160 * n) he (by positivity) (by exact_mod_cast hK₁) (by exact_mod_cast hcapN)
      (fun k hk => by exact_mod_cast hsmallN k hk)
    have hent := key T K fun c hc => by
      obtain ⟨h₁, h₂⟩ := hmem hc
      refine hsep.isSafe (by linarith) (j := 0) (by rwa [ambientDilation_zero]) ?_
      rw [boxSize_latticeDyadicCell]
      have : ((2 ^ c.1 : ℕ) : ℝ) ≤ s₀ := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) h₁).trans hK₁
      have hs : (1 : ℝ) ≤ s₀ := by exact_mod_cast hs₀
      push_cast at this ⊢
      nlinarith
    have hpow : 0 ≤ (s₀ : ℝ) ^ e := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc _ ≤ _ := hent
      _ ≤ Ce * ((2 * n + 160 * n / ((2 : ℝ) ^ e - 1)) * (s₀ : ℝ) ^ e) :=
          mul_le_mul_of_nonneg_left hsum hCe
      _ = Ce * (2 + 160 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e := by ring
      _ ≤ _ := by
          have : 0 ≤ Ce * (2816 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e := by positivity
          nlinarith
  · -- the shells `A ∩ (T_j \ T)`, capped at the least power of two above `2j`
    intro L j hL hLs hj
    set S := ambientDilation T j \ T
    set K := Nat.log 2 (2 * j) + 1
    have hK₁ : 2 * j < 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) (2 * j)
    have hK₂ : 2 ^ K ≤ 4 * L := by
      rcases Nat.eq_zero_or_pos j with rfl | hj₀
      · simp [K]; omega
      · have := Nat.pow_log_le_self 2 (show 2 * j ≠ 0 by omega)
        rw [pow_succ]
        omega
    have hcap0 : (cappedDyadicPartition S K).filter (fun c ↦ c.1 = K) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun c hc hcK => ?_
      obtain ⟨-, hsub⟩ := hmem hc
      rw [hcK] at hsub
      have hu : (2 * j : ℤ) < 2 ^ K := by exact_mod_cast hK₁
      have hx : (c.2.1 * 2 ^ K + j, c.2.2 * 2 ^ K + j) ∈ latticeDyadicCell K c.2 :=
        (mem_latticeDyadicCell_iff_bounds _ _ _).2 ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by dsimp only; omega⟩
      obtain ⟨t, ht, h₁, h₂⟩ := mem_ambientDilation.1 (Finset.mem_sdiff.1 (hsub hx)).1
      rw [abs_le] at h₁ h₂
      have htc : t ∈ latticeDyadicCell K c.2 :=
        (mem_latticeDyadicCell_iff_bounds _ _ _).2 ⟨by dsimp only at h₁; omega,
          by dsimp only at h₁; omega, by dsimp only at h₂; omega, by dsimp only at h₂; omega⟩
      exact (Finset.mem_sdiff.1 (hsub htc)).2 ht
    have hsmallN : ∀ k < K,
        2 ^ k * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card ≤ 704 * n := by
      intro k hk
      have hk' : 2 ^ (k + 1) ≤ 4 * (s₀ + 1) := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show k + 1 ≤ K by omega)
        omega
      have h₁ := card_cappedDyadicPartition_below_cap_le S K k hk
      have h₂ := card_mixedDyadicIndices_sdiff_le (ambientDilation T j) T (k + 1)
      have h₃ := hT.card_mixedDyadicIndices_ambientDilation_le hCtpl (j := j) (by omega)
        (k := k + 1) (a := 4) hk'
      have h₄ := hT.card_mixedDyadicIndices_ambientDilation_le hCtpl (Nat.zero_le s₀)
        (k := k + 1) (a := 4) hk'
      rw [ambientDilation_zero] at h₄
      calc _ ≤ 2 ^ k * (4 * (mixedDyadicIndices S (k + 1)).card) := Nat.mul_le_mul_left _ h₁
        _ = 2 * (2 ^ (k + 1) * (mixedDyadicIndices S (k + 1)).card) := by ring
        _ ≤ 2 * (2 ^ (k + 1) * (mixedDyadicIndices (ambientDilation T j) (k + 1)).card +
              2 ^ (k + 1) * (mixedDyadicIndices T (k + 1)).card) := by
            rw [← mul_add]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h₂)
        _ ≤ 2 * (16 * (3 + 2 * 4) * n + 16 * (3 + 2 * 4) * n) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add h₃ h₄)
        _ = 704 * n := by ring
    have hsum := sum_rpow_cappedDyadicPartition_le S K (L := 4 * (L : ℝ)) (A := 0)
      (B := 704 * n) he (by positivity) (by exact_mod_cast hK₂) (by simp [hcap0])
      (fun k hk => by exact_mod_cast hsmallN k hk)
    have hent := key S K fun c hc => by
      obtain ⟨h₁, h₂⟩ := hmem hc
      have hcK : c.1 ≠ K := fun h => by
        have : c ∈ (cappedDyadicPartition S K).filter (fun c ↦ c.1 = K) :=
          Finset.mem_filter.2 ⟨hc, h⟩
        rw [hcap0] at this
        simp at this
      refine hsep.isSafe (by linarith) (j := j) (h₂.trans Finset.sdiff_subset) ?_
      rw [boxSize_latticeDyadicCell]
      have h2k : 2 ^ c.1 * 2 ≤ 4 * L := by
        rw [← pow_succ]
        exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hK₂
      have : ((2 ^ c.1 : ℕ) : ℝ) ≤ 2 * s₀ := by exact_mod_cast (by omega : 2 ^ c.1 ≤ 2 * s₀)
      have hj' : (j : ℝ) ≤ s₀ := by exact_mod_cast hj.trans hLs
      have hs : (1 : ℝ) ≤ s₀ := by exact_mod_cast hs₀
      push_cast at this ⊢
      nlinarith
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have h4 : (4 * (L : ℝ)) ^ e ≤ 4 * (L : ℝ) ^ e := by
      rw [Real.mul_rpow (by norm_num) hL0]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0 _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) he₁.le
    have hpow : 0 ≤ (L : ℝ) ^ e := Real.rpow_nonneg hL0 _
    have hc : 0 ≤ Ce * (704 * n / ((2 : ℝ) ^ e - 1)) := by positivity
    calc _ ≤ _ := hent
      _ ≤ Ce * ((0 + 704 * n / ((2 : ℝ) ^ e - 1)) * (4 * (L : ℝ)) ^ e) :=
          mul_le_mul_of_nonneg_left hsum hCe
      _ = Ce * (704 * n / ((2 : ℝ) ^ e - 1)) * (4 * (L : ℝ)) ^ e := by ring
      _ ≤ Ce * (704 * n / ((2 : ℝ) ^ e - 1)) * (4 * (L : ℝ) ^ e) :=
          mul_le_mul_of_nonneg_left h4 hc
      _ = Ce * (2816 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by ring
      _ ≤ _ := by
          have : 0 ≤ Ce * (2 + 160 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by positivity
          nlinarith

end OpenAI
