import OpenAI.BoxEntropy
import OpenAI.Scan.SourceScan
import OpenAI.TemplateEntropy
import OpenAI.WeakRectangleShellSafety

/-!
# The shell entropy of a safe rectangle

A box bound `F_box(r) ≤ C_e r^{1+e}` bounds the entropy of every shell `A ∩ (Q_j \ Q)`, `j ≤ L`,
of a safe rectangle by `C size(Q) L^e` [OAI265, proof of Proposition 9.5].  The shell is
partitioned into maximal contained dyadic squares capped at the largest power of two `2^K ≤ L`.
The cap squares are disjoint inside a shell of area at most `8 L size(Q)`; below the cap the
parent of each square is mixed for `Q_j` or for `Q`, and a rectangle of size `s` has at most
`16 (s + 2u) / u` mixed squares of side `u`.  Every square is safe, so subadditivity and the box
bound give a geometric sum `C size(Q) ∑_{u ≤ L dyadic} u^e ≤ C' size(Q) L^e`.

## Main statements

* `OpenAI.IsIntRect.card_mixedDyadicIndices_ambientDilation_le`: the mixed-square count of a
  dilated rectangle.
* `OpenAI.Scan.isSafe_shell_regionEntropy_le`: the shell entropy bound.
-/

open OpenAI.Geometry

namespace OpenAI

/-- The sites of an integer rectangle form an octagonally convex set. -/
theorem IsIntRect.isOctagonallyConvex {Q : Finset (ℤ × ℤ)} (hQ : IsIntRect Q) :
    IsOctagonallyConvex (Q : Set (ℤ × ℤ)) := by
  obtain ⟨a, b, -, rfl⟩ := hQ
  intro p hp r hr x h₁ h₂ h₃ h₄ _ _ _ _
  simp only [Finset.coe_Icc, Set.mem_Icc, Prod.le_def] at hp hr ⊢
  omega

/-- **Mixed squares of a dilated rectangle.**  At most `16 (size(Q) + 2j + 2u) / u` dyadic
squares of side `u = 2^k` meet both `Q_j` and its complement. -/
theorem IsIntRect.card_mixedDyadicIndices_ambientDilation_le {Q : Finset (ℤ × ℤ)}
    (hQ : IsIntRect Q) (j k : ℕ) :
    2 ^ k * (mixedDyadicIndices (ambientDilation Q j) k).card ≤
      16 * (boxSize Q + 2 * j + 2 * 2 ^ k) :=
  hQ.isOctagonallyConvex.card_mixedDyadicIndices_ambientDilation_le (fun x hx x' hx' => by
    have h := hQ.abs_sub_lt_boxSize hx hx'
    rw [abs_lt, abs_lt] at h
    omega) j k

end OpenAI

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- **The shell entropy of a safe rectangle** [OAI265, proof of Proposition 9.5, lines
717–726].  If `F_box(r) ≤ C_e r^{1+e}` for `r ≥ 1`, there is `C` such that for every safe
rectangle `Q` and `1 ≤ L` with `2L ≤ size(Q)`, every shell `Q_j \ Q` with `j ≤ L` has
`S_Ω(A ∩ (Q_j \ Q)) ≤ C size(Q) L^e`: its maximal dyadic squares of side `u ≤ L` number
`O(size(Q)/u)` and are safe. -/
theorem isSafe_shell_regionEntropy_le {𝕜 : Type*} [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ)
    {Ce e : ℝ} (he : 0 < e) (he₁ : e < 1)
    (hF : ∀ r : ℕ, 1 ≤ r → boxEntropy 𝕜 q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) :
    ∃ C : ℝ, ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)), IsIntRect Q → IsSafe D₀ Λ A Q →
    ∀ L j : ℕ, 1 ≤ L → 2 * L ≤ boxSize Q → j ≤ L →
      (pureState Ω hΩ).regionEntropy
          (Finset.inter_subset_left.trans hA : A ∩ (ambientDilation Q j \ Q) ⊆ Λ) ≤
        C * boxSize Q * (L : ℝ) ^ e := by
  classical
  have hCe : 0 ≤ Ce := by
    have := (boxEntropy_nonneg (𝕜 := 𝕜) (q := q) (R := R) (J := J) (Δ := Δ) 1).trans
      (hF 1 le_rfl)
    simpa using this
  refine ⟨Ce * (16 + 160 / ((2 : ℝ) ^ e - 1)),
    fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hsafe L j hL hLs hj => ?_⟩
  have hD₀' : 1 ≤ D₀ := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  set s := boxSize Q
  set S := ambientDilation Q j \ Q
  set K := Nat.log 2 L
  have hK₁ : 2 ^ K ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hK₂ : L < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  -- the cap-scale squares
  have hcapN : 2 ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card ≤ 16 * s := by
    have hS : S.card ≤ 4 * j * (s + 2 * j) := by
      have := hQ.card_ambientDilation_sdiff_le (d := j) (k := j) le_rfl
      rwa [Nat.sub_self, ambientDilation_zero] at this
    have h : 2 ^ K * (2 ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card) ≤
        2 ^ K * (16 * s) := by
      calc _ = 4 ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card := by
            rw [← _root_.mul_assoc, ← mul_pow]
            norm_num
          _ ≤ S.card := card_cappedDyadicPartition_at_cap_le S K
          _ ≤ 4 * j * (s + 2 * j) := hS
          _ ≤ 4 * L * (s + 2 * L) := by gcongr
          _ ≤ 8 * L * s := by nlinarith
          _ ≤ 8 * 2 ^ (K + 1) * s := by gcongr
          _ = 2 ^ K * (16 * s) := by ring
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  -- the squares below the cap
  have hsmallN : ∀ k < K,
      2 ^ k * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card ≤ 160 * s := by
    intro k hk
    have hk' : 2 ^ (k + 1) ≤ L :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hK₁
    have h₁ := card_cappedDyadicPartition_below_cap_le S K k hk
    have h₂ := card_mixedDyadicIndices_sdiff_le (ambientDilation Q j) Q (k + 1)
    have h₃ := hQ.card_mixedDyadicIndices_ambientDilation_le j (k + 1)
    have h₄ := hQ.card_mixedDyadicIndices_ambientDilation_le 0 (k + 1)
    rw [ambientDilation_zero] at h₄
    calc _ ≤ 2 ^ k * (4 * (mixedDyadicIndices S (k + 1)).card) := Nat.mul_le_mul_left _ h₁
      _ = 2 * (2 ^ (k + 1) * (mixedDyadicIndices S (k + 1)).card) := by ring
      _ ≤ 2 * (2 ^ (k + 1) * (mixedDyadicIndices (ambientDilation Q j) (k + 1)).card +
            2 ^ (k + 1) * (mixedDyadicIndices Q (k + 1)).card) := by
          rw [← mul_add]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h₂)
      _ ≤ 2 * (16 * (s + 2 * j + 2 * 2 ^ (k + 1)) + 16 * (s + 2 * 0 + 2 * 2 ^ (k + 1))) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add h₃ h₄)
      _ ≤ 160 * s := by omega
  have hsum := sum_rpow_cappedDyadicPartition_le S K (L := (L : ℝ)) (A := 16 * s)
    (B := 160 * s) he (by positivity) (by exact_mod_cast hK₁) (by exact_mod_cast hcapN)
    (fun k hk => by exact_mod_cast hsmallN k hk)
  -- every selected square is safe, so its entropy is at most `C_e (side)^{1+e}`
  have hent : (pureState Ω hΩ).regionEntropy
      (Finset.inter_subset_left.trans hA : A ∩ S ⊆ Λ) ≤
        Ce * ∑ c ∈ cappedDyadicPartition S K, ((2 : ℝ) ^ c.1) ^ (1 + e) := by
    refine (regionEntropy_inter_le_sum_cappedDyadicPartition _ hA S K).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hbudget : D₀ * L + L ≤ D₀ * s := by
      have : (2 * L : ℝ) ≤ s := by exact_mod_cast hLs
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    have hcs := hsafe.isSafe_cappedDyadicPartition_shell (by linarith) j L K c.1 c.2 hj hK₁
      hbudget hc
    refine (regionEntropy_le_boxEntropy hD₀ hΦ hΩ hE hgap hA (isIntRect_latticeDyadicCell c.1 c.2)
      hcs (boxSize_latticeDyadicCell c.1 c.2).le).trans ?_
    have := hF (2 ^ c.1) Nat.one_le_two_pow
    simpa using this
  have hpow : 0 ≤ (L : ℝ) ^ e := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc _ ≤ _ := hent
    _ ≤ Ce * ((16 * s + 160 * s / ((2 : ℝ) ^ e - 1)) * (L : ℝ) ^ e) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hsum) hCe
    _ = _ := by ring

end OpenAI.Scan
