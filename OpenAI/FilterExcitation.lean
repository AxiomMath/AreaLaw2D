import OpenAI.FilterChainEnergy
import OpenAI.FilterMaximizer

/-!
# Excitation energy of an optimal nested product of filters

Let `K = L_{m-1} ⋯ L_0` be a nested product of invertible filters on subregions
`D_0 ⊆ ⋯ ⊆ D_{m-1}` of a region `U`, each commuting with the marginal of a unit vector `φ` on
its region and clipped relative to it.  If `K H K⁻¹ φ = E₀ φ` for `H = ∑_i h_i`, the excitation
energy `⟨φ, H φ⟩ - E₀` is the sum over the terms of the defects
`⟨φ, h_i φ⟩ - ⟨φ, K h_i K⁻¹ φ⟩`, each bounded by `OpenAI.abs_re_inner_sub_chain_conj_le_sharp`.
For the optimal nested product of feasible filters applied to a ground vector `Ω`,
`H Ω = E₀ Ω`, the normalized output `φ = K Ω / ‖K Ω‖` satisfies `K H K⁻¹ φ = E₀ φ`, and all its
filters are stationary and clipped by `OpenAI.forall_clipped_of_max`.  This is
`(eq:initial-product-energy)` in the proof of Lemma 3.2 of [OAI265].

## Main statements

* `OpenAI.re_inner_sub_le_of_chain_sharp`, `OpenAI.re_inner_sub_le_of_chain`: the excitation
  energy of a stationary nested product.
* `OpenAI.re_inner_sub_le_of_max`: the excitation energy of the optimal nested product.

## Implementation notes

Ported from QICLean (LionSR/QICLean), `QICLean/Entropy/FilterChainEnergy.lean` at commit
`32a5a1a8` (Apache 2.0), the second part of that file; the first part is
`OpenAI.FilterChainEnergy`.  Changes: the namespace `Entropy` is `OpenAI`, and the region model
is that of `OpenAI.chainList`, with the regional state `regionState D φ` written
`Arealaw.ptrace hD (vecMulVec φ (star φ))` and `supportDim n S` written
`Fintype.card (Reg loc S)`.  The terms `h i` are supported on `S i ⊆ U`, so the statements
carry `hSU : ∀ i, S i ⊆ U`.  QICLean's `regionState_smul` is `OpenAI.ptrace_vecMulVec_star_smul`
and is not restated.  The witness configuration `σ₀` is no longer an argument: the coarse bound
obtains a configuration of each support from the unit vector.  `toEuclideanLin_conj_apply_eq`
is stated over `RCLike 𝕜`.

The excitation bounds are over `ℂ`, as are the conjugation estimates they sum and
`OpenAI.forall_clipped_of_max`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.2, proof of Lemma 3.2, eq. (initial-product-energy).
-/

namespace OpenAI

open Arealaw Matrix
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

/-- An eigenvector equation survives conjugation: if `H Ω = E₀ Ω` and `K⁻¹ K = 1`, then
`K H K⁻¹` has eigenvalue `E₀` on every multiple of `K Ω`. -/
theorem toEuclideanLin_conj_apply_eq {𝕜 : Type*} [RCLike 𝕜] {k : Type*} [Fintype k]
    [DecidableEq k] {H K Kinv : Matrix k k 𝕜} {Ω : EuclideanSpace 𝕜 k} {E₀ : 𝕜}
    (heig : toEuclideanLin H Ω = E₀ • Ω) (hK : Kinv * K = 1) (c : 𝕜) :
    toEuclideanLin (K * H * Kinv) (c • toEuclideanLin K Ω) =
      E₀ • (c • toEuclideanLin K Ω) := by
  have h : K * H * Kinv * K = K * H := by rw [Matrix.mul_assoc, hK, Matrix.mul_one]
  rw [map_smul, ← LinearMap.comp_apply, ← toLpLin_mul_same, h, toLpLin_mul_same,
    LinearMap.comp_apply, heig, map_smul, smul_comm]

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {m : ℕ}

/-- Commutation, spectral data and clipping relative to a marginal survive scaling the vector
by a nonzero constant. -/
theorem clipped_smul {D : Finset σ} (hD : D ⊆ U) {L : Matrix (Reg loc D) (Reg loc D) ℂ}
    {ψ : EuclideanSpace ℂ (Reg loc U)} {a : ℝ} {c : ℂ} (hc : c ≠ 0)
    (h : L * ptrace hD (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) =
        ptrace hD (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) * L ∧
      ∃ (W : Matrix (Reg loc D) (Reg loc D) ℂ) (l q : Reg loc D → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ L = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ptrace hD (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) =
          W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a / 2 * |Real.log (q i) - Real.log (q k)|) :
    L * ptrace hD (vecMulVec (WithLp.ofLp (c • ψ)) (star (WithLp.ofLp (c • ψ)))) =
        ptrace hD (vecMulVec (WithLp.ofLp (c • ψ)) (star (WithLp.ofLp (c • ψ)))) * L ∧
      ∃ (W : Matrix (Reg loc D) (Reg loc D) ℂ) (l q : Reg loc D → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ L = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ptrace hD (vecMulVec (WithLp.ofLp (c • ψ)) (star (WithLp.ofLp (c • ψ)))) =
          W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a / 2 * |Real.log (q i) - Real.log (q k)| := by
  obtain ⟨hcomm, W, l, q, hW, hl, hL, hρ, hclip⟩ := h
  have hs : 0 < ‖c‖ ^ 2 := by positivity
  rw [ptrace_vecMulVec_star_smul]
  refine ⟨by rw [Matrix.mul_smul, Matrix.smul_mul, hcomm], W, l, fun i ↦ ‖c‖ ^ 2 * q i, hW, hl,
    hL, ?_, fun i k hi hk ↦ ?_⟩
  · have hd : diagonal (fun i ↦ (((‖c‖ ^ 2 * q i : ℝ)) : ℂ)) =
        ((‖c‖ ^ 2 : ℝ) : ℂ) • diagonal (fun i ↦ (q i : ℂ)) := by
      ext i k
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik]
    rw [hρ, hd, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  · have hi' : 0 < q i := pos_of_mul_pos_right hi hs.le
    have hk' : 0 < q k := pos_of_mul_pos_right hk hs.le
    rw [Real.log_mul hs.ne' hi'.ne', Real.log_mul hs.ne' hk'.ne', add_sub_add_left_eq_sub]
    exact hclip i k hi' hk'

/-- **Excitation energy of a stationary nested product.** Let `K_j` be invertible filters on
nested subregions `D_j ⊆ U`, each commuting with the marginal of the unit vector `φ` on its
region and clipped relative to it, with weights `a_j ≤ 1`.  Let `H = ∑_i h_i` with `h_i`
Hermitian, supported on `S_i`, `‖h_i‖ ≤ c₀`, every `S_i` split by at most one region, and
suppose `K H K⁻¹ φ = E₀ φ`.  Then
`Re ⟨φ, H φ⟩ - E₀ ≤ ∑_j a_j² ∑_{i crossing D_j} d_{ij}² c₀`, `d_{ij} = dim (S_i ∩ D_j)`. -/
theorem re_inner_sub_le_of_chain_sharp (D : ℕ → Finset σ) (hDU : ∀ i : Fin m, D i ⊆ U)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (K : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) ℂ)
    (hunit : ∀ i, IsUnit (K i).det) {φ : EuclideanSpace ℂ (Reg loc U)} (hφ : ‖φ‖ = 1)
    (a : Fin m → ℝ) (ha : ∀ j, a j ≤ 1)
    (hcl : ∀ j, K j * ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) * K j ∧
      ∃ (W : Matrix (Reg loc (D j)) (Reg loc (D j)) ℂ) (l q : Reg loc (D j) → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
          W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a j / 2 * |Real.log (q i) - Real.log (q k)|)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (Reg loc U) (Reg loc U) ℂ)
    (S : ι → Finset σ) (hSU : ∀ i, S i ⊆ U) (hsupp : ∀ i, IsSupportedOn (hSU i) (h i))
    (hherm : ∀ i, (h i).IsHermitian) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m, ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ : ℝ}
    (heig : toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True) * (∑ i, h i) *
      liftProdInv (chainList D hDU K fun _ ↦ True)) φ = (E₀ : ℂ) • φ) :
    (⟪φ, toEuclideanLin (∑ i, h i) φ⟫_ℂ).re - E₀ ≤
      ∑ j : Fin m, a j ^ 2 *
        ∑ i ∈ crossingTerms S (D j), Fintype.card (Reg loc (S i ∩ D j)) ^ 2 * c₀ := by
  set P := liftProd (chainList D hDU K fun _ ↦ True)
  set Pi := liftProdInv (chainList D hDU K fun _ ↦ True)
  have hE : ⟪φ, toEuclideanLin (P * (∑ i, h i) * Pi) φ⟫_ℂ = E₀ := by
    rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hφ]
    simp
  have hsum : ∀ Y : ι → Matrix (Reg loc U) (Reg loc U) ℂ,
      ⟪φ, toEuclideanLin (∑ i, Y i) φ⟫_ℂ = ∑ i, ⟪φ, toEuclideanLin (Y i) φ⟫_ℂ := fun Y ↦ by
    rw [map_sum, LinearMap.sum_apply, inner_sum]
  have hexp : (⟪φ, toEuclideanLin (∑ i, h i) φ⟫_ℂ).re - E₀ =
      ∑ i, (⟪φ, toEuclideanLin (h i) φ⟫_ℂ - ⟪φ, toEuclideanLin (P * h i * Pi) φ⟫_ℂ).re := by
    rw [← Complex.ofReal_re E₀, ← hE, ← Complex.sub_re, Finset.mul_sum, Finset.sum_mul, hsum,
      hsum, ← Finset.sum_sub_distrib, Complex.re_sum]
  rw [hexp]
  calc ∑ i, (⟪φ, toEuclideanLin (h i) φ⟫_ℂ - ⟪φ, toEuclideanLin (P * h i * Pi) φ⟫_ℂ).re
      ≤ ∑ i, ∑ j ∈ splitIndices (S i) D m,
          a j ^ 2 * (Fintype.card (Reg loc (S i ∩ D j)) ^ 2 * c₀) :=
        Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans
          (abs_re_inner_sub_chain_conj_le_sharp D hDU hD K hunit hφ a ha hcl (hSU i) (hsupp i)
            (hherm i) (hnorm i) (hsingle i))
    _ = ∑ j : Fin m, ∑ i ∈ crossingTerms S (D j),
          a j ^ 2 * (Fintype.card (Reg loc (S i ∩ D j)) ^ 2 * c₀) := by
        refine Finset.sum_comm' fun i j ↦ ?_
        simp [splitIndices, crossingTerms]
    _ = ∑ j : Fin m, a j ^ 2 *
          ∑ i ∈ crossingTerms S (D j), Fintype.card (Reg loc (S i ∩ D j)) ^ 2 * c₀ := by
        simp only [Finset.mul_sum]

/-- **Excitation energy of a stationary nested product**, the coarse form of [OAI265]: under
the hypotheses of `OpenAI.re_inner_sub_le_of_chain_sharp` with weights `a_j ≤ 1/2`,
`Re ⟨φ, H φ⟩ - E₀ ≤ ∑_j 4 a_j² ∑_{i crossing D_j} d_i² c₀`, `d_i = dim S_i`. -/
theorem re_inner_sub_le_of_chain (D : ℕ → Finset σ) (hDU : ∀ i : Fin m, D i ⊆ U)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (K : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) ℂ)
    (hunit : ∀ i, IsUnit (K i).det) {φ : EuclideanSpace ℂ (Reg loc U)} (hφ : ‖φ‖ = 1)
    (a : Fin m → ℝ) (ha : ∀ j, a j ≤ 1 / 2)
    (hcl : ∀ j, K j * ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) * K j ∧
      ∃ (W : Matrix (Reg loc (D j)) (Reg loc (D j)) ℂ) (l q : Reg loc (D j) → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ptrace (hDU j) (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
          W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a j / 2 * |Real.log (q i) - Real.log (q k)|)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (Reg loc U) (Reg loc U) ℂ)
    (S : ι → Finset σ) (hSU : ∀ i, S i ⊆ U) (hsupp : ∀ i, IsSupportedOn (hSU i) (h i))
    (hherm : ∀ i, (h i).IsHermitian) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m, ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ : ℝ}
    (heig : toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True) * (∑ i, h i) *
      liftProdInv (chainList D hDU K fun _ ↦ True)) φ = (E₀ : ℂ) • φ) :
    (⟪φ, toEuclideanLin (∑ i, h i) φ⟫_ℂ).re - E₀ ≤
      ∑ j : Fin m, 4 * a j ^ 2 *
        ∑ i ∈ crossingTerms S (D j), Fintype.card (Reg loc (S i)) ^ 2 * c₀ := by
  refine (re_inner_sub_le_of_chain_sharp D hDU hD K hunit hφ a
    (fun j ↦ by linarith [ha j]) hcl h S hSU hsupp hherm hnorm hsingle heig).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun i _ ↦ ?_
  have hne : Nonempty (Reg loc (S i)) :=
    nonempty_reg_of_ne_zero (hSU i) (φ := φ) (by rintro rfl; simp at hφ)
  have hc₀ : 0 ≤ c₀ := (norm_nonneg (h i)).trans (hnorm i)
  have hdim : (Fintype.card (Reg loc (S i ∩ D j)) : ℝ) ^ 2 ≤
      Fintype.card (Reg loc (S i)) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left (card_reg_le_of_subset Finset.inter_subset_left) 2
  calc a j ^ 2 * (Fintype.card (Reg loc (S i ∩ D j)) ^ 2 * c₀)
      ≤ a j ^ 2 * (Fintype.card (Reg loc (S i)) ^ 2 * c₀) := by gcongr
    _ ≤ 4 * a j ^ 2 * (Fintype.card (Reg loc (S i)) ^ 2 * c₀) := by
      nlinarith [mul_nonneg (sq_nonneg (a j))
        (mul_nonneg (sq_nonneg (Fintype.card (Reg loc (S i)) : ℝ)) hc₀)]

/-- **Excitation energy of the optimal nested product.** Let feasible filters `K_j` on nested
subregions `D_j ⊆ U`, with floors `f_j > 0`, `card · f_j < 1` and weights `0 < a_j ≤ 1/2`,
maximize `‖L_{m-1} ⋯ L_0 Ω‖`, where `Ω ≠ 0` satisfies `H Ω = E₀ Ω` for `H = ∑_i h_i` with
`h_i` Hermitian, supported on `S_i`, `‖h_i‖ ≤ c₀`, and every `S_i` split by at most one region.
Then the normalized output `φ = K Ω / ‖K Ω‖` satisfies
`Re ⟨φ, H φ⟩ - E₀ ≤ ∑_j 4 a_j² ∑_{i crossing D_j} d_i² c₀`, `d_i = dim S_i`. -/
theorem re_inner_sub_le_of_max (D : ℕ → Finset σ) (hDU : ∀ i : Fin m, D i ⊆ U)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (f a : Fin m → ℝ) (hf : ∀ j, 0 < f j) (ha : ∀ j, 0 < a j) (ha2 : ∀ j, a j ≤ 1 / 2)
    (hcard : ∀ j : Fin m, Fintype.card (Reg loc (D j)) * f j < 1)
    (K : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) ℂ)
    (hK : ∀ j, IsFeasibleFilter (f j) (a j) (K j)) {Ω : EuclideanSpace ℂ (Reg loc U)}
    (hΩ : Ω ≠ 0)
    (hmax : ∀ K' : (i : Fin m) → Matrix (Reg loc (D i)) (Reg loc (D i)) ℂ,
      (∀ j, IsFeasibleFilter (f j) (a j) (K' j)) →
      ‖toEuclideanLin (liftProd (chainList D hDU K' fun _ ↦ True)) Ω‖ ≤
        ‖toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True)) Ω‖)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (Reg loc U) (Reg loc U) ℂ)
    (S : ι → Finset σ) (hSU : ∀ i, S i ⊆ U) (hsupp : ∀ i, IsSupportedOn (hSU i) (h i))
    (hherm : ∀ i, (h i).IsHermitian) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m, ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ : ℝ} (heig : toEuclideanLin (∑ i, h i) Ω = (E₀ : ℂ) • Ω) :
    (⟪((‖toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True)) Ω‖⁻¹ : ℝ) : ℂ) •
        toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True)) Ω,
      toEuclideanLin (∑ i, h i)
        (((‖toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True)) Ω‖⁻¹ : ℝ) : ℂ) •
          toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True)) Ω)⟫_ℂ).re - E₀ ≤
      ∑ j : Fin m, 4 * a j ^ 2 *
        ∑ i ∈ crossingTerms S (D j), Fintype.card (Reg loc (S i)) ^ 2 * c₀ := by
  set ψ := toEuclideanLin (liftProd (chainList D hDU K fun _ ↦ True)) Ω
  have hψ : ψ ≠ 0 := toEuclideanLin_liftProd_chainList_ne_zero D hDU hf hK _ hΩ
  have hunit : ∀ i, IsUnit (K i).det := fun i ↦
    (Matrix.isUnit_iff_isUnit_det _).mp ((hK i).posDef (hf i)).isUnit
  have hc : (((‖ψ‖⁻¹ : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact inv_ne_zero (norm_ne_zero_iff.mpr hψ)
  have hφ : ‖(((‖ψ‖⁻¹ : ℝ)) : ℂ) • ψ‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ)]
  have hinv : liftProdInv (chainList D hDU K fun _ ↦ True) *
      liftProd (chainList D hDU K fun _ ↦ True) = 1 := by
    refine liftProdInv_mul_liftProd_of_isUnit fun p hp ↦ ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact hunit i
  exact re_inner_sub_le_of_chain D hDU hD K hunit hφ a ha2
    (fun j ↦ clipped_smul (hDU j) hc
      (forall_clipped_of_max D hDU hD f a hf ha hcard K hK Ω hmax hψ j))
    h S hSU hsupp hherm hnorm hsingle (toEuclideanLin_conj_apply_eq heig hinv _)

end OpenAI
