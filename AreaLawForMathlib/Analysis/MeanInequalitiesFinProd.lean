import Mathlib.Analysis.MeanInequalities

/-!
# Hölder's inequality for a weighted sum of a product of `N` functions

`∑ᵢ wᵢ ∏_{j} x_j(i) ≤ ∏_{j} (∑ᵢ wᵢ x_j(i)^N)^{1/N}` for nonnegative weights and functions,
`N` the number of factors; proved from the weighted AM–GM inequality.
-/

open Real Finset

/-- Hölder's inequality with `N = |κ|` equal exponents. -/
theorem sum_mul_prod_le_prod_rpow_sum {ι κ : Type*} [Fintype κ] (hκ : 0 < Fintype.card κ)
    (s : Finset ι) (w : ι → ℝ) (x : κ → ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ j, ∀ i ∈ s, 0 ≤ x j i) :
    ∑ i ∈ s, w i * ∏ j, x j i ≤
      ∏ j, (∑ i ∈ s, w i * x j i ^ Fintype.card κ) ^ ((Fintype.card κ : ℝ)⁻¹) := by
  set N := Fintype.card κ
  set A : κ → ℝ := fun j => ∑ i ∈ s, w i * x j i ^ N
  have hA : ∀ j, 0 ≤ A j := fun j => sum_nonneg fun i hi => mul_nonneg (hw i hi)
    (pow_nonneg (hx j i hi) _)
  have hN : (0 : ℝ) < N := by exact_mod_cast hκ
  by_cases h0 : ∃ j, A j = 0
  · obtain ⟨j₀, hj₀⟩ := h0
    have hz : ∀ i ∈ s, w i * ∏ j, x j i = 0 := by
      intro i hi
      have hterm := (sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hw i hi)
        (pow_nonneg (hx j₀ i hi) _)).mp hj₀ i hi
      rcases mul_eq_zero.mp hterm with h | h
      · rw [h, zero_mul]
      · rw [prod_eq_zero (mem_univ j₀) ((pow_eq_zero_iff hκ.ne').mp h), mul_zero]
    rw [sum_eq_zero hz]
    exact prod_nonneg fun j _ => rpow_nonneg (hA j) _
  simp only [not_exists] at h0
  have hApos : ∀ j, 0 < A j := fun j => (hA j).lt_of_ne (Ne.symm (h0 j))
  have hP : 0 < ∏ j, A j ^ ((N : ℝ)⁻¹) := prod_pos fun j _ => rpow_pos_of_pos (hApos j) _
  -- weighted AM–GM at each `i`
  have hamgm : ∀ i ∈ s, ∏ j, x j i ≤
      (∏ j, A j ^ ((N : ℝ)⁻¹)) * ∑ j, (N : ℝ)⁻¹ * (x j i ^ N / A j) := by
    intro i hi
    have h := geom_mean_le_arith_mean_weighted (univ : Finset κ) (fun _ => (N : ℝ)⁻¹)
      (fun j => x j i ^ N / A j) (fun _ _ => by positivity)
      (by rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_inv_cancel₀ hN.ne')
      (fun j _ => div_nonneg (pow_nonneg (hx j i hi) _) (hA j))
    have he : ∀ j, (x j i ^ N / A j) ^ ((N : ℝ)⁻¹) = x j i / A j ^ ((N : ℝ)⁻¹) := fun j => by
      rw [div_rpow (pow_nonneg (hx j i hi) _) (hA j), pow_rpow_inv_natCast (hx j i hi) hκ.ne']
    simp only [he, prod_div_distrib] at h
    rwa [div_le_iff₀' hP] at h
  calc ∑ i ∈ s, w i * ∏ j, x j i
      ≤ ∑ i ∈ s, w i * ((∏ j, A j ^ ((N : ℝ)⁻¹)) * ∑ j, (N : ℝ)⁻¹ * (x j i ^ N / A j)) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hamgm i hi) (hw i hi)
    _ = (∏ j, A j ^ ((N : ℝ)⁻¹)) * ((N : ℝ)⁻¹ * ∑ j, (∑ i ∈ s, w i * x j i ^ N) / A j) := by
        simp only [mul_sum, sum_div]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
        ring
    _ = ∏ j, A j ^ ((N : ℝ)⁻¹) := by
        simp only [A, div_self (hApos _).ne', sum_const, card_univ, nsmul_eq_mul, mul_one]
        rw [inv_mul_cancel₀ hN.ne', mul_one]
