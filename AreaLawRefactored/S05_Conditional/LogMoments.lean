import AreaLawRefactored.S05_Conditional.Defs

/-!
# §5 D5.3 The log-moment generating function

Digest `digest/05-conditional.md`, D5.3. A real random variable `L` on a finite index set with
weights `w` and two-sided exponential moments `𝔼 e^{±L} ≤ d` has sub-exponential tails, an
exponentially weighted second moment `≲ ℓ²` and log-mgf `≤ b 𝔼L + C b² ℓ²`, `ℓ = log(e d)`,
for `|b| ℓ ≤ c`. `Conditional.logMoments_of_spectral` is the eigenvalue level of D5.2.3–5
(it produces the hypotheses of D5.3 from the two eigenbases). D5.3.2 is proved by a direct
split at `|L| ≤ 2ℓ` (pointwise `L² ≤ 8ℓ² + 16 e^{|L|/2-ℓ}`) instead of the paper's layer cake.
-/

namespace AreaLaw

open Real

namespace Conditional

/-- `z² ≤ 2 l² + 4 e^{|z| - l}` for `l ≥ 0` (the split at `|z| ≤ l`). -/
theorem sq_le_cutoff (z l : ℝ) (hl : 0 ≤ l) : z ^ 2 ≤ 2 * l ^ 2 + 4 * exp (|z| - l) := by
  by_cases hz : |z| ≤ l
  · have hh := (sq_le_sq₀ (abs_nonneg z) hl).mpr hz
    rw [sq_abs] at hh
    nlinarith [exp_pos (|z| - l), sq_nonneg l]
  · have he := pow_div_factorial_le_exp (|z| - l) (sub_nonneg.mpr (le_of_not_ge hz)) 2
    norm_num only [Nat.factorial, Nat.cast_ofNat] at he
    nlinarith [sq_abs z, sq_nonneg (|z| - 2 * l)]

/-- Lagrange remainder: `e^x ≤ 1 + x + 3 x² e^{|x|}`. -/
theorem exp_le_one_add_add_sq (x : ℝ) : exp x ≤ 1 + x + 3 * x ^ 2 * exp |x| := by
  have he : 1 ≤ exp |x| := one_le_exp (abs_nonneg _)
  by_cases hx : |x| ≤ 1
  · have hh := Complex.norm_exp_sub_one_sub_id_le (x := (x : ℂ)) (by simpa using hx)
    rw [show Complex.exp (x : ℂ) - 1 - (x : ℂ) = ((exp x - 1 - x : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    nlinarith [(le_abs_self (exp x - 1 - x)).trans hh, sq_nonneg x]
  · have hsq : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    nlinarith only [exp_le_exp.mpr (le_abs_self x), add_one_le_exp |x|, he,
      mul_le_mul_of_nonneg_right hsq (exp_nonneg |x|), neg_abs_le x]

/-- D5.2.3–5, eigenvalue level. `p_i` the eigenvalues of `ρ` (`∑ p = 1`), `q_j > 0` those of
`Q`, `u j i = |⟨i,j⟩|²` (columns and rows of a unitary: `∑_j u j i = 1`, `∑_i u j i ≤ 1`).
If `⟨i,j⟩ = 0` for `p_i > 0`, `j ∉ S` (D5.2.2, `S` the basis of `x ⊗ supp ρ_U`),
`∑_{j∈S} q_j ≤ d` and `Tr ρ² Q⁻¹ = ∑ p_i² |⟨i,j⟩|² / q_j ≤ d` (D5.2.4), then the weights
`w(i,j) = p_i |⟨i,j⟩|²` and `L = log p_i − log q_j` satisfy `∑ w = 1`, `𝔼 e^{L} ≤ d`,
`𝔼 e^{-L} ≤ d`. -/
theorem logMoments_of_spectral {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → ℝ) (q : κ → ℝ)
    (u : κ → ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 < q j) (hu : ∀ j i, 0 ≤ u j i)
    (hs : ∑ i, p i = 1) (hcol : ∀ i, ∑ j, u j i = 1) (hrow : ∀ j, ∑ i, u j i ≤ 1) (d : ℝ)
    (S : Finset κ) (hsupp : ∀ i j, 0 < p i → j ∉ S → u j i = 0) (hS : ∑ j ∈ S, q j ≤ d)
    (hcoll : ∑ i, ∑ j, p i ^ 2 * u j i / q j ≤ d) :
    ∑ ij : ι × κ, p ij.1 * u ij.2 ij.1 = 1 ∧
    ∑ ij : ι × κ, p ij.1 * u ij.2 ij.1 * exp (log (p ij.1) - log (q ij.2)) ≤ d ∧
    ∑ ij : ι × κ, p ij.1 * u ij.2 ij.1 * exp (-(log (p ij.1) - log (q ij.2))) ≤ d := by
  simp only [Fintype.sum_prod_type]
  refine ⟨by simp_rw [← Finset.mul_sum, hcol, mul_one, hs], ?_, ?_⟩
  · -- D5.2.4 `𝔼 e^L = Tr ρ² Q⁻¹`
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_))
      hcoll
    rcases (hp i).eq_or_lt with h | h
    · simp [← h]
    rw [exp_sub, exp_log h, exp_log (hq j)]; ring
  · -- D5.2.5 `𝔼 e^{-L} = Tr Π_{supp ρ} Q ≤ ∑_{j∈S} q_j`
    have hterm : ∀ i j, p i * u j i * exp (-(log (p i) - log (q j))) ≤ q j * u j i := by
      intro i j
      rcases (hp i).eq_or_lt with h | h
      · simp only [← h, zero_mul]; exact mul_nonneg (hq j).le (hu j i)
      rw [neg_sub, exp_sub, exp_log h, exp_log (hq j)]
      exact le_of_eq (by field_simp)
    calc _ = ∑ i, ∑ j ∈ S, p i * u j i * exp (-(log (p i) - log (q j))) :=
          Finset.sum_congr rfl fun i _ ↦ (Finset.sum_subset (Finset.subset_univ S)
            fun j _ hj ↦ by
              rcases (hp i).eq_or_lt with h | h
              · simp [← h]
              · simp [hsupp i j h hj]).symm
      _ ≤ ∑ j ∈ S, q j * ∑ i, u j i := by
          rw [Finset.sum_comm]
          exact Finset.sum_le_sum fun j _ ↦ by
            rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ ↦ hterm i j
      _ ≤ _ := (Finset.sum_le_sum fun j _ ↦
          mul_le_of_le_one_right (hq j).le (hrow j)).trans hS

end Conditional

universe u

open Conditional in
/-- D5.3 (`eq:conditional-log-mgf`). `ℓ = log(e d)`. Universal `c ≤ 1/2`, `C > 0`
(`c = 1/2`, `C = 228`) such that for every finite `ι`, weights `w ≥ 0` with `∑ w = 1`, and real
`L` with `𝔼 e^{L} ≤ d`, `𝔼 e^{-L} ≤ d` (`𝔼 f = ∑ w f`, `1 ≤ d`):
`Pr(|L| > v) ≤ 2 d e^{-v}`, `𝔼[L² e^{|bL|}] ≤ C ℓ²` and `log 𝔼 e^{bL} ≤ b 𝔼L + C b² ℓ²` for
`|b| ℓ ≤ c`. (The paper's `𝔼 L = -S(x|U)`, D5.2.) -/
theorem step_5_3 : ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 < C ∧
    ∀ (ι : Type u) [Fintype ι] (w L : ι → ℝ) (d : ℕ), 1 ≤ d → (∀ i, 0 ≤ w i) →
      ∑ i, w i = 1 → ∑ i, w i * exp (L i) ≤ d → ∑ i, w i * exp (-L i) ≤ d →
      (∀ v : ℝ, ∑ i ∈ Finset.univ.filter (fun i ↦ v < |L i|), w i ≤ 2 * d * exp (-v)) ∧
      (∀ b : ℝ, |b| * ℓ d ≤ c → ∑ i, w i * (L i ^ 2 * exp |b * L i|) ≤ C * ℓ d ^ 2) ∧
      (∀ b : ℝ, |b| * ℓ d ≤ c →
        log (∑ i, w i * exp (b * L i)) ≤ b * ∑ i, w i * L i + C * b ^ 2 * ℓ d ^ 2) := by
  refine ⟨1 / 2, 228, by norm_num, le_rfl, by norm_num, ?_⟩
  intro ι _ w L d hd hw hs hpos hneg
  set l := ℓ d
  have hl : 1 ≤ l := one_le_ℓ hd
  have hdl : (d : ℝ) ≤ exp l := by
    rw [show l = log (exp 1 * d) from rfl, exp_log (by positivity)]
    nlinarith [add_one_le_exp (1 : ℝ), (by exact_mod_cast hd : (1 : ℝ) ≤ d)]
  have hmass : ∑ i, w i * exp |L i| ≤ 2 * d := by
    calc _ ≤ ∑ i, w i * (exp (L i) + exp (-L i)) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left (by
              rcases abs_cases (L i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
                linarith [exp_pos (L i), exp_pos (-L i)]) (hw i)
      _ ≤ 2 * d := by simp only [mul_add, Finset.sum_add_distrib]; linarith
  -- D5.3.1 Markov on D5.2
  have tails : ∀ v : ℝ, ∑ i ∈ Finset.univ.filter (fun i ↦ v < |L i|), w i ≤
      2 * d * exp (-v) := fun v ↦ calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ v < |L i|), w i * exp |L i| * exp (-v) :=
        Finset.sum_le_sum fun i hi ↦ by
          rw [mul_assoc, ← exp_add]
          exact le_mul_of_one_le_right (hw i)
            (one_le_exp (by linarith [(Finset.mem_filter.1 hi).2]))
    _ ≤ ∑ i, w i * exp |L i| * exp (-v) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ ↦ by have := hw i; positivity
    _ ≤ _ := by rw [← Finset.sum_mul]; gcongr
  -- D5.3.2 second moment with exponential weight, split at `|L| ≤ 2ℓ`
  have second : ∀ b : ℝ, |b| * l ≤ 1 / 2 →
      ∑ i, w i * (L i ^ 2 * exp |b * L i|) ≤ 76 * l ^ 2 := by
    intro b hb
    set β := |b|
    have hβ : 0 ≤ β := abs_nonneg b
    have hβh : β ≤ 1 / 2 := by nlinarith
    have hcenter : ∑ i, w i * exp (|L i| - l) ≤ 2 := by
      simp only [exp_sub, ← mul_div_assoc, ← Finset.sum_div]
      exact (div_le_iff₀ (exp_pos l)).mpr (by linarith)
    have htilt : ∑ i, w i * exp (β * |L i|) ≤ 2 * exp 1 := by
      have hp : ∑ i, w i * exp (β * (|L i| - l)) ≤ 2 := calc
        _ ≤ ∑ i, w i * (1 - β + β * exp (|L i| - l)) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left (by
              simpa only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] using
                convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (|L i| - l))
                  (by linarith : 0 ≤ 1 - β) hβ (by ring)) (hw i)
        _ = 1 - β + β * ∑ i, w i * exp (|L i| - l) := by
          simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.sum_mul, hs, one_mul, Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ ≤ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hcenter hβ, hβ, hβh]
      calc _ = exp (β * l) * ∑ i, w i * exp (β * (|L i| - l)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [mul_left_comm, ← exp_add]; ring_nf
        _ ≤ exp (β * l) * 2 := mul_le_mul_of_nonneg_left hp (exp_nonneg _)
        _ ≤ 2 * exp 1 := by
          nlinarith only [exp_le_exp.mpr (by linarith : β * l ≤ 1), exp_pos (β * l)]
    have hpt : ∀ i, L i ^ 2 * exp |b * L i| ≤
        8 * l ^ 2 * exp (β * |L i|) + 16 * exp (|L i| - l) := fun i ↦ by
      have hh := sq_le_cutoff (L i / 2) l (by linarith)
      rw [abs_div, abs_two] at hh
      have hm := mul_le_mul_of_nonneg_right hh (exp_nonneg (β * |L i|))
      have hsmall : exp (|L i| / 2 - l) * exp (β * |L i|) ≤ exp (|L i| - l) := by
        rw [← exp_add]
        have := mul_le_mul_of_nonneg_right hβh (abs_nonneg (L i))
        exact exp_le_exp.mpr (by linarith)
      rw [abs_mul]
      nlinarith only [hm, hsmall]
    have he := exp_one_lt_d9
    calc _ ≤ ∑ i, w i * (8 * l ^ 2 * exp (β * |L i|) + 16 * exp (|L i| - l)) :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hpt i) (hw i)
      _ = 8 * l ^ 2 * ∑ i, w i * exp (β * |L i|) + 16 * ∑ i, w i * exp (|L i| - l) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ 76 * l ^ 2 := by
          nlinarith only [mul_le_mul_of_nonneg_left htilt (by positivity : 0 ≤ 8 * l ^ 2),
            hcenter, he, hl]
  refine ⟨tails, fun b hb ↦ (second b hb).trans (by nlinarith), fun b hb ↦ ?_⟩
  -- D5.3.3 Taylor, then `log (1 + y) ≤ y`
  have hmgf : ∑ i, w i * exp (b * L i) ≤ 1 + b * ∑ i, w i * L i + 228 * b ^ 2 * l ^ 2 := calc
    _ ≤ ∑ i, w i * (1 + b * L i + 3 * (b * L i) ^ 2 * exp |b * L i|) :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (exp_le_one_add_add_sq _) (hw i)
    _ = 1 + b * ∑ i, w i * L i + 3 * b ^ 2 * ∑ i, w i * (L i ^ 2 * exp |b * L i|) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hs, Finset.mul_sum]
        congr 1
        · congr 1; exact Finset.sum_congr rfl fun _ _ ↦ by ring
        · exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left (second b hb) (sq_nonneg b)]
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ ↦ (0 : ℝ))
    (g := w) (by simp [hs])
  have hpos' : 0 < ∑ i, w i * exp (b * L i) := Finset.sum_pos' (fun j _ ↦ by
    have := hw j; positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  linarith [log_le_sub_one_of_pos hpos']

end AreaLaw
