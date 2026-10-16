import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators

/-!
# Shannon entropy of a finite real vector

The Shannon entropy `H p = ∑ i, Real.negMulLog (p i)` of a finite real family, in nats, with
`H₂` the base-2 form the paper displays.  `H` sees only the multiset of values, and is
additive over finite products of probability vectors.
-/

namespace Arealaw

/-- Shannon entropy of a finite real family `p : ι → ℝ`, `H p = ∑ i, -p i · log (p i)`. -/
noncomputable def H {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- `H p` is the sum of `Real.negMulLog` over the multiset of values of `p`. -/
theorem H_eq_multiset_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    H p = (Multiset.map (fun x => Real.negMulLog x) (Finset.univ.val.map p)).sum := by
  rw [H, Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def]

/-- `H` depends only on the multiset of values: if two families have equal value
multisets, their entropies agree. -/
theorem H_eq_of_multiset_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → ℝ} {q : κ → ℝ}
    (h : Finset.univ.val.map p = Finset.univ.val.map q) : H p = H q := by
  rw [H_eq_multiset_sum, H_eq_multiset_sum, h]

/-- **Additivity over a product distribution**: for probability vectors `d₁`, `d₂`, the
entropy of `(i,j) ↦ d₁ i · d₂ j` is `H d₁ + H d₂`. -/
theorem H_mul_add {ι κ : Type*} [Fintype ι] [Fintype κ] (d₁ : ι → ℝ) (d₂ : κ → ℝ)
    (h1 : ∑ i, d₁ i = 1) (h2 : ∑ j, d₂ j = 1) :
    H (fun p : ι × κ => d₁ p.1 * d₂ p.2) = H d₁ + H d₂ := by
  simp [H, Fintype.sum_prod_type, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, h1, h2]

/-- **Additivity over a finite product distribution**: for probability vectors `pₖ`, the
entropy of `x ↦ ∏ₖ pₖ(xₖ)` is `∑ₖ H pₖ`.  The `n`-fold form of `H_mul_add`. -/
theorem H_prod_eq_sum {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)] (p : ∀ k, ι k → ℝ) (hp : ∀ k, ∑ i, p k i = 1) :
    H (fun x : ∀ k, ι k => ∏ k, p k (x k)) = ∑ k, H (p k) := by
  -- Weighting site `j` by `negMulLog` and the others by `p` integrates to `H (p j)`.
  let F (j : κ) : ∀ k, ι k → ℝ := Function.update p j fun y => Real.negMulLog (p j y)
  have hF (j : κ) (x : ∀ k, ι k) :
      ∏ k, F j k (x k) = (∏ k, p k (x k)) * -Real.log (p j (x j)) := by
    rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j (fun k => p k (x k)),
      Finset.prod_congr rfl (g := fun k => p k (x k)) fun k hk => by
        simp only [F, Function.update_of_ne (Finset.mem_compl.mp hk ∘ Finset.mem_singleton.mpr)]]
    simp only [F, Function.update_self, Real.negMulLog]
    ring
  have hpt (x : ∀ k, ι k) : Real.negMulLog (∏ k, p k (x k)) = ∑ j, ∏ k, F j k (x k) := by
    simp_rw [hF, ← Finset.mul_sum, Finset.sum_neg_distrib]
    by_cases h0 : ∏ k, p k (x k) = 0
    · simp [h0]
    · rw [Real.negMulLog, Real.log_prod fun k _ => Finset.prod_ne_zero_iff.mp h0 k
        (Finset.mem_univ k)]
      ring
  simp_rw [H, hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fintype.prod_sum, Fintype.prod_eq_mul_prod_compl j, Finset.prod_eq_one fun k hk => by
    simp only [F, Function.update_of_ne (Finset.mem_compl.mp hk ∘ Finset.mem_singleton.mpr), hp]]
  simp [F]

/-! ## Base 2 -/

/-- Shannon entropy in base 2, `H p / log 2`. -/
noncomputable def H₂ {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := H p / Real.log 2

theorem H₂_def {ι : Type*} [Fintype ι] (p : ι → ℝ) : H₂ p = H p / Real.log 2 := rfl

end Arealaw
