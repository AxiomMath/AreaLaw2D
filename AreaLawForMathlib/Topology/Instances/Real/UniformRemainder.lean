import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A uniform remainder from uniform eventual bounds

If, for every `ε > 0`, eventually in `k` the family `F k x` is at most `ε` uniformly in `x`,
and each `F k ·` is bounded above, then `F k x ≤ r k` for one sequence `r k → 0`, `r k ≥ 0`.
-/

open Filter Topology

namespace Real

theorem exists_tendsto_zero_of_forall_eventually_le {α : ℕ → Type*} (F : ∀ k, α k → ℝ)
    (hB : ∀ k, ∃ b, ∀ x, F k x ≤ b) (h : ∀ ε > 0, ∀ᶠ k in atTop, ∀ x, F k x ≤ ε) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ k, 0 ≤ r k) ∧ ∀ k x, F k x ≤ r k := by
  refine ⟨fun k => max 0 (⨆ x, F k x), ?_, fun k => le_max_left _ _, fun k x => ?_⟩
  · rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun k => lt_of_lt_of_le ha (le_max_left _ _),
      fun b hb => ?_⟩
    filter_upwards [h (b / 2) (by linarith)] with k hk
    exact lt_of_le_of_lt (max_le (by linarith) (Real.iSup_le hk (by linarith))) (by linarith)
  · obtain ⟨b, hb⟩ := hB k
    exact (le_ciSup ⟨b, Set.forall_mem_range.mpr hb⟩ x).trans (le_max_right _ _)

end Real
