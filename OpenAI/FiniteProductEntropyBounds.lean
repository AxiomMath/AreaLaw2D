import OpenAI.FiniteProductEntropy
import Arealaw.EntropyBounds

/-!
# Elementary bounds on regional entropies of finite-product pure states

For a normalized pure state on a finite product, a regional entropy is nonnegative and at
most the logarithmic dimension of the region, and for nested regions `A ⊆ B` it obeys the two
triangle inequalities `S(B) ≤ S(A) + S(B \ A)` and `S(A) ≤ S(B) + S(B \ A)`.  The first is
subadditivity; the second is Araki–Lieb, here obtained from subadditivity and the equality of
complementary entropies.
-/

open scoped BigOperators Matrix ComplexOrder

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Regional entropies of a normalized pure state are nonnegative. -/
theorem entropy_nonneg (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (R : Finset V) : 0 ≤ entropy β ψ R := by
  unfold entropy
  rw [Arealaw.vonNeumann_eq_H]
  exact Arealaw.entropy_nonneg (reducedPure_posSemidef β ψ R)
    (by rw [trace_reducedPure β ψ hψ R, RCLike.one_re])

/-- A regional entropy of a normalized pure state is at most the logarithmic dimension of the
region. -/
theorem entropy_le_log_card (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (R : Finset V) : entropy β ψ R ≤ Real.log (Fintype.card (Configuration β R)) := by
  unfold entropy
  rw [Arealaw.vonNeumann_eq_H]
  exact Arealaw.entropy_le_log_card (reducedPure_posSemidef β ψ R)
    (by rw [trace_reducedPure β ψ hψ R, RCLike.one_re])

/-- **Subadditivity for nested regions**: `S(B) ≤ S(A) + S(B \ A)` when `A ⊆ B`. -/
theorem entropy_le_entropy_add_sdiff (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    {A B : Finset V} (hAB : A ⊆ B) :
    entropy β ψ B ≤ entropy β ψ A + entropy β ψ (B \ A) := by
  simpa only [Finset.union_sdiff_of_subset hAB] using
    entropy_union_le β ψ hψ A (B \ A) Finset.disjoint_sdiff

/-- **Araki–Lieb for nested regions**: `S(A) ≤ S(B) + S(B \ A)` when `A ⊆ B`. -/
theorem entropy_le_entropy_sdiff_add (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    {A B : Finset V} (hAB : A ⊆ B) :
    entropy β ψ A ≤ entropy β ψ B + entropy β ψ (B \ A) := by
  have hcompl : Aᶜ = (B \ A) ∪ Bᶜ := by
    ext x
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    by_cases hB : x ∈ B
    · exact ⟨fun h => Or.inl ⟨hB, h⟩, fun h => h.elim And.right (absurd hB)⟩
    · exact ⟨fun _ => Or.inr hB, fun _ h => hB (hAB h)⟩
  have hdisj : Disjoint (B \ A) Bᶜ :=
    Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_compl.mp hx' (Finset.mem_sdiff.mp hx).1
  have h := entropy_union_le β ψ hψ (B \ A) Bᶜ hdisj
  rw [← hcompl, entropy_compl, entropy_compl] at h
  linarith

end FiniteProduct

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With a common local dimension `q`, a regional entropy is at most `|R| log q`. -/
theorem entropy_le_card_mul_log (q : ℕ) (ψ : EuclideanSpace ℂ (V → Fin q)) (hψ : ‖ψ‖ = 1)
    (R : Finset V) :
    entropy (fun _ : V => Fin q) ψ R ≤ (R.card : ℝ) * Real.log q := by
  have h := entropy_le_log_card (fun _ : V => Fin q) ψ hψ R
  simpa only [Configuration, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    Nat.cast_pow, Real.log_pow] using h

end FiniteProduct
