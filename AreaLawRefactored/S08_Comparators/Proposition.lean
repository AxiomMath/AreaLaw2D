import AreaLawRefactored.S08_Comparators.Interfaces
import AreaLawRefactored.S08_Comparators.Entropy

/-!
# §8.1 Proposition 8.1

Digest `digest/08-comparators.md` D8.8, D8.37, paper `paper/sections/07-comparators.tex`
125–214, 659–667. Over an arbitrary finite site type with arbitrary local dimensions, arbitrary
status collections and arbitrary trees; no geometry. D8.37 (uniformity of the errors) has no
declaration of its own: it is the quantifier order of the statement (`o_k(1)` chosen before the
tree, the label sequence before `a`, `τ` and the statuses).
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

/-- D8.8 **Proposition 8.1**, from the anchors D8.12, D8.13, D8.20, D8.22, D8.35 (D8.36 and
D8.30.6 are proved in `Entropy.lean`). -/
theorem prop_8_1_of (h12 : Step_8_12.{u}) (h13 : Step_8_13.{u, v}) (h20 : Step_8_20.{u, v})
    (h22 : Step_8_22.{u, v}) (h35 : Step_8_35.{u, v}) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧ ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
    ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X),
    ∃ l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ,
        pre D E.d k (l k) ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧ pre D E.d k (l k) ≠ 0 ∧
        (star (pre D E.d k (l k)) ⬝ᵥ pre D E.d k (l k)).re ≤ 1 ∧
        (0 < k → Hbar D E.d k *ᵥ pre D E.d k (l k) = (D.E₀ : ℂ) • pre D E.d k (l k)) ∧
        piC E.d k (l k) *ᵥ pre D E.d k (l k) = pre D E.d k (l k) ∧
        piR E.d k (l k) *ᵥ pre D E.d k (l k) = pre D E.d k (l k)) ∧
      ∀ {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St] (Γ : Statuses σ K St X),
        (∀ (𝓡 : Finset (Finset σ)) (Bsh Bexc : ℝ), PrefixData D Γ 𝓡 Bsh Bexc →
          ∀ a : ℝ, 0 < a → a ≤ a₀ → RoughUpper D Γ E a l Bsh Bexc) ∧
        (∀ a τ : ℝ, 0 < a → a ≤ a₀ → 0 < τ → τ < 1 / 2 → RoughLower D Γ E C a τ l) ∧
        (∀ s g, 0 ≤ gpre D Γ s g) ∧
        (∀ 𝓑 : ℝ, MgfData D Γ C₀ c₀ 𝓑 → ∀ a τ : ℝ, 0 < a → a ≤ c / Real.sqrt 𝓑 → 0 < τ →
          τ < 1 / 2 → SharpUpper D Γ E C₁ a 𝓑 l ∧ SharpLower D Γ E C₂ a τ 𝓑 l) ∧
        ∀ s g, 2 * D.S X + gpre D Γ s g - gpost D Γ s g =
          D.I X (Γ.V s g) + D.I X (Γ.Y s g ∪ Γ.V s g) := by
  obtain ⟨a₁, ha₁, hU⟩ := h20
  obtain ⟨a₂, C, ha₂, hC, hL, hLs⟩ := h35
  refine ⟨min a₁ a₂, C, lt_min ha₁ ha₂, hC, fun C₀ c₀ hC₀ hc₀ => ?_⟩
  obtain ⟨c₁, C₁, hc₁, hC₁, hSU⟩ := h22 C₀ c₀ hC₀ hc₀
  obtain ⟨c₂, C₂, hc₂, hC₂, hSL⟩ := hLs C₀ c₀ hC₀ hc₀
  refine ⟨min c₁ c₂, C₁, C₂, lt_min hc₁ hc₂, hC₁, hC₂, ?_⟩
  intro σ _ _ n _ D X E
  -- D8.8.1: labels and prevector (D8.12, D8.13)
  obtain ⟨l, hl⟩ := h12 E
  refine ⟨l, fun k => ?_, fun {K St} _ _ Γ => ⟨?_, ?_, gpre_nonneg Γ, ?_, step_8_36 Γ⟩⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h13 D E l hl k
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  -- D8.8.2: upper bounds (D8.20, D8.22)
  · exact fun 𝓡 Bsh Bexc h𝓡 a ha ha₀ =>
      hU D E Γ l hl 𝓡 Bsh Bexc h𝓡 a ha (ha₀.trans (min_le_left _ _))
  -- D8.8.3, D8.8.4: lower bounds (D8.35)
  · exact fun a τ ha ha₀ hτ hτ' => hL D E Γ l hl a τ ha (ha₀.trans (min_le_right _ _)) hτ hτ'
  · intro 𝓑 h𝓑 a τ ha hac hτ hτ'
    have hs : Real.sqrt 𝓑 > 0 := Real.sqrt_pos.2 (lt_of_lt_of_le one_pos h𝓑.one_le)
    have hc₁' : a ≤ c₁ / Real.sqrt 𝓑 :=
      hac.trans (div_le_div_of_nonneg_right (min_le_left _ _) hs.le)
    have hc₂' : a ≤ c₂ / Real.sqrt 𝓑 :=
      hac.trans (div_le_div_of_nonneg_right (min_le_right _ _) hs.le)
    exact ⟨hSU D E Γ l hl 𝓑 h𝓑 a ha hc₁', hSL D E Γ l hl 𝓑 h𝓑 a τ ha hc₂' hτ hτ'⟩

end AreaLaw.Comparators
