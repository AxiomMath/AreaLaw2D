import AreaLaw.S05_Conditional.Defs

/-!
# §5 statements of the faithful case of Lemma 5.2 and of D5.16

The two intermediate statements through which `lemma_5_2` and `lemma_5_3` are assembled:
`Lemma_5_2_faithful` (D5.12.1–10, Hilbert–Schmidt form, faithful `ρ_f`) and `Step_5_16`
(D5.16, the strip bounds of the entire function `f` of Lemma 5.3).
-/

namespace AreaLaw

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder

universe u v

/-- D5.12.1–10, the faithful case of **Lemma 5.2** in Hilbert–Schmidt form. Universal `C` such
that for every faithful density matrix `ρ_f` on `xUF` and real `u`,
`‖(ρ̂_U^{-iu} ρ̂_{xU}^{iu} − ρ̂_{UF}^{-iu} ρ̂_{xUF}^{iu}) √ρ_f‖₂ ≤ C |sinh πu| 𝓡_η`,
`η = I(x:F|U)_{ρ_f}`, `d = dim x`. -/
@[nolint defsWithUnderscore]
def Lemma_5_2_faithful : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (T X U F : Finset σ) (hX : X ⊆ T) (hU : U ⊆ T) (hF : F ⊆ T),
      T = X ∪ U ∪ F → Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (ρ : MState (Reg loc T) ℂ), ρ.M.PosDef → ∀ u : ℝ,
      let W := (extendId hU (hatPow (ptrace hU ρ.M) (-(u * Complex.I))) *
          extendId (Finset.union_subset hX hU)
            (hatPow (ptrace (Finset.union_subset hX hU) ρ.M) (u * Complex.I)) -
          extendId (Finset.union_subset hU hF)
            (hatPow (ptrace (Finset.union_subset hU hF) ρ.M) (-(u * Complex.I))) *
          extendId (Finset.union_subset (Finset.union_subset hX hU) hF)
            (hatPow (ptrace (Finset.union_subset (Finset.union_subset hX hU) hF) ρ.M)
              (u * Complex.I))) * CFC.sqrt ρ.M
      √(Wᴴ * W).trace.re ≤
        C * |Real.sinh (Real.pi * u)| *
          𝓡 (Fintype.card (Reg loc X)) (condMutualInfo ρ.toSubState hX hU hF)

/-- D5.16 (with D5.16.4–5 and `f(0) = p`). For the function `f` of **Lemma 5.3**: `f` is entire,
`f(-z̄) = conj f(z)`, `0 ≤ f(iu) ≤ 1`, `|f(z)| ≤ d_h²` on `|Re z| ≤ 1/4`, and
`f(0) = p = ⟨θ, hθ⟩`. -/
@[nolint defsWithUnderscore]
def Step_5_16 : Prop :=
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P₀ P₁ X U F : Finset σ) (hP₀ : P₀ ⊆ Λ) (hP₁ : P₁ ⊆ Λ)
      (hX : X ⊆ Λ) (hU : U ⊆ Λ) (_hF : F ⊆ Λ), Λ = P₀ ∪ P₁ ∪ X ∪ U ∪ F →
      Disjoint P₀ P₁ → Disjoint (P₀ ∪ P₁) X → Disjoint (P₀ ∪ P₁) U → Disjoint (P₀ ∪ P₁) F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ), star θ ⬝ᵥ θ = 1 →
    ∀ (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ), 0 ≤ h → h ≤ 1 →
      let f := Conditional.f (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU)
        (Finset.union_subset hP₀ hX) θ h
      Differentiable ℂ f ∧ (∀ z, f (-(starRingEnd ℂ z)) = starRingEnd ℂ (f z)) ∧
      (∀ t : ℝ, (f (t * Complex.I)).im = 0 ∧ 0 ≤ (f (t * Complex.I)).re ∧
        (f (t * Complex.I)).re ≤ 1) ∧
      (∀ z : ℂ, |z.re| ≤ 1 / 4 → ‖f z‖ ≤ (Fintype.card (Reg loc (P₀ ∪ X)) : ℝ) ^ 2) ∧
      f 0 = star θ ⬝ᵥ (extendId (Finset.union_subset hP₀ hX) h *ᵥ θ)

end AreaLaw
