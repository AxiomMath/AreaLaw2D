import AreaLawRefactored.S02_Preliminaries

/-!
# §6 inputs from §5 (to be discharged by S05 after merge)

Verbatim copies of the §5 declarations §6 uses, from `AreaLawRefactored/S05_Conditional/Defs.lean`
on branch `…-s05`: the D5.1 definitions `bracketPow`, `hatPow`, `hat`, `marg`, `ℓ` and the
statements `Lemma_5_1 : Prop` (D5.5) and `Lemma_5_3 : Prop` (D5.15, with `Conditional.f`). §6
takes the lemmas as hypotheses `(lemma_5_1 : Lemma_5_1)`, `(lemma_5_3 : Lemma_5_3)`. At the
merge this file is deleted and replaced by `import AreaLawRefactored.S05_Conditional`.
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## D5.1 Spectral powers, hat, norms -/

section D51

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D5.1. `ρ^{[z]} = ∑_{p>0} p^z Π_p` (`z ∈ ℂ`), in the eigenbasis of a Hermitian `ρ`; it is `0`
on `ker ρ` for every `z`, so `ρ^{[0]} = Π_{supp ρ}`. Brackets are omitted for positive real
powers: `ρ^a = ρ^{[a]}`, `a > 0`. -/
noncomputable def bracketPow (ρ : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  if h : ρ.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i ↦ if 0 < h.eigenvalues i then Complex.exp (z * Real.log (h.eigenvalues i))
        else 0) * star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 0

/-- D5.1. `ρ̂^z` for `ρ̂ = ρ + Π_{ker ρ}`: `p^z` on the eigenvalues `p > 0`, `1` on `ker ρ`.
`ρ̂ > 0`, and `ρ̂^{iu}` is unitary and `= 1` on `ker ρ`; likewise `ρ̂^{-a} = 1` on `ker ρ`. -/
noncomputable def hatPow (ρ : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  if h : ρ.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i ↦ if 0 < h.eigenvalues i then Complex.exp (z * Real.log (h.eigenvalues i))
        else 1) * star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 1

/-- D5.1. `ρ̂ = ρ + Π_{ker ρ}`. -/
noncomputable def hat (ρ : Matrix n n ℂ) : Matrix n n ℂ := hatPow ρ 1

/-- D5.1 Pitfall. `ρ̂^0 = I` (whereas `ρ^{[0]} = Π_{supp ρ}`). -/
theorem hatPow_zero (ρ : Matrix n n ℂ) : hatPow ρ 0 = 1 := by
  unfold hatPow
  split_ifs with h
  · simp only [zero_mul, Complex.exp_zero, ite_self, diagonal_one, Matrix.mul_one]
    exact Unitary.coe_mul_star_self h.eigenvectorUnitary
  · rfl

end D51

section Setting

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ D : Finset σ}

/-- `ρ_D`: the marginal of the vector `θ` on `D ⊆ Λ`. -/
noncomputable def marg (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) : Matrix (Reg loc D) (Reg loc D) ℂ :=
  ptrace hD (vecMulVec θ (star θ))

/-- `ℓ = log(e d)`. -/
noncomputable def ℓ (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)


end Setting

section Statements

universe u v

/-- D5.5 **Lemma 5.1** (conditional movement estimate). `θ` unit pure vector on
finite-dimensional `P, x, U, F`; `ρ_D` its marginals; `d = dim x`, `ℓ = log(e d)`,
`η = S(x|P)_θ + S(x|U)_θ = I(x:F|U)_θ = I(x:F|P)_θ`. Universal `c, C > 0` such that for
`0 < aℓ ≤ c` and all density matrices `σ` on `xP`, `τ` on `xU`:
`‖σ^{a/2} ρ̂_P^{-a/2} τ^{a/2} ρ̂_U^{-a/2} θ‖ ≤ exp(-(a/2) η + C a^{5/4} ℓ²)`.
Same bound for positive subnormalised `σ, τ` (stated so: `σ, τ ≥ 0`, `Tr ≤ 1`). -/
def Lemma_5_1 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P X U F : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
      (hF : F ⊆ Λ), Λ = P ∪ X ∪ U ∪ F → Disjoint P X → Disjoint P U → Disjoint P F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1) (a : ℝ),
      0 < a * ℓ (Fintype.card (Reg loc X)) → a * ℓ (Fintype.card (Reg loc X)) ≤ c →
    ∀ (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
      (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ),
      σ'.PosSemidef → σ'.trace.re ≤ 1 → τ.PosSemidef → τ.trace.re ≤ 1 →
      ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hP) (bracketPow σ' (a / 2 : ℝ)) *
          extendId hP (hatPow (marg θ hP) (-(a / 2 : ℝ))) *
          extendId (Finset.union_subset hX hU) (bracketPow τ (a / 2 : ℝ)) *
          extendId hU (hatPow (marg θ hU) (-(a / 2 : ℝ)))) *ᵥ θ) :
            EuclideanSpace ℂ (Reg loc Λ))‖ ≤
        Real.exp (-(a / 2) * condMutualInfo (pureState θ hθ).toSubState hX hU hF +
          C * a ^ (5 / 4 : ℝ) * ℓ (Fintype.card (Reg loc X)) ^ 2)

namespace Conditional

/-- D5.15. The entire function
`f(z) = ⟨θ, ρ_P^{[z]} ρ_Y^{[-z]} h ρ_P^{[-z]} ρ_Y^{[z]} θ⟩` of Lemma 5.3, `Y = xU`,
`P = P₀P₁`, `h` on `P₀x`. -/
noncomputable def f {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {Λ P₀ P₁ X U : Finset σ} (hP : P₀ ∪ P₁ ⊆ Λ) (hY : X ∪ U ⊆ Λ)
    (hPX : P₀ ∪ X ⊆ Λ) (θ : Reg loc Λ → ℂ) (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ)
    (z : ℂ) : ℂ :=
  star θ ⬝ᵥ ((extendId hP (bracketPow (marg θ hP) z) * extendId hY (bracketPow (marg θ hY) (-z)) *
    extendId hPX h * extendId hP (bracketPow (marg θ hP) (-z)) *
    extendId hY (bracketPow (marg θ hY) z)) *ᵥ θ)

end Conditional

/-- D5.15 **Lemma 5.3** (conditional skew estimate). `θ` unit pure vector on `P, x, U, F`;
`Y = xU`; `P = P₀P₁` and `0 ≤ h ≤ I` supported on `P₀x`. `d_h = (dim P₀)(dim x)`,
`ℓ_h = log(e d_h)`, `η = I(x:F|U)_θ = I(x:F|P)_θ`. Universal `c, C > 0` such that for
`0 < aℓ_h ≤ c` and `t = a/2`: `|f(t)| − Re f(t) ≤ C a² ℓ_h⁴ η^{1/8}`. -/
def Lemma_5_3 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P₀ P₁ X U F : Finset σ) (hP₀ : P₀ ⊆ Λ) (hP₁ : P₁ ⊆ Λ)
      (hX : X ⊆ Λ) (hU : U ⊆ Λ) (hF : F ⊆ Λ), Λ = P₀ ∪ P₁ ∪ X ∪ U ∪ F →
      Disjoint P₀ P₁ → Disjoint (P₀ ∪ P₁) X → Disjoint (P₀ ∪ P₁) U → Disjoint (P₀ ∪ P₁) F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
      (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ), 0 ≤ h → h ≤ 1 →
    ∀ a : ℝ, 0 < a * ℓ (Fintype.card (Reg loc (P₀ ∪ X))) →
      a * ℓ (Fintype.card (Reg loc (P₀ ∪ X))) ≤ c →
      ‖Conditional.f (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU)
          (Finset.union_subset hP₀ hX) θ h (a / 2 : ℝ)‖ -
        (Conditional.f (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU)
          (Finset.union_subset hP₀ hX) θ h (a / 2 : ℝ)).re ≤
        C * a ^ 2 * ℓ (Fintype.card (Reg loc (P₀ ∪ X))) ^ 4 *
          condMutualInfo (pureState θ hθ).toSubState hX hU hF ^ (1 / 8 : ℝ)

end Statements

end AreaLaw
