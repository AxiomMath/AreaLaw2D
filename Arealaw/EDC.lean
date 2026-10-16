import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Arealaw.Cor
import Arealaw.Geometry

/-!
# Exponential decay of correlations

BH12's hypothesis, Eq. (2).  Stated over an arbitrary site metric `d`, so the same
definition serves the ring (`ringDist`) and the line (`Nat.dist` on `Fin n`), and in base
2 as the paper writes it, a change of base being a rescaling of `ξ`.  `0 < ξ` is not part
of the definition: a consumer that divides by `ξ` carries it.
-/

namespace Arealaw

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U : Finset σ}

/-- `(ξ, l₀)`-exponential decay of correlations over the site metric `d` (BH12, Eq. (2)):
`Cor(X : Y) ≤ 2^(-l/ξ)` for every `l ≥ l₀` and every two regions separated by more than
`l` sites. -/
def SubState.HasEDC (ρ : SubState (Reg loc U) 𝕜) (d : σ → σ → ℕ) (ξ : ℝ) (l₀ : ℕ) : Prop :=
  ∀ ⦃X Y : Finset σ⦄ (hd : Disjoint X Y) (hX : X ⊆ U) (hY : Y ⊆ U) ⦃l : ℕ⦄,
    l₀ ≤ l → l < separation d X Y → ρ.Cor hd hX hY ≤ 2 ^ (-(l : ℝ) / ξ)

namespace SubState

variable {ρ : SubState (Reg loc U) 𝕜} {d : σ → σ → ℕ} {ξ ξ' : ℝ} {l₀ l₀' : ℕ}

/-- Exponential decay of correlations is monotone: a longer correlation length and a
larger onset length are weaker hypotheses.  `0 < ξ` is necessary: for `ξ < 0` the bound
*grows* with `l`. -/
theorem HasEDC.mono (h : ρ.HasEDC d ξ l₀) (hξ : 0 < ξ) (hξξ' : ξ ≤ ξ') (hl : l₀ ≤ l₀') :
    ρ.HasEDC d ξ' l₀' := fun X Y hd hX hY l hl' hsep =>
  (h hd hX hY (hl.trans hl') hsep).trans <|
    Real.rpow_le_rpow_of_exponent_le one_le_two (by simp only [neg_div]; gcongr)

/-- A state with no correlations has exponential decay of correlations for every
correlation length. -/
theorem hasEDC_of_Cor_eq_zero
    (h : ∀ (X Y : Finset σ) (hd : Disjoint X Y) (hX : X ⊆ U) (hY : Y ⊆ U),
      ρ.Cor hd hX hY = 0) (d : σ → σ → ℕ) (ξ : ℝ) (l₀ : ℕ) : ρ.HasEDC d ξ l₀ :=
  fun X Y hd hX hY _ _ _ => (h X Y hd hX hY).trans_le (by positivity)

end SubState

end Arealaw
