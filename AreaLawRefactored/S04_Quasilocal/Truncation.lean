import AreaLawRefactored.S04_Quasilocal.VolumeFree
import AreaLawRefactored.S04_Quasilocal.GroundState
import AreaLawRefactored.S04_Quasilocal.Crossing

/-!
# §4.3 Proposition 4.5: truncation near a finite set

Digest `digest/04-quasilocal.md` (D4.11), paper `paper/sections/03-quasilocal.tex`
lines 405–521. Graph-level: a simple graph `G` with ball growth `V(r) ≤ K (r+1)^m` (on `ℤ^d`,
`V = v d`, `m = d`; the paper is `m = 2`) and `|S₀| ≤ C₀ n^s` (paper `s = 2`).

The input is the output of Proposition 4.3 (D4.6) at `p = 1`, `α = 1/2`: the constraints `k_i`
with `0 ≤ k_i ≤ I`, `k_i Ω = 0`, `H_F = ∑ k_i ≥ g (I - P_Ω)`, `k_{i,l} ∈ [0, I]` and
`‖k_i - k_{i,l}‖ ≤ C e^{-c l^{1/2}}`. Until D4.6 is formalized it enters as these hypotheses,
with the constants `C, c, g` of D4.6 fixed before `C₁`.
-/

namespace AreaLaw

open Arealaw OpenAI Matrix Finset GraphDomain Real
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

/-- D4.11 (Proposition 4.5). Use D4.6 with `p = 1`, `α = 1/2`. Fix `C₀ > 0`. There is `C₁`
depending only on `q, R, J, Δ, C₀` such that for every real `n ≥ 2` and every `S₀ ⊆ Λ` with
`|S₀| ≤ C₀ n^s`: put `r₀ = ⌈C₁ (log n)²⌉`. If `d_i^0 := d_Λ(a_i, S₀) < ∞`,
`r_i = max {r₀, ⌊d_i^0/2⌋}`, `h̃_i = k_{i,r_i}`, `X̃_i = N_{r_i}(a_i)`. If `d_i^0 = ∞`:
`h̃_i = k_i`, `X̃_i` = whole component of `a_i`. Then `H̃ = ∑_i h̃_i` is a sum of positive
contractions and `‖H̃ - H_F‖ ≤ ε_n := min {n^{-1000}, g/4}`. Its ground energy
`Ẽ₀ ∈ [0, ε_n]`, ground vector `Ω̃` unique, gap `≥ g/2`. After a choice of phase,
`‖Ω̃ - Ω‖ ≤ 2√(ε_n/g)`, `½‖|Ω̃⟩⟨Ω̃| - P_Ω‖₁ ≤ √(2ε_n/g)`. For `X ⊆ S₀` let `b_X = |∂_Λ X|` and
`𝓒_X` the labels whose `X̃_i` meet both `X` and `Λ \ X`. Each such support has radius exactly
`r₀` and `|𝓒_X| ≤ C b_X (r₀+1)^m`, `log d_i ≤ C (r₀+1)^m` (`i ∈ 𝓒_X`), `d_i := q^{|X̃_i|}`,
`𝓑_X := 1 + ∑_{i ∈ 𝓒_X} log²(e d_i) ≤ C (1 + b_X)(r₀+1)^{3m}`. In particular `b_X ≤ C₂ n D`,
`D ≥ 1` ⇒ `𝓑_X ≤ C n D (log n)^{6m}` (`C` also depends on `C₂`). -/
theorem prop_4_5 {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]
    (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {K : ℝ}
    (hK : 0 ≤ K) (m : ℕ) (hVpoly : ∀ r : ℕ, (V r : ℝ) ≤ K * (r + 1) ^ m) {q : ℕ} (hq : 1 ≤ q)
    (R : ℕ) {C c g C₀ s : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hg : 0 < g) (hC₀ : 0 ≤ C₀)
    (hs : 0 ≤ s) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ Cb : ℝ, 0 ≤ Cb ∧
    (∀ (Λ : Finset σ) (a : Finset σ → σ), (∀ X ∈ supports G Λ R, a X ∈ X) →
      ∀ (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
        (k : Finset σ → Matrix (Reg (fun _ : σ => Fin q) Λ) (Reg (fun _ : σ => Fin q) Λ) ℂ),
        (∀ X ∈ supports G Λ R, 0 ≤ k X ∧ k X ≤ 1 ∧ k X *ᵥ Ω = 0) →
        (g : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤ ∑ X ∈ supports G Λ R, k X →
        (∀ X ∈ supports G Λ R, ∀ l : ℕ, 0 ≤ E G Λ (a X) l (k X) ∧ E G Λ (a X) l (k X) ≤ 1 ∧
          ‖k X - E G Λ (a X) l (k X)‖ ≤ C * exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ)))) →
      ∀ (n : ℝ), 2 ≤ n → ∀ S₀ : Finset σ, (#S₀ : ℝ) ≤ C₀ * n ^ s →
        (∀ X ∈ supports G Λ R, 0 ≤ truncated G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a X) (k X) ∧
          truncated G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a X) (k X) ≤ 1) ∧
        ‖∑ X ∈ supports G Λ R, truncated G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a X) (k X) -
            ∑ X ∈ supports G Λ R, k X‖ ≤ min (n ^ (-1000 : ℝ)) (g / 4) ∧
        (∃ (E₀ : ℝ) (Ωt : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩt : star Ωt ⬝ᵥ Ωt = 1),
          (∑ X ∈ supports G Λ R, truncated G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a X) (k X)) *ᵥ Ωt =
            (E₀ : ℂ) • Ωt ∧ 0 ≤ E₀ ∧ E₀ ≤ min (n ^ (-1000 : ℝ)) (g / 4) ∧
          HasGlobalGap (∑ X ∈ supports G Λ R, truncated G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a X) (k X))
            Ωt E₀ (g / 2) ∧
          (∀ w, (∑ X ∈ supports G Λ R, truncated G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a X) (k X)) *ᵥ w =
            (E₀ : ℂ) • w → ∃ z : ℂ, w = z • Ωt) ∧
          (∃ t : ℝ, 0 ≤ t ∧ star Ω ⬝ᵥ Ωt = t) ∧
          √(star (Ωt - Ω) ⬝ᵥ (Ωt - Ω)).re ≤ 2 * √(min (n ^ (-1000 : ℝ)) (g / 4) / g) ∧
          traceDist (pureState Ωt hΩt) (pureState Ω hΩ) ≤
            √(2 * min (n ^ (-1000 : ℝ)) (g / 4) / g)) ∧
        ∀ X ⊆ S₀,
          (∀ Y ∈ crossingLabels G Λ S₀ R ⌈C₁ * log n ^ 2⌉₊ a X,
            truncatedSupport G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a Y) = ball G Λ (a Y) ⌈C₁ * log n ^ 2⌉₊) ∧
          (#(crossingLabels G Λ S₀ R ⌈C₁ * log n ^ 2⌉₊ a X) : ℝ) ≤
            Cb * #(edgeBoundary G Λ X) * ((⌈C₁ * log n ^ 2⌉₊ : ℝ) + 1) ^ m ∧
          (∀ Y ∈ crossingLabels G Λ S₀ R ⌈C₁ * log n ^ 2⌉₊ a X,
            log ((q : ℝ) ^ #(truncatedSupport G Λ S₀ ⌈C₁ * log n ^ 2⌉₊ (a Y))) ≤
              Cb * ((⌈C₁ * log n ^ 2⌉₊ : ℝ) + 1) ^ m) ∧
          cutBudget G q Λ S₀ R ⌈C₁ * log n ^ 2⌉₊ a X ≤
            Cb * (1 + #(edgeBoundary G Λ X)) * ((⌈C₁ * log n ^ 2⌉₊ : ℝ) + 1) ^ (3 * m)) ∧
    ∀ C₂ : ℝ, 0 ≤ C₂ → ∃ CD : ℝ, ∀ (Λ S₀ X : Finset σ) (a : Finset σ → σ) (n D : ℝ),
      (∀ Y ∈ supports G Λ R, a Y ∈ Y) → X ⊆ S₀ → 2 ≤ n → 1 ≤ D →
      (#(edgeBoundary G Λ X) : ℝ) ≤ C₂ * n * D →
      cutBudget G q Λ S₀ R ⌈C₁ * log n ^ 2⌉₊ a X ≤ CD * n * D * log n ^ (6 * m) := by
  -- D4.12: constants `C', c'` of the volume-free bound, fixed before `r₀` and `S₀`
  obtain ⟨C', c', hC', hc', hvol⟩ := step_4_12 hC hc (by norm_num : (0 : ℝ) < 1 / 2) hK m
    (μ V R)
  -- D4.12.7: the choice of `C₁`
  obtain ⟨C₁, hC₁, hC₁n⟩ := step_4_12_7 hC'.le hc' hC₀ hg hs
  -- D4.14: the crossing constant
  obtain ⟨Cb, hCb, hcross⟩ := (step_4_14 G V hV hq R).2 K m hVpoly
  refine ⟨C₁, hC₁, Cb, hCb, ?_, fun C₂ hC₂ => step_4_14_7 G V hV hq R K m hVpoly hC₁ hC₂⟩
  intro Λ a ha Ω hΩ k hk hgap htail n hn S₀ hS₀
  set r₀ := ⌈C₁ * log n ^ 2⌉₊
  set εn := min (n ^ (-1000 : ℝ)) (g / 4)
  -- D4.11.1: `h̃_i ∈ [0, I]`
  have h1 : ∀ X ∈ supports G Λ R, 0 ≤ truncated G Λ S₀ r₀ (a X) (k X) ∧
      truncated G Λ S₀ r₀ (a X) (k X) ≤ 1 := by
    intro X hX
    unfold truncated
    split_ifs
    · exact ⟨(hk X hX).1, (hk X hX).2.1⟩
    · exact ⟨(htail X hX _).1, (htail X hX _).2.1⟩
  -- D4.11.2: the truncation error, D4.12 then the choice of `C₁`
  have h2 : ‖∑ X ∈ supports G Λ R, truncated G Λ S₀ r₀ (a X) (k X) -
      ∑ X ∈ supports G Λ R, k X‖ ≤ εn := by
    refine (hvol G V hV hVpoly R le_rfl Λ a ha k (fun X hX l => (htail X hX l).2.2) r₀ S₀).trans
      ((?_ : _ ≤ C' * C₀ * n ^ s * exp (-(c' * (r₀ : ℝ) ^ (1 / 2 : ℝ)))).trans (hC₁n n hn))
    have := mul_le_mul_of_nonneg_left hS₀ hC'.le
    nlinarith [exp_pos (-(c' * (r₀ : ℝ) ^ (1 / 2 : ℝ)))]
  -- D4.11.3: spectrum and ground vector, D4.13
  have hHF : 0 ≤ ∑ X ∈ supports G Λ R, k X := sum_nonneg fun X hX => (hk X hX).1
  have hHFΩ : (∑ X ∈ supports G Λ R, k X) *ᵥ Ω = 0 := by
    rw [sum_mulVec]
    exact sum_eq_zero fun X hX => (hk X hX).2.2
  have hεn : εn ≤ g / 4 := min_le_right _ _
  obtain ⟨E₀, Ωt, hΩt, hEig, hE0, hE1, -, -, -, -, hgap2, huniq, hphase, hdist, htd⟩ :=
    step_4_13 hΩ hHF hHFΩ hgap (sum_nonneg fun X hX => (h1 X hX).1) h2 hg hεn
  refine ⟨h1, h2, ⟨E₀, Ωt, hΩt, hEig, hE0, hE1, hgap2, huniq, hphase, hdist, htd⟩, ?_⟩
  -- D4.11.4: crossing supports and budgets, D4.14
  intro X hX
  have hr₀ : 1 ≤ r₀ := Nat.one_le_iff_ne_zero.2 fun h => by
    have hlog : 0 < log n := log_pos (by linarith)
    have := Nat.ceil_eq_zero.1 h
    nlinarith [pow_pos hlog 2]
  obtain ⟨hc1, hc2, hc3⟩ := hcross Λ S₀ X r₀ a ha hX hr₀
  exact ⟨fun Y hY => ((step_4_14 G V hV hq R).1 Λ S₀ X r₀ a ha hX hr₀).1 Y hY |>.2.2,
    hc1, hc2, hc3⟩

end AreaLaw
