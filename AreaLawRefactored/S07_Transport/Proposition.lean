import AreaLawRefactored.S07_Transport.EntropyGain
import AreaLawRefactored.S07_Transport.Energy
import AreaLawRefactored.S07_Transport.Endpoints

/-!
# §7.4 Proposition 7.4

Digest `digest/07-transport.md` D7.14, D7.27, paper `paper/sections/06-transport.tex` 377–779.
Over an arbitrary finite site type with arbitrary local dimensions, arbitrary `k`; no geometry.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Set Filter Topology Entropy

namespace AreaLaw.Transport

universe u

/-- D7.14 **Proposition 7.4** (entropy and energy transport). Fix a finite `𝒱`, history and
choice trees, partitions with cross-band commutation (D7.9), `a > 0`, contractions `h_i` with
designated supports (D7.11). Let `ℓ` bound `log(e dim ·)` of every transferred subsystem and of
every `D_i` with `𝒥_i ≠ ∅`, with `a ℓ` small (D7.10). For every `k` and nonzero `pre ∈ 𝒮_k`,
`s = 1/4`, `N(p) = ‖𝓜(p)^{-s} pre‖`, `v(p) = 𝓜(p)^{-s} pre / N(p)`; for `0 < p < 1`, `Φ_j` the
normalized map of leaf `j` (Lemma 7.2), `σ_{j,u} = Φ_j^*(|𝓜^{-iu} v⟩⟨𝓜^{-iu} v|)`,
`σ_{h,u}` the state at `(h, old)`, `C_h = A_h^{-1/2} B_h A_h^{-1/2}`:
(a) `-∂_p log N(p)² = ∑_h w_h ∫ m_s(u) Tr(σ_{h,u} log C_h) du`;
(b) there is `β_k = O_fixed(log(k+1))`, independent of `p` and `pre`, with
`-∂_p log N² ≥ ka ∑_{h,g} w_h ∫ m_s(u) ∫ ∑_c q_{c|h} η_{h,c,g}(θ) dμ_{σ_{h,u}}(θ) du
  − C k a K a^{1/4} ℓ^C − β_k`;
(c) if `H̄ pre = E₀ pre`:
`⟨v, H̄ v⟩ ≤ 2E₀ + C a² ℓ^C ∑_i W_i(p) ∑_{j∈𝒥_i} π_j ∫ m_s(u) ∫ η_{i,j}(θ)^{1/8} dμ_{σ_{j,u}}(θ) du
  + o_k(1)`,
the `o_k(1)` uniform in `p ∈ (0,1)`, in `pre` and in the replica states. `C` and the exponents are
universal; only `β_k` and the rate of `o_k(1)` depend on the fixed data. (b) may be integrated
over any closed subinterval of `[0,1]` using the continuous endpoint values of `N`. -/
theorem prop_7_4 :
    ∃ c₀ Cg e Ce : ℝ, 0 < c₀ ∧ 0 < Cg ∧ 0 < Ce ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)] {K : ℕ}
        {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
        [∀ h, DecidableEq (C h)] (R : Round V K H C) {ι : Type*} [Fintype ι]
        (E : EnergyTerms V n ι), R.IsAdmissible → R.SupportCompatible E →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, R.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim (n := n) (R.move h c g).subsystem ≤ ℓ) →
        (∀ i, (R.splitLeaves E i).Nonempty → logDim (n := n) (E.support i) ≤ ℓ) →
      ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧ Tendsto r atTop (𝓝 0) ∧
        ∀ (k : ℕ) (pre : Config n k → ℂ), pre ∈ Replicas.S (fun v => Fin (n v)) k →
          pre ≠ 0 →
          (∀ p : I, 0 < (p : ℝ) → (p : ℝ) < 1 →
            -- (a)
            HasDerivAt (fun q => -Real.log (R.normSq n (a / 2) k pre q))
              (R.exactDerivative n (a / 2) k pre p) p ∧
            (∀ j u, IsSymDensity n (R.state n (a / 2) k pre p j u)) ∧
            -- (b)
            (k : ℝ) * a * R.entropyGain n (a / 2) k pre p -
                Cg * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ e - β k ≤
              R.exactDerivative n (a / 2) k pre p ∧
            -- (c)
            ∀ E₀ : ℝ, E.Hbar k *ᵥ pre = (E₀ : ℂ) • pre →
              (star (R.v n (a / 2) k pre p) ⬝ᵥ (E.Hbar k *ᵥ R.v n (a / 2) k pre p)).re ≤
                2 * E₀ + Ce * a ^ 2 * ℓ ^ 4 * R.energyError n E (a / 2) k pre p + r k) ∧
          -- endpoints
          Continuous (fun q => R.normSq n (a / 2) k pre q) ∧
          ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
            IntervalIntegrable (fun p => R.exactDerivative n (a / 2) k pre
                (projIcc 0 1 zero_le_one p)) volume p₀ p₁ ∧
            Real.log (R.normSq n (a / 2) k pre p₀) - Real.log (R.normSq n (a / 2) k pre p₁) =
              ∫ p in p₀..p₁, R.exactDerivative n (a / 2) k pre (projIcc 0 1 zero_le_one p) := by
  obtain ⟨c₁, Cg, e, hc₁, hCg, Hb⟩ := step_7_20
  obtain ⟨c₂, Ce, hc₂, hCe, Hc⟩ := step_7_25
  refine ⟨min c₁ c₂, Cg, e, Ce, lt_min hc₁ hc₂, hCg, hCe, ?_⟩
  intro V _ _ n _ K H _ _ C _ _ R ι _ E hR hE a ℓ ha hℓ haℓ hcomm hmove hsplit
  obtain ⟨b, -, -, -, hβ, hb⟩ := Hb R hR ha hℓ (haℓ.trans (min_le_left _ _)) hcomm hmove
  obtain ⟨r, hr, hc⟩ := Hc V n R E hR hE ha hℓ (haℓ.trans (min_le_right _ _)) hcomm hsplit
  have ht : (0 : ℝ) ≤ a / 2 := by positivity
  refine ⟨_, r, hβ, hr, fun k pre hpreS hpre => ⟨fun p hp0 hp1 => ?_, ?_, ?_⟩⟩
  · -- D7.27: one state `σ_{j,u}` serves (a), (b) and (c)
    have hp : (p : ℝ) ∈ Ioo 0 1 := ⟨hp0, hp1⟩
    obtain ⟨hD, hEq, hσ⟩ := R.step_7_16 hR ht (hcomm k) hpreS hpre hp
    -- (a): D7.15–D7.16
    refine ⟨hEq ▸ hD, hσ, ?_, ?_⟩
    -- (b): D7.17–D7.20
    · exact hb k pre hpreS hpre p hp0 hp1
    -- (c): D7.21–D7.25
    · exact hc k pre hpreS hpre p hp0 hp1 hσ
  -- D7.26
  · exact (R.continuous_normSq hR ht (hcomm k) pre).1
  · exact fun p₀ p₁ h0 h01 h1 =>
      R.log_normSq_sub_eq_integral hR ht (hcomm k) hpreS hpre h0 h01 h1

end AreaLaw.Transport
