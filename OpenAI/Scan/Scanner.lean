/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/Scanner.lean` (Apache 2.0). Namespace `TNLean.PEPS.AreaLaw.Scan`
renamed to `OpenAI.Scan`, `## Main results` spelled `## Main statements`, and the
scope-restriction paragraph rewritten for this repository. Statements are unchanged.
-/
import OpenAI.Scan.Budgets
import OpenAI.Scan.EntropyBalance
import OpenAI.Scan.Selection
import OpenAI.Scan.EnergyBalance

/-!
# The scanner estimate, conditional on its inputs (Proposition 9.2)

The step-5 deduction of Proposition 9.2 (`prop:scanner`) from a `ScanData` record: the
integrated entropy balance, the selection of a low-defect charge point, the energy accounting
at that point, and the comparator budgets.

**Scope restriction (inputs as hypotheses):** the conclusions of Lemma 9.1
(`scanner:histories`), Proposition 7.4 (`prop:transport`), Proposition 8.1
(`prop:comparators`), Lemma 2.1 (`lem:continuity`) and Lemma 3.1 (`lem:tail`) for the concrete
scan are the fields of `ScanData`; this module proves the step of the source from those
conclusions to the conclusion of Proposition 9.2. A `ScanData` value is a hypothesis of that
step, never an assumed existence: `scanner_estimate` proves only that its conclusion follows
from those fields, no result here asserts that a `ScanData` exists, and `scanner_estimate` is
not Proposition 9.2 itself. It becomes the source statement once a `ScanData` is constructed
from the scan geometry and the transported states of the same original and truncated ground
vectors. TNLean records the restriction in `docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## Main statements

* `OpenAI.Scan.scanner_estimate`: the conclusion of Proposition 9.2 for every `ScanData`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 9.2, section file `08-scanner.tex`, lines 349–533.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace OpenAI.Scan

open Filter Topology Set

/-- **Scanner estimate from its inputs** (the deduction of Proposition 9.2 from the record
`ScanData`, `08-scanner.tex`, lines 349–533). It is conditional on that record, whose fields are
the conclusions of Lemma 9.1, Propositions 7.4 and 8.1 and Lemmas 2.1 and 3.1, and it is not
Proposition 9.2 itself: no `ScanData` is constructed here. For all sufficiently large `n` and
every `S : ScanData X κ n`, the comparator budgets
`B_sh ≤ C_b (n L^e + n)`, `B_exc ≤ C_b n D`, `𝓑 ≤ C_b n D (log n)^{C_{lb}}` hold, and there is a
remainder `ρ_k → 0`, uniform over the selected round and parameter, such that for every
replica count `k ≥ 1` some charge round and common `p_k ∈ [ε/2, ε]` satisfy
`𝒬(p_k)/(KnD) ≤ δ_n + ρ_k` (`scanner:selected-density`) and
`E_def ≤ C n^ℓ D² W² (log n)^{C_l} (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000} + ρ_k`
(`scanner:energy-output`). The constants and the threshold for `n` depend only on the fixed
exponents and on the constants `κ` of the inputs. They do not depend on the total metric weight
`W = S.W ≥ 1`, which is part of the scan, so `W` may grow with `n` as in
`scanner:final-parameters` (line 843). -/
theorem scanner_estimate (X : ScannerExponents) (κ : ScanConstants) :
    ∃ Cb Clb C Cl Cδ : ℝ, ∀ᶠ n in atTop, ∀ S : ScanData X κ n,
      (S.Bsh ≤ Cb * (n * (X.L n : ℝ) ^ X.e + n) ∧ S.Bexc ≤ Cb * n * X.D n ∧
        S.Bmarg ≤ Cb * n * X.D n * Real.log n ^ Clb) ∧
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k, 1 ≤ k →
        ∃ r ∈ X.chargeRounds n, ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
          (S.round r).chargeDefect k p / (X.K n * n * X.D n) ≤ X.delta S.W Cδ κ.Cl n + ρ k ∧
          S.defectEnergy r k p ≤
            C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * S.W ^ 2 * Real.log n ^ Cl *
                (X.delta S.W Cδ κ.Cl n ^ (1 / 8 : ℝ) + X.eps n + (n : ℝ) ^ (-100 : ℝ)) +
              C * (n : ℝ) ^ (-1000 : ℝ) + ρ k := by
  obtain ⟨C₁, hC₁⟩ := eventually_scaleFacts X
  obtain ⟨Cb, Clb, hB⟩ := exists_budgets X κ
  obtain ⟨Cδ, hCδ, hsel⟩ := exists_selected_density X κ C₁ Cb
  obtain ⟨C, Cl, hE⟩ := exists_defectEnergy_le X κ C₁ Cδ hCδ
  refine ⟨Cb, Clb, C, Cl, Cδ, ?_⟩
  filter_upwards [hC₁, hB, hsel, hE] with n hfacts hb hs he
  intro S
  obtain ⟨hBsh, hBexc, hBmarg, hT⟩ := hb S
  refine ⟨⟨hBsh, hBexc, hBmarg⟩, ?_⟩
  obtain ⟨ρ, hρ0, hρ, hρsel⟩ := hs hfacts S hT
  obtain ⟨Λ, hΛ, hΛE⟩ := he hfacts S
  have hρ8 : Tendsto (fun k ↦ ρ k ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0)] using
      hρ.rpow_const (p := (1 / 8 : ℝ)) (Or.inr (by norm_num))
  refine ⟨fun k ↦ ρ k + Λ * (S.rem k + ρ k ^ (1 / 8 : ℝ)), ?_, ?_⟩
  · simpa using hρ.add ((S.tendsto_rem.add hρ8).const_mul Λ)
  intro k hk
  obtain ⟨r, hr, p, hp, hQ⟩ := hρsel k hk (S.integratedChargeBound hfacts k hk)
  have hextra : 0 ≤ Λ * (S.rem k + ρ k ^ (1 / 8 : ℝ)) :=
    mul_nonneg hΛ (add_nonneg (S.rem_nonneg k) (Real.rpow_nonneg (hρ0 k) _))
  refine ⟨r, hr, p, hp, by linarith, ?_⟩
  have := hΛE r k p (ρ k) hp (hρ0 k) hQ
  linarith [hρ0 k]

end OpenAI.Scan
