import OpenAI.Scan.ScannerSelection
import OpenAI.Scan.ActualRoughLower
import OpenAI.Scan.SourceScanScales
import OpenAI.Scan.TypicalReplicaAbsorption
import OpenAI.Scan.BootstrapComparisonBudget
import OpenAI.Scan.BootstrapPrincipalEnergyBounds

/-!
# The bootstrap comparison of the safe-box estimate

The comparison step in the proof of Proposition 9.5 [OAI265, §9.4, eqs. (9.14) and (9.15)]: a
target scanned at total metric weight `W = 4`, with entropy inputs at exponent `e_* < e ≤ e₀`,
has `S(X) ≤ C n^{1+(1-ℓ)e}` for the truncated ground state, `ℓ = ν/100` the fixed improvement
fraction of eq. (9.13).  The rough upper and lower comparisons at the interpolation selected
by Proposition 9.2 give this bound.

## Main statements

* `OpenAI.Scan.sourceScan_bootstrap_entropy_le`: the bootstrap comparison.
* `OpenAI.Scan.exists_bootstrap_comparison_cost_le`: the additive cost of eq. (9.15) is at most
  `C n^{1+(1-ℓ)e}`.

## Implementation notes

Proposition 9.2 selects its round and parameter separately for every remainder `η > 0`;
`OpenAI.Scan.exists_seq_le_add_of_forall_eventually` turns this into one selected point for
every replica count `k`, with a vanishing remainder, so that both rough comparisons are taken
along a single sequence before the limit `k → ∞`.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- A family of values that for every `η > 0` eventually comes within `η` of `c` at some
point admits one point `x k` for every `k` with `f k (x k) ≤ c + r k`, `r k → 0`. -/
theorem exists_seq_le_add_of_forall_eventually {α : Type*} {f : ℕ → α → ℝ} {c : ℝ}
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∃ x, f k x ≤ c + η) :
    ∃ x : ℕ → α, ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k, f k (x k) ≤ c + r k := by
  obtain ⟨-, x₀, -⟩ := (h 1 one_pos).exists
  have : Nonempty α := ⟨x₀⟩
  let g : ℕ → α → ℝ := fun k x => max (f k x - c) 0
  have hbdd : ∀ k, BddBelow (Set.range (g k)) := fun k =>
    ⟨0, by rintro _ ⟨x, rfl⟩; exact le_max_right _ _⟩
  let i : ℕ → ℝ := fun k => ⨅ x, g k x
  have hlt : ∀ k, ∃ x, g k x < i k + 1 / ((k : ℝ) + 1) := fun k =>
    exists_lt_of_ciInf_lt (lt_add_of_pos_right _ Nat.one_div_pos_of_nat)
  choose x hx using hlt
  have hi : Tendsto i atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k =>
      ha.trans_le (le_ciInf fun x => le_max_right _ _), fun b hb => ?_⟩
    filter_upwards [h (b / 2) (half_pos hb)] with k ⟨y, hy⟩
    refine (ciInf_le (hbdd k) y).trans_lt (max_lt ?_ (half_pos hb |>.trans (half_lt_self hb)))
    linarith [half_lt_self hb]
  refine ⟨x, fun k => i k + 1 / ((k : ℝ) + 1), ?_, fun k => ?_⟩
  · simpa using hi.add tendsto_one_div_add_atTop_nhds_zero_nat
  · have := hx k
    have := le_max_left (f k (x k) - c) 0
    simp only [g] at *
    linarith

/-- **The cost of the bootstrap comparison** [OAI265, proof of Proposition 9.5, eq. (9.15) and
lines 772–787].  At the bootstrap exponents of `e₀`, the typical-window, shell, mismatch and
binary-entropy costs `7 (n^{3/5} - log z) - log z + 4 B_sh / z + 4 B_exc + 6 h(τ) / a`, with
`B_sh = C_e (n L^e + n)`, `B_exc = 1 + 3 n D log q`, `z ≥ 1/2` and `0 ≤ τ ≤ 1`, are at most
`C n^{1+(1-ℓ)e}` at every large scale, uniformly in `e_* < e ≤ e₀`. -/
theorem exists_bootstrap_comparison_cost_le {e₀ : ℝ} (he₀ : (Exponents.boxError : ℝ) < e₀)
    (he₀₁ : e₀ < 1) {Ce lq : ℝ} (hCe : 0 ≤ Ce) (hlq : 0 ≤ lq) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ τ z : ℝ, 0 ≤ τ → τ ≤ 1 → 1 / 2 ≤ z →
        let X := bootstrapExponents e₀ he₀ he₀₁
        7 * ((n : ℝ) ^ (3 / 5 : ℝ) - Real.log z) - Real.log z +
            4 * (Ce * ((n : ℝ) * (X.L n : ℝ) ^ e + n)) / z +
            4 * (1 + 3 * (n : ℝ) * (X.D n : ℝ) * lq) +
            2 * 3 * Real.binEntropy τ / (4 / (X.K n : ℝ)) ≤
          C * (n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  obtain ⟨N, hN, hB⟩ := exists_bootstrap_comparison_budget_bound he₀ he₀₁
  refine ⟨(25 + 8 * Ce + 12 * lq) * (5 + Real.log 2 / 4) + 8 * Ce, N, fun n hn e he hee₀ τ z
    hτ0 hτ1 hz => ?_⟩
  intro X
  obtain ⟨hK, ha, hb⟩ := hB n hn
  have hb := hb e he hee₀ τ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hN.trans hn
  have hn0 : (0 : ℝ) < n := one_pos.trans_le hn1
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  set P := (n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e)
  have hℓ1 : BootstrapParameters.ell e₀ < 1 :=
    (BootstrapParameters.parameter_bounds
      (lt_trans (by norm_num [Exponents.boxError]) he₀) he₀₁).2.2.2.1
  have hPn : (n : ℝ) ≤ P := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
          (by nlinarith [mul_pos (sub_pos.2 hℓ1) hepos])
  -- The five terms of the comparison budget.
  set t₁ := (n : ℝ) * (X.L n : ℝ) ^ e
  set t₂ := (n : ℝ) * (X.D n : ℝ)
  set t₃ := (n : ℝ) ^ (3 / 5 : ℝ)
  set t₄ := Real.binEntropy τ / (4 / (X.K n : ℝ))
  have hK0 : (0 : ℝ) < X.K n := by exact_mod_cast hK
  have ht₁ : 0 ≤ t₁ := by positivity
  have ht₂ : 0 ≤ t₂ := by positivity
  have ht₃ : 0 ≤ t₃ := by positivity
  have ht₄ : 0 ≤ t₄ := div_nonneg (Real.binEntropy_nonneg hτ0 hτ1) (by positivity)
  set B₀ := t₁ + t₂ + t₃ + t₄ + 1
  have hB₀P : B₀ ≤ (5 + Real.log 2 / 4) * P := hb
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogz : -Real.log z ≤ Real.log 2 := by
    have := Real.log_le_log (by norm_num) hz
    rw [one_div, Real.log_inv] at this
    linarith
  have hBsh : 0 ≤ Ce * (t₁ + n) := by positivity
  have hdiv : 4 * (Ce * (t₁ + n)) / z ≤ 8 * (Ce * (t₁ + n)) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h1 : Ce * t₁ ≤ Ce * B₀ := mul_le_mul_of_nonneg_left (by linarith) hCe
  have h2 : lq * t₂ ≤ lq * B₀ := mul_le_mul_of_nonneg_left (by linarith) hlq
  have h3 : Ce * (n : ℝ) ≤ Ce * P := mul_le_mul_of_nonneg_left hPn hCe
  have h4 : (25 + 8 * Ce + 12 * lq) * B₀ ≤ (25 + 8 * Ce + 12 * lq) * ((5 + Real.log 2 / 4) * P) :=
    mul_le_mul_of_nonneg_left hB₀P (by positivity)
  have hdiv' : 4 * (Ce * (t₁ + n)) / z ≤ 8 * (Ce * t₁) + 8 * (Ce * n) := by
    linarith [mul_add Ce t₁ (n : ℝ)]
  have hmn : 4 * (1 + 3 * (n : ℝ) * (X.D n : ℝ) * lq) = 4 + 12 * (lq * t₂) := by ring
  have hbin : 2 * 3 * Real.binEntropy τ / (4 / (X.K n : ℝ)) = 6 * t₄ := by ring
  have hexp : (25 + 8 * Ce + 12 * lq) * B₀ = 25 * B₀ + 8 * (Ce * B₀) + 12 * (lq * B₀) := by
    ring
  have hexp' : ((25 + 8 * Ce + 12 * lq) * (5 + Real.log 2 / 4) + 8 * Ce) * P =
      (25 + 8 * Ce + 12 * lq) * ((5 + Real.log 2 / 4) * P) + 8 * (Ce * P) := by ring
  rw [hmn, hbin, hexp']
  linarith


open Classical in
/-- **The bootstrap comparison for a supplied truncated ground state** [OAI265, proof of
Proposition 9.5, eqs. (9.14) and (9.15) and lines 752–787].  Fix `e_* < e ≤ e₀ < 1` and the
bootstrap exponents of `e₀`.  At every large scale, for the collar scan of a target obeying the
test geometry, every unit ground vector `Ωt` of the truncated Hamiltonian with energy at most
`n^{-1000}` and gap at least `g₀`, with a spectral set `E` of its target marginal of mass at
least `1 - n^{-100}` in the window of width `n^{3/5}`, with target entropy at most
`C_e n^{1+e}`, every positive-depth prefix of entropy at most `C_e (n L^e + n)`, and with a
Schmidt–Bell label sequence, has `S_{Ωt}(X) ≤ C n^{1+(1-ℓ)e}`.  The proof selects an
interpolation by Proposition 9.2 at `W = 4`, applies the rough upper and lower comparisons
there, lets `k → ∞`, and takes `τ = n^{-ν/4}`. -/
theorem sourceScan_bootstrap_entropy_le (q R : ℕ) [NeZero q]
    {J Δ Ctr CT Ce g₀ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) (hCtr : 0 < Ctr) (hCT : 0 ≤ CT)
    (hg₀ : 0 < g₀) {e₀ : ℝ} (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1)
    {e : ℝ} (he : (Exponents.boxError : ℝ) < e) (hee₀ : e ≤ e₀) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hA : A ⊆ Λ)
      (hT : T.Nonempty),
      let L := (bootstrapExponents e₀ he₀ he₀₁).L n
      (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
      (∀ d : ℕ, 1 ≤ d → d ≤ L →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * L + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) <
          ambientSupDistance t z) →
    let S := sourceScan (bootstrapExponents e₀ he₀ he₀₁) Ctr R Λ A T hT n
    ∀ (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
      IsAdmissible Λ R J Φ →
    ∀ (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
    ∀ (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (e' gap : ℝ), ‖Ωt‖ = 1 →
      (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ Ωt.ofLp = (e' : ℂ) • Ωt.ofLp →
      ((∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) - (e' : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 ≤ e' → e' ≤ (n : ℝ) ^ (-1000 : ℝ) → g₀ ≤ gap →
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let Xs := S.A.filter fun x => x.val ∈ T
    ∀ (E : Finset (FiniteProduct.Configuration β Xs)) [NeZero E.card],
      1 - (n : ℝ) ^ (-100 : ℝ) ≤
        (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E →
      (∀ i ∈ E,
        Real.exp (-FiniteProduct.entropy β Ωt Xs - (n : ℝ) ^ (3 / 5 : ℝ)) ≤
            (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues i ∧
          (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues i ≤
            Real.exp (-FiniteProduct.entropy β Ωt Xs + (n : ℝ) ^ (3 / 5 : ℝ))) →
      FiniteProduct.entropy β Ωt Xs ≤ Ce * (n : ℝ) ^ (1 + e) →
      (∀ j : Fin (L + 1),
        FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) →
    ∀ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      IsSchmidtBellLabels (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) Ωt e' Xs E ell →
      FiniteProduct.entropy β Ωt Xs ≤
        C * (n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  classical
  set X := bootstrapExponents e₀ he₀ he₀₁
  have he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  have hμ : X.mu < 1 - X.ell := X.mu_lt_one_sub_ell
  set Ce' := max Ce 0
  have hCe'0 : 0 ≤ Ce' := le_max_right _ _
  set ω := (1 - X.ell - X.mu) / 2 with hωdef
  have hω0 : 0 < ω := by rw [hωdef]; linarith
  have hω : ω < 1 - X.ell - X.mu := by rw [hωdef]; linarith
  have hγ : 0 < 1 - X.ell - X.mu := by linarith
  obtain ⟨C₂, Cl, hC₂, N₂, hsel⟩ :=
    exists_sourceScan_selection X q R (J := J) (Ce := Ce' + 2) hJ hΔ hCtr hCT hg₀ hω
  obtain ⟨Nen, -, hen⟩ :=
    exists_bootstrap_energy_expression_bound he₀pos he₀₁ C₂ C₂ Cl Cl hC₂ hC₂
  obtain ⟨Nloss, -, hloss⟩ :=
    exists_bootstrap_comparison_loss_threshold (2 * 3) (1 + C₂) he₀pos he₀₁
  obtain ⟨C, Ncost, hcost⟩ := exists_bootstrap_comparison_cost_le he₀ he₀₁ (Ce := Ce')
    (lq := Real.log q) hCe'0 (Real.log_natCast_nonneg q)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp
    ((eventually_sourceScan_scales X hCtr.le).and ((eventually_rpow_le_bandCount X).and
      ((eventually_le_natCast_rpow hγ 256).and (eventually_le_natCast_rpow hω0 4))))
  refine ⟨C, max (max N₂ Nen) (max (max Nloss Ncost) N₃), ?_⟩
  intro n hn Λ A T _ hA hT L hTcard hrows hclear S Φ hΦ Ω hΩ Ωt e' gap hΩt hE hgap he'0 he'
    hgap₀ β Xs E _ hmass hwin hent hsh ell hell
  obtain ⟨⟨hn2, hr, -, hD1, h4D, hL8⟩, hK32, h256, h4ω⟩ :=
    hN₃ n (le_of_max_le_right (le_of_max_le_right hn))
  have hnN₂ : N₂ ≤ n := le_of_max_le_left (le_of_max_le_left hn)
  have hnEn : Nen ≤ n := le_of_max_le_right (le_of_max_le_left hn)
  have hnL : Nloss ≤ n := le_of_max_le_left (le_of_max_le_left (le_of_max_le_right hn))
  have hnC : Ncost ≤ n := le_of_max_le_right (le_of_max_le_left (le_of_max_le_right hn))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := one_pos.trans_le hn1
  have hK8 : 8 ≤ S.K := by
    have : (8 : ℝ) ≤ X.K n := by linarith
    exact_mod_cast this
  have hK0 : (0 : ℝ) < S.K := by
    have : (8 : ℝ) ≤ S.K := by exact_mod_cast hK8
    linarith
  have hm1 : 1 ≤ X.m n := by omega
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ 8 * X.K n * X.m n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this.trans hL8
  -- The typical mass and the typical dimension.
  set z := (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E
  have hpow100 : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
    have h1 : (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_neg_one] at h1
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have : (n : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hn0 (by norm_num)]; linarith
    linarith
  have hz2 : 1 / 2 ≤ z := by linarith
  have hz0 : 0 < z := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlogz : -Real.log z ≤ Real.log 2 := by
    have := Real.log_le_log (by norm_num) hz2
    rw [one_div, Real.log_inv] at this
    linarith
  have hcard := (abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt Xs E
    ((n : ℝ) ^ (3 / 5 : ℝ)) hz0 hwin).1
  have hXe : X.e = e₀ := rfl
  have hP₁ : (n : ℝ) ^ (1 + e) ≤ (n : ℝ) ^ (1 + X.e) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hXe]; linarith)
  have hP₂ : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (1 + X.e) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hXe]; linarith)
  have hP₃ : (1 : ℝ) ≤ (n : ℝ) ^ (1 + X.e) := Real.one_le_rpow hn1 (by rw [hXe]; linarith)
  have hCe1 : Ce * (n : ℝ) ^ (1 + e) ≤ Ce' * (n : ℝ) ^ (1 + X.e) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hP₁ hCe'0)
  have hlogE : Real.log (E.card : ℝ) ≤ (Ce' + 2) * (n : ℝ) ^ (1 + X.e) := by
    have := (abs_le.mp hcard).2
    nlinarith
  -- The shell inputs.
  have hLe : (L : ℝ) ^ e ≤ (L : ℝ) ^ X.e :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hXe]; exact hee₀)
  have hsh' : ∀ j : Fin (L + 1),
      FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
        Ce' * ((n : ℝ) * (L : ℝ) ^ e + n) := fun j =>
    (hsh j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsh₂ : ∀ j : Fin (X.L n + 1),
      FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
        (Ce' + 2) * ((n : ℝ) * (X.L n : ℝ) ^ X.e + n) := fun j =>
    (hsh' j).trans (mul_le_mul (by linarith) (by gcongr) (by positivity) (by linarith))
  -- Proposition 9.2 at `W = 4`, with the bootstrap energy scale.
  obtain ⟨hm, hM, hsel'⟩ := hsel n hnN₂ Λ A T hA hT hTcard hrows hclear
  let d := E.card
  let a : ℝ := 4 / (S.K : ℝ)
  let nA := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
  let pre : (k : ℕ) → Config k (fun v => Fin (nA v)) → ℂ := fun k =>
    replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
  let defect : ℕ → Fin (S.n * S.m) × ℝ → ℝ := fun k x =>
    ((S.actualChargeScanRound hm hM x.1.val nA
      (S.actualEnergyTerms Φ Ω J Δ L (fun _ => d)) a pre).meanEnergy k x.2 - e') / gap
  set Edef := (1 + C₂) * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2)
  have hEn := hen n hnEn e₀ le_rfl
  dsimp only at hEn
  have hdef : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∃ x, defect k x ≤ Edef + η := by
    intro η hη
    have h := hsel' Φ hΦ Ω hΩ Ωt e' gap hΩt hE he'0 he' hgap₀ E hz2 hlogE hsh₂ ell hell 4
      (by norm_num) h4ω η hη
    filter_upwards [h] with k hk
    obtain ⟨s, p, -, hk⟩ := hk
    exact ⟨(s, p), hk.trans (add_le_add hEn le_rfl)⟩
  obtain ⟨x, r, hr0, hxr⟩ := exists_seq_le_add_of_forall_eventually hdef
  -- The rough lower and upper comparisons along the selected points.
  obtain ⟨ρ, hρ, hlow⟩ := exists_actualScan_suppliedPrevector_rough_lower S hm hM hK8 Φ Ω Δ L
    Ωt e' gap hΩt hE hgap (hg₀.trans_le hgap₀) T E ell hell
  have ha0 : 0 < a := div_pos (by norm_num) hK0
  have h4D' : 4 * S.D ≤ S.m := by
    change 4 * X.D n ≤ X.m n
    omega
  obtain ⟨c, -, hrem, hup⟩ := CollarScan.eventually_actualScan_suppliedPrevector_rough_upper hT S
    rfl rfl hm hM a ha0 (by change 0 < n; omega) hr hD1 h4D' L hL8 hrows Ωt hΩt E ell
    (Ce' * ((n : ℝ) * (L : ℝ) ^ e + n)) hsh' hz0 hell.2.1
  let Nsq : ℕ → ℝ := fun k => Matrix.Transport.filteredNormSq
    ((S.actualChargeData hm hM (x k).1.val).rootPath nA (a / 2) k (x k).2) (pre k)
  set τ := (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)
  obtain ⟨hτ0, hτhalf, hsmall⟩ := hloss n hnL
  have hEdef0 : 0 ≤ Edef := mul_nonneg (by linarith) (Real.rpow_nonneg hn0.le _)
  have haK : a * (S.K : ℝ) = 4 := div_mul_cancel₀ _ hK0.ne'
  have hupper : ∀ᶠ k in atTop, -Real.log (Nsq k) / (k : ℝ) ≤
      2 * Real.log (E.card : ℝ) - Real.log z + 4 * (Ce' * ((n : ℝ) * (L : ℝ) ^ e + n)) / z +
        4 * (1 + 3 * (n : ℝ) * (X.D n : ℝ) * Real.log q) +
        Real.bellOverlapRemainder E.card c S.K k := by
    filter_upwards [hup] with k hk
    obtain ⟨-, -, hk⟩ := hk (x k).1.val (x k).1.isLt (x k).2
    change -Real.log (Nsq k) / (k : ℝ) ≤ 2 * Real.log (E.card : ℝ) - Real.log z +
      (a * (S.K : ℝ)) * (Ce' * ((n : ℝ) * (L : ℝ) ^ e + n) / z +
        (1 + 3 * (n : ℝ) * (X.D n : ℝ) * Real.log q)) +
      Real.bellOverlapRemainder E.card c S.K k at hk
    refine hk.trans (le_of_eq ?_)
    rw [haK]
    ring
  let S' : ℝ := Arealaw.vonNeumann (Matrix.posSemidef_vecMulVec_self_star (fun x =>
    Matrix.compressedTypicalPureState
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β Xs) Ωt) E
      ((Finset.equivFin E).symm x.2, x.1) :
      FiniteProduct.Configuration β Xsᶜ × Fin E.card → ℂ)).traceLeft.isHermitian
  have hlower : ∀ᶠ k in atTop,
      4 * S' - 2 * 3 * (τ * Real.log (E.card : ℝ) + Real.binEntropy τ / a) -
        3 * (defect k (x k) / τ) * max 0 (2 * S') - ρ k ≤ -Real.log (Nsq k) / (k : ℝ) := by
    filter_upwards [hlow] with k hk
    obtain ⟨-, -, hk⟩ := hk (x k).1 (x k).2
    have h' : 4 * S' - 6 * (τ * Real.log (E.card : ℝ) + Real.binEntropy τ / a) -
        3 * (defect k (x k) / τ) * max 0 (2 * S') - ρ k ≤ -Real.log (Nsq k) / (k : ℝ) :=
      hk τ hτ0 hτhalf.le
    linarith
  have key := regionalEntropy_le_of_rough_typical_comparisons Ωt hΩt Xs E
    ((n : ℝ) ^ (3 / 5 : ℝ)) hz0 hwin (C := 3) (τ := τ) (a := a) (Edef := Edef)
    (F := fun k => -Real.log (Nsq k) / (k : ℝ)) (d := fun k => defect k (x k))
    (by norm_num) hτ0 hτhalf ha0 hEdef0 hsmall hrem hρ hr0 (Eventually.of_forall hxr)
    hupper hlower
  exact key.trans (hcost n hnC e he hee₀ τ z hτ0.le (by linarith) hz2)

end OpenAI.Scan
