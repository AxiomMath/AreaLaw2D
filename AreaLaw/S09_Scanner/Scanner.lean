import AreaLaw.S09_Scanner.Scanner.Energy

/-!
# §9.2 Proposition 9.2: the scanner estimate (D9.9)

Digest `digest/09-scanner.md` D9.9–D9.13, paper `paper/sections/08-scanner.tex` 349–533.
Graph-level (Map.md, Dimension: `any d`): a simple graph with ball growth
`V r ≤ K₀ (r + 1)^{m₀}` and a depth function. The entropy cost `𝒬(p)` and the gain (D9.10,
D9.11) are in `Scanner/Entropy.lean`, the selection (D9.12) in `Scanner/Selection.lean`, the
energy at the selected point (D9.13) in `Scanner/Energy.lean`.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Finset
open OpenAI (pureState HasGlobalGap)

namespace AreaLaw.Scanner

open Comparators
open Transport (Round EnergyTerms)

universe u

/-! ## Log-dimensions of physical regions -/

section LogDim

variable {Λ : Type*} [DecidableEq Λ] {q : ℕ} [NeZero q] {d : ℕ} [NeZero d]

omit [NeZero q] [NeZero d] in
theorem card_reg_physReg (Q : Finset Λ) :
    Fintype.card (Reg (fun v => Fin (dims (fun _ : Λ => q) d v)) (physReg Q)) = q ^ #Q := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_coe_sort (physReg Q) (fun v => dims (fun _ : Λ => q) d v), physReg,
    prod_map]
  exact prod_const q

omit [NeZero d] in
theorem logDim_physReg (Q : Finset Λ) :
    Transport.logDim (n := dims (fun _ : Λ => q) d) (physReg Q) = 1 + #Q * Real.log q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [Transport.logDim, AreaLaw.ℓ, card_reg_physReg, Nat.cast_pow,
    Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]

theorem logDim_mono {x y : Finset (Site Λ)} (h : x ⊆ y) :
    Transport.logDim (n := dims (fun _ : Λ => q) d) x ≤
      Transport.logDim (n := dims (fun _ : Λ => q) d) y := by
  have h1 := one_le_card_reg (n := dims (fun _ : Λ => q) d) x
  have h2 := log_card_reg_mono (n := dims (fun _ : Λ => q) d) h
  simp only [Transport.logDim, AreaLaw.ℓ]
  have h3 := one_le_card_reg (n := dims (fun _ : Λ => q) d) y
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity),
    Real.log_mul (Real.exp_pos 1).ne' (by positivity)]
  linarith

end LogDim

/-! ## Regions of the domain type -/

section Regions

variable {σ : Type*} [DecidableEq σ] {Λ : Finset σ}

theorem up_subtype_eq {S : Finset σ} (h : S ⊆ Λ) : up (S.subtype (· ∈ Λ)) = S := by
  rw [up, subtype_map, filter_true_of_mem h]

omit [DecidableEq σ] in
theorem up_mono {Q Q' : Finset Λ} (h : Q ⊆ Q') : up Q ⊆ up Q' := Finset.map_subset_map.2 h

end Regions

/-! ## The typical set -/

section Typical

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : PhysData n} {X : Finset V}
  (E : TypicalSet D X)

/-- D8.2: `0 < z ≤ 1` and `log d_* ≤ S(X) + w` (every typical `p_i ≥ e^{-S(X) - w}`). -/
theorem typicalSet_log_d_le : 0 < E.z ∧ E.z ≤ 1 ∧ Real.log E.d ≤ D.S X + E.w := by
  have hp0 (j) : 0 ≤ D.p X j := (D.state.restrict (subset_univ X)).psd.eigenvalues_nonneg j
  have hsum1 : ∑ j, D.p X j = 1 := (D.state.restrict (subset_univ X)).sum_eigenvalues_eq_one
  have hz1 : E.z ≤ 1 := by
    rw [← hsum1]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => hp0 j
  have hlow : (E.d : ℝ) * Real.exp (-D.S X - E.w) ≤ E.z := by
    rw [TypicalSet.z, TypicalSet.d, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => E.lower i hi
  have hd : (0 : ℝ) < E.d := by exact_mod_cast E.nonempty.card_pos
  have hz0 : 0 < E.z := lt_of_lt_of_le (by positivity) hlow
  refine ⟨hz0, hz1, ?_⟩
  have h := Real.log_le_log (by positivity) (hlow.trans hz1)
  rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at h
  linarith

end Typical

/-! ## The terms of the truncated Hamiltonian, indexed by the labelled terms -/

section Terms

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {n : Λ → ℕ} {N : ℕ} {ι : Type*} [Fintype ι]

/-- The energy terms `h̃_i` indexed through `e : Fin N ≃ ι`. -/
noncomputable def termsOn (Et : EnergyTerms Λ n (Fin N)) (e : Fin N ≃ ι) : EnergyTerms Λ n ι where
  support i := Et.support (e.symm i)
  op i := Et.op (e.symm i)
  nonneg _ := Et.nonneg _
  le_one _ := Et.le_one _

theorem Hbar_termsOn (Et : EnergyTerms Λ n (Fin N)) (e : Fin N ≃ ι) (k : ℕ) :
    Et.Hbar k = (termsOn Et e).Hbar k :=
  (e.symm.sum_comp fun i => Et.hbar k i).symm

end Terms

/-! ## Arithmetic of the scales -/

section Arith

/-- D9.12.6: the selected density `δ = (B_init + B_fin + ∑ Err)/(rate) ≤ C n^ν (n^{e-μ} +
a^{1/4} (log n)^C)`. -/
theorem delta_le {n m K W a c₁ ε e μ ν A1 Cg XU LT LCl Bep Cδ : ℝ} (hn : 1 ≤ n) (hm : 0 < m)
    (hK : 0 < K) (hW : 1 ≤ W) (haK : a * K = W) (ha : 0 < a) (hc₁ : 0 < c₁) (hε : ε = n ^ (-ν))
    (hmμ : n ^ μ / 2 ≤ m) (hA1 : 0 ≤ A1) (hCg : 0 ≤ Cg) (hXU : XU ≤ W * A1 * n ^ (1 + e))
    (hLTl : LT ≤ Bep * LCl) (hBep : 0 ≤ Bep)
    (hCδ : (4 * A1 + 4 * Cg * Bep) / c₁ ≤ Cδ) (hLCl : 0 ≤ LCl) :
    (XU + 2 * n * m * (Cg * a * K * a ^ (1 / 4 : ℝ) * LT)) / (n * m * (ε / 2) * a * c₁ * K) ≤
      Cδ * n ^ ν * (n ^ (e - μ) + a ^ (1 / 4 : ℝ) * LCl) := by
  have hn0 : 0 < n := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεν : ε * n ^ ν = 1 := by rw [hε, ← Real.rpow_add hn0]; simp
  have hnμ : 0 < n ^ μ := Real.rpow_pos_of_pos hn0 _
  have heμ : n ^ (1 + e) = n * n ^ μ * n ^ (e - μ) := by
    rw [mul_assoc, ← Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]
    ring_nf
  have ha4 : 0 ≤ a ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha.le _
  have hden : 0 < n * m * (ε / 2) * a * c₁ * K := by positivity
  rw [div_le_iff₀ hden]
  have hk1 : n * m * (ε / 2) * a * c₁ * K = n * m * ε * c₁ * W / 2 := by rw [← haK]; ring
  rw [hk1]
  -- the first term: `XU ≤ W A1 n^{1+e} = W A1 n n^μ n^{e-μ} ≤ 2 W A1 n m n^{e-μ}`
  have h1 : XU ≤ 2 * W * A1 * n * m * n ^ (e - μ) := by
    refine hXU.trans ?_
    rw [heμ]
    have : n ^ μ ≤ 2 * m := by linarith
    have h0 : 0 ≤ W * A1 * n * n ^ (e - μ) := by positivity
    nlinarith
  have h2 : 2 * n * m * (Cg * a * K * a ^ (1 / 4 : ℝ) * LT) =
      2 * n * m * W * Cg * a ^ (1 / 4 : ℝ) * LT := by rw [← haK]; ring
  rw [h2]
  have h3 : Cδ * n ^ ν * (n ^ (e - μ) + a ^ (1 / 4 : ℝ) * LCl) * (n * m * ε * c₁ * W / 2) =
      Cδ * c₁ * (n * m * W / 2) * (n ^ (e - μ) + a ^ (1 / 4 : ℝ) * LCl) * (ε * n ^ ν) := by ring
  rw [h3, hεν, mul_one]
  have hC : 4 * A1 + 4 * Cg * Bep ≤ Cδ * c₁ := by rwa [div_le_iff₀ hc₁] at hCδ
  have hp : 0 ≤ n * m * W / 2 := by positivity
  have hq : 0 ≤ n ^ (e - μ) := Real.rpow_nonneg hn0.le _
  have h4 : LT * a ^ (1 / 4 : ℝ) ≤ Bep * LCl * a ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right hLTl ha4
  have h5 : (4 * A1 + 4 * Cg * Bep) * (n * m * W / 2) * (n ^ (e - μ) + a ^ (1 / 4 : ℝ) * LCl) ≤
      Cδ * c₁ * (n * m * W / 2) * (n ^ (e - μ) + a ^ (1 / 4 : ℝ) * LCl) := by
    gcongr
  have h6 : 0 ≤ 4 * Cg * Bep * (n * m * W / 2) * n ^ (e - μ) := by positivity
  have h7 : 0 ≤ 4 * A1 * (n * m * W / 2) * (a ^ (1 / 4 : ℝ) * LCl) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * n * m * W * Cg)]

/-- D9.13.4–D9.13.5: the energy bound at the selected point in the form of Proposition 9.2. -/
theorem edef_le {E₀ g Ce a ℓ₇ C₂ Dn m K n W X Xc Z A₁ ε N100 N1000 B7 LN2 LN8 LCl nℓ C : ℝ}
    (hg : 0 < g) (hE₀ : E₀ ≤ N1000) (hN1000 : 0 ≤ N1000) (hCe : 0 ≤ Ce) (hC₂ : 0 ≤ C₂)
    (hm : 0 < m) (hK : 0 < K) (hn : 0 < n) (hDn : 0 ≤ Dn)
    (haK : a * K = W) (hnmK : n / (m * K) ≤ 32 * nℓ)
    (hX0 : 0 ≤ X) (hX : X ≤ Xc) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2 * B7 * LN2) (hA₁ : 0 ≤ A₁)
    (hε : 0 ≤ ε) (hN100 : 0 ≤ N100) (hB7 : 0 ≤ B7) (hℓ₇ : 0 ≤ ℓ₇) (hℓ4 : ℓ₇ ^ 4 ≤ B7 ^ 4 * LN8)
    (hLN8 : LN8 ≤ LCl) (hLN28 : LN8 * LN2 ≤ LCl) (hLN80 : 0 ≤ LN8)
    (hnℓ : 0 ≤ nℓ)
    (hC : 2 / g * (32 * Ce * C₂ * B7 ^ 4 * (A₁ + C₂ * B7)) ≤ C) (hC' : 2 / g ≤ C) :
    (E₀ + Ce * a ^ 2 * ℓ₇ ^ 4 * (C₂ * Dn / m) * (K * n * Dn) *
        (X * A₁ + C₂ * (Z / 2) * (ε + N100))) / (g / 2) ≤
      C * nℓ * Dn ^ 2 * W ^ 2 * LCl * (Xc + ε + N100) + C * N1000 := by
  -- D9.13.4: `a² (D/m) K n D = W² n D²/(mK) ≤ 32 W² n^ℓ D²`
  have h1 : a ^ 2 * (Dn / m) * (K * n * Dn) ≤ 32 * W ^ 2 * nℓ * Dn ^ 2 := by
    have e : a ^ 2 * (Dn / m) * (K * n * Dn) = (a * K) ^ 2 * Dn ^ 2 * (n / (m * K)) := by
      have hm0 : m ≠ 0 := hm.ne'
      have hK0 : K ≠ 0 := hK.ne'
      field_simp
    rw [e, haK]
    have h := mul_le_mul_of_nonneg_left hnmK (by positivity : 0 ≤ W ^ 2 * Dn ^ 2)
    linarith
  have hXc : 0 ≤ Xc := hX0.trans hX
  have hL : 0 ≤ LCl := hLN80.trans hLN8
  have hY : X * A₁ + C₂ * (Z / 2) * (ε + N100) ≤ Xc * A₁ + C₂ * (B7 * LN2) * (ε + N100) := by
    have h2 : C₂ * (Z / 2) ≤ C₂ * (B7 * LN2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₂
    have h3 := mul_le_mul_of_nonneg_right h2 (add_nonneg hε hN100)
    have h4 := mul_le_mul_of_nonneg_right hX hA₁
    linarith
  have hY0 : 0 ≤ X * A₁ + C₂ * (Z / 2) * (ε + N100) :=
    add_nonneg (mul_nonneg hX0 hA₁) (mul_nonneg (mul_nonneg hC₂ (by linarith))
      (add_nonneg hε hN100))
  have hP : Ce * a ^ 2 * ℓ₇ ^ 4 * (C₂ * Dn / m) * (K * n * Dn) =
      Ce * C₂ * ℓ₇ ^ 4 * (a ^ 2 * (Dn / m) * (K * n * Dn)) := by ring
  have hP0 : 0 ≤ a ^ 2 * (Dn / m) * (K * n * Dn) := by positivity
  have hP1 : Ce * C₂ * ℓ₇ ^ 4 * (a ^ 2 * (Dn / m) * (K * n * Dn)) ≤
      Ce * C₂ * (B7 ^ 4 * LN8) * (32 * W ^ 2 * nℓ * Dn ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hℓ4 (mul_nonneg hCe hC₂)) h1 hP0
      (mul_nonneg (mul_nonneg hCe hC₂) (mul_nonneg (pow_nonneg hB7 4) hLN80))
  have hQ1 : Xc * A₁ * LN8 + C₂ * B7 * (LN8 * LN2) * (ε + N100) ≤
      (A₁ + C₂ * B7) * LCl * (Xc + ε + N100) := by
    have h5 := mul_le_mul_of_nonneg_left hLN8 (mul_nonneg hXc hA₁)
    have h6 := mul_le_mul_of_nonneg_left hLN28
      (mul_nonneg (mul_nonneg hC₂ hB7) (add_nonneg hε hN100))
    nlinarith [mul_nonneg (mul_nonneg hA₁ hL) (add_nonneg hε hN100),
      mul_nonneg (mul_nonneg (mul_nonneg hC₂ hB7) hL) hXc]
  have hR0 : 0 ≤ 32 * Ce * C₂ * B7 ^ 4 * (nℓ * Dn ^ 2 * W ^ 2) := by positivity
  have hmain : Ce * a ^ 2 * ℓ₇ ^ 4 * (C₂ * Dn / m) * (K * n * Dn) *
      (X * A₁ + C₂ * (Z / 2) * (ε + N100)) ≤
      32 * Ce * C₂ * B7 ^ 4 * (A₁ + C₂ * B7) * (nℓ * Dn ^ 2 * W ^ 2 * LCl * (Xc + ε + N100)) := by
    rw [hP]
    calc Ce * C₂ * ℓ₇ ^ 4 * (a ^ 2 * (Dn / m) * (K * n * Dn)) *
          (X * A₁ + C₂ * (Z / 2) * (ε + N100))
        ≤ Ce * C₂ * (B7 ^ 4 * LN8) * (32 * W ^ 2 * nℓ * Dn ^ 2) *
          (Xc * A₁ + C₂ * (B7 * LN2) * (ε + N100)) :=
          mul_le_mul hP1 hY hY0 (le_trans (mul_nonneg (mul_nonneg (mul_nonneg hCe hC₂)
            (pow_nonneg hℓ₇ 4)) hP0) hP1)
      _ = 32 * Ce * C₂ * B7 ^ 4 * (nℓ * Dn ^ 2 * W ^ 2) *
          (Xc * A₁ * LN8 + C₂ * B7 * (LN8 * LN2) * (ε + N100)) := by ring
      _ ≤ 32 * Ce * C₂ * B7 ^ 4 * (nℓ * Dn ^ 2 * W ^ 2) *
          ((A₁ + C₂ * B7) * LCl * (Xc + ε + N100)) := mul_le_mul_of_nonneg_left hQ1 hR0
      _ = _ := by ring
  have hQ0 : 0 ≤ nℓ * Dn ^ 2 * W ^ 2 * LCl * (Xc + ε + N100) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hK' : 32 * Ce * C₂ * B7 ^ 4 * (A₁ + C₂ * B7) ≤ C * (g / 2) := by
    have h := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ g / 2)
    have e : 2 / g * (32 * Ce * C₂ * B7 ^ 4 * (A₁ + C₂ * B7)) * (g / 2) =
        32 * Ce * C₂ * B7 ^ 4 * (A₁ + C₂ * B7) := by field_simp
    linarith
  have h1g : 1 ≤ C * (g / 2) := by
    have h := mul_le_mul_of_nonneg_right hC' (by positivity : 0 ≤ g / 2)
    have e : 2 / g * (g / 2) = 1 := by field_simp
    linarith
  have ha' := mul_le_mul_of_nonneg_right hK' hQ0
  have hb' := mul_le_mul_of_nonneg_right h1g hN1000
  have eR : (C * nℓ * Dn ^ 2 * W ^ 2 * LCl * (Xc + ε + N100) + C * N1000) * (g / 2) =
      C * (g / 2) * (nℓ * Dn ^ 2 * W ^ 2 * LCl * (Xc + ε + N100)) + C * (g / 2) * N1000 := by
    ring
  rw [eR]
  linarith

end Arith

/-! ## Proposition 9.2 -/

set_option maxHeartbeats 1600000 in
-- one declaration assembles the comparator data, Propositions 7.4 and 8.1 and Lemma 9.1 at `n`
/-- D9.9 **Proposition 9.2** (the scanner estimate). Assume `scanner:scales`
(`0 < ℓ < 1`, `0 < κ < μ < 1 - ℓ`), `scanner:test-geometry`, `0 < e < 1` with `κ ≤ e`, and
`S_Ω(X) ≤ C_e n^{1+e}`, `S_Ω(Q_j) ≤ C_e (n L^e + n)` (`0 ≤ j ≤ L`). Let `ε = n^{-ν}`, `ν > 0`
fixed, `a (r₀ + 1)^{m₀}` sufficiently small (`a r₀²` on `ℤ²`). Build the auxiliary systems, label
sector and `pre` as in Proposition 8.1 with width `w = n^{3/5}`. For every sufficiently large
replica count `k` there are a charge round and a common `p_k ∈ [ε/2, ε]` such that
`v_k = 𝓜^{-s} pre / N`, `s = 1/4`, has
`E_def,k = (⟨v_k, \overline{H̃} v_k⟩ - Ẽ₀)/g̃ ≤ C n^ℓ D² W² (log n)^C (δ_n^{1/8} + ε + n^{-100})
  + C n^{-1000} + o_k(1)`, `δ_n = C_e ε^{-1} (n^{e-μ} + a^{1/4} (log n)^C)`.
All norm comparisons of Proposition 8.1 hold at the selected point with `B_sh ≤ C_e (nL^e + n)`,
`B_exc ≤ C n D`, `𝓑 ≤ C n D (log n)^C`; the sharp ones further need `a √𝓑 ≤ c`. The finite
system, `n`, the scan and all auxiliary dimensions are fixed before `k → ∞`; remainders are
uniform over the selected round and `p` (which may depend on `k`). Constants depend on the
exponents and `C_e`. -/
theorem prop_9_2 :
    ∀ {σ : Type u} [DecidableEq σ] [Nonempty σ] (G : SimpleGraph σ) [DecidableRel G.Adj]
      (V : ℕ → ℕ),
      (∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(GraphDomain.ball G Λ x r) ≤ V r) →
      ∀ (K₀ : ℝ) (m₀ : ℕ), 0 ≤ K₀ → (∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) →
      ∀ (q : ℕ) [NeZero q] (R : ℕ) (J Δ : ℝ), 0 < Δ →
      ∀ (ℓ κ μ ν e Ce CT : ℝ), 0 < ℓ → ℓ < 1 → 0 < κ → κ < μ → μ < 1 - ℓ → 0 < ν →
        0 < e → e < 1 → κ ≤ e → 0 < Ce → 0 < CT →
      ∃ (C₁ c Crl csh Csu Csl C₀ c₀ C Cl Cm : ℝ) (n₀ : ℕ), 0 < C₁ ∧ 0 < c ∧ 0 < csh ∧
        0 < Csl ∧ 0 < Csu ∧ 0 < Crl ∧ 0 < Cm ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ W : ℝ, 1 ≤ W → a ℓ μ W n * ((r₀ C₁ n : ℝ) + 1) ^ m₀ ≤ c →
        ∀ (Λ : Finset σ)
          (Φ : (X : Finset σ) → Matrix (Reg (fun _ : σ => Fin q) X)
            (Reg (fun _ : σ => Fin q) X) ℂ),
          GraphDomain.IsAdmissible G Λ R J Φ →
        ∀ (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
          GraphDomain.hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω →
          HasGlobalGap (GraphDomain.hamiltonian Λ Φ) Ω E₀ Δ →
        ∀ (A : Finset σ) (hA : A ⊆ Λ) (dep : σ → ℕ),
          TestGeometry G Λ A dep CT n (L ℓ n) (r₀ C₁ n) →
          (pureState Ω hΩ).regionEntropy
              ((filter_subset _ A).trans hA : A.filter (fun x => dep x = 0) ⊆ Λ) ≤
            Ce * (n : ℝ) ^ (1 + e) →
          (∀ j ≤ L ℓ n, (pureState Ω hΩ).regionEntropy
              ((filter_subset _ A).trans hA : A.filter (fun x => 0 < dep x ∧ dep x ≤ j) ⊆ Λ) ≤
            Ce * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n)) →
        ∃ (aY : Finset σ → σ) (hm : 0 < m μ n) (hM : 0 < Mn Cm n (D κ n))
          (Dt : PhysData (fun _ : Λ => q))
          (E : TypicalSet Dt ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)))
          (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) (𝓡 : Finset (Finset Λ))
          (Bsh Bexc 𝓑 : ℝ),
          -- D9.9.1: transfer `Ω → Ω̃`
          (∀ Q : Finset Λ,
            |Dt.S Q - (pureState Ω hΩ).regionEntropy (up_subset Q)| ≤
              (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
          (∀ Q Q' : Finset Λ, Disjoint Q Q' →
            |Dt.I Q Q' - (pureState Ω hΩ).mutualInfo (up_subset Q) (up_subset Q')| ≤
              (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
          -- D9.9.2: comparator data
          E.w = (n : ℝ) ^ (3 / 5 : ℝ) ∧ 1 - (n : ℝ) ^ (-100 : ℝ) ≤ E.z ∧
          PrefixData Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ 𝓡 Bsh Bexc ∧
          Bsh ≤ C * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n) ∧ Bexc ≤ C * n * D κ n ∧
          MgfData Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ C₀ c₀ 𝓑 ∧
          𝓑 ≤ C * n * D κ n * Real.log n ^ Cl ∧
          -- D9.28.2: the far region contains `Λ \ S₀`
          (∀ s g, (Λ \ A.filter fun x => dep x ≤ L ℓ n).subtype (· ∈ Λ) ⊆
            (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ.V s g) ∧
          -- the norm comparisons of Proposition 8.1
          RoughUpper Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ E (a ℓ μ W n) l Bsh Bexc ∧
          (∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
            RoughLower Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ E Crl (a ℓ μ W n) τ l) ∧
          (a ℓ μ W n ≤ csh / Real.sqrt 𝓑 →
            SharpUpper Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ E Csu (a ℓ μ W n) 𝓑 l ∧
            ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
              SharpLower Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ E Csl (a ℓ μ W n) τ
                𝓑 l) ∧
          -- the selected point: a charge round `t` and `p_k ∈ [ε/2, ε]`
          ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
            ∃ t : Fin (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).T, t.1 % 2 = 1 ∧
            ∃ p : unitInterval, (n : ℝ) ^ (-ν) / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (-ν) ∧
              Edef Dt (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ E
                ((((scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).round t).tree p).map
                  (Sigma.mk t)) (a ℓ μ W n) k (l k) ≤
                C * (n : ℝ) ^ ℓ * (D κ n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
                    ((C * (n : ℝ) ^ ν * ((n : ℝ) ^ (e - μ) +
                        a ℓ μ W n ^ (1 / 4 : ℝ) * Real.log n ^ Cl)) ^ (1 / 8 : ℝ) +
                      (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) +
                  C * (n : ℝ) ^ (-1000 : ℝ) + r k := by
  intro σ _ _ G _ V hV K₀ m₀ hK₀ hVK q _ R J Δ hΔ ℓ κ μ ν e Ce CT hℓ hℓ1 hκ hκμ hμ hν he he1
    hκe hCe hCT
  -- D9.3: the truncated system (Proposition 4.5)
  obtain ⟨g, C₁, Cb, hg, hC₁, hCb, hcut, Htr⟩ := step_9_3 G V hV hK₀ m₀ hVK q R J hΔ hCT.le
  -- D9.8: Lemma 9.1
  obtain ⟨Cm, C₂, c₁, n₁, hCm, hC₂, hc₁, hsc, hitems, htails⟩ :=
    lemma_9_1 G V hV K₀ m₀ hK₀ hVK R ℓ κ μ CT C₁ hℓ hℓ1 hκ hκμ hμ hCT hC₁
  obtain ⟨n₂, htail⟩ := htails 100 (by norm_num)
  -- D9.9.1, D9.9.2
  obtain ⟨n₃, htr⟩ := step_9_9_1 (σ := σ) q hg
  obtain ⟨n₄, htyp⟩ := step_9_9_2_typical G hV q R (C₁ := C₁) (Cb := Cb) hg hcut
  obtain ⟨CD, hmgf⟩ := step_9_9_2_mgf.{u, 0} G q R (Cb := Cb) hg hcut hC₂.le
  obtain ⟨n₅, hpref⟩ := step_9_9_2_prefix.{u, 0} G q R (C₁ := C₁) (Cb := Cb) (m₀ := m₀) hg hCT.le
  obtain ⟨n₆, hn₆⟩ := eventually_rpow_neg_mul_le hCT.le
  -- D8.8: Proposition 8.1
  obtain ⟨a₀, Crl, ha₀, hCrl, H81⟩ := prop_8_1.{u, 0}
  obtain ⟨csh, Csu, Csl, hcsh, hCsu, hCsl, H81'⟩ :=
    H81 (1024 * Real.exp 1 / g) (32 * √(1 + 2 / g))⁻¹ (by positivity) (by positivity)
  -- D7.14: Proposition 7.4
  obtain ⟨c₇, Cg, e₇, Ce₇, hc₇, hCg, hCe₇, H74⟩ := Transport.prop_7_4.{u}
  -- the scales of D9.2 for large `n`
  have hev := (eventually_scales hℓ hκ hκμ hμ hC₁).and
    ((eventually_rpow_le (by linarith : μ < 1 - ℓ) 32).and
      ((eventually_le_rpow (hκ.trans hκμ) 2).and (eventually_ge_atTop 3)))
  obtain ⟨n₇, hn₇⟩ := eventually_atTop.1 hev
  -- the constants
  set lq := Real.log q with hlq_def
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlq : 0 ≤ lq := Real.log_nonneg hq1
  set B7 := 1 + K₀ * (C₁ + 2) ^ m₀ * lq
  have hC12 : (0 : ℝ) ≤ (C₁ + 2) ^ m₀ := pow_nonneg (by linarith) m₀
  have hB7 : 1 ≤ B7 := by
    have := mul_nonneg (mul_nonneg hK₀ hC12) hlq
    simp only [B7]
    linarith
  set ep := max e₇ 0
  set Csh := Ce + lq + 1
  set Cex := 1 + C₂ * lq
  set A1 := 2 * Ce + 5 + 4 * Csh + 2 * Cex
  set Cδ := (4 * A1 + 4 * Cg * B7 ^ ep) / c₁
  set A₁ := 7 * C₂ / 16 + 1 / 8
  set CE := 2 / g * (32 * Ce₇ * C₂ * B7 ^ 4 * (A₁ + C₂ * B7))
  set C := Csh + Cex + max CD 1 + Cδ + CE + 2 / g
  set Cl : ℝ := (2 * ep + 16) * m₀
  set c := min a₀ (c₇ / (1 + K₀ * lq))
  have hc : 0 < c := lt_min ha₀ (by positivity)
  refine ⟨C₁, c, Crl, csh, Csu, Csl, 1024 * Real.exp 1 / g, (32 * √(1 + 2 / g))⁻¹, C, Cl, Cm,
    max (max (max n₁ n₂) (max n₃ n₄)) (max (max n₅ n₆) n₇), hC₁, hc, hcsh, hCsl, hCsu, hCrl,
    hCm, ?_⟩
  intro n hn W hW har Λ Φ hΦ Ω hΩ E₀ hE hgap A hA dep hgeom hX hQ
  simp only [max_le_iff] at hn
  obtain ⟨⟨⟨hn1, hn2⟩, hn3, hn4⟩, ⟨hn5, hn6⟩, hn7⟩ := hn
  obtain ⟨⟨h1n, hm1, hD1, -, -, -, hLn⟩, h32, h2m, h3n⟩ := hn₇ n hn7
  -- the scales at `n`
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast h3n
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1' : (1 : ℝ) ≤ n := by linarith
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hnR
  have hmR : (m μ n : ℝ) ≤ (n : ℝ) ^ μ := Nat.floor_le (by positivity)
  have hmR' : (n : ℝ) ^ μ - 1 < m μ n := Nat.sub_one_lt_floor _
  have hLR' : (n : ℝ) ^ (1 - ℓ) - 1 < L ℓ n := Nat.sub_one_lt_floor _
  have hm0 : (0 : ℝ) < m μ n := by exact_mod_cast hm1
  have hL16 : 16 * m μ n ≤ L ℓ n := by
    have : ((16 * m μ n : ℕ) : ℝ) < L ℓ n := by push_cast; linarith
    exact_mod_cast this.le
  have hK2 : 2 ≤ K ℓ μ n := by
    change 2 ≤ L ℓ n / (8 * m μ n)
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hKR : (2 : ℝ) ≤ K ℓ μ n := by exact_mod_cast hK2
  have hK0 : (0 : ℝ) < K ℓ μ n := by linarith
  have hLmK : (L ℓ n : ℝ) < 8 * m μ n * (K ℓ μ n + 1) := by
    have := Nat.lt_mul_div_succ (L ℓ n) (by omega : 0 < 8 * m μ n)
    exact_mod_cast this
  have hnmK : (n : ℝ) / (m μ n * K ℓ μ n) ≤ 32 * (n : ℝ) ^ ℓ := by
    have hL16' : (16 * m μ n : ℝ) ≤ L ℓ n := by exact_mod_cast hL16
    have h1 : (n : ℝ) ^ (1 - ℓ) / 32 ≤ m μ n * K ℓ μ n := by nlinarith
    have h2 : (n : ℝ) ^ (1 - ℓ) * (n : ℝ) ^ ℓ = n := by
      rw [← Real.rpow_add hn0]; simp
    rw [div_le_iff₀ (by positivity)]
    have h3 : 0 < (n : ℝ) ^ ℓ := Real.rpow_pos_of_pos hn0 _
    calc (n : ℝ) = (n : ℝ) ^ (1 - ℓ) * (n : ℝ) ^ ℓ := h2.symm
      _ = 32 * (n : ℝ) ^ ℓ * ((n : ℝ) ^ (1 - ℓ) / 32) := by ring
      _ ≤ 32 * (n : ℝ) ^ ℓ * (m μ n * K ℓ μ n) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hmμ : (n : ℝ) ^ μ / 2 ≤ m μ n := by linarith
  set aW := a ℓ μ W n with haW
  have ha : 0 < aW := div_pos (by linarith) hK0
  have haK : aW * K ℓ μ n = W := div_mul_cancel₀ W hK0.ne'
  have hr1 : (1 : ℝ) ≤ ((r₀ C₁ n : ℝ) + 1) ^ m₀ :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg (r₀ C₁ n) : (0 : ℝ) ≤ r₀ C₁ n)])
  have hac : aW ≤ c := le_trans (le_mul_of_one_le_right ha.le hr1) har
  have haa₀ : aW ≤ a₀ := hac.trans (min_le_left _ _)
  set ℓ₇ := 1 + K₀ * ((r₀ C₁ n : ℝ) + 1) ^ m₀ * lq
  have hℓ₇0 : 0 ≤ K₀ * ((r₀ C₁ n : ℝ) + 1) ^ m₀ * lq := by positivity
  have hℓ₇ : 1 ≤ ℓ₇ := by linarith
  have haℓ : aW * ℓ₇ ≤ c₇ := by
    have h1 : aW * ℓ₇ = aW + aW * ((r₀ C₁ n : ℝ) + 1) ^ m₀ * (K₀ * lq) := by ring
    have h2 : c ≤ c₇ / (1 + K₀ * lq) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h2
    have h3 := mul_le_mul_of_nonneg_right har (by positivity : 0 ≤ K₀ * lq)
    rw [h1]
    linarith
  -- `ℓ₇ ≤ B₇ (log n)^{2m₀}`
  have hr₀ : (r₀ C₁ n : ℝ) + 1 ≤ (C₁ + 2) * Real.log n ^ 2 := by
    have h1 := r₀_le C₁ hC₁.le n
    have h2 : 1 ≤ Real.log n ^ 2 := one_le_pow₀ hlog
    linarith only [h1, h2]
  have hLN2 : 1 ≤ Real.log n ^ (2 * m₀) := one_le_pow₀ hlog
  have hℓ₇B : ℓ₇ ≤ B7 * Real.log n ^ (2 * m₀) := by
    have h1 : ((r₀ C₁ n : ℝ) + 1) ^ m₀ ≤ (C₁ + 2) ^ m₀ * Real.log n ^ (2 * m₀) := by
      calc ((r₀ C₁ n : ℝ) + 1) ^ m₀ ≤ ((C₁ + 2) * Real.log n ^ 2) ^ m₀ :=
            pow_le_pow_left₀ (by positivity) hr₀ m₀
        _ = (C₁ + 2) ^ m₀ * Real.log n ^ (2 * m₀) := by rw [mul_pow, ← pow_mul]
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK₀ hlq)
    simp only [ℓ₇, B7]
    linarith only [h2, hLN2]
  -- powers of `log n`
  have hLCl : ∀ k : ℕ, (k : ℝ) ≤ Cl → Real.log n ^ k ≤ Real.log n ^ Cl := fun k hk => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlog hk
  have hm₀ : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
  have hep : 0 ≤ ep := le_max_right _ _
  have hCl0 : 0 ≤ Cl := by positivity
  -- D9.3: the truncated system at `S₀ = A ∩ T_L`
  obtain ⟨Tr⟩ := Htr n (L ℓ n) (by omega) hLn Λ Φ hΦ Ω hΩ E₀ hE hgap A hA dep (r₀ C₁ n) hgeom
  obtain ⟨hm, hM⟩ := hsc n hn1
  set S := scanAt G Λ A dep R Tr.a ℓ κ μ C₁ Cm n hm hM with hS
  -- D9.8: Lemma 9.1 for the scan
  obtain ⟨h1, h2, h3, h4⟩ := hitems n hn1 Λ A dep Tr.a hm hM hA Tr.anchor hgeom
  have hT100 := htail n hn2 Λ A dep Tr.a hm hM hA Tr.anchor hgeom
  -- D9.9.2: the typical set at the target
  obtain ⟨E, hEw, hEz⟩ := htyp n (L ℓ n) hn4 (by omega) Λ Ω hΩ A hA dep CT (r₀ C₁ n) hgeom Tr
  -- D9.9.1: the transfer `Ω → Ω̃`
  obtain ⟨htrS, htrI⟩ := htr n hn3 Λ Ω hΩ Tr.Dt Tr.traceDist_le
  -- D9.9.2: prefix data (Lemma 9.1 (2))
  set M := ⌊C₂ * n * D κ n⌋₊ with hMdef
  have hrows : ∀ B ∈ S.prefixes, ∃ j ≤ L ℓ n,
      A.filter (fun x => 0 < dep x ∧ dep x < j) ⊆ up B ∧
        up B ⊆ A.filter (fun x => 0 < dep x ∧ dep x ≤ j) := fun B hB => by
    obtain ⟨j, -, hjL, hlo, hhi⟩ := h2.rows B hB
    exact ⟨j, hjL, (up_subtype_eq ((filter_subset _ _).trans hA)).symm.subset.trans (up_mono hlo),
      (up_mono hhi).trans (up_subtype_eq ((filter_subset _ _).trans hA)).subset⟩
  have hmatch : ∀ s j, ∀ Q ∈ ({S.Γ.U s j, S.Γ.U s j ∪ S.Γ.Y s j} : Finset (Finset Λ)),
      ∃ B ∈ S.prefixes, (Q ⊆ B ∧ #(B \ Q) ≤ M) ∨ (B ⊆ Q ∧ #(Q \ B) ≤ M) := fun s j Q hQ' => by
    obtain ⟨B, hB, h⟩ := h2.matched s j Q hQ'
    exact ⟨B, hB, h.imp (fun h => ⟨h.1, Nat.le_floor h.2⟩) (fun h => ⟨h.1, Nat.le_floor h.2⟩)⟩
  have PD := hpref n (L ℓ n) hn5 hLn Λ Ω hΩ A hA dep (r₀ C₁ n) hgeom Ce e hQ Tr S.prefixes
    h2.nested h2.disjoint hrows S.Γ M hmatch
  -- D9.9.2: marginal moment data (Lemma 9.1 (2), D4.14)
  have MD := hmgf n (L ℓ n) h3n Λ Ω hΩ A dep Tr S.Γ (D κ n) (by exact_mod_cast hD1)
    fun s j Q hQ' => by
      have hQ'' : Q ∈ ({S.X ∪ S.Γ.U s j, S.X ∪ S.Γ.U s j ∪ S.Γ.Y s j, S.Γ.Y s j, S.Γ.U s j,
          S.Γ.U s j ∪ S.Γ.Y s j} : Finset (Finset S.Λ)) := by
        simp only [mem_insert, mem_singleton] at hQ'
        rcases hQ' with rfl | rfl | rfl | rfl | rfl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))
        · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _)))
        · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
            (mem_singleton_self _))))
        · exact mem_insert_of_mem (mem_insert_self _ _)
      obtain ⟨hc, hs⟩ := h2.cut s j Q hQ''
      exact ⟨hs, hc⟩
  -- D8.8: Proposition 8.1 for `Ω̃`, the typical set and the statuses of the scan
  obtain ⟨l, hl, hΓ⟩ := H81' Tr.Dt E
  obtain ⟨hRU, hRL, -, hSh, -⟩ := hΓ S.Γ
  -- the energy terms `h̃_i` on their designated supports `X̃_i`
  obtain ⟨eq, heq⟩ := Tr.support_eq
  set E7 := termsOn (siteTerms Tr.Et E.d) eq
  have hE7 : S.HasSupports E7 := fun i => by
    change physReg (Tr.Et.support (eq.symm i)) = physReg (S.Xt i)
    rw [heq, Equiv.apply_symm_apply]
    rfl
  have hHbar : ∀ k, Hbar Tr.Dt E.d k = E7.Hbar k := fun k => by
    rw [Hbar_eq Tr.Dt Tr.Et Tr.H_eq E.d k, Hbar_termsOn (siteTerms Tr.Et E.d) eq k]
  -- D9.11.4: the transferred subsystems and the split supports lie in `r₀`-balls
  have hball : ∀ x : σ, Transport.logDim (n := dims (fun _ : Λ => q) E.d)
      (physReg ((GraphDomain.ball G Λ x (r₀ C₁ n)).subtype (· ∈ Λ))) ≤ ℓ₇ := fun x => by
    rw [logDim_physReg]
    have hc1 : #((GraphDomain.ball G Λ x (r₀ C₁ n)).subtype (· ∈ Λ)) ≤ V (r₀ C₁ n) := by
      rw [Finset.card_subtype]
      exact (Finset.card_filter_le _ _).trans (hV Λ x _)
    have hc2 : (#((GraphDomain.ball G Λ x (r₀ C₁ n)).subtype (· ∈ Λ)) : ℝ) ≤
        K₀ * ((r₀ C₁ n : ℝ) + 1) ^ m₀ :=
      (by exact_mod_cast hc1 : _ ≤ (V (r₀ C₁ n) : ℝ)).trans (hVK _)
    have := mul_le_mul_of_nonneg_right hc2 hlq
    simp only [ℓ₇]
    linarith only [this]
  have hmove : ∀ t h c g, Transport.logDim (n := dims (fun _ : Λ => q) E.d)
      ((S.round t).move h c g).subsystem ≤ ℓ₇ := fun t h c g => by
    obtain ⟨x, hx⟩ := h1.move_ball t h c g
    exact (logDim_mono hx).trans (hball x)
  have hsplit : ∀ t i j g, ¬ ((S.round t).leafPart j g).Contains (E7.support i) →
      Transport.logDim (n := dims (fun _ : Λ => q) E.d) (E7.support i) ≤ ℓ₇ := by
    intro t i j g hg
    rw [S.round_leafPart, hE7 i] at hg
    rw [hE7 i, (h1.ball_of_split ⟨t, j⟩ g i hg).1]
    exact hball _
  have hcb : ∀ t k, (S.round t).CrossBandCommute (dims (fun _ : Λ => q) E.d) (aW / 2) k :=
    fun t k => h1.crossBand (fun _ => q) E.d (aW / 2) (by positivity) k t
  -- `ε = n^{-ν}`
  have hε0 : 0 < (n : ℝ) ^ (-ν) := Real.rpow_pos_of_pos hn0 _
  have hε1 : (n : ℝ) ^ (-ν) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  -- D9.12–D9.13 at this `n` (Proposition 7.4 on every round)
  obtain ⟨r, hr, hsel⟩ := selected_point S Tr.Dt E E7 hE7 hHbar l
    (fun k => ⟨(hl k).1, (hl k).2.1, (hl k).2.2.1, (hl k).2.2.2.1⟩) hc₁ hC₂.le h3 h4
    h2.splitCount hT100 h1n hm1 (le_trans (by norm_num) hK2) hD1 ha hε0 hε1 hℓ₇ hcb
    (fun t => h1.supportCompatible t E7 hE7) hsplit hCe₇.le
    (fun t => by
      obtain ⟨β, r, hβ, hr, H⟩ := H74 (dims (fun _ : Λ => q) E.d) (S.round t) E7
        (S.round_isAdmissible t) (h1.supportCompatible t E7 hE7) ha hℓ₇ haℓ (hcb t) (hmove t)
        (fun i hi => by
          classical
          obtain ⟨j, hj⟩ := hi
          obtain ⟨g, hg⟩ := (mem_filter.1 hj).2
          exact hsplit t i j g hg)
      exact ⟨β, r, hβ, hr, fun k pre hpS hp => ⟨fun p hp0 hp1 =>
        ⟨((H k pre hpS hp).1 p hp0 hp1).2.2.1, ((H k pre hpS hp).1 p hp0 hp1).2.2.2⟩,
        (H k pre hpS hp).2.2⟩⟩)
    (hRU S.prefixes _ _ PD aW ha haa₀)
  -- the constants: every summand of `C` is nonnegative
  have hCsh0 : 0 ≤ Csh := by simp only [Csh]; positivity
  have hCex0 : 0 ≤ Cex := by simp only [Cex]; positivity
  have hA10 : 0 ≤ A1 := by simp only [A1]; positivity
  have hCδ0 : 0 ≤ Cδ := by simp only [Cδ]; positivity
  have hA₁0 : 0 ≤ A₁ := by simp only [A₁]; positivity
  have hCE0 : 0 ≤ CE := by simp only [CE]; positivity
  have hmax1 : 1 ≤ max CD 1 := le_max_right _ _
  have hg2 : 0 ≤ 2 / g := by positivity
  have hCsh : Csh ≤ C := by simp only [C]; linarith only [hCex0, hmax1, hCδ0, hCE0, hg2]
  have hCex : Cex ≤ C := by simp only [C]; linarith only [hCsh0, hmax1, hCδ0, hCE0, hg2]
  have hCD : max CD 1 ≤ C := by simp only [C]; linarith only [hCsh0, hCex0, hCδ0, hCE0, hg2]
  have hCδ : Cδ ≤ C := by simp only [C]; linarith only [hCsh0, hCex0, hmax1, hCE0, hg2]
  have hCE : CE ≤ C := by simp only [C]; linarith only [hCsh0, hCex0, hmax1, hCδ0, hg2]
  have hCgC : 2 / g ≤ C := by simp only [C]; linarith only [hCsh0, hCex0, hmax1, hCδ0, hCE0]
  have hC0 : 0 ≤ C := hCsh0.trans hCsh
  -- the scales
  have hne0 : (1 : ℝ) ≤ (n : ℝ) ^ e := Real.one_le_rpow hn1' he.le
  have hN : (n : ℝ) ^ (1 + e) = n * (n : ℝ) ^ e := by rw [Real.rpow_add hn0, Real.rpow_one]
  have hN1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 + e) := Real.one_le_rpow hn1' (by linarith)
  have hnN : (n : ℝ) ≤ (n : ℝ) ^ (1 + e) := by
    rw [hN]; exact le_mul_of_one_le_right hn0.le hne0
  have hDe : (D κ n : ℝ) ≤ 2 * (n : ℝ) ^ e := by
    have h1 := D_le κ n
    have h2 : (n : ℝ) ^ κ ≤ (n : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_le hn1' hκe
    linarith only [h1, h2, hne0]
  have hD1' : (1 : ℝ) ≤ D κ n := by exact_mod_cast hD1
  have hnD : (n : ℝ) * D κ n ≤ 2 * (n : ℝ) ^ (1 + e) := by
    rw [hN]
    have := mul_le_mul_of_nonneg_left hDe hn0.le
    linarith only [this]
  have hnD1 : (1 : ℝ) ≤ (n : ℝ) * D κ n := one_le_mul_of_one_le_of_one_le hn1' hD1'
  have hLe : (L ℓ n : ℝ) ^ e ≤ (n : ℝ) ^ e :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hLn) he.le
  have hLe0 : (0 : ℝ) ≤ (L ℓ n : ℝ) ^ e := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsh : (n : ℝ) * (L ℓ n : ℝ) ^ e + n ≤ 2 * (n : ℝ) ^ (1 + e) := by
    have := mul_le_mul_of_nonneg_left hLe hn0.le
    rw [hN] at hnN ⊢
    linarith only [this, hnN]
  have hsh1 : (n : ℝ) ≤ (n : ℝ) * (L ℓ n : ℝ) ^ e + n := by
    have := mul_nonneg hn0.le hLe0
    linarith only [this]
  -- D9.9.2: `B_sh ≤ C (nL^e + n)`, `B_exc ≤ C n D`, `𝓑 ≤ C n D (log n)^C`
  set Bsh := Ce * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n) + n * lq + 1
  set Bexc := 1 + (M : ℝ) * lq
  have hBsh : Bsh ≤ Csh * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n) := by
    have := mul_le_mul_of_nonneg_left hsh1 hlq
    simp only [Bsh, Csh]
    linarith only [this, hsh1, hn1']
  have hMle : (M : ℝ) ≤ C₂ * n * D κ n := Nat.floor_le (by positivity)
  have hBexc : Bexc ≤ Cex * n * D κ n := by
    have := mul_le_mul_of_nonneg_right hMle hlq
    simp only [Bexc, Cex]
    linarith only [this, hnD1]
  have hBsh0 : 0 ≤ Bsh := add_nonneg (add_nonneg (mul_nonneg hCe.le
    (add_nonneg (mul_nonneg hn0.le hLe0) hn0.le)) (mul_nonneg hn0.le hlq)) zero_le_one
  have hBexc0 : 0 ≤ Bexc := add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hlq)
  have h6 : Real.log n ^ (6 * m₀) ≤ Real.log n ^ Cl :=
    hLCl _ (by
      push_cast
      simp only [Cl]
      have := mul_le_mul_of_nonneg_right (by linarith only [hep] : (6 : ℝ) ≤ 2 * ep + 16) hm₀
      linarith only [this])
  -- D9.12.3: the final budget `2 log d_* - log z + W(B_sh/z + B_exc) ≤ W A1 n^{1+e}`
  obtain ⟨hz0, hz1, hd₀⟩ := typicalSet_log_d_le E
  have hd : Real.log E.d ≤ Tr.Dt.S S.X + E.w := hd₀
  have hz2 : 1 / 2 ≤ E.z := by
    have h1 : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg hn0.le]
      have : (3 : ℝ) ≤ (n : ℝ) ^ (100 : ℝ) :=
        hnR.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hn1' (by norm_num :
          (1 : ℝ) ≤ 100))
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hSX : Tr.Dt.S S.X ≤ Ce * (n : ℝ) ^ (1 + e) + 1 := by
    have h1 := (abs_le.1 (htrS S.X)).2
    have h2 : (pureState Ω hΩ).regionEntropy (up_subset S.X) ≤ Ce * (n : ℝ) ^ (1 + e) := by
      exact ((pureState Ω hΩ).regionEntropy_congr (up_target hA dep) (up_subset _) _).trans_le hX
    have hX1 : (#S.X : ℝ) ≤ (CT + 1) * (n : ℝ) ^ 2 := by
      have h3 : #S.X ≤ #(Λ.filter fun x => dep x = 0) := by
        change #((A.filter fun x => dep x = 0).subtype (· ∈ Λ)) ≤ _
        rw [Finset.card_subtype]
        exact (Finset.card_filter_le _ _).trans (card_le_card (filter_subset_filter _ hA))
      have h4 := hgeom.card_target
      have h5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
      have h3' : (#S.X : ℝ) ≤ #(Λ.filter fun x => dep x = 0) := by exact_mod_cast h3
      linarith only [h3', h4, h5]
    have h3 : (n : ℝ) ^ (-200 : ℝ) * (1 + #S.X) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (by linarith only [hX1])
        (Real.rpow_nonneg hn0.le _)).trans (hn₆ n hn6)
    linarith only [h1, h2, h3]
  have hw : E.w ≤ (n : ℝ) ^ (1 + e) := by
    rw [hEw]; exact Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
  have hXU : 2 * Real.log E.d - Real.log E.z + 2 * (1 / 4) * (aW * S.K) *
      (2 * Bsh / E.z + 2 * Bexc) ≤ W * A1 * (n : ℝ) ^ (1 + e) := by
    have hlz : -Real.log E.z ≤ 1 := by
      have h1 : Real.log (1 / 2) ≤ Real.log E.z := Real.log_le_log (by norm_num) hz2
      rw [one_div, Real.log_inv] at h1
      linarith only [h1, Real.log_two_lt_d9]
    have hb : 2 * Bsh / E.z ≤ 4 * Bsh := by
      rw [div_le_iff₀ hz0]
      have := mul_le_mul_of_nonneg_left hz2 hBsh0
      linarith only [this]
    have haK' : aW * S.K = W := haK
    rw [haK']
    have hsum : 2 * Bsh / E.z + 2 * Bexc ≤ (4 * Csh + 2 * Cex) * (2 * (n : ℝ) ^ (1 + e)) := by
      have h1 := mul_le_mul_of_nonneg_left hsh hCsh0
      have h2 : Cex * n * D κ n ≤ Cex * (2 * (n : ℝ) ^ (1 + e)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hnD hCex0
      linarith only [hb, hBsh, hBexc, h1, h2]
    have hW1 : (2 * Ce + 5) * (n : ℝ) ^ (1 + e) ≤ W * ((2 * Ce + 5) * (n : ℝ) ^ (1 + e)) :=
      le_mul_of_one_le_left (by positivity) hW
    have h3 := mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ 2 * (1 / 4) * W)
    simp only [A1]
    linarith only [hd, hSX, hw, hlz, h3, hW1, hN1]
  -- D9.12.6: `ℓ^C ≤ (log n)^C`
  have hLT : ℓ₇ ^ e₇ ≤ B7 ^ ep * Real.log n ^ Cl := by
    have hL0 : 0 ≤ Real.log n ^ (2 * m₀) := by linarith only [hLN2]
    have h1 : ℓ₇ ^ e₇ ≤ ℓ₇ ^ ep := Real.rpow_le_rpow_of_exponent_le hℓ₇ (le_max_left _ _)
    have h2 : ℓ₇ ^ ep ≤ (B7 * Real.log n ^ (2 * m₀)) ^ ep :=
      Real.rpow_le_rpow (by linarith only [hℓ₇]) hℓ₇B hep
    have h3 : (B7 * Real.log n ^ (2 * m₀)) ^ ep =
        B7 ^ ep * Real.log n ^ (((2 * m₀ : ℕ) : ℝ) * ep) := by
      rw [Real.mul_rpow (by linarith only [hB7]) hL0, ← Real.rpow_natCast (Real.log n),
        ← Real.rpow_mul (by linarith only [hlog])]
    have h4 : Real.log n ^ (((2 * m₀ : ℕ) : ℝ) * ep) ≤ Real.log n ^ Cl := by
      refine Real.rpow_le_rpow_of_exponent_le hlog ?_
      have := mul_nonneg hm₀ hep
      push_cast
      simp only [Cl]
      linarith only [this, hm₀]
    calc ℓ₇ ^ e₇ ≤ (B7 * Real.log n ^ (2 * m₀)) ^ ep := h1.trans h2
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by linarith only [hB7]) _)
  have hDn0 : (0 : ℝ) ≤ D κ n := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log n := by linarith only [hlog]
  have hLCl0 : 0 ≤ Real.log n ^ Cl := Real.rpow_nonneg hlog0 _
  have hcastm₀ : ∀ j : ℕ, ((j * m₀ : ℕ) : ℝ) ≤ Cl ↔ (j : ℝ) * m₀ ≤ (2 * ep + 16) * m₀ := by
    intro j; push_cast; rfl
  refine ⟨Tr.a, hm, hM, Tr.Dt, E, l, S.prefixes, Bsh, Bexc,
    max CD 1 * n * D κ n * Real.log n ^ (6 * m₀), htrS, htrI, hEw, hEz, PD,
    hBsh.trans (mul_le_mul_of_nonneg_right hCsh (by linarith only [hsh1, hn0])),
    hBexc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCex hn0.le) hDn0), MD,
    ?_, fun s g => h1.far s g, hRU S.prefixes _ _ PD aW ha haa₀,
    fun τ hτ hτ' => hRL aW τ ha haa₀ hτ hτ',
    fun hac' => ⟨(hSh _ MD aW (1 / 4) ha hac' (by norm_num) (by norm_num)).1,
      fun τ hτ hτ' => (hSh _ MD aW τ ha hac' hτ hτ').2⟩, r, hr, fun k hk => ?_⟩
  · -- `𝓑 ≤ C n D (log n)^C`
    have h0 : (0 : ℝ) ≤ n * D κ n := mul_nonneg hn0.le hDn0
    calc max CD 1 * n * D κ n * Real.log n ^ (6 * m₀)
        = max CD 1 * (n * D κ n) * Real.log n ^ (6 * m₀) := by ring
      _ ≤ C * (n * D κ n) * Real.log n ^ Cl :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCD h0) h6 (pow_nonneg hlog0 _)
            (mul_nonneg hC0 h0)
      _ = _ := by ring
  -- the selected point
  obtain ⟨t, ht, p, hp1, hp2, hEd⟩ := hsel k hk
  refine ⟨t, ht, p, hp1, hp2, hEd.trans (add_le_add ?_ le_rfl)⟩
  rw [Tr.g_eq]
  have hTc : ((S.T : ℕ) : ℝ) = 2 * (S.n : ℝ) * S.m := by
    simp only [Scan.T]; push_cast; ring
  rw [hTc]
  refine edef_le (B7 := B7) (LN2 := Real.log n ^ (2 * m₀)) (LN8 := Real.log n ^ (8 * m₀)) hg
    Tr.E₀_le (Real.rpow_nonneg hn0.le _) hCe₇.le hC₂.le hm0 hK0 hn0 hDn0 haK hnmK
    (Real.rpow_nonneg (le_max_right _ _) _) ?_ (Real.rpow_nonneg (by linarith only [hℓ₇]) _) ?_
    hA₁0 hε0.le (Real.rpow_nonneg hn0.le _) (by linarith only [hB7]) (by linarith only [hℓ₇])
    ?_ ?_ ?_ (pow_nonneg hlog0 _) (Real.rpow_nonneg hn0.le _) hCE hCgC
  · -- D9.12.6: the selected density
    refine Real.rpow_le_rpow (le_max_right _ _) (max_le ?_ ?_) (by norm_num)
    · refine (delta_le hn1' hm0 hK0 hW haK ha hc₁ rfl hmμ hA10 hCg.le hXU hLT
        (Real.rpow_nonneg (by linarith only [hB7]) _) le_rfl hLCl0).trans ?_
      have hq0 : 0 ≤ (n : ℝ) ^ (e - μ) + aW ^ (1 / 4 : ℝ) * Real.log n ^ Cl :=
        add_nonneg (Real.rpow_nonneg hn0.le _) (mul_nonneg (Real.rpow_nonneg ha.le _) hLCl0)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCδ
        (Real.rpow_nonneg hn0.le _)) hq0
    · exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hn0.le _))
        (add_nonneg (Real.rpow_nonneg hn0.le _) (mul_nonneg (Real.rpow_nonneg ha.le _) hLCl0))
  · -- `η^{1/8} ≤ (2ℓ)^{1/8} ≤ 2ℓ ≤ 2 B₇ (log n)^{2m₀}`
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith only [hℓ₇] : (1 : ℝ) ≤ 2 * ℓ₇)
      (by norm_num : (1 / 8 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h
    linarith only [h, hℓ₇B]
  · -- `ℓ⁴ ≤ B₇⁴ (log n)^{8m₀}`
    calc ℓ₇ ^ 4 ≤ (B7 * Real.log n ^ (2 * m₀)) ^ 4 :=
          pow_le_pow_left₀ (by linarith only [hℓ₇]) hℓ₇B 4
      _ = B7 ^ 4 * Real.log n ^ (8 * m₀) := by
          rw [mul_pow, ← pow_mul]
          ring_nf
  · exact hLCl _ ((hcastm₀ 8).2 (by
      have := mul_le_mul_of_nonneg_right (by linarith only [hep] : (8 : ℝ) ≤ 2 * ep + 16) hm₀
      exact this))
  · rw [← pow_add]
    refine hLCl _ ?_
    have := mul_le_mul_of_nonneg_right (by linarith only [hep] : (10 : ℝ) ≤ 2 * ep + 16) hm₀
    push_cast
    simp only [Cl]
    linarith only [this]

/-- D9.9 **Proposition 9.2** in the form consumed by Propositions 9.5 and 9.6 (`Prop_9_2`): the
statuses are those of the scan and the selected tree is the terminal tree of the selected charge
round at the selected `p_k`. -/
theorem prop_9_2' : Prop_9_2.{u} := by
  intro σ _ _ G _ V hV K₀ m₀ hK₀ hVK q _ R J Δ hΔ ℓ κ μ ν e Ce CT hℓ hℓ1 hκ hκμ hμ hν he he1
    hκe hCe hCT
  obtain ⟨C₁, c, Crl, csh, Csu, Csl, C₀, c₀, C, Cl, Cm, n₀, hC₁, hc, hcsh, hCsl, hCsu, hCrl, -,
    H⟩ := prop_9_2 G V hV K₀ m₀ hK₀ hVK q R J Δ hΔ ℓ κ μ ν e Ce CT hℓ hℓ1 hκ hκμ hμ hν he he1
      hκe hCe hCT
  refine ⟨C₁, c, Crl, csh, Csu, Csl, C₀, c₀, C, Cl, n₀, hC₁, hc, hcsh, hCsl, hCsu, hCrl,
    fun n hn W hW har Λ Φ hΦ Ω hΩ E₀ hE hgap A hA dep hgeom hX hQ => ?_⟩
  obtain ⟨aY, hm, hM, Dt, E, l, 𝓡, Bsh, Bexc, 𝓑, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, r, hr, hsel⟩ := H n hn W hW har Λ Φ hΦ Ω hΩ E₀ hE hgap A hA dep hgeom hX hQ
  refine ⟨Dt, E, _, inferInstance, inferInstance, (scanAt G Λ A dep R aY ℓ κ μ C₁ Cm n hm hM).Γ,
    l, 𝓡, Bsh, Bexc, 𝓑, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, r, hr,
    fun k hk => ?_⟩
  obtain ⟨t, -, p, -, -, hEd⟩ := hsel k hk
  exact ⟨_, hEd⟩

end AreaLaw.Scanner
