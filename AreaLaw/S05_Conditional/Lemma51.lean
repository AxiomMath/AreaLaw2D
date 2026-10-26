import AreaLaw.S05_Conditional.Movement.LogMomentsMatrix
import AreaLaw.S05_Conditional.Movement.Schatten
import AreaLaw.S05_Conditional.Movement.Hellinger
import AreaLaw.S05_Conditional.Movement.StateMovement
import AreaLaw.S05_Conditional.Movement.Analytic
import AreaLaw.S05_Conditional.Movement.Regularise

/-!
# §5.1 Lemma 5.1, the conditional movement estimate

Assembly of D5.5: the faithful case `lemma_5_1_faithful` (D5.5.1–10) from the steps in
`S05_Conditional/Movement/`, and **Lemma 5.1** `lemma_5_1` by the regularisation D5.5.11.
-/

namespace AreaLaw

open Arealaw Matrix Complex
open OpenAI (pureState)
open Conditional
open scoped ComplexOrder MatrixOrder

universe u v

/-- D5.10.3 bookkeeping: `√(C w (√λ + √a ℓ)) ≤ √C w^{1/2} (λ^{1/4} + a^{1/4} ℓ^{1/2})`. -/
private theorem sqrt_movement_le {C w lam a l : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w) (hlam : 0 ≤ lam)
    (ha : 0 ≤ a) (hl : 0 ≤ l) :
    √(C * w * (√lam + √a * l)) ≤
      √C * w ^ (1 / 2 : ℝ) * (lam ^ (1 / 4 : ℝ) + a ^ (1 / 4 : ℝ) * l ^ (1 / 2 : ℝ)) := by
  have h4 (x : ℝ) (hx : 0 ≤ x) : √(√x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num
  have hadd : √(√lam + √a * l) ≤ √(√lam) + √(√a * l) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [Real.sqrt_nonneg (√lam), Real.sqrt_nonneg (√a * l)]
  rw [Real.sqrt_mul (mul_nonneg hC hw), Real.sqrt_mul hC, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow, ← h4 lam hlam, ← h4 a ha, ← Real.sqrt_mul (Real.sqrt_nonneg a)]
  exact mul_le_mul_of_nonneg_left hadd (by positivity)

/-- D5.5.2 **Lemma 5.1** for faithful `τ` (D5.5.1–10). `θ` unit pure vector on `P, x, U, F`;
`d = dim x`, `ℓ = log(e d)`, `η = S(x|P)_θ + S(x|U)_θ = I(x:F|U)_θ`. Universal `c, C > 0` such
that for `0 < aℓ ≤ c`, `σ ≥ 0` on `xP`, `τ > 0` on `xU`, `Tr σ, Tr τ ≤ 1`:
`‖σ^{a/2} ρ̂_P^{-a/2} τ^{a/2} ρ̂_U^{-a/2} θ‖ ≤ exp(-(a/2) η + C a^{5/4} ℓ²)`. -/
theorem lemma_5_1_faithful : Lemma_5_1_faithful.{u, v} := by
  have h4all := step_5_4_of araki_lieb_thirring.{max u v} step_5_2.{max u v}
  obtain ⟨c₇, C₇, hc₇, hC₇, h7⟩ :=
    step_5_7_matrix_of step_5_2.{max u v} h4all step_5_6.{max u v}
  obtain ⟨C₉, hC₉, h9⟩ := step_5_9_of step_5_2.{max u v}
  obtain ⟨c₄, C₄, hc₄, hc₄8, hC₄, h4⟩ := h4all
  set C₀ := C₄ / 2 with hC₀def
  set C' := C₉ * (1 + √C₇) with hC'def
  set Cr := max C₀ (4 * √C')
  have hC₀ : 0 ≤ C₀ := by positivity
  have hC' : 0 ≤ C' := by positivity
  have hCr : 0 ≤ Cr := le_max_of_le_left hC₀
  refine ⟨min c₄ c₇, C₀ + 3 * Cr + 2 * Cr ^ (4 / 3 : ℝ), lt_min hc₄ hc₇, by positivity,
    fun σ _ loc _ _ Λ P X U F hP hX hU hF hΛ hPX hPU hPF hXU hXF hUF θ hθ a ha0 hac σ' τ hσ
      hσ1 hτ hτ1 ↦ ?_⟩
  set d := Fintype.card (Reg loc X)
  set l := ℓ d
  set dU := condEntropy (pureState θ hθ).toSubState hX hU
  set dP := condEntropy (pureState θ hθ).toSubState hX hP
  set ρ := marg θ (Finset.union_subset hX hU)
  set Q := Qmat θ hU X
  -- D5.5.2, D5.2 for `(ρ_{xU}, I_x ⊗ ρ̂_U)`
  obtain ⟨hcp, hrel, hnorm⟩ := step_5_2_region σ loc Λ X U hX hU hXU θ hθ
  have hl : 1 ≤ l := one_le_ℓ hcp.2.2.2.1
  have ha : 0 < a := by
    by_contra h
    nlinarith [not_lt.1 h]
  have hal₄ : a * l ≤ c₄ := hac.trans (min_le_left _ _)
  have hal₇ : a * l ≤ c₇ := hac.trans (min_le_right _ _)
  have ha8 : a ≤ 1 / 8 := by nlinarith
  -- D5.4, D5.6, D5.7 for the pair
  obtain ⟨hZ, hlogZ, hτZ⟩ := h4 _ ρ Q d hcp a ha hal₄
  obtain ⟨-, h6⟩ := step_5_6 _ ρ Q d hcp a ha (by linarith)
  obtain ⟨hξ, hξ1, hH⟩ := h7 _ ρ Q d hcp a ha hal₇
  rw [hrel] at hlogZ
  -- D5.5.4, D5.6: `M(u) = ‖τ_u^a Q^{-a} θ‖` and the slack `λ(u)`
  set M : ℝ → ℝ := fun u ↦ ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hU)
    (bracketPow (tauU θ hU X τ a u) a) * extendId hU (hatPow (marg θ hU) ((-a : ℝ) : ℂ))) *ᵥ θ) :
      EuclideanSpace ℂ (Reg loc Λ))‖ with hM
  set lam : ℝ → ℝ := fun u ↦ -a * dU + C₀ * a ^ 2 * l ^ 2 - Real.log (M u) with hlamdef
  have hleft (u : ℝ) := step_5_6_1 σ loc Λ P X U hP hX hU hPX hPU hXU θ a σ' τ ha hσ hτ u
  have hτu (u : ℝ) : (tauU θ hU X τ a u).trace.re ≤ 1 := by rw [(hleft u).2.2]; exact hτ1
  have hM2 (u : ℝ) : M u ^ 2 =
      (bracketPow (tauU θ hU X τ a u) ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace.re :=
    hnorm _ (hleft u).2.1.posSemidef a ha
  have hMpos (u : ℝ) : 0 < M u := by
    have h := (h6 _ (hleft u).2.1.posSemidef).2 (hleft u).2.1
    rw [← hM2] at h
    by_contra hc
    have h0 : M u = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [h0] at h
    norm_num at h
  have hlog (u : ℝ) : 2 * Real.log (M u) ≤ 2 * a * -dU + C₄ * a ^ 2 * l ^ 2 := by
    have h := Real.log_le_log (pow_pos (hMpos u) 2)
      ((hM2 u).trans_le (hτZ _ (hleft u).2.1.posSemidef (hτu u)))
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hC₀e : C₀ * a ^ 2 * l ^ 2 = C₄ * a ^ 2 * l ^ 2 / 2 := by rw [hC₀def]; ring
  -- D5.6.3: `λ ≥ 0`
  have hlam (u : ℝ) : 0 ≤ lam u := by
    simp only [hlamdef]
    linarith [hlog u]
  -- D5.5.4: left boundary
  have hL (u : ℝ) : ‖Gfun θ hP hX hU σ' τ a (u * I)‖ ≤
      Real.exp (-a * dU + C₀ * a ^ 2 * l ^ 2 - lam u) := by
    rw [show -a * dU + C₀ * a ^ 2 * l ^ 2 - lam u = Real.log (M u) by simp only [hlamdef]; ring,
      Real.exp_log (hMpos u)]
    exact (hleft u).1
  -- D5.6.4: `Tr τ_u^{2a} ξ^{1-2a} = M²/Z ≥ e^{-2λ}`
  have hov (u : ℝ) : Real.exp (-2 * lam u) ≤ (bracketPow (tauU θ hU X τ a u) ((2 * a : ℝ) : ℂ) *
      bracketPow (xiMat ρ Q a) ((1 - 2 * a : ℝ) : ℂ)).trace.re := by
    rw [(h6 _ (hleft u).2.1.posSemidef).1, ← hM2 u, le_div_iff₀ hZ, ← Real.exp_log hZ,
      ← Real.exp_add, ← Real.exp_log (pow_pos (hMpos u) 2), Real.log_pow]
    refine Real.exp_le_exp.2 ?_
    simp only [hlamdef]
    push_cast
    linarith
  -- D5.5.5, D5.5.7 (D5.7, D5.9, D5.9.1): `‖θ_u − θ‖ ≤ C' (1+|u|)(√λ + √a ℓ)`
  have hHξ : √((CFC.sqrt ρ - CFC.sqrt (xiMat ρ Q a))ᴴ *
      (CFC.sqrt ρ - CFC.sqrt (xiMat ρ Q a))).trace.re ≤ √C₇ * √a * l := by
    refine (Real.sqrt_le_sqrt hH).trans_eq ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC₇.le, Real.sqrt_sq (by linarith)]
  have hmove (u : ℝ) : ‖(WithLp.toLp 2 (thetaU θ hX hU τ a u - θ) :
      EuclideanSpace ℂ (Reg loc Λ))‖ ≤ C' * (1 + |u|) * (√(lam u) + √a * l) := by
    rw [step_5_9_1 σ loc Λ X U hX hU hXU θ hθ τ hτ a u]
    have hm := h9 _ ρ Q (xiMat ρ Q a) (tauU θ hU X τ a u) d hcp hξ hξ1 (hleft u).2.1 (hτu u) a
      (lam u) u ha (by linarith) (hlam u) (hov u)
    have hw : 0 ≤ C₉ * (1 + |u|) := by positivity
    refine (hm.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hHξ) hw)).trans ?_
    have e : C' * (1 + |u|) * (√(lam u) + √a * l) = C₉ * (1 + |u|) * (√(lam u) + √a * l +
        √C₇ * √a * l) + C₉ * (1 + |u|) * √C₇ * √(lam u) := by rw [hC'def]; ring
    rw [e]
    exact le_add_of_nonneg_right (by positivity)
  -- D5.5.8, D5.10: right boundary
  have hR (u : ℝ) : ‖Gfun θ hP hX hU σ' τ a (1 + u * I)‖ ≤ Real.exp (-a * dP + Cr * a ^ 2 * l ^ 2 +
      Cr * a * l * (1 + |u|) ^ (1 / 2 : ℝ) *
        (lam u ^ (1 / 4 : ℝ) + a ^ (1 / 4 : ℝ) * l ^ (1 / 2 : ℝ))) := by
    obtain ⟨hGR, hσu, hσtr, hθu1, hmarg⟩ :=
      step_5_10_1 σ loc Λ P X U hP hX hU hPX hPU hXU θ hθ a σ' τ ha hσ hτ u
    have hmv := hmove u
    generalize thetaU θ hX hU τ a u = θu at hGR hθu1 hmarg hmv
    rw [← hmarg] at hGR
    -- D5.10.2: D5.4 with `U → P` for `θ_u`
    obtain ⟨hcpu, hrelu, hnormu⟩ := step_5_2_region σ loc Λ X P hX hP hPX.symm θu hθu1
    obtain ⟨hZu, hlogZu, hτZu⟩ := h4 _ _ _ d hcpu a ha hal₄
    rw [hrelu] at hlogZu
    have hZu' := hτZu _ hσu (by rw [hσtr]; exact hσ1)
    rw [← hnormu _ hσu a ha] at hZu'
    -- D5.10.3: Lemma 2.1 and D2.5
    have hcont := step_5_10_3 σ loc Λ X P hX hP hPX.symm θ θu hθ hθu1
    set dPu := condEntropy (pureState θu hθu1).toSubState hX hP
    have hN : ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hP)
        (bracketPow (sigmaU θ hP X σ' a u) a) * extendId hP (hatPow (marg θu hP) ((-a : ℝ) : ℂ))) *ᵥ
          θu) : EuclideanSpace ℂ (Reg loc Λ))‖ ≤ Real.exp (-a * dPu + C₀ * a ^ 2 * l ^ 2) := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 ?_
      rw [← Real.exp_nat_mul]
      refine hZu'.trans ?_
      rw [← Real.exp_log hZu]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    obtain ⟨B, hBdef⟩ : ∃ B, B = (1 + |u|) ^ (1 / 2 : ℝ) *
        (lam u ^ (1 / 4 : ℝ) + a ^ (1 / 4 : ℝ) * l ^ (1 / 2 : ℝ)) := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by linarith
    have hB : 0 ≤ B := by
      rw [hBdef]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (add_nonneg
        (Real.rpow_nonneg (hlam u) _) (mul_nonneg (Real.rpow_nonneg ha.le _)
          (Real.rpow_nonneg hl0 _)))
    obtain ⟨t, ht⟩ : ∃ t, t = √‖(WithLp.toLp 2 (θu - θ) : EuclideanSpace ℂ (Reg loc Λ))‖ :=
      ⟨_, rfl⟩
    rw [← ht] at hcont
    have hsq : t ≤ √C' * B := by
      rw [ht, hBdef]
      exact (Real.sqrt_le_sqrt hmv).trans ((sqrt_movement_le (w := 1 + |u|) hC' (by positivity)
        (hlam u) ha.le (by linarith)).trans_eq (by ring))
    have e1 : -a * dPu ≤ -a * dP + a * (4 * t * l) := by
      have := mul_le_mul_of_nonneg_left (abs_le.1 hcont).1 ha.le
      linarith
    have e2 : 4 * t ≤ Cr * B := by
      calc _ ≤ 4 * (√C' * B) := by linarith
        _ = (4 * √C') * B := by ring
        _ ≤ Cr * B := mul_le_mul_of_nonneg_right (le_max_right _ _) hB
    refine (hGR.trans hN).trans (Real.exp_le_exp.2 ?_)
    have e3 : C₀ * a ^ 2 * l ^ 2 ≤ Cr * a ^ 2 * l ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (by positivity)
    have e4 : a * (4 * t * l) ≤ Cr * a * l * B := by
      have := mul_le_mul_of_nonneg_left e2 (mul_nonneg ha.le hl0)
      linarith
    have : Cr * a * l * (1 + |u|) ^ (1 / 2 : ℝ) *
        (lam u ^ (1 / 4 : ℝ) + a ^ (1 / 4 : ℝ) * l ^ (1 / 2 : ℝ)) = Cr * a * l * B := by
      rw [hBdef]; ring
    linarith
  -- D5.5.9–10: interpolation and the sum
  obtain ⟨hG12, hGd, hbdd⟩ := step_5_5_3 σ loc Λ P X U hP hX hU θ a σ' τ ha hσ hτ
  have key := step_5_5_10 (Gfun θ hP hX hU σ' τ a) hGd.diffContOnCl hbdd ha (by linarith) hl
    hC₀ hCr lam hlam hL hR
  rw [hG12] at key
  refine key.trans (Real.exp_le_exp.2 (le_of_eq ?_))
  -- D5.5.1, D5.5.A: `η = d_P + d_U`
  rw [step_5_5_A σ loc Λ P X U F hP hX hU hF hΛ hPX hPU hPF hXU hXF hUF θ hθ]
  ring

/-- D5.5 **Lemma 5.1** (conditional movement estimate): the faithful case `lemma_5_1_faithful`
(D5.5.1–10) and the regularisation `lemma_5_1_of_faithful` (D5.5.11). -/
theorem lemma_5_1 : Lemma_5_1.{u, v} := lemma_5_1_of_faithful lemma_5_1_faithful

end AreaLaw
