import OpenAI.Statements
import Arealaw.OpNorm
import AreaLawForMathlib.Data.Int.L1Ball
import AreaLawForMathlib.QuantumInfo.Entropy.ClassicalQuantum
import AreaLawForMathlib.QuantumInfo.Region

/-!
# §2 Entropy and induced-graph locality

Digest `digest/02-preliminaries.md`, paper `paper/sections/01-preliminaries.tex`.
-/

namespace AreaLaw

open Arealaw OpenAI
open scoped ComplexOrder MatrixOrder

/-! ## D2.1 Conditional entropy and conditional mutual information -/

section Entropy

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U D E F : Finset σ}

/-- D2.1. `S(D|E)_ρ = S(DE)_ρ - S(E)_ρ`. -/
noncomputable def condEntropy (ρ : SubState (Reg loc U) ℂ) (hD : D ⊆ U) (hE : E ⊆ U) : ℝ :=
  ρ.regionEntropy (Finset.union_subset hD hE) - ρ.regionEntropy hE

/-- D2.1. `I(D:F|E)_ρ = S(DE)_ρ + S(EF)_ρ - S(E)_ρ - S(DEF)_ρ`.  The mutual information
`I(D:E)_ρ = S(D)_ρ + S(E)_ρ - S(DE)_ρ` is `Arealaw.SubState.mutualInfo`. -/
noncomputable def condMutualInfo (ρ : SubState (Reg loc U) ℂ) (hD : D ⊆ U) (hE : E ⊆ U)
    (hF : F ⊆ U) : ℝ :=
  ρ.regionEntropy (Finset.union_subset hD hE) + ρ.regionEntropy (Finset.union_subset hE hF) -
    ρ.regionEntropy hE - ρ.regionEntropy (Finset.union_subset (Finset.union_subset hD hE) hF)

end Entropy

/-! ## D2.2 Entropy facts used without proof -/

section D22

open Arealaw OpenAI Matrix
open scoped ComplexOrder MatrixOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U D E F X : Finset σ}


/-- D2.2. For normalized finite-dimensional density operators:
1. Strong subadditivity (SSA): `I(D:F|E)_ρ ≥ 0` [Lieb–Ruskai 1973].
2. `S(D|EF) ≤ S(D|E)`; equals item 1 via `I(D:F|E) = S(D|E) - S(D|EF)`.
3. `I(D:E) ≤ I(D:EF)`; equals item 1 via `I(D:EF) - I(D:E) = I(D:F|E)`.
4. Subadditivity + purification ⇒ `|S(D|E)_ρ| ≤ log dim D`.
5. Pure state on `DE`: `S(D) = S(E)`.
6. All hold with empty `D, E, F`; `𝓗_∅ = ℂ` (empty tensor product), entropies `0`. -/
theorem step_2_2 (ρ : MState (Reg loc U) ℂ) (hD : D ⊆ U) (hE : E ⊆ U) (hF : F ⊆ U)
    (hDE : Disjoint D E) (hDF : Disjoint D F) (hEF : Disjoint E F) :
    0 ≤ condMutualInfo ρ.toSubState hD hE hF ∧
    condEntropy ρ.toSubState hD (Finset.union_subset hE hF) ≤ condEntropy ρ.toSubState hD hE ∧
    ρ.toSubState.mutualInfo hD hE ≤ ρ.toSubState.mutualInfo hD (Finset.union_subset hE hF) ∧
    |condEntropy ρ.toSubState hD hE| ≤ Real.log (Fintype.card (Reg loc D)) ∧
    (∀ (Ω : Reg loc U → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) {A : Finset σ} (hA : A ⊆ U),
      (pureState Ω hΩ).toSubState.regionEntropy hA =
        (pureState Ω hΩ).toSubState.regionEntropy (Finset.sdiff_subset : U \ A ⊆ U)) ∧
    ρ.toSubState.regionEntropy (Finset.empty_subset U) = 0 := by
  have h₁ := ρ.regionEntropy_strong_subadditivity hDE hDF hEF hD hE hF
  refine ⟨?_, ρ.regionEntropy_union_sub_le hDE hDF hEF hD hE hF,
    ρ.mutualInfo_le_mutualInfo_union hDE hDF hEF hD hE hF,
    ρ.abs_regionEntropy_union_sub_le_log_card hDE hD hE,
    fun Ω hΩ _ hA => MState.regionEntropy_pureState_sdiff Ω hΩ hA, ρ.regionEntropy_empty⟩
  rw [condMutualInfo]
  linarith

end D22

/-! ## D2.3 Binary entropy and trace distance -/

/-- D2.3. Trace distance of states `ρ, σ`: `δ = ½‖ρ - σ‖₁`.  The binary entropy
`h(u) = -u log u - (1-u) log(1-u)` is Mathlib's `Real.binEntropy`. -/
noncomputable abbrev traceDist {ι : Type*} [Fintype ι] (ρ τ : MState ι ℂ) : ℝ :=
  ρ.toSubState.D₁ τ.toSubState

/-- D2.4.4. `C_h = 1 + 2/e`, the constant of `h(u) ≤ C_h √u`. -/
noncomputable def C_h : ℝ := 1 + 2 / Real.exp 1

section Lemma21

open Matrix Real

/-! ## D2.4 Lemma 2.1 -/


variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

/-- D2.4.4. For `0 ≤ δ ≤ 1` and `d ≥ 1`:
`2δ log d + (1+δ) h(δ/(1+δ)) ≤ 2 C_h √δ log(e d)`, from `h(u) ≤ C_h √u`. -/
theorem step_2_4_4 {δ d : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) :
    2 * δ * log d + (1 + δ) * binEntropy (δ / (1 + δ)) ≤ 2 * C_h * √δ * log (exp 1 * d) := by
  -- `-t log t ≤ 1/e`
  have hη (t : ℝ) (ht : 0 < t) : -(t * log t) ≤ (exp 1)⁻¹ := by
    have h := log_le_sub_one_of_pos (show 0 < t⁻¹ / exp 1 by positivity)
    rw [log_div (by positivity) (exp_pos 1).ne', log_inv, log_exp] at h
    calc -(t * log t) = t * -log t := by ring
      _ ≤ t * (t⁻¹ / exp 1) := mul_le_mul_of_nonneg_left (by linarith) ht.le
      _ = (exp 1)⁻¹ := by field_simp
  -- `h(u) ≤ C_h √u`
  have hh (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : binEntropy u ≤ C_h * √u := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, C_h]
    have h₁ : negMulLog u ≤ 2 / exp 1 * √u := by
      rcases hu0.eq_or_lt with rfl | hu
      · simp
      have ht := sqrt_pos.2 hu
      have e : u * log u = 2 * √u * (√u * log √u) := by
        rw [log_sqrt hu0]; nth_rewrite 1 [← mul_self_sqrt hu0]; ring
      have := hη _ ht
      rw [negMulLog, neg_mul, e]
      have h2 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * √u)
      have h3 : 2 / exp 1 * √u = 2 * √u * (exp 1)⁻¹ := by ring
      linarith
    have h₂ : negMulLog (1 - u) ≤ √u := by
      have := negMulLog_le_one_sub_self (show 0 ≤ 1 - u by linarith)
      have hs : u ≤ √u := by nlinarith [mul_self_sqrt hu0, sqrt_nonneg u, sqrt_le_one.2 hu1]
      linarith
    nlinarith
  have hu0 : 0 ≤ δ / (1 + δ) := by positivity
  have hu1 : δ / (1 + δ) ≤ δ := div_le_self hδ0 (by linarith)
  have hsq : √(δ / (1 + δ)) ≤ √δ := sqrt_le_sqrt hu1
  have hδsq : δ ≤ √δ := by
    nlinarith [mul_self_sqrt hδ0, sqrt_nonneg δ, sqrt_le_one.2 hδ1]
  have hC : 1 ≤ C_h := by rw [C_h]; have := exp_pos 1; linarith [div_pos two_pos this]
  have hlog : 0 ≤ log d := log_nonneg hd
  have hH := hh _ hu0 (hu1.trans hδ1)
  have hc : 0 < 1 + δ := by linarith
  have hA : (1 + δ) * binEntropy (δ / (1 + δ)) ≤ 2 * C_h * √δ :=
    calc (1 + δ) * binEntropy (δ / (1 + δ)) ≤ (1 + δ) * (C_h * √(δ / (1 + δ))) :=
          mul_le_mul_of_nonneg_left hH hc.le
      _ ≤ 2 * (C_h * √δ) := mul_le_mul (by linarith)
          (mul_le_mul_of_nonneg_left hsq (by linarith)) (by positivity) (by norm_num)
      _ = 2 * C_h * √δ := by ring
  have hB : δ * log d ≤ C_h * √δ * log d := by
    have h₁ := mul_le_mul_of_nonneg_right hδsq hlog
    have h₂ : √δ * log d ≤ C_h * (√δ * log d) :=
      le_mul_of_one_le_left (mul_nonneg (sqrt_nonneg δ) hlog) hC
    linarith [show C_h * √δ * log d = C_h * (√δ * log d) by ring]
  rw [log_mul (exp_pos 1).ne' (by linarith), log_exp]
  nlinarith [hA, hB]

omit [Fintype E] [DecidableEq E] in
/-- D2.4.1–D2.4.3, D2.4.5. For states `ρ, σ` on `D ⊗ E` with `δ = ½‖ρ - σ‖₁`:
`|S(D|E)_ρ - S(D|E)_σ| ≤ 2δ log d_D + (1+δ) h(δ/(1+δ))`. -/
theorem step_2_4_3 [Fintype E] [DecidableEq E] (ρ σ : _root_.MState (D × E)) :
    |qConditionalEnt ρ - qConditionalEnt σ| ≤ 2 * TrDistance ρ σ * log (Fintype.card D) +
      (1 + TrDistance ρ σ) * binEntropy (TrDistance ρ σ / (1 + TrDistance ρ σ)) := by
  set δ := TrDistance ρ σ with hδdef
  -- D2.4.2: `ρ - σ = P - N`, `Tr P = Tr N = δ`
  obtain ⟨P, N, hP, hN, hPN, hPtr, hNtr⟩ := _root_.MState.exists_sub_eq_sub ρ σ
  have hδ0 : 0 ≤ δ := mul_nonneg (by norm_num) (Matrix.traceNorm_nonneg _)
  rcases hδ0.eq_or_lt with h0 | hδ
  · -- D2.4.5: `δ = 0`, so `ρ = σ`
    have hP0 : P = 0 := by
      have h := (HermitianMat.trace_eq_zero_iff P).1 (by rw [hPtr]; exact h0.symm)
      exact HermitianMat.ext ((HermitianMat.zero_le_iff.1 hP).trace_eq_zero_iff.1 h)
    have hN0 : N = 0 := by
      have h := (HermitianMat.trace_eq_zero_iff N).1 (by rw [hNtr]; exact h0.symm)
      exact HermitianMat.ext ((HermitianMat.zero_le_iff.1 hN).trace_eq_zero_iff.1 h)
    have : ρ = σ := _root_.MState.ext (sub_eq_zero.1 (by rw [hPN, hP0, hN0, sub_zero]))
    subst this
    rw [← h0]
    simp
  -- D2.4.2: `τ₊ = P/δ`, `τ₋ = N/δ`, `u = δ/(1+δ)`
  let τp : _root_.MState (D × E) := ⟨δ⁻¹ • P, smul_nonneg (inv_nonneg.2 hδ.le) hP, by
    rw [HermitianMat.trace_smul, hPtr, inv_mul_cancel₀ hδ.ne']⟩
  let τn : _root_.MState (D × E) := ⟨δ⁻¹ • N, smul_nonneg (inv_nonneg.2 hδ.le) hN, by
    rw [HermitianMat.trace_smul, hNtr, inv_mul_cancel₀ hδ.ne']⟩
  have hc : 0 < 1 + δ := by linarith
  let u : Prob := ⟨δ / (1 + δ), by positivity, div_le_one_of_le₀ (by linarith) hc.le⟩
  have hu : (u : ℝ) * δ⁻¹ = (1 + δ)⁻¹ := by
    change δ / (1 + δ) * δ⁻¹ = _; field_simp
  have hu' : 1 - (u : ℝ) = (1 + δ)⁻¹ := by
    change 1 - δ / (1 + δ) = _; field_simp; ring
  -- D2.4.2: `ω = (ρ + δ τ₋)/(1+δ) = (σ + δ τ₊)/(1+δ)`
  have hω : (_root_.MState.cq (ProbDistribution.coin u) ![τn, ρ]).traceRight =
      (_root_.MState.cq (ProbDistribution.coin u) ![τp, σ]).traceRight := by
    refine _root_.MState.ext_m ?_
    rw [_root_.MState.cq_traceRight, _root_.MState.cq_traceRight]
    simp only [Fin.sum_univ_two, ProbDistribution.coin_val_zero, ProbDistribution.coin_val_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Prob.coe_one_minus]
    have hm : ρ.m + N.mat = P.mat + σ.m := by
      have := congrArg HermitianMat.mat hPN
      simp only [HermitianMat.mat_sub] at this
      exact sub_eq_sub_iff_add_eq_add.1 this
    change (u : ℝ) • (δ⁻¹ • N.mat) + (1 - (u : ℝ)) • ρ.m =
      (u : ℝ) • (δ⁻¹ • P.mat) + (1 - (u : ℝ)) • σ.m
    rw [smul_smul, smul_smul, hu, hu', ← smul_add, ← smul_add]
    congr 1
    rw [add_comm]
    exact hm
  -- D2.4.1 on both mixtures of `ω`, weights `(δ/(1+δ), 1/(1+δ))`, `H(p) = h(δ/(1+δ))`
  have hw (τ : Fin 2 → _root_.MState (D × E)) :
      (u : ℝ) * qConditionalEnt (τ 0) + (1 - u) * qConditionalEnt (τ 1) ≤
        qConditionalEnt (_root_.MState.cq (ProbDistribution.coin u) τ).traceRight ∧
      qConditionalEnt (_root_.MState.cq (ProbDistribution.coin u) τ).traceRight ≤
        (u : ℝ) * qConditionalEnt (τ 0) + (1 - u) * qConditionalEnt (τ 1) +
          binEntropy (δ / (1 + δ)) := by -- D2.4.1
    have h₁ := _root_.MState.sum_qConditionalEnt_le (ProbDistribution.coin u) τ
    have h₂ := _root_.MState.qConditionalEnt_le (ProbDistribution.coin u) τ
    simp only [Fin.sum_univ_two, ProbDistribution.coin_val_zero, ProbDistribution.coin_val_one,
      Prob.coe_one_minus, Hₛ_coin] at h₁ h₂
    exact ⟨h₁, h₂⟩
  obtain ⟨hρ₁, hρ₂⟩ := hw ![τn, ρ]
  obtain ⟨hσ₁, hσ₂⟩ := hw ![τp, σ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hω] at hρ₁ hρ₂ hσ₁ hσ₂
  -- D2.2 item 4: `|S(D|E)_{τ±}| ≤ log d_D`
  have hp := abs_le.1 (abs_qConditionalEnt_le_log_card τp)
  have hn := abs_le.1 (abs_qConditionalEnt_le_log_card τn)
  -- D2.4.3: multiply by `1 + δ`
  have hcu : (1 + δ) * (u : ℝ) = δ := by change (1 + δ) * (δ / (1 + δ)) = δ; field_simp
  have hc1u : (1 + δ) * (1 - (u : ℝ)) = 1 := by rw [hu']; field_simp
  have key {a b x y : ℝ} (h : (u : ℝ) * a + (1 - u) * b ≤
      (u : ℝ) * x + (1 - u) * y + binEntropy (δ / (1 + δ))) :
      b - y ≤ δ * (x - a) + (1 + δ) * binEntropy (δ / (1 + δ)) := by
    have := mul_le_mul_of_nonneg_left h hc.le
    have e₁ : (1 + δ) * ((u : ℝ) * a + (1 - u) * b) = δ * a + b := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, hcu, hc1u, one_mul]
    have e₂ : (1 + δ) * ((u : ℝ) * x + (1 - u) * y + binEntropy (δ / (1 + δ))) =
        δ * x + y + (1 + δ) * binEntropy (δ / (1 + δ)) := by
      rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, hcu, hc1u, one_mul]
    linarith
  have k₁ := key (hρ₁.trans hσ₂)
  have k₂ := key (hσ₁.trans hρ₂)
  rw [abs_le]
  constructor <;> nlinarith [hp.1, hp.2, hn.1, hn.2]

/-- D2.4 **Lemma 2.1**. Let `ρ, σ` be density operators on finite-dimensional `D ⊗ E`,
`δ = ½‖ρ - σ‖₁ ≤ 1`, `d_D = dim D`. Then
`|S(D|E)_ρ - S(D|E)_σ| ≤ 2δ log d_D + (1+δ) h(δ/(1+δ)) ≤ C √δ log(e d_D)`.
Same for `S(D)` (`E` trivial). -/
theorem lemma_2_1 {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] : ConditionalContinuity σ loc ℂ := by
  intro U X Y hX hY hd ρ τ
  have hS (ω : Arealaw.MState (Reg loc U) ℂ) :
      ω.toSubState.regionEntropy (Finset.union_subset hX hY) - ω.toSubState.regionEntropy hY =
        qConditionalEnt (unionState ω hd hX hY) := by
    rw [qConditionalEnt, Sᵥₙ_unionState, Sᵥₙ_traceLeft_unionState]
  have hδ : (ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
      (τ.toSubState.restrict (Finset.union_subset hX hY)) =
        TrDistance (unionState ρ hd hX hY) (unionState τ hd hX hY) := by
    rw [unionState, unionState, Arealaw.MState.trDistance_physlibEquiv]
    simp
  have hd1 : (1 : ℝ) ≤ Fintype.card (Reg loc X) := by
    have := (unionState ρ hd hX hY).nonempty
    have : Nonempty (Reg loc X) := ⟨(Classical.arbitrary (Reg loc X × Reg loc Y)).1⟩
    exact_mod_cast Fintype.card_pos
  have h₁ := step_2_4_3 (unionState ρ hd hX hY) (unionState τ hd hX hY)
  have h₂ := step_2_4_4 (hδ ▸ SubState.D₁_nonneg _ _) (hδ ▸ SubState.D₁_le_one _ _) hd1
  rw [hS, hS, hδ]
  refine ⟨h₁, h₁.trans (h₂.trans ?_)⟩
  -- D2.4.4: the paper's constant `2 C_h` is at most the statement's `4`
  have he : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hC : 2 * C_h ≤ 4 := by
    have := (div_le_one (exp_pos 1)).2 he
    rw [C_h]; linarith
  have hl : 0 ≤ log (exp 1 * Fintype.card (Reg loc X)) := log_nonneg (by nlinarith)
  have := mul_le_mul_of_nonneg_right hC (mul_nonneg (sqrt_nonneg
    (TrDistance (unionState ρ hd hX hY) (unionState τ hd hX hY))) hl)
  linarith [this]

end Lemma21

/-! ## D2.5 Pure-state trace distance -/

section D25

open Arealaw OpenAI Matrix
open scoped ComplexOrder MatrixOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U D E F X : Finset σ}

omit [∀ i, DecidableEq (loc i)] in
/-- D2.5. For unit vectors `ξ, η`: `½‖|ξ⟩⟨ξ| - |η⟩⟨η|‖₁ ≤ ‖ξ - η‖`, and the bound passes to the
reductions to every region `X`. -/
theorem step_2_5 (ξ η : Reg loc U → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (hη : star η ⬝ᵥ η = 1)
    (hX : X ⊆ U) :
    traceDist ((pureState ξ hξ).restrict hX) ((pureState η hη).restrict hX) ≤
      √(star (ξ - η) ⬝ᵥ (ξ - η)).re := by
  -- D2.5.1
  have h₁ : traceDist (pureState ξ hξ) (pureState η hη) = √(1 - ‖star ξ ⬝ᵥ η‖ ^ 2) := by
    rw [traceDist, MState.D₁_eq_traceNorm_div_two]
    exact traceNorm_vecMulVec_sub_vecMulVec_div_two hξ hη
  -- D2.5.2
  have h₂ : 1 - ‖star ξ ⬝ᵥ η‖ ^ 2 ≤ (star (ξ - η) ⬝ᵥ (ξ - η)).re := by
    have hηξ : star η ⬝ᵥ ξ = star (star ξ ⬝ᵥ η) := by
      rw [← Matrix.star_dotProduct_star, star_star, dotProduct_comm]
    have hre := Complex.re_le_norm (star ξ ⬝ᵥ η)
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hξ, hη, hηξ]
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    nlinarith [sq_nonneg (1 - ‖star ξ ⬝ᵥ η‖)]
  -- D2.5.3
  have h₃ := SubState.D₁_restrict_le hX (pureState ξ hξ).toSubState (pureState η hη).toSubState
  calc traceDist ((pureState ξ hξ).restrict hX) ((pureState η hη).restrict hX)
      ≤ traceDist (pureState ξ hξ) (pureState η hη) := h₃
    _ ≤ √(star (ξ - η) ⬝ᵥ (ξ - η)).re := h₁ ▸ Real.sqrt_le_sqrt h₂

end D25

/-! ## D2.6 Balls, graph neighborhoods, ambient dilations -/

/-- D2.6. `B_Λ(x,r) = {y ∈ Λ : d_Λ(x,y) ≤ r}`.  The neighbourhood `N^Λ_r(D)` is
`OpenAI.graphNbhd Λ D r` and the ambient dilation `T_j` is `OpenAI.ambientDilation T j`. -/
noncomputable abbrev ball (Λ : Finset (ℤ × ℤ)) (x : ℤ × ℤ) (r : ℕ) : Finset (ℤ × ℤ) :=
  graphNbhd Λ {x} r

/-- D2.7. `v_r = 1 + 2r(r+1)`. -/
def v (r : ℕ) : ℕ := 1 + 2 * r * (r + 1)

/-- D2.8. `μ_R = 2^(v_R - 1)`. -/
def μ (R : ℕ) : ℕ := 2 ^ (v R - 1)

section Counting

open Finset Matrix SimpleGraph
open scoped Matrix.Norms.L2Operator Kronecker

/-! ## D2.7 Ball cardinality -/

/-- The square-lattice graph induced on `Λ`, whose distance is `d_Λ`. -/
local notation "𝔾" Λ =>
  SimpleGraph.induce ((Λ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) (SimpleGraph.boxProd (hasse ℤ) (hasse ℤ))

theorem mem_ball {Λ : Finset (ℤ × ℤ)} {x y : ℤ × ℤ} {r : ℕ} :
    y ∈ ball Λ x r ↔ y ∈ Λ ∧ domainEDist Λ y x ≤ r := by
  simp [graphNbhd]

theorem mem_supports {Λ X : Finset (ℤ × ℤ)} {R : ℕ} :
    X ∈ supports Λ R ↔ X ⊆ Λ ∧ X.Nonempty ∧ domainEDiam Λ X ≤ R := by
  simp [supports]

theorem domainEDist_eq {Λ : Finset (ℤ × ℤ)} (x y : Λ) :
    domainEDist Λ x y = (𝔾 Λ).edist x y := by
  rw [domainEDist, dif_pos ⟨x.2, y.2⟩]
  rfl

/-- D2.7.1. A path of the induced graph changes `|·|₁` by at most one per edge. -/
theorem natAbs_add_natAbs_le_length {Λ : Finset (ℤ × ℤ)} {y x : Λ} (p : (𝔾 Λ).Walk y x) :
    ((y : ℤ × ℤ).1 - (x : ℤ × ℤ).1).natAbs + ((y : ℤ × ℤ).2 - (x : ℤ × ℤ).2).natAbs
      ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [comap_adj, Function.Embedding.subtype_apply, boxProd_adj, hasse_adj,
      Order.covBy_iff_add_one_eq] at h
    rw [Walk.length_cons]
    omega

/-- D2.7 (eq:ball-count). For every site `x` and integer `r ≥ 0`:
`|B_Λ(x,r)| ≤ v_r := 1 + 2r(r+1)`. -/
theorem eq_ball_count (Λ : Finset (ℤ × ℤ)) (x : ℤ × ℤ) (r : ℕ) : #(ball Λ x r) ≤ v r := by
  -- D2.7.1
  have h1 : ∀ y ∈ ball Λ x r, (y.1 - x.1).natAbs + (y.2 - x.2).natAbs ≤ r := by
    intro y hy
    obtain ⟨hy, hd⟩ := mem_ball.1 hy
    have hx : x ∈ Λ := by
      by_contra hx
      simp [domainEDist, hx] at hd
    rw [domainEDist_eq ⟨y, hy⟩ ⟨x, hx⟩] at hd
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (hd.trans_lt (ENat.natCast_lt_top r)).ne
    exact (natAbs_add_natAbs_le_length p).trans (ENat.natCast_le_natCast.1 (hp ▸ hd))
  -- D2.7.2
  exact card_le_of_forall_natAbs_add_natAbs_le x r h1

/-! ## D2.8 Term multiplicity and norm budget -/

/-- D2.8.1. A support through `x` lies in `B_Λ(x,R)`. -/
theorem subset_ball_of_mem_supports {Λ X : Finset (ℤ × ℤ)} {R : ℕ} {x : ℤ × ℤ}
    (hX : X ∈ supports Λ R) (hx : x ∈ X) : X ⊆ ball Λ x R := by
  obtain ⟨hXΛ, -, hd⟩ := mem_supports.1 hX
  exact fun y hy => mem_ball.2 ⟨hXΛ hy, (le_iSup₂_of_le (f := fun i (_ : i ∈ X) =>
    ⨆ j ∈ X, domainEDist Λ i j) y hy (le_iSup₂ (f := fun j (_ : j ∈ X) => domainEDist Λ y j)
      x hx)).trans hd⟩

/-- D2.8. For an anchor map `a` (`a X ∈ X`) and `μ_R = 2^(v_R - 1)`, for every `x ∈ Λ`:
`#{X ∋ x} ≤ μ_R`, `#{X anchored at x} ≤ μ_R`, `∑_{X ∋ x} ‖h_X‖ ≤ J μ_R`, and `|X| ≤ v_R` for
every support `X`. -/
theorem step_2_8 (Λ : Finset (ℤ × ℤ)) (R : ℕ) (x : ℤ × ℤ) :
    #{X ∈ supports Λ R | x ∈ X} ≤ μ R ∧
    (∀ a : Finset (ℤ × ℤ) → ℤ × ℤ, (∀ X ∈ supports Λ R, a X ∈ X) →
      #{X ∈ supports Λ R | a X = x} ≤ μ R) ∧
    (∀ {q : ℕ} (J : ℝ) (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
      IsAdmissible Λ R J Φ → ∑ X ∈ supports Λ R with x ∈ X, ‖Φ X‖ ≤ J * μ R) ∧
    ∀ X ∈ supports Λ R, #X ≤ v R := by
  -- D2.8.1, D2.8.2
  have h2 : #{X ∈ supports Λ R | x ∈ X} ≤ μ R := by
    by_cases hx : x ∈ Λ
    · have hxB : x ∈ ball Λ x R := mem_ball.2 ⟨hx, by simp [domainEDist_eq ⟨x, hx⟩ ⟨x, hx⟩]⟩
      calc #{X ∈ supports Λ R | x ∈ X} ≤ #((ball Λ x R).erase x).powerset :=
            card_le_card_of_injOn (·.erase x)
              (fun X hX => mem_powerset.2 (erase_subset_erase x
                (subset_ball_of_mem_supports (mem_filter.1 hX).1 (mem_filter.1 hX).2)))
              fun X hX Y hY => erase_injOn' x (mem_filter.1 hX).2 (mem_filter.1 hY).2
        _ = 2 ^ (#(ball Λ x R) - 1) := by rw [card_powerset, card_erase_of_mem hxB]
        _ ≤ μ R := Nat.pow_le_pow_right two_pos (Nat.sub_le_sub_right (eq_ball_count Λ x R) 1)
    · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun X hX hxX => hx ((mem_supports.1 hX).1 hxX))]
      exact Nat.zero_le _
  refine ⟨h2, ?_, ?_, ?_⟩
  -- D2.8.3
  · exact fun a ha => (card_le_card fun X hX => mem_filter.2
      ⟨(mem_filter.1 hX).1, (mem_filter.1 hX).2 ▸ ha X (mem_filter.1 hX).1⟩).trans h2
  · intro q J Φ hΦ
    have hJ : 0 ≤ J := (norm_nonneg _).trans (hΦ ∅ (empty_subset Λ)).2.1
    calc ∑ X ∈ supports Λ R with x ∈ X, ‖Φ X‖ ≤ #{X ∈ supports Λ R | x ∈ X} • J :=
          sum_le_card_nsmul _ _ _ fun X hX =>
            (hΦ X (mem_supports.1 (mem_filter.1 hX).1).1).2.1
      _ ≤ J * μ R := by
          rw [nsmul_eq_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hJ
  -- D2.8.4
  · intro X hX
    obtain ⟨y, hy⟩ := (mem_supports.1 hX).2.1
    exact (card_le_card (subset_ball_of_mem_supports hX hy)).trans (eq_ball_count Λ y R)

/-! ## D2.9 Terms split by a set -/

/-- D2.9.2. A path of the induced graph between the two sides of `D` meets an endpoint `z` of an
edge of `∂_Λ D`, and its initial segment up to `z` is no longer than the path. -/
theorem exists_cutEndpoints_of_walk {Λ D : Finset (ℤ × ℤ)} {u w : Λ} (p : (𝔾 Λ).Walk u w)
    (h : ¬((u : ℤ × ℤ) ∈ D ↔ (w : ℤ × ℤ) ∈ D)) :
    ∃ z : Λ, (z : ℤ × ℤ) ∈ cutEndpoints Λ D ∧ ∃ p' : (𝔾 Λ).Walk u z, p'.length ≤ p.length := by
  induction p with
  | nil => exact absurd Iff.rfl h
  | @cons u v w huv p ih =>
    by_cases hs : (u : ℤ × ℤ) ∈ D ↔ (v : ℤ × ℤ) ∈ D
    · obtain ⟨z, hz, p', hp'⟩ := ih fun h' => h (hs.trans h')
      exact ⟨z, hz, .cons huv p', by simp only [Walk.length_cons]; omega⟩
    refine ⟨u, ?_, .nil, by simp⟩
    have hadj : (hasse ℤ □ hasse ℤ).Adj u v := huv
    by_cases hu : (u : ℤ × ℤ) ∈ D
    · exact mem_union_left _ (mem_image.2 ⟨((u : ℤ × ℤ), (v : ℤ × ℤ)),
        (mk_mem_interedges_iff _).2 ⟨hu, mem_sdiff.2 ⟨v.2, fun hv => hs ⟨fun _ => hv, fun _ => hu⟩⟩,
          hadj⟩, rfl⟩)
    · exact mem_union_right _ (mem_image.2 ⟨((v : ℤ × ℤ), (u : ℤ × ℤ)),
        (mk_mem_interedges_iff _).2 ⟨by tauto, mem_sdiff.2 ⟨u.2, hu⟩, hadj.symm⟩, rfl⟩)

/-- D2.9 (eq:crossing-count). A support `X` is split by `D ⊆ Λ` if `X ∩ D ≠ ∅ ≠ X \ D`. Then
`#{terms split by D} ≤ 2 v_R μ_R |∂_Λ D|`. -/
theorem eq_crossing_count (Λ D : Finset (ℤ × ℤ)) (R : ℕ) :
    #{X ∈ supports Λ R | (X ∩ D).Nonempty ∧ (X \ D).Nonempty} ≤
      2 * v R * μ R * #(edgeBoundary Λ D) := by
  classical
  let a : Finset (ℤ × ℤ) → ℤ × ℤ := fun X => if hX : X.Nonempty then hX.choose else 0
  have ha : ∀ X ∈ supports Λ R, a X ∈ X := fun X hX => by
    simp only [a, dif_pos (mem_supports.1 hX).2.1]
    exact (mem_supports.1 hX).2.1.choose_spec
  let Z := cutEndpoints Λ D
  have h3 : ∀ X ∈ supports Λ R, (X ∩ D).Nonempty → (X \ D).Nonempty →
      a X ∈ Z.biUnion (ball Λ · R) := by
    intro X hX ⟨d, hd⟩ ⟨e, he⟩
    rw [mem_inter] at hd
    rw [mem_sdiff] at he
    -- D2.9.1
    obtain ⟨y, hyX, hy⟩ : ∃ y ∈ X, ¬(a X ∈ D ↔ y ∈ D) := by
      by_cases haD : a X ∈ D
      · exact ⟨e, he.1, by tauto⟩
      · exact ⟨d, hd.1, by tauto⟩
    obtain ⟨haΛ, hay⟩ := mem_ball.1 (subset_ball_of_mem_supports hX hyX (ha X hX))
    have hyΛ := (mem_supports.1 hX).1 hyX
    rw [domainEDist_eq ⟨a X, haΛ⟩ ⟨y, hyΛ⟩] at hay
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (hay.trans_lt (ENat.natCast_lt_top R)).ne
    -- D2.9.2
    obtain ⟨z, hz, p', hp'⟩ := exists_cutEndpoints_of_walk p hy
    -- D2.9.3
    refine mem_biUnion.2 ⟨z, hz, mem_ball.2 ⟨haΛ, ?_⟩⟩
    rw [domainEDist_eq ⟨a X, haΛ⟩ z]
    exact p'.edist_le.trans ((Nat.cast_le.2 hp').trans (hp ▸ hay))
  -- D2.9.4
  calc #{X ∈ supports Λ R | (X ∩ D).Nonempty ∧ (X \ D).Nonempty}
      ≤ #((Z.biUnion (ball Λ · R)).biUnion fun x => {X ∈ supports Λ R | a X = x}) :=
        card_le_card fun X hX => by
          obtain ⟨hX, h1, h2⟩ := mem_filter.1 hX
          exact mem_biUnion.2 ⟨a X, h3 X hX h1 h2, mem_filter.2 ⟨hX, rfl⟩⟩
    _ ≤ #(Z.biUnion (ball Λ · R)) * μ R :=
        card_biUnion_le_card_mul _ _ _ fun x _ => (step_2_8 Λ R x).2.1 a ha
    _ ≤ #Z * v R * μ R := by
        gcongr
        exact card_biUnion_le_card_mul _ _ _ fun z _ => eq_ball_count Λ z R
    _ ≤ 2 * #(edgeBoundary Λ D) * v R * μ R := by
        gcongr
        exact (card_union_le _ _).trans (by
          have := card_image_le (s := edgeBoundary Λ D) (f := Prod.fst)
          have := card_image_le (s := edgeBoundary Λ D) (f := Prod.snd)
          omega)
    _ = 2 * v R * μ R * #(edgeBoundary Λ D) := by ring

/-! ## D2.10 Product decomposition across a bipartition -/

/-- D2.10.1. A configuration of `X` is a pair of configurations of `X₁ = X ∩ B` and
`X₂ = X \ B`. -/
def cutEquiv {q : ℕ} (X B : Finset (ℤ × ℤ)) :
    Reg (Qudits q) (X ∩ B) × Reg (Qudits q) (X \ B) ≃ Reg (Qudits q) X :=
  (unionEquiv (disjoint_sdiff_inter X B).symm).symm.trans (regEquivOfEq (sup_inf_sdiff X B))

/-- D2.10. For a bipartition `B | Λ \ B` and a term `h_X`, split `X = X₁ ⊔ X₂` with
`X₁ = X ∩ B`, `X₂ = X \ B`; matrix units decompose `h_X = ∑ c_{ijkl} E_{ij} ⊗ E_{kl}`,
`c_{ijkl} = ⟨i,k|h_X|j,l⟩`, a sum of `q^{2|X|}` products with `|c_{ijkl}| ≤ ‖h_X‖` and
`‖E_{ij}‖ = ‖E_{kl}‖ = 1`. -/
theorem step_2_10 {q : ℕ} (X B : Finset (ℤ × ℤ))
    (h : Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ) :
    h = ∑ p, ∑ p', h (cutEquiv X B p) (cutEquiv X B p') •
        reindex (cutEquiv X B) (cutEquiv X B) (single p.1 p'.1 1 ⊗ₖ single p.2 p'.2 1) ∧
    Fintype.card ((Reg (Qudits q) (X ∩ B) × Reg (Qudits q) (X \ B)) ×
      (Reg (Qudits q) (X ∩ B) × Reg (Qudits q) (X \ B))) = q ^ (2 * #X) ∧
    (∀ p p', ‖h (cutEquiv X B p) (cutEquiv X B p')‖ ≤ ‖h‖) ∧
    (∀ i j : Reg (Qudits q) (X ∩ B), ‖single i j (1 : ℂ)‖ = 1) ∧
    ∀ k l : Reg (Qudits q) (X \ B), ‖single k l (1 : ℂ)‖ = 1 := by
  refine ⟨?_, ?_, fun _ _ => norm_entry_le_l2_opNorm _ _ _, by simp, by simp⟩
  -- D2.10.1
  · simp only [reindex_apply, single_kronecker_single, mul_one, submatrix_single_equiv,
      Equiv.symm_symm, smul_single, smul_eq_mul]
    conv_lhs => rw [matrix_eq_sum_single h]
    refine Fintype.sum_equiv (cutEquiv X B).symm _ _ fun w => ?_
    refine Fintype.sum_equiv (cutEquiv X B).symm _ _ fun w' => ?_
    simp
  -- D2.10.2
  · simp only [Fintype.card_prod, Fintype.card_pi, univ_eq_attach, Fintype.card_fin, prod_const,
      card_attach]
    rw [← card_sdiff_add_card_inter X B]
    ring

end Counting

section ZeroBoundary2

open Matrix SimpleGraph

/-! ## D2.12 Lemma 2.2 -/

section Glue

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, DecidableEq (loc i)]
  {Λ A X : Finset σ}

/-- A term supported in `A` acts on the `A`-factor of `glue x z` only. -/
theorem extendId_glue_of_subset (hA : A ⊆ Λ) (hXA : X ⊆ A)
    (L : Matrix (Reg loc X) (Reg loc X) ℂ) (x x' : Reg loc A) (z z' : Reg loc (Λ \ A)) :
    extendId (hXA.trans hA) L (glue x z) (glue x' z') =
      if z = z' then extendId hXA L x x' else 0 := by
  have hr : ∀ (y : Reg loc A) (w : Reg loc (Λ \ A)),
      restr (hXA.trans hA) (glue y w) = restr hXA y :=
    fun y w => funext fun i => by simp [restr, glue, hXA i.2]
  have hc : restr (S := Λ \ X) Finset.sdiff_subset (glue x z) =
      restr Finset.sdiff_subset (glue x' z') ↔
        z = z' ∧ restr (S := A \ X) Finset.sdiff_subset x = restr Finset.sdiff_subset x' := by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff, glue]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · simpa [hi.2] using h i ⟨hi.1, fun hX => hi.2 (hXA hX)⟩
      · simpa [hi.1] using h i ⟨hA hi.1, hi.2⟩
    · rintro ⟨hz, hx⟩ i ⟨hiΛ, hiX⟩
      by_cases hiA : i ∈ A
      · simpa [hiA] using hx i ⟨hiA, hiX⟩
      · simpa [hiA] using hz i ⟨hiΛ, hiA⟩
  simp only [extendId, of_apply, hr, hc]
  by_cases hz : z = z' <;> simp [hz]

/-- A term supported in `Λ \ A` acts on the `(Λ \ A)`-factor of `glue x z` only. -/
theorem extendId_glue_of_subset_sdiff (hA : A ⊆ Λ) (hXB : X ⊆ Λ \ A)
    (L : Matrix (Reg loc X) (Reg loc X) ℂ) (x x' : Reg loc A) (z z' : Reg loc (Λ \ A)) :
    extendId (hXB.trans Finset.sdiff_subset) L (glue x z) (glue x' z') =
      if x = x' then extendId hXB L z z' else 0 := by
  have hr : ∀ (y : Reg loc A) (w : Reg loc (Λ \ A)),
      restr (hXB.trans Finset.sdiff_subset) (glue y w) = restr hXB w :=
    fun y w => funext fun i => by simp [restr, glue, (Finset.mem_sdiff.1 (hXB i.2)).2]
  have hc : restr (S := Λ \ X) Finset.sdiff_subset (glue x z) =
      restr Finset.sdiff_subset (glue x' z') ↔
        x = x' ∧ restr (S := (Λ \ A) \ X) Finset.sdiff_subset z = restr Finset.sdiff_subset z' := by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff, glue]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := h i ⟨hA hi, fun hX => (Finset.mem_sdiff.1 (hXB hX)).2 hi⟩
        simpa [hi] using this
      · simpa [hi.1.2] using h i ⟨hi.1.1, hi.2⟩
    · rintro ⟨hx, hz⟩ i ⟨hiΛ, hiX⟩
      by_cases hiA : i ∈ A
      · simpa [hiA] using hx i hiA
      · simpa [hiA] using hz i ⟨⟨hiΛ, hiA⟩, hiX⟩
  simp only [extendId, of_apply, hr, hc]
  by_cases hx : x = x' <;> simp [hx]

end Glue

section ZeroBoundary

variable {q : ℕ} {Λ A : Finset (ℤ × ℤ)} {R : ℕ} {J Δ E₀ : ℝ}
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ}
  {Ω : Reg (Qudits q) Λ → ℂ}

/-- Uniqueness of the ground vector: under a positive gap every eigenvector of `H` with
eigenvalue `E₀` is a multiple of `Ω`. -/
theorem eq_smul_of_hasGlobalGap {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    {Ω v : ι → ℂ} (hgap : HasGlobalGap H Ω E₀ Δ) (hΔ : 0 < Δ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hE : H *ᵥ Ω = (E₀ : ℂ) • Ω) (hv : H *ᵥ v = (E₀ : ℂ) • v) : v = (star Ω ⬝ᵥ v) • Ω := by
  set w := v - (star Ω ⬝ᵥ v) • Ω with hw
  have hHw : (H - (E₀ : ℂ) • 1) *ᵥ w = 0 := by
    rw [hw, sub_mulVec, smul_mulVec, one_mulVec, mulVec_sub, mulVec_smul, hv, hE]
    module
  have hΩw : star Ω ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, hΩ, smul_eq_mul, mul_one, sub_self]
  have hPw : (1 - vecMulVec Ω (star Ω)) *ᵥ w = w := by
    rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, hΩw, MulOpposite.op_zero, zero_smul, sub_zero]
  have hgap' : (Δ : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤ H - (E₀ : ℂ) • 1 := hgap
  have h := (Matrix.le_iff.1 hgap').dotProduct_mulVec_nonneg w
  rw [sub_mulVec, hHw, smul_mulVec, hPw, zero_sub, dotProduct_neg, dotProduct_smul,
    smul_eq_mul, neg_nonneg] at h
  have hww : star w ⬝ᵥ w = 0 := by
    refine le_antisymm ?_ (dotProduct_star_self_nonneg w)
    have h' := mul_nonpos_of_nonneg_of_nonpos (Complex.zero_le_real.2 (inv_nonneg.2 hΔ.le)) h
    rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hΔ.ne', Complex.ofReal_one,
      one_mul] at h'
  exact sub_eq_zero.1 (dotProduct_star_self_eq_zero.1 hww)

/-- D2.12.3 in coefficient form: if every nonzero term lies in `A` or in `Λ \ A`, then
`H = H_A ⊗ 1 + 1 ⊗ H_{Λ∖A}`: on the coefficient matrix `N x z = v (glue x z)` it acts as
`N ↦ P N + N G`. -/
theorem exists_hamiltonian_coeff (hA : A ⊆ Λ) (hsplit : ∀ X ⊆ Λ, Φ X ≠ 0 → X ⊆ A ∨ X ⊆ Λ \ A) :
    ∃ (P : Matrix (Reg (Qudits q) A) (Reg (Qudits q) A) ℂ)
      (G : Matrix (Reg (Qudits q) (Λ \ A)) (Reg (Qudits q) (Λ \ A)) ℂ),
      ∀ (v : Reg (Qudits q) Λ → ℂ) (x : Reg (Qudits q) A) (z : Reg (Qudits q) (Λ \ A)),
        (hamiltonian Λ Φ *ᵥ v) (glue x z) =
          ∑ x', P x x' * v (glue x' z) + ∑ z', v (glue x z') * G z' z := by
  refine ⟨∑ X ∈ Λ.powerset.attach, if h : X.1 ⊆ A then extendId h (Φ X) else 0,
    ∑ X ∈ Λ.powerset.attach,
      if h : X.1 ⊆ Λ \ A ∧ ¬ X.1 ⊆ A then (extendId h.1 (Φ X))ᵀ else 0, fun v x z => ?_⟩
  have key : ∀ X ∈ Λ.powerset.attach,
      (extendId (Finset.mem_powerset.1 X.2) (Φ X) *ᵥ v) (glue x z) =
        ∑ x', (if h : X.1 ⊆ A then extendId h (Φ X) else 0) x x' * v (glue x' z) +
        ∑ z', v (glue x z') *
          (if h : X.1 ⊆ Λ \ A ∧ ¬ X.1 ⊆ A then (extendId h.1 (Φ X))ᵀ else 0) z' z := by
    intro X _
    have hX := Finset.mem_powerset.1 X.2
    simp only [mulVec, dotProduct, ← (glueEquiv hA).sum_comp, Fintype.sum_prod_type,
      glueEquiv_apply]
    by_cases hXA : X.1 ⊆ A
    · rw [dif_pos hXA, dif_neg (fun h => h.2 hXA)]
      simp [extendId_glue_of_subset hA hXA, ite_mul]
    by_cases hXB : X.1 ⊆ Λ \ A
    · rw [dif_neg hXA, dif_pos ⟨hXB, hXA⟩]
      simp [extendId_glue_of_subset_sdiff hA hXB, mul_comm]
    have h0 : Φ X = 0 := not_not.1 fun h => (hsplit X hX h).elim hXA hXB
    rw [dif_neg hXA, dif_neg (fun h => hXB h.1), h0]
    simp
  rw [hamiltonian, sum_mulVec, Finset.sum_apply, Finset.sum_congr rfl key, Finset.sum_add_distrib]
  simp only [Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ), Finset.sum_comm (s := Finset.univ)]

/-- The no-split core of Lemma 2.2 (and of D2.11.2): if no nonzero term of `H` is split by
`A`, the gapped ground vector has `S_Ω(A) = 0`. -/
theorem regionEntropy_eq_zero_of_split (hsplit : ∀ X ⊆ Λ, Φ X ≠ 0 → X ⊆ A ∨ X ⊆ Λ \ A)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω)
    (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ) (hΔ : 0 < Δ) (hA : A ⊆ Λ) :
    (pureState Ω hΩ).regionEntropy hA = 0 := by
  set M : Matrix (Reg (Qudits q) A) (Reg (Qudits q) (Λ \ A)) ℂ := Matrix.of fun x z => Ω (glue x z)
  -- D2.12.3
  obtain ⟨P, G, hPG⟩ := exists_hamiltonian_coeff hA hsplit
  -- D2.12.4: the ground space, in coefficient form, is `ℂ M`
  have huniq : ∀ N, P * N + N * G = (E₀ : ℂ) • N → ∃ c : ℂ, N = c • M := by
    intro N hN
    set v : Reg (Qudits q) Λ → ℂ := fun w => N (restr hA w) (restr Finset.sdiff_subset w)
    have hv : hamiltonian Λ Φ *ᵥ v = (E₀ : ℂ) • v := funext fun w => by
      have := congrFun (congrFun hN (restr hA w)) (restr Finset.sdiff_subset w)
      rw [← glue_restr hA w, hPG]
      simpa [v, mul_apply] using this
    refine ⟨star Ω ⬝ᵥ v, ?_⟩
    ext x z
    simpa [v, M] using congrFun (eq_smul_of_hasGlobalGap hgap hΔ hΩ hE hv) (glue x z)
  have hM : P * M + M * G = (E₀ : ℂ) • M := by
    ext x z
    simpa [M, mul_apply, hE] using (hPG Ω x z).symm
  obtain ⟨a, ha⟩ := huniq (P * M) (by rw [Matrix.mul_assoc, ← Matrix.mul_add, hM, Matrix.mul_smul])
  have hb : M * G = ((E₀ : ℂ) - a) • M := by rw [sub_smul, ← hM, ha]; abel
  -- D2.12.5: `M` has rank one, `Ω = Ω_A ⊗ Ω_{Λ∖A}`
  obtain ⟨x₀, z₀, h0⟩ : ∃ x z, M x z ≠ 0 := by
    by_contra! h
    have : Ω = 0 := funext fun w => by simpa [M] using h (restr hA w) (restr Finset.sdiff_subset w)
    simp [this] at hΩ
  have hu : P *ᵥ (fun x => M x z₀) = a • fun x => M x z₀ := funext fun x => by
    simpa [mulVec, dotProduct, mul_apply] using congrFun (congrFun ha x) z₀
  have hr : (fun z => M x₀ z) ᵥ* G = ((E₀ : ℂ) - a) • fun z => M x₀ z := funext fun z => by
    simpa [vecMul, dotProduct, mul_apply] using congrFun (congrFun hb x₀) z
  obtain ⟨c, hc⟩ := huniq (vecMulVec (fun x => M x z₀) fun z => M x₀ z) (by
    rw [mul_vecMulVec, vecMulVec_mul, hu, hr, smul_vecMulVec, vecMulVec_smul, ← add_smul,
      add_sub_cancel])
  have hc0 : c ≠ 0 := by
    rintro rfl
    simpa [vecMulVec_apply, h0] using congrFun (congrFun hc x₀) z₀
  have hMr : M = vecMulVec (fun x => M x z₀) (c⁻¹ • fun z => M x₀ z) := by
    rw [vecMulVec_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  -- D2.12.6: `ρ_A = M Mᴴ` is a rank-one projection, so `S_Ω(A) = 0`
  have hρ : ((pureState Ω hΩ).toSubState.restrict hA).M =
      vecMulVec (fun x => M x z₀)
        (((c⁻¹ • fun z => M x₀ z) ⬝ᵥ star (c⁻¹ • fun z => M x₀ z)) • star fun x => M x z₀) := by
    rw [← vecMulVec_mul_vecMulVec, ← conjTranspose_vecMulVec, ← hMr]
    ext x y
    simp only [SubState.restrict_M, ptrace, of_apply, mul_apply, conjTranspose_apply, M]
    rfl
  have htr := ((pureState Ω hΩ).restrict hA).trace_eq_one
  refine SubState.entropy_eq_zero_of_isIdempotentElem _ ?_
  obtain ⟨u, w, hρ⟩ : ∃ u w, ((pureState Ω hΩ).toSubState.restrict hA).M = vecMulVec u w :=
    ⟨_, _, hρ⟩
  rw [IsIdempotentElem, hρ, vecMulVec_mul_vecMulVec, vecMulVec_smul, dotProduct_comm,
    ← trace_vecMulVec, ← hρ]
  erw [htr, one_smul]

/-- Two sites of an admissible support are at `d_Λ`-distance at most `R`. -/
theorem domainEDist_le_of_mem_supports {X : Finset (ℤ × ℤ)} {x y : ℤ × ℤ}
    (hX : X ∈ supports Λ R) (hx : x ∈ X) (hy : y ∈ X) : domainEDist Λ x y ≤ R :=
  ((le_iSup₂ (f := fun y (_ : y ∈ X) => domainEDist Λ x y) y hy).trans
    (le_iSup₂ (f := fun x (_ : x ∈ X) => ⨆ y ∈ X, domainEDist Λ x y) x hx)).trans
    (Finset.mem_filter.1 hX).2.2

/-- D2.12 **Lemma 2.2.** Under the hypotheses of Theorem 1.1 ($H$ admissible, unique
normalized ground vector $\Omega$ up to phase, gap $\Delta$), if $A\subseteq\Lambda$ and
$\partial_\Lambda A=\varnothing$, then $S_\Omega(A)=0$. -/
theorem lemma_2_2 (hΦ : IsAdmissible Λ R J Φ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    (hΔ : 0 < Δ) (hA : A ⊆ Λ) (h : edgeBoundary Λ A = ∅) :
    (pureState Ω hΩ).regionEntropy hA = 0 := by
  -- D2.12.1: no edge of the induced graph joins `A` to `Λ \ A`
  have hcut : ∀ x ∈ A, ∀ y ∈ Λ \ A, ¬ (hasse ℤ □ hasse ℤ).Adj x y := fun x hx y hy hxy => by
    have : (x, y) ∈ edgeBoundary Λ A := (SimpleGraph.mem_interedges_iff _).2 ⟨hx, hy, hxy⟩
    simp [h] at this
  -- D2.12.2: a support has finite `d_Λ`-diameter, so it lies in `A` or in `Λ \ A`
  have hsplit : ∀ X ⊆ Λ, Φ X ≠ 0 → X ⊆ A ∨ X ⊆ Λ \ A := by
    intro X hXΛ h0
    have hX : X ∈ supports Λ R := by_contra fun hn => h0 ((hΦ X hXΛ).2.2 hn)
    by_contra! hc
    obtain ⟨y, hyX, hyA⟩ := Finset.not_subset.1 hc.1
    obtain ⟨x, hxX, hxB⟩ := Finset.not_subset.1 hc.2
    have hxA : x ∈ A := by_contra fun hxA => hxB (Finset.mem_sdiff.2 ⟨hXΛ hxX, hxA⟩)
    have hd := domainEDist_le_of_mem_supports hX hxX hyX
    rw [domainEDist, dif_pos ⟨hXΛ hxX, hXΛ hyX⟩] at hd
    obtain ⟨p⟩ := reachable_of_edist_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top R) hd)
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {v | v.1 ∈ A} hxA hyA
    exact hcut _ hd1 _ (Finset.mem_sdiff.2 ⟨d.snd.2, hd2⟩) d.adj
  -- D2.12.3–D2.12.6
  exact regionEntropy_eq_zero_of_split hsplit hΩ hE hgap hΔ hA

/-- D2.11 **Degenerate cases.** If $q=1$ or $\Lambda=\varnothing$: all entropies vanish.
If $R=0$: $H$ is a sum of on-site operators; uniqueness of its ground state makes $\Omega$ a
tensor product, so $S_\Omega(A)=0$ and Theorem 1.1 holds. Henceforth $q\ge2$, $R\ge1$,
$\Lambda\ne\varnothing$. -/
theorem step_2_11 :
    (∀ (q : ℕ) (Λ A : Finset (ℤ × ℤ)), q = 1 ∨ Λ = ∅ →
      ∀ (ρ : MState (Reg (Qudits q) Λ) ℂ) (hA : A ⊆ Λ), ρ.regionEntropy hA = 0) ∧
    (∀ (q : ℕ) (Λ A : Finset (ℤ × ℤ)) (J Δ E₀ : ℝ)
      (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
      IsAdmissible Λ 0 J Φ → ∀ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ → 0 < Δ →
      ∀ hA : A ⊆ Λ, (pureState Ω hΩ).regionEntropy hA = 0) := by
  refine ⟨fun q Λ A hq ρ hA => ?_, fun q Λ A J Δ E₀ Φ hΦ Ω hΩ hE hgap hΔ hA => ?_⟩
  · -- D2.11.1: `𝓗_A = ℂ`, so `ρ_A` is pure
    obtain ⟨_⟩ : Nonempty (Unique (Reg (Qudits q) A)) := by
      rcases hq with rfl | rfl
      · exact ⟨inferInstance⟩
      · have : IsEmpty A := ⟨fun i => by simpa using hA i.2⟩
        exact ⟨Pi.uniqueOfIsEmpty _⟩
    rw [SubState.regionEntropy_def, SubState.entropy_of_unique, SubState.restrict_M,
      trace_ptrace, ρ.tr_eq_one, Real.negMulLog_one]
  · -- D2.11.2: only singletons have `diam X ≤ 0`, and a singleton is not split by `A`
    refine regionEntropy_eq_zero_of_split (fun X hXΛ h0 => ?_) hΩ hE hgap hΔ hA
    have hX : X ∈ supports Λ 0 := by_contra fun hn => h0 ((hΦ X hXΛ).2.2 hn)
    obtain ⟨x, hx⟩ := (Finset.mem_filter.1 hX).2.1
    obtain rfl : X = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => by
      have hd := domainEDist_le_of_mem_supports hX hy hx
      rw [domainEDist, dif_pos ⟨hXΛ hy, hXΛ hx⟩, Nat.cast_zero, nonpos_iff_eq_zero,
        edist_eq_zero_iff] at hd
      exact congrArg Subtype.val hd⟩
    by_cases hxA : x ∈ A
    · exact Or.inl (Finset.singleton_subset_iff.2 hxA)
    · exact Or.inr (Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hXΛ hx, hxA⟩))

end ZeroBoundary

end ZeroBoundary2

end AreaLaw
