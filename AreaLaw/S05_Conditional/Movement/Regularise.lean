import AreaLaw.S05_Conditional.Movement.Setup
import AreaLaw.S05_Conditional.Lemma52

/-!
# §5.1 Lemma 5.1: removing faithfulness (D5.5.11) and entropy continuity (D5.10.3)

`lemma_5_1_of_faithful` derives `Lemma_5_1` from `Lemma_5_1_faithful` by the regularisation
`τ_ε = (1-ε) τ + ε I / dim(xU)`; `step_5_10_3` is Lemma 2.1 with D2.5.
-/

namespace AreaLaw

open Arealaw Matrix Filter Topology Conditional
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder

universe u v

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ : Finset σ}

omit [∀ i, DecidableEq (loc i)] in
private theorem nonempty_of_unit {θ : Reg loc Λ → ℂ} (hθ : star θ ⬝ᵥ θ = 1) :
    Nonempty (Reg loc Λ) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  simp [dotProduct] at hθ

/-- D5.10.3 (Lemma 2.1 with `D = x`, `E = P`, and D2.5). For unit `θ, θ'` and disjoint `x, P`:
`|S(x|P)_{θ'} − S(x|P)_θ| ≤ 4 √δ ℓ` with `δ = ½‖ρ_{xP}[θ'] − ρ_{xP}[θ]‖₁ ≤ ‖θ' − θ‖`. -/
theorem step_5_10_3 : Step_5_10_3.{u, v} := by
  intro σ _ loc _ _ Λ X P hX hP hXP θ θ' hθ hθ'
  have hne := nonempty_of_unit hθ
  have hd : 1 ≤ Fintype.card (Reg loc X) := Fintype.card_pos_iff.2 ⟨restr hX hne.some⟩
  -- D5.10.3: Lemma 2.1
  have h := (lemma_2_1 Λ X P hX hP hXP (pureState θ' hθ') (pureState θ hθ)).2
  -- D5.10.3: D2.5, `δ ≤ ‖θ' − θ‖`
  have hδ := step_2_5 θ' θ hθ' hθ (Finset.union_subset hX hP)
  rw [← Conditional.norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)] at hδ
  refine h.trans ?_
  gcongr
  · exact (zero_lt_one.trans_le (one_le_ℓ hd)).le
  · exact hδ
  · exact le_rfl

/-- D5.5.11 (remove faithfulness). `Lemma_5_1` from its faithful case: replace `τ` by
`τ_ε = (1-ε) τ + ε I / dim(xU)` (faithful, `Tr τ_ε ≤ 1`) and let `ε → 0⁺`; the positive power
`τ_ε^{[a/2]}` (exponent `a/2 > 0`) is continuous, so the bound passes to the limit. -/
theorem lemma_5_1_of_faithful (h : Lemma_5_1_faithful.{u, v}) : Lemma_5_1.{u, v} := by
  obtain ⟨c, C, hc, hC, hf⟩ := h
  refine ⟨c, C, hc, hC, ?_⟩
  intro σ _ loc _ _ Λ P X U F hP hX hU hF hΛ hPX hPU hPF hXU hXF hUF θ hθ a ha0 hac σ' τ hσ hσtr
    hτ hτtr
  have hne := nonempty_of_unit hθ
  set hXU' := Finset.union_subset hX hU
  have hd : 1 ≤ Fintype.card (Reg loc X) := Fintype.card_pos_iff.2 ⟨restr hX hne.some⟩
  have ha : 0 < a := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h (zero_lt_one.trans_le (one_le_ℓ hd)).le]
  set N : ℝ := (Fintype.card (Reg loc (X ∪ U)) : ℝ)
  have hN : 0 < N := by
    have : Nonempty (Reg loc (X ∪ U)) := ⟨restr hXU' hne.some⟩
    simp only [N]; exact_mod_cast Fintype.card_pos
  have hτh := hτ.isHermitian
  -- D5.5.11: `τ_ε = (1-ε) τ + ε I / N` is faithful with `Tr τ_ε ≤ 1`
  have hpd {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) : (aff (1 - ε) (ε / N) τ).PosDef :=
    PosDef.posSemidef_add (hτ.smul (Complex.zero_le_real.2 (by linarith [hε.2])))
      (PosDef.one.smul (Complex.zero_lt_real.2 (div_pos hε.1 hN)))
  have htr {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) : (aff (1 - ε) (ε / N) τ).trace.re ≤ 1 := by
    have : (aff (1 - ε) (ε / N) τ).trace.re = (1 - ε) * τ.trace.re + ε / N * N := by
      simp only [aff, trace_add, trace_smul, trace_one, smul_eq_mul, Complex.add_re,
        Complex.re_ofReal_mul, Complex.natCast_re, N]
    rw [this, div_mul_cancel₀ _ hN.ne']
    nlinarith [hε.2]
  -- D5.5.11: `τ_ε^{[a/2]} → τ^{[a/2]}`
  have hlim : Tendsto (fun ε ↦ bracketPow (aff (1 - ε) (ε / N) τ) ((a / 2 : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (bracketPow τ ((a / 2 : ℝ) : ℂ))) := by
    have e (ε : ℝ) : bracketPow (aff (1 - ε) (ε / N) τ) ((a / 2 : ℝ) : ℂ) =
        specFun hτh (fun t ↦ bfun ((a / 2 : ℝ) : ℂ) ((1 - ε) * t + ε / N)) := by
      rw [bracketPow_eq (isHermitian_aff hτh _ _), specFun_aff hτh]
    rw [bracketPow_eq hτh]
    refine (tendsto_specFun hτh fun k ↦ ?_).congr fun ε ↦ (e ε).symm
    set t := hτh.eigenvalues k
    have ht : 0 ≤ t := hτ.eigenvalues_nonneg k
    have hca : ContinuousAt (fun ε : ℝ ↦ ((((1 - ε) * t + ε / N) ^ (a / 2) : ℝ) : ℂ)) 0 :=
      Complex.continuous_ofReal.continuousAt.comp
        ((show ContinuousAt (fun ε : ℝ ↦ (1 - ε) * t + ε / N) 0 by fun_prop).rpow_const
          (Or.inr (by positivity)))
    have h0 := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simp only [sub_zero, one_mul, zero_div, add_zero] at h0
    rw [bfun_ofReal (by positivity) ht]
    refine h0.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    rw [bfun_ofReal (by positivity)
      (add_nonneg (mul_nonneg (by linarith [hε.2]) ht) (div_pos hε.1 hN).le)]
  -- D5.5.11: the norm is continuous in the `τ`-factor; pass to the limit
  have hL : Continuous (extendIdₗ (loc := loc) hXU') :=
    LinearMap.continuous_of_finiteDimensional _
  have hΦ : Continuous fun Y ↦ ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hP)
      (bracketPow σ' (a / 2 : ℝ)) * extendId hP (hatPow (marg θ hP) (-(a / 2 : ℝ))) *
      extendIdₗ hXU' Y * extendId hU (hatPow (marg θ hU) (-(a / 2 : ℝ)))) *ᵥ θ) :
        EuclideanSpace ℂ (Reg loc Λ))‖ :=
    continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp
      (((continuous_const.matrix_mul hL).matrix_mul continuous_const).matrix_mulVec
        continuous_const))
  refine le_of_tendsto ((hΦ.tendsto _).comp hlim) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  exact hf σ loc Λ P X U F hP hX hU hF hΛ hPX hPU hPF hXU hXF hUF θ hθ a ha0 hac σ' _ hσ hσtr
    (hpd hε) (htr hε)

end AreaLaw
