import AreaLaw.S04_Quasilocal.Propagation
import AreaLaw.S04_Quasilocal.Filter

/-!
# §4.2 Locality of the filtered terms `M_i` (D4.8)

Digest `digest/04-quasilocal.md` (D4.8), paper `paper/sections/03-quasilocal.tex` lines 272–286.
Graph-level (`Map.md`, Dimension): the localizing map is `E_{i,l}` on the graph induced on `Λ`
(`step_4_8`); the time-splitting argument itself is stated for any unital linear map `L`
satisfying the localization bound `eq:quasilocal-lr-ce` (`norm_M_sub_le`).

Some declarations here come from the v1 file `OpenAI/SpectralFilter/FilterLocality.lean`, whose
header records it as ported or adapted from `LionSR/QICLean` and `LionSR/TNLean` (see `NOTICE`).
-/

namespace AreaLaw

open MeasureTheory Matrix Finset Arealaw
open OpenAI (condExpect)
open Quasilocal (M)
open scoped Matrix.Norms.L2Operator

/-! ## The kernel tail (D4.8.3) -/

/-- D4.8.3. There is `K₀ > 0` with `|f(t)| ≤ K₀ (1 + |t|)^{-2} e^{-(c_f/2) T^α}` whenever
`0 ≤ T ≤ |t|`, `c_f` the decay rate of D4.5; the factor `(1 + |t|)^{-2}` is integrable. -/
theorem abs_f_le_tail {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ t T : ℝ, 0 ≤ T → T ≤ |t| →
      |f p δ t| ≤ K₀ / (1 + |t|) ^ 2 *
        Real.exp (-(GevreyBump.kernelDecayRate p δ / 2 * T ^ ((p : ℝ) / (p + 1)))) := by
  rw [f_eq_kernel]
  obtain ⟨A₄, hA₄⟩ := GevreyBump.one_add_abs_pow_mul_abs_kernel_le hp hδ 4
  set K := GevreyBump.kernelDecayConst δ
  set c := GevreyBump.kernelDecayRate p δ
  have hK : 0 < K := GevreyBump.kernelDecayConst_pos hδ
  have hc : 0 < c := GevreyBump.kernelDecayRate_pos hp hδ
  set A := max A₄ 1
  refine ⟨Real.sqrt (A * K), Real.sqrt_pos.mpr (by positivity), fun t T hT hTt => ?_⟩
  set R := 1 + |t|
  have hR0 : 0 < R := by positivity
  set α : ℝ := (p : ℝ) / (p + 1)
  have hα : 0 < α := by have : (0 : ℝ) < p := by exact_mod_cast hp
                        positivity
  have hf0 := abs_nonneg (GevreyBump.kernel p δ t)
  have h1 : |GevreyBump.kernel p δ t| ≤ A / R ^ 4 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (hA₄ t).trans (le_max_left _ _)
  have h2 : |GevreyBump.kernel p δ t| ≤ K * Real.exp (-(c * |t| ^ α)) :=
    GevreyBump.abs_kernel_le_exp hp hδ t
  have hsq : |GevreyBump.kernel p δ t| ^ 2 ≤ A / R ^ 4 * (K * Real.exp (-(c * |t| ^ α))) := by
    rw [sq]; exact mul_le_mul h1 h2 hf0 (by positivity)
  have hexp : Real.exp (-(c * |t| ^ α)) =
      Real.exp (-(c / 2 * |t| ^ α)) * Real.exp (-(c / 2 * |t| ^ α)) := by
    rw [← Real.exp_add]; ring_nf
  set X := Real.sqrt (A * K) / R ^ 2 * Real.exp (-(c / 2 * |t| ^ α))
  have hX : X ^ 2 = A / R ^ 4 * (K * Real.exp (-(c * |t| ^ α))) := by
    simp only [X, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ A * K), hexp]
    ring
  have hfX : |GevreyBump.kernel p δ t| ≤ X := by
    rw [← hX] at hsq
    exact (sq_le_sq₀ hf0 (by positivity)).mp hsq
  refine hfX.trans ?_
  have hTα : T ^ α ≤ |t| ^ α := Real.rpow_le_rpow hT hTt hα.le
  simp only [X]
  gcongr

theorem integrable_inv_one_add_abs_sq : Integrable fun t : ℝ => 1 / (1 + |t|) ^ 2 := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + |t| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg h1.le, Real.rpow_two, one_div]

/-- D4.8.4. `-c l / 2 ≤ c / 2 - (c / 2) l^α` for `0 ≤ l`, `0 ≤ c`, `0 < α ≤ 1`. -/
theorem neg_mul_le_sub_mul_rpow {c l α : ℝ} (hc : 0 ≤ c) (hl : 0 ≤ l) (hα : 0 < α)
    (hα1 : α ≤ 1) : -(c * l / 2) ≤ c / 2 - c / 2 * l ^ α := by
  have : l ^ α ≤ 1 + l := by
    rcases le_total l 1 with h | h
    · have := Real.rpow_le_one hl h hα.le; linarith
    · have := Real.rpow_le_rpow_of_exponent_le h hα1; rw [Real.rpow_one] at this; linarith
  nlinarith

/-! ## D4.8 for an abstract localizing map -/

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem integrable_f_smul_τ {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (B : Matrix n n ℂ) : Integrable fun t => f p δ t • τ H t B :=
  ((lemma_4_2 p hp δ hδ).2.2.2.2.2.2.2.2.2.1.norm.mul_const ‖B‖).mono'
    ((lemma_4_2 p hp δ hδ).2.2.2.2.2.2.2.2.2.1.aestronglyMeasurable.smul
      (continuous_τ H B).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => by rw [norm_smul, norm_τ hH])

/-- D4.8.1–3, explicit form. There is `K₁ ≥ 0`, depending only on `p, δ`, such that for every
linear map `L`, Hermitian `H` and `A`: if `‖τ_t(A) - L τ_t(A)‖ ≤ ‖A‖ min {2, C e^{v|t| - c l}}`
for all `t` (`v, c > 0`, `C, l ≥ 0`), then, splitting at `|t| = ε l` with `ε = c/(2v)`,
`‖F(A) - L F(A)‖ ≤ ‖A‖ (C e^{-cl/2} ‖f‖₁ + K₁ e^{-(c_f/2)(εl)^α})`, `F(A) = ∫ f(t) τ_t(A) dt`. -/
theorem norm_filter_sub_le {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ},
      H.IsHermitian → ∀ (A : Matrix n n ℂ) (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
      {C v c l : ℝ}, 0 ≤ C → 0 < v → 0 < c → 0 ≤ l →
      (∀ t : ℝ, ‖τ H t A - L (τ H t A)‖ ≤ ‖A‖ * min 2 (C * Real.exp (v * |t| - c * l))) →
      ‖(∫ t, f p δ t • τ H t A) - L (∫ t, f p δ t • τ H t A)‖ ≤
        ‖A‖ * (C * Real.exp (-(c * l / 2)) * (∫ t, |f p δ t|) +
          K₁ * Real.exp (-(GevreyBump.kernelDecayRate p δ / 2 *
            (c * l / (2 * v)) ^ ((p : ℝ) / (p + 1))))) := by
  obtain ⟨K₀, hK₀, htail⟩ := abs_f_le_tail hp hδ
  have hfi : Integrable (f p δ) := (lemma_4_2 p hp δ hδ).2.2.2.2.2.2.2.2.2.1
  set I := ∫ t : ℝ, 1 / (1 + |t|) ^ 2
  have hI : 0 ≤ I := integral_nonneg fun t => by positivity
  refine ⟨2 * K₀ * I, by positivity, ?_⟩
  intro n _ _ H hH A L C v c l hC hv hc hl hτ
  set T := c * l / (2 * v) with hTdef
  have hT : 0 ≤ T := by positivity
  set ε := Real.exp (-(GevreyBump.kernelDecayRate p δ / 2 * T ^ ((p : ℝ) / (p + 1))))
  set Lc := LinearMap.toContinuousLinearMap L
  have hLc : ∀ X, Lc X = L X := fun X => rfl
  have hint := integrable_f_smul_τ hp hδ hH A
  -- D4.8.1: `L` commutes with the Bochner integral.
  have hrepr : (∫ t, f p δ t • τ H t A) - L (∫ t, f p δ t • τ H t A) =
      ∫ t, f p δ t • (τ H t A - L (τ H t A)) := by
    rw [← hLc, ← Lc.integral_comp_comm hint, ← integral_sub hint (Lc.integrable_comp hint)]
    congr 1; funext t
    rw [hLc, LinearMap.map_smul_of_tower, smul_sub]
  rw [hrepr]
  set g : ℝ → ℝ := fun t => ‖A‖ * (C * Real.exp (-(c * l / 2)) * |f p δ t| +
    2 * K₀ * ε * (1 / (1 + |t|) ^ 2))
  have hpt : ∀ t, ‖f p δ t • (τ H t A - L (τ H t A))‖ ≤ g t := by
    intro t
    rw [norm_smul, Real.norm_eq_abs]
    have hf0 := abs_nonneg (f p δ t)
    have hb := hτ t
    have hA0 := norm_nonneg A
    rcases le_or_gt |t| T with ht | ht
    · -- D4.8.2: `|t| ≤ εl`
      have hmin : min 2 (C * Real.exp (v * |t| - c * l)) ≤ C * Real.exp (-(c * l / 2)) := by
        refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
        have : v * |t| ≤ v * T := mul_le_mul_of_nonneg_left ht hv.le
        have hvT : v * T = c * l / 2 := by rw [hTdef]; field_simp
        linarith
      calc |f p δ t| * ‖τ H t A - L (τ H t A)‖
          ≤ |f p δ t| * (‖A‖ * (C * Real.exp (-(c * l / 2)))) :=
            mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hmin hA0)) hf0
        _ ≤ g t := by
            simp only [g]
            have : 0 ≤ ‖A‖ * (2 * K₀ * ε * (1 / (1 + |t|) ^ 2)) := by positivity
            nlinarith
    · -- D4.8.3: `|t| > εl`, integrand `≤ 2‖A‖`
      have hft := htail t T hT ht.le
      calc |f p δ t| * ‖τ H t A - L (τ H t A)‖
          ≤ (K₀ / (1 + |t|) ^ 2 * ε) * (‖A‖ * 2) :=
            mul_le_mul hft (hb.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hA0))
              (norm_nonneg _) (by positivity)
        _ ≤ g t := by
            simp only [g]
            have : 0 ≤ ‖A‖ * (C * Real.exp (-(c * l / 2)) * |f p δ t|) := by positivity
            have he : K₀ / (1 + |t|) ^ 2 * ε * (‖A‖ * 2) =
                ‖A‖ * (2 * K₀ * ε * (1 / (1 + |t|) ^ 2)) := by ring
            nlinarith
  have hgint : Integrable g :=
    ((hfi.abs.const_mul _).add (integrable_inv_one_add_abs_sq.const_mul _)).const_mul _
  refine (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)).trans_eq ?_
  simp only [g]
  rw [integral_const_mul, integral_add (hfi.abs.const_mul _)
    (integrable_inv_one_add_abs_sq.const_mul _), integral_const_mul, integral_const_mul]
  simp only [I, ε]
  ring

/-- D4.8 for an abstract unital linear map `L` with the localization bound
`eq:quasilocal-lr-ce` at radius `l`: there are `C' ≥ 0`, `c'' > 0`, depending only on
`p, δ, C, v, c`, with `‖M_i - L M_i‖ ≤ C' e^{-c'' l^α} ‖h_i‖`, `α = p/(p+1)`. -/
theorem norm_M_sub_le {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {C v c : ℝ} (hC : 0 ≤ C)
    (hv : 0 < v) (hc : 0 < c) :
    ∃ C' c'' : ℝ, 0 ≤ C' ∧ 0 < c'' ∧ ∀ {n : Type*} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ}, H.IsHermitian → ∀ (Ω : n → ℂ) (h : Matrix n n ℂ)
      (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), L 1 = 1 → ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖τ H t h - L (τ H t h)‖ ≤ ‖h‖ * min 2 (C * Real.exp (v * |t| - c * l))) →
      ‖M H Ω (f p δ) h - L (M H Ω (f p δ) h)‖ ≤
        C' * Real.exp (-(c'' * l ^ ((p : ℝ) / (p + 1)))) * ‖h‖ := by
  obtain ⟨K₁, hK₁, hloc⟩ := norm_filter_sub_le hp hδ
  set α : ℝ := (p : ℝ) / (p + 1)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hα : 0 < α := by positivity
  have hα1 : α ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  set cf := GevreyBump.kernelDecayRate p δ
  have hcf : 0 < cf := GevreyBump.kernelDecayRate_pos hp hδ
  set c₂ := min (c / 2) (cf / 2 * (c / (2 * v)) ^ α)
  have hc₂ : 0 < c₂ := lt_min (by positivity) (by positivity)
  have hf1 : 0 ≤ ∫ t, |f p δ t| := integral_nonneg fun t => abs_nonneg _
  refine ⟨C * Real.exp (c / 2) * (∫ t, |f p δ t|) + K₁, c₂, by positivity, hc₂, ?_⟩
  intro n _ _ H hH Ω h L hL1 l hl hτ
  -- D4.8.1: `L` fixes the scalar.
  have hML : M H Ω (f p δ) h - L (M H Ω (f p δ) h) =
      (∫ t, f p δ t • τ H t h) - L (∫ t, f p δ t • τ H t h) := by
    simp only [M, map_sub, map_smul, hL1]; abel
  rw [hML]
  refine (hloc hH h L hC hv hc hl hτ).trans ?_
  -- D4.8.4
  have hl' : 0 ≤ l ^ α := Real.rpow_nonneg hl _
  have e1 : Real.exp (-(c * l / 2)) ≤ Real.exp (c / 2) * Real.exp (-(c₂ * l ^ α)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ((neg_mul_le_sub_mul_rpow hc.le hl hα hα1).trans ?_)
    have : c₂ * l ^ α ≤ c / 2 * l ^ α := mul_le_mul_of_nonneg_right (min_le_left _ _) hl'
    linarith
  have e2 : Real.exp (-(cf / 2 * (c * l / (2 * v)) ^ α)) ≤ Real.exp (-(c₂ * l ^ α)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    rw [show c * l / (2 * v) = c / (2 * v) * l by ring,
      Real.mul_rpow (by positivity) hl, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hl'
  have hA0 := norm_nonneg h
  calc ‖h‖ * (C * Real.exp (-(c * l / 2)) * (∫ t, |f p δ t|) +
          K₁ * Real.exp (-(cf / 2 * (c * l / (2 * v)) ^ α)))
      ≤ ‖h‖ * (C * (Real.exp (c / 2) * Real.exp (-(c₂ * l ^ α))) * (∫ t, |f p δ t|) +
          K₁ * Real.exp (-(c₂ * l ^ α))) := by gcongr
    _ = (C * Real.exp (c / 2) * (∫ t, |f p δ t|) + K₁) * Real.exp (-(c₂ * l ^ α)) * ‖h‖ := by
        ring

end Abstract

/-! ## D4.8 on the graph induced on `Λ` -/

namespace GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- `E_{i,l}` as a linear map. -/
noncomputable def Eₗ (Λ : Finset σ) (a : σ) (l : ℕ) :
    Matrix (Reg loc Λ) (Reg loc Λ) ℂ →ₗ[ℂ] Matrix (Reg loc Λ) (Reg loc Λ) ℂ where
  toFun := E G Λ a l
  map_add' A B := by simp [E, condExpect, smul_add]
  map_smul' c A := by simp [E, condExpect, smul_comm _ c]

end GraphDomain

section Graph

open GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) (V : ℕ → ℕ)
  (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
  {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)]

include hV in
/-- D4.8 (eq:quasilocal-filter-locality). For `p ≥ 1`, `α = p/(p+1)`, `δ > 0` and the
constants `R, J` of `Φ`: there are `C' ≥ 0`, `c'' > 0` (depending on `p, δ, R, J, V` and the
rate `c > 0` of D4.4, not on `Λ`) such that for every label `X ∈ supports` with anchor `a ∈ X`,
every `Ω` and every integer `l ≥ 0`, `‖M_i - E_{i,l}(M_i)‖ ≤ C' e^{-c'' l^α} ‖h_i‖`, with
`h_i = Φ_X ⊗ I` and `M_i` the centered filtered term of D4.7 for `f` of D4.5. -/
theorem step_4_8 {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) (R : ℕ) (J : ℝ) {c : ℝ}
    (hc : 0 < c) :
    ∃ C' c'' : ℝ, 0 ≤ C' ∧ 0 < c'' ∧ ∀ {Λ : Finset σ}
      {Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ}, IsAdmissible G Λ R J Φ →
      ∀ {X : Finset σ} (hX : X ∈ supports G Λ R) {a : σ}, a ∈ X → ∀ (Ω : Reg loc Λ → ℂ)
      (l : ℕ),
      ‖M (hamiltonian Λ Φ) Ω (f p δ) (extendId ((GraphDomain.mem_supports G).1 hX).1 (Φ X)) -
          E G Λ a l (M (hamiltonian Λ Φ) Ω (f p δ)
            (extendId ((GraphDomain.mem_supports G).1 hX).1 (Φ X)))‖ ≤
        C' * Real.exp (-(c'' * (l : ℝ) ^ ((p : ℝ) / (p + 1)))) *
          ‖extendId ((GraphDomain.mem_supports G).1 hX).1 (Φ X)‖ := by
  set v : ℝ := |2 * (V R * J * μ V R) * Real.exp (c * R)| + 1
  obtain ⟨C', c'', hC', hc'', hM⟩ := norm_M_sub_le hp hδ (C := 2 * Real.exp (c * R)) (v := v)
    (by positivity) (by positivity) hc
  refine ⟨C', c'', hC', hc'', fun {Λ Φ} hΦ {X} hX {a} ha Ω l => ?_⟩
  have h1 : E G Λ a l (1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) = 1 := (eq_quasilocal_ce Λ a l).1
  refine hM (isHermitian_hamiltonian G hΦ) Ω _ (Eₗ G Λ a l) h1 (Nat.cast_nonneg l) fun t => ?_
  refine ((lemma_4_1 G V hV R J hc hΦ hX ha ⟨Φ X, rfl⟩ t).2 l).trans ?_
  gcongr
  exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)

end Graph

end AreaLaw
