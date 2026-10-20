import AreaLawRefactored.S04_Quasilocal.Setup

/-!
# §4.2 The centered filtered terms `M_i`

Digest `digest/04-quasilocal.md` (D4.7), paper `paper/sections/03-quasilocal.tex` lines 249–270.
Generality `any d`: no geometry. An arbitrary finite index type `ι`, a finite label set `s` with
Hermitian terms `h_i`, `‖h_i‖ ≤ J`, `H = ∑ h_i`, a unit ground vector `Ω` with the global gap
`H - E₀ ≥ Δ (I - |Ω⟩⟨Ω|)`. The filter `f` of D4.5 enters through its properties: `f ∈ L¹`,
`∫ f = 1` (that is, `χ(0) = 1`) and `χ(ω) = ∫ f(t) e^{itω} dt = 0` for `|ω| ≥ δ`, for any
`δ ≤ Δ` (D4.7 uses `δ = Δ/2`).
-/

open MeasureTheory Matrix Complex
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix exponential acts on an eigenvector by the exponential of the eigenvalue. -/
theorem exp_mulVec_of_mulVec_eq_smul (X : Matrix ι ι ℂ) {w : ι → ℂ} {c : ℂ}
    (h : X *ᵥ w = c • w) : NormedSpace.exp X *ᵥ w = Complex.exp c • w := by
  have hpow : ∀ k : ℕ, (X ^ k) *ᵥ w = c ^ k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  let L : Matrix ι ι ℂ →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ w
      map_add' := fun M N => Matrix.add_mulVec M N w
      map_smul' := fun c M => Matrix.smul_mulVec c M w }
  have hL : ∀ M : Matrix ι ι ℂ, L M = M *ᵥ w := fun M => rfl
  rw [NormedSpace.exp_eq_tsum ℂ, ← hL, L.map_tsum (NormedSpace.expSeries_summable' X)]
  simp_rw [map_smul, hL, hpow, smul_smul]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
  simpa only [smul_eq_mul] using
    ((NormedSpace.expSeries_summable' (𝕂 := ℂ) c).tsum_smul_const w)

end Matrix

namespace AreaLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The Heisenberg evolution `τ_t` -/

section Tau

variable {H : Matrix ι ι ℂ}

theorem exp_smul_conjTranspose (hH : H.IsHermitian) (c : ℂ) :
    (NormedSpace.exp (c • H))ᴴ = NormedSpace.exp (star c • H) := by
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hH.eq]

theorem exp_smul_mul_exp_neg_smul (H : Matrix ι ι ℂ) (c : ℂ) :
    NormedSpace.exp (c • H) * NormedSpace.exp ((-c) • H) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl H).smul_left c).smul_right (-c)),
    ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]

theorem exp_I_smul_mem_unitary (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t * I) • H) ∈ unitary (Matrix ι ι ℂ) := by
  rw [← Matrix.unitaryGroup, Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose,
    exp_smul_conjTranspose hH]
  convert exp_smul_mul_exp_neg_smul H ((t : ℂ) * I) using 4
  simp [Complex.conj_ofReal]

theorem exp_neg_I_smul_mem_unitary (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-(t * I)) • H) ∈ unitary (Matrix ι ι ℂ) := by
  have := exp_I_smul_mem_unitary hH (-t)
  rwa [Complex.ofReal_neg, neg_mul] at this

/-- `‖τ_t(B)‖ = ‖B‖`. -/
theorem norm_τ (hH : H.IsHermitian) (t : ℝ) (B : Matrix ι ι ℂ) : ‖τ H t B‖ = ‖B‖ := by
  rw [τ, CStarRing.norm_mul_mem_unitary _ (exp_neg_I_smul_mem_unitary hH t),
    CStarRing.norm_mem_unitary_mul _ (exp_I_smul_mem_unitary hH t)]

theorem continuous_τ (H B : Matrix ι ι ℂ) : Continuous fun t => τ H t B := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  unfold τ
  fun_prop

/-- `τ_t` is a `*`-map: `τ_t(B)ᴴ = τ_t(Bᴴ)`. -/
theorem τ_conjTranspose (hH : H.IsHermitian) (t : ℝ) (B : Matrix ι ι ℂ) :
    (τ H t B)ᴴ = τ H t Bᴴ := by
  rw [τ, τ, conjTranspose_mul, conjTranspose_mul, exp_smul_conjTranspose hH,
    exp_smul_conjTranspose hH, Matrix.mul_assoc]
  have hs : star ((t : ℂ) * I) = -(t * I) := by simp [Complex.conj_ofReal]
  rw [hs, star_neg, hs, neg_neg]

theorem τ_sum {κ : Type*} (s : Finset κ) (t : ℝ) (h : κ → Matrix ι ι ℂ) :
    τ H t (∑ i ∈ s, h i) = ∑ i ∈ s, τ H t (h i) := by
  simp only [τ, Finset.mul_sum, Finset.sum_mul]

/-- `τ_t(H) = H`. -/
theorem τ_self (H : Matrix ι ι ℂ) (t : ℝ) : τ H t H = H := by
  have hc : Commute (NormedSpace.exp (((t : ℂ) * I) • H)) H :=
    ((Commute.refl H).smul_left _).exp_left
  rw [τ, hc.eq, Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, Matrix.mul_one]

/-- Matrix elements of `τ_t(A)` between eigenvectors: `e^{it(E - E')} ⟨v, A w⟩`. -/
theorem dotProduct_τ_mulVec (hH : H.IsHermitian) (A : Matrix ι ι ℂ) {v w : ι → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) (t : ℝ) :
    star v ⬝ᵥ (τ H t A *ᵥ w) = Complex.exp (t * (E - E') * I) * (star v ⬝ᵥ (A *ᵥ w)) := by
  have hexp : ∀ (c : ℂ) {u : ι → ℂ} {e : ℝ}, H *ᵥ u = (e : ℂ) • u →
      NormedSpace.exp (c • H) *ᵥ u = Complex.exp (c * e) • u := fun c u e hu =>
    Matrix.exp_mulVec_of_mulVec_eq_smul _ (by rw [Matrix.smul_mulVec, hu, smul_smul])
  have hstar : star v ᵥ* NormedSpace.exp (((t : ℂ) * I) • H) =
      Complex.exp (t * E * I) • star v := by
    rw [← conjTranspose_conjTranspose (NormedSpace.exp _), ← Matrix.star_mulVec,
      exp_smul_conjTranspose hH, hexp _ hv, star_smul, Complex.star_def, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
    ring
  rw [τ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hexp _ hw, Matrix.mulVec_smul,
    Matrix.mulVec_smul, dotProduct_smul, dotProduct_mulVec, hstar, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end Tau

/-! ## D4.7 The centered filtered terms -/

/-- D4.7. The centered filtered term `M_i = ∫_ℝ f(t) τ_t(h_i) dt - ⟨Ω, h_i Ω⟩ I`. In the
section namespace `Quasilocal`: `AreaLaw.M` is the moment generating function of D3.1. -/
noncomputable def Quasilocal.M (H : Matrix ι ι ℂ) (Ω : ι → ℂ) (f : ℝ → ℝ) (h : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (∫ t, f t • τ H t h) - (star Ω ⬝ᵥ (h *ᵥ Ω)) • 1

open Quasilocal (M)

/-- D4.7. With `f` from D4.5 at `δ = Δ/2`,
`M_i = ∫_ℝ f(t) τ_t(h_i) dt - ⟨Ω, h_i Ω⟩ I`.
The integral converges in norm; `M_i = M_i^*`; `M_i Ω = 0`; `∑_i M_i = H - E₀ I`;
`‖M_i‖ ≤ J (‖f‖₁ + 1)`. -/
theorem step_4_7 {κ : Type*} (s : Finset κ) (h : κ → Matrix ι ι ℂ) {J : ℝ}
    (hh : ∀ i ∈ s, (h i).IsHermitian) (hJ : ∀ i ∈ s, ‖h i‖ ≤ J) {H : Matrix ι ι ℂ}
    (hH : H = ∑ i ∈ s, h i) {Ω : ι → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1) {E₀ Δ δ : ℝ}
    (hHΩ : H *ᵥ Ω = (E₀ : ℂ) • Ω) (hgap : OpenAI.HasGlobalGap H Ω E₀ Δ) (hΔ : 0 < Δ)
    (hδ : δ ≤ Δ) {f : ℝ → ℝ} (hf : Integrable f) (hf1 : ∫ t, f t = 1)
    (hχ : ∀ ω : ℝ, δ ≤ |ω| → ∫ t, (f t : ℂ) * Complex.exp (t * ω * Complex.I) = 0) :
    (∀ i ∈ s, Integrable fun t => f t • τ H t (h i)) ∧
    (∀ i ∈ s, (M H Ω f (h i)).IsHermitian) ∧
    (∀ i ∈ s, M H Ω f (h i) *ᵥ Ω = 0) ∧
    ∑ i ∈ s, M H Ω f (h i) = H - (E₀ : ℂ) • 1 ∧
    ∀ i ∈ s, ‖M H Ω f (h i)‖ ≤ J * ((∫ t, |f t|) + 1) := by
  have hHh : H.IsHermitian := by
    rw [hH, IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun i hi => (hh i hi).eq
  -- D4.7.1 Norm convergence: `‖τ_t(h_i)‖ = ‖h_i‖`, `f ∈ L¹`.
  have hint : ∀ B : Matrix ι ι ℂ, Integrable fun t => f t • τ H t B := fun B =>
    (hf.norm.mul_const ‖B‖).mono'
      (hf.aestronglyMeasurable.smul (continuous_τ H B).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [norm_smul, norm_τ hHh])
  -- D4.7.1 Hermitian: `f` real, `τ_t` a `*`-map.
  have hFstar : ∀ B : Matrix ι ι ℂ, (∫ t, f t • τ H t B)ᴴ = ∫ t, f t • τ H t Bᴴ := by
    intro B
    have := (starL' ℝ : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ).integral_comp_comm (μ := volume)
      (fun t => f t • τ H t B)
    simp only [starL'_apply] at this
    rw [← star_eq_conjTranspose, ← this]
    congr 1; funext t
    rw [star_smul, star_trivial, star_eq_conjTranspose, τ_conjTranspose hHh]
  -- D4.7.2 Eigenbasis of `H`: `⟨E| ∫ f τ_t(A) |E'⟩ = χ(E - E') ⟨E|A|E'⟩`.
  have hF : ∀ (A : Matrix ι ι ℂ) {v w : ι → ℂ} {E E' : ℝ}, H *ᵥ v = (E : ℂ) • v →
      H *ᵥ w = (E' : ℂ) • w → star v ⬝ᵥ ((∫ t, f t • τ H t A) *ᵥ w) =
        (∫ t, (f t : ℂ) * Complex.exp (t * ((E - E' : ℝ) : ℂ) * Complex.I)) *
          (star v ⬝ᵥ (A *ᵥ w)) := by
    intro A v w E E' hv hw
    let L : Matrix ι ι ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun X => star v ⬝ᵥ (X *ᵥ w)
        map_add' := fun X Y => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c X => by simp [Matrix.smul_mulVec, dotProduct_smul] }
    have hL : ∀ X, L X = star v ⬝ᵥ (X *ᵥ w) := fun X => rfl
    rw [← hL, ← L.integral_comp_comm (hint A), ← integral_mul_const]
    congr 1; funext t
    rw [L.map_smul_of_tower, hL, dotProduct_τ_mulVec hHh A hv hw, Complex.real_smul]
    push_cast; ring
  -- D4.7.3 Gap: on `Ω^⊥`, an eigenvector of energy `E` has `E - E₀ ≥ Δ`.
  have hgv : ∀ {x : ι → ℂ} {E : ℝ}, H *ᵥ x = (E : ℂ) • x → star Ω ⬝ᵥ x = 0 →
      0 ≤ ((E : ℂ) - E₀ - Δ) * (star x ⬝ᵥ x) := by
    intro x E hx hΩx
    have := (Matrix.le_iff.mp hgap).dotProduct_mulVec_nonneg x
    simpa [sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hΩx, hx, dotProduct_sub,
      sub_mul, mul_sub] using this
  have hχ0 : ∫ t, (f t : ℂ) * Complex.exp (t * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by
    simp [integral_complex_ofReal, hf1]
  -- D4.7.4 Only `E = E₀` survives: `∫ f τ_t(A) Ω = ⟨Ω, A Ω⟩ Ω`.
  have hFΩ : ∀ A : Matrix ι ι ℂ,
      (∫ t, f t • τ H t A) *ᵥ Ω = (star Ω ⬝ᵥ (A *ᵥ Ω)) • Ω := by
    intro A
    set b := hHh.eigenvectorBasis
    rw [← sub_eq_zero]
    apply WithLp.toLp_injective 2
    rw [WithLp.toLp_zero, ← b.sum_repr' (WithLp.toLp 2 _)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_eq_zero]
    left
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    set u : ι → ℂ := ⇑(b k)
    set E := hHh.eigenvalues k
    have hu : H *ᵥ u = (E : ℂ) • u := by
      rw [hHh.mulVec_eigenvectorBasis, Complex.coe_smul]
    have hu1 : star u ⬝ᵥ u = 1 := by
      have := orthonormal_iff_ite.mp b.orthonormal k k
      rw [if_pos rfl, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
      exact this
    rw [dotProduct_sub, dotProduct_smul, hF A hu hHΩ, smul_eq_mul]
    by_cases hE : E = E₀
    · -- D4.7.4 the ground eigenvector is a multiple of `Ω`
      set a := star Ω ⬝ᵥ u
      have hx : H *ᵥ (u - a • Ω) = (E₀ : ℂ) • (u - a • Ω) := by
        rw [mulVec_sub, Matrix.mulVec_smul, hu, hHΩ, hE, smul_sub, smul_comm]
      have hΩx : star Ω ⬝ᵥ (u - a • Ω) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, hΩ, smul_eq_mul, mul_one, sub_self]
      have h1 := hgv hx hΩx
      have h2 := dotProduct_star_self_nonneg (u - a • Ω)
      have h3 : star (u - a • Ω) ⬝ᵥ (u - a • Ω) = 0 := by
        have hΔ' : (0 : ℂ) < Δ := by exact_mod_cast hΔ
        rw [sub_self, zero_sub, neg_mul] at h1
        have := mul_nonneg hΔ'.le h2
        exact (mul_eq_zero.mp (le_antisymm (neg_nonneg.mp h1) this)).resolve_left hΔ'.ne'
      have hua : u = a • Ω := sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp h3)
      rw [hE, sub_self, hχ0, hua, star_smul, smul_dotProduct, smul_dotProduct, hΩ]
      simp only [smul_eq_mul]
      ring
    · -- D4.7.3 an excited eigenvector is orthogonal to `Ω`, at energy `≥ E₀ + Δ`
      have horth : star u ⬝ᵥ Ω = 0 := by
        have h1 : star (H *ᵥ u) ⬝ᵥ Ω = star u ⬝ᵥ (H *ᵥ Ω) := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hHh.eq]
        rw [hu, hHΩ, star_smul, smul_dotProduct, dotProduct_smul, Complex.star_def,
          Complex.conj_ofReal, smul_eq_mul, smul_eq_mul] at h1
        have : ((E : ℂ) - E₀) * (star u ⬝ᵥ Ω) = 0 := by rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.mp this).resolve_left
          (sub_ne_zero.mpr (by exact_mod_cast hE))
      have hΩu : star Ω ⬝ᵥ u = 0 := by
        rw [star_dotProduct, horth, star_zero]
      have hge := hgv hu hΩu
      rw [hu1, mul_one] at hge
      have hge' : Δ ≤ E - E₀ := by
        have : (0 : ℂ) ≤ ((E - E₀ - Δ : ℝ) : ℂ) := by push_cast; exact hge
        have := Complex.zero_le_real.mp this
        linarith
      rw [hχ _ (by rw [abs_of_nonneg (by linarith)]; linarith), horth]
      simp
  have hreal : ∀ i ∈ s, star (star Ω ⬝ᵥ (h i *ᵥ Ω)) = star Ω ⬝ᵥ (h i *ᵥ Ω) := by
    intro i hi
    rw [← star_dotProduct_star, star_star, star_mulVec, (hh i hi).eq, dotProduct_comm,
      dotProduct_mulVec, dotProduct_comm]
  have hΩn : ‖(WithLp.toLp 2 Ω : EuclideanSpace ℂ ι)‖ = 1 := by
    have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 Ω : EuclideanSpace ℂ ι)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h1
    change star Ω ⬝ᵥ Ω = _ at h1
    rw [hΩ] at h1
    have h2 : ‖(WithLp.toLp 2 Ω : EuclideanSpace ℂ ι)‖ ^ 2 = 1 :=
      RCLike.ofReal_injective (K := ℂ) (by simpa using h1.symm)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  refine ⟨fun i _ => hint (h i), fun i hi => ?_, fun i _ => ?_, ?_, fun i hi => ?_⟩
  · -- D4.7.1 `M_i = M_i^*`
    rw [M, IsHermitian, conjTranspose_sub, hFstar, (hh i hi).eq, conjTranspose_smul,
      conjTranspose_one, hreal i hi]
  · -- D4.7.4 centering cancels: `M_i Ω = 0`
    rw [M, sub_mulVec, hFΩ, Matrix.smul_mulVec, one_mulVec, sub_self]
  · -- D4.7.5 `∑_i τ_t(h_i) = τ_t(H) = H`, `∫ f = 1`, `∑_i ⟨Ω, h_i Ω⟩ = E₀`
    simp only [M, Finset.sum_sub_distrib]
    rw [← integral_finsetSum s fun i _ => hint (h i)]
    simp_rw [← Finset.smul_sum, ← τ_sum, ← hH, τ_self]
    rw [integral_smul_const, hf1, one_smul, ← Finset.sum_smul, ← dotProduct_sum,
      ← Matrix.sum_mulVec, ← hH, hHΩ, dotProduct_smul, hΩ, smul_eq_mul, mul_one]
  · -- D4.7.6 `‖M_i‖ ≤ ‖f‖₁ J + |⟨Ω, h_i Ω⟩| ≤ J (‖f‖₁ + 1)`
    have hint1 : ‖∫ t, f t • τ H t (h i)‖ ≤ (∫ t, |f t|) * ‖h i‖ := by
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le (hf.abs.mul_const _)
        (Filter.Eventually.of_forall fun t => ?_)
      rw [norm_smul, norm_τ hHh, Real.norm_eq_abs]
    have hc : ‖star Ω ⬝ᵥ (h i *ᵥ Ω)‖ ≤ ‖h i‖ := by
      have he : star Ω ⬝ᵥ (h i *ᵥ Ω) = inner ℂ (WithLp.toLp 2 Ω : EuclideanSpace ℂ ι)
          ((EuclideanSpace.equiv ι ℂ).symm (h i *ᵥ Ω)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
      rw [he]
      calc _ ≤ ‖(WithLp.toLp 2 Ω : EuclideanSpace ℂ ι)‖ *
            ‖(EuclideanSpace.equiv ι ℂ).symm (h i *ᵥ Ω)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖h i‖ * 1) := by
          rw [hΩn]; gcongr; simpa [hΩn] using (h i).l2_opNorm_mulVec (WithLp.toLp 2 Ω)
        _ = ‖h i‖ := by ring
    have hone : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
      rcases subsingleton_or_nontrivial (Matrix ι ι ℂ) with h' | h'
      · simp [Subsingleton.elim (1 : Matrix ι ι ℂ) 0]
      · rw [CStarRing.norm_one]
    have hf0 : 0 ≤ ∫ t, |f t| := integral_nonneg fun _ => abs_nonneg _
    calc ‖M H Ω f (h i)‖
        ≤ ‖∫ t, f t • τ H t (h i)‖ + ‖star Ω ⬝ᵥ (h i *ᵥ Ω)‖ * ‖(1 : Matrix ι ι ℂ)‖ := by
          rw [M, ← norm_smul]; exact norm_sub_le _ _
      _ ≤ (∫ t, |f t|) * ‖h i‖ + ‖h i‖ * 1 := by gcongr
      _ = ‖h i‖ * ((∫ t, |f t|) + 1) := by ring
      _ ≤ J * ((∫ t, |f t|) + 1) := by gcongr; exact hJ i hi

end AreaLaw
