import AreaLawRefactored.S05_Conditional.Spectral
import AreaLawRefactored.S05_Conditional.SkewAnalytic
import AreaLawRefactored.S05_Conditional.Interfaces
import AreaLawRefactored.S05_Conditional.SkewStrip
import AreaLawRefactored.S05_Conditional.Lemma52

/-!
# §5.3 Lemma 5.3 from D5.16 and Lemma 5.2 (D5.15, D5.17, D5.18.1, D5.20)

Digest `digest/05-conditional.md`, D5.15–D5.20: the imaginary-axis comparison D5.17, the
phase-to-skew inequality D5.18.1, and the assembly of **Lemma 5.3** from the strip bounds
`Step_5_16`, **Lemma 5.2** and the complex analysis of `step_5_19`.
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder

universe u v

namespace Conditional

section Vectors

variable {n : Type*} [Fintype n]

/-- `⟨v, v⟩ = ‖v‖²`. -/
theorem star_dotProduct_self (v : n → ℂ) :
    star v ⬝ᵥ v = ((‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ n)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h.trans (by push_cast; rfl)

variable [DecidableEq n]

/-- A unitary `V` commuting with `H` preserves `⟨v, H v⟩`. -/
theorem dotProduct_mulVec_unitary {V : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ))
    {H : Matrix n n ℂ} (hVH : Commute V H) (v : n → ℂ) :
    star (V *ᵥ v) ⬝ᵥ (H *ᵥ (V *ᵥ v)) = star v ⬝ᵥ (H *ᵥ v) := by
  have hV' : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
    ← hVH.eq, ← Matrix.mul_assoc, hV', Matrix.one_mul]

/-- A unitary preserves the norm. -/
theorem norm_toLp_unitary_mulVec {V : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ))
    (v : n → ℂ) :
    ‖(WithLp.toLp 2 (V *ᵥ v) : EuclideanSpace ℂ n)‖ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  have h := dotProduct_mulVec_unitary hV (Commute.one_right V) v
  simp only [one_mulVec] at h
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_toLp_sq, norm_toLp_sq, h]

omit [DecidableEq n] in
/-- Commuting matrices commute on vectors. -/
theorem mulVec_mulVec_comm {A B : Matrix n n ℂ} (h : Commute A B) (v : n → ℂ) :
    A *ᵥ (B *ᵥ v) = B *ᵥ (A *ᵥ v) := by
  rw [mulVec_mulVec, h.eq, ← mulVec_mulVec]

end Vectors

section Phases

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ D E : Finset σ}

/-- `ρ̂_D^z ⊗ I`: the hat power of the marginal `ρ_D` of `θ`, extended to `Λ`. -/
noncomputable def ph (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (z : ℂ) :
    Matrix (Reg loc Λ) (Reg loc Λ) ℂ :=
  extendId hD (hatPow (marg θ hD) z)

theorem extendId_mem_unitary (hD : D ⊆ Λ) {A : Matrix (Reg loc D) (Reg loc D) ℂ}
    (hA : A ∈ unitary (Matrix (Reg loc D) (Reg loc D) ℂ)) :
    extendId hD A ∈ unitary (Matrix (Reg loc Λ) (Reg loc Λ) ℂ) := by
  rw [Unitary.mem_iff] at hA ⊢
  simp only [star_eq_conjTranspose, ← extendId_conjTranspose, ← extendId_mul] at hA ⊢
  simp [hA.1, hA.2]

theorem ph_mem_unitary (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (u : ℝ) :
    ph θ hD (u * Complex.I) ∈ unitary (Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :=
  extendId_mem_unitary hD (hatPow_mul_I_mem_unitary _ u)

theorem ph_neg_mem_unitary (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (u : ℝ) :
    ph θ hD (-(u * Complex.I)) ∈ unitary (Matrix (Reg loc Λ) (Reg loc Λ) ℂ) := by
  simpa [neg_mul] using ph_mem_unitary θ hD (-u)

theorem ph_neg_mul_ph (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (z : ℂ) :
    ph θ hD (-z) * ph θ hD z = 1 := by
  rw [ph, ph, ← extendId_mul, hatPow_neg_mul_hatPow, extendId_one]

theorem commute_ph (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (hE : E ⊆ Λ) (hd : Disjoint D E)
    (z w : ℂ) : Commute (ph θ hD z) (ph θ hE w) :=
  commute_extendId_extendId hD hE hd _ _

/-- On `supp ρ ⊗ I` brackets and hats agree. -/
theorem extendId_bracketPow_mulVec_eq_hatPow (hD : D ⊆ Λ) (ρ : Matrix (Reg loc D) (Reg loc D) ℂ)
    (s : ℂ) {v : Reg loc Λ → ℂ} (hv : extendId hD (bracketPow ρ 0) *ᵥ v = v) :
    extendId hD (bracketPow ρ s) *ᵥ v = extendId hD (hatPow ρ s) *ᵥ v := by
  have h1 : extendId hD (1 - bracketPow ρ 0) = 1 - extendId hD (bracketPow ρ 0) := by
    rw [eq_sub_iff_add_eq, ← extendId_add, sub_add_cancel, extendId_one]
  rw [hatPow_eq_bracketPow_add, extendId_add, add_mulVec, h1, sub_mulVec, one_mulVec, hv,
    sub_self, add_zero]

end Phases

end Conditional

open Conditional

section D517

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ P₀ P₁ X U F : Finset σ}

/-- D5.17. For real `u`, `f(iu) = ⟨w_u, h w_u⟩` with `w_u = ρ̂_Y^{iu} ρ̂_{YF}^{-iu} θ`
(`Y = xU`, `P = P₀P₁`); with `w_u⁰ = ρ̂_U^{iu} ρ̂_{UF}^{-iu} θ`: `⟨w_u⁰, h w_u⁰⟩ = p = ⟨θ, hθ⟩`, and
`‖w_u − w_u⁰‖ = ‖(ρ̂_U^{-iu} ρ̂_Y^{iu} − ρ̂_{UF}^{-iu} ρ̂_{YF}^{iu}) θ‖`, the vector of
Lemma 5.2. -/
theorem step_5_17 (hP₀ : P₀ ⊆ Λ) (hP₁ : P₁ ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ) (hF : F ⊆ Λ)
    (hΛ : Λ = P₀ ∪ P₁ ∪ X ∪ U ∪ F) (hPX : Disjoint (P₀ ∪ P₁) X) (hPU : Disjoint (P₀ ∪ P₁) U)
    (hPF : Disjoint (P₀ ∪ P₁) F) (hXU : Disjoint X U) (hXF : Disjoint X F)
    (θ : Reg loc Λ → ℂ) (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ) (u : ℝ) :
    let hY := Finset.union_subset hX hU
    let hYF := Finset.union_subset hY hF
    let hUF := Finset.union_subset hU hF
    let H := extendId (Finset.union_subset hP₀ hX) h
    let w := ph θ hY (u * Complex.I) *ᵥ (ph θ hYF (-(u * Complex.I)) *ᵥ θ)
    let w₀ := ph θ hU (u * Complex.I) *ᵥ (ph θ hUF (-(u * Complex.I)) *ᵥ θ)
    Conditional.f (Finset.union_subset hP₀ hP₁) hY (Finset.union_subset hP₀ hX) θ h
        (u * Complex.I) = star w ⬝ᵥ (H *ᵥ w) ∧
      star w₀ ⬝ᵥ (H *ᵥ w₀) = star θ ⬝ᵥ (H *ᵥ θ) ∧
      ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ (Reg loc Λ))‖ =
        ‖(WithLp.toLp 2 ((ph θ hU (-(u * Complex.I)) * ph θ hY (u * Complex.I) -
          ph θ hUF (-(u * Complex.I)) * ph θ hYF (u * Complex.I)) *ᵥ θ) :
            EuclideanSpace ℂ (Reg loc Λ))‖ := by
  intro hY hYF hUF H w w₀
  set z : ℂ := u * Complex.I
  set hP := Finset.union_subset hP₀ hP₁
  have hΛ' : (P₀ ∪ P₁) ∪ ((X ∪ U) ∪ F) = Λ := by rw [hΛ]; simp only [Finset.union_assoc]
  have hdY : Disjoint (P₀ ∪ P₁) (X ∪ U) := Finset.disjoint_union_right.2 ⟨hPX, hPU⟩
  have hdYF : Disjoint (P₀ ∪ P₁) (X ∪ U ∪ F) := Finset.disjoint_union_right.2 ⟨hdY, hPF⟩
  have hdUF : Disjoint (P₀ ∪ P₁) (U ∪ F) := Finset.disjoint_union_right.2 ⟨hPU, hPF⟩
  have hd0 : Disjoint P₀ (U ∪ F) := hdUF.mono_left Finset.subset_union_left
  have hHU : Disjoint (P₀ ∪ X) U := Finset.disjoint_union_left.2
    ⟨hd0.mono_right Finset.subset_union_left, hXU⟩
  have hHUF : Disjoint (P₀ ∪ X) (U ∪ F) := Finset.disjoint_union_left.2
    ⟨hd0, Finset.disjoint_union_right.2 ⟨hXU, hXF⟩⟩
  have hF2 : ph θ hP z *ᵥ θ = ph θ hYF z *ᵥ θ := step_5_1_F2_hat θ hP hYF hdYF hΛ' z
  refine ⟨?_, ?_, ?_⟩
  · -- D5.17.1
    have hW : extendId hP (bracketPow (marg θ hP) (-z)) *ᵥ
        (extendId hY (bracketPow (marg θ hY) z) *ᵥ θ) = w := by
      rw [mulVec_mulVec_comm (commute_extendId_extendId hP hY hdY _ _),
        step_5_1_F2 θ hP hYF hdYF hΛ', ← extendId_hatPow_marg_mulVec θ hYF,
        extendId_bracketPow_mulVec_eq_hatPow hY _ _
          (extendId_bracketPow_zero_marg_mulVec_hatPow θ hP hYF hdYF hΛ' hY
            Finset.subset_union_left _)]
      rfl
    have hc1 : (extendId hP (bracketPow (marg θ hP) (-z)))ᴴ =
        extendId hP (bracketPow (marg θ hP) z) := by
      rw [← extendId_conjTranspose, conjTranspose_bracketPow]; simp [z]
    have hc2 : (extendId hY (bracketPow (marg θ hY) z))ᴴ =
        extendId hY (bracketPow (marg θ hY) (-z)) := by
      rw [← extendId_conjTranspose, conjTranspose_bracketPow]; simp [z]
    rw [← hW, mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_mul,
      hc1, hc2, (commute_extendId_extendId hY hP hdY.symm _ _).eq]
    simp only [Conditional.f, H, Matrix.mul_assoc, mulVec_mulVec]
  · -- D5.17.2
    have h := dotProduct_mulVec_unitary
      (mul_mem (ph_mem_unitary θ hU u) (ph_neg_mem_unitary θ hUF u))
      (((commute_extendId_extendId hU (Finset.union_subset hP₀ hX) hHU.symm _ h).mul_left
        (commute_extendId_extendId hUF (Finset.union_subset hP₀ hX) hHUF.symm _ h))) θ
    rwa [← mulVec_mulVec] at h
  · -- D5.17.3
    have e1 : (ph θ hU (-z) * ph θ hP z) *ᵥ w = (ph θ hU (-z) * ph θ hY z) *ᵥ θ := by
      rw [← mulVec_mulVec, mulVec_mulVec_comm (commute_ph θ hP hY hdY z z),
        mulVec_mulVec_comm (commute_ph θ hP hYF hdYF z (-z)), hF2, mulVec_mulVec _ (ph θ hYF _),
        ph_neg_mul_ph, one_mulVec, mulVec_mulVec]
    have e2 : (ph θ hU (-z) * ph θ hP z) *ᵥ w₀ = (ph θ hUF (-z) * ph θ hYF z) *ᵥ θ := by
      rw [← mulVec_mulVec, mulVec_mulVec_comm (commute_ph θ hP hU hPU z z),
        mulVec_mulVec_comm (commute_ph θ hP hUF hdUF z (-z)), hF2,
        mulVec_mulVec _ (ph θ hU (-z)), ph_neg_mul_ph, one_mulVec, mulVec_mulVec]
    rw [← norm_toLp_unitary_mulVec (mul_mem (ph_neg_mem_unitary θ hU u) (ph_mem_unitary θ hP u)),
      mulVec_sub, e1, e2, sub_mulVec]

end D517

/-- D5.18.1. For `0 ≤ H ≤ 1`, vectors `w, w⁰`, `Δ = w − w⁰` and `p = ⟨w⁰, H w⁰⟩`:
`|⟨w, H w⟩ − p| ≤ 2√p ‖Δ‖ + ‖Δ‖²`. -/
theorem step_5_18_1 {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (h0 : 0 ≤ H)
    (h1 : H ≤ 1) (w w₀ : n → ℂ) :
    ‖star w ⬝ᵥ (H *ᵥ w) - star w₀ ⬝ᵥ (H *ᵥ w₀)‖ ≤
      2 * √(star w₀ ⬝ᵥ (H *ᵥ w₀)).re * ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ n)‖ +
        ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ n)‖ ^ 2 := by
  set B := CFC.sqrt H
  have hB : Bᴴ = B := (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq
  set N : (n → ℂ) → ℝ := fun v ↦ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖
  -- `⟨v, H v⟩ = ‖H^{1/2} v‖²`
  have hq : ∀ v, star v ⬝ᵥ (H *ᵥ v) = ((N (B *ᵥ v) ^ 2 : ℝ) : ℂ) := fun v ↦ by
    rw [← star_dotProduct_self, star_mulVec, ← dotProduct_mulVec, hB, mulVec_mulVec,
      CFC.sqrt_mul_sqrt_self H h0]
  -- `‖H^{1/2} v‖ ≤ ‖v‖` (`H ≤ 1`)
  have hle : ∀ v, N (B *ᵥ v) ≤ N v := fun v ↦ by
    have := (Matrix.le_iff.1 h1).dotProduct_mulVec_nonneg v
    rw [sub_mulVec, dotProduct_sub, one_mulVec, hq, star_dotProduct_self, ← Complex.ofReal_sub,
      Complex.zero_le_real, sub_nonneg] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hΔ : |N (B *ᵥ w) - N (B *ᵥ w₀)| ≤ N (w - w₀) := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← WithLp.toLp_sub, ← mulVec_sub]
    exact hle _
  rw [hq, hq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re,
    Real.sqrt_sq (norm_nonneg _)]
  have ha := norm_nonneg (WithLp.toLp 2 (B *ᵥ w) : EuclideanSpace ℂ n)
  have hb := norm_nonneg (WithLp.toLp 2 (B *ᵥ w₀) : EuclideanSpace ℂ n)
  change |N (B *ᵥ w) ^ 2 - N (B *ᵥ w₀) ^ 2| ≤ 2 * N (B *ᵥ w₀) * N (w - w₀) + N (w - w₀) ^ 2
  obtain ⟨hl, hr⟩ := abs_le.1 hΔ
  rw [abs_le]
  constructor <;> nlinarith

/-- D5.15 **Lemma 5.3** (conditional skew estimate), assembled from D5.16 (`Step_5_16`),
**Lemma 5.2**, D5.17, D5.18.1, D5.19 and D5.20: universal `c, C > 0` such that for
`0 < aℓ_h ≤ c` and `t = a/2`, `|f(t)| − Re f(t) ≤ C a² ℓ_h⁴ η^{1/8}`. -/
theorem lemma_5_3_of_step_5_16 (h516 : Step_5_16.{u, v}) (h52 : Lemma_5_2.{u, v}) :
    Lemma_5_3.{u, v} := by
  obtain ⟨K, hK, h52⟩ := h52
  obtain ⟨c₀, C, hc₀, -, hC, h519⟩ := step_5_19 K hK.le
  -- D5.15.5: `c = c₀/4`, so that `aℓ_h ≤ c` gives `t = a/2 ≤ b/8`
  refine ⟨c₀ / 4, 10 * C, by positivity, by positivity, ?_⟩
  intro σ _ loc _ _ Λ P₀ P₁ X U F hP₀ hP₁ hX hU hF hΛ h01 hPX hPU hPF hXU hXF hUF θ hθ h h0 h1 a
    ha hac
  -- D5.15.1 (D5.16)
  obtain ⟨hf, hsymm, hax, hstrip, hf0⟩ :=
    h516 σ loc Λ P₀ P₁ X U F hP₀ hP₁ hX hU hF hΛ h01 hPX hPU hPF hXU hXF hUF θ hθ h h0 h1
  set f := Conditional.f (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU)
    (Finset.union_subset hP₀ hX) θ h
  set dh := Fintype.card (Reg loc (P₀ ∪ X))
  set d := Fintype.card (Reg loc X)
  set η := condMutualInfo (pureState θ hθ).toSubState hX hU hF
  set R := 𝓡 d η
  -- dimensions: `1 ≤ d ≤ d_h = (dim P₀)(dim x)`
  have hcard : dh = Fintype.card (Reg loc P₀) * d :=
    (Fintype.card_congr (unionEquiv (hPX.mono_left Finset.subset_union_left))).trans
      (Fintype.card_prod _ _)
  have hdh : 1 ≤ dh := by
    by_contra hc
    rw [show dh = 0 by omega, ℓ, Nat.cast_zero, mul_zero, Real.log_zero, mul_zero] at ha
    exact lt_irrefl _ ha
  have hP0 : 0 < Fintype.card (Reg loc P₀) := Nat.pos_of_ne_zero fun h ↦ by
    rw [hcard, h, zero_mul] at hdh; omega
  have hd : 1 ≤ d := Nat.pos_of_ne_zero fun h ↦ by rw [hcard, h, mul_zero] at hdh; omega
  have hddh : d ≤ dh := hcard ▸ Nat.le_mul_of_pos_left d hP0
  have hL := one_le_ℓ hdh
  have ha0 : 0 < a := by nlinarith
  -- D5.20.2: `0 ≤ η = S(x|U) − S(x|UF) ≤ 2 log d ≤ 2ℓ_h` (D2.2 items 1, 4)
  obtain ⟨hη0, -, -, h4, -⟩ := step_2_2 (pureState θ hθ) hX hU hF hXU hXF hUF
  have h4' := (step_2_2 (pureState θ hθ) hX (Finset.union_subset hU hF) (Finset.empty_subset Λ)
    (Finset.disjoint_union_right.2 ⟨hXU, hXF⟩) (Finset.disjoint_empty_right _)
    (Finset.disjoint_empty_right _)).2.2.2.1
  have hη2 : η ≤ 2 * ℓ dh := by
    have he : η = condEntropy (pureState θ hθ).toSubState hX hU -
        condEntropy (pureState θ hθ).toSubState hX (Finset.union_subset hU hF) := by
      simp only [η, condMutualInfo, condEntropy, (pureState θ hθ).toSubState.regionEntropy_congr
        (Finset.union_assoc X U F) (Finset.union_subset (Finset.union_subset hX hU) hF)
        (Finset.union_subset hX (Finset.union_subset hU hF))]
      ring
    have hl : Real.log d ≤ ℓ dh := Real.log_le_log (by exact_mod_cast hd) <| by
      have : (d : ℝ) ≤ dh := by exact_mod_cast hddh
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    rw [he]
    linarith [(abs_le.1 h4).2, (abs_le.1 h4').1]
  have hR0 : 0 ≤ R := by simp only [R, 𝓡]; split_ifs <;> positivity
  -- `p = f(0) = ⟨θ, hθ⟩ ∈ ℝ`
  set p := (f 0).re
  have hp : f 0 = p := Complex.ext rfl (by simpa using (hax 0).1)
  have hH0 : 0 ≤ extendId (Finset.union_subset hP₀ hX) h := Matrix.nonneg_iff_posSemidef.2
    (posSemidef_extendId _ (Matrix.nonneg_iff_posSemidef.1 h0))
  have hH1 : extendId (Finset.union_subset hP₀ hX) h ≤ 1 := by
    rw [Matrix.le_iff] at h1 ⊢
    rw [show (1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) - extendId (Finset.union_subset hP₀ hX) h =
      extendId (Finset.union_subset hP₀ hX) (1 - h) by
        rw [eq_comm, eq_sub_iff_add_eq, ← extendId_add, sub_add_cancel, extendId_one]]
    exact posSemidef_extendId _ h1
  -- D5.15.2–3 (D5.17, D5.18.1, Lemma 5.2)
  have hphase : ∀ u : ℝ, ‖f (u * Complex.I) - p‖ ≤
      2 * √p * K * |Real.sinh (Real.pi * u)| * R +
        K ^ 2 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2 := by
    intro u
    obtain ⟨e1, e2, e3⟩ := step_5_17 hP₀ hP₁ hX hU hF hΛ hPX hPU hPF hXU hXF θ h u
    set w := ph θ (Finset.union_subset hX hU) (u * Complex.I) *ᵥ
      (ph θ (Finset.union_subset (Finset.union_subset hX hU) hF) (-(u * Complex.I)) *ᵥ θ)
    set w₀ := ph θ hU (u * Complex.I) *ᵥ
      (ph θ (Finset.union_subset hU hF) (-(u * Complex.I)) *ᵥ θ)
    have hΔ : ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ (Reg loc Λ))‖ ≤
        K * |Real.sinh (Real.pi * u)| * R :=
      e3.trans_le (h52 σ loc Λ (P₀ ∪ P₁) X U F hX hU hF hΛ hPX hPU hPF hXU hXF hUF θ hθ u)
    have h518 := step_5_18_1 hH0 hH1 w w₀
    rw [← e1, e2, ← hf0, hp, Complex.ofReal_re] at h518
    refine h518.trans ?_
    have hs := Real.sqrt_nonneg p
    have hn := norm_nonneg (WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ (Reg loc Λ))
    calc _ ≤ 2 * √p * (K * |Real.sinh (Real.pi * u)| * R) +
          (K * |Real.sinh (Real.pi * u)| * R) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, sq_abs]; ring
  -- D5.15.4–5 (D5.19, D5.20)
  calc ‖f ((a / 2 : ℝ) : ℂ)‖ - (f ((a / 2 : ℝ) : ℂ)).re ≤
        C * a ^ 2 * (ℓ dh ^ 2 * √(min 1 R) + R ^ 2) :=
      h519 f p R a dh hf hsymm hp hax hdh hstrip hphase hR0 ha0 hac
    _ ≤ C * a ^ 2 * (10 * ℓ dh ^ 4 * η ^ (1 / 8 : ℝ)) := by
      gcongr; exact step_5_20 hd hddh hη0 hη2
    _ = 10 * C * a ^ 2 * ℓ dh ^ 4 * η ^ (1 / 8 : ℝ) := by ring

/-- D5.15 **Lemma 5.3** (conditional skew estimate), from D5.16 (`step_5_16`) and Lemma 5.2
(`lemma_5_2`). -/
theorem lemma_5_3 : Lemma_5_3.{u, v} := lemma_5_3_of_step_5_16 step_5_16 lemma_5_2

end AreaLaw
