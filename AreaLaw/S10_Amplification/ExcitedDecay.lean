import AreaLaw.S10_Amplification.Setup

/-!
# §10.1 Excited-state decay (D10.3); estimates before polar decomposition (D10.13)

Digest `digest/10-amplification.md` (D10.3, D10.13), paper
`paper/sections/09-amplification.tex` lines 237–253 and 501–522. No geometry.

Some declarations here come from the v1 file `OpenAI/Transport/ErrorFourier.lean`, whose header
records it as ported or adapted from `LionSR/QICLean` (see `NOTICE`).
-/

namespace AreaLaw

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator InnerProductSpace

section Factors

variable {n κ : Type*} [Fintype n] [Fintype κ] [DecidableEq κ]

-- helper
theorem star_mulVec_dotProduct_mulVec (A : Matrix n n ℂ) (u v : n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (A *ᵥ v) = star u ⬝ᵥ ((Aᴴ * A) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

-- helper
theorem vnorm_mulVec_sq (A : Matrix n n ℂ) (v : n → ℂ) :
    vnorm (A *ᵥ v) ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [vnorm_sq, star_mulVec_dotProduct_mulVec]

-- helper
theorem mul_kronecker_one (A B : Matrix n n ℂ) :
    (A * B) ⊗ₖ (1 : Matrix κ κ ℂ) = (A ⊗ₖ (1 : Matrix κ κ ℂ)) * (B ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  rw [← mul_kronecker_mul, mul_one]

variable [DecidableEq n]

-- helper
/-- D10.2.1. `G = (I - k)^{1/2}` is self-adjoint, `G² = I - k`, and `G Ω = Ω` when `k Ω = 0`. -/
theorem sqrt_one_sub {k : Matrix n n ℂ} (hk : 0 ≤ k ∧ k ≤ 1) {Ω : n → ℂ} (hkΩ : k *ᵥ Ω = 0) :
    (CFC.sqrt (1 - k)).IsHermitian ∧ CFC.sqrt (1 - k) * CFC.sqrt (1 - k) = 1 - k ∧
      CFC.sqrt (1 - k) *ᵥ Ω = Ω := by
  have h2 := CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hk.2)
  refine ⟨(nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian, h2, ?_⟩
  simpa using mulVec_eq_smul_of_mul_self_mulVec (CFC.sqrt_nonneg (1 - k)) zero_le_one (v := Ω)
    (by rw [h2, Matrix.sub_mulVec, hkΩ]; simp)

/-- D10.13.1. Every exact factor `G_i` is self-adjoint with `G_i Ω = Ω`; then `D Ω = Ω`,
`D^† Ω = Ω` and `[D, P_Ω] = 0` (also with spectators, `D P_Ω = P_Ω D = P_Ω`). -/
theorem step_10_13_1 {ι : Type*} (G : ι → Matrix n n ℂ) (hG : ∀ i, (G i).IsHermitian)
    {Ω : n → ℂ} (hGΩ : ∀ i, G i *ᵥ Ω = Ω) (m : ℕ) (w : Fin m → ι) :
    wordProd G m w *ᵥ Ω = Ω ∧ (wordProd G m w)ᴴ *ᵥ Ω = Ω ∧
      wordProd G m w * vecMulVec Ω (star Ω) = vecMulVec Ω (star Ω) * wordProd G m w ∧
      (wordProd G m w ⊗ₖ (1 : Matrix κ κ ℂ)) * (vecMulVec Ω (star Ω) ⊗ₖ (1 : Matrix κ κ ℂ)) =
        vecMulVec Ω (star Ω) ⊗ₖ (1 : Matrix κ κ ℂ) ∧
      (vecMulVec Ω (star Ω) ⊗ₖ (1 : Matrix κ κ ℂ)) * (wordProd G m w ⊗ₖ (1 : Matrix κ κ ℂ)) =
        vecMulVec Ω (star Ω) ⊗ₖ (1 : Matrix κ κ ℂ) := by
  have hfix : ∀ m (w : Fin m → ι), wordProd G m w *ᵥ Ω = Ω ∧ (wordProd G m w)ᴴ *ᵥ Ω = Ω := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro w
      rw [wordProd_succ, ← mulVec_mulVec, (ih _).1, hGΩ, conjTranspose_mul, (hG _).eq,
        ← mulVec_mulVec, hGΩ, (ih _).2]
      exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := hfix m w
  have hl : wordProd G m w * vecMulVec Ω (star Ω) = vecMulVec Ω (star Ω) := by
    rw [mul_vecMulVec, h1]
  have hr : vecMulVec Ω (star Ω) * wordProd G m w = vecMulVec Ω (star Ω) := by
    rw [vecMulVec_mul]
    simpa [star_mulVec] using congrArg (fun v => vecMulVec Ω (star v)) h2
  refine ⟨h1, h2, hl.trans hr.symm, ?_, ?_⟩
  · rw [← mul_kronecker_one, hl]
  · rw [← mul_kronecker_one, hr]

end Factors

/-! ## D10.3 Excited-state decay -/

section Decay

variable {n κ ι : Type*} [Fintype n] [Fintype κ] [DecidableEq κ] [Fintype ι]

-- helper
/-- The quadratic form `B ↦ Re ⟨χ, (B ⊗ I) χ⟩`. -/
noncomputable def quadKron (χ : n × κ → ℂ) : Matrix n n ℂ →+ ℝ where
  toFun B := (star χ ⬝ᵥ ((B ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ)).re
  map_zero' := by simp
  map_add' A B := by simp [add_kronecker, add_mulVec, dotProduct_add]

omit [Fintype ι] in
-- helper
theorem quadKron_smul (χ : n × κ → ℂ) (c : ℝ) (B : Matrix n n ℂ) :
    quadKron χ ((c : ℂ) • B) = c * quadKron χ B := by
  simp [quadKron, smul_kronecker, smul_mulVec, dotProduct_smul]

omit [Fintype ι] in
-- helper
theorem quadKron_mono (χ : n × κ → ℂ) {A B : Matrix n n ℂ} (h : A ≤ B) :
    quadKron χ A ≤ quadKron χ B := by
  have h0 : 0 ≤ star χ ⬝ᵥ (((B - A) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) :=
    ((Matrix.le_iff.mp h).kronecker PosSemidef.one).dotProduct_mulVec_nonneg χ
  have := (Complex.le_def.mp h0).1
  rw [← sub_nonneg, ← map_sub]
  simpa [quadKron] using this

variable [DecidableEq n]

/-- D10.3. Under D10.1, for every vector `ζ` including spectators (`P_Ω → P_Ω ⊗ I`), with `D`
the product of all `G_i` over the clocks of D10.2 on `[0, t]`:
`𝔼‖D(I - P_Ω)ζ‖² ≤ e^{-gt} ‖(I - P_Ω)ζ‖²`. -/
theorem step_10_3
    (k : ι → Matrix n n ℂ) (hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1) {Ω : n → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hkΩ : ∀ i, k i *ᵥ Ω = 0) {g : ℝ} (hgap : (g : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤ ∑ i, k i)
    {t : ℝ} (ht : 0 ≤ t) (ζ : n × κ → ℂ) :
    let P := vecMulVec Ω (star Ω) ⊗ₖ (1 : Matrix κ κ ℂ)
    let D := wordProd (fun i => CFC.sqrt (1 - k i))
    Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι,
        vnorm ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ ((1 - P) *ᵥ ζ)) ^ 2) ∧
      clockExp ι t (fun m w => vnorm ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ ((1 - P) *ᵥ ζ)) ^ 2) ≤
        Real.exp (-g * t) * vnorm ((1 - P) *ᵥ ζ) ^ 2 := by
  intro P D
  set G : ι → Matrix n n ℂ := fun i => CFC.sqrt (1 - k i)
  set N : ℝ := (Fintype.card ι : ℝ)
  have hG : ∀ i, (G i).IsHermitian ∧ G i * G i = 1 - k i ∧ G i *ᵥ Ω = Ω := fun i =>
    sqrt_one_sub (hk i) (hkΩ i)
  -- D10.3.1
  have h1 : ∀ m w χ, P *ᵥ χ = 0 → P *ᵥ ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) = 0 := by
    intro m w χ hχ
    rw [mulVec_mulVec, (step_10_13_1 (κ := κ) G (fun i => (hG i).1) (fun i => (hG i).2.2) m
      w).2.2.2.2, hχ]
  have hψ : P *ᵥ ((1 - P) *ᵥ ζ) = 0 := by
    have hPP : P * P = P := by
      rw [← mul_kronecker_one, vecMulVec_mul_vecMulVec, hΩ, one_smul]
    rw [mulVec_mulVec, mul_sub, mul_one, hPP, sub_self, zero_mulVec]
  -- D10.3.2
  have h2 : ∀ χ, P *ᵥ χ = 0 →
      ∑ i, vnorm ((G i ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) ^ 2 ≤ (N - g) * vnorm χ ^ 2 := by
    intro χ hχ
    have hq1 : quadKron χ 1 = vnorm χ ^ 2 := by simp [quadKron, vnorm_sq]
    have hqP : quadKron χ (vecMulVec Ω (star Ω)) = 0 := by
      simp only [quadKron, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [show (vecMulVec Ω (star Ω) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ = 0 from hχ]
      simp
    have hi : ∀ i, vnorm ((G i ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) ^ 2 = quadKron χ (1 - k i) := by
      intro i
      rw [vnorm_mulVec_sq, conjTranspose_kronecker, conjTranspose_one, (hG i).1.eq,
        ← mul_kronecker_one, (hG i).2.1]
      rfl
    have hgap' := quadKron_mono χ hgap
    rw [quadKron_smul, map_sub, hq1, hqP, map_sum] at hgap'
    simp only [hi, map_sub, hq1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    linarith
  -- D10.3.3
  have h3 : ∀ χ, P *ᵥ χ = 0 → ∀ m, ∑ w : Fin m → ι,
      vnorm ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) ^ 2 ≤ vnorm χ ^ 2 * (N - g) ^ m := by
    intro χ hχ m
    induction m with
    | zero => simp [D]
    | succ m ih =>
      rw [sum_word_succ, Finset.sum_comm]
      simp only [D, wordProd_succ, Fin.cons_zero, Fin.tail_cons, mul_kronecker_one,
        ← mulVec_mulVec]
      have hS : 0 ≤ ∑ w : Fin m → ι, vnorm ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h0 : 0 ≤ (N - g) * vnorm χ ^ 2 :=
        (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (h2 χ hχ)
      calc _ ≤ ∑ w : Fin m → ι, (N - g) * vnorm ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) ^ 2 :=
            Finset.sum_le_sum fun w _ => h2 _ (h1 m w χ hχ)
        _ = (N - g) * ∑ w : Fin m → ι, vnorm ((D m w ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ χ) ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ vnorm χ ^ 2 * (N - g) ^ (m + 1) := by
            rcases le_or_gt 0 (N - g) with hNg | hNg
            · calc _ ≤ (N - g) * (vnorm χ ^ 2 * (N - g) ^ m) := mul_le_mul_of_nonneg_left ih hNg
                _ = _ := by ring
            · have hv : vnorm χ ^ 2 = 0 := by nlinarith [sq_nonneg (vnorm χ)]
              rw [hv, zero_mul]; nlinarith
  have h := clockExp_le_of_sum_le ht (fun _ _ => sq_nonneg _) (h3 _ hψ)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [show (N - g - (Fintype.card ι : ℝ)) * t = -g * t by ring, mul_comm]

end Decay

/-! ## D10.13 Estimates before polar decomposition -/

section BeforePolar

variable {n : Type*} [Fintype n]

/-- D10.13.2. `‖L'ζ‖ ≤ ‖(L' - D_ret)ζ‖ + ‖(D_ret - D)ζ‖ + ‖Dζ‖ ≤ 1 + 3x`: with
`‖ζ‖ ≤ M₀`, `‖D(I - P)ζ‖ ≤ x`, `‖(D - D_ret)ζ‖ ≤ x`, `M₀‖D_ret - L'‖ ≤ x` and
`‖D P ζ‖ ≤ 1`. -/
theorem step_10_13_2 [DecidableEq n] {ζ : n → ℂ} {D Dr L' P : Matrix n n ℂ} {M₀ x : ℝ}
    (hζ : vnorm ζ ≤ M₀) (h₁ : vnorm (D *ᵥ ((1 - P) *ᵥ ζ)) ≤ x)
    (h₂ : vnorm ((D - Dr) *ᵥ ζ) ≤ x) (h₃ : M₀ * ‖Dr - L'‖ ≤ x)
    (h₄ : vnorm (D *ᵥ (P *ᵥ ζ)) ≤ 1) : vnorm (L' *ᵥ ζ) ≤ 1 + 3 * x := by
  have e1 : L' *ᵥ ζ = (L' - Dr) *ᵥ ζ + (-((D - Dr) *ᵥ ζ) +
      (D *ᵥ (P *ᵥ ζ) + D *ᵥ ((1 - P) *ᵥ ζ))) := by
    simp only [sub_mulVec, mulVec_sub, one_mulVec]; abel
  have hL : vnorm ((L' - Dr) *ᵥ ζ) ≤ x := by
    refine (vnorm_mulVec_le _ _).trans ?_
    rw [← norm_neg, neg_sub]
    nlinarith [norm_nonneg (Dr - L'), vnorm_nonneg ζ]
  rw [e1]
  refine (vnorm_add_le _ _).trans ?_
  have := vnorm_add_le (-((D - Dr) *ᵥ ζ)) (D *ᵥ (P *ᵥ ζ) + D *ᵥ ((1 - P) *ᵥ ζ))
  have := vnorm_add_le (D *ᵥ (P *ᵥ ζ)) (D *ᵥ ((1 - P) *ᵥ ζ))
  rw [vnorm_neg] at *
  linarith

/-- D10.13.3. `(L')^† Ω - Ω = (L' - D_ret)^† Ω` (using `D_ret^† Ω = Ω`), of norm
`≤ ‖L' - D_ret‖ ≤ M₀ ‖L' - D_ret‖ ≤ x` (uses `M₀ ≥ 1`). -/
theorem step_10_13_3 [DecidableEq n] {v : n → ℂ} {Dr L' : Matrix n n ℂ} {M₀ x : ℝ}
    (hDr : Drᴴ *ᵥ v = v) (hv : vnorm v = 1) (hM₀ : 1 ≤ M₀) (h : M₀ * ‖Dr - L'‖ ≤ x) :
    vnorm (L'ᴴ *ᵥ v - v) ≤ x := by
  have e : L'ᴴ *ᵥ v - v = (L' - Dr)ᴴ *ᵥ v := by
    rw [conjTranspose_sub, sub_mulVec, hDr]
  rw [e]
  refine (vnorm_mulVec_le _ _).trans ?_
  rw [l2_opNorm_conjTranspose, hv, mul_one, ← norm_neg, neg_sub]
  nlinarith [norm_nonneg (Dr - L')]

-- helper
theorem inner_toLp (u v : n → ℂ) :
    ⟪(WithLp.toLp 2 u : EuclideanSpace ℂ n), WithLp.toLp 2 v⟫_ℂ = star u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- D10.13.5–6. For unit `φ, η` with `‖R'φ‖ ≤ 1 + a` and `‖R'^†η - φ‖ ≤ b`:
`Re⟨η, R'φ⟩ = Re⟨R'^†η, φ⟩ ≥ 1 - b` and
`‖R'φ - η‖² = ‖R'φ‖² + 1 - 2 Re⟨η, R'φ⟩ ≤ 2a + a² + 2b`. -/
theorem step_10_13_6 {φ η : n → ℂ} {R' : Matrix n n ℂ} {a b : ℝ} (hφ : vnorm φ = 1)
    (hη : vnorm η = 1) (h₁ : vnorm (R' *ᵥ φ) ≤ 1 + a) (h₂ : vnorm (R'ᴴ *ᵥ η - φ) ≤ b)
    (ha : 0 ≤ a) : vnorm (R' *ᵥ φ - η) ^ 2 ≤ 2 * a + a ^ 2 + 2 * b := by
  set x : EuclideanSpace ℂ n := WithLp.toLp 2 φ
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 η
  set z : EuclideanSpace ℂ n := WithLp.toLp 2 (R' *ᵥ φ)
  set e : EuclideanSpace ℂ n := WithLp.toLp 2 (R'ᴴ *ᵥ η - φ)
  -- D10.13.5
  have h5 : 1 - b ≤ RCLike.re ⟪z, y⟫_ℂ := by
    have hzy : ⟪z, y⟫_ℂ = ⟪x, x⟫_ℂ + ⟪x, e⟫_ℂ := by
      simp only [x, y, z, e, inner_toLp, star_mulVec, ← dotProduct_mulVec, ← dotProduct_add,
        add_sub_cancel]
    have hxx : RCLike.re ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq, show ‖x‖ = 1 from hφ, one_pow]
    have hxe := abs_le.mp ((RCLike.abs_re_le_norm _).trans
      ((norm_inner_le_norm (𝕜 := ℂ) x e).trans (by rw [show ‖x‖ = 1 from hφ, one_mul])))
    rw [hzy, map_add, hxx]
    linarith [hxe.1, show ‖e‖ ≤ b from h₂]
  -- D10.13.6
  have h6 : vnorm (R' *ᵥ φ - η) ^ 2 = ‖z‖ ^ 2 - 2 * RCLike.re ⟪z, y⟫_ℂ + ‖y‖ ^ 2 := by
    rw [← norm_sub_sq (𝕜 := ℂ)]; rfl
  rw [h6, show ‖y‖ = 1 from hη]
  have hz : ‖z‖ ≤ 1 + a := h₁
  nlinarith [norm_nonneg z]

end BeforePolar

end AreaLaw
