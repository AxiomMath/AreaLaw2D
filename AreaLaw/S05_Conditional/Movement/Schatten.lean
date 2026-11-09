import AreaLaw.S05_Conditional.Movement.Setup

/-!
# §5.1 D5.4, D5.6: the conditional Schatten estimate and the left-boundary overlap

Digest `digest/05-conditional.md`, D5.4 and D5.6, at the matrix level of a conditional pair
(`IsCondPair`). `step_5_4_of` takes the Araki–Lieb–Thirring inequality and D5.2 as hypotheses.
-/

namespace AreaLaw

open Matrix Conditional
open scoped ComplexOrder MatrixOrder

universe u

namespace Conditional.Sch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re Tr P^{[b]} K = ∑_{ij} p_i^b κ_j |⟨i,j⟩|²` for `P, K ≥ 0`, real `b ≠ 0`. -/
theorem re_trace_bracketPow_mul {P K : Matrix n n ℂ} (hP : P.PosSemidef) (hK : K.PosSemidef)
    {b : ℝ} (hb : b ≠ 0) :
    (bracketPow P b * K).trace.re = ∑ i, ∑ j, hP.1.eigenvalues i ^ b * hK.1.eigenvalues j *
      ovl hP.1 hK.1 i j := by
  conv_lhs => rw [bracketPow_eq hP.1, ← specFun_ofReal hK.1, trace_specFun_mul_specFun]
  simp only [Complex.re_sum, bfun_ofReal hb (hP.eigenvalues_nonneg _)]
  norm_cast

/-- `Re Tr K^{[r]} = ∑_j κ_j^r` for `K ≥ 0`, real `r ≠ 0`. -/
theorem re_trace_bracketPow {K : Matrix n n ℂ} (hK : K.PosSemidef) {r : ℝ} (hr : r ≠ 0) :
    (bracketPow K r).trace.re = ∑ j, hK.1.eigenvalues j ^ r := by
  rw [bracketPow_eq hK.1, trace_specFun, Complex.re_sum]
  simp only [bfun_ofReal hr (hK.eigenvalues_nonneg _), Complex.ofReal_re]

/-- Hölder on eigenvalue sums: for `P ≥ 0` with `Re Tr P ≤ 1`, `K ≥ 0`, `0 < β < 1`,
`Re Tr P^{[β]} K ≤ (∑_j κ_j^{1/(1-β)})^{1-β}`. -/
theorem re_trace_bracketPow_mul_le {P K : Matrix n n ℂ} (hP : P.PosSemidef) (hK : K.PosSemidef)
    (htr : P.trace.re ≤ 1) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    (bracketPow P β * K).trace.re ≤ (∑ j, hK.1.eigenvalues j ^ (1 / (1 - β))) ^ (1 - β) := by
  set t := hP.1.eigenvalues
  set κ := hK.1.eigenvalues
  set o := ovl hP.1 hK.1
  have ht := hP.eigenvalues_nonneg
  have hκ := hK.eigenvalues_nonneg
  have ho := ovl_nonneg hP.1 hK.1
  have hr : ∀ i, ∑ j, o i j = 1 := sum_ovl_right _ _
  have hl : ∀ j, ∑ i, o i j = 1 := sum_ovl_left _ _
  have hβ' : 0 < 1 - β := by linarith
  have H := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (n × n))
    (f := fun x ↦ (o x.1 x.2 * t x.1) ^ β)
    (g := fun x ↦ (o x.1 x.2 * κ x.2 ^ (1 / (1 - β))) ^ (1 - β))
    (Real.holderConjugate_one_div hβ hβ' (by ring))
    (fun x _ ↦ by have := ho x.1 x.2; have := ht x.1; positivity)
    (fun x _ ↦ by have := ho x.1 x.2; have := hκ x.2; positivity)
  have hf : ∀ x : n × n, ((o x.1 x.2 * t x.1) ^ β) ^ (1 / β) = o x.1 x.2 * t x.1 := fun x ↦ by
    rw [← Real.rpow_mul (mul_nonneg (ho _ _) (ht _)), mul_one_div_cancel hβ.ne', Real.rpow_one]
  have hg : ∀ x : n × n, ((o x.1 x.2 * κ x.2 ^ (1 / (1 - β))) ^ (1 - β)) ^ (1 / (1 - β)) =
      o x.1 x.2 * κ x.2 ^ (1 / (1 - β)) := fun x ↦ by
    rw [← Real.rpow_mul (mul_nonneg (ho _ _) (Real.rpow_nonneg (hκ _) _)),
      mul_one_div_cancel hβ'.ne', Real.rpow_one]
  simp only [hf, hg, one_div_one_div, Fintype.sum_prod_type] at H
  have hfg : ∀ i j, (o i j * t i) ^ β * (o i j * κ j ^ (1 / (1 - β))) ^ (1 - β) =
      t i ^ β * κ j * o i j := fun i j ↦ by
    rw [Real.mul_rpow (ho _ _) (ht _), Real.mul_rpow (ho _ _) (Real.rpow_nonneg (hκ _) _),
      ← Real.rpow_mul (hκ _), one_div_mul_cancel hβ'.ne', Real.rpow_one]
    have : o i j ^ β * o i j ^ (1 - β) = o i j := by
      rw [← Real.rpow_add' (ho _ _) (by norm_num), add_sub_cancel, Real.rpow_one]
    linear_combination t i ^ β * κ j * this
  simp only [hfg] at H
  have hmass : (∑ i, ∑ j, o i j * t i) ^ β ≤ 1 := by
    refine Real.rpow_le_one (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (ho _ _) (ht _)) ?_ hβ.le
    simp_rw [← Finset.sum_mul, hr, one_mul]
    simpa [hP.1.trace_eq_sum_eigenvalues] using htr
  rw [re_trace_bracketPow_mul hP hK hβ.ne']
  refine H.trans ?_
  rw [Finset.sum_comm (f := fun i j ↦ o i j * κ j ^ (1 / (1 - β)))]
  simp_rw [← Finset.sum_mul, hr, hl, one_mul] at hmass ⊢
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Finset.sum_nonneg fun j _ ↦
    Real.rpow_nonneg (hκ j) _) _) hmass

/-- A nonzero `K ≥ 0` has a positive eigenvalue. -/
theorem exists_eigenvalues_pos {K : Matrix n n ℂ} (hK : K.PosSemidef) (hK0 : K ≠ 0) :
    ∃ j, 0 < hK.1.eigenvalues j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ((hK.1.eigenvalues_eq_zero_iff).not.mpr hK0)
  exact ⟨j, (hK.eigenvalues_nonneg j).lt_of_ne' hj⟩

/-- `Re Tr P^{[b]} K > 0` for `P > 0`, `K ≥ 0`, `K ≠ 0`, real `b ≠ 0`. -/
theorem re_trace_bracketPow_mul_pos {P K : Matrix n n ℂ} (hP : P.PosDef) (hK : K.PosSemidef)
    (hK0 : K ≠ 0) {b : ℝ} (hb : b ≠ 0) : 0 < (bracketPow P b * K).trace.re := by
  obtain ⟨j, hj⟩ := exists_eigenvalues_pos hK hK0
  obtain ⟨i, hi⟩ : ∃ i, 0 < ovl hP.1 hK.1 i j := by
    by_contra! h
    linarith [sum_ovl_left hP.1 hK.1 j, Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) ↦ h i]
  have hnn : ∀ i j, 0 ≤ hP.1.eigenvalues i ^ b * hK.1.eigenvalues j * ovl hP.1 hK.1 i j :=
    fun i j ↦ mul_nonneg (mul_nonneg (Real.rpow_nonneg (hP.eigenvalues_pos i).le _)
      (hK.eigenvalues_nonneg j)) (ovl_nonneg _ _ i j)
  rw [re_trace_bracketPow_mul hP.posSemidef hK hb]
  exact Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j) ⟨i, Finset.mem_univ _,
    Finset.sum_pos' (fun j _ ↦ hnn i j) ⟨j, Finset.mem_univ _,
      mul_pos (mul_pos (Real.rpow_pos_of_pos (hP.eigenvalues_pos i) _) hj) hi⟩⟩

variable {ρ Q : Matrix n n ℂ} {d : ℕ}

/-- `K = Q^{-a} ρ Q^{-a} ≥ 0`. -/
theorem posSemidef_Kmat (hc : IsCondPair ρ Q d) (a : ℝ) : (Kmat ρ Q a).PosSemidef := by
  have h := hc.1.conjTranspose_mul_mul_same (hatPow Q ((-a : ℝ) : ℂ))
  rwa [(isHermitian_hatPow_ofReal Q (-a)).eq] at h

/-- `K ≠ 0`, since `Q^{-a}` is invertible and `Tr ρ = 1`. -/
theorem Kmat_ne_zero (hc : IsCondPair ρ Q d) (a : ℝ) : Kmat ρ Q a ≠ 0 := by
  intro h
  have e : hatPow Q ((a : ℝ) : ℂ) * Kmat ρ Q a * hatPow Q ((a : ℝ) : ℂ) = ρ := by
    simp only [Kmat, Complex.ofReal_neg, Matrix.mul_assoc]
    rw [hatPow_neg_mul_hatPow, Matrix.mul_one, ← Matrix.mul_assoc, hatPow_mul_hatPow_neg,
      Matrix.one_mul]
  have := hc.2.1
  rw [← e, h, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at this
  exact zero_ne_one this

theorem rexp_ne_zero {a : ℝ} (ha : a < 1 / 2) : rexp a ≠ 0 :=
  inv_ne_zero (by linarith)

/-- `Tr K^r = ∑_j κ_j^r > 0`. -/
theorem trKr_pos (hc : IsCondPair ρ Q d) {a : ℝ} (ha : a < 1 / 2) : 0 < trKr ρ Q a := by
  have hK := posSemidef_Kmat hc a
  obtain ⟨j, hj⟩ := exists_eigenvalues_pos hK (Kmat_ne_zero hc a)
  rw [trKr, re_trace_bracketPow hK (rexp_ne_zero ha)]
  exact Finset.sum_pos' (fun j _ ↦ Real.rpow_nonneg (hK.eigenvalues_nonneg j) _)
    ⟨j, Finset.mem_univ _, Real.rpow_pos_of_pos hj _⟩

end Conditional.Sch

open Conditional.Sch

/-- D5.6.2, D5.6.4 (`eq:conditional-overlap`), matrix level. For a conditional pair and
`0 < a < 1/2`: `Tr K^r > 0`; for `τ ≥ 0`, `Tr τ^{2a} ξ^{[1-2a]} = Tr τ^{2a} K / Z`
(`ξ^{[1-2a]} = K / Z`), and `Tr τ^{2a} K > 0` when `τ > 0`. -/
theorem step_5_6 : Step_5_6.{u} := by
  intro n _ _ ρ Q d hc a ha ha'
  have hK := posSemidef_Kmat hc a
  have hpos := trKr_pos hc ha'
  have hr := rexp_ne_zero ha'
  have hr1 : rexp a * (1 - 2 * a) = 1 := inv_mul_cancel₀ (by linarith)
  refine ⟨hpos, fun τ hτ ↦ ⟨?_, fun hτ' ↦
    re_trace_bracketPow_mul_pos hτ' hK (Kmat_ne_zero hc a) (by positivity)⟩⟩
  -- D5.6.4 `ξ^{[1-2a]} = ξ^{1/r} = K / Z`
  have hξ : xiMat ρ Q a = specFun hK.1 fun t ↦ (((trKr ρ Q a)⁻¹ * t ^ rexp a : ℝ) : ℂ) := by
    rw [xiMat, bracketPow_eq hK.1, ← specFun_const_mul]
    exact specFun_congr _ fun i ↦ by
      rw [bfun_ofReal hr (hK.eigenvalues_nonneg i)]; push_cast; rfl
  have hK' := isHermitian_specFun_ofReal hK.1 fun t ↦ (trKr ρ Q a)⁻¹ * t ^ rexp a
  have hxi : bracketPow (xiMat ρ Q a) ((1 - 2 * a : ℝ) : ℂ) =
      (((trKr ρ Q a)⁻¹ ^ (1 - 2 * a) : ℝ) : ℂ) • Kmat ρ Q a := by
    conv_rhs => rw [← specFun_ofReal hK.1]
    rw [hξ, bracketPow_eq hK', specFun_specFun hK.1 _ hK', ← specFun_const_mul]
    refine specFun_congr _ fun i ↦ ?_
    have hκ := hK.eigenvalues_nonneg i
    rw [bfun_ofReal (by linarith) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hκ, hr1, Real.rpow_one]
    push_cast; rfl
  rw [hxi, Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, Zval,
    Real.inv_rpow hpos.le, div_eq_inv_mul]

/-- D5.4 (`eq:conditional-schatten`) with D5.6.2 (Hölder). Universal `c ≤ 1/8`, `C`: for a
conditional pair `(ρ, Q)` with dimension `d` and `0 < a`, `a ℓ ≤ c`: `Z > 0`,
`log Z ≤ 2a 𝔼L + C a² ℓ²`, and `Tr τ^{2a} K ≤ Z` for every `τ ≥ 0` with `Tr τ ≤ 1`.

Formal route: D5.4.1–4 (Stein interpolation) is replaced by the Araki–Lieb–Thirring inequality
`hALT` with `A = ρ`, `s = -a` (`2 s r = 1 - r`), giving `Tr K^r ≤ Tr ρ^r Q^{1-r} = 𝔼 e^{(r-1)L}`
(D5.2, `h2`); D5.6.2 (Schatten-norm Hölder) is Hölder on eigenvalue sums,
`Tr τ^{2a} K = ∑_{ij} t_i^{2a} κ_j |⟨i,j⟩|² ≤ (Tr τ)^{2a} (Tr K^r)^{1/r}`. -/
theorem step_5_4_of (hALT : ArakiLiebThirring.{u}) (h2 : Step_5_2.{u}) : Step_5_4.{u} := by
  obtain ⟨c₃, C₃, hc₃, hc₃', hC₃, h53⟩ := step_5_3.{u}
  refine ⟨c₃ / 4, 8 * C₃, by positivity, by linarith, by positivity, ?_⟩
  intro n _ _ ρ Q d hc a ha hac
  have hℓ := one_le_ℓ hc.2.2.2.1
  have ha8 : a ≤ 1 / 8 := by linarith [mul_le_mul_of_nonneg_left hℓ ha.le]
  have hpos := trKr_pos hc (a := a) (by linarith)
  have hK := posSemidef_Kmat hc a
  have h12 : 0 < 1 - 2 * a := by linarith
  have hr0 : 0 < rexp a := inv_pos.mpr h12
  have hr1 : rexp a * (1 - 2 * a) = 1 := inv_mul_cancel₀ h12.ne'
  have hr2 : rexp a ≤ 2 := by
    linarith [mul_le_mul_of_nonneg_left (show 1 / 2 ≤ 1 - 2 * a by linarith) hr0.le]
  have hr3 : 1 ≤ rexp a := by
    linarith [mul_le_mul_of_nonneg_left (show 1 - 2 * a ≤ 1 by linarith) hr0.le]
  have hb : rexp a - 1 ≤ 4 * a := by linarith [mul_nonneg ha.le (sub_nonneg.mpr hr2)]
  refine ⟨Real.rpow_pos_of_pos hpos _, ?_, fun τ hτ htr ↦ ?_⟩
  · -- D5.4.2–4 (Araki–Lieb–Thirring): `Tr K^r ≤ Tr ρ^r Q^{1-r}`
    have hA := hALT n ρ Q hc.1 hc.2.2.1 (-a) (rexp a) hr3
    -- D5.2: `Tr ρ^r Q^{1-r} = 𝔼 e^{(r-1)L}`
    obtain ⟨hw, hs, hp, hm, hE, hmgf⟩ := h2 n ρ Q d hc.1.1 hc.2.2.1.1 hc
    have he := hmgf (rexp a - 1)
    rw [add_sub_cancel, show -(rexp a - 1) = 2 * -a * rexp a by linear_combination -hr1] at he
    -- D5.3 with `b = r - 1`
    have h3 := (h53 (n × n) (fun x ↦ hc.1.1.eigenvalues x.1 * ovl hc.1.1 hc.2.2.1.1 x.1 x.2)
      (fun x ↦ Real.log (hc.1.1.eigenvalues x.1) - Real.log (hc.2.2.1.1.eigenvalues x.2)) d
      hc.2.2.2.1 (fun x ↦ hw x.1 x.2) (by rw [Fintype.sum_prod_type]; exact hs)
      (by rw [Fintype.sum_prod_type]; exact hp) (by rw [Fintype.sum_prod_type]; exact hm)).2.2
      (rexp a - 1) (by
        rw [abs_of_nonneg (by linarith)]
        linarith [mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ ℓ d)])
    simp only [Fintype.sum_prod_type] at h3
    rw [hE, ← he] at h3
    -- D5.4.5 `log Z = (1/r) log Tr K^r ≤ 2a 𝔼L + 8 C₃ a² ℓ²`
    have e1 : (1 - 2 * a) * (rexp a - 1) = 2 * a := by linear_combination hr1
    have e2 : (1 - 2 * a) * (rexp a - 1) ^ 2 = 4 * a ^ 2 * rexp a := by
      linear_combination (rexp a - 1 + 2 * a) * hr1
    rw [Zval, Real.log_rpow hpos]
    calc (1 - 2 * a) * Real.log (trKr ρ Q a)
        ≤ (1 - 2 * a) * ((rexp a - 1) * relEnt ρ Q + C₃ * (rexp a - 1) ^ 2 * ℓ d ^ 2) :=
          mul_le_mul_of_nonneg_left ((Real.log_le_log hpos hA).trans h3) h12.le
      _ = 2 * a * relEnt ρ Q + C₃ * ℓ d ^ 2 * (4 * a ^ 2 * rexp a) := by
          linear_combination relEnt ρ Q * e1 + C₃ * ℓ d ^ 2 * e2
      _ ≤ _ := by
          have h := mul_nonneg (mul_nonneg hC₃.le (sq_nonneg (ℓ d)))
            (mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hr2))
          linarith
  · -- D5.6.2 Hölder: `Tr τ^{2a} K ≤ (Tr τ)^{2a} (Tr K^r)^{1/r} ≤ Z`
    have h := re_trace_bracketPow_mul_le hτ hK htr (β := 2 * a) (by positivity) (by linarith)
    rwa [Zval, trKr, re_trace_bracketPow hK hr0.ne', rexp, ← one_div]

end AreaLaw
