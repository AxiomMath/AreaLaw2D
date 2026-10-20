import AreaLawRefactored.S02_Preliminaries
import AreaLawForMathlib.Analysis.Matrix.TraceRightDomination

/-!
# §5 Two conditional operator estimates

Digest `digest/05-conditional.md`, paper `paper/sections/04-conditional.tex`. Lattice-free
(`Map.md`, Dimension: every §5 anchor is `any d`): a pure vector `θ` on four disjoint regions
`P, x, U, F` of an arbitrary site type `σ` with finite local spaces `loc`. Constants depend only
on `d = dim x` (resp. `d_h`).
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## D5.1 Spectral powers, hat, norms -/

section D51

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D5.1. `ρ^{[z]} = ∑_{p>0} p^z Π_p` (`z ∈ ℂ`), in the eigenbasis of a Hermitian `ρ`; it is `0`
on `ker ρ` for every `z`, so `ρ^{[0]} = Π_{supp ρ}`. Brackets are omitted for positive real
powers: `ρ^a = ρ^{[a]}`, `a > 0`. -/
noncomputable def bracketPow (ρ : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  if h : ρ.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i ↦ if 0 < h.eigenvalues i then Complex.exp (z * Real.log (h.eigenvalues i))
        else 0) * star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 0

/-- D5.1. `ρ̂^z` for `ρ̂ = ρ + Π_{ker ρ}`: `p^z` on the eigenvalues `p > 0`, `1` on `ker ρ`.
`ρ̂ > 0`, and `ρ̂^{iu}` is unitary and `= 1` on `ker ρ`; likewise `ρ̂^{-a} = 1` on `ker ρ`. -/
noncomputable def hatPow (ρ : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  if h : ρ.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i ↦ if 0 < h.eigenvalues i then Complex.exp (z * Real.log (h.eigenvalues i))
        else 1) * star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 1

/-- D5.1. `ρ̂ = ρ + Π_{ker ρ}`. -/
noncomputable def hat (ρ : Matrix n n ℂ) : Matrix n n ℂ := hatPow ρ 1

/-- D5.1 Pitfall. `ρ̂^0 = I` (whereas `ρ^{[0]} = Π_{supp ρ}`). -/
theorem hatPow_zero (ρ : Matrix n n ℂ) : hatPow ρ 0 = 1 := by
  unfold hatPow
  split_ifs with h
  · simp only [zero_mul, Complex.exp_zero, ite_self, diagonal_one, Matrix.mul_one]
    exact Unitary.coe_mul_star_self h.eigenvectorUnitary
  · rfl

end D51

/-! ## The four-region setting -/

section Setting

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ D : Finset σ}

/-- `ρ_D`: the marginal of the vector `θ` on `D ⊆ Λ`. -/
noncomputable def marg (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) : Matrix (Reg loc D) (Reg loc D) ℂ :=
  ptrace hD (vecMulVec θ (star θ))

/-- `ℓ = log(e d)`. -/
noncomputable def ℓ (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)

/-- D5.12. `y = min(1, η)`, `𝓡_η = √y + √(η log(e d / y))` for `η > 0`, `𝓡_0 = 0`. -/
noncomputable def 𝓡 (d : ℕ) (η : ℝ) : ℝ :=
  if 0 < η then √(min 1 η) + √(η * Real.log (Real.exp 1 * d / min 1 η)) else 0

end Setting

/-! ## D5.2.1 Domination `ρ ≤ d (I_x ⊗ ρ_U)` -/

section D52

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T U : Finset σ}

/-- D5.2.1. For `ρ ≥ 0` on `T ⊇ U` and `d = dim(T \ U)`: `ρ ≤ d (I ⊗ ρ_U)`, `ρ_U = Tr_{T∖U} ρ`. -/
theorem step_5_2_1 (hU : U ⊆ T) {ρ : Matrix (Reg loc T) (Reg loc T) ℂ} (hρ : ρ.PosSemidef) :
    ρ ≤ (Fintype.card (Reg loc (T \ U)) : ℂ) • extendId hU (ptrace hU ρ) := by
  set e := glueEquiv (loc := loc) hU
  have hM := (posSemidef_submatrix_equiv e).2 hρ
  have h := hM.le_smul_traceRight_kronecker_one
  have htr : (ρ.submatrix e e).traceRight = ptrace hU ρ := by
    ext x y; simp [traceRight, ptrace, e]
  have hext : (extendId hU (ptrace hU ρ)).submatrix e e = ptrace hU ρ ⊗ₖ 1 := by
    rw [extendId_eq_kronecker, submatrix_submatrix]
    simp [e]
  rw [htr, ← hext, Matrix.le_iff] at h
  rw [Matrix.le_iff, ← posSemidef_submatrix_equiv e]
  convert h using 1
  ext a b
  simp

end D52

/-! ## D5.8 Phases are Hellinger-continuous (termwise inequality) -/

section D58

open Real

/-- D5.8 (D5.8.1–3), the termwise inequality: for eigenvalues `α, β ≥ 0` and real `b`, with
`α̂^{ib} = e^{ib log α}` (`= 1` at `α = 0`, D5.1),
`β |α̂^{ib} − β̂^{ib}|² ≤ 16 (1+|b|)² (√α − √β)²`. -/
theorem step_5_8 {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ℝ) :
    β * ‖Complex.exp (Complex.I * ((b * log α : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((b * log β : ℝ) : ℂ))‖ ^ 2 ≤
      16 * (1 + |b|) ^ 2 * (√α - √β) ^ 2 := by
  have h1b : b ^ 2 ≤ (1 + |b|) ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
  have hph : ∀ x y : ℝ, ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ 2 :=
    fun x y => (norm_sub_le _ _).trans (by
      rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num)
  have hph2 : ∀ x y : ℝ, ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ^ 2 ≤ 4 :=
    fun x y => by nlinarith [hph x y, norm_nonneg (Complex.exp (Complex.I * x) -
      Complex.exp (Complex.I * y))]
  rcases hβ.eq_or_lt with rfl | hβ
  · -- D5.8.1
    simp only [zero_mul]; positivity
  rcases hα.eq_or_lt with rfl | hα
  · -- D5.8.3
    have := hph2 (b * log 0) (b * log β)
    rw [sqrt_zero, zero_sub, neg_sq, sq_sqrt hβ.le]
    have h1 : 1 ≤ (1 + |b|) ^ 2 := by nlinarith [abs_nonneg b]
    nlinarith [mul_le_mul_of_nonneg_left this hβ.le]
  -- D5.8.2, `v = α/β`, `s = √v`
  set s := √α / √β with hs
  have hsα : √α = s * √β := by rw [hs, div_mul_cancel₀ _ (sqrt_pos.2 hβ).ne']
  have hspos : 0 < s := div_pos (sqrt_pos.2 hα) (sqrt_pos.2 hβ)
  have hβs : (√α - √β) ^ 2 = β * (s - 1) ^ 2 := by
    rw [hsα, show (s * √β - √β) ^ 2 = (s - 1) ^ 2 * √β ^ 2 by ring, sq_sqrt hβ.le]; ring
  have hlog : log α - log β = 2 * log s := by
    rw [hs, log_div (sqrt_pos.2 hα).ne' (sqrt_pos.2 hβ).ne', log_sqrt hα.le, log_sqrt hβ.le]
    ring
  have hdiff : ‖Complex.exp (Complex.I * ((b * log α : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((b * log β : ℝ) : ℂ))‖ =
      ‖Complex.exp (Complex.I * ((b * (2 * log s) : ℝ) : ℂ)) - 1‖ := by
    have : Complex.exp (Complex.I * ((b * log α : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((b * log β : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((b * log β : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * ((b * (2 * log s) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, ← hlog]
      congr 2
      push_cast; ring
    rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hsq : ‖Complex.exp (Complex.I * ((b * (2 * log s) : ℝ) : ℂ)) - 1‖ ^ 2 ≤
      16 * (1 + |b|) ^ 2 * (s - 1) ^ 2 := by
    by_cases hs2 : 1 / 2 ≤ s
    · have hl : |log s| ≤ 2 * |s - 1| := by
        rw [abs_le]
        have hup := log_le_sub_one_of_pos hspos
        have hlo := log_le_sub_one_of_pos (inv_pos.2 hspos)
        rw [log_inv] at hlo
        have hinv : s⁻¹ ≤ 2 := by rw [inv_le_comm₀ hspos two_pos]; linarith
        have hsinv : s⁻¹ - 1 = (1 - s) * s⁻¹ := by field_simp
        constructor
        · nlinarith [le_abs_self (s - 1), neg_abs_le (s - 1), abs_nonneg (s - 1),
            inv_pos.2 hspos]
        · nlinarith [le_abs_self (s - 1), abs_nonneg (s - 1)]
      have hn := Real.norm_exp_I_mul_ofReal_sub_one_le (x := b * (2 * log s))
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two] at hn
      have h4 : ‖Complex.exp (Complex.I * ((b * (2 * log s) : ℝ) : ℂ)) - 1‖ ≤
          4 * |b| * |s - 1| := by nlinarith [abs_nonneg b]
      have := pow_le_pow_left₀ (norm_nonneg _) h4 2
      nlinarith [sq_abs b, sq_abs (s - 1), sq_nonneg (s - 1)]
    · have hs3 : 1 / 4 ≤ (s - 1) ^ 2 := by nlinarith
      have := hph2 (b * (2 * log s)) 0
      rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
      nlinarith [sq_nonneg (s - 1), abs_nonneg b]
  rw [hdiff, hβs]
  nlinarith [mul_le_mul_of_nonneg_left hsq hβ.le]

end D58

/-! ## D5.20 Parameter bookkeeping -/

section D520

open Real

theorem one_le_ℓ {d : ℕ} (hd : 1 ≤ d) : 1 ≤ ℓ d := by
  rw [ℓ, le_log_iff_exp_le (by positivity)]
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [exp_pos 1]

theorem ℓ_mono {d d' : ℕ} (hd : 1 ≤ d) (h : d ≤ d') : ℓ d ≤ ℓ d' := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact log_le_log (by positivity) (by gcongr)

/-- D5.20. With `1 ≤ d = dim x ≤ d_h`, `m = min(1, 𝓡_η)` and `0 ≤ η ≤ 2ℓ_h` (D2.2 item 4:
`η = S(x|P) + S(x|U) ≤ 2 log d`): `ℓ_h² m^{1/2} + 𝓡_η² ≤ C ℓ_h⁴ η^{1/8}`, with `C = 10`. -/
theorem step_5_20 {d dh : ℕ} (hd : 1 ≤ d) (hddh : d ≤ dh) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 2 * ℓ dh) :
    ℓ dh ^ 2 * √(min 1 (𝓡 d η)) + 𝓡 d η ^ 2 ≤ 10 * ℓ dh ^ 4 * η ^ (1 / 8 : ℝ) := by
  set L := ℓ dh
  have hL : 1 ≤ L := one_le_ℓ (hd.trans hddh)
  have hld : ℓ d ≤ L := ℓ_mono hd hddh
  rcases hη0.eq_or_lt with rfl | hηp
  · simp [𝓡]
  set q := η ^ (1 / 8 : ℝ) with hq
  have hq0 : 0 < q := rpow_pos_of_pos hηp _
  have hq8 : q ^ 8 = η := by
    rw [hq, ← rpow_natCast, ← rpow_mul hηp.le]; norm_num
  have hsq : √η = q ^ 4 := by rw [← hq8, show q ^ 8 = (q ^ 4) ^ 2 by ring, sqrt_sq (by positivity)]
  have hR0 : 0 ≤ 𝓡 d η := by rw [𝓡, if_pos hηp]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases h1 : η ≤ 1
  · -- D5.20.1
    have hmin : min 1 η = η := min_eq_right h1
    have hq1 : q ≤ 1 := (pow_le_one_iff_of_nonneg hq0.le (by norm_num : 8 ≠ 0)).1 (hq8 ▸ h1)
    have hq4 : 0 < q ^ 4 := pow_pos hq0 4
    have hlogη : -log η ≤ 2 * (q ^ 4)⁻¹ := by
      have h := log_le_sub_one_of_pos (inv_pos.2 hq4)
      rw [log_inv] at h
      have : log η = 2 * log (q ^ 4) := by
        rw [← hq8, show q ^ 8 = (q ^ 4) ^ 2 by ring, log_pow]; norm_num
      nlinarith [inv_pos.2 hq4]
    have hge : 1 ≤ exp 1 * d / η := by
      rw [le_div_iff₀ hηp]
      nlinarith [add_one_le_exp (1 : ℝ), (by exact_mod_cast hd : (1 : ℝ) ≤ d)]
    have hA0 : 0 ≤ η * log (exp 1 * d / η) := mul_nonneg hηp.le (log_nonneg hge)
    have hA : η * log (exp 1 * d / η) ≤ 3 * L * q ^ 4 := by
      rw [log_div (by positivity) hηp.ne']
      have e1 : η * (2 * (q ^ 4)⁻¹) = 2 * q ^ 4 := by
        rw [← hq8]; field_simp
      have e2 : q ^ 8 ≤ q ^ 4 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
      have := mul_le_mul_of_nonneg_left hlogη hηp.le
      have := mul_le_mul_of_nonneg_left hld hηp.le
      have hℓ : ℓ d = log (exp 1 * d) := rfl
      nlinarith [mul_le_mul_of_nonneg_left hL hq4.le]
    have hR : 𝓡 d η = q ^ 4 + √(η * log (exp 1 * d / η)) := by
      rw [𝓡, if_pos hηp, hmin, hsq]
    have hR2 : 𝓡 d η ^ 2 ≤ 8 * L * q ^ 4 := by
      rw [hR]
      have hs2 := sq_sqrt hA0
      have e2 : q ^ 8 ≤ q ^ 4 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
      nlinarith [sq_nonneg (q ^ 4 - √(η * log (exp 1 * d / η))),
        mul_le_mul_of_nonneg_left hL hq4.le]
    have hR4 : 𝓡 d η ≤ 4 * L ^ 2 * q ^ 2 := by
      have : 𝓡 d η ^ 2 ≤ (4 * L ^ 2 * q ^ 2) ^ 2 := by
        have hL1 : L ≤ L ^ 4 := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hL1 hq4.le]
      exact (pow_le_pow_iff_left₀ hR0 (by positivity) two_ne_zero).1 this
    have hm : √(min 1 (𝓡 d η)) ≤ 2 * L * q := by
      rw [show 2 * L * q = √((2 * L * q) ^ 2) by rw [sqrt_sq (by positivity)]]
      exact sqrt_le_sqrt ((min_le_right _ _).trans (by nlinarith))
    have hq41 : q ^ 4 ≤ q := by
      calc q ^ 4 ≤ q ^ 1 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
        _ = q := pow_one q
    have hL3 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    have hL1 : L ≤ L ^ 4 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg L), mul_le_mul_of_nonneg_left hL3 hq0.le,
      mul_le_mul_of_nonneg_left hq41 (by linarith : (0 : ℝ) ≤ 8 * L),
      mul_le_mul_of_nonneg_left hL1 hq0.le]
  · -- D5.20.2
    have h1' : 1 < η := not_le.1 h1
    have hmin : min 1 η = 1 := min_eq_left h1'.le
    have hR : 𝓡 d η = 1 + √(η * ℓ d) := by rw [𝓡, if_pos hηp, hmin, sqrt_one, div_one, ℓ]
    have hηl : η * ℓ d ≤ (2 * L) ^ 2 := by nlinarith [one_le_ℓ hd]
    have hs : √(η * ℓ d) ≤ 2 * L := by
      rw [sqrt_le_left (by positivity)]; exact hηl
    have hR3 : 𝓡 d η ≤ 3 * L := by rw [hR]; linarith
    have hm : √(min 1 (𝓡 d η)) ≤ 1 := by
      rw [sqrt_le_one]; exact min_le_left _ _
    have hq1 : 1 ≤ q := one_le_rpow h1'.le (by norm_num)
    have hL2 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    nlinarith [pow_le_pow_left₀ hR0 hR3 2, mul_le_mul_of_nonneg_left hm (sq_nonneg L),
      mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ 10 * L ^ 4)]

end D520

/-! ## Lemma 5.1, Lemma 5.2, Lemma 5.3: statements -/

section Statements

universe u v

/-- D5.5 **Lemma 5.1** (conditional movement estimate). `θ` unit pure vector on
finite-dimensional `P, x, U, F`; `ρ_D` its marginals; `d = dim x`, `ℓ = log(e d)`,
`η = S(x|P)_θ + S(x|U)_θ = I(x:F|U)_θ = I(x:F|P)_θ`. Universal `c, C > 0` such that for
`0 < aℓ ≤ c` and all density matrices `σ` on `xP`, `τ` on `xU`:
`‖σ^{a/2} ρ̂_P^{-a/2} τ^{a/2} ρ̂_U^{-a/2} θ‖ ≤ exp(-(a/2) η + C a^{5/4} ℓ²)`.
Same bound for positive subnormalised `σ, τ` (stated so: `σ, τ ≥ 0`, `Tr ≤ 1`). -/
def Lemma_5_1 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P X U F : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
      (hF : F ⊆ Λ), Λ = P ∪ X ∪ U ∪ F → Disjoint P X → Disjoint P U → Disjoint P F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1) (a : ℝ),
      0 < a * ℓ (Fintype.card (Reg loc X)) → a * ℓ (Fintype.card (Reg loc X)) ≤ c →
    ∀ (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
      (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ),
      σ'.PosSemidef → σ'.trace.re ≤ 1 → τ.PosSemidef → τ.trace.re ≤ 1 →
      ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hP) (bracketPow σ' (a / 2 : ℝ)) *
          extendId hP (hatPow (marg θ hP) (-(a / 2 : ℝ))) *
          extendId (Finset.union_subset hX hU) (bracketPow τ (a / 2 : ℝ)) *
          extendId hU (hatPow (marg θ hU) (-(a / 2 : ℝ)))) *ᵥ θ) :
            EuclideanSpace ℂ (Reg loc Λ))‖ ≤
        Real.exp (-(a / 2) * condMutualInfo (pureState θ hθ).toSubState hX hU hF +
          C * a ^ (5 / 4 : ℝ) * ℓ (Fintype.card (Reg loc X)) ^ 2)

/-- D5.12 **Lemma 5.2** (marginal-phase comparison). `θ` unit pure vector on finite-dimensional
`P, x, U, F`; `d = dim x`, `η = I(x:F|U)_θ`, `𝓡_η` as in `𝓡`. Universal `C` such that for every
real `u`: `‖(ρ̂_U^{-iu} ρ̂_{xU}^{iu} − ρ̂_{UF}^{-iu} ρ̂_{xUF}^{iu}) θ‖ ≤ C |sinh(πu)| 𝓡_η`.
Constants independent of `dim P, U, F`. -/
def Lemma_5_2 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P X U F : Finset σ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
      (hF : F ⊆ Λ), Λ = P ∪ X ∪ U ∪ F → Disjoint P X → Disjoint P U → Disjoint P F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1) (u : ℝ),
      ‖(WithLp.toLp 2 ((extendId hU (hatPow (marg θ hU) (-(u * Complex.I))) *
          extendId (Finset.union_subset hX hU)
            (hatPow (marg θ (Finset.union_subset hX hU)) (u * Complex.I)) -
          extendId (Finset.union_subset hU hF)
            (hatPow (marg θ (Finset.union_subset hU hF)) (-(u * Complex.I))) *
          extendId (Finset.union_subset (Finset.union_subset hX hU) hF)
            (hatPow (marg θ (Finset.union_subset (Finset.union_subset hX hU) hF))
              (u * Complex.I))) *ᵥ θ) : EuclideanSpace ℂ (Reg loc Λ))‖ ≤
        C * |Real.sinh (Real.pi * u)| *
          𝓡 (Fintype.card (Reg loc X)) (condMutualInfo (pureState θ hθ).toSubState hX hU hF)

/-- D5.15. The entire function
`f(z) = ⟨θ, ρ_P^{[z]} ρ_Y^{[-z]} h ρ_P^{[-z]} ρ_Y^{[z]} θ⟩` of Lemma 5.3, `Y = xU`,
`P = P₀P₁`, `h` on `P₀x`. -/
noncomputable def f {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {Λ P₀ P₁ X U : Finset σ} (hP : P₀ ∪ P₁ ⊆ Λ) (hY : X ∪ U ⊆ Λ)
    (hPX : P₀ ∪ X ⊆ Λ) (θ : Reg loc Λ → ℂ) (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ)
    (z : ℂ) : ℂ :=
  star θ ⬝ᵥ ((extendId hP (bracketPow (marg θ hP) z) * extendId hY (bracketPow (marg θ hY) (-z)) *
    extendId hPX h * extendId hP (bracketPow (marg θ hP) (-z)) *
    extendId hY (bracketPow (marg θ hY) z)) *ᵥ θ)

/-- D5.15 **Lemma 5.3** (conditional skew estimate). `θ` unit pure vector on `P, x, U, F`;
`Y = xU`; `P = P₀P₁` and `0 ≤ h ≤ I` supported on `P₀x`. `d_h = (dim P₀)(dim x)`,
`ℓ_h = log(e d_h)`, `η = I(x:F|U)_θ = I(x:F|P)_θ`. Universal `c, C > 0` such that for
`0 < aℓ_h ≤ c` and `t = a/2`: `|f(t)| − Re f(t) ≤ C a² ℓ_h⁴ η^{1/8}`. -/
def Lemma_5_3 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P₀ P₁ X U F : Finset σ) (hP₀ : P₀ ⊆ Λ) (hP₁ : P₁ ⊆ Λ)
      (hX : X ⊆ Λ) (hU : U ⊆ Λ) (hF : F ⊆ Λ), Λ = P₀ ∪ P₁ ∪ X ∪ U ∪ F →
      Disjoint P₀ P₁ → Disjoint (P₀ ∪ P₁) X → Disjoint (P₀ ∪ P₁) U → Disjoint (P₀ ∪ P₁) F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
      (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ), 0 ≤ h → h ≤ 1 →
    ∀ a : ℝ, 0 < a * ℓ (Fintype.card (Reg loc (P₀ ∪ X))) →
      a * ℓ (Fintype.card (Reg loc (P₀ ∪ X))) ≤ c →
      ‖f (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU) (Finset.union_subset hP₀ hX)
          θ h (a / 2 : ℝ)‖ -
        (f (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU)
          (Finset.union_subset hP₀ hX) θ h (a / 2 : ℝ)).re ≤
        C * a ^ 2 * ℓ (Fintype.card (Reg loc (P₀ ∪ X))) ^ 4 *
          condMutualInfo (pureState θ hθ).toSubState hX hU hF ^ (1 / 8 : ℝ)

end Statements

end AreaLaw
