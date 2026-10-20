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
