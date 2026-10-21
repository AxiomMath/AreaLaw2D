import AreaLaw.S05_Conditional.Spectral
import AreaLaw.S05_Conditional.LogMoments
import AreaLaw.S05_Conditional.Interpolation
import AreaLaw.S05_Conditional.Faithful52

/-!
# §5.1 Lemma 5.1: shared objects and the statements of its steps

Digest `digest/05-conditional.md`, D5.2–D5.11. The matrix level works on one finite index type
with a *conditional pair* `(ρ, Q)` (`IsCondPair`: `ρ` a density matrix, `Q > 0`, `ρ ≤ d Q`,
`Tr Π_{supp ρ} Q ≤ d`), the abstraction of `ρ = ρ_{xU}`, `Q = I_x ⊗ ρ̂_U` (D5.2). The region
level is the four-region setting of `Lemma_5_1`.

* Generic spectral lemmas: eigenvector overlaps `ovl`, `trace_specFun_mul_specFun`,
  `specFun_specFun`, `hatPow_hat`, `hatPow_Qmat`.
* Objects: `relEnt` (`𝔼 L`), `Kmat` (`K = Q^{-a} ρ Q^{-a}`), `rexp` (`r = (1-2a)⁻¹`), `trKr`,
  `Zval` (`Z = (Tr K^r)^{1/r}`), `xiMat` (`ξ = K^r / Tr K^r`); `Qmat`, `tauU` (`τ_u`), `thetaU`
  (`θ_u`), `sigmaU` (`σ'` of D5.10.1), `Gfun` (`G`).
* Statements: `ArakiLiebThirring` (formal route of D5.4.2–4), `Step_5_2`, `Step_5_4`,
  `Step_5_6`, `Step_5_7_matrix`, `Step_5_9` (matrix level); `Step_5_2_region`, `Step_5_5_A`,
  `Step_5_9_1`, `Step_5_5_3`, `Step_5_6_1`, `Step_5_10_1`, `Step_5_10_3` (region level);
  `Lemma_5_1_faithful`.
-/

namespace AreaLaw

open Arealaw Matrix Complex
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder

universe u v

namespace Conditional

/-! ## Generic spectral lemmas -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `|⟨v_i, w_j⟩|²` for the eigenvectors `v_i` of `A`, `w_j` of `B` (Hermitian). -/
noncomputable def ovl {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    ℝ :=
  Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *
    (hB.eigenvectorUnitary : Matrix n n ℂ)) i j)

variable {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)

theorem ovl_nonneg (i j : n) : 0 ≤ ovl hA hB i j := Complex.normSq_nonneg _

private theorem unitary_V :
    star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ) ∈
      unitary (Matrix n n ℂ) :=
  Submonoid.mul_mem _ (Unitary.star_mem (SetLike.coe_mem _)) (SetLike.coe_mem _)

private theorem sum_normSq_row {V : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ)) (i : n) :
    ∑ j, Complex.normSq (V i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ ↦ (M i i).re) (Unitary.mul_star_self_of_mem hV)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_conj] using h

private theorem sum_normSq_col {V : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ)) (j : n) :
    ∑ i, Complex.normSq (V i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ ↦ (M j j).re) (Unitary.star_mul_self_of_mem hV)
  simpa [Matrix.mul_apply, Matrix.star_apply, ← Complex.normSq_eq_conj_mul_self] using h

/-- Rows of the overlap matrix sum to one. -/
theorem sum_ovl_right (i : n) : ∑ j, ovl hA hB i j = 1 := sum_normSq_row (unitary_V hA hB) i

/-- Columns of the overlap matrix sum to one. -/
theorem sum_ovl_left (j : n) : ∑ i, ovl hA hB i j = 1 := sum_normSq_col (unitary_V hA hB) j

private theorem trace_diagonal_mul_mul_star (V : Matrix n n ℂ) (F G : n → ℂ) :
    (diagonal F * V * diagonal G * star V).trace =
      ∑ i, ∑ j, F i * G j * (Complex.normSq (V i j) : ℂ) := by
  have e : diagonal F * V * diagonal G = of fun i j ↦ F i * V i j * G j := by
    ext i j; simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  ring

/-- `Tr f(A) g(B) = ∑_{ij} f(α_i) g(β_j) |⟨v_i, w_j⟩|²`. -/
theorem trace_specFun_mul_specFun (f g : ℝ → ℂ) :
    (specFun hA f * specFun hB g).trace =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) * (ovl hA hB i j : ℂ) := by
  have e : specFun hA f * specFun hB g = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (diagonal (fun i ↦ f (hA.eigenvalues i)) * (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
        (hB.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (fun j ↦ g (hB.eigenvalues j)) *
        star (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ))) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    simp only [specFun, star_mul, star_star, Matrix.mul_assoc]
    rw [Unitary.mul_star_self_of_mem (SetLike.coe_mem _), Matrix.mul_one]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul,
    trace_diagonal_mul_mul_star]
  rfl

/-- A real spectral function of a Hermitian matrix is Hermitian. -/
theorem isHermitian_specFun_ofReal {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (g : ℝ → ℝ) :
    (specFun h fun t ↦ (g t : ℂ)).IsHermitian := by
  rw [IsHermitian, ← star_eq_conjTranspose, star_specFun]
  congr 1
  funext t
  simp

/-- Composition: `f(g(ρ)) = (f ∘ g)(ρ)` for real `g`. -/
theorem specFun_specFun {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (g : ℝ → ℝ)
    (h' : (specFun h fun t ↦ (g t : ℂ)).IsHermitian) (f : ℝ → ℂ) :
    specFun h' f = specFun h fun t ↦ f (g t) := by
  have key := Conditional.diagonal_intertwine (Unitary.coe_star_mul_self h'.eigenvectorUnitary)
    (Unitary.coe_mul_star_self h'.eigenvectorUnitary)
    (Unitary.coe_star_mul_self h.eigenvectorUnitary)
    (Unitary.coe_mul_star_self h.eigenvectorUnitary)
    (a := h'.eigenvalues) (b := fun i ↦ g (h.eigenvalues i)) (1 : Matrix n n ℂ) (by
      rw [Matrix.mul_one, Matrix.one_mul]
      change specFun h' (fun t ↦ (t : ℂ)) = _
      rw [specFun_ofReal]
      rfl) f
  rw [Matrix.mul_one, Matrix.one_mul] at key
  exact key

/-- `(ρ̂)^̂z = ρ̂^z`. -/
theorem hatPow_hat {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (z : ℂ) :
    hatPow (hat ρ) z = hatPow ρ z := by
  set g : ℝ → ℝ := fun t ↦ if 0 < t then t else 1
  have e : hat ρ = specFun h fun t ↦ (g t : ℂ) := by
    rw [hat, hatPow_eq h]
    refine specFun_congr h fun i ↦ ?_
    by_cases ht : 0 < h.eigenvalues i
    · simp [hfun, g, ht, ← Complex.ofReal_exp, Real.exp_log ht]
    · simp [hfun, g, ht]
  have h' := isHermitian_specFun_ofReal h g
  rw [e, hatPow_eq h', specFun_specFun h g h', hatPow_eq h]
  refine specFun_congr h fun i ↦ ?_
  by_cases ht : 0 < h.eigenvalues i <;> simp [hfun, g, ht]

end Generic

/-! ## Matrix-level objects (D5.2, D5.4, D5.6) -/

section Objects

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D5.2 setting. `(ρ, Q)` is a *conditional pair* with dimension `d`: `ρ` a density matrix,
`Q > 0`, `ρ ≤ d Q` (D5.2.1) and `Tr Π_{supp ρ} Q ≤ d` (D5.2.2, D5.2.5). For `ρ = ρ_{xU}`,
`Q = I_x ⊗ ρ̂_U`, `d = dim x` (`Step_5_2_region`). -/
def IsCondPair (ρ Q : Matrix n n ℂ) (d : ℕ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧ Q.PosDef ∧ 1 ≤ d ∧ ρ ≤ (d : ℂ) • Q ∧
    (bracketPow ρ 0 * Q).trace.re ≤ d

/-- D5.2. `𝔼 L = Tr ρ log ρ − Tr ρ log Q` (`= -S(x|U)` for the regional pair). -/
noncomputable def relEnt (ρ Q : Matrix n n ℂ) : ℝ :=
  (ρ * cfc Real.log ρ).trace.re - (ρ * cfc Real.log Q).trace.re

/-- D5.4. `K = Q^{-a} ρ Q^{-a}`. -/
noncomputable def Kmat (ρ Q : Matrix n n ℂ) (a : ℝ) : Matrix n n ℂ :=
  hatPow Q ((-a : ℝ) : ℂ) * ρ * hatPow Q ((-a : ℝ) : ℂ)

/-- D5.4. `r = (1 - 2a)⁻¹`. -/
noncomputable def rexp (a : ℝ) : ℝ := (1 - 2 * a)⁻¹

/-- D5.4. `Tr K^r`. -/
noncomputable def trKr (ρ Q : Matrix n n ℂ) (a : ℝ) : ℝ :=
  (bracketPow (Kmat ρ Q a) (rexp a : ℂ)).trace.re

/-- D5.4. `Z = (Tr K^r)^{1/r} = ‖K‖_r`. -/
noncomputable def Zval (ρ Q : Matrix n n ℂ) (a : ℝ) : ℝ := trKr ρ Q a ^ (1 - 2 * a)

/-- D5.6. `ξ = K^r / Tr K^r`. -/
noncomputable def xiMat (ρ Q : Matrix n n ℂ) (a : ℝ) : Matrix n n ℂ :=
  ((trKr ρ Q a)⁻¹ : ℂ) • bracketPow (Kmat ρ Q a) (rexp a : ℂ)

end Objects

/-! ## Region-level objects (D5.5.3, D5.6, D5.9, D5.10) -/

section RegionObjects

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ P X U : Finset σ}

/-- D5.2. `Q = I_x ⊗ ρ̂_E` on `x ∪ E`. -/
noncomputable def Qmat (θ : Reg loc Λ → ℂ) {E : Finset σ} (hE : E ⊆ Λ) (X : Finset σ) :
    Matrix (Reg loc (X ∪ E)) (Reg loc (X ∪ E)) ℂ :=
  extendId Finset.subset_union_right (hat (marg θ hE))

/-- `Q^̂z = I_x ⊗ ρ̂_E^z`. -/
theorem hatPow_Qmat (θ : Reg loc Λ → ℂ) {E : Finset σ} (hE : E ⊆ Λ) (X : Finset σ) (z : ℂ) :
    hatPow (Qmat θ hE X) z = extendId Finset.subset_union_right (hatPow (marg θ hE) z) := by
  have h : (hat (marg θ hE)).IsHermitian := by
    simpa [hat] using isHermitian_hatPow_ofReal (marg θ hE) 1
  rw [Qmat, hatPow_extendId _ h, hatPow_hat (isHermitian_marg θ hE)]

/-- D5.6. `τ_u = Q^{-iau} τ Q^{iau}` on `x ∪ U`. -/
noncomputable def tauU (θ : Reg loc Λ → ℂ) (hU : U ⊆ Λ) (X : Finset σ)
    (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ) (a u : ℝ) :
    Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ :=
  hatPow (Qmat θ hU X) ((-(a * u) : ℝ) * I) * τ * hatPow (Qmat θ hU X) ((a * u : ℝ) * I)

/-- D5.9. `θ_u = τ^{-iau} ρ̂_U^{iau} θ`. -/
noncomputable def thetaU (θ : Reg loc Λ → ℂ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
    (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ) (a u : ℝ) : Reg loc Λ → ℂ :=
  extendId (Finset.union_subset hX hU) (hatPow τ ((-(a * u) : ℝ) * I)) *ᵥ
    (extendId hU (hatPow (marg θ hU) ((a * u : ℝ) * I)) *ᵥ θ)

/-- D5.10.1. `σ' = ρ̂_P^{iau} σ ρ̂_P^{-iau}` on `x ∪ P`. -/
noncomputable def sigmaU (θ : Reg loc Λ → ℂ) (hP : P ⊆ Λ) (X : Finset σ)
    (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ) (a u : ℝ) :
    Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ :=
  extendId Finset.subset_union_right (hatPow (marg θ hP) ((a * u : ℝ) * I)) * σ' *
    extendId Finset.subset_union_right (hatPow (marg θ hP) ((-(a * u) : ℝ) * I))

/-- D5.5.3. `G(z) = σ^{[az]} ρ̂_P^{-az} τ^{[a(1-z)]} ρ̂_U^{-a(1-z)} θ`. -/
noncomputable def Gfun (θ : Reg loc Λ → ℂ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
    (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
    (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ) (a : ℝ) (z : ℂ) :
    EuclideanSpace ℂ (Reg loc Λ) :=
  WithLp.toLp 2 ((extendId (Finset.union_subset hX hP) (bracketPow σ' (a * z)) *
    extendId hP (hatPow (marg θ hP) (-(a * z))) *
    extendId (Finset.union_subset hX hU) (bracketPow τ (a * (1 - z))) *
    extendId hU (hatPow (marg θ hU) (-(a * (1 - z))))) *ᵥ θ)

end RegionObjects

end Conditional

open Conditional

/-! ## Matrix-level statements -/

/-- D5.4.2–4, formal route (Araki–Lieb–Thirring): for `A ≥ 0`, `Q > 0`, real `s` and `r ≥ 1`,
`Tr (Q^s A Q^s)^r ≤ Tr A^r Q^{2sr}`. (The paper's Stein interpolation of
`T(z) = ρ^{[z/2]} Q^{-az}` proves the case `s = -a`.) -/
def ArakiLiebThirring : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n] (A Q : Matrix n n ℂ), A.PosSemidef → Q.PosDef →
    ∀ s r : ℝ, 1 ≤ r →
      (bracketPow (hatPow Q (s : ℂ) * A * hatPow Q (s : ℂ)) (r : ℂ)).trace.re ≤
        (bracketPow A (r : ℂ) * hatPow Q ((2 * s * r : ℝ) : ℂ)).trace.re

/-- D5.2 (`eq:conditional-log-moments`), matrix level. For a conditional pair `(ρ, Q)`,
eigenvalues `p_i` of `ρ`, `q_j > 0` of `Q`, the weights `w_{ij} = p_i |⟨i, j⟩|²` and
`L_{ij} = log p_i − log q_j`: `∑ w = 1`, `𝔼 e^{L} ≤ d`, `𝔼 e^{-L} ≤ d`, `𝔼 L = Tr ρ log ρ −
Tr ρ log Q`, and `Tr ρ^{1+s} Q^{-s} = 𝔼 e^{sL}` for real `s`. -/
def Step_5_2 : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n] (ρ Q : Matrix n n ℂ) (d : ℕ)
    (hρ : ρ.IsHermitian) (hQ : Q.IsHermitian), IsCondPair ρ Q d →
    (∀ i j, 0 ≤ hρ.eigenvalues i * ovl hρ hQ i j) ∧
    ∑ i, ∑ j, hρ.eigenvalues i * ovl hρ hQ i j = 1 ∧
    ∑ i, ∑ j, hρ.eigenvalues i * ovl hρ hQ i j *
      Real.exp (Real.log (hρ.eigenvalues i) - Real.log (hQ.eigenvalues j)) ≤ d ∧
    ∑ i, ∑ j, hρ.eigenvalues i * ovl hρ hQ i j *
      Real.exp (-(Real.log (hρ.eigenvalues i) - Real.log (hQ.eigenvalues j))) ≤ d ∧
    ∑ i, ∑ j, hρ.eigenvalues i * ovl hρ hQ i j *
      (Real.log (hρ.eigenvalues i) - Real.log (hQ.eigenvalues j)) = relEnt ρ Q ∧
    ∀ s : ℝ, (bracketPow ρ ((1 + s : ℝ) : ℂ) * hatPow Q ((-s : ℝ) : ℂ)).trace.re =
      ∑ i, ∑ j, hρ.eigenvalues i * ovl hρ hQ i j *
        Real.exp (s * (Real.log (hρ.eigenvalues i) - Real.log (hQ.eigenvalues j)))

/-- D5.4 (`eq:conditional-schatten`) with D5.6.2 (Hölder). Universal `c ≤ 1/8`, `C`: for a
conditional pair `(ρ, Q)` with dimension `d` and `0 < a`, `a ℓ ≤ c`: `Z > 0`,
`log Z ≤ 2a 𝔼L + C a² ℓ²`, and `Tr τ^{2a} K ≤ Z` for every `τ ≥ 0` with `Tr τ ≤ 1`. -/
def Step_5_4 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 8 ∧ 0 < C ∧
    ∀ (n : Type u) [Fintype n] [DecidableEq n] (ρ Q : Matrix n n ℂ) (d : ℕ), IsCondPair ρ Q d →
    ∀ a : ℝ, 0 < a → a * ℓ d ≤ c →
      0 < Zval ρ Q a ∧ Real.log (Zval ρ Q a) ≤ 2 * a * relEnt ρ Q + C * a ^ 2 * ℓ d ^ 2 ∧
      ∀ τ : Matrix n n ℂ, τ.PosSemidef → τ.trace.re ≤ 1 →
        (bracketPow τ ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace.re ≤ Zval ρ Q a

/-- D5.6.2, D5.6.4 (`eq:conditional-overlap`), matrix level. For a conditional pair and
`0 < a < 1/2`: `Tr K^r > 0`; for `τ ≥ 0`, `Tr τ^{2a} ξ^{[1-2a]} = Tr τ^{2a} K / Z`
(`ξ^{[1-2a]} = K / Z`), and `Tr τ^{2a} K > 0` when `τ > 0`. -/
def Step_5_6 : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n] (ρ Q : Matrix n n ℂ) (d : ℕ), IsCondPair ρ Q d →
    ∀ a : ℝ, 0 < a → a < 1 / 2 → 0 < trKr ρ Q a ∧
      ∀ τ : Matrix n n ℂ, τ.PosSemidef →
        (bracketPow τ ((2 * a : ℝ) : ℂ) * bracketPow (xiMat ρ Q a) ((1 - 2 * a : ℝ) : ℂ)).trace.re =
          (bracketPow τ ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace.re / Zval ρ Q a ∧
        (τ.PosDef → 0 < (bracketPow τ ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace.re)

/-- D5.7 (`eq:conditional-hellinger`), matrix level. Universal `c, C`: for a conditional pair
and `0 < a`, `a ℓ ≤ c`: `ξ` is a density matrix and `H² = ‖√ρ − √ξ‖₂² ≤ C a ℓ²`. -/
def Step_5_7_matrix : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (n : Type u) [Fintype n] [DecidableEq n] (ρ Q : Matrix n n ℂ) (d : ℕ), IsCondPair ρ Q d →
    ∀ a : ℝ, 0 < a → a * ℓ d ≤ c →
      (xiMat ρ Q a).PosSemidef ∧ (xiMat ρ Q a).trace = 1 ∧
      ((CFC.sqrt ρ - CFC.sqrt (xiMat ρ Q a))ᴴ * (CFC.sqrt ρ - CFC.sqrt (xiMat ρ Q a))).trace.re ≤
        C * a * ℓ d ^ 2

/-- D5.9 (`eq:conditional-state-movement`, D5.9.1–7) with D5.8, matrix level. Universal `C`:
for a conditional pair `(ρ, Q)`, a density matrix `ξ`, `τ > 0` with `Tr τ ≤ 1`, `0 < a ≤ 1/4`,
`λ ≥ 0` with `Tr τ^{2a} ξ^{[1-2a]} ≥ e^{-2λ}`, and real `u`:
`‖(τ^{-iau} − Q^{-iau}) √ρ‖₂ ≤ C (1+|u|) (√λ + √a ℓ + ‖√ρ − √ξ‖₂)`. -/
def Step_5_9 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : Type u) [Fintype n] [DecidableEq n] (ρ Q ξ τ : Matrix n n ℂ) (d : ℕ),
      IsCondPair ρ Q d → ξ.PosSemidef → ξ.trace = 1 → τ.PosDef → τ.trace.re ≤ 1 →
    ∀ a lam u : ℝ, 0 < a → a ≤ 1 / 4 → 0 ≤ lam →
      Real.exp (-2 * lam) ≤
        (bracketPow τ ((2 * a : ℝ) : ℂ) * bracketPow ξ ((1 - 2 * a : ℝ) : ℂ)).trace.re →
      √((((hatPow τ ((-(a * u) : ℝ) * I) - hatPow Q ((-(a * u) : ℝ) * I)) * CFC.sqrt ρ)ᴴ *
          ((hatPow τ ((-(a * u) : ℝ) * I) - hatPow Q ((-(a * u) : ℝ) * I)) * CFC.sqrt ρ)).trace.re)
        ≤ C * (1 + |u|) * (√lam + √a * ℓ d +
          √((CFC.sqrt ρ - CFC.sqrt ξ)ᴴ * (CFC.sqrt ρ - CFC.sqrt ξ)).trace.re)

/-! ## Region-level statements -/

/-- D5.2 at the region level, with (F1) for D5.6.2. For a unit `θ` and disjoint `X, E`:
`(ρ_{XE}, I_X ⊗ ρ̂_E)` is a conditional pair with `d = dim X`, its `𝔼 L` is `-S(X|E)_θ`, and
`‖τ^{[a]} ρ̂_E^{-a} θ‖² = Tr τ^{[2a]} K` for `τ ≥ 0`, `a > 0`. -/
def Step_5_2_region : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ X E : Finset σ) (hX : X ⊆ Λ) (hE : E ⊆ Λ), Disjoint X E →
  ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1),
    IsCondPair (marg θ (Finset.union_subset hX hE)) (Qmat θ hE X) (Fintype.card (Reg loc X)) ∧
    relEnt (marg θ (Finset.union_subset hX hE)) (Qmat θ hE X) =
      -condEntropy (pureState θ hθ).toSubState hX hE ∧
    ∀ (τ : Matrix (Reg loc (X ∪ E)) (Reg loc (X ∪ E)) ℂ), τ.PosSemidef → ∀ a : ℝ, 0 < a →
      ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hE) (bracketPow τ (a : ℂ)) *
          extendId hE (hatPow (marg θ hE) ((-a : ℝ) : ℂ))) *ᵥ θ) :
            EuclideanSpace ℂ (Reg loc Λ))‖ ^ 2 =
        (bracketPow τ ((2 * a : ℝ) : ℂ) *
          Kmat (marg θ (Finset.union_subset hX hE)) (Qmat θ hE X) a).trace.re

/-- D5.5.A. For a unit `θ` on `P ⊔ X ⊔ U ⊔ F`: `I(X:F|U)_θ = S(X|P)_θ + S(X|U)_θ`. -/
def Step_5_5_A : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ P X U F : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
    (hF : F ⊆ Λ), Λ = P ∪ X ∪ U ∪ F → Disjoint P X → Disjoint P U → Disjoint P F →
    Disjoint X U → Disjoint X F → Disjoint U F →
  ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1),
    condMutualInfo (pureState θ hθ).toSubState hX hU hF =
      condEntropy (pureState θ hθ).toSubState hX hP + condEntropy (pureState θ hθ).toSubState hX hU

/-- D5.9.1 with (F1). For a unit `θ`, disjoint `X, U`, `τ > 0` on `XU`:
`‖θ_u − θ‖ = ‖(τ_u^{-iau} − Q^{-iau}) √ρ_{XU}‖₂`. -/
def Step_5_9_1 : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ X U : Finset σ) (hX : X ⊆ Λ) (hU : U ⊆ Λ), Disjoint X U →
  ∀ (θ : Reg loc Λ → ℂ), star θ ⬝ᵥ θ = 1 →
  ∀ (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ), τ.PosDef → ∀ a u : ℝ,
    let W := (hatPow (tauU θ hU X τ a u) ((-(a * u) : ℝ) * I) -
        hatPow (Qmat θ hU X) ((-(a * u) : ℝ) * I)) * CFC.sqrt (marg θ (Finset.union_subset hX hU))
    ‖(WithLp.toLp 2 (thetaU θ hX hU τ a u - θ) : EuclideanSpace ℂ (Reg loc Λ))‖ =
      √(Wᴴ * W).trace.re

/-- D5.5.3. `G` is entire, bounded on the closed strip `0 ≤ Re z ≤ 1`, and `G(1/2)` is the vector
of Lemma 5.1, for `σ ≥ 0` on `XP`, `τ > 0` on `XU`. -/
def Step_5_5_3 : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ P X U : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
    (θ : Reg loc Λ → ℂ) (a : ℝ) (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
    (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ), 0 < a → σ'.PosSemidef → τ.PosDef →
    Gfun θ hP hX hU σ' τ a (1 / 2) =
      WithLp.toLp 2 ((extendId (Finset.union_subset hX hP) (bracketPow σ' (a / 2 : ℝ)) *
        extendId hP (hatPow (marg θ hP) (-(a / 2 : ℝ))) *
        extendId (Finset.union_subset hX hU) (bracketPow τ (a / 2 : ℝ)) *
        extendId hU (hatPow (marg θ hU) (-(a / 2 : ℝ)))) *ᵥ θ) ∧
    Differentiable ℂ (Gfun θ hP hX hU σ' τ a) ∧
    BddAbove ((norm ∘ Gfun θ hP hX hU σ' τ a) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)

/-- D5.6.1. Left boundary: `‖G(iu)‖ ≤ ‖τ_u^{[a]} ρ̂_U^{-a} θ‖`, and `τ_u > 0`, `Tr τ_u = Tr τ`. -/
def Step_5_6_1 : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ P X U : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ),
    Disjoint P X → Disjoint P U → Disjoint X U →
  ∀ (θ : Reg loc Λ → ℂ) (a : ℝ) (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
    (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ), 0 < a → σ'.PosSemidef → τ.PosDef →
  ∀ u : ℝ,
    ‖Gfun θ hP hX hU σ' τ a (u * I)‖ ≤
      ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hU) (bracketPow (tauU θ hU X τ a u) a) *
          extendId hU (hatPow (marg θ hU) ((-a : ℝ) : ℂ))) *ᵥ θ) :
            EuclideanSpace ℂ (Reg loc Λ))‖ ∧
    (tauU θ hU X τ a u).PosDef ∧ (tauU θ hU X τ a u).trace = τ.trace

/-- D5.10.1. Right boundary: `‖G(1+iu)‖ ≤ ‖σ_u^{[a]} ρ̂_P^{-a} θ_u‖`, `σ_u ≥ 0`,
`Tr σ_u = Tr σ`, `θ_u` is a unit vector with the `P`-marginal of `θ`. -/
def Step_5_10_1 : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ P X U : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ),
    Disjoint P X → Disjoint P U → Disjoint X U →
  ∀ (θ : Reg loc Λ → ℂ), star θ ⬝ᵥ θ = 1 → ∀ (a : ℝ)
    (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
    (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ), 0 < a → σ'.PosSemidef → τ.PosDef →
  ∀ u : ℝ,
    ‖Gfun θ hP hX hU σ' τ a (1 + u * I)‖ ≤
      ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hP) (bracketPow (sigmaU θ hP X σ' a u) a) *
          extendId hP (hatPow (marg θ hP) ((-a : ℝ) : ℂ))) *ᵥ thetaU θ hX hU τ a u) :
            EuclideanSpace ℂ (Reg loc Λ))‖ ∧
    (sigmaU θ hP X σ' a u).PosSemidef ∧ (sigmaU θ hP X σ' a u).trace = σ'.trace ∧
    star (thetaU θ hX hU τ a u) ⬝ᵥ thetaU θ hX hU τ a u = 1 ∧
    marg (thetaU θ hX hU τ a u) hP = marg θ hP

/-- D5.10.3 (Lemma 2.1 with `D = X`, `E = P`, and D2.5). For unit `θ, θ'` and disjoint `X, P`:
`|S(X|P)_{θ'} − S(X|P)_θ| ≤ 4 √‖θ' − θ‖ ℓ`, `ℓ = log(e dim X)`. -/
def Step_5_10_3 : Prop :=
  ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] (Λ X P : Finset σ) (hX : X ⊆ Λ) (hP : P ⊆ Λ), Disjoint X P →
  ∀ (θ θ' : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1) (hθ' : star θ' ⬝ᵥ θ' = 1),
    |condEntropy (pureState θ' hθ').toSubState hX hP -
        condEntropy (pureState θ hθ).toSubState hX hP|
      ≤ 4 * √‖(WithLp.toLp 2 (θ' - θ) : EuclideanSpace ℂ (Reg loc Λ))‖ *
        ℓ (Fintype.card (Reg loc X))

/-- D5.5.2. **Lemma 5.1** for faithful `τ` (`Lemma_5_1` with `τ > 0`). -/
def Lemma_5_1_faithful : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (σ : Type u) [DecidableEq σ] (loc : σ → Type v) [∀ i, Fintype (loc i)]
      [∀ i, DecidableEq (loc i)] (Λ P X U F : Finset σ) (hP : P ⊆ Λ) (hX : X ⊆ Λ) (hU : U ⊆ Λ)
      (hF : F ⊆ Λ), Λ = P ∪ X ∪ U ∪ F → Disjoint P X → Disjoint P U → Disjoint P F →
      Disjoint X U → Disjoint X F → Disjoint U F →
    ∀ (θ : Reg loc Λ → ℂ) (hθ : star θ ⬝ᵥ θ = 1) (a : ℝ),
      0 < a * ℓ (Fintype.card (Reg loc X)) → a * ℓ (Fintype.card (Reg loc X)) ≤ c →
    ∀ (σ' : Matrix (Reg loc (X ∪ P)) (Reg loc (X ∪ P)) ℂ)
      (τ : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ),
      σ'.PosSemidef → σ'.trace.re ≤ 1 → τ.PosDef → τ.trace.re ≤ 1 →
      ‖(WithLp.toLp 2 ((extendId (Finset.union_subset hX hP) (bracketPow σ' (a / 2 : ℝ)) *
          extendId hP (hatPow (marg θ hP) (-(a / 2 : ℝ))) *
          extendId (Finset.union_subset hX hU) (bracketPow τ (a / 2 : ℝ)) *
          extendId hU (hatPow (marg θ hU) (-(a / 2 : ℝ)))) *ᵥ θ) :
            EuclideanSpace ℂ (Reg loc Λ))‖ ≤
        Real.exp (-(a / 2) * condMutualInfo (pureState θ hθ).toSubState hX hU hF +
          C * a ^ (5 / 4 : ℝ) * ℓ (Fintype.card (Reg loc X)) ^ 2)

end AreaLaw
