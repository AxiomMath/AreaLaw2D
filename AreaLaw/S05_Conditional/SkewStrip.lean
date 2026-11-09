import AreaLaw.S05_Conditional.Spectral
import AreaLaw.S05_Conditional.Interfaces

/-!
# D5.16 The strip bounds of the function `f` of Lemma 5.3

For `f(z) = ⟨θ, ρ_P^{[z]} ρ_Y^{[-z]} h ρ_P^{[-z]} ρ_Y^{[z]} θ⟩` (`Conditional.f`, D5.15):
`f` is entire, `f(-z̄) = conj f(z)` (D5.16.4), `0 ≤ f(iu) ≤ 1` (D5.16.5), `|f| ≤ d_h²` on
`|Re z| ≤ 1/4` (D5.16.1–3) and `f(0) = ⟨θ, hθ⟩`.
-/

namespace AreaLaw

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder

namespace Conditional

section Core

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cauchy–Schwarz: `|⟨u, v⟩| ≤ 1` when `⟨u, u⟩ ≤ 1` and `⟨v, v⟩ ≤ 1`. -/
theorem norm_star_dotProduct_le_one {u v : n → ℂ} (hu : (star u ⬝ᵥ u).re ≤ 1)
    (hv : (star v ⬝ᵥ v).re ≤ 1) : ‖star u ⬝ᵥ v‖ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ n) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
  have h1 := norm_toLp_sq u
  have h2 := norm_toLp_sq v
  have := norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ n)
  have := norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ n)
  exact h.trans (mul_le_one₀ (by nlinarith) (norm_nonneg _) (by nlinarith))

omit [DecidableEq n] in
/-- `⟨u, M v⟩ = ⟨Mᴴ u, v⟩`. -/
theorem star_dotProduct_mulVec (M : Matrix n n ℂ) (u v : n → ℂ) :
    star u ⬝ᵥ (M *ᵥ v) = star (Mᴴ *ᵥ u) ⬝ᵥ v := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

/-- `|t^{[z]}|² |t'^{[-z]}|² t' ≤ 2s t + (1 - 2s) t'` for `t, t' ≥ 0`, `s = Re z ∈ [0, 1/2]`
(weighted AM–GM). -/
theorem normSq_bfun_mul_le {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1 / 2) {t t' : ℝ}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    Complex.normSq (bfun z t) * Complex.normSq (bfun (-z) t') * t' ≤
      2 * z.re * t + (1 - 2 * z.re) * t' := by
  have h0 : 0 ≤ 2 * z.re * t + (1 - 2 * z.re) * t' :=
    add_nonneg (mul_nonneg (by linarith) ht) (mul_nonneg (by linarith) ht')
  unfold bfun
  split_ifs with h1 h2 h2
  · have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 2 * z.re) (w₂ := 1 - 2 * z.re)
      (by linarith) (by linarith) ht ht' (by ring)
    rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2] at this
    refine le_of_eq_of_le ?_ this
    simp only [Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, mul_zero, sub_zero]
    rw [← Real.exp_log h2]
    rw [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    push_cast; ring
  all_goals simpa using h0

/-- D5.16.3, the Hölder step. For `ρ ≥ 0`, `Tr ρ ≤ 1`, a contraction `c` (`cc*, c*c ≤ 1`) and
`0 ≤ Re z ≤ 1/2`: `Re Tr((ρ^{[z]} c ρ^{[-z]})* (ρ^{[z]} c ρ^{[-z]}) ρ) ≤ 1`. -/
theorem re_trace_sandwich_le {ρ c : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hc₁ : c * cᴴ ≤ 1) (hc₂ : cᴴ * c ≤ 1) {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1 / 2) :
    ((bracketPow ρ z * c * bracketPow ρ (-z))ᴴ * (bracketPow ρ z * c * bracketPow ρ (-z)) *
      ρ).trace.re ≤ 1 := by
  set hH := hρ.isHermitian
  set U : Matrix n n ℂ := ↑hH.eigenvectorUnitary
  have re_apply_le_one : ∀ {M : Matrix n n ℂ}, M ≤ 1 → ∀ j, (M j j).re ≤ 1 := fun hM j ↦ by
    have := (le_iff.1 hM).diag_nonneg (i := j)
    rw [Matrix.sub_apply, one_apply_eq, Complex.nonneg_iff, Complex.sub_re, Complex.one_re] at this
    linarith [this.1]
  set a := hH.eigenvalues
  have ha : ∀ k, 0 ≤ a k := hρ.eigenvalues_nonneg
  have hU₁ : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU : ∀ X : Matrix n n ℂ, star U * (U * X) = X := fun X ↦ by
    rw [← Matrix.mul_assoc, hU₁, Matrix.one_mul]
  have hUU' : ∀ X : Matrix n n ℂ, U * (star U * X) = X := fun X ↦ by
    rw [← Matrix.mul_assoc, show U * star U = 1 from Unitary.coe_mul_star_self _, Matrix.one_mul]
  have hUs : Uᴴ = star U := rfl
  have hUs' : (star U)ᴴ = U := by rw [← star_eq_conjTranspose, star_star]
  set c' := star U * c * U
  set N := diagonal (fun i ↦ bfun z (a i)) * c' * diagonal (fun i ↦ bfun (-z) (a i))
  have hT : bracketPow ρ z * c * bracketPow ρ (-z) = U * N * star U := by
    rw [bracketPow_eq hH, bracketPow_eq hH]
    simp only [specFun, N, c', Matrix.mul_assoc]
    rfl
  have hρU : ρ = U * diagonal (fun i ↦ (a i : ℂ)) * star U := (specFun_ofReal hH).symm
  have hconj : ∀ {M : Matrix n n ℂ}, M ≤ 1 → star U * M * U ≤ 1 := fun {M} hM ↦ by
    have := (le_iff.1 hM).conjTranspose_mul_mul_same U
    rwa [hUs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU₁, ← le_iff] at this
  -- rows and columns of `c'` have squared norm `≤ 1`
  have hrow : ∀ j, ∑ k, Complex.normSq (c' j k) ≤ 1 := fun j ↦ by
    have h := re_apply_le_one (hconj hc₁) j
    rw [show star U * (c * cᴴ) * U = c' * c'ᴴ by
      simp only [c', conjTranspose_mul, hUs, hUs', Matrix.mul_assoc, hUU']] at h
    simpa [mul_apply, Complex.normSq_apply, Complex.mul_re] using h
  have hcol : ∀ k, ∑ j, Complex.normSq (c' j k) ≤ 1 := fun k ↦ by
    have h := re_apply_le_one (hconj hc₂) k
    rw [show star U * (cᴴ * c) * U = c'ᴴ * c' by
      simp only [c', conjTranspose_mul, hUs, hUs', Matrix.mul_assoc, hUU']] at h
    simpa [mul_apply, Complex.normSq_apply, Complex.mul_re, mul_comm] using h
  have htrA : ∑ k, a k ≤ 1 := by
    rw [hH.trace_eq_sum_eigenvalues] at htr
    simpa using htr
  have htrace : ((U * N * star U)ᴴ * (U * N * star U) * ρ).trace =
      (Nᴴ * N * diagonal (fun i ↦ (a i : ℂ))).trace := by
    rw [hρU, conjTranspose_mul, conjTranspose_mul, hUs', hUs]
    simp only [Matrix.mul_assoc, hUU]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc, hU₁, Matrix.mul_one]
  have hN : ∀ j k, N j k = bfun z (a j) * c' j k * bfun (-z) (a k) := fun j k ↦ by
    simp [N, mul_diagonal, diagonal_mul]
  have hterm : ∀ (x : ℂ) (r : ℝ), (star x * x * r).re = Complex.normSq x * r := fun x r ↦ by
    simp [Complex.mul_re, Complex.normSq_apply]
  rw [hT, htrace]
  set s := z.re
  calc (Nᴴ * N * diagonal (fun i ↦ (a i : ℂ))).trace.re
      = ∑ j, ∑ k, Complex.normSq (c' j k) *
          (Complex.normSq (bfun z (a j)) * Complex.normSq (bfun (-z) (a k)) * a k) := by
        simp only [trace, diag, mul_diagonal]
        simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, Complex.re_sum, hterm, hN,
          Complex.normSq_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ ∑ j, ∑ k, Complex.normSq (c' j k) * (2 * s * a j + (1 - 2 * s) * a k) := by
        gcongr with j _ k _
        · exact Complex.normSq_nonneg _
        · exact normSq_bfun_mul_le hz₀ hz₁ (ha j) (ha k)
    _ = 2 * s * ∑ j, a j * ∑ k, Complex.normSq (c' j k) +
          (1 - 2 * s) * ∑ k, a k * ∑ j, Complex.normSq (c' j k) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ 2 * s * ∑ j, a j * 1 + (1 - 2 * s) * ∑ k, a k * 1 := by
        apply add_le_add <;> refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left ?_ (ha j)) (by linarith)
        exacts [hrow j, hcol j]
    _ ≤ 1 := by
        have : 2 * s * ∑ j, a j * 1 + (1 - 2 * s) * ∑ k, a k * 1 = ∑ k, a k := by
          simp only [mul_one]; ring
        linarith

omit [Fintype n] in
/-- For `0 ≤ h ≤ 1`: `|h_{ij}| ≤ 1`. -/
theorem norm_apply_le_one [Finite n] {h : Matrix n n ℂ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i j : n) :
    ‖h i j‖ ≤ 1 := by
  have := Fintype.ofFinite n
  set B := CFC.sqrt h
  have hB : Bᴴ = B := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have hBB : B * B = h := CFC.sqrt_mul_sqrt_self h hh0
  set u : n → n → ℂ := fun k m ↦ B m k
  have hu : ∀ k l, h k l = star (u k) ⬝ᵥ u l := fun k l ↦ by
    rw [← hBB, mul_apply]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    change B k m * B m l = star (B m k) * B m l
    rw [← conjTranspose_apply, hB]
  have hdiag : ∀ k, (star (u k) ⬝ᵥ u k).re ≤ 1 := fun k ↦ by
    have := (le_iff.1 hh1).diag_nonneg (i := k)
    rw [Matrix.sub_apply, one_apply_eq, Complex.nonneg_iff, Complex.sub_re, Complex.one_re,
      hu] at this
    linarith [this.1]
  rw [hu]
  exact norm_star_dotProduct_le_one (hdiag i) (hdiag j)

end Core

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ : Finset σ}

/-- `(M ⊗ N) ⊗ 1 = (M ⊗ 1)(N ⊗ 1)` for disjoint `S, T ⊆ Λ`. -/
theorem extendId_kronUnion {S T : Finset σ} (hS : S ⊆ Λ) (hT : T ⊆ Λ) (hd : Disjoint S T)
    (M : Matrix (Reg loc S) (Reg loc S) ℂ) (N : Matrix (Reg loc T) (Reg loc T) ℂ) :
    extendId (Finset.union_subset hS hT) (kronUnion hd M N) = extendId hS M * extendId hT N := by
  ext w w'
  rw [extendId_mul_extendId_apply hS hT hd]
  simp only [extendId, kronUnion, of_apply, unionEquiv_apply]
  have : restr (S := Λ \ (S ∪ T)) Finset.sdiff_subset w =
      restr (S := Λ \ (S ∪ T)) Finset.sdiff_subset w' ↔
        ∀ i : Λ, i.1 ∉ S → i.1 ∉ T → w i = w' i := by
    refine ⟨fun h i hS hT ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩
    · exact congrFun h ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, by simp [hS, hT]⟩⟩
    · have := (Finset.mem_sdiff.1 i.2).2
      exact h ⟨i.1, Finset.sdiff_subset i.2⟩ (fun h' ↦ this (Finset.mem_union_left _ h'))
        (fun h' ↦ this (Finset.mem_union_right _ h'))
  simp only [this]
  rfl

omit [∀ i, Fintype (loc i)] in
/-- A matrix unit on `S ⊔ T` is a product of matrix units: `|i⟩⟨j| = |i_S⟩⟨j_S| ⊗ |i_T⟩⟨j_T|`. -/
theorem single_eq_kronUnion {S T : Finset σ} (hd : Disjoint S T) (i j : Reg loc (S ∪ T)) :
    single i j (1 : ℂ) = kronUnion hd (single (unionEquiv hd i).1 (unionEquiv hd j).1 1)
      (single (unionEquiv hd i).2 (unionEquiv hd j).2 1) := by
  have key : ∀ u v : Reg loc (S ∪ T), u = v ↔
      (unionEquiv hd u).1 = (unionEquiv hd v).1 ∧ (unionEquiv hd u).2 = (unionEquiv hd v).2 :=
    fun u v ↦ by rw [← Prod.ext_iff, (unionEquiv hd).apply_eq_iff_eq]
  ext w w'
  simp only [kronUnion, of_apply, single_apply, key i w, key j w']
  split_ifs <;> simp_all

/-- `c = |a⟩⟨b| ⊗ 1` is a contraction: `cc* ≤ 1` and `c*c ≤ 1`. -/
theorem extendId_single_contraction {S : Finset σ} (hS : S ⊆ Λ) (a b : Reg loc S) :
    extendId hS (single a b (1 : ℂ)) * (extendId hS (single a b 1))ᴴ ≤ 1 ∧
      (extendId hS (single a b (1 : ℂ)))ᴴ * extendId hS (single a b 1) ≤ 1 := by
  have aux : ∀ a b : Reg loc S,
      extendId hS (single a b (1 : ℂ)) * extendId hS (single b a 1) ≤ 1 := fun a b ↦ by
    rw [← extendId_mul, single_mul_single_same, mul_one, le_iff,
      show (1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) - extendId hS (single a a 1) =
        extendId hS (1 - single a a 1) by
        rw [eq_comm, eq_sub_iff_add_eq, ← extendId_add, sub_add_cancel, extendId_one]]
    refine posSemidef_extendId hS ?_
    rw [show (1 : Matrix (Reg loc S) (Reg loc S) ℂ) - single a a 1 =
        diagonal (fun k ↦ if k = a then 0 else 1) by
      ext i j
      by_cases hij : i = j <;> by_cases hi : i = a <;>
        simp [hij, hi, single_apply, one_apply] <;> aesop]
    exact PosSemidef.diagonal fun k ↦ by dsimp; split_ifs <;> norm_num
  simp only [← extendId_conjTranspose, conjTranspose_single, star_one]
  exact ⟨aux a b, aux b a⟩

/-- Operators on disjoint regions commute. -/
theorem extendId_mul_comm {P Y : Finset σ} (hP : P ⊆ Λ) (hY : Y ⊆ Λ) (hd : Disjoint P Y)
    (x : Matrix (Reg loc P) (Reg loc P) ℂ) (y : Matrix (Reg loc Y) (Reg loc Y) ℂ) :
    extendId hP x * extendId hY y = extendId hY y * extendId hP x :=
  (commute_extendId_extendId hP hY hd x y).eq

/-- D5.16.2. `P`- and `Y`-factors commute across: `a₁ b₁ (c d) a₂ b₂ = (a₁ c a₂)(b₁ d b₂)`. -/
theorem mul_rearrange {P Y : Finset σ} (hP : P ⊆ Λ) (hY : Y ⊆ Λ) (hd : Disjoint P Y)
    (a₁ c a₂ : Matrix (Reg loc P) (Reg loc P) ℂ) (b₁ d b₂ : Matrix (Reg loc Y) (Reg loc Y) ℂ) :
    extendId hP a₁ * extendId hY b₁ * (extendId hP c * extendId hY d) * extendId hP a₂ *
      extendId hY b₂ = extendId hP (a₁ * c * a₂) * extendId hY (b₁ * d * b₂) := by
  have e₁ : ∀ (x : Matrix (Reg loc P) (Reg loc P) ℂ) (y : Matrix (Reg loc Y) (Reg loc Y) ℂ),
      extendId hY y * extendId hP x = extendId hP x * extendId hY y :=
    fun x y ↦ (extendId_mul_comm hP hY hd x y).symm
  have e₂ : ∀ (x : Matrix (Reg loc P) (Reg loc P) ℂ) (y : Matrix (Reg loc Y) (Reg loc Y) ℂ)
      (Z : Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
      extendId hY y * (extendId hP x * Z) = extendId hP x * (extendId hY y * Z) :=
    fun x y Z ↦ by rw [← Matrix.mul_assoc, e₁, Matrix.mul_assoc]
  simp only [extendId_mul, Matrix.mul_assoc, e₁, e₂]

/-- D5.16.3. A single term: for contractions `c` on `P`, `d` on `Y` (disjoint) and
`0 ≤ Re z ≤ 1/2`, `|⟨θ, (ρ_P^{[z]} c ρ_P^{[-z]})(ρ_Y^{[-z]} d ρ_Y^{[z]}) θ⟩| ≤ 1`. -/
theorem norm_term_le {P Y : Finset σ} (hP : P ⊆ Λ) (hY : Y ⊆ Λ) (hd : Disjoint P Y)
    {θ : Reg loc Λ → ℂ} (hθ : star θ ⬝ᵥ θ = 1) {c : Matrix (Reg loc P) (Reg loc P) ℂ}
    (hc₁ : c * cᴴ ≤ 1) (hc₂ : cᴴ * c ≤ 1) {d : Matrix (Reg loc Y) (Reg loc Y) ℂ}
    (hd₁ : d * dᴴ ≤ 1) (hd₂ : dᴴ * d ≤ 1) {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1 / 2) :
    ‖star θ ⬝ᵥ ((extendId hP (bracketPow (marg θ hP) z * c * bracketPow (marg θ hP) (-z)) *
      extendId hY (bracketPow (marg θ hY) (-z) * d * bracketPow (marg θ hY) z)) *ᵥ θ)‖ ≤ 1 := by
  have htr : ∀ {D} (hD : D ⊆ Λ), (marg θ hD).trace.re ≤ 1 := fun hD ↦ by
    rw [trace_marg, hθ, Complex.one_re]
  have hB : (bracketPow (marg θ hY) (-z) * d * bracketPow (marg θ hY) z)ᴴ =
      bracketPow (marg θ hY) (starRingEnd ℂ z) * dᴴ *
        bracketPow (marg θ hY) (-starRingEnd ℂ z) := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_bracketPow, conjTranspose_bracketPow,
      map_neg, Matrix.mul_assoc]
  rw [extendId_mul_comm hP hY hd, ← mulVec_mulVec, star_dotProduct_mulVec,
    ← extendId_conjTranspose, hB]
  refine norm_star_dotProduct_le_one ?_ ?_
  · rw [step_5_1_F1]
    exact re_trace_sandwich_le (posSemidef_marg θ hY) (htr hY)
      (by rwa [conjTranspose_conjTranspose]) (by rwa [conjTranspose_conjTranspose])
      (by simpa using hz₀) (by simpa using hz₁)
  · rw [step_5_1_F1]
    exact re_trace_sandwich_le (posSemidef_marg θ hP) (htr hP) hc₁ hc₂ hz₀ hz₁

/-- D5.16.1. Matrix units on `P₀ ⊔ X`: `h ⊗ 1 = ∑_{ij} h_{ij} (c_{ij} ⊗ 1)(d_{ij} ⊗ 1)` with
`c_{ij} = |i_{P₀}⟩⟨j_{P₀}| ⊗ 1_{P₁}` on `P` and `d_{ij} = |i_X⟩⟨j_X| ⊗ 1_U` on `Y`. -/
theorem extendId_eq_sum {P₀ P₁ X U : Finset σ} (hP : P₀ ∪ P₁ ⊆ Λ) (hY : X ∪ U ⊆ Λ)
    (hPX : P₀ ∪ X ⊆ Λ) (hd : Disjoint P₀ X) (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ) :
    extendId hPX h = ∑ i, ∑ j, h i j •
      (extendId hP (extendId Finset.subset_union_left
          (single (unionEquiv hd i).1 (unionEquiv hd j).1 (1 : ℂ))) *
        extendId hY (extendId Finset.subset_union_left
          (single (unionEquiv hd i).2 (unionEquiv hd j).2 (1 : ℂ)))) := by
  have hadd : ∀ (s : Finset (Reg loc (P₀ ∪ X)))
      (g : Reg loc (P₀ ∪ X) → Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ),
      extendId hPX (∑ i ∈ s, g i) = ∑ i ∈ s, extendId hPX (g i) := fun s g ↦
    map_sum (AddMonoidHom.mk' (extendId hPX) (extendId_add hPX)) g s
  conv_lhs => rw [matrix_eq_sum_single h]
  rw [hadd]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hadd]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show single i j (h i j) = h i j • single i j 1 by rw [smul_single, smul_eq_mul, mul_one],
    extendId_smul, single_eq_kronUnion hd,
    extendId_kronUnion (Finset.subset_union_left.trans hP) (Finset.subset_union_left.trans hY) hd,
    Arealaw.extendId_extendId Finset.subset_union_left hP,
    Arealaw.extendId_extendId Finset.subset_union_left hY]

variable {P₀ P₁ X U : Finset σ} (hP : P₀ ∪ P₁ ⊆ Λ) (hY : X ∪ U ⊆ Λ) (hPX : P₀ ∪ X ⊆ Λ)
  (θ : Reg loc Λ → ℂ) (h : Matrix (Reg loc (P₀ ∪ X)) (Reg loc (P₀ ∪ X)) ℂ)

/-- D5.15. `f` is entire: finite sums and products of entire matrix entries. -/
theorem differentiable_f : Differentiable ℂ (f hP hY hPX θ h) := by
  have hE : ∀ {D : Finset σ} (hD : D ⊆ Λ) (ρ : Matrix (Reg loc D) (Reg loc D) ℂ) (g : ℂ → ℂ),
      Differentiable ℂ g → ∀ w w', Differentiable ℂ fun z ↦ extendId hD (bracketPow ρ (g z)) w w' :=
    fun hD ρ g hg w w' ↦ by
      simp only [extendId, of_apply]
      split_ifs
      · exact (differentiable_bracketPow_apply ρ _ _).comp hg
      · exact differentiable_const _
  have hmul : ∀ (M N : ℂ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
      (∀ i j, Differentiable ℂ fun z ↦ M z i j) → (∀ i j, Differentiable ℂ fun z ↦ N z i j) →
        ∀ i j, Differentiable ℂ fun z ↦ (M z * N z) i j := fun M N hM hN i j ↦ by
    simp only [mul_apply]
    exact Differentiable.fun_sum fun k _ ↦ (hM i k).mul (hN k j)
  have hM : ∀ i j, Differentiable ℂ fun z ↦ (extendId hP (bracketPow (marg θ hP) z) *
      extendId hY (bracketPow (marg θ hY) (-z)) * extendId hPX h *
      extendId hP (bracketPow (marg θ hP) (-z)) * extendId hY (bracketPow (marg θ hY) z)) i j := by
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_
    exacts [hE hP _ _ differentiable_id, hE hY _ _ differentiable_neg,
      fun _ _ ↦ differentiable_const _, hE hP _ _ differentiable_neg, hE hY _ _ differentiable_id]
  unfold f
  simp only [dotProduct, mulVec]
  exact Differentiable.fun_sum fun i _ ↦ (differentiable_const _).mul
    (Differentiable.fun_sum fun j _ ↦ (hM i j).mul (differentiable_const _))

/-- D5.16.4. Reflection: `f(-z̄) = conj f(z)` for Hermitian `h`. -/
theorem f_neg_conj (hd : Disjoint (P₀ ∪ P₁) (X ∪ U)) (hh : h.IsHermitian) (z : ℂ) :
    f hP hY hPX θ h (-(starRingEnd ℂ z)) = starRingEnd ℂ (f hP hY hPX θ h z) := by
  have key : ∀ M : Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
      starRingEnd ℂ (star θ ⬝ᵥ (M *ᵥ θ)) = star θ ⬝ᵥ (Mᴴ *ᵥ θ) := fun M ↦ by
    rw [star_dotProduct_mulVec, ← Complex.star_def, star_dotProduct θ]
  -- D5.16.4: the adjoint of the operator in `f`, `h = h*`, `(ρ^{[z]})* = ρ^{[z̄]}`
  unfold f
  rw [key]
  simp only [conjTranspose_mul, ← extendId_conjTranspose, conjTranspose_bracketPow, hh.eq,
    map_neg, neg_neg, Matrix.mul_assoc]
  -- D5.16.4: `P`- and `Y`-factors commute
  rw [extendId_mul_comm hP hY hd (bracketPow _ (starRingEnd ℂ z)), ← Matrix.mul_assoc,
    extendId_mul_comm hP hY hd, Matrix.mul_assoc]

/-- D5.16.5, the sandwich: `⟨θ, A* B* H A B θ⟩ = ⟨v, H v⟩` with `v = A B θ`. -/
theorem dotProduct_sandwich (hd : Disjoint (P₀ ∪ P₁) (X ∪ U))
    (A : Matrix (Reg loc (P₀ ∪ P₁)) (Reg loc (P₀ ∪ P₁)) ℂ) (B : Matrix (Reg loc (X ∪ U))
      (Reg loc (X ∪ U)) ℂ) (H : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    star θ ⬝ᵥ ((extendId hP Aᴴ * extendId hY Bᴴ * H * extendId hP A * extendId hY B) *ᵥ θ) =
      star (extendId hP A *ᵥ (extendId hY B *ᵥ θ)) ⬝ᵥ
        (H *ᵥ (extendId hP A *ᵥ (extendId hY B *ᵥ θ))) := by
  rw [mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    conjTranspose_mul, ← extendId_conjTranspose, ← extendId_conjTranspose,
    extendId_mul_comm hY hP hd.symm]
  simp only [Matrix.mul_assoc]

/-- D5.16.5. On the imaginary axis `f(iu) = ⟨Vθ, hVθ⟩` with `‖Vθ‖ = 1`, so `0 ≤ f(iu) ≤ 1`. -/
theorem f_mul_I (hd : Disjoint (P₀ ∪ P₁) (X ∪ U)) (hθ : star θ ⬝ᵥ θ = 1) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1) (t : ℝ) :
    (f hP hY hPX θ h (t * Complex.I)).im = 0 ∧ 0 ≤ (f hP hY hPX θ h (t * Complex.I)).re ∧
      (f hP hY hPX θ h (t * Complex.I)).re ≤ 1 := by
  set A := bracketPow (marg θ hP) (-(t * Complex.I)) with hAdef
  set B := bracketPow (marg θ hY) (t * Complex.I) with hBdef
  set v := extendId hP A *ᵥ (extendId hY B *ᵥ θ)
  have hc : starRingEnd ℂ (t * Complex.I) = -(t * Complex.I) := by simp
  have hA : Aᴴ = bracketPow (marg θ hP) (t * Complex.I) := by
    rw [conjTranspose_bracketPow, map_neg, hc, neg_neg]
  have hB : Bᴴ = bracketPow (marg θ hY) (-(t * Complex.I)) := by rw [conjTranspose_bracketPow, hc]
  -- D5.16.5: `f(iu) = ⟨Vθ, hVθ⟩`, `V = ρ_P^{[-iu]} ρ_Y^{[iu]}`
  have hf : f hP hY hPX θ h (t * Complex.I) = star v ⬝ᵥ (extendId hPX h *ᵥ v) := by
    rw [← dotProduct_sandwich hP hY θ hd, hA, hB]
    rfl
  -- D5.16.5: `‖Vθ‖² = ⟨θ, ρ_P^{[0]} ρ_Y^{[0]} θ⟩ = 1`
  have hv : star v ⬝ᵥ v = 1 := by
    have := dotProduct_sandwich hP hY θ hd A B (extendId hP 1 * extendId hY 1)
    rw [mul_rearrange hP hY hd, hA, hB] at this
    simp only [extendId_one, Matrix.mul_one, one_mulVec] at this
    rw [hAdef, hBdef, bracketPow_mul_bracketPow, bracketPow_mul_bracketPow, add_neg_cancel,
      neg_add_cancel, ← mulVec_mulVec, extendId_bracketPow_zero_marg_mulVec,
      extendId_bracketPow_zero_marg_mulVec, hθ] at this
    exact this.symm
  have hH0 := posSemidef_extendId hPX hh0.posSemidef
  have hH1 : (1 - extendId hPX h).PosSemidef := by
    rw [show 1 - extendId hPX h = extendId hPX (1 - h) by
      rw [eq_comm, eq_sub_iff_add_eq, ← extendId_add, sub_add_cancel, extendId_one]]
    exact posSemidef_extendId hPX (le_iff.1 hh1)
  have h0 := Complex.nonneg_iff.1 (hH0.dotProduct_mulVec_nonneg v)
  have h1 := Complex.nonneg_iff.1 (hH1.dotProduct_mulVec_nonneg v)
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hv, Complex.sub_re, Complex.one_re,
    sub_nonneg] at h1
  rw [hf]
  exact ⟨h0.2.symm, h0.1, h1.1⟩

/-- `f(0) = p = ⟨θ, hθ⟩`: the support projections act trivially on `θ`. -/
theorem f_zero : f hP hY hPX θ h 0 = star θ ⬝ᵥ (extendId hPX h *ᵥ θ) := by
  unfold f
  rw [neg_zero, ← mulVec_mulVec, extendId_bracketPow_zero_marg_mulVec, ← mulVec_mulVec,
    extendId_bracketPow_zero_marg_mulVec, ← mulVec_mulVec, star_dotProduct_mulVec,
    conjTranspose_mul, ← extendId_conjTranspose, ← extendId_conjTranspose,
    conjTranspose_bracketPow, conjTranspose_bracketPow, map_zero, ← mulVec_mulVec,
    extendId_bracketPow_zero_marg_mulVec, extendId_bracketPow_zero_marg_mulVec]

/-- D5.16.1–3. `|f(z)| ≤ d_h²` on `0 ≤ Re z ≤ 1/2`, `d_h = dim(P₀ X)`. -/
theorem norm_f_le (hd : Disjoint (P₀ ∪ P₁) (X ∪ U)) (hd₀ : Disjoint P₀ X)
    (hθ : star θ ⬝ᵥ θ = 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) {z : ℂ} (hz₀ : 0 ≤ z.re)
    (hz₁ : z.re ≤ 1 / 2) : ‖f hP hY hPX θ h z‖ ≤ (Fintype.card (Reg loc (P₀ ∪ X)) : ℝ) ^ 2 := by
  -- D5.16.1: decompose `h` in matrix units on `P₀ ⊔ X`
  have hsum : f hP hY hPX θ h z = ∑ i, ∑ j, h i j * star θ ⬝ᵥ
      ((extendId hP (bracketPow (marg θ hP) z * extendId Finset.subset_union_left
          (single (unionEquiv hd₀ i).1 (unionEquiv hd₀ j).1 (1 : ℂ)) *
          bracketPow (marg θ hP) (-z)) *
        extendId hY (bracketPow (marg θ hY) (-z) * extendId Finset.subset_union_left
          (single (unionEquiv hd₀ i).2 (unionEquiv hd₀ j).2 (1 : ℂ)) *
          bracketPow (marg θ hY) z)) *ᵥ θ) := by
    -- D5.16.2: `c`, `ρ_P^{[±z]}` act on `P`; `d'`, `ρ_Y^{[±z]}` on `Y`; commute across
    unfold f
    rw [extendId_eq_sum hP hY hPX hd₀]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, sum_mulVec,
      smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_rearrange hP hY hd]
  rw [hsum]
  -- D5.16.3: each term has modulus `≤ 1`
  calc ‖∑ i, ∑ j, _‖ ≤ ∑ _i : Reg loc (P₀ ∪ X), ∑ _j : Reg loc (P₀ ∪ X), (1 : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        rw [norm_mul, ← one_mul (1 : ℝ)]
        have hc := extendId_single_contraction (Finset.subset_union_left (s₂ := P₁))
          (unionEquiv hd₀ i).1 (unionEquiv hd₀ j).1
        have hd' := extendId_single_contraction (Finset.subset_union_left (s₂ := U))
          (unionEquiv hd₀ i).2 (unionEquiv hd₀ j).2
        exact mul_le_mul (norm_apply_le_one hh0 hh1 i j)
          (norm_term_le hP hY hd hθ hc.1 hc.2 hd'.1 hd'.2 hz₀ hz₁) (norm_nonneg _) zero_le_one
    _ = (Fintype.card (Reg loc (P₀ ∪ X)) : ℝ) ^ 2 := by simp [sq]

end Region

end Conditional

open Conditional in
/-- D5.16 (with D5.16.4–5 and `f(0) = p`). For the function `f` of **Lemma 5.3**: `f` is entire,
`f(-z̄) = conj f(z)`, `0 ≤ f(iu) ≤ 1`, `|f(z)| ≤ d_h²` on `|Re z| ≤ 1/4`, and
`f(0) = p = ⟨θ, hθ⟩`. -/
theorem step_5_16 : Step_5_16 := by
  intro σ _ loc _ _ Λ P₀ P₁ X U F hP₀ hP₁ hX hU _ _ _ hPX hPU _ _ _ _ θ hθ h hh0 hh1
  have hd : Disjoint (P₀ ∪ P₁) (X ∪ U) := Finset.disjoint_union_right.2 ⟨hPX, hPU⟩
  have hd₀ : Disjoint P₀ X := hPX.mono_left Finset.subset_union_left
  have hH : h.IsHermitian := hh0.posSemidef.isHermitian
  refine ⟨differentiable_f _ _ _ θ h, f_neg_conj _ _ _ θ h hd hH,
    f_mul_I _ _ _ θ h hd hθ hh0 hh1, fun z hz ↦ ?_, f_zero _ _ _ θ h⟩
  -- D5.16.3 on `0 ≤ Re z ≤ 1/4`, D5.16.4 for the negative side
  rcases le_total 0 z.re with h0 | h0
  · exact norm_f_le _ _ _ θ h hd hd₀ hθ hh0 hh1 h0 (by linarith [le_abs_self z.re])
  · have := f_neg_conj (Finset.union_subset hP₀ hP₁) (Finset.union_subset hX hU)
      (Finset.union_subset hP₀ hX) θ h hd hH (-(starRingEnd ℂ z))
    rw [map_neg, Complex.conj_conj, neg_neg] at this
    rw [this, Complex.norm_conj]
    exact norm_f_le _ _ _ θ h hd hd₀ hθ hh0 hh1 (by simp; linarith)
      (by simp; linarith [neg_abs_le z.re])

end AreaLaw
