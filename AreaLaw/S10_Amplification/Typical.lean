import AreaLaw.S10_Amplification.Setup
import AreaLaw.S03_InitialBox.MarginalTails

/-!
# §10 Typical projections (D10.5)

Digest `digest/10-amplification.md` (D10.5, and the spectral inequalities of D10.8.2),
paper `paper/sections/09-amplification.tex` lines 304–322. Graph-level (`Map.md`, Dimension):
a simple graph `G` on a site type `σ` with ball growth `V`.
-/

namespace AreaLaw

open Arealaw Matrix GraphDomain Finset Amplification
open OpenAI (pureState HasGlobalGap IsSupportedOn)
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Spectral projections of a Hermitian matrix -/

section SpecProj

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)

/-- `U diag(f) U*` in the eigenbasis `U` of `A`, for real `f`. -/
noncomputable def conjDiag (f : n → ℝ) : Matrix n n ℂ := -- helper
  (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j => (f j : ℂ)) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

theorem conjDiag_mul (f g : n → ℝ) :
    conjDiag hA f * conjDiag hA g = conjDiag hA (fun j => f j * g j) := by
  set U := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  calc conjDiag hA f * conjDiag hA g =
      U * diagonal (fun j => (f j : ℂ)) * (star U * U) * diagonal (fun j => (g j : ℂ)) *
        star U := by simp only [conjDiag, U, Matrix.mul_assoc]
    _ = _ := by
      rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
      simp [conjDiag, U]

theorem smul_conjDiag (c : ℝ) (f : n → ℝ) :
    (c : ℂ) • conjDiag hA f = conjDiag hA (fun j => c * f j) := by
  have h : diagonal (fun j => ((c * f j : ℝ) : ℂ)) = (c : ℂ) • diagonal (fun j => (f j : ℂ)) := by
    rw [← diagonal_smul]; congr 1; funext j; simp
  rw [conjDiag, conjDiag, h, Matrix.mul_smul, Matrix.smul_mul]

theorem conjDiag_le {f g : n → ℝ} (h : ∀ j, f j ≤ g j) : conjDiag hA f ≤ conjDiag hA g := by
  rw [Matrix.le_iff]
  have : conjDiag hA g - conjDiag hA f = conjDiag hA (fun j => g j - f j) := by
    simp only [conjDiag, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 3
    funext j
    simp
  rw [this]
  have := (posSemidef_diagonal_iff.2 fun j => (by exact_mod_cast sub_nonneg.2 (h j) :
    (0 : ℂ) ≤ ((g j - f j : ℝ) : ℂ))).mul_mul_conjTranspose_same
    (hA.eigenvectorUnitary : Matrix n n ℂ)
  simpa [conjDiag, star_eq_conjTranspose] using this

theorem eq_conjDiag : A = conjDiag hA hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

theorem specProj_eq_conjDiag (sel : Finset n) :
    specProj hA sel = conjDiag hA (fun j => if j ∈ sel then 1 else 0) := by
  simp only [specProj, conjDiag]
  congr 3
  funext j
  split_ifs <;> simp

theorem specProj_isHermitian (sel : Finset n) : (specProj hA sel).IsHermitian := by
  rw [specProj_eq_conjDiag, conjDiag, star_eq_conjTranspose]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_iff.2 fun j => Complex.conj_ofReal _)

theorem specProj_mul_self (sel : Finset n) :
    specProj hA sel * specProj hA sel = specProj hA sel := by
  rw [specProj_eq_conjDiag, conjDiag_mul]
  congr 1; funext j; split_ifs <;> simp

theorem specProj_mul (sel : Finset n) :
    specProj hA sel * A = conjDiag hA (fun j => if j ∈ sel then hA.eigenvalues j else 0) := by
  rw [show specProj hA sel * A = specProj hA sel * conjDiag hA hA.eigenvalues from
    congrArg _ (eq_conjDiag hA), specProj_eq_conjDiag, conjDiag_mul]
  congr 1; funext j; split_ifs <;> simp

theorem specProj_commute (sel : Finset n) : Commute (specProj hA sel) A := by
  have h : A * specProj hA sel =
      conjDiag hA (fun j => if j ∈ sel then hA.eigenvalues j else 0) := by
    rw [show A * specProj hA sel = conjDiag hA hA.eigenvalues * specProj hA sel from
      congrArg (· * _) (eq_conjDiag hA), specProj_eq_conjDiag, conjDiag_mul]
    congr 1; funext j; split_ifs <;> simp
  exact (specProj_mul hA sel).trans h.symm

/-- D10.8.2 shape: eigenvalues `≥ lo` on `sel` give `lo P ≤ P A`. -/
theorem specProj_smul_le_mul {sel : Finset n} {lo : ℝ} (h : ∀ j ∈ sel, lo ≤ hA.eigenvalues j) :
    (lo : ℂ) • specProj hA sel ≤ specProj hA sel * A := by
  rw [specProj_mul, specProj_eq_conjDiag, smul_conjDiag]
  refine conjDiag_le hA fun j => ?_
  split_ifs with hj
  · simpa using h j hj
  · simp

/-- D10.8.2 shape: eigenvalues `≤ hi` on `sel` give `P A P ≤ hi P`. -/
theorem specProj_mul_mul_le {sel : Finset n} {hi : ℝ} (h : ∀ j ∈ sel, hA.eigenvalues j ≤ hi) :
    specProj hA sel * A * specProj hA sel ≤ (hi : ℂ) • specProj hA sel := by
  rw [specProj_mul, specProj_eq_conjDiag, smul_conjDiag, conjDiag_mul]
  refine conjDiag_le hA fun j => ?_
  split_ifs with hj
  · simpa using h j hj
  · simp

/-- D10.8.2 shape: for `A ≥ 0` with eigenvalues `≥ lo > 0` on `sel`, `P ≤ lo⁻¹ A`. -/
theorem specProj_le_smul {sel : Finset n} {lo : ℝ} (hlo : 0 < lo)
    (h0 : ∀ j, 0 ≤ hA.eigenvalues j)
    (h : ∀ j ∈ sel, lo ≤ hA.eigenvalues j) :
    specProj hA sel ≤ ((lo⁻¹ : ℝ) : ℂ) • A := by
  conv_rhs => rw [eq_conjDiag hA]
  rw [specProj_eq_conjDiag, smul_conjDiag]
  refine conjDiag_le hA fun j => ?_
  split_ifs with hj
  · rw [le_inv_mul_iff₀ hlo, mul_one]; exact h j hj
  · exact mul_nonneg (inv_nonneg.2 hlo.le) (h0 j)

-- helper
theorem trace_conjDiag (f : n → ℝ) : (conjDiag hA f).trace = ∑ j, (f j : ℂ) := by
  rw [conjDiag, trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]

/-- The mass of the selected spectrum: `Tr(A P) = ∑_{j ∈ sel} λ_j`. -/
theorem trace_mul_specProj (sel : Finset n) :
    (A * specProj hA sel).trace = ∑ j ∈ sel, (hA.eigenvalues j : ℂ) := by
  rw [trace_mul_comm, specProj_mul, trace_conjDiag]
  calc _ = ∑ j, if j ∈ sel then (hA.eigenvalues j : ℂ) else 0 :=
        sum_congr rfl fun j _ => by split_ifs <;> simp
    _ = _ := by rw [sum_ite_mem, univ_inter]

end SpecProj

/-! ## D10.5 Typical projections -/

section Typical

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {Λ B : Finset σ}
  (Ω : Reg loc Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (hB : B ⊆ Λ)

/-- D10.5. The typical eigenvalue indices of `ρ_B`: `p > 0` with `-log p ∈ [S - w, S + w]`. -/
noncomputable def typicalSet (w : ℝ) : Finset (Reg loc B) :=
  univ.filter fun j => 0 < (marg Ω hΩ hB).psd.isHermitian.eigenvalues j ∧
    |-Real.log ((marg Ω hΩ hB).psd.isHermitian.eigenvalues j) - (marg Ω hΩ hB).entropy| ≤ w

/-- D10.5. The typical spectral projection of `ρ_B`. -/
noncomputable def typicalProj (w : ℝ) : Matrix (Reg loc B) (Reg loc B) ℂ :=
  specProj (marg Ω hΩ hB).psd.isHermitian (typicalSet Ω hΩ hB w)

omit [∀ i, Nonempty (loc i)] in
/-- D10.5.2. `‖(I - P_B) Ω‖² = ⟨Ω, (I - P_B) Ω⟩ = P{|K - S| > w}`, `K = -log p` the surprisal
with probability `p` (the eigenvalues of `ρ_B`). -/
theorem step_10_5_2 (w : ℝ) :
    vnorm ((1 - extendId hB (typicalProj Ω hΩ hB w)) *ᵥ Ω) ^ 2 =
      ∑ j ∈ univ.filter (fun j => 0 < (marg Ω hΩ hB).psd.isHermitian.eigenvalues j ∧
        w < |-Real.log ((marg Ω hΩ hB).psd.isHermitian.eigenvalues j) -
          (marg Ω hΩ hB).entropy|), (marg Ω hΩ hB).psd.isHermitian.eigenvalues j := by
  set hρ := (marg Ω hΩ hB).psd.isHermitian
  set p := hρ.eigenvalues
  set S := (marg Ω hΩ hB).entropy
  set P := typicalProj Ω hΩ hB w
  set Q := 1 - extendId hB P
  have hPh : Pᴴ = P := specProj_isHermitian hρ _
  have hQ : Qᴴ * Q = Q := by
    have hP2 : P * P = P := specProj_mul_self hρ _
    have hE : (extendId hB P)ᴴ = extendId hB P := by rw [← extendId_conjTranspose, hPh]
    have hE2 : extendId hB P * extendId hB P = extendId hB P := by rw [← extendId_mul, hP2]
    simp only [Q, conjTranspose_sub, conjTranspose_one, hE, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hE2]
    abel
  -- `‖Q Ω‖² = ⟨Ω, Q Ω⟩ = 1 - Tr(ρ_B P)`
  have h1 : star (Q *ᵥ Ω) ⬝ᵥ (Q *ᵥ Ω) = 1 - ((marg Ω hΩ hB).M * P).trace := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, hQ]
    simp only [Q, sub_mulVec, one_mulVec, dotProduct_sub, hΩ, dotProduct_extendId_mulVec]
    rw [show (marg Ω hΩ hB).M = ptrace hB (vecMulVec Ω (star Ω)) from rfl]
  have htr : (marg Ω hΩ hB).M.trace = 1 := ((pureState Ω hΩ).restrict hB).trace_eq_one
  rw [hρ.trace_eq_sum_eigenvalues] at htr
  have hs : ∑ j, p j = 1 := by
    have := congrArg Complex.re htr
    simpa [p, Complex.re_sum] using this
  rw [vnorm_sq, h1, show P = specProj hρ (typicalSet Ω hΩ hB w) from rfl,
    trace_mul_specProj]
  simp only [Complex.sub_re, Complex.one_re, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [← hs, typicalSet, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hp : 0 ≤ p j := (marg Ω hΩ hB).psd.eigenvalues_nonneg j
  by_cases h0 : 0 < p j
  · by_cases hw : |-Real.log (p j) - S| ≤ w
    · rw [if_pos ⟨h0, hw⟩, if_neg fun h => not_lt.2 hw h.2, sub_self]
    · rw [if_neg fun h => hw h.2, if_pos ⟨h0, not_le.1 hw⟩, sub_zero]
  · rw [if_neg fun h => h0 h.1, if_neg fun h => h0 h.1, le_antisymm (not_lt.1 h0) hp, sub_zero]

omit [∀ i, Nonempty (loc i)] in
/-- D10.5.4, D10.8.2. Typical eigenvalues are positive with
`e^{-(S+w)} ≤ p ≤ e^{-S+w}`; hence `P ≤ e^{S+w} ρ_B`, `P ρ_B P ≤ e^{-S+w} P`, `P` commutes with
`ρ_B`, and `P` is an orthogonal projection. Only `p > 0` is ever inverted. -/
theorem step_10_5_4 (w : ℝ) :
    (∀ j ∈ typicalSet Ω hΩ hB w, 0 < (marg Ω hΩ hB).psd.isHermitian.eigenvalues j ∧
      Real.exp (-((marg Ω hΩ hB).entropy + w)) ≤ (marg Ω hΩ hB).psd.isHermitian.eigenvalues j ∧
      (marg Ω hΩ hB).psd.isHermitian.eigenvalues j ≤ Real.exp (-(marg Ω hΩ hB).entropy + w)) ∧
    typicalProj Ω hΩ hB w ≤ (Real.exp ((marg Ω hΩ hB).entropy + w) : ℂ) • (marg Ω hΩ hB).M ∧
    typicalProj Ω hΩ hB w * (marg Ω hΩ hB).M * typicalProj Ω hΩ hB w ≤
      (Real.exp (-(marg Ω hΩ hB).entropy + w) : ℂ) • typicalProj Ω hΩ hB w ∧
    Commute (typicalProj Ω hΩ hB w) (marg Ω hΩ hB).M ∧
    (typicalProj Ω hΩ hB w)ᴴ = typicalProj Ω hΩ hB w ∧
    typicalProj Ω hΩ hB w * typicalProj Ω hΩ hB w = typicalProj Ω hΩ hB w := by
  set hρ := (marg Ω hΩ hB).psd.isHermitian
  set S := (marg Ω hΩ hB).entropy
  have hmem : ∀ j ∈ typicalSet Ω hΩ hB w, 0 < hρ.eigenvalues j ∧
      Real.exp (-(S + w)) ≤ hρ.eigenvalues j ∧ hρ.eigenvalues j ≤ Real.exp (-S + w) := by
    intro j hj
    obtain ⟨hp, hw⟩ := (mem_filter.1 hj).2
    have hl := Real.exp_log hp
    obtain ⟨h1, h2⟩ := abs_le.1 hw
    exact ⟨hp, by rw [← hl]; exact Real.exp_le_exp.2 (by linarith),
      by rw [← hl]; exact Real.exp_le_exp.2 (by linarith)⟩
  refine ⟨hmem, ?_, specProj_mul_mul_le hρ fun j hj => (hmem j hj).2.2,
    specProj_commute hρ _, specProj_isHermitian hρ _, specProj_mul_self hρ _⟩
  have := specProj_le_smul hρ (Real.exp_pos (-(S + w)))
    (marg Ω hΩ hB).psd.eigenvalues_nonneg fun j hj => (hmem j hj).2.1
  rwa [← Real.exp_neg, neg_neg] at this

/-! ### The tail bound D10.5.1–D10.5.3 -/

omit [∀ i, DecidableEq (loc i)] in
/-- D10.5.1 (D2.8, D2.9, D3.2 on a graph). Each support `X` has `log² (e d_X) ≤ (1 + V_R log q)²`
and at most `2 V_R μ_R |∂_Λ B|` supports are split by `B`, so
`𝓑 ≤ 1 + 2 V_R μ_R (1 + V_R log q)² |∂_Λ B|`. -/
theorem step_10_5_1 (G : SimpleGraph σ) [DecidableRel G.Adj] (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {q : ℕ} (hq : ∀ i, Fintype.card (loc i) ≤ q) (Λ B : Finset σ) (R : ℕ) :
    1 + ∑ X ∈ supports G Λ R with (X ∩ B).Nonempty ∧ (X \ B).Nonempty,
        Real.log (Real.exp 1 * Fintype.card (Reg loc X)) ^ 2 ≤
      1 + 2 * V R * μ V R * (1 + V R * Real.log q) ^ 2 * #(edgeBoundary G Λ B) := by
  -- D10.5.1: `log² (e d_X) ≤ log² (e q^{V_R})` (D2.8)
  have hlog : ∀ X ∈ supports G Λ R,
      Real.log (Real.exp 1 * Fintype.card (Reg loc X)) ^ 2 ≤ (1 + V R * Real.log q) ^ 2 := by
    intro X hX
    obtain ⟨-, ⟨x, hx⟩, -⟩ := (GraphDomain.mem_supports G).1 hX
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fintype.card_pos (α := loc x)).trans_le (hq x)
    have hc1 : (1 : ℝ) ≤ Fintype.card (Reg loc X) := by exact_mod_cast Fintype.card_pos
    have hc : (Fintype.card (Reg loc X) : ℝ) ≤ (q : ℝ) ^ #X := by
      have : Fintype.card (Reg loc X) ≤ q ^ #X := by
        rw [Fintype.card_pi]
        exact (prod_le_pow_card (univ : Finset X) (fun i : X => Fintype.card (loc i)) q
          fun i _ => hq i).trans_eq (by rw [card_univ, Fintype.card_coe])
      exact_mod_cast this
    have hv : (#X : ℝ) ≤ V R := by exact_mod_cast (step_2_8 G V hV Λ R x).2.2.2 X hX
    have hl : 0 ≤ Real.log q := Real.log_nonneg hq1
    have h1 : Real.log (Fintype.card (Reg loc X)) ≤ V R * Real.log q :=
      (Real.log_le_log (by linarith) hc).trans (by
        rw [Real.log_pow]; exact mul_le_mul_of_nonneg_right hv hl)
    rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) (by linarith) 2
  have h1 := sum_le_card_nsmul {X ∈ supports G Λ R | (X ∩ B).Nonempty ∧ (X \ B).Nonempty}
    (fun X => Real.log (Real.exp 1 * Fintype.card (Reg loc X)) ^ 2) _ fun X hX =>
    hlog X (mem_filter.1 hX).1
  -- D10.5.1: the crossing count (D2.9)
  have h2 : (#{X ∈ supports G Λ R | (X ∩ B).Nonempty ∧ (X \ B).Nonempty} : ℝ) ≤
      2 * V R * μ V R * #(edgeBoundary G Λ B) := by
    exact_mod_cast eq_crossing_count G V hV Λ B R
  rw [nsmul_eq_mul] at h1
  nlinarith [sq_nonneg (1 + V R * Real.log q)]

omit [DecidableEq σ] [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  [∀ i, Nonempty (loc i)] in
/-- D10.5.3. For fixed `K` and `n ≥ n₀(K)`: `C exp(-c n^{1/10}) ≤ n^{-2K}`. -/
theorem step_10_5_3 (C : ℝ) {c : ℝ} (hc : 0 < c) (K : ℕ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      C * Real.exp (-(c * (n : ℝ) ^ (1 / 10 : ℝ))) ≤ ((n : ℝ) ^ (2 * K))⁻¹ := by
  have hC : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hx : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 10 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (20 * K) c hc).comp hx).eventually
    (ge_mem_nhds (inv_pos.2 hC))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 1))
  refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n ((le_max_left _ _).trans hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h2
  have hpow : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ (20 * (K : ℝ)) = (n : ℝ) ^ (2 * K) := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  simp only [Function.comp, hpow, neg_mul] at h1
  have hP : 0 < (n : ℝ) ^ (2 * K) := by positivity
  set E := Real.exp (-(c * (n : ℝ) ^ (1 / 10 : ℝ)))
  calc C * E ≤ max C 1 * E := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ = max C 1 * ((n : ℝ) ^ (2 * K) * E) / (n : ℝ) ^ (2 * K) := by field_simp
    _ ≤ max C 1 * (max C 1)⁻¹ / (n : ℝ) ^ (2 * K) := by gcongr
    _ = ((n : ℝ) ^ (2 * K))⁻¹ := by field_simp

end Typical

/-- D10.5 (`eq:amplification-typical-error`). Put `w = n^{3/5}`, `δ = n^{-2K}`. For a cut `B`
with `|∂_Λ B| ≤ C₀ n`, let `P_B` be the spectral projection of `ρ_B` onto the positive
eigenvalues `p` with `-log p ∈ [S - w, S + w]`, `S = S(B)`. For `n` large (given `K`),
`‖(I - P_B) Ω‖² ≤ δ`. -/
theorem step_10_5 {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]
    (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)]
    {q : ℕ} (hq : ∀ i, Fintype.card (loc i) ≤ q) (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (C₀ : ℝ) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (Λ : Finset σ) (Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ),
      IsAdmissible G Λ R J Φ →
    ∀ (Ω : Reg loc Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (B : Finset σ) (hB : B ⊆ Λ), (#(edgeBoundary G Λ B) : ℝ) ≤ C₀ * n →
      vnorm ((1 - extendId hB (typicalProj Ω hΩ hB ((n : ℝ) ^ (3 / 5 : ℝ)))) *ᵥ Ω) ^ 2 ≤
        ((n : ℝ) ^ (2 * K))⁻¹ := by
  set A₀ : ℝ := 2 * V R * μ V R * (1 + V R * Real.log q) ^ 2
  have hA₀ : 0 ≤ A₀ := by positivity
  set C₁ : ℝ := 1 + A₀ * |C₀|
  have hC₁ : 1 ≤ C₁ := le_add_of_nonneg_right (by positivity)
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hC₁ϑ : 0 < (1 + J / Δ) * C₁ := mul_pos (by linarith) (by linarith)
  set c : ℝ := (32 * √((1 + J / Δ) * C₁))⁻¹
  have hc : 0 < c := inv_pos.2 (mul_pos (by norm_num) (Real.sqrt_pos.2 hC₁ϑ))
  -- D10.5.3: the threshold `n₀(K)`
  obtain ⟨n₀, hn₀1, hn₀⟩ := step_10_5_3 (2 * Real.exp (Real.exp 1 / 2)) hc K
  refine ⟨n₀, fun n hn Λ Φ hΦ Ω hΩ E₀ heig hgap B hB hbd => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn₀1.trans hn
  rw [step_10_5_2]
  -- D10.5.2: Lemma 3.1 for `H = ∑_X h_X ⊗ 1`, labels the supports, `c₀ = J`, `g₀ = Δ`
  set N := #(supports G Λ R)
  let e := (supports G Λ R).equivFin
  let D : Fin N → Finset σ := fun i => (e.symm i).1
  have hD : ∀ i, D i ⊆ Λ := fun i => ((GraphDomain.mem_supports G).1 (e.symm i).2).1
  have hH : ∑ i, extendId (hD i) (Φ (D i)) = hamiltonian Λ Φ := by
    rw [hamiltonian_eq_sum_supports G hΦ]
    exact e.symm.sum_comp fun Y => extendId ((GraphDomain.mem_supports G).1 Y.2).1 (Φ Y.1)
  have hT := (lemma_3_1 (σ := σ) (loc := loc) Λ (Fin N) D hD
    (fun i => extendId (hD i) (Φ (D i))) J Δ E₀ Ω hΩ (fun i => ⟨_, rfl⟩)
    (fun i => isHermitian_extendId _ (hΦ _ (hD i)).1) hJ
    (fun i => (norm_extendId_le _ _).trans (hΦ _ (hD i)).2.1) hΔ (by rw [hH]; exact heig)
    (by rw [hH]; exact hgap) B hB).2 ((n : ℝ) ^ (3 / 5 : ℝ)) (by positivity)
  refine (hT.trans (min_le_right _ _)).trans (le_trans ?_ (hn₀ n hn))
  -- D10.5.1: `𝓑 ≤ C₁ n`
  have h𝓑 : 1 + ∑ i ∈ univ.filter (fun i => (D i ∩ B).Nonempty ∧ (D i \ B).Nonempty),
      Real.log (Real.exp 1 * Fintype.card (Reg loc (D i))) ^ 2 ≤ C₁ * n := by
    have heq : ∑ i ∈ univ.filter (fun i => (D i ∩ B).Nonempty ∧ (D i \ B).Nonempty),
        Real.log (Real.exp 1 * Fintype.card (Reg loc (D i))) ^ 2 =
        ∑ X ∈ supports G Λ R with (X ∩ B).Nonempty ∧ (X \ B).Nonempty,
          Real.log (Real.exp 1 * Fintype.card (Reg loc X)) ^ 2 := by
      rw [sum_filter, sum_filter, ← sum_coe_sort (supports G Λ R)]
      exact e.symm.sum_comp fun Y => if (Y.1 ∩ B).Nonempty ∧ (Y.1 \ B).Nonempty then
        Real.log (Real.exp 1 * Fintype.card (Reg loc Y.1)) ^ 2 else 0
    rw [heq]
    refine (step_10_5_1 G V hV hq Λ B R).trans ?_
    have hb : (#(edgeBoundary G Λ B) : ℝ) ≤ |C₀| * n :=
      hbd.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h1 := mul_le_mul_of_nonneg_left hb hA₀
    have h2 : A₀ * |C₀| * 1 ≤ A₀ * |C₀| * n := mul_le_mul_of_nonneg_left hn1 (by positivity)
    simp only [C₁]
    nlinarith
  -- D10.5.2: `w / (32 √((1 + ϑ) 𝓑)) ≥ c n^{1/10}`
  have key : ∀ b : ℝ, 0 < b → b ≤ C₁ * n →
      c * (n : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) / (32 * √((1 + J / Δ) * b)) := by
    intro b hb0 hb
    have hn0 : (0 : ℝ) < n := by linarith
    have hs : √((1 + J / Δ) * b) ≤ √((1 + J / Δ) * C₁) * √n := by
      rw [← Real.sqrt_mul hC₁ϑ.le]
      exact Real.sqrt_le_sqrt (by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb (by linarith))
    have hw : (n : ℝ) ^ (3 / 5 : ℝ) = (n : ℝ) ^ (1 / 10 : ℝ) * √n := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; norm_num
    have hpos : 0 < √((1 + J / Δ) * b) := Real.sqrt_pos.2 (mul_pos (by linarith) hb0)
    have h32 : c * (32 * √((1 + J / Δ) * C₁)) = 1 :=
      inv_mul_cancel₀ (mul_pos (by norm_num) (Real.sqrt_pos.2 hC₁ϑ)).ne'
    rw [le_div_iff₀ (by positivity), hw]
    calc c * (n : ℝ) ^ (1 / 10 : ℝ) * (32 * √((1 + J / Δ) * b)) ≤
        c * (n : ℝ) ^ (1 / 10 : ℝ) * (32 * (√((1 + J / Δ) * C₁) * √n)) := by gcongr
      _ = c * (32 * √((1 + J / Δ) * C₁)) * ((n : ℝ) ^ (1 / 10 : ℝ) * √n) := by ring
      _ = _ := by rw [h32, one_mul]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) (by positivity)
  exact key _ (lt_of_lt_of_le one_pos (le_add_of_nonneg_right
    (sum_nonneg fun _ _ => sq_nonneg _))) h𝓑

end AreaLaw
