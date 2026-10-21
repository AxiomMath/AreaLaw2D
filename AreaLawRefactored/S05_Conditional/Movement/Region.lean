import AreaLawRefactored.S05_Conditional.Movement.Setup

/-!
# §5.1 Lemma 5.1: the region-level steps D5.2, D5.5.A, D5.9.1

Digest `digest/05-conditional.md`. The regional conditional pair `(ρ_{XE}, I_X ⊗ ρ̂_E)` and its
log-moment data (`step_5_2_region`), the purity identity `I(X:F|U) = S(X|P) + S(X|U)`
(`step_5_5_A`), and the reduction (F1) of the state movement to a Hilbert–Schmidt norm
(`step_5_9_1`).
-/

namespace AreaLaw

open Arealaw Matrix Complex
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder

universe u v

namespace Conditional.Reg51

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- `Π_{ker ρ} = 1 - ρ^{[0]}` is Hermitian. -/
theorem conjTranspose_kerProj (ρ : Matrix n n ℂ) :
    (1 - bracketPow ρ 0)ᴴ = 1 - bracketPow ρ 0 := by
  rw [conjTranspose_sub, conjTranspose_one, (isHermitian_bracketPow_zero ρ).eq]

/-- `Π_{ker ρ}` is idempotent. -/
theorem kerProj_mul_self (ρ : Matrix n n ℂ) :
    (1 - bracketPow ρ 0) * (1 - bracketPow ρ 0) = 1 - bracketPow ρ 0 := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    bracketPow_zero_mul_self, sub_self, sub_zero]

/-- `Π_{ker ρ} ≥ 0`. -/
theorem posSemidef_kerProj (ρ : Matrix n n ℂ) : (1 - bracketPow ρ 0).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (1 - bracketPow ρ 0)
  rwa [conjTranspose_kerProj, kerProj_mul_self] at h

/-- `ρ̂ = ρ + Π_{ker ρ}` for `ρ ≥ 0`. -/
theorem hat_eq_add (hρ : ρ.PosSemidef) : hat ρ = ρ + (1 - bracketPow ρ 0) := by
  rw [hat, hatPow_eq_bracketPow_add, bracketPow_one hρ]

/-- `Re Tr(Π_{supp ρ} A) ≤ Re Tr A` for `A ≥ 0`. -/
theorem re_trace_bracketPow_zero_mul_le (ρ : Matrix n n ℂ) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : (bracketPow ρ 0 * A).trace.re ≤ A.trace.re := by
  have h := (Complex.le_def.1
    (hA.conjTranspose_mul_mul_same (1 - bracketPow ρ 0)).trace_nonneg).1
  rw [Complex.zero_re, conjTranspose_kerProj, trace_mul_comm, ← Matrix.mul_assoc,
    kerProj_mul_self, Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re] at h
  linarith

/-- `ρ * f(ρ)` only sees `f` on `[0, ∞)` for `ρ ≥ 0`. -/
theorem mul_specFun_congr (hρ : ρ.PosSemidef) {f₁ f₂ : ℝ → ℂ}
    (hf : ∀ t : ℝ, 0 ≤ t → (t : ℂ) * f₁ t = t * f₂ t) :
    ρ * specFun hρ.isHermitian f₁ = ρ * specFun hρ.isHermitian f₂ := by
  have h1 := specFun_mul hρ.isHermitian (fun t ↦ (t : ℂ)) f₁
  have h2 := specFun_mul hρ.isHermitian (fun t ↦ (t : ℂ)) f₂
  rw [specFun_ofReal] at h1 h2
  rw [h1, h2]
  exact specFun_congr _ fun i ↦ hf _ (hρ.eigenvalues_nonneg i)

/-- A unitary preserves the Euclidean norm. -/
theorem norm_toLp_unitary_mulVec {M : Matrix n n ℂ} (hM : M ∈ unitary (Matrix n n ℂ))
    (w : n → ℂ) :
    ‖(WithLp.toLp 2 (M *ᵥ w) : EuclideanSpace ℂ n)‖ = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_toLp_sq, norm_toLp_sq, star_mulVec,
    ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hM,
    one_mulVec]

end Matrix

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ X E : Finset σ}

omit [∀ i, DecidableEq (loc i)] in
/-- `ρ_{XE} ↦ ρ_E`. -/
theorem ptrace_marg (θ : Reg loc Λ → ℂ) (hX : X ⊆ Λ) (hE : E ⊆ Λ) :
    ptrace (Finset.subset_union_right : E ⊆ X ∪ E) (marg θ (Finset.union_subset hX hE)) =
      marg θ hE :=
  ptrace_ptrace _ _ _

/-- `(Π_{ker ρ_E} ⊗ I) ρ_{XE} = 0`. -/
theorem extendId_kerProj_mul_marg (θ : Reg loc Λ → ℂ) (hX : X ⊆ Λ) (hE : E ⊆ Λ) :
    extendId Finset.subset_union_right (1 - bracketPow (marg θ hE) 0) *
      marg θ (Finset.union_subset hX hE) = 0 := by
  change _ * ptrace (Finset.union_subset hX hE) (vecMulVec θ (star θ)) = 0
  rw [← extendId_mul_ptrace, Arealaw.extendId_extendId, mul_vecMulVec,
    extendId_one_sub_bracketPow_marg_mulVec θ hE]
  simp

omit [∀ i, Fintype (loc i)] in
/-- `(A - B) ⊗ I = A ⊗ I - B ⊗ I`. -/
theorem extendId_sub {S T : Finset σ} (h : S ⊆ T) (A B : Matrix (Reg loc S) (Reg loc S) ℂ) :
    extendId h (A - B) = extendId h A - extendId h B := by
  rw [sub_eq_add_neg, extendId_add, ← neg_one_smul ℂ B, extendId_smul, neg_one_smul,
    ← sub_eq_add_neg]

/-- (F1): `‖(W ⊗ I) θ‖ = ‖W √ρ_T‖₂` for `W` on `T ⊆ Λ`. -/
theorem norm_extendId_mulVec {T : Finset σ} (θ : Reg loc Λ → ℂ) (hT : T ⊆ Λ)
    (W : Matrix (Reg loc T) (Reg loc T) ℂ) :
    ‖(WithLp.toLp 2 (extendId hT W *ᵥ θ) : EuclideanSpace ℂ (Reg loc Λ))‖ =
      √(((W * CFC.sqrt (marg θ hT))ᴴ * (W * CFC.sqrt (marg θ hT))).trace.re) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq, step_5_1_F1_sqrt]

/-- `U ↦ U ⊗ I` preserves unitarity. -/
theorem extendId_mem_unitary {S T : Finset σ} (h : S ⊆ T) {W : Matrix (Reg loc S) (Reg loc S) ℂ}
    (hW : W ∈ unitary (Matrix (Reg loc S) (Reg loc S) ℂ)) :
    extendId h W ∈ unitary (Matrix (Reg loc T) (Reg loc T) ℂ) := by
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩ <;>
  · rw [star_eq_conjTranspose, ← extendId_conjTranspose, ← extendId_mul, ← star_eq_conjTranspose]
    simp [Unitary.star_mul_self_of_mem hW, Unitary.mul_star_self_of_mem hW]

end Region

end Conditional.Reg51

open Conditional Conditional.Reg51

/-- D5.2 at the region level, with (F1) for D5.6.2. For a unit `θ` and disjoint `X, E`:
`(ρ_{XE}, I_X ⊗ ρ̂_E)` is a conditional pair with `d = dim X` (`ρ ≤ d (I_X ⊗ ρ_E)`,
`Tr Π_{supp ρ} Q ≤ d`), its `𝔼 L = Tr ρ log ρ − Tr ρ log Q` is `-S(XE) + S(E) = -S(X|E)_θ`,
and `‖τ^{[a]} ρ̂_E^{-a} θ‖² = Tr τ^{[2a]} K` for `τ ≥ 0`, `a > 0`. -/
theorem step_5_2_region : Step_5_2_region.{u, v} := by
  intro σ _ loc _ _ Λ X E hX hE hXE θ hθ
  set hT := Finset.union_subset hX hE
  have hE' : E ⊆ X ∪ E := Finset.subset_union_right
  set ρ := marg θ hT
  have hρ := posSemidef_marg θ hT
  have hρE := posSemidef_marg θ hE
  have hcard : Fintype.card (Reg loc ((X ∪ E) \ E)) = Fintype.card (Reg loc X) := by
    rw [Finset.union_sdiff_cancel_right hXE]
  have hQ : Qmat θ hE X = extendId hE' (marg θ hE) +
      extendId hE' (1 - bracketPow (marg θ hE) 0) := by
    rw [Qmat, hat_eq_add hρE, extendId_add]
  -- D5.2.2: `(I ⊗ Π_{ker ρ_E}) ρ^{[0]} = 0`
  have hker : extendId hE' (1 - bracketPow (marg θ hE) 0) * bracketPow ρ 0 = 0 := by
    have h := bracketPow_mul_bracketPow ρ 1 (-1)
    rw [bracketPow_one hρ, show (1 : ℂ) + -1 = 0 by norm_num] at h
    rw [← h, ← Matrix.mul_assoc, extendId_kerProj_mul_marg θ hX hE, Matrix.zero_mul]
  refine ⟨⟨hρ, by rw [trace_marg, hθ], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- `Q > 0`
    have hhat : (hat (marg θ hE)).PosSemidef := by
      rw [hat_eq_add hρE]
      exact hρE.add (posSemidef_kerProj _)
    refine (posSemidef_extendId hE' hhat).posDef_iff_isUnit.2 ?_
    have h : Qmat θ hE X * hatPow (Qmat θ hE X) (-1) = 1 := by
      rw [hatPow_Qmat, Qmat, hat, ← extendId_mul, hatPow_mul_hatPow_neg, extendId_one]
    exact ⟨⟨_, _, h, mul_eq_one_comm.1 h⟩, rfl⟩
  · -- `1 ≤ dim X`
    have hne : Nonempty (Reg loc Λ) := by
      by_contra hne
      simp [not_nonempty_iff.1 hne, dotProduct] at hθ
    exact Fintype.card_pos_iff.2 ⟨restr hX hne.some⟩
  · -- D5.2.1: `ρ ≤ d (I ⊗ ρ_E) ≤ d Q`
    have h := step_5_2_1 hE' hρ
    rw [ptrace_marg θ hX hE, hcard, Matrix.le_iff] at h
    rw [Matrix.le_iff, hQ, smul_add, show ∀ A B C : Matrix (Reg loc (X ∪ E)) (Reg loc (X ∪ E)) ℂ,
      A + B - C = (A - C) + B from fun _ _ _ ↦ by abel]
    exact h.add ((posSemidef_extendId hE' (posSemidef_kerProj _)).smul
      (by exact_mod_cast Complex.zero_le_real.2 (Nat.cast_nonneg (Fintype.card (Reg loc X)))))
  · -- D5.2.2, D5.2.5: `Tr Π_{supp ρ} Q = Tr Π_{supp ρ} (I ⊗ ρ_E) ≤ Tr (I ⊗ ρ_E) = d`
    rw [hQ, Matrix.mul_add, trace_add, trace_mul_comm (bracketPow ρ 0)
      (extendId hE' (1 - _)), hker, trace_zero, add_zero]
    refine (re_trace_bracketPow_zero_mul_le ρ (posSemidef_extendId hE' hρE)).trans_eq ?_
    rw [trace_extendId, hcard, trace_marg, hθ, mul_one, Complex.natCast_re]
  · -- D5.2.3: `𝔼 L = -S(XE) + S(E)`
    have hρEh := hρE.isHermitian
    set g : ℝ → ℝ := fun t ↦ if 0 < t then t else 1
    have hg : hat (marg θ hE) = specFun hρEh fun t ↦ (g t : ℂ) := by
      rw [hat, hatPow_eq hρEh]
      refine specFun_congr hρEh fun i ↦ ?_
      by_cases ht : 0 < hρEh.eigenvalues i
      · simp [hfun, g, ht, ← Complex.ofReal_exp, Real.exp_log ht]
      · simp [hfun, g, ht]
    have h' := isHermitian_specFun_ofReal hρEh g
    have hlogQ : cfc Real.log (Qmat θ hE X) =
        extendId hE' (specFun hρEh fun t ↦ (Real.log (g t) : ℂ)) := by
      rw [Qmat, hg, ← specFun_ofReal_comp (isHermitian_extendId hE' h'), specFun_extendId hE' h',
        specFun_specFun hρEh g h']
    have h2 : (ρ * cfc Real.log (Qmat θ hE X)).trace.re = -vonNeumann hρEh := by
      rw [hlogQ, ← trace_ptrace_mul, ptrace_marg θ hX hE, mul_specFun_congr hρE (f₂ := fun t ↦
        (Real.log t : ℂ)) fun t ht ↦ ?_, re_trace_mul_log]
      rcases ht.eq_or_lt with rfl | ht
      · simp
      · simp [g, ht]
    rw [relEnt, ← specFun_ofReal_comp hρ.isHermitian, re_trace_mul_log, h2, condEntropy]
    change -vonNeumann hρ.isHermitian - -vonNeumann hρEh =
      -(vonNeumann hρ.isHermitian - vonNeumann hρEh)
    ring
  · -- (F1), D5.6.2: `‖τ^{[a]} Q^{-a} θ‖² = Tr τ^{[2a]} Q^{-a} ρ Q^{-a}`
    intro τ _ a _
    have e (A B C : Matrix (Reg loc (X ∪ E)) (Reg loc (X ∪ E)) ℂ) :
        (B * A * (A * B) * C).trace = (A * A * (B * C * B)).trace := by
      rw [show A * A * (B * C * B) = A * A * (B * C) * B by simp only [Matrix.mul_assoc],
        trace_mul_comm (A * A * (B * C)) B]
      simp only [Matrix.mul_assoc]
    rw [← Arealaw.extendId_extendId hE' hT, ← extendId_mul, step_5_1_F1_norm, Kmat,
      ← hatPow_Qmat, conjTranspose_mul, conjTranspose_hatPow, conjTranspose_bracketPow,
      Complex.conj_ofReal, Complex.conj_ofReal,
      show ((2 * a : ℝ) : ℂ) = (a : ℂ) + a by push_cast; ring, ← bracketPow_mul_bracketPow, e]

/-- D5.5.A. For a unit `θ` on `P ⊔ X ⊔ U ⊔ F`, purity (`S(XUF) = S(P)`, `S(UF) = S(XP)`) gives
`I(X:F|U)_θ = S(XU) + S(UF) − S(U) − S(XUF) = S(X|P)_θ + S(X|U)_θ`. -/
theorem step_5_5_A : Step_5_5_A.{u, v} := by
  intro σ _ loc _ _ Λ P X U F hP hX hU hF hΛ hPX hPU hPF hXU hXF hUF θ hθ
  have h1 := MState.regionEntropy_pureState_union θ hθ
    (A := U ∪ F) (B := X ∪ P) (Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨hXU.symm, hPU.symm⟩, Finset.disjoint_union_right.2 ⟨hXF.symm, hPF.symm⟩⟩)
    (by rw [hΛ]; ext; simp only [Finset.mem_union]; tauto)
    (Finset.union_subset hU hF) (Finset.union_subset hX hP)
  have h2 := MState.regionEntropy_pureState_union θ hθ
    (A := X ∪ U ∪ F) (B := P) (Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2
      ⟨hPX.symm, hPU.symm⟩, hPF.symm⟩)
    (by rw [hΛ]; ext; simp only [Finset.mem_union]; tauto)
    (Finset.union_subset (Finset.union_subset hX hU) hF) hP
  simp only [condMutualInfo, condEntropy]
  linarith

/-- D5.9.1 with (F1). For a unit `θ`, disjoint `X, U`, `τ > 0` on `XU`:
`‖θ_u − θ‖ = ‖(τ_u^{-iau} − Q^{-iau}) √ρ_{XU}‖₂`. Since `τ_u^{-iau} = Q^{-iau} τ^{-iau} Q^{iau}`,
`((τ_u^{-iau} − Q^{-iau}) ⊗ I) θ = (Q^{-iau} ⊗ I)(θ_u − θ)`, `Q^{-iau}` is unitary, and (F1). -/
theorem step_5_9_1 : Step_5_9_1.{u, v} := by
  intro σ _ loc _ _ Λ X U hX hU _ θ _ τ _ a u W
  set hT := Finset.union_subset hX hU
  set Q := Qmat θ hU X
  set z : ℂ := ((-(a * u) : ℝ) : ℂ) * I
  have hW0 := hatPow_mul_I_mem_unitary Q (-(a * u))
  have hstar : star (hatPow Q z) = hatPow Q ((a * u : ℝ) * I) := by
    rw [star_hatPow]
    congr 1
    simp [z]
  have htau : hatPow (tauU θ hU X τ a u) z = hatPow Q z * hatPow τ z * star (hatPow Q z) := by
    rw [← hatPow_unitary_conj hW0, hstar]
    rfl
  have hext : extendId hT (star (hatPow Q z)) =
      extendId hU (hatPow (marg θ hU) ((a * u : ℝ) * I)) := by
    rw [hstar, hatPow_Qmat, Arealaw.extendId_extendId]
  -- D5.9.1: `((τ_u^{-iau} − Q^{-iau}) ⊗ I) θ = (Q^{-iau} ⊗ I)(θ_u − θ)`
  have key : extendId hT (hatPow (tauU θ hU X τ a u) z - hatPow Q z) *ᵥ θ =
      extendId hT (hatPow Q z) *ᵥ (thetaU θ hX hU τ a u - θ) := by
    rw [htau, extendId_sub, extendId_mul, extendId_mul, hext, thetaU, sub_mulVec, mulVec_sub,
      mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← norm_toLp_unitary_mulVec (extendId_mem_unitary hT hW0), ← key]
  exact norm_extendId_mulVec θ hT _

end AreaLaw
