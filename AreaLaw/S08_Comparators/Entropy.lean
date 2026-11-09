import AreaLaw.S08_Comparators.Setup

/-!
# §8 Typical entropies (D8.3) and the entropy identity (D8.36)

Digest `digest/08-comparators.md` D8.3, D8.36 (and D8.30.6, `g^pre ≥ 0`). No geometry.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Arealaw Entropy

namespace AreaLaw.Comparators

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}

/-- D8.3 (`comparator:typical-entropies`). `|log d_* - S_X| ≤ w + |log z|` and
`|S' - S_X| ≤ w + |log z|`. -/
theorem step_8_3 (E : TypicalSet D X) :
    |Real.log E.d - D.S X| ≤ E.w + |Real.log E.z| ∧ |E.S' - D.S X| ≤ E.w + |Real.log E.z| := by
  have hp : ∀ i ∈ E.E, 0 < D.p X i := fun i hi => (Real.exp_pos _).trans_le (E.lower i hi)
  have hd : (0 : ℝ) < E.d := by exact_mod_cast E.nonempty.card_pos
  -- D8.3.1: `d_* e^{-S_X - w} ≤ z ≤ d_* e^{-S_X + w}`
  have hz₁ : E.d * Real.exp (-D.S X - E.w) ≤ E.z := by
    have := Finset.card_nsmul_le_sum E.E (D.p X) _ E.lower
    simpa [TypicalSet.z, TypicalSet.d, nsmul_eq_mul] using this
  have hz₂ : E.z ≤ E.d * Real.exp (-D.S X + E.w) := by
    have := Finset.sum_le_card_nsmul E.E (D.p X) _ E.upper
    simpa [TypicalSet.z, TypicalSet.d, nsmul_eq_mul] using this
  have hz : 0 < E.z := (mul_pos hd (Real.exp_pos _)).trans_le hz₁
  have hl₁ := Real.log_le_log (mul_pos hd (Real.exp_pos _)) hz₁
  have hl₂ := Real.log_le_log hz hz₂
  rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hl₁
  rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hl₂
  refine ⟨abs_le.2 ⟨?_, ?_⟩, ?_⟩
  · linarith [neg_abs_le (Real.log E.z), le_abs_self (Real.log E.z)]
  · linarith [neg_abs_le (Real.log E.z), le_abs_self (Real.log E.z)]
  -- D8.3.2: `-log p'_i ∈ [S_X + log z - w, S_X + log z + w]`, averaged under `p'`
  have hp' : ∀ i ∈ E.E, 0 < E.p' i := fun i hi => div_pos (hp i hi) hz
  have hsum : ∑ i ∈ E.E, E.p' i = 1 := by
    simp only [TypicalSet.p', ← Finset.sum_div]
    exact div_self hz.ne'
  have hlog : ∀ i ∈ E.E, D.S X + Real.log E.z - E.w ≤ -Real.log (E.p' i) ∧
      -Real.log (E.p' i) ≤ D.S X + Real.log E.z + E.w := fun i hi => by
    have h₁ := Real.log_le_log (Real.exp_pos _) (E.lower i hi)
    have h₂ := Real.log_le_log (hp i hi) (E.upper i hi)
    rw [Real.log_exp] at h₁ h₂
    rw [TypicalSet.p', Real.log_div (hp i hi).ne' hz.ne']
    constructor <;> linarith
  have hS : E.S' = ∑ i ∈ E.E, E.p' i * -Real.log (E.p' i) := by
    simp only [TypicalSet.S', Real.negMulLog, neg_mul, mul_neg]
  have hlo : D.S X + Real.log E.z - E.w ≤ E.S' := by
    rw [hS]
    calc D.S X + Real.log E.z - E.w = ∑ i ∈ E.E, E.p' i * (D.S X + Real.log E.z - E.w) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hlog i hi).1 (hp' i hi).le
  have hhi : E.S' ≤ D.S X + Real.log E.z + E.w := by
    rw [hS]
    calc ∑ i ∈ E.E, E.p' i * -Real.log (E.p' i) ≤
          ∑ i ∈ E.E, E.p' i * (D.S X + Real.log E.z + E.w) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hlog i hi).2 (hp' i hi).le
      _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_abs_le (Real.log E.z), le_abs_self (Real.log E.z)]
  · linarith [neg_abs_le (Real.log E.z), le_abs_self (Real.log E.z)]

namespace PhysData

variable (D)

/-- Purity: `S(A) = S(B)` for complementary `A, B`. -/
theorem S_eq_of_compl {A B : Finset σ} (h : Finset.univ \ A = B) : D.S A = D.S B := by
  have e := MState.regionEntropy_pureState_sdiff (D.Ω ∘ univEquiv) D.norm_Ω_univEquiv
    (Finset.subset_univ A)
  exact e.trans (D.state.toSubState.regionEntropy_congr h _ _)

/-- Subadditivity: `S(A ∪ B) ≤ S(A) + S(B)` for disjoint `A, B`. -/
theorem S_union_le {A B : Finset σ} (h : Disjoint A B) : D.S (A ∪ B) ≤ D.S A + D.S B :=
  regionEntropy_union_le D.state h (Finset.subset_univ A) (Finset.subset_univ B)

end PhysData

variable {K : ℕ} {St : Type*} (Γ : Statuses σ K St X) (s : St) (g : Fin K)

private theorem compl_eq {A B : Finset σ} (h : Disjoint A B) (hAB : A ∪ B = Finset.univ) :
    Finset.univ \ A = B := by
  rw [← hAB, Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint]
  exact h.symm

/-- D8.36 (`comparator:entropy-identity`). For every physical partition `X, U, Y, V`:
`2 S_X + g^pre - g^post = I(X : V) + I(X : YV)`. -/
theorem step_8_36 :
    2 * D.S X + gpre D Γ s g - gpost D Γ s g =
      D.I X (Γ.V s g) + D.I X (Γ.Y s g ∪ Γ.V s g) := by
  have hc := Γ.cover s g
  have hXU := Γ.disjoint_XU s g
  have hXY := Γ.disjoint_XY s g
  have hXV := Γ.disjoint_XV s g
  have hUY := Γ.disjoint_UY s g
  have hUV := Γ.disjoint_UV s g
  have hYV := Γ.disjoint_YV s g
  -- D8.36.1: purity, `S(XU) = S(YV)`, `S(XV) = S(UY)`, `S(XYV) = S(U)`
  have h₁ : D.S (X ∪ Γ.U s g) = D.S (Γ.Y s g ∪ Γ.V s g) :=
    D.S_eq_of_compl (compl_eq (by simp [hXY, hXV, hUY, hUV, Finset.disjoint_union_left,
      Finset.disjoint_union_right]) (by rw [← hc]; ac_rfl))
  have h₂ : D.S (X ∪ Γ.V s g) = D.S (Γ.U s g ∪ Γ.Y s g) :=
    D.S_eq_of_compl (compl_eq (by simp [hXU, hXY, hUV.symm, hYV.symm,
      Finset.disjoint_union_left, Finset.disjoint_union_right]) (by rw [← hc]; ac_rfl))
  have h₃ : D.S (X ∪ (Γ.Y s g ∪ Γ.V s g)) = D.S (Γ.U s g) :=
    D.S_eq_of_compl (compl_eq (by simp [hXU, hUY.symm, hUV.symm, Finset.disjoint_union_left])
      (by rw [← hc]; ac_rfl))
  -- D8.36.2, D8.36.3
  have hI₁ : D.I X (Γ.V s g) = D.S X + D.S (Γ.V s g) - D.S (X ∪ Γ.V s g) := rfl
  have hI₂ : D.I X (Γ.Y s g ∪ Γ.V s g) =
      D.S X + D.S (Γ.Y s g ∪ Γ.V s g) - D.S (X ∪ (Γ.Y s g ∪ Γ.V s g)) := rfl
  rw [hI₁, hI₂, gpre, gpost]
  linarith

/-- D8.30.6. `g^pre_{j,g} ≥ 0`: `S(Y) = S(XUV) ≤ S(XU) + S(V)` by purity and subadditivity. -/
theorem gpre_nonneg : 0 ≤ gpre D Γ s g := by
  have hc := Γ.cover s g
  have hY : D.S (Γ.Y s g) = D.S (X ∪ Γ.U s g ∪ Γ.V s g) :=
    D.S_eq_of_compl (compl_eq (by
      simp [(Γ.disjoint_XY s g).symm, Γ.disjoint_UY s g |>.symm, Γ.disjoint_YV s g,
        Finset.disjoint_union_right]) (by rw [← hc]; ac_rfl))
  have hsub := D.S_union_le (A := X ∪ Γ.U s g) (B := Γ.V s g)
    (Finset.disjoint_union_left.2 ⟨Γ.disjoint_XV s g, Γ.disjoint_UV s g⟩)
  rw [gpre, hY]
  linarith

end AreaLaw.Comparators
