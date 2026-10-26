import AreaLaw.S05_Conditional.Movement.Region
import AreaLaw.S05_Conditional.Movement.ArakiLiebThirring

/-!
# §5.1 Lemma 5.1: the analytic function `G` and its boundary values (D5.5.3, D5.6.1, D5.10.1)

Digest `digest/05-conditional.md`. `G(z) = σ^{[az]} ρ̂_P^{-az} τ^{[a(1-z)]} ρ̂_U^{-a(1-z)} θ` is
entire and bounded on the strip `0 ≤ Re z ≤ 1` (`step_5_5_3`); on the left boundary
`‖G(iu)‖ ≤ ‖τ_u^{[a]} ρ̂_U^{-a} θ‖` (`step_5_6_1`), on the right boundary
`‖G(1+iu)‖ ≤ ‖σ_u^{[a]} ρ̂_P^{-a} θ_u‖` (`step_5_10_1`).
-/

namespace AreaLaw

open Arealaw Matrix Complex
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u v

namespace Conditional.An

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A contraction does not increase the Euclidean norm. -/
theorem norm_mulVec_le {M : Matrix n n ℂ} (hM : ‖M‖ ≤ 1) (w : n → ℂ) :
    ‖(WithLp.toLp 2 (M *ᵥ w) : EuclideanSpace ℂ n)‖ ≤ ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ :=
  (l2_opNorm_mulVec M (WithLp.toLp 2 w)).trans (mul_le_of_le_one_left (norm_nonneg _) hM)

/-- A unitary preserves `⟨w, w⟩`. -/
theorem star_mulVec_dotProduct {M : Matrix n n ℂ} (hM : M ∈ unitary (Matrix n n ℂ)) (w : n → ℂ) :
    star (M *ᵥ w) ⬝ᵥ (M *ᵥ w) = star w ⬝ᵥ w := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
    Unitary.star_mul_self_of_mem hM, one_mulVec]

/-- For `τ > 0`, `τ^{[z]} = τ̂^z`. -/
theorem bracketPow_eq_hatPow {τ : Matrix n n ℂ} (hτ : τ.PosDef) (z : ℂ) :
    bracketPow τ z = hatPow τ z := by
  rw [bracketPow_eq hτ.1]
  exact specFun_eq_hatPow hτ fun t ht ↦ if_pos ht

/-- On the strip: `‖g_w(ρ)‖ ≤ exp ‖c log λ‖` when `|g_w(t)| ≤ exp |Re w log t|`,
`Re w = c x`, `0 ≤ x ≤ 1`. -/
theorem norm_specFun_le {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) {g : ℂ → ℝ → ℂ}
    (hg : ∀ w t, ‖g w t‖ ≤ Real.exp |w.re * Real.log t|) (c : ℝ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) {w : ℂ} (hw : w.re = c * x) :
    ‖specFun h (g w)‖ ≤ Real.exp ‖fun j ↦ c * Real.log (h.eigenvalues j)‖ :=
  ALT.norm_specFun_le h (Real.exp_nonneg _) fun i ↦ (hg w _).trans <| by
    rw [hw]; exact ALT.exp_abs_le c (fun j ↦ Real.log (h.eigenvalues j)) i hx0 hx1

/-- Imaginary powers are contractions: `‖g_w(ρ)‖ ≤ 1` for `Re w = 0`. -/
theorem norm_specFun_le_one {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) {g : ℂ → ℝ → ℂ}
    (hg : ∀ w t, ‖g w t‖ ≤ Real.exp |w.re * Real.log t|) {w : ℂ} (hw : w.re = 0) :
    ‖specFun h (g w)‖ ≤ 1 :=
  ALT.norm_specFun_le h zero_le_one fun _ ↦ (hg w _).trans (by simp [hw])

end Matrix

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ S T : Finset σ}

/-- `‖(ρ^{[w]} ⊗ I)‖ ≤ exp ‖c log λ‖` for `Re w = c x`, `0 ≤ x ≤ 1`. -/
theorem norm_extendId_bracketPow_le (h : S ⊆ T) {M : Matrix (Reg loc S) (Reg loc S) ℂ}
    (hM : M.IsHermitian) (c : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {w : ℂ}
    (hw : w.re = c * x) : ‖extendId h (bracketPow M w)‖ ≤
      Real.exp ‖fun j ↦ c * Real.log ((isHermitian_extendId h hM).eigenvalues j)‖ := by
  rw [bracketPow_eq hM, ← specFun_extendId h hM]
  exact norm_specFun_le _ ALT.norm_bfun_le c hx0 hx1 hw

/-- `‖(ρ̂^w ⊗ I)‖ ≤ exp ‖c log λ‖` for `Re w = c x`, `0 ≤ x ≤ 1`. -/
theorem norm_extendId_hatPow_le (h : S ⊆ T) {M : Matrix (Reg loc S) (Reg loc S) ℂ}
    (hM : M.IsHermitian) (c : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {w : ℂ}
    (hw : w.re = c * x) : ‖extendId h (hatPow M w)‖ ≤
      Real.exp ‖fun j ↦ c * Real.log ((isHermitian_extendId h hM).eigenvalues j)‖ := by
  rw [hatPow_eq hM, ← specFun_extendId h hM]
  exact norm_specFun_le _ ALT.norm_hfun_le c hx0 hx1 hw

/-- `‖(ρ^{[w]} ⊗ I)‖ ≤ 1` for `Re w = 0`. -/
theorem norm_extendId_bracketPow_le_one (h : S ⊆ T) {M : Matrix (Reg loc S) (Reg loc S) ℂ}
    (hM : M.IsHermitian) {w : ℂ} (hw : w.re = 0) : ‖extendId h (bracketPow M w)‖ ≤ 1 := by
  rw [bracketPow_eq hM, ← specFun_extendId h hM]
  exact norm_specFun_le_one _ ALT.norm_bfun_le hw

/-- `‖(ρ̂^w ⊗ I)‖ ≤ 1` for `Re w = 0`. -/
theorem norm_extendId_hatPow_le_one (h : S ⊆ T) {M : Matrix (Reg loc S) (Reg loc S) ℂ}
    (hM : M.IsHermitian) {w : ℂ} (hw : w.re = 0) : ‖extendId h (hatPow M w)‖ ≤ 1 := by
  rw [hatPow_eq hM, ← specFun_extendId h hM]
  exact norm_specFun_le_one _ ALT.norm_hfun_le hw

/-- A unitary on `T` disjoint from `P` keeps the `P`-marginal. -/
theorem marg_extendId_unitary_mulVec {P : Finset σ} (hT : T ⊆ Λ) (hP : P ⊆ Λ)
    (hd : Disjoint T P) {W : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hW : W ∈ unitary (Matrix (Reg loc T) (Reg loc T) ℂ)) (θ : Reg loc Λ → ℂ) :
    marg (extendId hT W *ᵥ θ) hP = marg θ hP := by
  refine Matrix.ext_iff_trace_mul_right.2 fun A ↦ ?_
  rw [marg, marg, ← dotProduct_extendId_mulVec, ← dotProduct_extendId_mulVec, star_mulVec,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
    ← (commute_extendId_extendId hT hP hd W A).eq, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
    Unitary.star_mul_self_of_mem (Reg51.extendId_mem_unitary hT hW), Matrix.one_mul]

end Region

end Conditional.An

open Conditional Conditional.An

/-- D5.5.3. `G(z) = σ^{[az]} ρ̂_P^{-az} τ^{[a(1-z)]} ρ̂_U^{-a(1-z)} θ` is entire, bounded on the
closed strip `0 ≤ Re z ≤ 1` (imaginary powers are contractions, real powers bounded by the fixed
factors), and `G(1/2)` is the vector of Lemma 5.1, for `σ ≥ 0` on `XP`, `τ > 0` on `XU`. -/
theorem step_5_5_3 : Step_5_5_3.{u, v} := by
  intro σ _ loc _ _ Λ P X U hP hX hU θ a σ' τ _ hσ hτ
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (a : ℂ) * (1 / 2) = ((a / 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (a : ℂ) * (1 - 1 / 2) = ((a / 2 : ℝ) : ℂ) := by push_cast; ring
    simp only [Gfun, e1, e2]
  · have hE : ∀ {D : Finset σ} (hD : D ⊆ Λ) (ρ : Matrix (Reg loc D) (Reg loc D) ℂ)
        (F : Matrix (Reg loc D) (Reg loc D) ℂ → ℂ → Matrix (Reg loc D) (Reg loc D) ℂ),
        (∀ i j, Differentiable ℂ fun z ↦ F ρ z i j) → ∀ (g : ℂ → ℂ), Differentiable ℂ g →
        ∀ w w', Differentiable ℂ fun z ↦ extendId hD (F ρ (g z)) w w' :=
      fun hD ρ F hF g hg w w' ↦ by
        simp only [extendId, of_apply]
        split_ifs
        · exact (hF _ _).comp hg
        · exact differentiable_const _
    have hmul : ∀ (M N : ℂ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
        (∀ i j, Differentiable ℂ fun z ↦ M z i j) → (∀ i j, Differentiable ℂ fun z ↦ N z i j) →
          ∀ i j, Differentiable ℂ fun z ↦ (M z * N z) i j := fun M N hM hN i j ↦ by
      simp only [mul_apply]
      exact Differentiable.fun_sum fun k _ ↦ (hM i k).mul (hN k j)
    have hc : Differentiable ℂ fun z : ℂ ↦ (a : ℂ) * z := differentiable_id.const_mul _
    have hc' : Differentiable ℂ fun z : ℂ ↦ (a : ℂ) * (1 - z) :=
      ((differentiable_const _).sub differentiable_id).const_mul _
    refine differentiable_euclidean.2 fun i ↦ ?_
    simp only [Gfun, PiLp.toLp_apply, mulVec, dotProduct]
    refine Differentiable.fun_sum fun j _ ↦ Differentiable.mul ?_ (differentiable_const _)
    refine hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_ i j
    exacts [hE _ σ' bracketPow (differentiable_bracketPow_apply σ') _ hc,
      hE _ _ hatPow (differentiable_hatPow_apply _) _ hc.neg,
      hE _ τ bracketPow (differentiable_bracketPow_apply τ) _ hc',
      hE _ _ hatPow (differentiable_hatPow_apply _) _ hc'.neg]
  · let K {D : Finset σ} (hD : D ⊆ Λ) {M : Matrix (Reg loc D) (Reg loc D) ℂ} (hM : M.IsHermitian)
        (c : ℝ) : ℝ := Real.exp ‖fun j ↦ c * Real.log ((isHermitian_extendId hD hM).eigenvalues j)‖
    refine ⟨K (Finset.union_subset hX hP) hσ.1 a * K hP (isHermitian_marg θ hP) (-a) *
      K (Finset.union_subset hX hU) hτ.1 a *
      K hU (isHermitian_marg θ hU) (-a) * ‖(WithLp.toLp 2 θ : EuclideanSpace ℂ (Reg loc Λ))‖,
      Set.forall_mem_image.2 fun z hz ↦ (l2_opNorm_mulVec _ (WithLp.toLp 2 θ)).trans ?_⟩
    obtain ⟨h0, h1⟩ : 0 ≤ z.re ∧ z.re ≤ 1 := hz
    gcongr
    refine norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le ?_ ?_) ?_) ?_
    exacts [norm_extendId_bracketPow_le _ hσ.1 a h0 h1 (by simp),
      norm_extendId_hatPow_le _ (isHermitian_marg θ hP) (-a) h0 h1 (by simp),
      norm_extendId_bracketPow_le _ hτ.1 a (sub_nonneg.2 h1) (sub_le_self _ h0) (by simp),
      norm_extendId_hatPow_le _ (isHermitian_marg θ hU) (-a) (sub_nonneg.2 h1) (sub_le_self _ h0)
        (by simp)]

/-- D5.6.1. Left boundary: `‖G(iu)‖ ≤ ‖τ_u^{[a]} ρ̂_U^{-a} θ‖`, and `τ_u = Q^{-iau} τ Q^{iau} > 0`,
`Tr τ_u = Tr τ`. -/
theorem step_5_6_1 : Step_5_6_1.{u, v} := by
  intro σ _ loc _ _ Λ P X U hP hX hU _ _ _ θ a σ' τ _ hσ hτ u
  set hT := Finset.union_subset hX hU
  have hq : ∀ w, extendId hU (hatPow (marg θ hU) w) = extendId hT (hatPow (Qmat θ hU X) w) :=
    fun w ↦ by rw [hatPow_Qmat, Arealaw.extendId_extendId]
  have hW := hatPow_mul_I_mem_unitary (Qmat θ hU X) (-(a * u))
  have hW' := hatPow_mul_I_mem_unitary (Qmat θ hU X) (a * u)
  have hsW : star (hatPow (Qmat θ hU X) ((-(a * u) : ℝ) * I)) =
      hatPow (Qmat θ hU X) ((a * u : ℝ) * I) := by
    rw [star_hatPow]; congr 1; simp
  have hsW' : star (hatPow (Qmat θ hU X) ((a * u : ℝ) * I)) =
      hatPow (Qmat θ hU X) ((-(a * u) : ℝ) * I) := by
    rw [star_hatPow]; congr 1; simp
  -- D5.6.1: `Q^{iau} τ_u^{[a]} = τ^{[a]} Q^{iau}`
  have hcomm : hatPow (Qmat θ hU X) ((a * u : ℝ) * I) * bracketPow (tauU θ hU X τ a u) a =
      bracketPow τ a * hatPow (Qmat θ hU X) ((a * u : ℝ) * I) := by
    have h := bracketPow_unitary_conj (ρ := τ) hW a
    rw [hsW] at h
    rw [tauU, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hsW', Unitary.mul_star_self_of_mem hW',
      Matrix.one_mul]
  -- D5.6.1: `τ^{[a-iau]} Q^{-a+iau} = τ^{[-iau]} Q^{iau} · τ_u^{[a]} Q^{-a}`
  have key : extendId hT (bracketPow τ (a * (1 - u * I))) *
      extendId hU (hatPow (marg θ hU) (-(a * (1 - u * I)))) =
      extendId hT (bracketPow τ ((-(a * u) : ℝ) * I)) *
        extendId hU (hatPow (marg θ hU) ((a * u : ℝ) * I)) *
        (extendId hT (bracketPow (tauU θ hU X τ a u) a) *
          extendId hU (hatPow (marg θ hU) ((-a : ℝ) : ℂ))) := by
    simp only [hq, ← extendId_mul]
    refine congrArg (extendId hT) ?_
    rw [Matrix.mul_assoc (bracketPow τ _), ← Matrix.mul_assoc (hatPow _ _), hcomm,
      Matrix.mul_assoc (bracketPow τ (a : ℂ)), ← Matrix.mul_assoc (bracketPow τ _),
      bracketPow_mul_bracketPow, hatPow_mul_hatPow,
      show -((a : ℂ) * (1 - u * I)) = ((a * u : ℝ) : ℂ) * I + ((-a : ℝ) : ℂ) by push_cast; ring,
      show (a : ℂ) * (1 - u * I) = ((-(a * u) : ℝ) : ℂ) * I + a by push_cast; ring]
  have hG : Gfun θ hP hX hU σ' τ a (u * I) = WithLp.toLp 2
      (extendId (Finset.union_subset hX hP) (bracketPow σ' (a * (u * I))) *ᵥ
      (extendId hP (hatPow (marg θ hP) (-(a * (u * I)))) *ᵥ
      (extendId hT (bracketPow τ ((-(a * u) : ℝ) * I)) *ᵥ
      (extendId hU (hatPow (marg θ hU) ((a * u : ℝ) * I)) *ᵥ
      ((extendId hT (bracketPow (tauU θ hU X τ a u) a) *
        extendId hU (hatPow (marg θ hU) ((-a : ℝ) : ℂ))) *ᵥ θ))))) := by
    rw [Gfun, Matrix.mul_assoc _ (extendId hT _), key]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · -- D5.6.1: drop the contractions `σ^{[iau]}`, `ρ̂_P^{-iau}`, `τ^{[-iau]}`, `Q^{iau}`
    rw [hG]
    exact (norm_mulVec_le (norm_extendId_bracketPow_le_one _ hσ.1 (by simp)) _).trans <|
      (norm_mulVec_le (norm_extendId_hatPow_le_one _ (isHermitian_marg θ hP) (by simp)) _).trans <|
      (norm_mulVec_le (norm_extendId_bracketPow_le_one _ hτ.1 (by simp)) _).trans <|
      norm_mulVec_le (norm_extendId_hatPow_le_one _ (isHermitian_marg θ hU) (by simp)) _
  · have hinj : Function.Injective (hatPow (Qmat θ hU X) ((a * u : ℝ) * I)).mulVec :=
      fun x y hxy ↦ by
        have h := congrArg (star (hatPow (Qmat θ hU X) ((a * u : ℝ) * I)) *ᵥ ·) hxy
        simpa only [mulVec_mulVec, Unitary.star_mul_self_of_mem hW', one_mulVec] using h
    have h := hτ.conjTranspose_mul_mul_same hinj
    rwa [← star_eq_conjTranspose, hsW'] at h
  · rw [tauU, trace_mul_cycle, ← hsW, Unitary.star_mul_self_of_mem hW, Matrix.one_mul]

/-- D5.10.1. Right boundary: `‖G(1+iu)‖ ≤ ‖σ_u^{[a]} ρ̂_P^{-a} θ_u‖` with
`σ_u = ρ̂_P^{iau} σ ρ̂_P^{-iau} ≥ 0`, `Tr σ_u = Tr σ`, and `θ_u = τ^{-iau} ρ̂_U^{iau} θ` a unit
vector with the `P`-marginal of `θ`. -/
theorem step_5_10_1 : Step_5_10_1.{u, v} := by
  intro σ _ loc _ _ Λ P X U hP hX hU hPX hPU _ θ hθ a σ' τ _ hσ hτ u
  set hT := Finset.union_subset hX hU
  set hS := Finset.union_subset hX hP
  have hPP : P ⊆ X ∪ P := Finset.subset_union_right
  have hp : ∀ w, extendId hP (hatPow (marg θ hP) w) =
      extendId hS (extendId hPP (hatPow (marg θ hP) w)) :=
    fun w ↦ (Arealaw.extendId_extendId _ _ _).symm
  have hW := Reg51.extendId_mem_unitary hPP (hatPow_mul_I_mem_unitary (marg θ hP) (a * u))
  have hsW : star (extendId hPP (hatPow (marg θ hP) ((a * u : ℝ) * I))) =
      extendId hPP (hatPow (marg θ hP) ((-(a * u) : ℝ) * I)) := by
    rw [star_eq_conjTranspose, ← extendId_conjTranspose, conjTranspose_hatPow]; congr 2; simp
  have hσu : sigmaU θ hP X σ' a u = extendId hPP (hatPow (marg θ hP) ((a * u : ℝ) * I)) * σ' *
      star (extendId hPP (hatPow (marg θ hP) ((a * u : ℝ) * I))) := by
    rw [sigmaU, hsW]
  -- D5.10.1: `ρ̂_P^{-iau} σ_u^{[a]} = σ^{[a]} ρ̂_P^{-iau}`
  have hcomm : extendId hPP (hatPow (marg θ hP) ((-(a * u) : ℝ) * I)) *
      bracketPow (sigmaU θ hP X σ' a u) a =
      bracketPow σ' a * extendId hPP (hatPow (marg θ hP) ((-(a * u) : ℝ) * I)) := by
    rw [hσu, bracketPow_unitary_conj hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hsW,
      Unitary.star_mul_self_of_mem hW, Matrix.one_mul]
  -- D5.10.1: `σ^{[a+iau]} ρ̂_P^{-a-iau} = σ^{[iau]} ρ̂_P^{-iau} · σ_u^{[a]} ρ̂_P^{-a}`
  have key : extendId hS (bracketPow σ' (a * (1 + u * I))) *
      extendId hP (hatPow (marg θ hP) (-(a * (1 + u * I)))) =
      extendId hS (bracketPow σ' ((a * u : ℝ) * I)) *
        extendId hP (hatPow (marg θ hP) ((-(a * u) : ℝ) * I)) *
        (extendId hS (bracketPow (sigmaU θ hP X σ' a u) a) *
          extendId hP (hatPow (marg θ hP) ((-a : ℝ) : ℂ))) := by
    simp only [hp, ← extendId_mul]
    refine congrArg (extendId hS) ?_
    rw [Matrix.mul_assoc (bracketPow σ' _), ← Matrix.mul_assoc (extendId hPP _), hcomm,
      Matrix.mul_assoc (bracketPow σ' (a : ℂ)), ← Matrix.mul_assoc (bracketPow σ' _),
      bracketPow_mul_bracketPow, ← extendId_mul, hatPow_mul_hatPow,
      show -((a : ℂ) * (1 + u * I)) = ((-(a * u) : ℝ) : ℂ) * I + ((-a : ℝ) : ℂ) by push_cast; ring,
      show (a : ℂ) * (1 + u * I) = ((a * u : ℝ) : ℂ) * I + a by push_cast; ring]
  -- D5.10.1: `τ^{[-iau]} ρ̂_U^{iau} θ = θ_u`
  have hθu : extendId hT (bracketPow τ (a * (1 - (1 + u * I)))) *ᵥ
      (extendId hU (hatPow (marg θ hU) (-(a * (1 - (1 + u * I))))) *ᵥ θ) =
      thetaU θ hX hU τ a u := by
    rw [thetaU, bracketPow_eq_hatPow hτ,
      show (a : ℂ) * (1 - (1 + u * I)) = ((-(a * u) : ℝ) : ℂ) * I by push_cast; ring,
      show -(((-(a * u) : ℝ) : ℂ) * I) = ((a * u : ℝ) : ℂ) * I by push_cast; ring]
  have hG : Gfun θ hP hX hU σ' τ a (1 + u * I) = WithLp.toLp 2
      (extendId hS (bracketPow σ' ((a * u : ℝ) * I)) *ᵥ
      (extendId hP (hatPow (marg θ hP) ((-(a * u) : ℝ) * I)) *ᵥ
      ((extendId hS (bracketPow (sigmaU θ hP X σ' a u) a) *
        extendId hP (hatPow (marg θ hP) ((-a : ℝ) : ℂ))) *ᵥ thetaU θ hX hU τ a u))) := by
    rw [Gfun, ← hθu, key]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  have hτW := hatPow_mul_I_mem_unitary τ (-(a * u))
  have hUW := hatPow_mul_I_mem_unitary (marg θ hU) (a * u)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- D5.10.1: drop the contractions `σ^{[iau]}`, `ρ̂_P^{-iau}`
    rw [hG]
    exact (norm_mulVec_le (norm_extendId_bracketPow_le_one _ hσ.1 (by simp)) _).trans
      (norm_mulVec_le (norm_extendId_hatPow_le_one _ (isHermitian_marg θ hP) (by simp)) _)
  · rw [hσu]; exact hσ.mul_mul_conjTranspose_same _
  · rw [hσu, trace_mul_cycle, Unitary.star_mul_self_of_mem hW, Matrix.one_mul]
  · rw [thetaU, star_mulVec_dotProduct (Reg51.extendId_mem_unitary _ hτW),
      star_mulVec_dotProduct (Reg51.extendId_mem_unitary _ hUW), hθ]
  · rw [thetaU, marg_extendId_unitary_mulVec _ hP
      (Finset.disjoint_union_left.2 ⟨hPX.symm, hPU.symm⟩) hτW,
      marg_extendId_unitary_mulVec _ hP hPU.symm hUW]

end AreaLaw
