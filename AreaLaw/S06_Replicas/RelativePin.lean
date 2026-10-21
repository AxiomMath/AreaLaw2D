import AreaLaw.S05_Conditional.Lemma51
import AreaLaw.S06_Replicas.Ported.RelativePinCommute
import AreaLaw.S06_Replicas.Setup

/-!
# §6 Lemma 6.3: the relative coherent pin (D6.10)

Digest `digest/06-replicas.md` D6.10, paper `paper/sections/05-replicas.tex` lines 480–587.
Lemma 5.1 enters as `AreaLaw.lemma_5_1` (§5). The sites are an arbitrary finite
type `V` with local dimensions `Fin (n v)`; a vector of the §2 encoding is a function on
`Reg (fun v => Fin (n v)) univ`, identified with `SiteConfig n` by `univEquiv`.
-/

namespace AreaLaw.Replicas

open MeasureTheory Matrix PermutationRepresentation Entropy TensorPower Arealaw
open OpenAI (pureState)
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

/-! ## Spectral powers as functional calculus -/

section Powers

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem hatPow_ofReal {ρ : Matrix X X ℂ} (hρ : ρ.IsHermitian) (r : ℝ) :
    hatPow ρ r = cfc (fun s : ℝ => if 0 < s then s ^ r else 1) ρ := by
  rw [hatPow, dif_pos hρ, hρ.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  congr 3
  funext i
  simp only [Function.comp_apply]
  split_ifs with h
  · rw [Real.rpow_def_of_pos h]; simp [Complex.ofReal_exp, mul_comm]
  · simp

/-- `ρ^t ρ̂^{-t} = 1 - Π_{ker ρ}` for `ρ ≥ 0`, `t > 0`. -/
theorem rpow_mul_hatPow_neg {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) {t : ℝ} (ht : 0 < t) :
    ρ ^ t * hatPow ρ ((-t : ℝ) : ℂ) = 1 - cfc (fun s : ℝ => if 0 < s then 0 else 1) ρ := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ ρ) := fun f =>
    (finite_real_spectrum (A := ρ)).continuousOn f
  rw [hatPow_ofReal hρ.isHermitian, CFC.rpow_eq_cfc_real hρ.nonneg,
    ← cfc_mul _ _ ρ (hfin _) (hfin _), ← cfc_const_one ℝ ρ (ha := hρ.isHermitian.isSelfAdjoint),
    ← cfc_sub (a := ρ) (fun _ : ℝ => (1 : ℝ)) _ (hfin _) (hfin _)]
  refine cfc_congr fun s hs => ?_
  rcases (spectrum_nonneg_of_nonneg hρ.nonneg hs).lt_or_eq with hpos | rfl
  · simp [hpos, ← Real.rpow_add hpos]
  · simp [Real.zero_rpow ht.ne']

theorem mul_cfc_kernel {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) :
    ρ * cfc (fun s : ℝ => if 0 < s then 0 else 1) ρ = 0 := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ ρ) := fun f =>
    (finite_real_spectrum (A := ρ)).continuousOn f
  conv_lhs => enter [1]; rw [← cfc_id ℝ ρ hρ.isHermitian.isSelfAdjoint]
  rw [← cfc_mul _ _ ρ (hfin _) (hfin _), ← cfc_zero ℝ ρ]
  refine cfc_congr fun s hs => ?_
  rcases (spectrum_nonneg_of_nonneg hρ.nonneg hs).lt_or_eq with hpos | rfl <;> simp [*]

end Powers

/-! ## Regional lifts in the §2 encoding -/

section Lift

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- The ported `localLift D K` is `extendId (D ⊆ univ) K` along `Reg _ univ ≃ SiteConfig n`. -/
theorem localLift_eq_extendId (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D K =
      (extendId (Finset.subset_univ D) K).submatrix univEquiv.symm univEquiv.symm := by
  ext a b
  simp only [submatrix_apply, extendId, of_apply, localLift_apply]
  refine if_congr ⟨fun h => funext fun i => h i (Finset.mem_sdiff.mp i.2).2, fun h v hv => ?_⟩
    rfl rfl
  exact congrFun h ⟨v, by simp [hv]⟩

theorem norm_toLp_comp_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (u : Y → ℂ) :
    ‖(WithLp.toLp 2 (u ∘ e) : EuclideanSpace ℂ X)‖ = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ Y)‖ := by
  simp only [EuclideanSpace.norm_eq, Function.comp_apply]
  rw [e.sum_comp (fun y => ‖u y‖ ^ 2)]


/-- If `θ` is a vector of the §2 encoding and `ρ_D` its marginal, then
`(ρ_D^t ρ̂_D^{-t} ⊗ 1) θ = θ`: `θ` lies in `supp ρ_D ⊗ 𝒱_{D^c}`. -/
theorem localLift_rpow_mul_hatPow_mulVec (D : Finset V)
    (θ : Reg (fun v => Fin (n v)) Finset.univ → ℂ) {t : ℝ} (ht : 0 < t) :
    localLift D ((marg θ (Finset.subset_univ D)) ^ t) *ᵥ
        (localLift D (hatPow (marg θ (Finset.subset_univ D)) ((-t : ℝ) : ℂ)) *ᵥ
          (θ ∘ univEquiv.symm)) = θ ∘ univEquiv.symm := by
  set ρ := marg θ (Finset.subset_univ D)
  set K := cfc (fun s : ℝ => if 0 < s then 0 else 1) ρ
  have hρ : ρ.PosSemidef := posSemidef_ptrace _ (posSemidef_vecMulVec_self_star θ)
  have hK : K.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (cfc_nonneg fun s _ => by split_ifs <;> norm_num)
  have hL : (localLift D K).PosSemidef := by
    rw [localLift_eq_extendId]
    exact (posSemidef_extendId _ hK).submatrix _
  have hzero : localLift D K *ᵥ (θ ∘ univEquiv.symm) = 0 := by
    refine (hL.dotProduct_mulVec_zero_iff _).mp ?_
    rw [localLift_eq_extendId, submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    rw [show star (θ ∘ univEquiv.symm) = star θ ∘ univEquiv.symm from rfl,
      comp_equiv_dotProduct_comp_equiv, dotProduct_mulVec, dotProduct_comm, ← trace_vecMulVec,
      ← vecMulVec_mul, ← (trace_ptrace_mul (Finset.subset_univ D) (vecMulVec θ (star θ)) K)]
    change (ρ * K).trace = 0
    rw [mul_cfc_kernel hρ, trace_zero]
  have hsub : localLift D (1 - K) = 1 - localLift D K := by
    rw [eq_sub_iff_add_eq, ← localLift_add, sub_add_cancel, localLift_one]
  rw [mulVec_mulVec, ← localLift_mul, rpow_mul_hatPow_neg hρ ht, hsub, sub_mulVec, hzero,
    one_mulVec, sub_zero]

end Lift

/-! ## D6.10 Lemma 6.3 -/

universe u

/-- D6.10 **Lemma 6.3** (relative coherent pin). `P, x, Y₀, F` partition `𝒱`, `Y = xY₀`,
`0 < t < 1/4`, `a = 2t`, `A_k = A_k(P, xY₀, F)`, `B_k = A_k(Px, Y₀, F)`,
`C_{x,k} = A_k^{-1/2} B_k A_k^{-1/2}`. Assume `a log(e dim x) ≤ c` (`c` of Lemma 5.1). Unit
`θ ∈ 𝒱`: `η_θ = S_θ(x|P) + S_θ(x|Y₀) = I_θ(x:F|P) = I_θ(x:F|Y₀) ≥ 0`. Polynomial bound uniform
in `θ`; on `𝒮_k`, `P_{θ,k} = |θ^{⊗k}⟩⟨θ^{⊗k}|`:
`C_{x,k} ≥ poly(k)^{-1} exp{ka[η_θ - C a^{1/4} log^C(e dim x)]} P_{θ,k}`.
Same for a move to `F` with the outer parts exchanged. No move (`x = ∅`): `C_{x,k} = I`,
gain `0`. -/
theorem lemma_6_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y₀ F : Finset V}, P ∪ x ∪ Y₀ ∪ F = Finset.univ → Disjoint P x → Disjoint P Y₀ →
        Disjoint P F → Disjoint x Y₀ → Disjoint x F → Disjoint Y₀ F →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → 2 * t * ℓ (Fintype.card (Reg (fun v => Fin (n v)) x)) ≤ c →
      ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : Reg (fun v => Fin (n v)) Finset.univ → ℂ)
        (hθ : star θ ⬝ᵥ θ = 1) (w : Replicas.Config (fun v => Fin (n v)) k → ℂ),
        ‖star (tensorVec k (θ ∘ univEquiv.symm)) ⬝ᵥ w‖ ^ 2 *
            Real.exp (k * (2 * t) * (condMutualInfo (pureState θ hθ).toSubState
              (Finset.subset_univ x) (Finset.subset_univ Y₀) (Finset.subset_univ F) -
              C * (2 * t) ^ (1 / 4 : ℝ) * ℓ (Fintype.card (Reg (fun v => Fin (n v)) x)) ^ 2)) ≤
          K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re := by
  obtain ⟨c, C₀, hc, hC₀, H⟩ := lemma_5_1.{u, 0}
  refine ⟨2 * C₀, c, by positivity, hc, ?_⟩
  intro V _ _ n _ P x Y₀ F hcov hPx hPY hPF hxY hxF hYF t ht0 ht1 hsmall
  have hmove : MoveParts P x Y₀ F := ⟨hPx, hPY, hPF, hxY, hxF, hYF⟩
  have σ₀ : SiteConfig n := fun v => ⟨0, Nat.pos_of_ne_zero (NeZero.ne (n v))⟩
  obtain ⟨Cc, hCc0, Hcomp⟩ := exists_l2_opNorm_compensator_le (n := n) ht0
  obtain ⟨Ω₁, _, P₁, hP₁, σ, hσ, hint₁, heq₁⟩ :=
    exists_replicaMetric_integral_localLift (n := n) ht0 ht1 (x ∪ P)
  obtain ⟨Ω₂, _, P₂, hP₂, τ, hτ, hint₂, heq₂⟩ :=
    exists_replicaMetric_integral_localLift (n := n) ht0 ht1 (x ∪ Y₀)
  refine ⟨1, 4 * Cc, one_pos, fun k θ hθ w => ?_⟩
  have hP := Finset.subset_univ P
  have hX := Finset.subset_univ x
  have hU := Finset.subset_univ Y₀
  have hF := Finset.subset_univ F
  set ℓx := ℓ (Fintype.card (Reg (fun v => Fin (n v)) x))
  set η := condMutualInfo (pureState θ hθ).toSubState hX hU hF
  set θs : SiteConfig n → ℂ := θ ∘ univEquiv.symm
  set z := tensorVec k θs
  set ρP := marg θ hP
  set ρY := marg θ hU
  have hρ : ∀ {D : Finset V} (hD : D ⊆ Finset.univ), (marg θ hD).PosSemidef ∧
      (marg θ hD).trace = 1 := fun hD =>
    ⟨posSemidef_ptrace _ (posSemidef_vecMulVec_self_star θ), by
      rw [marg, trace_ptrace, trace_vecMulVec, dotProduct_comm, hθ]⟩
  set DP := hatPow ρP ((-t : ℝ) : ℂ)
  set DY := hatPow ρY ((-t : ℝ) : ℂ)
  set v := localLift P DP *ᵥ (localLift Y₀ DY *ᵥ θs)
  set y := tensorVec k v
  set Wa := replicaMetric (fun v => Fin (n v)) t k (P ∪ x)
  set Wb := replicaMetric (fun v => Fin (n v)) t k (x ∪ Y₀)
  set Wp := replicaMetric (fun v => Fin (n v)) t k P
  set Wy := replicaMetric (fun v => Fin (n v)) t k Y₀
  set tP := tensorPow (k := k) (localLift P (ρP ^ t))
  set tY := tensorPow (k := k) (localLift Y₀ (ρY ^ t))
  set E := Real.exp (k * (-t * η + C₀ * (2 * t) ^ (5 / 4 : ℝ) * ℓx ^ 2))
  -- D6.10.5 the support identity `θ^{⊗k} = T_P T_{Y₀} (ρ̂_P^{-t} ρ̂_{Y₀}^{-t} θ)^{⊗k}`
  have hz : z = tP *ᵥ (tY *ᵥ y) := by
    have hcomm : localLift Y₀ (ρY ^ t) * localLift P DP = localLift P DP * localLift Y₀ (ρY ^ t) :=
      localLift_commute_of_disjoint _ _ hPY
    have h1 : localLift Y₀ (ρY ^ t) *ᵥ v = localLift P DP *ᵥ θs := by
      simp only [v]
      rw [mulVec_mulVec, hcomm, ← mulVec_mulVec, localLift_rpow_mul_hatPow_mulVec Y₀ θ ht0]
    have h2 : localLift P (ρP ^ t) *ᵥ (localLift P DP *ᵥ θs) = θs :=
      localLift_rpow_mul_hatPow_mulVec P θ ht0
    simp only [z, y, tP, tY, tensorPow_mulVec_tensorVec, h1, h2]
  -- D6.10.4 moving the compensators left
  have hM : moveWord n t k P x Y₀ *ᵥ z =
      (Wp⁻¹ * tP) *ᵥ ((Wy⁻¹ * tY) *ᵥ (Wa *ᵥ (Wb *ᵥ y))) := by
    have hPsub : P ⊆ P ∪ x := Finset.subset_union_left
    have hYx : Y₀ ⊆ x ∪ Y₀ := Finset.subset_union_right
    have hPxY : Disjoint P (x ∪ Y₀) := Finset.disjoint_union_right.mpr ⟨hPx, hPY⟩
    have hYPx : Disjoint Y₀ (P ∪ x) := Finset.disjoint_union_right.mpr ⟨hPY.symm, hxY.symm⟩
    have hWp := replicaMetric_inv_eq (n := n) ht0.le k P
    have hWy := replicaMetric_inv_eq (n := n) ht0.le k Y₀
    have LWa := isLabelFunctionOn_replicaMetric (ι := fun v => Fin (n v)) (k := k) t (P ∪ x)
    have LWb := isLabelFunctionOn_replicaMetric (ι := fun v => Fin (n v)) (k := k) t (x ∪ Y₀)
    have LWp := isLabelFunctionOn_replicaMetric_inv (ι := fun v => Fin (n v)) (k := k) ht0.le P
    have LWy := isLabelFunctionOn_replicaMetric_inv (ι := fun v => Fin (n v)) (k := k) ht0.le Y₀
    have c1 : Commute Wy⁻¹ tP := by
      rw [hWy]
      exact commute_labelObservable_tensorPow_of_disjoint hPY σ₀ _ _
    have cap : Commute Wa (Wp⁻¹ * tP) :=
      ((LWp.commute_of_subset LWa hPsub).symm).mul_right
        (commute_labelObservable_tensorPow_of_subset hPsub σ₀ _ _)
    have cbp : Commute Wb (Wp⁻¹ * tP) :=
      ((LWp.commute_of_disjoint LWb hPxY).symm).mul_right
        (commute_labelObservable_tensorPow_of_disjoint hPxY σ₀ _ _)
    have cay : Commute Wa (Wy⁻¹ * tY) :=
      ((LWy.commute_of_disjoint LWa hYPx).symm).mul_right
        (commute_labelObservable_tensorPow_of_disjoint hYPx σ₀ _ _)
    have cby : Commute Wb (Wy⁻¹ * tY) :=
      ((LWy.commute_of_subset LWb hYx).symm).mul_right
        (commute_labelObservable_tensorPow_of_subset hYx σ₀ _ _)
    have hmat : moveWord n t k P x Y₀ * tP * tY = (Wp⁻¹ * tP) * (Wy⁻¹ * tY) * (Wa * Wb) := by
      have e1 : moveWord n t k P x Y₀ * tP * tY = Wa * Wb * ((Wp⁻¹ * tP) * (Wy⁻¹ * tY)) := by
        simp only [moveWord, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Wy⁻¹ tP tY, c1.eq, Matrix.mul_assoc]
      rw [e1, ((cap.mul_left cbp).mul_right (cay.mul_left cby)).eq]
    rw [hz, mulVec_mulVec, mulVec_mulVec, hmat]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  -- D6.10.6–D6.10.9 the averaged numerators and the one-copy word (Lemma 5.1)
  have hWW : ‖(EuclideanSpace.equiv _ ℂ).symm (Wa *ᵥ (Wb *ᵥ y))‖ ≤ E := by
    have hWa : Wa = Matrix.of fun a b =>
        ∫ ω, tensorPow (k := k) (localLift (x ∪ P) (σ ω ^ t)) a b ∂P₁ := by
      ext a b
      rw [of_apply, ← heq₁ k a b, Finset.union_comm x P]
    have hWb : Wb = Matrix.of fun a b =>
        ∫ ω, tensorPow (k := k) (localLift (x ∪ Y₀) (τ ω ^ t)) a b ∂P₂ := by
      ext a b
      exact heq₂ k a b
    rw [hWa]
    refine norm_of_integral_mulVec_le _ (hint₁ k) _ ?_
    filter_upwards [hσ] with ω hω
    rw [mulVec_mulVec, hWb, mul_of_integral _ _ (hint₂ k)]
    refine norm_of_integral_mulVec_le _ (fun a b => ?_) y ?_
    · simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun c _ => (hint₂ k c b).const_mul _
    filter_upwards [hτ] with ω' hω'
    rw [← tensorPow_mul, tensorPow_mulVec_tensorVec, norm_tensorVec]
    have hcomm : localLift (x ∪ Y₀) (τ ω' ^ t) * localLift P DP =
        localLift P DP * localLift (x ∪ Y₀) (τ ω' ^ t) :=
      localLift_commute_of_disjoint _ _ (Finset.disjoint_union_right.mpr ⟨hPx, hPY⟩)
    have hop : (localLift (x ∪ P) (σ ω ^ t) * localLift (x ∪ Y₀) (τ ω' ^ t)) *ᵥ v =
        ((extendId (Finset.union_subset hX hP) (σ ω ^ t) * extendId hP DP *
          extendId (Finset.union_subset hX hU) (τ ω' ^ t) * extendId hU DY) *ᵥ θ) ∘
          univEquiv.symm := by
      simp only [v, mulVec_mulVec, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (localLift (x ∪ Y₀) _), hcomm]
      simp only [localLift_eq_extendId, submatrix_mul_equiv, Matrix.mul_assoc]
      rw [submatrix_mulVec_equiv]
      simp only [θs, Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self,
        Function.comp_id]
    have hℓ : 0 < ℓx := by
      have hd : (1 : ℝ) ≤ Fintype.card (Reg (fun v => Fin (n v)) x) := mod_cast Fintype.card_pos
      exact Real.log_pos (by nlinarith [Real.exp_one_gt_d9])
    have hone := H V (fun v => Fin (n v)) Finset.univ P x Y₀ F hP hX hU hF hcov.symm hPx hPY
      hPF hxY hxF hYF θ hθ (2 * t) (by positivity) hsmall (σ ω) (τ ω') hω.1.posSemidef hω.2
      hω'.1.posSemidef hω'.2
    rw [show 2 * t / 2 = t by ring, bracketPow_ofReal hω.1.posSemidef ht0.ne',
      bracketPow_ofReal hω'.1.posSemidef ht0.ne'] at hone
    calc ‖(EuclideanSpace.equiv _ ℂ).symm
          ((localLift (x ∪ P) (σ ω ^ t) * localLift (x ∪ Y₀) (τ ω' ^ t)) *ᵥ v)‖ ^ k
        ≤ Real.exp (-t * η + C₀ * (2 * t) ^ (5 / 4 : ℝ) * ℓx ^ 2) ^ k := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ k
          rw [hop]
          change ‖(WithLp.toLp 2 (_ ∘ _) : EuclideanSpace ℂ (SiteConfig n))‖ ≤ _
          rw [← Complex.ofReal_neg] at hone
          rwa [norm_toLp_comp_equiv]
      _ = E := by rw [← Real.exp_nat_mul]
  -- D6.10.3 the compensators
  have hTP : ‖Wp⁻¹ * tP‖ ≤ ((k : ℝ) + 2) ^ Cc := Hcomp k P ρP (hρ hP).1 (hρ hP).2
  have hTY : ‖Wy⁻¹ * tY‖ ≤ ((k : ℝ) + 2) ^ Cc := Hcomp k Y₀ ρY (hρ hU).1 (hρ hU).2
  have hMz : ‖(EuclideanSpace.equiv _ ℂ).symm (moveWord n t k P x Y₀ *ᵥ z)‖ ≤
      ((k : ℝ) + 2) ^ Cc * (((k : ℝ) + 2) ^ Cc * E) := by
    rw [hM]
    exact (norm_mulVec_le _ _).trans (mul_le_mul hTP ((norm_mulVec_le _ _).trans
      (mul_le_mul hTY hWW (norm_nonneg _) (by positivity))) (norm_nonneg _) (by positivity))
  -- D6.10.1–D6.10.2 inverse Cauchy–Schwarz and the norm identity
  have key := norm_star_dotProduct_sq_le_moveWord ht0.le k hmove z w
  have hre : 0 ≤ (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re :=
    (posDef_relativeMetric_and_inv ht0.le k hmove).1.posSemidef.re_dotProduct_nonneg w
  set X := Real.exp (k * (2 * t) * (η - 2 * C₀ * (2 * t) ^ (1 / 4 : ℝ) * ℓx ^ 2))
  have hX : 0 ≤ X := (Real.exp_pos _).le
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hE2 : E ^ 2 * X = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff,
      show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add h2t, Real.rpow_one]
    ring
  have hpow : (((k : ℝ) + 2) ^ Cc * (((k : ℝ) + 2) ^ Cc * E)) ^ 2 =
      ((k : ℝ) + 2) ^ (4 * Cc) * E ^ 2 := by
    rw [show (4 * Cc) = Cc * ((4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul_natCast hk.le]
    ring
  -- D6.10.9
  calc ‖star z ⬝ᵥ w‖ ^ 2 * X
      ≤ (‖(EuclideanSpace.equiv _ ℂ).symm (moveWord n t k P x Y₀ *ᵥ z)‖ ^ 2 *
          (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re) * X :=
        mul_le_mul_of_nonneg_right key hX
    _ ≤ ((((k : ℝ) + 2) ^ Cc * (((k : ℝ) + 2) ^ Cc * E)) ^ 2 *
          (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re) * X := by gcongr
    _ = 1 * ((k : ℝ) + 2) ^ (4 * Cc) *
          (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re := by
      rw [hpow]
      linear_combination (((k : ℝ) + 2) ^ (4 * Cc) *
        (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re) * hE2

/-! ## D6.10.10 Exchange and the empty move -/

section Exchange

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- `A_k(P, Y, F) = A_k(F, Y, P)`. -/
theorem leafMetric_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V} (h : Disjoint P F) :
    leafMetric n t k P Y F = leafMetric n t k F Y P := by
  rw [leafMetric, leafMetric, leafRoot, leafRoot,
    ((isLabelFunctionOn_replicaMetric_inv (ι := fun v => Fin (n v)) (k := k) ht
      P).commute_of_disjoint
        (isLabelFunctionOn_replicaMetric_inv (ι := fun v => Fin (n v)) (k := k) ht F) h).eq]

/-- D6.10.10, no move: for `x = ∅`, `B_k = A_k` and `C_{x,k} = I`. -/
theorem lemma_6_3_empty {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y₀ F : Finset V} (hPY : Disjoint P Y₀)
    (hPF : Disjoint P F) (hYF : Disjoint Y₀ F) : relativeMetric n t k P ∅ Y₀ F = 1 := by
  rw [relativeMetric_eq ht k ⟨Finset.disjoint_empty_right _, hPY, hPF,
    Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, hYF⟩]
  simp only [Finset.empty_union, Finset.union_empty]
  have hu : IsUnit (leafRoot n t k P Y₀ F).det :=
    (posDef_leafRoot ht k hPY hPF hYF).det_pos.ne'.isUnit
  rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, mul_nonsing_inv _ hu]

end Exchange

/-- D6.10.10 **Lemma 6.3**, move to `F` (outer parts exchanged): with
`A_k = A_k(P, xY₀, F)` and `B_k = A_k(P, Y₀, xF)`,
`A_k^{-1/2} B_k A_k^{-1/2} ≥ poly(k)^{-1} exp{ka[η_θ - C a^{1/4} log^C(e dim x)]} P_{θ,k}`, now
with `η_θ = S_θ(x|F) + S_θ(x|Y₀) = I_θ(x:P|Y₀)`. -/
theorem lemma_6_3_exchange :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y₀ F : Finset V}, P ∪ x ∪ Y₀ ∪ F = Finset.univ → Disjoint P x → Disjoint P Y₀ →
        Disjoint P F → Disjoint x Y₀ → Disjoint x F → Disjoint Y₀ F →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → 2 * t * ℓ (Fintype.card (Reg (fun v => Fin (n v)) x)) ≤ c →
      ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : Reg (fun v => Fin (n v)) Finset.univ → ℂ)
        (hθ : star θ ⬝ᵥ θ = 1) (w : Replicas.Config (fun v => Fin (n v)) k → ℂ),
        ‖star (tensorVec k (θ ∘ univEquiv.symm)) ⬝ᵥ w‖ ^ 2 *
            Real.exp (k * (2 * t) * (condMutualInfo (pureState θ hθ).toSubState
              (Finset.subset_univ x) (Finset.subset_univ Y₀) (Finset.subset_univ P) -
              C * (2 * t) ^ (1 / 4 : ℝ) * ℓ (Fintype.card (Reg (fun v => Fin (n v)) x)) ^ 2)) ≤
          K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ (((CFC.sqrt (leafMetric n t k P (x ∪ Y₀) F))⁻¹ *
            leafMetric n t k P Y₀ (x ∪ F) * (CFC.sqrt (leafMetric n t k P (x ∪ Y₀) F))⁻¹) *ᵥ
              w)).re := by
  obtain ⟨C, c, hC, hc, H⟩ := lemma_6_3
  refine ⟨C, c, hC, hc, ?_⟩
  intro V _ _ n _ P x Y₀ F hcov hPx hPY hPF hxY hxF hYF t ht0 ht1 hsmall
  obtain ⟨K, N, hK, H'⟩ := H (P := F) (x := x) (Y₀ := Y₀) (F := P)
    (by rw [← hcov]; ext; simp only [Finset.mem_union]; tauto) hxF.symm hYF.symm hPF.symm hxY
    hPx.symm hPY.symm ht0 ht1 hsmall
  refine ⟨K, N, hK, fun k θ hθ w => ?_⟩
  have hA : leafMetric n t k F (x ∪ Y₀) P = leafMetric n t k P (x ∪ Y₀) F :=
    leafMetric_comm ht0.le k hPF.symm
  have hB : leafMetric n t k (F ∪ x) Y₀ P = leafMetric n t k P Y₀ (x ∪ F) := by
    rw [leafMetric_comm ht0.le k (Finset.disjoint_union_left.mpr ⟨hPF.symm, hPx.symm⟩),
      Finset.union_comm]
  have := H' k θ hθ w
  rwa [relativeMetric, hA, hB] at this

end AreaLaw.Replicas
