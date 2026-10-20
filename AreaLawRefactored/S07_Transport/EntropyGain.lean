import AreaLawRefactored.S07_Transport.ExactDerivative
import AreaLawRefactored.S07_Transport.LogJensen
import AreaLawForMathlib.Analysis.Matrix.CommutingProductLog

/-!
# §7.4 Proposition 7.4 (b): the entropy gain

Digest `digest/07-transport.md` D7.17–D7.20, paper `paper/sections/06-transport.tex` 487–572.
No geometry: an arbitrary finite site type `V`, arbitrary `k`. Operators on `𝒮_k` are written on
the whole tensor space as `Π_k X + (1 − Π_k)` (the band metric D7.8).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Set Filter Asymptotics Entropy PermutationRepresentation Arealaw

namespace AreaLaw.Transport

universe u

/-! ## Coherent projectors and coherent integrals -/

section Coherent

variable {J : Type*} [Fintype J] [DecidableEq J] {ι : J → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {k : ℕ}

theorem projS_mul_P (θ : ((f : J) → ι f) → ℂ) :
    Replicas.projS ι k * Replicas.P ι k θ = Replicas.P ι k θ := by
  rw [Replicas.P, TensorPower.coherentProj, mul_vecMulVec, Replicas.projS_eq,
    symProj_mulVec_of_mem _ (TensorPower.tensorVec_mem_symmetricSubspace θ)]

theorem P_mul_projS (θ : ((f : J) → ι f) → ℂ) :
    Replicas.P ι k θ * Replicas.projS ι k = Replicas.P ι k θ := by
  have h := congrArg conjTranspose (projS_mul_P (k := k) θ)
  have hH : (Replicas.projS ι k)ᴴ = Replicas.projS ι k :=
    (isStarProjection_projS (ι := ι) (k := k)).isSelfAdjoint.star_eq
  rwa [conjTranspose_mul, (posSemidef_P θ).isHermitian.eq, hH] at h

omit [∀ f, DecidableEq (ι f)] in
/-- `P_{θ,k}` is an orthogonal projection for a unit `θ`. -/
theorem isStarProjection_P {θ : ((f : J) → ι f) → ℂ} (hθ : θ ∈ TensorPower.unitSphere) :
    IsStarProjection (Replicas.P ι k θ) := by
  have h1 : star (TensorPower.tensorVec k θ) ⬝ᵥ TensorPower.tensorVec k θ = 1 := by
    have h := TensorPower.trace_coherentProj (k := k) θ
    rw [TensorPower.coherentProj, trace_vecMulVec] at h
    rw [dotProduct_comm, h, show θ ⬝ᵥ star θ = 1 from hθ, one_pow]
  refine ⟨?_, (posSemidef_P θ).isHermitian⟩
  change Replicas.P ι k θ * Replicas.P ι k θ = Replicas.P ι k θ
  rw [Replicas.P, TensorPower.coherentProj, vecMulVec_mul_vecMulVec, h1, one_smul]

variable [∀ f, Nonempty (ι f)]

variable (ι k) in
theorem one_le_D : (1 : ℝ) ≤ Replicas.D ι k := by
  have h : Replicas.D ι k ≠ 0 := by exact_mod_cast D_ne_zero ι k
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem Q_const_mul (c : ℝ) (f : Replicas.Sphere ι → ℝ) :
    Q ι k (fun θ => c * f θ) = (c : ℂ) • Q ι k f := by
  rw [Q, Q, smul_comm]
  congr 1
  ext x y
  simp only [of_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  exact integral_const_mul _ _

/-- D7.20.1. Integrating a pointwise pin `b e^{φ(θ)} P_{θ,k} ≤ X` against `dθ`, for `X` commuting
with `Π_k` and `≥ 1` on `𝒮_k^⊥`: `(b / D_k) (𝒬_k(e^φ) + (1 − Π_k)) ≤ X`. -/
theorem smul_Q_add_le_of_pin {X : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ}
    (hX : Commute (Replicas.projS ι k) X) (hX1 : 1 - Replicas.projS ι k ≤ X) {b : ℝ}
    (hb1 : b ≤ 1) {φ : Replicas.Sphere ι → ℝ} (hφ : Continuous φ)
    (hpin : ∀ θ : Replicas.Sphere ι, (b * Real.exp (φ θ)) • Replicas.P ι k θ.1 ≤ X) :
    (b / Replicas.D ι k) • (Q ι k (fun θ => Real.exp (φ θ)) + (1 - Replicas.projS ι k)) ≤ X := by
  have hD := one_le_D ι k
  have hD0 : (Replicas.D ι k : ℂ) ≠ 0 := D_ne_zero ι k
  set d := b / (Replicas.D ι k : ℝ) with hd_def
  have hd1 : d ≤ 1 := (div_le_one (by linarith)).mpr (hb1.trans hD)
  have hPS := isStarProjection_projS (ι := ι) (k := k)
  have hf : Continuous fun θ : Replicas.Sphere ι => Real.exp (φ θ) := Real.continuous_exp.comp hφ
  have hr : Continuous fun θ : Replicas.Sphere ι => b * Real.exp (φ θ) := continuous_const.mul hf
  set M : Replicas.Sphere ι → Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
    fun θ => X - ((b * Real.exp (φ θ)) • Replicas.P ι k θ.1 + d • (1 - Replicas.projS ι k))
    with hM_def
  -- pointwise: `X - b e^{φ(θ)} P_{θ,k} - d (1 - Π_k) ≥ 0`, split along `Π_k`
  have hpt : ∀ θ, (M θ).PosSemidef := fun θ => by
    have hY : Replicas.projS ι k * ((b * Real.exp (φ θ)) • Replicas.P ι k θ.1) *
        Replicas.projS ι k = (b * Real.exp (φ θ)) • Replicas.P ι k θ.1 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, projS_mul_P, P_mul_projS]
    have hZ : (1 - Replicas.projS ι k) * (d • (1 - Replicas.projS ι k)) *
        (1 - Replicas.projS ι k) = d • (1 - Replicas.projS ι k) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hPS.one_sub.isIdempotentElem.eq,
        hPS.one_sub.isIdempotentElem.eq]
    have hZX : d • (1 - Replicas.projS ι k) ≤ X :=
      (smul_le_of_le_one_left hPS.one_sub.nonneg hd1).trans hX1
    exact Matrix.le_iff.mp (add_le_of_isStarProjection hPS hX hY hZ (hpin θ) hZX)
  have hent : ∀ θ x y, M θ x y = X x y - ((b : ℂ) * ((Real.exp (φ θ) : ℂ) *
      Replicas.P ι k θ.1 x y) + (d : ℂ) * (1 - Replicas.projS ι k) x y) := by
    intro θ x y
    simp only [hM_def, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.ofReal_mul]
    ring
  have hi : ∀ x y, Integrable (fun θ : Replicas.Sphere ι =>
      (Real.exp (φ θ) : ℂ) * Replicas.P ι k θ.1 x y) (Replicas.dθ ι) := fun x y => by
    simpa only [Matrix.smul_apply, smul_eq_mul] using integrable_Q_apply (k := k) hf x y
  have hMi : ∀ x y, Integrable (fun θ => M θ x y) (Replicas.dθ ι) := fun x y => by
    simp only [hent]
    exact (integrable_const _).sub (((hi x y).const_mul _).add (integrable_const _))
  have hpsd := PosSemidef.of_integral (M := M) hMi hpt
  -- `∫ (X - b e^φ P_θ - d (1 - Π_k)) dθ = X - (b / D_k) (𝒬_k(e^φ) + (1 - Π_k))`
  have heq : (of fun x y => ∫ θ, M θ x y ∂(Replicas.dθ ι)) =
      X - d • (Q ι k (fun θ => Real.exp (φ θ)) + (1 - Replicas.projS ι k)) := by
    ext x y
    simp only [of_apply, hent]
    have hg : Integrable (fun θ : Replicas.Sphere ι => (b : ℂ) * ((Real.exp (φ θ) : ℂ) *
        Replicas.P ι k θ.1 x y) + (d : ℂ) * (1 - Replicas.projS ι k) x y) (Replicas.dθ ι) :=
      ((hi x y).const_mul _).add (integrable_const _)
    rw [integral_sub (integrable_const _) hg,
      integral_add ((hi x y).const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul, Q, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.add_apply, of_apply, smul_eq_mul, Complex.real_smul]
    rw [hd_def]
    push_cast
    field_simp
  rw [heq] at hpsd
  exact Matrix.le_iff.mpr hpsd

end Coherent

/-! ## The band relative metrics -/

/-- `log(e dim x) ≥ 1`. -/
theorem one_le_logDim {V : Type*} [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
    (x : Finset V) : 1 ≤ logDim (n := n) x := by
  have hd : (1 : ℝ) ≤ Fintype.card (Reg (fun v => Fin (n v)) x) := by
    exact_mod_cast Fintype.card_pos
  change 1 ≤ Real.log (Real.exp 1 * Fintype.card (Reg (fun v => Fin (n v)) x))
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hd]

namespace Round

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {K : ℕ} {H : Type*}
  {C : H → Type*} (R : Round V K H C)

variable (n) in
/-- D7.17. `B_{h,g}`, the conditional choice tree at `h` of the new metrics of band `g`. -/
noncomputable def bandChoiceRoot (t : ℝ) (k : ℕ) (h : H) (g : Fin K) :
    Matrix (Config n k) (Config n k) ℂ :=
  (R.choiceTree h).eval fun c => bandMetric n t k (R.new h c g)

variable (n) in
/-- D7.17. `C_{h,g} = A_{h,g}^{-1/2} B_{h,g} A_{h,g}^{-1/2}`. -/
noncomputable def bandRelRatio (t : ℝ) (k : ℕ) (h : H) (g : Fin K) :
    Matrix (Config n k) (Config n k) ℂ :=
  bandMetric n t k (R.old h g) ^ (-(1 / 2) : ℝ) * R.bandChoiceRoot n t k h g *
    bandMetric n t k (R.old h g) ^ (-(1 / 2) : ℝ)

variable (n) in
/-- D7.17. The single-move relative metric `A_{h,g}^{-1/2} A_{h,c,g} A_{h,g}^{-1/2}`. -/
noncomputable def moveRelMetric (t : ℝ) (k : ℕ) (h : H) (c : C h) (g : Fin K) :
    Matrix (Config n k) (Config n k) ℂ :=
  bandMetric n t k (R.old h g) ^ (-(1 / 2) : ℝ) * bandMetric n t k (R.new h c g) *
    bandMetric n t k (R.old h g) ^ (-(1 / 2) : ℝ)

variable [DecidableEq H] [∀ h, DecidableEq (C h)] [∀ v, NeZero (n v)]

theorem posDef_old (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H) (g : Fin K) :
    (bandMetric n t k (R.old h g)).PosDef :=
  posDef_bandMetric (n := n) (hR.old_isPartition h g) ht k

theorem posDef_new (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H) (c : C h)
    (g : Fin K) : (bandMetric n t k (R.new h c g)).PosDef :=
  posDef_bandMetric (n := n) (R.isPartition_leafPart hR ⟨h, some c⟩ g) ht k

theorem posDef_moveRelMetric (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (c : C h) (g : Fin K) : (R.moveRelMetric n t k h c g).PosDef :=
  (R.posDef_old (n := n) hR ht k h g).whiten (R.posDef_new (n := n) hR ht k h c g)

/-- D7.17.3. Congruence (Lemma 7.1 (1), `S = A_{h,g}^{-1/2}`) in the choice tree:
`C_{h,g} = 𝒯_choice(A_{h,g}^{-1/2} A_{h,c,g} A_{h,g}^{-1/2} : c)`. -/
theorem bandRelRatio_eq_eval (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) :
    R.bandRelRatio n t k h g = (R.choiceTree h).eval fun c => R.moveRelMetric n t k h c g := by
  have hA := R.posDef_old (n := n) hR ht k h g
  have := lemma_7_1_1 (fun c => R.posDef_new (n := n) hR ht k h c g) (hA.rpow (-(1 / 2) : ℝ)).isUnit
    (R.choiceTree h)
  simp only [hA.star_rpow] at this
  exact this.symm

theorem posDef_bandRelRatio (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) : (R.bandRelRatio n t k h g).PosDef := by
  rw [R.bandRelRatio_eq_eval (n := n) hR ht]
  exact MeanTree.posDef_eval (fun c => R.posDef_moveRelMetric (n := n) hR ht k h c g) _

theorem commute_Pi_bandRelRatio (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) : Commute (Pi n k) (R.bandRelRatio n t k h g) := by
  have hA := R.posDef_old (n := n) hR ht k h g
  have hr : Commute (Pi n k) (bandMetric n t k (R.old h g) ^ (-(1 / 2) : ℝ)) :=
    (hA.commute_rpow_left (commute_Pi_bandMetric t k _).symm _).symm
  exact (hr.mul_right (MeanTree.commute_eval_right (fun c => R.posDef_new (n := n) hR ht k h c g)
    (fun c => commute_Pi_bandMetric t k _) _)).mul_right hr

/-- On `𝒮_k^⊥` every relative metric is the identity: `1 − Π_k ≤ C_{h,g}`. -/
theorem one_sub_Pi_le_bandRelRatio (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) [Finite (C h)] : 1 - Pi n k ≤ R.bandRelRatio n t k h g := by
  have := Fintype.ofFinite (C h)
  have hPS : IsStarProjection (1 - Pi n k) := by
    rw [Pi_eq_projS]; exact isStarProjection_projS.one_sub
  have hle : ∀ c, (1 : ℝ) • (1 - Pi n k) ≤ R.moveRelMetric n t k h c g := fun c => by
    have hπ := hR.old_isPartition h g
    have hA := posDef_A (n := n) hπ ht k
    have hB := posDef_A (n := n) (R.isPartition_leafPart hR ⟨h, some c⟩ g) ht k
    have hPA := commute_Pi_A (n := n) t k (R.old h g).P (R.old h g).Y (R.old h g).F
    have hPB := commute_Pi_A (n := n) t k (R.new h c g).P (R.new h c g).Y (R.new h c g).F
    have hW := hA.whiten_proj_mul_add_one_sub (isHermitian_Pi k) (Pi_mul_Pi k) hPA hPB
    unfold moveRelMetric
    unfold bandMetric
    rw [hW, one_smul, le_add_iff_nonneg_left]
    have hPr : Commute (Pi n k) (Replicas.A (fun v => Fin (n v)) t k (R.old h g).P
        (R.old h g).Y (R.old h g).F ^ (-(1 / 2) : ℝ)) := (hA.commute_rpow_left hPA.symm _).symm
    have hPW := (hPr.mul_right hPB).mul_right hPr
    have e : ∀ W : Matrix (Config n k) (Config n k) ℂ, Commute (Pi n k) W →
        Pi n k * W = (Pi n k)ᴴ * W * Pi n k := fun W hW => by
      rw [(isHermitian_Pi k).eq, Matrix.mul_assoc, ← hW.eq, ← Matrix.mul_assoc, Pi_mul_Pi]
    rw [e _ hPW]
    exact Matrix.nonneg_iff_posSemidef.mpr
      ((hA.whiten hB).posSemidef.conjTranspose_mul_mul_same _)
  have key := lemma_7_1_5 (fun c => R.posDef_moveRelMetric (n := n) hR ht k h c g) hPS
    (c := fun _ => 1) (fun _ => one_pos) hle (R.choiceTree h)
  simp only [Real.one_rpow, Finset.prod_const_one, one_smul] at key
  rw [R.bandRelRatio_eq_eval (n := n) hR ht]
  exact key

/-- D7.17 Step `transport:relative-factorization`. `𝓜 = ∏_g 𝓜_g`, `𝓜_g` the tree evaluated on
band-`g` inputs. With `B_{h,g}` the conditional tree of new metrics in band `g`:
`C_h = ∏_g C_{h,g}`, `C_{h,g} = A_{h,g}^{-1/2} B_{h,g} A_{h,g}^{-1/2}`,
`log C_h = ∑_g log C_{h,g}`. `C_{h,g}` is the conditional choice tree of the single-move relative
metrics `A_{h,g}^{-1/2} A_{h,c,g} A_{h,g}^{-1/2}`. -/
theorem step_7_17 (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) :
    (∀ p : I, R.root n t k p = (List.ofFn fun g =>
        (R.tree p).eval fun j => bandMetric n t k (R.leafPart j g)).prod ∧
      ∀ g g', g ≠ g' → Commute ((R.tree p).eval fun j => bandMetric n t k (R.leafPart j g))
        ((R.tree p).eval fun j => bandMetric n t k (R.leafPart j g'))) ∧
    ∀ h, R.relRatio n t k h = (List.ofFn fun g => R.bandRelRatio n t k h g).prod ∧
      CFC.log (R.relRatio n t k h) = ∑ g, CFC.log (R.bandRelRatio n t k h g) ∧
      ∀ g, R.bandRelRatio n t k h g =
        (R.choiceTree h).eval fun c => R.moveRelMetric n t k h c g := by
  have hD : ∀ j g, (bandMetric n t k (R.leafPart j g)).PosDef := fun j g =>
    posDef_bandMetric (n := n) (R.isPartition_leafPart hR j g) ht k
  refine ⟨fun p => ?_, fun h => ?_⟩
  -- D7.17.1: Lemma 7.1 (6) applied to the terminal tree, whose inputs factor by band
  · have hroot : R.root n t k p = (R.tree p).eval (R.input n t k) := by
      rw [root, Set.projIcc_val]
    have hin : R.input n t k =
        fun j => (List.ofFn fun g => bandMetric n t k (R.leafPart j g)).prod :=
      funext (R.input_eq_prod n t k)
    rw [hroot, hin]
    exact lemma_7_1_6 hD hcomm (R.tree p)
  · have hA : ∀ g, (bandMetric n t k (R.old h g)).PosDef := fun g =>
      R.posDef_old (n := n) hR ht k h g
    have hN : ∀ c g, (bandMetric n t k (R.new h c g)).PosDef := fun c g =>
      R.posDef_new (n := n) hR ht k h c g
    have hNN : ∀ c c' g g', g ≠ g' → Commute (bandMetric n t k (R.new h c g))
        (bandMetric n t k (R.new h c' g')) := fun c c' g g' hg =>
      hcomm ⟨h, some c⟩ ⟨h, some c'⟩ g g' hg
    have hAA : ∀ g g', g ≠ g' → Commute (bandMetric n t k (R.old h g))
        (bandMetric n t k (R.old h g')) := fun g g' hg => hcomm ⟨h, none⟩ ⟨h, none⟩ g g' hg
    have hAB : ∀ g g', g ≠ g' → Commute (bandMetric n t k (R.old h g))
        (R.bandChoiceRoot n t k h g') := fun g g' hg =>
      MeanTree.commute_eval_right (fun c => hN c g')
        (fun c => hcomm ⟨h, none⟩ ⟨h, some c⟩ g g' hg) _
    -- D7.17.1: Lemma 7.1 (6) applied to the choice tree, `B_h = ∏_g B_{h,g}`, commuting factors
    obtain ⟨hB, hBB⟩ := lemma_7_1_6 (D := fun c g => bandMetric n t k (R.new h c g))
      (fun c g => hN c g) hNN (R.choiceTree h)
    have hB' : R.choiceRoot n t k h = (List.ofFn fun g => R.bandChoiceRoot n t k h g).prod := hB
    have hold : R.oldMetric n t k h = (List.ofFn fun g => bandMetric n t k (R.old h g)).prod :=
      rfl
    -- D7.17.2: `C_h = ∏_g A_{h,g}^{-1/2} ∏_g B_{h,g} ∏_g A_{h,g}^{-1/2} = ∏_g C_{h,g}`
    have hrel : R.relRatio n t k h = (List.ofFn fun g => R.bandRelRatio n t k h g).prod := by
      rw [relRatio, hB', hold]
      exact listProd_whiten hA hAA hAB
    have hCC : ∀ g g', g ≠ g' → Commute (R.bandRelRatio n t k h g)
        (R.bandRelRatio n t k h g') := fun g g' hg => by
      have hBB' : Commute (R.bandChoiceRoot n t k h g) (R.bandChoiceRoot n t k h g') := hBB g g' hg
      have r1 : ∀ r s : ℝ, Commute (bandMetric n t k (R.old h g) ^ r)
          (bandMetric n t k (R.old h g') ^ s) := fun r s =>
        (hA g).commute_rpow (hA g') (hAA g g' hg) r s
      have r2 : ∀ r : ℝ, Commute (bandMetric n t k (R.old h g) ^ r)
          (R.bandChoiceRoot n t k h g') := fun r => (hA g).commute_rpow_left (hAB g g' hg) r
      have r3 : ∀ r : ℝ, Commute (R.bandChoiceRoot n t k h g)
          (bandMetric n t k (R.old h g') ^ r) := fun r =>
        ((hA g').commute_rpow_left (hAB g' g hg.symm) r).symm
      unfold bandRelRatio
      refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_
      all_goals refine Commute.mul_right (Commute.mul_right ?_ ?_) ?_
      all_goals first | exact r1 _ _ | exact r2 _ | exact r3 _ | exact hBB'
    -- D7.17.2: commuting positive factors, `log C_h = ∑_g log C_{h,g}`
    refine ⟨hrel, ?_, fun g => R.bandRelRatio_eq_eval hR ht k h g⟩
    rw [hrel]
    exact cfc_log_listProd_ofFn (fun g => R.posDef_bandRelRatio (n := n) hR ht k h g) hCC

end Round

/-! ## D7.18 The conditional pin -/

/-- `-log (K (k + 2)^N)⁻¹ = O(log (k + 1))`. -/
theorem isBigO_neg_log_inv_poly {K N : ℝ} (hK : 0 < K) :
    (fun k : ℕ => -Real.log (K * ((k : ℝ) + 2) ^ N)⁻¹) =O[atTop]
      fun k : ℕ => Real.log (k + 1) := by
  refine IsBigO.of_bound (|Real.log K| + 2 * |N|) ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have hl1 : 1 ≤ Real.log ((k : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl2 : Real.log ((k : ℝ) + 2) ≤ 2 * Real.log ((k : ℝ) + 1) := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log h2 (by norm_num; nlinarith)
  have hl2' : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  rw [Real.log_inv, neg_neg, Real.log_mul hK.ne' (Real.rpow_pos_of_pos h2 N).ne',
    Real.log_rpow h2, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤
      Real.log ((k : ℝ) + 1))]
  calc |Real.log K + N * Real.log (↑k + 2)|
        ≤ |Real.log K| + |N * Real.log (↑k + 2)| := abs_add_le _ _
    _ = |Real.log K| + |N| * Real.log (↑k + 2) := by rw [abs_mul, abs_of_nonneg hl2']
    _ ≤ |Real.log K| * Real.log (↑k + 1) + |N| * (2 * Real.log (↑k + 1)) :=
        add_le_add (le_mul_of_one_le_right (abs_nonneg _) hl1)
          (mul_le_mul_of_nonneg_left hl2 (abs_nonneg _))
    _ = (|Real.log K| + 2 * |N|) * Real.log (↑k + 1) := by ring

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- D7.18.1, transfer. A quadratic-form pin for the whole-space relative metric
`(√A)⁻¹ A' (√A)⁻¹` (Lemma 6.3's form) gives the Loewner pin for the padded band metrics
`Π_k A + (1 − Π_k)`. -/
theorem pin_transfer {π π' : PYF V} (hπ : π.IsPartition) (hπ' : π'.IsPartition) {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (θ : SiteConfig n → ℂ) {Kc N E : ℝ} (hK : 0 < Kc)
    (h : ∀ w, ‖star (TensorPower.tensorVec k θ) ⬝ᵥ w‖ ^ 2 * Real.exp E ≤ Kc * ((k : ℝ) + 2) ^ N *
      (star w ⬝ᵥ (((CFC.sqrt (Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F))⁻¹ *
        Replicas.A (fun v => Fin (n v)) t k π'.P π'.Y π'.F *
          (CFC.sqrt (Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F))⁻¹) *ᵥ w)).re) :
    ((Kc * ((k : ℝ) + 2) ^ N)⁻¹ * Real.exp E) • Replicas.P (fun v => Fin (n v)) k θ ≤
      bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k π' *
        bandMetric n t k π ^ (-(1 / 2) : ℝ) := by
  have hA := posDef_A (n := n) hπ ht k
  have hA' := posDef_A (n := n) hπ' ht k
  rw [← hA.rpow_neg_half_eq_inv_sqrt] at h
  have hpos : 0 < Kc * ((k : ℝ) + 2) ^ N := mul_pos hK (Real.rpow_pos_of_pos (by positivity) N)
  have hwhole : ((Kc * ((k : ℝ) + 2) ^ N)⁻¹ * Real.exp E) • Replicas.P (fun v => Fin (n v)) k θ ≤
      Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F ^ (-(1 / 2) : ℝ) *
        Replicas.A (fun v => Fin (n v)) t k π'.P π'.Y π'.F *
          Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F ^ (-(1 / 2) : ℝ) := by
    refine smul_vecMulVec_le_of_forall (hA.whiten hA').isHermitian fun w => ?_
    calc (Kc * ((k : ℝ) + 2) ^ N)⁻¹ * Real.exp E * ‖star (TensorPower.tensorVec k θ) ⬝ᵥ w‖ ^ 2
        = (Kc * ((k : ℝ) + 2) ^ N)⁻¹ *
            (‖star (TensorPower.tensorVec k θ) ⬝ᵥ w‖ ^ 2 * Real.exp E) := by ring
      _ ≤ _ := (inv_mul_le_iff₀ hpos).2 (h w)
  unfold bandMetric
  refine hA.le_whiten_proj_mul_add_one_sub (isHermitian_Pi k) (Pi_mul_Pi k)
    (commute_Pi_A t k _ _ _) (commute_Pi_A t k _ _ _) ?_ hwhole
  rw [Matrix.mul_smul, Matrix.smul_mul, Pi_eq_projS, projS_mul_P, P_mul_projS]

end Transfer

/-- D7.18.1 (single move). Lemma 6.3 for one move of one band, with its hypotheses
`0 < t ≤ 1`, `2t ℓ(dim x) ≤ c` from `a ℓ ≤ c₀`, `ℓ ≥ log(e dim x)`, `t = a/2`:
`A^{-1/2} A_{move} A^{-1/2} ≥ b exp(ka[η(θ) − C a^{1/4} ℓ^2]) P_{θ,k}`, `-log b = O(log(k+1))`;
for no move, `b = 1`. -/
theorem conditional_pin_move :
    ∃ Cg c₀ : ℝ, 0 < Cg ∧ 0 < c₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {π : PYF V}, π.IsPartition → ∀ {m : Move V}, m.subsystem ⊆ π.Y →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → logDim (n := n) m.subsystem ≤ ℓ →
      ∃ bm : ℕ → ℝ, (∀ k, 0 < bm k) ∧
        (fun k : ℕ => -Real.log (bm k)) =O[atTop] (fun k : ℕ => Real.log (k + 1)) ∧
        ∀ (k : ℕ) (θ : Replicas.Sphere (fun v => Fin (n v))),
          (bm k * Real.exp (k * a * (Round.moveEta π m θ.1 -
              Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ)))) • Replicas.P (fun v => Fin (n v)) k θ.1 ≤
            bandMetric n (a / 2) k π ^ (-(1 / 2) : ℝ) * bandMetric n (a / 2) k (m.apply π) *
              bandMetric n (a / 2) k π ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, H₁⟩ := Replicas.lemma_6_3
  obtain ⟨C₂, c₂, hC₂, hc₂, H₂⟩ := Replicas.lemma_6_3_exchange
  refine ⟨max C₁ C₂, min (min c₁ c₂) 1, lt_max_of_lt_left hC₁,
    lt_min (lt_min hc₁ hc₂) one_pos, ?_⟩
  intro V _ _ n _ π hπ m hm a ℓ ha hℓ haℓ hdim
  set Cg := max C₁ C₂
  have ht0 : 0 < a / 2 := by positivity
  have haℓ1 : a * ℓ ≤ 1 := haℓ.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := by nlinarith
  have ht1 : a / 2 ≤ 1 := by linarith
  have hx1 := one_le_logDim (n := n) m.subsystem
  have hsmall : 2 * (a / 2) * logDim (n := n) m.subsystem ≤ a * ℓ := by
    rw [show 2 * (a / 2) = a by ring]; exact mul_le_mul_of_nonneg_left hdim ha.le
  have hP : ∀ (k : ℕ) (θ : Replicas.Sphere (fun v => Fin (n v))),
      IsStarProjection (Replicas.P (fun v => Fin (n v)) k θ.1) := fun k θ =>
    isStarProjection_P θ.2
  -- the error term of Lemma 6.3 is below `C a^{1/4} ℓ²`
  have hexp : ∀ C' : ℝ, 0 < C' → C' ≤ Cg → ∀ (k : ℕ) (η : ℝ),
      Real.exp (k * a * (η - Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ))) ≤
        Real.exp (k * (2 * (a / 2)) * (η - C' * (2 * (a / 2)) ^ (1 / 4 : ℝ) *
          logDim (n := n) m.subsystem ^ 2)) := by
    intro C' hC' hC'g k η
    rw [show 2 * (a / 2) = a by ring, Real.rpow_two]
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h1 : logDim (n := n) m.subsystem ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by linarith) hdim 2
    have h2 : C' * a ^ (1 / 4 : ℝ) ≤ Cg * a ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hC'g (Real.rpow_nonneg ha.le _)
    have h3 : C' * a ^ (1 / 4 : ℝ) * logDim (n := n) m.subsystem ^ 2 ≤
        Cg * a ^ (1 / 4 : ℝ) * ℓ ^ 2 :=
      mul_le_mul h2 h1 (by positivity) (by positivity)
    linarith
  obtain ⟨hPY, hPF, hYF, hU⟩ := hπ
  cases m with
  | stay =>
    -- D7.18.2, no move: the relative metric is `I`, `η = 0`, `P_θ ≤ I`
    refine ⟨fun _ => 1, fun _ => one_pos, ?_, fun k θ => ?_⟩
    · simp only [Real.log_one, neg_zero]; exact isBigO_zero _ _
    have hA := posDef_bandMetric (n := n) ⟨hPY, hPF, hYF, hU⟩ ht0.le k
    change _ ≤ bandMetric n (a / 2) k π ^ (-(1 / 2) : ℝ) * bandMetric n (a / 2) k π *
      bandMetric n (a / 2) k π ^ (-(1 / 2) : ℝ)
    rw [Matrix.Transport.rpow_neg_half_mul_self_mul hA]
    have hc : 1 * Real.exp (k * a * (Round.moveEta π .stay θ.1 -
        Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ))) ≤ 1 := by
      rw [one_mul, Real.exp_le_one_iff]
      change (k : ℝ) * a * (0 - Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ)) ≤ 0
      have : 0 ≤ Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ) := by positivity
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) ha.le]
    exact (smul_le_of_le_one_left (hP k θ).nonneg hc).trans (hP k θ).le_one
  | toP x =>
    have hx : x ⊆ π.Y := hm
    have hcov : π.P ∪ x ∪ (π.Y \ x) ∪ π.F = Finset.univ := by
      rw [← hU]; ext v; have hxv := @hx v
      simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    obtain ⟨Kc, N, hK, H6⟩ := H₁ (P := π.P) (x := x) (Y₀ := π.Y \ x) (F := π.F) hcov
      (hPY.mono_right hx) (hPY.mono_right Finset.sdiff_subset) hPF Finset.disjoint_sdiff
      (hYF.mono_left hx) (hYF.mono_left Finset.sdiff_subset) ht0 ht1
      (hsmall.trans (haℓ.trans ((min_le_left _ _).trans (min_le_left _ _))))
    refine ⟨fun k => (Kc * ((k : ℝ) + 2) ^ N)⁻¹,
      fun k => inv_pos.mpr (mul_pos hK (Real.rpow_pos_of_pos (by positivity) N)),
      isBigO_neg_log_inv_poly hK, fun k θ => ?_⟩
    have hθ : star (θ.1 ∘ univEquiv) ⬝ᵥ (θ.1 ∘ univEquiv) = 1 := by
      rw [dotProduct_comm, Replicas.dotProduct_star_comp_univEquiv]; exact θ.2
    have h6 := H6 k (θ.1 ∘ univEquiv) hθ
    rw [show (θ.1 ∘ univEquiv) ∘ univEquiv.symm = θ.1 by funext y; simp] at h6
    simp only [TensorPower.relativeMetric, Finset.union_sdiff_of_subset hx] at h6
    have hη : Round.moveEta π (.toP x) θ.1 = condMutualInfo (OpenAI.pureState _ hθ).toSubState
        (Finset.subset_univ x) (Finset.subset_univ (π.Y \ x)) (Finset.subset_univ π.F) := by
      simp only [Round.moveEta, Replicas.η, dif_pos hθ]
    rw [hη]
    refine le_trans (smul_le_smul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hexp C₁ hC₁ (le_max_left _ _) k _) (inv_pos.mpr (mul_pos hK
        (Real.rpow_pos_of_pos (by positivity) N))).le) (hP k θ).nonneg) ?_
    exact pin_transfer ⟨hPY, hPF, hYF, hU⟩
      (Round.Move.isPartition_apply ⟨hPY, hPF, hYF, hU⟩ hm) ht0.le θ.1 hK h6
  | toF x =>
    have hx : x ⊆ π.Y := hm
    have hcov : π.P ∪ x ∪ (π.Y \ x) ∪ π.F = Finset.univ := by
      rw [← hU]; ext v; have hxv := @hx v
      simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    obtain ⟨Kc, N, hK, H6⟩ := H₂ (P := π.P) (x := x) (Y₀ := π.Y \ x) (F := π.F) hcov
      (hPY.mono_right hx) (hPY.mono_right Finset.sdiff_subset) hPF Finset.disjoint_sdiff
      (hYF.mono_left hx) (hYF.mono_left Finset.sdiff_subset) ht0 ht1
      (hsmall.trans (haℓ.trans ((min_le_left _ _).trans (min_le_right _ _))))
    refine ⟨fun k => (Kc * ((k : ℝ) + 2) ^ N)⁻¹,
      fun k => inv_pos.mpr (mul_pos hK (Real.rpow_pos_of_pos (by positivity) N)),
      isBigO_neg_log_inv_poly hK, fun k θ => ?_⟩
    have hθ : star (θ.1 ∘ univEquiv) ⬝ᵥ (θ.1 ∘ univEquiv) = 1 := by
      rw [dotProduct_comm, Replicas.dotProduct_star_comp_univEquiv]; exact θ.2
    have h6 := H6 k (θ.1 ∘ univEquiv) hθ
    rw [show (θ.1 ∘ univEquiv) ∘ univEquiv.symm = θ.1 by funext y; simp] at h6
    rw [Finset.union_sdiff_of_subset hx, Finset.union_comm x π.F] at h6
    have hη : Round.moveEta π (.toF x) θ.1 = condMutualInfo (OpenAI.pureState _ hθ).toSubState
        (Finset.subset_univ x) (Finset.subset_univ (π.Y \ x)) (Finset.subset_univ π.P) := by
      simp only [Round.moveEta, Replicas.η, dif_pos hθ]
    rw [hη]
    refine le_trans (smul_le_smul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hexp C₂ hC₂ (le_max_right _ _) k _) (inv_pos.mpr (mul_pos hK
        (Real.rpow_pos_of_pos (by positivity) N))).le) (hP k θ).nonneg) ?_
    exact pin_transfer ⟨hPY, hPF, hYF, hU⟩
      (Round.Move.isPartition_apply ⟨hPY, hPF, hYF, hU⟩ hm) ht0.le θ.1 hK h6

/-- D7.18 Step `transport:conditional-pin`. There is `b_k > 0`, `-log b_k = O_fixed(log(k+1))`,
`b_k ≤ 1`, such that for every unit `θ`, every `h, g`, on `𝒮_k`:
`C_{h,g} ≥ b_k exp(ka[∑_c q_{c|h} η_{h,c,g}(θ) − C a^{1/4} ℓ^C]) P_{θ,k}`. -/
theorem step_7_18 :
    ∃ c₀ Cg e : ℝ, 0 < c₀ ∧ 0 < Cg ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)] {K : ℕ}
        {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
        [∀ h, DecidableEq (C h)] (R : Round V K H C), R.IsAdmissible →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ →
        (∀ h c g, logDim (n := n) (R.move h c g).subsystem ≤ ℓ) →
      ∃ b : ℕ → ℝ, (∀ k, 0 < b k ∧ b k ≤ 1) ∧
        (fun k : ℕ => -Real.log (b k)) =O[atTop] (fun k : ℕ => Real.log (k + 1)) ∧
        ∀ (k : ℕ) (θ : Replicas.Sphere (fun v => Fin (n v))) (h : H) (g : Fin K),
          (b k * Real.exp (k * a * (∑ c, (R.choiceTree h).weight c * R.eta h c g θ.1 -
              Cg * a ^ (1 / 4 : ℝ) * ℓ ^ e))) • Replicas.P (fun v => Fin (n v)) k θ.1 ≤
            R.bandRelRatio n (a / 2) k h g := by
  obtain ⟨Cg, c₀, hCg, hc₀, Hm⟩ := conditional_pin_move
  refine ⟨c₀, Cg, 2, hc₀, hCg, ?_⟩
  intro V _ _ n _ K H _ _ C _ _ R hR a ℓ ha hℓ haℓ hdim
  have ht0 : (0 : ℝ) ≤ a / 2 := by positivity
  -- D7.18.1: Lemma 6.3 for every move
  choose bm hbm0 hbmO hbm using fun h (c : C h) g =>
    Hm (hR.old_isPartition h g) (hR.move_subset h c g) ha hℓ haℓ (hdim h c g)
  -- D7.18.2: a common `b_k`, the smallest prefactor over the finitely many moves and `1`
  set f : Option (Σ h, C h × Fin K) → ℕ → ℝ := fun x k => x.elim 1 fun y => bm y.1 y.2.1 y.2.2 k
  set b : ℕ → ℝ := fun k => ⨅ x, f x k
  have hf0 : ∀ x k, 0 < f x k := by
    rintro (_ | ⟨h, c, g⟩) k
    exacts [one_pos, hbm0 h c g k]
  have hble : ∀ x k, b k ≤ f x k := fun x k => ciInf_le (Set.finite_range _).bddBelow x
  have hbex : ∀ k, ∃ x, b k = f x k := fun k => by
    obtain ⟨x, hx⟩ := exists_eq_ciInf_of_finite (f := fun x => f x k)
    exact ⟨x, hx.symm⟩
  have hb : ∀ k, 0 < b k ∧ b k ≤ 1 := fun k => by
    obtain ⟨x, hx⟩ := hbex k
    exact ⟨hx ▸ hf0 x k, hble none k⟩
  have hbO : (fun k : ℕ => -Real.log (b k)) =O[atTop] fun k : ℕ => Real.log (k + 1) := by
    have hsum : (fun k : ℕ => ∑ x, max (-Real.log (f x k)) 0) =O[atTop]
        fun k : ℕ => Real.log (k + 1) := by
      refine IsBigO.fun_sum fun x _ => ?_
      have hx : (fun k : ℕ => -Real.log (f x k)) =O[atTop] fun k : ℕ => Real.log (k + 1) := by
        rcases x with _ | ⟨h, c, g⟩
        · simp only [f, Option.elim, Real.log_one, neg_zero]; exact isBigO_zero _ _
        · exact hbmO h c g
      refine (IsBigO.of_bound 1 (Eventually.of_forall fun k => ?_)).trans hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun k => ?_)).trans hsum
    obtain ⟨x, hx⟩ := hbex k
    have h0 : 0 ≤ -Real.log (b k) := neg_nonneg.mpr (Real.log_nonpos (hb k).1.le (hb k).2)
    have h1 : -Real.log (b k) ≤ ∑ y, max (-Real.log (f y k)) 0 := by
      rw [hx]
      exact (le_max_left _ _).trans (Finset.single_le_sum
        (f := fun y => max (-Real.log (f y k)) 0) (fun _ _ => le_max_right _ _)
        (Finset.mem_univ x))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _), one_mul]
    exact h1
  refine ⟨b, hb, hbO, fun k θ h g => ?_⟩
  -- D7.18.3: projection transfer (Lemma 7.1 (5)) in the choice tree, `P := P_{θ,k}`
  have hP : IsStarProjection (Replicas.P (fun v => Fin (n v)) k θ.1) := isStarProjection_P θ.2
  set x : C h → ℝ := fun c => k * a * (R.eta h c g θ.1 - Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ))
  have hAP : ∀ c, (b k * Real.exp (x c)) • Replicas.P (fun v => Fin (n v)) k θ.1 ≤
      R.moveRelMetric n (a / 2) k h c g := fun c =>
    le_trans (smul_le_smul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hble (some ⟨h, c, g⟩) k) (Real.exp_pos _).le) hP.nonneg) (hbm h c g k θ)
  have key := lemma_7_1_5 (fun c => R.posDef_moveRelMetric (n := n) hR ht0 k h c g) hP
    (c := fun c => b k * Real.exp (x c)) (fun c => mul_pos (hb k).1 (Real.exp_pos _)) hAP
    (R.choiceTree h)
  rw [R.bandRelRatio_eq_eval hR ht0]
  convert key using 2
  -- `∏_c (b_k e^{x_c})^{q_{c|h}} = b_k exp(∑_c q_{c|h} x_c)` since `∑_c q_{c|h} = 1`
  rw [Finset.prod_congr rfl (fun c _ => Real.mul_rpow (hb k).1.le (Real.exp_pos _).le),
    Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (hb k).1, MeanTree.sum_weight, Real.rpow_one]
  congr 1
  simp only [← Real.exp_mul, ← Real.exp_sum]
  congr 1
  have hw := (R.choiceTree h).sum_weight
  simp only [x]
  have hs : ∑ c, (k : ℝ) * a * (R.eta h c g θ.1 - Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ)) *
      (R.choiceTree h).weight c = (k : ℝ) * a * ∑ c, (R.choiceTree h).weight c * R.eta h c g θ.1 -
        (k : ℝ) * a * (Cg * a ^ (1 / 4 : ℝ) * ℓ ^ (2 : ℝ)) * ∑ c, (R.choiceTree h).weight c := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hs, hw]
  ring

/-! ## D7.20 The entropy gain -/

/-- `D_k` is polynomial in `k`: `D_k = binom(k + d − 1, d − 1) ≤ (k + 1)^{d − 1}`, so
`log D_k = O(log(k + 1))`. -/
theorem log_D_isBigO {J : Type*} [Fintype J] [DecidableEq J] (ι : J → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] :
    (fun k : ℕ => Real.log (Replicas.D ι k)) =O[atTop] fun k : ℕ => Real.log (k + 1) := by
  set d := Fintype.card ((f : J) → ι f)
  have hd : 0 < d := Fintype.card_pos
  refine IsBigO.of_bound ((d - 1 : ℕ) : ℝ) (Eventually.of_forall fun k => ?_)
  have hk : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hD1 := one_le_D ι k
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hD1),
    abs_of_nonneg (Real.log_nonneg hk)]
  have hle : (Replicas.D ι k : ℝ) ≤ (((k + 1) ^ (d - 1) : ℕ) : ℝ) := by
    rw [Replicas.D_eq_choose ι k hd, show k + d - 1 = k + (d - 1) by omega]
    exact_mod_cast Nat.choose_add_le_add_one_pow k (d - 1)
  calc Real.log (Replicas.D ι k) ≤ Real.log (((k + 1) ^ (d - 1) : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) hle
    _ = ((d - 1 : ℕ) : ℝ) * Real.log (k + 1) := by push_cast; rw [Real.log_pow]

namespace Round

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {K : ℕ} {H : Type*}
  {C : H → Type*} (R : Round V K H C)

/-- `θ ↦ η_{h,c,g}(θ)` is continuous on the unit sphere. -/
theorem continuous_eta (h : H) (c : C h) (g : Fin K) :
    Continuous fun θ : Replicas.Sphere (fun v => Fin (n v)) => R.eta h c g θ.1 := by
  unfold eta
  generalize R.move h c g = m
  cases m with
  | stay => exact continuous_const
  | toP x =>
    exact (Replicas.continuousOn_η _ _ _).comp_continuous continuous_subtype_val fun θ => θ.2
  | toF x =>
    exact (Replicas.continuousOn_η _ _ _).comp_continuous continuous_subtype_val fun θ => θ.2

variable [DecidableEq H] [∀ h, DecidableEq (C h)] [∀ v, NeZero (n v)]

/-- `u ↦ m_s(u) Tr(σ_{j,u} Z)` is integrable (`s = 1/4`). -/
theorem integrable_m_mul_trace_state (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (pre : Config n k → ℂ) (p : I) (j : Leaf H C)
    (Z : Matrix (Config n k) (Config n k) ℂ) :
    Integrable fun u => m (1 / 4) u * (R.state n t k pre p j u * Z).trace.re := by
  have hM : (R.root n t k p).IsHermitian := (R.posDef_root hR ht hcomm p).isHermitian
  refine (Matrix.Transport.integrable_fourierWeight_mul_quadForm hM
    ((R.tree p).leafMap (R.input n t k) j Z) (R.v n t k pre p)).congr
      (Eventually.of_forall fun u => ?_)
  have := star_dotProduct_mulVec_eq_trace_traceAdjointMap
    ((R.tree p).leafMap (R.input n t k) j).toLinearMap Z
    (Matrix.Transport.imagPow (R.root n t k p) u *ᵥ R.v n t k pre p)
  rw [ContinuousLinearMap.coe_coe] at this
  dsimp only
  rw [this]
  rfl

/-- D7.20.1–D7.20.2 for one band. From the pin `b e^{φ(θ)} P_{θ,k} ≤ C_{h,g}` for all unit `θ`:
`C_{h,g} ≥ (b/D_k) 𝒬_k(e^φ)` (integration over `θ`), then log monotone and Jensen (D7.19):
`log C_{h,g} ≥ 𝒬_k(φ) + (log b − log D_k) I`. -/
theorem log_relative_of_pin [∀ h, Finite (C h)] (hR : R.IsAdmissible) {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} {h : H} {g : Fin K} {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    {φ : Replicas.Sphere (fun v => Fin (n v)) → ℝ} (hφ : Continuous φ)
    (hpin : ∀ θ : Replicas.Sphere (fun v => Fin (n v)),
      (b * Real.exp (φ θ)) • Replicas.P (fun v => Fin (n v)) k θ.1 ≤ R.bandRelRatio n t k h g) :
    Q (fun v => Fin (n v)) k φ + (Real.log b - Real.log (Replicas.D (fun v => Fin (n v)) k)) •
        (1 : Matrix (Config n k) (Config n k) ℂ) ≤ CFC.log (R.bandRelRatio n t k h g) := by
  have hD := one_le_D (fun v => Fin (n v)) k
  have hd : 0 < b / Replicas.D (fun v => Fin (n v)) k := div_pos hb0 (by linarith)
  have hf : Continuous fun θ => Real.exp (φ θ) := Real.continuous_exp.comp hφ
  have hfpos : ∀ θ, 0 < Real.exp (φ θ) := fun θ => Real.exp_pos _
  have hc : Commute (Replicas.projS (fun v => Fin (n v)) k) (R.bandRelRatio n t k h g) := by
    rw [← Pi_eq_projS]; exact R.commute_Pi_bandRelRatio hR ht k h g
  have hc1 : 1 - Replicas.projS (fun v => Fin (n v)) k ≤ R.bandRelRatio n t k h g := by
    rw [← Pi_eq_projS]; exact R.one_sub_Pi_le_bandRelRatio hR ht k h g
  -- D7.20.1: `C_{h,g} ≥ (b / D_k) 𝒬_k(e^φ)` on `𝒮_k`, and `≥ 1` on `𝒮_k^⊥`
  have h1 := smul_Q_add_le_of_pin hc hc1 hb1 hφ hpin
  -- D7.20.2: log monotone, then Jensen (D7.19)
  have hY : (Q (fun v => Fin (n v)) k (fun θ => Real.exp (φ θ)) +
      (1 - Replicas.projS (fun v => Fin (n v)) k)).PosDef := by
    have h := posDef_Q_add (k := k) hf hfpos one_pos
    rwa [Complex.ofReal_one, one_smul] at h
  have h19 := step_7_19 (ι := fun v => Fin (n v)) (k := k)
  have hlog := h19.2.2.2 _ _ (hY.smul hd) h1
  rw [CFC.log_smul' _ hd hY.isStrictlyPositive, Algebra.algebraMap_eq_smul_one] at hlog
  have hJ := (h19.2.2.1 _ hf hfpos).2
  have hlf : (Real.log ∘ fun θ => Real.exp (φ θ)) = φ := funext fun θ => Real.log_exp _
  rw [hlf] at hJ
  rw [← Real.log_div hb0.ne' (lt_of_lt_of_le one_pos hD).ne', add_comm]
  refine le_trans ?_ hlog
  rw [Matrix.le_iff] at hJ ⊢
  rwa [add_sub_add_left_eq_sub]

end Round

/-- D7.20 Step `transport:log-relative`, `transport:entropy-gain` (Proposition 7.4 (b)).
`log C_{h,g} ≥ k a 𝒬_k(∑_c q_{c|h} η_{h,c,g} − C a^{1/4} ℓ^C) + (log b_k − log D_k) I`.
Consequently Proposition 7.4 (b) holds with `β_k = (K/2)(log D_k − log b_k)`:
`-∂_p log N² ≥ ka ∑_{h,g} w_h ∫ m_s(u) ∫ ∑_c q_{c|h} η_{h,c,g}(θ) dμ_{σ_{h,u}}(θ) du
  − C k a K a^{1/4} ℓ^C − β_k`, with `β_k = O_fixed(log(k+1))` independent of `p` and `pre`. -/
theorem step_7_20 :
    ∃ c₀ Cg e : ℝ, 0 < c₀ ∧ 0 < Cg ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)] {K : ℕ}
        {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
        [∀ h, DecidableEq (C h)] (R : Round V K H C), R.IsAdmissible →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, R.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim (n := n) (R.move h c g).subsystem ≤ ℓ) →
      ∃ b : ℕ → ℝ, (∀ k, 0 < b k ∧ b k ≤ 1) ∧
        (fun k : ℕ => -Real.log (b k)) =O[atTop] (fun k : ℕ => Real.log (k + 1)) ∧
        (∀ (k : ℕ) (h : H) (g : Fin K),
          ((k : ℝ) * a) • Q (fun v => Fin (n v)) k (fun θ =>
              ∑ c, (R.choiceTree h).weight c * R.eta h c g θ.1 - Cg * a ^ (1 / 4 : ℝ) * ℓ ^ e) +
            (Real.log (b k) - Real.log (Replicas.D (fun v => Fin (n v)) k)) •
              (1 : Matrix (Config n k) (Config n k) ℂ) ≤
          CFC.log (R.bandRelRatio n (a / 2) k h g)) ∧
        (fun k : ℕ => (K : ℝ) / 2 * (Real.log (Replicas.D (fun v => Fin (n v)) k) -
          Real.log (b k))) =O[atTop] (fun k : ℕ => Real.log (k + 1)) ∧
        ∀ (k : ℕ) (pre : Config n k → ℂ), pre ∈ Replicas.S (fun v => Fin (n v)) k → pre ≠ 0 →
          ∀ p : I, 0 < (p : ℝ) → (p : ℝ) < 1 →
            (k : ℝ) * a * R.entropyGain n (a / 2) k pre p -
                Cg * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ e -
                (K : ℝ) / 2 * (Real.log (Replicas.D (fun v => Fin (n v)) k) - Real.log (b k)) ≤
              R.exactDerivative n (a / 2) k pre p := by
  obtain ⟨c₀, Cg, e, hc₀, hCg, H18⟩ := step_7_18
  refine ⟨c₀, Cg, e, hc₀, hCg, ?_⟩
  intro V _ _ n _ K H _ _ C _ _ R hR a ℓ ha hℓ haℓ hcomm hdim
  obtain ⟨b, hb, hbO, hpin⟩ := H18 R hR ha hℓ haℓ hdim
  have ht0 : (0 : ℝ) ≤ a / 2 := by positivity
  set E := Cg * a ^ (1 / 4 : ℝ) * ℓ ^ e with hE
  set F : ∀ h, Fin K → Replicas.Sphere (fun v => Fin (n v)) → ℝ :=
    fun h g θ => ∑ c, (R.choiceTree h).weight c * R.eta h c g θ.1 with hF_def
  have hF : ∀ h g, Continuous (F h g) := fun h g =>
    continuous_finsetSum _ fun c _ => continuous_const.mul (R.continuous_eta h c g)
  -- D7.20 `transport:log-relative`: D7.18 integrated over `θ` (D7.20.1), log and Jensen (D7.20.2)
  have hlogrel : ∀ (k : ℕ) (h : H) (g : Fin K),
      ((k : ℝ) * a) • Q (fun v => Fin (n v)) k (fun θ => F h g θ - E) +
        (Real.log (b k) - Real.log (Replicas.D (fun v => Fin (n v)) k)) •
          (1 : Matrix (Config n k) (Config n k) ℂ) ≤
        CFC.log (R.bandRelRatio n (a / 2) k h g) := by
    intro k h g
    have hφ : Continuous fun θ => (k : ℝ) * a * (F h g θ - E) :=
      continuous_const.mul ((hF h g).sub continuous_const)
    have key := R.log_relative_of_pin hR ht0 (h := h) (g := g) (hb k).1 (hb k).2 hφ
      (fun θ => hpin k θ h g)
    have hQ : Q (fun v => Fin (n v)) k (fun θ => (k : ℝ) * a * (F h g θ - E)) =
        (((k : ℝ) * a : ℝ) : ℂ) • Q (fun v => Fin (n v)) k (fun θ => F h g θ - E) :=
      Q_const_mul _ _
    rw [hQ, Complex.coe_smul] at key
    exact key
  refine ⟨b, hb, hbO, hlogrel, ?_, ?_⟩
  · refine (((log_D_isBigO (fun v => Fin (n v))).add hbO).const_mul_left
      ((K : ℝ) / 2)).congr_left fun k => ?_
    ring
  intro k pre hpreS hpre p hp0 hp1
  have hσ : ∀ h u, IsSymDensity n (R.state n (a / 2) k pre p ⟨h, none⟩ u) := fun h u =>
    R.isSymDensity_state hR ht0 (hcomm k) hpreS hpre hp0 hp1 _ u
  set G : H → Fin K → ℝ → ℝ := fun h g u => ∫ θ, F h g θ
    ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n (a / 2) k pre p ⟨h, none⟩ u)) with hG_def
  have hGtr : ∀ h g u, G h g u =
      (R.state n (a / 2) k pre p ⟨h, none⟩ u * Q (fun v => Fin (n v)) k (F h g)).trace.re := by
    intro h g u
    rw [trace_mul_Q (hσ h u).1 (hF h g), integral_complex_ofReal, Complex.ofReal_re]
  -- D7.20.3: expectation in the trace-one `σ_{h,u}`
  have hg3 : ∀ h g u, (k : ℝ) * a * (G h g u - E) +
      (Real.log (b k) - Real.log (Replicas.D (fun v => Fin (n v)) k)) ≤
      (R.state n (a / 2) k pre p ⟨h, none⟩ u *
        CFC.log (R.bandRelRatio n (a / 2) k h g)).trace.re := by
    intro h g u
    obtain ⟨hp, htr, hU⟩ := hσ h u
    have := Replicas.eq_replicas_husimi (fun v => Fin (n v)) k hp htr hU
    have hmono := hp.re_trace_mul_mono (hlogrel k h g)
    have hcont : Continuous fun θ => F h g θ - E := (hF h g).sub continuous_const
    have hint : ∫ θ, (F h g θ - E)
        ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n (a / 2) k pre p ⟨h, none⟩ u)) =
        G h g u - E := by
      rw [integral_sub ((hF h g).integrable_of_hasCompactSupport (.of_compactSpace _))
        (integrable_const E), integral_const, probReal_univ, one_smul]
    refine le_trans (le_of_eq ?_) hmono
    rw [Matrix.mul_add, trace_add, Complex.add_re, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_one, trace_smul, trace_smul, htr, trace_mul_Q hp hcont, integral_complex_ofReal,
      hint, Complex.real_smul, Complex.real_smul, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      Complex.ofReal_re, Complex.one_re, mul_one]
  -- D7.20.4: sum over `g` with D7.17 (`K` bands)
  have hg4 : ∀ h u, (k : ℝ) * a * ∑ g, G h g u -
      K * ((k : ℝ) * a * E + Real.log (Replicas.D (fun v => Fin (n v)) k) - Real.log (b k)) ≤
      (R.state n (a / 2) k pre p ⟨h, none⟩ u * CFC.log (R.relRatio n (a / 2) k h)).trace.re := by
    intro h u
    rw [((R.step_7_17 hR ht0 (hcomm k)).2 h).2.1, Matrix.mul_sum, trace_sum, Complex.re_sum]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun g _ => hg3 h g u)
    simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- D7.20.4: in `u` with `∫ m_s = 1/2`
  have hint_tr : ∀ h (Z : Matrix (Config n k) (Config n k) ℂ), Integrable fun u =>
      m (1 / 4) u * (R.state n (a / 2) k pre p ⟨h, none⟩ u * Z).trace.re := fun h Z =>
    R.integrable_m_mul_trace_state hR ht0 (hcomm k) pre p _ Z
  have hintG : ∀ h g, Integrable fun u => m (1 / 4) u * G h g u := fun h g =>
    (hint_tr h (Q (fun v => Fin (n v)) k (F h g))).congr
      (Eventually.of_forall fun u => by simp only [hGtr])
  have hm : Integrable (m (1 / 4)) := integrable_m ⟨by norm_num, by norm_num⟩
  have hm0 : ∀ u, 0 ≤ m (1 / 4) u := fun u =>
    (Real.sinhRatioDensity_pos ⟨by norm_num, by norm_num⟩ u).le
  set E' := (K : ℝ) * ((k : ℝ) * a * E + Real.log (Replicas.D (fun v => Fin (n v)) k) -
    Real.log (b k)) with hE'
  have hhist : ∀ h, (k : ℝ) * a * ∑ g, (∫ u, m (1 / 4) u * G h g u) - E' / 2 ≤
      ∫ u, m (1 / 4) u *
        (R.state n (a / 2) k pre p ⟨h, none⟩ u * CFC.log (R.relRatio n (a / 2) k h)).trace.re := by
    intro h
    have e : ∀ u, m (1 / 4) u * ((k : ℝ) * a * ∑ g, G h g u - E') =
        (∑ g, (k : ℝ) * a * (m (1 / 4) u * G h g u)) - E' * m (1 / 4) u := fun u => by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun g _ => by ring
      · ring
    have hsumint : Integrable fun u => ∑ g, (k : ℝ) * a * (m (1 / 4) u * G h g u) :=
      integrable_finsetSum _ fun g _ => (hintG h g).const_mul _
    have hlow : ∫ u, m (1 / 4) u * ((k : ℝ) * a * ∑ g, G h g u - E') =
        (k : ℝ) * a * ∑ g, (∫ u, m (1 / 4) u * G h g u) - E' / 2 := by
      rw [integral_congr_ae (Eventually.of_forall e), integral_sub hsumint (hm.const_mul _),
        integral_finsetSum _ fun g _ => (hintG h g).const_mul _, integral_const_mul,
        integral_m_quarter]
      simp only [integral_const_mul]
      rw [Finset.mul_sum]
      ring
    rw [← hlow]
    refine integral_mono ((hsumint.sub (hm.const_mul E')).congr
      (Eventually.of_forall fun u => (e u).symm)) (hint_tr h _) fun u =>
        mul_le_mul_of_nonneg_left (hg4 h u) (hm0 u)
  -- D7.20.4: over `h` with `∑_h w_h = 1`
  have hw := R.histTree.sum_weight
  have hEG : R.entropyGain n (a / 2) k pre p =
      ∑ h, R.histTree.weight h * ∑ g, ∫ u, m (1 / 4) u * G h g u := by
    simp only [Round.entropyGain, Finset.mul_sum]
    rfl
  have hT : 0 ≤ Cg * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ e := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ℓ) e
    have := Real.rpow_nonneg ha.le (1 / 4 : ℝ)
    positivity
  have hsplit : ∑ h, R.histTree.weight h * ((k : ℝ) * a * ∑ g, (∫ u, m (1 / 4) u * G h g u) -
      E' / 2) = (k : ℝ) * a * R.entropyGain n (a / 2) k pre p - E' / 2 := by
    rw [hEG, Finset.mul_sum]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
    congr 1
    exact Finset.sum_congr rfl fun h _ => by ring
  calc (k : ℝ) * a * R.entropyGain n (a / 2) k pre p -
        Cg * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ e -
        (K : ℝ) / 2 * (Real.log (Replicas.D (fun v => Fin (n v)) k) - Real.log (b k))
      ≤ ∑ h, R.histTree.weight h * ((k : ℝ) * a * ∑ g, (∫ u, m (1 / 4) u * G h g u) -
          E' / 2) := by
        rw [hsplit, hE', hE]
        nlinarith [hT]
    _ ≤ R.exactDerivative n (a / 2) k pre p :=
        Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hhist h)
          (hR.histWeight_pos h).le

end AreaLaw.Transport
