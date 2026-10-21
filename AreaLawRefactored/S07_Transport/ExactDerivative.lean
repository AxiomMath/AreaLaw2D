import AreaLawRefactored.S07_Transport.States
import AreaLawForMathlib.Analysis.Matrix.CommutantModule

/-!
# §7.4 Proposition 7.4 (a): the exact derivative

Digest `digest/07-transport.md` D7.15–D7.16, paper `paper/sections/06-transport.tex` 441–485.
No geometry: an arbitrary finite site type, arbitrary `k`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Set Filter Topology Entropy PermutationRepresentation
open Matrix.Transport (filteredVector filteredNormSq imagPow fourierWeight)

namespace AreaLaw.Transport

/-! ## Leaf maps over the commutant of the inputs -/

namespace MeanTree

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [DecidableEq ι]
  {A : ι → Matrix n n ℂ}

theorem derivLabel_mul_right (hA : ∀ i, (A i).PosDef) {Z : Matrix n n ℂ}
    (hZ : ∀ i, Commute Z (A i)) (T : MeanTree ι) (j : ι) (X : Matrix n n ℂ) :
    T.derivLabel A j (X * Z) = T.derivLabel A j X * Z := by
  induction T with
  | leaf i =>
    unfold derivLabel
    split_ifs <;> simp
  | node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply, ihl, ihr,
      Matrix.add_mul]
    rw [geomMeanDerivLeft_mul_right (posDef_eval hA l) (posDef_eval hA r)
        (commute_eval_right hZ l) (commute_eval_right hZ r) p.2,
      geomMeanDerivRight_mul_right (posDef_eval hA l) (posDef_eval hA r)
        (commute_eval_right hZ l) (commute_eval_right hZ r) p.2]

/-- `Φ_j(X Z) = Φ_j(X) Z` for `Z` commuting with every input. -/
theorem leafMap_mul_right (hA : ∀ i, (A i).PosDef) {Z : Matrix n n ℂ}
    (hZ : ∀ i, Commute Z (A i)) (T : MeanTree ι) (j : ι) (X : Matrix n n ℂ) :
    T.leafMap A j (X * Z) = T.leafMap A j X * Z := by
  have hM : Commute Z (T.eval A ^ (-(1 / 2) : ℝ)) :=
    (PosDef.commute_rpow_left (posDef_eval hA T) (commute_eval_right hZ T).symm _).symm
  have hAj : Commute Z (A j ^ (1 / 2 : ℝ)) :=
    (PosDef.commute_rpow_left (hA j) (hZ j).symm _).symm
  simp only [leafMap, normalizedDerivMap, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [sandwich_mul_right hAj, derivLabel_mul_right hA hZ, sandwich_mul_right hM, smul_mul_assoc]

end MeanTree

/-! ## D7.15 The derivative at an interpolating vertex and at the root -/

namespace Round

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {K : ℕ} {H : Type*}
  [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)] (R : Round V K H C)

omit [DecidableEq H] [∀ h, DecidableEq (C h)] in
theorem eval_map_choice (t : ℝ) (k : ℕ) (h : H) :
    ((R.choiceTree h).map fun c => (⟨h, some c⟩ : Leaf H C)).eval (R.input n t k) =
      R.choiceRoot n t k h :=
  MeanTree.eval_map _ _ _

theorem posDef_choiceRoot [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : R.CrossBandCommute n t k) (h : H) : (R.choiceRoot n t k h).PosDef :=
  MeanTree.posDef_eval (fun c => R.posDef_input hR ht hcomm ⟨h, some c⟩) _

/-- The interpolated subtree of a history subtree `T₀`. -/
def itree (T₀ : MeanTree H) (p : I) : MeanTree (Leaf H C) :=
  T₀.bind fun h => .node p (.leaf ⟨h, none⟩) ((R.choiceTree h).map fun c => ⟨h, some c⟩)

omit [Fintype V] [DecidableEq V] [DecidableEq H] [∀ h, DecidableEq (C h)] in
theorem tree_eq_itree (p : I) : R.tree p = R.itree R.histTree p := rfl

variable [Fintype H]

/-- D7.15.4 for a history subtree: the derivative of `q ↦ 𝒯₀(M_h(q) : h)` is
`∑_h ∂_{(h,old)} 𝒯₀[(1-p)^{-1} A_h^{1/2} log C_h A_h^{1/2}]`. -/
theorem hasDerivAt_eval_itree [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : R.CrossBandCommute n t k) {p : ℝ} (hp : p ∈ Ioo 0 1) (T₀ : MeanTree H) :
    HasDerivAt (fun q => (R.itree T₀ (projIcc (0 : ℝ) 1 zero_le_one q)).eval (R.input n t k))
      (∑ h, (R.itree T₀ (projIcc (0 : ℝ) 1 zero_le_one p)).derivLabel (R.input n t k)
        ⟨h, none⟩ ((1 - p)⁻¹ • (R.oldMetric n t k h ^ (1 / 2 : ℝ) *
          CFC.log (R.relRatio n t k h) * R.oldMetric n t k h ^ (1 / 2 : ℝ)))) p := by
  have hIn := R.posDef_input hR ht hcomm
  have hpI : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
    congrArg Subtype.val (projIcc_of_mem _ (Ioo_subset_Icc_self hp))
  induction T₀ with
  | leaf h₀ =>
    have hA : (R.oldMetric n t k h₀).PosDef := hIn ⟨h₀, none⟩
    have hB := R.posDef_choiceRoot hR ht hcomm h₀
    have hnot : ∀ h, (⟨h, none⟩ : Leaf H C) ∉
        ((R.choiceTree h₀).map fun c => (⟨h₀, some c⟩ : Leaf H C)).labels := by
      intro h hh
      obtain ⟨c, hc⟩ := mem_labels_map _ hh
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hc
      simp at h2
    have hsum : (∑ h, (R.itree (.leaf h₀) (projIcc (0 : ℝ) 1 zero_le_one p)).derivLabel
        (R.input n t k) ⟨h, none⟩ ((1 - p)⁻¹ • (R.oldMetric n t k h ^ (1 / 2 : ℝ) *
          CFC.log (R.relRatio n t k h) * R.oldMetric n t k h ^ (1 / 2 : ℝ)))) =
        geomMeanDerivLeft p (R.oldMetric n t k h₀) (R.choiceRoot n t k h₀)
          ((1 - p)⁻¹ • (R.oldMetric n t k h₀ ^ (1 / 2 : ℝ) * CFC.log (R.relRatio n t k h₀) *
            R.oldMetric n t k h₀ ^ (1 / 2 : ℝ))) := by
      simp only [itree, MeanTree.bind, MeanTree.derivLabel, MeanTree.derivLabel_of_not_mem (hnot _),
        add_zero, ContinuousLinearMap.comp_zero, MeanTree.eval_leaf, eval_map_choice, hpI]
      rw [Finset.sum_eq_single h₀]
      · simp [input]
      · intro h _ hh
        simp [Ne.symm hh]
      · simp
    -- D7.15.3: `∂_A M[A^{1/2} log C A^{1/2}] = (1-p) A^{1/2} C^p log C A^{1/2}`, divided by
    -- `1 - p`, is `∂_p M_h` (D7.15.2)
    rw [hsum, ContinuousLinearMap.map_smul_of_tower, relRatio,
      geomMeanDerivLeft_sandwich_log hA hB (Ioo_subset_Icc_self hp),
      smul_smul, inv_mul_cancel₀ (by linarith [hp.2] : (1 - p) ≠ 0), one_smul]
    have hev : (fun q => (R.itree (.leaf h₀) (projIcc (0 : ℝ) 1 zero_le_one q)).eval
        (R.input n t k)) =ᶠ[𝓝 p]
          fun q => geomMean q (R.oldMetric n t k h₀) (R.choiceRoot n t k h₀) := by
      filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
      simp only [itree, MeanTree.bind, MeanTree.eval_node, MeanTree.eval_leaf, eval_map_choice]
      rw [projIcc_of_mem _ (Ioo_subset_Icc_self hq)]
      rfl
    exact (hasDerivAt_geomMean_param hA hB p).congr_of_eventuallyEq hev
  | node r l rr ihl ihr =>
    have hL := MeanTree.isHermitian_eval (fun j => (hIn j).isHermitian)
    have h := hasDerivAt_geomMean_of_hasDerivAt r.2 ihl ihr
      (fun q => hL _) (fun q => hL _) (MeanTree.posDef_eval hIn _) (MeanTree.posDef_eval hIn _)
    refine h.congr_deriv ?_
    simp only [itree, MeanTree.bind, MeanTree.derivLabel, _root_.add_apply,
      ContinuousLinearMap.comp_apply, map_sum, Finset.sum_add_distrib]

/-- D7.15 (`transport:node-p-derivative`, `transport:root-p-derivative`). At
`M_h = A_h #_p B_h`, `V_h = C_h^{p/2} A_h^{1/2} M_h^{-1/2}` is unitary and
`M_h^{-1/2}(∂_p M_h) M_h^{-1/2} = V_h^*(log C_h) V_h = Φ_{A_h}(log C_h)`, `Φ_{A_h}` the normalized
old-child map at this vertex (weight `1 − p`). Hence at the root
`HH := 𝓜^{-1/2}(∂_p 𝓜)𝓜^{-1/2} = ∑_h w_h Φ_{(h,old)}(log C_h)`. -/
theorem step_7_15 [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    (∀ h, let A := R.oldMetric n t k h; let B := R.choiceRoot n t k h
      let Cr := R.relRatio n t k h; let M := geomMean p A B
      let Vh := Cr ^ (p / 2) * A ^ (1 / 2 : ℝ) * M ^ (-(1 / 2) : ℝ)
      Vhᴴ * Vh = 1 ∧ Vh * Vhᴴ = 1 ∧
      HasDerivAt (fun q => geomMean q A B) (A ^ (1 / 2 : ℝ) * (Cr ^ p * CFC.log Cr) *
        A ^ (1 / 2 : ℝ)) p ∧
      M ^ (-(1 / 2) : ℝ) * (A ^ (1 / 2 : ℝ) * (Cr ^ p * CFC.log Cr) * A ^ (1 / 2 : ℝ)) *
          M ^ (-(1 / 2) : ℝ) = Vhᴴ * CFC.log Cr * Vh ∧
      Vhᴴ * CFC.log Cr * Vh =
        normalizedDerivMap (geomMeanDerivLeft p A B) (1 - p) M A (CFC.log Cr)) ∧
    ∃ D, HasDerivAt (fun q => R.root n t k q) D p ∧
      R.root n t k p ^ (-(1 / 2) : ℝ) * D * R.root n t k p ^ (-(1 / 2) : ℝ) =
        ∑ h, R.histTree.weight h • (R.tree ⟨p, Ioo_subset_Icc_self hp⟩).leafMap (R.input n t k)
          ⟨h, none⟩ (CFC.log (R.relRatio n t k h)) := by
  have hIn := R.posDef_input hR ht hcomm
  have hpI : (projIcc (0 : ℝ) 1 zero_le_one p : I) = ⟨p, Ioo_subset_Icc_self hp⟩ :=
    projIcc_of_mem _ (Ioo_subset_Icc_self hp)
  refine ⟨fun h => ?_, ?_⟩
  · intro A B Cr M Vh
    have hA : A.PosDef := hIn ⟨h, none⟩
    have hB : B.PosDef := R.posDef_choiceRoot hR ht hcomm h
    have hC : Cr.PosDef := hA.whiten hB
    have hM : M.PosDef := hA.geomMean hB p
    have hCC : Cr ^ (p / 2) * Cr ^ (p / 2) = Cr ^ p := by
      rw [hC.rpow_mul_rpow]; ring_nf
    have hMeq : M = A ^ (1 / 2 : ℝ) * Cr ^ p * A ^ (1 / 2 : ℝ) := rfl
    have hsA : (A ^ (1 / 2 : ℝ))ᴴ = A ^ (1 / 2 : ℝ) := (hA.rpow_isHermitian _).eq
    have hsM : (M ^ (-(1 / 2) : ℝ))ᴴ = M ^ (-(1 / 2) : ℝ) := (hM.rpow_isHermitian _).eq
    have hsC : (Cr ^ (p / 2))ᴴ = Cr ^ (p / 2) := (hC.rpow_isHermitian _).eq
    have hstar : Vhᴴ = M ^ (-(1 / 2) : ℝ) * A ^ (1 / 2 : ℝ) * Cr ^ (p / 2) := by
      simp only [Vh, conjTranspose_mul, hsA, hsM, hsC, Matrix.mul_assoc]
    -- D7.15.1: `V_h^* V_h = M^{-1/2} A^{1/2} C^p A^{1/2} M^{-1/2} = M^{-1/2} M M^{-1/2} = I`
    have hVV : Vhᴴ * Vh = 1 := by
      rw [hstar]
      calc M ^ (-(1 / 2) : ℝ) * A ^ (1 / 2 : ℝ) * Cr ^ (p / 2) * Vh
          = M ^ (-(1 / 2) : ℝ) * (A ^ (1 / 2 : ℝ) * (Cr ^ (p / 2) * Cr ^ (p / 2)) *
              A ^ (1 / 2 : ℝ)) * M ^ (-(1 / 2) : ℝ) := by simp only [Vh, Matrix.mul_assoc]
        _ = M ^ (-(1 / 2) : ℝ) * M * M ^ (-(1 / 2) : ℝ) := by rw [hCC, ← hMeq]
        _ = 1 := Matrix.Transport.rpow_neg_half_mul_self_mul hM
    have hcl : Commute (Cr ^ (p / 2)) (CFC.log Cr) := by
      rw [CFC.rpow_eq_cfc_real hC.posSemidef.nonneg]; exact cfc_commute_cfc _ _ _
    -- D7.15.2: `∂_p M_h = A^{1/2} C^p (log C) A^{1/2}` with `C^p log C = C^{p/2} (log C) C^{p/2}`
    have hkey : Cr ^ p * CFC.log Cr = Cr ^ (p / 2) * CFC.log Cr * Cr ^ (p / 2) := by
      rw [← hCC, Matrix.mul_assoc, Matrix.mul_assoc]; exact congrArg _ hcl.eq
    have hD2 : M ^ (-(1 / 2) : ℝ) * (A ^ (1 / 2 : ℝ) * (Cr ^ p * CFC.log Cr) * A ^ (1 / 2 : ℝ)) *
        M ^ (-(1 / 2) : ℝ) = Vhᴴ * CFC.log Cr * Vh := by
      rw [hkey, hstar]; simp only [Vh, Matrix.mul_assoc]
    -- finite dimension: `V_h` is unitary
    refine ⟨hVV, mul_eq_one_comm.mp hVV, hasDerivAt_geomMean_param hA hB p, hD2, ?_⟩
    -- D7.15.3: perturbing `A` along `A^{1/2} (log C) A^{1/2}` gives
    -- `(1-p) A^{1/2} C^p log C A^{1/2}`
    have hsl : geomMeanDerivLeft p A B (A ^ (1 / 2 : ℝ) * CFC.log Cr * A ^ (1 / 2 : ℝ)) =
        (1 - p) • (A ^ (1 / 2 : ℝ) * (Cr ^ p * CFC.log Cr) * A ^ (1 / 2 : ℝ)) :=
      geomMeanDerivLeft_sandwich_log hA hB (Ioo_subset_Icc_self hp)
    rw [← hD2, normalizedDerivMap, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, sandwichL_apply, sandwichL_apply, hsl, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, inv_mul_cancel₀ (by linarith [hp.2] : (1 - p) ≠ 0), one_smul]
  -- D7.15.4: `p` enters `𝓜` only through the `M_h`; the history path has weight `w_h`
  · refine ⟨_, R.hasDerivAt_eval_itree hR ht hcomm hp R.histTree, ?_⟩
    have hroot : R.root n t k p = (R.tree ⟨p, Ioo_subset_Icc_self hp⟩).eval (R.input n t k) := by
      rw [root, hpI]
    rw [hroot, hpI, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hw : (R.tree ⟨p, Ioo_subset_Icc_self hp⟩).weight ⟨h, none⟩ ≠ 0 :=
      (R.weight_tree_pos hR (p := ⟨p, Ioo_subset_Icc_self hp⟩) hp.1 hp.2 _).ne'
    -- Lemma 7.2 (`transport:leaf-map`) at the leaf `(h, old)`, of weight `(1 - p) w_h`
    have key := MeanTree.sandwich_derivLabel_eq_smul_leafMap (A := R.input n t k)
      (R.tree ⟨p, Ioo_subset_Icc_self hp⟩) hw (CFC.log (R.relRatio n t k h))
    rw [ContinuousLinearMap.map_smul_of_tower, mul_smul_comm, smul_mul_assoc, ← tree_eq_itree]
    change (1 - p)⁻¹ • ((R.tree ⟨p, _⟩).eval (R.input n t k) ^ (-(1 / 2) : ℝ) *
      (R.tree ⟨p, _⟩).derivLabel (R.input n t k) ⟨h, none⟩ (R.input n t k ⟨h, none⟩ ^ (1 / 2 : ℝ) *
        CFC.log (R.relRatio n t k h) * R.input n t k ⟨h, none⟩ ^ (1 / 2 : ℝ)) *
      (R.tree ⟨p, _⟩).eval (R.input n t k) ^ (-(1 / 2) : ℝ)) = _
    rw [key, weight_tree_old, smul_smul, ← mul_assoc,
      inv_mul_cancel₀ (by linarith [hp.2] : (1 - p) ≠ 0), one_mul]

/-! ## D7.16 The exact formula for `-∂_p log N²` -/

omit [Fintype V] [DecidableEq V] [DecidableEq H] [∀ h, DecidableEq (C h)] [Fintype H] in
theorem conjTranspose_imagPow_mul_imagPow {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) (u : ℝ) : (imagPow M u)ᴴ * imagPow M u = 1 := by
  have hlog : (CFC.log M).IsHermitian := by
    unfold CFC.log; exact cfc_predicate _ _
  exact mul_eq_one_comm.mp (hermitianUnitaryPath_mul_conjTranspose _ hlog _)

omit [Fintype V] [DecidableEq V] [DecidableEq H] [∀ h, DecidableEq (C h)] [Fintype H] in
/-- D7.16.6: `⟨ψ, Φ(Z) ψ⟩ = Tr(Φ^*(|ψ⟩⟨ψ|) Z)`. -/
theorem star_dotProduct_mulVec_eq_trace_traceAdjointMap {m : Type*} [Fintype m]
    (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) (Z : Matrix m m ℂ) (w : m → ℂ) :
    star w ⬝ᵥ (Φ Z *ᵥ w) = (traceAdjointMap Φ (vecMulVec w (star w)) * Z).trace := by
  rw [trace_traceAdjointMap_mul, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
    dotProduct_comm]

omit [Fintype H] in
theorem posDef_root [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (q : ℝ) : (R.root n t k q).PosDef :=
  MeanTree.posDef_eval (R.posDef_input hR ht hcomm) _

omit [Fintype H] in
/-- D7.16.7: for `0 < p < 1` every `σ_{j,u}` is a density matrix on `𝒮_k`. -/
theorem isSymDensity_state [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : R.CrossBandCommute n t k) {pre : Config n k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k) (hpre : pre ≠ 0) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : Leaf H C) (u : ℝ) :
    IsSymDensity n (R.state n t k pre p j u) := by
  have hIn := R.posDef_input hR ht hcomm
  have hroot : R.root n t k p = (R.tree p).eval (R.input n t k) := by
    rw [root, Set.projIcc_val]
  have hM : (R.root n t k p).PosDef := R.posDef_root hR ht hcomm p
  set w := imagPow (R.root n t k p) u *ᵥ R.v n t k pre p with hw_def
  have hst : R.state n t k pre p j u = (R.tree p).leafDual (R.input n t k) j
      (vecMulVec w (star w)) := rfl
  obtain ⟨hpsd, htr, -⟩ := leafDual_posSemidef_trace hIn (R.tree p) j
    (posSemidef_vecMulVec_self_star w)
  refine ⟨hst ▸ hpsd, ?_, fun π => ?_⟩
  -- `Tr σ_{j,u} = ⟨ψ, Φ_j(I) ψ⟩ = ‖ψ‖² = 1` (`Φ_j` unital, `𝓜^{-iu}` unitary)
  · rw [hst, htr (R.weight_tree_pos hR hp0 hp1 j), trace_vecMulVec, dotProduct_comm, hw_def,
      star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_imagPow_mul_imagPow,
      one_mulVec]
    exact Matrix.Transport.star_dotProduct_filteredVector hM hpre
  -- supported on `𝒮_k`: every input commutes with the copy permutations, so `Φ_j` is a right
  -- module map over them and `Φ_j^*` a left one, and `ψ ∈ 𝒮_k`
  · set Z := Replicas.U (fun v => Fin (n v)) k Finset.univ π
    have hZ : Z = permOp (TensorPower.copyPerm (SiteConfig n) k) π :=
      Replicas.U_univ_eq (fun v => Fin (n v)) k π
    have hZin : ∀ j, Commute Z (R.input n t k j) := fun j => hZ ▸ R.commute_permOp_input k π j
    have hZM : Commute Z (R.root n t k p) := hroot ▸ MeanTree.commute_eval_right hZin _
    have hpre' : Z *ᵥ pre = pre := by
      have hmem : pre ∈ invariantSubspace (TensorPower.copyPerm (SiteConfig n) k) := by
        rw [← Replicas.S_eq]; exact hpreS
      rw [hZ]; exact hmem π
    have hwZ : Z *ᵥ w = w := by
      rw [hw_def, mulVec_mulVec, (Matrix.Transport.commute_imagPow hZM u).eq, ← mulVec_mulVec,
        Round.v, Matrix.Transport.mulVec_filteredVector hM hZM hpre']
    rw [hst, MeanTree.leafDual, ← traceAdjointMap_mul_left
      (fun X => MeanTree.leafMap_mul_right hIn hZin (R.tree p) j X), mul_vecMulVec, hwZ]

/-- D7.16 (`transport:norm-derivative`, `transport:exact-derivative`). For `0 < p < 1` and
nonzero `pre ∈ 𝒮_k`:
`-∂_p log N² = ⟨v, g_s(ad_{log 𝓜})(HH) v⟩ = ∑_h w_h ∫ m_s(u) Tr(σ_{h,u} log C_h) du`, with
`⟨v, g_s(ad_{log 𝓜})(HH) v⟩ = ∫ m_s(u) ⟨𝓜^{-iu} v, HH 𝓜^{-iu} v⟩ du`; `σ_{j,u}` is a density
matrix for all `j, u`. -/
theorem step_7_16 [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) {pre : Config n k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k) (hpre : pre ≠ 0) {p : ℝ}
    (hp : p ∈ Ioo 0 1) :
    let pI : I := ⟨p, Ioo_subset_Icc_self hp⟩
    let HH := ∑ h, R.histTree.weight h • (R.tree pI).leafMap (R.input n t k) ⟨h, none⟩
      (CFC.log (R.relRatio n t k h))
    let ψ := fun u => imagPow (R.root n t k p) u *ᵥ R.v n t k pre p
    HasDerivAt (fun q => -Real.log (R.normSq n t k pre q))
      (∫ u, m (1 / 4) u * (star (ψ u) ⬝ᵥ (HH *ᵥ ψ u)).re) p ∧
    ∫ u, m (1 / 4) u * (star (ψ u) ⬝ᵥ (HH *ᵥ ψ u)).re = R.exactDerivative n t k pre pI ∧
    ∀ j u, IsSymDensity n (R.state n t k pre pI j u) := by
  intro pI HH ψ
  have hpI : (projIcc (0 : ℝ) 1 zero_le_one p : I) = pI :=
    projIcc_of_mem _ (Ioo_subset_Icc_self hp)
  have hroot : R.root n t k p = (R.tree pI).eval (R.input n t k) := by rw [root, hpI]
  obtain ⟨-, D, hD, hDH⟩ := R.step_7_15 hR ht hcomm hp
  refine ⟨?_, ?_, fun j u => R.isSymDensity_state hR ht hcomm hpreS hpre hp.1 hp.2 j u⟩
  -- D7.16.1–D7.16.5: Daleckii–Krein in the eigenbasis of `𝓜`, the bracket is
  -- `g_s(log x_r − log x_t)`, and Lemma 7.3 (1) turns it into `∫ m_s(u) 𝓜^{iu} HH 𝓜^{-iu} du`
  · have h := Matrix.Transport.hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt
      (R.posDef_root hR ht hcomm) hD hpre
    rw [hDH] at h
    exact h
  -- D7.16.6: insert `HH = ∑_h w_h Φ_{(h,old)}(log C_h)` (D7.15) and move each `Φ` to its dual
  · have hMh : (R.root n t k p).IsHermitian := (R.posDef_root hR ht hcomm p).isHermitian
    have hint : ∀ h, Integrable fun u : ℝ => m (1 / 4) u *
        (star (ψ u) ⬝ᵥ ((R.tree pI).leafMap (R.input n t k) ⟨h, none⟩
          (CFC.log (R.relRatio n t k h)) *ᵥ ψ u)).re :=
      fun h => Matrix.Transport.integrable_fourierWeight_mul_quadForm hMh _ _
    have htr : ∀ h u, (R.state n t k pre pI ⟨h, none⟩ u * CFC.log (R.relRatio n t k h)).trace =
        star (ψ u) ⬝ᵥ ((R.tree pI).leafMap (R.input n t k) ⟨h, none⟩
          (CFC.log (R.relRatio n t k h)) *ᵥ ψ u) := fun h u => by
      have := star_dotProduct_mulVec_eq_trace_traceAdjointMap
        ((R.tree pI).leafMap (R.input n t k) ⟨h, none⟩).toLinearMap
        (CFC.log (R.relRatio n t k h)) (ψ u)
      rw [ContinuousLinearMap.coe_coe] at this
      exact this.symm
    simp only [exactDerivative, htr]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun h _ => (hint h).const_mul (R.histTree.weight h)]
    congr 1
    funext u
    simp only [HH, sum_mulVec, dotProduct_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mulVec, dotProduct_smul, Complex.smul_re]
    ring

end Round

end AreaLaw.Transport
