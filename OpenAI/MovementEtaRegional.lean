/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MovementEtaRegional.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.ConditionalMovementRegional
import OpenAI.FiniteProductConditional

/-!
# The movement entropy in region form

The exponent in the conditional movement estimate is the sum
`S(x|P) + S(x|Y)`.  This file identifies the coordinate expression
`Entropy.movementEta (Entropy.frameVector h θ)` with the same expression written using the
repository's canonical `FiniteProduct.entropy`, and with conditional mutual information.

Unlike the source file, this port uses `FiniteProduct.reducedPure` and Physlib's
`Matrix.traceLeft`/`traceRight` directly; it does not introduce QICLean's duplicate
`regionState` or partial-trace API.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Entropy

open ConditionalMovement ConditionalMovement.QuantumSSA

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Coordinates split along `D` when their first coordinate is the restriction to `D`,
up to `φ`, and equality of second coordinates is equality off `D`. -/
structure IsRegionSplit (D : Finset V) {A B : Type*} (φ : RegionConfig n D ≃ A)
    (e : SiteConfig n ≃ A × B) : Prop where
  fst : ∀ σ, (e σ).1 = φ fun v : {v // v ∈ D} => σ v
  snd : ∀ σ τ, (e σ).2 = (e τ).2 ↔ ∀ v ∉ D, σ v = τ v

namespace IsRegionSplit

variable {D : Finset V} {A B : Type*} {φ : RegionConfig n D ≃ A}
  {e : SiteConfig n ≃ A × B}

omit [Fintype V] [DecidableEq V] in
theorem siteConfig_eq_of_mem_of_not_mem {σ τ : SiteConfig n}
    (h1 : ∀ v ∈ D, σ v = τ v) (h2 : ∀ v ∉ D, σ v = τ v) : σ = τ := by
  funext v
  by_cases hv : v ∈ D
  · exact h1 v hv
  · exact h2 v hv

omit [Fintype V] [DecidableEq V] in
theorem restrict_symm (he : IsRegionSplit D φ e) (p : A × B) :
    (fun v : {v // v ∈ D} => e.symm p v) = φ.symm p.1 := by
  have h := he.fst (e.symm p)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

omit [Fintype V] [DecidableEq V] in
theorem symm_apply_mem (he : IsRegionSplit D φ e) (p : A × B) {v : V}
    (hv : v ∈ D) : e.symm p v = φ.symm p.1 ⟨v, hv⟩ :=
  congrFun (he.restrict_symm p) ⟨v, hv⟩

/-- The first marginal in any regional split is the canonical finite-product reduced state. -/
theorem traceRight_vecMulVec (he : IsRegionSplit D φ e) [Fintype B]
    (θ : SiteConfig n → ℂ) :
    Matrix.traceRight (vecMulVec (θ ∘ e.symm) (star (θ ∘ e.symm))) =
      (FiniteProduct.reducedPure (fun v => Fin (n v)) (WithLp.toLp 2 θ) D).submatrix
        φ.symm φ.symm := by
  ext a₀ a₀'
  rw [submatrix_apply]
  set a := φ.symm a₀
  set a' := φ.symm a₀'
  have ha : a₀ = φ a := (Equiv.apply_symm_apply φ a₀).symm
  have ha' : a₀' = φ a' := (Equiv.apply_symm_apply φ a₀').symm
  rw [ha, ha']
  rw [Matrix.traceRight, FiniteProduct.reducedPure, FiniteProduct.reducedMatrix_apply]
  set c : B → FiniteProduct.Configuration (fun v => Fin (n v)) Dᶜ :=
    fun b v => e.symm (φ a, b) v
  have hc : Function.Bijective c := by
    constructor
    · intro b b' hbb
      have h := (he.snd (e.symm (φ a, b)) (e.symm (φ a, b'))).mpr fun v hv =>
        congrFun hbb ⟨v, Finset.mem_compl.mpr hv⟩
      simpa using h
    · intro w
      refine
        ⟨(e ((FiniteProduct.splitEquiv (fun v => Fin (n v)) D).symm (a, w))).2,
          funext fun v => ?_⟩
      have hσ : e.symm (φ a,
          (e ((FiniteProduct.splitEquiv (fun v => Fin (n v)) D).symm (a, w))).2) =
          (FiniteProduct.splitEquiv (fun v => Fin (n v)) D).symm (a, w) := by
        rw [Equiv.symm_apply_eq]
        refine Prod.ext ?_ rfl
        rw [he.fst]
        change φ a = φ _
        congr 1
        funext u
        exact (FiniteProduct.splitEquiv_symm_apply_of_mem
          (fun v => Fin (n v)) D a w u.1 u.2).symm
      simp only [c, hσ]
      exact FiniteProduct.splitEquiv_symm_apply_of_notMem
        (fun v => Fin (n v)) D a w v.1 (Finset.mem_compl.mp v.2)
  have hpt : ∀ (a'' : RegionConfig n D) (b : B),
      e.symm (φ a'', b) =
        (FiniteProduct.splitEquiv (fun v => Fin (n v)) D).symm (a'', c b) := by
    intro a'' b
    refine siteConfig_eq_of_mem_of_not_mem (D := D) (fun v hv => ?_) (fun v hv => ?_)
    · rw [he.symm_apply_mem _ hv,
        FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ v hv,
        Equiv.symm_apply_apply]
    · rw [FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ v hv]
      exact (he.snd (e.symm (φ a'', b)) (e.symm (φ a, b))).mp (by simp) v hv
  simp only [Matrix.of_apply, vecMulVec_apply, Function.comp_apply, Pi.star_apply]
  simp_rw [hpt]
  exact Function.Bijective.sum_comp hc (fun w =>
    θ ((FiniteProduct.splitEquiv (fun v => Fin (n v)) D).symm (a, w)) *
      star (θ ((FiniteProduct.splitEquiv (fun v => Fin (n v)) D).symm (a', w))))

end IsRegionSplit

/-- The movement entropy `S(x|P) + S(x|Y)`, using actual reduced-state entropies. -/
noncomputable def regionalMovementEta (P x Y : Finset V)
    (θ : EuclideanSpace ℂ (SiteConfig n)) : ℝ :=
  FiniteProduct.entropy (fun v => Fin (n v)) θ (P ∪ x) -
      FiniteProduct.entropy (fun v => Fin (n v)) θ P +
    (FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ Y) -
      FiniteProduct.entropy (fun v => Fin (n v)) θ Y)

/-- The conditional-movement trace entropy is the repository's von Neumann entropy. -/
theorem traceEntropy_eq_vonNeumann {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    traceEntropy A = Arealaw.vonNeumann hA := by
  rw [traceEntropy_spectral, Arealaw.vonNeumann_eq_H]
  rfl

/-- Trace entropy agrees with finite-product entropy after a basis reindexing. -/
theorem traceEntropy_eq_entropy_of_eq_submatrix {m : Type*} [Fintype m] [DecidableEq m]
    {D : Finset V} (θ : EuclideanSpace ℂ (SiteConfig n)) (A : Matrix m m ℂ)
    (hA : A.IsHermitian) (e : m ≃ RegionConfig n D)
    (h : A = (FiniteProduct.reducedPure (fun v => Fin (n v)) θ D).submatrix e e) :
    traceEntropy A = FiniteProduct.entropy (fun v => Fin (n v)) θ D := by
  calc
    traceEntropy A = Arealaw.vonNeumann hA := traceEntropy_eq_vonNeumann _ _
    _ = Arealaw.vonNeumann
        ((FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v)) θ D).submatrix e).isHermitian :=
      Arealaw.vonNeumann_congr hA
        ((FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v)) θ D).submatrix e).isHermitian h
    _ = FiniteProduct.entropy (fun v => Fin (n v)) θ D := by
      simpa [FiniteProduct.entropy] using
        Arealaw.vonNeumann_submatrix_equiv
          (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v)) θ D).isHermitian e

/-- Trace entropy agrees with finite-product entropy for the canonical reduced matrix. -/
theorem traceEntropy_eq_entropy_of_eq_reducedPure {D : Finset V}
    (θ : EuclideanSpace ℂ (SiteConfig n))
    (A : Matrix (RegionConfig n D) (RegionConfig n D) ℂ)
    (hA : A.IsHermitian)
    (h : A = FiniteProduct.reducedPure (fun v => Fin (n v)) θ D) :
    traceEntropy A = FiniteProduct.entropy (fun v => Fin (n v)) θ D := by
  calc
    traceEntropy A = Arealaw.vonNeumann hA := traceEntropy_eq_vonNeumann _ _
    _ = FiniteProduct.entropy (fun v => Fin (n v)) θ D := by
      simpa [FiniteProduct.entropy] using
        Arealaw.vonNeumann_congr hA
          (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v)) θ D).isHermitian h

namespace FourPartition

variable {P x Y F : Finset V} (h : FourPartition P x Y F)
include h

omit [Fintype V] [DecidableEq V] in
/-- Exchanging the outer parts keeps a four-part partition. -/
theorem swap : FourPartition F x Y P where
  Px := h.xF.symm
  PY := h.YF.symm
  PF := h.PF.symm
  xY := h.xY
  xF := h.Px.symm
  YF := h.PY.symm
  cover v := by
    rcases h.cover v with h1 | h1 | h1 | h1 <;> simp [h1]

omit [Fintype V] in
theorem isRegionSplit_XY :
    IsRegionSplit (x ∪ Y) (unionEquivXY (n := n) h) (frameEquiv h) where
  fst _ := rfl
  snd σ τ := by
    have hs := frameEquiv_symm_eq_off_XY h (frameEquiv h σ) (frameEquiv h τ)
    simp only [Equiv.symm_apply_apply] at hs
    exact hs.symm

omit [Fintype V] in
theorem isRegionSplit_PX :
    IsRegionSplit (P ∪ x) (unionEquivXP (n := n) h)
      ((frameEquiv h).trans (Equiv.prodProdProdComm _ _ _ _).symm) where
  fst _ := rfl
  snd σ τ := by
    have hs := frameEquiv_symm_eq_off_PX h (frameEquiv h σ) (frameEquiv h τ)
    simp only [Equiv.symm_apply_apply] at hs
    exact hs.symm

theorem movementMarginalXU_frameVector (θ : EuclideanSpace ℂ (SiteConfig n)) :
    movementMarginalXU (frameVector h θ) =
      (FiniteProduct.reducedPure (fun v => Fin (n v)) θ (x ∪ Y)).submatrix
        (unionEquivXY h).symm (unionEquivXY h).symm := by
  have hs := h.isRegionSplit_XY.traceRight_vecMulVec θ.ofLp
  rw [WithLp.toLp_ofLp] at hs
  exact hs

theorem movementMarginalXP_frameVector (θ : EuclideanSpace ℂ (SiteConfig n)) :
    movementMarginalXP (frameVector h θ) =
      (FiniteProduct.reducedPure (fun v => Fin (n v)) θ (P ∪ x)).submatrix
        (unionEquivXP h).symm (unionEquivXP h).symm := by
  have hs := h.isRegionSplit_PX.traceRight_vecMulVec θ.ofLp
  rw [WithLp.toLp_ofLp] at hs
  exact hs

/-- The `Y` marginal in movement coordinates is the canonical state on `Y`. -/
theorem frameMarginalY_eq (θ : EuclideanSpace ℂ (SiteConfig n)) :
    frameMarginalY h θ = FiniteProduct.reducedPure (fun v => Fin (n v)) θ Y := by
  rw [frameMarginalY, movementMarginalXU_frameVector]
  simp only [FiniteProduct.reducedPure]
  change ((FiniteProduct.reducedMatrix (fun v => Fin (n v))
      (vecMulVec θ.ofLp (star θ.ofLp)) (x ∪ Y)).submatrix
        (FiniteProduct.unionEquiv (fun v => Fin (n v)) x Y h.xY).symm
        (FiniteProduct.unionEquiv (fun v => Fin (n v)) x Y h.xY).symm).traceLeft =
    FiniteProduct.reducedMatrix (fun v => Fin (n v))
      (vecMulVec θ.ofLp (star θ.ofLp)) Y
  exact FiniteProduct.traceLeft_reducedMatrix_union (fun v => Fin (n v))
    (vecMulVec θ.ofLp (star θ.ofLp)) x Y h.xY

/-- The `P` marginal in movement coordinates is the canonical state on `P`. -/
theorem frameMarginalP_eq (θ : EuclideanSpace ℂ (SiteConfig n)) :
    frameMarginalP h θ = FiniteProduct.reducedPure (fun v => Fin (n v)) θ P := by
  rw [frameMarginalP, movementMarginalXP_frameVector]
  let ρ := FiniteProduct.reducedPure (fun v => Fin (n v)) θ (P ∪ x)
  let e := FiniteProduct.unionEquiv (fun v => Fin (n v)) P x h.Px
  have he : unionEquivXP (n := n) h = e.trans (Equiv.prodComm _ _) := rfl
  rw [he]
  change Matrix.traceLeft ((ρ.submatrix e.symm e.symm).reindex
    (Equiv.prodComm _ _) (Equiv.prodComm _ _)) = _
  rw [← Matrix.traceRight_eq_traceLeft_reindex]
  simpa [ρ, FiniteProduct.reducedPure] using
    FiniteProduct.traceRight_reducedMatrix_union (fun v => Fin (n v))
      (vecMulVec θ.ofLp (star θ.ofLp)) P x h.Px

/-- The exponent in the coordinate form of Lemma 5.1 is the regional movement entropy. -/
theorem movementEta_frameVector (θ : EuclideanSpace ℂ (SiteConfig n)) :
    movementEta (frameVector h θ) = regionalMovementEta P x Y θ := by
  have hXP := movementMarginalXP_posSemidef (frameVector h θ)
  have hXU := movementMarginalXU_posSemidef (frameVector h θ)
  have e1 : traceEntropy (movementMarginalXP (frameVector h θ)) =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (P ∪ x) :=
    traceEntropy_eq_entropy_of_eq_submatrix θ _ hXP.isHermitian
      (unionEquivXP h).symm (h.movementMarginalXP_frameVector θ)
  have e2 : traceEntropy (movementMarginalXU (frameVector h θ)) =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ Y) :=
    traceEntropy_eq_entropy_of_eq_submatrix θ _ hXU.isHermitian
      (unionEquivXY h).symm (h.movementMarginalXU_frameVector θ)
  have e3 : traceEntropy (ptrL (movementMarginalXP (frameVector h θ))) =
      FiniteProduct.entropy (fun v => Fin (n v)) θ P :=
    traceEntropy_eq_entropy_of_eq_reducedPure θ _ hXP.traceLeft.isHermitian
      (h.frameMarginalP_eq θ)
  have e4 : traceEntropy (ptrL (movementMarginalXU (frameVector h θ))) =
      FiniteProduct.entropy (fun v => Fin (n v)) θ Y :=
    traceEntropy_eq_entropy_of_eq_reducedPure θ _ hXU.traceLeft.isHermitian
      (h.frameMarginalY_eq θ)
  rw [movementEta, conditionalEntropy, conditionalEntropy, e1, e2, e3, e4,
    regionalMovementEta]

theorem compl_union_xY : (x ∪ Y)ᶜ = F ∪ P := by
  ext v
  have hcov := h.cover v
  have hPx : v ∈ P → v ∉ x := fun hv => Finset.disjoint_left.mp h.Px hv
  have hPY : v ∈ P → v ∉ Y := fun hv => Finset.disjoint_left.mp h.PY hv
  have hxF : v ∈ x → v ∉ F := fun hv => Finset.disjoint_left.mp h.xF hv
  have hYF : v ∈ Y → v ∉ F := fun hv => Finset.disjoint_left.mp h.YF hv
  simp only [Finset.mem_compl, Finset.mem_union]
  tauto

theorem compl_Y : Yᶜ = x ∪ F ∪ P := by
  ext v
  have hcov := h.cover v
  have hxY : v ∈ x → v ∉ Y := fun hv => Finset.disjoint_left.mp h.xY hv
  have hPY : v ∈ P → v ∉ Y := fun hv => Finset.disjoint_left.mp h.PY hv
  have hYF : v ∈ Y → v ∉ F := fun hv => Finset.disjoint_left.mp h.YF hv
  simp only [Finset.mem_compl, Finset.mem_union]
  tauto

end FourPartition

variable {P x Y F : Finset V}

/-- `S(x|P) + S(x|Y) = I(x:F|P)` for a pure four-part state. -/
theorem regionalMovementEta_eq_cmi_left (h : FourPartition P x Y F)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    regionalMovementEta P x Y θ =
      FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ x F P := by
  have e1 : FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ Y) =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (F ∪ P) := by
    rw [← FiniteProduct.entropy_compl (fun v => Fin (n v)) θ (x ∪ Y),
      h.compl_union_xY]
  have e2 : FiniteProduct.entropy (fun v => Fin (n v)) θ Y =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ F ∪ P) := by
    rw [← FiniteProduct.entropy_compl (fun v => Fin (n v)) θ Y, h.compl_Y]
  rw [regionalMovementEta, e1, e2, Finset.union_comm P x,
    FiniteProduct.conditionalMutualInformation]
  ring

/-- `S(x|P) + S(x|Y) = I(x:F|Y)` for a pure four-part state. -/
theorem regionalMovementEta_eq_cmi_right (h : FourPartition P x Y F)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    regionalMovementEta P x Y θ =
      FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ x F Y := by
  have h' : FourPartition Y x P F :=
    ⟨h.xY.symm, h.PY.symm, h.YF, h.Px.symm, h.xF, h.PF,
      fun v => by
        rcases h.cover v with h1 | h1 | h1 | h1 <;> simp [h1]⟩
  rw [← regionalMovementEta_eq_cmi_left h', regionalMovementEta, regionalMovementEta,
    Finset.union_comm P x, Finset.union_comm Y x]
  ring

end Entropy
