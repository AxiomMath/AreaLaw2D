/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/RegionSplit.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.MovementEtaRegional

/-!
# Splitting configurations along a region

This file completes the regional-coordinate interface used by the skew-symbol estimate.  It
extends the split-coordinate structure already used by the regional movement estimate, while
continuing to use the repository's concrete `Entropy.localLift`.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

namespace IsRegionSplit

variable {D : Finset V} {A B : Type*} {φ : RegionConfig n D ≃ A}
  {e : SiteConfig n ≃ A × B}

/-- In coordinates splitting `D` from its complement, a regional lift is `K ⊗ 1`. -/
theorem localLift_submatrix (he : IsRegionSplit D φ e) [DecidableEq B]
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    (localLift D K).submatrix e.symm e.symm =
      K.submatrix φ.symm φ.symm ⊗ₖ (1 : Matrix B B ℂ) := by
  ext p q
  rw [submatrix_apply, localLift_apply, kroneckerMap_apply, one_apply, submatrix_apply,
    he.restrict_symm, he.restrict_symm]
  have hsnd := he.snd (e.symm p) (e.symm q)
  simp only [Equiv.apply_symm_apply] at hsnd
  by_cases h : p.2 = q.2
  · rw [if_pos (hsnd.mp h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hsnd.mpr h')), if_neg h, mul_zero]

omit [Fintype V] [DecidableEq V] in
/-- Composing equivalences on both factors preserves a regional split. -/
theorem trans_prodCongr (he : IsRegionSplit D φ e) {A' B' : Type*}
    (ψ : A ≃ A') (χ : B ≃ B') :
    IsRegionSplit D (φ.trans ψ) (e.trans (Equiv.prodCongr ψ χ)) := by
  constructor
  · intro σ
    simp [he.fst σ]
  · intro σ τ
    rw [← he.snd σ τ]
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd]
    exact χ.injective.eq_iff

end IsRegionSplit

omit [DecidableEq V] in
/-- Matrix expectations are invariant under a change of finite coordinates. -/
theorem star_dotProduct_submatrix_mulVec {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (M : Matrix X X ℂ) (θ : X → ℂ) :
    star (θ ∘ e.symm) ⬝ᵥ (M.submatrix e.symm e.symm *ᵥ (θ ∘ e.symm)) =
      star θ ⬝ᵥ (M *ᵥ θ) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply, Pi.star_apply]
  refine Fintype.sum_equiv e.symm _ _ fun y => ?_
  congr 1
  exact Fintype.sum_equiv e.symm _ _ fun y' => rfl

/-- Configurations on a disjoint cover `V = D ∪ D'` as a pair of regional configurations. -/
def regionSplitEquiv {D D' : Finset V} (hDD : Disjoint D D')
    (hcov : ∀ v, v ∈ D ∨ v ∈ D') :
    SiteConfig n ≃ RegionConfig n D × RegionConfig n D' where
  toFun σ := (fun v => σ v, fun v => σ v)
  invFun p v := if h : v ∈ D then p.1 ⟨v, h⟩ else p.2 ⟨v, (hcov v).resolve_left h⟩
  left_inv σ := by
    funext v
    by_cases h : v ∈ D <;> simp [h]
  right_inv p := by
    ext v
    · simp [v.2]
    · have : v.1 ∉ D := fun hv => Finset.disjoint_left.mp hDD hv v.2
      simp [this]

omit [Fintype V] in
/-- The canonical coordinates of a disjoint regional cover split along the first region. -/
theorem isRegionSplit_regionSplitEquiv {D D' : Finset V} (hDD : Disjoint D D')
    (hcov : ∀ v, v ∈ D ∨ v ∈ D') :
    IsRegionSplit D (Equiv.refl _) (regionSplitEquiv (n := n) hDD hcov) := by
  constructor
  · intro σ
    rfl
  · intro σ τ
    change (fun v : {v // v ∈ D'} => σ v) = (fun v : {v // v ∈ D'} => τ v) ↔ _
    constructor
    · intro h v hv
      exact congrFun h ⟨v, (hcov v).resolve_left hv⟩
    · intro h
      funext v
      exact h v.1 fun hv => Finset.disjoint_left.mp hDD hv v.2

end Entropy
