import OpenAI.Statements

/-!
# Region states of a finite domain read on the site type `↥Λ`

Extends `Arealaw/Mixed.lean` (region entropies of `Arealaw.Reg`) and `OpenAI.pureState`: a
vector `ψ` on a finite domain `Λ ⊆ σ` is also a vector on the full chain of the site type `↥Λ`
(through `Arealaw.univEquiv`). A region `Q : Finset Λ` of that chain is the region
`Q.map (Embedding.subtype _) ⊆ Λ` of `σ`; the two marginals of `|ψ⟩⟨ψ|` agree after the
relabelling `regEquivMap Q` of configurations, so they have the same eigenvalues, the same
entropy and the same mutual informations.

## Main statements

* `Arealaw.ptrace_comp_univEquiv`: the marginal on `Q` is the relabelled marginal on the image.
* `Arealaw.regionEntropy_comp_univEquiv`, `Arealaw.mutualInfo_comp_univEquiv`.
-/

namespace Arealaw

open Matrix Finset

variable {σ : Type*} {loc : σ → Type*} {Λ : Finset σ}

/-- A region `Q` of the site type `↥Λ`, read as a region of `σ`, lies in `Λ`. -/
theorem map_subtype_subset_self (Q : Finset Λ) :
    Q.map (Function.Embedding.subtype (· ∈ Λ)) ⊆ Λ := fun x hx => by
  obtain ⟨y, -, rfl⟩ := mem_map.1 hx
  exact y.2

theorem mem_of_mem_map_subtype {Q : Finset Λ} {x : σ}
    (hx : x ∈ Q.map (Function.Embedding.subtype (· ∈ Λ))) :
    (⟨x, map_subtype_subset_self Q hx⟩ : Λ) ∈ Q := by
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  exact hy

variable [DecidableEq σ]

/-- Configurations of a region `Q` of the site type `↥Λ` are the configurations of its image
in `σ`. -/
def regEquivMap (Q : Finset Λ) :
    Reg (fun i : Λ => loc i) Q ≃ Reg loc (Q.map (Function.Embedding.subtype (· ∈ Λ))) where
  toFun x j := x ⟨⟨j.1, map_subtype_subset_self Q j.2⟩, mem_of_mem_map_subtype j.2⟩
  invFun y i := y ⟨i.1.1, mem_map_of_mem _ i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The configurations off `Q` in the chain `↥Λ` are the configurations of `Λ` off the image of
`Q`. -/
def regEquivMapCompl (Q : Finset Λ) :
    Reg (fun i : Λ => loc i) (univ \ Q) ≃
      Reg loc (Λ \ Q.map (Function.Embedding.subtype (· ∈ Λ))) where
  toFun z j := z ⟨⟨j.1, (mem_sdiff.1 j.2).1⟩, mem_sdiff.2 ⟨mem_univ _, fun h =>
    (mem_sdiff.1 j.2).2 (mem_map_of_mem _ h)⟩⟩
  invFun y i := y ⟨i.1.1, mem_sdiff.2 ⟨i.1.2, fun h => (mem_sdiff.1 i.2).2
    (mem_of_mem_map_subtype h)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem univEquiv_glue (Q : Finset Λ) (x : Reg (fun i : Λ => loc i) Q)
    (z : Reg (fun i : Λ => loc i) (univ \ Q)) :
    (univEquiv (glue x z) : Reg loc Λ) = glue (regEquivMap Q x) (regEquivMapCompl Q z) := by
  funext i
  by_cases hi : i ∈ Q
  · have : i.1 ∈ Q.map (Function.Embedding.subtype (· ∈ Λ)) := mem_map_of_mem _ hi
    simp only [univEquiv_apply, glue, dif_pos hi, dif_pos this]
    rfl
  · have : i.1 ∉ Q.map (Function.Embedding.subtype (· ∈ Λ)) := fun h =>
      hi (mem_of_mem_map_subtype h)
    simp only [univEquiv_apply, glue, dif_neg hi, dif_neg this]
    rfl

variable [∀ i, Fintype (loc i)] {𝕜 : Type*} [RCLike 𝕜]

/-- The marginal on a region `Q` of the chain `↥Λ` of `|ψ⟩⟨ψ|` is the marginal of `|ψ⟩⟨ψ|` on
the image of `Q`, relabelled by `regEquivMap Q`; in particular the two have the same
eigenvalues. -/
theorem ptrace_comp_univEquiv (ψ : Reg loc Λ → 𝕜) (Q : Finset Λ) :
    ptrace (subset_univ Q) (vecMulVec (ψ ∘ univEquiv) (star (ψ ∘ univEquiv))) =
      (ptrace (map_subtype_subset_self Q) (vecMulVec ψ (star ψ))).submatrix
        (regEquivMap Q) (regEquivMap Q) := by
  ext x y
  simp only [ptrace, of_apply, submatrix_apply, vecMulVec_apply, Pi.star_apply,
    Function.comp_apply]
  exact Fintype.sum_equiv (regEquivMapCompl Q) _ _ fun z => by
    rw [univEquiv_glue, univEquiv_glue]

variable [∀ i, DecidableEq (loc i)]

/-- The entropy of a region `Q` of the chain `↥Λ` in `|ψ⟩⟨ψ|` is the entropy of its image. -/
theorem regionEntropy_comp_univEquiv (ψ : Reg loc Λ → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hψ' : star (ψ ∘ univEquiv) ⬝ᵥ (ψ ∘ univEquiv) = 1) (Q : Finset Λ) :
    (OpenAI.pureState (ψ ∘ univEquiv) hψ').toSubState.regionEntropy (subset_univ Q) =
      (OpenAI.pureState ψ hψ).toSubState.regionEntropy (map_subtype_subset_self Q) := by
  have h : (OpenAI.pureState (ψ ∘ univEquiv) hψ').toSubState.restrict (subset_univ Q) =
      ((OpenAI.pureState ψ hψ).toSubState.restrict (map_subtype_subset_self Q)).submatrix
        (regEquivMap Q) :=
    SubState.ext (ptrace_comp_univEquiv ψ Q)
  rw [SubState.regionEntropy_def, h, SubState.entropy_submatrix, SubState.regionEntropy_def]

/-- The mutual information of two regions of the chain `↥Λ` in `|ψ⟩⟨ψ|` is that of their
images. -/
theorem mutualInfo_comp_univEquiv (ψ : Reg loc Λ → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hψ' : star (ψ ∘ univEquiv) ⬝ᵥ (ψ ∘ univEquiv) = 1) (Q Q' : Finset Λ) :
    (OpenAI.pureState (ψ ∘ univEquiv) hψ').toSubState.mutualInfo (subset_univ Q)
        (subset_univ Q') =
      (OpenAI.pureState ψ hψ).toSubState.mutualInfo (map_subtype_subset_self Q)
        (map_subtype_subset_self Q') := by
  simp only [SubState.mutualInfo_def, regionEntropy_comp_univEquiv ψ hψ hψ']
  congr 1
  exact (OpenAI.pureState ψ hψ).toSubState.regionEntropy_congr (map_union _ _) _ _

end Arealaw
