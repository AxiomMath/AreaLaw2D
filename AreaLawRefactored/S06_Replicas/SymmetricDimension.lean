import AreaLawRefactored.S06_Replicas.Setup
import Mathlib.Data.Sym.Card

/-!
# §6 The dimension of the symmetric subspace (D6.1 Output)
-/

namespace AreaLaw.Replicas

open PermutationRepresentation

section Words

variable {Y : Type*} {k : ℕ}

/-- The multiset of letters of a word `x : Fin k → Y`. -/
noncomputable def wordSym (x : Fin k → Y) : Sym Y k := ⟨Finset.univ.val.map x, by simp⟩

theorem wordSym_comp (x : Fin k → Y) (σ : Equiv.Perm (Fin k)) :
    wordSym (x ∘ σ) = wordSym x := by
  apply Subtype.ext
  simp only [wordSym, Fin.univ_val_map]
  exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm x)

theorem wordSym_surjective : Function.Surjective (wordSym (Y := Y) (k := k)) := by
  intro s
  have h : s.1.toList.length = k := by simp
  refine ⟨fun i => s.1.toList.get (Fin.cast h.symm i), Subtype.ext ?_⟩
  simp only [wordSym, Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList s.1]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.get_eq_getElem]
  rfl

theorem exists_perm_of_wordSym_eq {x y : Fin k → Y} (h : wordSym x = wordSym y) :
    ∃ σ : Equiv.Perm (Fin k), x = y ∘ σ := by
  classical
  have hc : ∀ c, Fintype.card {i // x i = c} = Fintype.card {i // y i = c} := by
    intro c
    have e1 : ∀ z : Fin k → Y, Fintype.card {i // z i = c} =
        Multiset.card (Multiset.filter (fun a => c = z a) Finset.univ.val) := fun z => by
      rw [Fintype.card_subtype, Finset.card, Finset.filter_val]
      exact congrArg _ (Multiset.filter_congr fun _ _ => eq_comm)
    have := congrArg (fun s : Sym Y k => Multiset.count c s.1) h
    simp only [wordSym, Multiset.count_map] at this
    rw [e1, e1, this]
  let e : ∀ c, {i // x i = c} ≃ {i // y i = c} := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv y)), ?_⟩
  funext i
  simp only [Equiv.coe_trans, Function.comp_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply]
  exact ((e (x i) ⟨i, rfl⟩).2).symm

end Words

variable {I : Type*} [DecidableEq I] (ι : I → Type*) (k : ℕ)
  [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

theorem mem_S_iff (v : Config ι k → ℂ) :
    v ∈ S ι k ↔ ∀ (x : Config ι k) (σ : Equiv.Perm (Fin k)), v (x ∘ σ) = v x := by
  have key : ∀ (σ : Equiv.Perm (Fin k)) (x : Config ι k),
      (copyPerm ι k Finset.univ σ).symm x = x ∘ σ := fun σ x =>
    (Equiv.symm_apply_eq _).2 (by ext j f; simp)
  simp only [S, mem_invariantSubspace, permOp_mulVec]
  exact ⟨fun h x σ => by simpa [key] using congrFun (h σ) x, fun h σ => funext fun x => by
    simp [key, h]⟩

/-- The symmetric vectors are the functions of the multiset of a configuration. -/
noncomputable def symEquiv : S ι k ≃ₗ[ℂ] (Sym ((f : I) → ι f) k → ℂ) where
  toFun v s := v.1 (wordSym_surjective s).choose
  invFun g := ⟨g ∘ wordSym, (mem_S_iff ι k _).2 fun x σ => by simp [wordSym_comp]⟩
  map_add' v w := rfl
  map_smul' c v := rfl
  left_inv v := by
    apply Subtype.ext
    funext x
    obtain ⟨σ, hσ⟩ := exists_perm_of_wordSym_eq (wordSym_surjective (wordSym x)).choose_spec
    simp only [Function.comp_apply]
    rw [hσ]
    exact (mem_S_iff ι k v.1).1 v.2 x σ
  right_inv g := by
    funext s
    simp [(wordSym_surjective s).choose_spec]

/-- D6.1. `D_k = dim 𝒮_k = binom(k+d−1, d−1)`. -/
theorem D_eq_choose (hd : 0 < Fintype.card ((f : I) → ι f)) :
    D ι k = (k + Fintype.card ((f : I) → ι f) - 1).choose
      (Fintype.card ((f : I) → ι f) - 1) := by
  rw [D, (symEquiv ι k).finrank_eq, Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_choose,
    Nat.add_comm (Fintype.card _) k]
  exact Nat.choose_symm_of_eq_add (by omega)

end AreaLaw.Replicas
