import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic

/-!
# Regions of a spin chain

The index layer for mixed multipartite states.  Sites are an abstract `Fintype σ` with a
dependent family of local spaces `loc : σ → Type*`; a *region* is a plain `Finset σ`; the
Hilbert-space index of a region is the subtype-Pi `Reg loc S := ∀ i : S, loc i`.

The design is cast-free by construction: the local family is indexed by the *ambient* site
type while region indices are subtypes over it, so `loc ↑(⟨↑i, _⟩ : T)` and `loc ↑i` are
definitionally equal and every regrouping map typechecks with no `cast`, no `▸`.

This file provides the index combinators (`restr`, `glue`) and the equivalences between
region index types (`glueEquiv`, `splitEquiv`, `unionEquiv`, `sdiffEquiv`) that the partial
trace in `Arealaw.PTrace` is built on.

## Implementation notes

`restr` is Mathlib's `Finset.restrict₂`, but kept behind a region-language name of its own:
`Finset.restrict₂` carries `@[simp]`, so spelling it directly unfolds every restriction into
raw subtype applications and steps past the simp pack below.

Every equivalence here carries its own `_apply`/`_symm_apply` lemmas, written out rather
than generated: `Reg` is a Pi type, so `@[simps]` would state them pointwise at a site,
where consumers index matrices by a whole configuration.  Where a site index is
unavoidable the membership proof is an argument, so callers never rebuild it.

Regions are compared by `Finset` equality throughout; `regEquivOfEq` names the transport
that would otherwise be re-derived with `▸`.
-/

namespace Arealaw

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}

/-- The Hilbert-space index of the region `S`: a configuration assigns to every site of `S`
a basis label of its local space. -/
abbrev Reg (loc : σ → Type*) (S : Finset σ) := ∀ i : S, loc i

variable {S T U : Finset σ}

/-- Restrict a configuration on `T` to a subregion `S ⊆ T`: Mathlib's `Finset.restrict₂`
under a region-language name. -/
def restr (h : S ⊆ T) (z : Reg loc T) : Reg loc S := Finset.restrict₂ h z

/-- Glue a configuration on `S` with one on `T \ S` to a configuration on `T`. -/
def glue (x : Reg loc S) (z : Reg loc (T \ S)) : Reg loc T :=
  fun j => if hj : (j : σ) ∈ S then x ⟨j, hj⟩ else z ⟨j, Finset.mem_sdiff.2 ⟨j.2, hj⟩⟩

/-! ## Simp pack for the region combinators

These are the rewrites every partial-trace proof consumes, and the equations the
equivalences below are assembled from.  Proved once, so that downstream files never
re-derive the `dif_pos`/`dif_neg` case split. -/

section
omit [DecidableEq σ]

/-- Restricting to the same region does nothing. -/
@[simp] theorem restr_refl (z : Reg loc S) : restr (Finset.Subset.refl S) z = z := rfl

/-- Restriction is transitive. -/
@[simp] theorem restr_restr (hST : S ⊆ T) (hTU : T ⊆ U) (w : Reg loc U) :
    restr hST (restr hTU w) = restr (hST.trans hTU) w := rfl

end

/-- Gluing then restricting to the subregion returns the subregion part. -/
@[simp] theorem restr_glue (h : S ⊆ T) (x : Reg loc S) (z : Reg loc (T \ S)) :
    restr h (glue x z) = x :=
  funext fun i => dif_pos i.2

/-- Gluing with the empty complement changes nothing. -/
@[simp] theorem glue_sdiff_self (x : Reg loc T) (z : Reg loc (T \ T)) : glue x z = x :=
  restr_glue Finset.Subset.rfl x z

/-- Gluing then restricting to the complement returns the complement part. -/
@[simp] theorem restr_glue_compl (x : Reg loc S) (z : Reg loc (T \ S)) :
    restr Finset.sdiff_subset (glue x z) = z :=
  funext fun i => dif_neg (Finset.mem_sdiff.1 i.2).2

/-- A configuration is recovered from its two restrictions. -/
@[simp] theorem glue_restr (h : S ⊆ T) (w : Reg loc T) :
    glue (restr h w) (restr Finset.sdiff_subset w) = w :=
  funext fun j => by simp [restr, glue]

/-- With `S ⊆ T`, `glue` reads all of `x`, hence is injective in the subregion argument.
The hypothesis is necessary: without it `glue` ignores `x` on `S \ T`, and injectivity
fails already for `σ = Unit`, `loc _ = Bool`, `S = {()}`, `T = ∅`. -/
theorem glue_left_injective (h : S ⊆ T) (z : Reg loc (T \ S)) :
    Function.Injective fun x : Reg loc S => glue (T := T) x z :=
  Function.LeftInverse.injective fun x => restr_glue h x z

/-- `glue` reads all of its complement argument, so it is injective there unconditionally,
unlike `glue_left_injective`, which needs `S ⊆ T`. -/
theorem glue_right_injective (x : Reg loc S) :
    Function.Injective fun z : Reg loc (T \ S) => glue (T := T) x z :=
  Function.LeftInverse.injective (restr_glue_compl x)

/-! ## Equivalences between region index types -/

/-- `glue` and the two restrictions assemble to an equivalence
`Reg S × Reg (T \ S) ≃ Reg T`. -/
def glueEquiv (h : S ⊆ T) : Reg loc S × Reg loc (T \ S) ≃ Reg loc T where
  toFun p := glue p.1 p.2
  invFun w := (restr h w, restr Finset.sdiff_subset w)
  left_inv p := Prod.ext (restr_glue h p.1 p.2) (restr_glue_compl p.1 p.2)
  right_inv := glue_restr h

@[simp] theorem glueEquiv_apply (h : S ⊆ T) (p : Reg loc S × Reg loc (T \ S)) :
    glueEquiv h p = glue p.1 p.2 := rfl

@[simp] theorem glueEquiv_symm_apply (h : S ⊆ T) (w : Reg loc T) :
    (glueEquiv h).symm w = (restr h w, restr Finset.sdiff_subset w) := rfl

/-- For `S ⊆ T ⊆ U`, the two-step complement `(T \ S) × (U \ T)` regroups to the one-step
complement `U \ S`. -/
def splitEquiv (hST : S ⊆ T) (hTU : T ⊆ U) :
    Reg loc (T \ S) × Reg loc (U \ T) ≃ Reg loc (U \ S) where
  toFun p := fun j =>
    if hj : (j : σ) ∈ T then p.1 ⟨j, by grind⟩ else p.2 ⟨j, by grind⟩
  invFun v :=
    (restr (Finset.sdiff_subset_sdiff hTU le_rfl) v, restr (Finset.sdiff_subset_sdiff le_rfl hST) v)
  left_inv p := by ext1 <;> funext i <;> simp [restr, Finset.mem_sdiff.1 i.2]
  right_inv v := funext fun j => by by_cases hj : (j : σ) ∈ T <;> simp [restr, hj]

theorem splitEquiv_apply_fst (hST : S ⊆ T) (hTU : T ⊆ U) (p : Reg loc (T \ S) × Reg loc (U \ T))
    (j : ↥(U \ S)) (hj : (j : σ) ∈ T \ S) :
    splitEquiv hST hTU p j = p.1 ⟨j, hj⟩ := dif_pos (Finset.mem_sdiff.1 hj).1

theorem splitEquiv_apply_snd (hST : S ⊆ T) (hTU : T ⊆ U) (p : Reg loc (T \ S) × Reg loc (U \ T))
    (j : ↥(U \ S)) (hj : (j : σ) ∈ U \ T) :
    splitEquiv hST hTU p j = p.2 ⟨j, hj⟩ := dif_neg (Finset.mem_sdiff.1 hj).2

theorem splitEquiv_symm_apply_fst (hST : S ⊆ T) (hTU : T ⊆ U) (v : Reg loc (U \ S)) (i : ↥(T \ S))
    (hi : (i : σ) ∈ U \ S) : ((splitEquiv hST hTU).symm v).1 i = v ⟨i, hi⟩ := rfl

theorem splitEquiv_symm_apply_snd (hST : S ⊆ T) (hTU : T ⊆ U) (v : Reg loc (U \ S)) (i : ↥(U \ T))
    (hi : (i : σ) ∈ U \ S) : ((splitEquiv hST hTU).symm v).2 i = v ⟨i, hi⟩ := rfl

/-- Gluing in two steps agrees with gluing once, along `splitEquiv`. -/
theorem glue_splitEquiv (hST : S ⊆ T) (hTU : T ⊆ U) (x : Reg loc S) (z : Reg loc (T \ S))
    (w : Reg loc (U \ T)) :
    glue x (splitEquiv hST hTU (z, w)) = glue (T := U) (glue (T := T) x z) w := by
  grind [glue, splitEquiv]

section
omit [DecidableEq σ]

/-- Equal regions have equivalent index types. -/
def regEquivOfEq (hst : S = T) : Reg loc S ≃ Reg loc T where
  toFun := restr (le_of_eq hst.symm)
  invFun := restr (le_of_eq hst)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem regEquivOfEq_apply (hst : S = T) (z : Reg loc S) :
    regEquivOfEq hst z = restr (le_of_eq hst.symm) z := rfl

@[simp] theorem regEquivOfEq_symm_apply (hst : S = T) (w : Reg loc T) :
    (regEquivOfEq (loc := loc) hst).symm w = restr (le_of_eq hst) w := rfl

end

/-- The complement of `A` inside `A ∪ B` is `B`, as index types. -/
def sdiffEquiv {A B : Finset σ} (hd : Disjoint A B) : Reg loc B ≃ Reg loc ((A ∪ B) \ A) where
  toFun y j := y ⟨j, (Finset.union_sdiff_cancel_left hd).subset j.2⟩
  invFun v i := v ⟨i, (Finset.union_sdiff_cancel_left hd).symm.subset i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sdiffEquiv_apply {A B : Finset σ} (hd : Disjoint A B) (y : Reg loc B)
    (j : ↥((A ∪ B) \ A)) (hj : (j : σ) ∈ B) : sdiffEquiv hd y j = y ⟨j, hj⟩ := rfl

theorem sdiffEquiv_symm_apply {A B : Finset σ} (hd : Disjoint A B) (v : Reg loc ((A ∪ B) \ A))
    (i : ↥B) (hi : (i : σ) ∈ (A ∪ B) \ A) : (sdiffEquiv hd).symm v i = v ⟨i, hi⟩ := rfl

/-- A configuration on a disjoint union is a pair of configurations. -/
def unionEquiv {A B : Finset σ} (hd : Disjoint A B) :
    Reg loc (A ∪ B) ≃ Reg loc A × Reg loc B where
  toFun z := (restr Finset.subset_union_left z, restr Finset.subset_union_right z)
  invFun p := glue p.1 (sdiffEquiv hd p.2)
  left_inv := glue_restr Finset.subset_union_left
  right_inv _ :=
    Prod.ext (restr_glue Finset.subset_union_left _ _)
      ((sdiffEquiv hd).injective (restr_glue_compl _ _))

@[simp] theorem unionEquiv_apply {A B : Finset σ} (hd : Disjoint A B) (z : Reg loc (A ∪ B)) :
    unionEquiv hd z = (restr Finset.subset_union_left z, restr Finset.subset_union_right z) :=
  rfl

/-- `unionEquiv.symm` glues on the left factor, whose complement in `A ∪ B` is `B`. -/
@[simp] theorem unionEquiv_symm_apply {A B : Finset σ} (hd : Disjoint A B) (x : Reg loc A)
    (y : Reg loc B) : (unionEquiv hd).symm (x, y) = glue x (sdiffEquiv hd y) := rfl

/-- `unionEquiv.symm` read from the right factor: gluing on `B` transports `A` along
`(A ∪ B) \ B = A`.  Not definitional: `glue` branches on `B` where `unionEquiv` branches on
`A`, so disjointness is used. -/
theorem unionEquiv_symm_apply_eq_glue_right {A B : Finset σ} (hd : Disjoint A B) (x : Reg loc A)
    (y : Reg loc B) : (unionEquiv hd).symm (x, y) =
      glue y (regEquivOfEq (Finset.union_sdiff_cancel_right hd).symm x) := by
  funext j
  by_cases hj : (j : σ) ∈ A
  · simp [glue, restr, hj, Finset.disjoint_left.1 hd hj]
  · simp [glue, sdiffEquiv, hj, (Finset.mem_union.1 j.2).resolve_left hj]

/-- `unionEquiv` with the two regions swapped is `unionEquiv` followed by swapping the pair,
after transporting along `B ∪ A = A ∪ B`. -/
theorem unionEquiv_comm {A B : Finset σ} (hd : Disjoint A B) :
    unionEquiv (loc := loc) hd.symm = (regEquivOfEq (Finset.union_comm B A)).trans
      ((unionEquiv hd).trans (Equiv.prodComm _ _)) :=
  Equiv.ext fun _ => rfl

/-- Configurations on the full chain are exactly the sections of the local family. -/
def univEquiv [Fintype σ] : Reg loc (Finset.univ : Finset σ) ≃ (∀ i, loc i) where
  toFun z i := z ⟨i, Finset.mem_univ i⟩
  invFun f i := f i.1
  left_inv _ := rfl
  right_inv _ := rfl

section
omit [DecidableEq σ]

@[simp] theorem univEquiv_apply [Fintype σ] (z : Reg loc (Finset.univ : Finset σ)) (i : σ) :
    univEquiv z i = z ⟨i, Finset.mem_univ i⟩ := rfl

@[simp] theorem univEquiv_symm_apply [Fintype σ] (f : ∀ i, loc i) (i : (Finset.univ : Finset σ)) :
    (univEquiv (loc := loc)).symm f i = f i.1 := rfl

end

/-! ## Cardinality -/

/-- The empty region has exactly one configuration. -/
instance : Unique (Reg loc (∅ : Finset σ)) := Pi.uniqueOfIsEmpty _

variable [∀ i, Fintype (loc i)]

/-- The dimension of a region is the product of the local dimensions. -/
theorem card_reg (S : Finset σ) : Fintype.card (Reg loc S) = ∏ i ∈ S, Fintype.card (loc i) :=
  Fintype.card_pi.trans (Finset.prod_coe_sort S fun i => Fintype.card (loc i))

/-- The dimension of a disjoint union is the product of the dimensions. -/
theorem card_reg_union {A B : Finset σ} (hd : Disjoint A B) :
    Fintype.card (Reg loc (A ∪ B)) = Fintype.card (Reg loc A) * Fintype.card (Reg loc B) :=
  (Fintype.card_congr (unionEquiv hd)).trans (Fintype.card_prod _ _)

/-- With constant local dimension `d`, a region of `k` sites has dimension `d ^ k`. -/
theorem card_reg_const {d : ℕ} (hd : ∀ i, Fintype.card (loc i) = d) (S : Finset σ) :
    Fintype.card (Reg loc S) = d ^ S.card := by
  simp [hd]

end Arealaw
