import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SubsystemTransport
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.GroupedCopies
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.IsotypicDimension
import AreaLawForMathlib.Analysis.Matrix.ReducedVectorState

/-!
# Splitting the copies of a tensor power

A split `Fin m ⊕ Fin r ≃ Fin k` of the copies identifies `V^{⊗k}` with `V^{⊗m} ⊗ V^{⊗r}`, compatibly
with the copy permutations of subsystems.
-/

open Matrix PermutationRepresentation
open scoped Kronecker

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype X] [DecidableEq X]

/-- A label occurring on a permutation module has dimension at most its dimension. -/
theorem dim_le_card_of_labelProj_ne_zero [Fintype G] (φ : G →* Equiv.Perm X) {l : IrrepLabel G}
    (h : labelProj φ l ≠ 0) : l.dim ≤ Fintype.card X := by
  refine (dim_le_finrank_of_invariant (φ := φ) (W := LinearMap.range (toLin' (labelProj φ l))) l
    (by rintro g _ ⟨v, rfl⟩; exact ⟨permOp φ g *ᵥ v, by
      simp only [toLin'_apply, mulVec_mulVec, (commute_labelProj_permOp φ l g).eq]⟩)
    (by rintro _ ⟨v, rfl⟩; simp only [toLin'_apply, mulVec_mulVec, labelProj_mul_self])
    (by rwa [Ne, LinearMap.range_eq_bot, ← map_zero toLin', toLin'.injective.eq_iff])).trans ?_
  exact (Submodule.finrank_le _).trans_eq (Module.finrank_fintype_fun_eq_card ℂ)

/-- Label observables transport like the label projectors along `X ≃ Y × Z`. -/
theorem reindex_labelObservable_eq {Y Z : Type*} [Fintype G] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (Φ : X ≃ Y × Z) {φ : G →* Equiv.Perm X}
    {ψ : G →* Equiv.Perm Y}
    (h : ∀ l, reindex Φ Φ (labelProj φ l) = labelProj ψ l ⊗ₖ (1 : Matrix Z Z ℂ))
    (f : IrrepLabel G → ℝ) :
    reindex Φ Φ (labelObservable φ f) = labelObservable ψ f ⊗ₖ (1 : Matrix Z Z ℂ) := by
  ext p q
  have hl := fun l => congrFun (congrFun (h l) p) q
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply] at hl
  simp only [labelObservable, reindex_apply, submatrix_apply, kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hl, Finset.sum_mul, mul_assoc]

omit [DecidableEq X] in
/-- `reindex` is multiplicative. -/
theorem reindex_mul_reindex {Y : Type*} [Fintype Y] (Φ : X ≃ Y) (A B : Matrix X X ℂ) :
    reindex Φ Φ (A * B) = reindex Φ Φ A * reindex Φ Φ B := by
  simp only [reindex_apply, submatrix_mul_equiv]

end PermutationRepresentation

namespace TensorPower

variable {F : Type*} [DecidableEq F] (ι : F → Type*) {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)

theorem groupHom₁_apply_inl (a : Equiv.Perm (Fin m)) (i : Fin m) :
    groupHom₁ e a (e (.inl i)) = e (.inl (a i)) := by
  simp [groupHom₁, youngHom, Equiv.permCongr_apply]

theorem groupHom₁_apply_inr (a : Equiv.Perm (Fin m)) (j : Fin r) :
    groupHom₁ e a (e (.inr j)) = e (.inr j) := by
  simp [groupHom₁, youngHom, Equiv.permCongr_apply]

theorem groupHom₂_apply_inl (b : Equiv.Perm (Fin r)) (i : Fin m) :
    groupHom₂ e b (e (.inl i)) = e (.inl i) := by
  simp [groupHom₂, youngHom, Equiv.permCongr_apply]

theorem groupHom₂_apply_inr (b : Equiv.Perm (Fin r)) (j : Fin r) :
    groupHom₂ e b (e (.inr j)) = e (.inr (b j)) := by
  simp [groupHom₂, youngHom, Equiv.permCongr_apply]

/-- The split with the two groups exchanged. -/
def swapSplit : Fin r ⊕ Fin m ≃ Fin k := (Equiv.sumComm _ _).trans e

/-- The second-group permutations are the first-group permutations of the swapped split. -/
theorem groupHom₂_eq : groupHom₂ e = groupHom₁ (swapSplit e) := by
  ext b x : 2
  obtain ⟨y, rfl⟩ := e.surjective x
  rcases y with i | j <;> simp [groupHom₂, groupHom₁, youngHom, Equiv.permCongr_apply, swapSplit]

/-- `V^{⊗k} ≅ V^{⊗m} ⊗ V^{⊗r}` along the split `e` of the copies. -/
def copySplit : Config k ι ≃ Config m ι × Config r ι :=
  (Equiv.arrowCongr e.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

omit [DecidableEq F] in
@[simp]
theorem copySplit_apply_fst (x : Config k ι) (i : Fin m) :
    (copySplit ι e x).1 i = x (e (.inl i)) := by
  simp [copySplit, Equiv.arrowCongr_apply]

omit [DecidableEq F] in
@[simp]
theorem copySplit_apply_snd (x : Config k ι) (j : Fin r) :
    (copySplit ι e x).2 j = x (e (.inr j)) := by
  simp [copySplit, Equiv.arrowCongr_apply]

/-- Under `copySplit`, the first-group permutations of `T` act on the first factor. -/
theorem copySplit_subsystemPerm_groupHom₁ (T : Finset F) (a : Equiv.Perm (Fin m))
    (x : Config k ι) :
    copySplit ι e (subsystemPerm k ι T (groupHom₁ e a) x) =
      prodLeft (Config r ι) (subsystemPerm m ι T) a (copySplit ι e x) := by
  have h1 : ∀ i, (groupHom₁ e a)⁻¹ (e (.inl i)) = e (.inl (a⁻¹ i)) := fun i => by
    rw [← map_inv, groupHom₁_apply_inl]
  have h2 : ∀ j, (groupHom₁ e a)⁻¹ (e (.inr j)) = e (.inr j) := fun j => by
    rw [← map_inv, groupHom₁_apply_inr]
  ext i f
  · simp [subsystemPerm_apply, h1]
  · simp [subsystemPerm_apply, h2]

variable [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- The first-group label projectors of `T` are those of `T` on `V^{⊗m}`, tensored with the
identity on `V^{⊗r}`. -/
theorem labelProj_groupHom₁_eq (T : Finset F) (α : IrrepLabel (Equiv.Perm (Fin m))) :
    reindex (copySplit ι e) (copySplit ι e)
        (labelProj ((subsystemPerm k ι T).comp (groupHom₁ e)) α) =
      labelProj (subsystemPerm m ι T) α ⊗ₖ (1 : Matrix (Config r ι) (Config r ι) ℂ) := by
  rw [← labelProj_prodLeft, labelProj_of_intertwine (φ := (subsystemPerm k ι T).comp
    (groupHom₁ e)) (copySplit ι e) (fun a x => (copySplit_subsystemPerm_groupHom₁ ι e T a x).symm)]

/-! ## Sub-subsystems -/

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
/-- Under `splitEquiv` of `S`, the copy permutations of `T ⊆ S` act on `S^{⊗m}` as those of the
sub-subsystem `T ⊆ S`. -/
theorem splitEquiv_subsystemPerm_of_subset {S T : Finset F} (hT : T ⊆ S)
    (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    splitEquiv ι m S (subsystemPerm m ι T σ x) =
      prodLeft (Fin m → ComplConfig ι S)
        (subsystemPerm m (fun f : {f // f ∈ S} => ι f) (T.subtype (· ∈ S))) σ
        (splitEquiv ι m S x) := by
  ext j f
  · simp [splitEquiv, subsystemPerm_apply]
  · simp [splitEquiv, subsystemPerm_apply, show (f : F) ∉ T from fun h => f.2 (hT h)]

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
/-- Under `splitEquiv` of `S`, the copy permutations of `T` disjoint from `S` act on the
complement factor only. -/
theorem splitEquiv_subsystemPerm_of_disjoint {S T : Finset F} (hT : Disjoint T S)
    (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    splitEquiv ι m S (subsystemPerm m ι T σ x) =
      ((splitEquiv ι m S x).1,
        subsystemPerm m (fun f : {f // f ∉ S} => ι f) (T.subtype (· ∉ S)) σ
          (splitEquiv ι m S x).2) := by
  ext j f
  · simp [splitEquiv, subsystemPerm_apply,
      show (f : F) ∉ T from fun h => Finset.disjoint_left.mp hT h f.2]
  · simp [splitEquiv, subsystemPerm_apply]

/-- `V^{⊗k} ≅ S^{⊗m} ⊗ ((Sᶜ)^{⊗m} ⊗ V^{⊗r})`: the first group of copies of the region `S`
split off. -/
def goodSplit (S : Finset F) :
    Config k ι ≃ (Fin m → SubConfig ι S) × ((Fin m → ComplConfig ι S) × Config r ι) :=
  (copySplit ι e).trans ((Equiv.prodCongr (splitEquiv ι m S) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _))

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
/-- Under `goodSplit S`, the first-group permutations of `T ⊆ S` act on `S^{⊗m}` as those of the
sub-subsystem `T ⊆ S`. -/
theorem goodSplit_subsystemPerm_of_subset {S T : Finset F} (hT : T ⊆ S)
    (a : Equiv.Perm (Fin m)) (x : Config k ι) :
    goodSplit ι e S (subsystemPerm k ι T (groupHom₁ e a) x) =
      prodLeft ((Fin m → ComplConfig ι S) × Config r ι)
        (subsystemPerm m (fun f : {f // f ∈ S} => ι f) (T.subtype (· ∈ S))) a
        (goodSplit ι e S x) := by
  simp only [goodSplit, Equiv.trans_apply, copySplit_subsystemPerm_groupHom₁, prodLeft_apply,
    Equiv.prodCongr_apply, Prod.map, splitEquiv_subsystemPerm_of_subset ι hT,
    Equiv.prodAssoc_apply, Equiv.refl_apply]

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
/-- Under `goodSplit S`, the first-group permutations of `T` disjoint from `S` fix the
`S^{⊗m}` coordinate. -/
theorem goodSplit_subsystemPerm_of_disjoint {S T : Finset F} (hT : Disjoint T S)
    (a : Equiv.Perm (Fin m)) (x : Config k ι) :
    goodSplit ι e S (subsystemPerm k ι T (groupHom₁ e a) x) =
      ((goodSplit ι e S x).1,
        Equiv.prodCongr (subsystemPerm m (fun f : {f // f ∉ S} => ι f) (T.subtype (· ∉ S)) a)
          (Equiv.refl (Config r ι)) (goodSplit ι e S x).2) := by
  simp only [goodSplit, Equiv.trans_apply, copySplit_subsystemPerm_groupHom₁, prodLeft_apply,
    Equiv.prodCongr_apply, Prod.map, splitEquiv_subsystemPerm_of_disjoint ι hT,
    Equiv.prodAssoc_apply, Equiv.refl_apply]

set_option synthInstance.maxSize 256 in
/-- The first-group label projectors of `T ⊆ S` are those of the sub-subsystem `T ⊆ S` of
`S^{⊗m}`, tensored with the identity. -/
theorem labelProj_goodSplit_eq {S T : Finset F} (hT : T ⊆ S) (α : IrrepLabel (Equiv.Perm (Fin m))) :
    reindex (goodSplit ι e S) (goodSplit ι e S)
        (labelProj ((subsystemPerm k ι T).comp (groupHom₁ e)) α) =
      labelProj (subsystemPerm m (fun f : {f // f ∈ S} => ι f) (T.subtype (· ∈ S))) α ⊗ₖ
        (1 : Matrix ((Fin m → ComplConfig ι S) × Config r ι)
          ((Fin m → ComplConfig ι S) × Config r ι) ℂ) := by
  rw [← labelProj_prodLeft, labelProj_of_intertwine (φ := (subsystemPerm k ι T).comp
    (groupHom₁ e)) (goodSplit ι e S)
    (fun a x => (goodSplit_subsystemPerm_of_subset ι e hT a x).symm)]

/-- Under `goodSplit S`, a vector invariant under the first-group permutations of `T ∪ T₂`
(`T ⊆ S`, `T₂` disjoint from `S`) satisfies `u(π a, z) = u(a, τ z)` for the action `π` of the
sub-subsystem `T ⊆ S` and a permutation `τ` of the other factor. -/
theorem goodSplit_apply_perm {S T T₂ : Finset F} (hT : T ⊆ S) (h2 : Disjoint T₂ S)
    {v : Config k ι → ℂ}
    (hv : v ∈ invariantSubspace ((subsystemPerm k ι (T ∪ T₂)).comp (groupHom₁ e)))
    (g : Equiv.Perm (Fin m)) (a : Fin m → SubConfig ι S)
    (z : (Fin m → ComplConfig ι S) × Config r ι) :
    v ((goodSplit ι e S).symm
        (subsystemPerm m (fun f : {f // f ∈ S} => ι f) (T.subtype (· ∈ S)) g a, z)) =
      v ((goodSplit ι e S).symm (a, (Equiv.prodCongr
        (subsystemPerm m (fun f : {f // f ∉ S} => ι f) (T₂.subtype (· ∉ S)) g)
        (Equiv.refl (Config r ι))).symm z)) := by
  have hTT₂ : Disjoint T T₂ := Finset.disjoint_of_subset_left hT h2.symm
  set κ := Equiv.prodCongr (subsystemPerm m (fun f : {f // f ∉ S} => ι f) (T₂.subtype (· ∉ S)) g)
    (Equiv.refl (Config r ι))
  set x₀ := (goodSplit ι e S).symm (a, κ.symm z)
  have hinv : v (subsystemPerm k ι (T ∪ T₂) (groupHom₁ e g) x₀) = v x₀ := by
    simpa [permOp_mulVec, Function.comp_apply, map_inv, inv_inv] using congrFun (hv g⁻¹) x₀
  rw [subsystemPerm_union k ι hTT₂, Equiv.Perm.mul_apply] at hinv
  have h1 : goodSplit ι e S (subsystemPerm k ι T₂ (groupHom₁ e g) x₀) = (a, z) := by
    rw [goodSplit_subsystemPerm_of_disjoint ι e h2, Equiv.apply_symm_apply]
    exact Prod.ext rfl (κ.apply_symm_apply z)
  have h2' : goodSplit ι e S (subsystemPerm k ι T (groupHom₁ e g)
      (subsystemPerm k ι T₂ (groupHom₁ e g) x₀)) =
      (subsystemPerm m (fun f : {f // f ∈ S} => ι f) (T.subtype (· ∈ S)) g a, z) := by
    rw [goodSplit_subsystemPerm_of_subset ι e hT, h1, prodLeft_apply]
  rw [← h2', Equiv.symm_apply_apply, hinv]

end TensorPower
