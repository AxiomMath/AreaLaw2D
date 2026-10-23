import OpenAI.AreaLaw
import OpenAI.CutTransport
import OpenAI.Statements3D
import OpenAI.SupportCounting

/-!
# The area law on cylinders over a planar domain

Target B.1 of `docs/3D/Targets.md`: a cylinder `Λ = Λ' × [0, h)` over a finite planar domain
`Λ' ⊂ ℤ²` is a planar system once each column `{u} × [0, h)` is read as one site of dimension
`q ^ h`, so Theorem 1.1 of [OAI265] (`OpenAI.area_law`) gives the area law on cylinders.

The column `(x₁, x₂)` of a site `x` of `ℤ³` identifies `Reg (Qudits3D q) Λ` with
`Reg (Qudits (q ^ h)) Λ'` through `finFunctionFinEquiv : (Fin h → Fin q) ≃ Fin (q ^ h)`.  The
terms of the interaction with the same column projection add up to one planar term; there are
at most `2 ^ (h (2R + 1)²)` of them, and a path in `Λ` projects to a walk in `Λ'` no longer
than it, so the planar interaction has range `R` and strength `2 ^ (h (2R + 1)²) max J 1`.
The Hamiltonian, the ground vector and the gap are relabelled, and so is the entropy of a union
of columns.  A cut `A` that splits columns is the union of the full columns `P × [0, h)` it
contains and a remainder `B`; subadditivity gives `S(A) ≤ S(P × [0, h)) + |B| log q`.  Each
column met by `B` carries a vertical crossing edge of `A`, so `|B| ≤ h |∂_Λ A|`, and each
planar crossing edge of `P` lifts to a horizontal crossing edge of `A`, so
`|∂_{Λ'} P| ≤ |∂_Λ A|`.

## Main statements

* `OpenAI.cylinderAreaLawOfPlanar3D`: `CylinderAreaLawOfPlanar3D` for every parameter set.
* `OpenAI.cylinderAreaLaw3D`: `CylinderAreaLaw3D` whenever `0 < Δ`, from `area_law`.

## Implementation notes

`CylinderAreaLaw3D` is not proved for every parameter set, and does not hold for all of them:
for `Δ ≤ 0` and `q ≥ 2`, the interaction `Φ = 0` with `E₀ = 0` satisfies the gap hypothesis for
every unit vector, and a unit vector maximally entangled across half of an `n × n × h` box has
entropy of order `n² h` against a boundary of order `n h`.
For `q = 0` and `h ≥ 1` the planar local dimension is `0`, where `area_law` does not apply but
the planar area law holds with constant `0`, since every region entropy is at most
`|A| log 0 = 0`.
-/

namespace OpenAI

open Arealaw Matrix SimpleGraph
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Cylinder

/-! ## Columns and cylinders -/

/-- The planar column `(x₁, x₂)` of a site of `ℤ³`. -/
abbrev column (x : ℤ × ℤ × ℤ) : ℤ × ℤ := (x.1, x.2.1)

/-- `S` is the cylinder `S' × [0, h)`: a site lies in `S` exactly when its column lies in `S'`
and its height in `[0, h)`.  This is the condition of `IsCylinderDomain3D`. -/
def IsCyl (h : ℕ) (S' : Finset (ℤ × ℤ)) (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∀ x : ℤ × ℤ × ℤ, x ∈ S ↔ (x.1, x.2.1) ∈ S' ∧ 0 ≤ x.2.2 ∧ x.2.2 < h

/-- The cylinder `S' × [0, h)` as a finite set. -/
noncomputable def cyl (h : ℕ) (S' : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  (S' ×ˢ Finset.Ico (0 : ℤ) h).image fun p => (p.1.1, p.1.2, p.2)

variable {h : ℕ}

/-- `cyl h S'` is the cylinder over `S'`. -/
theorem isCyl_cyl (h : ℕ) (S' : Finset (ℤ × ℤ)) : IsCyl h S' (cyl h S') := by
  intro x
  simp only [cyl, Finset.mem_image, Finset.mem_product, Finset.mem_Ico, Prod.exists]
  constructor
  · rintro ⟨a, b, c, ⟨hab, hc⟩, rfl⟩
    exact ⟨hab, hc⟩
  · rintro ⟨hx, hc⟩
    exact ⟨x.1, x.2.1, x.2.2, ⟨hx, hc⟩, rfl⟩

/-- The cylinder over `S'` has `|S'| h` sites. -/
theorem card_cyl (h : ℕ) (S' : Finset (ℤ × ℤ)) : (cyl h S').card = S'.card * h := by
  rw [cyl, Finset.card_image_of_injective, Finset.card_product, Int.card_Ico, sub_zero,
    Int.toNat_natCast]
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ he
  simp only [Prod.mk.injEq] at he ⊢
  exact ⟨⟨he.1, he.2.1⟩, he.2.2⟩

/-- Cylinders are monotone in their base. -/
theorem IsCyl.subset {S' T' : Finset (ℤ × ℤ)} {S T : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S)
    (hT : IsCyl h T' T) (hST : S' ⊆ T') : S ⊆ T := fun x hx => by
  rw [hS] at hx
  exact (hT x).2 ⟨hST hx.1, hx.2⟩

/-- The difference of two cylinders is the cylinder over the difference of their bases. -/
theorem IsCyl.sdiff {S' T' : Finset (ℤ × ℤ)} {S T : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S)
    (hT : IsCyl h T' T) : IsCyl h (T' \ S') (T \ S) := fun x => by
  simp only [Finset.mem_sdiff, hS x, hT x]
  tauto

/-- The column of a site of a cylinder lies in its base. -/
theorem IsCyl.column_mem {S' : Finset (ℤ × ℤ)} {S : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S)
    {x : ℤ × ℤ × ℤ} (hx : x ∈ S) : column x ∈ S' :=
  ((hS x).1 hx).1

/-! ## Regrouping the sites of a column -/

variable {q : ℕ}

/-- The relabelling of configurations: a configuration on the planar region `S'` with local
dimension `q ^ h` is a configuration on the cylinder `S = S' × [0, h)` with local dimension
`q`, reading the label of a column through `finFunctionFinEquiv`. -/
def colEquiv {S' : Finset (ℤ × ℤ)} {S : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S) :
    Reg (Qudits (q ^ h)) S' ≃ Reg (Qudits3D q) S where
  toFun f x := finFunctionFinEquiv.symm (f ⟨column x, hS.column_mem x.2⟩ : Fin (q ^ h))
    ⟨x.1.2.2.toNat, by have := ((hS x).1 x.2).2; omega⟩
  invFun g p := finFunctionFinEquiv fun k : Fin h =>
    g ⟨(p.1.1, p.1.2, (k : ℤ)), (hS _).2 ⟨p.2, show (0 : ℤ) ≤ (k : ℕ) by omega,
      show ((k : ℕ) : ℤ) < h by exact_mod_cast k.2⟩⟩
  left_inv f := by
    funext p
    refine (congrArg finFunctionFinEquiv (funext fun k => ?_)).trans
      (finFunctionFinEquiv.apply_symm_apply (f p))
    congr 1
  right_inv g := by
    funext x
    simp only [Equiv.symm_apply_apply]
    have h0 := ((hS x).1 x.2).2.1
    congr 1
    exact Subtype.ext (Prod.ext rfl (Prod.ext rfl (by simp [Int.toNat_of_nonneg h0])))

/-- The relabelling commutes with restriction to a subcylinder. -/
theorem restr_colEquiv {S' T' : Finset (ℤ × ℤ)} {S T : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S)
    (hT : IsCyl h T' T) (hST : S ⊆ T) (hST' : S' ⊆ T') (f : Reg (Qudits (q ^ h)) T') :
    restr hST (colEquiv hT f) = colEquiv hS (restr hST' f) := rfl

/-- The relabelling commutes with gluing. -/
theorem colEquiv_glue {S' T' : Finset (ℤ × ℤ)} {S T : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S)
    (hT : IsCyl h T' T) (hST' : S' ⊆ T') (x : Reg (Qudits (q ^ h)) S')
    (z : Reg (Qudits (q ^ h)) (T' \ S')) :
    colEquiv hT (glue x z) = glue (colEquiv hS x) (colEquiv (hS.sdiff hT) z) := by
  have hST := hS.subset hT hST'
  rw [← glue_restr hST (colEquiv hT (glue x z)), restr_colEquiv hS hT hST hST',
    restr_colEquiv (hS.sdiff hT) hT Finset.sdiff_subset Finset.sdiff_subset, restr_glue hST',
    restr_glue_compl]

/-- The relabelling commutes with extension by the identity. -/
theorem extendId_submatrix_colEquiv {𝕜 : Type*} [RCLike 𝕜] {S' T' : Finset (ℤ × ℤ)}
    {S T : Finset (ℤ × ℤ × ℤ)} (hS : IsCyl h S' S) (hT : IsCyl h T' T) (hST' : S' ⊆ T')
    (M : Matrix (Reg (Qudits3D q) S) (Reg (Qudits3D q) S) 𝕜) :
    extendId hST' (M.submatrix (colEquiv hS) (colEquiv hS)) =
      (extendId (hS.subset hT hST') M).submatrix (colEquiv hT) (colEquiv hT) := by
  ext w w'
  obtain ⟨⟨x, z⟩, rfl⟩ := (glueEquiv hST').surjective w
  obtain ⟨⟨x', z'⟩, rfl⟩ := (glueEquiv hST').surjective w'
  simp only [glueEquiv_apply, extendId_apply_glue, submatrix_apply, colEquiv_glue hS hT hST',
    EmbeddingLike.apply_eq_iff_eq]

/-- The relabelling preserves the entropy of a union of columns of a pure state. -/
theorem regionEntropy_pureState_colEquiv {𝕜 : Type*} [RCLike 𝕜] {P' Λ' : Finset (ℤ × ℤ)}
    {P Λ : Finset (ℤ × ℤ × ℤ)} (hP : IsCyl h P' P) (hΛ : IsCyl h Λ' Λ) (hPΛ' : P' ⊆ Λ')
    (hPΛ : P ⊆ Λ) (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hΩ' : star (Ω ∘ colEquiv hΛ) ⬝ᵥ (Ω ∘ colEquiv hΛ) = 1) :
    (pureState (Ω ∘ colEquiv hΛ) hΩ').regionEntropy hPΛ' =
      (pureState Ω hΩ).regionEntropy hPΛ := by
  rw [regionEntropy_pureState, regionEntropy_pureState]
  have hM : coeffMatrix P' (Ω ∘ colEquiv hΛ) =
      (coeffMatrix P Ω).submatrix (colEquiv hP) (colEquiv (hP.sdiff hΛ)) := by
    ext x z
    simp [colEquiv_glue hP hΛ hPΛ']
  rw [hM]
  set M := coeffMatrix P Ω
  have h1 : M.submatrix (colEquiv hP) (colEquiv (hP.sdiff hΛ)) =
      (M.submatrix (colEquiv hP) id).submatrix id (colEquiv (hP.sdiff hΛ)) := rfl
  have h2 : M.submatrix (colEquiv hP) id = ((Mᵀ).submatrix id (colEquiv hP))ᵀ := rfl
  rw [h1, EE_submatrix_id_equiv, h2, EE_transpose, EE_submatrix_id_equiv, EE_transpose]

/-! ## Projecting distances and supports -/

/-- Adjacency in the cubic lattice in coordinates: two coordinates agree and the third changes
by one. -/
theorem cubicLattice3D_adj_iff (x y : ℤ × ℤ × ℤ) :
    cubicLattice3D.Adj x y ↔
      (x.2.2 = y.2.2 ∧ (hasse ℤ □ hasse ℤ).Adj (column x) (column y)) ∨
        (column x = column y ∧ (x.2.2 + 1 = y.2.2 ∨ y.2.2 + 1 = x.2.2)) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  simp only [cubicLattice3D, boxProd_adj, hasse_adj, Order.covBy_iff_add_one_eq, Prod.mk.injEq]
  tauto

/-- A walk in the cubic lattice induced on a cylinder projects to a walk, no longer, in the
square lattice induced on its base: horizontal steps project to steps, vertical steps to
nothing. -/
theorem exists_walk_column {Λ' : Finset (ℤ × ℤ)} {Λ : Finset (ℤ × ℤ × ℤ)} (hΛ : IsCyl h Λ' Λ)
    {u v : (Λ : Set (ℤ × ℤ × ℤ))} (p : (cubicLattice3D.induce (Λ : Set (ℤ × ℤ × ℤ))).Walk u v) :
    ∃ p' : ((hasse ℤ □ hasse ℤ).induce (Λ' : Set (ℤ × ℤ))).Walk
        ⟨column u, hΛ.column_mem u.2⟩ ⟨column v, hΛ.column_mem v.2⟩,
      p'.length ≤ p.length := by
  induction p with
  | nil => exact ⟨Walk.nil, le_rfl⟩
  | @cons u w v hadj p ih =>
    obtain ⟨p', hp'⟩ := ih
    rw [Walk.length_cons]
    rcases (cubicLattice3D_adj_iff _ _).1 (induce_adj.1 hadj) with ⟨-, hc⟩ | ⟨hc, -⟩
    · exact ⟨Walk.cons (induce_adj.2 hc) p', by rw [Walk.length_cons]; omega⟩
    · refine ⟨p'.copy (Subtype.ext hc.symm) rfl, ?_⟩
      rw [Walk.length_copy]
      omega

/-- The planar domain distance between columns is at most the cubic domain distance. -/
theorem domainEDist_column_le {Λ' : Finset (ℤ × ℤ)} {Λ : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ) (x y : ℤ × ℤ × ℤ) :
    domainEDist Λ' (column x) (column y) ≤ domainEDist3D Λ x y := by
  by_cases hxy : x ∈ Λ ∧ y ∈ Λ
  · rw [domainEDist3D, dif_pos hxy, domainEDist_of_mem (hΛ.column_mem hxy.1)
      (hΛ.column_mem hxy.2)]
    rcases eq_or_ne ((cubicLattice3D.induce (Λ : Set (ℤ × ℤ × ℤ))).edist ⟨x, hxy.1⟩ ⟨y, hxy.2⟩)
      ⊤ with htop | htop
    · rw [htop]
      exact le_top
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top htop
    obtain ⟨p', hp'⟩ := exists_walk_column hΛ p
    rw [← hp]
    exact p'.edist_le.trans (by exact_mod_cast hp')
  · rw [domainEDist3D, dif_neg hxy]
    exact le_top

/-- The column projection of an admissible support of range `R` on a cylinder is an admissible
support of range `R` on its base. -/
theorem image_column_mem_supports {Λ' : Finset (ℤ × ℤ)} {Λ X : Finset (ℤ × ℤ × ℤ)} {R : ℕ}
    (hΛ : IsCyl h Λ' Λ) (hX : X ∈ supports3D Λ R) : X.image column ∈ supports Λ' R := by
  rw [supports3D, Finset.mem_filter, Finset.mem_powerset] at hX
  obtain ⟨hXΛ, hne, hdiam⟩ := hX
  rw [mem_supports_iff, domainEDiam_le_iff]
  refine ⟨fun c hc => ?_, hne.image _, fun c hc d hd => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact hΛ.column_mem (hXΛ hx)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
    exact (domainEDist_column_le hΛ x y).trans
      ((le_iSup₂_of_le (f := fun y _ => domainEDist3D Λ x y) y hy le_rfl).trans
        ((le_iSup₂_of_le (f := fun x _ => ⨆ y ∈ X, domainEDist3D Λ x y) x hx le_rfl).trans
          hdiam))

/-! ## The planar interaction -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A finite sum of square matrices relabels termwise. -/
theorem submatrix_finset_sum {ι m n : Type*} (s : Finset ι) (f : ι → Matrix n n 𝕜) (e : m → n) :
    (∑ i ∈ s, f i).submatrix e e = ∑ i ∈ s, (f i).submatrix e e := by
  ext a b
  simp [Matrix.sum_apply]

/-- The Hamiltonian on `ℤ³` as a sum over all `X ⊆ Λ`, without `attach`. -/
theorem hamiltonian3D_eq_sum (Λ : Finset (ℤ × ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜) :
    hamiltonian3D Λ Φ =
      ∑ X ∈ Λ.powerset, if hX : X ⊆ Λ then extendId hX (Φ X) else 0 := by
  rw [hamiltonian3D, ← Finset.sum_attach Λ.powerset
    (fun X => if hX : X ⊆ Λ then extendId hX (Φ X) else 0)]
  exact Finset.sum_congr rfl fun X _ => by rw [dif_pos (Finset.mem_powerset.1 X.2)]

/-- The planar Hamiltonian as a sum over all `X ⊆ Λ`, without `attach`. -/
theorem hamiltonian_eq_sum {d : ℕ} (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits d) X) (Reg (Qudits d) X) 𝕜) :
    hamiltonian Λ Φ = ∑ X ∈ Λ.powerset, if hX : X ⊆ Λ then extendId hX (Φ X) else 0 := by
  rw [hamiltonian, ← Finset.sum_attach Λ.powerset
    (fun X => if hX : X ⊆ Λ then extendId hX (Φ X) else 0)]
  exact Finset.sum_congr rfl fun X _ => by rw [dif_pos (Finset.mem_powerset.1 X.2)]

/-- The supports inside the cylinder over `X'` whose columns are exactly `X'`. -/
noncomputable def fibre (h : ℕ) (X' : Finset (ℤ × ℤ)) : Finset (Finset (ℤ × ℤ × ℤ)) :=
  (cyl h X').powerset.filter fun X => X.image column = X'

/-- Over a base `X' ⊆ Λ'`, the fibre consists of the subsets of the cylinder `Λ` with columns
`X'`. -/
theorem fibre_eq_filter {Λ' X' : Finset (ℤ × ℤ)} {Λ : Finset (ℤ × ℤ × ℤ)} (hΛ : IsCyl h Λ' Λ)
    (hX' : X' ⊆ Λ') : fibre h X' = Λ.powerset.filter fun X => X.image column = X' := by
  ext X
  simp only [fibre, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hX, he⟩
    exact ⟨hX.trans ((isCyl_cyl h X').subset hΛ hX'), he⟩
  · rintro ⟨hX, he⟩
    refine ⟨fun x hx => (isCyl_cyl h X' x).2 ⟨?_, ((hΛ x).1 (hX hx)).2⟩, he⟩
    rw [← he]
    exact Finset.mem_image_of_mem column hx

/-- The fibre over `X'` has at most `2 ^ (|X'| h)` members, the subsets of the cylinder over
`X'`. -/
theorem card_fibre_le (h : ℕ) (X' : Finset (ℤ × ℤ)) : (fibre h X').card ≤ 2 ^ (X'.card * h) := by
  rw [← card_cyl h X', ← Finset.card_powerset]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A term `Φ X`, extended to the cylinder over `X'` when `X` lies in it. -/
noncomputable def colTerm (h : ℕ)
    (Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜)
    (X' : Finset (ℤ × ℤ)) (X : Finset (ℤ × ℤ × ℤ)) :
    Matrix (Reg (Qudits3D q) (cyl h X')) (Reg (Qudits3D q) (cyl h X')) 𝕜 :=
  if hX : X ⊆ cyl h X' then extendId hX (Φ X) else 0

/-- **The planar interaction** of the column grouping: on the planar support `X'`, the sum of
the terms `Φ X` with column set `X'`, extended to the cylinder over `X'` and relabelled to
`q ^ h`-dimensional planar sites. -/
noncomputable def colInteraction (h : ℕ)
    (Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜)
    (X' : Finset (ℤ × ℤ)) : Matrix (Reg (Qudits (q ^ h)) X') (Reg (Qudits (q ^ h)) X') 𝕜 :=
  (∑ X ∈ fibre h X', colTerm h Φ X' X).submatrix (colEquiv (isCyl_cyl h X'))
    (colEquiv (isCyl_cyl h X'))

/-- **The Hamiltonians agree**: the planar Hamiltonian of `colInteraction` is the Hamiltonian
on the cylinder, relabelled. -/
theorem hamiltonian_colInteraction {Λ' : Finset (ℤ × ℤ)} {Λ : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ)
    (Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜) :
    hamiltonian Λ' (colInteraction h Φ) =
      (hamiltonian3D Λ Φ).submatrix (colEquiv hΛ) (colEquiv hΛ) := by
  rw [hamiltonian_eq_sum, hamiltonian3D_eq_sum,
    ← Finset.sum_fiberwise_of_maps_to (s := Λ.powerset) (t := Λ'.powerset)
      (g := fun X => X.image column) fun X hX => Finset.mem_powerset.2
        (Finset.image_subset_iff.2 fun x hx => hΛ.column_mem (Finset.mem_powerset.1 hX hx)),
    submatrix_finset_sum]
  refine Finset.sum_congr rfl fun X' hX' => ?_
  have hX'Λ' := Finset.mem_powerset.1 hX'
  have hc := (isCyl_cyl h X').subset hΛ hX'Λ'
  rw [dif_pos hX'Λ', colInteraction, extendId_submatrix_colEquiv (isCyl_cyl h X') hΛ hX'Λ',
    extendId_sum, submatrix_finset_sum, submatrix_finset_sum, ← fibre_eq_filter hΛ hX'Λ']
  refine Finset.sum_congr rfl fun X hX => ?_
  have hXc : X ⊆ cyl h X' := Finset.mem_powerset.1 (Finset.mem_filter.1 hX).1
  rw [colTerm, dif_pos hXc, extendId_extendId, dif_pos (hXc.trans hc)]

/-! ## Admissibility of the planar interaction -/

variable {R : ℕ} {J : ℝ}

/-- A planar term vanishes off the admissible planar supports. -/
theorem colInteraction_eq_zero {Λ' X' : Finset (ℤ × ℤ)} {Λ : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ)
    {Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜}
    (hΦ : IsAdmissible3D Λ R J Φ) (hX' : X' ⊆ Λ') (hs : X' ∉ supports Λ' R) :
    colInteraction h Φ X' = 0 := by
  rw [colInteraction, Finset.sum_eq_zero, submatrix_zero]
  · rfl
  intro X hX
  have hXc : X ⊆ cyl h X' := Finset.mem_powerset.1 (Finset.mem_filter.1 hX).1
  have he : X.image column = X' := (Finset.mem_filter.1 hX).2
  have hzero : Φ X = 0 := (hΦ X (hXc.trans ((isCyl_cyl h X').subset hΛ hX'))).2.2
    fun hXs => hs (he ▸ image_column_mem_supports hΛ hXs)
  rw [colTerm, dif_pos hXc, hzero, extendId_zero]

/-- **Admissibility transfers**: the planar interaction has range `R` and strength
`max J 1 · 2 ^ ((2R + 1)² h)`. -/
theorem isAdmissible_colInteraction {Λ' : Finset (ℤ × ℤ)} {Λ : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ)
    {Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜}
    (hΦ : IsAdmissible3D Λ R J Φ) :
    IsAdmissible Λ' R (max J 1 * 2 ^ ((2 * R + 1) ^ 2 * h)) (colInteraction h Φ) := by
  have hJ : 0 ≤ J := (norm_nonneg _).trans (hΦ ∅ (Finset.empty_subset _)).2.1
  intro X' hX'
  have hc := (isCyl_cyl h X').subset hΛ hX'
  have hXΛ : ∀ X ∈ fibre h X', X ⊆ Λ := fun X hX =>
    (Finset.mem_powerset.1 (Finset.mem_filter.1 hX).1).trans hc
  refine ⟨?_, ?_, colInteraction_eq_zero hΛ hΦ hX'⟩
  · refine IsHermitian.submatrix ?_ _
    refine (isSelfAdjoint_sum _ fun X hX => ?_).isHermitian
    rw [colTerm]
    split_ifs with hXc
    · exact (isHermitian_extendId _ (hΦ X (hXΛ X hX)).1).isSelfAdjoint
    · exact IsSelfAdjoint.zero _
  · have hpos : (0 : ℝ) < max J 1 * 2 ^ ((2 * R + 1) ^ 2 * h) := by positivity
    by_cases hs : X' ∈ supports Λ' R
    · rw [colInteraction, l2_opNorm_submatrix]
      have hterm : ∀ X ∈ fibre h X', ‖colTerm h Φ X' X‖ ≤ J := fun X hX => by
        rw [colTerm]
        split_ifs with hXc
        · exact (l2_opNorm_extendId_le hXc _).trans (hΦ X (hXΛ X hX)).2.1
        · simpa using hJ
      have hcard : ((fibre h X').card : ℝ) ≤ 2 ^ ((2 * R + 1) ^ 2 * h) := by
        exact_mod_cast (card_fibre_le h X').trans
          (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right h (card_le_of_mem_supports hs)))
      calc ‖∑ X ∈ fibre h X', colTerm h Φ X' X‖
          ≤ ∑ X ∈ fibre h X', ‖colTerm h Φ X' X‖ := norm_sum_le _ _
        _ ≤ ∑ _X ∈ fibre h X', J := Finset.sum_le_sum hterm
        _ = (fibre h X').card * J := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 ^ ((2 * R + 1) ^ 2 * h) * max J 1 :=
          mul_le_mul hcard (le_max_left _ _) hJ (by positivity)
        _ = max J 1 * 2 ^ ((2 * R + 1) ^ 2 * h) := mul_comm _ _
    · rw [colInteraction_eq_zero hΛ hΦ hX' hs, norm_zero]
      exact hpos.le

/-! ## The ground vector and the gap under relabelling -/

/-- Relabelling preserves the Euclidean normalization. -/
theorem dotProduct_star_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (Ω : ι → 𝕜)
    (e : κ ≃ ι) : star (Ω ∘ e) ⬝ᵥ (Ω ∘ e) = star Ω ⬝ᵥ Ω := by
  simp only [dotProduct, Pi.star_apply, Function.comp_apply]
  exact e.sum_comp fun i => star (Ω i) * Ω i

/-- Relabelling commutes with applying a matrix to a vector. -/
theorem submatrix_mulVec_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι 𝕜)
    (Ω : ι → 𝕜) (e : κ ≃ ι) : M.submatrix e e *ᵥ (Ω ∘ e) = (M *ᵥ Ω) ∘ e := by
  rw [submatrix_mulVec_equiv]
  congr 2
  funext i
  simp

/-- Relabelling preserves the global gap. -/
theorem hasGlobalGap_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {H : Matrix ι ι 𝕜} {Ω : ι → 𝕜} {E₀ Δ : ℝ} (hgap : HasGlobalGap H Ω E₀ Δ)
    (e : κ ≃ ι) : HasGlobalGap (H.submatrix e e) (Ω ∘ e) E₀ Δ := by
  rw [HasGlobalGap, Matrix.le_iff] at hgap ⊢
  have heq : H.submatrix e e - (E₀ : 𝕜) • 1 - (Δ : 𝕜) • (1 - vecMulVec (Ω ∘ e) (star (Ω ∘ e))) =
      (H - (E₀ : 𝕜) • 1 - (Δ : 𝕜) • (1 - vecMulVec Ω (star Ω))).submatrix e e := by
    ext a b
    simp [Matrix.one_apply, vecMulVec_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [heq]
  exact hgap.submatrix e

/-! ## Cuts that split columns -/

/-- A discrete intermediate value step: if `Q` holds at `a` and fails at `a + n`, it holds at
some `z ∈ [a, a + n)` and fails at `z + 1`. -/
theorem exists_step (Q : ℤ → Prop) :
    ∀ (n : ℕ) (a : ℤ), Q a → ¬Q (a + n) → ∃ z, a ≤ z ∧ z < a + n ∧ Q z ∧ ¬Q (z + 1)
  | 0, a, ha, hn => absurd (by simpa using ha) hn
  | n + 1, a, ha, hn => by
    by_cases h1 : Q (a + 1)
    · have hn' : ¬Q (a + 1 + n) := by
        have : a + 1 + (n : ℤ) = a + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rwa [this]
      obtain ⟨z, hz1, hz2, hz, hz'⟩ := exists_step Q n (a + 1) h1 hn'
      exact ⟨z, by omega, by push_cast; omega, hz, hz'⟩
    · exact ⟨a, le_rfl, by push_cast; omega, ha, h1⟩

/-- A column of a cylinder that meets both `A` and its complement carries a vertical crossing
edge of `A`. -/
theorem exists_vertical_edge {Λ' : Finset (ℤ × ℤ)} {Λ A : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ) {p : ℤ × ℤ} (hp : p ∈ Λ') {a c : ℤ} (ha0 : 0 ≤ a) (hah : a < h)
    (hc0 : 0 ≤ c) (hch : c < h) (ha : (p.1, p.2, a) ∈ A) (hc : (p.1, p.2, c) ∉ A) :
    ∃ e ∈ edgeBoundary3D Λ A, column e.1 = p := by
  rcases le_or_gt a c with hac | hca
  · obtain ⟨z, hz1, hz2, hz, hz'⟩ := exists_step (fun z => (p.1, p.2, z) ∈ A) (c - a).toNat a ha
      (by rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel])
    refine ⟨((p.1, p.2, z), (p.1, p.2, z + 1)), ?_, rfl⟩
    rw [edgeBoundary3D, mem_interedges_iff, cubicLattice3D_adj_iff]
    rw [Int.toNat_of_nonneg (by omega)] at hz2
    exact ⟨hz, Finset.mem_sdiff.2 ⟨(hΛ _).2 ⟨hp, by dsimp only; omega, by dsimp only; omega⟩, hz'⟩,
      Or.inr ⟨rfl, Or.inl rfl⟩⟩
  · obtain ⟨z, hz1, hz2, hz, hz'⟩ := exists_step (fun z => (p.1, p.2, -z) ∈ A) (a - c).toNat (-a)
      (by simpa using ha)
      (by rwa [Int.toNat_of_nonneg (by omega), show -a + (a - c) = -c by ring, neg_neg])
    refine ⟨((p.1, p.2, -z), (p.1, p.2, -(z + 1))), ?_, rfl⟩
    rw [edgeBoundary3D, mem_interedges_iff, cubicLattice3D_adj_iff]
    rw [Int.toNat_of_nonneg (by omega)] at hz2
    exact ⟨hz, Finset.mem_sdiff.2 ⟨(hΛ _).2 ⟨hp, by dsimp only; omega, by dsimp only; omega⟩, hz'⟩,
      Or.inr ⟨rfl, Or.inr (by dsimp only; ring)⟩⟩

/-- The columns of `Λ'` contained in `A`. -/
noncomputable def fullColumns (h : ℕ) (Λ' : Finset (ℤ × ℤ)) (A : Finset (ℤ × ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  Λ'.filter fun p => ∀ z : ℤ, 0 ≤ z → z < h → (p.1, p.2, z) ∈ A

/-- The full columns of `A` lie in `A`. -/
theorem cyl_fullColumns_subset (Λ' : Finset (ℤ × ℤ)) (A : Finset (ℤ × ℤ × ℤ)) :
    cyl h (fullColumns h Λ' A) ⊆ A := fun x hx => by
  obtain ⟨hx, h0, hh⟩ := (isCyl_cyl h _ x).1 hx
  exact (Finset.mem_filter.1 hx).2 _ h0 hh

/-- The sites of `A` outside its full columns number at most `h |∂_Λ A|`: each of their columns
carries a vertical crossing edge, and a column has `h` sites. -/
theorem card_sdiff_cyl_fullColumns_le {Λ' : Finset (ℤ × ℤ)} {Λ A : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ) (hA : A ⊆ Λ) :
    (A \ cyl h (fullColumns h Λ' A)).card ≤ h * (edgeBoundary3D Λ A).card := by
  set B := A \ cyl h (fullColumns h Λ' A)
  refine (Finset.card_le_mul_card_image (f := column) B h fun p _ => ?_).trans
    (Nat.mul_le_mul_left h ((Finset.card_le_card ?_).trans
      (Finset.card_image_le (f := fun e : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) => column e.1))))
  · calc (B.filter fun x => column x = p).card ≤ (Finset.Ico (0 : ℤ) h).card := by
          refine Finset.card_le_card_of_injOn (fun x => x.2.2) (fun x hx => ?_) ?_
          · obtain ⟨hxB, -⟩ := Finset.mem_filter.1 hx
            have := ((hΛ x).1 (hA (Finset.mem_sdiff.1 hxB).1)).2
            exact Finset.mem_Ico.2 this
          · intro x hx y hy hxy
            have hc : column x = column y :=
              (Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hy).2.symm
            simp only [column, Prod.mk.injEq] at hc
            exact Prod.ext hc.1 (Prod.ext hc.2 hxy)
      _ = h := by rw [Int.card_Ico, sub_zero, Int.toNat_natCast]
  · intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hbA, hbP⟩ := Finset.mem_sdiff.1 hb
    obtain ⟨hbΛ', hb0, hbh⟩ := (hΛ b).1 (hA hbA)
    have hnot : column b ∉ fullColumns h Λ' A := fun hP =>
      hbP ((isCyl_cyl h _ b).2 ⟨hP, hb0, hbh⟩)
    simp only [fullColumns, Finset.mem_filter, not_and, not_forall] at hnot
    obtain ⟨z, hz0, hzh, hz⟩ := hnot hbΛ'
    obtain ⟨e, he, hec⟩ := exists_vertical_edge hΛ hbΛ' hb0 hbh hz0 hzh hbA hz
    exact Finset.mem_image.2 ⟨e, he, hec⟩

/-- The planar edge boundary of the full columns of `A` is at most the edge boundary of `A`:
a planar crossing edge lifts to a horizontal crossing edge at a height where the outer column
leaves `A`. -/
theorem card_edgeBoundary_fullColumns_le {Λ' : Finset (ℤ × ℤ)} {Λ A : Finset (ℤ × ℤ × ℤ)}
    (hΛ : IsCyl h Λ' Λ) :
    (edgeBoundary Λ' (fullColumns h Λ' A)).card ≤ (edgeBoundary3D Λ A).card := by
  refine (Finset.card_le_card fun e he => ?_).trans
    (Finset.card_image_le (f := fun e : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) => (column e.1, column e.2)))
  obtain ⟨hp, hp', hadj⟩ := mem_edgeBoundary.1 he
  obtain ⟨hp'Λ, hp'P⟩ := Finset.mem_sdiff.1 hp'
  simp only [fullColumns, Finset.mem_filter, not_and, not_forall] at hp'P
  obtain ⟨z, hz0, hzh, hz⟩ := hp'P hp'Λ
  refine Finset.mem_image.2 ⟨((e.1.1, e.1.2, z), (e.2.1, e.2.2, z)), ?_, rfl⟩
  rw [edgeBoundary3D, mem_interedges_iff, cubicLattice3D_adj_iff]
  exact ⟨(Finset.mem_filter.1 hp).2 z hz0 hzh,
    Finset.mem_sdiff.2 ⟨(hΛ _).2 ⟨hp'Λ, hz0, hzh⟩, hz⟩, Or.inl ⟨rfl, hadj⟩⟩

end Cylinder

open Cylinder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The planar area law holds trivially at local dimension `0`, with constant `0`: every
region entropy is at most `|A| log 0 = 0`. -/
theorem areaLaw_zero (R : ℕ) (J Δ : ℝ) : AreaLaw 𝕜 0 R J Δ :=
  ⟨0, fun _ _ _ Ω hΩ _ _ _ _ hA => by
    simpa using (pureState Ω hΩ).regionEntropy_le_card_mul_log hA (d := 0)
      fun _ => Fintype.card_fin 0⟩

/-- **Target 1 as a corollary** (`docs/3D/Targets.md`, B.1): the planar area law with local
dimension `q ^ h` at every strength gives the area law on cylinders `Λ' × [0, h)`, for every
parameter set.  The constant is `max C 0 + h log q`, where `C` is the planar constant at
strength `max J 1 · 2 ^ ((2R + 1)² h)`. -/
theorem cylinderAreaLawOfPlanar3D (q R : ℕ) (J Δ : ℝ) (h : ℕ) :
    CylinderAreaLawOfPlanar3D 𝕜 q R J Δ h := by
  intro hplanar
  obtain ⟨C, hC⟩ := hplanar _ (by positivity : (0 : ℝ) < max J 1 * 2 ^ ((2 * R + 1) ^ 2 * h))
  refine ⟨max C 0 + h * Real.log q, fun Λ hΛ Φ hΦ Ω hΩ E₀ hE hgap A hA => ?_⟩
  obtain ⟨Λ', hcyl⟩ := hΛ
  change IsCyl h Λ' Λ at hcyl
  set e := colEquiv (q := q) hcyl
  have hΩ' : star (Ω ∘ e) ⬝ᵥ (Ω ∘ e) = 1 := by rw [dotProduct_star_comp_equiv, hΩ]
  have hH := hamiltonian_colInteraction hcyl Φ
  have hE' : hamiltonian Λ' (colInteraction h Φ) *ᵥ (Ω ∘ e) = (E₀ : 𝕜) • (Ω ∘ e) := by
    rw [hH, submatrix_mulVec_comp_equiv, hE]
    rfl
  have hgap' : HasGlobalGap (hamiltonian Λ' (colInteraction h Φ)) (Ω ∘ e) E₀ Δ := by
    rw [hH]
    exact hasGlobalGap_submatrix hgap e
  set P := fullColumns h Λ' A
  have hPΛ' : P ⊆ Λ' := Finset.filter_subset _ _
  have hPA : cyl h P ⊆ A := cyl_fullColumns_subset Λ' A
  have hPΛ : cyl h P ⊆ Λ := hPA.trans hA
  have hBΛ : A \ cyl h P ⊆ Λ := Finset.sdiff_subset.trans hA
  -- The full columns: the planar area law.
  have hP := hC Λ' (colInteraction h Φ) (isAdmissible_colInteraction hcyl hΦ) (Ω ∘ e) hΩ' E₀
    hE' hgap' P hPΛ'
  rw [regionEntropy_pureState_colEquiv (isCyl_cyl h P) hcyl hPΛ' hPΛ Ω hΩ hΩ'] at hP
  -- The rest of `A`: subadditivity and the dimension bound.
  have hsub := (pureState Ω hΩ).regionEntropy_union_le Finset.disjoint_sdiff hPΛ hBΛ
  rw [SubState.regionEntropy_congr _ (Finset.union_sdiff_of_subset hPA) _ hA] at hsub
  have hB := (pureState Ω hΩ).regionEntropy_le_card_mul_log hBΛ (d := q)
    fun _ => Fintype.card_fin q
  have hcardB : ((A \ cyl h P).card : ℝ) ≤ h * (edgeBoundary3D Λ A).card := by
    exact_mod_cast card_sdiff_cyl_fullColumns_le hcyl hA
  have hcardP : ((edgeBoundary Λ' P).card : ℝ) ≤ (edgeBoundary3D Λ A).card := by
    exact_mod_cast card_edgeBoundary_fullColumns_le hcyl
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have h1 : C * (edgeBoundary Λ' P).card ≤ max C 0 * (edgeBoundary3D Λ A).card :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hcardP (le_max_right _ _))
  have h2 : ((A \ cyl h P).card : ℝ) * Real.log q ≤ h * (edgeBoundary3D Λ A).card * Real.log q :=
    mul_le_mul_of_nonneg_right hcardB hlog
  have h3 : (max C 0 + h * Real.log q) * (edgeBoundary3D Λ A).card =
      max C 0 * (edgeBoundary3D Λ A).card + h * (edgeBoundary3D Λ A).card * Real.log q := by
    ring
  linarith

/-- **Target 1** (`docs/3D/Targets.md`, B.1): the area law on cylinders `Λ' × [0, h)`, for
every `q`, `R`, `J`, `h` and every `Δ > 0`, from `cylinderAreaLawOfPlanar3D` and `area_law`
at local dimension `q ^ h` (and `areaLaw_zero` when `q ^ h = 0`). -/
theorem cylinderAreaLaw3D (q R : ℕ) (J Δ : ℝ) (h : ℕ) (hΔ : 0 < Δ) :
    CylinderAreaLaw3D 𝕜 q R J Δ h :=
  cylinderAreaLawOfPlanar3D q R J Δ h fun J' hJ' => by
    rcases Nat.eq_zero_or_pos (q ^ h) with h0 | h0
    · rw [h0]
      exact areaLaw_zero R J' Δ
    · exact area_law (q ^ h) R J' Δ h0 hJ' hΔ

end OpenAI
