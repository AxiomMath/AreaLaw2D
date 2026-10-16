import OpenAI.Statements
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bridges to the TNLean encoding

Lemmas identifying the objects of `OpenAI.Statements` with the defining formulas of the
corresponding declarations of TNLean (commit `f4c2d204`) and QICLean (commit `32a5a1a8`), each
written with Mathlib and Physlib primitives.  Our object is on the left, the TNLean formula on
the right, so that a proof written against TNLean's characterization applies to ours.

## Main definitions

* `regEquivPiSubtype`, `regSdiffEquivPiSubtype`: configurations on `S ⊆ T` and on `T \ S` as
  configurations on the sites of `T` satisfying, or failing, a predicate that cuts out `S`.

## Main statements

* `ptrace_eq_traceRight_piEquivPiSubtypeProd`: the region partial trace is the binary right
  partial trace after splitting the configuration by `Equiv.piEquivPiSubtypeProd`.
* `regionEntropy_pureState_eq_sum_negMulLog`: region entropies of a pure state are the
  `negMulLog`-sums of the eigenvalues of the reduced matrix in that split form.
* `normalized_eigen_hasGlobalGap_iff_euclidean`: the ground-state hypotheses of the statements
  are the three conditions of a gapped ground state on `EuclideanSpace`.
* `mem_supports_iff_walk`, `mem_graphNbhd_iff_walk`: admissible supports and graph
  neighbourhoods through walks in the induced graph.
* `isSupportedOn_iff_mem_span`: supported operators are the span of product operators
  `Matrix.piProd m` with `m i = 1` off the support.

## Implementation notes

The predicate `p` cutting out `S` is a parameter of the reindexing equivalences, with
`∀ x, p x ↔ x.1 ∈ S` as hypothesis, so that one lemma covers both cut encodings: our
`A ⊆ T`, read as `fun x : T => x.1 ∈ A`, and a cut `A' : Finset T` of the subtype, read as
`(· ∈ A')` with `A = A'.map (Function.Embedding.subtype _)`.

The gap bridge is stated over `RCLike 𝕜`; at `𝕜 = ℂ` its right-hand side is the formula of
the `ℂ`-only TNLean predicate.  The product operators are Physlib's `Matrix.piProd`, whose
formula `fun x y => ∏ i, m i (x i) (y i)` is that of TNLean's `rectKronecker` on square
factors.
-/

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder
open Matrix SimpleGraph

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Reduced states -/

section ReducedState

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} {S T : Finset σ} {p : T → Prop}

/-- A configuration on `S ⊆ T` is a configuration on the sites of `T` satisfying `p`, for any
predicate `p` cutting `S` out of `T`.  With `regSdiffEquivPiSubtype` it is the region form of
the two factors of TNLean `configurationSplit` (`TNLean/PEPS/AreaLaw/FiniteDomain.lean:97`,
commit `f4c2d204`), `Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ ↦ Fin q)`. -/
def regEquivPiSubtype (h : S ⊆ T) (hp : ∀ x, p x ↔ x.1 ∈ S) :
    Reg loc S ≃ (∀ x : {x : T // p x}, loc x.1.1) where
  toFun z x := z ⟨x.1.1, (hp x.1).1 x.2⟩
  invFun w i := w ⟨⟨i.1, h i.2⟩, (hp _).2 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq σ] in
@[simp] theorem regEquivPiSubtype_apply (h : S ⊆ T) (hp : ∀ x, p x ↔ x.1 ∈ S) (z : Reg loc S)
    (x : {x : T // p x}) : regEquivPiSubtype h hp z x = z ⟨x.1.1, (hp x.1).1 x.2⟩ := rfl

omit [DecidableEq σ] in
@[simp] theorem regEquivPiSubtype_symm_apply (h : S ⊆ T) (hp : ∀ x, p x ↔ x.1 ∈ S)
    (w : ∀ x : {x : T // p x}, loc x.1.1) (i : S) :
    (regEquivPiSubtype h hp).symm w i = w ⟨⟨i.1, h i.2⟩, (hp _).2 i.2⟩ := rfl

/-- A configuration on `T \ S` is a configuration on the sites of `T` failing `p`, for any
predicate `p` cutting `S` out of `T`. -/
def regSdiffEquivPiSubtype (hp : ∀ x, p x ↔ x.1 ∈ S) :
    Reg loc (T \ S) ≃ (∀ x : {x : T // ¬p x}, loc x.1.1) where
  toFun z x := z ⟨x.1.1, Finset.mem_sdiff.2 ⟨x.1.2, fun hx => x.2 ((hp x.1).2 hx)⟩⟩
  invFun w i := w ⟨⟨i.1, (Finset.mem_sdiff.1 i.2).1⟩,
    fun hx => (Finset.mem_sdiff.1 i.2).2 ((hp _).1 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem regSdiffEquivPiSubtype_apply (hp : ∀ x, p x ↔ x.1 ∈ S) (z : Reg loc (T \ S))
    (x : {x : T // ¬p x}) :
    regSdiffEquivPiSubtype hp z x =
      z ⟨x.1.1, Finset.mem_sdiff.2 ⟨x.1.2, fun hx => x.2 ((hp x.1).2 hx)⟩⟩ := rfl

@[simp] theorem regSdiffEquivPiSubtype_symm_apply (hp : ∀ x, p x ↔ x.1 ∈ S)
    (w : ∀ x : {x : T // ¬p x}, loc x.1.1) (i : ↥(T \ S)) :
    (regSdiffEquivPiSubtype hp).symm w i =
      w ⟨⟨i.1, (Finset.mem_sdiff.1 i.2).1⟩, fun hx => (Finset.mem_sdiff.1 i.2).2 ((hp _).1 hx)⟩ :=
  rfl

/-- Splitting a glued configuration by `Equiv.piEquivPiSubtypeProd` recovers its two parts. -/
theorem piEquivPiSubtypeProd_symm_regEquivPiSubtype [DecidablePred p] (h : S ⊆ T)
    (hp : ∀ x, p x ↔ x.1 ∈ S) (x : Reg loc S) (z : Reg loc (T \ S)) :
    (Equiv.piEquivPiSubtypeProd p fun j : T => loc j).symm
      (regEquivPiSubtype h hp x, regSdiffEquivPiSubtype hp z) = glue x z := by
  funext j
  by_cases hj : j.1 ∈ S
  · simp [glue, hj, (hp j).2 hj, regEquivPiSubtype_apply]
  · simp [glue, hj, mt (hp j).1 hj, regSdiffEquivPiSubtype_apply]

variable [∀ i, Fintype (loc i)] [DecidablePred p]

section Fintype

-- The subtype instances are arguments, not derived from `DecidablePred p`, so that callers
-- whose subtype carries another instance (`↥A'` for a `Finset`) apply these lemmas directly.
variable [Fintype {x : T // p x}] [Fintype {x : T // ¬p x}]

omit [Fintype {x : T // p x}] in
/-- **The partial trace in split form**: `ptrace h M` is `Matrix.traceRight` of `M` after
splitting configurations of `T` into the sites satisfying and failing `p`.  The right-hand side
is QICLean `Matrix.partialTraceRight` (`QICLean/Channel/PartialTrace.lean:98`, commit
`32a5a1a8`, `fun i j => ∑ k, X (i, k) (j, k)`) as used in TNLean `reducedState`
(`TNLean/PEPS/AreaLaw/TheoremStatements.lean:38`, commit `f4c2d204`). -/
theorem ptrace_eq_traceRight_piEquivPiSubtypeProd (h : S ⊆ T) (hp : ∀ x, p x ↔ x.1 ∈ S)
    (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h M = (traceRight (M.submatrix (Equiv.piEquivPiSubtypeProd p fun j : T => loc j).symm
      (Equiv.piEquivPiSubtypeProd p fun j : T => loc j).symm)).submatrix
        (regEquivPiSubtype h hp) (regEquivPiSubtype h hp) := by
  ext x y
  simp only [ptrace, traceRight, of_apply, submatrix_apply]
  exact Fintype.sum_equiv (regSdiffEquivPiSubtype hp) _ _ fun z => by
    rw [piEquivPiSubtypeProd_symm_regEquivPiSubtype, piEquivPiSubtypeProd_symm_regEquivPiSubtype]

variable [∀ i, DecidableEq (loc i)]

/-- **Region entropies of a pure state in split form**: the entropy of the region `S ⊆ T` of
`|Ω⟩⟨Ω|` is `∑ negMulLog` of the eigenvalues of the right partial trace of `|Ω⟩⟨Ω|`, split
along `p`.  The right-hand side is TNLean `regionalEntropy`
(`TNLean/PEPS/AreaLaw/TheoremStatements.lean:63`, commit `f4c2d204`), QICLean
`vonNeumannEntropy` (`QICLean/Analysis/Entropy.lean:96`, commit `32a5a1a8`) of
`reducedState` (`TheoremStatements.lean:38`). -/
theorem regionEntropy_pureState_eq_sum_negMulLog (Ω : Reg loc T → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (h : S ⊆ T) (hp : ∀ x, p x ↔ x.1 ∈ S)
    (hρ : (traceRight ((vecMulVec Ω (star Ω)).submatrix
      (Equiv.piEquivPiSubtypeProd p fun j : T => loc j).symm
      (Equiv.piEquivPiSubtypeProd p fun j : T => loc j).symm)).IsHermitian) :
    (pureState Ω hΩ).regionEntropy h = ∑ i, Real.negMulLog (hρ.eigenvalues i) := by
  rw [← H, ← vonNeumann_eq_H, ← vonNeumann_submatrix_equiv hρ (regEquivPiSubtype h hp)]
  simp only [SubState.regionEntropy, SubState.entropy]
  congr 1
  exact ptrace_eq_traceRight_piEquivPiSubtypeProd h hp _

end Fintype

omit [DecidableEq σ] in
/-- A cut `A' : Finset T` of the sites of `T`, read as a region of the ambient sites, lies
in `T`. -/
theorem map_embeddingSubtype_subset (A' : Finset T) :
    A'.map (Function.Embedding.subtype _) ⊆ T := fun _ hx => by
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  exact y.2

omit [DecidableEq σ] in
/-- Membership in a cut of the subtype of sites is membership of the underlying site in its
image region. -/
theorem mem_map_embeddingSubtype_iff (A' : Finset T) (x : T) :
    x ∈ A' ↔ x.1 ∈ A'.map (Function.Embedding.subtype _) := by
  simp

variable [∀ i, DecidableEq (loc i)]

/-- `regionEntropy_pureState_eq_sum_negMulLog` for a cut `A' : Finset T` of the subtype of
sites, transported to the region `A'.map (Function.Embedding.subtype _)`: the entropy of our
region is TNLean `regionalEntropy Λ q Ω A'` (`TNLean/PEPS/AreaLaw/TheoremStatements.lean:63`,
commit `f4c2d204`) at `T = Λ`, `loc = Qudits q`. -/
theorem regionEntropy_pureState_map_embeddingSubtype (Ω : Reg loc T → 𝕜)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (A' : Finset T)
    (hρ : (traceRight ((vecMulVec Ω (star Ω)).submatrix
      (Equiv.piEquivPiSubtypeProd (· ∈ A') fun j : T => loc j).symm
      (Equiv.piEquivPiSubtypeProd (· ∈ A') fun j : T => loc j).symm)).IsHermitian) :
    (pureState Ω hΩ).regionEntropy (map_embeddingSubtype_subset A') =
      ∑ i, Real.negMulLog (hρ.eigenvalues i) :=
  regionEntropy_pureState_eq_sum_negMulLog (p := (· ∈ A')) Ω hΩ _
    (mem_map_embeddingSubtype_iff A') hρ

/-- `regionEntropy_pureState_eq_sum_negMulLog` for a region `A ⊆ T`, with the cut written on
the subtype of sites as `A.subtype (· ∈ T)`: the entropy of `A` is TNLean
`regionalEntropy Λ q Ω (A.subtype (· ∈ Λ))` (`TNLean/PEPS/AreaLaw/TheoremStatements.lean:63`,
commit `f4c2d204`) at `T = Λ`, `loc = Qudits q`. -/
theorem regionEntropy_pureState_eq_sum_negMulLog_subtype (Ω : Reg loc T → 𝕜)
    (hΩ : star Ω ⬝ᵥ Ω = 1) {A : Finset σ} (hA : A ⊆ T)
    (hρ : (traceRight ((vecMulVec Ω (star Ω)).submatrix
      (Equiv.piEquivPiSubtypeProd (· ∈ A.subtype (· ∈ T)) fun j : T => loc j).symm
      (Equiv.piEquivPiSubtypeProd (· ∈ A.subtype (· ∈ T)) fun j : T => loc j).symm)).IsHermitian) :
    (pureState Ω hΩ).regionEntropy hA = ∑ i, Real.negMulLog (hρ.eigenvalues i) :=
  regionEntropy_pureState_eq_sum_negMulLog (p := (· ∈ A.subtype (· ∈ T))) Ω hΩ hA
    (fun _ => Finset.mem_subtype) hρ

end ReducedState

/-! ## Gapped ground states -/

section Gap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The Euclidean normalization `star Ω ⬝ᵥ Ω = 1` is the unit norm of `Ω` in
`EuclideanSpace`. -/
theorem norm_toLp_eq_one_iff (Ω : ι → 𝕜) : ‖WithLp.toLp 2 Ω‖ = 1 ↔ star Ω ⬝ᵥ Ω = 1 := by
  have h : star Ω ⬝ᵥ Ω = ((‖WithLp.toLp 2 Ω‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  rw [h, ← RCLike.ofReal_one (K := 𝕜), RCLike.ofReal_inj,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- **Gapped ground states in Euclidean form**: a normalized eigenvector with the global gap
is a unit vector of `EuclideanSpace` on which `toEuclideanCLM H` acts as `E₀`, with
`H - E₀ - Δ (1 - |Ω⟩⟨Ω|)` positive semidefinite.  At `𝕜 = ℂ` the right-hand side is TNLean
`Matrix.IsGappedGroundState H E₀ (WithLp.toLp 2 Ω) Δ`
(`TNLean/Algebra/GappedGroundState.lean:45`, commit `f4c2d204`). -/
theorem normalized_eigen_hasGlobalGap_iff_euclidean (H : Matrix ι ι 𝕜) (Ω : ι → 𝕜)
    (E₀ Δ : ℝ) :
    (star Ω ⬝ᵥ Ω = 1 ∧ H *ᵥ Ω = (E₀ : 𝕜) • Ω ∧ HasGlobalGap H Ω E₀ Δ) ↔
      (‖WithLp.toLp 2 Ω‖ = 1 ∧
        toEuclideanCLM (n := ι) (𝕜 := 𝕜) H (WithLp.toLp 2 Ω) = (E₀ : 𝕜) • WithLp.toLp 2 Ω ∧
        (H - (E₀ : 𝕜) • (1 : Matrix ι ι 𝕜) - (Δ : 𝕜) •
          (1 - vecMulVec Ω (star Ω))).PosSemidef) := by
  rw [norm_toLp_eq_one_iff, toEuclideanCLM_toLp, ← WithLp.toLp_smul,
    (WithLp.toLp_injective 2).eq_iff, HasGlobalGap, Matrix.le_iff]

end Gap

/-! ## Admissible supports and graph neighbourhoods -/

section Walks

/-- A walk of length at most `n` from `u` to `v` exists iff the extended graph distance from
`u` to `v` is at most `n`; between components both sides fail.  TNLean
`exists_walk_length_le_iff_edist_le` (`TNLean/PEPS/AreaLaw/FiniteDomain.lean:131`, commit
`f4c2d204`) for an arbitrary graph. -/
theorem exists_walk_length_le_iff_edist_le {V : Type*} (G : SimpleGraph V) {u v : V} {n : ℕ} :
    (∃ p : G.Walk u v, p.length ≤ n) ↔ G.edist u v ≤ n := by
  constructor
  · rintro ⟨p, hp⟩
    exact p.edist_le.trans (by exact_mod_cast hp)
  · intro h
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) h)
    exact ⟨p, by exact_mod_cast hp ▸ h⟩

/-- **Admissible supports through walks**: `X` is an admissible support of range `R` iff it
is a nonempty subset of `Λ` any two of whose sites are joined by a walk of length at most `R`
inside `Λ`.  The right-hand side is TNLean `IsAdmissibleSupport`
(`TNLean/PEPS/AreaLaw/FiniteDomain.lean:61`, commit `f4c2d204`) on the induced graph. -/
theorem mem_supports_iff_walk {Λ X : Finset (ℤ × ℤ)} {R : ℕ} :
    X ∈ supports Λ R ↔ ∃ hX : X ⊆ Λ, X.Nonempty ∧ ∀ x (hx : x ∈ X) y (hy : y ∈ X),
      ∃ p : ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).Walk ⟨x, hX hx⟩ ⟨y, hX hy⟩,
        p.length ≤ R := by
  simp only [supports, Finset.mem_filter, Finset.mem_powerset, domainEDiam, iSup₂_le_iff]
  constructor
  · rintro ⟨hX, hne, hd⟩
    refine ⟨hX, hne, fun x hx y hy => ?_⟩
    have hxy := hd x hx y hy
    rw [domainEDist, dif_pos ⟨hX hx, hX hy⟩] at hxy
    exact (exists_walk_length_le_iff_edist_le _).2 hxy
  · rintro ⟨hX, hne, hw⟩
    refine ⟨hX, hne, fun x hx y hy => ?_⟩
    rw [domainEDist, dif_pos ⟨hX hx, hX hy⟩]
    exact (exists_walk_length_le_iff_edist_le _).1 (hw x hx y hy)

/-- **Graph neighbourhoods through walks**: `x ∈ N_r(S)` iff `x ∈ Λ` and some site of `S ∩ Λ`
is joined to `x` by a walk of length at most `r` inside `Λ`.  The right-hand side is
membership in TNLean `graphNeighborhood` (`TNLean/PEPS/AreaLaw/FiniteDomain.lean:74`, commit
`f4c2d204`) on the induced graph. -/
theorem mem_graphNbhd_iff_walk {Λ S : Finset (ℤ × ℤ)} {r : ℕ} {x : ℤ × ℤ} :
    x ∈ graphNbhd Λ S r ↔ ∃ hx : x ∈ Λ, ∃ y ∈ S, ∃ hy : y ∈ Λ,
      ∃ p : ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).Walk ⟨y, hy⟩ ⟨x, hx⟩,
        p.length ≤ r := by
  rw [graphNbhd, Finset.mem_filter, ← Finset.inf_eq_iInf, Finset.inf_le_iff (ENat.natCast_lt_top r)]
  constructor
  · rintro ⟨hx, y, hy, hd⟩
    by_cases hyΛ : y ∈ Λ
    · rw [domainEDist, dif_pos ⟨hx, hyΛ⟩, edist_comm] at hd
      exact ⟨hx, y, hy, hyΛ, (exists_walk_length_le_iff_edist_le _).2 hd⟩
    · rw [domainEDist, dif_neg fun h => hyΛ h.2] at hd
      exact absurd hd (by simp)
  · rintro ⟨hx, y, hy, hyΛ, hw⟩
    refine ⟨hx, y, hy, ?_⟩
    rw [domainEDist, dif_pos ⟨hx, hyΛ⟩, edist_comm]
    exact (exists_walk_length_le_iff_edist_le _).1 hw

end Walks

/-! ## Supported operators -/

section PiProd

variable {ι : Type*} [Fintype ι] {d : ι → Type*} [∀ i, DecidableEq (d i)] {R : Type*}

/-- The product of identities is the identity. -/
@[simp] theorem piProd_one [CommSemiring R] :
    piProd (fun i => (1 : Matrix (d i) (d i) R)) = 1 := by
  ext x y
  simp only [piProd, of_apply, one_apply, Fintype.prod_boole, funext_iff]

/-- A matrix unit of `∀ i, d i` is the product of the matrix units of its sites. -/
theorem single_eq_piProd [CommSemiring R] (x y : ∀ i, d i) :
    single x y (1 : R) = piProd fun i => single (x i) (y i) 1 := by
  ext a b
  simp only [piProd, of_apply, single_apply, Fintype.prod_boole, funext_iff, forall_and]

end PiProd

section Supported

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, DecidableEq (loc i)]
  {S T : Finset σ}

/-- **Extension of a product operator**: extending `⊗_{i ∈ S} mᵢ` by the identity is the product
operator on `T` that is `mᵢ` on `S` and `1` off `S`. -/
theorem extendId_piProd (h : S ⊆ T) (m : ∀ i : S, Matrix (loc i) (loc i) 𝕜) :
    extendId h (piProd m) = piProd fun i : T => if hi : i.1 ∈ S then m ⟨i, hi⟩ else 1 := by
  ext w w'
  obtain ⟨⟨x, z⟩, rfl⟩ := (glueEquiv h).surjective w
  obtain ⟨⟨x', z'⟩, rfl⟩ := (glueEquiv h).surjective w'
  rw [glueEquiv_apply, glueEquiv_apply, extendId_apply_glue]
  have hsplit : ∀ i : T,
      (if hi : i.1 ∈ S then m ⟨i, hi⟩ else 1 : Matrix (loc i) (loc i) 𝕜) (glue x z i)
        (glue x' z' i) =
      if hi : i.1 ∈ S then m ⟨i, hi⟩ (x ⟨i, hi⟩) (x' ⟨i, hi⟩) else
        (1 : Matrix (loc i) (loc i) 𝕜) (z ⟨i, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩)
          (z' ⟨i, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩) := fun i => by
    by_cases hi : i.1 ∈ S
    · simp only [dif_pos hi, glue]
    · simp only [dif_neg hi, glue]
  simp only [piProd, of_apply]
  rw [Fintype.prod_congr _ _ hsplit, Fintype.prod_dite,
    Fintype.prod_equiv (Equiv.subtypeSubtypeEquivSubtype fun hx => h hx)
      (fun a : {a : T // a.1 ∈ S} => m ⟨a.1.1, a.2⟩ (x ⟨a.1.1, a.2⟩) (x' ⟨a.1.1, a.2⟩))
      (fun i : S => m i (x i) (x' i)) fun _ => rfl]
  simp only [one_apply, Fintype.prod_boole]
  have hz : (∀ a : {a : T // a.1 ∉ S}, z ⟨a, Finset.mem_sdiff.2 ⟨a.1.2, a.2⟩⟩ =
      z' ⟨a, Finset.mem_sdiff.2 ⟨a.1.2, a.2⟩⟩) ↔ z = z' :=
    ⟨fun H => funext fun j => H ⟨⟨j.1, (Finset.mem_sdiff.1 j.2).1⟩, (Finset.mem_sdiff.1 j.2).2⟩,
      fun H _ => H ▸ rfl⟩
  simp only [hz, mul_ite, mul_one, mul_zero]

/-- An extended operator is supported on its original region. -/
theorem isSupportedOn_extendId (h : S ⊆ T) (B : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    IsSupportedOn h (extendId h B) :=
  ⟨B, rfl⟩

theorem isSupportedOn_zero (h : S ⊆ T) : IsSupportedOn h (0 : Matrix (Reg loc T) (Reg loc T) 𝕜) :=
  ⟨0, (extendId_zero h).symm⟩

theorem isSupportedOn_one (h : S ⊆ T) : IsSupportedOn h (1 : Matrix (Reg loc T) (Reg loc T) 𝕜) :=
  ⟨1, (extendId_one h).symm⟩

theorem IsSupportedOn.add {h : S ⊆ T} {B C : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hB : IsSupportedOn h B) (hC : IsSupportedOn h C) : IsSupportedOn h (B + C) := by
  obtain ⟨B, rfl⟩ := hB
  obtain ⟨C, rfl⟩ := hC
  exact ⟨B + C, (extendId_add h B C).symm⟩

theorem IsSupportedOn.smul {h : S ⊆ T} {B : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hB : IsSupportedOn h B) (c : 𝕜) : IsSupportedOn h (c • B) := by
  obtain ⟨B, rfl⟩ := hB
  exact ⟨c • B, (extendId_smul h c B).symm⟩

/-- **Supported operators are spans of product operators**: an operator on `T` is supported in
`S` iff it lies in the span of the product operators `⊗ᵢ mᵢ` with `mᵢ = 1` off `S`.  The
right-hand side is TNLean `QuantumCircuit.supportedOperators`
(`TNLean/Circuit/LocalCircuit.lean:90`, commit `f4c2d204`), with `rectKronecker`
(`TNLean/Algebra/FinKronecker.lean:95`) on square factors as `Matrix.piProd`. -/
theorem isSupportedOn_iff_mem_span [∀ i, Finite (loc i)] (h : S ⊆ T)
    (B : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    IsSupportedOn h B ↔ B ∈ Submodule.span 𝕜
      {M | ∃ m : ∀ i : T, Matrix (loc i) (loc i) 𝕜, (∀ i : T, i.1 ∉ S → m i = 1) ∧
        M = piProd m} := by
  constructor
  · rintro ⟨B, rfl⟩
    induction B using Matrix.induction_on' with
    | h_zero => rw [extendId_zero]; exact zero_mem _
    | h_add B C hB hC => rw [extendId_add]; exact add_mem hB hC
    | h_std_basis x y c =>
      rw [← mul_one c, ← smul_eq_mul, ← smul_single, extendId_smul]
      refine Submodule.smul_mem _ c (Submodule.subset_span ⟨fun i : T =>
        if hi : i.1 ∈ S then single (x ⟨i, hi⟩) (y ⟨i, hi⟩) 1 else 1, fun i hi => dif_neg hi, ?_⟩)
      rw [single_eq_piProd, extendId_piProd]
  · intro hB
    induction hB using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨m, hm, rfl⟩ := hM
      refine ⟨piProd fun i : S => m ⟨i, h i.2⟩, ?_⟩
      rw [extendId_piProd]
      congr 1
      funext i
      by_cases hi : i.1 ∈ S
      · rw [dif_pos hi]
      · rw [dif_neg hi, hm i hi]
    | zero => exact isSupportedOn_zero h
    | add _ _ _ _ hB hC => exact hB.add hC
    | smul c _ _ hB => exact hB.smul c

variable [∀ i, Fintype (loc i)]

/-- Extension by the identity is multiplicative. -/
theorem extendId_mul (h : S ⊆ T) (A B : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (A * B) = extendId h A * extendId h B := by
  rw [extendId_eq_kronecker, extendId_eq_kronecker, extendId_eq_kronecker,
    submatrix_mul_equiv, ← mul_kronecker_mul, one_mul]

theorem IsSupportedOn.mul {h : S ⊆ T} {B C : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hB : IsSupportedOn h B) (hC : IsSupportedOn h C) : IsSupportedOn h (B * C) := by
  obtain ⟨B, rfl⟩ := hB
  obtain ⟨C, rfl⟩ := hC
  exact ⟨B * C, (extendId_mul h B C).symm⟩

end Supported

end OpenAI
