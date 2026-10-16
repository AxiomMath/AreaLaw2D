import OpenAI.ConditionalEntropy
import Arealaw.Mixed

/-!
# Strong subadditivity on regions

For a subnormalized state `ρ` on a region `U` and pairwise disjoint `X Y Z ⊆ U`, strong
subadditivity reads `S(X ∪ Y ∪ Z) + S(Y) ≤ S(X ∪ Y) + S(Y ∪ Z)`, that is, the conditional
mutual information `I(X : Z | Y) = S(X ∪ Y) + S(Y ∪ Z) - S(X ∪ Y ∪ Z) - S(Y)` is nonnegative.
It is the matrix inequality `Arealaw.vonNeumann_strong_subadditivity` for the marginal on
`X ∪ (Y ∪ Z)`, read on `X ⊗ Y ⊗ Z` through `unionEquiv`.  Two consequences follow by
linear arithmetic: conditioning on a larger region lowers the conditional entropy,
`S(X ∪ T') - S(T') ≤ S(X ∪ T) - S(T)` for `T ⊆ T'` disjoint from `X`, and the mutual
information grows with its second region, `I(X : Y) ≤ I(X : Y ∪ Z)`.

The file also proves concavity of the entropy over a finite family, in the unnormalized form
`∑ₖ (S(Aₖ) - η(tr Aₖ)) ≤ S(∑ₖ Aₖ) - η(tr ∑ₖ Aₖ)` with `η(x) = -x log x`, and in the state form
`∑ₖ pₖ S(ρₖ) ≤ S(∑ₖ pₖ ρₖ)`.  The first is `Arealaw.sum_vonNeumann_sub_traceLeft_le` with a
one-dimensional conditioning system; the second is the first applied to `pₖ ρₖ`, by the
scaling law `S(t ρ) = t S(ρ) + η(t)`.

## Main statements

* `Arealaw.SubState.regionEntropy_strong_subadditivity`: strong subadditivity on regions.
* `Arealaw.SubState.regionEntropy_union_sub_le_of_subset`: monotonicity of the conditional
  entropy in the conditioning region.
* `Arealaw.SubState.mutualInfo_le_mutualInfo_union`: monotonicity of the mutual information.
* `Arealaw.sum_vonNeumann_sub_negMulLog_le`, `Arealaw.MState.sum_mul_entropy_le`: concavity
  of the entropy.

## Implementation notes

The region statements are about `SubState`, and apply to a normalized state `ρ` as
`ρ.toSubState.regionEntropy_strong_subadditivity`; no normalization enters, since
`Arealaw.vonNeumann_strong_subadditivity` holds for positive semidefinite matrices of any trace.
The conditional mutual information is not given a definition: strong subadditivity is its
nonnegativity, stated with the four entropies explicit.

The derivation of monotonicity of the conditional entropy from strong subadditivity, applied to
`X`, `T` and `T' \ T`, follows QICLean, `QICLean/Entropy/RegionEntropy.lean`
(`regionEntropy_ssa`, `regionEntropy_cond_anti`) at commit `32a5a1a8` (Apache 2.0).  The changes:
the statements are about `Arealaw.SubState.regionEntropy` of a mixed state over a general
`RCLike` field, where QICLean's are about the region entropies of a pure state over `ℂ`; and the
tripartite reindexing is `unionEquiv` composed with itself, with the one non-definitional
identification isolated in `Arealaw.unionEquiv_symm_union_eq_glue`.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §2.1, §3.2 (Lemma 3.2), §3.3 (Proposition 3.3).
* E. H. Lieb, M. B. Ruskai, *Proof of the strong subadditivity of quantum-mechanical entropy*,
  J. Math. Phys. 14 (1973), 1938–1941.
-/

namespace Arealaw

open Matrix
open scoped ComplexOrder

section PartialTrace

variable {R : Type*} [AddCommMonoid R] {m n m' n' : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
/-- Tracing out the first factor commutes with reindexing the second. -/
theorem traceLeft_submatrix_prodMap (A : Matrix (m × n) (m × n) R) (f g : n' → n) :
    (A.submatrix (Prod.map id f) (Prod.map id g)).traceLeft = A.traceLeft.submatrix f g := by
  ext; simp [traceLeft]

omit [Fintype m] in
/-- Tracing out the second factor commutes with reindexing the first. -/
theorem traceRight_submatrix_prodMap (A : Matrix (m × n) (m × n) R) (f g : m' → m) :
    (A.submatrix (Prod.map f id) (Prod.map g id)).traceRight = A.traceRight.submatrix f g := by
  ext; simp [traceRight]

end PartialTrace

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} {X Y Z : Finset σ}

/-- The complement of `X ∪ Y` in `X ∪ (Y ∪ Z)` is `Z` when `Z` is disjoint from both. -/
theorem union_union_sdiff_union (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (X ∪ (Y ∪ Z)) \ (X ∪ Y) = Z := by
  rw [← Finset.union_assoc,
    Finset.union_sdiff_cancel_left (Finset.disjoint_union_left.2 ⟨hXZ, hYZ⟩)]

/-- Gluing a configuration on pairwise disjoint `X`, `Y`, `Z` as `X ∪ (Y ∪ Z)` agrees with
gluing `X ∪ Y` first and then `Z`. -/
theorem unionEquiv_symm_union_eq_glue (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (x : Reg loc X) (y : Reg loc Y) (z : Reg loc Z) :
    (unionEquiv (Finset.disjoint_union_right.2 ⟨hXY, hXZ⟩)).symm
        (x, (unionEquiv hYZ).symm (y, z)) =
      glue ((unionEquiv hXY).symm (x, y))
        (regEquivOfEq (union_union_sdiff_union hXZ hYZ).symm z) := by
  funext j
  by_cases hX : (j : σ) ∈ X
  · simp [glue, hX]
  · by_cases hY : (j : σ) ∈ Y
    · simp [glue, hX, hY, sdiffEquiv]
    · simp [glue, hX, hY, sdiffEquiv, restr]

variable [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U : Finset σ}

namespace SubState

/-- **Strong subadditivity on regions**: `S(X ∪ Y ∪ Z) + S(Y) ≤ S(X ∪ Y) + S(Y ∪ Z)` for
pairwise disjoint regions; equivalently, the conditional mutual information `I(X : Z | Y)` is
nonnegative. -/
theorem regionEntropy_strong_subadditivity (ρ : SubState (Reg loc U) 𝕜) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    ρ.regionEntropy (Finset.union_subset (Finset.union_subset hX hY) hZ) + ρ.regionEntropy hY ≤
      ρ.regionEntropy (Finset.union_subset hX hY) +
        ρ.regionEntropy (Finset.union_subset hY hZ) := by
  have hd : Disjoint X (Y ∪ Z) := Finset.disjoint_union_right.2 ⟨hXY, hXZ⟩
  have hW : X ∪ (Y ∪ Z) ⊆ U := Finset.union_subset hX (Finset.union_subset hY hZ)
  set M := ptrace hW ρ.M with hMdef
  have hM : M.PosSemidef := posSemidef_ptrace hW ρ.psd
  set e : Reg loc X × Reg loc Y × Reg loc Z ≃ Reg loc (X ∪ (Y ∪ Z)) :=
    ((Equiv.refl _).prodCongr (unionEquiv hYZ).symm).trans (unionEquiv hd).symm
  have hω := hM.submatrix e
  have h := vonNeumann_strong_subadditivity hω
  have hL : (M.submatrix e e).traceLeft = (ptrace Finset.subset_union_right M).submatrix
      (unionEquiv hYZ).symm (unionEquiv hYZ).symm := by
    rw [ptrace_eq_traceLeft hd, ← traceLeft_submatrix_prodMap]
    rfl
  have hR :
      ((M.submatrix e e).submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)).traceRight =
      (ptrace (Finset.union_subset Finset.subset_union_left
        (Finset.subset_union_left.trans Finset.subset_union_right)) M).submatrix
        (unionEquiv hXY).symm (unionEquiv hXY).symm := by
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [traceRight, ptrace, submatrix_apply, of_apply]
    refine Fintype.sum_equiv (regEquivOfEq (union_union_sdiff_union hXZ hYZ).symm) _ _ fun z => ?_
    exact congrArg₂ M (unionEquiv_symm_union_eq_glue hXY hXZ hYZ x y z)
      (unionEquiv_symm_union_eq_glue hXY hXZ hYZ x' y' z)
  have e₁ : vonNeumann hω.isHermitian =
      ρ.regionEntropy (Finset.union_subset (Finset.union_subset hX hY) hZ) := by
    rw [ρ.regionEntropy_congr (Finset.union_assoc X Y Z) _ hW]
    exact vonNeumann_submatrix_equiv hM.isHermitian e
  have e₂ : vonNeumann hω.isHermitian.traceLeft.traceRight = ρ.regionEntropy hY := by
    refine vonNeumann_congr _ _ ?_
    change _ = ptrace hY ρ.M
    rw [hL, ← ptrace_eq_traceRight hYZ, ptrace_ptrace, hMdef, ptrace_ptrace]
  have e₃ : vonNeumann (hω.isHermitian.submatrix (Equiv.prodAssoc _ _ _)).traceRight =
      ρ.regionEntropy (Finset.union_subset hX hY) := by
    have hH := (posSemidef_ptrace (Finset.union_subset Finset.subset_union_left
      (Finset.subset_union_left.trans Finset.subset_union_right) : X ∪ Y ⊆ X ∪ (Y ∪ Z))
      hM).isHermitian
    rw [vonNeumann_congr _ (hH.submatrix _) hR, vonNeumann_submatrix_equiv hH]
    refine vonNeumann_congr _ _ ?_
    rw [hMdef, ptrace_ptrace]
    rfl
  have e₄ :
      vonNeumann hω.isHermitian.traceLeft = ρ.regionEntropy (Finset.union_subset hY hZ) := by
    have hH := (posSemidef_ptrace (Finset.subset_union_right : Y ∪ Z ⊆ X ∪ (Y ∪ Z)) hM).isHermitian
    rw [vonNeumann_congr _ (hH.submatrix _) hL, vonNeumann_submatrix_equiv hH]
    refine vonNeumann_congr _ _ ?_
    rw [hMdef, ptrace_ptrace]
    rfl
  linarith

/-- **Conditioning reduces entropy**: `S(X | T') ≤ S(X | T)` for `T ⊆ T'` with `X` disjoint
from `T'`, writing `S(X | T) = S(X ∪ T) - S(T)`. -/
theorem regionEntropy_union_sub_le_of_subset (ρ : SubState (Reg loc U) 𝕜) {T T' : Finset σ}
    (hTT' : T ⊆ T') (hXT' : Disjoint X T') (hX : X ⊆ U) (hT' : T' ⊆ U) :
    ρ.regionEntropy (Finset.union_subset hX hT') - ρ.regionEntropy hT' ≤
      ρ.regionEntropy (Finset.union_subset hX (hTT'.trans hT')) -
        ρ.regionEntropy (hTT'.trans hT') := by
  have hU : T ∪ (T' \ T) = T' := Finset.union_sdiff_of_subset hTT'
  have h := ρ.regionEntropy_strong_subadditivity (hXT'.mono_right hTT')
    (hXT'.mono_right Finset.sdiff_subset) Finset.disjoint_sdiff hX (hTT'.trans hT')
    (Finset.sdiff_subset.trans hT')
  rw [ρ.regionEntropy_congr (by rw [Finset.union_assoc, hU]) _ (Finset.union_subset hX hT'),
    ρ.regionEntropy_congr hU _ hT'] at h
  linarith

/-- **Monotonicity of mutual information**: `I(X : Y) ≤ I(X : Y ∪ Z)` for pairwise disjoint
`X`, `Y`, `Z`. -/
theorem mutualInfo_le_mutualInfo_union (ρ : SubState (Reg loc U) 𝕜) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hX : X ⊆ U) (hY : Y ⊆ U) (hZ : Z ⊆ U) :
    ρ.mutualInfo hX hY ≤ ρ.mutualInfo hX (Finset.union_subset hY hZ) := by
  have h := ρ.regionEntropy_strong_subadditivity hXY hXZ hYZ hX hY hZ
  rw [ρ.regionEntropy_congr (Finset.union_assoc X Y Z) _
    (Finset.union_subset hX (Finset.union_subset hY hZ))] at h
  rw [mutualInfo_def, mutualInfo_def]
  linarith

end SubState

/-! ## Concavity of the entropy -/

section Concavity

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- **Concavity of the entropy over a family, unnormalized**:
`∑ₖ (S(Aₖ) - η(tr Aₖ)) ≤ S(∑ₖ Aₖ) - η(tr ∑ₖ Aₖ)` for positive semidefinite `Aₖ`, with
`η(x) = -x log x`. -/
theorem sum_vonNeumann_sub_negMulLog_le (A : ι → Matrix n n 𝕜) (hA : ∀ k, (A k).PosSemidef) :
    ∑ k, (vonNeumann (hA k).isHermitian - Real.negMulLog (RCLike.re (A k).trace)) ≤
      vonNeumann (posSemidef_sum Finset.univ fun k _ => hA k).isHermitian -
        Real.negMulLog (RCLike.re (∑ k, A k).trace) := by
  let e : n × Unit ≃ n := Equiv.prodPUnit n
  have key {B C : Matrix _ _ 𝕜} (hB : B.IsHermitian) (hC : C.IsHermitian)
      (h : C = B.submatrix e e) :
      vonNeumann hC - vonNeumann hC.traceLeft =
        vonNeumann hB - Real.negMulLog (RCLike.re B.trace) := by
    subst h
    rw [vonNeumann_submatrix_equiv hB e, vonNeumann_of_unique hC.traceLeft, traceLeft_trace,
      trace_submatrix]
  have h := sum_vonNeumann_sub_traceLeft_le (fun k => (A k).submatrix e e)
    fun k => (hA k).submatrix e
  rwa [Finset.sum_congr rfl fun k _ => key (hA k).isHermitian _ rfl,
    key (posSemidef_sum Finset.univ fun k _ => hA k).isHermitian _
      (by ext; simp [Matrix.sum_apply])] at h

namespace MState

/-- **Concavity of the entropy for arbitrary nonnegative weights**:
`∑ₖ pₖ S(ρₖ) + η(∑ₖ pₖ) ≤ S(∑ₖ pₖ ρₖ)` for states `ρₖ` and `pₖ ≥ 0`. -/
theorem sum_mul_entropy_add_negMulLog_le (ρ : ι → MState n 𝕜) {p : ι → ℝ} (hp : ∀ k, 0 ≤ p k) :
    ∑ k, p k * (ρ k).entropy + Real.negMulLog (∑ k, p k) ≤
      vonNeumann (posSemidef_sum Finset.univ fun k _ => (ρ k).psd.smul (hp k)).isHermitian := by
  have h := sum_vonNeumann_sub_negMulLog_le (fun k => p k • (ρ k).M)
    fun k => (ρ k).psd.smul (hp k)
  have htr : ∀ k, RCLike.re (p k • (ρ k).M).trace = p k := fun k => by
    rw [trace_smul, RCLike.smul_re, (ρ k).tr_eq_one, mul_one]
  rw [Finset.sum_congr rfl fun k _ => by
      rw [vonNeumann_of_eq_smul _ (ρ k).psd.isHermitian rfl, (ρ k).tr_eq_one, htr k, mul_one,
        add_sub_cancel_right],
    trace_sum, map_sum, Finset.sum_congr rfl fun k _ => htr k] at h
  change ∑ k, p k * vonNeumann (ρ k).psd.isHermitian + _ ≤ _
  linarith

/-- **Concavity of the entropy**: `∑ₖ pₖ S(ρₖ) ≤ S(∑ₖ pₖ ρₖ)` for states `ρₖ` and probability
weights `pₖ`. -/
theorem sum_mul_entropy_le (ρ : ι → MState n 𝕜) {p : ι → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) :
    ∑ k, p k * (ρ k).entropy ≤
      vonNeumann (posSemidef_sum Finset.univ fun k _ => (ρ k).psd.smul (hp k)).isHermitian := by
  simpa [hp1] using sum_mul_entropy_add_negMulLog_le ρ hp

end MState

end Concavity

end Arealaw
