import Arealaw.Purify

/-!
# The ancilla as an extra site

`Arealaw.Purify` purifies at the level of one index type.  Here the purifying system becomes
one extra site of an extended chain, so it is a `Finset` region like any other and the
area-law regions can avoid it.  Theorem 4 of the target paper needs this.

## Main statements

* `purifyChain_spec`: tracing the ancilla out returns the original state.
* `MState.isIdempotentElem_purifyChain`: the purified state is pure, recorded as
  idempotence of its density matrix.
* `MState.regionEntropy_purifyChain`: the chain region carries the entropy it purifies.

## Implementation notes

The extended site type is `Option σ` with `none` the ancilla.  Its local space is the
whole-chain index `Reg loc univ`, which in general lives one universe above `loc i`, so this
file pins `σ` and `loc` to `Type`.  The bridge to `PureState` and the zero-entropy corollary
are absent.
-/

namespace Arealaw

open scoped ComplexOrder

variable {σ : Type} [DecidableEq σ] [Fintype σ] {loc : σ → Type}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  {𝕜 : Type*} [RCLike 𝕜]

/-! ## The extended chain -/

/-- The extended local family on `Option σ`: the ancilla site `none` carries a copy of the
whole-chain index, every other site is unchanged. -/
def LocP (loc : σ → Type) : Option σ → Type
  | none => Reg loc (Finset.univ : Finset σ)
  | some i => loc i

/-- Every extended local space is finite: the ancilla carries the whole-chain index. -/
instance : ∀ o : Option σ, Fintype (LocP loc o)
  | none => inferInstanceAs (Fintype (Reg loc _))
  | some i => inferInstanceAs (Fintype (loc i))

/-- Every extended local space has decidable equality. -/
instance : ∀ o : Option σ, DecidableEq (LocP loc o)
  | none => inferInstanceAs (DecidableEq (Reg loc _))
  | some i => inferInstanceAs (DecidableEq (loc i))

/-- The original chain, as a region of the extended chain. -/
def chainSites (σ : Type) [Fintype σ] : Finset (Option σ) :=
  Finset.univ.map Function.Embedding.some

omit [DecidableEq σ] in
/-- The chain sites form a region of the extended chain. -/
theorem chainSites_subset_univ : chainSites σ ⊆ (Finset.univ : Finset (Option σ)) :=
  Finset.subset_univ _

/-- The complement of the chain is exactly the ancilla. -/
theorem sdiff_chainSites : (Finset.univ : Finset (Option σ)) \ chainSites σ = {none} := by
  ext (_ | _) <;> simp [chainSites]

/-- Configurations on the chain sites of the extended chain are configurations on the
original chain. -/
def embedEquiv : Reg (LocP loc) (chainSites σ) ≃ Reg loc (Finset.univ : Finset σ) where
  toFun z i := z ⟨some i.1, by simp [chainSites]⟩
  invFun x := fun ⟨o, ho⟩ =>
    match o, ho with
    | some j, _ => x ⟨j, Finset.mem_univ j⟩
    | none, h => by simp [chainSites] at h
  left_inv z := funext fun ⟨o, ho⟩ => by cases o <;> grind [chainSites]
  right_inv _ := rfl

section
omit [DecidableEq σ] [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

theorem embedEquiv_apply (z : Reg (LocP loc) (chainSites σ)) (i : (Finset.univ : Finset σ))
    (hi : some (i : σ) ∈ chainSites σ) : embedEquiv z i = z ⟨some i.1, hi⟩ := rfl

theorem embedEquiv_symm_apply (x : Reg loc (Finset.univ : Finset σ)) (j : σ)
    (hj : some j ∈ chainSites σ) :
    (embedEquiv (loc := loc)).symm x ⟨some j, hj⟩ = x ⟨j, Finset.mem_univ j⟩ := rfl

end

/-- The ancilla region also carries the chain index. -/
def ancEquiv : Reg (LocP loc) ({none} : Finset (Option σ)) ≃ Reg loc (Finset.univ : Finset σ) where
  toFun z := z ⟨none, Finset.mem_singleton_self _⟩
  invFun x := fun ⟨o, ho⟩ =>
    match o, ho with
    | none, _ => x
    | some j, h => by simp at h
  left_inv z := funext fun ⟨o, ho⟩ => by cases o <;> grind
  right_inv _ := rfl

section
omit [DecidableEq σ] [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

theorem ancEquiv_apply (z : Reg (LocP loc) ({none} : Finset (Option σ)))
    (h : none ∈ ({none} : Finset (Option σ))) : ancEquiv z = z ⟨none, h⟩ := rfl

theorem ancEquiv_symm_apply (x : Reg loc (Finset.univ : Finset σ))
    (h : none ∈ ({none} : Finset (Option σ))) : (ancEquiv (loc := loc)).symm x ⟨none, h⟩ = x := rfl

end

/-! ## The purified chain state -/

/-- The chain part of an extended configuration. -/
def chainPart (w : Reg (LocP loc) (Finset.univ : Finset (Option σ))) :
    Reg loc (Finset.univ : Finset σ) :=
  embedEquiv (restr chainSites_subset_univ w)

/-- The ancilla configurations of the extended chain carry the chain index. -/
def ancPartEquiv : Reg (LocP loc) ((Finset.univ : Finset (Option σ)) \ chainSites σ)
      ≃ Reg loc (Finset.univ : Finset σ) :=
  (regEquivOfEq sdiff_chainSites).trans ancEquiv

/-- The ancilla part of an extended configuration, read through
`univ \ chainSites = {none}`. -/
def ancPart (w : Reg (LocP loc) (Finset.univ : Finset (Option σ))) :
    Reg loc (Finset.univ : Finset σ) :=
  ancEquiv (regEquivOfEq sdiff_chainSites (restr Finset.sdiff_subset w))

section
omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

theorem ancPartEquiv_apply (z : Reg (LocP loc) ((Finset.univ : Finset (Option σ)) \ chainSites σ)) :
    ancPartEquiv z = ancEquiv (regEquivOfEq sdiff_chainSites z) := rfl

theorem ancPartEquiv_symm_apply (x : Reg loc (Finset.univ : Finset σ)) :
    (ancPartEquiv (loc := loc)).symm x
      = (regEquivOfEq sdiff_chainSites).symm (ancEquiv.symm x) := rfl

/-- The chain part of a glued configuration is its chain-site argument. -/
@[simp] theorem chainPart_glue (x : Reg (LocP loc) (chainSites σ))
    (z : Reg (LocP loc) ((Finset.univ : Finset (Option σ)) \ chainSites σ)) :
    chainPart (glue x z) = embedEquiv x := by
  simp [chainPart]

/-- The ancilla part of a glued configuration is its ancilla argument. -/
@[simp] theorem ancPart_glue (x : Reg (LocP loc) (chainSites σ))
    (z : Reg (LocP loc) ((Finset.univ : Finset (Option σ)) \ chainSites σ)) :
    ancPart (glue x z) = ancEquiv (regEquivOfEq sdiff_chainSites z) := by
  simp [ancPart]

end

/-- The purifying vector of the chain: `√ρ` along the chain and ancilla parts. -/
noncomputable def purifyVec (ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    Reg (LocP loc) (Finset.univ : Finset (Option σ)) → 𝕜 :=
  fun w => purifyMat ρ (chainPart w) (ancPart w)

/-- **The purified chain state**: the pure state with coefficient matrix `√ρ`, as a density
matrix on the extended chain, chain sites indexing one leg and the ancilla the other. -/
noncomputable def purifyChain (ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    Matrix (Reg (LocP loc) (Finset.univ : Finset (Option σ)))
      (Reg (LocP loc) (Finset.univ : Finset (Option σ))) 𝕜 :=
  Matrix.of fun w w' =>
    purifyMat ρ (chainPart w) (ancPart w) * star (purifyMat ρ (chainPart w') (ancPart w'))

/-- **The purification specification**: tracing the ancilla out of the purified chain returns
the original state, relabelled along `embedEquiv`.  Positive semidefiniteness is needed because
`√ρ` squares to `ρ` only then. -/
theorem purifyChain_spec {ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜} (hρ : ρ.PosSemidef) :
    ptrace chainSites_subset_univ (purifyChain ρ) = ρ.submatrix embedEquiv embedEquiv := by
  -- summing the purifying matrix against its conjugate over the ancilla index is `rhoA`
  have key : ∀ a b : Reg loc (Finset.univ : Finset σ),
      (∑ c : Reg loc (Finset.univ : Finset σ),
        purifyMat ρ a c * star (purifyMat ρ b c)) = ρ a b := fun a b => by
    simpa [rhoA, Matrix.mul_apply] using congr_fun₂ (rhoA_purifyMat hρ) a b
  ext x y
  simp only [ptrace, purifyChain, Matrix.of_apply, Matrix.submatrix_apply,
    chainPart_glue, ancPart_glue]
  exact (Fintype.sum_equiv (ancPartEquiv (loc := loc)) _ _ fun z => rfl).trans
    (key (embedEquiv x) (embedEquiv y))

/-- The purified chain state is rank one: `v vᴴ` for the purifying vector. -/
theorem purifyChain_eq_vecMulVec (ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    purifyChain ρ = Matrix.vecMulVec (purifyVec ρ) (star (purifyVec ρ)) := rfl

/-- The purified chain state is positive semidefinite. -/
theorem posSemidef_purifyChain (ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜) : (purifyChain ρ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (purifyVec ρ)

/-- The purified chain state has the same trace as `ρ`, so it is normalized exactly when
`ρ` is. -/
theorem trace_purifyChain {ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜} (hρ : ρ.PosSemidef) :
    (purifyChain ρ).trace = ρ.trace := by
  rw [← trace_ptrace chainSites_subset_univ, purifyChain_spec hρ, Matrix.trace_submatrix]

/-! ## Purity -/

/-- Purity before normalization: a rank-one matrix is idempotent up to its trace. -/
theorem purifyChain_mul_self (ρ : Matrix (Reg loc (Finset.univ : Finset σ))
    (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    purifyChain ρ * purifyChain ρ = (purifyChain ρ).trace • purifyChain ρ := by
  rw [purifyChain_eq_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
    Matrix.trace_vecMulVec, dotProduct_comm]

/-! ## The purified chain as a state -/

namespace MState

/-- The purified chain state of a normalized chain state: an ordinary state on the extended
chain, not on a separate tensor factor. -/
noncomputable def purifyChain (ρ : MState (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    MState (Reg (LocP loc) (Finset.univ : Finset (Option σ))) 𝕜 :=
  mk' (posSemidef_purifyChain ρ.M) (trace_purifyChain ρ.psd ▸ ρ.tr_eq_one)

/-- The density matrix of the purified chain state. -/
@[simp] theorem purifyChain_M (ρ : MState (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    ρ.purifyChain.M = Arealaw.purifyChain ρ.M := rfl

/-- The purified chain state is pure: normalized, a rank-one orthogonal projection. -/
theorem isIdempotentElem_purifyChain (ρ : MState (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    IsIdempotentElem ρ.purifyChain.M := by
  simp [IsIdempotentElem, purifyChain_mul_self, trace_purifyChain ρ.psd, ρ.trace_eq_one]

/-- Restricting the purified chain state back to the chain sites returns the original
state, relabelled along `embedEquiv`: the state-level form of `purifyChain_spec`. -/
theorem restrict_purifyChain (ρ : MState (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    (ρ.purifyChain.restrict chainSites_subset_univ).M = ρ.M.submatrix embedEquiv embedEquiv :=
  purifyChain_spec ρ.psd

/-- The same as an equation of states: relabelling along `embedEquiv` is the only
difference between the two sides. -/
theorem restrict_purifyChain_eq (ρ : MState (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    ρ.purifyChain.restrict chainSites_subset_univ = ρ.submatrix embedEquiv :=
  MState.ext (restrict_purifyChain ρ)

/-- **The purification is entropically faithful on the chain**: the chain region of the
purified state carries exactly the entropy of the state it purifies. -/
@[simp] theorem regionEntropy_purifyChain (ρ : MState (Reg loc (Finset.univ : Finset σ)) 𝕜) :
    ρ.purifyChain.toSubState.regionEntropy chainSites_subset_univ = ρ.entropy := by
  rw [SubState.regionEntropy_def, ← toSubState_restrict, restrict_purifyChain_eq,
    toSubState_submatrix, SubState.entropy_submatrix]

end MState

end Arealaw
