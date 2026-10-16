import OpenAI.ConditionalContinuity
import OpenAI.RegionEntropy
import OpenAI.RegionSSA

/-!
# The entropy identity and continuity steps of the collar bound

Two deterministic steps of the proof of Proposition 9.6 [OAI265, §9.5].  At each leaf of the
scan the sites are partitioned into `X, U, Y, V`; for a pure state the sharp-comparison
quantities `g_pre = S(XU) + S(V) - S(Y)` and `g_post = S(U) + S(UY) - S(Y)` satisfy
`2 S(X) + g_pre - g_post = I(X : V) + I(X : YV)` (eq. (9.20)), and a region `W ⊆ V` gives the
lower bound `2 I(X : W)`.  The mutual information `I(X : B)` moves under a change of state by at
most `8 √δ log (e d_X)`, `δ` the trace distance (Lemma 2.1): only the dimension of `X` enters.

## Main statements

* `OpenAI.collarLeaf_entropy_identity`: eq. (9.20).
* `OpenAI.two_mutualInfo_le_collarLeaf`: the lower bound by `2 I(X : W)`.
* `OpenAI.abs_mutualInfo_sub_le`: continuity of mutual information.
-/

namespace Arealaw.SubState

open scoped MatrixOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {S T : Finset σ}

/-- The trace distance contracts under restriction to a subregion. -/
theorem D₁_restrict_le (h : S ⊆ T) (ρ τ : SubState (Reg loc T) 𝕜) :
    (ρ.restrict h).D₁ (τ.restrict h) ≤ ρ.D₁ τ := by
  classical
  obtain ⟨M, hM, hM1, hval⟩ := ((ρ.restrict h).isGreatest_D₁ (τ.restrict h)).1
  have hE0 : 0 ≤ extendId h M := by
    rw [Matrix.nonneg_iff_posSemidef] at hM ⊢
    exact posSemidef_extendId h hM
  have hE1 : extendId h M ≤ 1 := by
    rw [Matrix.le_iff] at hM1 ⊢
    have : (1 : Matrix (Reg loc T) (Reg loc T) 𝕜) - extendId h M = extendId h (1 - M) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, extendId_add, extendId_one, ← neg_one_smul 𝕜 M,
        extendId_smul, neg_one_smul]
    rw [this]
    exact posSemidef_extendId h hM1
  have htr : (M * ((ρ.restrict h).M - (τ.restrict h).M)).trace =
      (extendId h M * (ρ.M - τ.M)).trace := by
    rw [restrict_M, restrict_M, ← ptrace_sub, Matrix.trace_mul_comm, trace_ptrace_mul,
      Matrix.trace_mul_comm]
  rw [hval, htr]
  exact ρ.abs_re_trace_mul_le_D₁ τ hE0 hE1

end Arealaw.SubState

namespace OpenAI

open Arealaw Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜]

/-- **The leaf entropy identity** [OAI265, §9.5, eq. (9.20)]: for a pure state on `Λ` and a
partition `Λ = X ∪ U ∪ Y ∪ V` into pairwise disjoint regions,
`2 S(X) + (S(XU) + S(V) - S(Y)) - (S(U) + S(UY) - S(Y)) = I(X : V) + I(X : YV)`. -/
theorem collarLeaf_entropy_identity {Λ X U Y V : Finset σ} (ψ : Reg loc Λ → 𝕜)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hX : X ⊆ Λ) (hU : U ⊆ Λ) (hY : Y ⊆ Λ) (hV : V ⊆ Λ)
    (hXU : Disjoint X U) (hXY : Disjoint X Y) (hXV : Disjoint X V) (hUY : Disjoint U Y)
    (hUV : Disjoint U V) (hYV : Disjoint Y V) (hcover : X ∪ U ∪ Y ∪ V = Λ) :
    2 * (pureState ψ hψ).regionEntropy hX +
        ((pureState ψ hψ).regionEntropy (Finset.union_subset hX hU) +
          (pureState ψ hψ).regionEntropy hV - (pureState ψ hψ).regionEntropy hY) -
        ((pureState ψ hψ).regionEntropy hU +
          (pureState ψ hψ).regionEntropy (Finset.union_subset hU hY) -
          (pureState ψ hψ).regionEntropy hY) =
      (pureState ψ hψ).mutualInfo hX hV +
        (pureState ψ hψ).mutualInfo hX (Finset.union_subset hY hV) := by
  rw [Finset.disjoint_left] at hXU hXY hXV hUY hUV hYV
  have hsd : ∀ {A B : Finset σ} (hA : A ⊆ Λ) (hB : B ⊆ Λ), Λ \ A = B →
      (pureState ψ hψ).regionEntropy hB = (pureState ψ hψ).regionEntropy hA := fun hA hB e =>
    ((pureState ψ hψ).regionEntropy_congr e.symm hB Finset.sdiff_subset).trans
      (regionEntropy_pureState_sdiff hA ψ hψ)
  have e₁ := hsd (Finset.union_subset hU hY) (Finset.union_subset hX hV) (by
    subst hcover; ext a; simp only [Finset.mem_sdiff, Finset.mem_union]; grind)
  have e₂ := hsd (Finset.union_subset hX hU) (Finset.union_subset hY hV) (by
    subst hcover; ext a; simp only [Finset.mem_sdiff, Finset.mem_union]; grind)
  have e₃ := hsd hU (Finset.union_subset hX (Finset.union_subset hY hV)) (by
    subst hcover; ext a; simp only [Finset.mem_sdiff, Finset.mem_union]; grind)
  rw [SubState.mutualInfo_def, SubState.mutualInfo_def, e₁, e₂, e₃]
  ring

/-- The lower bound of the leaf identity [OAI265, §9.5, after eq. (9.20)]: if a region `W` lies
in the far part `V` of the leaf partition, the left side of eq. (9.20) is at least
`2 I(X : W)`. -/
theorem two_mutualInfo_le_collarLeaf {Λ X U Y V W : Finset σ} (ψ : Reg loc Λ → 𝕜)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hX : X ⊆ Λ) (hU : U ⊆ Λ) (hY : Y ⊆ Λ) (hV : V ⊆ Λ)
    (hXU : Disjoint X U) (hXY : Disjoint X Y) (hXV : Disjoint X V) (hUY : Disjoint U Y)
    (hUV : Disjoint U V) (hYV : Disjoint Y V) (hcover : X ∪ U ∪ Y ∪ V = Λ) (hWV : W ⊆ V) :
    2 * (pureState ψ hψ).mutualInfo hX (hWV.trans hV) ≤
      2 * (pureState ψ hψ).regionEntropy hX +
        ((pureState ψ hψ).regionEntropy (Finset.union_subset hX hU) +
          (pureState ψ hψ).regionEntropy hV - (pureState ψ hψ).regionEntropy hY) -
        ((pureState ψ hψ).regionEntropy hU +
          (pureState ψ hψ).regionEntropy (Finset.union_subset hU hY) -
          (pureState ψ hψ).regionEntropy hY) := by
  rw [collarLeaf_entropy_identity ψ hψ hX hU hY hV hXU hXY hXV hUY hUV hYV hcover]
  set ρ := (pureState ψ hψ).toSubState
  have h₁ : ρ.mutualInfo hX (hWV.trans hV) ≤ ρ.mutualInfo hX hV :=
    (ρ.mutualInfo_le_mutualInfo_union (hXV.mono_right hWV) (hXV.mono_right Finset.sdiff_subset)
      Finset.disjoint_sdiff hX (hWV.trans hV) (Finset.sdiff_subset.trans hV)).trans_eq
      (ρ.mutualInfo_congr rfl (Finset.union_sdiff_of_subset hWV) _ _ _ _)
  have h₂ : ρ.mutualInfo hX hV ≤ ρ.mutualInfo hX (Finset.union_subset hY hV) :=
    (ρ.mutualInfo_le_mutualInfo_union hXV hXY hYV.symm hX hV hY).trans_eq
      (ρ.mutualInfo_congr rfl (Finset.union_comm V Y) _ _ _ _)
  linarith

/-- **Continuity of mutual information** [OAI265, Lemma 2.1, as used at the end of §9.5]: for
disjoint regions `X`, `B` and states `ρ`, `τ` at trace distance `δ`,
`|I_ρ(X : B) - I_τ(X : B)| ≤ 8 √δ log (e d_X)`, with `d_X` the dimension of `X` alone. -/
theorem abs_mutualInfo_sub_le {U X B : Finset σ} (hX : X ⊆ U) (hB : B ⊆ U)
    (hXB : Disjoint X B) (ρ τ : MState (Reg loc U) 𝕜) :
    |ρ.mutualInfo hX hB - τ.mutualInfo hX hB| ≤
      8 * Real.sqrt (ρ.toSubState.D₁ τ.toSubState) *
        Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
  have hlog : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (Reg loc X)) with h0 | h0
    · simp [h0]
    · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one)
        (by exact_mod_cast h0))
  have hδ : ∀ {Z : Finset σ} (hZ : Z ⊆ U), Real.sqrt ((ρ.toSubState.restrict hZ).D₁
      (τ.toSubState.restrict hZ)) ≤ Real.sqrt (ρ.toSubState.D₁ τ.toSubState) := fun hZ =>
    Real.sqrt_le_sqrt (SubState.D₁_restrict_le hZ _ _)
  have hc := (conditional_continuity U X B hX hB hXB ρ τ).2
  have h0 := (conditional_continuity U X ∅ hX (Finset.empty_subset U)
    (Finset.disjoint_empty_right X) ρ τ).2
  have hX₀ := fun (ρ : MState (Reg loc U) 𝕜) => ρ.toSubState.regionEntropy_congr
    (Finset.union_empty X) (Finset.union_subset hX (Finset.empty_subset U)) hX
  rw [hX₀, hX₀, MState.regionEntropy_empty, MState.regionEntropy_empty] at h0
  have key := mul_le_mul_of_nonneg_right (hδ (Finset.union_subset hX hB)) hlog
  have key₀ := mul_le_mul_of_nonneg_right
    (hδ (Finset.union_subset hX (Finset.empty_subset U))) hlog
  rw [SubState.mutualInfo_def, SubState.mutualInfo_def]
  rw [abs_le] at hc h0 ⊢
  constructor <;> linarith

end OpenAI
