import OpenAI.FilterChain
import OpenAI.RegionLift

/-!
# Pinning a Schmidt vector of a region

Let `Ω` be a vector on a region `U`, let `X ⊆ U`, and let `ρ_{Ω,X} = W diag(p) Wᴴ` be the
marginal of `Ω` on `X`, with `W` unitary.  The projection `Pᵢ = W |i⟩⟨i| Wᴴ` onto the `i`-th
eigenvector `uᵢ` of the marginal, acting on `X`, sends `Ω` to its Schmidt term `√pᵢ uᵢ ⊗ wᵢ`
at the cut `X | U \ X`.  The Schmidt terms have squared norms `pᵢ`, and on every `T ⊆ U` disjoint
from `X` the marginal of `Ω` is the sum of the marginals of the Schmidt terms.  For the trial
filters `Pᵢ ⊗ Mⱼ` on `X ∪ Tⱼ`, with every `Tⱼ` disjoint from `X`, the nested product of the
trial filters applied to `Ω` is at least as long as the nested product of the `Mⱼ` applied to
`Pᵢ Ω`.

## Main definitions

* `OpenAI.pinProj`: the projection `W |i⟩⟨i| Wᴴ` onto the `i`-th column of `W`.

## Main statements

* `OpenAI.norm_sq_extendId_pinProj`: `‖Pᵢ Ω‖² = pᵢ`.
* `OpenAI.ptrace_vecMulVec_star_eq_sum_pinProj`: `ρ_{Ω,T} = ∑ᵢ ρ_{Pᵢ Ω, T}` for `T` disjoint
  from `X`.
* `OpenAI.norm_liftProd_trial_ge`: the trial-filter norm comparison.

## Implementation notes

Ported from QICLean (LionSR/QICLean), `QICLean/Entropy/SchmidtPinning.lean` at commit
`32a5a1a8` (Apache 2.0), written there from the proof of Lemma 3.2 of [OAI265].  The region
model is that of `OpenAI.RegionFilter`: vectors live on `Reg loc U`, the pinned region is
`X ⊆ U`, `localLift X` is `Arealaw.extendId hX`, the regional state `regionState T Ω` is the
marginal `Arealaw.ptrace hT (vecMulVec Ω (star Ω))`, the reindexed Kronecker product along
`regionUnionEquiv` is `Arealaw.kronUnion`, and the witness configuration `σ₀` is no longer an
argument.  The trial-filter comparison takes the proofs `hTU` that the regions of the chain lie
in `U`, as `OpenAI.chainList` does, and needs the disjointness of `X` and `Tⱼ` only for the
indices `j < m` of the chain.

QICLean's `eq_of_forall_trace_mul_eq` is Mathlib's `Matrix.ext_iff_trace_mul_right`, its
`norm_toEuclideanLin_sq` is `OpenAI.norm_toEuclideanLin_sq`, and its `mul_prod_eq_prod_mul` is
Mathlib's `Commute.list_prod_right`; none is restated.  QICLean's
`mul_prod_map_mul_of_idempotent` is stated in a monoid, as
`OpenAI.IsIdempotentElem.mul_prod_map_mul`.  With `localLift` replaced by `extendId`,
`norm_sq_localLift_pinProj` is `OpenAI.norm_sq_extendId_pinProj`, `inner_localLift_eq_sum_pinProj`
is `OpenAI.inner_toEuclideanLin_extendId_eq_sum_pinProj`, and `regionState_eq_sum_pinProj` is
`OpenAI.ptrace_vecMulVec_star_eq_sum_pinProj`; `OpenAI.trace_mul_pinProj` is lifted from the
proof of the first.  QICLean works over `ℂ`; everything here is over a general `RCLike` field.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.2, proof of Lemma 3.2.
-/

namespace OpenAI

open Arealaw Matrix
open scoped InnerProductSpace ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Projections onto the columns of a unitary -/

section Proj

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The projection `W |i⟩⟨i| Wᴴ` onto the `i`-th column of `W`. -/
noncomputable def pinProj (W : Matrix m m 𝕜) (i : m) : Matrix m m 𝕜 :=
  W * diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) * Wᴴ

theorem pinProj_conjTranspose (W : Matrix m m 𝕜) (i : m) : (pinProj W i)ᴴ = pinProj W i := by
  simp only [pinProj, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  split_ifs <;> simp_all

theorem pinProj_mul_self {W : Matrix m m 𝕜} (hW : Wᴴ * W = 1) (i : m) :
    pinProj W i * pinProj W i = pinProj W i := by
  have hd : diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) *
      diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) =
      diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext k
    split_ifs <;> simp
  calc pinProj W i * pinProj W i
      = W * (diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) * (Wᴴ * W) *
          diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0)) * Wᴴ := by
        simp only [pinProj, Matrix.mul_assoc]
    _ = pinProj W i := by rw [hW, Matrix.mul_one, hd, pinProj]

theorem sum_pinProj {W : Matrix m m 𝕜} (hW' : W * Wᴴ = 1) : ∑ i, pinProj W i = 1 := by
  have hd : ∑ i : m, diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) = 1 := by
    ext a b
    simp [Matrix.sum_apply, diagonal_apply, one_apply]
  simp only [pinProj]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hd, Matrix.mul_one, hW']

/-- The trace of `W diag(p) Wᴴ` against the `i`-th projection is `pᵢ`. -/
theorem trace_mul_pinProj {W : Matrix m m 𝕜} (hW : Wᴴ * W = 1) (p : m → ℝ) (i : m) :
    (W * diagonal (fun k ↦ (p k : 𝕜)) * Wᴴ * pinProj W i).trace = p i := by
  have : W * diagonal (fun k ↦ (p k : 𝕜)) * Wᴴ *
      (W * diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0) * Wᴴ) =
      W * (diagonal (fun k ↦ (p k : 𝕜)) * diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0)) *
        Wᴴ := by
    calc _ = W * (diagonal (fun k ↦ (p k : 𝕜)) * (Wᴴ * W) *
          diagonal (fun k ↦ if k = i then (1 : 𝕜) else 0)) * Wᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW, Matrix.mul_one]
  rw [pinProj, this, trace_mul_cycle, hW, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal]
  simp

/-- **Projections do not increase norms.** -/
theorem norm_toEuclideanLin_le_of_proj {Q : Matrix m m 𝕜} (hQh : Qᴴ = Q) (hQ : Q * Q = Q)
    (v : EuclideanSpace 𝕜 m) : ‖toEuclideanLin Q v‖ ≤ ‖v‖ := by
  have h : ‖toEuclideanLin Q v‖ ^ 2 ≤ ‖v‖ * ‖toEuclideanLin Q v‖ := by
    rw [norm_toEuclideanLin_sq, hQh, hQ]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (toEuclideanLin Q v)) with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Proj

/-- An idempotent commuting with every factor of a product can be removed from each factor. -/
theorem IsIdempotentElem.mul_prod_map_mul {M : Type*} [Monoid M] {q : M}
    (hq : IsIdempotentElem q) :
    ∀ {l : List M}, (∀ b ∈ l, Commute q b) → q * (l.map (q * ·)).prod = q * l.prod
  | [], _ => by simp
  | b :: l, h => by
    have ih := IsIdempotentElem.mul_prod_map_mul hq fun c hc ↦ h c (List.mem_cons_of_mem b hc)
    have hb : q * b = b * q := h b List.mem_cons_self
    simp only [List.map_cons, List.prod_cons]
    calc q * (q * b * (l.map (q * ·)).prod)
        = q * q * b * (l.map (q * ·)).prod := by simp only [mul_assoc]
      _ = b * (q * (l.map (q * ·)).prod) := by rw [hq.eq, hb, mul_assoc]
      _ = q * (b * l.prod) := by rw [ih, ← mul_assoc, ← hb, mul_assoc]

/-! ## Schmidt terms -/

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U X : Finset σ}

/-- **Squared norms of the Schmidt terms.** If `ρ_{Ω,X} = W diag(p) Wᴴ` with `W` unitary, then
`‖Pᵢ Ω‖² = pᵢ`. -/
theorem norm_sq_extendId_pinProj (hX : X ⊆ U) {Ω : EuclideanSpace 𝕜 (Reg loc U)}
    {W : Matrix (Reg loc X) (Reg loc X) 𝕜} (hW : Wᴴ * W = 1) {p : Reg loc X → ℝ}
    (hρ : ptrace hX (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) =
      W * diagonal (fun k ↦ (p k : 𝕜)) * Wᴴ)
    (i : Reg loc X) :
    ‖toEuclideanLin (extendId hX (pinProj W i)) Ω‖ ^ 2 = p i := by
  rw [norm_toEuclideanLin_extendId_sq, pinProj_conjTranspose, pinProj_mul_self hW, hρ,
    trace_mul_pinProj hW, RCLike.ofReal_re]

/-- On a region disjoint from `X`, expectations split over the Schmidt terms. -/
theorem inner_toEuclideanLin_extendId_eq_sum_pinProj {T : Finset σ} (hX : X ⊆ U) (hT : T ⊆ U)
    (hXT : Disjoint X T) {W : Matrix (Reg loc X) (Reg loc X) 𝕜} (hW : Wᴴ * W = 1)
    (hW' : W * Wᴴ = 1) (A : Matrix (Reg loc T) (Reg loc T) 𝕜)
    (Ω : EuclideanSpace 𝕜 (Reg loc U)) :
    ⟪Ω, toEuclideanLin (extendId hT A) Ω⟫_𝕜 =
      ∑ i, ⟪toEuclideanLin (extendId hX (pinProj W i)) Ω,
        toEuclideanLin (extendId hT A) (toEuclideanLin (extendId hX (pinProj W i)) Ω)⟫_𝕜 := by
  have hterm : ∀ i, ⟪toEuclideanLin (extendId hX (pinProj W i)) Ω,
      toEuclideanLin (extendId hT A) (toEuclideanLin (extendId hX (pinProj W i)) Ω)⟫_𝕜 =
      ⟪Ω, toEuclideanLin (extendId hT A * extendId hX (pinProj W i)) Ω⟫_𝕜 := fun i ↦ by
    have hmul : toEuclideanLin (extendId hT A) (toEuclideanLin (extendId hX (pinProj W i)) Ω) =
        toEuclideanLin (extendId hT A * extendId hX (pinProj W i)) Ω := by
      simp only [toLpLin_mul_same, LinearMap.comp_apply]
    rw [hmul, inner_toEuclideanLin_toEuclideanLin,
      ← extendId_conjTranspose, pinProj_conjTranspose]
    refine congrArg (fun K ↦ ⟪Ω, toEuclideanLin K Ω⟫_𝕜) ?_
    rw [← Matrix.mul_assoc, (commute_extendId_extendId hX hT hXT (pinProj W i) A).eq,
      Matrix.mul_assoc, ← extendId_mul, pinProj_mul_self hW]
  simp_rw [hterm]
  have hsum : ∑ i, extendId hX (pinProj W i) = 1 := by
    have h := (map_sum (extendIdₗ hX) (fun i ↦ pinProj W i) Finset.univ).symm
    simp only [extendIdₗ_apply] at h
    rw [h, sum_pinProj hW', extendId_one]
  calc ⟪Ω, toEuclideanLin (extendId hT A) Ω⟫_𝕜
      = ⟪Ω, toEuclideanLin (extendId hT A * ∑ i, extendId hX (pinProj W i)) Ω⟫_𝕜 := by
        rw [hsum, Matrix.mul_one]
    _ = _ := by rw [Finset.mul_sum, map_sum, LinearMap.sum_apply, inner_sum]

/-- **Marginals split over the Schmidt terms.** On a region `T ⊆ U` disjoint from `X`,
`ρ_{Ω,T} = ∑ᵢ ρ_{Pᵢ Ω, T}`. -/
theorem ptrace_vecMulVec_star_eq_sum_pinProj {T : Finset σ} (hX : X ⊆ U) (hT : T ⊆ U)
    (hXT : Disjoint X T) {W : Matrix (Reg loc X) (Reg loc X) 𝕜} (hW : Wᴴ * W = 1)
    (hW' : W * Wᴴ = 1) (Ω : EuclideanSpace 𝕜 (Reg loc U)) :
    ptrace hT (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) =
      ∑ i, ptrace hT
        (vecMulVec (WithLp.ofLp (toEuclideanLin (extendId hX (pinProj W i)) Ω))
          (star (WithLp.ofLp (toEuclideanLin (extendId hX (pinProj W i)) Ω)))) := by
  refine ext_iff_trace_mul_right.mpr fun A ↦ ?_
  rw [← inner_toEuclideanLin_extendId,
    inner_toEuclideanLin_extendId_eq_sum_pinProj hX hT hXT hW hW' A Ω, Finset.sum_mul,
    trace_sum]
  simp only [inner_toEuclideanLin_extendId]

/-- **Trial filters.** Let `Tⱼ ⊆ U` be regions disjoint from `X ⊆ U`, and let the filter on
`X ∪ Tⱼ` be `Pᵢ ⊗ Mⱼ`.  Then the nested product of the trial filters applied to `Ω` is at least
as long as the nested product of the `Mⱼ` applied to `Pᵢ Ω`. -/
theorem norm_liftProd_trial_ge {m : ℕ} (hX : X ⊆ U) (T : ℕ → Finset σ)
    (hTU : ∀ j : Fin m, T j ⊆ U) (hXT : ∀ j : Fin m, Disjoint X (T j))
    {W : Matrix (Reg loc X) (Reg loc X) 𝕜} (hW : Wᴴ * W = 1) (i : Reg loc X)
    (M : (j : Fin m) → Matrix (Reg loc (T j)) (Reg loc (T j)) 𝕜)
    (Ω : EuclideanSpace 𝕜 (Reg loc U)) :
    ‖toEuclideanLin (liftProd (chainList T hTU M fun _ ↦ True))
        (toEuclideanLin (extendId hX (pinProj W i)) Ω)‖ ≤
      ‖toEuclideanLin (liftProd (chainList (fun j ↦ X ∪ T j)
        (fun j ↦ Finset.union_subset hX (hTU j))
        (fun j : Fin m ↦ kronUnion (hXT j) (pinProj W i) (M j)) fun _ ↦ True)) Ω‖ := by
  set Q := extendId hX (pinProj W i)
  set idx := ((List.finRange m).filter fun _ ↦ decide True).reverse
  have hQ : IsIdempotentElem Q := by
    rw [IsIdempotentElem, ← extendId_mul, pinProj_mul_self hW]
  have hQh : Qᴴ = Q := by rw [← extendId_conjTranspose, pinProj_conjTranspose]
  have hcomm : ∀ B ∈ idx.map (fun j : Fin m ↦ extendId (hTU j) (M j)), Commute Q B := by
    intro B hB
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hB
    exact commute_extendId_extendId hX (hTU j) (hXT j) _ _
  have hL : liftProd (chainList (fun j ↦ X ∪ T j) (fun j ↦ Finset.union_subset hX (hTU j))
      (fun j : Fin m ↦ kronUnion (hXT j) (pinProj W i) (M j)) fun _ ↦ True) =
      ((idx.map fun j : Fin m ↦ extendId (hTU j) (M j)).map (Q * ·)).prod := by
    simp only [liftProd, chainList, List.map_map, Function.comp_def, idx]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    exact extendId_kronUnion hX (hTU j) (hXT j) _ _
  have hM : liftProd (chainList T hTU M fun _ ↦ True) =
      (idx.map fun j : Fin m ↦ extendId (hTU j) (M j)).prod := by
    simp only [liftProd, chainList, List.map_map, Function.comp_def, idx]
  calc ‖toEuclideanLin (liftProd (chainList T hTU M fun _ ↦ True)) (toEuclideanLin Q Ω)‖
      = ‖toEuclideanLin Q (toEuclideanLin (liftProd (chainList (fun j ↦ X ∪ T j)
          (fun j ↦ Finset.union_subset hX (hTU j))
          (fun j : Fin m ↦ kronUnion (hXT j) (pinProj W i) (M j)) fun _ ↦ True)) Ω)‖ := by
        rw [← LinearMap.comp_apply, ← toLpLin_mul_same, ← LinearMap.comp_apply,
          ← toLpLin_mul_same, hL,
          IsIdempotentElem.mul_prod_map_mul hQ hcomm, hM, (Commute.list_prod_right _ _ hcomm).eq]
    _ ≤ _ := norm_toEuclideanLin_le_of_proj hQh hQ.eq _

end OpenAI
