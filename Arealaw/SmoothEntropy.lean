import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.EReal.Inv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Lattice.Nat

import Arealaw.PurifiedDist

/-!
# Smooth entropies for the area-law theorem

This file defines the quantum entropy quantities in Brandão–Horodecki's area-law paper:
log-rank max-entropy, conditional min-entropy, and their smoothing over subnormalized states.
It uses the existing purified distance and ball from `PurifiedDist.lean`; the mixed-state
structures and their restriction and relabelling operations remain in `Mixed.lean`.

## Main definitions

* `maxEntropy`: logarithm of matrix rank, the paper's `H_max` in Eq. (4).
* `MinEntropyFeasible`, `minEntropy`: the normalized-conditioning-state domination condition
  and the supremum of its feasible thresholds, as in Eq. (16).
* `SubState.smoothMaxEntropy`, `SubState.smoothMinEntropy`: the infimum and supremum over
  `SubState.ball`, as in Eqs. (4) and (17).
* `SubState.smoothMaxMutualInfo`: the difference of smooth entropies in Eq. (18), evaluated
  on two disjoint regions.

## Main statements

* Log-rank entropy is bounded by logarithmic dimension and is invariant under relabelling.
* Every state in the smoothing ball gives the corresponding one-sided entropy bound.
* `SubState.exists_smoothMaxEntropy_minimizer`: the smooth log-rank infimum is attained,
  because any nonempty set of feasible support dimensions has a least natural number.
* Enlarging the smoothing ball decreases smooth max-entropy and increases smooth min-entropy.
* `minEntropy₂_eq_iSup` identifies the bit-valued min-entropy with the paper's `2^(-r)` formula.

## Notation

Natural logarithms stay primitive, following the existing Shannon convention in
`Entropy.lean`. Names ending in `₂` give the paper's base-two values by division by `log 2`.

## Implementation notes

`maxEntropy` is Rényi entropy of order zero, the log-rank quantity. The Rényi-1/2 entropy
expressed through fidelity is a different quantity: later min/max duality and the paper's
subadditivity proof require a separate symbol and an explicit conversion inequality. Those
results are not claimed here. Physlib has no corresponding entropy definitions at the pinned
revision.

We use extended real values (`EReal`) because rank zero has logarithm minus infinity,
conditional min-entropy can be plus infinity, and a negative-radius ball is empty. Thus the
optimization formulas follow the paper directly without identifying `log 0` with Lean's
real-logarithm value zero. Real-valued wrappers need finite-value theorems first, since
`EReal.toReal` would otherwise send both infinities to zero. Matrix-level primitives carry
only the assumptions needed by their formulas.

Keeping this layer above `PurifiedDist.lean` reuses `SubState.D` and `SubState.ball`
without changing the foundational import order of `Entropy.lean`, `State.lean`, or
`Mixed.lean`. The lemmas here provide witnesses, optimal supports, radius monotonicity,
dimension bounds, and endpoint conventions; substantial entropy inequalities belong in
separate files.
-/

namespace Arealaw

open scoped ENNReal ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

/-- Logarithmic rank in nats, the unsmoothed max-entropy used in Eq. (4).
The zero matrix has entropy `⊥`, meaning minus infinity. -/
noncomputable def maxEntropy (M : Matrix ι ι 𝕜) : EReal :=
  ENNReal.log (M.rank : ℝ≥0∞)

/-- Log-rank entropy in bits, derived from its natural-log value. -/
noncomputable def maxEntropy₂ (M : Matrix ι ι 𝕜) : EReal :=
  maxEntropy M / (Real.log 2 : EReal)

/-- Zero rank has logarithm minus infinity. -/
@[simp] theorem maxEntropy_zero : maxEntropy (0 : Matrix ι ι 𝕜) = ⊥ := by
  simp [maxEntropy]

/-- At positive rank, the extended definition is the usual finite real logarithm. -/
theorem maxEntropy_eq_log_rank {M : Matrix ι ι 𝕜} (h : M.rank ≠ 0) :
    maxEntropy M = (Real.log (M.rank : ℝ) : EReal) := by
  simp [maxEntropy, ENNReal.log_pos_real', Nat.pos_iff_ne_zero, h]

/-- At positive rank, bit-valued max-entropy is the real base-two logarithm. -/
theorem maxEntropy₂_eq_log_rank {M : Matrix ι ι 𝕜} (h : M.rank ≠ 0) :
    maxEntropy₂ M = ((Real.log (M.rank : ℝ) / Real.log 2 : ℝ) : EReal) := by
  rw [maxEntropy₂, maxEntropy_eq_log_rank h, ← EReal.coe_div]

/-- Log-rank entropy never exceeds logarithmic dimension, including dimension zero. -/
theorem maxEntropy_le_log_card (M : Matrix ι ι 𝕜) :
    maxEntropy M ≤ ENNReal.log (Fintype.card ι : ℝ≥0∞) :=
  ENNReal.log_le_log (mod_cast M.rank_le_card_width)

/-- A change of basis labels leaves the support dimension unchanged. -/
@[simp] theorem maxEntropy_submatrix_equiv {κ : Type*} [Fintype κ]
    (M : Matrix ι ι 𝕜) (e : κ ≃ ι) :
    maxEntropy (M.submatrix e e) = maxEntropy M := by
  simp only [maxEntropy, Matrix.rank_submatrix]

/-- A positive-rank matrix has nonnegative log-rank entropy. -/
theorem maxEntropy_nonneg {M : Matrix ι ι 𝕜} (h : M.rank ≠ 0) :
    0 ≤ maxEntropy M :=
  ENNReal.zero_le_log_iff.mpr (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero h))

/-- A finite matrix never has infinite positive log-rank entropy. -/
theorem maxEntropy_ne_top (M : Matrix ι ι 𝕜) : maxEntropy M ≠ ⊤ := by
  simp [maxEntropy]

namespace SubState

variable [DecidableEq ι]

/-- Enlarging the allowed error enlarges the purified-distance ball. -/
theorem ball_mono (ρ : SubState ι 𝕜) {ε δ : ℝ} (hεδ : ε ≤ δ) :
    ρ.ball ε ⊆ ρ.ball δ :=
  fun _ hτ => hτ.trans hεδ

/-- Smooth log-rank entropy in nats, defined as in Eq. (4) by minimizing `log rank`
over the subnormalized purified-distance ball. The extended infimum is `⊤` for an empty
ball. At nonnegative radius the minimum is attained, as proved below. -/
noncomputable def smoothMaxEntropy (ρ : SubState ι 𝕜) (ε : ℝ) : EReal :=
  ⨅ (τ : SubState ι 𝕜) (_ : τ ∈ ρ.ball ε), maxEntropy τ.M

/-- Smooth max-entropy in bits, the display convention of Theorem 1. -/
noncomputable def smoothMaxEntropy₂ (ρ : SubState ι 𝕜) (ε : ℝ) : EReal :=
  ρ.smoothMaxEntropy ε / (Real.log 2 : EReal)

/-- Any approximating state bounds smooth max-entropy from above. -/
theorem smoothMaxEntropy_le_of_mem (ρ : SubState ι 𝕜) {τ : SubState ι 𝕜} {ε : ℝ}
    (hτ : τ ∈ ρ.ball ε) : ρ.smoothMaxEntropy ε ≤ maxEntropy τ.M :=
  iInf₂_le τ hτ

/-- The minimum in Eq. (4) is attained whenever the smoothing radius is nonnegative. -/
theorem exists_smoothMaxEntropy_minimizer (ρ : SubState ι 𝕜) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ τ : SubState ι 𝕜, τ ∈ ρ.ball ε ∧ maxEntropy τ.M = ρ.smoothMaxEntropy ε := by
  -- Ranks are natural numbers, so the nonempty ball (it contains `ρ`) has a rank-minimal member.
  obtain ⟨τ, hτ, hmin⟩ := (measure fun τ : SubState ι 𝕜 => τ.M.rank).wf.has_min (ρ.ball ε)
    ⟨ρ, ρ.self_mem_ball hε⟩
  refine ⟨τ, hτ, le_antisymm ?_ (ρ.smoothMaxEntropy_le_of_mem hτ)⟩
  -- Monotonicity of the logarithm turns the least rank into the least entropy.
  exact le_iInf₂ fun υ hυ => ENNReal.log_monotone (Nat.cast_le.mpr (not_lt.mp (hmin υ hυ)))

/-- Smoothing at nonnegative radius cannot increase max-entropy. -/
theorem smoothMaxEntropy_le_maxEntropy (ρ : SubState ι 𝕜) {ε : ℝ} (hε : 0 ≤ ε) :
    ρ.smoothMaxEntropy ε ≤ maxEntropy ρ.M :=
  ρ.smoothMaxEntropy_le_of_mem (ρ.self_mem_ball hε)

/-- Smooth max-entropy is bounded above by logarithmic dimension at nonnegative radius. -/
theorem smoothMaxEntropy_le_log_card (ρ : SubState ι 𝕜) {ε : ℝ} (hε : 0 ≤ ε) :
    ρ.smoothMaxEntropy ε ≤ ENNReal.log (Fintype.card ι : ℝ≥0∞) :=
  (ρ.smoothMaxEntropy_le_maxEntropy hε).trans (maxEntropy_le_log_card ρ.M)

/-- Allowing more approximation error can only lower smooth max-entropy. -/
theorem smoothMaxEntropy_antitone (ρ : SubState ι 𝕜) : Antitone ρ.smoothMaxEntropy :=
  fun _ _ h => iInf_le_iInf_of_subset (ρ.ball_mono h)

/-- The bit-valued smooth max-entropy has the same monotonicity in its radius. -/
theorem smoothMaxEntropy₂_antitone (ρ : SubState ι 𝕜) : Antitone ρ.smoothMaxEntropy₂ :=
  fun _ _ hεδ => EReal.div_le_div_right_of_nonneg
    (EReal.coe_nonneg.mpr (Real.log_nonneg one_le_two)) (ρ.smoothMaxEntropy_antitone hεδ)

/-- A negative smoothing radius has no admissible states, giving the extended infimum `⊤`. -/
theorem smoothMaxEntropy_eq_top_of_neg (ρ : SubState ι 𝕜) {ε : ℝ} (hε : ε < 0) :
    ρ.smoothMaxEntropy ε = ⊤ :=
  -- Nonnegative distance cannot satisfy a negative error budget.
  iInf₂_eq_top.mpr fun τ hτ => False.elim (not_le_of_gt hε ((ρ.D_nonneg τ).trans hτ))

/-- At radius at least one the ball contains the zero substate, giving `⊥`. -/
theorem smoothMaxEntropy_eq_bot_of_one_le (ρ : SubState ι 𝕜) {ε : ℝ} (hε : 1 ≤ ε) :
    ρ.smoothMaxEntropy ε = ⊥ := by
  let τ : SubState ι 𝕜 := ⟨0, Matrix.PosSemidef.zero, by simp⟩
  exact le_bot_iff.mp
    ((ρ.smoothMaxEntropy_le_of_mem ((ρ.D_le_one τ).trans hε)).trans_eq maxEntropy_zero)

end SubState

section Conditional

variable {A B : Type*} [Fintype B] [DecidableEq A]

/-- A conditional min-entropy lower bound in nats is feasible when some normalized state
`σ_B` satisfies `ρ_AB ≤ exp(-r) (id_A ⊗ σ_B)` in positive-semidefinite order. -/
def MinEntropyFeasible (ρ : Matrix (A × B) (A × B) 𝕜) (r : ℝ) : Prop :=
  ∃ σ : MState B 𝕜,
    (((Real.exp (-r) : ℝ) : 𝕜) • ((1 : Matrix A A 𝕜) ⊗ₖ σ.M) - ρ).PosSemidef

/-- Conditional min-entropy in nats, following the normalized-state optimization in
Eq. (16): the supremum of `r` with `ρ_AB ≤ exp(-r) (id_A ⊗ σ_B)` for some normalized `σ_B`.
The paper uses bits and `2^(-λ)`; the change of variable is `r = λ * log 2`.

The extended supremum records an unbounded feasible set as `⊤` and an empty one as `⊥`.
In particular, a zero-dimensional conditioning space has no normalized witness. -/
noncomputable def minEntropy (ρ : Matrix (A × B) (A × B) 𝕜) : EReal :=
  ⨆ (r : ℝ) (_ : MinEntropyFeasible ρ r), (r : EReal)

/-- Conditional min-entropy in bits, the logarithm-base convention of Eq. (16). -/
noncomputable def minEntropy₂ (ρ : Matrix (A × B) (A × B) 𝕜) : EReal :=
  minEntropy ρ / (Real.log 2 : EReal)

/-- A normalized conditioning state satisfying the domination inequality witnesses a
lower bound on conditional min-entropy. -/
theorem le_minEntropy_of_feasible {ρ : Matrix (A × B) (A × B) 𝕜} {r : ℝ}
    (hr : MinEntropyFeasible ρ r) : (r : EReal) ≤ minEntropy ρ :=
  le_iSup₂_of_le r hr le_rfl

/-- Dividing a supremum of real thresholds by a positive constant rescales the thresholds. -/
theorem iSup_coe_div_eq_iSup_coe_mul {c : ℝ} (hc : 0 < c) (P : ℝ → Prop) :
    (⨆ (r : ℝ) (_ : P r), (r : EReal)) / (c : EReal) = ⨆ (s : ℝ) (_ : P (s * c)), (s : EReal) := by
  -- Positive scaling respects order even at infinity. The adjunction below lets us
  -- move division through the supremum without assuming the entropy is finite.
  have hgc : GaloisConnection (fun a : EReal => a / (c : EReal))
      (fun a : EReal => (c : EReal) * a) := fun _ _ =>
      EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hc) (EReal.coe_ne_top c)
  -- Reindex the thresholds by r = s * c; multiplication by nonzero c is bijective.
  rw [hgc.l_iSup₂, ← (mulRight_bijective₀ c hc.ne').surjective.iSup_comp]
  simp only [← EReal.coe_div, mul_div_cancel_right₀ _ hc.ne']

/-- The bit-valued definition is the normalized-state formula in Eq. (16), with `2^(-r)`. -/
theorem minEntropy₂_eq_iSup (ρ : Matrix (A × B) (A × B) 𝕜) :
    minEntropy₂ ρ =
      ⨆ (r : ℝ) (_ : ∃ σ : MState B 𝕜,
        ((((2 : ℝ) ^ (-r) : ℝ) : 𝕜) • ((1 : Matrix A A 𝕜) ⊗ₖ σ.M) - ρ).PosSemidef),
        (r : EReal) := by
  -- A threshold of r bits is r * log 2 nats, with the same domination factor.
  simp only [Real.rpow_def_of_pos two_pos, mul_comm (Real.log 2), neg_mul]
  exact iSup_coe_div_eq_iSup_coe_mul (Real.log_pos one_lt_two) (MinEntropyFeasible ρ)

/-- The zero operator has unbounded conditional min-entropy when the conditioning
space is nonempty. This assumption supplies a normalized witness: an empty space has
none, and the paper's literal supremum over witnesses would instead be `⊥`. -/
@[simp] theorem minEntropy_zero [Finite A] [Nonempty B] :
    minEntropy (0 : Matrix (A × B) (A × B) 𝕜) = ⊤ := by
  classical
  -- Put unit mass on any one basis vector of the nonempty conditioning space.
  let M : Matrix B B 𝕜 := Matrix.diagonal (Pi.single (Classical.arbitrary B) 1)
  have htr : RCLike.re M.trace = 1 := by simp [M]
  let σ : MState B 𝕜 :=
    { M, psd := Matrix.PosSemidef.diagonal (Pi.single_nonneg.mpr zero_le_one),
      tr_le_one := htr.le, tr_eq_one := htr }
  refine (EReal.eq_top_iff_forall_lt _).mpr fun r => lt_of_lt_of_le
    (EReal.coe_lt_coe_iff.mpr (lt_add_one r)) (le_minEntropy_of_feasible (r := r + 1) ⟨σ, ?_⟩)
  -- Every finite entropy threshold is feasible for the zero operator.
  simpa only [sub_zero, RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
    (Matrix.PosSemidef.one.kronecker σ.psd).smul (Real.exp_pos (-(r + 1))).le

namespace SubState

variable [Fintype A] [DecidableEq B]

/-- Smooth conditional min-entropy is the supremum over the subnormalized purified ball,
in nats, as in Eq. (17). -/
noncomputable def smoothMinEntropy (ρ : SubState (A × B) 𝕜) (ε : ℝ) : EReal :=
  ⨆ (τ : SubState (A × B) 𝕜) (_ : τ ∈ ρ.ball ε), minEntropy τ.M

/-- Smooth conditional min-entropy in bits. -/
noncomputable def smoothMinEntropy₂ (ρ : SubState (A × B) 𝕜) (ε : ℝ) : EReal :=
  ρ.smoothMinEntropy ε / (Real.log 2 : EReal)

/-- Any approximating state bounds smooth min-entropy from below. -/
theorem minEntropy_le_smoothMinEntropy_of_mem (ρ : SubState (A × B) 𝕜)
    {τ : SubState (A × B) 𝕜} {ε : ℝ} (hτ : τ ∈ ρ.ball ε) :
    minEntropy τ.M ≤ ρ.smoothMinEntropy ε :=
  le_iSup₂_of_le τ hτ le_rfl

/-- Smoothing at nonnegative radius cannot decrease conditional min-entropy. -/
theorem minEntropy_le_smoothMinEntropy (ρ : SubState (A × B) 𝕜) {ε : ℝ} (hε : 0 ≤ ε) :
    minEntropy ρ.M ≤ ρ.smoothMinEntropy ε :=
  ρ.minEntropy_le_smoothMinEntropy_of_mem (ρ.self_mem_ball hε)

/-- Allowing more approximation error can only increase smooth conditional min-entropy. -/
theorem smoothMinEntropy_monotone (ρ : SubState (A × B) 𝕜) :
    Monotone ρ.smoothMinEntropy :=
  fun _ _ h => iSup_le_iSup_of_subset (ρ.ball_mono h)

/-- The bit-valued smooth conditional min-entropy is monotone in its radius. -/
theorem smoothMinEntropy₂_monotone (ρ : SubState (A × B) 𝕜) :
    Monotone ρ.smoothMinEntropy₂ :=
  fun _ _ hεδ => EReal.div_le_div_right_of_nonneg
    (EReal.coe_nonneg.mpr (Real.log_nonneg one_le_two)) (ρ.smoothMinEntropy_monotone hεδ)

/-- A negative smoothing radius gives the empty extended supremum, minus infinity. -/
theorem smoothMinEntropy_eq_bot_of_neg (ρ : SubState (A × B) 𝕜) {ε : ℝ} (hε : ε < 0) :
    ρ.smoothMinEntropy ε = ⊥ :=
  iSup₂_eq_bot.mpr fun τ hτ => False.elim (not_le_of_gt hε ((ρ.D_nonneg τ).trans hτ))

end SubState
end Conditional

namespace SubState

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {U X Y : Finset σ}

/-- Smooth max-mutual information in nats, `H_max^ε(X) - H_min^ε(X|Y)`, Eq. (18).
Disjointness is needed to identify the union with the tensor product of its regions. -/
noncomputable def smoothMaxMutualInfo (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) (ε : ℝ) : EReal :=
  (ρ.restrict hX).smoothMaxEntropy ε -
    ((ρ.restrict (Finset.union_subset hX hY)).submatrix (unionEquiv hd).symm).smoothMinEntropy ε

/-- Smooth max-mutual information in bits, derived from the natural-log quantity. -/
noncomputable def smoothMaxMutualInfo₂ (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) (ε : ℝ) : EReal :=
  ρ.smoothMaxMutualInfo hd hX hY ε / (Real.log 2 : EReal)

end SubState
end Arealaw
