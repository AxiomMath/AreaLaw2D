import Arealaw.Bridge.MState

/-!
# Purified distance

`D(ρ, σ) = √(1 - F̄(ρ, σ)²)` with `F̄(ρ, σ) = F(ρ, σ) + √((1 - tr ρ)(1 - tr σ))`, the purified
distance and generalized fidelity of Brandão–Horodecki (arXiv:1206.2947, Definition 10,
Eqs. (A1)–(A2)) on subnormalized states, through the failure flag `ρ̂ = ρ ⊕ (1 - tr ρ)` of
Tomamichel–Colbeck–Renner (arXiv:0907.5238, Lemma 3), on which `F̄` and `D₁` are the ordinary
fidelity and trace distance.

## Main definitions

* `SubState.hat`, `SubState.F`, `SubState.D`, `SubState.ball`: `ρ̂`, `F̄`, `D`, `B_ε`.

## Main statements

* `SubState.fidelity_hat`, `SubState.D₁_hat`: what the flag computes.
* `SubState.D_sq_le_two_mul_D₁`: the right half of BH12 Lemma 12, which Lemma 9 consumes.

## Notation

BH12's `D`, `D₁`, `F̄` are Tomamichel15's `P`, `Δ`, `√F∗` and TCR09's `P`, `D̄`, `F̄`; BH12's
letters are used.

## Implementation notes

`F_le_one`, `F_eq_one_iff` and `D_eq_zero_iff` are `ℂ`: Physlib's `MState` carries a
`HermitianMat d ℂ`, so its `fidelity_le_one` and `fidelity_eq_one_iff_self` have no `𝕜`.  The
rest is `RCLike`-generic.

Waiting on the channel layer: monotonicity under trace-nonincreasing maps (TCR09 Lemma 7),
which BH12 Eq. (47) uses and mislabels as monotonicity of the trace norm.  Absent, and built
on `Arealaw.uhlmann` when they land: the triangle inequality, the `D₁ ≤ D` half of Lemma 12,
BH12 Lemmas 11 and 13.  BH12 attributes Lemmas 11–13 to its ref. [63], which has no
generalized fidelity; the source is TCR09.
-/

namespace Arealaw

open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

/-! ## The one-dimensional failure flag -/

private theorem traceNorm_diagonal_unit (c : ℝ) :
    (Matrix.diagonal fun _ : Unit => ((c : ℝ) : 𝕜)).traceNorm = |c| := by
  rw [← Matrix.smul_one_eq_diagonal, Matrix.traceNorm_smul]
  simp

private theorem cfcSqrt_diagonal_unit {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (Matrix.diagonal fun _ : Unit => ((c : ℝ) : 𝕜)) =
      Matrix.diagonal fun _ : Unit => ((Real.sqrt c : ℝ) : 𝕜) :=
  cfcSqrt_diagonal (d := fun _ => c) fun _ => hc

namespace SubState

theorem posSemidef_flag (ρ : SubState ι 𝕜) :
    (Matrix.diagonal fun _ : Unit => ((1 - RCLike.re ρ.M.trace : ℝ) : 𝕜)).PosSemidef :=
  Matrix.posSemidef_diagonal_iff.mpr fun _ => RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr ρ.tr_le_one)

/-- The **failure flag** `ρ̂ = ρ ⊕ (1 - tr ρ)` (TCR09 Lemma 3): the missing weight on one extra
dimension normalizes `ρ`. -/
noncomputable def hat (ρ : SubState ι 𝕜) : MState (ι ⊕ Unit) 𝕜 :=
  MState.mk' (posSemidef_fromBlocks_zero ρ.psd ρ.posSemidef_flag) (by simp [trace_fromBlocks])

@[simp] theorem hat_M (ρ : SubState ι 𝕜) :
    ρ.hat.M = Matrix.fromBlocks ρ.M 0 0
      (Matrix.diagonal fun _ : Unit => ((1 - RCLike.re ρ.M.trace : ℝ) : 𝕜)) := rfl

theorem hat_injective : Function.Injective (hat : SubState ι 𝕜 → MState (ι ⊕ Unit) 𝕜) :=
  fun _ _ h => SubState.ext (Matrix.fromBlocks_inj.mp (congrArg (·.M) h)).1

/-- Tomamichel15 Eq. (3.24): the extra dimension carries the trace defect. -/
@[simp] theorem D₁_hat (ρ σ : SubState ι 𝕜) : ρ.hat.toSubState.D₁ σ.hat.toSubState = ρ.D₁ σ := by
  rw [MState.D₁_eq_traceNorm_div_two, D₁_def, show ρ.hat.M - σ.hat.M = Matrix.fromBlocks
    (ρ.M - σ.M) 0 0 (Matrix.diagonal fun _ : Unit =>
      ((RCLike.re σ.M.trace - RCLike.re ρ.M.trace : ℝ) : 𝕜)) by
      ext (i | i) (j | j) <;> simp,
    traceNorm_fromBlocks_zero, traceNorm_diagonal_unit, abs_sub_comm]

/-! ## The generalized fidelity -/

variable [DecidableEq ι]

/-- **Generalized fidelity** `F̄ = F + √((1 - tr ρ)(1 - tr σ))` (BH12 Definition 10). -/
noncomputable def F (ρ σ : SubState ι 𝕜) : ℝ :=
  fidelity ρ.M σ.M + Real.sqrt ((1 - RCLike.re ρ.M.trace) * (1 - RCLike.re σ.M.trace))

theorem F_def (ρ σ : SubState ι 𝕜) : ρ.F σ = fidelity ρ.M σ.M +
    Real.sqrt ((1 - RCLike.re ρ.M.trace) * (1 - RCLike.re σ.M.trace)) := rfl

theorem F_nonneg (ρ σ : SubState ι 𝕜) : 0 ≤ ρ.F σ :=
  add_nonneg (fidelity_nonneg _ _) (Real.sqrt_nonneg _)

-- Not `@[simp]`: it loops.
theorem F_comm (ρ σ : SubState ι 𝕜) : ρ.F σ = σ.F ρ := by
  rw [F_def, F_def, fidelity_comm, mul_comm]

@[simp] theorem F_self (ρ : SubState ι 𝕜) : ρ.F ρ = 1 := by
  simp [F_def, fidelity_self ρ.psd, ρ.tr_le_one]

/-- TCR09 Lemma 3: `F̄` is the fidelity of the flagged states. -/
theorem fidelity_hat (ρ σ : SubState ι 𝕜) : fidelity ρ.hat.M σ.hat.M = ρ.F σ := by
  have ha := sub_nonneg.mpr ρ.tr_le_one
  rw [fidelity_def, hat_M, hat_M, cfcSqrt_fromBlocks_zero ρ.psd ρ.posSemidef_flag,
    cfcSqrt_fromBlocks_zero σ.psd σ.posSemidef_flag, Matrix.fromBlocks_multiply,
    cfcSqrt_diagonal_unit ha, cfcSqrt_diagonal_unit (sub_nonneg.mpr σ.tr_le_one)]
  simp [traceNorm_fromBlocks_zero, ← fidelity_def, F_def, ← RCLike.ofReal_mul,
    traceNorm_diagonal_unit, ← Real.sqrt_mul ha]

/-! ## The purified distance -/

/-- **Purified distance** `D = √(1 - F̄²)` (BH12 Eq. (A1)). -/
noncomputable def D (ρ σ : SubState ι 𝕜) : ℝ := Real.sqrt (1 - ρ.F σ ^ 2)

theorem D_def (ρ σ : SubState ι 𝕜) : ρ.D σ = Real.sqrt (1 - ρ.F σ ^ 2) := rfl

theorem D_nonneg (ρ σ : SubState ι 𝕜) : 0 ≤ ρ.D σ := Real.sqrt_nonneg _

-- Not `@[simp]`: it loops.
theorem D_comm (ρ σ : SubState ι 𝕜) : ρ.D σ = σ.D ρ := by rw [D_def, D_def, F_comm]

@[simp] theorem D_self (ρ : SubState ι 𝕜) : ρ.D ρ = 0 := by simp [D_def]

theorem D_le_one (ρ σ : SubState ι 𝕜) : ρ.D σ ≤ 1 :=
  Real.sqrt_le_one.mpr (sub_le_self _ (sq_nonneg _))

/-- The ε-**ball** (BH12 Eq. (A2)).  No guard on `ε`, as in BH12; consumers carry theirs. -/
def ball (ρ : SubState ι 𝕜) (ε : ℝ) : Set (SubState ι 𝕜) := {σ | ρ.D σ ≤ ε}

@[simp] theorem mem_ball {ρ σ : SubState ι 𝕜} {ε : ℝ} : σ ∈ ρ.ball ε ↔ ρ.D σ ≤ ε := Iff.rfl

theorem self_mem_ball (ρ : SubState ι 𝕜) {ε : ℝ} (hε : 0 ≤ ε) : ρ ∈ ρ.ball ε := by simp [hε]

/-! ## Fuchs–van de Graaf, the half BH12 Lemma 12 needs -/

private theorem min_le_sqrt_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : min x y ≤ Real.sqrt (x * y) :=
  Real.le_sqrt_of_sq_le (by nlinarith [min_le_left x y, min_le_right x y, le_min hx hy])

/-- **Fuchs–van de Graaf**, lower bound (Tomamichel15 Eq. (3.56)); Renner05 Lemma A.2.6 is
its input. -/
theorem one_sub_F_le_D₁ (ρ σ : SubState ι 𝕜) : 1 - ρ.F σ ≤ ρ.D₁ σ := by
  grind [F_def, D₁_def, trace_add_trace_sub_two_mul_fidelity_le_traceNorm_sub ρ.psd σ.psd,
    min_le_sqrt_mul (sub_nonneg.mpr ρ.tr_le_one) (sub_nonneg.mpr σ.tr_le_one)]

/-- **BH12 Lemma 12**, right half.  `1 - F̄² ≤ 2(1 - F̄)` is `0 ≤ (1 - F̄)²`, so `F̄ ≤ 1` is
not needed. -/
theorem D_le_sqrt_two_mul_D₁ (ρ σ : SubState ι 𝕜) : ρ.D σ ≤ Real.sqrt (2 * ρ.D₁ σ) :=
  Real.sqrt_le_sqrt (by linarith [one_sub_F_le_D₁ ρ σ, sq_nonneg (1 - ρ.F σ)])

/-- The form BH12 Eq. (83) uses. -/
theorem D_sq_le_two_mul_D₁ (ρ σ : SubState ι 𝕜) : ρ.D σ ^ 2 ≤ 2 * ρ.D₁ σ :=
  (Real.le_sqrt (ρ.D_nonneg σ) (mul_nonneg zero_le_two (ρ.D₁_nonneg σ))).mp
    (D_le_sqrt_two_mul_D₁ ρ σ)

/-! ## The complex layer -/

theorem F_le_one (ρ σ : SubState ι ℂ) : ρ.F σ ≤ 1 :=
  fidelity_hat ρ σ ▸ MState.fidelity_physlibEquiv ρ.hat σ.hat ▸ _root_.MState.fidelity_le_one _ _

theorem F_eq_one_iff {ρ σ : SubState ι ℂ} : ρ.F σ = 1 ↔ ρ = σ := by
  rw [← fidelity_hat, ← MState.fidelity_physlibEquiv, _root_.MState.fidelity_eq_one_iff_self,
    MState.physlibEquiv.injective.eq_iff, hat_injective.eq_iff]

theorem D_eq_zero_iff {ρ σ : SubState ι ℂ} : ρ.D σ = 0 ↔ ρ = σ := by
  rw [D_def, Real.sqrt_eq_zero', sub_nonpos, one_le_sq_iff₀ (ρ.F_nonneg σ),
    (ρ.F_le_one σ).ge_iff_eq, ← F_eq_one_iff]

end SubState

/-! ## Normalized states -/

variable [DecidableEq ι]

-- Not `@[simp]`: it abandons the `.toSubState` spelling callers hold.
theorem MState.F_eq_fidelity (ρ σ : Arealaw.MState ι 𝕜) :
    ρ.toSubState.F σ.toSubState = fidelity ρ.M σ.M := by
  simp [SubState.F_def, ρ.tr_eq_one]

-- Not `@[simp]`: it abandons the `.toSubState` spelling callers hold.
theorem MState.D_eq (ρ σ : Arealaw.MState ι 𝕜) :
    ρ.toSubState.D σ.toSubState = Real.sqrt (1 - fidelity ρ.M σ.M ^ 2) := by
  rw [SubState.D_def, MState.F_eq_fidelity]

end Arealaw
