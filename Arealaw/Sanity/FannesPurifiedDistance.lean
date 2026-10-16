import Arealaw.Bell
import Arealaw.PurifiedDist
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The paper's Fannes-type inequality is false as printed

Brandão–Horodecki (arXiv:1206.2947; Comm. Math. Phys. **333** (2015) 761) fix `D` globally as
the **purified distance**, then state a Fannes-type inequality
`|H(ρ) - H(σ)| ≤ log (d-1) · D + h D`, citing Audenaert (*J. Phys. A* **40** (2007) 8127),
whose inequality is for the **trace distance** `D₁`.  Substituting one for the other is what
breaks it: `printed_fails` refutes the printed form at `d = 2`, `ρ = |0⟩⟨0|`, `σ = I/2`.

The paper's own Purified Distance Versus Trace Norm lemma gives
`D₁ ≤ D`, and `h` increases on `[0, 1/2]`, so below the midpoint the substitution only weakens
the bound: that is `substitution_safe`, and `repaired_of_audenaert` assembles it into the
printed statement for `D ≤ 1/2`.  The failure is confined to `D > 1/2`.  The lemma is invoked
exactly once, on an `ε`-ball element with `D ≤ ε` small, inside the valid regime.  This file
records an erratum, not a gap in the result; no published erratum exists.

`repaired_of_audenaert` carries its two external inputs as hypotheses, neither being available
in Mathlib or in the pinned Physlib: Audenaert's inequality for `D₁`, and `D₁ ≤ D`.

## Implementation notes

The lemma is in bits, `SubState.entropy` and `Real.binEntropy` are in nats; each is divided by
`Real.log 2`, through `entropy₂` and `h₂` respectively.  Both states are diagonal, which keeps
this a concrete `2 × 2` computation.

Statement numbers in that paper are unstable between versions, so the statement is identified
by its `\label{fanaudineq}` and its attribution rather than by a number.
-/

namespace Arealaw

namespace FannesAudenaert

open Matrix
open scoped ComplexOrder MatrixOrder

/-- The spectrum of `|0⟩⟨0|`. -/
def pureSpec : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- The spectrum of the maximally mixed qubit `I/2`. -/
noncomputable def mixedSpec : Fin 2 → ℝ := fun _ => 1 / 2

/-- The pure state `|0⟩⟨0|`, as the diagonal matrix `diagonal (1, 0)`. -/
noncomputable def pureZero : MState (Fin 2) ℂ :=
  MState.mk' (M := diagonal (RCLike.ofReal ∘ pureSpec))
    (Matrix.PosSemidef.diagonal fun i => by fin_cases i <;> simp [pureSpec]) (by simp [pureSpec])

/-- The maximally mixed qubit `I/2`. -/
noncomputable def maxMixed : MState (Fin 2) ℂ :=
  MState.mk' (M := diagonal (RCLike.ofReal ∘ mixedSpec))
    (Matrix.PosSemidef.diagonal fun i => by simp [mixedSpec]) (by simp [mixedSpec])

/-! ## Entropies

The pair has entropies `0` and `1` bit, so the left side of Lemma 17 is `1`. -/

/-- The pure state carries no entropy. -/
theorem entropy_pureZero : pureZero.entropy = 0 := by
  rw [SubState.entropy_eq_H]
  refine (H_eq_of_multiset_eq (eigenvalues_diagonal_multiset pureSpec)).trans ?_
  simp [H, pureSpec, Real.negMulLog]

/-- The maximally mixed qubit carries `log 2` nats, one bit. -/
theorem entropy_maxMixed : maxMixed.entropy = Real.log 2 := by
  rw [SubState.entropy_eq_H]
  exact (H_eq_of_multiset_eq (eigenvalues_diagonal_multiset mixedSpec)).trans H_half

/-- The pure state carries no entropy, in bits. -/
theorem entropy₂_pureZero : pureZero.entropy₂ = 0 := by
  rw [SubState.entropy₂, entropy_pureZero, zero_div]

/-- The maximally mixed qubit carries exactly one bit. -/
theorem entropy₂_maxMixed : maxMixed.entropy₂ = 1 := by
  rw [SubState.entropy₂, entropy_maxMixed, div_self (Real.log_pos one_lt_two).ne']

/-- The left side of Lemma 17 for this pair is one bit. -/
theorem abs_sub_entropy₂ : |pureZero.entropy₂ - maxMixed.entropy₂| = 1 := by
  simp [entropy₂_pureZero, entropy₂_maxMixed]

/-! ## The purified distance of this pair -/

/-- **Uhlmann fidelity of the pair**: `F = √2/2`, so `F² = 1/2`.  The pure state is its own
square root, conjugating `σ` by it leaves `diagonal (1/2, 0)`, and that matrix's square root
has trace `√(1/2)`. -/
theorem fidelity_eq : fidelity pureZero.M maxMixed.M = Real.sqrt 2 / 2 := by
  change fidelity (diagonal (RCLike.ofReal ∘ pureSpec)) (diagonal (RCLike.ofReal ∘ mixedSpec)) = _
  rw [fidelity_def, cfcSqrt_diagonal (by simp [pureSpec, Pi.le_def, Fin.forall_fin_two]),
    cfcSqrt_diagonal (by simp [mixedSpec, Pi.le_def]), diagonal_mul_diagonal]
  apply RCLike.ofReal_injective (K := ℂ)
  simp [PosSemidef.traceNorm_eq_trace, Fin.sum_univ_two, pureSpec, mixedSpec, Real.sqrt_div_self]

/-- **Purified distance of the pair**: `P = √2/2`, since `F² = 1/2`. -/
theorem purifiedDist_eq : pureZero.toSubState.D maxMixed.toSubState = Real.sqrt 2 / 2 := by
  norm_num [MState.D_eq, fidelity_eq, Real.sqrt_div_self]

/-! ## The binary entropy in bits, and the refutation -/

/-- The binary entropy in bits, `h p = -p log₂ p - (1-p) log₂ (1-p)`. -/
noncomputable def h₂ (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- **Sub-bit off the midpoint**: `h p < 1` for every `p ≠ 1/2`. -/
theorem h₂_lt_one {p : ℝ} (hp : p ≠ 2⁻¹) : h₂ p < 1 :=
  (div_lt_one (Real.log_pos one_lt_two)).2 (Real.binEntropy_lt_log_two.2 hp)

/-- The purified distance of this pair is not `1/2`, since `√2 ≠ 1`. -/
theorem purifiedDist_ne : pureZero.toSubState.D maxMixed.toSubState ≠ 2⁻¹ := by
  norm_num [purifiedDist_eq]

/-- **Lemma 17 of arXiv:1206.2947 is false as printed**: for `ρ = |0⟩⟨0|` and `σ = I/2` on a
qubit, its right-hand side `P · log₂ (d-1) + h (P)` is strictly below its left-hand side
`|S(ρ) - S(σ)| = 1` bit. -/
theorem printed_fails :
    pureZero.toSubState.D maxMixed.toSubState * Real.logb 2 ((Fintype.card (Fin 2) : ℝ) - 1) +
      h₂ (pureZero.toSubState.D maxMixed.toSubState) < |pureZero.entropy₂ - maxMixed.entropy₂| := by
  norm_num [abs_sub_entropy₂, h₂_lt_one purifiedDist_ne]

/-! ## The repaired statement

Why the defect is confined to `D > 1/2`, and what the printed form becomes below it. -/

/-- **The substitution is safe left of the midpoint**: for `0 ≤ a ≤ b ≤ 1/2` and `0 ≤ c`,
`c · a + h a ≤ c · b + h b`. -/
theorem substitution_safe {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hc : 0 ≤ c) :
    c * a + h₂ a ≤ c * b + h₂ b := by
  rw [one_div] at hb
  unfold h₂
  gcongr
  exact Real.binEntropy_strictMonoOn.monotoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

/-- **The repaired inequality**: the printed form does hold once `D ≤ 1/2`, given Audenaert's
inequality for the trace distance `t` and the paper's `t ≤ D`.

`audenaert` is Audenaert's sharp Fannes inequality and `hle` is the paper's Purified Distance
Versus Trace Norm lemma; neither is in Mathlib or the pinned Physlib. -/
theorem repaired_of_audenaert {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]
    (ρ σ : MState ι 𝕜) (t : ℝ) (hcard : 2 ≤ Fintype.card ι) (ht : 0 ≤ t)
    (audenaert : |ρ.entropy₂ - σ.entropy₂| ≤ Real.logb 2 ((Fintype.card ι : ℝ) - 1) * t + h₂ t)
    (hle : t ≤ ρ.toSubState.D σ.toSubState) (hhalf : ρ.toSubState.D σ.toSubState ≤ 1 / 2) :
    |ρ.entropy₂ - σ.entropy₂| ≤ Real.logb 2 ((Fintype.card ι : ℝ) - 1) * ρ.toSubState.D σ.toSubState
      + h₂ (ρ.toSubState.D σ.toSubState) :=
  audenaert.trans <| substitution_safe ht hle hhalf <|
    Real.logb_nonneg one_lt_two <| le_sub_iff_add_le.2 <| by norm_cast

end FannesAudenaert

end Arealaw
