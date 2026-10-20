import AreaLawForMathlib.QuantumInfo.Entropy.ClassicalQuantum
import Arealaw.Bridge.VonNeumann
import Arealaw.PTrace

/-!
# Concavity of the von Neumann entropy for `Arealaw.MState`

Extends `AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean`: the concavity
`∑ᵢ pᵢ S(τᵢ) ≤ S(∑ᵢ pᵢ τᵢ)` of `Arealaw.SubState.entropy`, transported from
`MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight` through `Arealaw.MState.physlibEquiv`, and its region
version for `regionEntropy`.
-/

open scoped ComplexOrder MatrixOrder

namespace Arealaw

namespace MState

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

omit [DecidableEq ι] in
/-- **Concavity of the von Neumann entropy**: if `ρ = ∑ᵢ pᵢ τᵢ` is a convex combination, then
`∑ᵢ pᵢ S(τᵢ) ≤ S(ρ)`. -/
theorem sum_mul_entropy_le_entropy {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (τ : ι → Arealaw.MState d ℂ) (ρ : Arealaw.MState d ℂ)
    (hρ : ρ.M = ∑ i, (p i : ℂ) • (τ i).M) :
    ∑ i, p i * (τ i).entropy ≤ ρ.entropy := by
  classical
  let P : ProbDistribution ι := ProbDistribution.mk' p hp hp1
  have h := MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight P (fun i => physlibEquiv (τ i))
  have hP : ∀ i, (P i : ℝ) = p i := fun i => rfl
  have hT : (MState.cq P fun i => physlibEquiv (τ i)).traceRight = physlibEquiv ρ := by
    refine _root_.MState.ext_m ?_
    rw [MState.cq_traceRight, physlibEquiv_m, hρ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP, physlibEquiv_m, Complex.coe_smul]
  rw [hT, MState.Sᵥₙ_physlibEquiv] at h
  simpa [hP, MState.Sᵥₙ_physlibEquiv] using h

end MState

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U T : Finset σ} {ι : Type*} [Fintype ι]

/-- **Concavity of the region entropy**: for a convex combination `ρ = ∑ᵢ pᵢ τᵢ` of states on `U`
and a subregion `T ⊆ U`, `∑ᵢ pᵢ S(τᵢ|_T) ≤ S(ρ|_T)`. -/
theorem sum_mul_regionEntropy_le_regionEntropy {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (τ : ι → Arealaw.MState (Reg loc U) ℂ)
    (ρ : Arealaw.MState (Reg loc U) ℂ) (hρ : ρ.M = ∑ i, (p i : ℂ) • (τ i).M) (h : T ⊆ U) :
    ∑ i, p i * (τ i).toSubState.regionEntropy h ≤ ρ.toSubState.regionEntropy h := by
  classical
  simp only [SubState.regionEntropy_def]
  exact MState.sum_mul_entropy_le_entropy hp hp1 (fun i => (τ i).restrict h) (ρ.restrict h)
    (by simp [hρ, ptrace_sum, ptrace_smul])

end Region

end Arealaw

