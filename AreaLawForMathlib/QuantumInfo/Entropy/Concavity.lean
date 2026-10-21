import AreaLawForMathlib.QuantumInfo.Entropy.ClassicalQuantum
import AreaLawForMathlib.QuantumInfo.Region.Physlib
import AreaLawForMathlib.QuantumInfo.Region.PartialTrace

/-!
# Concavity of the von Neumann entropy for `Arealaw.MState`

Extends `AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean`: the concavity
`∑ᵢ pᵢ S(τᵢ) ≤ S(∑ᵢ pᵢ τᵢ)` of `Arealaw.SubState.entropy`, transported from
`MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight` through `Arealaw.MState.physlibEquiv`.
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

end Arealaw

