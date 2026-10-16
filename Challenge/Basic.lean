import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.HausdorffDistance
import QuantumInfo.ClassicalInfo.Entropy
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.HermitianMat.Proj
import QuantumInfo.ForMathlib.Matrix
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-! # The formal challenge file

The area law for gapped ground states of local Hamiltonians on finite domains of `ℤ²`, from
OpenAI, *A two-dimensional area law from a global spectral gap* (2026), Theorem 1.1.

-/

namespace Arealaw

/-! ## Regions, the partial trace and states -/

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}

/-- The index of the region `S`: a basis label of the local space at every site of `S`. -/
abbrev Reg (loc : σ → Type*) (S : Finset σ) := ∀ i : S, loc i

variable {S T U : Finset σ}

/-- The restriction of a configuration on `T` to `S ⊆ T`. -/
def restr (h : S ⊆ T) (z : Reg loc T) : Reg loc S := Finset.restrict₂ h z

/-- A configuration on `S` glued to one on `T \ S`, giving one on `T`. -/
def glue (x : Reg loc S) (z : Reg loc (T \ S)) : Reg loc T :=
  fun j => if hj : (j : σ) ∈ S then x ⟨j, hj⟩ else z ⟨j, Finset.mem_sdiff.2 ⟨j.2, hj⟩⟩

end Region

section PTrace

open scoped ComplexOrder Matrix.Norms.L2Operator
open Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] {𝕜 : Type*} [RCLike 𝕜] {S T U : Finset σ}

/-- The partial trace from the region `T` to `S ⊆ T`, summing over configurations of
`T \ S`. -/
noncomputable def ptrace (_h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    Matrix (Reg loc S) (Reg loc S) 𝕜 :=
  Matrix.of fun x y => ∑ z : Reg loc (T \ S), M (glue x z) (glue y z)

/-- The partial trace of a positive semidefinite matrix is positive semidefinite. -/
theorem posSemidef_ptrace (h : S ⊆ T) {M : Matrix (Reg loc T) (Reg loc T) 𝕜} (hM : M.PosSemidef) :
    (ptrace h M).PosSemidef :=
  sorry

/-- The partial trace preserves the trace. -/
theorem trace_ptrace (h : S ⊆ T) (M : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    (ptrace h M).trace = M.trace :=
  sorry

section DecEqLoc
variable [∀ i, DecidableEq (loc i)]

/-- A matrix on `S ⊆ T` extended to `T` by the identity on `T \ S`. -/
noncomputable def extendId (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    Matrix (Reg loc T) (Reg loc T) 𝕜 :=
  Matrix.of fun w w' =>
    if restr (S := T \ S) (T := T) Finset.sdiff_subset w
        = restr (S := T \ S) (T := T) Finset.sdiff_subset w'
    then A (restr h w) (restr h w') else 0

end DecEqLoc

end PTrace

section VonNeumann

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `-tr(ρ log ρ)` of a Hermitian matrix, in nats. -/
noncomputable def vonNeumann {ρ : Matrix n n 𝕜} (hρ : ρ.IsHermitian) : ℝ :=
  RCLike.re (-(hρ.cfc (fun x => x * Real.log x)).trace)

end VonNeumann

section Mixed

open scoped ComplexOrder
open Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {S T U : Finset σ}

/-- A subnormalized state: positive semidefinite with real trace at most one. -/
@[ext] structure SubState (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜] where
  /-- the (sub)density matrix -/
  M : Matrix ι ι 𝕜
  /-- positive semidefiniteness -/
  psd : M.PosSemidef
  /-- subnormalization: real trace at most one -/
  tr_le_one : RCLike.re M.trace ≤ 1

/-- A state: a subnormalized state of unit trace. -/
structure MState (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜] extends SubState ι 𝕜 where
  /-- normalization: unit trace -/
  tr_eq_one : RCLike.re M.trace = 1

namespace SubState

/-- The restriction of a state on `T` to `S ⊆ T`, by the partial trace. -/
noncomputable def restrict (h : S ⊆ T) (ρ : SubState (Reg loc T) 𝕜) : SubState (Reg loc S) 𝕜 where
  M := ptrace h ρ.M
  psd := posSemidef_ptrace h ρ.psd
  tr_le_one := trace_ptrace h ρ.M ▸ ρ.tr_le_one

/-- The von Neumann entropy of a state, in nats. -/
noncomputable def entropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : SubState ι 𝕜) : ℝ :=
  vonNeumann ρ.psd.isHermitian

end SubState

namespace MState

/-- The state with density matrix `M`, given positivity and unit trace. -/
@[simps] def mk' {ι : Type*} [Fintype ι] {M : Matrix ι ι 𝕜} (psd : M.PosSemidef)
    (tr_eq_one : RCLike.re M.trace = 1) : MState ι 𝕜 where
  M := M
  psd := psd
  tr_le_one := tr_eq_one.le
  tr_eq_one := tr_eq_one

end MState

variable {X Y : Finset σ} [∀ i, DecidableEq (loc i)]

namespace SubState

/-- The entropy `S_ρ(X)` of the region `X ⊆ U` of a state `ρ` on `U`. -/
noncomputable def regionEntropy (ρ : SubState (Reg loc U) 𝕜) (h : X ⊆ U) : ℝ :=
  (ρ.restrict h).entropy

end SubState

end Mixed

end Arealaw

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Pointwise
open Matrix SimpleGraph

/-! ## The square lattice, Hamiltonians and ground states -/

/-- Adjacency in the square lattice `ℤ²` is decidable. -/
instance instDecidableRelAdjSquareLattice : DecidableRel (hasse ℤ □ hasse ℤ).Adj :=
  fun x y => decidable_of_iff ((x.1 + 1 = y.1 ∨ y.1 + 1 = x.1) ∧ x.2 = y.2 ∨
      (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2) ∧ x.1 = y.1)
    (by simp only [boxProd_adj, hasse_adj, Order.covBy_iff_add_one_eq])

/-- The graph distance `d_Λ` of the square lattice induced on `Λ`: `⊤` between components
of `Λ`, and when either point lies outside `Λ`. -/
noncomputable def domainEDist (Λ : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) : ℕ∞ :=
  if h : x ∈ Λ ∧ y ∈ Λ then
    ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist ⟨x, h.1⟩ ⟨y, h.2⟩
  else ⊤

/-- The diameter of `X` in the distance `d_Λ`. -/
noncomputable def domainEDiam (Λ X : Finset (ℤ × ℤ)) : ℕ∞ :=
  ⨆ x ∈ X, ⨆ y ∈ X, domainEDist Λ x y

/-- The edge boundary `∂_Λ A`: lattice edges `(x, y)` with `x ∈ A` and `y ∈ Λ \ A`, each
counted once. -/
noncomputable def edgeBoundary (Λ A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (hasse ℤ □ hasse ℤ).interedges A (Λ \ A)

/-- Every site of `ℤ²` carries a qudit `ℂ^q`, with basis `Fin q`. -/
abbrev Qudits (q : ℕ) : ℤ × ℤ → Type := fun _ => Fin q

/-- The admissible supports: nonempty `X ⊆ Λ` of `d_Λ`-diameter at most `R`. -/
noncomputable def supports (Λ : Finset (ℤ × ℤ)) (R : ℕ) : Finset (Finset (ℤ × ℤ)) :=
  Λ.powerset.filter fun X => X.Nonempty ∧ domainEDiam Λ X ≤ R

variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}

/-- The Hamiltonian `H = ∑_{X ⊆ Λ} Φ X`, each term acting on `X` and as the identity on
`Λ \ X`. -/
noncomputable def hamiltonian (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) :
    Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜 :=
  ∑ X ∈ Λ.powerset.attach, extendId (Finset.mem_powerset.1 X.2) (Φ X.1)

/-- An interaction of range `R` and strength `J`: every term is Hermitian of operator norm
at most `J`, and vanishes off the admissible supports. -/
def IsAdmissible (Λ : Finset (ℤ × ℤ)) (R : ℕ) (J : ℝ)
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) : Prop :=
  ∀ X ⊆ Λ, (Φ X).IsHermitian ∧ ‖Φ X‖ ≤ J ∧ (X ∉ supports Λ R → Φ X = 0)

/-- The spectral gap `H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)`, in the Loewner order. -/
def HasGlobalGap {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι 𝕜) (Ω : ι → 𝕜)
    (E₀ Δ : ℝ) : Prop :=
  (Δ : 𝕜) • (1 - vecMulVec Ω (star Ω)) ≤ H - (E₀ : 𝕜) • 1

/-- The pure state `|Ω⟩⟨Ω|` of a unit vector `Ω`. -/
noncomputable def pureState {ι : Type*} [Fintype ι] (Ω : ι → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) :
    MState ι 𝕜 :=
  MState.mk' (posSemidef_vecMulVec_self_star Ω)
    (by rw [trace_vecMulVec, dotProduct_comm, hΩ, RCLike.one_re])

/-- The area law at fixed `q`, `R`, `J`, `Δ`: one constant `C` with `S_Ω(A) ≤ C |∂_Λ A|`
for every finite `Λ ⊂ ℤ²`, every admissible `H` with a unit eigenvector `Ω` of eigenvalue
`E₀` and gap `Δ`, and every `A ⊆ Λ`. -/
def AreaLaw (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hA ≤ C * (edgeBoundary Λ A).card

end OpenAI

namespace OpenAI.Challenge

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **`area_law` — Theorem 1.1, the area law.** For `q ≥ 1`, `J > 0` and `Δ > 0`, the
ground-state entanglement entropy of a cut is at most a constant times its edge boundary. -/
theorem area_law (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    AreaLaw 𝕜 q R J Δ :=
  sorry

end OpenAI.Challenge
