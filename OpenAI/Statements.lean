import AreaLawForMathlib.QuantumInfo.Region.State
import AreaLawForMathlib.QuantumInfo.Region.TraceDistance
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Statements of the two-dimensional area law from a global spectral gap

The statement layer for OpenAI, *A two-dimensional area law from a global spectral gap*
(24 September 2026, github.com/openai/math, `preprints/`, unrefereed), cited below as
[OAI265] by section and equation number.

Every definition is total and free of `sorry`.  Each result of the paper is a `def … : Prop`
carrying no `sorry`, asserted by a `theorem` in the file that proves it.  The only proved
declarations here are a decidability instance and two subset facts the statements need.

## Main definitions

* `domainEDist`, `domainEDiam`: the induced-graph distance `d_Λ` and diameter, in `ℕ∞`.
* `IsAdmissible`, `hamiltonian`: the Hamiltonian class of eq. (1.1).
* `HasGlobalGap`: the Loewner-form gap `H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)` of Theorem 1.1.
* `edgeBoundary`, `innerBoundary`, `cutEndpoints`: `∂_Λ A`, `∂_in A` and `Z_A` of §1.1.
* `condExpect`: the conditional expectation `E_{i,l}` of eq. (4.1).
* `IsTemplate`, `IsSeparatedFromCut`: Definition 9.3.
* `IsIntRect`, `boxSize`, `IsSafe`: integer rectangles, their size and safety (§3.2).

## Main statements

* `AreaLaw`: Theorem 1.1, proved as `area_law` in `OpenAI.AreaLaw`.
* `AreaLawCorollary`: Corollary 1.2, proved from `area_law` as `area_law_corollary` in
  `OpenAI.AreaLaw`.
* `PositiveReplacement`, `positive_replacement`: Proposition 4.3.
* `CollarBound`: Proposition 9.6, proved as `collar_bound` in `OpenAI.CollarBound`.
* `Amplification`: Proposition 10.2, proved as `amplification` in `OpenAI.Amplification`.
* `TwoFamilyCancellation`: Lemma 11.1, proved as `two_family_cancellation` in
  `OpenAI.TwoFamily`.
* `TwoFamilyDecomposition`: Proposition 11.2, proved as `two_family_decomposition` in
  `OpenAI.TwoFamilyDecomposition`.
* `ConditionalContinuity`, `MarginalTails`, `BufferDiscount`, `InitialBoxEstimate`: Lemma 2.1,
  Lemma 3.1, Lemma 3.2 and Proposition 3.3.  These carry no theorem here; each is asserted in
  the file that proves it.

## Implementation notes

*Conventions.*  Entropies are in nats: `regionEntropy` is `Arealaw.vonNeumann`, whose
logarithm is `Real.log`, as in §1.1 ("All logarithms are natural").  The boundary measure of
Theorem 1.1 is the edge boundary; vertex forms appear only in Corollary 1.2.  The gap is the
Loewner inequality `Δ • (1 - |Ω⟩⟨Ω|) ≤ H - E₀ • 1` of Mathlib's `MatrixOrder`, the direction
of Theorem 1.1.  Sites carry `Fin q`, the basis of `ℂ^q`, so the site spaces live in `Type`;
the scalar field `𝕜` is any `RCLike` field, in any universe.  The paper works over `ℂ`.

*Distances.*  `d_Λ` is `SimpleGraph.edist` of the induced graph, valued in `ℕ∞` and `⊤`
between components (§1.1).  Mathlib's `SimpleGraph.dist` is `0` between components
(`SimpleGraph.dist_eq_zero_of_not_reachable`), so a diameter built on it would admit
disconnected supports; it is never used.  Ambient distances (`dist_∞` of §3.2 and
Definition 9.3) are the sup-norm `edist` of `ℤ × ℤ` and `ℝ × ℝ`, through `Metric.infEDist`
and `Metric.ediam`, with distance `⊤` to the empty set, as §3.2 requires; this is what makes
every box safe for the cut `A = Λ`.  `Metric.diam` is not used: it is `0` on unbounded sets.

*The square lattice.*  `ℤ²` is Mathlib's `hasse ℤ □ hasse ℤ`, whose adjacency is Euclidean
distance one.  Mathlib provides no decidability instance for `boxProd`, so the instance below
supplies one for this graph.

*Ground states.*  Theorem 1.1 assumes a unique normalized ground vector up to phase with
ground energy `E₀`.  The statements take `star Ω ⬝ᵥ Ω = 1`, `H *ᵥ Ω = E₀ • Ω` and the gap,
the hypotheses of Proposition 4.3 verbatim.  For `Δ > 0` these force `E₀` to be the ground
energy and its eigenspace to be the line of `Ω`, so uniqueness is not a separate hypothesis.
Normalization is the Euclidean `star Ω ⬝ᵥ Ω`, never `‖Ω‖`, which on `ι → 𝕜` is the sup norm.

*Hamiltonians.*  The interaction is a total family `Φ X` over every `X ⊆ ℤ²`, and
`hamiltonian` sums it over every `X ⊆ Λ`; `IsAdmissible` makes the terms off the admissible
supports vanish.  This is the paper's convention of one summand per support (§1.1).

*Owned here, not in `Arealaw/`.*  `pureState`, `condExpect` and `IsSupportedOn` are general
region-layer notions with no counterpart in Mathlib, Physlib or `Arealaw`; they live in this
file only because this phase does not touch the BH12 tree.
-/

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Pointwise
open Matrix SimpleGraph

/-! ## The square lattice and its finite induced domains -/

/-- Adjacency in the square lattice `hasse ℤ □ hasse ℤ` is decidable: one coordinate agrees and
the other changes by one. -/
instance instDecidableRelAdjSquareLattice : DecidableRel (hasse ℤ □ hasse ℤ).Adj :=
  fun x y => decidable_of_iff ((x.1 + 1 = y.1 ∨ y.1 + 1 = x.1) ∧ x.2 = y.2 ∨
      (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2) ∧ x.1 = y.1)
    (by simp only [boxProd_adj, hasse_adj, Order.covBy_iff_add_one_eq])

/-- The graph distance `d_Λ` of the square-lattice graph induced on a finite domain
`Λ ⊂ ℤ²` [OAI265, §1.1]: `⊤` between different components of `Λ`, and `⊤` when either point
lies outside `Λ`. -/
noncomputable def domainEDist (Λ : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) : ℕ∞ :=
  if h : x ∈ Λ ∧ y ∈ Λ then
    ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist ⟨x, h.1⟩ ⟨y, h.2⟩
  else ⊤

/-- The diameter `diam_{d_Λ} X` of a set of sites in the induced-graph distance
[OAI265, eq. (1.1)]. -/
noncomputable def domainEDiam (Λ X : Finset (ℤ × ℤ)) : ℕ∞ :=
  ⨆ x ∈ X, ⨆ y ∈ X, domainEDist Λ x y

/-- The graph neighbourhood `N_r(S) = {x ∈ Λ : d_Λ(x, S) ≤ r}` [OAI265, §2.2 and §10];
`N_r(∅) = ∅`. -/
noncomputable def graphNbhd (Λ S : Finset (ℤ × ℤ)) (r : ℕ) : Finset (ℤ × ℤ) :=
  Λ.filter fun x => (⨅ y ∈ S, domainEDist Λ x y) ≤ r

theorem graphNbhd_subset (Λ S : Finset (ℤ × ℤ)) (r : ℕ) : graphNbhd Λ S r ⊆ Λ :=
  Finset.filter_subset _ _

/-- The connected component of the site `a` in the induced graph on `Λ` [OAI265, §4.2]. -/
noncomputable def domainComponent (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Λ.filter fun x => domainEDist Λ a x ≠ ⊤

theorem domainComponent_subset (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : domainComponent Λ a ⊆ Λ :=
  Finset.filter_subset _ _

/-- The edge boundary `∂_Λ A` [OAI265, §1.1]: nearest-neighbour pairs `(x, y)` with `x ∈ A`
and `y ∈ Λ \ A`.  Each crossing edge `{x, y}` of the paper appears once, oriented out of `A`,
so the cardinality is the paper's `|∂_Λ A|`. -/
noncomputable def edgeBoundary (Λ A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (hasse ℤ □ hasse ℤ).interedges A (Λ \ A)

/-- The inner vertex boundary `∂_in A`: the sites of `A` on a crossing edge
[OAI265, §1.1]. -/
noncomputable def innerBoundary (Λ A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (edgeBoundary Λ A).image Prod.fst

/-- The crossing-edge endpoints `Z_A = ⋃_{e ∈ ∂_Λ A} e` [OAI265, §1.1]. -/
noncomputable def cutEndpoints (Λ A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (edgeBoundary Λ A).image Prod.fst ∪ (edgeBoundary Λ A).image Prod.snd

/-- The ambient sup-norm distance `dist_∞(T, Z)` between two finite sets of `ℤ²`
[OAI265, §3.2 and Definition 9.3]; `⊤` when either set is empty. -/
noncomputable def ambientEDist (T Z : Finset (ℤ × ℤ)) : ENNReal :=
  ⨅ x ∈ T, Metric.infEDist x (Z : Set (ℤ × ℤ))

/-- The ambient integer dilation `T_j = T + ([-j, j]² ∩ ℤ²)` [OAI265, §2.2]. -/
noncomputable def ambientDilation (T : Finset (ℤ × ℤ)) (j : ℕ) : Finset (ℤ × ℤ) :=
  T + Finset.Icc (-(j : ℤ), -(j : ℤ)) ((j : ℤ), (j : ℤ))

/-! ## Hamiltonians, ground states and the global gap -/

/-- The local family of the square lattice: every site carries `Fin q`, the basis of `ℂ^q`
[OAI265, §1.1]. -/
abbrev Qudits (q : ℕ) : ℤ × ℤ → Type := fun _ => Fin q

/-- The admissible supports of eq. (1.1): nonempty `X ⊆ Λ` with `diam_{d_Λ} X ≤ R`
[OAI265, eq. (1.1)]. -/
noncomputable def supports (Λ : Finset (ℤ × ℤ)) (R : ℕ) : Finset (Finset (ℤ × ℤ)) :=
  Λ.powerset.filter fun X => X.Nonempty ∧ domainEDiam Λ X ≤ R

variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}

/-- The Hamiltonian `H = ∑_X h_X` of [OAI265, eq. (1.1)]: each term acts on its support
`X ⊆ Λ` and as the identity elsewhere. -/
noncomputable def hamiltonian (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) :
    Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜 :=
  ∑ X ∈ Λ.powerset.attach, extendId (Finset.mem_powerset.1 X.2) (Φ X.1)

/-- An admissible interaction of range `R` and strength `J` [OAI265, eq. (1.1)]: every term
is Hermitian with operator norm at most `J`, and a term vanishes unless its support is
nonempty with `d_Λ`-diameter at most `R`. -/
def IsAdmissible (Λ : Finset (ℤ × ℤ)) (R : ℕ) (J : ℝ)
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜) : Prop :=
  ∀ X ⊆ Λ, (Φ X).IsHermitian ∧ ‖Φ X‖ ≤ J ∧ (X ∉ supports Λ R → Φ X = 0)

/-- The global gap of Theorem 1.1 in Loewner form, `H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)`
[OAI265, Theorem 1.1 (§1.1) and Proposition 4.3 (§4.2)]. -/
def HasGlobalGap {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι 𝕜) (Ω : ι → 𝕜)
    (E₀ Δ : ℝ) : Prop :=
  (Δ : 𝕜) • (1 - vecMulVec Ω (star Ω)) ≤ H - (E₀ : 𝕜) • 1

/-- The pure state `|Ω⟩⟨Ω|` of a unit vector.  The normalization is the field `MState`
needs. -/
noncomputable def pureState {ι : Type*} [Fintype ι] (Ω : ι → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) :
    MState ι 𝕜 :=
  MState.mk' (posSemidef_vecMulVec_self_star Ω)
    (by rw [trace_vecMulVec, dotProduct_comm, hΩ, RCLike.one_re])

/-! ## Theorem 1.1 and Corollary 1.2 -/

/-- **Theorem 1.1** [OAI265, §1.1, eq. (1.2)], for fixed `q`, `R`, `J` and `Δ`: one constant
`C` bounds `S_Ω(A) ≤ C |∂_Λ A|` for every finite domain `Λ ⊂ ℤ²`, every admissible
Hamiltonian (eq. (1.1)) with a normalized eigenvector `Ω` of eigenvalue `E₀` and global gap
`H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)`, and every `A ⊆ Λ`. -/
def AreaLaw (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hA ≤ C * (edgeBoundary Λ A).card

/-- The vertex-boundary forms of Corollary 1.2 [OAI265, §1.1]: one constant `C` with
`S_Ω(A) ≤ C |∂_Λ A|`, `S_Ω(A) ≤ 4C |∂_in A|` and `S_Ω(A) ≤ 2C |Z_A|` on every domain covered
by Theorem 1.1. -/
def VertexAreaLaw (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hA ≤ C * (edgeBoundary Λ A).card ∧
      (pureState Ω hΩ).regionEntropy hA ≤ 4 * C * (innerBoundary Λ A).card ∧
      (pureState Ω hΩ).regionEntropy hA ≤ 2 * C * (cutEndpoints Λ A).card

/-- **Corollary 1.2** [OAI265, §1.1]: the area law for on-site and nearest-neighbour
interactions, which is range `R = 1`, on every finite domain, hence on every subset of a
finite rectangle; and the vertex-boundary forms for every range `R`. -/
def AreaLawCorollary (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) (J Δ : ℝ) : Prop :=
  AreaLaw 𝕜 q 1 J Δ ∧ ∀ R : ℕ, VertexAreaLaw 𝕜 q R J Δ

/-! ## Proposition 4.3: positive replacement of the Hamiltonian -/

section RegionOps

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}

/-- The normalized conditional expectation onto a subregion `S ⊆ T` [OAI265, eq. (4.1)]:
the partial trace over `T \ S` divided by its dimension, extended by the identity. -/
noncomputable def condExpect (h : S ⊆ T) (B : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    Matrix (Reg loc T) (Reg loc T) 𝕜 :=
  (Fintype.card (Reg loc (T \ S)) : 𝕜)⁻¹ • extendId h (ptrace h B)

/-- An operator on `T` is supported in `S ⊆ T`: it acts as the identity on `T \ S`
[OAI265, §1.1]. -/
def IsSupportedOn (h : S ⊆ T) (B : Matrix (Reg loc T) (Reg loc T) 𝕜) : Prop :=
  ∃ B' : Matrix (Reg loc S) (Reg loc S) 𝕜, B = extendId h B'

end RegionOps

/-- **Proposition 4.3** [OAI265, §4.2, eqs. (4.8) and (4.9)], for a fixed integer `p ≥ 1`:
constants `c_*`, `C`, `c` independent of the domain such that, for every admissible `H` with
gapped ground vector `Ω` and every choice of anchors `a_X ∈ X`, there are operators `k_X`
indexed by the supports with `0 ≤ k_X ≤ 1`, `k_X Ω = 0`,
`H_F = ∑ k_X ≥ c_*⁻¹ (H - E₀) ≥ (Δ / c_*) (1 - |Ω⟩⟨Ω|)`, local approximants
`k_{X,l} = E_{X,l}(k_X) ∈ [0, 1]` with `‖k_X - k_{X,l}‖ ≤ C e^{-c l^α}`, `α = p / (p + 1)`,
and `k_X` supported in the component of `a_X`.  The constants depend only on `q`, `R`, `J`,
`Δ` and `p` (§4, preamble). -/
def PositiveReplacement (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) : Prop :=
  ∃ cstar : ℝ, 0 < cstar ∧ ∃ C c : ℝ, 0 < c ∧
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (_ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ anchor : Finset (ℤ × ℤ) → ℤ × ℤ, (∀ X ∈ supports Λ R, anchor X ∈ X) →
    ∃ k : Finset (ℤ × ℤ) → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜,
      (∀ X ∈ supports Λ R, 0 ≤ k X ∧ k X ≤ 1 ∧ k X *ᵥ Ω = 0) ∧
      (cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1) ≤ ∑ X ∈ supports Λ R, k X ∧
      ((Δ / cstar : ℝ) : 𝕜) • (1 - vecMulVec Ω (star Ω)) ≤
        (cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1) ∧
      (∀ X ∈ supports Λ R, ∀ l : ℕ,
        0 ≤ condExpect (graphNbhd_subset Λ {anchor X} l) (k X) ∧
        condExpect (graphNbhd_subset Λ {anchor X} l) (k X) ≤ 1 ∧
        ‖k X - condExpect (graphNbhd_subset Λ {anchor X} l) (k X)‖ ≤
          C * Real.exp (-c * (l : ℝ) ^ ((p : ℝ) / (p + 1)))) ∧
      ∀ X ∈ supports Λ R, IsSupportedOn (domainComponent_subset Λ (anchor X)) (k X)

/-! ## Definition 9.3 and Proposition 9.6: templates and the collar bound -/

/-- The collar width `L = ⌊n^{1-ε}⌋`, `ε = 10⁻⁵`, of Propositions 9.6 and 10.2
[OAI265, §9.5 and §10.2]. -/
noncomputable def collarWidth (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 - (1 / 100000 : ℝ))⌋₊

/-- A planar direction of slope `0`, `∞`, `1` or `-1` [OAI265, Definition 9.3]. -/
def HasTemplateSlope (v : ℝ × ℝ) : Prop :=
  v.2 = 0 ∨ v.1 = 0 ∨ v.2 = v.1 ∨ v.2 = -v.1

/-- A closed convex rectangle or triangle in the plane all of whose sides have slope `0`, `∞`,
`1` or `-1` [OAI265, Definition 9.3]: the hull of `a, a + u, a + u + v, a + v` with `u ⊥ v`
nonzero, or of three affinely independent points. -/
def IsTemplatePiece (P : Set (ℝ × ℝ)) : Prop :=
  (∃ a u v : ℝ × ℝ, u ≠ 0 ∧ v ≠ 0 ∧ u.1 * v.1 + u.2 * v.2 = 0 ∧
      HasTemplateSlope u ∧ HasTemplateSlope v ∧
      P = convexHull ℝ {a, a + u, a + u + v, a + v}) ∨
  (∃ a b c : ℝ × ℝ, (b - a).1 * (c - a).2 - (b - a).2 * (c - a).1 ≠ 0 ∧
      HasTemplateSlope (b - a) ∧ HasTemplateSlope (c - b) ∧ HasTemplateSlope (a - c) ∧
      P = convexHull ℝ {a, b, c})

/-- **Definition 9.3**, templates [OAI265, §9.3]: for the numerical constant `C_tpl`, a
nonempty `T ⊂ ℤ²` that is the union of the lattice samples of `N₀ ≥ 1` template pieces, each
of sup-norm diameter at most `s₀`, with `n ≥ C_tpl N₀ (s₀ + 1)` and `diam_∞ T ≤ n`. -/
def IsTemplate (Ctpl : ℝ) (n s₀ : ℕ) (T : Finset (ℤ × ℤ)) : Prop :=
  1 ≤ n ∧ 1 ≤ s₀ ∧ T.Nonempty ∧
    ∃ (N₀ : ℕ) (P : Fin N₀ → Set (ℝ × ℝ)), 1 ≤ N₀ ∧
      (∀ i, IsTemplatePiece (P i) ∧ Metric.ediam (P i) ≤ (s₀ : ENNReal)) ∧
      (T : Set (ℤ × ℤ)) = ⋃ i, (fun z : ℤ × ℤ => ((z.1 : ℝ), (z.2 : ℝ))) ⁻¹' P i ∧
      Ctpl * N₀ * (s₀ + 1) ≤ n ∧
      Metric.ediam (T : Set (ℤ × ℤ)) ≤ (n : ENNReal)

/-- A template is separated from the cut `A`, `dist_∞(T, Z_A) > 4 D₀ s₀`
[OAI265, Definition 9.3], with `D₀` the constant of §3.2. -/
def IsSeparatedFromCut (D₀ : ℝ) (s₀ : ℕ) (Λ A T : Finset (ℤ × ℤ)) : Prop :=
  ENNReal.ofReal (4 * D₀ * s₀) < ambientEDist T (cutEndpoints Λ A)

/-- **Proposition 9.6** [OAI265, §9.5, eq. (9.16)]: for a template `T` separated from the cut,
`L = ⌊n^{1-10⁻⁵}⌋ ≤ s₀`, `X = A ∩ T` and `S₀ = A ∩ T_L`, at all `n` beyond a threshold,
`I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}` with `ε = 10⁻⁵`, the cuts of `X`, `S₀` and `S₀ \ X` have at
most `C n` edges, and `|S₀| ≤ C n²`.  `D₀` is any constant above `2R + 10` (§3.2), `C_tpl`
any constant large enough (§9.3, Lemma 9.4); `C` and the threshold are independent of `T`,
`s₀`, `n`, `Λ` and `A`. -/
def CollarBound (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∀ D₀ : ℝ, 2 * R + 10 < D₀ → ∃ Ctpl₀ : ℝ, ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∃ C : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s₀ : ℕ),
      IsTemplate Ctpl n s₀ T → IsSeparatedFromCut D₀ s₀ Λ A T →
      collarWidth n ≤ s₀ → n₀ ≤ n →
      (pureState Ω hΩ).mutualInfo (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
          (Finset.sdiff_subset :
            Λ \ (A ∩ ambientDilation T (collarWidth n)) ⊆ Λ) ≤
        C * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) ∧
      ((edgeBoundary Λ (A ∩ T)).card : ℝ) ≤ C * n ∧
      ((edgeBoundary Λ (A ∩ ambientDilation T (collarWidth n))).card : ℝ) ≤ C * n ∧
      ((edgeBoundary Λ ((A ∩ ambientDilation T (collarWidth n)) \ (A ∩ T))).card : ℝ) ≤
        C * n ∧
      ((A ∩ ambientDilation T (collarWidth n)).card : ℝ) ≤ C * n ^ 2

/-! ## Proposition 10.2: amplification -/

/-- **Proposition 10.2** [OAI265, §10.2, eqs. (10.15)–(10.18)], with `ε = 10⁻⁵`,
`β = 1 - 2·10⁻⁶` and `α = p / (p + 1)` of eq. (10.1).  For every `C₀ > 0` and `M ≥ 1` there
are `C_M` and a threshold, independent of `Λ`, `A` and `T`, such that: if `L = ⌊n^{1-ε}⌋`,
`X = A ∩ T`, `S₀ = A ∩ T_L`, `|S₀| ≤ C₀ n²`, the cuts `X`, `S₀ \ X`, `S₀` have at most `C₀ n`
edges and `I_Ω(X : Λ \ S₀) ≤ C₀ n^{1-ε}`, then some radius `r ≤ C_M n^{(1-ε)/α}` gives
`I_Ω(X' : J) ≤ C_M n^{-M}` for every `X' ⊆ X` and every `J ⊆ Λ \ N_{2r}(S₀)`, and
`N_{2r}(S₀) ⊆ A` once `dist_∞(T, Z_A) > L + n^β`.

The paper's clause `L + 2r = o(n^β)` in (10.16) is not stated separately: it follows from
`r ≤ C_M n^{(1-ε)/α}`, since `α > 1 - 10⁻⁶` makes `(1-ε)/α < β`. -/
def Amplification (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ M : ℕ, 1 ≤ M → ∃ C_M : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n : ℕ), 2 ≤ n → n₀ ≤ n →
      ((A ∩ ambientDilation T (collarWidth n)).card : ℝ) ≤ C₀ * n ^ 2 →
      ((edgeBoundary Λ (A ∩ T)).card : ℝ) ≤ C₀ * n →
      ((edgeBoundary Λ ((A ∩ ambientDilation T (collarWidth n)) \ (A ∩ T))).card : ℝ) ≤
        C₀ * n →
      ((edgeBoundary Λ (A ∩ ambientDilation T (collarWidth n))).card : ℝ) ≤ C₀ * n →
      (pureState Ω hΩ).mutualInfo (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
          (Finset.sdiff_subset :
            Λ \ (A ∩ ambientDilation T (collarWidth n)) ⊆ Λ) ≤
        C₀ * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) →
      ∃ r : ℕ, (r : ℝ) ≤ C_M * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / ((p : ℝ) / (p + 1))) ∧
        (∀ (X' : Finset (ℤ × ℤ)) (hX' : X' ⊆ A ∩ T) (J : Finset (ℤ × ℤ))
            (hJ : J ⊆ Λ \ graphNbhd Λ (A ∩ ambientDilation T (collarWidth n)) (2 * r)),
          (pureState Ω hΩ).mutualInfo (hX'.trans (Finset.inter_subset_left.trans hA))
              (hJ.trans Finset.sdiff_subset) ≤ C_M * ((n : ℝ) ^ M)⁻¹) ∧
        (ENNReal.ofReal (collarWidth n + (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)))
            < ambientEDist T (cutEndpoints Λ A) →
          graphNbhd Λ (A ∩ ambientDilation T (collarWidth n)) (2 * r) ⊆ A)

/-! ## Lemma 11.1: two-family entropy cancellation -/

/-- **Lemma 11.1** [OAI265, §11.1]: for a pure state `ψ` on the region `Λ`, a partition
`A = D ∪ ⋃ᵢ Xᵢ ⊆ Λ` into disjoint sets, labels `f i ∈ {0, 1}` and errors `εᵢ` with
`I_ψ(Xᵢ : (Λ \ A) ∪ ⋃_{j < i, f j = f i} X_j) ≤ εᵢ`, one has
`S_ψ(A) ≤ S_ψ(D) + ½ ∑ εᵢ`.  The two ordered families of the paper are the fibres of `f`,
ordered as in `Fin m`. -/
def TwoFamilyCancellation (σ : Type*) [DecidableEq σ] (loc : σ → Type*)
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (Λ : Finset σ) (ψ : Reg loc Λ → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1)
    (A D : Finset σ) (hA : A ⊆ Λ) (hD : D ⊆ Λ) (m : ℕ) (X : Fin m → Finset σ)
    (hX : ∀ i, X i ⊆ Λ) (f : Fin m → Fin 2) (ε : Fin m → ℝ),
    A = D ∪ Finset.univ.biUnion X → (∀ i, Disjoint D (X i)) →
    Pairwise (Function.onFun Disjoint X) →
    (∀ i, (pureState ψ hψ).mutualInfo (hX i)
        (Finset.union_subset Finset.sdiff_subset
          (Finset.biUnion_subset.2 fun j _ => hX j) :
          Λ \ A ∪ (Finset.univ.filter fun j => f j = f i ∧ j < i).biUnion X ⊆ Λ) ≤ ε i) →
    (pureState ψ hψ).regionEntropy hA ≤ (pureState ψ hψ).regionEntropy hD + (1 / 2) * ∑ i, ε i

/-! ## Proposition 11.2: two families with separated birth templates -/

/-- **Proposition 11.2** [OAI265, §11.2, eqs. (11.3) and (11.4)], with `β = 1 - 2·10⁻⁶` and
`ℓ = 10⁻⁵` of eq. (11.1): for fixed `D₀`, `C_tpl` and a scale threshold `n_* ≥ 1` there is a
constant `C` such that every cut `A ⊆ Λ` with `b = |∂_Λ A| > 0` decomposes as
`A = D ∪ ⋃ᵢ Xᵢ`, disjointly, with `|D| ≤ C b`, nonempty `Xᵢ ⊆ A ∩ Tᵢ` for templates `Tᵢ` with
parameters `(nᵢ, sᵢ)` separated from the cut, `nᵢ ≥ n_*`, `⌊nᵢ^{1-ℓ}⌋ ≤ sᵢ`,
`dist_∞(Tᵢ, Z_A) > 2 nᵢ^β`, `dist_∞(Tᵢ, ⋃_{j < i, f j = f i} X_j) > 2 nᵢ^β`, and
`∑ᵢ nᵢ^{-100} ≤ C b`.  Purely geometric: no Hamiltonian enters. -/
def TwoFamilyDecomposition : Prop :=
  ∀ (D₀ Ctpl : ℝ) (nStar : ℕ), 1 ≤ nStar → ∃ C : ℝ,
    ∀ Λ A : Finset (ℤ × ℤ), A ⊆ Λ → 0 < (edgeBoundary Λ A).card →
    ∃ (D : Finset (ℤ × ℤ)) (m : ℕ) (X : Fin m → Finset (ℤ × ℤ)) (f : Fin m → Fin 2)
      (T : Fin m → Finset (ℤ × ℤ)) (n s : Fin m → ℕ),
      A = D ∪ Finset.univ.biUnion X ∧ (∀ i, Disjoint D (X i)) ∧
      Pairwise (Function.onFun Disjoint X) ∧
      (D.card : ℝ) ≤ C * (edgeBoundary Λ A).card ∧
      (∀ i, (X i).Nonempty ∧ X i ⊆ A ∩ T i ∧ nStar ≤ n i ∧
        IsTemplate Ctpl (n i) (s i) (T i) ∧ IsSeparatedFromCut D₀ (s i) Λ A (T i) ∧
        collarWidth (n i) ≤ s i ∧
        ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
          ambientEDist (T i) (cutEndpoints Λ A) ∧
        ENNReal.ofReal (2 * (n i : ℝ) ^ (1 - (2 / 1000000 : ℝ))) <
          ambientEDist (T i) ((Finset.univ.filter fun j => j < i ∧ f j = f i).biUnion X)) ∧
      ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C * (edgeBoundary Λ A).card

/-! ## Lemma 2.1: continuity of conditional entropy -/

/-- **Lemma 2.1** [OAI265, §2.1, eq. (2.1)], on regions: for states `ρ`, `τ` on `U` and
disjoint regions `X`, `Y ⊆ U` (the paper's `D`, `E`), with `δ` the trace distance of the
marginals on `X ∪ Y` and `d_X` the dimension of `X`,
`|S(X|Y)_ρ - S(X|Y)_τ| ≤ 2 δ log d_X + (1 + δ) h(δ / (1 + δ)) ≤ 4 √δ log (e d_X)`, where
`S(X|Y) = S(X ∪ Y) - S(Y)` and `h` is the binary entropy.  The paper's absolute constant `C` is
`4`.  The paper's bipartite `D ⊗ E` is the case `U = X ∪ Y`; `Y = ∅` gives the bound for
`S(X)`. -/
def ConditionalContinuity (σ : Type*) [DecidableEq σ] (loc : σ → Type*)
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (U X Y : Finset σ) (hX : X ⊆ U) (hY : Y ⊆ U), Disjoint X Y →
    ∀ ρ τ : MState (Reg loc U) 𝕜,
      |(ρ.toSubState.regionEntropy (Finset.union_subset hX hY) - ρ.toSubState.regionEntropy hY) -
          (τ.toSubState.regionEntropy (Finset.union_subset hX hY) -
            τ.toSubState.regionEntropy hY)| ≤
        2 * (ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
            (τ.toSubState.restrict (Finset.union_subset hX hY)) *
            Real.log (Fintype.card (Reg loc X)) +
          (1 + (ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
            (τ.toSubState.restrict (Finset.union_subset hX hY))) *
            Real.binEntropy ((ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
                (τ.toSubState.restrict (Finset.union_subset hX hY)) /
              (1 + (ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
                (τ.toSubState.restrict (Finset.union_subset hX hY)))) ∧
      |(ρ.toSubState.regionEntropy (Finset.union_subset hX hY) - ρ.toSubState.regionEntropy hY) -
          (τ.toSubState.regionEntropy (Finset.union_subset hX hY) -
            τ.toSubState.regionEntropy hY)| ≤
        4 * Real.sqrt ((ρ.toSubState.restrict (Finset.union_subset hX hY)).D₁
            (τ.toSubState.restrict (Finset.union_subset hX hY))) *
          Real.log (Real.exp 1 * Fintype.card (Reg loc X))

/-! ## Lemma 3.1: marginal moment and tail bounds -/

/-- **Lemma 3.1** [OAI265, §3.1, eqs. (3.1) and (3.2)], on any finite tensor product: let
`H = ∑ᵢ hᵢ` with `hᵢ` Hermitian, `‖hᵢ‖ ≤ c₀`, supported on `Dᵢ ⊆ U`, with normalized ground
vector `Ψ` of energy `E₀` and gap `g₀ > 0`.  For a cut `B ⊆ U` let `ρ` be the marginal on `B`,
`pⱼ` its positive eigenvalues, `S` its entropy, `ϑ = c₀ / g₀` and
`𝓑 = 1 + ∑_{i crossing} log² (e dᵢ)` over the terms whose support meets both `B` and `U \ B`,
`dᵢ` the dimension of `Dᵢ`.  The surprisal `K = -log pⱼ` (with probability `pⱼ`) satisfies
`log E e^{uK} ≤ u S + 512 e ϑ 𝓑 u²` for `|u| ≤ (32 √((1 + ϑ) 𝓑))⁻¹`, and
`P{|K - S| > w} ≤ min 1 (2 e^{e/2} exp (-w / (32 √((1 + ϑ) 𝓑))))` for `w ≥ 0`. -/
def MarginalTails (σ : Type*) [DecidableEq σ] (loc : σ → Type*)
    [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (U : Finset σ) (ι : Type) [Fintype ι] (D : ι → Finset σ) (hD : ∀ i, D i ⊆ U)
    (h : ι → Matrix (Reg loc U) (Reg loc U) 𝕜) (c₀ g₀ E₀ : ℝ) (Ψ : Reg loc U → 𝕜)
    (hΨ : star Ψ ⬝ᵥ Ψ = 1),
    (∀ i, IsSupportedOn (hD i) (h i)) → (∀ i, (h i).IsHermitian) → 0 ≤ c₀ →
    (∀ i, ‖h i‖ ≤ c₀) → 0 < g₀ → (∑ i, h i) *ᵥ Ψ = (E₀ : 𝕜) • Ψ →
    HasGlobalGap (∑ i, h i) Ψ E₀ g₀ →
    ∀ (B : Finset σ) (hB : B ⊆ U),
      let ρ := (pureState Ψ hΨ).toSubState.restrict hB
      let p := ρ.psd.isHermitian.eigenvalues
      let 𝓑 := 1 + ∑ i ∈ Finset.univ.filter (fun i => (D i ∩ B).Nonempty ∧ (D i \ B).Nonempty),
        Real.log (Real.exp 1 * Fintype.card (Reg loc (D i))) ^ 2
      (∀ u : ℝ, |u| ≤ (32 * Real.sqrt ((1 + c₀ / g₀) * 𝓑))⁻¹ →
        Real.log (∑ j ∈ Finset.univ.filter (fun j => 0 < p j),
            p j * Real.exp (-u * Real.log (p j))) ≤
          u * ρ.entropy + 512 * Real.exp 1 * (c₀ / g₀) * 𝓑 * u ^ 2) ∧
      ∀ w : ℝ, 0 ≤ w →
        ∑ j ∈ Finset.univ.filter (fun j => 0 < p j ∧ w < |-Real.log (p j) - ρ.entropy|), p j ≤
          min 1 (2 * Real.exp (Real.exp 1 / 2) *
            Real.exp (-(w / (32 * Real.sqrt ((1 + c₀ / g₀) * 𝓑)))))

/-! ## Lemma 3.2 and Proposition 3.3: safe rectangles -/

/-- An integer rectangle: a product of two finite nonempty integer intervals
[OAI265, §3.2]. -/
def IsIntRect (Q : Finset (ℤ × ℤ)) : Prop :=
  ∃ a b : ℤ × ℤ, a ≤ b ∧ Q = Finset.Icc a b

/-- The size of a set of sites: the larger number of sites along an axis, which for an
integer rectangle is the size of [OAI265, §3.2]. -/
def boxSize (Q : Finset (ℤ × ℤ)) : ℕ :=
  max (Q.image Prod.fst).card (Q.image Prod.snd).card

/-- A rectangle is safe for the cut `A` when `dist_∞(Q, Z_A) > D₀ size(Q)`, distance to the
empty set being infinite [OAI265, §3.2]. -/
def IsSafe (D₀ : ℝ) (Λ A Q : Finset (ℤ × ℤ)) : Prop :=
  ENNReal.ofReal (D₀ * boxSize Q) < ambientEDist Q (cutEndpoints Λ A)

/-- **Lemma 3.2** [OAI265, §3.2, eq. (3.9)]: there are an integer `C_pad ≥ 1` and a constant
`C_buf`, depending only on `q`, `R`, `J`, `Δ`, such that for every `D₀ > 2R + 10`, every
admissible Hamiltonian with gapped ground vector `Ω`, every cut `A`, every safe rectangle `Q`,
every integer `r ≥ 1` and every rectangle `Q₀` of size at most `r` with
`Q₀^{+C_pad r} ⊆ Q`, the sets `X = A ∩ Q₀` and `T = (A ∩ Q₀^{+C_pad r}) \ X` satisfy
`S(X | T) ≤ S(X) / 2 + C_buf r`. -/
def BufferDiscount (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ Cpad : ℕ, 1 ≤ Cpad ∧ ∃ Cbuf : ℝ, ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)), IsIntRect Q → IsSafe D₀ Λ A Q →
    ∀ (r : ℕ), 1 ≤ r → ∀ Q₀ : Finset (ℤ × ℤ), IsIntRect Q₀ → boxSize Q₀ ≤ r →
      ambientDilation Q₀ (Cpad * r) ⊆ Q →
      (pureState Ω hΩ).regionEntropy
          ((Finset.union_subset (Finset.inter_subset_left.trans hA)
            (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA))) :
            A ∩ Q₀ ∪ (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) -
        (pureState Ω hΩ).regionEntropy
          (Finset.sdiff_subset.trans (Finset.inter_subset_left.trans hA) :
            (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) ⊆ Λ) ≤
      (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q₀ ⊆ Λ) / 2 +
        Cbuf * r

/-- **Proposition 3.3** [OAI265, §3.3, eq. (3.21)]: there are constants `C` and
`e₀ ∈ (0, 1)`, depending only on `q`, `R`, `J`, `Δ`, such that `S_Ω(A ∩ Q) ≤ C r^{1 + e₀}` for
every `D₀ > 2R + 10`, every admissible Hamiltonian with gapped ground vector `Ω`, every cut
`A` and every safe rectangle `Q` of size at most `r ≥ 1`.  This is the paper's
`F_box(r) ≤ C r^{1 + e₀}` with the supremum `F_box` unfolded. -/
def InitialBoxEstimate (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ C e₀ : ℝ, 0 < e₀ ∧ e₀ < 1 ∧ ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)) (r : ℕ), 1 ≤ r → IsIntRect Q →
      IsSafe D₀ Λ A Q → boxSize Q ≤ r →
      (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤
        C * (r : ℝ) ^ (1 + e₀)

end OpenAI
