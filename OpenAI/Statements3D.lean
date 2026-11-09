import OpenAI.Statements

/-!
# Statements of three-dimensional targets for the area law

The statement layer for a three-dimensional continuation of [OAI265] (OpenAI, *A two-dimensional
area law from a global spectral gap*, 24 September 2026, unrefereed).  The document
`docs/3D/Targets.md` explains every statement below, its plausibility and its role.

Every declaration here is a definition; nothing is proved.  Each target is a `def … : Prop`.
The only terms of `Prop` type that appear are the subset witnesses a region needs to be well
typed, as in `OpenAI.Statements`.  The statements are frozen: a proof attempt targets one of them
and does not change it.

## Encoding

Sites are `ℤ × ℤ × ℤ` (that is, `ℤ × (ℤ × ℤ)`) with Mathlib's `hasse ℤ □ (hasse ℤ □ hasse ℤ)`,
whose adjacency is Euclidean distance one.  This is the smallest change to the 2D encoding
`ℤ × ℤ` with `hasse ℤ □ hasse ℤ`: the product order gives `Finset.Icc` boxes, the product
extended metric is the sup norm `dist_∞` of [OAI265, §3.2], and pointwise addition gives the
dilations `T_j`, all exactly as in two dimensions.  `Fin 3 → ℤ` would also carry the sup metric
and the order, but has no Mathlib graph structure, so its adjacency would have to be written
by hand.  A slab `ℤ² × [0, h)` is a set of sites of `ℤ³` with third coordinate in `[0, h)`,
so slab statements use the same types as the cubic ones.

Decidability of adjacency is supplied classically: the 2D file proves a decidable instance,
and a proof is what this file must not contain.

## Main definitions

* `cubicLattice3D`, `domainEDist3D`, `graphNbhd3D`, `edgeBoundary3D`, `cutEndpoints3D`,
  `ambientEDist3D`, `ambientDilation3D`: the cubic lattice and its induced domains.
* `Qudits3D`, `supports3D`, `hamiltonian3D`, `IsAdmissible3D`: the Hamiltonian class of
  [OAI265, eq. (1.1)] on `ℤ³`.
* `IsTemplatePiece3D`, `IsTemplate3D`, `IsSeparatedFromCut3D`: a 3D version of Definition 9.3.
* `IsIntBox3D`, `boxSize3D`, `IsSafe3D`: integer boxes and safety (§3.2).

## Statements

* `AreaLaw3D`: the north star, Theorem 1.1 on `ℤ³`.  Not a target.
* `CylinderAreaLaw3D`, `CylinderAreaLawOfPlanar3D`: target 1 (slabs over a planar domain).
* `SlabAreaLaw3D`: target 2 (arbitrary domains inside a slab).
* `PositiveReplacement3D`: target 3 (Proposition 4.3 on `ℤ³`).
* `Amplification3D`: target 4 (Proposition 10.2 on `ℤ³`).
* `AreaLawAssembly3D`: target 5 (the assembly of §11.8 from three 3D inputs).
* `CollarBound3D`, `InitialBoxEstimate3D`, `TwoFamilyDecomposition3D`: open problems, frozen so
  that `AreaLawAssembly3D` and later work have fixed interfaces.

Statements of `OpenAI.Statements` that already quantify over an arbitrary site type
(`TwoFamilyCancellation`, `ConditionalContinuity`, `MarginalTails`) need no 3D version: they
apply to `ℤ × ℤ × ℤ` as they stand.
-/

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Pointwise
open Matrix SimpleGraph

/-! ## The cubic lattice and its finite induced domains -/

/-- The cubic lattice `ℤ³` as `hasse ℤ □ (hasse ℤ □ hasse ℤ)`: two sites are adjacent when two
coordinates agree and the third changes by one.  Changed from 2D: one more factor `hasse ℤ`. -/
noncomputable abbrev cubicLattice3D : SimpleGraph (ℤ × ℤ × ℤ) := hasse ℤ □ (hasse ℤ □ hasse ℤ)

/-- Adjacency in `cubicLattice3D` is decidable.  Changed from
`instDecidableRelAdjSquareLattice`: the instance is classical, so that this file carries no
proof. -/
noncomputable instance instDecidableRelAdjCubicLattice3D : DecidableRel cubicLattice3D.Adj :=
  Classical.decRel _

/-- The graph distance `d_Λ` of the cubic-lattice graph induced on a finite domain
`Λ ⊂ ℤ³` [OAI265, §1.1].  Changed from `domainEDist`: `ℤ³` and `cubicLattice3D` in place of
`ℤ²` and the square lattice; `⊤` between components and off `Λ`, as there. -/
noncomputable def domainEDist3D (Λ : Finset (ℤ × ℤ × ℤ)) (x y : ℤ × ℤ × ℤ) : ℕ∞ :=
  if h : x ∈ Λ ∧ y ∈ Λ then
    (cubicLattice3D.induce (Λ : Set (ℤ × ℤ × ℤ))).edist ⟨x, h.1⟩ ⟨y, h.2⟩
  else ⊤

/-- The diameter `diam_{d_Λ} X` [OAI265, eq. (1.1)].  Changed from `domainEDiam`: sites in
`ℤ³`, distance `domainEDist3D`. -/
noncomputable def domainEDiam3D (Λ X : Finset (ℤ × ℤ × ℤ)) : ℕ∞ :=
  ⨆ x ∈ X, ⨆ y ∈ X, domainEDist3D Λ x y

/-- The graph neighbourhood `N_r(S)` [OAI265, §2.2 and §10].  Changed from `graphNbhd`: sites
in `ℤ³`, distance `domainEDist3D`. -/
noncomputable def graphNbhd3D (Λ S : Finset (ℤ × ℤ × ℤ)) (r : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Λ.filter fun x => (⨅ y ∈ S, domainEDist3D Λ x y) ≤ r

/-- The connected component of `a` in the induced graph on `Λ` [OAI265, §4.2].  Changed from
`domainComponent`: sites in `ℤ³`, distance `domainEDist3D`. -/
noncomputable def domainComponent3D (Λ : Finset (ℤ × ℤ × ℤ)) (a : ℤ × ℤ × ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  Λ.filter fun x => domainEDist3D Λ a x ≠ ⊤

/-- The edge boundary `∂_Λ A` [OAI265, §1.1], each crossing edge once, oriented out of `A`.
Changed from `edgeBoundary`: the edges are those of `cubicLattice3D`. -/
noncomputable def edgeBoundary3D (Λ A : Finset (ℤ × ℤ × ℤ)) :
    Finset ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  cubicLattice3D.interedges A (Λ \ A)

/-- The crossing-edge endpoints `Z_A` [OAI265, §1.1].  Changed from `cutEndpoints`: built on
`edgeBoundary3D`. -/
noncomputable def cutEndpoints3D (Λ A : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  (edgeBoundary3D Λ A).image Prod.fst ∪ (edgeBoundary3D Λ A).image Prod.snd

/-- The ambient sup-norm distance `dist_∞(T, Z)` [OAI265, §3.2], `⊤` when either set is empty.
Changed from `ambientEDist`: the sup-norm extended metric of `ℤ × ℤ × ℤ`. -/
noncomputable def ambientEDist3D (T Z : Finset (ℤ × ℤ × ℤ)) : ENNReal :=
  ⨅ x ∈ T, Metric.infEDist x (Z : Set (ℤ × ℤ × ℤ))

/-- The ambient dilation `T_j = T + ([-j, j]³ ∩ ℤ³)` [OAI265, §2.2].  Changed from
`ambientDilation`: the cube `[-j, j]³` in place of the square `[-j, j]²`. -/
noncomputable def ambientDilation3D (T : Finset (ℤ × ℤ × ℤ)) (j : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  T + Finset.Icc (-(j : ℤ), -(j : ℤ), -(j : ℤ)) ((j : ℤ), (j : ℤ), (j : ℤ))

/-! ## Hamiltonians on the cubic lattice -/

/-- Every site of `ℤ³` carries `Fin q` [OAI265, §1.1].  Changed from `Qudits`: the index type
is `ℤ × ℤ × ℤ`. -/
abbrev Qudits3D (q : ℕ) : ℤ × ℤ × ℤ → Type := fun _ => Fin q

/-- The admissible supports: nonempty `X ⊆ Λ` with `diam_{d_Λ} X ≤ R` [OAI265, eq. (1.1)].
Changed from `supports`: sites in `ℤ³`, diameter `domainEDiam3D`. -/
noncomputable def supports3D (Λ : Finset (ℤ × ℤ × ℤ)) (R : ℕ) :
    Finset (Finset (ℤ × ℤ × ℤ)) :=
  Λ.powerset.filter fun X => X.Nonempty ∧ domainEDiam3D Λ X ≤ R

variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}

/-- The Hamiltonian `H = ∑_{X ⊆ Λ} h_X` [OAI265, eq. (1.1)].  Changed from `hamiltonian`:
supports are subsets of `ℤ³` and sites carry `Qudits3D q`. -/
noncomputable def hamiltonian3D (Λ : Finset (ℤ × ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜) :
    Matrix (Reg (Qudits3D q) Λ) (Reg (Qudits3D q) Λ) 𝕜 :=
  ∑ X ∈ Λ.powerset.attach, extendId (Finset.mem_powerset.1 X.2) (Φ X.1)

/-- An admissible interaction of range `R` and strength `J` [OAI265, eq. (1.1)].  Changed from
`IsAdmissible`: supports in `ℤ³`, admissibility through `supports3D`. -/
def IsAdmissible3D (Λ : Finset (ℤ × ℤ × ℤ)) (R : ℕ) (J : ℝ)
    (Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜) :
    Prop :=
  ∀ X ⊆ Λ, (Φ X).IsHermitian ∧ ‖Φ X‖ ≤ J ∧ (X ∉ supports3D Λ R → Φ X = 0)

/-! ## The north star -/

/-- **The three-dimensional area law** (not a target).  Theorem 1.1 of [OAI265] with `ℤ³` in
place of `ℤ²`: one constant `C`, depending on `q`, `R`, `J`, `Δ` only, bounds
`S_Ω(A) ≤ C |∂_Λ A|` for every finite `Λ ⊂ ℤ³`, every admissible Hamiltonian with a normalized
eigenvector `Ω` of eigenvalue `E₀` and global gap `Δ`, and every `A ⊆ Λ`.  Changed from
`AreaLaw`: every lattice notion is its `3D` version; the gap, the pure state and the entropy are
the 2D ones unchanged. -/
def AreaLaw3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ Λ : Finset (ℤ × ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hA ≤ C * (edgeBoundary3D Λ A).card

/-! ## Targets 1 and 2: slabs -/

/-- A domain inside the slab `ℤ² × [0, h)`: every site has third coordinate in `[0, h)`. -/
def IsSlabDomain3D (h : ℕ) (Λ : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∀ x ∈ Λ, 0 ≤ x.2.2 ∧ x.2.2 < h

/-- A cylinder domain `Λ' × [0, h)` over a finite planar domain `Λ' ⊂ ℤ²`: every column over
`Λ'` is present in full. -/
def IsCylinderDomain3D (h : ℕ) (Λ : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∃ Λ' : Finset (ℤ × ℤ), ∀ x : ℤ × ℤ × ℤ, x ∈ Λ ↔ (x.1, x.2.1) ∈ Λ' ∧ 0 ≤ x.2.2 ∧ x.2.2 < h

/-- **Target 2**, the area law inside a slab of thickness `h`: `AreaLaw3D` restricted to
domains `Λ` with `IsSlabDomain3D h Λ`.  The constant may depend on `h`. -/
def SlabAreaLaw3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (h : ℕ) : Prop :=
  ∃ C : ℝ, ∀ Λ : Finset (ℤ × ℤ × ℤ), IsSlabDomain3D h Λ →
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hA ≤ C * (edgeBoundary3D Λ A).card

/-- **Target 1**, the area law on cylinder domains `Λ' × [0, h)`: `AreaLaw3D` restricted to
domains with `IsCylinderDomain3D h Λ`, for every cut `A ⊆ Λ`, including cuts that split
columns.  The constant may depend on `h`. -/
def CylinderAreaLaw3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (h : ℕ) : Prop :=
  ∃ C : ℝ, ∀ Λ : Finset (ℤ × ℤ × ℤ), IsCylinderDomain3D h Λ →
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hA ≤ C * (edgeBoundary3D Λ A).card

/-- **Target 1 as a corollary**: the planar area law with local dimension `q ^ h`, at every
strength, gives the area law on cylinders of thickness `h`.  Grouping each column into one
planar site of dimension `q ^ h` keeps the range `R` and multiplies the strength by a factor
depending on `h` and `R` only, which is why the hypothesis quantifies over every strength.
With `area_law` the hypothesis holds whenever `1 ≤ q` and `0 < Δ`. -/
def CylinderAreaLawOfPlanar3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (h : ℕ) : Prop :=
  (∀ J' : ℝ, 0 < J' → AreaLaw 𝕜 (q ^ h) R J' Δ) → CylinderAreaLaw3D 𝕜 q R J Δ h

/-! ## Target 3: positive replacement on the cubic lattice -/

/-- **Target 3**, Proposition 4.3 [OAI265, §4.2, eqs. (4.8) and (4.9)] on `ℤ³`, for a fixed
integer `p ≥ 1` and `α = p / (p + 1)`: operators `0 ≤ k_X ≤ 1` with `k_X Ω = 0`,
`∑ k_X ≥ c_*⁻¹ (H - E₀) ≥ (Δ / c_*) (1 - |Ω⟩⟨Ω|)`, local approximants
`E_{X,l}(k_X) ∈ [0, 1]` within `C e^{-c l^α}`, and `k_X` supported in the component of its
anchor.  Changed from `PositiveReplacement`: every lattice notion is its `3D` version; the
exponent `α` and the form of every clause are unchanged. -/
def PositiveReplacement3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) : Prop :=
  ∃ cstar : ℝ, 0 < cstar ∧ ∃ C c : ℝ, 0 < c ∧
    ∀ Λ : Finset (ℤ × ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (_ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ anchor : Finset (ℤ × ℤ × ℤ) → ℤ × ℤ × ℤ, (∀ X ∈ supports3D Λ R, anchor X ∈ X) →
    ∃ k : Finset (ℤ × ℤ × ℤ) → Matrix (Reg (Qudits3D q) Λ) (Reg (Qudits3D q) Λ) 𝕜,
      (∀ X ∈ supports3D Λ R, 0 ≤ k X ∧ k X ≤ 1 ∧ k X *ᵥ Ω = 0) ∧
      (cstar : 𝕜)⁻¹ • (hamiltonian3D Λ Φ - (E₀ : 𝕜) • 1) ≤ ∑ X ∈ supports3D Λ R, k X ∧
      ((Δ / cstar : ℝ) : 𝕜) • (1 - vecMulVec Ω (star Ω)) ≤
        (cstar : 𝕜)⁻¹ • (hamiltonian3D Λ Φ - (E₀ : 𝕜) • 1) ∧
      (∀ X ∈ supports3D Λ R, ∀ l : ℕ,
        0 ≤ condExpect (Finset.filter_subset _ _ : graphNbhd3D Λ {anchor X} l ⊆ Λ) (k X) ∧
        condExpect (Finset.filter_subset _ _ : graphNbhd3D Λ {anchor X} l ⊆ Λ) (k X) ≤ 1 ∧
        ‖k X - condExpect (Finset.filter_subset _ _ : graphNbhd3D Λ {anchor X} l ⊆ Λ) (k X)‖ ≤
          C * Real.exp (-c * (l : ℝ) ^ ((p : ℝ) / (p + 1)))) ∧
      ∀ X ∈ supports3D Λ R,
        IsSupportedOn (Finset.filter_subset _ _ : domainComponent3D Λ (anchor X) ⊆ Λ) (k X)

/-! ## Target 4: amplification on the cubic lattice -/

/-- **Target 4**, Proposition 10.2 [OAI265, §10.2, eqs. (10.15) to (10.18)] on `ℤ³`, with
`α = p / (p + 1)` and a collar exponent `θ`; the target is the statement for every `p ≥ 1` and
every `θ > 1`.  For every `C₀ > 0` and `M ≥ 1` there are `C_M` and a threshold such that: if
`X = A ∩ T`, `S₀ = A ∩ T_L`, `|S₀| ≤ C₀ n³`, the cuts `X`, `S₀ \ X`, `S₀` have at most `C₀ n²`
edges and `I_Ω(X : Λ \ S₀) ≤ C₀ n^θ`, then some radius `r ≤ C_M n^{θ/α}` gives
`I_Ω(X' : J) ≤ C_M n^{-M}` for every `X' ⊆ X` and every `J ⊆ Λ \ N_{2r}(S₀)`, and
`N_{2r}(S₀) ⊆ A` once `dist_∞(T, Z_A) > L + 2r`.

Changed from `Amplification`: lattice notions are their `3D` versions; the volume and cut
hypotheses are `C₀ n³` and `C₀ n²` in place of `C₀ n²` and `C₀ n`; the collar information
hypothesis is `C₀ n^θ` with `θ > 1` in place of `C₀ n^{1-ε}`, and the radius bound is
`n^{θ/α}` in place of `n^{(1-ε)/α}`.  The collar width `L` is a free parameter instead of
`⌊n^{1-ε}⌋`, since no clause of the proposition depends on its value.  The clearance clause
names the radius `r` itself in place of the 2D threshold `n^β`, because in three dimensions
`r` exceeds `n` (see `docs/3D/Targets.md`, §C.3). -/
def Amplification3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) (θ : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ M : ℕ, 1 ≤ M → ∃ C_M : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ × ℤ)) (n L : ℕ),
      2 ≤ n → n₀ ≤ n →
      ((A ∩ ambientDilation3D T L).card : ℝ) ≤ C₀ * n ^ 3 →
      ((edgeBoundary3D Λ (A ∩ T)).card : ℝ) ≤ C₀ * n ^ 2 →
      ((edgeBoundary3D Λ ((A ∩ ambientDilation3D T L) \ (A ∩ T))).card : ℝ) ≤ C₀ * n ^ 2 →
      ((edgeBoundary3D Λ (A ∩ ambientDilation3D T L)).card : ℝ) ≤ C₀ * n ^ 2 →
      (pureState Ω hΩ).mutualInfo (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
          (Finset.sdiff_subset : Λ \ (A ∩ ambientDilation3D T L) ⊆ Λ) ≤
        C₀ * (n : ℝ) ^ θ →
      ∃ r : ℕ, (r : ℝ) ≤ C_M * (n : ℝ) ^ (θ / ((p : ℝ) / (p + 1))) ∧
        (∀ (X' : Finset (ℤ × ℤ × ℤ)) (hX' : X' ⊆ A ∩ T) (J : Finset (ℤ × ℤ × ℤ))
            (hJ : J ⊆ Λ \ graphNbhd3D Λ (A ∩ ambientDilation3D T L) (2 * r)),
          (pureState Ω hΩ).mutualInfo (hX'.trans (Finset.inter_subset_left.trans hA))
              (hJ.trans Finset.sdiff_subset) ≤ C_M * ((n : ℝ) ^ M)⁻¹) ∧
        (ENNReal.ofReal ((L : ℝ) + 2 * r) < ambientEDist3D T (cutEndpoints3D Λ A) →
          graphNbhd3D Λ (A ∩ ambientDilation3D T L) (2 * r) ⊆ A)

/-! ## Templates in three dimensions -/

/-- The 26 template directions: the nonzero vectors of `{-1, 0, 1}³`. -/
noncomputable def templateDirections3D : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-1, -1, -1) (1, 1, 1)).erase 0

/-- The pairing `⟨v, x⟩` of an integer direction with a point of `ℝ³`. -/
def directionPairing3D (v : ℤ × ℤ × ℤ) (x : ℝ × ℝ × ℝ) : ℝ :=
  v.1 * x.1 + v.2.1 * x.2.1 + v.2.2 * x.2.2

/-- A template piece in space: a polytope with nonempty interior cut out by one pair of
inequalities `lo v ≤ ⟨v, x⟩ ≤ hi v` for each of the 26 template directions.  Changed from
`IsTemplatePiece`: the planar pieces are rectangles and triangles with sides of slope `0`, `∞`,
`1`, `-1`, which are exactly the planar polygons of this form with at most four sides.  In
space the class is the whole family of such polytopes: it contains boxes, prisms over the
planar pieces and the simplices of the barycentric subdivision of a cube.  The family a 3D
Section 11 would need is not known, so the class is taken broad; a broader class makes
`CollarBound3D` stronger and `TwoFamilyDecomposition3D` weaker. -/
def IsTemplatePiece3D (P : Set (ℝ × ℝ × ℝ)) : Prop :=
  (interior P).Nonempty ∧ ∃ lo hi : ℤ × ℤ × ℤ → ℝ,
    P = {x | ∀ v ∈ templateDirections3D,
      lo v ≤ directionPairing3D v x ∧ directionPairing3D v x ≤ hi v}

/-- Templates in space [OAI265, Definition 9.3]: a nonempty `T ⊂ ℤ³` that is the union of the
lattice samples of `N₀ ≥ 1` pieces, each of sup-norm diameter at most `s₀`, with
`n ≥ C_tpl N₀ (s₀ + 1)` and `diam_∞ T ≤ n`.  Changed from `IsTemplate`: pieces are
`IsTemplatePiece3D`, sites and points are in `ℤ³` and `ℝ³`; the numerical conditions are
unchanged. -/
def IsTemplate3D (Ctpl : ℝ) (n s₀ : ℕ) (T : Finset (ℤ × ℤ × ℤ)) : Prop :=
  1 ≤ n ∧ 1 ≤ s₀ ∧ T.Nonempty ∧
    ∃ (N₀ : ℕ) (P : Fin N₀ → Set (ℝ × ℝ × ℝ)), 1 ≤ N₀ ∧
      (∀ i, IsTemplatePiece3D (P i) ∧ Metric.ediam (P i) ≤ (s₀ : ENNReal)) ∧
      (T : Set (ℤ × ℤ × ℤ)) =
        ⋃ i, (fun z : ℤ × ℤ × ℤ => ((z.1 : ℝ), (z.2.1 : ℝ), (z.2.2 : ℝ))) ⁻¹' P i ∧
      Ctpl * N₀ * (s₀ + 1) ≤ n ∧
      Metric.ediam (T : Set (ℤ × ℤ × ℤ)) ≤ (n : ENNReal)

/-- A template separated from the cut, `dist_∞(T, Z_A) > 4 D₀ s₀` [OAI265, Definition 9.3].
Changed from `IsSeparatedFromCut`: `ambientEDist3D` and `cutEndpoints3D`. -/
def IsSeparatedFromCut3D (D₀ : ℝ) (s₀ : ℕ) (Λ A T : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ENNReal.ofReal (4 * D₀ * s₀) < ambientEDist3D T (cutEndpoints3D Λ A)

/-- The collar width `L = ⌊n^{1-ε}⌋` with the exponent `ε` a parameter.  Changed from
`collarWidth`, which fixes `ε = 10⁻⁵`: no value of `ε` is known to work in three
dimensions. -/
noncomputable def collarWidth3D (ε : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 - ε)⌋₊

/-! ## Open problem: the collar bound -/

/-- **Open problem C.1**, Proposition 9.6 [OAI265, §9.5, eq. (9.16)] on `ℤ³` with row size `n²`
in place of `n`, for a collar exponent `ε`; the open question is whether it holds for some
`ε ∈ (0, 1)`.  For a 3D template `T` separated from the cut with `L = ⌊n^{1-ε}⌋ ≤ s₀`,
`X = A ∩ T` and `S₀ = A ∩ T_L`, at all `n` beyond a threshold:
`I_Ω(X : Λ \ S₀) ≤ C (n²)^{1-ε}`, the cuts of `X`, `S₀` and `S₀ \ X` have at most `C n²` edges,
and `|S₀| ≤ C n³`.

Changed from `CollarBound`: lattice notions and templates are their `3D` versions; the bounds
`C n^{1-ε}`, `C n` and `C n²` become `C (n²)^{1-ε}`, `C n²` and `C n³`; `ε` is a parameter in
place of `10⁻⁵`. -/
def CollarBound3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (ε : ℝ) : Prop :=
  ∀ D₀ : ℝ, 2 * R + 10 < D₀ → ∃ Ctpl₀ : ℝ, ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∃ C : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ × ℤ)) (n s₀ : ℕ),
      IsTemplate3D Ctpl n s₀ T → IsSeparatedFromCut3D D₀ s₀ Λ A T →
      collarWidth3D ε n ≤ s₀ → n₀ ≤ n →
      (pureState Ω hΩ).mutualInfo (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
          (Finset.sdiff_subset :
            Λ \ (A ∩ ambientDilation3D T (collarWidth3D ε n)) ⊆ Λ) ≤
        C * ((n : ℝ) ^ 2) ^ (1 - ε) ∧
      ((edgeBoundary3D Λ (A ∩ T)).card : ℝ) ≤ C * n ^ 2 ∧
      ((edgeBoundary3D Λ (A ∩ ambientDilation3D T (collarWidth3D ε n))).card : ℝ) ≤
        C * n ^ 2 ∧
      ((edgeBoundary3D Λ
          ((A ∩ ambientDilation3D T (collarWidth3D ε n)) \ (A ∩ T))).card : ℝ) ≤ C * n ^ 2 ∧
      ((A ∩ ambientDilation3D T (collarWidth3D ε n)).card : ℝ) ≤ C * n ^ 3

/-! ## Open problem: the first subvolume exponent -/

/-- An integer box: a product of three finite nonempty integer intervals [OAI265, §3.2].
Changed from `IsIntRect`: three factors in place of two. -/
def IsIntBox3D (Q : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∃ a b : ℤ × ℤ × ℤ, a ≤ b ∧ Q = Finset.Icc a b

/-- The size of a set of sites: the largest number of sites along an axis [OAI265, §3.2].
Changed from `boxSize`: the maximum over three axes. -/
def boxSize3D (Q : Finset (ℤ × ℤ × ℤ)) : ℕ :=
  max (Q.image Prod.fst).card (max (Q.image fun x => x.2.1).card (Q.image fun x => x.2.2).card)

/-- A box is safe for the cut `A` when `dist_∞(Q, Z_A) > D₀ size(Q)` [OAI265, §3.2].  Changed
from `IsSafe`: `boxSize3D`, `ambientEDist3D` and `cutEndpoints3D`. -/
def IsSafe3D (D₀ : ℝ) (Λ A Q : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ENNReal.ofReal (D₀ * boxSize3D Q) < ambientEDist3D Q (cutEndpoints3D Λ A)

/-- **Open problem C.2**, Proposition 3.3 [OAI265, §3.3, eq. (3.21)] on `ℤ³`: constants `C`
and `e₀ ∈ (0, 1)` with `S_Ω(A ∩ Q) ≤ C r^{2 + e₀}` for every safe box `Q` of size at most
`r ≥ 1`.  Changed from `InitialBoxEstimate`: boxes in place of rectangles and the exponent
`2 + e₀` in place of `1 + e₀`, so that the bound is again strictly below the volume `r³` and
above the area `r²`. -/
def InitialBoxEstimate3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∃ C e₀ : ℝ, 0 < e₀ ∧ e₀ < 1 ∧ ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
    ∀ Λ : Finset (ℤ × ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ × ℤ)) → Matrix (Reg (Qudits3D q) X) (Reg (Qudits3D q) X) 𝕜,
      IsAdmissible3D Λ R J Φ →
    ∀ (Ω : Reg (Qudits3D q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian3D Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian3D Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ × ℤ)) (r : ℕ), 1 ≤ r →
      IsIntBox3D Q → IsSafe3D D₀ Λ A Q → boxSize3D Q ≤ r →
      (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤
        C * (r : ℝ) ^ (2 + e₀)

/-! ## Open problem: two families in space -/

/-- **Open problem C.4**, Proposition 11.2 [OAI265, §11.2, eqs. (11.3) and (11.4)] on `ℤ³`, for
a collar exponent `ε` and a clearance exponent `β`: for fixed `D₀`, `C_tpl` and `n_* ≥ 1` there
is `C` such that every cut `A ⊆ Λ ⊂ ℤ³` with `b = |∂_Λ A| > 0` decomposes as
`A = D ∪ ⋃ᵢ Xᵢ`, disjointly, with `|D| ≤ C b`, nonempty `Xᵢ ⊆ A ∩ Tᵢ` for 3D templates `Tᵢ`
with parameters `(nᵢ, sᵢ)` separated from the cut, `nᵢ ≥ n_*`, `⌊nᵢ^{1-ε}⌋ ≤ sᵢ`,
`dist_∞(Tᵢ, Z_A) > 2 nᵢ^β`, `dist_∞(Tᵢ, ⋃_{j < i, f j = f i} X_j) > 2 nᵢ^β`, and
`∑ᵢ nᵢ^{-100} ≤ C b`.  Purely geometric.

Changed from `TwoFamilyDecomposition`: lattice notions and templates are their `3D` versions;
`β` and `ε` are parameters in place of `1 - 2·10⁻⁶` and `10⁻⁵`.  `AreaLawAssembly3D` needs it
with `β > 1`, which the planar construction never provides (`docs/3D/Targets.md`, §C.3). -/
def TwoFamilyDecomposition3D (ε β : ℝ) : Prop :=
  ∀ (D₀ Ctpl : ℝ) (nStar : ℕ), 1 ≤ nStar → ∃ C : ℝ,
    ∀ Λ A : Finset (ℤ × ℤ × ℤ), A ⊆ Λ → 0 < (edgeBoundary3D Λ A).card →
    ∃ (D : Finset (ℤ × ℤ × ℤ)) (m : ℕ) (X : Fin m → Finset (ℤ × ℤ × ℤ)) (f : Fin m → Fin 2)
      (T : Fin m → Finset (ℤ × ℤ × ℤ)) (n s : Fin m → ℕ),
      A = D ∪ Finset.univ.biUnion X ∧ (∀ i, Disjoint D (X i)) ∧
      Pairwise (Function.onFun Disjoint X) ∧
      (D.card : ℝ) ≤ C * (edgeBoundary3D Λ A).card ∧
      (∀ i, (X i).Nonempty ∧ X i ⊆ A ∩ T i ∧ nStar ≤ n i ∧
        IsTemplate3D Ctpl (n i) (s i) (T i) ∧ IsSeparatedFromCut3D D₀ (s i) Λ A (T i) ∧
        collarWidth3D ε (n i) ≤ s i ∧
        ENNReal.ofReal (2 * (n i : ℝ) ^ β) < ambientEDist3D (T i) (cutEndpoints3D Λ A) ∧
        ENNReal.ofReal (2 * (n i : ℝ) ^ β) <
          ambientEDist3D (T i) ((Finset.univ.filter fun j => j < i ∧ f j = f i).biUnion X)) ∧
      ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C * (edgeBoundary3D Λ A).card

/-! ## Target 5: the assembly -/

/-- **Target 5**, the assembly of [OAI265, §11.8] on `ℤ³`: for `1 ≤ q`, `0 < J`, `0 < Δ`, a
collar exponent `0 < ε < 1/2`, an integer `p ≥ 1` and a clearance exponent
`β > (2 - 2ε) (p + 1) / p`, the collar bound with exponent `ε`, amplification with
`θ = 2 - 2ε` and the two-family decomposition with exponents `ε`, `β` give the area law on
`ℤ³`.  The condition on `β` is what makes `L + 2r < 2 n^β` at large `n` when
`r ≤ C_M n^{(2 - 2ε)/α}`, the clearance that §11.8 uses for (11.3) and (11.4). -/
def AreaLawAssembly3D (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) : Prop :=
  1 ≤ q → 0 < J → 0 < Δ →
  ∀ (ε β : ℝ) (p : ℕ), 1 ≤ p → 0 < ε → ε < 1 / 2 →
    (2 - 2 * ε) / ((p : ℝ) / (p + 1)) < β →
    CollarBound3D 𝕜 q R J Δ ε → Amplification3D 𝕜 q R J Δ p (2 - 2 * ε) →
    TwoFamilyDecomposition3D ε β → AreaLaw3D 𝕜 q R J Δ

end OpenAI
