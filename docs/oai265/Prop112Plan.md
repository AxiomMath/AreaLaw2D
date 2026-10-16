# Proposition 11.2 port and proof plan

Target: the frozen proposition `OpenAI.TwoFamilyDecomposition` and theorem
`OpenAI.two_family_decomposition` in `OpenAI/Statements.lean`, corresponding to Proposition
11.2 of OpenAI, *A two-dimensional area law from a global spectral gap*, Section 11
(`10-geometry.tex`).  This work is purely geometric.  It does not use or modify Hamiltonian,
operator, entropy, or BH12 (`Arealaw/`) files.

This plan was prepared before starting any Proposition 11.2 proof code.

## Fixed sources and scope

- Local branch at planning time: `ruiz/oai265-prop112`, commit
  `be98eff4ad1c921177fb71a7b1689c700032f7f4`.
- Read-only TNLean clone: `/home/ruiz/TNLean`, branch `main`, clean at
  `fc565830cec69e8226e521d56c86d39845d45576` (2026-10-14).  It is Apache 2.0.  It will not be
  built or modified.  Every adapted source file will retain an attribution header naming this
  commit and the Apache 2.0 license.
- Paper source: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
  `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`,
  especially lines 89--131 (statement), 137--344 (layers, belts, initial stars), 346--615
  (repairs and birth separation), and 621--743 (counting, templates, and final assembly).
- Frozen local statement: no change to `TwoFamilyDecomposition`, `IsTemplate`,
  `IsSeparatedFromCut`, `collarWidth`, `ambientEDist`, `cutEndpoints`, or `edgeBoundary` is
  planned.  `Statements.lean` will only be edited at the end to move the theorem body to the
  proving module, following the existing project pattern.  `Audit.lean` will only be edited at
  the end to enrol newly proved headline declarations.
- `TNLean/PEPS/AreaLaw/Geometry/NestedPatches.lean` is not in this port.  It belongs to the
  separate polynomial-PEPS nested-square patch argument.  The “nested neighborhoods” used here
  are `dyadicNeighborhood` and `dyadicNeighborhood_subset_succ` from `DyadicLayers.lean`.

## Convention bridges required before assembly

The port will use Mathlib and the already frozen OpenAI notions rather than install TNLean or
introduce a second public encoding.

1. **Integer embedding and sup metric.**  Add local geometry lemmas identifying
   `((z.1 : ℝ), (z.2 : ℝ))` distances with the product sup metric on `ℤ × ℤ`, and convert
   pointwise real inequalities into `edist`/`ENNReal.ofReal` inequalities.  Use the existing
   `OpenAI.ambientEDist_eq_inf`, `le_ambientEDist_iff`, and `lt_ambientEDist_iff` from
   `OpenAI/Rectangles.lean`.  TNLean's `DistanceLayers` uses real-valued `dist` on `ℝ × ℝ`;
   the frozen proposition uses `ambientEDist : ENNReal` on lattice points.
2. **Cut endpoints and boundary count.**  Parameterize the geometry by the ambient finite set
   `Z := cutEndpoints Λ A`, instead of carrying TNLean's `A : Finset (Site Λ)` and
   `boundaryEndpoints`.  Reuse/prove in the geometry cone the elementary bound
   `Z.card ≤ 2 * (edgeBoundary Λ A).card`.  TNLean uses an unordered
   `Finset (Sym2 (Site Λ))`; ours uses ordered pairs directed from `A` to `Λ \ A`.  Existing
   `card_image_mk_edgeBoundary` and `mem_image_mk_edgeBoundary` show that ours counts every
   unordered crossing edge once.  This avoids making the TNLean subtype boundary a second
   public definition.
3. **Ambient dilation.**  Prove the equality between the frozen Minkowski-sum definition
   `T + Finset.Icc (-r,-r) (r,r)` and TNLean's `T.biUnion` of coordinate intervals, or adapt
   `CellCounting` directly to the frozen definition.  All later cell counts must be stated for
   `OpenAI.ambientDilation`.
4. **Allowed slopes.**  TNLean's `IsAllowedSlope u` lists
   `u.1 = 0 ∨ u.2 = 0 ∨ u.1 = u.2 ∨ u.1 = -u.2`; frozen
   `HasTemplateSlope u` lists the same four cases with coordinates/equalities reversed.
   Prove an iff and use `HasTemplateSlope` in exported results.
5. **Template pieces.**  Adapt TNLean's concrete triangle/rectangle constructors only as
   internal witnesses for frozen `IsTemplatePiece`.  Bridge pointwise max-distance bounds on a
   polygon to `Metric.ediam P ≤ (s : ENNReal)`, and pointwise lattice diameter bounds to
   `Metric.ediam (T : Set (ℤ × ℤ)) ≤ (n : ENNReal)`.  Then prove one constructor theorem
   assembling frozen `IsTemplate Ctpl n s T` from a finite list of nondegenerate TNLean-style
   pieces, exact lattice sampling, cover, scale, and diameter data.  No `Template` existence
   structure with a deferred proof will be introduced.
6. **Strict clearances.**  Prove the pointwise equivalence, including empty-set behavior,
   between TNLean-style
   `∀ x ∈ T, ∀ z ∈ Z, c < dist (integerPoint x) (integerPoint z)` and
   `ENNReal.ofReal c < ambientEDist T Z`.  This bridge supplies both frozen
   `IsSeparatedFromCut` and the two later `ambientEDist` conjuncts.
7. **Exponents and collar.**  Identify TNLean `Exponents.beta`, `geometryDelta`, `zeta`,
   `rho` and `boxError` with the literal exponents in the frozen statement.  Add eventual
   threshold lemmas for `collarWidth n ≤ s`, `2 * n^beta` clearance, and `nStar ≤ n`; TNLean
   proves the underlying exponent gaps and some scale ratios but does not state the frozen
   `Nat.floor` collar conclusion.
8. **Finite indexing.**  Convert the finite set of retained identifiers to `Fin m`, preserving
   the paper's order (primaries, then initial belt tiles, then replacements by generation), and
   prove that TNLean-style pairwise disjointness is exactly the frozen
   `Pairwise (Function.onFun Disjoint X)` and filtered earlier-family union.

## Port list

The useful proved cone at TNLean HEAD has 69 geometry modules and about 11,500 lines.  The port
will be staged; each stage builds, updates this plan/memory if its route changes, and is committed
and pushed before the next begins.

### A. Scalar, cells, layers, distance, and sparse belts

- `Exponents`, `CellCounting`, `DyadicOrigin`, `DyadicLayers`, `DyadicClosure`,
  `DyadicExhaustion`, `DyadicRefinement`, `LayerPartition`.
- `DyadicScales`, `DistanceLayers`, `SparseBelts`, `FineBelts`, `ScaleSeparation`.
- `PolynomialBudget`, `SimultaneousRepair`, `RepairDepth` (only their actually proved scalar and
  set-theoretic contents; see the open-work section below).

Principal declarations to preserve/adapt include `dyadicCellIndex`, `dyadicCell`,
`dyadicNeighborhood`, `dyadicNeighborhood_subset_succ`, `dyadicLayerIndices`,
`dyadicLayer_eq_iUnion`, `card_dyadicLayerIndices_le`, `closure_dyadicCell`,
`closure_dyadicLayer_eq_iUnion`, `iUnion_dyadicNeighborhood_eq_univ`,
`dyadicLayer_pairwiseDisjoint`, `dyadicNeighborhood_union_iUnion_layers_eq_univ`,
`fineLayerIndices`, `dyadicLayer_eq_iUnion_fine`, `card_fineLayerIndices`,
`dyadicLayer_infDist_bounds`, `dyadicLayer_dist_nonadjacent`,
`exists_sparse_dyadic_belt_shift`, `exists_dyadicScale_side_ratios`,
`exists_uniform_polynomial_dyadic_sum_bound`, `repairHalfSide` and its margin bounds,
`exists_repair_descendant_count_layer_bound`, and `eventually_fine_clearance`.

### B. Primary regions and fine-cell coverage

- `PrimaryRegions`, `PrimaryFragments`, `PrimaryCounting`, `NonbeltPrimaries`,
  `FineCellPartition`, `PrimaryFineCellCover`, `LocalLayers`.

The main outputs are the exact primary-fragment union, closed-rectangle form and diameter,
primary birth-region diameter and within-layer separation, primary counts, unique assignment of
nonbelt fine cells, and fine-cell exhaustion outside the dummy neighborhood.

### C. Cell contacts, side matching, fans, and colours

- `AdjacentScales`, `MeshGeometry`, `AllowedSlopeAffineLine`.
- `CellFans`, `CellFanCycle`, `CellFanRays`, `CellFanSectors`, `CellFanSlopes`, `CellSides`,
  `SideEndpoints`, `SideSubdivision`, `SideSubdivisionMask`.
- `CellContacts`, `ActualSideMatching`, `ElementarySideOpponents`,
  `ElementarySideOpponentUniqueness`, `ElementarySideReciprocity`.
- `FanRuns`, `FanRunContacts`, `FanSideContacts`, `FanRegularity`, `FanFrontiers`.
- `BeltFanColors`, `BeltRunInterfaces`, `BeltMarks`.

These prove the exact side subdivision, unique reciprocal opponent, at-most-eight triangular fan,
allowed slopes, fan cover/intersection formulas, run merging, opposite colours across nontrivial
interfaces, and the at-most-nine initial marks per selected belt cell.  They do not prove the
recursive repair invariant.

### D. Initial regions and initial isolated-star ingredients

- `DummyContacts`, `DummyCorners`, `DummyRunInterfaces`, `NearMarkGeometry`,
  `FineMarkSeparation`.
- `InitialRegions`, `InitialRegionInteriors`, `InitialRegionBoundaries`,
  `InitialRegionInterfaces`, `InitialRegionRegularity`, `InitialLatticePartition`.
- `InitialStarFrontiers`, `InitialSectorAssignment`, `InitialSectorColors`,
  `InitialSectorCycle`, `InitialSectorRuns`, `InitialActiveRays`, `InitialActiveRayCount`,
  `ConcentricFans`, `InitialMarkFamily`.

The high-level outputs are finite sparse initial marks with a uniform boundary count,
quarter-scale separation, local allowed radial frontiers with alternating colours, closure/open
regularity, pairwise-disjoint initial open regions, and unique coverage of every lattice point.

`Templates.lean` is a source reference for the geometric polygon construction, but its public
`Template` and `OrderedTwoFamilyPartition` structures will not be copied: the target already has
the frozen `IsTemplate` predicate and explicit `D,m,X,f,T,n,s` witnesses.

## Map to every frozen conjunct

| Frozen conclusion | Proved source material | Remaining assembly or open mathematics |
|---|---|---|
| `A = D ∪ univ.biUnion X`, `Disjoint D (X i)`, pairwise `X` | Exact layer/fine-cell exhaustion; `initialBirthRegions_cover`; `initialOpenRegion_pairwise_disjoint`; `exists_unique_initialOpenRegion_integerPoint`; supporting boundary-avoidance lemmas | Must construct every repair generation and final actual regions, prove final coverage/disjointness, then restrict to identifiers meeting finite `A` and enumerate them. Open in TNLean. |
| `D.card ≤ C * edgeBoundary.card` | `card_dyadicLayerIndices_boundary_le`; sparse belt/mark estimates; descendant-depth/count bounds; uniform polynomial dyadic sum | Must relate actual repair nodes and terminal squares to the scalar descendant tree, and count the dummy plus terminal lattice sites. `geometry:total-repairs` is not proved by TNLean. |
| `(X i).Nonempty` and `X i ⊆ A ∩ T i` | Initial lattice partition and birth/open-region closure facts | Define `X_i := A ∩ actual_i`, discard empty identifiers, and prove `actual_i ⊆ birth_i` for recursive replacements. Final construction is open. |
| `nStar ≤ n i` | Exponent gaps, scale separation, repair thresholds | Choose scanner constants and thresholds in the paper's order and prove them uniformly for primary, belt, and replacement tiles. |
| `IsTemplate Ctpl (n i) (s i) (T i)` | Primary fragment rectangle cover/count/diameter; fan triangles, allowed slopes and at-most-eight count; initial region regularity | Apply the template bridge. Replacement birth sectors and their triangle decompositions still need construction; the three tile classes then need one uniform assembly. |
| `IsSeparatedFromCut D₀ (s i) Λ A (T i)` | Layer endpoint lower bounds; primary diameter/placement; scalar descendant displacement bounds | Primary case is a bridge/threshold argument. Belt/replacement cases need the actual descendant-location invariant, absent upstream. |
| `collarWidth (n i) ≤ s i` | Exact exponent gaps and scale ratios | New eventual-floor lemmas and the uniform threshold choice for all three tile classes. |
| Cut clearance `2*n_i^beta < ambientEDist T_i (cutEndpoints Λ A)` | `dyadicLayer_dist_lower`/`dyadicLayer_infDist_bounds`, `LocalLayers`, scale gaps | Primary case follows after thresholding. Descendant birth templates require the missing repair displacement theorem. |
| Earlier same-family clearance | Primary within-layer belt gap and nonadjacent-layer separation; opposite colours on positive-length initial interfaces; initial contact localization | The entire birth-separation lemma is open in TNLean. It must compare each full birth region with final earlier/peer actual regions after later trimming. |
| `∑ i (n i ^ 100)⁻¹ ≤ C * edgeBoundary.card` | Primary counts, sparse belt decay, repair descendant count, summable polynomial budget | Must bound actual repair tiles by descendant nodes and split the sum into primaries and the `O(b)` belt/replacement family after final enumeration. |

## Work still open in TNLean, and the paper's proof route

1. **Simultaneous repairs / Lemma 11.4 (`geometry:repair-induction`).**  TNLean's
   `SimultaneousRepair.lean` currently defines `repairSquare`, the common removal union,
   remnants, nine child locations/scales, and proves the scalar half-side estimates.
   `RepairDepth.lean` proves only depth/count and fine-clearance inequalities.  There is no
   generation-indexed repair state, replacement region construction, invariant, or theorem that
   actual repairs obey those counts.

   The paper chooses a fixed small `a₀` and large `SStar`.  At each generation it simultaneously
   removes every active mark's closed square from every old identifier, creates oppositely
   labelled sectors inside each nonterminal square, and makes the center/corners/midpoints the
   next marks.  The induction uses `6*d(S)` containment in the parent star, separation of removal
   squares from `a₀*max(S,T)`, and a normalized finite configuration consisting of eight radial
   rays plus four square support lines.  Child stars inherit one uniform `a₀`; geometric shrinkage
   gives terminal-square avoidance and total descendant displacement `< 2*d(S)`; `rho < 1`
   gives finite termination.  The native implementation should use explicit finite generations
   and finite identifier types, not a structure whose existence is postulated.

2. **Birth-template separation / Lemma 11.5 (`geometry:birth-separation`).**  No TNLean theorem
   establishes this.  The paper compares an initial belt/replacement birth closure with old
   remnants after the same generation's removal and with peer replacements.  Outside a bounded
   normalized box distance is already `≥ 2u`.  Inside, only finitely many affine quarter-mesh
   patterns occur.  Away from small contact squares compactness gives a uniform positive
   multiple of `u`; inside a contact star, disjoint sets of the eight ray directions have angle
   at least `pi/4`, yielding an angular gap.  The next trim removes radius
   `c4*u^rho` from the older/peer identifier, so final same-label actual regions are at least
   `c1*u^rho` from the whole new birth region.  The Lean proof should make the finite direction
   patterns explicit where possible; a bare appeal to an unconstructed finite-pattern type is
   not acceptable.

3. **Full partition and Proposition 11.2.**  TNLean does not define the final repaired family or
   prove the proposition.  Following paper lines 621--743, prove actual descendant counts,
   finiteness, the `O(b)` dummy/terminal residual, and template data for: primaries with
   `s0=2^k`, `n=ceil(CP*(2^k)^(1+2*delta0))`; belt tiles with `s0=u`,
   `n=ceil(CB*u)`; replacements with `s0=2u`, `n=ceil(CB*u)`.  Fix constants in the paper's
   order (`C0,CP,CB,a0`, then `SStar`, then `k0`).  Retain only identifiers whose final actual
   region meets `A`, enumerate them in the required order, set `X_i` to that intersection, and
   discharge the residual, two clearance clauses, collar, and `n^-100` sum separately by tile
   class.

## Verification, commits, and estimate

- Each port stage gets `lake build OpenAI`; each new proved public declaration gets a local
  `#print axioms` check.  Only the final headline proof is enrolled in `OpenAI/Audit.lean`, unless
  an intermediate theorem is intentionally exported as a stable OpenAI API.
- Each stage is a separate commit pushed explicitly to
  `origin ruiz/oai265-prop112`.  `OpenAI.lean` is regenerated only when a new module is ready.
- Expected porting effort for the directly useful proved cone: roughly 20--35 hours, dominated
  by the fan/initial-region modules and Lean 4.35-to-4.33 API adjustments.  The genuinely open
  repair, birth-separation, and final assembly are estimated at an additional 35--70 hours.
  The present run's 12-hour stop therefore most likely reaches a pushed foundational port rather
  than a complete Proposition 11.2.  This estimate is based on the 69-module/11.5k-line proved
  cone and the absence of the three decisive upstream theorems, not on build time.


## Native route for the open parts (autopilot run, 2026-10-14)

Sources re-verified on this machine: `/home/ruiz/TNLean` does not exist here, but the same
repository is public at `github.com/LionSR/TNLean` (cloned read-only into a gitignored scratch
directory, never pushed to).  Its HEAD (`61bb695d0`) adds only `PowerScaleDepth.lean` and small
changes to `RepairDepth.lean`/`InitialMarkFamily.lean` to the geometry since `fc565830`; the
repair induction, birth separation and assembly are still absent upstream.  The paper section
was fetched read-only from `openai/math@adc7f124` (`10-geometry.tex`).

The three open parts are formalized natively, without the paper's compactness argument:

1. **Octant stars** (`Geometry/Octants.lean`).  The eight closed sup-norm octants about a point;
   inside a closed ball of radius `d` they are the all-midpoint fan triangles.  Explicit
   clearance with constant `1/2`: the angular gap between non-adjacent octants, and the ray-hit
   clearance once the hit point is trimmed.  `childOctant` tabulates, for each of the nine
   children of a removal square, which parent octant (inside or outside) each child octant is;
   checked numerically before freezing (`mem_octantConeAt_child_iff`, radius `R < d/2`).
2. **Repair tree** (`Geometry/RepairTree.lean`).  Marks are `(root, path of offsets)`; scale
   `d^[gen] S₀`, position by recursion.  Separation invariant, descendant displacement `< 2d`,
   finiteness, descendant count.
3. **Repair regions** (`Geometry/RepairRegions.lean`).  Identifiers `init i | repl m old`; the
   replacement `repl m old` fills the inner octants of `m` whose outer identifier is `old`, with
   the opposite label (runs merge automatically).  Removal is by *open* squares so all regions
   are closed; lattice points never lie on a square boundary, so the lattice sets agree with the
   paper's.  Lemma 11.4 is `currentRegion_inter_closedBall`: at every mark the current regions
   form an octant star of radius `a₀ S`.
4. **Separation** (`Geometry/RepairSeparation.lean`, `Geometry/BeltSeparation.lean`).  Lemma 11.5
   with explicit constants: replacements `d(u)/2`; belt runs `r₀/2` for marks trimmed by
   `r₀ ≤ t/4096`, via the stars at the nine cell marks and the elementary-segment opponents.
5. **Lattice partition** (`Geometry/RepairPartition.lean`): disjointness and coverage on the
   lattice, birth regions within `2 d(S₀)` of their initial mark.
6. **Instantiation, templates, scales, counting** (`Geometry/InitialRepairSetup.lean`,
   `Geometry/TwoFamilyTemplates.lean`, `Geometry/TwoFamilyScales.lean`,
   `Geometry/TwoFamilyCounting.lean`), and the assembly `OpenAI/TwoFamilyDecomposition.lean`
   (`two_family_decomposition`, moved out of `Statements.lean` once proved, as for
   `two_family_cancellation`).

Order of tiles: primaries, belt runs, replacements by generation (rank `0`, `1`, `gen + 2`).
Constants: `a₀ = 1/64` (initial stars of radius `t/64`), `S_*`, `C_B` from
`exists_twoFamily_constants`, then `k₀`.

## Status (2026-10-15)

Proposition 11.2 is proved: `OpenAI.two_family_decomposition` in
`OpenAI/TwoFamilyDecomposition.lean`, enrolled in `OpenAI/Audit.lean`, axioms
`[propext, Classical.choice, Quot.sound]`.  The three parts listed above as open upstream
(Lemma 11.4, Lemma 11.5, final assembly) are proved natively by the route above.
