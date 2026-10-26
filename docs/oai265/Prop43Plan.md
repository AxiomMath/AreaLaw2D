# OAI265 Proposition 4.3 port plan

Target: the frozen proposition `OpenAI.PositiveReplacement` and theorem
`OpenAI.positive_replacement` in `OpenAI/Statements.lean`.  This plan was made before any
Proposition 4.3 proof code was written.

## Source revisions and scope

- Repository tip when planning: `be98eff` on `ruiz/oai265-prop43`.
- Read-only TNLean source: `LionSR/TNLean` at
  `fc565830cec69e8226e521d56c86d39845d45576` (2026-10-14), Apache 2.0.  The clone at
  `/home/ruiz/TNLean` was inspected only; it was not built.
- TNLean pins QICLean at `5f76b263e3a1c418645102d90f7bef6b92f04cf3`, Apache 2.0.  Its
  eight-file spectral-filter cone was inspected separately at that exact revision.
- The implementation will use Mathlib and Physlib declarations first, adapt only the proof cone
  needed here to Lean 4.33, and put the source repository, commit and Apache 2.0 attribution in
  every ported file header.
- No `Arealaw/` file, `OpenAI/TwoFamily*.lean`, or geometry file will be modified.  The frozen
  definitions and theorem statement in `OpenAI/Statements.lean` will not be changed.

## What TNLean actually proves

`TNLean/PEPS/AreaLaw/PositiveConstraints.lean` is a proof of Proposition 4.3, not an
assumption wrapper.  Its theorem `exists_positiveQuasilocalConstraints` chooses

```text
c_* = positiveNormalization p (Δ / 2) J
k_i = positiveConstraint c_* (centeredFilter p (Δ / 2) H Ω h_i)
```

and proves all of the following in its conclusion:

1. `0 ≤ k_i ≤ 1` and `k_i Ω = 0`;
2. `c_*⁻¹ (H-E₀) ≤ ∑ i, k_i`;
3. `(Δ/c_*) (1-P_Ω) ≤ c_*⁻¹ (H-E₀)`;
4. positivity, contractivity and the stretched-exponential tail for each graph-ball
   expectation; and
5. exact support in the connected component of the anchor.

The Hamiltonian filter and its lower bound are therefore proved, not assumed.  More precisely,
the spectral part is QICLean's theorem `SpectralFilter.positive_replacement`; the TNLean theorem
instantiates it and adds graph locality and component support.  There is no separate `H_F`
definition: the finite sum `∑ i, k i` is the paper's `H_F`.

`TNLean/PEPS/AreaLaw/QuasilocalRoots.lean` is downstream.  Its theorem `quasilocalRoots`
assumes a single positive contraction, its annihilation of `Ω`, and its conditional-expectation
tail, then proves Lemma 4.4 about square roots and channels.  It consumes Proposition 4.3; it
does not supply or assume away the Hamiltonian lower bound.  It will not be ported for this
target.

## Declaration-to-clause map

The table lists every TNLean declaration intended for direct use or adaptation.  Private helper
declarations travel with their containing ported theorem but are not an API dependency.

| Source declaration | Role in frozen `PositiveReplacement` |
|---|---|
| `QuantumCircuit.heisenbergEvolution`, `heisenbergEvolution_def` (`CommutatorRecursion`) | Time evolution used only to prove the localization tail. |
| `QuantumCircuit.heisenbergCommutatorNorm`, `norm_heisenberg_commutator_le_heisenbergCommutatorNorm`, `heisenbergCommutatorNorm_le_integral`, `continuous_heisenbergCommutatorNorm`, `heisenbergCommutatorNorm_zero_le`, `heisenbergCommutatorNorm_zero_of_disjoint` (`CommutatorRecursion`) | Recursive commutator estimate feeding the graph Lieb--Robinson bound, hence clause 4. |
| `norm_commutator_le`, `norm_exp_commutator_eq` (`CommutatorRecursion`) | Analytic matrix bounds inside the same clause-4 recursion. |
| `finite_volterra_le_weight_mul_exp`, `finite_volterra_zero_le_weight_mul_exp_sub_one`, `finite_rectangular_volterra_zero_le_weight_mul_exp_sub_one` (`Volterra`) | Solves the finite recursive inequality used for clause 4. |
| `QuantumCircuit.commute_heisenbergEvolution_of_closed` (`ComponentLocality`) | Exact commutation across graph components; after filtering and absolute value, gives clause 5. |
| `QuantumCircuit.norm_heisenberg_commutator_le_graphDistance`, `heisenberg_commutator_eq_zero_of_edist_eq_top`, `exists_graph_lieb_robinson` (`Circuit/LiebRobinson/GraphPropagation`) | Graph-distance commutator decay and exact disconnected-component vanishing, used for clauses 4 and 5. |
| `QuantumCircuit.sum_pow_mul_exp_neg_le`, `graphBall`, `mem_graphBall`, `norm_heisenberg_sub_siteExpectation_graphBall_le` (`GraphLocalization`) | Converts on-site commutator bounds to a conditional-expectation bound on `N_l(a)`, clause 4. |
| `latticeL1Distance_le_one_of_domainGraph_adj`, `card_domainGraph_sphere_le` (`PEPS/AreaLaw/GraphPropagation`) | Supplies the square-lattice sphere-growth hypothesis for clause 4.  These will be adapted to the Mathlib induced graph, not to a copied `domainGraph`. |
| `IsAdmissibleSupport.edist_le`, `IsAdmissibleSupport.card_le` (`PEPS/AreaLaw/GraphPropagation`) | Range and support-size hypotheses for clause 4.  Existing `mem_supports_iff_walk` and `card_le_of_mem_supports` replace them. |
| `LocalHamiltonian.sum_norm_term_containing_le`, `norm_sub_siteExpectation_graphBall_le` (`PEPS/AreaLaw/GraphPropagation`) | Uniform per-site interaction budget and its lattice specialization, clause 4.  These will be restated directly for `IsAdmissible`/`hamiltonian`. |
| `commute_filterIntegral_of_forall_commute` (`PositiveConstraints`) | Carries component commutation through the spectral filter, clause 5. |
| `positiveConstraint_mem_supportedOperators_component` (`PositiveConstraints`) | Exact component support, clause 5. |
| `localizationPrefactor`, `localizationPrefactor_nonneg` (`PositiveConstraints`) | Uniform constant entering clause 4. |
| `exists_positiveQuasilocalConstraints` (`PositiveConstraints`) | Final complex-valued assembly of clauses 1--5. |

Two inspected TNLean declarations are deliberately outside the port list:

- `GraphBallStabilization.graphBall_mono`, `notMem_graphBall_of_edist_eq_top`,
  `coe_graphBall_eq_reachable_of_sup_dist_le`, and `exists_graphBall_eq_reachable` are not in
  the `PositiveConstraints` dependency cone; component support is proved directly by
  `ComponentLocality`.
- `QuasilocalRoots.sqrt_mul_exp_neg` and `quasilocalRoots` serve Lemma 4.4, after Proposition
  4.3, and are not needed to discharge the frozen proposition.

The QICLean declarations reached by TNLean, and their clauses, are:

| Source declaration group | Role |
|---|---|
| `SpectralFilter.profile` through `spectralCutoff` (`Profile`, `Cutoff`) | Smooth compactly supported frequency cutoff used in clauses 1--4. |
| `spectralKernel`, its Fourier inversion and decay estimates (`Kernel`, `Inversion`, `Decay`) | Real even time kernel and stretched-exponential decay, clause 4. |
| `filterIntegral`, `filterIntegral_self`, `filterIntegral_mulVec_of_gap` (`MatrixFilter`) | Filtered local terms, preservation of the sum, and annihilation of the ground state, clauses 1--3. |
| `centeredFilter`, `positiveConstraint`, `positiveNormalization`, `positive_replacement` (`PositiveReplacement`) | Constructs the positive contractions and proves both `H_F` inequalities, clauses 1--3. |
| `kernelExponent`, `exists_norm_filterIntegral_sub_map_le`, `norm_abs_sub_map_abs_le`, `exists_norm_positiveConstraint_sub_map_le` (`FilterLocality`) | Turns Lieb--Robinson localization into `C exp (-c l^(p/(p+1)))`, clause 4. |

## Model differences and bridge lemmas

TNLean and the frozen statement describe the same finite tensor product, but not with the same
surface encoding.  The port will not introduce a second public lattice/Hamiltonian model.

### Domain graph and supports

- TNLean's `Site Λ` is the subtype `↥Λ`; ours keeps ambient sites `ℤ × ℤ` plus subset proofs.
- TNLean's hand-written `domainGraph Λ` lives on `↥Λ`; ours uses
  `(hasse ℤ □ hasse ℤ).induce Λ`, and `domainEDist` is totalized to `⊤` outside `Λ`.
- TNLean's admissible support is a `Finset (Site Λ)` with pairwise bounded walks.  Ours is an
  ambient `Finset` in `supports Λ R`, with `domainEDiam ≤ R`.

Existing bridges `squareLattice_adj_iff`, `mem_supports_iff_walk`,
`exists_walk_length_le_iff_edist_le`, `domainEDist_of_mem`, `graphNbhd_subset`, and
`domainComponent_subset` cover adjacency, walks and subsets.  New lemmas needed are:

1. subtype/ambient membership and edistance rewrites for the induced graph;
2. the exact correspondence between the generic graph ball on `↥Λ` and
   `graphNbhd Λ {a} l`;
3. a sphere-cardinality bound for the induced square lattice; and
4. a reachable-set/domain-component correspondence.

### Hamiltonian and supported operators

- TNLean packages one full-domain term per admissible support in `LocalHamiltonian`; ours has a
  total local family `Φ X`, an `IsAdmissible` predicate, and inserts terms with `extendId`.
- TNLean's `supportedOperators` is a span of product operators.  Ours says directly that a
  matrix equals `extendId` of a local matrix.

Existing `isSupportedOn_iff_mem_span`, `isSupportedOn_extendId`,
`IsSupportedOn.commute`, `IsAdmissible.hamiltonian_eq_sum_supports`,
`IsAdmissible.isHermitian_extendId`, `IsAdmissible.norm_extendId_le`,
`card_le_of_mem_supports`, and `card_filter_mem_supports_le` provide most of this bridge.  New
lemmas needed are:

1. a finite-indexed term family over `↥(supports Λ R)` whose sum is `hamiltonian Λ Φ`;
2. the per-site norm budget
   `∑_{X containing x} ‖extendId (Φ X)‖ ≤ 2^((2R+1)^2) J`; and
3. support monotonicity/closed-component forms specialized to ambient regions.

The coarser box constants already proved in `OpenAI/SupportCounting.lean` replace TNLean's
diamond constants.  Proposition 4.3 permits any constants depending only on `R` and `J`.

### Conditional expectation

- TNLean's `siteExpectation q K` is written on configurations of the subtype domain using a
  hand-written partial trace and site embedding.
- The frozen conclusion uses `condExpect h`, namely normalized `Arealaw.ptrace` followed by
  `extendId`, on ambient regions.

The port will prove directly for `condExpect`: linearity, preservation of `1`, positivity,
order preservation, operator-norm contraction, fixed points on supported operators, and the
commutator-to-localization inequality.  The finite Weyl-average argument from TNLean
`SiteExpectation.lean` is the fallback only where Mathlib/Physlib has no conditional-expectation
norm theorem.  A bridge will identify the graph-ball specialization with exactly the
`condExpect (graphNbhd_subset ...)` occurring in the frozen proposition.

### Vectors, gap, and scalar field

- TNLean uses `EuclideanSpace ℂ` and `WithLp.ofLp`; ours states vectors as functions and the
  gap in Loewner order over every `RCLike 𝕜`.
- `normalized_eigen_hasGlobalGap_iff_euclidean` and the matrix-order lemmas in
  `OpenAI/Embedding.lean` already bridge the complex gap.

The Lieb--Robinson time evolution and QICLean spectral integral will be proved over `ℂ`.
The final objects cannot be transferred merely by applying an existential complex theorem:
for real-like `RCLike` fields an arbitrary complex matrix has no preimage.  The implementation
must therefore construct the filtered Hermitian operator and its absolute value in a form that
is defined over the source field, then prove that its `toComplex` image is the complex object.
Mathlib's generic `Matrix.IsHermitian.cfc`/spectral theorem is the first choice for the absolute
value; the even real spectral kernel supplies the required real-form lemma for the filter.  New
embedding lemmas will cover `condExpect`, support, the filtered operator, Hermitian absolute
value, and the resulting `k`.  Once `k` is known to map to the complex construction, positivity,
Loewner inequalities, norms, sums, annihilation, and tails reflect through
`OpenAI/Embedding.lean` exactly as in Tier 2.  This is the main technical risk and will be done
before final assembly.

## Implementation steps

Each numbered step ends with `lake build OpenAI`, `lake env lean OpenAI/Audit.lean`, a commit,
and a push to `origin ruiz/oai265-prop43`.  New headline theorems are enrolled in
`OpenAI/Audit.lean` in the same step that proves them.

1. **Conditional expectation API.**  Add the algebraic/order/norm/fixed-point lemmas for the
   existing `condExpect`; no new expectation definition.
2. **Spectral filter.**  Port the eight-file QICLean spectral-filter cone at `5f76b263`, using
   Mathlib/Physlib equivalents where available.  Keep the positive-replacement and locality
   theorems separated so the `H_F` inequality is independently auditable.
3. **Generic graph Lieb--Robinson bound.**  Port/adapt TNLean
   `CommutatorRecursion`, `Volterra`, `ComponentLocality`, `GraphPropagation`, and
   `GraphLocalization` at `fc565830`.  Use `IsSupportedOn` and `condExpect` rather than adding
   TNLean's public encodings.
4. **Square-lattice specialization.**  Prove the sphere, support-size and per-site-budget
   hypotheses from `OpenAI/Basic.lean`, `Bridges.lean`, and `SupportCounting.lean`; specialize
   the generic localization bound to `hamiltonian Λ Φ`.
5. **Positive constraints over `ℂ`.**  Adapt TNLean `PositiveConstraints.lean`, obtaining a
   complex theorem matching every conjunct of the frozen proposition.
6. **`RCLike` construction and transfer.**  Establish the real-form/embedding lemmas for the
   constructed constraints and transfer the complex estimates to arbitrary `RCLike 𝕜`.
7. **Final theorem.**  Prove `OpenAI.positive_replacement` in a new module, remove only its
   original `sorry` stub from `Statements.lean` if required by the established project pattern,
   regenerate `OpenAI.lean`, update `Memory.md`, enrol the result in `Audit.lean`, and run
   `#print axioms OpenAI.positive_replacement`.

If the spectral filter requires a definition whose existence cannot be proved without a
sorried structure, work stops at that point as required.  No use of Lemma 4.4, Schur--Weyl,
replicas, or Sections 5--10 is planned.

## Estimate

- Conditional expectation and lattice bridges: 1--2 hours.
- Spectral-filter port and Lean 4.33 adaptation: 2--3 hours.
- Generic and lattice Lieb--Robinson port: 2--3 hours.
- Positive-constraint assembly: 1 hour.
- Real-form/`RCLike` transfer and final audit: 2--3 hours.

Total estimate: **8--12 hours**, with the real-form lemma for the filtered operator the largest
uncertainty.  The hard stop remains 12 hours of wall time or any earlier stop condition in the
campaign brief.
