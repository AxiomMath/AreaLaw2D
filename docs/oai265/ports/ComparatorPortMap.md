# Port map for the Proposition 8.1 comparator closure

Source list: `comparator_closure.txt` (264 modules). `TNLean.PEPS.AreaLaw.GlobalSchmidtBellRoughUpper` (122 lines; imports GlobalSchmidtBellPrevector and ReplicaPrevectorRoughUpper) is a further comparator root that is neither in the list nor ported; its dependencies are all in the list. Sources: TNLean `74ecad48c`, QICLean `e44381d9`. Repo: OpenAI/, Arealaw/, and `.lake/packages` (Mathlib, Physlib).

Method. (1) Every non-private declaration name of each source file was looked up in OpenAI/ and Arealaw/ (full name, and last component when ≥ 13 characters) and in Mathlib/Physlib (full name). (2) Each closure declaration was looked up in QICLean `5f76b263` and `32a5a1a8` in any *other* file (to catch ports of moved declarations): no hit. (3) The 15 closure files absent at `5f76b263` were checked with `git log --follow`: all were created after it, none renamed. (4) Header citations of every OpenAI/Arealaw file were grepped for each source path: no missed port. (5) Concept-level search for the general-purpose files (trace norm, fidelity, Uhlmann, Klein, condExpect, root channels, lattice constraints, two families, templates). (6) `cone` = declarations reachable by name from the declarations of the roots (Scan.ActualSharpUpper, Scan.ActualRoughUpper, GlobalSchmidtBellRoughLower, GlobalSchmidtBellPrevector) / declarations in the file; 0 means nothing in the file is referenced by name from that cone. Name reachability misses `@[simp]`/instance/notation use, so check those before skipping a file.

Flags: `SSA` = the file exists for strong subadditivity; `relative entropy` = relative-entropy machinery (the repo already has SSA, `Arealaw.vonNeumann_strong_subadditivity`).

| module | lines | verdict | OpenAI module / evidence | cone | notes |
|---|---|---|---|---|---|
| QICLean.Algebra.DependentBlockDiagonal | 316 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/13 | Not referenced by name from the roots. |
| QICLean.Algebra.FinSum | 230 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/7 |  |
| QICLean.Algebra.FiniteKroneckerOrder | 89 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Algebra.HermitianHelpers | 529 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/22 | Cone uses only `one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one` (ReplicaDefect). |
| QICLean.Algebra.KroneckerFactorPositivity | 481 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/14 | Hosts the definition `Matrix.finKronecker` used throughout the replica files. |
| QICLean.Algebra.MatrixGramUnitary | 261 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/5 |  |
| QICLean.Algebra.MatrixIsometryKronecker | 33 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Algebra.MatrixProductIntertwine | 42 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Algebra.MatrixReindexUnitary | 36 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 | Physlib `Matrix.reindex_one_mem_unitaryGroup` covers only the identity. |
| QICLean.Algebra.MatrixUnitaryBetween | 292 | PARTIAL | Physlib QuantumInfo.ForMathlib.Isometry `Matrix.Isometry`, `mem_unitaryGroup_iff_isometry`, `reindex_one_isometry` | 6/13 | Defines a parallel `IsIsometry`/`IsCoisometry`/`IsUnitaryBetween`; decide once whether ports use Physlib's `Matrix.Isometry` (cone uses `IsIsometry`, `isUnitaryBetween_iff_mem_unitaryGroup`, `reindex`). |
| QICLean.Algebra.OperatorBlock | 40 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/2 | Not referenced by name from the roots. |
| QICLean.Algebra.OperatorSchmidt | 274 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/13 | Not referenced by name from the roots. |
| QICLean.Algebra.PerronFrobenius.RankOne | 723 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/22 | Not in the cone. Only reached through MatrixTraceInequalities (`trace_sq_eq_sum_eigenvalues_sq`), itself not in the cone. |
| QICLean.Algebra.PiProductTrace | 32 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Algebra.PositiveSemidefiniteNormalization | 125 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/5 |  |
| QICLean.Algebra.ProjectionRangeIsometry | 47 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Algebra.TensorPowerPartialTrace | 53 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/2 | Not referenced by name from the roots. |
| QICLean.Analysis.EntropyDecomposition | 492 | PARTIAL | OpenAI.ConditionalEntropy `vonNeumann_blockDiagonal`; OpenAI.EntropyMixing `vonNeumann_smul`; Arealaw.VonNeumann `vonNeumann_submatrix_equiv`; Arealaw.Kronecker `EE_kronecker_add` | 0/14 | FLAG SSA: written for the Hayashi SSA-equality direction. QICLean `vonNeumannEntropy` = `Arealaw.vonNeumann` (cf. OpenAI.FiniteProductInformation). TypicalDensity imports it for `vonNeumannEntropy_diagonal`, `vonNeumannEntropy_units_conj` (missing by name, short); not referenced from the roots by name. |
| QICLean.Analysis.ExponentialPolynomialAbsorption | 64 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.FiniteExponentialRetainedMass | 90 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.FiveFactorAuxiliaryCoordinates | 112 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.FloorPin | 60 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/2 |  |
| QICLean.Analysis.GaussianFilter.Kernel | 151 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/15 | Cone does not reach it: the only declaration downstream code uses from the GaussianFilter chain is `reindex_exp` (GaussianFilter.Reindex). |
| QICLean.Analysis.GaussianFilter.MatrixIntegral | 294 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/22 | Not in the cone (see Kernel). Unrelated to OpenAI.SpectralFilter (spectral cutoff, not Gaussian). |
| QICLean.Analysis.GaussianFilter.Reindex | 93 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/6 | Cone uses only `reindex_exp` (reindex e e (exp A) = exp (reindex e e A), 4 lines via `NormedSpace.map_exp`); port that lemma alone, not the Gaussian chain (538 lines). Physlib has it only for `HermitianMat` (`HermitianMat.reindex_exp`). |
| QICLean.Analysis.IidTailThreshold | 76 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.InversePowerLogJensen | 108 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.IsometricDomainExtension | 164 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/12 | Cone uses only `norm_toLp_mulVec_of_isometry`. |
| QICLean.Analysis.IsometricIntertwiningCommute | 52 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.KleinInequality | 855 | PARTIAL | Physlib QuantumInfo.Entropy.Relative `inner_log_sub_log_nonneg`, `qRelativeEnt` (MState/HermitianMat encoding) | 4/22 | FLAG relative entropy: Klein's inequality exists in Physlib's encoding. The cone uses only four eigen-expansion helpers (`trace_diag_conj`, `re_trace_mul_cfc_eq_double_sum`, `trace_mul_cfc_eq_double_sum`, `row_sum_normSq_eq_one`) via RootFidelityRelativeEntropy; port those, not the 855 lines. |
| QICLean.Analysis.KroneckerExponential | 88 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/5 | OpenAI.CfcKronecker `cfc_kronecker_one` covers the Hermitian case only. |
| QICLean.Analysis.KyFanNorm | 503 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/21 | Not in the cone (MaximalOverlap uses it only in declarations the cone does not reach). |
| QICLean.Analysis.MarginalSupport | 347 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/15 | FLAG SSA: written to put (1_A/d_A) ⊗ ρ_BC in the domain of relative entropy for SSA-from-DPI. Cone uses only `proj_mul_eq_zero_of_trace_eq_zero`. |
| QICLean.Analysis.MatrixFramePerturbation | 124 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/4 |  |
| QICLean.Analysis.MatrixSqrt | 929 | PARTIAL | Arealaw.Fidelity `conjTranspose_cfcSqrt`, `cfcSqrt_diagonal`, `cfcSqrt_fromBlocks_zero`; OpenAI.PosSemidefSupport `PosSemidef.supportProj`; OpenAI.CfcKronecker `cfc_kronecker_one` | 10/52 | Missing: the `supportInvSqrt` / `supportInv` / `supportInvExtension` family, `PosSemidef.sqrt_kronecker`, `cfc_log_rpow`. Cone uses 10 of 52 declarations (the `supportInvSqrt` core and `cfc_sqrt_mul_self`). |
| QICLean.Analysis.MatrixTraceInequalities | 323 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/8 | Not in the cone. |
| QICLean.Analysis.MeanTreeExponentialLowerNorm | 93 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.MeanTreeLogFloorDeficit | 70 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.MeanTreeLogFloorExp | 90 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.MeanTreeMultibandLowerNorm | 98 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.MeanTreeProjectionLogBound | 69 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.MeanTreeProjectionMassBound | 79 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.MeanTreeProjectionMultibandUpper | 112 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.MeanTreeProjectionSectors | 109 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Analysis.MeanTreeProjectionUpper | 186 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/5 |  |
| QICLean.Analysis.MeanTreeSublinearRemainder | 89 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.MeanTreeUniformExpectation | 138 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Analysis.NormalizedInversePowerLogBound | 86 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.PhysicalSingletonDensity | 57 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/3 |  |
| QICLean.Analysis.PhysicalSingletonEntropy | 141 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/2 |  |
| QICLean.Analysis.PositiveProjectionCompression | 73 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ProbabilityEntropy | 93 | PARTIAL | Arealaw.Bridge.Entropy `H_le_log_card`; Arealaw.Mixed `MState.entropy_le_log_card` | 0/2 | Missing the support-cardinality form `probabilityEntropy_le_log_card_support`. Not in the cone. |
| QICLean.Analysis.ProjectionCalculus | 64 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ProjectionIntertwiningNorm | 70 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.RectangularTraceNorm | 294 | PARTIAL | Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm: `traceNorm` is already rectangular (`Matrix m n`), `traceNorm_isometry_left/right` | 0/14 | Missing rectangular contraction duality. Not referenced by name from the roots. |
| QICLean.Analysis.RectangularTraceNormAlgebra | 212 | PARTIAL | Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm: `traceNorm_smul` (rectangular), `traceNorm_add_le` (square only) | 0/13 | Missing rectangular triangle/sum bounds. Not referenced by name from the roots. |
| QICLean.Analysis.RegionalLowDefectLowerPin | 271 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/3 |  |
| QICLean.Analysis.RegionalLowDefectMass | 104 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.RegionalLowDefectProductMass | 133 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.RegionalLowDefectProjection | 173 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Analysis.RegionalPhysicalMarginals | 191 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/6 |  |
| QICLean.Analysis.RegionalRoughLowerNorm | 197 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.RegionalRoughLowerThree | 177 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.ReplicaBadCopyExponential | 223 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Analysis.ReplicaComponentInverseGoodExpectation | 98 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaComponentInverseRough | 89 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaComponentInverseRoughUniform | 132 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaComponentInverseSharp | 113 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Analysis.ReplicaComponentInverseSharpUniform | 118 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Analysis.ReplicaComponentMergeMoment | 176 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/9 |  |
| QICLean.Analysis.ReplicaDefect | 221 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 11/11 |  |
| QICLean.Analysis.ReplicaExcitationCompression | 184 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.ReplicaExcitationDecomposition | 276 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 14/15 |  |
| QICLean.Analysis.ReplicaExcitationSymmetry | 96 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Analysis.ReplicaGoodAuxiliaryLabelBound | 131 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/2 |  |
| QICLean.Analysis.ReplicaGoodAuxiliaryMarginal | 233 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 12/12 |  |
| QICLean.Analysis.ReplicaGoodConfigurationDensity | 244 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 11/11 |  |
| QICLean.Analysis.ReplicaGoodConfigurationExpectation | 251 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Analysis.ReplicaGoodConfigurationIndividualMergeMoment | 104 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/2 |  |
| QICLean.Analysis.ReplicaGoodConfigurationMergeMoment | 90 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.ReplicaGoodConfigurationMergeTransport | 208 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 12/12 |  |
| QICLean.Analysis.ReplicaGoodConfigurationPairMarginal | 118 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/5 |  |
| QICLean.Analysis.ReplicaGoodConfigurationProduct | 139 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/4 |  |
| QICLean.Analysis.ReplicaGoodConfigurationRegionalMoment | 101 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/2 |  |
| QICLean.Analysis.ReplicaGoodConfigurationSharpMoment | 153 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Analysis.ReplicaGoodConfigurationSignedMoments | 84 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Analysis.ReplicaGoodConfigurationSingletonMoment | 246 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/9 |  |
| QICLean.Analysis.ReplicaGoodCopyDensity | 131 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.ReplicaGoodCopyFactorization | 152 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/8 |  |
| QICLean.Analysis.ReplicaGoodPairMarginal | 345 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 10/12 |  |
| QICLean.Analysis.ReplicaGoodPhysicalExponential | 109 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.ReplicaGoodPhysicalSupport | 89 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaInverseRoughCompression | 84 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaJointAuxiliaryExponential | 297 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Analysis.ReplicaJointDensity | 135 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Analysis.ReplicaLowDefectCoordinateCovariance | 138 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Analysis.ReplicaLowDefectProjection | 320 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 11/11 |  |
| QICLean.Analysis.ReplicaLowDefectRoughLowerPin | 90 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaLowDefectSharpCompression | 100 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Analysis.ReplicaLowDefectSharpLowerPin | 97 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Analysis.ReplicaMarginalSymmetry | 90 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/2 |  |
| QICLean.Analysis.ReplicaPermutationCovariance | 137 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/7 |  |
| QICLean.Analysis.ReplicaRegionalDensity | 91 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.ReplicaTwoMergeMoment | 270 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 10/10 |  |
| QICLean.Analysis.RootFidelity | 101 | ALREADY | Arealaw.Fidelity `Arealaw.fidelity` (= ‖√A √B‖₁, same unsquared convention), `fidelity_nonneg`; Arealaw.Uhlmann `fidelity_eq_traceNorm_cfcSqrt_mul`, `isGreatest_norm_trace_conjTranspose_mul` | 4/5 | `exists_mem_unitaryGroup_trace_eq_rootFidelity` is the attainment half of the `IsGreatest` already proved; rename `rootFidelity` -> `Arealaw.fidelity`. |
| QICLean.Analysis.RootFidelityRelativeEntropy | 252 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/5 | Relative-entropy inequality F ≥ exp(-D/2) (not DPI); used by PurificationSplitting. |
| QICLean.Analysis.SchattenNorm | 175 | ALREADY | Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm: `Matrix.traceNorm`, `traceNorm_eq_sum_singularValues`, `traceNorm_zero_iff` | 6/13 | Defines a second `Matrix.traceNorm` (on `Fin D`). The repo already uses Physlib's rectangular `Matrix.traceNorm` (cf. OpenAI.PureStateTraceDistance); port callers onto it, do not port the file. |
| QICLean.Analysis.SharpBellOverlapLogBound | 103 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.ShiftedDensityPowers | 116 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/7 | Not in the cone. |
| QICLean.Analysis.ShiftedDensityTruncation | 234 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/21 | Cone uses only `spectralProjectionGE` and two lemmas about it (3 of 21). |
| QICLean.Analysis.SpectralCutoffMass | 91 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.SpectralExponentialDrop | 126 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Analysis.SpectralProjectionIntertwiner | 71 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.SupportCompression | 217 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/6 | Not referenced by name from the roots. |
| QICLean.Analysis.SupportLogJensen | 130 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.SurprisalFunctionalCalculus | 48 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.SurprisalProductMoment | 44 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Analysis.TraceDistance | 208 | PARTIAL | Arealaw.TraceDist `SubState.D₁`, `D₁_triangle`, `D₁_le_one`; OpenAI.ConditionalMovement.EntropyContinuity `traceDistance` (same `CFC.abs` definition, ℂ); OpenAI.CollarEntropyIdentity `D₁_restrict_le` | 1/9 | Cone uses only `trace_partialTraceRight_mul` (tr(Tr_B Y · X) = tr(Y (X ⊗ 1))), not found under that name; the general-matrix `traceDistance` API is unused. Imports TraceNormContractivity only for posPart-support lemmas. |
| QICLean.Analysis.TraceNormAbs | 196 | ALREADY | Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm: `traceNorm` is defined as `re tr √(AᴴA)`; `traceNorm_smul`, `traceNorm_unitary_conj`, `traceNorm_isometry_left/right` | 5/12 | `traceNorm_eq_re_trace_abs` is the definition there; `abs_eq_cfc_real_sqrt`-style helpers are a few lines if a caller needs them. |
| QICLean.Analysis.TraceNormContractivity | 531 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/22 | Not in the cone (TraceDistance imports it for posPart-support lemmas the cone does not reach). |
| QICLean.Analysis.TraceNormVariational | 342 | ALREADY | Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm: `traceNorm_eq_max_re_tr_U`, `traceNorm_add_le`, `abs_trace_le_traceNorm`; Arealaw.SVD `exists_mem_unitaryGroup_trace_mul_eq_traceNorm`; Arealaw.Uhlmann `isGreatest_norm_trace_conjTranspose_mul` | 6/11 | Cone uses `exists_mem_unitaryGroup_trace_conjTranspose_mul_eq`, `norm_trace_conjTranspose_mul_unitary_le`: both covered (Arealaw SVD/Uhlmann). `traceNorm_sum_le` is a one-line induction. |
| QICLean.Analysis.WeightedTraceExponential | 86 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Analysis.WeightedTraceHolder | 273 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| QICLean.Channel.MarginalSupportAbsorption | 461 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 7/12 | Support of marginals for the relative-entropy domain of ProductMarginals (relative-entropy chain); cone uses 7 of 12. |
| QICLean.Channel.MaximalOverlap | 417 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/17 | Cone uses 3 of 17: `partialTraceRight_vecMulVec_eq`, `star_dotProduct_eq_trace_conjTranspose_mul`, `trace_eq_ofReal_re`. |
| QICLean.Channel.MaximallyEntangled | 296 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/21 | Cone uses only `omegaVec`, `omegaCoeff_eq_inv`. |
| QICLean.Channel.SchmidtRank | 222 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/19 |  |
| QICLean.Channel.TensorMap | 282 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/26 | Not in the cone. |
| QICLean.Channel.UhlmannIsometry | 202 | PARTIAL | Arealaw.Uhlmann `uhlmann` (max over purifications in one space), `isGreatest_norm_trace_conjTranspose_mul`, `fidelity_vecMulVec`; Arealaw.Purify | 7/8 | Missing: isometry form between different purifying spaces (`exists_isIsometry_star_dotProduct_eq_rootFidelity`, `padPurification`, `exists_isIsometry_mul_eq_of_conjTranspose_mul_eq`); all are in the cone (via PurificationSplitting). |
| QICLean.Entropy.CompressedPhysicalMatchedCutoffs | 117 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Entropy.CompressedPhysicalRegions | 130 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 7/7 |  |
| QICLean.Entropy.CompressedSiteCoordinates | 56 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Entropy.CompressedTypicalCommonBellVector | 142 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.CompressedTypicalCommonRetainedMass | 142 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.CompressedTypicalRegionalMarginal | 92 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.CompressedTypicalRegionalTail | 85 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.CompressedTypicalSiteCoordinates | 189 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Entropy.CompressedTypicalSiteEntropy | 71 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.CompressedTypicalSiteNorm | 62 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.FiniteProductTypicalState | 211 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 12/14 |  |
| QICLean.Entropy.IidSchurExponentialMoments | 80 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.IidSchurLabelExponential | 89 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Entropy.IidSchurSignedMoments | 91 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Entropy.IidSurprisal | 263 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/9 |  |
| QICLean.Entropy.IidSurprisalExponential | 185 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Entropy.IidSurprisalMomentExponential | 63 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Entropy.ProductMarginals | 94 | PARTIAL | Physlib QuantumInfo.Entropy.Relative `qMutualInfo_as_qRelativeEnt`; Arealaw.Subadditivity `mutualInfo_nonneg` | 1/1 | FLAG relative entropy: D(ρ_AB ‖ ρ_A ⊗ ρ_B) = I(A:B). Physlib has it for `MState`; QICLean's Matrix-level `quantumRelativeEntropy` form (used by PurificationSplitting) missing. |
| QICLean.Entropy.PureTensorPower | 86 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Entropy.PurificationSplitting | 370 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 16/16 | Uses relative entropy / mutual information (Klein, ProductMarginals, RootFidelityRelativeEntropy) but not SSA; in the cone via TypicalPureState. |
| QICLean.Entropy.TypicalBellPin | 167 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 11/12 |  |
| QICLean.Entropy.TypicalBellPinPowers | 193 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 10/10 |  |
| QICLean.Entropy.TypicalDensity | 221 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/12 |  |
| QICLean.Entropy.TypicalPureCompression | 164 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 8/10 |  |
| QICLean.Entropy.TypicalPureState | 386 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 20/27 |  |
| QICLean.Entropy.TypicalSpectrum | 126 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/6 |  |
| QICLean.Representation.AddedSiteSpace | 43 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.AddedSiteTensorInsertion | 206 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 10/10 |  |
| QICLean.Representation.AddedSiteTensorInsertionNorm | 102 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.AddedSiteTensorInsertionSymmetry | 78 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/3 |  |
| QICLean.Representation.BellCompressedInverseNorm | 116 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.BellInsertionCoordinates | 265 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/9 |  |
| QICLean.Representation.BellInsertionRegisterCoordinates | 79 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/2 |  |
| QICLean.Representation.BellInsertionSymmetry | 174 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| QICLean.Representation.BellMetricFactorPositivity | 136 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.BellPhysicalRoughUpper | 130 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.BellPinnedCompressedPowers | 146 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.BellPinnedMetricCoordinates | 190 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| QICLean.Representation.BellPinnedProductAction | 126 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.BellPinnedTreeAction | 191 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.BellSymmetricPinProjection | 73 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.CommonSchurBellCutoffs | 172 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Representation.CommonSchurCutoffs | 273 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 10/10 |  |
| QICLean.Representation.CompatiblePhysicalLabel | 226 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 7/8 |  |
| QICLean.Representation.CompressedTypicalAuxiliaryCoordinates | 87 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Representation.CompressedTypicalExponential | 109 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.CompressedTypicalExponentialDomination | 95 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.CompressedTypicalLabelMass | 129 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.GroupAlgebraProductCoordinates | 70 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.GroupedConfigurationTransport | 111 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Representation.GroupedLabelSymmetricSupport | 170 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| QICLean.Representation.HighLabelWindow | 451 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 15/15 |  |
| QICLean.Representation.MatchedSchurCutoffs | 205 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.MergeExponential | 223 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 8/8 |  |
| QICLean.Representation.PairMergeDeficit | 171 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/7 |  |
| QICLean.Representation.PairMergeMoment | 306 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 18/20 |  |
| QICLean.Representation.PhysicalMergeHolder | 137 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/6 |  |
| QICLean.Representation.RegionalAuxiliaryLabels | 117 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.RegionalFiveFactorCoordinates | 118 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/8 |  |
| QICLean.Representation.RegionalPhysicalVector | 39 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.RegionalReplicaMetric | 204 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/9 |  |
| QICLean.Representation.RegionalReplicaMetricRegions | 123 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.ReplicaLaminarBandMetrics | 307 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| QICLean.Representation.ReplicaLowDefectSymmetricCoordinates | 81 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.ReplicaMeanIdentityExtension | 79 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/3 |  |
| QICLean.Representation.ReplicaPinnedLeafExpectation | 200 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 4/4 |  |
| QICLean.Representation.ReplicaPinnedMetricUpper | 183 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.ReplicaPinnedSharpLeaf | 440 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/9 |  |
| QICLean.Representation.ReplicaPinnedSharpTree | 263 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.ReplicaPinnedTreeExpectation | 101 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.ReplicaPrevector | 409 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 16/17 |  |
| QICLean.Representation.ReplicaPrevectorRoughUpper | 160 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.ReplicaPrevectorSharpUpper | 163 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.ReplicaSymmetricBandCommute | 116 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.ReplicaSymmetricBandLabelPreservation | 172 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.ReplicaSymmetricMeanTreeProduct | 73 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Representation.ReplicaSymmetricMetricFloor | 247 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/3 |  |
| QICLean.Representation.ReplicaSymmetricSupport | 75 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/1 |  |
| QICLean.Representation.ReplicaTransport.RootCompression | 104 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SchmidtBellEnumeratedCompression | 156 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.SchmidtBellEnumeratedPrevector | 79 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SchmidtBellPhysicalWitness | 194 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SchmidtBellPrevector | 315 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 7/10 |  |
| QICLean.Representation.SchmidtBellPrevectorOverlap | 115 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.SchmidtBellSharpUpper | 152 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SchmidtBellSitePin | 216 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Representation.SchmidtBellWitnessCoordinates | 94 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.SchmidtBellWitnessRange | 178 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.SchurLabelCutoff | 43 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SchurLabelMomentBounds | 161 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/3 |  |
| QICLean.Representation.SchurLabelMoments | 224 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Representation.SchurSectorMass | 137 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/2 |  |
| QICLean.Representation.SelectedBellPostInverseTransport | 133 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SelectedBellPostMass | 146 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Representation.SelectedBellPostPin | 170 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| QICLean.Representation.SubsystemLabelCoordinates | 163 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 5/5 |  |
| QICLean.Representation.SubsystemLabelExponential | 101 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| QICLean.Representation.SupportedSubsystemLabelDimension | 97 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| QICLean.Representation.UniformBellLabel | 163 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 8/8 |  |
| TNLean.Algebra.MatrixReindexGap | 73 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/3 |  |
| TNLean.Circuit.SiteEmbedding | 361 | ALREADY | Arealaw.PTrace `Arealaw.extendId` (X ↦ X ⊗ 1 on a region), `extendId_one`; OpenAI.Bridges `isSupportedOn_extendId`, `extendId_mul`, `IsSupportedOn.mul` | 3/29 | TNLean `QuantumCircuit` Fin-site encoding; the repo's region encoding (`Reg loc`, `Finset` regions) replaces it. Not referenced by name from the comparator roots. |
| TNLean.Circuit.SiteExpectation | 551 | ALREADY | OpenAI.Statements `condExpect` [OAI265 eq. 4.1]; OpenAI.ConditionalExpectation `norm_condExpect_le`, `condExpect_of_isSupportedOn`, `condExpect_submatrix_glueEquiv_eq_complementaryWeylTwirl`, `norm_sub_condExpect_le_of_forall_commutator` | 0/34 | `siteExpectation` = `condExpect`; Weyl-average proof already ported (OpenAI.ComplementaryWeylTwirl). Not in the comparator cone. |
| TNLean.Circuit.SiteExpectationOrder | 151 | PARTIAL | OpenAI.ConditionalExpectation `condExpect_nonneg`, `condExpect_mono`, `condExpect_le_one`, `IsSupportedOn.cfcAbs`, `condExpect_cfcAbs_condExpect` | 0/11 | Missing: `siteExpectation_eq_self_of_forall_commute` / `mem_supportedOperators_of_forall_commute` (commutant of the outside algebra is supported), `sqrt_mem_supportedOperators`, `heisenbergEvolution_eq_hermitianUnitaryPath`. Only consumer is LocalRootChannels; not in the comparator cone. |
| TNLean.PEPS.AreaLaw.Amplification.LocalRootChannels | 267 | PARTIAL | OpenAI.RootChannel `Matrix.rootChannel`, `norm_rootChannel_kronecker_sub_le`, `rootChannel_sqrt_eq_self_of_commute` | 0/17 | Missing: `localRootChannel`/`spectatorRootChannel` (root channel of `condExpect` roots) and the shells. Its only consumer is the proof of `exists_latticeQuasilocalRoots` (LatticeConstraints), which the repo has natively as `OpenAI.quasilocal_roots`; not in the comparator cone. |
| TNLean.PEPS.AreaLaw.EdgeBoundaryCalculus | 136 | GEOMETRY | OpenAI.Statements `edgeBoundary`; OpenAI.Basic `mem_edgeBoundary`, `card_image_mk_edgeBoundary`; OpenAI.Corollary `card_edgeBoundary_le_four_mul_innerBoundary` | 0/10 | Boundary calculus (complement, union, sdiff, `card ≤ 4|·|`, symmetric difference) on TNLean's unordered induced-graph edges. Restate on the repo's ordered `edgeBoundary`; not geometric-template specific but the same bridge. |
| TNLean.PEPS.AreaLaw.Geometry.AmbientBoundary | 184 | GEOMETRY | OpenAI.Statements `edgeBoundary`, `ambientDilation`; OpenAI.Geometry.TemplateCollar `latticeSteps`, `card_edgeBoundary_inter_le` | 0/16 | Defines `latticeNeighbors`, unordered `ambientBoundary` of a dilation; four-neighbour boundary counts. Repo uses ordered `edgeBoundary` pairs (OpenAI.Basic `card_image_mk_edgeBoundary` converts to `Sym2`). |
| TNLean.PEPS.AreaLaw.Geometry.TemplateBoundary | 48 | GEOMETRY | OpenAI.Geometry.TemplateCollar `IsTemplate.collar_cut_card_le` | 0/2 | `template_boundary_card_le`, `template_shell_boundary_card_le` (ambient boundary of templates, Lemma 9.4). |
| TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary | 116 | GEOMETRY | OpenAI.Geometry.TemplateCollar `card_edgeBoundary_inter_le`, `card_edgeBoundary_inter_sdiff_le`, `notMem_cutEndpoints_of_isSeparatedFromCut`, `IsTemplate.collar_cut_card_le` | 0/6 | Physical cut boundaries of separated templates, `4n`/`8n` bounds. Cone uses `card_edgeBoundary_filter_le_ambientBoundary`. |
| TNLean.PEPS.AreaLaw.Geometry.TemplateLayers | 284 | GEOMETRY | OpenAI.Geometry.TemplateCollar `IsTemplate.card_ambientDilation_le_sq`; OpenAI.Scan.CompactCollarCounting `card_ambientDilation_le_of_layers` | 0/9 | Dilation layers of templates (`template_layer_card_le`, Lemma 9.4). Bridge to the repo's template-collar counts. |
| TNLean.PEPS.AreaLaw.Geometry.TemplateRowBounds | 155 | GEOMETRY | OpenAI.Geometry.TemplatePieceStrips `exists_four_strip_bounds`; OpenAI.Geometry.TemplateMixedSquares `IsOctagonallyConvex.hasLipschitzRows` | 0/7 | Rounded row endpoints move by ≤ 1 between rows. Repo has the same content as `HasLipschitzRows`. Cone uses `latticeRow_nonempty_between`, `exists_sample_in_window_between`, `exists_nearby_sample_in_row` (from Scan files). |
| TNLean.PEPS.AreaLaw.Geometry.TemplateRows | 306 | GEOMETRY | OpenAI.Rectangles `ambientDilation_mono`, `mem_ambientDilation`; OpenAI.Geometry.TemplatePieceStrips `IsTemplatePiece.exists_four_strip_bounds`; OpenAI.Geometry.TemplateMixedSquares `HasLipschitzRows` | 0/23 | Integer rows `latticeRow` of a sampled polygon are intervals; `template_card_le`. Repo counterpart: the strip description and Lipschitz-row API of OpenAI.Geometry.* ; `IsTemplate.card_le` (TemplateMixedSquares). |
| TNLean.PEPS.AreaLaw.Geometry.Templates | 146 | GEOMETRY | OpenAI.Statements `IsTemplate`, `IsTemplatePiece`, `HasTemplateSlope`, `IsSeparatedFromCut`, `collarWidth`; `ambientDilation` | 4/10 | Defines `TemplatePolygon` (closed convex rectangle/triangle with allowed slopes), `Template` (sampled union), `Template.IsSeparated`, `core`, `collar`, and `OrderedTwoFamilyPartition`. Bridge: `Template` -> `IsTemplate Ctpl n s₀ T`, `TemplatePolygon.region` -> `IsTemplatePiece`, `IsAllowedSlope` -> `HasTemplateSlope`; `OrderedTwoFamilyPartition` -> the piece/label data of `OpenAI.TwoFamilyCancellation`. Cone uses `IsAllowedSlope`, `TemplatePolygon`, `region`, `OrderedTwoFamilyPartition`. |
| TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector | 150 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| TNLean.PEPS.AreaLaw.GlobalSchmidtBellRoughLower | 211 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| TNLean.PEPS.AreaLaw.LatticeConstraints | 323 | PARTIAL | OpenAI.PositiveReplacement `positive_replacement` (Prop 4.3); OpenAI.QuasilocalRoots `quasilocal_roots` (Lemma 4.4); OpenAI.FiniteSetTruncationOfGap `exists_finiteSetTruncation_of_gap` (Prop 4.5); OpenAI.CrossingBudget `cutBudget_le`, `le_of_cutBudget_le`; OpenAI.LatticeCounts `card_graphBall_domainGraph_le`, `card_anchor_fiber_le_diamond` | 0/6 | TNLean restates Props 4.3-4.5 for its `LocalHamiltonian` model; the repo states them natively over `IsAdmissible`. Missing: `exists_latticeCrossingBudget`, `exists_latticeCutBudget_le_log` (lattice instance of `cutBudget_le` + `le_of_cutBudget_le`, ~50 lines), `exists_latticeFiniteSetTruncation_eigenspace_eq_span`. Consumers: StatusMarginalBudget (`exists_latticeCutBudget_le_log`), ActualMarginalTails (`exists_latticeFiniteSetTruncation` = `exists_finiteSetTruncation_of_gap`). |
| TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails | 202 | PARTIAL | OpenAI.Scan.MarginalTailsBridge `IsAdmissible.log_surprisalMoment_reducedState_le`, `IsAdmissible.surprisalTail_reducedState_le`; OpenAI.MarginalTails `marginal_tails` | 0/3 | Missing: the three truncated-Hamiltonian versions (`*_truncated_reducedState_*`). Its consumer StatusMarginalMoments is imported by ActualSharpUpper but no declaration of either is referenced by name from the roots. |
| TNLean.PEPS.AreaLaw.Scan.ActualRoughUpper | 325 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| TNLean.PEPS.AreaLaw.Scan.ActualSharpUpper | 952 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 13/13 |  |
| TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions | 90 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates | 171 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 7/8 |  |
| TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaMetricCoordinates | 109 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties | 106 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/2 |  |
| TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression | 152 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| TNLean.PEPS.AreaLaw.Scan.FrontPrefixFamily | 39 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| TNLean.PEPS.AreaLaw.Scan.FrontThresholds | 39 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/1 |  |
| TNLean.PEPS.AreaLaw.Scan.PrefixApproximation | 111 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| TNLean.PEPS.AreaLaw.Scan.PrefixBoundary | 139 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/6 |  |
| TNLean.PEPS.AreaLaw.Scan.PrefixCardinality | 154 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 3/3 |  |
| TNLean.PEPS.AreaLaw.Scan.PrefixComparison | 185 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 9/10 |  |
| TNLean.PEPS.AreaLaw.Scan.PrefixFiniteFamily | 44 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 2/2 |  |
| TNLean.PEPS.AreaLaw.Scan.ReceivingRegions | 169 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 6/6 |  |
| TNLean.PEPS.AreaLaw.Scan.StatusCutBounds | 170 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/5 |  |
| TNLean.PEPS.AreaLaw.Scan.StatusMarginalBudget | 146 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 1/4 |  |
| TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments | 166 | NEW | none found (declaration names and concepts searched in OpenAI/, Arealaw/, Mathlib, Physlib) | 0/4 |  |
| TNLean.PEPS.AreaLaw.TwoFamilies | 153 | PARTIAL | OpenAI.TwoFamily `two_family_cancellation` (Lemma 11.1, native); OpenAI.ConditionalTwoFamilies; OpenAI.Bridges `regionEntropy_pureState_eq_sum_negMulLog` | 2/7 | Main theorem native. ActualSharpUpper uses only `reducedState_eq_finiteProduct`, `regionalEntropy_eq_finiteProduct`: encoding bridges from TNLean's lattice state to `FiniteProduct.reducedPure/entropy` (OpenAI.FiniteProductEntropy). In the repo they become a `pureState`/`regionEntropy` <-> `FiniteProduct` bridge; write that, not the file. |

## Summary

| verdict | modules | lines | of which lines in files with cone 0 |
|---|---|---|---|
| ALREADY | 6 | 1726 | 551 |
| PARTIAL | 15 | 4767 | 2034 |
| NEW | 235 | 38616 | 6262 |
| GEOMETRY | 8 | 1375 | 1229 |
| total | 264 | 46484 | 10076 |

## Modules a port must write (NEW + PARTIAL), dependency order

Each module follows every NEW/PARTIAL module it imports (the `<-` lists). GEOMETRY files are left out: they need bridges onto OpenAI.Statements/OpenAI.Geometry, to be in place before the first listed file that imports them (TwoFamilies; the Scan prefix/boundary files). `cone 0` files are marked `(skip?)`.

1. QICLean.Algebra.DependentBlockDiagonal (316 lines, NEW, cone 0/13) (skip?)
2. QICLean.Algebra.FinSum (230 lines, NEW, cone 1/7)
3. QICLean.Algebra.KroneckerFactorPositivity (481 lines, NEW, cone 9/14)
4. QICLean.Algebra.FiniteKroneckerOrder (89 lines, NEW, cone 2/2)
5. QICLean.Algebra.HermitianHelpers (529 lines, NEW, cone 1/22)
6. QICLean.Algebra.MatrixGramUnitary (261 lines, NEW, cone 1/5)
7. QICLean.Algebra.MatrixUnitaryBetween (292 lines, PARTIAL, cone 6/13)
8. QICLean.Algebra.MatrixIsometryKronecker (33 lines, NEW, cone 1/1)
9. QICLean.Algebra.MatrixProductIntertwine (42 lines, NEW, cone 1/1)
10. QICLean.Algebra.MatrixReindexUnitary (36 lines, NEW, cone 1/1)
11. QICLean.Algebra.OperatorBlock (40 lines, NEW, cone 0/2) (skip?)
12. QICLean.Algebra.OperatorSchmidt (274 lines, NEW, cone 0/13) (skip?)
13. QICLean.Algebra.PerronFrobenius.RankOne (723 lines, NEW, cone 0/22) (skip?)
14. QICLean.Algebra.PiProductTrace (32 lines, NEW, cone 1/1)
15. QICLean.Algebra.PositiveSemidefiniteNormalization (125 lines, NEW, cone 4/5)
16. QICLean.Algebra.ProjectionRangeIsometry (47 lines, NEW, cone 1/1)
17. QICLean.Algebra.TensorPowerPartialTrace (53 lines, NEW, cone 0/2) (skip?)
18. QICLean.Analysis.MatrixSqrt (929 lines, PARTIAL, cone 10/52)
19. QICLean.Analysis.EntropyDecomposition (492 lines, PARTIAL, cone 0/14) (skip?)
20. QICLean.Analysis.ExponentialPolynomialAbsorption (64 lines, NEW, cone 1/1)
21. QICLean.Analysis.FiniteExponentialRetainedMass (90 lines, NEW, cone 2/2)
22. QICLean.Analysis.MatrixTraceInequalities (323 lines, NEW, cone 0/8) (skip?)
23. QICLean.Analysis.ShiftedDensityPowers (116 lines, NEW, cone 0/7) (skip?)
24. QICLean.Analysis.ShiftedDensityTruncation (234 lines, NEW, cone 3/21)
25. QICLean.Analysis.SpectralCutoffMass (91 lines, NEW, cone 2/2)
26. QICLean.Analysis.ReplicaDefect (221 lines, NEW, cone 11/11)
27. QICLean.Analysis.ReplicaExcitationDecomposition (276 lines, NEW, cone 14/15)
28. QICLean.Analysis.ReplicaExcitationSymmetry (96 lines, NEW, cone 5/5)
29. QICLean.Analysis.ReplicaMarginalSymmetry (90 lines, NEW, cone 1/2)
30. QICLean.Analysis.ReplicaGoodAuxiliaryMarginal (233 lines, NEW, cone 12/12)
31. QICLean.Analysis.ReplicaGoodCopyFactorization (152 lines, NEW, cone 5/8)
32. QICLean.Analysis.ReplicaGoodCopyDensity (131 lines, NEW, cone 3/3)
33. QICLean.Analysis.ReplicaGoodPhysicalSupport (89 lines, NEW, cone 1/1)
34. QICLean.Analysis.ReplicaGoodConfigurationDensity (244 lines, NEW, cone 11/11)
35. QICLean.Analysis.FiveFactorAuxiliaryCoordinates (112 lines, NEW, cone 2/2)
36. QICLean.Analysis.FloorPin (60 lines, NEW, cone 1/2)
37. QICLean.Analysis.GaussianFilter.Kernel (151 lines, NEW, cone 0/15) (skip?)
38. QICLean.Analysis.GaussianFilter.MatrixIntegral (294 lines, NEW, cone 0/22) (skip?)
39. QICLean.Analysis.GaussianFilter.Reindex (93 lines, NEW, cone 1/6)
40. QICLean.Analysis.IidTailThreshold (76 lines, NEW, cone 1/1)
41. QICLean.Analysis.SupportLogJensen (130 lines, NEW, cone 1/1)
42. QICLean.Analysis.InversePowerLogJensen (108 lines, NEW, cone 2/2)
43. QICLean.Analysis.MatrixFramePerturbation (124 lines, NEW, cone 1/4)
44. QICLean.Analysis.RectangularTraceNorm (294 lines, PARTIAL, cone 0/14) (skip?)
45. QICLean.Analysis.RectangularTraceNormAlgebra (212 lines, PARTIAL, cone 0/13) (skip?)
46. QICLean.Analysis.IsometricDomainExtension (164 lines, NEW, cone 1/12)
47. QICLean.Analysis.IsometricIntertwiningCommute (52 lines, NEW, cone 1/1)
48. QICLean.Analysis.KleinInequality (855 lines, PARTIAL, cone 4/22)
49. QICLean.Analysis.KroneckerExponential (88 lines, NEW, cone 2/5)
50. QICLean.Analysis.KyFanNorm (503 lines, NEW, cone 0/21) (skip?)
51. QICLean.Analysis.MarginalSupport (347 lines, NEW, cone 1/15)
52. QICLean.Analysis.MeanTreeLogFloorExp (90 lines, NEW, cone 3/3)
53. QICLean.Analysis.MeanTreeLogFloorDeficit (70 lines, NEW, cone 1/1)
54. QICLean.Analysis.MeanTreeProjectionSectors (109 lines, NEW, cone 4/4)
55. QICLean.Analysis.ProjectionCalculus (64 lines, NEW, cone 1/1)
56. QICLean.Analysis.MeanTreeProjectionLogBound (69 lines, NEW, cone 1/1)
57. QICLean.Analysis.MeanTreeProjectionMassBound (79 lines, NEW, cone 1/1)
58. QICLean.Analysis.NormalizedInversePowerLogBound (86 lines, NEW, cone 2/2)
59. QICLean.Analysis.MeanTreeMultibandLowerNorm (98 lines, NEW, cone 1/1)
60. QICLean.Analysis.MeanTreeExponentialLowerNorm (93 lines, NEW, cone 1/1)
61. QICLean.Analysis.MeanTreeProjectionUpper (186 lines, NEW, cone 4/5)
62. QICLean.Analysis.MeanTreeProjectionMultibandUpper (112 lines, NEW, cone 3/3)
63. QICLean.Analysis.MeanTreeSublinearRemainder (89 lines, NEW, cone 2/2)
64. QICLean.Analysis.MeanTreeUniformExpectation (138 lines, NEW, cone 5/5)
65. QICLean.Analysis.ReplicaRegionalDensity (91 lines, NEW, cone 1/1)
66. QICLean.Analysis.ReplicaJointDensity (135 lines, NEW, cone 5/5)
67. QICLean.Analysis.TraceNormContractivity (531 lines, NEW, cone 0/22) (skip?)
68. QICLean.Analysis.TraceDistance (208 lines, PARTIAL, cone 1/9)
69. QICLean.Analysis.ReplicaGoodConfigurationProduct (139 lines, NEW, cone 0/4) (skip?)
70. QICLean.Analysis.ReplicaGoodConfigurationRegionalMoment (101 lines, NEW, cone 0/2) (skip?)
71. QICLean.Analysis.ReplicaGoodConfigurationSingletonMoment (246 lines, NEW, cone 0/9) (skip?)
72. QICLean.Analysis.PhysicalSingletonDensity (57 lines, NEW, cone 0/3) (skip?)
73. QICLean.Analysis.PhysicalSingletonEntropy (141 lines, NEW, cone 0/2) (skip?)
74. QICLean.Analysis.PositiveProjectionCompression (73 lines, NEW, cone 1/1)
75. QICLean.Analysis.ProbabilityEntropy (93 lines, PARTIAL, cone 0/2) (skip?)
76. QICLean.Analysis.ProjectionIntertwiningNorm (70 lines, NEW, cone 1/1)
77. QICLean.Analysis.ReplicaExcitationCompression (184 lines, NEW, cone 3/3)
78. QICLean.Analysis.ReplicaPermutationCovariance (137 lines, NEW, cone 6/7)
79. QICLean.Analysis.ReplicaLowDefectProjection (320 lines, NEW, cone 11/11)
80. QICLean.Representation.AddedSiteSpace (43 lines, NEW, cone 1/1)
81. QICLean.Representation.RegionalFiveFactorCoordinates (118 lines, NEW, cone 5/8)
82. QICLean.Analysis.ReplicaLowDefectCoordinateCovariance (138 lines, NEW, cone 4/4)
83. QICLean.Analysis.RegionalLowDefectProjection (173 lines, NEW, cone 4/4)
84. QICLean.Representation.RegionalPhysicalVector (39 lines, NEW, cone 1/1)
85. QICLean.Analysis.RegionalPhysicalMarginals (191 lines, NEW, cone 0/6) (skip?)
86. QICLean.Analysis.ReplicaGoodAuxiliaryLabelBound (131 lines, NEW, cone 1/2)
87. QICLean.Representation.MergeExponential (223 lines, NEW, cone 8/8)
88. QICLean.Representation.GroupedLabelSymmetricSupport (170 lines, NEW, cone 6/6)
89. QICLean.Analysis.ReplicaBadCopyExponential (223 lines, NEW, cone 5/5)
90. QICLean.Analysis.ReplicaJointAuxiliaryExponential (297 lines, NEW, cone 4/4)
91. QICLean.Analysis.ReplicaComponentInverseGoodExpectation (98 lines, NEW, cone 1/1)
92. QICLean.Analysis.SpectralProjectionIntertwiner (71 lines, NEW, cone 2/2)
93. QICLean.Representation.CompatiblePhysicalLabel (226 lines, NEW, cone 7/8)
94. QICLean.Representation.GroupedConfigurationTransport (111 lines, NEW, cone 4/4)
95. QICLean.Analysis.ReplicaGoodConfigurationExpectation (251 lines, NEW, cone 5/5)
96. QICLean.Analysis.ReplicaGoodPairMarginal (345 lines, NEW, cone 10/12)
97. QICLean.Analysis.ReplicaGoodConfigurationPairMarginal (118 lines, NEW, cone 4/5)
98. QICLean.Representation.GroupAlgebraProductCoordinates (70 lines, NEW, cone 1/1)
99. QICLean.Representation.PairMergeMoment (306 lines, NEW, cone 18/20)
100. QICLean.Representation.PairMergeDeficit (171 lines, NEW, cone 5/7)
101. QICLean.Analysis.ReplicaGoodConfigurationMergeTransport (208 lines, NEW, cone 12/12)
102. QICLean.Analysis.ReplicaComponentMergeMoment (176 lines, NEW, cone 9/9)
103. QICLean.Analysis.WeightedTraceExponential (86 lines, NEW, cone 2/2)
104. QICLean.Analysis.ReplicaTwoMergeMoment (270 lines, NEW, cone 10/10)
105. QICLean.Analysis.ReplicaGoodConfigurationMergeMoment (90 lines, NEW, cone 2/2)
106. QICLean.Analysis.SpectralExponentialDrop (126 lines, NEW, cone 3/3)
107. QICLean.Analysis.ReplicaGoodPhysicalExponential (109 lines, NEW, cone 2/2)
108. QICLean.Analysis.ReplicaComponentInverseRough (89 lines, NEW, cone 1/1)
109. QICLean.Analysis.ReplicaComponentInverseRoughUniform (132 lines, NEW, cone 1/1)
110. QICLean.Analysis.ReplicaInverseRoughCompression (84 lines, NEW, cone 1/1)
111. QICLean.Representation.ReplicaLowDefectSymmetricCoordinates (81 lines, NEW, cone 2/2)
112. QICLean.Analysis.ReplicaLowDefectRoughLowerPin (90 lines, NEW, cone 1/1)
113. QICLean.Analysis.ReplicaGoodConfigurationIndividualMergeMoment (104 lines, NEW, cone 0/2) (skip?)
114. QICLean.Analysis.SurprisalProductMoment (44 lines, NEW, cone 1/1)
115. QICLean.Entropy.IidSurprisal (263 lines, NEW, cone 9/9)
116. QICLean.Entropy.IidSurprisalMomentExponential (63 lines, NEW, cone 2/2)
117. QICLean.Analysis.WeightedTraceHolder (273 lines, NEW, cone 6/6)
118. QICLean.Representation.SchurLabelMoments (224 lines, NEW, cone 5/5)
119. QICLean.Representation.SchurLabelMomentBounds (161 lines, NEW, cone 2/3)
120. QICLean.Entropy.IidSchurSignedMoments (91 lines, NEW, cone 2/2)
121. QICLean.Entropy.IidSchurExponentialMoments (80 lines, NEW, cone 1/1)
122. QICLean.Analysis.ReplicaGoodConfigurationSignedMoments (84 lines, NEW, cone 0/1) (skip?)
123. QICLean.Representation.PhysicalMergeHolder (137 lines, NEW, cone 0/6) (skip?)
124. QICLean.Analysis.ReplicaGoodConfigurationSharpMoment (153 lines, NEW, cone 0/1) (skip?)
125. QICLean.Analysis.ReplicaComponentInverseSharp (113 lines, NEW, cone 0/1) (skip?)
126. QICLean.Analysis.ReplicaComponentInverseSharpUniform (118 lines, NEW, cone 0/1) (skip?)
127. QICLean.Analysis.ReplicaLowDefectSharpCompression (100 lines, NEW, cone 0/1) (skip?)
128. QICLean.Analysis.ReplicaLowDefectSharpLowerPin (97 lines, NEW, cone 0/1) (skip?)
129. QICLean.Representation.RegionalReplicaMetric (204 lines, NEW, cone 9/9)
130. QICLean.Analysis.RegionalLowDefectLowerPin (271 lines, NEW, cone 2/3)
131. QICLean.Representation.RegionalAuxiliaryLabels (117 lines, NEW, cone 1/1)
132. QICLean.Analysis.RegionalLowDefectMass (104 lines, NEW, cone 3/3)
133. QICLean.Representation.RegionalReplicaMetricRegions (123 lines, NEW, cone 3/3)
134. QICLean.Representation.ReplicaLaminarBandMetrics (307 lines, NEW, cone 6/6)
135. QICLean.Representation.ReplicaSymmetricBandCommute (116 lines, NEW, cone 2/2)
136. QICLean.Representation.ReplicaSymmetricMeanTreeProduct (73 lines, NEW, cone 0/1) (skip?)
137. QICLean.Representation.ReplicaSymmetricBandLabelPreservation (172 lines, NEW, cone 1/1)
138. QICLean.Analysis.RegionalLowDefectProductMass (133 lines, NEW, cone 1/1)
139. QICLean.Representation.ReplicaSymmetricSupport (75 lines, NEW, cone 0/1) (skip?)
140. QICLean.Representation.ReplicaSymmetricMetricFloor (247 lines, NEW, cone 2/3)
141. QICLean.Analysis.RegionalRoughLowerNorm (197 lines, NEW, cone 1/1)
142. QICLean.Analysis.RegionalRoughLowerThree (177 lines, NEW, cone 3/3)
143. QICLean.Analysis.RootFidelityRelativeEntropy (252 lines, NEW, cone 3/5)
144. QICLean.Analysis.SharpBellOverlapLogBound (103 lines, NEW, cone 2/2)
145. QICLean.Analysis.SupportCompression (217 lines, NEW, cone 0/6) (skip?)
146. QICLean.Analysis.SurprisalFunctionalCalculus (48 lines, NEW, cone 1/1)
147. QICLean.Channel.MarginalSupportAbsorption (461 lines, NEW, cone 7/12)
148. QICLean.Channel.SchmidtRank (222 lines, NEW, cone 5/19)
149. QICLean.Channel.MaximalOverlap (417 lines, NEW, cone 3/17)
150. QICLean.Channel.TensorMap (282 lines, NEW, cone 0/26) (skip?)
151. QICLean.Channel.MaximallyEntangled (296 lines, NEW, cone 2/21)
152. QICLean.Channel.UhlmannIsometry (202 lines, PARTIAL, cone 7/8)
153. QICLean.Entropy.CompressedSiteCoordinates (56 lines, NEW, cone 2/2)
154. QICLean.Entropy.ProductMarginals (94 lines, PARTIAL, cone 1/1)
155. QICLean.Entropy.PurificationSplitting (370 lines, NEW, cone 16/16)
156. QICLean.Entropy.TypicalSpectrum (126 lines, NEW, cone 0/6) (skip?)
157. QICLean.Entropy.TypicalDensity (221 lines, NEW, cone 6/12)
158. QICLean.Entropy.TypicalPureState (386 lines, NEW, cone 20/27)
159. QICLean.Entropy.FiniteProductTypicalState (211 lines, NEW, cone 12/14)
160. QICLean.Entropy.TypicalPureCompression (164 lines, NEW, cone 8/10)
161. QICLean.Entropy.CompressedTypicalRegionalMarginal (92 lines, NEW, cone 1/1)
162. QICLean.Entropy.CompressedTypicalSiteCoordinates (189 lines, NEW, cone 5/5)
163. QICLean.Entropy.CompressedPhysicalRegions (130 lines, NEW, cone 7/7)
164. QICLean.Entropy.PureTensorPower (86 lines, NEW, cone 3/3)
165. QICLean.Representation.SchurLabelCutoff (43 lines, NEW, cone 1/1)
166. QICLean.Representation.SubsystemLabelCoordinates (163 lines, NEW, cone 5/5)
167. QICLean.Representation.SupportedSubsystemLabelDimension (97 lines, NEW, cone 2/2)
168. QICLean.Representation.MatchedSchurCutoffs (205 lines, NEW, cone 3/3)
169. QICLean.Entropy.CompressedPhysicalMatchedCutoffs (117 lines, NEW, cone 3/3)
170. QICLean.Entropy.CompressedTypicalSiteEntropy (71 lines, NEW, cone 1/1)
171. QICLean.Entropy.CompressedTypicalSiteNorm (62 lines, NEW, cone 1/1)
172. QICLean.Entropy.IidSurprisalExponential (185 lines, NEW, cone 2/2)
173. QICLean.Entropy.IidSchurLabelExponential (89 lines, NEW, cone 1/1)
174. QICLean.Entropy.CompressedTypicalRegionalTail (85 lines, NEW, cone 1/1)
175. QICLean.Representation.CommonSchurCutoffs (273 lines, NEW, cone 10/10)
176. QICLean.Entropy.CompressedTypicalCommonRetainedMass (142 lines, NEW, cone 1/1)
177. QICLean.Entropy.TypicalBellPin (167 lines, NEW, cone 11/12)
178. QICLean.Entropy.TypicalBellPinPowers (193 lines, NEW, cone 10/10)
179. QICLean.Representation.CommonSchurBellCutoffs (172 lines, NEW, cone 4/4)
180. QICLean.Representation.CompressedTypicalAuxiliaryCoordinates (87 lines, NEW, cone 4/4)
181. QICLean.Entropy.CompressedTypicalCommonBellVector (142 lines, NEW, cone 1/1)
182. QICLean.Representation.AddedSiteTensorInsertion (206 lines, NEW, cone 10/10)
183. QICLean.Representation.AddedSiteTensorInsertionNorm (102 lines, NEW, cone 3/3)
184. QICLean.Representation.AddedSiteTensorInsertionSymmetry (78 lines, NEW, cone 1/3)
185. QICLean.Representation.BellInsertionCoordinates (265 lines, NEW, cone 9/9)
186. QICLean.Representation.BellInsertionSymmetry (174 lines, NEW, cone 6/6)
187. QICLean.Representation.BellPinnedMetricCoordinates (190 lines, NEW, cone 6/6)
188. QICLean.Representation.BellMetricFactorPositivity (136 lines, NEW, cone 1/1)
189. QICLean.Representation.BellSymmetricPinProjection (73 lines, NEW, cone 1/1)
190. QICLean.Representation.BellPinnedTreeAction (191 lines, NEW, cone 3/3)
191. QICLean.Representation.ReplicaPinnedLeafExpectation (200 lines, NEW, cone 4/4)
192. QICLean.Representation.ReplicaPinnedTreeExpectation (101 lines, NEW, cone 2/2)
193. QICLean.Representation.BellPinnedProductAction (126 lines, NEW, cone 1/1)
194. QICLean.Representation.BellPinnedCompressedPowers (146 lines, NEW, cone 1/1)
195. QICLean.Representation.BellCompressedInverseNorm (116 lines, NEW, cone 1/1)
196. QICLean.Representation.BellInsertionRegisterCoordinates (79 lines, NEW, cone 1/2)
197. QICLean.Representation.CompressedTypicalLabelMass (129 lines, NEW, cone 3/3)
198. QICLean.Representation.HighLabelWindow (451 lines, NEW, cone 15/15)
199. QICLean.Representation.SchurSectorMass (137 lines, NEW, cone 1/2)
200. QICLean.Representation.UniformBellLabel (163 lines, NEW, cone 8/8)
201. QICLean.Representation.ReplicaPrevector (409 lines, NEW, cone 16/17)
202. QICLean.Representation.SchmidtBellPrevector (315 lines, NEW, cone 7/10)
203. QICLean.Representation.SchmidtBellSitePin (216 lines, NEW, cone 5/5)
204. QICLean.Representation.SchmidtBellPrevectorOverlap (115 lines, NEW, cone 2/2)
205. QICLean.Representation.SchmidtBellWitnessCoordinates (94 lines, NEW, cone 2/2)
206. QICLean.Representation.SchmidtBellWitnessRange (178 lines, NEW, cone 3/3)
207. QICLean.Representation.SchmidtBellPhysicalWitness (194 lines, NEW, cone 1/1)
208. QICLean.Representation.BellPhysicalRoughUpper (130 lines, NEW, cone 1/1)
209. QICLean.Representation.SubsystemLabelExponential (101 lines, NEW, cone 1/1)
210. QICLean.Representation.CompressedTypicalExponential (109 lines, NEW, cone 1/1)
211. QICLean.Representation.CompressedTypicalExponentialDomination (95 lines, NEW, cone 1/1)
212. QICLean.Representation.ReplicaMeanIdentityExtension (79 lines, NEW, cone 0/3) (skip?)
213. QICLean.Representation.ReplicaPinnedMetricUpper (183 lines, NEW, cone 1/1)
214. QICLean.Representation.ReplicaPinnedSharpLeaf (440 lines, NEW, cone 9/9)
215. QICLean.Representation.ReplicaPinnedSharpTree (263 lines, NEW, cone 3/3)
216. QICLean.Representation.SchmidtBellEnumeratedPrevector (79 lines, NEW, cone 1/1)
217. QICLean.Representation.SchmidtBellEnumeratedCompression (156 lines, NEW, cone 2/2)
218. QICLean.Representation.ReplicaPrevectorRoughUpper (160 lines, NEW, cone 1/1)
219. QICLean.Representation.SelectedBellPostMass (146 lines, NEW, cone 5/5)
220. QICLean.Representation.SelectedBellPostPin (170 lines, NEW, cone 3/3)
221. QICLean.Representation.SelectedBellPostInverseTransport (133 lines, NEW, cone 1/1)
222. QICLean.Representation.SchmidtBellSharpUpper (152 lines, NEW, cone 1/1)
223. QICLean.Representation.ReplicaPrevectorSharpUpper (163 lines, NEW, cone 1/1)
224. QICLean.Representation.ReplicaTransport.RootCompression (104 lines, NEW, cone 1/1)
225. TNLean.Algebra.MatrixReindexGap (73 lines, NEW, cone 1/3)
226. TNLean.Circuit.SiteExpectationOrder (151 lines, PARTIAL, cone 0/11) (skip?)
227. TNLean.PEPS.AreaLaw.Amplification.LocalRootChannels (267 lines, PARTIAL, cone 0/17) (skip?)
228. TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector (150 lines, NEW, cone 1/1)
229. TNLean.PEPS.AreaLaw.GlobalSchmidtBellRoughLower (211 lines, NEW, cone 1/1)
230. TNLean.PEPS.AreaLaw.LatticeConstraints (323 lines, PARTIAL, cone 0/6) (skip?)
231. TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails (202 lines, PARTIAL, cone 0/3) (skip?)
232. TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions (90 lines, NEW, cone 6/6)
233. TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates (171 lines, NEW, cone 7/8)
234. TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaMetricCoordinates (109 lines, NEW, cone 2/2)
235. TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties (106 lines, NEW, cone 1/2)
236. TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression (152 lines, NEW, cone 2/2)
237. TNLean.PEPS.AreaLaw.Scan.FrontThresholds (39 lines, NEW, cone 1/1)
238. TNLean.PEPS.AreaLaw.Scan.PrefixComparison (185 lines, NEW, cone 9/10)
239. TNLean.PEPS.AreaLaw.Scan.PrefixFiniteFamily (44 lines, NEW, cone 2/2)
240. TNLean.PEPS.AreaLaw.Scan.FrontPrefixFamily (39 lines, NEW, cone 1/1)
241. TNLean.PEPS.AreaLaw.Scan.ReceivingRegions (169 lines, NEW, cone 6/6)
242. TNLean.PEPS.AreaLaw.Scan.PrefixCardinality (154 lines, NEW, cone 3/3)
243. TNLean.PEPS.AreaLaw.Scan.PrefixApproximation (111 lines, NEW, cone 2/2)
244. TNLean.PEPS.AreaLaw.Scan.PrefixBoundary (139 lines, NEW, cone 0/6) (skip?) [needs bridge: TemplateCutBoundary, EdgeBoundaryCalculus]
245. TNLean.PEPS.AreaLaw.Scan.StatusCutBounds (170 lines, NEW, cone 1/5)
246. TNLean.PEPS.AreaLaw.Scan.ActualRoughUpper (325 lines, NEW, cone 1/1)
247. TNLean.PEPS.AreaLaw.Scan.StatusMarginalBudget (146 lines, NEW, cone 1/4)
248. TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments (166 lines, NEW, cone 0/4) (skip?)
249. TNLean.PEPS.AreaLaw.TwoFamilies (153 lines, PARTIAL, cone 2/7) [needs bridge: Templates]
250. TNLean.PEPS.AreaLaw.Scan.ActualSharpUpper (952 lines, NEW, cone 13/13)
