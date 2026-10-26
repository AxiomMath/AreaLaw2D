# Merge notes: v2 candidate

This branch (`ruiz/v2-merge`) merges the restructured proof body of AreaLaw2D-internal
(`main`, commit 65fcc00) into the public repository (v1, `main`, commit 1e91b65, tag `v1.0`),
and restores what v1 has that the restructuring dropped.

Sources:

- v1: public `main`, commit 1e91b65.
- v2: internal `main`, commit 65fcc00.
- 3D: branch `ruiz/3d-targets`, commit 17c87f8. This branch is not on the public remote; it
  exists only as a local branch of the maintainer's clone of the public repository, and was
  fetched from there without modifying it.

## Step 1: merge

`git merge internal/main`. The merge base of the two histories is 1e91b65 itself (v2 was
branched from the tip of v1 and v1 has no later commits), so git applied every v2 change
without a conflict and the merged tree is exactly v2's tree at 65fcc00. No conflict had to be
resolved by hand.

Taken from v2 (all of it, as the merge base had nothing newer):

- `AreaLaw/` (161 files) and `AreaLaw.lean`, `AreaLawForMathlib/` (143 files) and
  `AreaLawForMathlib.lean`: the restructured proof body.
- `blueprint/`, `digest/`, `paper/`, `Map.md`, `RefactoringPlan.md`, `RefactoringResult.md`,
  `scripts/` (including `scripts/audit.lean` and `scripts/lint/`), `.github/workflows/`.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` (the Lean and Mathlib pins are
  unchanged at v4.33.0; the manifest gains the local `lintall` package).
- `OpenAI/Statements.lean` with its two first import lines re-pointed (handled again in Step 2).
- `Solution/Basic.lean` re-pointed to `AreaLaw.areaLaw` (see Step 3).
- `docs/StatementAudit.md` with one line changed (see Step 3).
- `README.md` (reworked in Step 5).
- v2's deletions under `OpenAI/` (918 of 919 files; only `Statements.lean` remains) and of
  `Arealaw/` (35 files) and `Arealaw.lean`, accepted for now as instructed.
- v2's deletions of `HISTORY.md`, `docs/oai265/`, `docs/README-quantum-arealaw.md` and
  `docs/charter-quantum-arealaw.md`, all reverted in Step 3.

Taken from v1 at this step: nothing beyond the common history; v1's files that v2 kept
unchanged (`Challenge/`, `Comparator/`, `LICENSE`, `NOTICE`) are identical on both sides.

## Step 2: statement layer

- `OpenAI/Statements.lean`: v2's file already differs from v1 only in its two first import
  lines (`Arealaw.Mixed` becomes `AreaLawForMathlib.QuantumInfo.Region.State`, `Arealaw.TraceDist`
  becomes `AreaLawForMathlib.QuantumInfo.Region.TraceDistance`; both files keep the `Arealaw`
  namespace and the declaration names the statements use). Kept as is. The diff check is in
  Step 6.
- The 3D files are handled in their own commit; see "Step 2, 3D files" below.

## Step 3: restored from v1

- `HISTORY.md`: restored from 1e91b65, unchanged.
- `docs/oai265/`: restored from 1e91b65 as an archived working record. One line added at the top
  of `docs/oai265/Memory.md` (the folder has no README) saying it describes the v1 tree.
- `docs/README-quantum-arealaw.md` and `docs/charter-quantum-arealaw.md`: v1 has them and v2
  deleted them; restored unchanged, as part of keeping what the restructuring dropped.
- `docs/StatementAudit.md`: the copies differ in one line. v2 replaced the reference to
  `docs/oai265/Memory.md` by "`RefactoringResult.md` §2 and §5". Since `docs/oai265/Memory.md` is
  restored, v1's copy is taken. Its only file references are `OpenAI/Statements.lean` and
  `docs/oai265/Memory.md`, neither of which moved, so no reference had to be re-pointed (no
  change made). The section headings name the v1 proof declarations (`area_law`,
  `collar_bound`, ...); their v2 names are in `OpenAI/Audit.lean` (Step 4) and `Map.md`. Left as
  an open decision below.
- `Challenge/` and `Comparator/`: identical on both sides, kept.
- `Solution/Basic.lean`: v2 changed only the import (`AreaLaw.Transfer`) and the proof term
  (`AreaLaw.areaLaw 𝕜 q R J Δ hq hJ hΔ` in place of `OpenAI.area_law q R J Δ hq hJ hΔ`); the
  statement is unchanged. v2's copy kept.
- `NOTICE`: the "Portions of OpenAI/" line now names `AreaLaw/` (chiefly
  `AreaLaw/S06_Replicas/Ported/`) and `AreaLawForMathlib/` (chiefly
  `RepresentationTheory/SchurWeyl/` and `Analysis/Matrix/`); one sentence added for files that
  hold only some ported declarations. The quantum-arealaw contributors line is unchanged.

### Port headers

v1 has 856 Lean files whose header carries `Ported from`, `Adapted from`, `Ported and adapted
from` or `Ported and specialized from` (any case). For each, the declarations were extracted
(namespace qualified) and looked up in v2; a v2 file counts as a descendant of a v1 file when
the v1 file supplies at least half of the v2 file's declarations, or at least half of its own
declarations (two or more) land there. Git rename detection over the same pair (117 renames)
was used as a cross check: every renamed v1 file with a header has one in v2 now.

v2 kept the header in 41 files. The `Copyright (c) 2026 TNLean/QICLean contributors` blocks
survived everywhere, but the `Ported from` lines were dropped in the files listed here.

Files that lost their header and got it back (95; the v1 header paragraph is restored verbatim in the module docstring; with several v1 sources each paragraph is prefixed by the v1 file it comes from):

- `AreaLaw/S04_Quasilocal/Positive.lean` from `OpenAI/MatrixSqrtKernel.lean`
- `AreaLaw/S05_Conditional/Interpolation.lean` from `OpenAI/ConditionalMovement/ThreeLines.lean`
- `AreaLaw/S06_Replicas/Ported/CoherentSymbol.lean` from `OpenAI/CoherentSymbol.lean`
- `AreaLaw/S06_Replicas/Ported/CoherentSymbolFunction.lean` from `OpenAI/CoherentSymbolFunction.lean`
- `AreaLaw/S06_Replicas/Ported/CoherentSymbolLimit.lean` from `OpenAI/CoherentSymbolLimit.lean`
- `AreaLaw/S06_Replicas/Ported/GroupedLabelEntropy.lean` from `OpenAI/GroupedLabelEntropy.lean`
- `AreaLaw/S06_Replicas/Ported/GroupedLabelSymmetricSupport.lean` from `OpenAI/GroupedLabelSymmetricSupport.lean`
- `AreaLaw/S06_Replicas/Ported/InjectionAverage.lean` from `OpenAI/InjectionAverage.lean`
- `AreaLaw/S06_Replicas/Ported/InjectionPoly.lean` from `OpenAI/InjectionPoly.lean`
- `AreaLaw/S06_Replicas/Ported/InjectionProduct.lean` from `OpenAI/InjectionProduct.lean`
- `AreaLaw/S06_Replicas/Ported/MarkedSimilaritySymbol.lean` from `OpenAI/MarkedSimilaritySymbol.lean`
- `AreaLaw/S06_Replicas/Ported/MarkedStar.lean` from `OpenAI/MarkedStar.lean`
- `AreaLaw/S06_Replicas/Ported/MarkedSymbol.lean` from `OpenAI/MarkedSymbol.lean`
- `AreaLaw/S06_Replicas/Ported/MergeExponential.lean` from `OpenAI/MergeExponential.lean`
- `AreaLaw/S06_Replicas/Ported/RegionPowerSymbol.lean` from `OpenAI/RegionPowerSymbol.lean`
- `AreaLaw/S06_Replicas/Ported/RelativePinAlgebra.lean` from `OpenAI/RelativePinAlgebra.lean`
- `AreaLaw/S06_Replicas/Ported/RelativePinCommute.lean` from `OpenAI/RelativePinCommute.lean`
- `AreaLaw/S06_Replicas/Ported/RelativePinCompensator.lean` from `OpenAI/RelativePinCompensator.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaDisjointMetricPositivity.lean` from `OpenAI/ReplicaDisjointMetricPositivity.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaGammaIntegral.lean` from `OpenAI/ReplicaGammaIntegral.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaGroupedInverse.lean` from `OpenAI/ReplicaGroupedInverse.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaIntegral.lean` from `OpenAI/ReplicaIntegral.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaLift.lean` from `OpenAI/ReplicaLift.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaMarkedRatio.lean` from `OpenAI/ReplicaMarkedRatio.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaMarkedRatioInverse.lean` from `OpenAI/ReplicaMarkedRatioInverse.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaMetric.lean` from `OpenAI/ReplicaMetric.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaRatio.lean` from `OpenAI/ReplicaRatio.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaRegionUnion.lean` from `OpenAI/ReplicaRegionUnion.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaSimilarity.lean` from `OpenAI/ReplicaSimilarity.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaSpectralLaw.lean` from `OpenAI/ReplicaSpectralLaw.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaSymmetricMetricFloor.lean` from `OpenAI/ReplicaSymmetricMetricFloor.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaWeight.lean` from `OpenAI/ReplicaWeight.lean`
- `AreaLaw/S06_Replicas/Ported/ReplicaWholeInverse.lean` from `OpenAI/ReplicaWholeInverse.lean`
- `AreaLaw/S06_Replicas/Ported/SchurSurprisal.lean` from `OpenAI/SchurSurprisal.lean`
- `AreaLaw/S06_Replicas/Ported/StarFunction.lean` from `OpenAI/StarFunction.lean`
- `AreaLaw/S06_Replicas/Ported/UniformHusimi.lean` from `OpenAI/UniformHusimi.lean`
- `AreaLaw/S06_Replicas/Symbol.lean` from `OpenAI/EntropyContinuity.lean`
- `AreaLaw/S07_Transport/Histories.lean` from `OpenAI/ReplicaTransportStates.lean`
- `AreaLaw/S07_Transport/Means.lean` from `OpenAI/TreeDerivative.lean`
- `AreaLawForMathlib/Analysis/CStarAlgebra/SqrtHolder.lean` from `OpenAI/SqrtHolder.lean`
- `AreaLawForMathlib/Analysis/Matrix/CompressedInverse.lean` from `OpenAI/InverseCompressionLowerPin.lean`
- `AreaLawForMathlib/Analysis/Matrix/GeometricMeanCongruence.lean` from `OpenAI/Transport/EnergyBlock.lean`
- `AreaLawForMathlib/Analysis/Matrix/OperatorConvexity.lean` from `OpenAI/OperatorConvexity.lean`
- `AreaLawForMathlib/Analysis/Matrix/SkewAbsReduction.lean` from `OpenAI/ReplicaTransportEnergy.lean`
- `AreaLawForMathlib/Analysis/Matrix/TraceCompression.lean` from `OpenAI/TraceCompression.lean`
- `AreaLawForMathlib/Analysis/ODE/LiebRobinson.lean` from `OpenAI/LiebRobinson/CommutatorRecursion.lean`
- `AreaLawForMathlib/Analysis/SpecialFunctions/BetaHalfLine.lean` from `OpenAI/BetaHalfLine.lean`
- `AreaLawForMathlib/QuantumInfo/SiteSupport.lean` from `OpenAI/ReplicaSupport.lean`
- `AreaLawForMathlib/RepresentationTheory/PermutationRepresentation.lean` from `OpenAI/IrrepLabels.lean`, `OpenAI/LabelProjectors.lean`, `OpenAI/PermutationRepresentation.lean`, `OpenAI/TensorPowerAction.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/Alternant.lean` from `OpenAI/Alternant.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/BranchProbability.lean` from `OpenAI/BranchProbability.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/Branching.lean` from `OpenAI/Branching.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/BranchingPieri.lean` from `OpenAI/BranchingPieri.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/Casimir.lean` from `OpenAI/Casimir.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/CentralLabelFunction.lean` from `OpenAI/CentralLabelFunction.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/CoherentMeasure.lean` from `OpenAI/CoherentMeasure.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/CoherentResolution.lean` from `OpenAI/CoherentResolution.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/ColumnAntisymmetrizer.lean` from `OpenAI/ColumnAntisymmetrizer.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/CommutantDimension.lean` from `OpenAI/CommutantDimension.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/CopySplit.lean` from `OpenAI/SupportedSubsystemLabelDimension.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/ExteriorPieri.lean` from `OpenAI/ExteriorPieri.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/GroupedCopies.lean` from `OpenAI/GroupedCopies.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/HermitianCfcSpectral.lean` from `OpenAI/HermitianCfcSpectral.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/HighestWeight.lean` from `OpenAI/HighestWeight.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/HookDimension.lean` from `OpenAI/HookDimension.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/HookFormula.lean` from `OpenAI/HookFormula.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/HookRecursion.lean` from `OpenAI/HookRecursion.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/HusimiIdentity.lean` from `OpenAI/HusimiIdentity.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/IrrepLabelCount.lean` from `OpenAI/IrrepLabelCount.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/IsotypicDimension.lean` from `OpenAI/IsotypicDimension.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/JointIsotypic.lean` from `OpenAI/JointIsotypic.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/JointResolution.lean` from `OpenAI/SchurSurprisal.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/MergeDimensions.lean` from `OpenAI/MergeDimensions.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/MergeMoment.lean` from `OpenAI/MergeMoment.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/OrthogonalResolution.lean` from `OpenAI/OrthogonalResolution.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/PartitionCount.lean` from `OpenAI/PartitionCount.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/RegularTrace.lean` from `OpenAI/RegularTrace.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SchurLabelCommutation.lean` from `OpenAI/SchurLabelCommutation.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SchurLabelEstimates.lean` from `OpenAI/SchurLabelEstimates.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SchurWeylCommutant.lean` from `OpenAI/SchurWeylCommutant.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SchurWeylLabels.lean` from `OpenAI/SchurWeylLabels.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SchurWeylLift.lean` from `OpenAI/SchurWeylLift.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SiteOp.lean` from `OpenAI/ReplicaSiteOp.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SplitCopies.lean` from `OpenAI/SplitCopies.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/StarOperator.lean` from `OpenAI/StarOperator.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/SubsystemTransport.lean` from `OpenAI/SubsystemTransport.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/TensorPowerAction.lean` from `OpenAI/TensorPowerAction.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/TensorPowerRpow.lean` from `OpenAI/TensorPowerRpow.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/TrivialLabel.lean` from `OpenAI/TrivialLabel.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/UnitaryCommutant.lean` from `OpenAI/UnitaryCommutant.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/UnitaryHaar.lean` from `OpenAI/UnitaryHaar.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/UnitaryTwirl.lean` from `OpenAI/UnitaryTwirl.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/WeylCharacter.lean` from `OpenAI/WeylCharacter.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/WeylDimension.lean` from `OpenAI/WeylDimension.lean`
- `AreaLawForMathlib/RepresentationTheory/SchurWeyl/WeylRecursion.lean` from `OpenAI/WeylRecursion.lean`

Files that hold only some declarations of a v1 file with a header (41; a one paragraph note names the v1 files and the source projects):

- `AreaLaw/S02_Preliminaries.lean` from `OpenAI/MarginalPhaseQuadratic.lean`
- `AreaLaw/S03_InitialBox/BufferDiscount.lean` from `OpenAI/Geometry/TemplateCollar.lean`, `OpenAI/LogClipping.lean`, `OpenAI/Rectangles.lean`
- `AreaLaw/S03_InitialBox/Filters.lean` from `OpenAI/FilterClipping.lean`, `OpenAI/FilterStationarity.lean`
- `AreaLaw/S03_InitialBox/Lemma32.lean` from `OpenAI/BufferDiscount.lean`
- `AreaLaw/S03_InitialBox/MarginalTails.lean` from `OpenAI/ModularExpectation.lean`, `OpenAI/SchmidtTilt.lean`
- `AreaLaw/S03_InitialBox/ZeroFloorPinning.lean` from `OpenAI/RegionLift.lean`, `OpenAI/SchmidtPinning.lean`
- `AreaLaw/S04_Quasilocal/CenteredFilter.lean` from `OpenAI/SpectralFilter/MatrixFilter.lean`
- `AreaLaw/S04_Quasilocal/Crossing.lean` from `OpenAI/CrossingBudget.lean`, `OpenAI/Scan/DesignatedSampling.lean`
- `AreaLaw/S04_Quasilocal/Locality.lean` from `OpenAI/SpectralFilter/FilterLocality.lean`
- `AreaLaw/S04_Quasilocal/Propagation.lean` from `OpenAI/LiebRobinson/GraphPropagation.lean`
- `AreaLaw/S04_Quasilocal/Setup.lean` from `OpenAI/ConditionalExpectation.lean`
- `AreaLaw/S05_Conditional/Compression.lean` from `OpenAI/ResolventDefect.lean`, `OpenAI/ResolventMellin.lean`
- `AreaLaw/S05_Conditional/Movement/Analytic.lean` from `OpenAI/ConditionalSkewValues.lean`, `OpenAI/MatrixSqrt.lean`, `OpenAI/ResolventDefect.lean`
- `AreaLaw/S05_Conditional/Movement/Region.lean` from `OpenAI/MarginalPhaseSupport.lean`
- `AreaLaw/S05_Conditional/SkewAnalytic.lean` from `OpenAI/SkewFromPhases.lean`
- `AreaLaw/S05_Conditional/Spectral.lean` from `OpenAI/PurificationSplitting.lean`
- `AreaLaw/S06_Replicas/RelativePin.lean` from `OpenAI/ConditionalMovementEstimate.lean`, `OpenAI/MatrixKroneckerContraction.lean`, `OpenAI/ReplicaEtaForms.lean`
- `AreaLaw/S07_Transport/Endpoints.lean` from `OpenAI/Transport/Derivative.lean`
- `AreaLaw/S07_Transport/Energy.lean` from `OpenAI/BlockDiagonal.lean`, `OpenAI/Transport/EnergyBlock.lean`, `OpenAI/Transport/ErrorFourier.lean`, `OpenAI/TreeDerivative.lean`
- `AreaLaw/S07_Transport/EntropyGain.lean` from `OpenAI/ReplicaTransportEntropyGain.lean`, `OpenAI/ReplicaTransportRelativePinBound.lean`
- `AreaLaw/S07_Transport/ExactDerivative.lean` from `OpenAI/Transport/Commutant.lean`, `OpenAI/Transport/Derivative.lean`
- `AreaLaw/S07_Transport/States.lean` from `OpenAI/ReplicaTransportSetup.lean`
- `AreaLaw/S09_Scanner/Scanner/Entropy.lean` from `OpenAI/ReplicaTransportEnergy.lean`, `OpenAI/Scan/ActualChargeEntropySum.lean`, `OpenAI/Scan/OldStateIntegral.lean`, `OpenAI/Scan/SplitEntropyBound.lean`
- `AreaLaw/S09_Scanner/Templates.lean` from `OpenAI/Geometry/TemplateCollar.lean`, `OpenAI/Rectangles.lean`
- `AreaLaw/S10_Amplification/Channels.lean` from `OpenAI/LiebRobinson/GraphBallStabilization.lean`
- `AreaLaw/S10_Amplification/ExcitedDecay.lean` from `OpenAI/Transport/ErrorFourier.lean`
- `AreaLaw/S10_Amplification/Lemma101.lean` from `OpenAI/Amplification/ConstraintWordTruncation.lean`, `OpenAI/Amplification/GraphChannelWeightedRow.lean`
- `AreaLaw/S10_Amplification/Restoring.lean` from `OpenAI/FinSum.lean`, `OpenAI/RestoringNorm.lean`
- `AreaLaw/S11_Geometry/Primaries.lean` from `OpenAI/Geometry/PrimaryRegions.lean`
- `AreaLaw/S11_Geometry/RepairScales.lean` from `OpenAI/Geometry/RepairDepth.lean`
- `AreaLaw/Transfer.lean` from `OpenAI/BufferDiscount.lean`, `OpenAI/Scan/MarginalTailsBridge.lean`
- `AreaLawForMathlib/Analysis/CStarAlgebra/Matrix.lean` from `OpenAI/ConditionalSkewPhaseCore.lean`, `OpenAI/FilterMaximizer.lean`, `OpenAI/MatrixKroneckerContraction.lean`, `OpenAI/RestoringVectors.lean`
- `AreaLawForMathlib/Analysis/Matrix/AdjointLogFunction.lean` from `OpenAI/Transport/ErrorFourier.lean`
- `AreaLawForMathlib/Analysis/Matrix/AuxiliaryBlock.lean` from `OpenAI/MarginalPhaseSupport.lean`, `OpenAI/Transport/EnergyBlock.lean`
- `AreaLawForMathlib/Analysis/Matrix/CommutingProductLog.lean` from `OpenAI/CfcLogListProduct.lean`, `OpenAI/ReplicaTransportEntropyGain.lean`, `OpenAI/ReplicaTransportRelativePinBound.lean`
- `AreaLawForMathlib/Analysis/Matrix/MatrixProjectionAux.lean` from `OpenAI/MatrixIntertwine.lean`
- `AreaLawForMathlib/Analysis/Matrix/SpecPow.lean` from `OpenAI/FilterPower.lean`, `OpenAI/ModularExpectation.lean`
- `AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean` from `OpenAI/ConditionalEntropy.lean`
- `AreaLawForMathlib/QuantumInfo/Region.lean` from `OpenAI/PureStateTraceDistance.lean`
- `AreaLawForMathlib/QuantumInfo/Region/State.lean` from `OpenAI/IidSurprisal.lean`
- `AreaLawForMathlib/QuantumInfo/RegionToComplex.lean` from `OpenAI/ConditionalExpectation.lean`

Not changed: `AreaLawForMathlib/RepresentationTheory/SchurWeyl/JucysRecursion.lean` (its v1
file had the TNLean copyright block but no port line; the block is still there), and
`SchurWeyl/LabelObservableCalculus.lean` and `SchurWeyl/ProductVectorMarginal.lean` (new in v2,
no v1 declarations).

## Internal tool names removed

The rule that no file names an AI model or agent product (beyond the v1 provenance sentence)
required these changes to v2's material:

- `.axiomcode/bugs/` (19 files): deleted. They are bug reports about the agent tooling used on
  v2, name its products throughout, and are not part of the formalization.
- `.gitignore`: the four lines for the tool's scratch directory removed.
- `Map.md` (14 lines) and `RefactoringResult.md` (38 lines): tool names replaced by neutral
  wording, nothing else changed. A named search service became "semantic search" (its glob mode
  "glob search"); a named remote build service and its diagnostics call became "remote route",
  "remote diagnostics", "a hosted build workspace" and "a remote comparator run"; references to
  the internal issue tracker became "an internal issue"; the tool's lock and scratch paths were
  dropped (`flock <lock> lake build` became `lake build`); a named root synchronization tool
  became "the root synchronization script"; one pointer to a deleted bug report was dropped.
  `loogle` (a public Lean community tool) is kept. The `agents/<id>` branch names in
  `RefactoringResult.md` and in v1's `HISTORY.md` are git branch names, not product names, and are
  kept.

## Step 2, 3D files

Taken from `ruiz/3d-targets` (17c87f8):

- `OpenAI/Statements3D.lean` and `OpenAI/Audit3D.lean`: byte identical to the branch. Their only
  imports (`OpenAI.Statements`, `OpenAI.Cylinder3D`) still exist, so no import had to change.
- `OpenAI/Cylinder3D.lean`: only the import lines changed. `OpenAI.AreaLaw`,
  `OpenAI.CutTransport` and `OpenAI.SupportCounting` no longer exist; they are replaced by
  `OpenAI.Cylinder3DSupport` (`OpenAI.Statements3D` is kept). Everything after the imports is
  byte identical to the branch (checked with `diff`).
- `OpenAI/Cylinder3DSupport.lean` (new, differs from both parents): the proof of Cylinder3D uses
  declarations of v1 that the restructuring removed (`regionEntropy_pureState`, `coeffMatrix`,
  `EE`, `EE_transpose`, `EE_submatrix_id_equiv`, `domainEDist_of_mem`, `mem_supports_iff`,
  `mem_edgeBoundary`, `extendId_sum`, `l2_opNorm_extendId_le`, `card_le_of_mem_supports`, the
  `𝕜` versions `Arealaw.MState.regionEntropy_union_le` and `regionEntropy_le_card_mul_log`, and
  `OpenAI.area_law`). This module restores them, with what they need, under their v1 names and
  with their v1 proofs. Two proofs differ from v1: `OpenAI.area_law` is
  `AreaLaw.areaLaw 𝕜 q R J Δ hq hJ hΔ`, and `Arealaw.MState.regionEntropy_union_le` goes
  through `AreaLawForMathlib/QuantumInfo/StateToComplex.lean` instead of v1's
  `OpenAI/Embedding.lean`. `exists_walk_length_le_iff_edist_le` keeps its v1 docstring, which
  cites TNLean.
- `docs/3D/Targets.md`: copied unchanged, since both Statements3D and Cylinder3D cite it.
- `lakefile.toml`: the `OpenAI` library roots become `OpenAI.Statements`,
  `OpenAI.Statements3D`, `OpenAI.Cylinder3DSupport`, `OpenAI.Cylinder3D` (v2 had only the
  first; the audit files are run with `lake env lean` and are not roots).

Types of the two theorems after the merge (`#check`), identical to their source signatures,
which are unchanged:

```
@OpenAI.cylinderAreaLawOfPlanar3D : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (h : ℕ),
  OpenAI.CylinderAreaLawOfPlanar3D 𝕜 q R J Δ h
@OpenAI.cylinderAreaLaw3D : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (h : ℕ),
  0 < Δ → OpenAI.CylinderAreaLaw3D 𝕜 q R J Δ h
```
