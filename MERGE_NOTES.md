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

- The tool state directory with its `bugs/` folder (19 files): deleted. They are bug reports about the agent tooling used on
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

## Step 4: audit

`OpenAI/Audit.lean` is rebuilt for v2. v1's file has 4309 `#print axioms` lines
(4304 distinct names). Each name was looked up in the environment of the merged tree
(`AreaLaw`, `AreaLawForMathlib`, `OpenAI.Cylinder3D`, `Solution.Basic`) by a Lean script; a name
that is gone was renamed when `Map.md` lists it first in the "Lean declaration(s) now" cell of
an anchor row whose Step 1 note names a v2 anchor declaration (`lemma_`, `prop_`, `step_`, `eq_`,
`theorem_` or `corollary_`) that exists.

| | count |
| --- | --- |
| kept under the same name | 1331 |
| renamed (v1 names) | 72 |
| renamed (distinct v2 anchors) | 71 |
| dropped | 2901 |
| `#print axioms` lines in the new file | 1416 |

The new file prints the 13 frozen results of `scripts/audit.lean`, the 2 theorems of
`OpenAI/Audit3D.lean`, the renamed anchors not already printed, and the kept names in v1's
order and groups (v1's group comments are kept; its expected output comments are not, since
`lake env lean` prints them). Of the kept names, 10 exist again only because
`OpenAI/Cylinder3DSupport.lean` restores them (for example `OpenAI.area_law`,
`OpenAI.mem_supports_iff`). Dropped names by leading namespace:

`OpenAI` 872, `Matrix` 734, `TensorPower` 492, `ConditionalMovement` 323, `Entropy` 282, `FiniteProduct` 76, `Real` 20, `Arealaw` 18, `Partition` 18, `PermutationRepresentation` 16, `Complex` 13, `TNLean` 6, `SpectralFilter` 4, `Fintype` 4, `NormedRing` 3, `IsStarProjection` 2, `IsOrthogonalProjection` 2, `finite_volterra_le_weight_mul_exp` 1, `Commute` 1, `IsPositiveMap` 1, `singleKrausMap_comp` 1, `MonoidAlgebra` 1, `isOrthogonalProjection_posSemidef` 1, `isOrthogonalProjection_sum_of_pairwise_mul_eq_zero` 1, `orthogonalProjection_mul_eq_zero_of_sum_eq_one` 1, `Finset` 1, `integral_inv_add_sub_inv_one_add` 1, `Asymptotics` 1, `Fin` 1, `LinearIndependent` 1, `MaximallyEntangled` 1, `quantumRelativeEntropy_product_marginals` 1, `Nat` 1.

Renamed (v1 name, Map.md row, v2 anchor):

- `OpenAI.regionEntropy_eq_zero_of_edgeBoundary_eq_empty` (D2.12) → `AreaLaw.lemma_2_2`
- `OpenAI.regionEntropy_eq_zero_of_range_zero` (D2.11) → `AreaLaw.step_2_11`
- `OpenAI.two_family_cancellation` (D11.1) → `AreaLaw.lemma_11_1`
- `OpenAI.two_family_decomposition` (D11.4) → `AreaLaw.Geometry.prop_11_2`
- `OpenAI.norm_deriv_le_of_phase` (D5.18) → `AreaLaw.step_5_18`
- `OpenAI.norm_sub_re_le_of_phase_bounds` (D5.19) → `AreaLaw.step_5_19`
- `OpenAI.exists_max_feasible_chain` (D3.7) → `AreaLaw.step_3_7_1`
- `OpenAI.pow_sqrt_mul_chainOptimum_le` (D3.11) → `AreaLaw.step_3_11_2`
- `OpenAI.neg_two_mul_log_le_entropy` (D3.13) → `AreaLaw.eq_initial_norm_upper`
- `OpenAI.two_mul_condEntropy_le` (D3.14) → `AreaLaw.step_3_14_1`
- `OpenAI.condEntropy_le_initialBuffer_of_constants` (D3.5) → `AreaLaw.step_3_5`
- `OpenAI.quasilocal_roots` (D4.10) → `AreaLaw.lemma_4_4`
- `OpenAI.IsAdmissible.sum_norm_extendId_containing_le` (D4.3) → `AreaLaw.step_4_3`
- `Matrix.exists_posSemidef_gap_of_norm_sub_le` (D4.13) → `AreaLaw.step_4_13`
- `Matrix.MeanTree.eval_star_conj` (D7.3) → `AreaLaw.Transport.lemma_7_1`
- `Matrix.MeanTree.eval_listProd_ofFn` (D7.17) → `AreaLaw.Transport.Round.step_7_17`
- `Matrix.Transport.exists_auxBlock` (D7.21) → `AreaLaw.Transport.Round.step_7_21`
- `Matrix.Transport.norm_sq_errorVec_le` (D7.23) → `AreaLaw.Transport.Round.step_7_23`
- `TensorPower.ReplicaTransport.relativePinBound` (D7.18) → `AreaLaw.Transport.step_7_18`
- `TensorPower.ReplicaTransport.transport` (D7.14) → `AreaLaw.Transport.prop_7_4`
- `Real.bellOverlapRemainder` (D8.37) → `AreaLaw.Comparators.prop_8_1`
- `ConditionalMovement.LocalMove.paired_three_lines` (D5.11) → `AreaLaw.step_5_11`
- `ConditionalMovement.ConditionalCollision.collision_le` (D5.2) → `AreaLaw.step_5_2_1`
- `ConditionalMovement.ConditionalCollision.one_filter_entropy_bound` (D5.4) → `AreaLaw.step_5_4_of`
- `ConditionalMovement.ConditionalCollision.conditional_optimizer_root_stability` (D5.7) → `AreaLaw.step_5_7`
- `ConditionalMovement.MatrixInterpolation.modular_state_distance` (D5.9) → `AreaLaw.step_5_9_of`
- `ConditionalMovement.ConditionalCollision.left_boundary_trace` (D5.6) → `AreaLaw.step_5_6`
- `ConditionalMovement.ConditionalCollision.right_boundary_entropy` (D5.10) → `AreaLaw.step_5_10_1`
- `Entropy.conditionalMovement_norm_le` (D5.5) → `AreaLaw.lemma_5_1`
- `Matrix.ResolventCompression.defect_nonneg` (D5.13) → `AreaLaw.step_5_13`
- `Matrix.ResolventCompression.defect_le_invQuadA` (D5.14) → `AreaLaw.step_5_14`
- `Entropy.MarginalPhase.norm_phaseDifference_mulVec_le` (D5.12) → `AreaLaw.lemma_5_2`
- `Entropy.ConditionalSkew.imag_vector_eq` (D5.17) → `AreaLaw.step_5_17`
- `Entropy.ConditionalSkew.phaseRate_le` (D5.20) → `AreaLaw.step_5_20`
- `Entropy.ConditionalSkew.conditionalSkew_le` (D5.15) → `AreaLaw.lemma_5_3`
- `OpenAI.collarLeaf_entropy_identity` (D8.36) → `AreaLaw.Comparators.step_8_36`
- `OpenAI.abs_mutualInfo_sub_le` (D9.30) → `AreaLaw.Scanner.step_9_30`
- `OpenAI.card_mixedDyadicIndices_le` (D9.17) → `AreaLaw.Scanner.step_9_17`
- `OpenAI.templateEntropy_le_of_boxEntropy_le` (D9.18) → `AreaLaw.Scanner.step_9_18`
- `OpenAI.card_latticeDiamond` (D2.7) → `AreaLaw.eq_ball_count`
- `OpenAI.card_admissibleSupport_containing_le` (D2.8) → `AreaLaw.step_2_8`
- `TensorPower.exists_commonLabelCutoff_vector` (D8.18) → `AreaLaw.Comparators.step_8_18`
- `Matrix.floor_pin_le` (D8.32) → `AreaLaw.Comparators.step_8_32`
- `Matrix.MeanTree.smul_one_sub_add_smul_projection_le_eval` (D8.33) → `AreaLaw.Comparators.step_8_33`
- `TensorPower.exists_replicaPinnedFactor_le_exp` (D8.16) → `AreaLaw.Comparators.step_8_16`
- `Entropy.typicalSpectrum_entropy_bounds` (D8.3) → `AreaLaw.Comparators.step_8_3`
- `TensorPower.exists_label_sequence_mass_entropy_asymptotic` (D8.12) → `AreaLaw.Comparators.step_8_12`
- `Matrix.MeanTree.re_dotProduct_log_eval_ge_of_projection_mass` (D8.34) → `AreaLaw.Comparators.step_8_34`
- `Matrix.MeanTree.re_inner_log_eval_prod_le_of_projection` (D8.21) → `AreaLaw.Comparators.step_8_21`
- `Matrix.PosSemidef.log_re_trace_finKronecker_signed_label_moments_le` (D8.10) → `AreaLaw.Comparators.step_8_10`
- `Matrix.MeanTree.mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound` (D8.35) → `AreaLaw.Comparators.step_8_35`
- `Matrix.compression_le_of_replicaExcitationComponent_bounds` (D8.31) → `AreaLaw.Comparators.step_8_31`
- `Matrix.replicaExcitationComponent_goodAuxiliary_labelEntropy_lower` (D8.27) → `AreaLaw.Comparators.step_8_27`
- `Matrix.partialTraceLeft_typicalPureState_decomposition` (D8.17) → `AreaLaw.Comparators.step_8_17`
- `Matrix.selectedBellProjection_bellPinPrevector` (D8.14) → `AreaLaw.Comparators.step_8_14`
- `TensorPower.exists_replicaMetric_compressed_bell_inverse_norm_bound` (D8.20) → `AreaLaw.Comparators.step_8_20`
- `TensorPower.eventually_suppliedSchmidtBell_sharp_upper` (D8.8) → `AreaLaw.Comparators.prop_8_1`
- `TensorPower.selectedBellPost_inverse_norm_le_physical` (D8.15) → `AreaLaw.Comparators.step_8_15`
- `Matrix.exists_replicaExcitationComponent_inverse_sharp_le` (D8.30) → `AreaLaw.Comparators.step_8_30`
- `Matrix.replicaGoodConfigurationMarginal_exp_mergeDeficits_le` (D8.29) → `AreaLaw.Comparators.step_8_29`
- `OpenAI.Scan.exists_bootstrap_principal_energy_bound` (D9.22) → `AreaLaw.Scanner.step_9_22`
- `OpenAI.exists_latticeCrossingBudget` (D4.14) → `AreaLaw.step_4_14`
- `OpenAI.Scan.exists_sourceScan_selection` (D9.9) → `AreaLaw.Scanner.prop_9_2`
- `OpenAI.Scan.exists_sourceScan_selected_density` (D9.12) → `AreaLaw.Scanner.step_9_12`
- `OpenAI.Scan.exists_sourceScan_energy_le` (D9.13) → `AreaLaw.Scanner.step_9_13`
- `OpenAI.Scan.isSafe_test_geometry` (D9.21) → `AreaLaw.Scanner.step_9_21`
- `OpenAI.Scan.isTemplate_test_geometry` (D9.15) → `AreaLaw.Scanner.lemma_9_4`
- `OpenAI.Scan.eventually_final_collar_errors_le` (D9.29) → `AreaLaw.Scanner.step_9_29`
- `OpenAI.Scan.exists_bootstrap_comparison_cost_le` (D9.23) → `AreaLaw.Scanner.step_9_23`
- `OpenAI.Scan.isSafe_regionEntropy_le_of_boxEntropy_le` (D9.24) → `AreaLaw.Scanner.step_9_24`
- `OpenAI.improved_box_estimate` (D9.19) → `AreaLaw.Scanner.prop_9_5`
- `OpenAI.amplification` (D10.4) → `AreaLaw.prop_10_2`

## Step 5: README

v2's README is the base. Changes:

- A paragraph on the three-dimensional statements and the cylinder theorem under "What is
  proved".
- Tree table: rows for the 3D files, the audit files, `HISTORY.md` with `docs/oai265/`, and this
  file; the `Statements.lean` row says when it was frozen and that only its imports moved;
  `Map.md` row mentions the faithfulness record. The `scripts/audit.lean` row is merged into the
  audit row.
- "Building" becomes "Building and verification": v1's commands updated to the new tree
  (`OpenAI/AuditAreaLaw.lean` no longer exists; `scripts/audit.lean` covers it), plus
  `OpenAI/Audit3D.lean`; v2's `mk_all --check` kept. `OpenAI.lean` was regenerated with
  `lake exe mk_all` so that the check passes (it now imports the six `OpenAI/` modules; it is not
  a library root, so this does not add the audits to `lake build`).
- v1's no-`sorry` sentence and trust boundary paragraph, updated: the deviations are recorded in
  `docs/oai265/Memory.md` and `RefactoringResult.md` §2 and §5, and `docs/StatementAudit.md` is
  named as the clause by clause comparison.
- A Provenance section with the two paragraphs (v1, v2) and one line that the removed v1 code
  stays in tag `v1.0` and the ported code stays attributed (headers and `NOTICE`). The only
  tooling mention is the one of v1's provenance sentence.

## Step 6: acceptance

All four checks pass. Outputs as run on the final tree.

### (a) `lake build` of every library target

The lakefile declares the libraries `OpenAI`, `Challenge`, `Solution`, `AreaLaw` and
`AreaLawForMathlib`. The Mathlib pin did not change (v4.33.0); `lake exe cache get` reported
"No files to download". `lake build AreaLawForMathlib OpenAI AreaLaw Challenge Solution`:

```
⚠ [9080/9090] Replayed Challenge.Basic
warning: Challenge/Basic.lean:75:8: declaration uses `sorry`
warning: Challenge/Basic.lean:80:8: declaration uses `sorry`
warning: Challenge/Basic.lean:257:8: declaration uses `sorry`
Build completed successfully (9090 jobs).
```

No line of the log starts with `error`; the only warnings are the three below in (c).

### (b) the audits

`lake env lean OpenAI/Audit.lean` exits 0 and prints 1416 `depends on axioms` lines: 1407 with
`[propext, Classical.choice, Quot.sound]`, 8 with `[propext, Quot.sound]`, 1 with `[propext]`;
`sorryAx` occurs 0 times. The full output follows.

`lake env lean OpenAI/Audit3D.lean`:

```
'OpenAI.cylinderAreaLawOfPlanar3D' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.cylinderAreaLaw3D' depends on axioms: [propext, Classical.choice, Quot.sound]
```

<details><summary>Full output of <code>lake env lean OpenAI/Audit.lean</code> (1502 lines)</summary>

```
'OpenAI.Challenge.area_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.areaLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.areaLawCorollary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.positiveReplacement' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.collarBound_of_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.prop_9_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.amplification' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.twoFamilyCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Geometry.prop_11_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.conditionalContinuity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.marginalTails' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.bufferDiscount' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.initialBoxEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.cylinderAreaLawOfPlanar3D' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.cylinderAreaLaw3D' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.lemma_2_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_2_11' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.lemma_11_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_19' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_3_7_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_3_11_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.eq_initial_norm_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_3_14_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_3_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.lemma_4_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_4_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Transport.lemma_7_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Transport.Round.step_7_17' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Transport.Round.step_7_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Transport.Round.step_7_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Transport.step_7_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Transport.prop_7_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.prop_8_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_11' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_2_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_4_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_9_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_10_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.lemma_5_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_14' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.lemma_5_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_17' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_5_20' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.lemma_5_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_36' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_30' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_17' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.eq_ball_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_2_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_32' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_33' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_16' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_34' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_10' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_35' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_31' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_27' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_17' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_14' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_20' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_15' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_30' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Comparators.step_8_29' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_22' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.step_4_14' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.prop_9_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.lemma_9_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_29' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.step_9_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.Scanner.prop_9_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'AreaLaw.prop_10_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.inv_le_inv_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.instDecidableRelAdjSquareLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.graphNbhd_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.domainComponent_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.domainEDist_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.domainEDiam_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.squareLattice_adj_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.mem_edgeBoundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.mem_supports_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.exists_walk_length_le_iff_edist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.SubState.entropy_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.SubState.regionEntropy_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.SubState.mutualInfo_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.pureState_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.EE_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.regionEntropy_pureState' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.MState.regionEntropy_union_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.re_trace_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.exists_unitary_diagonal_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.MState.regionEntropy_le_card_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.sum_weyl_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.complementaryWeylTwirl_eq_smul_traceRight_kronecker_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.norm_complementaryWeylTwirl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.reindexedWeyl_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.inv_sq_smul_sum_sum_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.norm_sub_complementaryWeylTwirl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rootChannel_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.norm_mul_mul_sub_mul_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.norm_rootChannel_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rootChannel_eq_self_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.sqrt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenAI.condExpect_map_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'CFC.norm_abs_sub_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.abs_eq_inv_sqrt_smul_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.cfc_log_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.cfc_log_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.mul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.smul_one_le_mul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.pow_smul_one_le_list_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.star_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_mul_rpow_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_neg_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_half_mul_rpow_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.smul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.commute_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.commute_rpow_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.mul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.mul_rpow_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.cfc_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.cfc_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.cfc_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.trace_cfc_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.trace_cfc_eq_sum_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.spectralWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.sum_spectralWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.re_dotProduct_cfc_mulVec_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.re_dotProduct_mulVec_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.diagonal_jensen_of_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.reindexStarAlgHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpow_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.whiten' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.geomMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.one_geomMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_star_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_mono_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_mono_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.re_dotProduct_rpow_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.re_dotProduct_geomMean_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Commute.geomMean_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_mul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.commute_geomMean_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'singleKrausMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsNPositiveMap.zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsNPositiveMap.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsNPositiveMap.smul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsNPositiveMap.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'isNPositiveMap_singleKrausMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'nPositiveEval_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'nPositiveEval_eq_ampliation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.integral_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.integral_of_ae'' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsNPositiveMap.integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NormedRing.norm_inverse_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NormedRing.isUnit_and_norm_inverse_le_of_norm_inverse_mul_sub_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.cfc_rpowIntegrand₀₁_eq_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpowConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.integrableOn_rpowIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpow_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.exists_pos_smul_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.norm_ringInverse_smul_one_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isStrictlyPositive_smul_one_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isUnit_and_norm_ringInverse_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpowFDerivIntegrand_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.integrableOn_rpowFDerivIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasFDerivAt_integral_rpowIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.posSemidef_of_norm_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasFDerivWithinAt_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpowFDeriv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_rpowFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpowFDeriv_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.posDef_of_norm_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.eventually_posDef_nhdsWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasFDerivWithinAt_rpow_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_rpowDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpowDeriv_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.sandwichL_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_sandwichL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasFDerivWithinAt_geomMean_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasFDerivWithinAt_geomMean_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMeanDerivRight_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMeanDerivLeft_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_geomMeanDerivRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_geomMeanDerivLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.normalizedDerivMap_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_normalizedDerivMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.normalizedDerivMap_right_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.normalizedDerivMap_left_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_normalizedDerivMap_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isNPositiveMap_normalizedDerivMap_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isHermitian_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isHermitian_geomMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hermitianUnitaryPath_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.continuous_hermitianUnitaryPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hermitianUnitaryPath_mul_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.sinhRatio_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.sinhRatio_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.sinhRatioDensity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.hasDerivAt_sinhRatioDensityPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.sinhRatioDensity_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.tendsto_sinhRatioDensityPrimitive_atTop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.tendsto_sinhRatioDensityPrimitive_atBot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.integrable_sinhRatioDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.integral_sinhRatioDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.integral_boundary_rect_inv_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.integral_boundary_rect_eq_of_simple_poles' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.cosh_ofReal_add_ofReal_mul_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.cosh_two_pi_mul_add_cos_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.exists_continuousAt_div_sub_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.fourierIntegrand_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.differentiable_densityDenom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.deriv_densityDenom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.densityDenom_pole₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.densityDenom_pole₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.pole₁_ne_pole₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.deriv_densityDenom_pole₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.deriv_densityDenom_pole₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.differentiable_fourierNumer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.two_pi_I_mul_residues' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.fourierIntegrand_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.densityDenom_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.rectBoundaryIntegral_fourierIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.abs_sinh_le_norm_cosh' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.densityDenom_add_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.fourierIntegrand_add_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.norm_fourierIntegrand_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.integrable_fourierIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.norm_fourierIntegrand_vertical_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.tendsto_vertical_fourierIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.integral_exp_mul_sinhRatioDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.cos_mul_cosh_le_norm_densityDenom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.norm_sinhRatioDensity_half_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.norm_fourierIntegrand_half_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.densityDenom_half_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complex.integral_exp_mul_sinhRatioDensity_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.traceBilinForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.trace_tracelessPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.trace_traceAdjointMap_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.traceAdjointMap_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.traceAdjointMap_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsPositiveMap.map_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'isNPositiveMap_one_iff_isPositiveMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.of_forall_trace_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsPositiveMap.traceAdjointMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.cfc_fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpow_fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.fromBlocks_diag_mul_blockDiagProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.toBlocks₁₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isBlockDiagonalMap_sandwichL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.ringInverse_smul_one_add_fromBlocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isBlockDiagonalMap_rpowFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isBlockDiagonalMap_rpowDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isBlockDiagonalMap_geomMeanDerivRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isBlockDiagonalMap_geomMeanDerivLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsBlockDiagonalMap.normalizedDerivMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_eq_exp_smul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.hasDerivAt_rpow_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.uniqueDiffWithinAt_hermitianSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.differentiableWithinAt_rpow_neg_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.differentiableWithinAt_geomMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasFDerivWithinAt_geomMean_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasDerivAt_geomMean_of_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.hasDerivAt_geomMean_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMean_rpow_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMeanDerivLeft_sandwich_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.sinhRatio_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.rpow_mul_sinhRatio_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.quarter_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.norm_cexp_I_mul_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.integrable_cexp_mul_fourierWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.integral_fourierWeight_mul_re_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.star_eigU_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.eigU_mul_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.cfc_eq_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.rpow_eq_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.log_eq_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.imagPow_eq_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.star_mulVec_dotProduct_mulVec_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.conj_mulVec_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.quadForm_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.quadForm_imagPow_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.integrable_fourierWeight_mul_re_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.integrable_fourierWeight_mul_quadForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.filteredNormSq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.rpow_neg_half_mul_self_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.exists_hasDerivAt_rpow_neg_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.coeff_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.filteredNormSq_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.star_dotProduct_filteredRaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.star_dotProduct_filteredVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.relation_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.commute_ringInverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.sandwich_mul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.rpowDeriv_mul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMeanDerivRight_mul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.geomMeanDerivLeft_mul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.traceAdjointMap_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.commute_imagPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.mulVec_filteredVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'finTwoSumEquiv_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'finTwoSumEquiv_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'finTwoSumEquiv_symm_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'finTwoSumEquiv_symm_inr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsNPositiveMap.isPositiveMap_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'kadison_schwarz_twoPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.re_star_mulVec_dotProduct_le_of_twoPositive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.Transport.inner_imagPow_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.continuous_inner_imagPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.norm_inner_imagPow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.conjTranspose_imagPow_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.re_mul_dotProduct_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.imagPow_eq_cfc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.imagPow_fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.Transport.star_sumElim_zero_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.star_dotProduct_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.re_star_dotProduct_self_eq_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.norm_apply_le_one_of_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.isCompact_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.instIsHaarMeasureSubtypeComplexMemSubmonoidUnitaryGroupUnitaryHaar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.instIsProbabilityMeasureSubtypeComplexMemSubmonoidUnitaryGroupUnitaryHaar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.mul_pow_eq_mul_pow_of_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.mul_cfc_eq_mul_cfc_of_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.cfc_proj_mul_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.cfc_proj_mul_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.commute_proj_mul_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.proj_mul_add_one_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.commute_proj_mul_add_one_sub_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.proj_mul_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_proj_mul_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.whiten_proj_mul_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.le_whiten_proj_mul_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'MonoidAlgebra.invStar_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'MonoidAlgebra.coeff_invStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'MonoidAlgebra.invStar_invStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.conjTranspose_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_inv_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mul_inv_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_invStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_groupAlgebraRep_of_forall_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.commute_groupAlgebraRep_of_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MonoidAlgebra.exists_algEquiv_pi_matrix_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.instNeZeroNatDim' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.dim_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.wedderburnEquiv_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.wedderburnEquiv_matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_mul_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_mul_centralIdem_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.sum_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.matrixUnit_mul_matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.matrixUnit_mul_matrixUnit_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.sum_matrixUnit_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_mul_matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.eq_sum_matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.exists_wedderburnEquiv_eq_scalar_of_central' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.groupAlgebraRep_regular_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.groupAlgebraRep_regular_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.invStar_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mul_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mul_labelProj_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.sum_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.isHermitian_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_labelProj_groupAlgebraRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_labelProj_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_labelProj_of_forall_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.isHermitian_labelObservable' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelObservable_mul_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_labelObservable_of_forall_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.mem_invariantSubspace' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mul_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.symProj_mulVec_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.symProj_mulVec_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.coeff_conj_of_mem_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.coeff_inv_of_mem_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.centralIdem_mem_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.copyPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.subsystemPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.subsystemPerm_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_subsystemPerm_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.subsystemPerm_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.augmentation_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.augmentation_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.augmentation_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.augmentation_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.averagingElement_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.mul_averagingElement' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.augmentation_averagingElement' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.augmentation_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.averagingElement_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.exists_centralIdem_eq_averagingElement' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_averagingElement' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.exists_labelProj_eq_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.isStarProjection_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.posSemidef_of_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.mul_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.sum_smul_mul_sum_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.hom_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.trace_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.continuous_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.exp_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.prod_hom_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.prod_hom_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.isHermitian_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.posSemidef_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.posSemidef_hom_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.mem_eigenvalueSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.cfc_eq_sum_smul_spectralProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.isHermitian_spectralProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.isOrthogonalResolution_spectralProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.cfc_eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.commute_spectralProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp_of_ne_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.sum_matrixUnitOp_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mul_matrixUnitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_mulVec_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.dim_le_finrank_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_eq_finrank_range_of_mul_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.trace_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp_of_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.commute_matrixUnitOp_unitAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.unitAverage_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.matrixUnitOp_zero_mul_unitAverage_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.eq_zero_of_vecMulVec_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.sum_multiplicity_le_finrank_commutant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.apply_eq_of_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.finrank_commutant_le_card_pairOrbits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.pairType_copyPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_copyPerm_of_pairType_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_pairOrbits_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_multiplicity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_labelProj_ne_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.exists_eq_smul_of_commute_corner' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.exists_eq_sum_labelProj_of_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.partialTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.partialTensor_univ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.partialTensor_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.partialTensor_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.partialTensor_mul_partialTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_partialTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_mem_diagAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_mul_siteOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_siteOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'MvPolynomial.esymm_mem_adjoin_psum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_mem_diagAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_superset_neg_one_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_image_eq_univ_eq_sum_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symTensor_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symTensor_mem_diagAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.eq_smul_sum_symTensor_of_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commutant_le_diagAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.mem_commutant_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_mul_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagAlgebra_le_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mul_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isWeightVector_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.gen_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.gen_self_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.toLex_add_single_sub_single_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.monomial_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.monomial_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.monomial_mem_lowerSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.self_mem_lowerSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mulVec_mem_lowerSpan_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsHighestWeight.gen_mulVec_mem_lowerSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_eq_sum_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isInvariant_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsHighestWeight.isInvariant_lowerSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.lowerSpan_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weightProj_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.weightProj_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.weightProj_mulVec_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isWeightVector_weightProj_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_comp_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weightProj_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsHighestWeight.weightProj_mulVec_mem_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsIrreducible.lowerSpan_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsIrreducible.mem_span_of_isWeightVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsIrreducible.toLex_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsIrreducible.weight_eq_of_isHighestWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_isHighestWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.relabel_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.relabel_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.relabel_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsIrreducible.antitone_of_isHighestWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rotation_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rotation_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hasDerivAt_rotation_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hasDerivAt_tensorPow_rotation_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_diagOp_of_commute_tensorPow_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.diagOp_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isRotationPair_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isRotationPair_imag' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isRotationPair_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_diagOp_of_forall_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_of_mem_commutant_of_forall_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_eq_sum_labelProj_of_forall_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.l2_opNorm_le_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.l2_opNorm_reindex_le_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.l2_opNorm_reindex_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.IsSupportedOn.apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_permOp_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_eq_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_siteOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.conjTranspose_siteOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_apply_of_isSupportedOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_subsystemPerm_siteOp_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_subsystemPerm_siteOp_of_fix' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_copyPerm_mul_siteOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.conjTranspose_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_copyPerm_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.continuous_unitary_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.continuous_twirlIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integrable_twirlIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_mul_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_mul_unitaryTwirl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_unitaryTwirl_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_unitaryTwirl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_labelProj_mul_unitaryTwirl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.unitaryTwirl_eq_sum_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_mulVec_tensorVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorVec_mem_symmetricSubspace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentProj_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.eq_zero_of_isHermitian_of_mul_self_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.unitaryTwirl_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_groupAlgebraRep_permOp_of_mem_center' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.permOp_of_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_groupAlgebraRep_of_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_mulVec_eq_of_eq_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.commute_groupAlgebraRep_subsystemPerm_of_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.commute_groupAlgebraRep_subsystemPerm_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_labelProj_subsystemPerm_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.hom_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.aeval_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.spectrum_hom_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.cfc_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.conjTranspose_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.l2_opNorm_hom_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_mulVec_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.IsOrthogonalResolution.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.sum_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.Gamma_add_le_rpow_mul_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.mul_Gamma_le_rpow_mul_Gamma_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.Gamma_add_div_Gamma_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.div_rpow_le_Gamma_add_div_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.rpow_sub_le_Gamma_add_div_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.log_factorial_sub_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.log_factorial_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.mul_log_add_sub_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.shiftedPart_sub_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.shiftedPart_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.entropyTerm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.abs_log_hookFormula_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.abs_log_hookFormula_sub_le_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.abs_log_Gamma_one_add_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.log_mul_add_add_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.one_le_replicaConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.replicaConst_eq_one_or_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.replicaWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.replicaWeight_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.replicaWeight_update_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.exists_abs_log_replicaWeight_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.abs_rpow_sub_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.replicaRatio_wendel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.exists_replicaRatio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.exists_abs_replicaRatio_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsOrthogonalProjection.isStarProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsStarProjection.isOrthogonalProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsOrthogonalProjection.one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.isOrthogonalResolution_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelObservable_eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_spectralProj_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.isOrthogonalResolution_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.isHermitian_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.joint_hom_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.joint_hom_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.eigenvalue_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.mul_dim_le_one_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.supportProj_eq_joint_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.neg_log_eq_joint_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelEntropy_eq_joint_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.supportProj_mul_labelEntropy_mul_supportProj_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.re_trace_mul_exp_le_sum_multiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.schurSurprisal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.mem_padded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.multiset_eq_of_countP_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.lt_card_filter_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.eq_of_filter_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.countP_le_countP_of_imp' depends on axioms: [propext, Quot.sound]
'Partition.sum_countP_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.conjVec_mem_padded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.conjVec_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.card_padded_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Equiv.Perm.nat_card_conjClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.coeff_classSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.classSum_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.classSum_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.classSum_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.eq_zero_of_central_of_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.card_eq_card_conjClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mul_matrixUnitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.matrixUnitOp_mul_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.finrank_blockSpan_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mulVec_mem_blockSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.blockSpan_le_range_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.finrank_pairBlockSpan_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mulVec_mem_pairBlockSpan_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.commute_matrixUnitOp_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mulVec_mem_pairBlockSpan_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.mul_dim_le_finrank_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.le_of_mem_padded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.card_box_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.card_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_sign_smul_single_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_rowConfig' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isWeightVector_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isWeightVector_columnVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.boxEquiv_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.columnVector_apply_rowConfig' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.columnVector_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mulVec_columnVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHighestWeight_columnVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.unitOp_mulVec_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.unitOp_mulVec_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_groupAlgebraRep_of_mem_commutant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isInvariant_multSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isIrreducible_multSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isWeightVector_iff_weightProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsHighestWeight.groupAlgebraRep_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_isHighestWeight_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.shape_eq_of_isHighestWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.shape_eq_of_labelProj_mulVec_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.shape_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multSpace_ne_bot_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.cast_labelShape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelShape_mem_padded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_labelShape_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_irrepLabel_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelShape_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelShape_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.block_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.branchMatrix_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.trace_branchMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.trace_block_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.dim_eq_sum_branchMult' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.sum_dim_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_mul_matrixUnitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_mul_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_mul_matrixUnitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_mul_groupAlgebraRep_mul_labelProj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.groupAlgebraRep_mul_labelProj_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.liftMat_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.liftMat_mulVec_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.liftMat_mulVec_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_mulVec_liftMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_mulVec_liftMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_castLE_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mulVec_liftMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gen_mulVec_liftMat_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsHighestWeight.liftMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelProj_mulVec_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.shape_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelShape_truncate_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multSpace_ne_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.shape_eq_labelShape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multSpace_eq_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelProj_ne_zero_iff_multSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelProj_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.exists_mulVec_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_labelProj_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_comp_mulVec_mem'' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.comp_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupImage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mulVec_mem_groupImage₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mulVec_mem_groupImage₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mulVec_groupImage₁' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mulVec_groupImage₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.exists_groupImage_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.mul_dim_le_dim_of_compatible' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.dim_le_index_mul_of_compatible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupHom_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.noncommCoprod_groupHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.youngHom_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.index_range_youngHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupedCopies_dim' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupedCopies_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.firstCopies_castSucc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.firstCopies_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.copyPerm_firstCopies_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.slice_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.slice_groupAlgebraRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.slice_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_mulVec_mem_hwSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.slice_firstUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_slice_isHighestWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.finrank_hwSpace_fixed_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.shape_eq_labelPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.branchMult_le_one_and' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.vand_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.vand_update_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.exists_X_sq_mul_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_mul_prod_sub_one_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_prod_add_one_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_eq_vand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.shiftedPart_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_update_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_update_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_update_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_update_add_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_shiftedPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.shiftedPart_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_eq_sum_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_hookFormula_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.shiftedPart_snoc_castSucc' depends on axioms: [propext, Quot.sound]
'Partition.shiftedPart_snoc_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.vand_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_nonneg_of_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.strictAnti_shiftedPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_update_sub_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.hookFormula_update_add_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelPart_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelPart_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_labelPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelPart_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hookFormula_part_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_le_sum_of_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_lt_sum_of_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.part_eq_of_labelPart_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.part_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.branchRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_cast_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_le_hookFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_hookFormula_mul_dim_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_eq_hookFormula_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_eq_hookFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_eq_hookFormula_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.branchMult_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.branchMult_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.single_mul_transpositionSum_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.transpositionSum_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.wedderburnEquiv_transpositionSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.transpositionSum_mul_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.update_update_eq_comp_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_transpositionSum_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_gen_mulVec_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.casimir_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.firstCopies_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.transpositionSum_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.two_smul_starElement' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.starElement_mul_centralIdem_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_rowPairs_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.casimir_sub_casimir' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.starOp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.starOp_mul_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.eq_zero_of_mul_self_of_trace_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_firstCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.block_restrict_centralIdem_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.labelProj_mul_labelProj_firstCopies_ne_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.trace_mul_labelProj_mul_labelProj_firstCopies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.sum_labelPart_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_div_dim_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sub_one_div_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dim_div_dim_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelPart_eq_zero_of_labelProj_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_of_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_of_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_of_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.prodLeft_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_prodLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_prodLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_prodLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.splitEquiv_subsystemPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelProj_subsystemPerm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelProj_copyPerm_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelProj_copyPerm_ne_zero_of_subsystemPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelPart_eq_zero_of_subsystemPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_subConfig_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelObservable_eq_groupAlgebraRep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.sum_smul_centralIdem_mem_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.replicaMetric_eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.replicaDim_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.replicaLabelWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.posDef_replicaMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.replicaMetric_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_replicaMetric_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_abs_log_replicaLabelWeight_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_replicaMetric_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.snocEquiv_apply' depends on axioms: [propext, Quot.sound]
'TensorPower.replicaMetricFirst_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isOrthogonalResolution_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.markedRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.starOp_subsystemPerm_eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.markedRatio_eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_branch_scalars' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_l2_opNorm_markedRatio_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_l2_opNorm_markedRatio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.dim_le_mul_dim_of_compatible' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_pairAction_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.vecOfMatrix_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.vecOfMatrix_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.vecOfMatrix_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.dim_le_mul_dim_of_compatible'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.merge_dim_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.pairUnit_mul_pairUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.pairUnit_mul_pairUnit_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_pairUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_mul_pairUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.pairUnit_mem_pairUnitSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.exists_trace_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelProj_mul_labelProj_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.permOp_mul_permOp_mul_pairUnit_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.trace_mul_trace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.isHermitian_mul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.re_trace_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.merge_conditional_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.re_trace_merge_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.merge_moment_le_sum_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.copyPerm_eq_mul_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.merge_conditional_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.merge_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_subsystemPerm_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_complAverage_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_complAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_compl_labelProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_branch_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_le_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.markedRatio_inv_eq_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.re_star_dotProduct_branch_hom_mulVec_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.branchWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.labelWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_labelWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_branchWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.branchWeight_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_branch_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_norm_markedRatio_inv_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_markedRatio_inv_sub_clipped_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_norm_markedRatio_inv_sub_clipped_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_eq_reindex_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.isSupportedOn_localLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.IsSupportedOn.exists_localLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.IsSupportedOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.regionUnionEquiv_apply_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.regionUnionEquiv_apply_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_union_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_commute_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.IsSupportedOn.exists_sum_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.commute_labelObservable_of_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.labelObservable_inv_mul'' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelObservable_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelObservable_mul_inv_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelObservable_inv_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.replicaMetric_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_replicaMetric_of_disjoint'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.posDef_leafRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sqrt_leafMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_copyPerm_labelObservable' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_copyPerm_copyMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.star_dotProduct_copyMean_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_star_dotProduct_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_labelObservable_siteOp_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_labelObservable_first_siteOp_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_labelObservable_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_labelObservable_first_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.replicaMetric_conj_siteOp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.markedSimilarity_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_copyPerm_markedSimilarity_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.star_dotProduct_markedSimilarity_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_norm_markedSimilarity_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.splitEquiv_apply_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.splitEquiv_apply_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.splitEquiv_symm_apply_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.splitEquiv_symm_apply_of_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.configurationCongr_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.reducedMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteProduct.trace_reducedMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symProj_mul_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.cfc_log_listProd_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosDef.rpow_conj_mul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.posDef_list_ofFn_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.list_ofFn_prod_rpow_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.smul_vecMulVec_le_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.mul_conjTranspose_le_smul_one_of_conjTranspose_mul_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.PosDef.inv_smul_projection_le_of_compression_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_replicaMetric_inv_square_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupedCopies_labelEntropy_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Matrix.IsHermitian.exp_le_exp_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exp_neg_whole_labelEntropy_le_exp_grouped' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_replicaMetric_inv_square_le_grouped_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.compression_cfc_le_of_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.compression_exp_neg_smul_le_of_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.tensorPow_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.eq_unitary_conj_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rpow_eq_unitary_conj_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.posSemidef_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_labelObservable_mul_tensorPow_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_star_dotProduct_sq_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsLabelFunctionOn.commute_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsLabelFunctionOn.commute_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isLabelFunctionOn_replicaMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isLabelFunctionOn_replicaMetric_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isUnit_det_replicaMetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leafRoot_inv_mul_leafRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.relativeMetric_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.posDef_relativeMetric_and_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_star_dotProduct_sq_le_moveWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.sum_dotProduct_eigenvectorBasis_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.conjTranspose_mul_mul_embedMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.star_embedMatrix_mulVec_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.star_eigenvectorBasis_dotProduct_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.re_trace_rpow_submatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.integrableOn_rpow_mul_one_add_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Real.integral_rpow_mul_one_add_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.weylFormula_eq_vand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.rowPairs_denom_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.weylFormula_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.weylFormula_eq_zero_of_shiftedPart_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.weylFormula_update_add_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.indic_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_eq_zero_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.elemSymm_eq_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.prod_pow_indic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_mul_elemSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_geom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.X_pow_sub_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.eval_one_geomPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_geom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.eval_one_elemSymm_geom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.eval_one_geomVand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_prod_add_indic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.prod_Ioi_eq_vand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_vand_add_indic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.shiftedPart_add_indic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_weylFormula_add_indic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.instSigmaFiniteOrthant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.ae_orthant_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.integrable_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.integral_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.integrable_and_integral_monomial_mul_rpow_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.integrable_monomial_mul_rpow_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.integral_monomial_mul_rpow_sum'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_mul_alternant_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.Gamma_one_add_add_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.delta_eq_revPerm' depends on axioms: [propext, Quot.sound]
'Partition.alternant_delta_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.det_risingPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.termExp_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_termExp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.gammaIntegrand_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.gammaIntegral_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.integrable_gammaIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_sign_prod_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.det_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.gammaIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sign_revPerm_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_delta_mul_rpow_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_delta_eq_vand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.alternant_delta_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.cast_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.sum_shiftedPart_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Partition.replicaWeight_eq_gammaIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_groupAlgebraRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_regular_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.trace_groupAlgebraRep_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.coordEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.groupAlgebraRep_regular_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.multiplicity_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.block_centralIdem_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepLabel.card_mul_coeff_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.characterSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_permOp_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixSum_eq_characterSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.decomp_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.firstCopies_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.decomp_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.decomp_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_filter_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.snoc_comp_firstCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.snoc_comp_decomp_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixCount_decomp_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixCount_decomp_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixSum_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixSum_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixSum_mul_centralIdem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixScalar_eq_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multiplicity_eq_weylFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leftCopies_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leftCopies_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rightCopies_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rightCopies_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leftCopies_symm_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leftCopies_symm_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rightCopies_symm_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rightCopies_symm_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leftCopies_mul_rightCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.copyPerm_leftCopies_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.copyPerm_rightCopies_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.splitOp_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.ext_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.splitOp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_splitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.append_eq_append_iff' depends on axioms: [propext, Quot.sound]
'TensorPower.permOp_leftCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_rightCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_leftCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_rightCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_eq_splitOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sign_mul_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.single_mul_antisym' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.antisym_mul_antisym' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_sign_fix' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_permOp_mul_tensorPow_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_injective_image_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_injective_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_antisym_mul_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.restrictHom_left_mul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.leftUnit_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.rightAntisym_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.pieriElem_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_pieriElem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sliceR_splitOp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sliceR_permOp_rightCopies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.castAdd_ne_natAdd' depends on axioms: [propext, Quot.sound]
'TensorPower.update_append_castAdd' depends on axioms: [propext, Quot.sound]
'TensorPower.update_append_natAdd' depends on axioms: [propext, Quot.sound]
'TensorPower.sliceR_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsWeightVector.sliceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.single_rightCopies_mul_antisym' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.fixed_left_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sliceR_copyPerm_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sliceR_eq_zero_of_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isPieriVector_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.zSum_update_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_sliceR_isHighestWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.weight_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_copyPerm_of_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.finrank_hwSpace_pieri_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_block_pieriElem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.pieriRank_le_one_and' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multSpace_ne_bot_iff_hasRows' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.unitOp_eq_zero_of_not_hasRows' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.glChar_eq_zero_of_not_hasRows' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.glChar_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multiplicity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.multiplicity_eq_zero_of_not_hasRows' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_mul_labelProj_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_labelProj_mul_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_mul_tensorPow_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_pieriElem_mul_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hasRows_iff_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.antitone_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_part_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_shiftedPart_eq_of_not_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mem_pieriSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_pieriSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.pieriRank_hasRows_eq_zero_or_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_pieriSet_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.pieriRank_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.glChar_mul_elemSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mem_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mem_rowSet_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_rowSet_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.glChar_of_part_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.alternant_mul_glChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.gammaIntegrand_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.specNorm_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.specDensity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.specNorm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.measurable_specWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coe_specWeight_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isProbabilityMeasure_specMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_specMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.ae_specMeasure_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.glChar_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.specDensity_mul_glChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.specSample_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.specSample_posDef' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_specSample' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorPow_specSample_rpow_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.measurable_sampleEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_sampleEntry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.ae_prod_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_unitary_sampleEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_specMeasure_label' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_specSample_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.groupAlgebraRep_comp_embedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_replicaMetric_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.splitEquiv_symm_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.reindex_tensorPow_localLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_replicaMetric_integral_localLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_tensorVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_of_integral_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mul_of_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.reindex_labelObservable_subsystemPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_l2_opNorm_compensator_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_permOp_subsystemPerm_tensorPow_of_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.commute_labelObservable_tensorPow_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_labelObservable_tensorPow_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.tensorVec_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentProj_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_mul_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_coherent_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.norm_star_dotProduct_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.PosSemidef.norm_trace_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.l2_opNorm_one_kronecker_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.dotProduct_star_unitary_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_coherentProj_unitary_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symProj_mul_of_permOp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_symProj_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.continuous_trace_mul_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integral_trace_mul_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentIntegral_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentIntegral_trace_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_coherentIntegral_trace_coherentProj_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeSplit_apply_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeSplit_apply_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeSplit_symm_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeSplit_symm_apply_of_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeOp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_placeOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_injectionAverage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwapFun_castAdd_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwapFun_castAdd_of_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwapFun_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwapFun_involutive' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwap_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionSwap_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_mul_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.splitCopies_copyPerm_injectionSwap' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.trace_kronecker_mul_injectionSwap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.l2_opNorm_permOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Equiv.Perm.card_filter_apply_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_goodPerms' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_filter_not_goodPerms_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.castAdd_restrictFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_mul_copyKronecker' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_goodPerms_exchangeTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_goodPerms' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_goodPerms_exchangeTrace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_exchangeTrace_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.factorial_mul_trace_copyKronecker_mul_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.le_of_mul_le_of_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_trace_mul_injectionAverage_sub_coherentIntegral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Function.Embedding.card_filter_apply_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeOp_apply'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.copyKronecker_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_copyKronecker_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeOp_castAdd_mul_placeOp_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_filter_not_overlapPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_filter_not_overlapPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_filter_apply_eq_apply_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.card_overlapPairs_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionAverage_mul_injectionAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_injectionAverage_mul_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mul_permOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symm_copyPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeOp_trans_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_mul_injectionAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_symProj_injectionAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.conjTranspose_placeOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.conjTranspose_injectionAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.placeOp_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionAverage_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionAverage_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.conjTranspose_coherentProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentExpect_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentExpect_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentExpect_copyKronecker' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.continuous_coherentExpect' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.continuous_unitary_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.integrable_coherentIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentIntegral_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentIntegral_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_coherentIntegral_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.commute_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_finProdFinEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.exists_norm_trace_sub_coherentIntegral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.isCompact_unitSphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.unitary_mulVec_single_mem_unitSphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_symProj_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_trace_mul_le_of_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsInjectionPoly.hasCoherentSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.exists_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.exists_bound'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.mul_symProj_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.eventually_norm_trace_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.freeAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_symProj_mul_mul_symProj_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.of_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.abs_eigenvalues_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.aeval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.symProj_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.cfc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasCoherentSymbol.skew' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.singleEmb_apply' depends on axioms: [propext]
'TensorPower.placeOp_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.coherentExpect_oneCopy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_placeOp_siteOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_oneCopy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_injectionAverage_mul_siteOp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symProj_mul_permOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.symProj_mul_siteOp_mul_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.center' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.injection' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.IsMarkedPoly.exists_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.of_isMarkedPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.of_norm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.congr_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.center' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.injection' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.aeval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.symProj_mul_mul_mul_symProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.norm_symProj_mul_mul_symProj_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.HasMarkedSymbol.hasCoherentSymbol_compress' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.regionUnit_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.siteOp_mul_siteOp_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_regionUnit_mul_regionUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.permOp_subsystemPerm_swap_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.localLift_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sum_expect_regionUnit_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.injectionAverage_oneCopy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.starOp_subsystemPerm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hasMarkedSymbol_starOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.commute_localLift_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.commute_localLift_of_isSupportedOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.localLift_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.aeval_localLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.l2_opNorm_localLift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.star_dotProduct_localLift_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Entropy.trace_margMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.mul_cfc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.l2_opNorm_cfc_sub_aeval_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsHermitian.l2_opNorm_cfc_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.suppRpow_eq_max_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.abs_suppRpow_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mul_rpow_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mul_suppRpow_neg_sq_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.mul_clip_sub_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_margMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.eigenvalues_margMatrix_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_localLift_cfc_mulVec_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.localLift_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_eq_one_of_mem_unitSphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_localLift_cfc_sub_aeval_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_sandwich_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_star_dotProduct_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_regionPow_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_regionPow_neg_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_regionPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_aeval_margLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_regionPow_sandwich_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.IsOrthogonalResolution.norm_le_l2_opNorm_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_starOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.abs_starValue_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_cfc_starOp_sub_aeval_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.l2_opNorm_aeval_starOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_aeval_starOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_sandwich_approx_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_pairing_approx_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.sandwich_rearrange' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.star_dotProduct_mul_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_markedScalarSymbol_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hasMarkedSymbol_polyWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.commute_symProj_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_markedRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.isHermitian_markedRatio_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.norm_markedSimilarity_sub_polyWord_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.hasCoherentSymbol_markedSimilarity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arealaw.SubState.D₁_restrict_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.labelEntropy_mul_symProj_of_eq_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TensorPower.commute_subsystemPerm_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.subgroup_signedLabelEntropy_symProj_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PermutationRepresentation.posSemidef_mergeDeficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TensorPower.exists_replicaMetric_symProj_inverse_bound_and_floor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PermutationRepresentation.dim_le_card_of_labelProj_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

</details>

### (c) the comparator pair

`lake build Challenge Solution`:

```
⚠ [8799/9011] Replayed Challenge.Basic
warning: Challenge/Basic.lean:75:8: declaration uses `sorry`
warning: Challenge/Basic.lean:80:8: declaration uses `sorry`
warning: Challenge/Basic.lean:257:8: declaration uses `sorry`
Build completed successfully (9081 jobs).
```

The three warnings are the three intended `sorry` of `Challenge/Basic.lean`
(`Arealaw.posSemidef_ptrace` at line 75, `Arealaw.trace_ptrace` at line 80,
`OpenAI.Challenge.area_law` at line 257). The full build in (a) has the same three sorry
warnings and no other.

### (d) the statement files

```
$ diff <(grep -v '^import' <v1 OpenAI/Statements.lean>) <(grep -v '^import' OpenAI/Statements.lean)
$ echo $?
0
$ diff <(grep -v '^import' <ruiz/3d-targets OpenAI/Statements3D.lean>) <(grep -v '^import' OpenAI/Statements3D.lean)
$ echo $?
0
```

Both diffs are empty. `OpenAI/Statements3D.lean` is in fact byte identical to the branch.

## Step 7: summary

### Taken from each side

- From v2: the whole proof body (`AreaLaw/`, `AreaLawForMathlib/`), `blueprint/`, `digest/`,
  `paper/`, `Map.md`, `RefactoringPlan.md`, `RefactoringResult.md`, `scripts/`,
  `.github/workflows/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
  `Solution/Basic.lean`, the README as a base, and the deletion of `OpenAI/` (except
  `Statements.lean`) and `Arealaw/`.
- From v1: `OpenAI/Statements.lean` (byte identical outside its two import lines),
  `HISTORY.md`, `docs/oai265/`, `docs/StatementAudit.md`, `docs/README-quantum-arealaw.md`,
  `docs/charter-quantum-arealaw.md`, `Challenge/`, `Comparator/`, `LICENSE`, `NOTICE` (paths
  rewritten), the port headers, the audit (rebuilt), the trust boundary and the verification
  commands of the README.
- From `ruiz/3d-targets`: `OpenAI/Statements3D.lean`, `OpenAI/Audit3D.lean`,
  `docs/3D/Targets.md` (unchanged) and `OpenAI/Cylinder3D.lean` (imports changed).
- Removed from v2: the tool state directory and tool names (see "Internal tool names removed").

### Files whose content differs from both parents

151 files differ from both v1 (1e91b65) and v2 (65fcc00).

New in neither parent: `MERGE_NOTES.md`, `OpenAI/Cylinder3DSupport.lean`, and the four files from
`ruiz/3d-targets` (`OpenAI/Statements3D.lean`, `OpenAI/Audit3D.lean`, `docs/3D/Targets.md`
identical to that branch; `OpenAI/Cylinder3D.lean` differing from it in its imports only).

Changed relative to both:

- `.gitignore` (tool lines removed), `NOTICE` (paths), `OpenAI.lean` (regenerated by `mk_all`),
  `README.md`, `lakefile.toml` (`OpenAI` roots).
- Present in v1 only: `OpenAI/Audit.lean` (rebuilt), `docs/oai265/Memory.md` (one archive line
  at the top).
- Present in v2 only: `Map.md`, `RefactoringResult.md` (tool names), and 136 Lean files under
  `AreaLaw/` and `AreaLawForMathlib/` whose module docstring gained a port header or a partial
  port note (listed under Step 3; no other change to them).

### Ported code kept

`AreaLaw/S06_Replicas/Ported/` holds 34 files, 8507 lines (8378 before the restored headers),
ported from QICLean and TNLean through v1 and not yet restated in the paper's shape. They are
kept as they are, each with its copyright block and, again, its `Ported from` header. The
`SchurWeyl/` chain under `AreaLawForMathlib/RepresentationTheory/` (49 files) is likewise ported
and attributed. The v1 code that v2 removed as unused remains in tag `v1.0`.

### Open decisions for the maintainers

1. README wording, in particular the Provenance section and whether the 3D paragraph belongs
   under "What is proved".
2. Whether to golf or restate `AreaLaw/S06_Replicas/Ported/` (34 files, about 8,500 lines), and
   whether `docs/StatementAudit.md` should name the v2 proof declarations in its headings (it
   still names v1's `area_law`, `collar_bound`, ...; `OpenAI.area_law` exists again as an alias
   in `OpenAI/Cylinder3DSupport.lean`, the others do not).
3. Whether `OpenAI/Cylinder3DSupport.lean` should stay, or the cylinder proof be moved onto v2's
   API (the `ℂ` lemmas of `AreaLawForMathlib` and the transfer of `AreaLaw/Transfer.lean`).
4. Whether the partial port notes (41 files whose source carried only a few v1 declarations) are
   wanted, or a per declaration attribution is preferred.
5. `NOTICE` does not mention the 12 v1 files `Adapted from openai/math`; 5 files of the new tree
   still say so in their headers. v1's NOTICE did not mention it either.
6. `ruiz/3d-targets` is not on the public remote; it should be pushed (or the 3D files
   reviewed separately) before this candidate is published.
7. `docs/3D/Targets.md` says the refactoring map "is not in this repository"; it now is
   (`Map.md`).
8. The step order of the task was kept except that the 3D half of Step 2 was committed after
   Step 3, because it needed the first build.
