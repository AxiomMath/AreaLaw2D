import AreaLawRefactored.S05_Conditional.Defs
import AreaLawRefactored.S05_Conditional.Spectral
import AreaLawRefactored.S05_Conditional.LogMoments
import AreaLawRefactored.S05_Conditional.Interpolation
import AreaLawRefactored.S05_Conditional.PhaseRate
import AreaLawRefactored.S05_Conditional.Compression
import AreaLawRefactored.S05_Conditional.SkewAnalytic

/-!
# §5 Two conditional operator estimates

Digest `digest/05-conditional.md`, paper `paper/sections/04-conditional.tex`. Lattice-free
(`Map.md`, Dimension: every §5 anchor is `any d`).

* `S05_Conditional/Defs.lean`: D5.1 definitions, D5.2.1, D5.8 (termwise), D5.20, and the
  statements `Lemma_5_1`, `Lemma_5_2`, `Lemma_5_3`.
* `S05_Conditional/Spectral.lean`: D5.1 API of `bracketPow`/`hatPow`, (F1), (F2).
* `S05_Conditional/LogMoments.lean`: §5.0, D5.3 (and the eigenvalue part of D5.2.3–5).
* `S05_Conditional/Interpolation.lean`: §5.1, D5.7 (scalar core), D5.11, D5.5.10.
* `S05_Conditional/PhaseRate.lean`, `Compression.lean`: §5.2, D5.12.7–8, D5.13, D5.14
  (abstract); the Mellin integral of D5.12.6 is
  `AreaLawForMathlib/Analysis/SpecialFunctions/ResolventMellin.lean`.
* `S05_Conditional/SkewAnalytic.lean`: §5.3, D5.16.6, D5.18, D5.19 for an arbitrary entire `f`.
-/
