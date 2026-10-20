import AreaLawRefactored.S04_Quasilocal.Roots
import AreaLawRefactored.S04_Quasilocal.Truncation

/-!
# §4 Positive constraints and truncation near a finite set

Digest `digest/04-quasilocal.md`, paper `paper/sections/03-quasilocal.tex`. Graph-level
(`Map.md`, Dimension): a simple graph `G` on a site type `σ` with ball growth `V`.

* `S04_Quasilocal/Setup.lean`: §4.0, D4.1–D4.3, and the definitions of D4.11.
* `S04_Quasilocal/Roots.lean`: §4.2, Lemma 4.4 (D4.10); D4.9 is
  `CFC.norm_sqrt_sub_sqrt_le` (`AreaLawForMathlib/Analysis/CStarAlgebra/SqrtHolder.lean`).
* `S04_Quasilocal/VolumeFree.lean`, `GroundState.lean`, `Crossing.lean`: §4.3, D4.12–D4.14.
* `S04_Quasilocal/Truncation.lean`: Proposition 4.5 (D4.11).
-/
