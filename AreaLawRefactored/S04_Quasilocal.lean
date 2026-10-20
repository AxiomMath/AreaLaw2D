import AreaLawRefactored.S04_Quasilocal.Propagation
import AreaLawRefactored.S04_Quasilocal.Filter
import AreaLawRefactored.S04_Quasilocal.CenteredFilter
import AreaLawRefactored.S04_Quasilocal.Locality
import AreaLawRefactored.S04_Quasilocal.Roots
import AreaLawRefactored.S04_Quasilocal.Truncation

/-!
# §4 Positive constraints and truncation near a finite set

Digest `digest/04-quasilocal.md`, paper `paper/sections/03-quasilocal.tex`. Graph-level
(`Map.md`, Dimension): a simple graph `G` on a site type `σ` with ball growth `V`.

* `S04_Quasilocal/Setup.lean`: §4.0, D4.1–D4.3 (contractivity and the twirl bound of D4.2,
  D4.4.9 through `AreaLawForMathlib/Analysis/Matrix/WeylTwirl.lean`), and the definitions of
  D4.11.
* `S04_Quasilocal/Propagation.lean`: §4.1, Lemma 4.1 (D4.4), both lines; Lieb–Robinson machinery
  in `AreaLawForMathlib/Analysis/ODE/LiebRobinson.lean`.
* `S04_Quasilocal/Filter.lean`: §4.1, Lemma 4.2 (D4.5); the bump in
  `AreaLawForMathlib/Analysis/Fourier/GevreyBump.lean`, `GevreyBumpFourier.lean`.
* `S04_Quasilocal/CenteredFilter.lean`: §4.2, D4.7.
* `S04_Quasilocal/Locality.lean`: §4.2, D4.8.
* `S04_Quasilocal/Roots.lean`: §4.2, Lemma 4.4 (D4.10); D4.9 is
  `CFC.norm_sqrt_sub_sqrt_le` (`AreaLawForMathlib/Analysis/CStarAlgebra/SqrtHolder.lean`).
* `S04_Quasilocal/VolumeFree.lean`, `GroundState.lean`, `Crossing.lean`: §4.3, D4.12–D4.14.
* `S04_Quasilocal/Truncation.lean`: Proposition 4.5 (D4.11).
-/
