import AreaLawRefactored.S07_Transport.Means
import AreaLawRefactored.S07_Transport.Fourier
import AreaLawRefactored.S07_Transport.Histories
import AreaLawRefactored.S07_Transport.LogJensen
import AreaLawRefactored.S07_Transport.States
import AreaLawRefactored.S07_Transport.ExactDerivative
import AreaLawRefactored.S07_Transport.EntropyGain
import AreaLawRefactored.S07_Transport.Energy
import AreaLawRefactored.S07_Transport.Endpoints
import AreaLawRefactored.S07_Transport.Proposition

/-!
# §7 Transport through finite trees of metrics

Digest `digest/07-transport.md`, paper `paper/sections/06-transport.tex`. No geometry: every §7
anchor is `any d` (Map.md, Dimension), stated over arbitrary finite index types, an arbitrary
finite site type with arbitrary local dimensions, and arbitrary copy number `k`.

* `Means`: §7.1, D7.1–D7.5 (`lemma_7_1`, `lemma_7_2`).
* `Fourier`: §7.2, D7.6–D7.7 (`lemma_7_3`).
* `Histories`: §7.3, D7.8–D7.13 (rounds, band metrics, moves, energy terms, `step_7_12`).
* §7.4 (D7.14–D7.27): `States` (the objects of Proposition 7.4), `ExactDerivative` (part (a),
  D7.15–D7.16), `LogJensen` (D7.19), `EntropyGain` (part (b), D7.17–D7.20), `Energy` (part (c),
  D7.21–D7.25), `Endpoints` (D7.26), `Proposition` (`prop_7_4`, D7.14, D7.27).
-/
