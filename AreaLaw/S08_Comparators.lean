import AreaLaw.S08_Comparators.Setup
import AreaLaw.S08_Comparators.Interfaces
import AreaLaw.S08_Comparators.Basics
import AreaLaw.S08_Comparators.Entropy
import AreaLaw.S08_Comparators.Labels
import AreaLaw.S08_Comparators.Pin
import AreaLaw.S08_Comparators.RoughUpper
import AreaLaw.S08_Comparators.SharpUpper
import AreaLaw.S08_Comparators.Components
import AreaLaw.S08_Comparators.Merge
import AreaLaw.S08_Comparators.ComponentInverse
import AreaLaw.S08_Comparators.Compression
import AreaLaw.S08_Comparators.Lower
import AreaLaw.S08_Comparators.Proposition

/-!
# §8 Norm comparisons from an auxiliary pair

Digest `digest/08-comparators.md`, paper `paper/sections/07-comparators.tex`. No geometry: every
§8 anchor is `any d` (Map.md, Dimension), stated over an arbitrary finite physical site type with
arbitrary local dimensions, the extended system `Site σ` (physical sites and the auxiliary
factors `C`, `R`), arbitrary status collections, arbitrary mean trees and arbitrary `k`.

* `Setup`: the objects (D8.1, D8.2, D8.4–D8.7, D8.11, D8.23) and the displays of D8.8.
* `Interfaces`: the anchors one subsection file cites from another, as `Prop`s.
* `Basics`: D8.1 Output (`step_8_1`), D8.11 Schmidt facts (`step_8_11`).
* `Entropy`: D8.3 (`step_8_3`), D8.36 (`step_8_36`), D8.30.6 (`gpre_nonneg`).
* `Labels`: §8.2 D8.9–D8.13 (`step_8_10`, `step_8_12`, `step_8_13`).
* `Pin`: §8.2 D8.14–D8.16.
* `RoughUpper`, `SharpUpper`: §8.3 D8.17–D8.22.
* `Components`, `Merge`, `ComponentInverse`, `Compression`: §8.4 D8.24–D8.31.
* `Lower`: D8.23 and §8.5 D8.32–D8.35.
* `Proposition`: Proposition 8.1 (`prop_8_1`, D8.8, D8.37).
-/
