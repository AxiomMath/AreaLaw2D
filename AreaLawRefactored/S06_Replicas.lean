import AreaLawRefactored.S06_Replicas.Setup
import AreaLawRefactored.S06_Replicas.SymmetricDimension
import AreaLawRefactored.S06_Replicas.Labels
import AreaLawRefactored.S06_Replicas.Surprisal
import AreaLawRefactored.S06_Replicas.InjectionAverage
import AreaLawRefactored.S06_Replicas.FromS05

/-!
# §6 Symmetric replicas and entropy metrics

Digest `digest/06-replicas.md`, paper `paper/sections/05-replicas.tex`. Over an arbitrary finite
family of tensor factors (`Map.md`, Dimension: every §6 anchor is `any d`).

* `Setup`: D6.1, D6.3; `SymmetricDimension`: D6.1 Output `D_k = binom(k+d−1, d−1)`.
* `Labels`: D6.4 (2) (`lemma_6_1_2`), D6.7 (`eq_replicas_fixed_factor`).
* `Surprisal`: D6.4 (5) (`lemma_6_1_5`).
* `InjectionAverage`: D6.14 `𝒯_{k,m}`, D6.15 (`eq_replicas_injection_product`).
* `FromS05`: the §5 inputs (D5.1, Lemma 5.1, Lemma 5.3), replaced by `S05_Conditional` at the merge.
-/
