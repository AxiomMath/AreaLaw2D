import AreaLawRefactored.S01_AreaLaw
import AreaLawRefactored.S02_Preliminaries
import AreaLawRefactored.S03_InitialBox
import AreaLawRefactored.S04_Quasilocal
import AreaLawRefactored.S05_Conditional
import AreaLawRefactored.S06_Replicas
import AreaLawRefactored.S07_Transport
import AreaLawRefactored.S08_Comparators
import AreaLawRefactored.S09_Scanner
import AreaLawRefactored.S10_Amplification
import AreaLawRefactored.S11_Geometry
import AreaLawRefactored.Transfer

/-!
# The area law for gapped two-dimensional lattice Hamiltonians

One module per paper section (`digest/00-overview.md` §2): `S02_Preliminaries`,
`S03_InitialBox`, `S04_Quasilocal`, … `S08_Comparators`, `S09_Scanner`, `S10_Amplification`,
…; `Transfer` proves the `RCLike 𝕜` frozen statements from their `ℂ` instances (one layer at the
top), among them Theorem 1.1 (`AreaLaw.areaLaw`) and Corollary 1.2 (`AreaLaw.areaLawCorollary`).
-/
