import AreaLaw.S01_AreaLaw
import AreaLaw.S02_Preliminaries
import AreaLaw.S03_InitialBox
import AreaLaw.S04_Quasilocal
import AreaLaw.S05_Conditional
import AreaLaw.S06_Replicas
import AreaLaw.S07_Transport
import AreaLaw.S08_Comparators
import AreaLaw.S09_Scanner
import AreaLaw.S10_Amplification
import AreaLaw.S11_Geometry
import AreaLaw.Transfer

/-!
# The area law for gapped two-dimensional lattice Hamiltonians

One module per paper section (`digest/00-overview.md` §2): `S02_Preliminaries`,
`S03_InitialBox`, `S04_Quasilocal`, … `S08_Comparators`, `S09_Scanner`, `S10_Amplification`,
…; `Transfer` proves the `RCLike 𝕜` frozen statements from their `ℂ` instances (one layer at the
top), among them Theorem 1.1 (`AreaLaw.areaLaw`) and Corollary 1.2 (`AreaLaw.areaLawCorollary`).
-/
