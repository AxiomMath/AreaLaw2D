Still present in **0.5.103**, and on `main` at 009f2559a9 (`absent_packages`/`built_without` are unchanged). There is one variant this thread does not have yet: a repo that `is_publication` marks as published (`Comparator/comparator.json`, no charter). In that case `axile_provision` refuses on purpose, so no environment can ever be recorded, and "a require left out when it was provisioned" can never be true. In one session the two routes contradicted each other:

```
lean_run_code("import Arealaw.Subadditivity ...")
  "substrate": "local Lean ... (Axile unavailable: /root/dev/AreaLaw2D-internal-18b3b627 is a published repo, which keeps no Axile environment ...)"
lean_diagnostic_messages("AreaLawRefactored/S02_Preliminaries.lean")
  "substrate": "local Lean ... (the Axile environment lacks Physlib (a require left out when it was provisioned, because it did not build), and this file imports it)"
```
```
axc python -c "from pathlib import Path; from axiomcode import publish as P; from axiomcode.tools import axile as A
r=Path('/root/dev/AreaLaw2D-internal-18b3b627'); print(P.is_publication(r), A.built_without(r), A.absent_packages(r))"
# True None {'Physlib': ['Physlib', 'PhyslibAlpha', 'QuantumInfo']}
```
In this case the false reason also hid the real blocker: readiness ignores the unbuilt Physlib, so the local call compiled it and timed out after 600 s (#14281).
