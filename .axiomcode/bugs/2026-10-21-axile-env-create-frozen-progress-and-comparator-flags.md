# axile env create: frozen progress line during a long phase (build_planning), and comparator theorem-flag error that names no flag / ignores comparator.json

- Date: 2026-10-21
- Outcome: filed (two axile issues + AxiomCode tracking issue)
- Blame: AxiomMath/axile — (1) clients/axile_client/env.py:1614-1615 on master 27298f97ef (installed copy: site-packages/axile_client/env.py:1268-1269); (2) clients/axile_client/comparator.py:79-82 (and no config-file input to build_comparator_config, called from cli/env.py:432 on master)
- Issue: https://github.com/AxiomMath/axile/issues/3346 (progress), https://github.com/AxiomMath/axile/issues/3347 (comparator flags), https://github.com/AxiomMath/axiom/issues/14894 (AxiomCode, label axiomcode-v5)

## What was done
`axile env create /root/dev/AreaLaw2D-internal-18b3b627 --no-cache-write --comparator-challenge-module Challenge.Basic --comparator-solution-module Solution.Basic --comparator-challenge-theorem OpenAI.Challenge.area_law --comparator-challenge-theorem Arealaw.posSemidef_ptrace --comparator-challenge-theorem Arealaw.trace_ptrace --comparator-permitted-axiom propext --comparator-permitted-axiom Quot.sound --comparator-permitted-axiom Classical.choice` (env 01M5F0PFYFN72QH1SQ5ZDB8DP5). Earlier, the same command without the theorem/axiom flags.

## What came back (verbatim)
(1) ~16 min with only
`axile env create: status: building, phase build_planning, 4s elapsed, 0s queued`
(`axile env status` showed `phase: build_planning`), then
`axile env create: status: building, phase building, compiled 0 of ~311 modules (9416 of 9727 cached), 1004s elapsed, 0s queued`; ended "Lean default kernel accepts the solution" / "Your solution is okay!" / "axile env create: environment 01M5F0PFYFN72QH1SQ5ZDB8DP5 ready", exit 0.
(2) `axile env create: comparator gate requires all of: challenge module, solution module, and at least one challenge theorem; missing at least one challenge theorem`, exit 1.

## Expected
(1) elapsed counter advances / line reprinted during a long phase. (2) CLI reads Comparator/comparator.json, or the error names `--comparator-challenge-theorem`.

## Reproduction
(2) reproduced offline (fails before any network call):
`axile env create /root/dev/AreaLaw2D-internal-18b3b627 --no-cache-write --comparator-challenge-module Challenge.Basic --comparator-solution-module Solution.Basic` -> same message, exit 1.
(1) reproduced with a stub: `.axiomcode/scratch/progress_repro.py` (run with /opt/axiomcode/venv/bin/python) — get_environment stubbed to return building/build_planning 7 times then ready; `_poll_until_settled` printed exactly one line (`status: building, phase build_planning, 0s elapsed, 0s queued`) across 8 polls.

## Cause
(1) `_poll_until_settled` reports only when `(status, phase)` changes or `modulesBuilt` moves (rate-limited); there is no time-based heartbeat, and with `progress=None` (as during build_planning) nothing triggers a line. Applies to both TTY (in-place line never rewritten) and log mode.
(2) `build_comparator_config` takes only the four flag values; its error uses prose names, not flag names; nothing reads comparator.json (module docstring says explicit flags are the intended design, so the message is the minimal fix).
AxiomCode checked, not at fault: `src/axiomcode/publish.py:918-928` (main 5f09e618c0; installed 0.5.103 at :899-910) builds the axile-route command from `Comparator/comparator.json` with every theorem and axiom flag. Error (2) arises only from a hand-written command.
Unpinned observation: ~16 min in build_planning for a build that then compiled 0 of ~311 modules looks slow server-side.

## Versions
AxiomCode substrate + plugin 0.5.103 (editable file:///opt/axiomcode/src); AxiomCode main 5f09e618c0 (0.5.105). axile_client 0.1.0, axile_core 0.1.0 (wheels /opt/axiomcode/wheels); axile master 27298f97ef0898da7a70302f5d81ccdb3f02da8a has both defects unchanged (comparator.py identical; env.py same condition at :1614-1615).

## Related issues and PRs
- AxiomMath/axile#2765 (open) — comparator verdict message is a raw lake tail; different defect, same output path.
- AxiomMath/axile#2595 (closed), #3302 (open) — ENOSPC during build_planning; different.
- AxiomMath/axiom#13507 (open) — comparator worker has no no-wait way to get the Axile verdict; related, different.
- AxiomMath/axiom#13181 (closed) — root-level comparator.json never read by AxiomCode; different (AxiomCode side, fixed).
- AxiomMath/AxiomCodeV5#82, #83 (closed) — silent Axile provisioning waits in AxiomCode; different layer.
No duplicate found in axile, axiom (axiomcode-v5) or AxiomCodeV5.

## Workaround
(1) While the line is frozen, poll `axile env status <id>` (or start with `--no-wait` and check status per call) to see phase changes. (2) Pass every `theorem_names` entry as `--comparator-challenge-theorem` and every `permitted_axioms` entry as `--comparator-permitted-axiom`, or use the command AxiomCode's publish_plan panel generates (it reads comparator.json).

## Upstream draft
none (all targets are AxiomMath; issues filed).
