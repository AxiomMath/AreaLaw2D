# AxiomCode agent image has no C compiler or libc headers: Verso blueprints (MD4Lean compiles C with cc) cannot lake build in a platform session

- Date: 2026-10-21
- Outcome: filed
- Blame: AxiomMath/axiom — agents/definitions/axiomcode/Dockerfile:43-52 (apt layer, no build-essential / gcc + libc6-dev), at 8ab043dc
- Issue: https://github.com/AxiomMath/axiom/issues/14867 (label axiomcode-v5)

## What was done
`lake build` in the Verso-blueprint package (`blueprint/`, verso-blueprint v4.33.0 template) for Step 3 of RefactoringPlan.md. Dependency MD4Lean compiles `md4c/*.c`.

## What came back (verbatim)
```
trace: .> cc -c -o .../.lake/packages/MD4Lean/.lake/build/md4c/entity.o .../MD4Lean/md4c/entity.c -I .../MD4Lean/md4c -fPIC
info: stderr:
could not execute external process 'cc'
error: external command 'cc' exited with code 255
```
With the Lean toolchain's clang as `cc`: `fatal error: 'stdlib.h' file not found`. With MD4Lean's adhoc_include headers, linking vbp fails: `ld.lld: error: undefined symbol: __acrt_iob_func`.

## Expected
The image carries a C toolchain (GitHub runners do), since AxiomCode's mathlib-quality blueprint workflow tells agents to build Verso blueprints.

## Reproduction
Reproduced 2026-10-21 in this session: `command -v cc gcc clang` prints nothing; `ls /usr/bin/cc /usr/bin/gcc` -> No such file; `dpkg -l` shows only gcc-12-base and libgcc-s1 (runtime), no compiler, no libc6-dev. Then `lake build` in any verso-blueprint project fails as above.

## Cause
- Defect: AxiomMath/axiom `agents/definitions/axiomcode/Dockerfile` L43-52 installs TeX, graphviz, unzip; L76-79 postgresql; nothing installs gcc/libc6-dev. Base `agents/definitions/base/sidecar/Dockerfile` (FROM runloop/starter-x86_64) has none either.
- Trigger: MD4Lean `lakefile.lean:22-24`, `:36-39` call `compileO ... flags` without a compiler on non-Windows, i.e. Lake's default `cc` (upstream design, not a bug).
- Fix: add `build-essential` (or `gcc libc6-dev`) to the L47-52 apt layer.

## Versions
AxiomCode plugin 0.5.103, substrate axiomcode 0.5.103 (/opt/axiomcode/src); Debian 12 bookworm; AI_AGENT=claude-code_2-1-286_agent; Dockerfile at 8ab043dc9527987426e7c3fafb1669c1fe008e9d; v5 dir head 5f09e618c0646f81311a7aaa28f894f4dfef78a7.

## Related issues and PRs
None found. Searched axiom label axiomcode-v5 and AxiomCodeV5 for Dockerfile, compiler, gcc, cc, Verso, apt-get, C code; owner-wide for "could not execute external process", "stdlib.h", "C toolchain", "MD4Lean", "build-essential". PRs: "build-essential", "axiomcode Dockerfile gcc" — nothing relevant.

## Workaround
Scratch `cc` wrapper (.axiomcode/scratch/blueprint/cc + include/) = toolchain clang + scratch include dir with glibc prototypes.

## Upstream draft
none
