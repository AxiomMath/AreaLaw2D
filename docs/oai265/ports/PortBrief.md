# Port brief: TNLean Lemma 9.1 (collar scan) chain into quantum-arealaw (read-only input)

Repository: /root/dev/quantum-arealaw-0cbdab1d (branch agents/0cbdab1d-a2fa-5f7c-9b5c-caa522495455).
Read /root/dev/quantum-arealaw-0cbdab1d/CLAUDE.md first: its conventions bind every file you write.

Goal of the campaign: Proposition 9.6 (`OpenAI.collar_bound`, OpenAI/Statements.lean) of OAI265.
This pass ports, file by file, the TNLean chain ending at
`TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_historyFacts_actualScanRound`
(Lemma 9.1 for the actual collar-scan rounds), which Proposition 9.2 and hence 9.6 use.
The charter says: "Port TNLean file by file at v4.33 with attribution, only along a spine
theorem's cone."

## Sources (read-only clones; never edit them)

- TNLean `74ecad48c` (2026-10-15): a TNLean clone at 74ecad48c: 
- QICLean `e44381d9` (TNLean's pin): a QICLean clone at e44381d9: 
- Paper TeX: .axiomcode/scratch/prop96-pass2/oaimath/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/
  (`08-scanner.tex` is Section 9; file numbers are one less than section numbers.)
- `portmap.txt` (same directory): `<source path> <OpenAI module>` lines for every TNLean/QICLean
  file the repo already ported (or cites). Use it to resolve your file's imports. A source
  module listed there is ALREADY in the repo: import the OpenAI module, never port it again.
  The repo's ports came from older QICLean revisions (`5f76b263`, `32a5a1a8`); if a declaration
  your file needs differs or is missing there, add the minimal missing lemma to YOUR file (or
  ask in your report), never edit the existing module.

## Where your files go, and their names

- `TNLean.PEPS.AreaLaw.Scan.X`  -> `OpenAI/Scan/X.lean`, module `OpenAI.Scan.X`.
- other `TNLean.PEPS.AreaLaw.X` -> `OpenAI/X.lean`, module `OpenAI.X`.
- `TNLean.Circuit.X`            -> `OpenAI/X.lean`.
- `QICLean.<Dir>.X`             -> `OpenAI/X.lean`; under `Representation/ReplicaTransport/`
  the repo convention is `OpenAI/ReplicaTransportX.lean`.
- Namespaces: `TNLean.PEPS.AreaLaw.Scan` -> `OpenAI.Scan`; `TNLean.PEPS.AreaLaw` -> `OpenAI`;
  QICLean-origin namespaces (`TensorPower`, `TensorPower.ReplicaTransport`, `Entropy`,
  `FiniteProduct`, ...) are kept exactly as the repo's existing ports keep them (check the
  imported OpenAI module). Declaration names otherwise unchanged, so later ports line up.
- Header: Apache-2.0 copyright block of the source, then a line
  `Ported from LionSR/TNLean commit 74ecad48c..., <source path> (Apache 2.0).`
  (or QICLean `e44381d9...`), listing any adaptation. Follow the existing ports, e.g.
  OpenAI/FiniteSetTruncation.lean and OpenAI/ReplicaTransportProposition.lean.

## Rules

1. Statements are the source's, verbatim up to the renamings above and Lean/Mathlib v4.33
   spelling. Never weaken one. If a statement cannot be ported as is, stop on that
   declaration and say exactly why in your report.
2. No `sorry`, no `axiom`, no `native_decide`, no `admit`. Every file you write must pass
   `axle_check` with no errors and no disallowed axioms; run `axiom_audit` on its main theorems.
3. Never `import Mathlib` (CLAUDE.md): replace TNLean's `import Mathlib` by the specific
   Mathlib modules needed (and the OpenAI modules from portmap.txt).
4. Never introduce a parallel encoding of something the repo already has. In particular:
   strong subadditivity is `Arealaw.vonNeumann_strong_subadditivity` (positive semidefinite
   matrices of any trace) and `OpenAI.RegionSSA` / `OpenAI.ConditionalMovement.StrongSubadditivity`;
   do NOT port QICLean's Lieb/Ando/Klein/relative-entropy chain. Lemma 3.1 (marginal tails) is
   `OpenAI.MarginalTails`; Lemma 11.1 (two families) is `OpenAI.TwoFamily`. Search the repo
   (Grep over OpenAI/ and Arealaw/) and `mathlib_search` before porting any helper.
5. Write ONLY the files assigned to you. Never edit an existing file, OpenAI.lean (generated
   umbrella), OpenAI/Audit.lean, Statements.lean, anything under Arealaw/ or OpenAI/Geometry/
   (owned by another run). Do not commit, push, or run `lake build` of the whole library;
   the coordinator does those. Scratch only in `.axiomcode/scratch/prop96-pass2/<your task id>/`
   (create it, remove it at the end); never use Arealaw/Probe.lean (shared).
6. You may use `lake env lean OpenAI/Scan/X.lean` or `lake build OpenAI.Scan.X` for your own
   modules if Axile is slow; never build the whole library.
7. Docstrings: every definition and main theorem keeps (or gets) one; keep the source's
   paper citations; no LLM prose (CLAUDE.md).

## Report back

- each file written, by path, with its main declarations `name file:line`;
- `axle_check` result per file and `axiom_audit` output quoted exactly;
- every adaptation (renamed dependency, added helper, changed spelling) by declaration;
- anything you could not port, stated plainly; any tool bug, starting `BUG:`.
# Addendum for the Proposition 8.1 comparator campaign (read after BRIEF.md)

The roots are TNLean `Scan/ActualSharpUpper`, `Scan/ActualRoughUpper`,
`GlobalSchmidtBellRoughLower`, `GlobalSchmidtBellRoughUpper`, `GlobalSchmidtBellPrevector`
(Proposition 8.1 pieces). `ComparatorPortMap.md` (this directory) classifies every module of
their closure: ALREADY (do not port; use the named repo declarations), PARTIAL (port only
what is missing, reuse the rest), NEW, GEOMETRY (not ported: the repo states templates
natively), with a `cone` column = declarations of the file reachable by name from the roots.

- Target path for `QICLean.<Dir>.<Sub>.X`: `OpenAI/X.lean`; if that file already exists, or the
  name is generic (Reindex, Kernel, Basic, Defs, ...), use `OpenAI/<Sub or Dir>X.lean`
  (e.g. `QICLean.Analysis.GaussianFilter.Reindex` -> `OpenAI/GaussianFilterReindex.lean`).
  TNLean files as in BRIEF.md. Record any rename in your report.
- A file whose map notes say the cone uses only a few declarations (e.g. HermitianHelpers,
  KleinInequality, MaximallyEntangled): port those declarations and whatever they need,
  not the rest; say which you left out. Otherwise port the whole file.
- Before porting a NEW general matrix/analysis lemma, search Mathlib and Physlib
  (`.lake/packages/mathlib`, `.lake/packages/Physlib`; `mathlib_search`): if the statement is
  there under another name, prove the source's statement from it in one line (keep the
  source name so downstream ports line up) rather than re-proving it.
- Never `import Mathlib`. Never `lake build` (another build runs in this checkout); use
  axle_check and retry after a few minutes when it times out.
