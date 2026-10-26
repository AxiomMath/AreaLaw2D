# A two-dimensional area law from a global spectral gap, in Lean 4

A Lean 4 formalization of *A two-dimensional area law from a global spectral gap*
(`paper/paper.pdf`, LaTeX in `paper/sections/`).

## What is proved

The paper's results are stated as `def … : Prop` in `OpenAI/Statements.lean`, for every
`RCLike` scalar field `𝕜`, and each is proved:

| Paper | Statement | Lean proof |
| --- | --- | --- |
| Theorem 1.1 (area law) | `OpenAI.AreaLaw` | `AreaLaw.areaLaw` |
| Corollary 1.2 | `OpenAI.AreaLawCorollary` | `AreaLaw.areaLawCorollary` |
| Lemma 2.1 | `OpenAI.ConditionalContinuity` | `AreaLaw.conditionalContinuity` |
| Lemma 3.1 | `OpenAI.MarginalTails` | `AreaLaw.marginalTails` |
| Lemma 3.2 | `OpenAI.BufferDiscount` | `AreaLaw.bufferDiscount` |
| Proposition 3.3 | `OpenAI.InitialBoxEstimate` | `AreaLaw.initialBoxEstimate` |
| Proposition 4.3 | `OpenAI.PositiveReplacement` | `AreaLaw.positiveReplacement` |
| Proposition 9.6 | `OpenAI.CollarBound` | `AreaLaw.Scanner.prop_9_6`, `AreaLaw.collarBound_of_complex` |
| Proposition 10.2 | `OpenAI.Amplification` | `AreaLaw.amplification` |
| Lemma 11.1 | `OpenAI.TwoFamilyCancellation` | `AreaLaw.twoFamilyCancellation` |
| Proposition 11.2 | `OpenAI.TwoFamilyDecomposition` | `AreaLaw.Geometry.prop_11_2` |

There is no `sorry` outside `Challenge/`, and every result depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## The tree

| Path | Content |
| --- | --- |
| `OpenAI/Statements.lean` | The statements: lattice domains, admissible Hamiltonians, the global gap, the edge boundary, and the results above as `def … : Prop`. Imports only Mathlib, Physlib and `AreaLawForMathlib`. |
| `AreaLaw/` | The proof, one module per paper section: `S01_AreaLaw`, `S02_Preliminaries`, `S03_InitialBox`, …, `S11_Geometry`; larger sections are split by subsection. Declarations are named by paper number (`lemma_6_4`, `prop_9_6`, `step_11_26_3`) and proof steps carry their digest ids (`-- D6.4.2`). The development is over `ℂ`; `AreaLaw/Transfer.lean` proves each `RCLike 𝕜` statement from its `ℂ` instance. |
| `AreaLawForMathlib/` | Results Mathlib and Physlib lack, in Mathlib's layout (`Analysis/Matrix/`, `RepresentationTheory/SchurWeyl/`, `QuantumInfo/`, …); each file names the Mathlib or Physlib file it extends. `QuantumInfo/Region/` holds the region encoding the statements use: configurations `Reg`, the partial trace `ptrace`, states `SubState`/`MState`, `regionEntropy`, `mutualInfo`, the trace distance. |
| `digest/` | The paper digest: one file per section, every result, definition and proof step with an anchor `D<section>.<n>`. |
| `Map.md` | Anchor → Lean declaration, with file and line. |
| `blueprint/` | The Verso blueprint (below). |
| `Challenge/`, `Solution/`, `Comparator/` | The comparator pair for Theorem 1.1 (below). |
| `scripts/audit.lean` | `#print axioms` of every frozen statement's proof. |
| `RefactoringPlan.md`, `RefactoringResult.md` | The structure the code follows, and the record of route differences from the paper, constants and digest corrections. |
| `docs/StatementAudit.md` | Clause-by-clause comparison of `OpenAI/Statements.lean` with the paper. |

## Building

Lean `v4.33.0`, Mathlib `v4.33.0`, [Physlib](https://github.com/leanprover-community/physlib)
at the commit pinned in `lake-manifest.json`.

```bash
lake exe cache get
lake build
lake env lean scripts/audit.lean     # axioms of each frozen statement's proof
lake exe mk_all --check            # the roots AreaLaw.lean, AreaLawForMathlib.lean, OpenAI.lean are up to date
```

## The comparator

`Challenge/Basic.lean` restates Theorem 1.1 with every definition it needs copied in,
importing only Mathlib and Physlib, and leaves the theorem and two partial-trace facts
(`Arealaw.posSemidef_ptrace`, `Arealaw.trace_ptrace`) as `sorry`. `Solution/Basic.lean` proves
them from the development (`OpenAI.Challenge.area_law` applies `AreaLaw.areaLaw`).
`Comparator/comparator.json` fixes the theorem names and the permitted axioms;
[comparator](https://github.com/leanprover/comparator) checks that the solution proves exactly the
challenge's statements with only those axioms:

```bash
comparator Comparator/comparator.json
```

## The blueprint

`blueprint/` is a [Verso Blueprint](https://github.com/leanprover/verso-blueprint) package: one
chapter per paper section, one node per digest anchor, each linked to its Lean declaration. Its
dependency graph is checked against the digest's DAG (`blueprint/scripts/check_dag.py`).

```bash
lake build                      # the library first
cd blueprint && ./scripts/ci-pages.sh   # site in blueprint/_out/site/html-multi/
```

## License

Apache License 2.0; see `LICENSE` and `NOTICE`.
