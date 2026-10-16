# Proposition 9.6 (`CollarBound`) plan

This note records the dependency audit for the frozen proposition
`OpenAI.CollarBound` and the implementation plan for `OpenAI.collar_bound`.  It
does not change either declaration in `OpenAI/Statements.lean`.

## Sources and conventions

The audit was made against:

- this repository at `e52509f` (the proved Proposition 4.3);
- the paper source at revision `adc7f4935e1a60f571e69a0d2567108452292ae9`,
  especially `03-quasilocal.tex` through `08-scanner.tex`;
- LionSR/TNLean at `fc565830cec69e8226e521d56c86d39845d45576`;
- QICLean at TNLean's pinned revision
  `5f76b263e3a1c418645102d90f7bef6b92f04cf3`.

TNLean and QICLean are read-only reference implementations.  Code ported from
them will retain the Apache-2.0 attribution used by the existing ports in this
repository.  The audited TNLean checkout currently contains 128 Lean files in
`TNLean/PEPS/AreaLaw/Scan`; the 122-file count in the task brief describes an
earlier snapshot and does not affect the conclusions below.

Paper section numbers are one greater than the leading numbers of the relevant
source files: `06-transport.tex` is Section 7, `07-comparators.tex` is Section
8, and `08-scanner.tex` is Section 9.

## Dependency cone

The direct proof of Proposition 9.6 in Section 9 has two branches.

1. Proposition 9.5 supplies the improved box/shell entropy estimate at exponent
   \(1-\varepsilon\).
2. Lemma 9.4 turns a separated template into the collar geometry and its
   boundary/cardinality estimates.  Proposition 9.2 is then applied to the
   scanner for that collar, using Proposition 8.1 for comparison, and Lemma 2.1
   for continuity.  The final step uses the exact entropy identity and
   monotonicity of mutual information under enlargement.

The full transitive cone is:

| Result | Essential inputs | Status in this repository | TNLean/QICLean status |
| --- | --- | --- | --- |
| Proposition 9.6, collar bound | Proposition 9.5, Lemma 9.4, Proposition 9.2, Proposition 8.1, Lemma 2.1, entropy identity and MI monotonicity | frozen statement; proof is `sorry` | deterministic collar reduction is proved conditionally in `CollarInformation.lean`; the required MI estimate is not supplied |
| Proposition 9.5, exponent bootstrap | Proposition 3.3, repeated Proposition 9.2 and rough Proposition 8.1, Lemmas 2.1 and 3.1, rectangle/template shell covering | Proposition 3.3 and Lemmas 2.1/3.1 are proved; the bootstrap is absent | initial rounded-collar entropy and the finite arithmetic iteration are proved; the one-step improvement, hence Proposition 9.5, is not |
| Proposition 9.2, scanner estimate | Proposition 4.5, Lemma 9.1, Proposition 7.4, Proposition 8.1, Lemmas 2.1 and 3.1 | absent | `scanner_estimate` proves the bookkeeping conclusion from a supplied `ScanData`; it does not construct `ScanData` from the physical model |
| Lemma 9.1, scan histories | scan geometry, rounding, fill and charge accounting | absent | many actual geometry/probability/history pieces are proved, including fill/charge specialization, but no complete physical scanner package |
| Proposition 8.1, comparators | Schur labels and replicas, common replica metric, coherent pins, scalar symbols, typical-label moments and defect projections | absent | common prevector and rough upper/lower components exist, as do sharp-lower primitives in QICLean; the complete sharp comparison and physical assembly are absent |
| Proposition 7.4, transport | Lemmas 7.1--7.3 and replica Lemmas 6.3--6.4 | absent | generic transport and an actual scan fill/charge specialization are proved; their construction relies on replica/coherent-pin data |
| Lemmas 7.1--7.3 | finite weighted geometric means, normalized derivative UCP maps, Fourier multipliers | absent | proved as matrix analysis in QICLean |
| Lemmas 6.1--6.4 | Schur--Weyl labels, common replica metric, relative coherent pin, scalar symbols; Section 5 conditional lemmas | absent | formalized across QICLean's representation/replica transport layer |
| Section 5 conditional lemmas | finite-dimensional marginal movement, marginal phase, skew estimates | absent as paper-numbered results | proved in QICLean/TNLean's conditional-estimate modules |
| Proposition 4.5, finite-set truncation | Proposition 4.3, Lemma 4.4, truncation series, crossing counts, gap perturbation | absent | proved in TNLean's finite-set truncation and crossing-budget files |
| Lemma 4.4, quasilocal roots | positive replacement from Proposition 4.3, square-root Hölder estimates, root channels | the needed square-root kernel/Hölder infrastructure and Proposition 4.3 are proved; lemma absent | proved in `QuasilocalRoots.lean` using QICLean `Analysis.RootChannel` |
| Proposition 4.3 | Lemmas 2.1, 3.1, 3.2 and Proposition 3.3 plus matrix-analysis support | proved | also proved in TNLean |

Thus Proposition 4.3 is not the remaining conceptual bottleneck.  The first
unavoidable wall on the scanner spine is the replica/Schur--Weyl chain: Lemma
6.1 (Schur labels), Lemma 6.2 (common replica metric), Lemma 6.3 (relative
coherent pin), and Lemma 6.4 (scalar symbols).  Those data are required to
instantiate Proposition 7.4 and then the sharp half of Proposition 8.1.

## What the reference development proves

The following are genuine theorems in TNLean/QICLean, rather than assumptions
hidden in a scanner interface:

- Lemma 4.4's root construction and its completely positive/unital,
  amplification-contractive, tail, ground-vector, and local-fixed-point
  properties;
- Proposition 4.5's finite-set truncation, gap perturbation, and crossing
  budget in TNLean's model encoding;
- the Section 5 finite-dimensional conditional estimates;
- the Section 6 replica/Schur--Weyl machinery in QICLean;
- the Section 7 operator-mean, normalized derivative, Fourier multiplier, and
  generic transport analysis, plus TNLean's actual scan fill/charge
  specialization;
- several Proposition 8.1 components: the global Schmidt--Bell prevector and
  rough comparisons, and lower-comparison primitives;
- substantial actual Lemma 9.1 scan geometry, histories, rounding, marginal
  tails, target-window, fill/charge, and scalar bookkeeping;
- the initial rounded-collar entropy estimate;
- the finite arithmetic iteration which converts an assumed eventual
  improvement into a uniform exponent bound;
- the deterministic entropy/MI and boundary/cardinality reduction used at the
  end of Proposition 9.6.

In particular, `InitialRoundedCollarEntropy.lean` supplies the initial weak
shell estimate.  It is not the one-step improvement required by Proposition
9.5.

## What is packaged as hypotheses

TNLean's `Scan.Scanner.scanner_estimate` is a substantial proved accounting
theorem, but its input `ScanData` contains fields corresponding to the needed
conclusions of Lemma 9.1, Proposition 7.4, Proposition 8.1, Lemma 2.1, and the
typical-window lemma.  Supplying such a structure is therefore not a proof of
Proposition 9.2.  The reference note
`docs/paper-gaps/arealaw2d_scanner_inputs.tex` explicitly records the missing
assembly from one original/truncated vector, transported measures, common
prevector, and full comparator bounds.

Likewise, `ExponentBootstrap.lean` proves an arithmetic conclusion only after
assuming the eventual one-step improvement.  `CollarInformation.lean` proves
the final collar reduction only after assuming the required mutual-information
inequality.  Neither assumption may be turned into a sorried existence
structure in this repository.

## What no audited implementation currently supplies

Neither this repository nor the audited TNLean/QICLean revisions contain all
of the following:

- a source-faithful construction of the physical inputs for Proposition 9.2
  from a single Hamiltonian, ground state, and finite-set truncation;
- the complete sharp upper and lower Proposition 8.1 comparison, including
  its scan-specific assembly;
- the one-step entropy improvement and therefore full Proposition 9.5;
- the resulting mutual-information inequality and full Proposition 9.6;
- bridges from TNLean's encodings to the frozen `OpenAI.Statements` interfaces.

The geometry branch through Lemma 9.4 is also not work for this run: the
geometry files are owned by the Proposition 11.2 run.

## Implementation sequence before the replica wall

Every new headline declaration will be enrolled in `OpenAI/Audit.lean`; every
step will be built, have its axioms printed, committed, and pushed separately.
No statement in `OpenAI/Statements.lean` and no geometry file will change.

1. **Root channel and Lemma 4.4.**  Port the minimal QICLean root-channel
   analysis and TNLean `QuasilocalRoots.lean`, then instantiate it from this
   repository's proved Proposition 4.3.  The C*-algebraic channel statements
   will be proved over `ℂ`; any frozen real/complex interface that later needs
   them will cross through `OpenAI/Embedding.lean`.  Scalar square-root
   identities will be isolated as their own lemmas.
2. **Proposition 4.5.**  Port the finite-set truncation, gap perturbation, and
   crossing-budget chain in this repository's interaction encoding.  This is
   the last physical localization input that does not require replicas.
3. **Pure Section 7 matrix analysis.**  Port only the reusable non-replica
   layer: finite weighted geometric means, normalized derivative UCP maps, and
   Fourier multiplier estimates.  Do not claim Proposition 7.4 until Lemmas
   6.3--6.4 are available.
4. **Pure Section 8--9 information identities.**  Add the non-geometric
   entropy identity, mutual-information monotonicity/continuity, and any scalar
   exponent bookkeeping that can be stated honestly in the existing model.
   Do not introduce a `ScanData`-like structure whose fields simply assume the
   missing spine conclusions.
5. **Stop at the hard wall.**  At that point the exact next spine work is the
   Section 6 replica/Schur--Weyl chain (Lemmas 6.1--6.4), followed by the full
   sharp Proposition 8.1 comparison and physical Proposition 9.2 assembly.

## Estimate

The plan and source audit take about 0.5 hour.  Lemma 4.4 and its root-channel
support are estimated at 1.5--2.5 hours; Proposition 4.5 at 3--5 hours; the
useful pure Section 7 layer at 3--5 hours; and the independent Section 8--9
information identities at 1--2 hours.  The total non-replica cone is therefore
roughly 9--14 hours including integration and audits.  Under the 12-hour stop,
the expected result is Lemma 4.4, Proposition 4.5, and as much of the pure
Section 7/9 layer as can be completed cleanly; the time limit may cut off the
tail of that list before the conceptual replica wall is reached.

