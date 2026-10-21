import Verso
import VersoManual
import VersoBlueprint
import AreaLawBlueprint.TexPrelude
import AreaLawRefactored

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Introduction" =>

§1 fixes the setting (finite induced subgraph $`\Lambda\subset\mathbb Z^2`, local dimension $`q`, Hamiltonians with supports of $`d_\Lambda`-diameter $`\le R` and term norms $`\le J`, global gap $`\Delta`) and states Theorem 1.1: $`S_\Omega(A)\le C|\partial_\Lambda A|`, $`C=C(q,R,J,\Delta)` independent of $`\Lambda`, $`A`, $`H`. Corollary 1.2 converts to the two vertex-boundary conventions and covers rectangles. Then a tensor-network consequence proved in a companion paper, and a five-stage outline reducing the area law to one analytic statement (mutual information of a region with everything beyond a collar is $`O(n^{-100})`) and one geometric statement (cover $`A` minus $`O(|\partial_\Lambda A|)` sites by two ordered families of well-separated templates). Only Cor 1.2 is proved in §1; Theorem 1.1 is proved at the end of §11 from §2–§11. Conventions exported: $`d_\Lambda`, $`\partial_\Lambda`, $`Z_A`, $`I_\Omega`, natural logarithms, $`C=C(q,R,J,\Delta)`.

:::definition "D1.1" (lean := "OpenAI.domainEDist, OpenAI.Qudits, Arealaw.Reg")
*D1.1* — Def: Domain, graph distance, Hilbert space

Source: `00-introduction.tex` L12–L18.

$`\Lambda\subset\mathbb Z^2` finite. Edges: pairs $`\{x,y\}\subseteq\Lambda` with $`|x-y|_2=1` (equivalently $`|x-y|_1=1`). $`\Lambda` carries the induced graph.

$`d_\Lambda` = graph distance in this graph; $`d_\Lambda(x,y)=+\infty` for $`x,y` in different components.

$`\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}\mathbb C^q`. An operator supported on $`X\subseteq\Lambda` acts as the identity on the factors outside $`X`.

_Used from._ none.

:::

:::definition "D1.2" (lean := "OpenAI.hamiltonian, OpenAI.IsAdmissible") (uses := "D1.1")
*D1.2* — Def: Admissible Hamiltonian (eq:hamiltonian)

Source: `00-introduction.tex` L18–L27.

Fix integers $`q\ge1`, $`R\ge0` and a real $`J>0`. $`H` is admissible if $$`H=\sum_{\substack{\varnothing\neq X\subseteq\Lambda\\ \operatorname{diam}_{d_\Lambda}X\le R}}h_X,\qquad h_X=h_X^*,\qquad\|h_X\|\le J,` with $`h_X` supported on $`X`. One summand per support $`X`; $`h_X=0` allowed.

_Used from._ {bpref "D1.1"}[D1.1].

:::

:::definition "D1.3" (lean := "OpenAI.edgeBoundary, OpenAI.pureState, Arealaw.SubState.regionEntropy") (uses := "D1.1")
*D1.3* — Def: Edge boundary, reduced state, entanglement entropy

Source: `00-introduction.tex` L29–L37.

$`\partial_\Lambda A=\{\{x,y\}: x\in A,\ y\in\Lambda\setminus A,\ |x-y|_1=1\}` for $`A\subseteq\Lambda`.

For a unit vector $`\Omega\in\mathcal H_\Lambda`: $`\rho_A=\operatorname{Tr}_{\Lambda\setminus A}|\Omega\rangle\langle\Omega|`, $`S_\Omega(A)=-\operatorname{Tr}\rho_A\log\rho_A`, $`0\log0=0`. Logarithms natural.

_Used from._ {bpref "D1.1"}[D1.1].

:::

:::theorem "D1.4" (lean := "AreaLaw.theorem_1_1")
*D1.4* — Theorem 1.1: Area law

Source: `00-introduction.tex` L39–L53 (statement). Proof: `10-geometry.tex` L801–L857.

For all integers $`q\ge1`, $`R\ge0` and reals $`J>0`, $`\Delta>0` there is a finite $`C=C(q,R,J,\Delta)` such that the following holds. Let $`\Lambda\subset\mathbb Z^2` be a finite induced square-lattice domain and $`H` an admissible Hamiltonian ({bpref "D1.2"}[D1.2]) on $`\mathcal H_\Lambda` with a unique normalized ground vector $`\Omega` (up to phase), ground energy $`E_0`, and $$`H-E_0\,\mathrm{id}\ \ge\ \Delta\bigl(\mathrm{id}-|\Omega\rangle\langle\Omega|\bigr).` Then for every $`A\subseteq\Lambda` $$`S_\Omega(A)\le C\,|\partial_\Lambda A|\qquad\text{(eq:area-law)}.` The same $`C` serves all such $`\Lambda`, $`A`, $`H`.

:::

:::proof "D1.4" (uses := "D1.1, D1.2, D1.3, D1.6, D1.11")
{bpref "D11.26"}[D11.26], from Lemma 11.1 (D1.12 = {bpref "D11.1"}[D11.1]), Prop 9.6 ({bpref "D9.25"}[D9.25]), Prop 10.2 ({bpref "D10.4"}[D10.4]), Prop 11.2 ({bpref "D11.4"}[D11.4]) and Lemma 2.2 ({bpref "D2.12"}[D2.12]).

_Used from._ {bpref "D1.1"}[D1.1], {bpref "D1.2"}[D1.2], {bpref "D1.3"}[D1.3], {bpref "D1.6"}[D1.6] ($`Z=Z_A`), {bpref "D1.11"}[D1.11] (statement only).

:::

:::definition "D1.6" (lean := "OpenAI.innerBoundary, OpenAI.cutEndpoints") (uses := "D1.3")
*D1.6* — Def: Inner boundary and endpoint set

Source: `00-introduction.tex` L60–L67.

For $`A\subseteq\Lambda`: $$`\partial_{\rm in}A=\{x\in A:\ \exists y\notin A,\ \{x,y\}\in\partial_\Lambda A\},\qquad Z_A=\bigcup_{e\in\partial_\Lambda A}e .` $`Z_A=\partial_{\rm in}A\ \dot\cup\ \partial_{\rm out}A` with $`\partial_{\rm out}A\subseteq\Lambda\setminus A` the outer endpoints (notation of this digest, not of the paper).

_Used from._ {bpref "D1.3"}[D1.3].

:::

:::corollary "D1.7" (lean := "AreaLaw.corollary_1_2")
*D1.7* — Corollary 1.2: Rectangles and vertex boundaries

Source: `00-introduction.tex` L69–L86.

(a) The conclusion of Theorem 1.1 holds for every subset of a finite rectangular square lattice with bounded on-site and nearest-neighbor interactions and a unique ground state separated by a fixed global gap. (b) For every domain covered by Theorem 1.1 and with $`C` its constant: $$`S_\Omega(A)\le4C|\partial_{\rm in}A|,\qquad S_\Omega(A)\le2C|Z_A|.`

:::

:::proof "D1.7" (uses := "D1.4, D1.6")
*D1.7.1* (a): $`\Lambda=\{1,\dots,L_1\}\times\{1,\dots,L_2\}` is an induced domain. Supports $`\{x\}` and $`\{x,y\}` with $`|x-y|_1=1` have $`d_\Lambda`-diameter $`\le1`. Merge terms on equal supports (norm $`\le J` after merging); $`H` is admissible with $`R=1`, $`C=C(q,1,J,\Delta)`.

*D1.7.2* $`|\partial_{\rm in}A|\le|\partial_\Lambda A|`: $`e\mapsto` (its endpoint in $`A`) maps $`\partial_\Lambda A` onto $`\partial_{\rm in}A`.

*D1.7.3* $`|\partial_\Lambda A|\le4|\partial_{\rm in}A|`: each $`x\in\partial_{\rm in}A` has between 1 and 4 crossing edges (degree $`\le4` in $`\mathbb Z^2`). So $`S_\Omega(A)\le C|\partial_\Lambda A|\le4C|\partial_{\rm in}A|`.

*D1.7.4* $`|Z_A|\le2|\partial_\Lambda A|`: union of $`|\partial_\Lambda A|` two-element sets.

*D1.7.5* $`|\partial_\Lambda A|\le2|Z_A|`: $`c(v)` = number of crossing edges at $`v\in Z_A`; $`1\le c(v)\le4` and $`\sum_{v\in Z_A}c(v)=2|\partial_\Lambda A|` (each edge counted at both endpoints). So $`2|\partial_\Lambda A|\le4|Z_A|` and $`S_\Omega(A)\le C|\partial_\Lambda A|\le2C|Z_A|`.

*D1.7.6* Empty boundary: $`\partial_\Lambda A`, $`\partial_{\rm in}A`, $`Z_A` empty simultaneously; inequalities read $`0\le0`.

_Formal route_ (RefactoringResult.md §5, D1.7.3, D1.7.5): any graph of degree ≤ k (`step_1_7_3`, `step_1_7_5`, AreaLawRefactored/S01\_AreaLaw.lean:77, :94), k = 4 by `card_filter_squareLattice_adj_le` (:124). Reason: dimension rule (2d in ℤ^d).

_Used from._ {bpref "D1.4"}[D1.4], {bpref "D1.6"}[D1.6].

:::

:::definition "D1.11" (lean := "Arealaw.SubState.mutualInfo") (uses := "D1.3")
*D1.11* — Def: Mutual information

Source: `00-introduction.tex` L123–L130.

For disjoint $`B,C\subseteq\Lambda`: $$`I_\Omega(B:C)=S_\Omega(B)+S_\Omega(C)-S_\Omega(B\cup C).`

_Used from._ {bpref "D1.3"}[D1.3].

:::
