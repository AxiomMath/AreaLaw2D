import Verso
import VersoManual
import VersoBlueprint
import AreaLawBlueprint.TexPrelude
import AreaLaw

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Norm comparisons from an auxiliary pair" =>

Fix normalized pure $`\widetilde\Omega` on a finite physical system, ground vector of positive $`\widetilde H` with gap $`\widetilde g`, target $`X`, finitely many statuses ($`K` four-part partitions $`X,U_g,Y_g,V_g`). Append Bell-paired auxiliaries $`C,R` of dimension $`d_*=|E|`, $`E` a typical Schmidt set of $`X`. On $`k` replicas: Schur metrics of §6, $`A_{j,g}=(W_{P}^{-1}W_{F}^{-1}W_{Y})^2`, $`P=CXU_{j,g}`, $`F=RV_{j,g}`, glued by the mean tree of §7. $`\mathrm{pre}_k` = physical mean-energy eigenvector with fixed Schur label on $`C`, $`R`. $`N=\|\mathcal M^{-s}\mathrm{pre}_k\|` bounded two ways. Upper: project $`XC` onto Bell => $`\mathrm{pre}_k` pinned to $`(\sqrt z/d_*)^k\pi_R^{\lambda_k}\mathrm{post}_k`; Cauchy–Schwarz and Jensen on the tree; rough version uses cutoffs from nested $`\mathcal R` with $`S(B)\le B_{\rm sh}`, sharp uses `comparator:mgf-data` and gives $`\langle g^{\rm post}\rangle_{\rm av}`. Lower: gap forces most copies of $`v=\mathcal M^{-s}\mathrm{pre}_k/N` into the ground state (defect mass $`\ge1-E_{\rm def}/\tau`); on components with $`r\le\tau k` excited copies the inverse metric is $`\le e^{-kaL}`, $`L\ni2S'` since large auxiliary labels survive on good copies; the operator lower pin passes through the tree by monotonicity and homogeneity; $`-\log N^2\ge2s\langle v,\log\mathcal M v\rangle`. Exact entropy identity turns the sharp lower-minus-upper gap into $`I(X{:}V)+I(X{:}YV)`. §9 consumes both bounds and the identity; §7 supplies smallness of $`E_{\rm def}`.

Standing conventions. $`\log` natural. $`\poly(k)` = polynomial in $`k`, degree/coefficients depending on the fixed system; $`o_k(1)`, $`o(k)` likewise. $`F_{Q}`, $`W_Q`, $`\pi^\lambda_Q` = Schur-label observable, metric, label projector of region $`Q` on $`k` copies (§6, `replicas:F-definition` {bpref "D6.3"}[D6.3], `replicas:w-definition` {bpref "D6.5"}[D6.5]); $`k` suppressed.

# 8.0 Setup

:::definition "D8.1" (lean := "AreaLaw.Comparators.Statuses, AreaLaw.Comparators.PhysData, AreaLaw.Comparators.step_8_1") (uses := "D4.11")
*D8.1* — Def: Physical data, statuses, nesting

_Source: 07-comparators.tex 13–35, `comparator:nesting`._

$`\widetilde\Omega\in\mathcal H_{\rm phys}` normalized pure vector; $`\widetilde H` positive Hamiltonian with unique ground vector $`\widetilde\Omega`, ground energy $`\widetilde E_0`, gap $`\widetilde g>0`. $`X` fixed physical subsystem. A _status_ is $`K` partitions $$`\mathcal H_{\rm phys}=\mathcal H_X\otimes\mathcal H_{U_g}\otimes\mathcal H_{Y_g}\otimes\mathcal H_{V_g},\qquad1\le g\le K.` Finitely many allowed statuses. For every allowed choice of two statuses and every $`g<g'` ($`g` from the first, $`g'` from the second): $$`XU_gY_g\subseteq XU_{g'}.\tag{comparator:nesting}` Juxtaposition = union of disjoint tensor factors. All entropies in $`\widetilde\Omega` unless said otherwise. No traversal procedure, no geometric scales.

_Used from._ None in §8 (Prop 4.5 ({bpref "D4.11"}[D4.11]) gives $`\widetilde\Omega,\widetilde H`; §9 supplies statuses).

:::

:::definition "D8.2" (lean := "AreaLaw.Comparators.TypicalSet") (uses := "D3.1")
*D8.2* — Def: Typical Schmidt set

_Source: 07-comparators.tex 37–47, `comparator:typical-set`._

$`p_i` = Schmidt coefficients (squared) of $`\widetilde\Omega` across $`X|X^c`, $`S_X=S(X)`. $`E` = nonempty set of positive Schmidt indices of $`X` such that for some $`w\ge0` $$`e^{-S_X-w}\le p_i\le e^{-S_X+w}\ (i\in E),\qquad z=\sum_{i\in E}p_i>0.\tag{comparator:typical-set}` $`d_*=|E|`, $`p_i'=p_i/z`, $`S'=-\sum_{i\in E}p_i'\log p_i'`.

_Used from._ None. Later: Lemma 3.1 ({bpref "D3.1"}[D3.1]) supplies $`w=n^{3/5}`, $`z\ge1-n^{-100}` for scale $`n\ge2`; only (comparator:typical-set) is used in §8.

:::

:::lemma_ "D8.3" (lean := "AreaLaw.Comparators.step_8_3")
*D8.3* — Step: Typical entropies

_Source: 07-comparators.tex 48–54, `comparator:typical-entropies`._

$$`|\log d_*-S_X|\le w+|\log z|,\qquad|S'-S_X|\le w+|\log z|.`

:::

:::proof "D8.3" (uses := "D8.2")
*D8.3.1* Sum {bpref "D8.2"}[D8.2] over $`E`: $`d_*e^{-S_X-w}\le z\le d_*e^{-S_X+w}`. Logs: $`\log d_*-S_X=\log z+\theta`, $`|\theta|\le w`. Triangle inequality.

*D8.3.2* For $`i\in E`: $`-\log p_i'=-\log p_i+\log z\in[S_X+\log z-w,\ S_X+\log z+w]`. $`S'` = $`p'`-average of this, so $`S'-S_X=\log z+\theta'`, $`|\theta'|\le w`. Triangle inequality.

_Used from._ {bpref "D8.2"}[D8.2].

:::

:::definition "D8.4" (lean := "AreaLaw.Comparators.PrefixData") (uses := "D8.1")
*D8.4* — Def: Prefix data (rough upper bound only)

_Source: 07-comparators.tex 56–68, `comparator:prefix-data`._

$`\mathcal R` finite nested family of physical subsystems disjoint from $`X`. For every status and band, each of $`U_g`, $`U_gY_g` has a matched $`B\in\mathcal R` containing it or contained in it. Constants $`B_{\rm sh},B_{\rm exc}` with, for every $`B\in\mathcal R` and every matched pair $`(B,Q)`, $`Q\in\{U_g,U_gY_g\}`: $$`S(B)\le B_{\rm sh},\qquad1+\log\dim\mathcal H_{B\triangle Q}\le B_{\rm exc}.\tag{comparator:prefix-data}` $`B\triangle Q` = difference of the two nested sets. The "$`1`" absorbs a fixed margin in a spectral cutoff ({bpref "D8.18"}[D8.18]).

_Used from._ {bpref "D8.1"}[D8.1].

:::

:::definition "D8.5" (lean := "AreaLaw.Comparators.MgfData") (uses := "D3.1")
*D8.5* — Def: Marginal moment data (sharp bounds only)

_Source: 07-comparators.tex 70–85, `comparator:mgf-data`._

For every $`Q\in\{XU_g,V_g,Y_g,U_g,U_gY_g\}` (all allowed statuses and bands), $`\rho_Q` the marginal of $`\widetilde\Omega`: there are $`C_0,c_0>0`, $`\mathcal B\ge1` with $$`\log\Tr\rho_Q^{1-u}\le uS(Q)+C_0\mathcal Bu^2,\qquad|u|\le c_0/\sqrt{\mathcal B}.\tag{comparator:mgf-data}` Only positive eigenvalues used. $`\mathcal B` carried with its logarithmic factors.

_Used from._ Form matches eq:initial-tail-mgf of Lemma 3.1 ({bpref "D3.1"}[D3.1]) ($`\log\E e^{uK}=\log\Tr\rho^{1-u}`, $`C_0=512e\vartheta`, $`c_0=(32\sqrt{1+\vartheta})^{-1}`); in §8 an assumption.

:::

:::definition "D8.6" (lean := "AreaLaw.Comparators.Site, AreaLaw.Comparators.Statuses.bandA, AreaLaw.Comparators.Statuses.leafA, AreaLaw.Comparators.Statuses.Atil") (uses := "D6.5, D6.8, D6.9, D6.4, D6.6")
*D8.6* — Def: Auxiliary pair, common-dimension metrics, leaf metrics

_Source: 07-comparators.tex 87–112, `comparator:metrics`._

Append $`C,R`, each of dimension $`d_*`, bases indexed by $`E`. $$`\mathrm{Bell}_{CR}=d_*^{-1/2}\sum_{i\in E}|i\rangle_C|i\rangle_R,\quad\mathcal V=\mathcal H_{\rm phys}\otimes\mathcal H_C\otimes\mathcal H_R,\quad\mathcal S_k=\Sym^k\mathcal V.` $`W_{Q,k}` = Schur metrics of §6 with labels padded to $`\dim\mathcal V` (one scalar function of the label for all $`Q`). Fix $`0<a\le a_0` ($`a_0` small absolute), $`t=a/2`, $`s=1/4`, $`W=aK`. At terminal leaf $`j` of any finite binary mean tree, band $`g`: $$`P_{j,g}=CXU_{j,g},\quad F_{j,g}=RV_{j,g},\quad A_{j,g}=(W_{P_{j,g}}^{-1}W_{F_{j,g}}^{-1}W_{Y_{j,g}})^2,\quad A_j=\prod_{g=1}^KA_{j,g}.` $`P_{j,g},Y_{j,g},F_{j,g}` partition $`\mathcal V`. $`C,R` start in $`\mathrm{Bell}_{CR}`, same in every band; only physical factors enter the Hamiltonian.

_Used from._ §6: Lemma 6.1; `replicas:w-definition` ({bpref "D6.5"}[D6.5]) with $`t<1/4`, $`a=2t` (so $`a_0<1/2`); `replicas:leaf-metric` ({bpref "D6.8"}[D6.8]) $`A_k(P,Y,F)=(W_P^{-1}W_F^{-1}W_Y)^2`; `replicas:leaf-floor` ({bpref "D6.9"}[D6.9]): $`\log A_k=a(F_P+F_F-F_Y)+O(\log(k+2))` in operator norm, $`A_k\ge\poly(k)^{-1}\id`; Lemma 6.2: $`\poly(k)^{-1}e^{-tF_{Q}}\le W_{Q}\le\poly(k)e^{-tF_{Q}}`, $`W_Q=W_{Q^c}` on $`\mathcal S_k`.

:::

:::definition "D8.7" (lean := "AreaLaw.Comparators.Statuses.root, AreaLaw.Comparators.Statuses.bandRoot, AreaLaw.Comparators.avg") (uses := "D7.3, D8.1")
*D8.7* — Def: Mean tree on bands and the average $`\langle\cdot\rangle_{\rm av}`

_Source: 07-comparators.tex 114–123._

$`w_j` terminal path probabilities; $`\mathcal M` = root with leaves $`A_j`; $`\mathcal M_g` = root of the same tree with leaves $`A_{j,g}`. $`\mathcal M=\prod_g\mathcal M_g`, commuting factors. For quantities $`f_{j,g}`: $$`\langle f\rangle_{\rm av}=\frac1K\sum_{g=1}^K\sum_jw_jf_{j,g}.` Includes old and new leaves when the tree has an interpolation.

_Used from._ Lemma 7.1 ({bpref "D7.3"}[D7.3]): item 6 (band-$`g` factors commute with band-$`g'` factors, $`g\ne g'`, at all leaves => $`M=\prod M_g`, $`M_g` commute; hypothesis from {bpref "D8.1"}[D8.1](ii)); item 2 monotonicity in each input; item 3 $`\mathcal T(c_jA_j)=\prod c_j^{w_j}M`; item 4 vector Jensen $`\langle z,Mz\rangle\le\prod_j\langle z,A_jz\rangle^{w_j}` (`transport:vector-jensen`); item 5 $`A_j\ge c_jP\Rightarrow M\ge\prod c_j^{w_j}P`.

:::

# 8.1 Statement

:::proposition "D8.8" (lean := "AreaLaw.Comparators.prop_8_1")
*D8.8* — Proposition 8.1: Upper and lower norm comparisons

_Source: 07-comparators.tex 125–214, `prop:comparators`._

Assume {bpref "D8.1"}[D8.1] (incl. nesting), {bpref "D8.2"}[D8.2], {bpref "D8.6"}[D8.6], {bpref "D8.7"}[D8.7]. There are labels $`\lambda_k` and nonzero vectors $$`\mathrm{pre}_k=\pi_R^{\lambda_k}(\widetilde\Omega\otimes\mathrm{Bell}_{CR})^{\otimes k}\in\mathcal S_k,\qquad\|\mathrm{pre}_k\|\le1,\tag{comparator:prevector}` ($`\pi^{\lambda_k}_R` = Schur-label projection on the $`R` copies), physical mean-energy eigenvectors of eigenvalue $`\widetilde E_0` with label $`\lambda_k` on $`C` and on $`R`. For every tree: $`N=\|\mathcal M^{-s}\mathrm{pre}_k\|`, $`v=\mathcal M^{-s}\mathrm{pre}_k/N`, $$`E_{\rm def}=\frac{\langle v,\overline{\widetilde H}v\rangle-\widetilde E_0}{\widetilde g},\qquad\overline{\widetilde H}=\frac1k\sum_{i=1}^k\widetilde H^{(i)}.`

_Rough._ For $`0<\tau<1/2`: $$`-\frac{\log N^2}{k}\le2\log d_*-\log z+2sW\Big(\frac{2B_{\rm sh}}z+2B_{\rm exc}\Big)+o_k(1)\tag{comparator:rough-upper}` (uses {bpref "D8.4"}[D8.4]), and $$`-\frac{\log N^2}k\ge2sW\Big[2S'-C\Big(\tau\log d_*+\frac{h(\tau)}a\Big)-C\frac{E_{\rm def}}\tau S'\Big]-o_k(1)\tag{comparator:rough-lower}` ($`h` binary entropy; needs neither {bpref "D8.4"}[D8.4] nor {bpref "D8.5"}[D8.5]).

_Sharp._ If {bpref "D8.5"}[D8.5] holds and $`a\le c/\sqrt{\mathcal B}` ($`c` small in terms of $`c_0`), put $$`g^{\rm pre}_{j,g}=S(XU_{j,g})+S(V_{j,g})-S(Y_{j,g}),\quad g^{\rm post}_{j,g}=S(U_{j,g})+S(U_{j,g}Y_{j,g})-S(Y_{j,g}),\quad g_{\max}=\max_{j,g}g^{\rm pre}_{j,g}.` Then $`g^{\rm pre}_{j,g}\ge0` and $$`-\frac{\log N^2}k\le2\log d_*-\log z+2sW\Big[\langle g^{\rm post}\rangle_{\rm av}+C\Big(a\mathcal B+\frac{|\log z|}a\Big)\Big]+o_k(1)\tag{comparator:sharp-upper}` (no {bpref "D8.4"}[D8.4] needed), $$`-\frac{\log N^2}k\ge2sW\Big[2S'+(1-\tau)\langle g^{\rm pre}\rangle_{\rm av}-C\Big(\tau\log d_*+\frac{h(\tau)}a+a\mathcal B\Big)-C\frac{E_{\rm def}}\tau(S'+g_{\max})\Big]-o_k(1).\tag{comparator:sharp-lower}` Exact identity for every physical partition: $$`2S_X+g^{\rm pre}_{j,g}-g^{\rm post}_{j,g}=I(X{:}V_{j,g})+I(X{:}Y_{j,g}V_{j,g}).\tag{comparator:entropy-identity}`

_Quantifiers._ Replica limits ($`k\to\infty`): physical system, auxiliary dimensions, status collection, tree, $`a`, $`\tau` fixed. $`o_k(1)` uniform over terminal probabilities (also their $`k`-dependence) and over the symmetric vectors to which the lower comparison is applied. Intermediate polynomial factors in $`k` may depend on the whole fixed system; they vanish in $`o_k(1)`. Displayed constants $`C` universal in the rough bounds; in the sharp bounds may also depend on $`C_0,c_0`. No dependence on system dimensions.

:::

:::proof "D8.8" (uses := "D8.1, D8.2, D8.3, D8.4, D8.5, D8.6, D8.7, D8.9, D8.10, D8.11, D8.12, D8.13, D8.14, D8.15, D8.16, D8.17, D8.18, D8.19, D8.20, D8.21, D8.22, D8.23, D8.24, D8.25, D8.26, D8.27, D8.28, D8.29, D8.30, D8.31, D8.32, D8.33, D8.34, D8.35, D8.36, D8.37")
Order:

*D8.8.1* Labels and pin: {bpref "D8.9"}[D8.9]–{bpref "D8.16"}[D8.16].

*D8.8.2* Upper bounds: {bpref "D8.17"}[D8.17]–{bpref "D8.22"}[D8.22].

*D8.8.3* Defect, component, compression, lower pin: {bpref "D8.23"}[D8.23]–{bpref "D8.31"}[D8.31].

*D8.8.4* Tree and conclusion: {bpref "D8.32"}[D8.32]–{bpref "D8.35"}[D8.35] (lower bounds), {bpref "D8.36"}[D8.36] (identity), {bpref "D8.37"}[D8.37] (uniformity).

_Used from._ {bpref "D8.1"}[D8.1]–{bpref "D8.7"}[D8.7]; internal steps {bpref "D8.9"}[D8.9]–{bpref "D8.37"}[D8.37].

:::

# 8.2 Labels selected by the auxiliary pair

:::lemma_ "D8.9" (lean := "AreaLaw.Comparators.log_dim_le_neg_log") (uses := "D6.4")
*D8.9* — Step: Label remainder

_Source: 07-comparators.tex 218–226, `comparator:label-remainder`._

$`\rho` permutation-invariant density on $`k` copies of a fixed region, $`L=-\log\rho` on its support, $`F=\log` Specht dimension (operator $`F_Q`). Then $$`F\le L,\quad[F,L]=0,\quad\Tr\rho\,e^{b(L-F)}\le\poly(k)\ (0\le b\le1).`

_Used from._ Lemma 6.1(5), `replicas:surprisal-moment`.

:::

:::lemma_ "D8.10" (lean := "AreaLaw.Comparators.step_8_10")
*D8.10* — Step: Signed label moments

_Source: 07-comparators.tex 227–238, `comparator:signed-label-moments`._

For an iid marginal $`\rho_Q^{\otimes k}` satisfying {bpref "D8.5"}[D8.5], $`F_Q` the label operator of $`Q^{\otimes k}`, $`0\le u\le c/\sqrt{\mathcal B}` ($`c` small): $$`\log\E\exp\{\pm u(F_Q-kS(Q))\}\le Ck\mathcal Bu^2+O(\log(k+1)).` Only the $`O(\log(k+1))` term depends on the fixed system.

:::

:::proof "D8.10" (uses := "D8.5, D8.9")
*D8.10.1* $`+` sign. $`F_Q\le L` ({bpref "D8.9"}[D8.9]) $`\Rightarrow` $`\E e^{u(F_Q-kS)}\le\E e^{u(L-kS)}`. $`L` = sum of $`k` iid copies of the one-copy surprisal: $`\log\E e^{uL}=k\log\Tr\rho_Q^{1-u}\le kuS+kC_0\mathcal Bu^2` ({bpref "D8.5"}[D8.5]). Subtract $`ukS`.

*D8.10.2* $`-` sign. $`e^{-u(F_Q-kS)}=e^{-u(L-kS)}\,e^{u(L-F_Q)}` (commuting). Cauchy–Schwarz: $`\E[\cdot]\le(\E e^{-2u(L-kS)})^{1/2}(\E e^{2u(L-F_Q)})^{1/2}`. First factor: {bpref "D8.5"}[D8.5] at $`-2u` (needs $`2u\le c_0/\sqrt{\mathcal B}`) gives $`\le\exp\{\tfrac12k\cdot4C_0\mathcal Bu^2\}`. Second: {bpref "D8.9"}[D8.9] with $`b=2u\le1` gives $`\le\poly(k)^{1/2}`.

*D8.10.3* Shrinking $`c` makes $`u\le c/\sqrt{\mathcal B}`, $`2u\le c_0/\sqrt{\mathcal B}`, $`2u\le1` all hold ($`\mathcal B\ge1`).

_Formal route_ (RefactoringResult.md §5, D8.10.2, {bpref "D8.12"}[D8.12]): expectations `Tr ρ f(ρ, F)` written as sums over the joint resolution `E_u π^λ` and estimated as scalars (Labels.lean). Reason: avoids operator `exp`/`cfc` algebra; same inequalities.

_Used from._ {bpref "D8.5"}[D8.5], {bpref "D8.9"}[D8.9].

:::

:::definition "D8.11" (lean := "AreaLaw.Comparators.step_8_11") (uses := "D8.2")
*D8.11* — Def: Schmidt vectors, $`\psi`, $`B_{XC}`, $`\mathrm{post}_k`, pin projection

_Source: 07-comparators.tex 240–258._

Schmidt vectors $`\widetilde\Omega=\sum_i\sqrt{p_i}|i\rangle_X|w_i\rangle` ($`w_i` orthonormal on $`X^c`). Set $$`\psi=\sum_{i\in E}\sqrt{p_i'}\,|i\rangle_R|w_i\rangle,\quad B_{XC}=\frac1{\sqrt{d_*}}\sum_{i\in E}|i\rangle_X|i\rangle_C,\quad\mathrm{post}_k=B_{XC}^{\otimes k}\otimes\psi^{\otimes k}.` $`\mathsf P` = projection of $`(XC)^{\otimes k}` onto $`B_{XC}^{\otimes k}` (tensored with identity elsewhere). $`\|\psi\|=\|B_{XC}\|=\|\mathrm{post}_k\|=1`.

_Used from._ {bpref "D8.2"}[D8.2].

:::

:::lemma_ "D8.12" (lean := "AreaLaw.Comparators.step_8_12")
*D8.12* — Step: High label $`\lambda_k`

_Source: 07-comparators.tex 260–272, `comparator:high-label`._

One can select $`\lambda_k\vdash k` (at most $`d_*` rows) with $$`q_k:=\|\pi_R^{\lambda_k}\psi^{\otimes k}\|^2\ge\poly(k)^{-1},\qquad\log d_{\lambda_k}=kS'+o(k).`

:::

:::proof "D8.12" (uses := "D6.4, D8.9, D8.11")
*D8.12.1* $`R`-marginal of $`\psi` is $`\mathrm{diag}(p_i')_{i\in E}` ($`w_i` orthonormal). Surprisal $`L` of $`\rho_R^{\otimes k}` = sum of $`k` iid variables, mean $`S'`, fixed finite variance. Chebyshev: $`\Pr\{|L-kS'|>k^{3/4}\}\le\mathrm{const}\cdot k^{-1/2}`.

*D8.12.2* {bpref "D8.9"}[D8.9]: $`L-F_R>k^{3/4}` has probability $`\le\poly(k)e^{-k^{3/4}/2}` (exponential Markov with $`b=1/2`: $`\Pr\le e^{-bk^{3/4}}\,\Tr\rho\,e^{b(L-F)}`).

*D8.12.3* So with probability $`\ge1/2` for large $`k`: $`F_R\in[kS'-2k^{3/4},kS'+k^{3/4}]` ($`F_R\le L`).

*D8.12.4* Label probability is $`\|\pi_R^\lambda\psi^{\otimes k}\|^2`. At most $`(k+1)^{d_*}` labels (Lemma 6.1(1)). Pigeonhole: some label in the window has probability $`\ge\poly(k)^{-1}`; for it $`\log d_\lambda=F_R=kS'+O(k^{3/4})`.

_Formal route_ (RefactoringResult.md §5, {bpref "D8.10"}[D8.10.2], D8.12): expectations `Tr ρ f(ρ, F)` written as sums over the joint resolution `E_u π^λ` and estimated as scalars (Labels.lean). Reason: avoids operator `exp`/`cfc` algebra; same inequalities.

_Used from._ {bpref "D8.9"}[D8.9], {bpref "D8.11"}[D8.11], Lemma 6.1(1).

:::

:::lemma_ "D8.13" (lean := "AreaLaw.Comparators.step_8_13")
*D8.13* — Step: $`\mathrm{pre}_k` is a nonzero symmetric mean-energy eigenvector with preserved labels

_Source: 07-comparators.tex 273–281._

(a) $`\mathrm{pre}_k\ne0`, $`\|\mathrm{pre}_k\|\le1`. (b) $`\overline{\widetilde H}\,\mathrm{pre}_k=\widetilde E_0\mathrm{pre}_k`. (c) $`\mathrm{pre}_k` has label $`\lambda_k` on $`C` and on $`R`. (d) Each $`W_{Q}` of {bpref "D8.6"}[D8.6] preserves these labels and $`\mathcal S_k`; hence so does every $`A_{j,g}`, $`A_j`, $`\mathcal M^{r}`.

:::

:::proof "D8.13" (uses := "D6.4, D8.12")
*D8.13.1* (a) $`R`-marginal of $`\mathrm{Bell}^{\otimes k}` is maximally mixed on $`R^{\otimes k}`, so $`\Pr(\lambda)=d_\lambda\dim V_\lambda/d_*^k>0` for every label with at most $`d_*` rows, $`\lambda_k` included; so $`\pi_R^{\lambda_k}(\widetilde\Omega\otimes\mathrm{Bell})^{\otimes k}\ne0`. (Equivalently, {bpref "D8.14"}[D8.14]: $`\|\mathsf P\mathrm{pre}_k\|^2=(z/d_*^2)^kq_k>0`.) $`\|\mathrm{pre}_k\|\le1`: projection of a unit vector.

*D8.13.2* (b) $`\pi_R^{\lambda_k}` acts on $`R` only, so commutes with every $`\widetilde H^{(i)}`; $`\widetilde H^{(i)}\widetilde\Omega^{(i)}=\widetilde E_0\widetilde\Omega^{(i)}`.

*D8.13.3* (c) $`\mathrm{Bell}_{CR}^{\otimes k}` is a pure vector in $`\Sym^k(C\otimes R)`: complementary labels agree (Lemma 6.1(2)), so its $`C` label equals its $`R` label. $`\pi_R^{\lambda_k}` commutes with the $`C` label, hence $`\mathrm{pre}_k` has label $`\lambda_k` on both.

*D8.13.4* (d) A central permutation function on an auxiliary system commutes with the simultaneous permutations on any larger region containing it, and with operators on disjoint regions. $`C\subset P_{j,g}`, $`R\subset F_{j,g}`, $`Y_{j,g}` disjoint. Tree: if a projection $`\pi` commutes with all leaves, $`V=\id-2\pi` is unitary with $`VA_jV^*=A_j`; congruence (Lemma 7.1(1)) gives $`V\mathcal MV^*=\mathcal M`, so $`\mathcal M` commutes with $`\pi`, hence with $`\mathcal M^{r}`.

_Formal route_ (RefactoringResult.md §5, D8.13 (d), {bpref "D8.15"}[D8.15.2]): induction on the tree through `geomMean` (products and real powers): a matrix commuting with every leaf commutes with the root (`commute_eval_of_commute`, Labels.lean, Pin.lean). Reason: Lemma 7.1 (1) needs positive definite leaves, i.e. band commutation, which D8.13 does not assume; the formal route needs no positivity.

_Used from._ {bpref "D8.12"}[D8.12]; Lemma 6.1(2) (complementary labels agree on $`\mathcal S_k`; central label functions commute for nested/disjoint regions).

:::

:::lemma_ "D8.14" (lean := "AreaLaw.Comparators.step_8_14")
*D8.14* — Step: Bell pin

_Source: 07-comparators.tex 283–290, `comparator:bell-pin`._

$$`\mathsf P\,\mathrm{pre}_k=\Big(\frac{\sqrt z}{d_*}\Big)^k\pi_R^{\lambda_k}\mathrm{post}_k.`

:::

:::proof "D8.14" (uses := "D8.11, D8.2")
*D8.14.1* One copy: $`\langle B_{XC}|_{XC}(\widetilde\Omega\otimes\mathrm{Bell}_{CR})=d_*^{-1}\sum_{m,l\in E}\sum_i\sqrt{p_i}\langle m|i\rangle\langle m|l\rangle|l\rangle_R|w_i\rangle`, collapsing to $`m=i=l\in E`: $`=d_*^{-1}\sum_{i\in E}\sqrt{p_i}|i\rangle_R|w_i\rangle=(\sqrt z/d_*)\psi`. So $`\mathsf P_1(\widetilde\Omega\otimes\mathrm{Bell})=(\sqrt z/d_*)B_{XC}\otimes\psi`.

*D8.14.2* $`k` copies: tensor power. $`\pi_R^{\lambda_k}` acts on $`R`, disjoint from $`XC`, so commutes with $`\mathsf P`.

_Used from._ {bpref "D8.11"}[D8.11], {bpref "D8.2"}[D8.2].

:::

:::lemma_ "D8.15" (lean := "AreaLaw.Comparators.step_8_15")
*D8.15* — Step: Pin norm

_Source: 07-comparators.tex 291–300, `comparator:pin-norm`._

$$`N^2\ge\Big(\frac z{d_*^2}\Big)^k\|\mathcal M^{-s}\pi_R^{\lambda_k}\mathrm{post}_k\|^2.`

:::

:::proof "D8.15" (uses := "D8.14, D8.6")
*D8.15.1* $`\mathsf P` commutes with every $`A_{j,g}`: $`W_{P_{j,g}}` is a central function of simultaneous permutations on $`P_{j,g}\supseteq XC`, and $`B_{XC}^{\otimes k}` is invariant under simultaneous permutations on $`XC`, so $`\mathsf P` commutes with each $`U_{P_{j,g}}(\pi)`; $`W_{F_{j,g}},W_{Y_{j,g}}` act on regions disjoint from $`XC`.

*D8.15.2* Hence $`\mathsf P` commutes with each $`A_j`. Tree: $`V=\id-2\mathsf P` unitary commuting with all leaves; congruence (Lemma 7.1(1)) gives $`V\mathcal MV^*=\mathcal M`. So $`\mathsf P` commutes with $`\mathcal M` and $`\mathcal M^{-s}`.

*D8.15.3* $`N=\|\mathcal M^{-s}\mathrm{pre}_k\|\ge\|\mathsf P\mathcal M^{-s}\mathrm{pre}_k\|=\|\mathcal M^{-s}\mathsf P\mathrm{pre}_k\|`. Insert {bpref "D8.14"}[D8.14], square.

_Formal route_ (RefactoringResult.md §5, {bpref "D8.13"}[D8.13] (d), D8.15.2): induction on the tree through `geomMean` (products and real powers): a matrix commuting with every leaf commutes with the root (`commute_eval_of_commute`, Labels.lean, Pin.lean). Reason: Lemma 7.1 (1) needs positive definite leaves, i.e. band commutation, which {bpref "D8.13"}[D8.13] does not assume; the formal route needs no positivity.

_Used from._ {bpref "D8.14"}[D8.14]; {bpref "D8.6"}[D8.6] ($`XC\subseteq P_{j,g}` for all $`j,g`).

:::

:::lemma_ "D8.16" (lean := "AreaLaw.Comparators.step_8_16")
*D8.16* — Step: Pinned metric

_Source: 07-comparators.tex 302–318, `comparator:pinned-metric`._

On the pinned symmetric range ($`B_{XC}^{\otimes k}\otimes` symmetric vector on the rest), $`P_{j,g}`-label = $`U_{j,g}`-label, $`F_{j,g}`-label = $`U_{j,g}Y_{j,g}`-label, and $`A_{j,g}` restricts exactly to $$`\widetilde A_{j,g}=(W_{U_{j,g}}^{-1}W_{U_{j,g}Y_{j,g}}^{-1}W_{Y_{j,g}})^2,\qquad\log\widetilde A_{j,g}=a(F_{U_{j,g}}+F_{U_{j,g}Y_{j,g}}-F_{Y_{j,g}})+O(\log(k+1))\id.` Error is an operator-norm bound, not asserted scalar. Restricted tree: $`\widetilde{\mathcal M}`, factors $`\widetilde{\mathcal M}_g`.

:::

:::proof "D8.16" (uses := "D6.7, D6.4, D8.6")
*D8.16.1* $`W_{CXU}\to W_U` by the fixed-factor identity with fixed vector $`B_{XC}^{\otimes k}` on $`XC` (internal entanglement irrelevant to simultaneous permutations of the whole factor).

*D8.16.2* $`F_{j,g}=RV_{j,g}` has complement $`CXU_{j,g}Y_{j,g}` in $`\mathcal V`. On $`\mathcal S_k`, $`W_{RV}=W_{CXUY}\to W_{UY}` by the same identity. $`W_Y` unaffected.

*D8.16.3* Restricted system $`UYVR` is partitioned by $`(U,Y,RV)` with the same label function; `replicas:leaf-floor` gives the logarithm formula, $`F_{RV}=F_{UY}` on symmetric vectors.

*D8.16.4* $`\mathsf P` commutes with $`A_{j,g}` ({bpref "D8.15"}[D8.15.1]), so the means commute with restriction to its range.

_Formal route_ (RefactoringResult.md §5, D8.16): `Ã` on the same tensor space; `bandA φ = Ã φ` for `φ ∈ 𝒮_k ∩ ran 𝖯` (Pin.lean:776); no restricted tree: {bpref "D8.20"}[D8.20]/{bpref "D8.21"}[D8.21] apply vector Jensen to the full root on pinned vectors. Reason: one encoding (the old code built a second, exterior site family).

_Used from._ {bpref "D8.6"}[D8.6] (`replicas:leaf-floor`), `replicas:fixed-factor` ({bpref "D6.7"}[D6.7]): $`W_{BQ,k}(\phi^{\otimes k}\otimes z)=\phi^{\otimes k}\otimes W_{Q,k}z` (same for $`F`, real powers of $`W`); Lemma 6.1(2).

:::

# 8.3 Upper comparisons

:::lemma_ "D8.17" (lean := "AreaLaw.Comparators.step_8_17")
*D8.17* — Step: Post marginals

_Source: 07-comparators.tex 322–332, `comparator:post-marginal`._

For physical $`B` disjoint from $`X`: $$`\rho_B=z\rho_{\psi,B}+(1-z)\rho_{{\rm rem},B},\qquad\rho_{\psi,B}\le z^{-1}\rho_B,\qquad S(\rho_{\psi,B})\le S(B)/z.` Remainder omitted if $`z=1`.

:::

:::proof "D8.17" (uses := "D8.2, D8.11")
*D8.17.1* Tracing out $`X` kills cross terms between orthonormal $`|i\rangle_X`: $`\rho_B=\sum_ip_i\omega_{i,B}`, $`\omega_{i,B}=\Tr_{\rm rest}|w_i\rangle\langle w_i|`. $`\rho_{\psi,B}=\sum_{i\in E}p_i'\omega_{i,B}`. So $`\rho_B=z\rho_{\psi,B}+(1-z)\rho_{\rm rem,B}`, $`\rho_{\rm rem,B}=\sum_{i\notin E}p_i\omega_{i,B}/(1-z)`.

*D8.17.2* $`(1-z)\rho_{\rm rem}\ge0\Rightarrow\rho_{\psi,B}\le z^{-1}\rho_B`.

*D8.17.3* Concavity: $`S(B)\ge zS(\rho_{\psi,B})+(1-z)S(\rho_{\rm rem,B})\ge zS(\rho_{\psi,B})`.

_Used from._ {bpref "D8.2"}[D8.2], {bpref "D8.11"}[D8.11].

:::

:::lemma_ "D8.18" (lean := "AreaLaw.Comparators.step_8_18")
*D8.18* — Step: Rough overlap

_Source: 07-comparators.tex 334–353, `comparator:rough-overlap`._

There is a unit vector $`\varphi` in the common range of the projections $`\{F_B\le k(S(B)/z+1)\}_{B\in\mathcal R}` with $$`|\langle\varphi,\pi_R^{\lambda_k}\mathrm{post}_k\rangle|^2\ge\poly(k)^{-1}.`

:::

:::proof "D8.18" (uses := "D6.4, D8.4, D8.9, D8.12, D8.17")
*D8.18.1* Cutoff projections commute (nested family, Lemma 6.1(2)) and commute with $`\pi_R^{\lambda_k}` (disjoint regions).

*D8.18.2* Under $`\mathrm{post}_k` the $`B`-marginal is $`\rho_{\psi,B}^{\otimes k}`. $`F_B\le L_B` ({bpref "D8.9"}[D8.9]), $`L_B` = sum of iid one-copy surprisals, each bounded on the positive spectrum at fixed system. Exponential Markov with $`\E e^{\theta L_B}\le\exp\{k\theta S(\rho_{\psi,B})+O(k\theta^2)\}` and $`S(\rho_{\psi,B})\le S(B)/z` ({bpref "D8.17"}[D8.17]): $`\Pr\{F_B>k(S(B)/z+1)\}\le e^{-ck}` for small $`\theta`.

*D8.18.3* Finite union over $`\mathcal R`: still exponentially small. Common projection $`\Pi_{\rm cut}`: $`\|\Pi_{\rm cut}\pi_R^{\lambda_k}\mathrm{post}_k\|^2\ge q_k-e^{-ck}\ge\poly(k)^{-1}` ({bpref "D8.12"}[D8.12]).

*D8.18.4* $`\varphi` = normalization. $`\langle\varphi,\pi\,\mathrm{post}\rangle=\|\Pi_{\rm cut}\pi\,\mathrm{post}\|`.

_Formal route_ (RefactoringResult.md §5, D8.18): {bpref "D8.10"}[D8.10] at a fixed small `u` with fixed-system moment data `C₀ = c₀ = 1`, then exponential Markov (RoughUpper.lean:899). Reason: the same estimate, already proved as {bpref "D8.10"}[D8.10].

_Used from._ {bpref "D8.4"}[D8.4], {bpref "D8.9"}[D8.9], {bpref "D8.12"}[D8.12], {bpref "D8.17"}[D8.17]; Lemma 6.1(2).

:::

:::lemma_ "D8.19" (lean := "AreaLaw.Comparators.step_8_19")
*D8.19* — Step: Actual cutoffs

_Source: 07-comparators.tex 355–365, `comparator:actual-cutoffs`._

For matched $`(B,Q)`: $`F_Q\le F_B+k\log\dim\mathcal H_{B\triangle Q}` (either inclusion direction), the two labels commute, and $`\varphi` lies in the range $$`F_Q\le k(B_{\rm sh}/z+B_{\rm exc}),\qquad Q=U_{j,g},\ U_{j,g}Y_{j,g}.`

:::

:::proof "D8.19" (uses := "D6.4, D8.4, D8.18")
*D8.19.1* $`Q\subseteq B`: $`B=Q\sqcup(B\setminus Q)`; Lemma 6.1(3) second inequality $`d_\lambda\le d_\nu d_\mu` gives $`F_Q\le F_B+F_{B\setminus Q}`. $`B\subseteq Q`: first inequality $`d_\nu\le d_\lambda d_\mu` gives $`F_Q\le F_B+F_{Q\setminus B}`. A Specht dimension for a system of dimension $`D` is at most $`D^k` (multiplicity space inside $`(\mathbb C^D)^{\otimes k}`), so the extra term is $`\le k\log\dim\mathcal H_{B\triangle Q}`.

*D8.19.2* $`F_B,F_Q` commute (nested). In each joint eigenspace with $`F_B\le k(S(B)/z+1)`: $`F_Q\le k(S(B)/z+1+\log\dim\mathcal H_{B\triangle Q})\le k(B_{\rm sh}/z+B_{\rm exc})` by {bpref "D8.4"}[D8.4]. $`\varphi` is supported on such eigenspaces.

_Used from._ {bpref "D8.4"}[D8.4], {bpref "D8.18"}[D8.18], Lemma 6.1(2)(3).

:::

:::lemma_ "D8.20" (lean := "AreaLaw.Comparators.step_8_20")
*D8.20* — Step: Proof of the rough upper bound

_Source: 07-comparators.tex 366–381, `comparator:rough-upper`._

(comparator:rough-upper) of {bpref "D8.8"}[D8.8].

:::

:::proof "D8.20" (uses := "D7.3, D8.15, D8.16, D8.18, D8.19, D8.1")
*D8.20.1* Within a product leaf all labels in $`\widetilde A_{j,g}` commute ({bpref "D8.1"}[D8.1](iii)). $`F_{Y}\ge0`, so dropping $`-aF_Y`: $`\prod_g\widetilde A_{j,g}\le\poly(k)\exp\{a\sum_g(F_{U_{j,g}}+F_{U_{j,g}Y_{j,g}})\}` ($`K` fixed). On $`\varphi`, {bpref "D8.19"}[D8.19]: $$`\langle\varphi,\textstyle\prod_g\widetilde A_{j,g}\varphi\rangle\le\poly(k)\exp\{2kaK(B_{\rm sh}/z+B_{\rm exc})\}.`

*D8.20.2* Vector Jensen through the tree: $`\langle\varphi,\widetilde{\mathcal M}\varphi\rangle\le\prod_j\langle\varphi,\prod_g\widetilde A_{j,g}\varphi\rangle^{w_j}`, same bound ($`\sum_jw_j=1`).

*D8.20.3* $`2s=1/2\le1`: scalar Jensen (concavity of $`x^{2s}`) on the spectral measure of $`\widetilde{\mathcal M}` in $`\varphi`: $`\langle\varphi,\widetilde{\mathcal M}^{2s}\varphi\rangle\le\langle\varphi,\widetilde{\mathcal M}\varphi\rangle^{2s}\le\poly(k)\exp\{2s\cdot2kW(B_{\rm sh}/z+B_{\rm exc})\}`.

*D8.20.4* Cauchy–Schwarz: $`|\langle\varphi,x\rangle|^2=|\langle\widetilde{\mathcal M}^s\varphi,\widetilde{\mathcal M}^{-s}x\rangle|^2\le\langle\varphi,\widetilde{\mathcal M}^{2s}\varphi\rangle\|\widetilde{\mathcal M}^{-s}x\|^2`, $`x=\pi_R^{\lambda_k}\mathrm{post}_k`. With {bpref "D8.18"}[D8.18]: $`\|\widetilde{\mathcal M}^{-s}x\|^2\ge\poly(k)^{-1}\exp\{-2sW\cdot2k(B_{\rm sh}/z+B_{\rm exc})\}`.

*D8.20.5* Insert in {bpref "D8.15"}[D8.15], take $`-\log`, divide by $`k`: $`-\log N^2/k\le2\log d_*-\log z+2sW(2B_{\rm sh}/z+2B_{\rm exc})+O(\log k/k)`.

_Formal route_ (RefactoringResult.md §5, D8.20, {bpref "D8.22"}[D8.22]): label-by-label from Lemma 6.2 (2) (`lemma_6_2_2`) on the explicit `Ã` (RoughUpper.lean, SharpUpper.lean). Reason: direct.

_Used from._ {bpref "D8.15"}[D8.15], {bpref "D8.16"}[D8.16], {bpref "D8.18"}[D8.18], {bpref "D8.19"}[D8.19], {bpref "D8.1"}[D8.1](iii); Lemma 7.1(4) (`transport:vector-jensen`).

:::

:::lemma_ "D8.21" (lean := "AreaLaw.Comparators.step_8_21")
*D8.21* — Step: Sharp Jensen bound on band logarithms

_Source: 07-comparators.tex 383–404, `comparator:sharp-jensen`._

$`\widehat\psi_k=\pi_R^{\lambda_k}\mathrm{post}_k/\sqrt{q_k}`. Then $$`\|\widetilde{\mathcal M}^{-s}\pi_R^{\lambda_k}\mathrm{post}_k\|^2\ge q_k\exp\{-2s\langle\widehat\psi_k,\log\widetilde{\mathcal M}\widehat\psi_k\rangle\},` and for each band $$`\langle\widehat\psi_k,\log\widetilde{\mathcal M}_g\widehat\psi_k\rangle\le\log\langle\widehat\psi_k,\widetilde{\mathcal M}_g\widehat\psi_k\rangle\le O(\log(k+1))+\sum_jw_j\log\langle\mathrm{post}_k,\widetilde A_{j,g}\mathrm{post}_k\rangle.`

:::

:::proof "D8.21" (uses := "D7.3, D8.7, D8.12, D8.13, D8.16")
*D8.21.1* $`\|\pi\,\mathrm{post}_k\|^2=q_k` ($`\|B^{\otimes k}\|=1`). $`\|\widetilde{\mathcal M}^{-s}\pi\,\mathrm{post}\|^2=q_k\langle\widehat\psi,e^{-2s\log\widetilde{\mathcal M}}\widehat\psi\rangle\ge q_k\exp\{-2s\langle\widehat\psi,\log\widetilde{\mathcal M}\widehat\psi\rangle\}`: convexity of $`\exp`.

*D8.21.2* $`\log\widetilde{\mathcal M}=\sum_g\log\widetilde{\mathcal M}_g` (commuting factors).

*D8.21.3* First $`\le`: concavity of $`\log` (spectral measure of $`\widetilde{\mathcal M}_g` in $`\widehat\psi`).

*D8.21.4* Second $`\le`: vector Jensen (`transport:vector-jensen`): $`\log\langle\widehat\psi,\widetilde{\mathcal M}_g\widehat\psi\rangle\le\sum_jw_j\log\langle\widehat\psi,\widetilde A_{j,g}\widehat\psi\rangle`. $`\widetilde A_{j,g}` commutes with $`\pi_R^{\lambda_k}` ({bpref "D8.13"}[D8.13](d)), so $`\langle\pi\,\mathrm{post},\widetilde A\,\pi\,\mathrm{post}\rangle=\langle\mathrm{post},\widetilde A^{1/2}\pi\widetilde A^{1/2}\mathrm{post}\rangle\le\langle\mathrm{post},\widetilde A\,\mathrm{post}\rangle` ($`\pi\le\id`), so $`\langle\widehat\psi,\widetilde A\widehat\psi\rangle\le q_k^{-1}\langle\mathrm{post},\widetilde A\,\mathrm{post}\rangle`. Conditioning cost $`-\log q_k=O(\log(k+1))` ({bpref "D8.12"}[D8.12]), constant in $`j` since $`\sum_jw_j=1`.

_Used from._ {bpref "D8.7"}[D8.7], {bpref "D8.12"}[D8.12], {bpref "D8.13"}[D8.13](d), {bpref "D8.16"}[D8.16]; Lemma 7.1(4).

:::

:::lemma_ "D8.22" (lean := "AreaLaw.Comparators.step_8_22")
*D8.22* — Step: Leaf expectation and proof of the sharp upper bound

_Source: 07-comparators.tex 405–418, `comparator:sharp-upper`._

$$`\log\langle\mathrm{post}_k,\widetilde A_{j,g}\mathrm{post}_k\rangle\le kag^{\rm post}_{j,g}+Cka^2\mathcal B+k|\log z|+O(\log(k+1)),` hence (comparator:sharp-upper).

:::

:::proof "D8.22" (uses := "D8.5, D8.10, D8.15, D8.16, D8.17, D8.21")
*D8.22.1* {bpref "D8.16"}[D8.16]: $`\widetilde A\le\poly(k)\,e^{aF_U}e^{aF_{UY}}e^{-aF_Y}` (commuting labels). Hölder with exponents $`3,3,3` for commuting positive factors: $`\langle\mathrm{post},\widetilde A\,\mathrm{post}\rangle\le\poly(k)\prod_{Q\in\{U,UY\}}\langle e^{3aF_Q}\rangle^{1/3}\cdot\langle e^{-3aF_Y}\rangle^{1/3}`.

*D8.22.2* Each $`Q\in\{U,UY,Y\}` is physical and disjoint from $`X`. $`Q`-marginal of $`\mathrm{post}_k` is $`\rho_{\psi,Q}^{\otimes k}\le z^{-k}\rho_Q^{\otimes k}` ({bpref "D8.17"}[D8.17]); $`e^{\pm3aF_Q}\ge0`, so $`\langle e^{\pm3aF_Q}\rangle_{\rm post}\le z^{-k}\Tr\rho_Q^{\otimes k}e^{\pm3aF_Q}`.

*D8.22.3* {bpref "D8.10"}[D8.10] at $`u=3a`: $`\Tr\rho_Q^{\otimes k}e^{\pm3aF_Q}\le\exp\{\pm3akS(Q)+9Cka^2\mathcal B+O(\log(k+1))\}`.

*D8.22.4* Take $`\tfrac13\log` of each and add: $`ak[S(U)+S(UY)-S(Y)]+Cka^2\mathcal B+k|\log z|` ($`z^{-k}` thrice at power $`\tfrac13`; $`|\log z|=-\log z`).

*D8.22.5* Assemble. {bpref "D8.15"}[D8.15]: $`-\log N^2\le k(2\log d_*-\log z)-\log\|\widetilde{\mathcal M}^{-s}\pi\,\mathrm{post}\|^2`. {bpref "D8.21"}[D8.21]: $`-\log\|\cdot\|^2\le-\log q_k+2s\sum_g\{O(\log(k+1))+\sum_jw_j\log\langle\mathrm{post},\widetilde A_{j,g}\mathrm{post}\rangle\}`. D8.22.4: $`\sum_g\sum_jw_j[\,\cdot\,]=aKk\langle g^{\rm post}\rangle_{\rm av}+KCka^2\mathcal B+Kk|\log z|+O(\log(k+1))`. With $`W=aK`: $`Kka^2\mathcal B=kWa\mathcal B`, $`Kk|\log z|=kW|\log z|/a`. Divide by $`k`.

_Formal route_ (RefactoringResult.md §5, {bpref "D8.20"}[D8.20], D8.22): label-by-label from Lemma 6.2 (2) (`lemma_6_2_2`) on the explicit `Ã` (RoughUpper.lean, SharpUpper.lean). Reason: direct.

_Used from._ {bpref "D8.5"}[D8.5], {bpref "D8.10"}[D8.10], {bpref "D8.15"}[D8.15], {bpref "D8.16"}[D8.16], {bpref "D8.17"}[D8.17], {bpref "D8.21"}[D8.21]. Requires $`3a\le c/\sqrt{\mathcal B}` (shrink $`c`).

:::

# 8.4 The inverse metric on copies near the ground state

:::lemma_ "D8.23" (lean := "AreaLaw.Comparators.step_8_23")
*D8.23* — Step: Defect mass

_Source: 07-comparators.tex 422–439, `comparator:defect-mass`._

$`Q_i=\id-|\widetilde\Omega\rangle\langle\widetilde\Omega|` on physical copy $`i`. On $`\mathcal S_k` with the two fixed auxiliary labels, $`\Pi` = projection onto $`\sum_iQ_i\le\tau k`. $$`\overline{\widetilde H}-\widetilde E_0\id\ge\frac{\widetilde g}k\sum_iQ_i,\qquad\langle v,\Pi v\rangle\ge1-E_{\rm def}/\tau.` $`\Pi` commutes with symmetry and the auxiliary sectors.

:::

:::proof "D8.23" (uses := "D8.1, D8.13")
*D8.23.1* Unique ground vector and gap: $`\widetilde H-\widetilde E_0\ge\widetilde gQ` per copy. Average over $`i`.

*D8.23.2* $`\sum_iQ_i` = integer count of excited copies. On $`\mathrm{ran}(\id-\Pi)` it exceeds $`\tau k`: $`\langle v,\sum Q_iv\rangle\ge\tau k\langle v,(\id-\Pi)v\rangle`. Also $`\langle v,\sum Q_iv\rangle\le k\langle v,(\overline{\widetilde H}-\widetilde E_0)v\rangle/\widetilde g=kE_{\rm def}`. So $`\langle v,(\id-\Pi)v\rangle\le E_{\rm def}/\tau`.

*D8.23.3* Count acts on physical copies only, invariant under simultaneous copy permutations.

_Used from._ {bpref "D8.1"}[D8.1], {bpref "D8.13"}[D8.13].

:::

:::lemma_ "D8.24" (lean := "AreaLaw.Comparators.step_8_24")
*D8.24* — Step: Defect components

_Source: 07-comparators.tex 441–453._

For unit $`u\in\mathrm{ran}\,\Pi` and $`B\subseteq\{1..k\}`, $`u_B` = component with exactly the copies in $`B` excited. $`u=\sum_{|B|\le\tau k}u_B`, $`\sum_B\|u_B\|^2=1`. For $`r=|B|`, $`k'=k-r`: $`u_B` is invariant under simultaneous permutations separately on the $`k'` good and $`r` bad copies; factors as $`\widetilde\Omega^{\otimes k'}` on the good physical factors tensored with a vector on the rest; has the two whole-copy auxiliary labels $`\lambda_k`. Terms with $`u_B=0` omitted in normalized estimates.

:::

:::proof "D8.24" (uses := "D8.13, D8.23")
*D8.24.1* $`\Pi_B=\prod_{i\in B}Q_i\prod_{i\notin B}(\id-Q_i)`: orthogonal projections summing to $`\id`; $`\sum Q_i=|B|` on $`\mathrm{ran}\,\Pi_B`.

*D8.24.2* $`u` symmetric $`\Rightarrow` $`u_B` invariant under $`S_{k'}\times S_r` on $`B^c,B` (permutations preserving $`B` commute with $`\Pi_B`). Good copies in the ground vector give the tensor factor. Auxiliary label projectors commute with the physical $`\Pi_B`.

_Used from._ {bpref "D8.13"}[D8.13], {bpref "D8.23"}[D8.23].

:::

:::lemma_ "D8.25" (lean := "AreaLaw.Comparators.step_8_25")
*D8.25* — Step: Restriction dimensions

_Source: 07-comparators.tex 455–467, `comparator:restriction-dimensions`._

For any region $`Q`, whole label and two subgroup labels commute. On a compatible triple, $$`F_Q^{\rm good}+F_Q^{\rm bad}\le F_Q^{\rm whole}\le F_Q^{\rm good}+F_Q^{\rm bad}+\log\binom kr.`

:::

:::proof "D8.25" (uses := "D6.4")
*D8.25.1* $`[\alpha]\otimes[\beta]` embeds in $`\mathrm{Res}^{S_k}_{S_{k'}\times S_r}[\lambda]` as a subspace $`U`: $`d_\alpha d_\beta=\dim U\le d_\lambda`. Take $`\log`.

*D8.25.2* Translates $`gU`, $`g\in S_k`, span $`[\lambda]` (irreducible). $`gU` depends only on the coset $`g(S_{k'}\times S_r)`; $`\binom kr` cosets. So $`d_\lambda\le\binom kr\dim U=\binom kr d_\alpha d_\beta`. Take $`\log`.

*D8.25.3* Commutation: central elements of $`S_k` commute with the subgroup algebra.

_Used from._ Lemma 6.1(4), `replicas:group-dimensions`: $`d_\alpha d_\beta\le d_\lambda\le\binom kr d_\alpha d_\beta`.

:::

:::lemma_ "D8.26" (lean := "AreaLaw.Comparators.step_8_26")
*D8.26* — Step: Whole inverse metric

_Source: 07-comparators.tex 468–479, `comparator:whole-inverse`._

With $`G=F_P+F_F-F_Y` for the partition $`P,Y,F` (all its labels commute): $$`A_{j,g}^{-1}\le\poly(k)\binom kr^{Ca}\exp\{-aG^{\rm good}-aG^{\rm bad}\}.`

:::

:::proof "D8.26" (uses := "D8.6, D8.25")
*D8.26.1* $`A^{-1}=(W_PW_FW_Y^{-1})^2\le\poly(k)e^{-a(F_P+F_F-F_Y)}=\poly(k)e^{-aG^{\rm whole}}` (Lemma 6.2 both directions, $`2t=a`).

*D8.26.2* {bpref "D8.25"}[D8.25] on $`P,F` (lower bound on $`F^{\rm whole}`) and on $`Y` (upper bound): $`G^{\rm whole}\ge G^{\rm good}+G^{\rm bad}-\log\binom kr`. Exponentiate with $`-a`.

_Used from._ {bpref "D8.6"}[D8.6] (`replicas:leaf-floor`, Lemma 6.2), {bpref "D8.25"}[D8.25].

:::

:::lemma_ "D8.27" (lean := "AreaLaw.Comparators.step_8_27")
*D8.27* — Step: Good auxiliary labels

_Source: 07-comparators.tex 481–493, `comparator:good-auxiliary`._

On $`u_B`: $$`F_C^{\rm good},\ F_R^{\rm good}\ge kS'-r\log d_*-\log\binom kr-o(k).` Also $`G^{\rm bad}\ge0` on the measured support.

:::

:::proof "D8.27" (uses := "D6.4, D8.12, D8.13, D8.24, D8.25")
*D8.27.1* $`F^{\rm whole}_C=F^{\rm whole}_R=\log d_{\lambda_k}=kS'+o(k)` on $`u_B` ({bpref "D8.12"}[D8.12]).

*D8.27.2* {bpref "D8.25"}[D8.25] upper: $`F^{\rm good}\ge F^{\rm whole}-F^{\rm bad}-\log\binom kr`. Bad-group Specht dimension on a $`d_*`-dimensional system with $`r` copies $`\le d_*^r`, so $`F^{\rm bad}\le r\log d_*`.

*D8.27.3* $`G^{\rm bad}=F_P^{\rm bad}+F_F^{\rm bad}-F_Y^{\rm bad}\ge0` on the symmetric bad vector: $`F_Y=F_{PF}\le F_P+F_F` on simultaneous symmetry (Lemma 6.1(2)(3)). Dropped in the expectation of {bpref "D8.26"}[D8.26]; good-group operators act on disjoint copies and preserve this support.

_Used from._ {bpref "D8.12"}[D8.12], {bpref "D8.13"}[D8.13], {bpref "D8.24"}[D8.24], {bpref "D8.25"}[D8.25]; Lemma 6.1(2)(3).

:::

:::lemma_ "D8.28" (lean := "AreaLaw.Comparators.step_8_28")
*D8.28* — Step: Merge deficits and decomposition

_Source: 07-comparators.tex 495–522, `comparator:merge-decomposition`._

On the good group put $`Q=XU_{j,g}`, $`V=V_{j,g}`, $`Y=Y_{j,g}` and $$`D_C=F_Q+F_C-F_{QC},\quad D_R=F_V+F_R-F_{VR},\quad G_{\rm phys}=F_Q+F_V-F_Y.` All commute with $`F_C,F_R` and each other; $`D_C,D_R\ge0`; and $$`G^{\rm good}=G_{\rm phys}+F_C+F_R-D_C-D_R.` Physical good copies lie in $`\mathsf J=\mathbf 1_{[0,\infty)}(G_{\rm phys})`; $`\mathsf J` commutes with $`D_C,D_R`.

:::

:::proof "D8.28" (uses := "D6.4, D8.24")
*D8.28.1* $`G^{\rm good}=F_{QC}+F_{VR}-F_Y` for the partition $`(P,Y,F)=(QC,Y,VR)`. Substitute $`F_{QC}=F_Q+F_C-D_C`, $`F_{VR}=F_V+F_R-D_R`.

*D8.28.2* $`D_C,D_R\ge0`: $`d_\nu\le d_\lambda d_\mu` (Lemma 6.1(3)).

*D8.28.3* Physical good copies are in $`\widetilde\Omega^{\otimes k'}`; $`Q,V,Y` partition the physical system: $`F_Y=F_{QV}\le F_Q+F_V`, so $`G_{\rm phys}\ge0` there.

*D8.28.4* $`\mathsf J` commutes with $`D_C,D_R`: each physical central label ($`Q,V,Y`) is nested in or disjoint from the merged regions $`QC,VR`.

_Used from._ {bpref "D8.24"}[D8.24]; Lemma 6.1(2)(3).

:::

:::lemma_ "D8.29" (lean := "AreaLaw.Comparators.step_8_29")
*D8.29* — Step: Merge moments

_Source: 07-comparators.tex 524–551, `comparator:merge-moments`._

For $`0\le b\le1`, $$`\E_{u_B/\|u_B\|}e^{bD_C}\le\poly(k),\qquad\E_{u_B/\|u_B\|}e^{bD_R}\le\poly(k).` No iid hypothesis on the auxiliary marginal.

:::

:::proof "D8.29" (uses := "D6.4, D8.24, D8.28")
*D8.29.1* In normalized $`u_B` the $`QC`-marginal on good copies is $`\rho_Q^{\otimes k'}\otimes\rho_C`, $`\rho_C` permutation-invariant (trace out other factors of the good-group symmetric component). Conditional on labels $`\gamma` (on $`Q`), $`\beta` (on $`C`) the two Specht factors are independent and maximally mixed ($`I/d_\gamma`, $`I/d_\beta`).

*D8.29.2* Combined label $`\nu` has conditional probability $`m^\nu_{\gamma\beta}\,d_\nu/(d_\gamma d_\beta)`, $`m^\nu_{\gamma\beta}` = multiplicity of $`[\nu]` in $`[\gamma]\otimes[\beta]`.

*D8.29.3* $`m^\nu_{\gamma\beta}\le\poly(k)`: embed one copy of $`[\gamma]\otimes[\beta]` into $`(QC)^{\otimes k'}` using vectors in the separate multiplicity spaces; the multiplicity of $`[\nu]` cannot exceed the dimension of the combined multiplicity space, polynomial by Schur–Weyl.

*D8.29.4* $`D_C=\log(d_\gamma d_\beta/d_\nu)\ge0`. $`\E[e^{bD_C}\mid\gamma,\beta]=\sum_\nu m^\nu_{\gamma\beta}(d_\nu/(d_\gamma d_\beta))^{1-b}\le\sum_\nu m^\nu_{\gamma\beta}\le\poly(k)` since $`d_\nu\le d_\gamma d_\beta`, $`1-b\ge0`. Average over $`\gamma,\beta`. $`D_R`: same with $`(V,R)`.

_Formal route_ (RefactoringResult.md §5, D8.29): reduced density on a sub-subsystem plus §6 `TensorPower.merge_moment_le` (Lemma 6.1 (3)) (Merge.lean:143). Reason: Lemma 6.1 (3) is already uniform in the state.

_Used from._ {bpref "D8.24"}[D8.24], {bpref "D8.28"}[D8.28], Lemma 6.1(3) (`replicas:merge-moment`), Schur–Weyl.

:::

:::lemma_ "D8.30" (lean := "AreaLaw.Comparators.step_8_30")
*D8.30* — Step: Component inverse

_Source: 07-comparators.tex 553–575, `comparator:component-inverse`._

For $`u_B\ne0`, $`r=|B|`, sharp case ($`a\le a_0`, $`a\le c/\sqrt{\mathcal B}` with $`10a\le c_0/\sqrt{\mathcal B}`): $$`\frac{\langle u_B,A_{j,g}^{-1}u_B\rangle}{\|u_B\|^2}\le\poly(k)\exp\Big\{-2kaS'-(k-r)ag^{\rm pre}_{j,g}+2ar\log d_*+Ca\log\tbinom kr+Cka^2\mathcal B+o(k)\Big\}.` Rough: omit $`g^{\rm pre}` and $`a^2\mathcal B` terms. $`g^{\rm pre}_{j,g}\ge0`.

:::

:::proof "D8.30" (uses := "D8.5, D8.10, D8.24, D8.26, D8.27, D8.28, D8.29")
*D8.30.1* {bpref "D8.26"}[D8.26] and {bpref "D8.28"}[D8.28]: $`\langle u_B,A^{-1}u_B\rangle/\|u_B\|^2\le\poly(k)\binom kr^{Ca}\E[e^{-aG^{\rm good}}]`, $`-aG^{\rm good}=-aG_{\rm phys}-aF_C-aF_R+aD_C+aD_R` (bad factor dropped, {bpref "D8.27"}[D8.27]).

*D8.30.2* Auxiliary: $`-aF_C-aF_R\le-2a(kS'-r\log d_*-\log\binom kr-o(k))` on $`u_B` ({bpref "D8.27"}[D8.27]).

*D8.30.3* Rough: $`\mathsf J` discards $`e^{-aG_{\rm phys}}\le1`. Cauchy–Schwarz: $`\E e^{aD_C+aD_R}\le(\E e^{2aD_C})^{1/2}(\E e^{2aD_R})^{1/2}\le\poly(k)` ({bpref "D8.29"}[D8.29], $`2a\le1`). Gives the displayed bound without $`g^{\rm pre}`, $`a^2\mathcal B`.

*D8.30.4* Sharp: scalar Hölder with exponent $`5` on the five commuting factors $`e^{aD_C},e^{aD_R},e^{-aF_Q},e^{-aF_V},e^{aF_Y}`. $`D` factors: $`\E e^{5aD}\le\poly(k)` ($`5a\le1`). Physical factors: evaluate in the exact iid state $`\widetilde\Omega^{\otimes k'}` with {bpref "D8.10"}[D8.10] at $`u=5a` (the $`-` sign needs $`10a\le c_0/\sqrt{\mathcal B}`): $`\E e^{-5aF_Q}\le\exp\{-5ak'S(Q)+25Ck'a^2\mathcal B+O(\log)\}`, similarly $`V` and $`e^{5aF_Y}` with $`+` sign. After the $`\tfrac15` power the physical part is $`\exp\{-ak'[S(XU)+S(V)-S(Y)]+15Ck'a^2\mathcal B\}=\exp\{-a(k-r)g^{\rm pre}+Cka^2\mathcal B\}` ($`Q=XU`, in the region list of {bpref "D8.5"}[D8.5]).

*D8.30.5* Combine D8.30.2 and D8.30.4; absorb the extra $`\binom kr^a` factors into $`C`.

*D8.30.6* $`g^{\rm pre}\ge0`: physical purity, $`S(Y)=S(QV)\le S(Q)+S(V)`, $`Q=XU`.

_Used from._ {bpref "D8.5"}[D8.5], {bpref "D8.10"}[D8.10], {bpref "D8.24"}[D8.24], {bpref "D8.26"}[D8.26]–{bpref "D8.29"}[D8.29].

:::

:::lemma_ "D8.31" (lean := "AreaLaw.Comparators.step_8_31")
*D8.31* — Step: Inverse compression and lower pin

_Source: 07-comparators.tex 577–600, `comparator:inverse-compression`, `comparator:lower-pin`._

For $`0<\tau<1/2`: $$`\Pi A_{j,g}^{-1}\Pi\le\exp\{-kaL_{j,g}+o(k)\}\Pi,\quad L_{j,g}=2S'+(1-\tau)g^{\rm pre}_{j,g}-C\Big(\tau\log d_*+\frac{h(\tau)}a+a\mathcal B\Big).` Rough: $`g^{\rm pre}=0` and no $`a\mathcal B`. Equivalently $$`A_{j,g}\ge\exp\{kaL_{j,g}-o(k)\}\Pi.`

:::

:::proof "D8.31" (uses := "D8.24, D8.30")
*D8.31.1* Count: subsets with $`r\le\tau k` number $`\le(k+1)e^{kh(\tau)}`; $`\log\binom kr\le kh(\tau)` there ($`\tau<1/2`).

*D8.31.2* For unit $`u\in\mathrm{ran}\,\Pi`: $`\|A^{-1/2}u\|^2=\|\sum_BA^{-1/2}u_B\|^2\le(k+1)e^{kh(\tau)}\sum_B\langle u_B,A^{-1}u_B\rangle\le(k+1)e^{kh(\tau)}\max_{r\le\tau k}\frac{\langle u_B,A^{-1}u_B\rangle}{\|u_B\|^2}` (Cauchy–Schwarz over $`B`, then $`\sum_B\|u_B\|^2=1`); bound the max by {bpref "D8.30"}[D8.30].

*D8.31.3* In {bpref "D8.30"}[D8.30]: $`(k-r)g^{\rm pre}\ge(1-\tau)kg^{\rm pre}` ($`g^{\rm pre}\ge0`, $`r\le\tau k`); $`2ar\log d_*\le2a\tau k\log d_*`; $`Ca\log\binom kr\le Cakh(\tau)`. Count factor adds $`kh(\tau)=ka\cdot h(\tau)/a`. With $`a\le1` merge into $`C\,h(\tau)/a`. Factor $`ka` out: $`L_{j,g}` as stated.

*D8.31.4* Lower pin: $`c=e^{kaL_{j,g}-o(k)}`. $`\|\Pi A^{-1/2}\|=\|A^{-1/2}\Pi\|\le c^{-1/2}`. For any $`x`: $`\|\Pi x\|=\|\Pi A^{-1/2}A^{1/2}x\|\le c^{-1/2}\|A^{1/2}x\|`, i.e. $`\langle x,\Pi x\rangle\le c^{-1}\langle x,Ax\rangle`.

_Used from._ {bpref "D8.24"}[D8.24], {bpref "D8.30"}[D8.30].

:::

# 8.5 Passing the lower pin through the tree

:::lemma_ "D8.32" (lean := "AreaLaw.Comparators.step_8_32")
*D8.32* — Step: Floor and block lower bound

_Source: 07-comparators.tex 604–615._

There is a common polynomial $`p(k)` with $`A_{j,g}\ge p(k)^{-1}\id` on $`\mathcal S_k` for all leaves. On the common auxiliary sector, with $`b_0=(2p(k))^{-1}`, $$`A_{j,g}\ge b_0(\id-\Pi)+b_{j,g}\Pi,\qquad b_{j,g}=b_0+\tfrac12\exp\{kaL_{j,g}-o(k)\}.`

:::

:::proof "D8.32" (uses := "D8.6, D8.31")
$`A=\tfrac12A+\tfrac12A\ge\tfrac12p^{-1}\id+\tfrac12e^{kaL-o(k)}\Pi=b_0\id+\tfrac12e^{kaL-o(k)}\Pi`. Finitely many leaves: take the maximal polynomial.

_Used from._ {bpref "D8.6"}[D8.6] ($`F_Y\le F_P+F_F` on simultaneous symmetry, `replicas:leaf-floor`), {bpref "D8.31"}[D8.31].

:::

:::lemma_ "D8.33" (lean := "AreaLaw.Comparators.step_8_33")
*D8.33* — Step: Tree bound for $`\mathcal M_g`

_Source: 07-comparators.tex 616–627._

$$`\mathcal M_g\ge b_0(\id-\Pi)+e^{\ell_g}\Pi,\quad\ell_g=\sum_jw_j\log b_{j,g},` $$`\ell_g\ge ka\sum_jw_jL_{j,g}-o(k),\qquad0\le\ell_g-\log b_0\le ka\max_j(L_{j,g})_++o(k),` uniformly in the probabilities.

:::

:::proof "D8.33" (uses := "D7.3, D8.32")
*D8.33.1* Monotone in each input: $`\mathcal M_g\ge` the tree with leaves $`b_0(\id-\Pi)+b_{j,g}\Pi`. These commute and are scalars on $`\mathrm{ran}\,\Pi` and on $`\mathrm{ran}(\id-\Pi)`. Homogeneity: on $`\mathrm{ran}(\id-\Pi)` the value is $`b_0` (all leaves equal, $`\sum w_j=1`); on $`\mathrm{ran}\,\Pi` it is $`\prod_jb_{j,g}^{w_j}=e^{\ell_g}`.

*D8.33.2* $`b_{j,g}\ge\tfrac12e^{kaL_{j,g}-o(k)}` gives the first bound on $`\ell_g` ($`\log2` absorbed).

*D8.33.3* $`b_{j,g}\ge b_0` gives $`\ell_g-\log b_0\ge0`. $`b_{j,g}/b_0\le1+e^{kaL-o(k)}p(k)`, so $`\log(b_{j,g}/b_0)\le\log2+\max\{0,kaL_{j,g}\}+O(\log k)+o(k)`. Average over $`j` with weights $`\le\max_j`.

_Used from._ {bpref "D8.32"}[D8.32]; Lemma 7.1(2)(3).

:::

:::lemma_ "D8.34" (lean := "AreaLaw.Comparators.step_8_34")
*D8.34* — Step: Log lower bound for the tree

_Source: 07-comparators.tex 628–639, `comparator:tree-log-lower`._

$$`\langle v,\log\mathcal M_gv\rangle\ge ka\Big[\sum_jw_jL_{j,g}-\frac{E_{\rm def}}\tau\max_j(L_{j,g})_+\Big]-o(k).` Rough: $`\max_j(L_{j,g})_+\le2S'`. Sharp: $`\le2S'+g_{\max}`.

:::

:::proof "D8.34" (uses := "D8.23, D8.33")
*D8.34.1* $`\log\mathcal M_g\ge\log b_0(\id-\Pi)+\ell_g\Pi` (log operator monotone; commuting RHS).

*D8.34.2* $`\langle v,\log\mathcal M_gv\rangle\ge\log b_0+(\ell_g-\log b_0)\langle v,\Pi v\rangle\ge\ell_g-(\ell_g-\log b_0)\min(1,E_{\rm def}/\tau)` ({bpref "D8.23"}[D8.23] and $`\ell_g\ge\log b_0`).

*D8.34.3* Insert {bpref "D8.33"}[D8.33]: $`\ge ka\sum_jw_jL_{j,g}-o(k)-(ka\max_j(L_{j,g})_++o(k))\min(1,E_{\rm def}/\tau)`. The $`o(k)\min(1,\cdot)\le o(k)` is uniform in $`v`. Weaken $`\min(1,E_{\rm def}/\tau)\to E_{\rm def}/\tau`.

*D8.34.4* Rough: $`L_{j,g}\le2S'`. Sharp: $`L_{j,g}\le2S'+(1-\tau)g^{\rm pre}\le2S'+g_{\max}`.

_Formal route_ (RefactoringResult.md §5, D8.34.2): `⟨v, Π v⟩ ∈ [0, 1]`, any `Λ ≥ 0` bounding `L` on the positive-weight leaves (Lower.lean:797). Reason: same effect.

_Used from._ {bpref "D8.23"}[D8.23], {bpref "D8.33"}[D8.33]; operator monotonicity of $`\log`.

:::

:::lemma_ "D8.35" (lean := "AreaLaw.Comparators.step_8_35")
*D8.35* — Step: Proof of the two lower bounds

_Source: 07-comparators.tex 641–650._

(comparator:rough-lower) and (comparator:sharp-lower).

:::

:::proof "D8.35" (uses := "D8.7, D8.34")
*D8.35.1* $`N^2\langle v,\mathcal M^{2s}v\rangle=\|\mathcal M^s(N v)\|^2=\|\mathrm{pre}_k\|^2\le1`.

*D8.35.2* $`-\log N^2\ge\log\langle v,\mathcal M^{2s}v\rangle\ge2s\langle v,\log\mathcal Mv\rangle` (convexity of $`\exp`).

*D8.35.3* $`\log\mathcal M=\sum_g\log\mathcal M_g`. Sum {bpref "D8.34"}[D8.34] over $`g`. $`\sum_g\sum_jw_jL_{j,g}=K\langle L\rangle_{\rm av}`, $`\langle L\rangle_{\rm av}=2S'+(1-\tau)\langle g^{\rm pre}\rangle_{\rm av}-C(\tau\log d_*+h(\tau)/a+a\mathcal B)`. $`\sum_g\max_j(L_{j,g})_+\le K\cdot2S'` (rough) or $`K(2S'+g_{\max})` (sharp). $`aK=W`.

*D8.35.4* Divide by $`k`. $`-\log N^2/k\ge2sW[\langle L\rangle_{\rm av}-(E_{\rm def}/\tau)(2S'\text{ or }2S'+g_{\max})]-o_k(1)`. Since $`2S'\le2(S'+g_{\max})` the coefficient of $`E_{\rm def}/\tau` is at most $`2(S'+g_{\max})`: the constant $`C` in the display is $`2`. Rough: drop $`g^{\rm pre}` and $`a\mathcal B`.

_Used from._ {bpref "D8.7"}[D8.7], the statement of the proposition this step belongs to, {bpref "D8.34"}[D8.34].

:::

:::lemma_ "D8.36" (lean := "AreaLaw.Comparators.step_8_36")
*D8.36* — Step: Entropy identity

_Source: 07-comparators.tex 652–657, `comparator:entropy-identity`._

$`2S_X+g^{\rm pre}-g^{\rm post}=I(X{:}V)+I(X{:}YV)` (index $`(j,g)` suppressed).

:::

:::proof "D8.36" (uses := "D8.1, D2.1")
*D8.36.1* Purity: $`S(XU)=S(YV)`, $`S(XV)=S(UY)`, $`S(XYV)=S(U)`.

*D8.36.2* $`g^{\rm pre}-g^{\rm post}=S(XU)+S(V)-S(U)-S(UY)=S(YV)+S(V)-S(U)-S(XV)`.

*D8.36.3* $`I(X{:}V)=S_X+S(V)-S(XV)`; $`I(X{:}YV)=S_X+S(YV)-S(XYV)=S_X+S(YV)-S(U)`. Sum $`=2S_X+S(V)+S(YV)-S(XV)-S(U)` = $`2S_X+g^{\rm pre}-g^{\rm post}` by D8.36.2.

_Used from._ {bpref "D8.1"}[D8.1] ($`\widetilde\Omega` pure on $`XUYV`), {bpref "D2.1"}[D2.1].

:::

:::lemma_ "D8.37" (lean := "AreaLaw.Comparators.prop_8_1") (uses := "D8.12, D8.29, D8.33, D8.34")
*D8.37* — Step: Uniformity of the errors

_Source: 07-comparators.tex 659–667; 205–213 of the statement._

All errors use maxima over finitely many statuses, fixed-dimension Schur polynomial bounds, and the single label sequence (comparator:high-label). Defect-component estimates are uniform in the auxiliary states. Jensen and mean monotonicity introduce no inverse terminal probability. Hence replica errors are uniform in all terminal probabilities (zero weights: omit those branches), permitting a different interpolation point of the tree for each $`k`, then $`k\to\infty` at the fixed finite physical system.

_Used from._ {bpref "D8.12"}[D8.12], {bpref "D8.29"}[D8.29], {bpref "D8.33"}[D8.33], {bpref "D8.34"}[D8.34].

:::
