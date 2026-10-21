import Verso
import VersoManual
import VersoBlueprint
import AreaLawBlueprint.TexPrelude
import AreaLawRefactored

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Entropy and induced-graph locality" =>

Entropy conventions; Lemma 2.1, continuity of $`S(D|E)` with constant depending on $`\dim D` only; counting: $`v_r=1+2r(r+1)` (eq:ball-count), $`\le\mu_R=2^{v_R-1}` terms through a site, norm budget $`J\mu_R`, $`\le2v_R\mu_R|\partial_\Lambda D|` terms split by $`D` (eq:crossing-count); degenerate cases ($`q=1`, $`\Lambda=\varnothing`, $`R=0`) $`\Rightarrow` standing $`q\ge2`, $`R\ge1`, $`\Lambda\ne\varnothing`; Lemma 2.2: $`\partial_\Lambda A=\varnothing\Rightarrow S_\Omega(A)=0` (uniqueness only); convention for $`C,c`. §3–§4 consume the counting bounds; §5, §9, §10 Lemma 2.1; §11 Lemma 2.2.

:::definition "D2.1" (lean := "AreaLaw.condEntropy, AreaLaw.condMutualInfo")
*D2.1* — Def: Conditional entropy, mutual information, conditional mutual information

Lines 8–18.

For a density matrix $`\rho` on systems $`D,E,F` (juxtaposition = tensor product / union of site sets): $$`S(D|E)_\rho=S(DE)_\rho-S(E)_\rho,\qquad I(D:E)_\rho=S(D)_\rho+S(E)_\rho-S(DE)_\rho,` $$`I(D:F|E)_\rho=S(DE)_\rho+S(EF)_\rho-S(E)_\rho-S(DEF)_\rho.` Conventions (lines 3–6): no subscript = entropies of the ground vector $`\Omega`; a changed state is shown as a subscript.

_Used from._ §1: $`S_\Omega`.

:::

:::lemma_ "D2.2" (lean := "AreaLaw.step_2_2")
*D2.2* — Step: Entropy facts used without proof

Lines 19–25.

For normalized finite-dimensional density operators:

(1) Strong subadditivity (SSA): $`I(D:F|E)_\rho\ge0` \[Lieb–Ruskai 1973\].

(2) $`S(D|EF)\le S(D|E)`; equals item 1 via $`I(D:F|E)=S(D|E)-S(D|EF)`.

(3) $`I(D:E)\le I(D:EF)`; equals item 1 via $`I(D:EF)-I(D:E)=I(D:F|E)`.

(4) Subadditivity + purification $`\Rightarrow` $`|S(D|E)_\rho|\le\log\dim D`.

(5) Pure state on $`DE`: $`S(D)=S(E)`.

(6) All hold with empty $`D,E,F`; $`\mathcal H_\varnothing=\mathbb C` (empty tensor product), entropies $`0`.

:::

:::proof "D2.2" (uses := "D2.1")
_Formal route_ (RefactoringResult.md §5, D2.2 item 4, lower bound): Araki–Lieb S(E) − S(D) ≤ S(DE). Reason: Araki–Lieb already on regions; no purification.

_Used from._ {bpref "D2.1"}[D2.1].

:::

:::definition "D2.3" (lean := "AreaLaw.traceDist, AreaLaw.C_h")
*D2.3* — Def: Binary entropy and trace distance

Lines 27–31.

$`h(u)=-u\log u-(1-u)\log(1-u)` for $`u\in[0,1]`, $`0\log 0=0`. Trace distance of states $`\rho,\sigma`: $`\delta=\tfrac12\|\rho-\sigma\|_1`.

_Used from._ none.

:::

:::lemma_ "D2.4" (lean := "AreaLaw.lemma_2_1")
*D2.4* — Lemma 2.1: Continuity with a fixed controlled system

Lines 33–72. Label `lem:continuity`; displayed estimate `eq:conditional-continuity` (lines 37–42).

Let $`\rho,\sigma` be density operators on finite-dimensional $`D\otimes E`, $`\delta=\tfrac12\|\rho-\sigma\|_1\le1`, $`d_D=\dim D`. Then $$`|S(D|E)_\rho-S(D|E)_\sigma|\ \le\ 2\delta\log d_D+(1+\delta)\,h\!\Big(\frac{\delta}{1+\delta}\Big)\ \le\ C\sqrt\delta\,\log(e\,d_D).` Same for $`S(D)` ($`E` trivial). Summing the two bounds controls $`|I(D:E)_\rho-I(D:E)_\sigma|` in terms of $`d_D`, independent of $`\dim E`.

:::

:::proof "D2.4" (uses := "D2.1, D2.2, D2.3, D2.5")
(Mixture bound: Winter 2016, Lemma 2. Jordan trick: Alicki–Fannes.)

*D2.4.1* _Mixture bound._ For $`\tau=\sum_jp_j\tau_j` on $`DE`, $`H(p)=-\sum p_j\log p_j`: $$`0\le S(D|E)_\tau-\sum_jp_jS(D|E)_{\tau_j}\le H(p).`

– Lower bound. Classical register $`X`, $`\tau_{XDE}=\sum_jp_j|j\rangle\langle j|\otimes\tau_j`. Then $`S(D|EX)_{\tau_{XDE}}=\sum_jp_jS(D|E)_{\tau_j}`, and the $`DE`-marginal of $`\tau_{XDE}` is $`\tau`. {bpref "D2.2"}[D2.2] item 2: $`S(D|EX)\le S(D|E)_\tau`.

– Upper bound. $`S(DE)_\tau\le\sum_jp_jS(DE)_{\tau_j}+H(p)` (mixing bound), $`S(E)_\tau\ge\sum_jp_jS(E)_{\tau_j}` (concavity). Subtract.

– Mixing bound. For the cq-state $`\sum_jp_j|j\rangle\langle j|\otimes\tau_j` on $`XB`: $`S(XB)=H(p)+\sum_jp_jS(\tau_j)`, and $`S(B)\le S(XB)` since $`S(X|B)\ge0` for classical $`X`. Paper's phrasing: duplicate register, conditional entropy given $`DE` nonnegative.

*D2.4.2* _Jordan decomposition._ Case $`\delta>0`. $`\rho-\sigma=P-N`, $`P,N\ge0` with orthogonal supports. $`\operatorname{Tr}(\rho-\sigma)=0\Rightarrow\operatorname{Tr}P=\operatorname{Tr}N=\tfrac12\|\rho-\sigma\|_1=\delta`. $`\tau_\pm=P/\delta,\ N/\delta` (states), so $`\rho-\sigma=\delta(\tau_+-\tau_-)`, $`\rho+\delta\tau_-=\sigma+\delta\tau_+`, hence $$`\omega:=\frac{\rho+\delta\tau_-}{1+\delta}=\frac{\sigma+\delta\tau_+}{1+\delta}.`

*D2.4.3* _D2.4.1 on both mixtures of $`\omega`_, weights $`(\tfrac1{1+\delta},\tfrac\delta{1+\delta})`, $`H(p)=h(\tfrac\delta{1+\delta})=:h_\delta`. Write $`s_\bullet=S(D|E)_\bullet`.

– $`\rho`-mixture, lower bound: $`(1+\delta)s_\omega\ge s_\rho+\delta s_{\tau_-}`.

– $`\sigma`-mixture, upper bound: $`(1+\delta)s_\omega\le s_\sigma+\delta s_{\tau_+}+(1+\delta)h_\delta`.

– Combine: $`s_\rho-s_\sigma\le\delta(s_{\tau_+}-s_{\tau_-})+(1+\delta)h_\delta\le2\delta\log d_D+(1+\delta)h_\delta`, using $`|s_{\tau_\pm}|\le\log d_D` ({bpref "D2.2"}[D2.2] item 4).

– Exchange $`\rho\leftrightarrow\sigma` ($`\tau_+\leftrightarrow\tau_-`) for the other sign. First inequality.

*D2.4.4* _Second inequality._ $`h(u)\le C_h\sqrt u` with $`C_h=1+2/e`: $`-u\log u=\sqrt u\cdot\sqrt u(-\log u)\le\tfrac2e\sqrt u` (max of $`t^{1/2}\log(1/t)` is $`2/e`); $`-(1-u)\log(1-u)\le u\le\sqrt u` (from $`\log\tfrac1{1-u}\le\tfrac u{1-u}`). With $`u=\tfrac\delta{1+\delta}\le\delta\le1`: $`(1+\delta)h_\delta\le2C_h\sqrt\delta`, $`2\delta\log d_D\le2\sqrt\delta\log d_D`. Sum $`\le2C_h\sqrt\delta(1+\log d_D)=2C_h\sqrt\delta\log(ed_D)`. $`C=2(1+2/e)` works; $`C` absolute.

*D2.4.5* _Case $`\delta=0`._ $`\rho=\sigma`, both sides vanish.

*D2.4.6* _$`S(D)` and $`I(D:E)`._ Lemma with $`E` trivial on $`\rho_D,\sigma_D`, trace distance $`\delta_D\le\delta` ({bpref "D2.5"}[D2.5.3]). $`f(\delta)=2\delta\log d_D+(1+\delta)h(\tfrac\delta{1+\delta})` is nondecreasing: $`(1+\delta)h(\tfrac\delta{1+\delta})=(1+\delta)\log(1+\delta)-\delta\log\delta`, derivative $`\log\tfrac{1+\delta}\delta>0`. So $`|S(D)_\rho-S(D)_\sigma|\le f(\delta)\le C\sqrt\delta\log(ed_D)`. $`I(D:E)=S(D)-S(D|E)` gives $`|I(D:E)_\rho-I(D:E)_\sigma|\le2f(\delta)\le2C\sqrt\delta\log(ed_D)`.

_Used from._ {bpref "D2.1"}[D2.1], {bpref "D2.2"}[D2.2] (items 1, 2, 4), {bpref "D2.3"}[D2.3], {bpref "D2.5"}[D2.5.3] (contractivity of trace distance under partial trace). Two textbook facts not restated in §2: concavity of $`S`; mixing bound $`S(\sum_jp_j\tau_j)\le\sum_jp_jS(\tau_j)+H(p)` (derived in D2.4.1 from $`S(X|B)\ge0` for classical $`X`).

:::

:::lemma_ "D2.5" (lean := "AreaLaw.step_2_5")
*D2.5* — Step: Pure-state trace distance; usage rule for Lemma 2.1

Lines 74–78.

For unit vectors $`\xi,\eta`: $`\tfrac12\|\,|\xi\rangle\langle\xi|-|\eta\rangle\langle\eta|\,\|_1\le\|\xi-\eta\|`. Lemma 2.1 is applied (i) on regions with a controlled number of sites, or (ii) with the controlled region as the first argument of a conditional entropy, so estimates never acquire the dimension of an uncontrolled complement.

:::

:::proof "D2.5"
*D2.5.1* $`\tfrac12\|\,|\xi\rangle\langle\xi|-|\eta\rangle\langle\eta|\,\|_1=\sqrt{1-|\langle\xi,\eta\rangle|^2}`: difference traceless, rank two, Hermitian, eigenvalues $`\pm\lambda` with $`\lambda^2=\tfrac12\operatorname{Tr}(\cdot)^2=1-|\langle\xi,\eta\rangle|^2`; trace norm $`2\lambda`.

*D2.5.2* $`x=|\langle\xi,\eta\rangle|\in[0,1]`: $`1-x^2=(1-x)(1+x)\le2(1-x)\le2-2\operatorname{Re}\langle\xi,\eta\rangle=\|\xi-\eta\|^2`.

*D2.5.3* Partial trace does not increase trace distance; bound passes to every reduced state.

_Formal route_ (RefactoringResult.md §5, D2.5.1): X³ = (1−\\|⟨ξ,η⟩\\|²)X, so \\|X\\| = c^\{−1/2\}X². Reason: avoids a spectral computation.

_Used from._ none (a usage rule for the continuity lemma of this section, not an input to it).

:::

:::definition "D2.6" (lean := "AreaLaw.GraphDomain.ball, OpenAI.graphNbhd, OpenAI.ambientDilation")
*D2.6* — Def: Balls, graph neighborhoods, ambient dilations

Lines 82–92.

$`B_\Lambda(x,r)=\{y\in\Lambda:d_\Lambda(x,y)\le r\}`. For $`D\subseteq\Lambda`: $`N^\Lambda_r(D)=\{x:d_\Lambda(x,D)\le r\}`. For finite $`T\subset\mathbb Z^2` and integer $`j\ge0`, ambient dilation $`T_j=T+([-j,j]^2\cap\mathbb Z^2)`. Graph neighborhoods reserved for support and propagation estimates.

_Used from._ §1: $`d_\Lambda`.

:::

:::lemma_ "D2.7" (lean := "AreaLaw.eq_ball_count")
*D2.7* — Step eq:ball-count: Ball cardinality

Lines 85–87.

For every site $`x\in\Lambda` and integer $`r\ge0`: $`|B_\Lambda(x,r)|\le v_r:=1+2r(r+1)`.

:::

:::proof "D2.7" (uses := "D2.6")
*D2.7.1* A graph path of length $`\le r` changes coordinates by $`|\cdot|_1\le1` per edge, so $`y\in B_\Lambda(x,r)\Rightarrow|y-x|_1\le r`.

*D2.7.2* $`|\{z\in\mathbb Z^2:|z|_1\le r\}|=1+\sum_{k=1}^r4k=1+2r(r+1)` (sphere $`|z|_1=k` has $`4k` points).

_Formal route_ (RefactoringResult.md §5, D2.7.2): ℓ¹-ball covered by two rotated squares of (r+1)² and r² points (parity of a+b+r); proves ≤ only. Reason: the anchor needs ≤; far shorter.

_Used from._ {bpref "D2.6"}[D2.6].

:::

:::lemma_ "D2.8" (lean := "AreaLaw.step_2_8")
*D2.8* — Step: Term multiplicity and norm budget per site

Lines 94–103.

Assign to each nonzero interaction (support) $`X` in eq:hamiltonian an _anchor_ in $`X`. Put $`\mu_R:=2^{v_R-1}`. Then for every $`x\in\Lambda`:

$`\#\{X:x\in X,\ X\text{ a summand of }H\}\le\mu_R`;

$`\#\{X\text{ anchored at }x\}\le\mu_R`;

$`\sum_{X\ni x}\|h_X\|\le J\mu_R`;

$`|X|\le v_R` for every support $`X` (consequence, D2.8.4).

Terms whose operator is a scalar multiple of the identity obey the same bounds with their assigned supports.

:::

:::proof "D2.8" (uses := "D1.2, D2.7")
*D2.8.1* $`x\in X`, $`\operatorname{diam}_{d_\Lambda}X\le R` $`\Rightarrow` every $`y\in X` has $`d_\Lambda(x,y)\le R`, so $`X\subseteq B_\Lambda(x,R)`.

*D2.8.2* Subsets of $`B_\Lambda(x,R)` containing $`x`: $`2^{|B_\Lambda(x,R)|-1}\le2^{v_R-1}=\mu_R` ({bpref "D2.7"}[D2.7]).

*D2.8.3* Anchored at $`x` $`\Rightarrow` contains $`x`. Each support appears once (§1), each $`\|h_X\|\le J`, so $`\sum_{X\ni x}\|h_X\|\le J\cdot\#\{X\ni x\}\le J\mu_R`.

*D2.8.4* D2.8.1 with any $`x\in X`: $`|X|\le|B_\Lambda(x,R)|\le v_R`.

_Used from._ {bpref "D2.7"}[D2.7]; §1 eq:hamiltonian.

:::

:::lemma_ "D2.9" (lean := "AreaLaw.eq_crossing_count")
*D2.9* — Step eq:crossing-count: Terms split by a set

Lines 105–113.

An assigned support $`X` is _split_ by $`D\subseteq\Lambda` if $`X\cap D\ne\varnothing\ne X\setminus D`. Then $$`\#\{\text{terms split by }D\}\le2v_R\mu_R\,|\partial_\Lambda D|.`

:::

:::proof "D2.9" (uses := "D2.6, D2.7, D2.8")
*D2.9.1* $`a` the anchor of a split $`X`. There is $`y\in X` on the opposite side of $`D` from $`a` ($`y\in X\setminus D` if $`a\in D`, $`y\in X\cap D` otherwise), $`d_\Lambda(a,y)\le R` ({bpref "D2.8"}[D2.8.1]).

*D2.9.2* A shortest $`\Lambda`-path $`a\to y` has length $`\le R`, endpoints on different sides of $`D`, hence contains an edge $`\{z,z'\}`, $`z\in D`, $`z'\in\Lambda\setminus D`: an edge of $`\partial_\Lambda D`.

*D2.9.3* So $`a\in B_\Lambda(z,R)` for one of the $`\le2|\partial_\Lambda D|` endpoints $`z` of edges of $`\partial_\Lambda D`.

*D2.9.4* Anchors: $`\le2|\partial_\Lambda D|\cdot v_R` ({bpref "D2.7"}[D2.7]). Terms per anchor: $`\le\mu_R` ({bpref "D2.8"}[D2.8]). Multiply.

_Used from._ {bpref "D2.6"}[D2.6], {bpref "D2.7"}[D2.7], {bpref "D2.8"}[D2.8].

:::

:::lemma_ "D2.10" (lean := "AreaLaw.step_2_10")
*D2.10* — Step: Product decomposition across a bipartition

Lines 114–116.

For a bipartition of $`\Lambda` and a term $`h_X`, matrix units on its finite support decompose $`h_X` into a bounded number of product operators (one factor each side) with bounded factors. For the original interactions the bounds depend only on $`q,R,J`.

:::

:::proof "D2.10" (uses := "D2.8")
_expansion; paper states only "bounded"._

*D2.10.1* Split $`X=X_1\sqcup X_2` along the bipartition. Expand in the matrix-unit basis of $`\operatorname{End}(\mathcal H_{X_1})\otimes\operatorname{End}(\mathcal H_{X_2})`: $`h_X=\sum c_{ijkl}\,E_{ij}\otimes E_{kl}`, $`c_{ijkl}=\langle i,k|h_X|j,l\rangle`.

*D2.10.2* Summands $`\le q^{2|X|}\le q^{2v_R}`. $`|c_{ijkl}|\le\|h_X\|\le J`. $`\|E_{ij}\|=\|E_{kl}\|=1`.

_Used from._ {bpref "D2.8"}[D2.8] ($`|X|\le v_R`, {bpref "D2.8"}[D2.8.4]).

:::

:::lemma_ "D2.11" (lean := "AreaLaw.step_2_11")
*D2.11* — Step: Degenerate cases

Lines 118–121.

If $`q=1` or $`\Lambda=\varnothing`: all entropies vanish. If $`R=0`: $`H` is a sum of on-site operators; uniqueness of its ground state makes $`\Omega` a tensor product, so $`S_\Omega(A)=0` and Theorem 1.1 holds. Henceforth $`q\ge2`, $`R\ge1`, $`\Lambda\ne\varnothing`.

:::

:::proof "D2.11" (uses := "D1.4")
*D2.11.1* $`q=1` or $`\Lambda=\varnothing`: $`\mathcal H_\Lambda=\mathbb C`, the only state is pure, every $`\rho_A` pure.

*D2.11.2* $`R=0`: only singletons have $`\operatorname{diam}X\le0`, so $`H=\sum_xh_{\{x\}}`, commuting operators on distinct tensor factors. Ground eigenspace $`\bigotimes_x\ker(h_{\{x\}}-e_x)`, $`e_x=\min\operatorname{spec}h_{\{x\}}`. One-dimensional $`\Rightarrow` each factor one-dimensional. So $`\Omega=\bigotimes_x\omega_x` (up to phase), $`\rho_A` pure, $`S_\Omega(A)=0\le C|\partial_\Lambda A|`.

_Formal route_ (RefactoringResult.md §5, D2.11.2 (R = 0)): the core lemma `regionEntropy_eq_zero_of_split`: for R = 0 every support is a singleton, which lies in A or Λ∖A. Reason: one argument serves D2.11.2 and {bpref "D2.12"}[D2.12].

_Used from._ §1 Theorem 1.1 (`thm:area`).

:::

:::lemma_ "D2.12" (lean := "AreaLaw.lemma_2_2")
*D2.12* — Lemma 2.2: A cut with no crossing edge

Lines 123–133. Label `lem:zero-boundary`.

Under the hypotheses of Theorem 1.1 ($`H` admissible, unique normalized ground vector $`\Omega` up to phase, gap $`\Delta`), if $`A\subseteq\Lambda` and $`\partial_\Lambda A=\varnothing`, then $`S_\Omega(A)=0`.

:::

:::proof "D2.12" (uses := "D1.2, D1.4")
*D2.12.1* No edge between $`A` and $`\Lambda\setminus A` $`\Rightarrow` $`A` is a union of connected components of the induced graph.

*D2.12.2* Every support $`X` has $`d_\Lambda`-diameter $`\le R<\infty`, $`d_\Lambda=\infty` across components, so $`X` lies in a single component $`c`.

*D2.12.3* Hence $`H=\sum_cH_c`, $`H_c=\sum_{X\subseteq c}h_X` on $`\mathcal H_c`, identity elsewhere ("tensor sum").

*D2.12.4* $`E_0=\sum_cE_0^c`, ground eigenspace $`\bigotimes_c\ker(H_c-E^c_0)`.

*D2.12.5* One-dimensional $`\Rightarrow` each factor one-dimensional: $`\Omega=\bigotimes_c\Omega_c` up to phase.

*D2.12.6* $`A` a union of components $`\Rightarrow` $`\Omega=\Omega_A\otimes\Omega_{\Lambda\setminus A}`. $`\rho_A` pure, $`S_\Omega(A)=0`.

_Formal route_ (RefactoringResult.md §5, D2.12 (Lemma 2.2), steps D2.12.3–6): two blocks A, Λ∖A only: on the coefficient matrix N(x,z) = v(glue x z), H acts as N ↦ PN + NG; uniqueness (from the gap, its size unused) gives PM = aM, MG = (E₀−a)M, so a column of M times a row of M is again a ground vector, M has rank one, ρ\_A = MMᴴ is a rank-one projection, S = 0 (`AreaLaw.exists_hamiltonian_coeff`, `regionEntropy_eq_zero_of_split`, S02\_Preliminaries.lean:626, :659). Reason: tensor sums over an arbitrary family of components are costly in Lean; the two-block version is the same mathematics.

_Used from._ §1: eq:hamiltonian (finite $`R`, supports), Theorem 1.1 uniqueness of $`\Omega`.

:::
