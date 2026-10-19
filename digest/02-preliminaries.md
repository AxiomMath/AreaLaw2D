# Digest of §2 — Entropy and induced-graph locality

Source: `paper/sections/01-preliminaries.tex` (139 lines), label `sec:prelim`. Notation from §1 (`00-introduction.tex`): $\Lambda\subset\mathbb Z^2$ finite with induced square-lattice graph and graph distance $d_\Lambda$ ($=+\infty$ across components); $\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}\mathbb C^q$; $H=\sum_{\varnothing\ne X\subseteq\Lambda,\ \operatorname{diam}_{d_\Lambda}X\le R}h_X$, $h_X=h_X^*$, $\|h_X\|\le J$ (eq:hamiltonian, one summand per support $X$, possibly zero); $\partial_\Lambda A=\{\{x,y\}:x\in A,\ y\in\Lambda\setminus A,\ |x-y|_1=1\}$; $S_\Omega(A)=-\operatorname{Tr}\rho_A\log\rho_A$, natural logs.

## Section in one paragraph

§2 fixes entropy conventions and proves the only analytic tool used later to move between nearby states: a dimension-free continuity bound for conditional entropy $S(D|E)$ (Lemma 2.1), whose constant depends on $\dim D$ but not on $\dim E$. Then it does the lattice bookkeeping: ball size $v_r=1+2r(r+1)$ (eq:ball-count), terms through a site $\le\mu_R=2^{v_R-1}$, norm budget $J\mu_R$, terms split by a set $D$ $\le 2v_R\mu_R|\partial_\Lambda D|$ (eq:crossing-count). It disposes of degenerate cases ($q=1$, $\Lambda=\varnothing$, $R=0$) so that later sections assume $q\ge2$, $R\ge1$, $\Lambda\ne\varnothing$. Lemma 2.2 shows $S_\Omega(A)=0$ when $\partial_\Lambda A=\varnothing$, using only uniqueness of the ground state. Last, it fixes the convention for the constants $C,c$. Order: entropy definitions and facts, continuity, counting, degenerate cases, zero-boundary lemma, constants. §3–§4 consume the counting bounds; §5, §9, §10 consume Lemma 2.1; §11 consumes Lemma 2.2.

---

#### D2.1 Def — Conditional entropy, mutual information, conditional mutual information
Lines 8–18.

**Statement.** For a density matrix $\rho$ on systems $D,E,F$ (juxtaposition = tensor product / union of site sets):
$$S(D|E)_\rho=S(DE)_\rho-S(E)_\rho,\qquad I(D:E)_\rho=S(D)_\rho+S(E)_\rho-S(DE)_\rho,$$
$$I(D:F|E)_\rho=S(DE)_\rho+S(EF)_\rho-S(E)_\rho-S(DEF)_\rho.$$
Conventions (lines 3–6): without subscript, entropies are those of the original ground vector $\Omega$; a changed state is shown as a subscript.

**Used from.** §1: $S_\Omega$.
**Output.** Notation for §5 onward. Identity $I(D:E)=S(D)-S(D|E)$ (immediate from the definitions; used in D2.4 and in §9, §10 where mutual information is written as $S(X)-S(X|\cdot)$).
**Standard?** Standard.

---

#### D2.2 Step — Entropy facts used without proof
Lines 19–25.

**Statement.** For normalized finite-dimensional density operators:
1. Strong subadditivity (SSA): $I(D:F|E)_\rho\ge0$ [Lieb–Ruskai 1973].
2. SSA $\Rightarrow$ conditioning decreases conditional entropy: $S(D|EF)\le S(D|E)$. Identity $I(D:F|E)=S(D|E)-S(D|EF)$ (expand both sides), so this is $I(D:F|E)\ge0$.
3. SSA $\Rightarrow$ discarding systems cannot increase mutual information: $I(D:E)\le I(D:EF)$. Same inequality, since $I(D:EF)-I(D:E)=I(D:F|E)$.
4. Subadditivity + purification $\Rightarrow$ $|S(D|E)_\rho|\le\log\dim D$.
5. Pure state on $DE$: $S(D)=S(E)$.
6. All hold when some of $D,E,F$ are empty; the Hilbert space of the empty region is $\mathbb C$ (empty tensor product), all its entropies are $0$.

**Used from.** D2.1.
**Output.** Item 4 enters D2.4 step 3; item 2 enters D2.4 step 1; items 2, 3, 5 are quoted in §5 (`04-conditional.tex:138`: "Purity and strong subadditivity give the displayed identities") and §6 onward.
**Standard?** Standard. SSA: Lieb–Ruskai, J. Math. Phys. 14 (1973). Item 4 expanded: upper, $S(D|E)\le S(D)\le\log\dim D$ (item 2 with $E$ trivial, then $S(D)\le\log\dim D$). Lower, purify $\rho_{DE}$ to $\rho_{DEF}$; then $S(D|E)=S(DE)-S(E)=S(F)-S(DF)=-S(D|F)\ge-S(D)\ge-\log\dim D$.
**Pitfall.** Item 4 bounds by $\log\dim D$ of the *first* argument only. This asymmetry is what makes Lemma 2.1 independent of $\dim E$.

---

#### D2.3 Def — Binary entropy and trace distance
Lines 27–31.

**Statement.** $h(u)=-u\log u-(1-u)\log(1-u)$ for $u\in[0,1]$, $0\log 0=0$. Trace distance of states $\rho,\sigma$: $\delta=\tfrac12\|\rho-\sigma\|_1$. Continuity is taken in the dimension-independent conditional-entropy form of Alicki–Fannes [2004] in Winter's sharpened version [2016].

**Used from.** none.
**Output.** $h$ and $\delta$ in D2.4.
**Standard?** Standard.

---

#### D2.4 Lemma 2.1 — Continuity with a fixed controlled system
Lines 33–72. Label `lem:continuity`; displayed estimate `eq:conditional-continuity` (lines 37–42).

**Statement.** Let $\rho,\sigma$ be density operators on finite-dimensional $D\otimes E$, $\delta=\tfrac12\|\rho-\sigma\|_1\le1$, $d_D=\dim D$. Then
$$|S(D|E)_\rho-S(D|E)_\sigma|\ \le\ 2\delta\log d_D+(1+\delta)\,h\!\Big(\frac{\delta}{1+\delta}\Big)\ \le\ C\sqrt\delta\,\log(e\,d_D).$$
Same for $S(D)$ (take $E$ trivial). Hence the same bounds, summed, control $|I(D:E)_\rho-I(D:E)_\sigma|$ in terms of $d_D$, independent of $\dim E$.

**Used from.** D2.1, D2.2 (items 1, 2, 4), D2.3, D2.5.3 (contractivity of trace distance under partial trace). Also two textbook facts not restated in §2: concavity of $S$, and the ordinary mixing bound $S(\sum_jp_j\tau_j)\le\sum_jp_jS(\tau_j)+H(p)$ (derived in D2.4.1 from $S(X|B)\ge0$ for classical $X$).

**Proof.** (Mixture bound is Winter 2016, Lemma 2; Jordan trick as in Alicki–Fannes.)

- D2.4.1 *Mixture bound.* For $\tau=\sum_jp_j\tau_j$ on $DE$, with $H(p)=-\sum p_j\log p_j$:
$$0\le S(D|E)_\tau-\sum_jp_jS(D|E)_{\tau_j}\le H(p).$$
  - Lower bound. Let $X$ be a classical register, $\tau_{XDE}=\sum_jp_j|j\rangle\langle j|\otimes\tau_j$. Then $S(D|EX)_{\tau_{XDE}}=\sum_jp_jS(D|E)_{\tau_j}$, and the $DE$-marginal of $\tau_{XDE}$ is $\tau$. SSA (D2.2 item 2): $S(D|EX)\le S(D|E)_\tau$.
  - Upper bound. $S(DE)_\tau\le\sum_jp_jS(DE)_{\tau_j}+H(p)$ (ordinary mixing bound), and $S(E)_\tau\ge\sum_jp_jS(E)_{\tau_j}$ (concavity). Subtract: $S(D|E)_\tau\le\sum_jp_jS(D|E)_{\tau_j}+H(p)$.
  - Ordinary mixing bound. For the cq-state $\sum_jp_j|j\rangle\langle j|\otimes\tau_j$ on $XB$: $S(XB)=H(p)+\sum_jp_jS(\tau_j)$, and $S(B)\le S(XB)$ because $S(X|B)\ge0$ for classical $X$. Paper: record a duplicate of the register; its conditional entropy given $DE$ is nonnegative.
- D2.4.2 *Jordan decomposition.* Case $\delta>0$. Write $\rho-\sigma=P-N$ with $P,N\ge0$ orthogonal supports. $\operatorname{Tr}(\rho-\sigma)=0\Rightarrow\operatorname{Tr}P=\operatorname{Tr}N=\tfrac12\|\rho-\sigma\|_1=\delta$. Put $\tau_\pm=P/\delta,\ N/\delta$ (states), so $\rho-\sigma=\delta(\tau_+-\tau_-)$. Then $\rho+\delta\tau_-=\sigma+\delta\tau_+$, hence
$$\omega:=\frac{\rho+\delta\tau_-}{1+\delta}=\frac{\sigma+\delta\tau_+}{1+\delta}.$$
- D2.4.3 *Apply D2.4.1 to both mixtures of $\omega$*, weights $(\tfrac1{1+\delta},\tfrac\delta{1+\delta})$, $H(p)=h(\tfrac\delta{1+\delta})=:h_\delta$. Write $s_\bullet=S(D|E)_\bullet$.
  - From the $\rho$-mixture, lower bound: $(1+\delta)s_\omega\ge s_\rho+\delta s_{\tau_-}$.
  - From the $\sigma$-mixture, upper bound: $(1+\delta)s_\omega\le s_\sigma+\delta s_{\tau_+}+(1+\delta)h_\delta$.
  - Combine: $s_\rho-s_\sigma\le\delta(s_{\tau_+}-s_{\tau_-})+(1+\delta)h_\delta\le2\delta\log d_D+(1+\delta)h_\delta$, using $|s_{\tau_\pm}|\le\log d_D$ (D2.2 item 4).
  - Exchange $\rho\leftrightarrow\sigma$ ($\tau_+\leftrightarrow\tau_-$) for the other sign. This is the first inequality.
- D2.4.4 *Second inequality.* Elementary bound $h(u)\le C_h\sqrt u$. Explicit $C_h=1+2/e$: $-u\log u=\sqrt u\cdot\sqrt u(-\log u)\le\tfrac2e\sqrt u$ (max of $t^{1/2}\log(1/t)$ is $2/e$), and $-(1-u)\log(1-u)\le u\le\sqrt u$ (from $\log\tfrac1{1-u}\le\tfrac u{1-u}$). With $u=\tfrac\delta{1+\delta}\le\delta\le1$: $(1+\delta)h_\delta\le2C_h\sqrt\delta$, and $2\delta\log d_D\le2\sqrt\delta\log d_D$. Sum $\le2C_h\sqrt\delta(1+\log d_D)=2C_h\sqrt\delta\log(ed_D)$. So $C=2(1+2/e)$ works; $C$ is absolute.
- D2.4.5 *Case $\delta=0$.* $\rho=\sigma$, both sides vanish.
- D2.4.6 *$S(D)$ and $I(D:E)$.* Apply the lemma with $E$ trivial to $\rho_D,\sigma_D$. Their trace distance is $\delta_D\le\delta$ (partial trace contracts $\|\cdot\|_1$, D2.5.3). The bound $f(\delta)=2\delta\log d_D+(1+\delta)h(\tfrac\delta{1+\delta})$ is nondecreasing: $\tfrac{d}{d\delta}[(1+\delta)h(\tfrac\delta{1+\delta})]=\log\tfrac{1+\delta}\delta>0$ (since $(1+\delta)h(\tfrac\delta{1+\delta})=(1+\delta)\log(1+\delta)-\delta\log\delta$). So $|S(D)_\rho-S(D)_\sigma|\le f(\delta)$, likewise $\le C\sqrt\delta\log(ed_D)$. $I(D:E)=S(D)-S(D|E)$ gives $|I(D:E)_\rho-I(D:E)_\sigma|\le2f(\delta)\le2C\sqrt\delta\log(ed_D)$. No $\dim E$.

**Output.** (a) Entropy and mutual-information transfer between $\Omega$ and a nearby state, cost $C\sqrt\delta\log(ed_D)$, where $D$ is the *small* system: used in §5 (`04-conditional.tex:270`, "using only $\dim x$"), §9 (`08-scanner.tex:403`, `938`: $O(n^2)$ sites, $\delta=O(n^{-500})$), §10 (`09-amplification.tex:551`, $\log\dim e'=|X|\log q\le Cn^2$). (b) Usage rule D2.5.
**Standard?** Standard. Alicki–Fannes, J. Phys. A 37 (2004); Winter, Commun. Math. Phys. 347 (2016), Thm 1 and Lemma 2: $|S(A|B)_\rho-S(A|B)_\sigma|\le2\delta\log d_A+(1+\delta)h(\tfrac\delta{1+\delta})$.
**Pitfall.** The controlled (small) system must be the *first* argument. $S(E|D)$ would cost $\log\dim E$. The mutual information is symmetric, so one picks which side to condition on. $C$ in the second inequality is absolute (D2.4.4).

---

#### D2.5 Step — Pure-state trace distance; usage rule for Lemma 2.1
Lines 74–78.

**Statement.** For unit vectors $\xi,\eta$: $\tfrac12\|\,|\xi\rangle\langle\xi|-|\eta\rangle\langle\eta|\,\|_1\le\|\xi-\eta\|$. Lemma 2.1 is applied (i) on regions with a controlled number of sites, or (ii) with the controlled region as the first argument of a conditional entropy, so that estimates never acquire the dimension of an uncontrolled complement.

**Used from.** D2.4.
**Proof.**
- D2.5.1 $\tfrac12\|\,|\xi\rangle\langle\xi|-|\eta\rangle\langle\eta|\,\|_1=\sqrt{1-|\langle\xi,\eta\rangle|^2}$: the difference is traceless, rank two, Hermitian, so its eigenvalues are $\pm\lambda$ with $\lambda^2=\tfrac12\operatorname{Tr}(\cdot)^2=1-|\langle\xi,\eta\rangle|^2$; trace norm $=2\lambda$.
- D2.5.2 With $x=|\langle\xi,\eta\rangle|\in[0,1]$: $1-x^2=(1-x)(1+x)\le2(1-x)\le2-2\operatorname{Re}\langle\xi,\eta\rangle=\|\xi-\eta\|^2$.
- D2.5.3 Partial traces do not increase trace distance, so the bound passes to every reduced state.

**Output.** $\delta\le\|\xi-\eta\|$ for the reductions of any two unit vectors to the same subsystem. §4 (`03-quasilocal.tex:499`) restates the equality in D2.5.1.
**Standard?** Standard (exact formula: Nielsen–Chuang, Ch. 9). D2.5.2–3 are expansions; the paper states the bound without proof.

---

#### D2.6 Def — Balls, graph neighborhoods, ambient dilations
Lines 82–92.

**Statement.** $B_\Lambda(x,r)=\{y\in\Lambda:d_\Lambda(x,y)\le r\}$. For $D\subseteq\Lambda$: $N^\Lambda_r(D)=\{x:d_\Lambda(x,D)\le r\}$. For finite $T\subset\mathbb Z^2$ and integer $j\ge0$, the ambient dilation is $T_j=T+([-j,j]^2\cap\mathbb Z^2)$. Graph neighborhoods are reserved for support and propagation estimates; $T_j$ is a different object (an $\ell^\infty$-box sum in $\mathbb Z^2$, not cut to $\Lambda$ and not using $d_\Lambda$).

**Used from.** §1: $d_\Lambda$.
**Output.** $B_\Lambda$, $N_r^\Lambda$ (written $N_r$ in §10, `09-amplification.tex:30`: $N_r(S)=N_r^\Lambda(S)$); $T_j$ in §3 (`02-initial.tex:579`, nested $T_j$).
**Standard?** Notation.
**Pitfall.** $N_r^\Lambda(D)$ and $T_j$ are not interchangeable. $d_\Lambda=+\infty$ between components, so $N_r^\Lambda(D)$ stays inside the components meeting $D$; holes only lengthen $d_\Lambda$.

---

#### D2.7 Step eq:ball-count — Ball cardinality
Lines 85–87.

**Statement.** For every site $x\in\Lambda$ and integer $r\ge0$: $|B_\Lambda(x,r)|\le v_r:=1+2r(r+1)$.

**Used from.** D2.6.
**Proof.**
- D2.7.1 A graph path of length $\le r$ changes the coordinates by $|\cdot|_1\le1$ per edge, so $y\in B_\Lambda(x,r)\Rightarrow|y-x|_1\le r$.
- D2.7.2 $|\{z\in\mathbb Z^2:|z|_1\le r\}|=1+\sum_{k=1}^r4k=1+2r(r+1)$ (the sphere $|z|_1=k$ has $4k$ points).

**Output.** $v_r$; used with $r=R$ in D2.8, D2.9, in §4 (`03-quasilocal.tex:31–37`: $|X_i|\le v_R$) and with general radii in §4 (`03-quasilocal.tex:461`: $\le C\mu_R|S_0|(d+1)^2$ labels at distance $d$; `515`: "at most $C(r_0+1)^2$ sites in each such ball").
**Standard?** Elementary counting.
**Pitfall.** $r$ must be an integer for the closed form; it is only an upper bound, since holes in $\Lambda$ shrink balls.

---

#### D2.8 Step — Term multiplicity and norm budget per site
Lines 94–103.

**Statement.** Assign to each nonzero interaction (support) $X$ in eq:hamiltonian an *anchor* in $X$. Put $\mu_R:=2^{v_R-1}$. Then for every $x\in\Lambda$:
- $\#\{X:x\in X,\ X\text{ a summand of }H\}\le\mu_R$;
- $\#\{X\text{ anchored at }x\}\le\mu_R$;
- $\sum_{X\ni x}\|h_X\|\le J\mu_R$;
- $|X|\le v_R$ for every support $X$ (consequence, D2.8.4).

Terms whose operator is a scalar multiple of the identity obey the same bounds with their assigned supports.

**Used from.** D2.7; §1 eq:hamiltonian.
**Proof.**
- D2.8.1 If $x\in X$ and $\operatorname{diam}_{d_\Lambda}X\le R$ then every $y\in X$ has $d_\Lambda(x,y)\le R$, so $X\subseteq B_\Lambda(x,R)$.
- D2.8.2 Such $X$ is a subset of $B_\Lambda(x,R)$ containing $x$. There are $2^{|B_\Lambda(x,R)|-1}\le2^{v_R-1}=\mu_R$ of them (D2.7).
- D2.8.3 Anchored at $x$ implies containing $x$. Each support appears once (§1), each $\|h_X\|\le J$, so $\sum_{X\ni x}\|h_X\|\le J\cdot\#\{X\ni x\}\le J\mu_R$.
- D2.8.4 By D2.8.1 with any $x\in X$: $|X|\le|B_\Lambda(x,R)|\le v_R$.

**Output.** $b_0:=J\mu_R$ in eq:quasilocal-budget (`03-quasilocal.tex:36`); $|X_i|\le v_R$; "at most $\mu_R$ labels with any specified anchor" (`03-quasilocal.tex:33, 462, 515`); the bound $\mathcal B\le C(1+|\partial_\Lambda B|)$ in §3 (`02-initial.tex:203–207`).
**Standard?** Specific to this paper (indexing by supports, one summand per support).
**Pitfall.** Terms are indexed by the support *set* $X$, not by the minimal support of the operator $h_X$. A zero or scalar $h_X$ still has its assigned support. The count $\mu_R$ is therefore over index sets and holds regardless of the operator values; this is why the budget depends on $R,J$ alone.

---

#### D2.9 Step eq:crossing-count — Terms split by a set
Lines 105–113.

**Statement.** Call an assigned support $X$ *split* by $D\subseteq\Lambda$ if $X\cap D\ne\varnothing\ne X\setminus D$. Then
$$\#\{\text{terms split by }D\}\le2v_R\mu_R\,|\partial_\Lambda D|.$$

**Used from.** D2.6, D2.7, D2.8.
**Proof.**
- D2.9.1 Let $a$ be the anchor of a split $X$. There is $y\in X$ on the opposite side of $D$ from $a$ ($y\in X\setminus D$ if $a\in D$, $y\in X\cap D$ otherwise), with $d_\Lambda(a,y)\le R$ (diameter, D2.8.1).
- D2.9.2 A shortest $\Lambda$-path $a\to y$ has length $\le R$ and starts and ends on different sides of $D$. It therefore contains an edge $\{z,z'\}$ with $z\in D$, $z'\in\Lambda\setminus D$, i.e. an edge of $\partial_\Lambda D$.
- D2.9.3 Hence $a$ lies within graph distance $R$ of an endpoint of an edge of $\partial_\Lambda D$: $a\in B_\Lambda(z,R)$ for one of the $\le2|\partial_\Lambda D|$ endpoints $z$.
- D2.9.4 Anchors available: $\le2|\partial_\Lambda D|\cdot v_R$ (D2.7). Terms per anchor: $\le\mu_R$ (D2.8). Multiply.

**Output.** Term count across any cut; the same argument with radius $r_0$ and modified supports is redone in §4 (`03-quasilocal.tex:510–517`: "at most $2b_X$ endpoints, $C(r_0+1)^2$ sites per ball, $\mu_R$ labels per anchor").
**Standard?** Specific to this paper (finite-range counting).
**Pitfall.** The count is in $|\partial_\Lambda D|$, the edge boundary of the induced graph. Anchors may lie on either side of $D$, at distance up to $R$ from the cut, which is why a ball of radius $R$ around each endpoint is used.

---

#### D2.10 Step — Product decomposition across a bipartition
Lines 114–116.

**Statement.** For a bipartition of $\Lambda$ and a term $h_X$, matrix units on its finite support give a decomposition of $h_X$ into a bounded number of product operators (one factor on each side) with bounded factors. For the original interactions the bounds depend only on $q,R,J$.

**Used from.** D2.8 ($|X|\le v_R$, D2.8.4).
**Proof (expansion; the paper states only "bounded").**
- D2.10.1 Split $X=X_1\sqcup X_2$ along the bipartition. Expand $h_X$ in the matrix-unit basis of $\operatorname{End}(\mathcal H_{X_1})\otimes\operatorname{End}(\mathcal H_{X_2})$: $h_X=\sum c_{ijkl}\,E_{ij}\otimes E_{kl}$, $c_{ijkl}=\langle i,k|h_X|j,l\rangle$.
- D2.10.2 Number of summands $\le q^{2|X|}\le q^{2v_R}$. $|c_{ijkl}|\le\|h_X\|\le J$. $\|E_{ij}\|=\|E_{kl}\|=1$.

**Output.** Constants of this decomposition depend on $(q,R,J)$ only. Not used elsewhere inside §2.
**Standard?** Standard linear algebra.
**Pitfall.** "For the original interactions": after the modifications of §4 (supports enlarged to $\widetilde X_i$) the bounds change, see `03-quasilocal.tex:515–517` ($\log d_i\le C(r_0+1)^2$).

---

#### D2.11 Step — Degenerate cases
Lines 118–121.

**Statement.** If $q=1$ or $\Lambda=\varnothing$: all entropies vanish. If $R=0$: $H$ is a sum of on-site operators; uniqueness of its ground state makes $\Omega$ a tensor product, so $S_\Omega(A)=0$ and Theorem 1.1 holds. Henceforth $q\ge2$, $R\ge1$, $\Lambda\ne\varnothing$.

**Used from.** §1 Theorem 1.1 (`thm:area`).
**Proof.**
- D2.11.1 $q=1$ or $\Lambda=\varnothing$: $\mathcal H_\Lambda=\mathbb C$, the only state is pure, every $\rho_A$ is pure.
- D2.11.2 $R=0$: the only $X$ with $\operatorname{diam}X\le0$ are singletons, so $H=\sum_xh_{\{x\}}$, a sum of commuting operators on distinct tensor factors. The ground eigenspace is $\bigotimes_x\ker(h_{\{x\}}-e_x)$ ($e_x=\min\operatorname{spec}h_{\{x\}}$). A one-dimensional ground eigenspace forces each factor to be one-dimensional. So $\Omega=\bigotimes_x\omega_x$ (up to phase), $\rho_A$ pure, $S_\Omega(A)=0\le C|\partial_\Lambda A|$.

**Output.** Standing assumptions $q\ge2$, $R\ge1$, $\Lambda\neq\varnothing$ in §3–§11. Emptiness of $A$ or $\Lambda\setminus A$ is treated in the proof of Theorem 1.1 (`10-geometry.tex:804`).
**Standard?** Specific bookkeeping.
**Pitfall.** The $R=0$ case uses uniqueness, not the gap.

---

#### D2.12 Lemma 2.2 — A cut with no crossing edge
Lines 123–133. Label `lem:zero-boundary`.

**Statement.** Under the hypotheses of Theorem 1.1 ($H$ admissible, unique normalized ground vector $\Omega$ up to phase, gap $\Delta$), if $A\subseteq\Lambda$ and $\partial_\Lambda A=\varnothing$, then $S_\Omega(A)=0$.

**Used from.** §1: eq:hamiltonian (finite $R$, supports), Theorem 1.1 uniqueness of $\Omega$.
**Proof.**
- D2.12.1 No edge between $A$ and $\Lambda\setminus A$ $\Rightarrow$ $A$ is a union of connected components of the induced graph.
- D2.12.2 Every support $X$ has finite $d_\Lambda$-diameter ($\le R$), and $d_\Lambda=\infty$ across components, so $X$ lies in a single component $c$.
- D2.12.3 Hence $H=\sum_cH_c$, $H_c=\sum_{X\subseteq c}h_X$ acting on $\mathcal H_c$ and as the identity elsewhere ("tensor sum").
- D2.12.4 For such a sum, $E_0=\sum_cE_0^c$ and the ground eigenspace is $\bigotimes_c\ker(H_c-E^c_0)$.
- D2.12.5 This space is one-dimensional, so each factor is one-dimensional: $\Omega=\bigotimes_c\Omega_c$ up to phase.
- D2.12.6 $A$ is a union of components, so $\Omega=\Omega_A\otimes\Omega_{\Lambda\setminus A}$. $\rho_A$ is pure, $S_\Omega(A)=0$.

**Output.** $b=0$ case of the proof of Theorem 1.1 (`10-geometry.tex:806`).
**Standard?** Specific to this paper (uses the induced-graph convention of §1).
**Pitfall.** Only uniqueness is used; the gap plays no role.

---

#### D2.13 Def — Convention for constants $C,c$
Lines 135–139.

**Statement.** $C,c>0$ may change from line to line. Unless a lemma specifies more fixed data, they depend only on $q,R,J,\Delta$ and never on the domain $\Lambda$, the cut $A$, or the particular Hamiltonian. Additional numerical exponents and sufficiently large thresholds are fixed in the order stated in the proof.

**Used from.** §1 Theorem 1.1: $C=C(q,R,J,\Delta)$.
**Output.** Uniformity requirement in Theorem 1.1 (same $C$ for all domains, sets, Hamiltonians); the order-of-choice rule for exponents $\alpha,\varepsilon,\dots$ and thresholds $n_*$ in §3–§11 (`10-geometry.tex:808`: "Choose $n_*$ large enough…").
**Standard?** Convention.
**Pitfall.** Constants of Lemma 2.1 are absolute (D2.4). $v_R,\mu_R,2v_R\mu_R$ depend on $R$ only, $J\mu_R$ on $R,J$, D2.10 on $q,R,J$.

---

## Parameters and constants

| Symbol | Value / meaning | Fixed in |
|---|---|---|
| $q\ge1$, $R\ge0$, $J>0$, $\Delta>0$ | on-site dimension, interaction range (graph diameter), norm bound, gap | §1 (eq:hamiltonian, Thm 1.1); reduced to $q\ge2,R\ge1$ in D2.11 |
| $h(u)$ | $-u\log u-(1-u)\log(1-u)$ | D2.3 |
| $\delta$ | $\tfrac12\|\rho-\sigma\|_1\in[0,1]$ | D2.4 |
| $d_D$ | $\dim D$ | D2.4 |
| $C$ in eq:conditional-continuity | absolute; $2(1+2/e)$ works | D2.4.4 |
| $C_h$ | $1+2/e$, $h(u)\le C_h\sqrt u$ | D2.4.4 (expansion) |
| $v_r$ | $1+2r(r+1)$, bound on $|B_\Lambda(x,r)|$ | D2.7 |
| $\mu_R$ | $2^{v_R-1}$, terms through a site | D2.8 |
| $J\mu_R$ | norm budget per site ($=b_0$ in §4) | D2.8 |
| $2v_R\mu_R$ | split-term constant (times $|\partial_\Lambda D|$) | D2.9 |
| $q^{2v_R}$, $J$ | number of product terms / coefficient bound in D2.10 | D2.10 (expansion) |
| $C,c$ | generic, depend on $q,R,J,\Delta$ only | D2.13 |
| exponents, thresholds | none fixed in §2; fixed later in the order of the proof | D2.13 |

## Dependencies

**Consumes.**
- §1: $\Lambda$, $d_\Lambda$, eq:hamiltonian, $\partial_\Lambda$, $S_\Omega$, Theorem 1.1 hypotheses.
- External: strong subadditivity (Lieb–Ruskai 1973); Alicki–Fannes 2004; Winter 2016 (Thm 1, Lemma 2).

**Exports.**
- D2.1–D2.3 (notation, SSA consequences): §5 onward.
- D2.4 Lemma 2.1: §5 (`04-conditional.tex:270`), §9 (`08-scanner.tex:403, 938`), §10 (`09-amplification.tex:551`).
- D2.5 pure-state trace distance: §4 (`03-quasilocal.tex:499`).
- D2.7 and D2.8 ($v_R$, $\mu_R$, $b_0=J\mu_R$, $|X_i|\le v_R$): §3 (`02-initial.tex:203`), §4 (`03-quasilocal.tex:31–37, 461–463, 515`).
- D2.9 crossing count: model for the radius-$r_0$ count in §4.
- D2.11 standing assumptions: §3–§11.
- D2.12 Lemma 2.2: §11 (`10-geometry.tex:806`).
- D2.13 constants convention: all sections.
