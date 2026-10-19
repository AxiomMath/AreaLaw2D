# Digest of §4 — Positive constraints and truncation near a finite set

Source: `paper/sections/03-quasilocal.tex` (lines 1–534). Label `sec:quasilocal`. Numbering: Lemma 4.1, Lemma 4.2, Proposition 4.3, Lemma 4.4, Proposition 4.5 (one shared counter; the file has no Definition/Remark environments).

## Section in one paragraph

$H=\sum_i h_i$ has a global gap $\Delta$ above a ground vector $\Omega$ but its terms $h_i$ do not annihilate $\Omega$. §4 builds two replacements using only the gap of the full $H$. (a) Exact: positive contractions $k_i$ with $k_i\Omega=0$, $\sum_i k_i\ge g(I-P_\Omega)$, and tails $\|k_i-E_{i,l}(k_i)\|\le Ce^{-cl^\alpha}$, $\alpha=p/(p+1)$ for any integer $p\ge1$, plus unital channels built from $\sqrt{k_i},\sqrt{I-k_i}$ with the same tails. (b) Truncated: for $p=1$ and a finite set $S_0$ with $|S_0|\le C_0n^2$, constraints near $S_0$ are cut to graph balls of radius $\sim(\log n)^2$, farther ones to radius $\sim d(a_i,S_0)/2$; total error is $n^{-1000}$ with no dependence on $|\Lambda|$, the truncated $\widetilde H$ keeps gap $\ge g/2$, and constraints crossing a cut $\partial X$, $X\subseteq S_0$, are counted by $|\partial_\Lambda X|(\log n)^4$. Order: ball setup and counting (D4.1–D4.3) → Lieb–Robinson in graph metric (D4.4) → compactly supported filter with stretched-exponential kernel (D4.5) → Kitaev centered filter, absolute value, locality (D4.6–D4.9) → square roots and channels (D4.10) → truncation (D4.11–D4.15). Consumers: (a) feeds the contraction products of §10 (amplification); (b) feeds the transport/scanner/comparator machinery of §7–§9 through $\widetilde g$, $\widetilde E_0$, $\|\widetilde\Omega-\Omega\|$ and the cut parameter $\mathcal B_X$.

Notation (from §2 unless stated). $\Lambda$ finite, $d_\Lambda$ graph metric of the induced graph ($=\infty$ across components). Distinct nonempty designated supports $X_i$, $i\in\mathcal I$, $h_i$ supported in $X_i$, $\|h_i\|\le J$, $\operatorname{diam}_{d_\Lambda}X_i\le R$, local dimension $q$. $v_r=1+2r(r+1)$ bounds $|B_\Lambda(x,r)|$ (`eq:ball-count`); $\mu_R=2^{v_R-1}$ bounds supports through a site. $P_\Omega=|\Omega\rangle\langle\Omega|$. $\tau_t(B)=e^{itH}Be^{-itH}$.

---

### 4.0 Setup

#### D4.1 Def — Anchored decomposition and graph balls
*Source: 03-quasilocal.tex 14–18.*

**Statement.** $H=\sum_{i\in\mathcal I}h_i$, $i$ indexing the distinct nonempty designated supports $X_i$. Fix anchor $a_i\in X_i$. Graph ball $N_l(a)=\{x\in\Lambda:d_\Lambda(a,x)\le l\}$, integer $l\ge0$. Hence $\operatorname{diam}_{d_\Lambda}X_i\le R$, $\|h_i\|\le J$, and $X_i\subseteq N_R(a_i)$.

**Used from.** §2 (Hamiltonian, `eq:hamiltonian`, anchor assignment, §2 "Local counting").

**Output.** Index set, anchors and balls used in every later anchor. $N_l$ is a graph neighbourhood; ambient dilations $T_j$ of §2 are a different object.

**Standard?** Notation.

#### D4.2 Def — Conditional expectation onto a ball, $E_{i,l}$
*Source: 03-quasilocal.tex 18–29, `eq:quasilocal-ce`.*

**Statement.** With $Y=\Lambda\setminus N_l(a_i)$,
$$E_{i,l}(B)=q^{-|Y|}\operatorname{Tr}_Y(B)\otimes I_Y .$$
Tensor factors sit at their original sites. Equivalently $E_{i,l}=\prod_{y\in Y}T_y$ with $T_y(B)=\int U_yBU_y^*\,dU_y$ (Haar, on-site unitaries). $E_{i,l}$ is positive, unital, contractive in operator norm, and fixes every operator supported in $N_l(a_i)$. Its range is the algebra on $N_l(a_i)$ (tensor $I_Y$).

**Used from.** D4.1.

**Output.** Defines $k_{i,l}=E_{i,l}(k_i)$ (D4.6), used by D4.10, D4.11. Positivity+unitality give $0\le B\le I\Rightarrow0\le E_{i,l}B\le I$. The $T_y$ form is used in D4.4.9.

**Standard?** Standard (partial trace / twirl identity; normalized partial trace is the Haar average over the unitary group of the traced factor).

#### D4.3 Step — Counting budget
*Source: 03-quasilocal.tex 31–41, `eq:quasilocal-budget`.*

**Statement.**
$$\sup_{x\in\Lambda}\sum_{i:x\in X_i}\|h_i\|\le b_0:=J\mu_R,\qquad |X_i|\le v_R .$$
Also: at most $\mu_R$ labels share any given anchor. All constants in §4 are independent of $\Lambda$ and may depend on $q,R,J,\Delta$ and explicitly fixed exponents or size bounds.

**Used from.** D4.1; §2 `eq:ball-count`, $\mu_R$ definition (each support through $x$ is a subset of $N_R(x)$ containing $x$; $N_R(x)$ has $\le v_R$ points, so $\le2^{v_R-1}$ such subsets).

**Proof.**
- D4.3.1 $X_i\subseteq N_R(a_i)$ since $a_i\in X_i$ and $\operatorname{diam}X_i\le R$ $\Rightarrow$ $|X_i|\le v_R$.
- D4.3.2 Supports through $x$: $\le\mu_R$, each $\|h_i\|\le J$ $\Rightarrow$ sum $\le J\mu_R=b_0$.
- D4.3.3 Labels with anchor $a$: supports containing $a$ $\Rightarrow$ $\le\mu_R$.

**Output.** $\kappa:=v_Rb_0$ in D4.4. $\mu_R$ (labels per anchor) in D4.12, D4.14.

**Standard?** Specific bookkeeping; §2 gives the counts.

---

### 4.1 Propagation and the spectral filter

#### D4.4 Lemma 4.1 — Graph-distance propagation
*Source: 03-quasilocal.tex 52–128; equations `eq:quasilocal-lr` (57–61), `eq:quasilocal-lr-ce` (63–67), `eq:quasilocal-lr-recursion` (87–92).*

**Statement.** There are $C,v,c>0$ (depending on $q,R,J$) such that for every label $i$, every $A$ supported in $X_i$, every site $y$, every operator $B_y$ on site $y$, every $t\in\mathbb R$:
$$\|[\tau_t(A),B_y]\|\le C\|A\|\|B_y\|e^{v|t|-c\,d_\Lambda(a_i,y)},\tag{`eq:quasilocal-lr`}$$
and the commutator is $0$ if $d_\Lambda(a_i,y)=\infty$. Moreover, for every integer $l\ge0$,
$$\|\tau_t(A)-E_{i,l}(\tau_t(A))\|\le\|A\|\min\{2,\ Ce^{v|t|-cl}\}.\tag{`eq:quasilocal-lr-ce`}$$
(The constants $C,c$ in the second line are renamed from the first.)

**Used from.** D4.1, D4.2, D4.3; §2 `eq:ball-count` ($|\{x:d_\Lambda(a,x)=d\}|\le v_d\le3(d+1)^2$).

**Proof.**
- D4.4.1 *Quantity.* Fix $y$, $B_y$. For any set $X$: $F(X,t)=\sup\{\|[\tau_t(A),B_y]\|:\operatorname{supp}A\subseteq X,\|A\|\le1\}$. Trivially $F\le2\|B_y\|$. Take $t\ge0$ (for $t<0$ replace $H\to-H$; same norms).
- D4.4.2 *Exact ODE.* Fix $A$ on $X$. $\mathcal J_X=\{j:X_j\cap X\ne\varnothing\}$, $Q_X(t)=\sum_{j\in\mathcal J_X}\tau_t(h_j)$. Terms with $j\notin\mathcal J_X$ commute with $A$, so $\partial_t\tau_t(A)=i\tau_t([H,A])=i[Q_X(t),\tau_t(A)]$. With $f(t)=[\tau_t(A),B_y]$ and $[[Q,T],B]=[Q,[T,B]]-[T,[Q,B]]$:
$$f'=i[Q_X,f]-i\sum_{j\in\mathcal J_X}[\tau_t(A),[\tau_t(h_j),B_y]].$$
- D4.4.3 *Duhamel.* The homogeneous flow $g\mapsto W(t,u)gW(t,u)^*$ with $W$ unitary ($\partial_tW=iQ_XW$) is norm-preserving. So $\|f(t)\|\le\|f(0)\|+\sum_{j\in\mathcal J_X}\int_0^t\|[\tau_u(A),[\tau_u(h_j),B_y]]\|du$.
- D4.4.4 *Estimate terms.* $f(0)=[A,B_y]$ has norm $\le2\|B_y\|\mathbf 1_{\{y\in X\}}$ (zero if $y\notin X$). $\|[\tau_u(A),[\tau_u(h_j),B_y]]\|\le2\|A\|\,\|[\tau_u(h_j),B_y]\|\le2\|h_j\|F(X_j,u)$ for $\|A\|\le1$. Sup over $A$:
$$F(X,t)\le2\|B_y\|\mathbf 1_{\{y\in X\}}+2\sum_{j\in\mathcal J_X}\|h_j\|\int_0^tF(X_j,u)\,du.\tag{`eq:quasilocal-lr-recursion`}$$
- D4.4.5 *Iterate from $X=X_i$.* Sum of available norms per step: $\sum_{j\in\mathcal J_X}\|h_j\|\le\sum_{x\in X}\sum_{j:x\in X_j}\|h_j\|\le|X|b_0\le v_Rb_0=:\kappa$ (D4.3; $X=X_{j}$ has $|X|\le v_R$). Simplex volume of $m$ nested integrals on $[0,t]$ is $t^m/m!$. After $M$ iterations the remainder is $\le2\|B_y\|(2\kappa t)^M/M!\to0$ (uses $F\le2\|B_y\|$).
- D4.4.6 *Chain sum.* The $m$-th term is nonzero only for a chain $X_i,X_{j_1},\dots,X_{j_m}$ with consecutive supports intersecting and $y\in X_{j_m}$. Then $d_\Lambda(a_i,y)\le(m+1)R$ (each support has diameter $\le R$, consecutive ones overlap). Hence
$$F(X_i,t)\le2\|B_y\|\sum_{m\ge0}\frac{(2\kappa t)^m}{m!}\mathbf 1_{\{d_\Lambda(a_i,y)\le(m+1)R\}}.$$
- D4.4.7 *Exponentiate.* For any $\mu>0$: $\mathbf 1_{\{d\le(m+1)R\}}\le e^{\mu((m+1)R-d)}$. So $F(X_i,t)\le2\|B_y\|e^{\mu R-\mu d_\Lambda(a_i,y)}\exp(2\kappa e^{\mu R}t)$. This is `eq:quasilocal-lr` with $c=\mu$, $v=2\kappa e^{cR}$, $C=2e^{cR}$ (times $\|A\|$ by homogeneity).
- D4.4.8 *Infinite distance.* No finite chain from $X_i$ reaches $y$, every term vanishes, remainder $\to0$ $\Rightarrow F=0$.
- D4.4.9 *Twirl telescoping.* $E_{i,l}=\prod_{y\in Y}T_y$, $Y=\Lambda\setminus N_l(a_i)$, each $T_y$ a contraction. For contractions, $B-T_1\cdots T_nB=\sum_kT_1\cdots T_{k-1}(B-T_kB)$, so $\|B-E_{i,l}B\|\le\sum_{y\in Y}\|B-T_yB\|$. And $\|B-T_yB\|\le\sup_{U_y}\|B-U_yBU_y^*\|=\sup_{U_y}\|[B,U_y]\|$.
- D4.4.10 *Sum.* Put $B=\tau_t(A)$, $B_y=U_y$ ($\|U_y\|=1$) in `eq:quasilocal-lr`; other components give $0$. Sites at distance exactly $d$ number $\le v_d\le3(d+1)^2$. $\sum_{d>l}3(d+1)^2e^{-cd}\le C'e^{-c'l}$ ($c'<c$, e.g. $c/2$). Gives $\|A\|Ce^{v|t|-c'l}$ after renaming.
- D4.4.11 *The 2.* $\|B-E_{i,l}B\|\le\|B\|+\|E_{i,l}B\|\le2\|A\|$ (contractivity, $\|\tau_t(A)\|=\|A\|$).

**Output.** `eq:quasilocal-lr-ce` with $A=h_i$ feeds D4.8 (locality of $M_i$). `eq:quasilocal-lr` is not used outside §4 in this form.

**Standard?** Standard: Lieb–Robinson bound by commutator iteration, Nachtergaele–Ogata–Sims (J. Stat. Phys. 124 (2006)); Lieb–Robinson (CMP 28 (1972)). Specific here: metric is $d_\Lambda$ (holes, components harmless) and anchors/original supports are the base of the iteration.

**Pitfall.** $c>0$ is free; $v$ depends on it ($v=2v_RJ\mu_Re^{cR}$ with $c=\mu$). Fixing $c$ first fixes $v$. D4.8 needs $v$ and $c$ simultaneously to choose the time cutoff $\varepsilon$.

#### D4.5 Lemma 4.2 — A compactly supported spectral filter
*Source: 03-quasilocal.tex 135–201; `eq:quasilocal-gevrey` (180–183), `eq:quasilocal-filter-decay` (152–156).*

**Statement.** Fix integer $p\ge1$, $\alpha=p/(p+1)$, $\delta>0$. Define the real even function
$$\chi(\omega)=\begin{cases}e\exp[-(1-(\omega/\delta)^2)^{-p}],&|\omega|<\delta,\\0,&|\omega|\ge\delta.\end{cases}$$
Then $\chi\in C_c^\infty(\mathbb R)$, $\chi(0)=1$, and $f(t)=\frac1{2\pi}\int\chi(\omega)e^{-it\omega}d\omega$ is real, even, with
$$\chi(\omega)=\int_{\mathbb R}f(t)e^{it\omega}dt,\qquad|f(t)|\le Ce^{-c|t|^\alpha},$$
$C,c>0$ depending only on $p,\delta$. In particular $f\in L^1$ and $\int f=\chi(0)=1$.

**Used from.** Nothing in the paper.

**Proof.**
- D4.5.1 *Value.* $\chi(0)=e\cdot e^{-1}=1$. Real, even, supported in $[-\delta,\delta]$ by definition. Write $\varphi(u)=e\exp[-(1-u^2)^{-p}]$ on $(-1,1)$, $w=1-u^2$, so $\chi(\omega)=\varphi(\omega/\delta)$.
- D4.5.2 *Complex disk.* For $u\in(-1,1)$ and $|z-u|\le\eta_pw$, $\eta_p\le1$: $1-z^2=w-2u(z-u)-(z-u)^2=w(1+\zeta)$ with $|\zeta|\le2\eta_p+\eta_p^2\le3\eta_p$ (use $|u|\le1$, $w\le1$). Choose $\eta_p$ so small that $\operatorname{Re}(1+\zeta)^{-p}\ge c_p>0$ for $|\zeta|\le3\eta_p$ (continuity at $\zeta=0$, where the value is $1$). Then $\operatorname{Re}(1-z^2)^{-p}\ge c_pw^{-p}$, so $|\varphi(z)|\le e\,e^{-c_pw^{-p}}$ on the disk.
- D4.5.3 *Cauchy.* $|\varphi^{(m)}(u)|\le m!\,(\eta_pw)^{-m}\sup|\varphi|\le Cm!\,\eta_p^{-m}w^{-m}e^{-c_pw^{-p}}$.
- D4.5.4 *Smooth extension.* For fixed $m$, $w^{-m}e^{-c_pw^{-p}}\to0$ as $u\to\pm1$. So all derivatives of $\varphi$ tend to $0$ at $\pm1$ and the zero extension is $C^\infty$.
- D4.5.5 *Uniformity in $u$.* Put $s=w^{-p}\ge1$, $w^{-m}=s^{m/p}$. $\sup_{s>0}s^{m/p}e^{-c_ps}=(m/(pc_pe))^{m/p}\le C^{m}(m^m)^{1/p}\le C^m(e^mm!)^{1/p}$, using $m!\ge(m/e)^m$. So $\|\varphi^{(m)}\|_\infty\le C^{m+1}(m!)^{1+1/p}$ ($m=0$ absorbed in $C$).
- D4.5.6 *Gevrey bound.* $\chi^{(m)}(\omega)=\delta^{-m}\varphi^{(m)}(\omega/\delta)$:
$$\|\chi^{(m)}\|_\infty\le C_1^{m+1}(m!)^{1+1/p}.\tag{`eq:quasilocal-gevrey`}$$
- D4.5.7 *Integration by parts.* $\chi\in C_c^\infty$: no boundary terms, $\int\chi e^{-it\omega}d\omega=(it)^{-m}\int\chi^{(m)}e^{-it\omega}d\omega$. Support length $2\delta$:
$$|f(t)|\le C\frac{C_1^m(m!)^{1+1/p}}{|t|^m}\le C\Big(\frac{C_1m^{1+1/p}}{|t|}\Big)^m\quad(t\neq0,\ m!\le m^m).$$
- D4.5.8 *Optimize $m$.* $m=\lfloor\eta|t|^{p/(p+1)}\rfloor$ gives $m^{(p+1)/p}\le\eta^{(p+1)/p}|t|$, so the bracket is $\le C_1\eta^{(p+1)/p}\le\frac12$ for $\eta$ small and fixed. $|f(t)|\le C2^{-m}\le2C\,2^{-\eta|t|^\alpha}$, i.e. $c=\eta\ln2$. Bounded $|t|\le t_0$: $|f|\le\frac1{2\pi}\int\chi\le\delta/\pi$ ($0\le\chi\le1$), enlarge $C$.
- D4.5.9 *Inversion.* $f\in L^1$, $\chi$ continuous and in $L^1$: Fourier inversion gives $\chi(\omega)=\int f(t)e^{it\omega}dt$. (Alternative in paper: insert $e^{-\varepsilon t^2}$, swap integrals, Gaussian approximate identity.) Reality/evenness of $f$ from those of $\chi$.

**Output.** $f$ with $\|f\|_1<\infty$, $\int f=1$, $\hat f=\chi$ supported in $[-\delta,\delta]$ (used with $\delta=\Delta/2$ in D4.7), and the pointwise bound $|f(t)|\le Ce^{-c|t|^\alpha}$, integrated into a tail bound in D4.8.3.

**Standard?** Standard: Gevrey-class compactly supported bumps and the corresponding stretched-exponential Fourier decay, cf. Hörmander, *Linear Partial Differential Operators I*, §1.3 (Denjoy–Carleman classes). The explicit constants here are specific.

**Pitfall.** $\alpha=p/(p+1)<1$: the filter decays only stretched-exponentially. $C_1,\eta$ are internal to this proof; $C_1$ is reused with a different meaning in D4.11.

---

### 4.2 Exact positive constraints

#### D4.6 Proposition 4.3 — Positive replacement of the Hamiltonian
*Source: 03-quasilocal.tex 220–329 (statement 220–246, proof 248–329); `eq:quasilocal-positive` (230–236), `eq:quasilocal-positive-tail` (239–244).*

**Statement.** Suppose $H\Omega=E_0\Omega$, $\|\Omega\|=1$, $H-E_0I\ge\Delta(I-P_\Omega)$. For each integer $p\ge1$, $\alpha=p/(p+1)$, there are operators $k_i$ ($i\in\mathcal I$, anchors retained) and $c_*>0$ with
$$0\le k_i\le I,\quad k_i\Omega=0,\quad H_F:=\sum_ik_i\ge c_*^{-1}(H-E_0I)\ge g(I-P_\Omega),\quad g:=\Delta/c_*.$$
So $H_F$ has unique ground vector $\Omega$, ground energy $0$, gap $\ge g$. Furthermore
$$k_{i,l}:=E_{i,l}(k_i)\in[0,I],\qquad\|k_i-k_{i,l}\|\le Ce^{-cl^\alpha}\quad(l\in\mathbb Z_{\ge0}).$$
Each $k_i$ is supported in the connected component of $a_i$. $c_*,g$ depend on $p$ (not on $|\Lambda|$); $C,c$ depend on $p,q,R,J,\Delta$.

**Used from.** D4.2, D4.4, D4.5, D4.7, D4.8, D4.9.

**Proof.**
- D4.6.1 Filter with $\delta=\Delta/2$; define $M_i$ (D4.7). Get $M_i=M_i^*$, $M_i\Omega=0$, $\sum_iM_i=H-E_0I$, $\|M_i\|\le J(\|f\|_1+1)$.
- D4.6.2 $c_*:=\max\{1,J(\|f\|_1+1)\}$, $k_i:=|M_i|/c_*$. Then $\|k_i\|=\|M_i\|/c_*\le1$ and $k_i\ge0$ $\Rightarrow$ $0\le k_i\le I$.
- D4.6.3 $\ker|M_i|=\ker M_i$ ($\||M_i|\xi\|^2=\langle\xi,M_i^2\xi\rangle=\|M_i\xi\|^2$) $\Rightarrow$ $k_i\Omega=0$.
- D4.6.4 $|M_i|\ge M_i$ for Hermitian $M_i$, so $H_F\ge c_*^{-1}\sum M_i=c_*^{-1}(H-E_0I)\ge(\Delta/c_*)(I-P_\Omega)=g(I-P_\Omega)$.
- D4.6.5 Uniqueness: $H_F\ge0$, $H_F\Omega=0$, $H_F\ge g$ on $\Omega^\perp$ $\Rightarrow$ $\ker H_F=\mathbb C\Omega$, next eigenvalue $\ge g$.
- D4.6.6 Tail. D4.8: $\|M_i-E_{i,l}M_i\|\le Ce^{-cl^\alpha}$. D4.9 with $U=M_i^2$, $V=M'^2$, $M':=E_{i,l}M_i$ (Hermitian, $E_{i,l}$ positive): $\|M^2-M'^2\|=\|M(M-M')+(M-M')M'\|\le(\|M\|+\|M'\|)\|M-M'\|\le2c_*\|M_i-E_{i,l}M_i\|$ ($\|M\|\le c_*$, $\|M'\|\le\|M\|$ by contractivity). So $\||M_i|-|M'|\|\le(2c_*\|M_i-E_{i,l}M_i\|)^{1/2}\le Ce^{-cl^\alpha}$.
- D4.6.7 Locality of $E$-image. $M'=Z\otimes I_Y$ with $Z$ on $N_l(a_i)$, so $|M'|=|Z|\otimes I_Y$ is supported in $N_l(a_i)$ and $E_{i,l}|M'|=|M'|$. Contractivity: $\||M_i|-E_{i,l}|M_i|\|\le\||M_i|-|E_{i,l}M_i|\|+\|E_{i,l}(|E_{i,l}M_i|-|M_i|)\|\le2\||M_i|-|E_{i,l}M_i|\|$. Divide by $c_*$: `eq:quasilocal-positive-tail`.
- D4.6.8 Order: $0\le k_i\le I$ and $E_{i,l}$ positive unital $\Rightarrow$ $k_{i,l}\in[0,I]$.
- D4.6.9 Component: $H$ is a tensor sum over components; $\tau_t(h_i)$, the integral, the scalar centering and $|\cdot|$ stay in the algebra of the component of $a_i$.

**Output.** §10 (amplification) takes $k_i,k_{i,l},H_F,g,\alpha$ with $p$ fixed so that $\alpha>1-10^{-6}$ (`eq:amplification-positive-system`). Inside §4: D4.10 takes arbitrary $p$, D4.11 takes $p=1$. $g=\Delta/c_*$ enters D4.13.

**Standard?** Filter construction: Kitaev, Ann. Phys. 321 (2006), Appendix D.1.2, Prop. D.1. The absolute-value step (positive sum retaining a gap) and the locality estimate for $|M_i|$ via D4.9 are specific to this paper; the distinction filtered-constraint vs positive-sum-with-gap: Swingle–McGreevy (2016), §8.4.

**Pitfall.** $E_{i,l}$ does not preserve $k_i\Omega=0$: $k_{i,l}\Omega\ne0$ in general. All uses of $k_{i,l}$ must pay an error or move to the exact ground vector of the truncated sum (D4.11, D4.13). $c_*$ depends on $p$ through $\|f\|_1$; $g$ is fixed only after $p$.

#### D4.7 Step — Centered filtered terms $M_i$
*Source: 03-quasilocal.tex 249–270; `eq:quasilocal-centered-filter` (251–253), `eq:quasilocal-filter-sum` (262–266).*

**Statement.** With $f$ from D4.5 at $\delta=\Delta/2$,
$$M_i=\int_{\mathbb R}f(t)\tau_t(h_i)\,dt-\langle\Omega,h_i\Omega\rangle I .$$
The integral converges in norm; $M_i=M_i^*$; $M_i\Omega=0$; $\sum_iM_i=H-E_0I$; $\|M_i\|\le J(\|f\|_1+1)$.

**Used from.** D4.5; hypotheses of D4.6 (gap).

**Proof.**
- D4.7.1 Norm convergence: $\|\tau_t(h_i)\|=\|h_i\|\le J$, $f\in L^1$. Hermitian: $f$ real, $h_i=h_i^*$, $\tau_t$ a $*$-automorphism.
- D4.7.2 Eigenbasis of $H$: $\langle E|\int f\tau_t(h_i)|E'\rangle=\int f(t)e^{it(E-E')}dt\,\langle E|h_i|E'\rangle=\chi(E-E')\langle E|h_i|E'\rangle$.
- D4.7.3 Gap: $H-E_0\ge\Delta(I-P_\Omega)$ $\Rightarrow$ $\Omega$ is the unique ground vector, all other eigenvalues satisfy $E-E_0\ge\Delta>\delta=\Delta/2$, so $\chi(E-E_0)=0$.
- D4.7.4 Hence $\int f\tau_t(h_i)\,\Omega=\chi(0)\langle\Omega,h_i\Omega\rangle\Omega=\langle\Omega,h_i\Omega\rangle\Omega$ (only $E=E_0$ survives); the scalar centering cancels it: $M_i\Omega=0$.
- D4.7.5 $\sum_i\tau_t(h_i)=\tau_t(H)=H$ and $\int f=\chi(0)=1$, so $\sum_i\int f\tau_t(h_i)=H$; $\sum_i\langle\Omega,h_i\Omega\rangle=\langle\Omega,H\Omega\rangle=E_0$. Therefore $\sum_iM_i=H-E_0I$.
- D4.7.6 $\|M_i\|\le\|f\|_1J+|\langle\Omega,h_i\Omega\rangle|\le J(\|f\|_1+1)$.

**Output.** D4.6.1–D4.6.4, and the object whose locality D4.8 quantifies.

**Standard?** Standard (Kitaev 2006, App. D.1.2: centered filtered Hamiltonian terms).

#### D4.8 Step — Locality of $M_i$
*Source: 03-quasilocal.tex 272–286, `eq:quasilocal-filter-locality`.*

**Statement.** For $p\ge1$ and $l\in\mathbb Z_{\ge0}$,
$$\|M_i-E_{i,l}(M_i)\|\le C'e^{-c''l^\alpha},\qquad\alpha=p/(p+1).$$

**Used from.** D4.2, D4.4 (`eq:quasilocal-lr-ce`), D4.5.

**Proof.**
- D4.8.1 $E_{i,l}$ is linear, unital, contractive: it commutes with the Bochner integral and fixes the scalar. So $M_i-E_{i,l}M_i=\int f(t)\big(\tau_t(h_i)-E_{i,l}\tau_t(h_i)\big)dt$.
- D4.8.2 Choose $\varepsilon>0$ with $v\varepsilon<c/2$ ($v,c$ of D4.4). For $|t|\le\varepsilon l$, `eq:quasilocal-lr-ce` with $A=h_i$ gives integrand norm $\le JCe^{v\varepsilon l-cl}\le C e^{-c'l}$, $c'=c/2$. Contribution $\le Ce^{-c'l}\|f\|_1$.
- D4.8.3 For $|t|>\varepsilon l$: integrand norm $\le2J$. Let $C_f,c_f$ be the constants of $|f(t)|\le C_fe^{-c_f|t|^\alpha}$ (D4.5; not the $c$ of D4.4). Contribution $\le2J\int_{|t|>\varepsilon l}|f|\le2JC_f\int_{|t|>\varepsilon l}e^{-c_f|t|^\alpha}dt=\frac{4JC_f}{\alpha}\int_{(\varepsilon l)^\alpha}^\infty u^{1/\alpha-1}e^{-c_fu}du$ ($u=|t|^\alpha$, $dt=\alpha^{-1}u^{1/\alpha-1}du$, two signs of $t$). Absorb $u^{1/\alpha-1}\le C_\alpha e^{c_fu/2}$ $\Rightarrow$ $\le C'e^{-(c_f/2)(\varepsilon l)^\alpha}$.
- D4.8.4 $e^{-c'l}\le e^{-c'l^\alpha}$ for $l\ge1$ ($\alpha<1$). Total $\le C'e^{-c''l^\alpha}$, $c''=\min\{c',(c_f/2)\varepsilon^\alpha\}$. $l=0$: $\le2\|M_i\|$, absorbed in $C'$.

**Output.** D4.6.6.

**Standard?** Standard Lieb–Robinson plus filter-tail estimate (the argument of Kitaev App. D); constants specific.

**Pitfall.** Rate is $l^\alpha$, not $l$: the second term, from times beyond $\varepsilon l$, is the bottleneck. The time cutoff $\varepsilon$ depends on $v,c$ of D4.4, hence on $q,R,J$ only.

#### D4.9 Step — Operator Hölder-$\tfrac12$ inequality
*Source: 03-quasilocal.tex 288–305, `eq:quasilocal-square-root`. (Stated inside the proof of D4.6; consumed by D4.6.6, D4.10.)*

**Statement.** For all positive semidefinite $U,V$ (any dimension):
$$\|U^{1/2}-V^{1/2}\|\le\|U-V\|^{1/2}.$$

**Used from.** Nothing.

**Proof.**
- D4.9.1 Scalar identity $\int_0^\infty\frac{\lambda}{\lambda+s}s^{-1/2}ds=\pi\sqrt\lambda$ ($\lambda\ge0$). Spectral theorem: $T^{1/2}=\frac1\pi\int_0^\infty T(T+sI)^{-1}s^{-1/2}ds$, norm-convergent (integrand $\le\min\{1,\|T\|/s\}s^{-1/2}$).
- D4.9.2 Monotone: $T(T+s)^{-1}=I-s(T+s)^{-1}$; inversion reverses order on positive invertible operators, so $T\mapsto T(T+s)^{-1}$ preserves it; integrate against $s^{-1/2}ds>0$ $\Rightarrow$ $U\le V\Rightarrow U^{1/2}\le V^{1/2}$.
- D4.9.3 $\epsilon=\|U-V\|$: $U\le V+\epsilon I$, so $U^{1/2}\le(V+\epsilon I)^{1/2}\le V^{1/2}+\sqrt\epsilon I$ (scalar $\sqrt{x+\epsilon}\le\sqrt x+\sqrt\epsilon$ applied to $V$).
- D4.9.4 Swap $U\leftrightarrow V$: $-\sqrt\epsilon I\le U^{1/2}-V^{1/2}\le\sqrt\epsilon I$; self-adjoint, so norm $\le\sqrt\epsilon$.

**Output.** D4.6.6, D4.10 (square roots of $k_i,k_{i,l},I-k_i,I-k_{i,l}$).

**Standard?** Standard: Hölder continuity of $t\mapsto t^{r}$, $0<r<1$ (Birman–Koplienko–Solomyak; Ando); see Bhatia, *Matrix Analysis*, Ch. X. The proof given is the elementary operator-monotone one.

**Pitfall.** Dimension-free; this is why $\|G_i-G_{i,l}\|$ has no volume or spectator-dimension factor. The price is the square-root loss: tail exponent constant halves ($c\to c/2$), rate $l^\alpha$ is unchanged.

#### D4.10 Lemma 4.4 — Square roots and local channels
*Source: 03-quasilocal.tex 336–390; `eq:quasilocal-root-tail` (345–349), `eq:quasilocal-channel-tail` (360–364).*

**Statement.** For $k_i,k_{i,l}$ of D4.6 define $G_i=(I-k_i)^{1/2}$, $K_i=k_i^{1/2}$, $G_{i,l}=(I-k_{i,l})^{1/2}$, $K_{i,l}=k_{i,l}^{1/2}$. These are positive contractions, $G_i\Omega=\Omega$, $K_i\Omega=0$, and
$$\|G_i-G_{i,l}\|+\|K_i-K_{i,l}\|\le Ce^{-cl^\alpha},\qquad G_{i,l}^2+K_{i,l}^2=I.$$
Define on the full operator algebra $\mathcal E_i(B)=G_iBG_i+K_iBK_i$, $\mathcal E_{i,l}(B)=G_{i,l}BG_{i,l}+K_{i,l}BK_{i,l}$. Both are unital, completely positive, operator-norm contractions, also after tensoring with $\mathrm{id}$ on any auxiliary matrix algebra, and
$$\|\mathcal E_i-\mathcal E_{i,l}\|_{\mathrm{cb}}\le Ce^{-cl^\alpha},$$
where $\|\cdot\|_{\mathrm{cb}}$ is the supremum of operator norms over all auxiliary extensions. $\mathcal E_{i,l}$ fixes every operator commuting with the full algebra on $N_l(a_i)$, including operators supported outside the ball. All of this holds with arbitrary spectator systems.

**Used from.** D4.6 (`eq:quasilocal-positive-tail`, $k_i\Omega=0$, $k_{i,l}\in[0,I]$), D4.9, D4.2.

**Proof.**
- D4.10.1 $0\le k_i,k_{i,l}\le I$ $\Rightarrow$ $I-k_i$, $I-k_{i,l}$, $k_i$, $k_{i,l}$ are positive contractions, and so are their square roots. $G^2+K^2=(I-k)+k=I$ for both pairs.
- D4.10.2 $\Omega$ is an eigenvector of $k_i$ with eigenvalue $0$; functional calculus: $K_i\Omega=\sqrt0\,\Omega=0$, $G_i\Omega=\sqrt1\,\Omega=\Omega$.
- D4.10.3 D4.9 with $(U,V)=(k_i,k_{i,l})$ and $(I-k_i,I-k_{i,l})$: each difference $\le\|k_i-k_{i,l}\|^{1/2}\le Ce^{-cl^\alpha/2}$. Sum gives `eq:quasilocal-root-tail` (renaming $c$).
- D4.10.4 CP: each summand is $B\mapsto A^*BA$ with $A=G$ or $K$. Unital: $G^2+K^2=I$.
- D4.10.5 Contractivity: $V:v\mapsto G v\oplus Kv$ satisfies $V^*V=G^2+K^2=I$, so is an isometry, and $\mathcal E(B)=V^*(B\oplus B)V$, hence $\|\mathcal E(B)\|\le\|B\oplus B\|=\|B\|$. Same for the local maps and after replacing $G,K$ by $G\otimes I,K\otimes I$ (norms unchanged).
- D4.10.6 Perturbation: $\|ABA-A'BA'\|\le\|(A-A')BA\|+\|A'B(A-A')\|\le(\|A\|+\|A'\|)\|A-A'\|\|B\|$, valid on every auxiliary extension. With $\|A\|,\|A'\|\le1$ applied to $(G_i,G_{i,l})$ and $(K_i,K_{i,l})$: $\|\mathcal E_i-\mathcal E_{i,l}\|_{\mathrm{cb}}\le2(\|G_i-G_{i,l}\|+\|K_i-K_{i,l}\|)\le Ce^{-cl^\alpha}$.
- D4.10.7 Fixed algebra: $G_{i,l},K_{i,l}$ are functions of $k_{i,l}$, which lies in the algebra on $N_l(a_i)$. If $B$ commutes with that algebra (with any spectators), then $\mathcal E_{i,l}(B)=B(G_{i,l}^2+K_{i,l}^2)=B$.

**Output.** §10: `eq:amplification-channel-approximation` (same bound, quoted) and unitality/spectator-fixing used to localize products of channels.

**Standard?** Standard (Stinespring/Kraus compression, cb-norm perturbation); square-root route specific to this paper.

**Pitfall.** Fixed-point claim is for the commutant of the ball algebra, not only operators supported outside the ball; with spectators it is the commutant in the extended algebra.

---

### 4.3 Truncation with volume-free error

#### D4.11 Proposition 4.5 — Truncation near a finite set
*Source: 03-quasilocal.tex 405–521 (motivation 392–403); equations `eq:quasilocal-variable-radius` (413–417), `eq:quasilocal-truncation-error` (421–425), `eq:quasilocal-ground-distance` (429–434), `eq:quasilocal-crossing-count` (440–444), `eq:quasilocal-cut-budget` (447–451).*

**Statement.** Use D4.6 with $p=1$, $\alpha=1/2$. Fix $C_0>0$. There is $C_1$ depending only on $q,R,J,\Delta,C_0$ such that for every real $n\ge2$ and every nonempty $S_0\subseteq\Lambda$ with $|S_0|\le C_0n^2$: put $r_0=\lceil C_1(\log n)^2\rceil$. If $d_i^0:=d_\Lambda(a_i,S_0)<\infty$,
$$r_i=\max\{r_0,\lfloor d_i^0/2\rfloor\},\quad\widetilde h_i=k_{i,r_i},\quad\widetilde X_i=N_{r_i}(a_i).$$
If $d_i^0=\infty$: $\widetilde h_i=k_i$, $\widetilde X_i$ = whole component of $a_i$. Then $\widetilde H=\sum_i\widetilde h_i$ is a sum of positive contractions and
$$\|\widetilde H-H_F\|\le\epsilon_n:=\min\{n^{-1000},g/4\}.$$
Its ground energy $\widetilde E_0\in[0,\epsilon_n]$, ground vector $\widetilde\Omega$ unique, gap $\ge g/2$. After a choice of phase,
$$\|\widetilde\Omega-\Omega\|\le2\sqrt{\epsilon_n/g},\qquad\tfrac12\big\||\widetilde\Omega\rangle\langle\widetilde\Omega|-P_\Omega\big\|_1\le\sqrt{2\epsilon_n/g}.$$
For $X\subseteq S_0$ let $b_X=|\partial_\Lambda X|$ and $\mathcal C_X$ the labels whose $\widetilde X_i$ meet both $X$ and $\Lambda\setminus X$. Each such support has radius exactly $r_0$ and
$$|\mathcal C_X|\le Cb_X(r_0+1)^2,\qquad\log d_i\le C(r_0+1)^2\ (i\in\mathcal C_X),\quad d_i:=q^{|\widetilde X_i|},$$
$$\mathcal B_X:=1+\sum_{i\in\mathcal C_X}\log^2(ed_i)\le C(1+b_X)(r_0+1)^6.$$
In particular $b_X\le C_2nD$, $D\ge1$ $\Rightarrow$ $\mathcal B_X\le CnD(\log n)^{12}$ ($C$ also depends on $C_2$).

**Used from.** D4.6 (all of Prop 4.3, $p=1$), D4.3 (counts), D4.2, §2 `eq:ball-count`; D4.12, D4.13, D4.14 (below).

**Proof.**
- D4.11.1 $\widetilde h_i\in[0,I]$ ($k_{i,l}\in[0,I]$ by D4.6; $k_i\in[0,I]$) $\Rightarrow$ $\widetilde H$ is a sum of positive contractions.
- D4.11.2 Error: D4.12 with $\alpha=1/2$, then choice of $C_1$: `eq:quasilocal-truncation-error`.
- D4.11.3 Spectrum and ground vector: D4.13.
- D4.11.4 Crossing supports and budgets: D4.14.

**Output.** §8/§9 (comparators, scanner): $\widetilde H,\widetilde h_i,\widetilde X_i,r_0$, $\widetilde E_0\le n^{-1000}$, $\widetilde g\ge g/2$, $\|\widetilde\Omega-\Omega\|$, $\mathcal B_X$, $\log d_i\le C(1+r_0)^2$ for crossing supports. §3's local-conjugation lemma consumes the dimension dependence only through $\log d_i$ (hence $\mathcal B_X$). §9 sets $S_0=A\cap T_L$.

**Standard?** Specific to this paper (variable-radius truncation with volume-free total error). Min–max/perturbation ingredients standard.

**Pitfall.** Order of quantifiers: $C_0$ first, then $C_1=C_1(q,R,J,\Delta,C_0)$ (through $g=\Delta/c_*$ at $p=1$), then $n$ and $S_0$. $d_i=q^{|\widetilde X_i|}$ is the Hilbert-space dimension of the support, unrelated to $d_i^0$ (distance) and $d_\Lambda$. Radii $r_i>r_0$ occur only for labels whose ball avoids $S_0$.

#### D4.12 Step — Volume-free summation of the truncation error
*Source: 03-quasilocal.tex 458–486, `eq:quasilocal-volume-free`.*

**Statement.** For any fixed $\alpha\in(0,1)$ for which `eq:quasilocal-positive-tail` holds, any integer $r_0\ge1$, and $r_i$ as in D4.11:
$$\|\widetilde H-H_F\|\le C|S_0|\sum_{d\ge0}(d+1)^2\exp\!\big(-c\max\{r_0,\lfloor d/2\rfloor\}^\alpha\big)\le C'|S_0|e^{-c'r_0^\alpha},$$
no factor $|\Lambda|$. With $\alpha=1/2$, $|S_0|\le C_0n^2$, $r_0=\lceil C_1(\log n)^2\rceil$, the right side is $\le C'C_0n^{2-c'\sqrt{C_1}}$; for $C_1$ large this gives `eq:quasilocal-truncation-error`.

**Used from.** D4.6 (tail), D4.3 ($\mu_R$ labels per anchor), §2 `eq:ball-count`.

**Proof.**
- D4.12.1 Labels at infinite distance have $\widetilde h_i=k_i$: zero error. Triangle inequality: $\|\widetilde H-H_F\|\le\sum_{i:d_i^0<\infty}\|k_i-k_{i,r_i}\|\le\sum_iCe^{-cr_i^\alpha}$.
- D4.12.2 Count at distance $d$: an anchor with $d(a,S_0)=d$ lies in $N_d(x)$ for some $x\in S_0$, so $\le|S_0|v_d\le3|S_0|(d+1)^2$ anchors, hence $\le3\mu_R|S_0|(d+1)^2$ labels.
- D4.12.3 This gives the first inequality with $r_i=\max\{r_0,\lfloor d/2\rfloor\}$.
- D4.12.4 Terms $d\le2r_0+2$: $r_i\ge r_0$, number of weighted terms $\sum_{d\le2r_0+2}(d+1)^2\le C(r_0+1)^3$, total $\le C(r_0+1)^3e^{-cr_0^\alpha}$.
- D4.12.5 Terms $d>2r_0+2$ ($d\ge5$): $\lfloor d/2\rfloor\ge d/3$ ($d\ge3$). Bound the tail by $\int(x+1)^2e^{-c(x/3)^\alpha}dx$ from $\sim2r_0$ (comparison costs a constant factor, summand eventually monotone). With $u=x^\alpha$, $dx=\alpha^{-1}u^{1/\alpha-1}du$: tail $\le C\int_{(2r_0)^\alpha}^\infty(u^{1/\alpha}+1)^2u^{1/\alpha-1}e^{-c3^{-\alpha}u}du\le C(1+r_0)^{k}e^{-c''r_0^\alpha}$, $k=k(\alpha)$, any $c''<c(2/3)^\alpha$ (incomplete-gamma tail $\int_{u_0}^\infty\mathrm{poly}(u)e^{-c'u}du\le C(1+u_0)^ke^{-c'u_0}$).
- D4.12.6 Absorb all powers of $(r_0+1)$ into the exponential by decreasing the exponential constant: $(r_0+1)^ke^{-cr_0^\alpha}\le C_ke^{-c'r_0^\alpha}$.
- D4.12.7 Numerics: $r_0^{1/2}\ge\sqrt{C_1}\log n$, so $e^{-c'r_0^{1/2}}\le n^{-c'\sqrt{C_1}}$. Choose $C_1$ with $c'\sqrt{C_1}\ge1002+\log_2(C'C_0)$ $\Rightarrow$ bound $\le n^{-1000}$ for $n\ge2$. Enlarging $C_1$ again gives $C'C_02^{2-c'\sqrt{C_1}}\le g/4$, and since the bound decreases in $n$ it holds for all $n\ge2$. Hence $\le\epsilon_n$.

**Output.** `eq:quasilocal-truncation-error` for D4.13.

**Standard?** Specific to this paper.

**Pitfall.** $C',c'$ come from `eq:quasilocal-positive-tail` at $p=1$ and the sum above; independent of $C_1,n,S_0$ (needed to choose $C_1$ afterwards). The requirement $\epsilon_n\le g/4$ (not just $n^{-1000}$) is what makes gap $\ge g/2$ in D4.13 hold for all $n\ge2$; $C_1$ depends on $g$ for that reason. The paper remarks that $1000$ can be any fixed positive exponent by enlarging $C_1$.

#### D4.13 Step — Ground energy, gap and ground vector of $\widetilde H$
*Source: 03-quasilocal.tex 488–503, `eq:quasilocal-ground-distance`.*

**Statement.** Given $\|\widetilde H-H_F\|\le\epsilon:=\epsilon_n\le g/4$: $\widetilde E_0\in[0,\epsilon]$; second eigenvalue of $\widetilde H$ $\ge g-\epsilon$; gap $\ge g-2\epsilon\ge g/2$; ground vector unique; with phase fixed so $\langle\Omega,\widetilde\Omega\rangle\ge0$: $\|\widetilde\Omega-\Omega\|\le2\sqrt{\epsilon/g}$ and $\tfrac12\||\widetilde\Omega\rangle\langle\widetilde\Omega|-P_\Omega\|_1\le\sqrt{2\epsilon/g}$.

**Used from.** D4.6 ($H_F\ge0$, $H_F\Omega=0$, $H_F\ge g(I-P_\Omega)$), D4.12.

**Proof.**
- D4.13.1 $\widetilde H\ge0$ (D4.11.1) $\Rightarrow$ $\widetilde E_0\ge0$. $\widetilde E_0\le\langle\Omega,\widetilde H\Omega\rangle=\langle\Omega,(\widetilde H-H_F)\Omega\rangle\le\epsilon$ ($H_F\Omega=0$).
- D4.13.2 $H_F$ has eigenvalues $0$ (simple) then $\ge g$. Min–max (Weyl): $\lambda_2(\widetilde H)\ge\lambda_2(H_F)-\epsilon\ge g-\epsilon$.
- D4.13.3 Gap $\lambda_2-\lambda_1\ge g-\epsilon-\epsilon=g-2\epsilon\ge g/2$ ($\epsilon\le g/4$). Positive gap $\Rightarrow$ $\lambda_1$ simple.
- D4.13.4 $s:=|\langle\Omega,\widetilde\Omega\rangle|$. $g(1-s^2)\le\langle\widetilde\Omega,H_F\widetilde\Omega\rangle$ (from $H_F\ge g(I-P_\Omega)$) $\le\langle\widetilde\Omega,\widetilde H\widetilde\Omega\rangle+\|H_F-\widetilde H\|\le\widetilde E_0+\epsilon\le2\epsilon$.
- D4.13.5 Pure-state trace distance $\frac12\||a\rangle\langle a|-|b\rangle\langle b|\|_1=\sqrt{1-|\langle a,b\rangle|^2}$, so $\le\sqrt{2\epsilon/g}$.
- D4.13.6 Phase with $\langle\Omega,\widetilde\Omega\rangle=s\in[0,1]$: $\|\widetilde\Omega-\Omega\|^2=2-2s\le2(1-s^2)\le4\epsilon/g$ ($s\ge s^2$).

**Output.** $\widetilde E_0,\widetilde g\ge g/2$, $\|\widetilde\Omega-\Omega\|$, trace distance of $\widetilde\Omega$ vs $\Omega$ used in §8/§9 to transfer entropies back to $\Omega$ (via §2 `lem:continuity`; trace distance of pure states $\le\|\xi-\eta\|$).

**Standard?** Standard (Weyl/min–max; spectral-gap perturbation of a ground state, Davis–Kahan type).

#### D4.14 Step — Crossing supports and the cut budget
*Source: 03-quasilocal.tex 436–454 (statement), 505–521 (proof); `eq:quasilocal-crossing-count`, `eq:quasilocal-cut-budget`.*

**Statement.** For $X\subseteq S_0$, $b_X=|\partial_\Lambda X|$: every $i\in\mathcal C_X$ has $r_i=r_0$, and
$$|\mathcal C_X|\le Cb_X(r_0+1)^2,\quad\log d_i\le C(r_0+1)^2,\quad\mathcal B_X=1+\sum_{i\in\mathcal C_X}\log^2(ed_i)\le C(1+b_X)(r_0+1)^6.$$
If $b_X\le C_2nD$, $D\ge1$, $n\ge2$: $\mathcal B_X\le CnD(\log n)^{12}$.

**Used from.** D4.11 (definitions of $r_i,\widetilde X_i$), §2 `eq:ball-count`, D4.3.

**Proof.**
- D4.14.1 *Finite distance.* $\widetilde X_i$ meets $X\subseteq S_0$. If $d_i^0=\infty$, $\widetilde X_i$ is the whole component of $a_i$, which has no point of $S_0$, contradiction. So $d_i^0<\infty$.
- D4.14.2 *Radius.* Suppose $r_i>r_0$. Then $r_i=\lfloor d_i^0/2\rfloor<d_i^0$ (as $d_i^0\ge1$ when $r_i>r_0\ge1$). Ball $N_{r_i}(a_i)$ contains no point of $S_0\supseteq X$, but $\widetilde X_i$ meets $X$. Contradiction, so $r_i=r_0$.
- D4.14.3 *Path to a crossing edge.* $\widetilde X_i=N_{r_0}(a_i)$ meets $X$ and $\Lambda\setminus X$. If $a_i\in X$ take a shortest path from $a_i$ to a point of the ball outside $X$; otherwise to a point of the ball inside $X$. Path length $\le r_0$, so all its vertices lie in the ball; it starts and ends on opposite sides of $X$ so contains an edge of $\partial_\Lambda X$. Hence $d_\Lambda(a_i,\text{endpoint})\le r_0$.
- D4.14.4 *Count.* $\le2b_X$ endpoints; $\le v_{r_0}\le C(r_0+1)^2$ anchors within $r_0$ of each; $\le\mu_R$ labels per anchor $\Rightarrow$ $|\mathcal C_X|\le2\mu_Rb_Xv_{r_0}\le Cb_X(r_0+1)^2$.
- D4.14.5 *Dimension.* $\log d_i=|\widetilde X_i|\log q\le v_{r_0}\log q\le C(r_0+1)^2$.
- D4.14.6 *Budget.* $\log^2(ed_i)=(1+\log d_i)^2\le C(r_0+1)^4$. Summing over $\mathcal C_X$: $\mathcal B_X\le1+Cb_X(r_0+1)^2(r_0+1)^4\le C(1+b_X)(r_0+1)^6$.
- D4.14.7 *Consequence.* $1+b_X\le(1+C_2)nD$ ($nD\ge1$). $r_0+1\le C_1(\log n)^2+2\le C(\log n)^2$ for $n\ge2$ ($\log n\ge\log2$). So $(r_0+1)^6\le C(\log n)^{12}$.

**Output.** $\mathcal B_X$ is the parameter $\mathcal B$ of §8 (comparators, `07-comparators.tex` ~76–84) and §9 (`08-scanner.tex` ~390). Crossing-support dimension $q^{C(1+r_0)^2}$ (`08-scanner.tex` ~407).

**Standard?** Specific to this paper (cut-edge counting for variable-radius balls; compare §2 `eq:crossing-count`, which does the same for original supports with radius $R$).

**Pitfall.** Only $X\subseteq S_0$ is covered. Supports with radius $>r_0$ never cross a cut inside $S_0$ (D4.14.2); this is why larger radii far away do not enter $\mathcal B_X$. $b_X=|\partial_\Lambda X|$ counts edges of the induced graph, not ambient lattice edges.

#### D4.15 Step — Remarks on the application and degenerate cases
*Source: 03-quasilocal.tex 523–534.*

**Statement.** (i) §9 takes $S_0=A\cap T_L$, $T_L=T+([-L,L]^2\cap\mathbb Z^2)$; only $|S_0|\le Cn^2$ is needed from D4.11, with geometric input $b_X=O(nD)$ supplied there. (ii) $S_0=\varnothing$: keep every constraint exactly ($\widetilde H=H_F$), every cut $X\subseteq S_0$ has no crossing label. (iii) Components not meeting $S_0$ are kept exactly throughout. (iv) The exponent $1000$ in $\epsilon_n$ can be replaced by any fixed positive exponent by enlarging $C_1$; the powers of $\log n$ in the support and cut bounds do not change.

**Used from.** D4.11, D4.12.

**Output.** Scope of D4.11 in §9; (ii)–(iii) are the $d_i^0=\infty$ branch of D4.11.

**Standard?** Remarks; (iv) follows from D4.12.7.

---

## Parameters and constants

| Symbol | Value / meaning | Fixed where |
|---|---|---|
| $q,R,J,\Delta$ | local dim., support diameter bound in $d_\Lambda$, $\|h_i\|\le J$, gap | §2 (hypotheses) |
| $v_r$ | $1+2r(r+1)\ge|B_\Lambda(x,r)|$ | §2 `eq:ball-count` |
| $\mu_R$ | $2^{v_R-1}$; bounds supports through a site and labels per anchor | §2; D4.3 |
| $b_0$ | $J\mu_R$ | `eq:quasilocal-budget`, D4.3 |
| $\kappa$ | $v_Rb_0$ | D4.4.5 |
| $c$ (D4.4) | free $>0$ ($=\mu$ in chain sum) | D4.4.7 |
| $v$ (D4.4) | $2\kappa e^{cR}$ | D4.4.7 |
| $C$ (D4.4) | $2e^{cR}$ | D4.4.7 |
| $p$ | integer $\ge1$ | free in D4.5, D4.6, D4.10; $=1$ in D4.11; fixed in §10 |
| $\alpha$ | $p/(p+1)$ | D4.5; $=1/2$ in D4.11; $>1-10^{-6}$ in §10 |
| $\delta$ | $\Delta/2$ | D4.6.1 / D4.7.3 |
| $\eta_p,c_p$ | disk radius factor, lower bound of $\operatorname{Re}(1+\zeta)^{-p}$ | D4.5.2 |
| $C_1$ (D4.5) | $\|\chi^{(m)}\|_\infty\le C_1^{m+1}(m!)^{1+1/p}$ | D4.5.6 (internal; distinct from D4.11 $C_1$) |
| $\eta$ (D4.5) | $m=\lfloor\eta|t|^\alpha\rfloor$, small | D4.5.8 |
| $\|f\|_1$ | finite, depends on $p,\Delta$ | D4.5 |
| $c_*$ | $\max\{1,J(\|f\|_1+1)\}$ | D4.6.2 |
| $g$ | $\Delta/c_*$ | D4.6 |
| $\varepsilon$ (D4.8) | time cutoff: $|t|\le\varepsilon l$, with $v\varepsilon<c/2$ | D4.8.2 (distinct from $\epsilon_n$ and §10's $\varepsilon=10^{-5}$) |
| $l$ | integer ball radius $\ge0$ | D4.2 |
| $C_0$ | $|S_0|\le C_0n^2$ | D4.11 hypothesis |
| $C_1$ (D4.11) | $r_0=\lceil C_1(\log n)^2\rceil$; depends on $q,R,J,\Delta,C_0$; large | D4.12.7 |
| $n$ | real $\ge2$ | D4.11 |
| $r_0$ | $\lceil C_1(\log n)^2\rceil\ge1$ | D4.11 |
| $r_i$ | $\max\{r_0,\lfloor d_i^0/2\rfloor\}$ | `eq:quasilocal-variable-radius` |
| $\epsilon_n$ | $\min\{n^{-1000},g/4\}$ | `eq:quasilocal-truncation-error` |
| $1000$ | replaceable by any fixed positive exponent | D4.15 |
| gap of $\widetilde H$ | $\ge g/2$ | D4.13 |
| $b_X$ | $|\partial_\Lambda X|$, $X\subseteq S_0$ | D4.11 |
| $C_2,D$ | $b_X\le C_2nD$, $D\ge1$ | D4.11 last line |
| $\mathcal B_X$ | $\le C(1+b_X)(r_0+1)^6\le CnD(\log n)^{12}$ | D4.14 |

## Dependencies

Consumed:
- §2: $v_r$, `eq:ball-count`; $\mu_R$; anchors and labels per anchor; the counts $|X_i|\le v_R$; $\sum_{i\ni x}\|h_i\|\le J\mu_R$; $\partial_\Lambda$ (edges of the induced graph).
- External: Lieb–Robinson (1972), Nachtergaele–Ogata–Sims (2006); Kitaev (2006) App. D.1.2 Prop. D.1; Swingle–McGreevy (2016) §8.4; operator Hölder/monotonicity of $\sqrt\cdot$ (Bhatia, Ch. X).

Exported:
- §3 (initial): truncated interactions $\widetilde h_i$ and their supports via $\log d_i$ (through $\mathcal B_X$, D4.14).
- §7–§9 (transport, comparators, scanner): D4.11 (data $\widetilde H,\widetilde h_i,\widetilde X_i,r_0,\widetilde E_0,\widetilde g,\widetilde\Omega$), D4.13, D4.14 ($\mathcal B_X$).
- §10 (amplification): D4.6 (Prop 4.3 with fixed $p$, $g$, $H_F$, tails), D4.10 (Lemma 4.4: channels, `eq:quasilocal-channel-tail`).
- §1: D4.6 cited in the introduction as the positive replacement with rapidly decaying spatial tails.
