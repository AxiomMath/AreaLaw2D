# Digest of §7 — Transport through finite trees of metrics

Source: `paper/sections/06-transport.tex` (779 lines), label `sec:transport`. Numbering (one shared counter per section): Lemma 7.1 (`transport:means`), Lemma 7.2 (`transport:cp`), Lemma 7.3 (`transport:fourier`), Proposition 7.4 (`prop:transport`). Upstream results are cited by paper number and tex label: Lemma 5.3 = `lem:skew`, Lemma 6.2 = `replicas:metric`, Lemma 6.3 = `lem:relative-pin`, Lemma 6.4 = `lem:symbol`. Upstream anchors: D2.1; D5.5 (Lemma 5.1), D5.15 (Lemma 5.3); D6.4 (Lemma 6.1), D6.5 (`replicas:w-definition`), D6.6 (Lemma 6.2), D6.8 (`replicas:leaf-metric`), D6.9, D6.10 (Lemma 6.3), D6.11 (`replicas:husimi`), D6.12 (Lemma 6.4).

## Section in one paragraph

Lemma 6.3 gives the entropy gain of one change of partition as a rank-one lower bound on one relative metric. §7 combines many such changes through a finite tree of weighted geometric means $A\#_pB$ and proves two estimates for $v(p)=\mathcal M(p)^{-1/4}\mathrm{pre}/N(p)$. (i) $-\partial_p\log N^2$ is an average of $\operatorname{Tr}(\sigma\log C_h)$ against trace-one states $\sigma_{h,u}$, bounded below by $ka\sum\int\eta\,d\mu_{\sigma_{h,u}}-(CkaKa^{1/4}\ell^C+\beta_k)$. (ii) If $\bar H\mathrm{pre}=E_0\mathrm{pre}$: $\langle v,\bar Hv\rangle\le2E_0+Ca^2\ell^C\sum_iW_i\sum_j\pi_j\int\!\!\int\eta^{1/8}+o_k(1)$ against the same states. Order: mean trees (D7.1–D7.3) → normalized derivative maps, unital CP (D7.4–D7.5) → Fourier multipliers (D7.6–D7.7) → data of a round (D7.8–D7.13) → Proposition 7.4 (D7.14): derivative states, exact formula (D7.15–D7.16), entropy gain (D7.17–D7.20), block metric, Fourier transport of its commutator (D7.21–D7.23), symbol cost, energy (D7.24–D7.25), endpoints (D7.26), shared state (D7.27). §9 uses both estimates at a common $p$ and projection transfer for the initial floor; §8 uses vector Jensen.

Notation. $\mathcal V$ finite one-copy space, $\mathcal S_k=\operatorname{Sym}^k\mathcal V$, $D_k=\dim\mathcal S_k$. $t<1/4$, $a=2t$. $W_{Q,k}$ metric of §6 (`replicas:w-definition`), suppressed $k$. $P_{\theta,k}=|\theta^{\otimes k}\rangle\langle\theta^{\otimes k}|$. $\operatorname{ad}_Q(Z)=QZ-ZQ$. $|O|=(O^*O)^{1/2}$.

---

### 7.1 Positive matrix means and their derivatives

#### D7.1 Def — Weighted geometric mean (`transport:mean-def`)
*Source: 06-transport.tex 18–27.*

**Statement.** For positive definite $A,B$ on a finite-dimensional Hilbert space, $0\le p\le1$:
$$A\#_pB=A^{1/2}\bigl(A^{-1/2}BA^{-1/2}\bigr)^pA^{1/2}.$$
$p=0$ gives $A$, $p=1$ gives $B$.

**Used from.** none.

**Output.** Vertex operation of every tree in §7–§9.

**Standard?** Kubo–Ando (1980); form version Pusz–Woronowicz (1975). Properties re-proved in D7.3.

#### D7.2 Def — Weighted binary tree and its root
*Source: 06-transport.tex 28–38.*

**Statement.** A weighted binary tree: finite rooted binary tree, parameter $p\in[0,1]$ at each internal vertex, outgoing edges of weights $1-p$ (first child) and $p$ (second child). Terminal weights $w_j$ = products of edge weights on root-to-leaf paths; $\sum_jw_j=1$. Positive definite operators $A_j$ at leaves; each internal vertex evaluated by D7.1. Value at root = root operator $M$, written $\mathcal T(A_j:j)$. Edges of weight $0$ are omitted, a vertex left with one child is contracted, so all retained $w_j>0$. Every finite probability vector arises, by successive splitting of its support with conditional probabilities.

**Used from.** D7.1.

**Output.** The tree is part of the data. No associativity of $\#_p$ is asserted or used.

**Standard?** Specific to this paper.

#### D7.3 Lemma 7.1 — Properties of a finite mean tree
*Source: 06-transport.tex 40–129; `transport:scalar-homogeneity`, `transport:vector-jensen`, `transport:projection-transfer`, `transport:power-integral`.*

**Statement.** $\mathcal T$ weighted binary tree, terminal weights $w_j$, positive definite inputs $A_j$, root $M$.
1. Congruence: $\mathcal T(S^*A_jS:j)=S^*MS$ for invertible $S$.
2. Monotone in each input.
3. $\mathcal T(c_jA_j:j)=\bigl(\prod_jc_j^{w_j}\bigr)M$ for $c_j>0$.
4. For every unit $z$: $\langle z,Mz\rangle\le\prod_j\langle z,A_jz\rangle^{w_j}$.
5. If $P$ is an orthogonal projection and $A_j\ge c_jP$, $c_j>0$, then $M\ge\bigl(\prod_jc_j^{w_j}\bigr)P$.
6. If $A_j=\prod_{g=1}^KA_{j,g}$ with positive definite factors and every factor of band $g$ commutes with every factor of band $g'\ne g$ (all leaves), then $M=\prod_gM_g$, $M_g$ = root of the same tree on inputs $(A_{j,g})_j$; the $M_g$ commute.

**Used from.** D7.1, D7.2.

**Proof.**
- D7.3.1 Congruence at a vertex. $\widehat A=S^*AS$, $U=A^{1/2}S\widehat A^{-1/2}$. $U^*U=\widehat A^{-1/2}S^*AS\widehat A^{-1/2}=I$ $\Rightarrow$ $U$ unitary (finite dimension). $\widehat A^{-1/2}S^*BS\widehat A^{-1/2}=U^*CU$ with $C=A^{-1/2}BA^{-1/2}$. Then $\widehat A^{1/2}(U^*CU)^p\widehat A^{1/2}=\widehat A^{1/2}U^*C^pU\widehat A^{1/2}=S^*A^{1/2}C^pA^{1/2}S$, using $U\widehat A^{1/2}=A^{1/2}S$. So $(S^*AS)\#_p(S^*BS)=S^*(A\#_pB)S$.
- D7.3.2 Symmetry $A\#_pB=B\#_{1-p}A$. By D7.3.1 with $S=A^{-1/2}$ reduce to $A=I$, $B=C$: claim $C^p=C^{1/2}(C^{-1})^{1-p}C^{1/2}$. True by functional calculus: exponent $\tfrac12+(p-1)+\tfrac12=p$.
- D7.3.3 Integral formula (`transport:power-integral`), $0<p<1$, $x>0$: $x^p=\frac{\sin\pi p}{\pi}\int_0^\infty\lambda^{p-1}\frac{x}{x+\lambda}d\lambda$. Substituting $\lambda=xt$: integral $=x^p\int_0^\infty\frac{t^{p-1}}{1+t}dt=x^p\,\frac{\pi}{\sin\pi p}$ (beta integral).
- D7.3.4 Operator monotonicity of $C\mapsto C^p$. Inversion reverses order on positive definite operators, so $\lambda(C+\lambda)^{-1}$ decreases in $C$, hence $\frac{C}{C+\lambda}=I-\lambda(C+\lambda)^{-1}$ increases. By functional calculus $C^p=\frac{\sin\pi p}{\pi}\int_0^\infty\lambda^{p-1}C(C+\lambda)^{-1}d\lambda$ with positive weight, so $C\le C'\Rightarrow C^p\le C'^p$. Monotone in $B$: $B\le B'\Rightarrow C\le C'\Rightarrow C^p\le C'^p\Rightarrow A\#_pB\le A\#_pB'$ (congruence by $A^{1/2}$ preserves order). Monotone in $A$: D7.3.2. $p\in\{0,1\}$ trivial.
- D7.3.5 Scalar homogeneity at a vertex: $(cA)\#_p(dB)=c^{1-p}d^p\,A\#_pB$, since $C\mapsto(d/c)C$ and $(cA)^{1/2}((d/c)C)^p(cA)^{1/2}=c\,(d/c)^pA^{1/2}C^pA^{1/2}$.
- D7.3.6 Vector inequality at a vertex. $r=\langle z,Az\rangle$, $y=A^{1/2}z/\sqrt r$ (unit). $\langle z,(A\#_pB)z\rangle=\langle A^{1/2}z,C^pA^{1/2}z\rangle=r\langle y,C^py\rangle$. Scalar Jensen ($x\mapsto x^p$ concave, spectral measure of $C$ in $y$ is a probability measure): $\langle y,C^py\rangle\le\langle y,Cy\rangle^p$. And $r\langle y,Cy\rangle^p=r^{1-p}\langle z,Bz\rangle^p$. So $\langle z,(A\#_pB)z\rangle\le\langle z,Az\rangle^{1-p}\langle z,Bz\rangle^p$.
- D7.3.7 Induction for items 1–4. Items 1, 2: vertexwise (D7.3.1, D7.3.4). Item 3: if subtree values scale by $c_L=\prod_{L}c_j^{w^L_j}$, $c_R=\prod_Rc_j^{w^R_j}$ (subtree-normalized weights), the vertex scales by $c_L^{1-p}c_R^p$ (D7.3.5); the exponent of $c_j$ is $(1-p)w^L_j$ resp. $pw^R_j$ = terminal weight in the full tree. Item 4: $\langle z,Mz\rangle\le\langle z,M_Lz\rangle^{1-p}\langle z,M_Rz\rangle^p$ (D7.3.6) $\le\prod_L\langle z,A_jz\rangle^{(1-p)w^L_j}\prod_R\langle z,A_jz\rangle^{pw^R_j}$ (induction on subtrees, monotonicity of $x\mapsto x^{1-p},x^p$).
- D7.3.8 Idempotence $X\#_pX=X$ ($C=I$), hence the tree on equal inputs $X$ returns $X$ (using $\sum w_j=1$).
- D7.3.9 Projection transfer. Fix $0<\varepsilon<1$. $A_j-(1-\varepsilon)c_jP=(1-\varepsilon)(A_j-c_jP)+\varepsilon A_j\ge\varepsilon\lambda_{\min}(A_j)I$. Pick common $\delta>0$ with $(1-\varepsilon)c_j\delta\le\varepsilon\lambda_{\min}(A_j)$ for all leaves. Then $A_j\ge(1-\varepsilon)c_j(P+\delta I)$, strictly positive. Monotonicity, homogeneity (item 3) and D7.3.8: $M\ge(1-\varepsilon)\prod_jc_j^{w_j}(P+\delta I)\ge(1-\varepsilon)\prod_jc_j^{w_j}P$. Let $\varepsilon\downarrow0$. The mean is never evaluated on singular input.
- D7.3.10 Band factorization at a vertex. $D=\prod_gD_g$, $E=\prod_gE_g$, cross-band commutation. $D^{-1/2}=\prod_gD_g^{-1/2}$ (commuting positives). $D^{-1/2}ED^{-1/2}=\prod_gX_g$, $X_g=D_g^{-1/2}E_gD_g^{-1/2}$ (each $D_{g'}^{-1/2}$, $g'\ne g$, commutes with $E_g$). $X_g$, $X_{g'}$ commute (involve disjoint bands). So $(\prod X_g)^p=\prod X_g^p$, and $D^{1/2}\prod_gX_g^pD^{1/2}=\prod_gD_g^{1/2}X_g^pD_g^{1/2}=\prod_g(D_g\#_pE_g)$.
- D7.3.11 Induction for item 6. $D_g\#_pE_g$ lies in the algebra generated by band-$g$ operators, so the cross-band commutation hypothesis passes to every internal vertex. Hence $M=\prod_gM_g$ with commuting factors.

**Output.** Item 1: reduction to $A=I$, relative metrics $C_{h,g}$ (D7.17). Item 3: derivative unitality (D7.5), constant-weight products in D7.18. Item 4: used in §8 for $\langle\varphi,\widetilde{\mathcal M}\varphi\rangle$. Item 5: D7.18 and §9 initial floor. Item 6: D7.17, D7.24.

**Standard?** Items 1–4: standard for Kubo–Ando means. Items 5, 6: specific to this paper.

**Pitfall.** $0<p<1$ needed for D7.3.3–D7.3.4; endpoints separately. In item 6 the hypothesis includes commutation between factors at *different leaves* (not only within one leaf).

#### D7.4 Def — Completely positive and unital maps
*Source: 06-transport.tex 131–134.*

**Statement.** A linear map on matrices is completely positive (CP) if its entrywise action on every matrix amplification preserves positive semidefinite matrices. Unital: maps $I$ to $I$.

**Used from.** none.

**Output.** Vocabulary of D7.5, D7.22–D7.23.

**Standard?** Standard.

#### D7.5 Lemma 7.2 — Normalized derivative maps
*Source: 06-transport.tex 136–177; `transport:edge-map`, `transport:leaf-map`, `transport:power-derivative`.*

**Statement.** At a binary vertex with output $M$ and a child $D$ of positive edge weight $w$ define
$$\Phi_D(Z)=\frac1w\,M^{-1/2}\,\partial_DM\bigl[D^{1/2}ZD^{1/2}\bigr]\,M^{-1/2},$$
$\partial_D$ = Fréchet derivative in $D$, other child and weight fixed. $\Phi_D$ is unital and CP. Composing these maps from terminal leaf $j$ to the root gives a unital CP map $\Phi_j$ with
$$M^{-1/2}\,\partial_{A_j}M\bigl[A_j^{1/2}ZA_j^{1/2}\bigr]\,M^{-1/2}=w_j\,\Phi_j(Z).$$
If all inputs are block diagonal for a fixed orthogonal decomposition, the maps preserve each block: the $(a,b)$ block of $\Phi_j(Z)$ depends only on the $(a,b)$ block of $Z$, and on the first diagonal block $\Phi_j$ is the normalized derivative map of the tree of first diagonal blocks, independent of the other diagonal blocks.

**Used from.** D7.1–D7.4; D7.3 (items 1, 3, D7.3.2, D7.3.3).

**Proof.**
- D7.5.1 Derivative of the power (from D7.3.3). $\frac{d}{dC}\bigl[I-\lambda(C+\lambda)^{-1}\bigr][H]=\lambda(C+\lambda)^{-1}H(C+\lambda)^{-1}$, so
$$D(C^p)[H]=\frac{\sin\pi p}{\pi}\int_0^\infty\lambda^p(C+\lambda)^{-1}H(C+\lambda)^{-1}d\lambda\qquad(\texttt{transport:power-derivative}).$$
- D7.5.2 Convergence in norm: $C\ge c_0>0$, integrand $O(\lambda^p)$ at $0$, $O(\lambda^{p-2})$ at $\infty$, $p-2<-1$.
- D7.5.3 CP for the second child $B$: $\partial_B(A\#_pB)[H]=A^{1/2}D(C^p)[A^{-1/2}HA^{-1/2}]A^{1/2}$ and D7.5.1. So $\Phi_B(Z)=\frac{\sin\pi p}{\pi p}\int_0^\infty\lambda^pX_\lambda B^{1/2}ZB^{1/2}X_\lambda^*\,d\lambda$ with $X_\lambda=M^{-1/2}A^{1/2}(C+\lambda)^{-1}A^{-1/2}$. Each integrand is a sandwich $Z\mapsto XZX^*$ (CP), coefficient $\ge0$, integrals of CP maps are CP.
- D7.5.4 CP for the first child $A$: exchange symmetry (D7.3.2), $A\#_pB=B\#_{1-p}A$.
- D7.5.5 Unital: homogeneity (D7.3.5) gives $A\#_p(e^\epsilon B)=e^{p\epsilon}M$, so $\partial_BM[B]=pM$, i.e. $\Phi_B(I)=\frac1pM^{-1/2}\,pM\,M^{-1/2}=I$. Same for $A$ with $1-p$.
- D7.5.6 Chain rule along the path $D_1\to M_1\to M_2\to\dots\to M_m=M$ with edge weights $w_1,\dots,w_m$: the square-root normalizations cancel at successive vertices ($M_i^{1/2}$ produced by $\Phi_{i}$ is exactly what $\partial_{M_i}M_{i+1}[M_i^{1/2}\,\cdot\,M_i^{1/2}]$ consumes). So $M^{-1/2}\partial_{A_j}M[A_j^{1/2}ZA_j^{1/2}]M^{-1/2}=\bigl(\prod_iw_i\bigr)\Phi_{M_{m-1}}\circ\dots\circ\Phi_{D_1}(Z)$, and $\prod_iw_i=w_j$. Compositions of unital CP maps are unital CP. Empty path: identity.
- D7.5.7 Blocks: block-diagonal inputs $\Rightarrow$ $C$, $(C+\lambda)^{-1}$, congruence factors block diagonal; a sandwich by a block-diagonal $X$ acts blockwise, $(XHX^*)_{ab}=X_aH_{ab}X_b^*$, and its first block uses only first blocks of the inputs. Same after exchanging children and after composing.

**Output.** $\sigma_{j,u}$ (D7.14); $\operatorname{Tr}\sigma=1$, endpoint bounds (D7.26); blocks: $\widehat\Phi_{i,j}$ (D7.22); unital CP for Schwarz (D7.23).

**Standard?** $D(C^p)$: Daleckii–Krein. CP along a mean tree, block restriction: specific to this paper.

**Pitfall.** Normalization divides by the *edge* weight $w$; $\Phi_j$ carries $w_j=\prod w_i$ outside (`transport:leaf-map`). Same $\Phi_{(h,\mathrm{old})}$ appears with $(1-p)w_h$ in leaf maps, $w_h$ in $\partial_p$ (D7.15).

---

### 7.2 Fourier formulas for inverse powers

#### D7.6 Def — The multipliers $g_s$ and $m_s$ (`transport:fourier-density`)
*Source: 06-transport.tex 181–192.*

**Statement.** For $0<s<1/2$:
$$g_s(z)=\frac{\sinh(sz)}{\sinh(z/2)},\quad g_s(0)=2s;\qquad m_s(u)=\frac{\sin(2\pi s)}{\cosh(2\pi u)+\cos(2\pi s)}.$$

**Used from.** none.

**Output.** $s=1/4$ in Proposition 7.4: $m_{1/4}(u)=1/\cosh(2\pi u)$, $\int m_{1/4}=1/2$.

**Standard?** $g_s$: rescaled kernel of Bhatia–Parthasarathy (2000, Thm 3.2). Shifted-density comparison: this paper.

#### D7.7 Lemma 7.3 — The two Fourier multipliers
*Source: 06-transport.tex 194–243; `transport:g-fourier`, `transport:h-def`, `transport:q-density`.*

**Statement.** Fix $0<s<1/2$.
1. For real $z$: $g_s(z)=\int_{\mathbb R}e^{iuz}m_s(u)du$, $m_s>0$, $\int_{\mathbb R}m_s=2s$.
2. For $s=1/4$ the functions (quotients read continuously at $0$)
$$h_\pm(z)=\frac{e^{\pm sz}-1}{2\sinh(z/2)}=\pm e^{\pm sz/2}g_{s/2}(z)$$
have Fourier densities $q_\pm(u)=\pm m_{s/2}(u\pm is/2)$, i.e. $h_\pm(z)=\int e^{iuz}q_\pm(u)du$, with
$$|q_\pm(u)|\le\tfrac1{\sqrt2}\,m_s(u).$$

**Used from.** D7.6.

**Proof.**
- D7.7.1 Poles. $\cosh2\pi u=-\cos2\pi s=\cos(\pi-2\pi s)$ $\Leftrightarrow$ $u=\pm i(\tfrac12-s)+in$. In the strip $0<\Im u<1$: $u_0=i(\tfrac12-s)$, $u_1=i(\tfrac12+s)$. Residues of $m_s$: $\sin(2\pi s)/(2\pi\sinh2\pi u_k)$ with $\sinh(2\pi u_0)=i\sin2\pi s$, $\sinh(2\pi u_1)=-i\sin2\pi s$ $\Rightarrow$ $\tfrac1{2\pi i}$ and $-\tfrac1{2\pi i}$.
- D7.7.2 Rectangle between $\mathbb R$ and $\mathbb R+i$, fixed $z\ne0$. Vertical sides vanish ($m_s$ decays like $e^{-2\pi|\Re u|}$). Periodicity $m_s(u+i)=m_s(u)$ gives $\int_{\mathbb R+i}=e^{-z}\int_{\mathbb R}$. Residue theorem: $(1-e^{-z})\int e^{iuz}m_s\,du=e^{-(1/2-s)z}-e^{-(1/2+s)z}$.
- D7.7.3 Divide: $\frac{e^{-z/2}\,2\sinh(sz)}{1-e^{-z}}=\frac{\sinh sz}{\sinh(z/2)}$. Value at $0$ by dominated convergence: $\int m_s=\lim_{z\to0}g_s(z)=2s$.
- D7.7.4 Positivity: $\sin2\pi s>0$ and $\cosh2\pi u+\cos2\pi s>0$ since $\cos2\pi s>-1$.
- D7.7.5 Algebra of $h_\pm$. $e^{\pm sz}-1=e^{\pm sz/2}\bigl(\pm2\sinh(sz/2)\bigr)$, so $h_\pm=\pm e^{\pm sz/2}\frac{\sinh(sz/2)}{\sinh(z/2)}=\pm e^{\pm sz/2}g_{s/2}(z)$.
- D7.7.6 Densities. $e^{\pm sz/2}e^{iuz}=e^{i(u\mp is/2)z}$. Substituting $u'=u\mp is/2$ moves the line of integration to $\mathbb R\mp is/2$ and the density to $m_{s/2}(u'\pm is/2)$. The nearest poles of $m_{s/2}$ have $|\Im|=\tfrac12-\tfrac s2>\tfrac s2$ ($s<1/2$), so shifting back to $\mathbb R$ crosses no pole. Gives $q_\pm$.
- D7.7.7 Bound at $s=1/4$ (so $s/2=1/8$). Put $c=\cosh2\pi u$. $m_s=1/c$ ($\sin\frac\pi2=1$, $\cos\frac\pi2=0$). $\cosh(2\pi u\pm i\tfrac\pi4)=\tfrac1{\sqrt2}(c\pm i\sinh2\pi u)$, so $m_{1/8}(u\pm\tfrac i8)=\dfrac{1/\sqrt2}{\tfrac1{\sqrt2}(c\pm i\sinh2\pi u)+\tfrac1{\sqrt2}}=\dfrac1{c+1\pm i\sinh2\pi u}$. $|c+1\pm i\sinh|^2=(c+1)^2+c^2-1=2c(c+1)$. Ratio to $m_s$: $\dfrac{c}{\sqrt{2c(c+1)}}=\sqrt{\dfrac{c}{2(c+1)}}\le\dfrac1{\sqrt2}$.

**Output.** Item 1 in D7.16; item 2 in D7.23. At $s=1/4$: $\int m_s=\tfrac12$, $\int|q_\pm|\le\tfrac1{2\sqrt2}$.

**Standard?** Item 1: classical (Bhatia–Parthasarathy). Item 2, constant $1/\sqrt2$: specific to this paper.

**Pitfall.** $|q_\pm|\le m_s/\sqrt2$ checked only at $s=1/4$, against $m_s$ (not $m_{s/2}$); feeds the exact $\tfrac14$ in D7.23.

---

### 7.3 Finite histories and entropy gains

#### D7.8 Def — Band metric and finiteness conventions (`transport:band-metric`)
*Source: 06-transport.tex 9–10, 247–258.*

**Statement.** All trees, one-copy spaces and partitions are finite and fixed before $k\to\infty$. $\mathcal V$ = finite tensor product of one-copy physical and auxiliary spaces, $\mathcal S_k=\operatorname{Sym}^k\mathcal V$. $W_{Q,k}$ from `replicas:w-definition` (common padding dimension $\dim\mathcal V$), $k$ suppressed. A partition $(P,Y,F)$ of the tensor factors has band metric
$$A(P,Y,F)=(W_P^{-1}W_F^{-1}W_Y)^2\quad\text{on }\mathcal S_k.$$
The three factors commute and are positive definite.

**Used from.** D6.5 (`replicas:w-definition`), D6.6 (Lemma 6.2: positivity, centrality), D6.8 (`replicas:leaf-metric`: same operator, written $A_k(P,Y,F)$).

**Output.** $A_{h,g}$, $A_{h,c,g}$ of D7.9.

**Standard?** Specific to this paper.

#### D7.9 Def — A round: history tree, choice trees, interpolated root $\mathcal M(p)$
*Source: 06-transport.tex 260–319; `transport:terminal-weights`, Figure `transport:tree-figure`.*

**Statement.** Data: $K\in\mathbb Z_{>0}$ bands; weighted history tree with leaves $h\in\mathcal H$, weights $w_h>0$ ($\sum_hw_h=1$); for each $(h,g)$ an old partition $(P_{h,g},Y_{h,g},F_{h,g})$; for each $h$ a conditional choice tree with leaves $c\in\mathcal C_h$, weights $q_{c\mid h}>0$ ($\sum_cq_{c\mid h}=1$). A choice $c$ specifies a new partition in every band $g$, obtained from the old one by doing nothing or by transferring a tensor subsystem $x\subseteq Y$ entirely to $P$ or entirely to $F$. Metrics: $A_{h,g}$, $A_{h,c,g}$ (D7.8) and
$$A_h=\prod_{g=1}^KA_{h,g},\qquad A_{h,c}=\prod_{g=1}^KA_{h,c,g}.$$
Commutation condition: every old or new metric of band $g$ commutes with every old or new metric of band $g'\ne g$, across all histories and choices. No commutation within a band is required.

$B_h$ = root of the choice tree with inputs $A_{h,c}$. For one common $p\in[0,1]$, replace each old input $h$ of the history tree by $M_h=A_h\#_pB_h$; call the root $\mathcal M(p)$. Terminal leaves for $0<p<1$:
$$j=(h,\mathrm{old}):\ \pi_j=(1-p)w_h,\ \text{metric }A_h;\qquad j=(h,c,\mathrm{new}):\ \pi_j=p\,w_hq_{c\mid h},\ \text{metric }A_{h,c}.$$
At $p=1$ this is the history tree with choice trees attached: the old tree of the next round.

**Used from.** D7.2, D7.8.

**Output.** $\mathcal M(p)$, $\pi_j$ for D7.14–D7.27. Check: $\sum_j\pi_j=\sum_hw_h[(1-p)+p\sum_cq_{c\mid h}]=1$.

**Standard?** Specific to this paper.

**Pitfall.** $\pi_{(h,\mathrm{old})}=(1-p)w_h$ but the derivative in $p$ weights the old leaf by $w_h$ (D7.15).

#### D7.10 Def — Entropy of a move, scale $\ell$, smallness (`transport:move-eta`)
*Source: 06-transport.tex 321–334.*

**Statement.** For unit $\theta\in\mathcal V$ and a move of $x$ to $P$ with $Y=xY_0$:
$$\eta_{h,c,g}(\theta)=S_\theta(x\mid P)+S_\theta(x\mid Y_0)=I_\theta(x:F\mid P)\ge0.$$
Move to $F$: exchange $P,F$. No move: $\eta_{h,c,g}=0$. The equality holds by purity of $\theta$ on $PxY_0F$. $\ell\ge1$ with $\log(e\dim x)\le\ell$ for every transferred $x$. Smallness (Lemmas 6.3, 5.3): $t<1/4$, $a\ell\le c_0$, $c_0$ small absolute constant (Lemma 6.3 asks $a\log(e\dim x)\le c$, $c$ of Lemma 5.1).

**Used from.** D2.1 (conditional entropy, mutual information), D6.10 (same $\eta_\theta$), D5.5 through $c_0$.

**Output.** $\eta_{h,c,g}$ in `transport:entropy-gain` (D7.20).

**Standard?** Specific to this paper.

#### D7.11 Def — Energy terms, designated supports, splits
*Source: 06-transport.tex 336–352.*

**Statement.** $0\le h_i\le I$ act on physical tensor factors, $i$ in a finite index set; $D_i$ designated tensor support $\supseteq\operatorname{supp}h_i$. For each terminal leaf $j$ and each band: $D_i$ lies in one of the three parts $P,Y,F$ of the leaf's partition, except possibly in one exceptional band, where $D_i$ meets $Y$ and exactly one of $P,F$. Such a leaf is a *split of $i$*; $\mathcal J_i$ = set of split leaves. At a split: $x=D_i\cap Y$, receiving side = the part $P$ or $F$ met by $D_i$, $\eta_{i,j}$ = D7.10 formula for this $x$ and side. Required: $\log(e\dim D_i)\le\ell$ for every $i$ with $\mathcal J_i\ne\varnothing$ (together with smallness of $a\ell$), and for all transferred subsystems. No dimension bound for terms unsplit at every leaf.

**Used from.** D7.9, D7.10.

**Output.** $\mathcal J_i$, $\eta_{i,j}$ in `transport:energy`; hypotheses of Lemma 6.4 in D7.24.

**Standard?** Specific to this paper.

#### D7.12 Step — Replica energy and commutation at unsplit leaves (`transport:replica-energy`)
*Source: 06-transport.tex 354–365.*

**Statement.**
$$\bar h_i=\Bigl.\tfrac1k\sum_{r=1}^kh_{i,r}\Bigr|_{\mathcal S_k},\qquad\bar H=\sum_i\bar h_i,\qquad W_i(p)=\sum_{j\in\mathcal J_i}\pi_j.$$
$h_{i,r}$ = $h_i$ acting on copy $r$. If leaf $j$ does not split $i$, then $[A_j,\bar h_i]=0$.

**Used from.** D7.8, D7.11; D6.5, D6.9 (same remark for $h$ inside one part).

**Proof.**
- D7.12.1 In every band $D_i$ lies in one part $Q\in\{P,Y,F\}$. $\sum_rh_{i,r}$ is invariant under copy permutations acting on the copies of $Q$ ($\pi_Qh_{i,r}\pi_Q^{-1}=h_{i,\pi(r)}$), and commutes with permutations acting only on the complement of $Q$ (disjoint support).
- D7.12.2 The metric of the band is a function of Schur labels of permutations on each of $P,Y,F$; by D7.12.1 $\bar h_i$ commutes with each. Apply in every band.

**Output.** $\mathsf D_{i,j}=0$ at unsplit leaves (D7.21); $K_{i,j}=0$ for $j\notin\mathcal J_i$ (D7.22).

**Standard?** Specific to this paper.

#### D7.13 Def — Coherent vectors and measures (`transport:coherent-measure`)
*Source: 06-transport.tex 367–375.*

**Statement.**
$$P_{\theta,k}=|\theta^{\otimes k}\rangle\langle\theta^{\otimes k}|,\quad D_k=\dim\mathcal S_k,\quad d\mu_\sigma(\theta)=D_k\operatorname{Tr}(\sigma P_{\theta,k})\,d\theta,$$
$d\theta$ = Haar probability on the unit sphere of $\mathcal V$. For a density matrix $\sigma$ on $\mathcal S_k$, $\mu_\sigma$ is a probability measure since $D_k\int P_{\theta,k}d\theta=I_{\mathcal S_k}$. Also $D_k=\binom{k+\dim\mathcal V-1}{\dim\mathcal V-1}$, polynomial in $k$.

**Used from.** D6.11 (`replicas:resolution`, `replicas:husimi`: same measure).

**Output.** $\mu_{\sigma_{j,u}}$ in D7.14.

**Standard?** Standard (coherent-state / de Finetti measure, Christandl et al. 2007, Lewin–Nam–Rougerie 2015).

---

### 7.4 Entropy and energy transport

#### D7.14 Proposition 7.4 — Entropy and energy transport
*Source: 06-transport.tex 377–434 (statement), 436–771 (proof); `transport:filtered-vector`, `transport:states`, `transport:exact-derivative`, `transport:entropy-gain`, `transport:energy`.*

**Statement.** Fix: finite $\mathcal V$, history and choice trees, partitions, cross-band commutation (D7.9), $a>0$, contractions $h_i$ with designated supports (D7.11). Let $\ell$ bound $\log(e\dim\cdot)$ of every transferred subsystem and every $D_i$ with $\mathcal J_i\ne\varnothing$, with $a\ell$ small (D7.10). For every $k$ and nonzero $\mathrm{pre}\in\mathcal S_k$:
$$s=\tfrac14,\quad N(p)=\|\mathcal M(p)^{-s}\mathrm{pre}\|,\quad v(p)=\frac{\mathcal M(p)^{-s}\mathrm{pre}}{N(p)}.$$
For $0<p<1$, $\Phi_j$ = normalized map of leaf $j$ to $\mathcal M(p)$ (Lemma 7.2), and for $u\in\mathbb R$
$$\sigma_{j,u}=\Phi_j^*\bigl(|\mathcal M(p)^{-iu}v(p)\rangle\langle\mathcal M(p)^{-iu}v(p)|\bigr),$$
$\operatorname{Tr}(\Phi_j^*(\sigma)Z)=\operatorname{Tr}(\sigma\Phi_j(Z))$. $\sigma_{h,u}$ := state at $j=(h,\mathrm{old})$, $C_h=A_h^{-1/2}B_hA_h^{-1/2}$.

(a) Exact derivative:
$$-\partial_p\log N(p)^2=\sum_hw_h\int_{\mathbb R}m_s(u)\operatorname{Tr}(\sigma_{h,u}\log C_h)\,du.$$
(b) There is $\beta_k=O_{\rm fixed}(\log(k+1))$, independent of $p$ and $\mathrm{pre}$, with
$$-\partial_p\log N^2\ge ka\sum_{h,g}w_h\int m_s(u)\int\sum_{c\in\mathcal C_h}q_{c\mid h}\,\eta_{h,c,g}(\theta)\,d\mu_{\sigma_{h,u}}(\theta)\,du\;-\;CkaK\,a^{1/4}\ell^C-\beta_k.$$
(c) If moreover $\bar H\mathrm{pre}=E_0\mathrm{pre}$:
$$\langle v,\bar Hv\rangle\le2E_0+Ca^2\ell^C\sum_iW_i(p)\sum_{j\in\mathcal J_i}\pi_j\int m_s(u)\int\eta_{i,j}(\theta)^{1/8}d\mu_{\sigma_{j,u}}(\theta)\,du+o_k(1).$$
The $o_k(1)$ is uniform in $p\in(0,1)$, in nonzero $\mathrm{pre}$ with the eigenvector property, and in all replica states. $C$ and the exponents called $C$ are universal; support dimensions enter only through $\ell$. Only the implicit constant in $\beta_k$ and the rate of $o_k(1)$ depend on the whole fixed finite data, never on $p$ or on the replica state. (b) may be integrated over any closed subinterval of $[0,1]$ using the continuous endpoint values of $N$.

**Used from.** D7.3 (items 1, 3, 5, 6), D7.5, D7.6, D7.7, D7.8–D7.13; D6.10 (Lemma 6.3); D6.12 (Lemma 6.4), inside it D5.15 (Lemma 5.3).

**Proof.** D7.15–D7.16: (a); D7.17–D7.20: (b); D7.21–D7.25: (c); D7.26: endpoints, uniformity.

**Output.** (a)–(b): §9 `scanner:charge-gain`, telescoped over rounds. (c): §9 at the same $p$. Shared state: D7.27.

**Standard?** Specific to this paper; matrix means standard.

**Pitfall.** (c) contains $W_i(p)\cdot\sum_{j\in\mathcal J_i}\pi_j$: the split weight appears twice (D7.23). $\ell$ bounds $\log(e\dim D_i)$ only for split terms.

#### D7.15 Step — Derivative at an interpolating vertex
*Source: 06-transport.tex 441–464; `transport:node-p-derivative`, `transport:root-p-derivative`.*

**Statement.** At $M_h=A_h\#_pB_h$, $V_h=C_h^{p/2}A_h^{1/2}M_h^{-1/2}$ is unitary and
$$M_h^{-1/2}(\partial_pM_h)M_h^{-1/2}=V_h^*(\log C_h)V_h=\Phi_{A_h}(\log C_h),$$
$\Phi_{A_h}$ = normalized old-child map at this vertex (weight $1-p$). Hence at the root
$$\mathsf H:=\mathcal M^{-1/2}(\partial_p\mathcal M)\mathcal M^{-1/2}=\sum_hw_h\,\Phi_{(h,\mathrm{old})}(\log C_h).$$

**Used from.** D7.5, D7.9.

**Proof.**
- D7.15.1 $V_h^*V_h=M^{-1/2}A^{1/2}C^pA^{1/2}M^{-1/2}=M^{-1/2}MM^{-1/2}=I$; finite dimension $\Rightarrow$ unitary.
- D7.15.2 $\partial_pM_h=A^{1/2}C^p(\log C)A^{1/2}$ ($C^p$, $\log C$ commute). Then $M^{-1/2}\partial_pMM^{-1/2}=M^{-1/2}A^{1/2}C^{p/2}(\log C)C^{p/2}A^{1/2}M^{-1/2}=V^*(\log C)V$.
- D7.15.3 Identification with $\Phi_{A_h}(\log C)$. Perturb $A\to A^{1/2}(I+\delta\log C)A^{1/2}$, $B$ fixed. Congruence by $A^{-1/2}$ (D7.3.1) gives inputs $I+\delta\log C$ and $C$, which commute: $(I+\delta\log C)\#_pC=(I+\delta\log C)^{1-p}C^p$. $\frac{d}{d\delta}|_0=(1-p)C^p\log C$. So $\partial_AM[A^{1/2}(\log C)A^{1/2}]=(1-p)A^{1/2}C^p(\log C)A^{1/2}$; divide by $1-p$ (D7.5 normalization) and compare with D7.15.2.
- D7.15.4 Root. $p$ enters $\mathcal M$ only through the $M_h$ ($w_h,q_{c\mid h},B_h$ do not depend on $p$). $\partial_p\mathcal M=\sum_h\partial_{M_h}\mathcal M[M_h^{1/2}\Phi_{A_h}(\log C_h)M_h^{1/2}]$. History path from vertex $M_h$ to the root has weight $w_h$, so Lemma 7.2 gives $\mathsf H=\sum_hw_h\Phi^{\rm path}_h(\Phi_{A_h}(\log C_h))=\sum_hw_h\Phi_{(h,\mathrm{old})}(\log C_h)$.

**Output.** $\mathsf H$ in D7.16.

**Standard?** Specific to this paper.

**Pitfall.** Coefficient $w_h$, not the terminal weight $(1-p)w_h$: the factor $1-p$ was divided out in D7.15.3.

#### D7.16 Step — Exact formula for $-\partial_p\log N^2$ (part (a))
*Source: 06-transport.tex 466–485; `transport:norm-derivative`, `transport:exact-derivative`.*

**Statement.**
$$-\partial_p\log N^2=\bigl\langle v,\,g_s(\operatorname{ad}_{\log\mathcal M})(\mathsf H)\,v\bigr\rangle=\sum_hw_h\int m_s(u)\operatorname{Tr}(\sigma_{h,u}\log C_h)du.$$
$\sigma_{j,u}$ is a density matrix for all $j,u$.

**Used from.** D7.5, D7.7 (item 1), D7.15.

**Proof.**
- D7.16.1 $N^2=\langle\mathrm{pre},\mathcal M^{-2s}\mathrm{pre}\rangle$, $\mathrm{pre}=N\mathcal M^sv$. Diagonalize $\mathcal M=\sum_rx_r|r\rangle\langle r|$. Daleckii–Krein: $D(\mathcal M^{-2s})[X]_{rt}=\frac{x_r^{-2s}-x_t^{-2s}}{x_r-x_t}X_{rt}$. With $X=\partial_p\mathcal M=\mathcal M^{1/2}\mathsf H\mathcal M^{1/2}$, $X_{rt}=(x_rx_t)^{1/2}\mathsf H_{rt}$.
- D7.16.2 $-\partial_p\log N^2=\sum_{r,t}\bar v_rv_t\,\Bigl[-(x_rx_t)^{s+1/2}\frac{x_r^{-2s}-x_t^{-2s}}{x_r-x_t}\Bigr]\mathsf H_{rt}$ (the factors $x_r^sx_t^s$ come from $\mathcal M^sv$ on both sides).
- D7.16.3 The bracket equals $g_s(\log x_r-\log x_t)$. With $x_r=e^\alpha$, $x_t=e^\beta$, $\delta=\alpha-\beta$: $x_r^{-2s}-x_t^{-2s}=-2e^{-s(\alpha+\beta)}\sinh(s\delta)$, $x_r-x_t=2e^{(\alpha+\beta)/2}\sinh(\delta/2)$; the sign of the bracket flips the first sign and $e^{(s+1/2)(\alpha+\beta)}$ cancels: bracket $=\sinh(s\delta)/\sinh(\delta/2)$. Equal eigenvalues: derivative of $x^{-2s}$ gives $-x^{2s+1}(-2s)x^{-2s-1}=2s=g_s(0)$.
- D7.16.4 $\operatorname{ad}_{\log\mathcal M}$ multiplies the $(r,t)$ entry by $\log x_r-\log x_t$. So D7.16.2 is $\langle v,g_s(\operatorname{ad}_{\log\mathcal M})(\mathsf H)v\rangle$ (`transport:norm-derivative`).
- D7.16.5 Lemma 7.3(1): $g_s(\operatorname{ad}_{\log\mathcal M})(\mathsf H)=\int m_s(u)\mathcal M^{iu}\mathsf H\mathcal M^{-iu}du$. So $-\partial_p\log N^2=\int m_s(u)\langle\mathcal M^{-iu}v,\mathsf H\mathcal M^{-iu}v\rangle du$.
- D7.16.6 Insert $\mathsf H$ (D7.15). $\langle\psi,\Phi(Z)\psi\rangle=\operatorname{Tr}(\Phi^*(|\psi\rangle\langle\psi|)Z)$. With $\psi=\mathcal M^{-iu}v$ this is $\operatorname{Tr}(\sigma_{h,u}Z)$.
- D7.16.7 $\sigma_{j,u}\ge0$ ($\Phi_j$ CP), $\operatorname{Tr}\sigma_{j,u}=\langle\psi,\Phi_j(I)\psi\rangle=\|\psi\|^2=1$ ($\Phi_j$ unital, $\mathcal M^{-iu}$ unitary).

**Output.** $\sigma_{j,u}$ in D7.20, D7.23–D7.25, §9 (`scanner:Q-definition`).

**Standard?** Specific to this paper.

#### D7.17 Step — Factorization of the relative metric over bands (`transport:relative-factorization`)
*Source: 06-transport.tex 487–500.*

**Statement.** $\mathcal M=\prod_g\mathcal M_g$, $\mathcal M_g$ = tree evaluated on band-$g$ inputs. With $B_{h,g}$ = conditional tree of new metrics in band $g$:
$$C_h=\prod_gC_{h,g},\quad C_{h,g}=A_{h,g}^{-1/2}B_{h,g}A_{h,g}^{-1/2},\quad\log C_h=\sum_g\log C_{h,g}.$$
$C_{h,g}$ is the conditional choice tree of the single-move relative metrics $A_{h,g}^{-1/2}A_{h,c,g}A_{h,g}^{-1/2}$.

**Used from.** D7.3 (items 1, 6), D7.9.

**Proof.**
- D7.17.1 Item 6 applied to the history tree (inputs $A_h\#_pB_h$ factorized by band), to the choice trees ($B_h=\prod_gB_{h,g}$), and to the vertex ($A_h\#_pB_h=\prod_gA_{h,g}\#_pB_{h,g}$): all factor over bands, factors commute.
- D7.17.2 $C_h=\prod_gA_{h,g}^{-1/2}\prod_gB_{h,g}\prod_gA_{h,g}^{-1/2}=\prod_gC_{h,g}$ (cross-band commutation); commuting positive factors $\Rightarrow$ $\log C_h=\sum_g\log C_{h,g}$.
- D7.17.3 Congruence (item 1, $S=A_{h,g}^{-1/2}$) applied to the choice tree: $C_{h,g}=\mathcal T_{\rm choice}\bigl(A_{h,g}^{-1/2}A_{h,c,g}A_{h,g}^{-1/2}:c\bigr)$.

**Output.** Reduces D7.20 to one band and one choice tree at a time.

**Standard?** Specific to this paper.

#### D7.18 Step — Conditional pin (`transport:conditional-pin`)
*Source: 06-transport.tex 501–518.*

**Statement.** There is $b_k>0$, $-\log b_k=O_{\rm fixed}(\log(k+1))$, $b_k\le1$, such that for every unit $\theta$, every $h,g$, on $\mathcal S_k$:
$$C_{h,g}\ge b_k\exp\Bigl(ka\Bigl[\sum_cq_{c\mid h}\eta_{h,c,g}(\theta)-Ca^{1/4}\ell^C\Bigr]\Bigr)P_{\theta,k}.$$

**Used from.** D6.10 (Lemma 6.3, `replicas:relative-pin`); D7.3 item 5; D7.10, D7.17.

**Proof.**
- D7.18.1 Single move. Lemma 6.3 (its hypotheses $t<1/4$, $a\log(e\dim x)\le c_0$ hold by D7.10): $A_{h,g}^{-1/2}A_{h,c,g}A_{h,g}^{-1/2}\ge b_k\exp\bigl(ka[\eta_{h,c,g}(\theta)-Ca^{1/4}\ell^C]\bigr)P_{\theta,k}$, with $\log^C(e\dim x)\le\ell^C$ (since $\ell\ge1$).
- D7.18.2 Common $b_k$: finitely many moves, take the smallest polynomial prefactor. No-move choice: relative metric $=I$, inequality holds after decreasing $b_k$ to at most $1$ ($\eta=0$, $P_\theta\le I$).
- D7.18.3 Projection transfer (D7.3 item 5) in the choice tree, $P:=P_{\theta,k}$, constants $c_c=b_k\exp(ka[\eta_{h,c,g}-Ca^{1/4}\ell^C])$: root $\ge\prod_cc_c^{q_{c\mid h}}P$. Since $\sum_cq_{c\mid h}=1$, $\prod_cb_k^{q_{c\mid h}}=b_k$ (one polynomial factor), and the exponents average to $\sum_cq_{c\mid h}\eta_{h,c,g}-Ca^{1/4}\ell^C$.

**Output.** Pointwise rank-one lower bound for D7.19–D7.20.

**Standard?** Specific to this paper.

#### D7.19 Step — Operator Jensen for coherent integrals (`transport:log-jensen`)
*Source: 06-transport.tex 520–547.*

**Statement.** $\mathcal Q_k(f)=D_k\int f(\theta)P_{\theta,k}\,d\theta$ is a unital positive map from functions to operators on $\mathcal S_k$, and for positive bounded $f$ bounded away from $0$:
$$\mathcal Q_k(f)^{-1}\le\mathcal Q_k(f^{-1}),\qquad\log\mathcal Q_k(f)\ge\mathcal Q_k(\log f).$$
The logarithm is operator monotone on positive definite operators.

**Used from.** D7.13, D6.11 (`replicas:resolution`: $D_k\int P_{\theta,k}d\theta=I$).

**Proof.**
- D7.19.1 $\mathcal Q_k(1)=I$. Positivity: $f\ge0\Rightarrow\mathcal Q_k(f)\ge0$.
- D7.19.2 For each $\theta$, $\begin{pmatrix}f&1\\1&f^{-1}\end{pmatrix}\ge0$ (positive entries, determinant $0$). Integrating against $D_kP_{\theta,k}\,d\theta$: $\begin{pmatrix}\mathcal Q_k(f)&I\\I&\mathcal Q_k(f^{-1})\end{pmatrix}\ge0$. Schur complement ($\mathcal Q_k(f)\ge\inf f>0$): $\mathcal Q_k(f)^{-1}\le\mathcal Q_k(f^{-1})$.
- D7.19.3 Apply to $f+\lambda$, $\mathcal Q_k(f+\lambda)=\mathcal Q_k(f)+\lambda I$: $(\mathcal Q_k(f)+\lambda)^{-1}\le\mathcal Q_k((f+\lambda)^{-1})$.
- D7.19.4 Scalar formula $\log x=\int_0^\infty\bigl((1+\lambda)^{-1}-(x+\lambda)^{-1}\bigr)d\lambda$ applied to $\mathcal Q_k(f)$, then D7.19.3 and $\mathcal Q_k(1)=I$: $\log\mathcal Q_k(f)\ge\int\bigl((1+\lambda)^{-1}I-\mathcal Q_k((f+\lambda)^{-1})\bigr)d\lambda=\mathcal Q_k(\log f)$. Integrals converge in norm on compact positive spectral intervals.
- D7.19.5 Monotone log: the same formula and order-reversal of inversion.

**Output.** Converts D7.18 into an operator inequality for $\log C_{h,g}$ (D7.20).

**Standard?** Operator Jensen for unital positive maps (Choi, Davis; Hansen–Pedersen); elementary proof given.

#### D7.20 Step — Entropy gain (part (b), `transport:log-relative`, `transport:entropy-gain`)
*Source: 06-transport.tex 549–572.*

**Statement.**
$$\log C_{h,g}\ge ka\,\mathcal Q_k\Bigl(\sum_cq_{c\mid h}\eta_{h,c,g}-Ca^{1/4}\ell^C\Bigr)+(\log b_k-\log D_k)I.$$
Consequently Proposition 7.4(b) holds with $\beta_k=\tfrac K2(\log D_k-\log b_k)$.

**Used from.** D7.16, D7.17, D7.18, D7.19, D7.13.

**Proof.**
- D7.20.1 Integrate D7.18 over $\theta$ ($\int d\theta=1$): $C_{h,g}\ge\frac{b_k}{D_k}\mathcal Q_k\bigl(\exp\{ka[\sum_cq_{c\mid h}\eta_{h,c,g}-Ca^{1/4}\ell^C]\}\bigr)$ (since $\int P_{\theta,k}\,\phi(\theta)d\theta=D_k^{-1}\mathcal Q_k(\phi)$).
- D7.20.2 The exponential symbol is positive and bounded away from $0$ for fixed $k$ ($\eta$ bounded in the fixed one-copy space). Log monotone, then Jensen (D7.19): $\log C_{h,g}\ge\log\frac{b_k}{D_k}I+\log\mathcal Q_k(\exp\{\cdot\})\ge(\log b_k-\log D_k)I+ka\,\mathcal Q_k(\sum_cq\eta-Ca^{1/4}\ell^C)$.
- D7.20.3 Expectation in the trace-one $\sigma_{h,u}$: $\operatorname{Tr}(\sigma\mathcal Q_k(f))=\int f\,d\mu_\sigma$ ($\mu_\sigma$ probability measure, constants integrate to themselves).
- D7.20.4 Sum over $g$ using D7.17 ($K$ bands), then over $h$ with $\sum_hw_h=1$, then in $u$ with $\int m_s=\tfrac12$ (D7.7): the error terms become $\tfrac12KkaCa^{1/4}\ell^C+\tfrac K2(\log D_k-\log b_k)$. $D_k$ polynomial in $k$ and $-\log b_k=O_{\rm fixed}(\log(k+1))$, so $\beta_k=O_{\rm fixed}(\log(k+1))$. $\tfrac12$ absorbed in $C$.

**Output.** Part (b). §9 telescopes it over rounds and integrates over $p$ in $[\epsilon/2,\epsilon]$.

**Standard?** Specific to this paper.

**Pitfall.** $D_k$ enters only once additively as $\log D_k$ (no factor $D_k$ survives after taking expectations); $b_k$ uniform over finitely many moves.

#### D7.21 Step — Auxiliary positive metric for each energy term
*Source: 06-transport.tex 579–644; `transport:unsplit-block`, `transport:rank-deficient-B`, `transport:skew-square`.*

**Statement.** For each $i$ with $T_i\ne0$ and each leaf $j$ there are a positive definite $B_{i,j}$ on $\mathcal D=\operatorname{ran}T_i$ and maps $Y_{i,j},Z_{i,j}:\mathcal S_k\to\mathcal D$ with
$$\mathsf D_{i,j}:=(Y_{i,j}-Z_{i,j})^*(Y_{i,j}-Z_{i,j})=|O_{i,j}^*|+|O_{i,j}|-O_{i,j}-O_{i,j}^*\ge0,$$
$O_{i,j}=A_j^{-1/2}\bar h_iA_j^{1/2}$. $\mathsf D_{i,j}=0$ when $[A_j,\bar h_i]=0$ (in particular at unsplit leaves).

**Used from.** D7.12 (commutation at unsplit leaves).

**Proof.**
- D7.21.1 $T:\mathcal S_k\to\mathcal D$, $T=h_i^{1/2}$ on the last copy restricted to $\mathcal S_k$. $T^*T=\bar h_i$ (matrix elements of any marked copy agree between symmetric vectors). $T=0$: term contributes nothing, omit. Otherwise $T$ surjective onto $\mathcal D$.
- D7.21.2 Commuting leaf. Polar decomposition $T=U|T|$, $U:\operatorname{supp}|T|\to\mathcal D$ unitary; $A_j$ commutes with $|T|=\bar h_i^{1/2}$ so $\operatorname{supp}|T|$ is $A_j$-invariant. $B_{i,j}:=U(A_j|_{\operatorname{supp}|T|})U^*$. Then $Y_{i,j}:=B^{1/2}TA_j^{-1/2}=UA_j^{1/2}|T|A_j^{-1/2}=U|T|=T$ and $Z_{i,j}:=B^{-1/2}TA_j^{1/2}=T$. $\mathsf D=0$.
- D7.21.3 Split leaf. $S_j=TA_j^{-1/2}$ (surjective), $Q_j=|O_{i,j}^*|$. $S_jS_j^*=TA_j^{-1}T^*>0$ on $\mathcal D$. $\operatorname{ran}O_{i,j}=A_j^{-1/2}\operatorname{ran}T^*=\operatorname{ran}S_j^*$ ($TA_j^{1/2}$ surjective), so $Q_j$ is strictly positive on $\operatorname{ran}S_j^*$. Define
$$B_{i,j}=(S_jS_j^*)^{-1}S_jQ_jS_j^*(S_jS_j^*)^{-1}.$$
- D7.21.4 $B_{i,j}>0$: $\langle d,Bd\rangle=\langle w,Q_jw\rangle$ with $w=S_j^*(S_jS_j^*)^{-1}d\in\operatorname{ran}S_j^*$, $w\ne0$ if $d\ne0$ ($S_jw=d$). $S_j^*BS_j=\Pi\,Q_j\,\Pi=Q_j$, $\Pi=S_j^*(S_jS_j^*)^{-1}S_j$ = projection onto $\operatorname{ran}S_j^*$.
- D7.21.5 $Y=B^{1/2}S_j$, $Z=B^{-1/2}TA_j^{1/2}$ (same formulas as D7.21.2). $Y^*Y=S_j^*BS_j=|O^*|$. $Y^*Z=A_j^{-1/2}T^*TA_j^{1/2}=O$.
- D7.21.6 $Y$ surjective $\Rightarrow$ $Y(Y^*Y)^+Y^*=I_{\mathcal D}$ ($+$ = inverse on support, $0$ on kernel). Multiply by $Z^*$ left, $Z$ right: $Z^*Z=O^*|O^*|^+O$. SVD $O=\sum_i\varsigma_i|a_i\rangle\langle b_i|$: $O^*|O^*|^+O=\sum_i\varsigma_i|b_i\rangle\langle b_i|=|O|$.
- D7.21.7 $\mathsf D=Y^*Y+Z^*Z-Y^*Z-Z^*Y=|O^*|+|O|-O-O^*$. Unsplit leaf: $O=\bar h_i\ge0$, $|O|=|O^*|=O$, formula gives $0$, consistent with D7.21.2. $\bar h_i$ is never inverted on its kernel.

**Output.** $B_{i,j}$ (blocks of $M_{i,j}$ in D7.22), $\mathsf D_{i,j}$ (D7.23–D7.24).

**Standard?** Specific to this paper.

**Pitfall.** At a split leaf $O_{i,j}=A_{j,g_0}^{-1/2}\bar h_iA_{j,g_0}^{1/2}$, $g_0$ the exceptional band (D7.24.1).

#### D7.22 Step — Transport of the commutator through the tree (`transport:block-rotation`)
*Source: 06-transport.tex 645–672.*

**Statement.** Evaluate the full terminal tree on $M_{i,j}=\operatorname{diag}(A_j,B_{i,j})$. Root $\mathbb M_i=\operatorname{diag}(\mathcal M,\mathcal B_i)$, normalized leaf maps $\widehat\Phi_{i,j}$ with first-block restrictions $\Phi_j$. With
$$L_i=\begin{pmatrix}0&T^*\\T&0\end{pmatrix},\quad K_{i,j}=M_{i,j}^{1/2}L_iM_{i,j}^{-1/2}-M_{i,j}^{-1/2}L_iM_{i,j}^{1/2},$$
$$2\sinh\bigl(\operatorname{ad}_{\log\mathbb M_i}/2\bigr)L_i=\sum_j\pi_j\widehat\Phi_{i,j}(K_{i,j}).$$
$K_{i,j}$ has lower-left block $Y_{i,j}-Z_{i,j}$, upper-right block $-(Y_{i,j}-Z_{i,j})^*$, upper-left block of $K_{i,j}^*K_{i,j}$ equal to $\mathsf D_{i,j}$, and $K_{i,j}=0$ for $j\notin\mathcal J_i$.

**Used from.** D7.5 (block statement), D7.3 (item 1), D7.21, D7.12.

**Proof.**
- D7.22.1 Block entries of $K$: $M^{\pm1/2}LM^{\mp1/2}$ has lower-left $B^{\pm1/2}TA^{\mp1/2}$ and upper-right $A^{\pm1/2}T^*B^{\mp1/2}$. Lower-left of $K$: $B^{1/2}TA^{-1/2}-B^{-1/2}TA^{1/2}=Y-Z$. Upper-right: $Z^*-Y^*=-(Y-Z)^*$. So $K^*=-K$ and $K^*K=\operatorname{diag}\bigl((Y-Z)^*(Y-Z),(Y-Z)(Y-Z)^*\bigr)$. $Y=Z=T$ at unsplit leaves, so $K=0$ there (D7.12, D7.21).
- D7.22.2 Rotation. Replace every input by $e^{itL}M_{i,j}e^{-itL}$. Congruence covariance with unitary $e^{-itL}$: the root becomes $e^{itL}\mathbb M_ie^{-itL}$. $\frac{d}{dt}|_0$: root $i[L,\mathbb M]$; leaf $j$: $i[L,M_j]$.
- D7.22.3 $[L,M]=-M^{1/2}KM^{1/2}$ (expand $M^{1/2}(M^{-1/2}LM^{1/2}-M^{1/2}LM^{-1/2})M^{1/2}=LM-ML$). So leaf perturbation $=-iM_j^{1/2}K_jM_j^{1/2}$, i.e. $Z=-iK_j$ in `transport:leaf-map`. Derivative at the root is the sum over leaves; Lemma 7.2 (leaf weight $\pi_j$): $\mathbb M^{-1/2}\,i[L,\mathbb M]\,\mathbb M^{-1/2}=-i\sum_j\pi_j\widehat\Phi_{i,j}(K_j)$.
- D7.22.4 Left side: in the eigenbasis of $\mathbb M$, entry $(r,t)$ of $\mathbb M^{-1/2}L\mathbb M^{1/2}-\mathbb M^{1/2}L\mathbb M^{-1/2}$ is $L_{rt}(e^{-\delta/2}-e^{\delta/2})=-2\sinh(\delta/2)L_{rt}$, $\delta=\log x_r-\log x_t$. So it equals $-2\sinh(\operatorname{ad}_{\log\mathbb M}/2)L$, and $i\cdot$ that. Cancel $-i$.
- D7.22.5 Block structure. For block-diagonal inputs each vertex mean is block diagonal with blocks the means of the blocks (functional calculus). So $\mathbb M_i=\operatorname{diag}(\mathcal M,\mathcal B_i)$ with $\mathcal B_i$ the root of the tree on $(B_{i,j})_j$. $\widehat\Phi_{i,j}$ is unital CP (D7.5), as all $B_{i,j}>0$ (D7.21).

**Output.** `transport:block-rotation` in D7.23.

**Standard?** Specific to this paper.

#### D7.23 Step — Bound on $E_{i,\pm}$ (`transport:E-def`, `transport:cp-schwarz`, `transport:block-bound`)
*Source: 06-transport.tex 673–713.*

**Statement.** With $\mathbb M_i=\operatorname{diag}(\mathcal M,\mathcal B_i)$ (D7.22), $E_{i,\pm}=\mathcal B_i^{\pm s}T\mathcal M^{\mp s}-T$, $s=\tfrac14$:
$$\|E_{i,\pm}v\|^2\le\tfrac14\,W_i\sum_{j\in\mathcal J_i}\pi_j\int_{\mathbb R}m_s(u)\operatorname{Tr}(\sigma_{j,u}\mathsf D_{i,j})\,du.$$
For unital CP $\Psi$: $\Psi(K)^*\Psi(K)\le\Psi(K^*K)$.

**Used from.** D7.7 (item 2), D7.5, D7.22, D7.16.7.

**Proof.**
- D7.23.1 Apply $h_\pm(\operatorname{ad}_{\log\mathbb M_i})$ to D7.22. $h_\pm(z)\cdot2\sinh(z/2)=e^{\pm sz}-1$, so the left side is $\mathbb M^{\pm s}L\mathbb M^{\mp s}-L$; its action on $(v,0)$ is $(0,E_{i,\pm}v)$ (lower-left block $\mathcal B^{\pm s}T\mathcal M^{\mp s}-T$).
- D7.23.2 Right side via $h_\pm(\operatorname{ad})X=\int q_\pm(u)\mathbb M^{iu}X\mathbb M^{-iu}du$ (Lemma 7.3(2)), blocks preserved, $K_{i,j}=0$ off $\mathcal J_i$:
$$(0,E_{i,\pm}v)=\sum_{j\in\mathcal J_i}\pi_j\int q_\pm(u)\,\mathbb M_i^{iu}\widehat\Phi_{i,j}(K_{i,j})\mathbb M_i^{-iu}(v,0)\,du.$$
- D7.23.3 Output phase $\mathbb M_i^{iu}$ unitary. Cauchy–Schwarz for the positive measure $\pi_j|q_\pm(u)|du$ on $(j,u)$, total mass $W_i\int|q_\pm|$:
$$\|E_{i,\pm}v\|^2\le W_i\Bigl(\int|q_\pm|\Bigr)\sum_{j\in\mathcal J_i}\pi_j\int|q_\pm(u)|\,\bigl\|\widehat\Phi_{i,j}(K_{i,j})(\mathcal M^{-iu}v,0)\bigr\|^2du.$$
- D7.23.4 Schwarz inequality for unital CP $\Psi$: the amplification $\Psi\otimes\mathrm{id}_2$ maps $\begin{pmatrix}K^*K&K^*\\K&I\end{pmatrix}\ge0$ to $\begin{pmatrix}\Psi(K^*K)&\Psi(K)^*\\\Psi(K)&I\end{pmatrix}\ge0$; Schur complement of $I$.
- D7.23.5 With $\Psi=\widehat\Phi_{i,j}$: $\|\widehat\Phi(K)(\psi,0)\|^2\le\langle(\psi,0),\widehat\Phi(K^*K)(\psi,0)\rangle=\langle\psi,\Phi_j(\mathsf D_{i,j})\psi\rangle=\operatorname{Tr}(\sigma_{j,u}\mathsf D_{i,j})$, $\psi=\mathcal M^{-iu}v$ (first-block restriction is $\Phi_j$; $(K^*K)_{11}=\mathsf D$).
- D7.23.6 $\int|q_\pm|\le\tfrac1{\sqrt2}\int m_s=\tfrac1{2\sqrt2}$ and $\int|q_\pm|\operatorname{Tr}(\sigma\mathsf D)du\le\tfrac1{\sqrt2}\int m_s\operatorname{Tr}(\sigma\mathsf D)du$ ($\mathsf D\ge0$). Product of constants: $\tfrac1{2\sqrt2}\cdot\tfrac1{\sqrt2}=\tfrac14$. Both signs identical.

**Output.** Input for D7.25.

**Standard?** Schwarz for unital CP (Choi): standard. Rest specific to this paper.

**Pitfall.** $W_i$ appears once from Cauchy–Schwarz, once inside $\sum_{j\in\mathcal J_i}\pi_j$: uniform bound $\tau$ on the trace integrals gives $W_i^2\tau$, not $W_i\tau$. §9 needs this square (split weights $O(D/m)$).

#### D7.24 Step — Symbol cost of a split (`transport:symbol-cost`)
*Source: 06-transport.tex 715–735.*

**Statement.** For every split pair $(i,j)$, uniformly over density matrices $\sigma$ on $\mathcal S_k$:
$$\operatorname{Tr}(\sigma\mathsf D_{i,j})\le Ca^2\ell^C\int\eta_{i,j}(\theta)^{1/8}d\mu_\sigma(\theta)+r_k,\qquad r_k\to0.$$
One common $r_k\ge0$ serves all (finitely many) split pairs ($r_k=0$ if none). Unsplit pairs: $\mathsf D_{i,j}=0$, no remainder and no dimension factor.

**Used from.** D6.12 (Lemma 6.4, `replicas:skew-bound`) and, inside it, D5.15 (Lemma 5.3); D7.9 (cross-band commutation), D7.11, D7.12, D7.21.

**Proof.**
- D7.24.1 At a split leaf only the exceptional band $g_0$ fails to commute with $\bar h_i$; in the other bands $D_i$ lies in one part, so for $g\ne g_0$ the factors $A_{j,g}^{\mp1/2}$ commute with $\bar h_i$ and with $A_{j,g_0}^{\pm1/2}$ (cross-band commutation), so they cancel against each other in $A_j^{-1/2}\bar h_iA_j^{1/2}$: $O_{i,j}=A_{j,g_0}^{-1/2}\bar h_iA_{j,g_0}^{1/2}$.
- D7.24.2 In band $g_0$, $D_i$ meets $Y$ and exactly one of $P,F$, so $h_i$ is supported on $PY$ (or $YF$ after exchanging outer parts), $0\le h_i\le I$ with designated support $D_i$, $x=Y\cap D_i$, $\log(e\dim D_i)\le\ell$, $a\ell$ small. These are the hypotheses of Lemma 6.4.
- D7.24.3 $\mathsf D_{i,j}$ is Lemma 6.4's $\mathcal D_k$ for $O_k=O_{i,j}$. `replicas:skew-bound` gives the stated bound with $\log^C(e\dim D_i)\le\ell^C$. The $o_k(1)$ of Lemma 6.4 is uniform in $\sigma$.
- D7.24.4 Applicability to $\sigma_{j,u}$: the metrics at terminal leaves do not depend on $p$, and the bound is uniform in $\sigma$, so it holds for every $\sigma_{j,u}$ regardless of $p$, $u$, $v$.

**Output.** Feeds D7.25.

**Standard?** Specific to this paper.

#### D7.25 Step — Assembly of the energy bound (part (c), `transport:energy-similarity`)
*Source: 06-transport.tex 737–760.*

**Statement.**
$$\operatorname{Re}\langle(T_i+E_{i,+})v,(T_i+E_{i,-})v\rangle=\operatorname{Re}\langle\mathcal M^{-s}v,\bar h_i\mathcal M^sv\rangle\ge\tfrac12\|T_iv\|^2-\tfrac32\bigl(\|E_{i,+}v\|^2+\|E_{i,-}v\|^2\bigr).$$
Hence $\langle v,\bar Hv\rangle\le2E_0+3\sum_{i,\pm}\|E_{i,\pm}v\|^2$, and Proposition 7.4(c) holds.

**Used from.** D7.23, D7.24; D7.14 (definition of $v$, hypothesis $\bar H\mathrm{pre}=E_0\mathrm{pre}$); D7.21.1 ($T^*T=\bar h_i$).

**Proof.**
- D7.25.1 $T+E_\pm=\mathcal B^{\pm s}T\mathcal M^{\mp s}$. $\langle\mathcal B^sT\mathcal M^{-s}v,\mathcal B^{-s}T\mathcal M^sv\rangle=\langle T\mathcal M^{-s}v,T\mathcal M^sv\rangle$ (opposite powers of $\mathcal B_i$ cancel) $=\langle\mathcal M^{-s}v,\bar h_i\mathcal M^sv\rangle$.
- D7.25.2 Let $\alpha=T_iv$, $e_\pm=E_{i,\pm}v$. $\operatorname{Re}\langle\alpha+e_+,\alpha+e_-\rangle\ge\|\alpha\|^2-\|\alpha\|\|e_-\|-\|\alpha\|\|e_+\|-\tfrac12(\|e_+\|^2+\|e_-\|^2)$. Each $\|\alpha\|\|e\|\le\tfrac14\|\alpha\|^2+\|e\|^2$. Total: $\tfrac12\|\alpha\|^2-\tfrac32(\|e_+\|^2+\|e_-\|^2)$.
- D7.25.3 Sum over $i$ of the left equality: $\operatorname{Re}\langle\mathcal M^{-s}v,\bar H\mathcal M^sv\rangle=E_0$, because $\mathcal M^sv=\mathrm{pre}/N$, $\bar H\mathrm{pre}=E_0\mathrm{pre}$, $\langle\mathcal M^{-s}v,\mathcal M^sv\rangle=\langle v,v\rangle=1$. And $\sum_i\|T_iv\|^2=\langle v,\bar Hv\rangle$. So $E_0\ge\tfrac12\langle v,\bar Hv\rangle-\tfrac32\sum_{i,\pm}\|E_{i,\pm}v\|^2$.
- D7.25.4 Insert D7.23 (factor $2$ for the two signs) and D7.24, with $\int m_s=\tfrac12$ for the $r_k$ term: main term $Ca^2\ell^C\sum_iW_i\sum_{j\in\mathcal J_i}\pi_j\int m_s\int\eta_{i,j}^{1/8}d\mu_{\sigma_{j,u}}du$; remainder $\le C'r_k\sum_iW_i^2\le C'r_k\cdot\#\{i\}\to0$ ($W_i\le1$, finite index set), uniform in $p$ and $v$.

**Output.** Part (c).

**Standard?** Specific to this paper.

**Pitfall.** Eigenvector hypothesis used only in D7.25.3.

#### D7.26 Step — Endpoints, uniformity, finite sequences of rounds
*Source: 06-transport.tex 762–771.*

**Statement.** For fixed $k$, $\mathcal M(p)$, $N(p)$ smooth on $[0,1]$. Entropy integrand and error of (b) bounded uniformly in $p\in(0,1)$; (b) integrates over closed subintervals of $[0,1]$ with endpoint values of $N$. Finite sequence of rounds: maxima of polynomial losses and remainders.

**Used from.** D7.5, D7.14, D7.20.

**Proof.**
- D7.26.1 Smoothness: $p\mapsto A_h\#_pB_h=A_h^{1/2}e^{p\log C_h}A_h^{1/2}$ is smooth, inputs positive definite $\Rightarrow$ $\mathcal M(p)$, $N(p)$ smooth on $[0,1]$.
- D7.26.2 Bounds uniform in $p$: right side of (b) has $\int d\mu_\sigma=1$, $\eta$ bounded in the fixed one-copy space, $\sum_hw_h=1$, $\int m_s=\tfrac12$. Unitality (D7.5) gives $\operatorname{Tr}\sigma_{j,u}=1$ uniformly as a branch weight $\to0$.
- D7.26.3 Integrate (b) over $[p_1,p_2]\subset(0,1)$, let $p_1\downarrow0$, $p_2\uparrow1$: bounded integrand and continuity of $N$.

**Output.** Telescoping of $\log N^2$ over rounds in §9 (adjacent endpoint metrics agree, $p=1$ of round $r$ = $p=0$ of round $r+1$).

**Standard?** Specific to this paper.

#### D7.27 Step — The shared-state remark
*Source: 06-transport.tex 773–779.*

**Statement.** $\sigma_{h,u}$ in (a) is the state of leaf $(h,\mathrm{old})$ in D7.23. Weights differ: $w_h$ in (a), $(1-p)w_h$ in (c).

**Used from.** D7.14, D7.15, D7.23.

**Output.** §9 selects one $p$, one round, with $\mathcal Q(p)$ small; energy bound at that $p$ reuses the states, with $1-p\le1$.

**Standard?** Specific to this paper.

---

## Parameters and constants

| Symbol | Value / range | Fixed where |
|---|---|---|
| $p$ | $[0,1]$ common interpolation parameter in a round; positive weights need $0<p<1$ | D7.2, D7.9 |
| $s$ in $g_s,m_s$ | $0<s<1/2$ (D7.6, D7.7 item 1) | D7.6 |
| $s$ in Prop. 7.4, $h_\pm$ | $1/4$; $h_\pm$ use $g_{s/2}$, $s/2=1/8$ | D7.7 item 2, D7.14 |
| $\int m_s$ | $2s$; $=1/2$ at $s=1/4$ | D7.7 |
| $\lvert q_\pm\rvert/m_s$ | $\le1/\sqrt2$ (only at $s=1/4$); $\int\lvert q_\pm\rvert\le1/(2\sqrt2)$ | D7.7.7, D7.23.6 |
| $t$, $a$ | $0<t<1/4$, $a=2t$ | D7.10 |
| $\ell$ | $\ge1$, $\ge\log(e\dim x)$ for transferred $x$ and $\ge\log(e\dim D_i)$ for split $i$ | D7.10, D7.11 |
| $c_0$ | small absolute constant, $a\ell\le c_0$ (Lemmas 6.3, 5.3) | D7.10 |
| $K$ | number of bands, fixed | D7.9 |
| $w_h$, $q_{c\mid h}$ | positive, each family sums to $1$ | D7.9 |
| $\pi_j$ | $(1-p)w_h$ or $p\,w_hq_{c\mid h}$, sum $1$ | D7.9 |
| $D_k$ | $\binom{k+\dim\mathcal V-1}{\dim\mathcal V-1}$, polynomial in $k$ | D7.13 |
| $b_k$ | $\le1$, $-\log b_k=O_{\rm fixed}(\log(k+1))$, common to finitely many moves | D7.18 |
| $\beta_k$ | $\tfrac K2(\log D_k-\log b_k)=O_{\rm fixed}(\log(k+1))$ (explicit from D7.20.4) | D7.14, D7.20 |
| $C$, exponents $C$ | universal, from Lemmas 6.3 and 6.4 | D7.14 |
| entropy error | $CkaK\,a^{1/4}\ell^C$ | D7.14 (b) |
| energy exponent of $\eta$ | $1/8$; coefficient $Ca^2\ell^C$ | D7.14 (c), D7.24 |
| $r_k$, $o_k(1)$ | $\to0$ as $k\to\infty$, uniform in $\sigma$, $p$, $\mathrm{pre}$; rate depends on fixed data | D7.24, D7.25 |
| $\varepsilon,\delta$ | auxiliary in projection transfer, $\varepsilon\downarrow0$ | D7.3.9 |
| $\tfrac12,\tfrac32,3,\tfrac14$ | energy-similarity and block-bound constants | D7.25, D7.23 |

## Dependencies

Consumed:
- D2.1: entropy definitions ($S_\theta(x\mid P)$, $I_\theta$), through $\eta$.
- D5.5 (Lemma 5.1) for the smallness constant $c_0$; D5.15 (Lemma 5.3) inside Lemma 6.4.
- D6.5, D6.8, D6.9, D6.6 (Lemma 6.2: positivity, centrality), D6.10 (Lemma 6.3), D6.12 (Lemma 6.4), D6.11.

Exported:
- Lemma 7.1: vector Jensen (`transport:vector-jensen`) used in §8 for $\langle\varphi,\widetilde{\mathcal M}\varphi\rangle$; projection transfer (item 5, $P=I$) used in §9 for the initial floor of $-\log N^2$.
- Proposition 7.4: `transport:entropy-gain` and `transport:energy` used in §9 (charge-round gain `scanner:charge-gain`, selection of one $p$, energy estimate at that $p$); states $\sigma_{h,u}$ and measure $\mu_\sigma$ in `scanner:Q-definition`; $m_s$ with $\int m_s=2s$.
- Round structure (D7.9, $p=1$ attaches choice trees) reused in §9.
