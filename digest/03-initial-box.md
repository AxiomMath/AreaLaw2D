# Digest of §3 — Marginal tails and an initial box estimate

Source: `paper/sections/02-initial.tex` (676 lines), label `sec:initial`. Numbering is shared by lemmas and propositions inside a section: Lemma 3.1 = `lem:tail`, Lemma 3.2 = `lem:initial-buffer`, Proposition 3.3 = `prop:initial-box`. Conventions of §1–§2 apply: $\Lambda\subset\mathbb Z^2$ finite, $d_\Lambda$ induced graph distance, $H=\sum_Xh_X$ with $\operatorname{diam}_{d_\Lambda}X\le R$, $\|h_X\|\le J$, unique ground vector $\Omega$, gap $\Delta$, $q\ge2$, $R\ge1$; natural logs; $C,c$ depend on $q,R,J,\Delta$ only (D2.13).

Letter clashes inside §3: $B$ = bipartition part (Lemma 3.1) vs $\mathcal B$ = interaction budget; $K$ = surprisal random variable (Lemma 3.1) vs $K=L_m\cdots L_1$ (Lemma 3.2); $N_i$ = number of product terms (Lemma 3.1) vs $N,N_j$ = filtered norms (Lemma 3.2); $d_i$ = dimension of a support (Lemma 3.1) vs $d_j=r+jD$ = dilation radius (Lemma 3.2); $M(u)$ = moment function vs $M_j$ = trial filters vs $M$ = integer scale (Prop 3.3); $Z$ = endpoints of crossing edges of $A$ ($=Z_A$ of §1) vs $Z_r$ = harmonic sum; $D_i$ = designated support (Lemma 3.1) vs $D$ = integer margin (Lemma 3.2).

## Section in one paragraph

(i) Lemma 3.1 (D3.1): surprisal $K=-\log p_j$ of a marginal across a cut has MGF $\le e^{uS+512e\vartheta\mathcal Bu^2}$ on $|u|\le[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}$, tail of width $\sqrt{\mathcal B}$; proof tilts $\Omega$ by $\rho^{-u/2}$, compares tilted energy with gap. Lattice: $\mathcal B\le C(1+|\partial_\Lambda B|)$ (D3.2). (ii) Lemma 3.2 (D3.4): $S(X|T)\le\frac12S(X)+C_{\rm buf}r$ for $X=A\cap Q_0$ buffered inside a safe rectangle; proof maximizes $\|L_m\cdots L_1\Omega\|$ over positive filters on nested $X_1\subset\dots\subset X_m$, $\operatorname{Tr}L_j^{2/a_j}=1$, $a_j\propto1/(r+d_j)$, $\sum a_j=2$; gap + Lemma 3.1 bound $-2\log N$ below by $\sum a_jS(X_j)$, Schmidt-pinned trials bound it above by $S(X)+\sum a_jS(T_j)$; SSA gives $\frac12$. (iii) Proposition 3.3 (D3.16): chain rule averaged over random orders of $\le M^2$ children of size $\le r$ => $F_{\rm box}(Mr)\le\lambda F_{\rm box}(r)+CM^2r$, $\lambda=(1-p_0/4)M^2<M^2$ => $F_{\rm box}(r)\le Cr^{1+e_0}$, $e_0\in(0,1)$. Downstream uses: Exports.

---

#### D3.1 Lemma 3.1 — Marginal moment and tail bounds
Lines 34–200 (statement 34–69, proof 71–200). Label `lem:tail`; displayed claims `eq:initial-tail-mgf` (53–59), `eq:initial-tail-probability` (61–68); intermediate labels `eq:initial-exact-tilt` (83–86), `eq:initial-support-conjugation` (109–112), `eq:initial-narrow-strip` (144–148), `eq:initial-real-quadratic` (158–163), `eq:initial-tilted-energy` (172–176).

**Statement.** Let $\mathcal H=\bigotimes_{v\in V}\mathcal H_v$, finite, finite-dimensional factors. Let $\mathsf H=\sum_{i\in\mathcal I}h_i$, $\mathcal I$ finite, $h_i=h_i^*$, $\|h_i\|\le c_0$ ($c_0\ge0$ fixed), $h_i$ with designated support $D_i\subseteq V$. Unique unit ground vector $\Psi$, $\mathsf H\Psi=E_0\Psi$, $g_0>0$ with $\mathsf H-E_0\ge g_0(\mathrm{id}-|\Psi\rangle\langle\Psi|)$. Fix a bipartition $B\sqcup B^c=V$; $\mathcal I_\times=\{i:D_i\cap B\ne\varnothing\ne D_i\cap B^c\}$. Put
$$\rho=\operatorname{Tr}_{B^c}|\Psi\rangle\langle\Psi|,\quad d_i=\prod_{v\in D_i}\dim\mathcal H_v,\quad \mathcal B=1+\sum_{i\in\mathcal I_\times}\log^2(e\,d_i),\quad \vartheta=c_0/g_0 .$$
Let $p_j$ be the positive eigenvalues of $\rho$, $K=-\log p_j$ with probability $p_j$, $S=S(\rho)$. Then
$$\log\mathbb E\,e^{uK}\le uS+512e\,\vartheta\,\mathcal B\,u^2,\qquad |u|\le\frac1{32\sqrt{(1+\vartheta)\mathcal B}},$$
and for every $w\ge0$
$$\Pr\{|K-S|>w\}\le\min\Big\{1,\;2e^{e/2}\exp\Big(-\frac{w}{32\sqrt{(1+\vartheta)\mathcal B}}\Big)\Big\}.$$

**Used from.** none. Textbook: three-lines, Cauchy coefficient estimate, exponential Markov.

**Proof.**
Notation: $M(u)=\sum_jp_j^{1-u}=\mathbb Ee^{uK}$, $L(u)=\log M(u)$. Then $L(0)=0$, $L'(0)=\sum_jp_j(-\log p_j)=S$.

- D3.1.1 *Tilted vector.* $P$ = support projection of $\rho$ on $\mathcal H_B$. $F=\rho^{-u/2}$ on $P\mathcal H_B$, $F=\mathrm{id}$ on $\ker\rho$; acts on $B$ only, invertible. Schmidt form $\Psi=\sum_j\sqrt{p_j}\,a_j\otimes b_j$: $\|F\Psi\|^2=\sum_jp_j^{1-u}=M(u)$. $\Theta=F\Psi/\sqrt{M(u)}$ unit, marginal $\sigma=\operatorname{Tr}_{B^c}|\Theta\rangle\langle\Theta|=\rho^{1-u}/M(u)$ (power $0$ on $\ker\rho$); $[F,\sigma]=0$.
- D3.1.2 *Exact tilted eigenequation* (eq:initial-exact-tilt). $F\mathsf HF^{-1}\Theta=E_0\Theta$ ($\mathsf H\Psi=E_0\Psi$, $F$ invertible). Hence $E_0=\langle\Theta,F\mathsf HF^{-1}\Theta\rangle$ and
$$\langle\Theta,(\mathsf H-E_0)\Theta\rangle=\sum_i\operatorname{Re}\langle\Theta,(h_i-Fh_iF^{-1})\Theta\rangle .$$
- D3.1.3 *Only crossing terms contribute.* $D_i\subseteq B^c$: $F$ commutes with $h_i$, term $=0$. $D_i\subseteq B$: $\langle\Theta,Fh_iF^{-1}\Theta\rangle=\operatorname{Tr}\sigma Fh_iF^{-1}=\operatorname{Tr}F^{-1}\sigma Fh_i=\operatorname{Tr}\sigma h_i$ (cyclicity, $[F,\sigma]=0$), term $=0$. Remains $i\in\mathcal I_\times$.
- D3.1.4 *Analytic interpolation of a crossing term.* For $i\in\mathcal I_\times$, $z\in\mathbb C$: $\sigma^z:=P\exp(z\log(\sigma|_{P\mathcal H_B}))P$, $f_i(z)=\langle\Theta,\sigma^zh_i\sigma^{-z}\Theta\rangle$, entire. $\sigma^0=P$, $\Theta\in\operatorname{ran}P$, so $f_i(0)=\langle\Theta,h_i\Theta\rangle$ (real). At $z_u=-u/[2(1-u)]$: on the support $\sigma^{z_u}=M(u)^{-z_u}\rho^{(1-u)z_u}=M(u)^{-z_u}F$ since $(1-u)z_u=-u/2$; likewise $\sigma^{-z_u}=M(u)^{z_u}F^{-1}$. Scalars cancel: $f_i(z_u)=\langle\Theta,Fh_iF^{-1}\Theta\rangle$ (eq:initial-support-conjugation). So
$$\langle\Theta,(\mathsf H-E_0)\Theta\rangle=\sum_{i\in\mathcal I_\times}\operatorname{Re}\big(f_i(0)-f_i(z_u)\big).$$
- D3.1.5 *Imaginary axis.* $\sigma^{iy}$ unitary on $\operatorname{ran}P\ni\Theta$: $|f_i(iy)|\le\|h_i\|\le c_0$.
- D3.1.6 *Crude strip bound $|f_i(z)|\le2c_0d_i^2$ for $|\operatorname{Re}z|\le\frac14$.* Matrix units of $\operatorname{End}(\mathcal H_{D_i\cap B})$: $h_i=\sum_{a,b}E_{ab}\otimes h_{ab}$, $h_{ab}=(\langle a|\otimes\mathrm{id})h_i(|b\rangle\otimes\mathrm{id})$; relabel $h_i=\sum_{\alpha=1}^{N_i}c_\alpha\otimes d_\alpha$, $c_\alpha=E_{ab}$ on $D_i\cap B$, $d_\alpha=h_{ab}$ on $D_i\cap B^c$. $N_i=(\dim\mathcal H_{D_i\cap B})^2\le d_i^2$, $\|c_\alpha\|=1$, $\|d_\alpha\|\le c_0$. Schmidt form $\Theta=\sum_j\sqrt{s_j}\,e_j\otimes g_j$: $f_i(z)=\sum_\alpha\sum_{j,k}s_j^{1/2+z}s_k^{1/2-z}(c_\alpha)_{jk}(d_\alpha)_{jk}$ (matrix elements in Schmidt bases). $x=\operatorname{Re}z\in[-\frac14,\frac14]$: $|s_j^{1/2+z}s_k^{1/2-z}|=s_j^{1/2+x}s_k^{1/2-x}\le s_j+s_k$ (weighted AM–GM). Cauchy–Schwarz: $\sum_k|(c_\alpha)_{jk}(d_\alpha)_{jk}|\le\|c_\alpha\|\|d_\alpha\|$ (row $\ell^2$ norm $\le$ operator norm), same for columns. $s_j$ over rows, $s_k$ over columns, $\sum s=1$: per $\alpha$ $\le2\|c_\alpha\|\|d_\alpha\|\le2c_0$. Sum over $\alpha$: $|f_i(z)|\le2c_0d_i^2$, uniform in $\operatorname{Im}z$.
- D3.1.7 *Narrow strip* (eq:initial-narrow-strip). $c_0=0$: trivial; else apply to $f_i/c_0$. Three-lines on $0\le\operatorname{Re}z\le\frac14$, bounds $c_0$ (D3.1.5), $2c_0d_i^2$ (D3.1.6): $|f_i(x+iy)|\le c_0(2d_i^2)^{4x}$. $\ell_i=\log(ed_i)$, $\log(2d_i^2)\le2\ell_i$ ($\log2\le2$). $x\le\delta_i:=1/(8\ell_i)$: $(2d_i^2)^{4x}\le e^{8\ell_i\delta_i}=e$. Same on $-\delta_i\le\operatorname{Re}z\le0$. So $|f_i|\le ec_0$ for $|\operatorname{Re}z|\le\delta_i$ ($\ell_i\ge1$ => $\delta_i\le\frac18<\frac14$).
- D3.1.8 *Real quadratic bound* (eq:initial-real-quadratic). Hermiticity: $f_i(-\bar z)=\overline{f_i(z)}$ (write $f_i(z)=\langle\sigma^{\bar z}\Theta,h_i\sigma^{-z}\Theta\rangle$ and use $h_i=h_i^*$). With $f_i=\sum a_nz^n$: $(-1)^na_n=\bar a_n$, so even $a_n$ real, odd $a_n$ imaginary. For real $x$: $\operatorname{Re}(f_i(x)-f_i(0))=\sum_{n\ge2\text{ even}}a_nx^n$. Cauchy on the disk of radius $\delta_i$ with sup $\le ec_0$ (D3.1.7): $|a_n|\le ec_0\delta_i^{-n}$. For $|x|\le\delta_i/2$: sum $\le ec_0(x/\delta_i)^2/(1-(x/\delta_i)^2)\le\frac43ec_0x^2\delta_i^{-2}\le2ec_0x^2\delta_i^{-2}=128\,ec_0\ell_i^2x^2$. $f_i'(0)=0$ not claimed; only $\operatorname{Re}$ of the linear term vanishes.
- D3.1.9 *Tilted excitation energy* (eq:initial-tilted-energy). $|u|\le[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}$ => $|u|\le\frac1{32}$, $|z_u|=|u|/(2|1-u|)\le|u|$. $\mathcal B\ge1+\sum_{\mathcal I_\times}\ell_i^2$ => $\ell_i\le\sqrt{\mathcal B}$, $|z_u|\le\frac1{32\ell_i}\le\delta_i/2$: D3.1.8 applies to every crossing term at $x=z_u$. By D3.1.4:
$$0\le\langle\Theta,(\mathsf H-E_0)\Theta\rangle\le128\,e\,c_0\sum_{\mathcal I_\times}\ell_i^2u^2\le128\,e\,c_0\,\mathcal B\,u^2 .$$
- D3.1.10 *Gap converts energy to overlap.* $\langle\Theta,(\mathsf H-E_0)\Theta\rangle\ge g_0(1-|\langle\Psi,\Theta\rangle|^2)$ and $\langle\Psi,\Theta\rangle=\sum_jp_j^{1-u/2}/\sqrt{M(u)}=M(u/2)/\sqrt{M(u)}$. Hence
$$\frac{M(u/2)^2}{M(u)}=|\langle\Psi,\Theta\rangle|^2\ge1-v,\qquad v:=128\,e\,\vartheta\,\mathcal B\,u^2 .$$
- D3.1.11 *Halving inequality.* $v\le128e\vartheta\mathcal B/[1024(1+\vartheta)\mathcal B]=e\vartheta/[8(1+\vartheta)]<e/8<\frac12$. Take logs: $2L(u/2)-L(u)\ge\log(1-v)\ge-2v$ ($-\log(1-v)\le2v$ on $[0,\frac12]$). So $L(u)\le2L(u/2)+\kappa u^2$, $\kappa=256\,e\,\vartheta\,\mathcal B$.
- D3.1.12 *Iteration* (eq:initial-tail-mgf). $u/2^i$ stays admissible, either sign. $L(u)\le2^jL(u/2^j)+\kappa u^2\sum_{i<j}2^i4^{-i}$. $j\to\infty$: $2^jL(u/2^j)\to uL'(0)=uS$ ($L$ smooth, $L(0)=0$); $\sum_i2^{-i}\le2$. So $L(u)\le uS+2\kappa u^2=uS+512\,e\,\vartheta\,\mathcal B\,u^2$.
- D3.1.13 *Tail* (eq:initial-tail-probability). $u_*=[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}$; quadratic term at $u_*$: $512e\vartheta\mathcal Bu_*^2=e\vartheta/[2(1+\vartheta)]\le e/2$. Exponential Markov, $u=+u_*$: $\Pr\{K-S>w\}\le e^{-u_*w}\mathbb Ee^{u_*(K-S)}\le e^{e/2}e^{-u_*w}$; $u=-u_*$: $\Pr\{K-S<-w\}\le e^{e/2}e^{-u_*w}$. Add; $\min$ with $1$ trivial.

**Output.** MGF at $u=-a_j/(1-a_j)$ (D3.11); D3.2; §4 truncated Hamiltonian (D4.14); tail with $w=n^{3/5}$ in §8–§10 (Exports).
**Standard?** Specific to this paper (tilting argument). Related: Anshu–Harrow–Soleimanifar 2022 (smooth entanglement spread); Van Acoleyen–Mariën–Verstraete 2013 (entanglement production bound independent of spectator dimension). Three-lines: standard.
**Pitfall.**
- Summand $1$ in $\mathcal B$ gives $\ell_i\le\sqrt{\mathcal B}$, hence $|z_u|\le\delta_i/2$ for all crossing terms at once.
- Factor $(1+\vartheta)$ in the $u$-range gives both $v<\frac12$ (D3.1.11) and quadratic term $\le e/2$ (D3.1.13); neither holds for large $\vartheta$ without it.
- $\sigma^0=P\ne\mathrm{id}$: $f_i(0)=\langle\Theta,h_i\Theta\rangle$ needs $\Theta\in\operatorname{ran}P$.
- $d_i$ enters only via $\log(ed_i)$; $\dim\mathcal H_{B^c}$ never appears.

---

#### D3.2 Step eq:initial-local-tail-parameter — Lattice specialization of Lemma 3.1
Lines 202–212.

**Statement.** Admissible lattice $H$ (D1.2), $B\subseteq\Lambda$, $b'=|\partial_\Lambda B|$; Lemma 3.1 with $c_0=J$, $g_0=\Delta$, $D_i=$ support $X$ of $h_X$, $\vartheta=J/\Delta$:
$$\mathcal B\le C(1+b').$$
Hence for every $n\ge1$ and fixed $M>0$ there is $C_M=C_M(q,R,J,\Delta,M)$ with
$$\Pr\{|K-S|>C_M\sqrt{1+b'}\,\log(n+2)\}\le(n+2)^{-M}.$$

**Used from.** D3.1; D2.8 ($|X|\le v_R$, D2.8.4; ball bound D2.7); D2.9 (terms split by $B$ number $\le2v_R\mu_R|\partial_\Lambda B|$); D2.13.
**Proof.**
- D3.2.1 Crossing indices = supports split by $B$; count $\le2v_R\mu_R\,b'$ (D2.9).
- D3.2.2 $d_i=q^{|X|}$, $|X|\le v_R$ (D2.8.4), so $\log(ed_i)=1+|X|\log q\le1+v_R\log q$.
- D3.2.3 $\mathcal B\le1+2v_R\mu_R(1+v_R\log q)^2b'\le C_1(1+b')$, $C_1=\max\{1,2v_R\mu_R(1+v_R\log q)^2\}$.
- D3.2.4 *Tail (digest expansion; paper states only constant dependence).* Take $C_M=32(M+2)\sqrt{(1+\vartheta)C_1}$ and $w=C_M\sqrt{1+b'}\log(n+2)$. Then $w/[32\sqrt{(1+\vartheta)\mathcal B}]\ge(M+2)\log(n+2)$. Since $2e^{e/2}<8<9\le(n+2)^2$ for $n\ge1$, eq:initial-tail-probability gives $\le2e^{e/2}(n+2)^{-(M+2)}\le(n+2)^{-M}$.

**Output.** $\mathcal B_j$ in D3.5.5; truncated analogue D4.14; $C_M$ at $M=100$ gives the $n^{-100}$ failure mass of §8–§10.
**Standard?** Specific to this paper (finite-range count, as D2.9).
**Pitfall.** $n$ free; no relation between $n$ and $b'$ assumed.

---

#### D3.3 Def — Safe rectangles, size, buffers, local entropy notation
Lines 219–238.

**Statement.** Fix $A\subseteq\Lambda$; $Z=Z_A$ (D1.6) = endpoints of edges of $\partial_\Lambda A$. Integer rectangle $Q$ = product of two finite nonempty integer intervals; $\operatorname{size}(Q)$ = larger side length in sites. Fix $D_0>2R+10$. $Q$ *safe* iff
$$\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q),\qquad\operatorname{dist}_\infty(Q,\varnothing)=\infty .$$
Integer $d\ge0$: $Q^{+d}=Q+([-d,d]^2\cap\mathbb Z^2)$ (ambient; as $T_j$ in D2.6). Physical regions: $A\cap Q^{+d}$. Unit vector $\xi$: $\rho_{\xi,D}$ marginal on $D$, $S_\xi(D)$ its entropy.

**Used from.** D1.3, D1.6, D2.6.
**Output.** "Safe" in D3.4, D3.16, §9–§11; $D_0$ is the constant of §9 (`08-scanner.tex:540–543`).
**Standard?** Specific to this paper.
**Pitfall.** §3 uses only $\operatorname{dist}_\infty(Q,Z)>R$ (via $D_0\operatorname{size}(Q)\ge D_0>R$); slack $2R+10$ is for later sections. Safety depends on $A$ through $Z$.

---

#### D3.4 Lemma 3.2 — Conditional entropy in a buffered rectangle
Lines 240–586 (statement 240–256, proof 258–586). Label `lem:initial-buffer`; displayed claim `eq:initial-buffer-discount` (252–255). Proof is split below into anchors D3.5–D3.14.

**Statement.** There are an integer $C_{\rm pad}\ge1$ and $C_{\rm buf}$, both depending only on $q,R,J,\Delta$ ($D_0>2R+10$, $D>2R+2$ fixed), such that for every safe $Q$, integer $r\ge1$, integer rectangle $Q_0$ with $\operatorname{size}(Q_0)\le r$ and $Q_0^{+C_{\rm pad}r}\subseteq Q$,
$$X=A\cap Q_0,\qquad T=(A\cap Q_0^{+C_{\rm pad}r})\setminus X,$$
in $\Omega$:
$$S(X\mid T)\le\tfrac12S(X)+C_{\rm buf}\,r .$$

**Used from.** D3.1, D3.2, D3.3; D2.2 item 2 (SSA); D2.7–D2.10; D2.13; D1.4 (gap, uniqueness); internal steps D3.5–D3.14.

**Proof.** $X=\varnothing$: both sides $0$. Else D3.5–D3.14 in order. Constants chosen: $D_0$, $D$ (depend on $R$) $\to$ $C_{\rm pad}$ (D3.6, enlarged D3.10) $\to$ $\epsilon$ (floor, removed D3.12) $\to$ $C_{\rm buf}$ (D3.14).
- D3.4.1 D3.5: nested regions, locality; contour budget independent of $C_{\rm pad}$.
- D3.4.2 D3.6: harmonic weights, $\mathcal E=4/Z_r$ small uniformly in $r$.
- D3.4.3 D3.7–D3.8: stationarity of optimized filters.
- D3.4.4 D3.9–D3.10: excitation energy of optimized vector $\le C\mathcal E$; fix $C_{\rm pad}$.
- D3.4.5 D3.11: lower bound on $-2\log N$.
- D3.4.6 D3.12–D3.13: upper bound on $-2\log N$ by Schmidt pinning.
- D3.4.7 D3.14: combine, SSA.

**Output.** D3.16 (with $C_{\rm pad}$, $C_{\rm buf}$).
**Standard?** Specific to this paper (log-norm optimization over nested positive filters).
**Pitfall.** Quantifier order: $C_{\rm buf}$ depends on $C_{\rm pad}$; all constants before D3.10 (contour, energy $C$) must be $C_{\rm pad}$-independent, else $\mathcal E\to0$ cannot compensate. $D$, $D_0$ fixed before $C_{\rm pad}$.

---

#### D3.5 Step — Nested regions, locality, single split, contour budget (Lemma 3.2, part 1)
Lines 269–301. Label `eq:initial-contour-budget` (295–299).

**Statement.** Fix an integer $D>2R+2$ and an integer $C_{\rm pad}>D+1$ (still free). Put
$$m=\Big\lfloor\frac{(C_{\rm pad}-1)r}{D}\Big\rfloor,\quad d_j=r+jD,\quad X_j=A\cap Q_0^{+d_j}\ (1\le j\le m),\quad X_0=X .$$
Then (a) $1\le m\le C_{\rm pad}r/D$, $X_0\subset X_1\subset\dots\subset X_m$, $Q_0^{+d_m}\subseteq Q$; (b) every interaction meeting some $X_j$ has support in $A$; no edge of $\partial_\Lambda A$ is incident with any $X_j$; (c) $|\partial_\Lambda X_j|\le4(r+2d_j)$; (d) support $S_h$ split by $X_j$ is disjoint from $X_i$ for $i<j$, contained in $X_i$ for $i>j$: each support split by at most one $X_j$; (e) constants independent of $C_{\rm pad}$:
$$\#\{\text{interactions split by }X_j\}\le C(r+d_j),\qquad\mathcal B_j\le C(r+d_j),$$
where $\mathcal B_j$ is the $\mathcal B$ of Lemma 3.1 for the bipartition $X_j\mid X_j^c$ of $\Omega$ ($c_0=J$, $g_0=\Delta$).

**Used from.** D3.3; D2.6–D2.9, D3.2.
**Proof.**
- D3.5.1 *(a).* $(C_{\rm pad}-1)r\ge C_{\rm pad}-1>D$ ($r\ge1$, $C_{\rm pad}>D+1$) => $m\ge1$. $d_m=r+mD\le r+(C_{\rm pad}-1)r=C_{\rm pad}r$ => $Q_0^{+d_m}\subseteq Q_0^{+C_{\rm pad}r}\subseteq Q$. Nesting: $d_j$ increasing; $X_0=A\cap Q_0\subseteq A\cap Q_0^{+d_1}$.
- D3.5.2 *(b).* $h_S$ meets $X_j$ at $x$, $S\ni y\notin A$. Shortest $\Lambda$-path $x\to y$: length $\le R$, from $A$ to $A^c$, so contains $\{z,z'\}\in\partial_\Lambda A$; $z\in Z$, $|z-x|_\infty\le|z-x|_1\le R$. Then $\operatorname{dist}_\infty(Q,Z)\le R<D_0\le D_0\operatorname{size}(Q)$, contradicting safety. Edge of $\partial_\Lambda A$ at $x\in X_j\subseteq Q$ puts $x\in Z\cap Q$: same contradiction.
- D3.5.3 *(c).* $\{x,y\}\in\partial_\Lambda X_j$, $x\in X_j$, $y\in\Lambda\setminus X_j$. $y\in Q_0^{+d_j}$ => $y\notin A$ => $\{x,y\}\in\partial_\Lambda A$, excluded by (b). So $y\notin Q_0^{+d_j}$: edge crosses the ambient perimeter; $\le r+2d_j$ sites per axis => $\le2\cdot2(r+2d_j)$ perimeter edges. Missing sites of $\Lambda$ only remove edges.
- D3.5.4 *(d).* Split: $S_h\cap X_j\ne\varnothing\ne S_h\setminus X_j$; by (b) $S_h\subseteq A$. Ambient diameter $\le$ graph diameter $\le R$ ($d_\Lambda\ge|\cdot|_1\ge|\cdot|_\infty$). Take $p\in S_h\cap Q_0^{+d_j}$, $p'\in S_h\setminus Q_0^{+d_j}$. Every $s\in S_h$: $|s-p|_\infty\le R<D$, so $s\in Q_0^{+d_j+R}\subseteq Q_0^{+d_{j+1}}$; with $S_h\subseteq A$, $S_h\subseteq X_i$ for $i>j$. For $i<j$: suppose $s\in S_h\cap Q_0^{+e_i}$, $e_0=0$, $e_i=d_i$ ($i\ge1$). $|p'-s|_\infty\le R$ => $p'\in Q_0^{+e_i+R}$. $e_i+R<d_j$: $i\ge1$: $d_i+R\le d_{j-1}+R<d_{j-1}+D=d_j$; $i=0$: $R<D<d_1\le d_j$. So $p'\in Q_0^{+d_j}$, contradiction.
- D3.5.5 *(e).* D2.9 with (c): $\#\{\text{split by }X_j\}\le2v_R\mu_R\cdot4(r+2d_j)\le16v_R\mu_R(r+d_j)$. Crossing indices for $X_j\mid X_j^c$ = split ones; D3.2.1–D3.2.3: $\mathcal B_j\le1+2v_R\mu_R(1+v_R\log q)^2\cdot4(r+2d_j)\le C(r+d_j)$ ($r+d_j\ge1$). Constants depend on $q,R$ only.

**Output.** (d)–(e): D3.7, D3.9, D3.10, D3.11; (a), (c): D3.6, D3.14.
**Standard?** Specific to this paper (geometric bookkeeping).
**Pitfall.** $X_0=A\cap Q_0$, not "$d_0=r$": margin $X_0\to X_1$ is $r+D$, $X_j\to X_{j+1}$ is $D$. $D>R$ gives single split; $D>2R+2$ is the paper's choice.

---

#### D3.6 Step eq:initial-harmonic-weights — Harmonic weights
Lines 303–333. Labels `eq:initial-harmonic-weights` (315–320), `eq:initial-harmonic-lower` (323–326).

**Statement.** Put $Z_r=\sum_{j=1}^m\frac1{r+d_j}$, $a_j=\frac{2}{Z_r(r+d_j)}$, $\mathcal E=\sum_j(r+d_j)a_j^2$. Then $\sum_ja_j=2$, $\mathcal E=4/Z_r$, $\mathcal E=\min\{\sum_j(r+d_j)b_j^2:\sum b_j=2\}$, and
$$Z_r\ge\frac1D\log\frac{C_{\rm pad}+1}{2+D}.$$
Hence $\mathcal E\le4D/\log\frac{C_{\rm pad}+1}{2+D}\to0$ as $C_{\rm pad}\to\infty$, uniformly in $r\ge1$. Choose $C_{\rm pad}$ so large that $a_j\le\frac12$ for all $j$; enlarged once more in D3.10.

**Used from.** D3.5.
**Proof.**
- D3.6.1 Cauchy–Schwarz: $4=(\sum_jb_j)^2\le\big(\sum_j(r+d_j)b_j^2\big)\big(\sum_j\frac1{r+d_j}\big)$, equality iff $b_j\propto\frac1{r+d_j}$. For $a_j$: $\sum a_j=\frac2{Z_r}Z_r=2$; $\mathcal E=\sum_j\frac{4}{Z_r^2(r+d_j)}=\frac4{Z_r}$.
- D3.6.2 $r+d_j=2r+jD$; summand decreasing: $\frac1{2r+jD}\ge\int_j^{j+1}\frac{dx}{2r+Dx}$, so $Z_r\ge\frac1D\log\frac{2r+D(m+1)}{2r+D}$. $m+1>(C_{\rm pad}-1)r/D$ => $2r+D(m+1)>(C_{\rm pad}+1)r$; $r\ge1$ => $2r+D\le(2+D)r$. Ratio $>(C_{\rm pad}+1)/(2+D)$, positive since $C_{\rm pad}>D+1$.
- D3.6.3 $r+d_j\ge2r+D\ge D+2$, so $a_j\le\frac{2}{Z_r(D+2)}\le\frac{2D}{(D+2)\log\frac{C_{\rm pad}+1}{2+D}}\to0$.

**Output.** $a_j\le\frac12$ => $a_j/(1-a_j)\le2a_j=\frac4{Z_r(r+d_j)}$ (D3.10); $\mathcal E$ small (D3.9–D3.11).
**Standard?** Weighted Cauchy–Schwarz; specific weights.
**Pitfall.** $\mathcal E\to0$ only logarithmically in $C_{\rm pad}$: error $C(m+1)\mathcal E$ in D3.11 is order $C_{\rm pad}r$, not $o(r)$; absorbed in $C_{\rm buf}r$.

---

#### D3.7 Step eq:initial-filter-commutation — Optimized filters commute with their marginals
Lines 335–382. Labels `eq:initial-filter-constraints` (341–344), `eq:initial-filter-commutation` (355–358).

**Statement.** Fix $\epsilon>0$ with $(\dim\mathcal H_{X_j})\epsilon^{2/a_j}<1$ for all $j$. Maximize $N=\|L_m\cdots L_1\Omega\|$ over positive operators $L_j$ on $\mathcal H_{X_j}$ with
$$L_j\ge\epsilon\,\mathrm{id},\qquad\operatorname{Tr}L_j^{2/a_j}=1 .$$
A maximizer exists, $N>0$. With $K=L_m\cdots L_1$, $\phi=K\Omega/N$: $[L_j,\rho_{\phi,X_j}]=0$ for $1\le j\le m$.

**Used from.** D3.5, D3.6.
**Proof.**
- D3.7.1 *Existence.* Feasible set of each $L_j$ nonempty (raise one eigenvalue above $\epsilon$ until trace $1$; slack allows it), compact ($L_j\le1$ since $\operatorname{Tr}L_j^{2/a_j}=1$); $N$ continuous. Feasible products invertible => $N>0$.
- D3.7.2 *Descending induction on $j$.* Assume claim for indices $>j$. Anti-Hermitian $B$ on $X_j$: $L_j(t)=e^{tB}L_je^{-tB}$ keeps both constraints (same spectrum). $\frac d{dt}L_j(t)|_0=(B-L_jBL_j^{-1})L_j$, so with $K_{>j}=L_m\cdots L_{j+1}$
$$\frac d{dt}\log N\Big|_0=\operatorname{Re}\langle\phi,K_{>j}(B-L_jBL_j^{-1})K_{>j}^{-1}\phi\rangle=0 .$$
- D3.7.3 *Peeling outer filters.* Operator inside, conjugated by $L_m$, is supported on $X_m$ (inner filters and $B$ live on regions $\subseteq X_m$). $\langle\phi,L_mWL_m^{-1}\phi\rangle=\operatorname{Tr}(\rho_{\phi,X_m}L_mWL_m^{-1})=\operatorname{Tr}(L_m^{-1}\rho_{\phi,X_m}L_mW)=\operatorname{Tr}(\rho_{\phi,X_m}W)$ by induction hypothesis. Repeat down to $L_{j+1}$. Left: $\operatorname{Re}\operatorname{Tr}\rho_{\phi,X_j}(B-L_jBL_j^{-1})=0$.
- D3.7.4 $\operatorname{Tr}(\rho B)$ imaginary ($\rho=\rho^*$, $B=-B^*$), so $\operatorname{Re}\operatorname{Tr}(L_j^{-1}\rho_{\phi,X_j}L_jB)=0$ for all anti-Hermitian $B$. $Y=L_j^{-1}\rho L_j=Y_h+Y_a$ (Hermitian + anti-Hermitian). $\operatorname{Tr}(Y_hB)$ imaginary; $B=Y_a$: $\operatorname{Re}\operatorname{Tr}Y_a^2=-\|Y_a\|_2^2=0$. So $Y=Y^*$: $L_j^{-1}\rho L_j=L_j\rho L_j^{-1}$, $\rho L_j^2=L_j^2\rho$, $L_j=(L_j^2)^{1/2}$ commutes with $\rho$.

**Output.** Peeling in D3.8, D3.9; prefix problems in D3.11.
**Standard?** Specific to this paper.
**Pitfall.** No commutation between distinct $L_i,L_j$ claimed; only expectation values simplify. Descending order essential: removal of $L_m$ uses commutation at $m$ first.

---

#### D3.8 Step eq:initial-filter-clipping — Clipping bounds log-ratios of filter eigenvalues
Lines 384–405. Label `eq:initial-filter-clipping` (397–403).

**Statement.** In a common eigenbasis of $L_j$ and $\rho_{\phi,X_j}$ with eigenvalues $l_i$ and $p_i$: for $p_i,p_k>0$,
$$\Big|\log\frac{l_i}{l_k}\Big|\le\frac{a_j}2\Big|\log\frac{p_i}{p_k}\Big| .$$

**Used from.** D3.7.
**Proof.**
- D3.8.1 $x_i=l_i^{2/a_j}$. Diagonal variation of $L_j$ and the peeling of D3.7.3 give $d\log N=\sum_ip_i\,dl_i/l_i=\frac{a_j}2\sum_ip_i\frac{dx_i}{x_i}$, subject to $\sum x_i=1$, $x_i\ge\epsilon^{2/a_j}$.
- D3.8.2 KKT at the maximizer on $\{\sum x_i=1,\ x_i\ge\epsilon^{2/a_j}\}$ (necessary only; no concavity): $p_i/x_i=\lambda$ on free coordinates, $\le\lambda$ on floored. Free coordinate exists: all floored => $\sum x_i=\dim\cdot\epsilon^{2/a_j}<1$. $\lambda\ge0$ as $p_i\ge0$. $\lambda>0$: if $\lambda=0$, free coordinates have $p_i=0$; $\sum p_i=1$ => some floored $k$ has $p_k>0$; moving mass from a free coordinate to $k$ raises $d\log N$; contradiction.
- D3.8.3 Hence $x_i=\max\{\epsilon^{2/a_j},p_i/\lambda\}$. $s\mapsto\log\max\{\epsilon^{2/a_j},e^s\}$ is 1-Lipschitz => $|\log(x_i/x_k)|\le|\log(p_i/p_k)|$. Multiply by $a_j/2$ ($l=x^{a_j/2}$).

**Output.** D3.9.4.
**Standard?** Specific to this paper (Lagrange multiplier with floor).
**Pitfall.** Only pairs with $p_i,p_k>0$; zero-probability pairs have zero coefficient in D3.9.

---

#### D3.9 Step eq:initial-product-energy — The optimized vector has small excitation energy
Lines 407–442. Label `eq:initial-product-energy` (437–440).

**Statement.** With $a_j\le\frac12$ (D3.6):
$$0\le\langle\phi,(H-E_0)\phi\rangle\le C\,\mathcal E,$$
$C=C(q,R,J)$, independent of $m$, of $C_{\rm pad}$, of the floor and of the dimensions of the $X_j$.

**Used from.** D3.5, D3.7, D3.8, D3.6; D2.10 (product decomposition, $\sum_\alpha\|c_\alpha\|\|d_\alpha\|\le q^{2v_R}J$); row/column Cauchy–Schwarz of D3.1.6.
**Proof.**
- D3.9.1 $KHK^{-1}\phi=E_0\phi$ ($H\Omega=E_0\Omega$, $K$ invertible). So $\langle\phi,(H-E_0)\phi\rangle=\sum_h\operatorname{Re}\langle\phi,(h-KhK^{-1})\phi\rangle$.
- D3.9.2 *Reduction for fixed $h$, support $S_h$.* $I_{\rm in}=\{i:X_i\cap S_h=\varnothing\}$, $I_{\rm out}=\{i:X_i\supseteq S_h\}$. By D3.5(d) and nesting: $I_{\rm in}=\{1,\dots,j-1\}$, $I_{\rm out}=\{j+1,\dots,m\}$, at most one $j$ in neither (split). $I_{\rm in}$ filters commute with $h$, innermost in $KhK^{-1}$. $I_{\rm out}$ filters: peel in descending order by D3.7 and cyclicity (operator inside supported in $X_i\supseteq S_h\cup X_{i-1}$). No split index: contribution $0$. Else $\operatorname{Re}\langle\phi,(h-L_jhL_j^{-1})\phi\rangle$.
- D3.9.3 *Split term in Schmidt bases.* $h=\sum_\alpha c_\alpha\otimes d_\alpha$ ($c_\alpha$ on $S_h\cap X_j$). Schmidt form of $\phi$ for $X_j\mid X_j^c$: $\phi=\sum_i\sqrt{p_i}\,e_i\otimes g_i$, $e_i$ common eigenbasis of $\rho_{\phi,X_j}$ and $L_j$ (D3.7). $H_{ik}=\sum_\alpha(c_\alpha)_{ik}(d_\alpha)_{ik}$ ($(ii,kk)$ matrix element of $h$; $H_{ki}=\overline{H_{ik}}$):
$$\operatorname{Re}\langle\phi,(h-L_jhL_j^{-1})\phi\rangle=-\sum_{i,k}\sqrt{p_ip_k}\Big(\cosh\log\frac{l_i}{l_k}-1\Big)\operatorname{Re}H_{ik},$$
pairing $(i,k)$ with $(k,i)$: $\operatorname{Re}[(\tfrac{l_i}{l_k}-1)H_{ik}+(\tfrac{l_k}{l_i}-1)\overline{H_{ik}}]=(\tfrac{l_i}{l_k}+\tfrac{l_k}{l_i}-2)\operatorname{Re}H_{ik}$, $t+1/t-2=2(\cosh\log t-1)$. Terms with $p_ip_k=0$ vanish.
- D3.9.4 *Coefficient bound.* $p_i,p_k>0$, $z=\frac12\log(p_i/p_k)$. D3.8: $\cosh\log\frac{l_i}{l_k}\le\cosh(a_jz)$. Taylor termwise: $\cosh t-1\le\frac12t^2\cosh t$. $\sqrt{p_ip_k}=\frac{p_i+p_k}{2\cosh z}$. With $a_j\le\frac12$:
$$\sqrt{p_ip_k}\,(\cosh(a_jz)-1)\le\frac{a_j^2}4(p_i+p_k)\frac{z^2\cosh(z/2)}{\cosh z}\le C a_j^2(p_i+p_k),$$
since $\sup_z z^2\cosh(z/2)/\cosh z\le\sup_z2z^2e^{-|z|/2}=32/e^2<4.4$.
- D3.9.5 *Row/column sums.* As D3.1.6: $\sum_{i,k}(p_i+p_k)|(c_\alpha)_{ik}(d_\alpha)_{ik}|\le2\|c_\alpha\|\|d_\alpha\|$; D2.10: $\sum_\alpha\|c_\alpha\|\|d_\alpha\|\le q^{2v_R}J$. Split term $\le Ca_j^2$, $C=C(q,R,J)$.
- D3.9.6 *Sum.* Each support split by at most one $X_j$ (D3.5(d)); $\le C(r+d_j)$ split by $X_j$ (D3.5(e)). Total $\le C\sum_j(r+d_j)a_j^2=C\mathcal E$.

**Output.** $1-|\langle\Omega,\phi\rangle|^2\le C\mathcal E/\Delta$ (D3.10, D3.11).
**Standard?** Specific to this paper.
**Pitfall.** $C$ independent of $C_{\rm pad}$, $m$, $\dim\mathcal H_{X_j}$: supports enter only via $q^{2v_R}J$ (D2.10). $a_j\le\frac12$ used in D3.9.4 ($\cosh(a_jz)\le\cosh(z/2)$).

---

#### D3.10 Step eq:initial-weight-range — Final choice of $C_{\rm pad}$
Lines 444–459. Label `eq:initial-weight-range` (448–453).

**Statement.** Fix $C_{\rm pad}=C_{\rm pad}(q,R,J,\Delta)$ so large that for all $r\ge1$, $m$, $j$:
(i) $C\mathcal E/\Delta\le\frac14$ ($C$ of D3.9), hence $|\langle\Omega,\phi\rangle|^2\ge1-C\mathcal E/\Delta\ge\frac34$;
(ii) $a_j\le\frac12$;
(iii) $\dfrac{a_j}{1-a_j}\le\dfrac1{32\sqrt{(1+J/\Delta)\mathcal B_j}}$.

**Used from.** D3.5(e), D3.6, D3.9, D3.1 (range of $u$).
**Proof.**
- D3.10.1 (i): $\mathcal E\le4D/\log\frac{C_{\rm pad}+1}{2+D}$ (D3.6), $C$ independent of $C_{\rm pad}$ (D3.9).
- D3.10.2 (iii): LHS $\le2a_j\le\frac4{Z_r(r+d_j)}\le\frac{4D}{\log\frac{C_{\rm pad}+1}{2+D}}\cdot\frac1{r+d_j}$. RHS $\ge c\,(r+d_j)^{-1/2}$ since $\mathcal B_j\le C(r+d_j)$ (D3.5(e)), $c=c(q,R,J,\Delta)>0$. $r+d_j\ge1$ => $(r+d_j)^{-1}\le(r+d_j)^{-1/2}$, so $\frac{4D}{\log((C_{\rm pad}+1)/(2+D))}\le c$ suffices.

**Output.** $C_{\rm pad}$ fixed; (iii) = admissibility of $u=-a_j/(1-a_j)$ in D3.11.
**Standard?** Specific to this paper.
**Pitfall.** Uniform in $r$ because $\mathcal B_j\sim r+d_j$ is matched by $a_j\sim1/(r+d_j)$.

---

#### D3.11 Step eq:initial-norm-lower — First norm comparison (lower bound on $-2\log N$)
Lines 461–495. Label `eq:initial-norm-lower` (491–494).

**Statement.** For the floor-$\epsilon$ maximizer,
$$-2\log N\ \ge\ \sum_{j=1}^ma_jS(X_j)-C(m+1)\mathcal E,$$
$C$ independent of the floor $\epsilon$.

**Used from.** D3.7, D3.9, D3.10, D3.1 (at $u=-a_j/(1-a_j)$), D3.2/D3.5(e).
**Proof.**
- D3.11.1 *Prefix problems.* $N_j$ = optimum with filters $1,\dots,j$ only (same floor, constraints), $N_0=1$, $N=N_m$. D3.7–D3.10 apply to each prefix (cost $\sum_{i\le j}(r+d_i)a_i^2\le\mathcal E$): prefix maximizer $\phi_j$ has $|\langle\Omega,\phi_j\rangle|\ge\sqrt{1-C\mathcal E}$, $C\mathcal E\le\frac14$ (rename $C\to C/\Delta$).
- D3.11.2 *Telescoping.* $L_1,\dots,L_j$ prefix maximizer, $K_{<j}=L_{j-1}\cdots L_1$, $\phi_j=L_jK_{<j}\Omega/N_j$:
$$\sqrt{1-C\mathcal E}\,N_j\le|\langle\Omega,L_jK_{<j}\Omega\rangle|=|\langle L_j\Omega,K_{<j}\Omega\rangle|\le\|L_j\Omega\|\,N_{j-1},$$
by $L_j=L_j^*$ and feasibility of $K_{<j}$ for prefix $j-1$.
- D3.11.3 *Hölder.* $\|L_j\Omega\|^2=\operatorname{Tr}\rho_{\Omega,X_j}L_j^2\le(\operatorname{Tr}\rho_{\Omega,X_j}^{1/(1-a_j)})^{1-a_j}$: Schatten Hölder, exponents $1/(1-a_j)$, $1/a_j$; $\|L_j^2\|_{1/a_j}=(\operatorname{Tr}L_j^{2/a_j})^{a_j}=1$.
- D3.11.4 *Lemma 3.1 at $u=-a_j/(1-a_j)$.* $1-u=\frac1{1-a_j}$, so $\operatorname{Tr}\rho^{1/(1-a_j)}=\mathbb Ee^{uK}$; $u$ admissible by D3.10(iii). $\log\|L_j\Omega\|^2\le(1-a_j)[uS(X_j)+512e\vartheta\mathcal B_ju^2]=-a_jS(X_j)+\frac{512e\vartheta\mathcal B_ja_j^2}{1-a_j}\le-a_jS(X_j)+C(r+d_j)a_j^2$ ($a_j\le\frac12$, $\vartheta=J/\Delta$, D3.5(e)).
- D3.11.5 *Sum.* $\log N=\sum_j\log(N_j/N_{j-1})\le\sum_j\big[\tfrac12\log\|L_j\Omega\|^2-\tfrac12\log(1-C\mathcal E)\big]$. Multiply by $-2$, use $\sum_j(r+d_j)a_j^2=\mathcal E$ and $-\log(1-v)\le2v$ for $v=C\mathcal E\le\frac14$:
$$-2\log N\ge\sum_ja_jS(X_j)-C\mathcal E-2mC\mathcal E\ge\sum_ja_jS(X_j)-C'(m+1)\mathcal E .$$

**Output.** D3.12(a), D3.14.
**Standard?** Specific to this paper.
**Pitfall.** Prefix optima $N_j$ are separate problems, each with own overlap bound; full maximizer not assumed to restrict to a prefix maximizer. Lemma 3.1 applied in $\Omega$ at cut $X_j\mid X_j^c$, not in a restricted Hamiltonian.

---

#### D3.12 Step eq:initial-trial-norm — Zero-floor limit and the trial-norm bound
Lines 497–562. Label `eq:initial-trial-norm` (524–527).

**Statement.** (a) As $\epsilon\downarrow0$, $N_\epsilon$ converges to $N$, the maximum of $\|L_m\cdots L_1\Omega\|$ over $L_j\ge0$ on $X_j$ with $\operatorname{Tr}L_j^{2/a_j}=1$; D3.11 holds for this $N$. (b) Schmidt form $\Omega=\sum_i\sqrt{p_i}\,u_i\otimes w_i$ at $X\mid X^c$, $p_i>0$; $T_j=X_j\setminus X$. For each $i$: $N\ge\sqrt{p_i}\,N_i$, $N_i:=\sup\|M_m\cdots M_1w_i\|$ over $M_j\ge0$ on $T_j$, $\operatorname{Tr}M_j^{2/a_j}=1$. (c)
$$\log N_i\ \ge\ -\frac12\sum_ja_jS_{w_i}(T_j).$$

**Used from.** D3.5(a) ($T_1\subseteq\dots\subseteq T_m$), D3.7, D3.11; vector three-lines [Tao, 247A Notes 1, Lemma 5.10].
**Proof.**
- D3.12.1 *(a).* Feasible sets shrink as $\epsilon$ grows: $N_\epsilon$ increases as $\epsilon\downarrow0$, bounded by $N$. Each feasible $L_j\ge0$ is a limit of strictly positive trace-normalized operators; their minimal eigenvalues as floors give $\liminf N_\epsilon\ge N$. RHS of D3.11 is $\epsilon$-independent => passes to the limit.
- D3.12.2 *(b).* $L_j=|u_i\rangle\langle u_i|\otimes M_j$ feasible: $\operatorname{Tr}L_j^{2/a_j}=\operatorname{Tr}|u_i\rangle\langle u_i|\cdot\operatorname{Tr}M_j^{2/a_j}=1$. Projector on $X$, $M_j$ on $T_j\subseteq X^c$: $L_m\cdots L_1\Omega=\sqrt{p_i}\,u_i\otimes M_m\cdots M_1w_i$. Take sup.
- D3.12.3 *(c), interpolation.* Fix strictly positive feasible $M_j$. $F_i(z)=M_m^z\cdots M_1^zw_i$ bounded analytic on $0\le\operatorname{Re}z\le1$; norm $1$ on $\operatorname{Re}z=0$ (unitaries).
- D3.12.4 *Boundary $\operatorname{Re}z=1$.* $U_j=M_j^{iy}$, $V_j=U_j\cdots U_1$, $V_0=\mathrm{id}$. Move unitaries left ($U_2M_2U_1M_1=U_2U_1\cdot U_1^*M_2U_1\cdot M_1$):
$$M_m^{1+iy}\cdots M_1^{1+iy}=(U_m\cdots U_1)\,(V_{m-1}^*M_mV_{m-1})\cdots(V_0^*M_1V_0).$$
$V_{j-1}$ supported in $T_{j-1}\subseteq T_j$, so $V_{j-1}^*M_jV_{j-1}$ positive on $T_j$, same spectrum, feasible. Leftmost unitary isometric: $\|F_i(1+iy)\|\le N_i$.
- D3.12.5 *Three lines, derivative.* Vector three-lines (test against unit vectors): $\log\|F_i(x)\|\le x\log N_i$, $x\in[0,1]$, equality at $x=0$ ($\|w_i\|=1$). Right derivative: $\frac d{dx}\log\|F_i(x)\|\big|_{0^+}=\sum_j\langle w_i,\log M_j\,w_i\rangle\le\log N_i$.
- D3.12.6 *Choice of $M_j$.* $M_j=\big((1-\delta)\rho_{w_i,T_j}+\frac\delta{\dim\mathcal H_{T_j}}\mathrm{id}\big)^{a_j/2}$, $0<\delta<1$: strictly positive, $\operatorname{Tr}M_j^{2/a_j}=1$. $\langle w_i,\log M_jw_i\rangle=\frac{a_j}2\sum_kp_k\log\big((1-\delta)p_k+\frac\delta{\dim}\big)\to\frac{a_j}2\sum_{p_k>0}p_k\log p_k=-\frac{a_j}2S_{w_i}(T_j)$ as $\delta\downarrow0$ (zero weight on kernel). Gives (c).

**Output.** D3.13.
**Standard?** Three-lines: standard. Unitary-commutation identity, Schmidt pinning: specific.
**Pitfall.** Pinned $L_j=|u_i\rangle\langle u_i|\otimes M_j$ not strictly positive: feasible only at zero floor, hence (a). Pinning removes $X$ from every $T_j$ at cost of the single term $-\log p_i$.

---

#### D3.13 Step eq:initial-norm-upper — Schmidt-averaged upper bound on $-2\log N$
Lines 564–573. Label `eq:initial-norm-upper` (570–573).

**Statement.**
$$-2\log N\ \le\ S(X)+\sum_{j=1}^ma_jS(T_j) .$$

**Used from.** D3.12.
**Proof.**
- D3.13.1 From $N\ge\sqrt{p_i}N_i$ and D3.12(c): $-2\log N\le-\log p_i+\sum_ja_jS_{w_i}(T_j)$ for every $i$.
- D3.13.2 Average with weights $p_i$: $\sum_ip_i(-\log p_i)=S(X)$; concavity: $\sum_ip_iS_{w_i}(T_j)\le S(\sum_ip_i\rho_{w_i,T_j})$; $\sum_ip_i|w_i\rangle\langle w_i|=\operatorname{Tr}_X|\Omega\rangle\langle\Omega|$ => $\sum_ip_i\rho_{w_i,T_j}=\rho_{\Omega,T_j}$, entropy $S(T_j)$.

**Output.** D3.14.
**Standard?** Concavity of entropy: standard. Rest specific.
**Pitfall.** $S(\cdot)$ = entropies in $\Omega$, as in D3.11.

---

#### D3.14 Step — Conclusion of Lemma 3.2
Lines 574–586.

**Statement.** $S(X\mid T)\le\frac12S(X)+C_{\rm buf}r$ for $C_{\rm buf}=C_{\rm buf}(q,R,J,\Delta)$.

**Used from.** D3.11, D3.12(a), D3.13, D3.5(a), D3.6; D2.2 item 2 (SSA).
**Proof.**
- D3.14.1 D3.11 (limit form) and D3.13: $\sum_ja_jS(X_j)-C(m+1)\mathcal E\le-2\log N\le S(X)+\sum_ja_jS(T_j)$.
- D3.14.2 $X_j=X\sqcup T_j$ so $S(X_j)-S(T_j)=S(XT_j)-S(T_j)=S(X|T_j)$. Hence
$$\sum_ja_jS(X\mid T_j)\le S(X)+C(m+1)\mathcal E .$$
- D3.14.3 $T_1\subseteq\dots\subseteq T_m$, SSA (D2.2 item 2): $S(X|T_j)\ge S(X|T_m)$. $a_j>0$, $\sum a_j=2$: $\sum_ja_jS(X|T_j)\ge2S(X|T_m)$ (also when $S(X|T_m)<0$).
- D3.14.4 $T_m\subseteq T$ ($d_m\le C_{\rm pad}r$) => $S(X|T)\le S(X|T_m)$ (SSA). So $S(X|T)\le\frac12S(X)+\frac12C(m+1)\mathcal E$.
- D3.14.5 $m+1\le(C_{\rm pad}/D+1)r$ ($r\ge1$), $\mathcal E\le4/Z_r$ bounded (D3.6), all parameters fixed: error $\le C_{\rm buf}r$.

**Output.** Lemma 3.2.
**Standard?** SSA: standard (Lieb–Ruskai 1973). Step specific.
**Pitfall.** Factor $\frac12=1/\sum_ja_j$, $\sum_ja_j=2$ fixed in D3.6; other total mass => other discount.

---

#### D3.15 Def — $F_{\rm box}(r)$
Lines 588–594.

**Statement.** For an integer $r\ge1$,
$$F_{\rm box}(r)=\sup S_\Omega(A\cap Q),$$
sup over admissible $H$ (unique ground vector, gap $\Delta$), domains $\Lambda$, cuts $A\subseteq\Lambda$, safe (D3.3, relative to $A$) integer rectangles $Q$ of size $\le r$; $q,R,J,\Delta$ fixed. $F_{\rm box}$ nondecreasing, $0\le F_{\rm box}(r)\le r^2\log q$.

**Used from.** D3.3, D1.2–D1.4.
**Proof.** $|A\cap Q|\le r^2$, $S\le|A\cap Q|\log q$; larger $r$ allows more rectangles.
**Output.** D3.16; §9 (`08-scanner.tex:540–543`), §11.
**Standard?** Definition.
**Pitfall.** Sup uniform over all $\Lambda,H,A$ (holes, disconnected components allowed): recursion in D3.16 must hold per instance.

---

#### D3.16 Proposition 3.3 — Initial safe-box estimate
Lines 596–668 (statement 596–604, proof 606–668). Label `prop:initial-box`; claim `eq:initial-box-bound` (600–603); recursion `eq:initial-box-recursion` (637–642).

**Statement.** There are $C<\infty$ and $e_0\in(0,1)$, depending only on $q,R,J,\Delta$, with
$$F_{\rm box}(r)\le C\,r^{1+e_0}\qquad(r\ge1).$$

**Used from.** D3.4 ($C_{\rm pad}$, $C_{\rm buf}$), D3.15, D3.3; D2.1 (chain rule $S(AB)=S(A)+S(B|A)$); D2.2 item 2 (SSA).

**Proof.**
- D3.16.1 *Children.* Integer $M\ge2$ (chosen D3.16.5). $Q$ safe parent, size $\le Mr$. $\operatorname{size}(Q)\le r$: $S_\Omega(A\cap Q)\le F_{\rm box}(r)$. Else cut each axis into chunks of $r$ sites plus possibly one shorter final chunk: $\le M$ chunks per axis, $\le M^2$ children $Q_i$ (chunk products), $\operatorname{size}(Q_i)\le r$, $\operatorname{dist}_\infty(Q_i,Z)\ge\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q)\ge D_0\operatorname{size}(Q_i)$: safe. $X_i=A\cap Q_i$ partition $A\cap Q$.
- D3.16.2 *Noninterior children.* $Q_i$ interior iff $Q_i^{+C_{\rm pad}r}\subseteq Q$. Chunk position $a\in\{1,\dots,n\}$ on an axis, $n\le M$: left containment needs $a\ge C_{\rm pad}+1$; right holds if $a\le n-C_{\rm pad}-1$ (parent has $\ge(n-1)r+1$ sites). Violating positions per axis: $a\le C_{\rm pad}$ or $a\ge n-C_{\rm pad}$, $\le2(C_{\rm pad}+2)$. Noninterior $\le2\cdot2(C_{\rm pad}+2)\cdot M=B_M:=4(C_{\rm pad}+2)M$. Thin parent ($n\le2(C_{\rm pad}+2)$ on an axis): all $\le M^2$ children may be noninterior; still counted, that axis contributing $\le2(C_{\rm pad}+2)$ positions times $\le M$ on the other.
- D3.16.3 *Random order.* Interior child: $Q_i^{+C_{\rm pad}r}$ meets $\le(2C_{\rm pad}+5)^2-1$ other children. Uniform random permutation of children. $E_i$: $Q_i$ after all children meeting its padded rectangle; $\Pr(E_i)\ge p_0:=(2C_{\rm pad}+5)^{-2}>0$ ($i$ last among $\le(2C_{\rm pad}+5)^2$). On $E_i$: $T=(A\cap Q_i^{+C_{\rm pad}r})\setminus X_i\subseteq X_{<i}$ (union of earlier children). Chain rule, any order: $S(A\cap Q)=\sum_iS(X_i|X_{<i})$. On $E_i$: $S(X_i|X_{<i})\le S(X_i|T)\le\frac12S(X_i)+C_{\rm buf}r$ (SSA; Lemma 3.2, $Q_0=Q_i$, parent $Q$ safe). Otherwise and for noninterior $i$: $S(X_i|X_{<i})\le S(X_i)$.
- D3.16.4 *Recursion* (eq:initial-box-recursion). Average over orders. Interior $i$: $\mathbb E\,S(X_i|X_{<i})\le S(X_i)-\Pr(E_i)\big(\tfrac12S(X_i)-C_{\rm buf}r\big)\le(1-\tfrac{p_0}2)S(X_i)+C_{\rm buf}r$, by $\Pr(E_i)\ge p_0$ on the negative term (needs $S(X_i)\ge0$), $\Pr(E_i)\le1$ on the error; no equality of $\Pr(E_i)$ across children needed. With $S(X_i)\le F_{\rm box}(r)$, $n_{\rm non}\le B_M$, $n_{\rm int}+n_{\rm non}\le M^2$:
$$S(A\cap Q)\le\big[(1-\tfrac{p_0}2)(M^2-n_{\rm non})+n_{\rm non}\big]F_{\rm box}(r)+C_{\rm buf}M^2r\le\big[(1-\tfrac{p_0}2)M^2+\tfrac{p_0}2B_M\big]F_{\rm box}(r)+CM^2r .$$
Parents of size $\le r$: same inequality since coefficient $\ge(1-p_0/2)M^2\ge1$ for $M\ge2$. Sup over $Q$: eq:initial-box-recursion for $F_{\rm box}(Mr)$.
- D3.16.5 *Choice of $M$.* $M\ge2$, $M\ge16(C_{\rm pad}+2)$. Then $B_M=4(C_{\rm pad}+2)M\le M^2/4$, coefficient $\le(1-\frac{3p_0}8)M^2\le\lambda:=(1-p_0/4)M^2$; $M<\lambda<M^2$ ($p_0\le\frac1{49}$, $M\ge48$). So $F_{\rm box}(Mr)\le\lambda F_{\rm box}(r)+CM^2r$.
- D3.16.6 *Iteration.* $f_j=F_{\rm box}(M^j)$: $f_{j+1}\le\lambda f_j+CM^{2+j}$. Divide by $\lambda^{j+1}$, sum: $f_j/\lambda^j\le f_0+\frac{CM^2}\lambda\sum_{i<j}(M/\lambda)^i\le f_0+\frac{CM^2}{\lambda-M}$, $f_0=F_{\rm box}(1)\le\log q$. So $F_{\rm box}(M^j)\le C\lambda^j$.
- D3.16.7 *Exponent.* $1+e_0:=\log_M\lambda=2+\frac{\log(1-p_0/4)}{\log M}\in(1,2)$; $e_0=1+\frac{\log(1-p_0/4)}{\log M}\in(0,1)$ since $0<-\log(1-p_0/4)<\log M$. $\lambda^j=(M^j)^{1+e_0}$.
- D3.16.8 *General $r$.* $j\ge0$ with $M^{j-1}<r\le M^j$. Monotone: $F_{\rm box}(r)\le F_{\rm box}(M^j)\le C(M^j)^{1+e_0}\le C(Mr)^{1+e_0}\le CM^2r^{1+e_0}$.

**Output.** $C$, $e_0$, $D_0$, $F_{\rm box}$ to §9–§11 (Exports); stage 1 of the outline (D1.14).
**Standard?** Specific to this paper ("average the chain rule over random orders" with per-child discount); recursion solving standard.
**Pitfall.**
- $M$ chosen after $C_{\rm pad}$ (hence $p_0$); $e_0$ depends on $M$ via $\log M$, can be small. Only $e_0<1$ claimed.
- Discount needed for a positive fraction of children only ($p_0$ lower bound), since noninterior children are $O(M)\ll M^2$.
- Children and parent safe w.r.t. the same $A$ (same $Z$); $F_{\rm box}$ uniform over instances, so $S(X_i)\le F_{\rm box}(r)$ per child.

---

#### D3.17 Step — Remarks closing §3
Lines 670–676.

**Statement.** Proposition 3.3 is uniform over induced domains (holes, several components). Only energy comparison is with the full $H$; no gap needed for restrictions to rectangles. Later sections improve $e_0$, then replace the box estimate by a mutual-information bound across a collar.

**Used from.** D3.9, D3.16.
**Output.** none (remark).
**Standard?** Remark.
**Pitfall.** Gap used only as $H-E_0\ge\Delta(\mathrm{id}-|\Omega\rangle\langle\Omega|)$ on the full system: D3.1 with $g_0=\Delta$ (D3.11.4), D3.10(i) (overlap).

---

## Parameters and constants

| Symbol | Value / meaning | Fixed in |
|---|---|---|
| $c_0$, $g_0$, $\vartheta=c_0/g_0$ | term-norm bound, gap, ratio; lattice: $J$, $\Delta$, $J/\Delta$ | D3.1; specialized D3.2 |
| $\mathcal B$ | $1+\sum_{i\in\mathcal I_\times}\log^2(ed_i)$ | D3.1 |
| $\ell_i$, $\delta_i$ | $\log(ed_i)$, $1/(8\ell_i)$ | D3.1.7 |
| $u$-range | $|u|\le[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}$ | D3.1 |
| $512e$, $128e$, $256e$ | MGF constant, tilted-energy constant, halving constant ($512e=2\cdot256e$) | D3.1.9, D3.1.11, D3.1.12 |
| $2e^{e/2}$ | tail prefactor | D3.1.13 |
| $C_1$, $C_M$ | $\max\{1,2v_R\mu_R(1+v_R\log q)^2\}$; $32(M+2)\sqrt{(1+\vartheta)C_1}$ (expansion, paper: depends on $q,R,J,\Delta,M$) | D3.2 |
| $D_0$ | $>2R+10$; safety factor | D3.3 |
| $D$ | integer $>2R+2$; margin between regions | D3.4 (before D3.5) |
| $C_{\rm pad}$ | integer; $>D+1$, then large so $a_j\le\frac12$, then larger for D3.10 (i),(iii); depends on $q,R,J,\Delta$ | D3.6, D3.10 |
| $m$, $d_j$ | $\lfloor(C_{\rm pad}-1)r/D\rfloor$; $r+jD$ | D3.5 |
| $Z_r$, $a_j$, $\mathcal E$ | $\sum_{j\le m}\frac1{r+d_j}$; $\frac2{Z_r(r+d_j)}$; $4/Z_r$ | D3.6 |
| $\epsilon$ | filter floor, $(\dim\mathcal H_{X_j})\epsilon^{2/a_j}<1$; sent to $0$ | D3.7, D3.12 |
| $C$ (D3.9) | $C(q,R,J)$, independent of $C_{\rm pad}$, $m$, floor, dimensions | D3.9 |
| $C_{\rm buf}$ | $C_{\rm buf}(q,R,J,\Delta)$, depends on $C_{\rm pad}$ | D3.14 |
| $F_{\rm box}$ | sup of $S_\Omega(A\cap Q)$ over safe $Q$, size $\le r$ | D3.15 |
| $B_M$, $p_0$ | $4(C_{\rm pad}+2)M$; $(2C_{\rm pad}+5)^{-2}$ | D3.16.2, D3.16.3 |
| $M$ | integer $\ge\max\{2,16(C_{\rm pad}+2)\}$ | D3.16.5 |
| $\lambda$ | $(1-p_0/4)M^2$, $M<\lambda<M^2$ | D3.16.5 |
| $e_0$ | $1+\log(1-p_0/4)/\log M\in(0,1)$ | D3.16.7 |
| $C$ (Prop 3.3) | $q,R,J,\Delta$ only | D3.16.6, D3.16.8 |

## Dependencies

**Consumes.**
- §1: $\Lambda$, $d_\Lambda$, admissible $H$ (D1.1, D1.2), $\partial_\Lambda$, $S_\Omega$ (D1.3), Theorem 1.1 hypotheses: unique $\Omega$, gap $\Delta$ (D1.4), $Z_A$ (D1.6).
- §2: SSA, conditioning decreases conditional entropy (D2.2 item 2); ambient dilation (D2.6); $v_r$, $\mu_R$ (D2.7, D2.8); crossing count (D2.9, eq:crossing-count); product decomposition with bounded norms (D2.10); $q\ge2$, $R\ge1$ (D2.11); constants convention (D2.13). Lemma 2.1 (continuity) not used in §3.
- External: three-lines (Tao, 247A Notes 1, Lemma 5.10), Cauchy coefficient estimate, Schatten–Hölder, concavity of entropy, entropy chain rule.

**Exports.**
- Lemma 3.1 (D3.1): §4 (truncated Hamiltonian, `02-initial.tex:25–28`, $\mathcal B_X$ of D4.14), tail with $w=n^{3/5}$ in §8 (`07-comparators.tex:43–47`), §9 (`08-scanner.tex:404–414`), §10 (`09-amplification.tex:300–310`).
- Lattice specialization (D3.2): tail width $C_M\sqrt{1+b'}\log(n+2)$, failure mass $(n+2)^{-M}$.
- Definitions D3.3, D3.15: $D_0$, "safe", $F_{\rm box}$ (§9 `08-scanner.tex:540–543`, §11).
- Proposition 3.3 (D3.16): $F_{\rm box}(r)\le Cr^{1+e_0}$, $e_0\in(0,1)$: §9 improves the exponent (`08-scanner.tex:674–795`, uses $e_0\in(0,1)$ at 692); box/shell entropy bounds of §9–§11 (`10-geometry.tex:723–755`); stage 1 of the outline (D1.14).
- Lemma 3.2 (D3.4): consumed inside D3.16 only; no other section cites `lem:initial-buffer`.
