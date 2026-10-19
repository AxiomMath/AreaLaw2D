# Overview — "A two-dimensional area law from a global spectral gap"

Digest files: `01-introduction.md` (§1) … `11-geometry.md` (§11). Anchors `D<sec>.<n>` are sequential in digest-file order, not paper numbers. Paper result -> anchor:

- §1: Thm 1.1 = D1.4 (statement) / D11.26 (proof); Cor 1.2 = D1.7; Lemma 11.1 also quoted as D1.12.
- §2: Lemma 2.1 = D2.4; Lemma 2.2 = D2.12.
- §3: Lemma 3.1 = D3.1; Lemma 3.2 = D3.4; Prop 3.3 = D3.16.
- §4: Lemma 4.1 = D4.4; Lemma 4.2 = D4.5; Prop 4.3 = D4.6; Lemma 4.4 = D4.10; Prop 4.5 = D4.11.
- §5: Lemma 5.1 = D5.5; Lemma 5.2 = D5.12; Lemma 5.3 = D5.15.
- §6: Lemma 6.1 = D6.4; Lemma 6.2 = D6.6; Lemma 6.3 = D6.10; Lemma 6.4 = D6.12.
- §7: Lemma 7.1 = D7.3; Lemma 7.2 = D7.5; Lemma 7.3 = D7.7; Prop 7.4 = D7.14.
- §8: Prop 8.1 = D8.8.
- §9: Lemma 9.1 = D9.8; Prop 9.2 = D9.9; Def 9.3 = D9.14; Lemma 9.4 = D9.15; Prop 9.5 = D9.19; Prop 9.6 = D9.25.
- §10: Lemma 10.1 = D10.2; Prop 10.2 = D10.4.
- §11: Lemma 11.1 = D11.1; Prop 11.2 = D11.4; Lemma 11.3 = D11.13; Lemma 11.4 = D11.15; Lemma 11.5 = D11.18.

---

## 1. Main results (exact)

**Setting** (D1.1–D1.3, D1.6, D1.11).
- $\Lambda\subset\mathbb Z^2$ finite; edges $\{x,y\}\subseteq\Lambda$, $|x-y|_1=1$; $d_\Lambda$ = graph distance of the induced graph ($+\infty$ across components). $\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}\mathbb C^q$.
- Admissible $H$ ($q\ge1$, $R\ge0$ integers, $J>0$): $H=\sum_{\varnothing\ne X\subseteq\Lambda,\ \operatorname{diam}_{d_\Lambda}X\le R}h_X$, $h_X=h_X^*$, $\|h_X\|\le J$, $h_X$ supported on $X$, one summand per support (eq:hamiltonian).
- $\partial_\Lambda A=\{\{x,y\}:x\in A,\ y\in\Lambda\setminus A,\ |x-y|_1=1\}$. $\partial_{\rm in}A=\{x\in A:\exists y\notin A,\{x,y\}\in\partial_\Lambda A\}$. $Z_A=\bigcup_{e\in\partial_\Lambda A}e$.
- $\rho_A=\operatorname{Tr}_{\Lambda\setminus A}|\Omega\rangle\langle\Omega|$, $S_\Omega(A)=-\operatorname{Tr}\rho_A\log\rho_A$ (natural log), $I_\Omega(B:C)=S_\Omega(B)+S_\Omega(C)-S_\Omega(BC)$ for disjoint $B,C$.

**Theorem 1.1** (`00-introduction.tex` L39–L53; proof `10-geometry.tex` L801–L857 = D11.26). For all integers $q\ge1$, $R\ge0$ and reals $J>0$, $\Delta>0$ there is a finite $C=C(q,R,J,\Delta)$ such that: for every finite induced domain $\Lambda\subset\mathbb Z^2$, every admissible $H$ on $\mathcal H_\Lambda$ with unit ground vector $\Omega$ (unique up to phase), ground energy $E_0$ and
$$H-E_0\,\mathrm{id}\ \ge\ \Delta\,(\mathrm{id}-|\Omega\rangle\langle\Omega|),$$
and every $A\subseteq\Lambda$:
$$S_\Omega(A)\le C\,|\partial_\Lambda A|.\qquad\text{(eq:area-law)}$$
Quantifiers: $\forall(q,R,J,\Delta)\ \exists C\ \forall(\Lambda,H,A)$. $C$ is uniform in the domain, its shape, holes, connectedness, $H$. The gap is the gap of the whole $H$; no gap for restrictions.

**Corollary 1.2** (`00-introduction.tex` L69–L86 = D1.7).
- (a) Thm 1.1 holds for every subset of a finite rectangle $\{1..L_1\}\times\{1..L_2\}$ with bounded on-site and nearest-neighbour terms, unique ground state, fixed global gap ($R=1$ after merging terms on equal supports).
- (b) With $C$ the constant of Thm 1.1: $S_\Omega(A)\le4C\,|\partial_{\rm in}A|$ and $S_\Omega(A)\le2C\,|Z_A|$.
- Proof: $|\partial_{\rm in}A|\le|\partial_\Lambda A|\le4|\partial_{\rm in}A|$ (degree $\le4$); $|Z_A|\le2|\partial_\Lambda A|\le4|Z_A|$ (double count $\sum_{v\in Z_A}c(v)=2|\partial_\Lambda A|$, $1\le c(v)\le4$). Not used by §2–§11.

---

## 2. Proof architecture

### 2.1 Dependency DAG

Edge `X <- Y, Z` = proof of X consumes Y, Z. Anchors of the same lemma are grouped on following lines (`internal`). External facts omitted here (see §6).

```
# top
D1.4 (Thm 1.1)  := D11.26
D11.26 <- D1.4, D1.6, D2.11, D2.12, D11.1, D11.4, D9.25, D10.4, D9.14      # M=100 in D10.4
D1.7 (Cor 1.2) <- D1.4, D1.6                                              # leaf

# §2 (no deps on later sections)
D2.2 <- D2.1                       D2.4 <- D2.1, D2.2, D2.3, D2.5
D2.7 <- D2.6                       D2.8 <- D2.7          D2.9 <- D2.7, D2.8
D2.10 <- D2.8                      D2.11 <- D1.4         D2.12 <- D1.2, D1.4

# §3
D3.1  <- (none)                    D3.2 <- D3.1, D2.8, D2.9
D3.4 (L3.2) <- D3.1, D3.2, D3.3, D2.2, D2.7-D2.10, D3.5-D3.14
  internal: D3.5 <- D3.3, D2.6-D2.9, D3.2        D3.6 <- D3.5
            D3.7 <- D3.5, D3.6                   D3.8 <- D3.7
            D3.9 <- D3.5, D3.6, D3.7, D3.8, D2.10
            D3.10 <- D3.5, D3.6, D3.9, D3.1      D3.11 <- D3.1, D3.2, D3.7, D3.9, D3.10
            D3.12 <- D3.5, D3.7, D3.11           D3.13 <- D3.12
            D3.14 <- D3.5, D3.6, D3.11, D3.12, D3.13, D2.2
D3.16 (P3.3) <- D3.4, D3.3, D3.15, D2.1, D2.2

# §4
D4.4 (L4.1) <- D4.1-D4.3, D2.7     D4.5 (L4.2) <- (none)      D4.9 <- (none)
D4.7 <- D4.5                       D4.8 <- D4.2, D4.4, D4.5
D4.6 (P4.3) <- D4.2, D4.4, D4.5, D4.7, D4.8, D4.9
D4.10 (L4.4) <- D4.6, D4.9, D4.2
D4.12 <- D4.3, D4.6, D2.7          D4.13 <- D4.6, D4.12, D2.5
D4.14 <- D4.3, D2.7, D4.11(defs)
D4.11 (P4.5) <- D4.6 [p=1], D4.12, D4.13, D4.14

# §5 (no Hamiltonian)
D5.2 <- D5.1, D2.1                 D5.3 <- D5.2          D5.4 <- D5.2, D5.3
D5.6 <- D5.2, D5.4                 D5.7 <- D5.2, D5.4, D5.6      D5.8 <- D5.1
D5.9 <- D5.2, D5.3, D5.6, D5.7, D5.8
D5.10 <- D5.4, D5.9, D2.4, D2.5    D5.11 <- (none)
D5.5 (L5.1) <- D5.4, D5.6, D5.7, D5.9, D5.10, D5.11, D2.2
D5.12 (L5.2) <- D5.1, D5.2, D5.13, D5.14
D5.15 (L5.3) <- D5.1, D5.12, D5.16, D5.17, D5.18, D5.19, D5.20, D2.2

# §6 (k -> infinity, fixed finite system)
D6.3 <- D6.2                       D6.4 (L6.1) <- D6.1, D6.2, D6.3       D6.5 <- D6.3
D6.6 (L6.2) <- D6.2, D6.3, D6.4, D6.5
D6.7 <- D6.4, D6.5, D6.6           D6.8 <- D6.4, D6.6
D6.9 <- D6.3, D6.4, D6.6, D6.8
D6.10 (L6.3) <- D6.1, D6.4, D6.6, D6.8, D5.5                  # gain
D6.12 (L6.4) <- D6.4, D6.6, D6.8, D6.9, D6.11, D6.13-D6.16, D5.15   # cost
  internal: D6.13 <- D6.4, D6.6, D6.8, D6.9    D6.14 <- D6.11    D6.15 <- D6.13, D6.14
            D6.16 <- D6.13, D6.14, D6.15, D5.15

# §7
D7.3 (L7.1) <- D7.1, D7.2          D7.5 (L7.2) <- D7.1-D7.4, D7.3      D7.7 (L7.3) <- D7.6
D7.8 <- D6.5, D6.6, D6.8           D7.9 <- D7.2, D7.8
D7.10 <- D2.1, D6.10               D7.11 <- D7.9, D7.10
D7.12 <- D7.8, D7.11, D6.5, D6.9   D7.13 <- D6.11
D7.14 (P7.4) <- D7.3, D7.5, D7.7, D7.8-D7.13, D6.10, D6.12, D7.15-D7.27
  internal (a): D7.15 <- D7.5, D7.9     D7.16 <- D7.5, D7.7, D7.15
  internal (b): D7.17 <- D7.3, D7.9     D7.18 <- D6.10, D7.3, D7.10, D7.17
                D7.19 <- D7.13, D6.11   D7.20 <- D7.13, D7.16, D7.17, D7.18, D7.19
  internal (c): D7.21 <- D7.12          D7.22 <- D7.3, D7.5, D7.12, D7.21
                D7.23 <- D7.5, D7.7, D7.22   D7.24 <- D6.12, D7.9, D7.11, D7.12, D7.21
                D7.25 <- D7.14(setup), D7.21, D7.23, D7.24
  D7.26 <- D7.5, D7.14, D7.20          D7.27 <- D7.14, D7.15, D7.23

# §8 (abstract: any pure Omega~, positive H~ with gap g~)
D8.6 <- D6.4, D6.5, D6.6, D6.8, D6.9         D8.7 <- D7.3, D8.1
D8.5 ~ shape of D3.1 (assumption in §8)       D8.3 <- D8.2     D8.11 <- D8.2
D8.8 (P8.1) <- D8.1-D8.7, D8.9-D8.37
  rough upper : D8.20 <- D8.15, D8.16, D8.18, D8.19, D7.3
                D8.15 <- D8.14 <- D8.11;  D8.16 <- D8.6;  D8.18 <- D8.4, D8.9, D8.12, D8.17
  sharp upper : D8.22 <- D8.5, D8.10, D8.15, D8.16, D8.17, D8.21;  D8.21 <- D8.7, D8.12, D8.13, D8.16
  lower       : D8.35 <- D8.34 <- D8.23, D8.33;  D8.33 <- D8.32, D7.3;  D8.32 <- D8.6, D8.31
                D8.31 <- D8.24, D8.30;  D8.30 <- D8.5, D8.10, D8.24, D8.26-D8.29
  identity    : D8.36 <- D8.1, D2.1

# §9
D9.2 <- D9.1 <- D2.6               D9.3 <- D4.11, D4.13, D4.14
D9.4 <- D8.6, D9.2                 D9.5 <- D9.4          D9.6 <- D9.3, D9.5
D9.7 <- D7.3, D7.9, D7.14, D9.4-D9.6
D9.8 (L9.1) <- D9.2-D9.7, D4.11, D6.4, D8.1, D2.7, D2.8
D9.9 (P9.2) <- D9.3, D9.8, D9.10-D9.13, D8.2-D8.5, D8.8, D4.11, D4.13, D4.14, D3.1, D2.4
  internal: D9.10 <- D9.8, D7.10, D7.13, D7.14     D9.11 <- D7.14(b), D9.10
            D9.12 <- D9.11, D7.3, D6.9, D8.8, D8.3 D9.13 <- D7.14(c), D9.10, D9.12
D9.14 (Def 9.3) <- D3.3, D3.15, D3.16
D9.15 (L9.4) <- D9.14, D9.16-D9.18, D3.3, D3.15, D2.2
D9.19 (P9.5) <- D3.16, D9.9, D9.15, D8.8, D9.20-D9.24
  internal: D9.20 <- D3.16   D9.21 <- D9.18, D9.20   D9.22 <- D9.9, D9.20
            D9.23 <- D8.3, D8.8, D9.9, D9.22         D9.24 <- D9.21, D9.23
D9.25 (P9.6) <- D9.19, D9.15, D9.9, D8.8, D2.4, D4.11, D4.13, D9.26-D9.30
  internal: D9.26 <- D9.9, D9.15, D9.19    D9.27 <- D8.8, D9.26   D9.28 <- D8.36, D2.2
            D9.29 <- D9.26, D9.27, D9.28   D9.30 <- D2.4, D4.13, D9.15

# §10 (uses exact H_F, p >= 10^6; NOT the truncated H~ of §9)
D10.1 <- D4.6, D4.2                D10.2 (L10.1) <- D4.2, D4.9, D4.10, D2.7
D10.3 <- D10.1, D10.2
D10.4 (P10.2) <- D10.1, D10.2, D10.3, D10.5-D10.16, D3.1, D2.2, D2.4, D2.5, D2.9
                 + hypotheses (size, cuts, MI <= C0 n^{1-eps}) from D9.25
  internal: D10.5 <- D3.1, D2.8, D2.9      D10.7 <- D10.5, D10.6
            D10.8, D10.9, D10.10 <- D10.5, D10.6, D10.7
            D10.11 <- D10.1, D10.2, D10.3, D10.8   D10.12 <- D10.2, D10.3, D10.7, D10.8, D10.11
            D10.13 <- D10.9, D10.10, D10.12   D10.14 <- D10.2, D10.7, D10.13
            D10.15 <- D2.4, D2.5, D10.6, D10.14   D10.16 <- D10.1, D10.11

# §11 (D11.4 consumes no operator input)
D11.1 <- D2.1, D2.2                D1.12 == D11.1
D11.4 (P11.2) <- D11.2, D11.25, D9.14, D9.15, D1.6
  internal: D11.6 <- D11.5   D11.7 <- D11.6   D11.8 <- D11.2, D11.6   D11.9 <- D11.6, D11.8
            D11.10 <- D11.6, D11.7, D11.8   D11.11 <- D11.8, D11.10   D11.12 <- D11.9, D11.11
            D11.13 <- D11.7, D11.8, D11.11, D11.12   D11.14 <- D11.2, D11.12, D11.13
            D11.15 <- D11.13, D11.14   D11.16 <- D11.5, D11.14   D11.17 <- D11.10, D11.11, D11.14
            D11.18 <- D11.13, D11.14, D11.15, D11.17   D11.19 <- D11.9, D11.11, D11.12, D11.14, D11.15
            D11.20 <- D11.6, D11.16, D11.19   D11.21 <- D11.2, D11.5, D11.6, D11.10, D9.14
            D11.22 <- D11.11, D11.14, D11.15   D11.23 <- D11.6, D11.15, D11.22, D9.15, D9.25
            D11.24 <- D11.2, D11.14, D11.18, D11.21, D11.22, D11.23
            D11.25 <- D11.6, D11.7, D11.10, D11.16-D11.24
D11.2 <- D10.1 (beta), D9.25 (L, eps=ell)
```

Critical path (longest chain of numbered results):
`D11.26 <- D10.4 <- D9.25 <- D9.19 <- D9.9 <- D7.14 <- D6.10, D6.12 <- D5.5, D5.15 <- D2.4`, with side inputs D3.16 -> D9.19; D4.11 -> D9.3/D9.9; D8.8 -> D9.9/D9.19/D9.25; D4.6/D4.10 -> D10.2 -> D10.4; D3.1 -> D3.4, D8.5, D9.9, D10.5.

Three Hamiltonian-like objects, never mixed (Pitfall for any refactor):
- $H$ original: §3 (Lemma 3.1/3.2 energy), D10.5 (typical projections), the gap hypothesis.
- $\widetilde H=\sum k_{i,r_i}$, truncated, $p=1$, depends on $S_0=A\cap T_L$: §8 (as $\widetilde H$), §9. Entropies of $\widetilde\Omega$ are transferred to $\Omega$ by D2.4 + D4.13 at cost $O(n^{-248})$ (D9.30).
- $H_F=\sum k_i$, exact, $p\ge10^6$, $\alpha>1-10^{-6}$: §10 only.

### 2.2 Milestone statements (one line each, constants as in the paper)

- **D2.4 Lemma 2.1.** $|S(D|E)_\rho-S(D|E)_\sigma|\le2\delta\log d_D+(1+\delta)h(\tfrac\delta{1+\delta})\le C\sqrt\delta\log(ed_D)$, $\delta=\tfrac12\|\rho-\sigma\|_1$; no $\dim E$.
- **D3.1 Lemma 3.1.** $\log\mathbb Ee^{uK}\le uS+512e\,\vartheta\mathcal B u^2$ for $|u|\le[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}$; $\Pr\{|K-S|>w\}\le2e^{e/2}\exp(-w/(32\sqrt{(1+\vartheta)\mathcal B}))$; $\mathcal B=1+\sum_{\rm crossing}\log^2(ed_i)$, $\vartheta=c_0/g_0$.
- **D3.4 Lemma 3.2.** $S(X|T)\le\tfrac12S(X)+C_{\rm buf}r$ for $X=A\cap Q_0$, $T=(A\cap Q_0^{+C_{\rm pad}r})\setminus X$, $Q_0^{+C_{\rm pad}r}\subseteq Q$ safe.
- **D3.16 Prop 3.3.** $F_{\rm box}(r)\le Cr^{1+e_0}$, $e_0\in(0,1)$.
- **D4.6 Prop 4.3.** $k_i\in[0,I]$, $k_i\Omega=0$, $H_F=\sum k_i\ge c_*^{-1}(H-E_0)\ge g(I-P_\Omega)$, $g=\Delta/c_*$, $\|k_i-E_{i,l}k_i\|\le Ce^{-cl^\alpha}$, $\alpha=p/(p+1)$.
- **D4.11 Prop 4.5** ($p=1$). $r_0=\lceil C_1(\log n)^2\rceil$, $r_i=\max\{r_0,\lfloor d_\Lambda(a_i,S_0)/2\rfloor\}$, $\|\widetilde H-H_F\|\le\min\{n^{-1000},g/4\}$, $\widetilde E_0\le n^{-1000}$, gap $\ge g/2$, $\|\widetilde\Omega-\Omega\|\le2\sqrt{\epsilon_n/g}$, $\mathcal B_X\le C(1+b_X)(r_0+1)^6$.
- **D5.5 Lemma 5.1.** $\|\sigma^{a/2}\widehat\rho_P^{-a/2}\tau^{a/2}\widehat\rho_U^{-a/2}\theta\|\le\exp(-\tfrac a2\eta+Ca^{5/4}\ell^2)$, $\eta=I(x:F|U)=I(x:F|P)$, $\ell=\log(e\dim x)$, $a\ell\le c$.
- **D5.15 Lemma 5.3.** $|f(a/2)|-\operatorname{Re}f(a/2)\le Ca^2\ell_h^4\eta^{1/8}$.
- **D6.10 Lemma 6.3.** $C_{x,k}\ge\poly(k)^{-1}\exp\{ka[\eta_\theta-Ca^{1/4}\log^C(e\dim x)]\}P_{\theta,k}$ on $\operatorname{Sym}^k$.
- **D6.12 Lemma 6.4.** $\operatorname{Tr}\sigma\mathcal D_k\le Ca^2\log^C(ed_h)\int\eta_\theta^{1/8}d\mu_\sigma+o_k(1)$ uniformly in $\sigma$.
- **D7.14 Prop 7.4.** (a) $-\partial_p\log N^2=\sum_hw_h\int m_s\operatorname{Tr}(\sigma_{h,u}\log C_h)du$; (b) $\ge ka\sum\int\!\!\int\eta\,d\mu-CkaK a^{1/4}\ell^C-\beta_k$; (c) $\langle v,\bar Hv\rangle\le2E_0+Ca^2\ell^C\sum\!\int\!\!\int\eta^{1/8}+o_k(1)$; $s=\tfrac14$.
- **D8.8 Prop 8.1.** Rough/sharp upper and lower bounds on $-\log N^2/k$; $E_{\rm def}=(\langle v,\overline{\widetilde H}v\rangle-\widetilde E_0)/\widetilde g$; $2S_X+g^{\rm pre}-g^{\rm post}=I(X{:}V)+I(X{:}YV)$.
- **D9.9 Prop 9.2.** Some (round, $p_k\in[\epsilon/2,\epsilon]$) has $E_{{\rm def},k}\le Cn^\ell D^2W^2(\log n)^C(\delta_n^{1/8}+\epsilon+n^{-100})+Cn^{-1000}+o_k(1)$, $\delta_n=C_e\epsilon^{-1}(n^{e-\mu}+a^{1/4}(\log n)^C)$.
- **D9.19 Prop 9.5.** $F_{\rm box}(r)\le Cr^{1+e_*}$, $e_*=2\cdot10^{-6}$.
- **D9.25 Prop 9.6.** Template $T$ separated from cut, $L=\lfloor n^{1-10^{-5}}\rfloor\le s_0$, $X=A\cap T$, $S_0=A\cap T_L$: $I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-\varepsilon}$, $\varepsilon=10^{-5}$; $|S_0|=O(n^2)$; cuts of $X,S_0,S_0\setminus X$ are $O(n)$.
- **D10.4 Prop 10.2.** Hyp: $|S_0|\le C_0n^2$, cuts $\le C_0n$, $I_\Omega(X:\Lambda\setminus S_0)\le C_0n^{1-\varepsilon}$. Concl: $\forall M\ \exists r\le C_Mn^{(1-\varepsilon)/\alpha}$, $L+2r=o(n^\beta)$, $I_\Omega(X:J)\le C_Mn^{-M}$ $\forall J\subseteq\Lambda\setminus N_{2r}(S_0)$; if $\operatorname{dist}_\infty(T,Z)>L+n^\beta$ then $N_{2r}(S_0)\subseteq A$.
- **D11.1 Lemma 11.1.** $I_\psi(X_i:B\cup\bigcup_{j<i,\,j\in\mathcal I_f}X_j)\le\varepsilon_i\Rightarrow S_\psi(A)\le S_\psi(D)+\tfrac12\sum_i\varepsilon_i$.
- **D11.4 Prop 11.2.** $A=D\dot\cup\dot\bigcup X_i$, $|D|\le Cb$, $X_i\subseteq A\cap T_i$ template$(n_i,s_i)$, $n_i\ge n_*$, $L_i\le s_i$, $\operatorname{dist}_\infty(T_i,Z)>2n_i^\beta$, $\operatorname{dist}_\infty(T_i,\bigcup_{j<i,f_j=f_i}X_j)>2n_i^\beta$, $\sum n_i^{-100}\le Cb$.

### 2.3 Induction / bootstrapping logic (ordered)

Top-down reduction, then bottom-up supply. A 1-to-1 formalization must reproduce the order of choices.

1. **Reduction (D11.26, D1.4.1–D1.4.7).** Trivial cases ($q=1$, $\Lambda=\varnothing$, $A\in\{\varnothing,\Lambda\}$, $R=0$: D2.11) and $b=|\partial_\Lambda A|=0$ (D2.12) give $S_\Omega(A)=0$. For $b>0$: $S_\Omega(A)\le|D|\log q+\tfrac12\sum_i\varepsilon_i$ (D11.1) with $\varepsilon_i=Cn_i^{-100}$. Needs $I_\Omega(X_i:J_i)\le Cn_i^{-100}$ for the **whole** set $J_i=(\Lambda\setminus A)\cup\bigcup_{j<i,f_j=f_i}X_j$.
2. **Two-family cancellation (D11.1).** Chain rule for each family $f$, purity of $\Omega$, subadditivity. Summing $f=0,1$ cancels every $S(X_i)$. Only same-family earlier tiles and $B=\Lambda\setminus A$ enter the conditioning set.
3. **Geometry supplies tiles (D11.4).** Pure plane geometry: dyadic layers around $Z$, primary tiles of pitch $s_k=2^{\lfloor(1+\delta_0)k\rfloor}$, belt strips of width $t_k=2^{\lfloor\zeta k\rfloor}$, fans with opposite labels, recursive repair of same-label point contacts at scale $d(S)\approx S^{\rho_0}$; $|D|\le Cb$, $\sum n_i^{-100}\le Cb$. Each tile is a template (D9.14) with scanner scale $n_i$; clearance $>2n_i^\beta$ is what makes $J_i\subseteq\Lambda\setminus N_{2r_i}(S_i)$ (D11.26.3).
4. **Amplification (D10.4).** From $I_\Omega(X:\Lambda\setminus S_0)\le C_0n^{1-\varepsilon}$ to $n^{-M}$ ($M=100$) outside $N_{2r}(S_0)$. Mechanism: typical projections of width $w=n^{3/5}$ (D10.5) give restoring operator $R_0$ with $\|R_0\|\le e^{(\mathcal I+3w)/2}$ (D10.8); run constraint clocks for $t_*=C(\mathcal I+w+K\log n)$ with $K\ge4(M+3)$ (D10.11): gap $g$ kills the excited part (D10.3), light cone localizes to $N_{2r}(S_0)$ (D10.2), $r=\lceil(C'(t_*+K\log n))^{1/\alpha}\rceil\le C_Mn^{(1-\varepsilon)/\alpha}$; polar decomposition gives local unitary (D10.14); continuity (D2.4) costs only $\log\dim e'\le Cn^2$ (D10.15). Scale match: $(1-10^{-5})/\alpha<1-2\cdot10^{-6}=\beta$; paper takes $\alpha>1-10^{-6}$, i.e. $p\ge10^6$ (D10.1), which suffices. This is why §10 uses the exact $H_F$ with large $p$.
5. **Sublinear collar bound (D9.25).** MI sublinear in the perimeter: $I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-10^{-5}}$ while $|\partial X|\sim n$. Mechanism: norm $N=\|\mathcal M^{-1/4}\mathrm{pre}_k\|$ of the filtered replica vector bounded above (pin to Bell pair on typical Schmidt set of $X$; D8.20–22) and below (gap forces most copies into ground state; D8.23–35). Sharp lower minus sharp upper, together with the exact identity $2S_X+g^{\rm pre}-g^{\rm post}=I(X{:}V)+I(X{:}YV)\ge I(X:\Lambda\setminus S_0)$ (D8.36, D9.28), gives the MI bound (D9.27, D9.29). Error table: worst power $n^{0.999952}<n^{0.99999}$ (D9.29).
6. **Scanner (D9.9, D9.8).** $K=\lfloor L/(8m)\rfloor$ bands, random offsets in $\{0..m-1\}$, $2nm$ fill/charge rounds move a near and a far partition through the collar of depth $L$. Per term the split probability is $\le CD/m$ (offsets), selection probability at a charge is $\ge c/(nD)$ (D9.8). Entropy production per round is $\ge$ (gain of D7.14b) $-$ error; integrated over all rounds it is bounded by the rough upper comparison (D9.12). So some (round, $p_k\in[\epsilon/2,\epsilon]$) has small split-entropy density $\delta_n$. At that point the energy defect is small via cost $\eta^{1/8}$ (D7.14c, D9.13). Small $E_{\rm def}$ is the hypothesis that makes the lower comparison of D8.8 non-vacuous.
7. **Gain vs cost (§5–§7).** A subsystem $x$ moving between parts of a partition: gain $\eta=I(x:F|U)$ as exponent in $\exp(ka\eta)$ (D5.5 -> D6.10 -> D7.14b); cost $\eta^{1/8}$ in energy (D5.15 -> D6.12 -> D7.14c). Both tested against the same states $\sigma_{h,u}$ (D7.27), uniformly in $\sigma$; this lets §9 choose one $p$ for all terms. Constants depend on $\dim x$ (resp. $d_h$) only, never on $\dim P,U,F$ (Lemma 2.1 usage rule D2.5).
8. **Input to the scanner: exponent bootstrap (D9.19).** Prop 9.2 (D9.9) and Prop 9.6 (D9.25) need $S_\Omega(X)\le C_en^{1+e}$, $S_\Omega(Q_j)\le C_e(nL^e+n)$, i.e. $F_{\rm box}(r)\le C_er^{1+e}$ with $e<1$ and in fact $e\le e_*$ for the sharp margins. Start: $e_0\in(0,1)$ from Prop 3.3. **Iterated:** $e\mapsto(1-\ell)e$ (D9.24): given $F_{\rm box}\le C_er^{1+e}$, Lemma 9.4 bounds core/shell entropies ($S(X)\le Cns_0^e$, $S(Q_j)\le CnL^e$), Prop 9.2 gives small $E_{\rm def}$, rough comparisons give $S_X\le C(nL^e+nD+w+h(\tau)/a+1)=O(n^{1+(1-\ell)e})$ because $L=n^{1-\ell}<s_0\asymp n$ (D9.23). Number of steps depends only on $e_0,\ell$ with $\ell=g_0/10^5$, $g_0=(1-e_0)/2$; ends at $e_*=2\cdot10^{-6}$. All scales ($\mu=1-g_0,\nu=g_0/1000,\kappa=\min(\nu/100,e_*/4),W=4$) depend on $e_0$ only (D9.20).
9. **Initial exponent (D3.16).** Recursion on box size: $F_{\rm box}(Mr)\le\lambda F_{\rm box}(r)+CM^2r$, $\lambda=(1-p_0/4)M^2<M^2$, $p_0=(2C_{\rm pad}+5)^{-2}$, $M\ge\max\{2,16(C_{\rm pad}+2)\}$ (D3.16.5). Each child of a random order gains $\tfrac12S(X_i)$ with probability $\ge p_0$ (D3.4: $S(X|T)\le\tfrac12S(X)+C_{\rm buf}r$) except $O(M)$ noninterior ones. $1+e_0=\log_M\lambda$. Lemma 3.2 itself: nested filters $L_j$ on $X_j=A\cap Q_0^{+r+jD}$, harmonic weights $a_j\propto1/(r+d_j)$, $\sum a_j=2$ (factor $\tfrac12$), lower bound on $-2\log N$ from D3.1 and gap, upper bound by Schmidt pinning (D3.12–D3.13), SSA (D3.14).
10. **Positive constraints (D4.6, D4.11).** Gap of full $H$ is converted into positive $k_i$ with $k_i\Omega=0$ and stretched-exponential tails (filter $f$ with $\hat f$ supported in $[-\Delta/2,\Delta/2]$, Gevrey bump D4.5, Lieb–Robinson D4.4, absolute value D4.6). For the scanner the system is truncated near $S_0$ (variable radius $r_i$, volume-free error $n^{-1000}$ summed over $\le3\mu_R|S_0|(d+1)^2$ labels at distance $d$; D4.12), keeping gap $\ge g/2$ and $\mathcal B_X\le CnD(\log n)^{12}$ (D4.14), so Lemma 3.1 (D3.1) applies with $\mathcal B$ nearly linear in perimeter.
11. **Order of choice of constants** (any formalization must fix in this order): $q,R,J,\Delta$ -> $D_0$ ($>2R+10$), $C_{\rm tpl}$ -> $C_{\rm pad}$ -> $M$, $p_0$, $e_0$ (D3.16) -> $p\ge10^6$, $c_*,g$ (D10.1) -> exponents $\varepsilon,\beta,\delta_0,\zeta,\rho_0,\ell$ (D10.1, D11.2) -> $C_0$ -> $C_1$ of D4.11 (depends on $C_0,g$) -> $n_*$ (D11.26.2: large enough for Prop 9.6, Prop 10.2 at $M=100$, $L+2r<n^\beta$) -> $S_*,k_0$ of D11.24 -> $C$ of Prop 11.2 (depends on $n_*$). Then, inside each application, $k\to\infty$ strictly after the finite system, schedule, $n$, $a$, $\tau$ are fixed (D6 conventions; D8.8 quantifiers).

---

## 3. Notation

Paper symbol | meaning | section introduced. Same letter, different object is flagged `[clash]`.

| Symbol | Meaning | § |
|---|---|---|
| $\Lambda$, $d_\Lambda$ | finite induced domain, graph distance ($\infty$ across components) | 1 |
| $q,R,J,\Delta$ | local dim., support diameter bound in $d_\Lambda$, term norm bound, global gap | 1 |
| $H=\sum_Xh_X$, $\Omega$, $E_0$, $P_\Omega$ | admissible Hamiltonian, unique ground vector, ground energy, $|\Omega\rangle\langle\Omega|$ | 1 |
| $\partial_\Lambda A$, $\partial_{\rm in}A$, $Z=Z_A$ | edge boundary, inner boundary, endpoints of cut edges | 1 |
| $b$ | $|\partial_\Lambda A|$ (§11 proof); $b_X=|\partial_\Lambda X|$ (§4); $b'$ (§3) | 1, 3, 4 |
| $S_\Omega(A)$, $I_\Omega(B{:}C)$ | entropy, mutual information of $\Omega$ | 1 |
| $S(D|E)$, $I(D{:}F|E)$ | conditional entropy, conditional MI | 2 |
| $h(u)$, $\delta$ | binary entropy, trace distance $\tfrac12\|\rho-\sigma\|_1$ | 2 |
| $B_\Lambda(x,r)$, $N_r^\Lambda(D)$ ($=N_r$) | graph ball, graph neighbourhood | 2 |
| $T_j$, $Q^{+d}$ | ambient dilation $T+[-j,j]^2\cap\mathbb Z^2$ | 2, 3 |
| $v_r$, $\mu_R$, $b_0$ | $1+2r(r+1)$; $2^{v_R-1}$; $J\mu_R$ | 2, 4 |
| anchor $a_i$, support $X_i$ | anchor of term $i$; $X_i\subseteq N_R(a_i)$ | 2, 4 |
| $C,c$ | generic constants, depend on $q,R,J,\Delta$ only | 2 |
| $K$ `[clash]` | surprisal r.v. (§3 L3.1); $L_m\cdots L_1$ (§3 L3.2); number of bands (§7–§9); error exponent $K\ge4(M+3)$ (§10); $k_i$-roots $K_i=k_i^{1/2}$ (§4) | 3, 4, 7, 9, 10 |
| $\mathcal B$, $\vartheta=c_0/g_0$ | crossing-term budget $1+\sum\log^2(ed_i)$; norm/gap ratio | 3 |
| $d_i$ `[clash]` | $\prod\dim\mathcal H_v$ over support (§3, §4: $q^{|\widetilde X_i|}$); $d_i^0=d_\Lambda(a_i,S_0)$ (§4); $d_j=r+jD$ (§3) | 3, 4 |
| safe rectangle, $\operatorname{size}(Q)$, $D_0$ | $\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q)$, $D_0>2R+10$ | 3 |
| $D$ `[clash]` | integer margin $>2R+2$ (§3); designated support (§3 L3.1); charge lookahead $\lceil n^\kappa\rceil$ (§9); exceptional set $D\subseteq A$ (§1, §11) | 3, 9, 11 |
| $C_{\rm pad},C_{\rm buf}$ | padding / buffer-error constants of L3.2 | 3 |
| $a_j$, $Z_r$, $\mathcal E$ | harmonic weights $\tfrac2{Z_r(r+d_j)}$, $\sum a_j=2$; $\mathcal E=4/Z_r$ | 3 |
| $F_{\rm box}(r)$ | $\sup S_\Omega(A\cap Q)$ over safe $Q$ of size $\le r$ | 3 |
| $e_0$, $e_*$, $e$ | box exponents: $F_{\rm box}\le Cr^{1+e}$; $e_0\in(0,1)$ (§3), $e_*=2\cdot10^{-6}$ (§9) | 3, 9 |
| $M$ `[clash]` | integer scale ratio (§3 P3.3); $M(u)=\mathbb Ee^{uK}$ (§3); exponent in $n^{-M}$ (§10, $=100$ in §11) | 3, 10 |
| $\tau_t$, $E_{i,l}$ | $e^{itH}\cdot e^{-itH}$; normalized partial trace onto $N_l(a_i)$ | 4 |
| $\chi,f$, $p,\alpha=\tfrac p{p+1}$ | Gevrey bump, its Fourier transform; stretched exponent | 4 |
| $M_i$, $k_i$, $c_*$, $g=\Delta/c_*$, $H_F$ | centered filtered terms; positive constraints; gap of $H_F$ | 4 |
| $G_i,K_i,\mathcal E_i$ | $(I-k_i)^{1/2},k_i^{1/2}$, unital CP channel | 4 |
| $r_0,r_i,\widetilde H,\widetilde\Omega,\widetilde E_0,\widetilde g,\widetilde X_i$ | truncation data of P4.5 | 4 |
| $\epsilon_n$, $\mathcal C_X$, $C_0$, $C_1$ `[clash]` | $\min\{n^{-1000},g/4\}$; crossing labels; $|S_0|\le C_0n^2$; $r_0=\lceil C_1(\log n)^2\rceil$ ($C_1$ also in L4.2, §3) | 4 |
| $\rho^{[z]}$, $\widehat\rho$, $\|\cdot\|_p$ | spectral power zero on kernel; $\rho+\Pi_{\ker\rho}$ | 5 |
| $\theta$ on $P,x,U,F$; $\eta$ | pure state; $\eta=S(x|P)+S(x|U)=I(x{:}F|U)=I(x{:}F|P)$ | 5 |
| $\ell$ `[clash]` | $\log(e\dim x)$ (§5, §7); $\ell_h=\log(ed_h)$ (§5); exponent $L=n^{1-\ell}$ (§9, $=10^{-5}$ in P9.6, §11) | 5, 7, 9, 11 |
| $a$ `[clash]` | exponent in $\sigma^{a/2}$ (§5); $a=2t$ (§6–§8); $a=W/K$ (§9); $a_j$ harmonic weights (§3); $a_0$ isolation const. (§11) | 3, 5, 6, 9, 11 |
| $\mathcal R_\eta$ | $\sqrt y+\sqrt{\eta\log(ed/y)}$, $y=\min(1,\eta)$ | 5 |
| $\mathcal V$, $\mathcal S_k=\operatorname{Sym}^k\mathcal V$, $d=\dim\mathcal V$ | one-copy space, symmetric $k$-copy space | 6 |
| $\lambda\vdash k$, $d_\lambda$, $\pi^\lambda_{Q,k}$, $F_{Q,k}$ | Schur label, $S_k$-irrep dimension, label projector, $\sum_\lambda\log d_\lambda\pi^\lambda$ | 6 |
| $t$, $w_k$, $W_{Q,k}$ | $0<t<\tfrac14$; label function; $W_{Q,k}\asymp e^{-tF_{Q,k}}$ | 6 |
| $A_k(P,Y,F)$ | $(W_P^{-1}W_F^{-1}W_Y)^2$, $\log A_k=a(F_P+F_F-F_Y)+O(\log k)$ | 6 |
| $C_{x,k}$, $\mu_\sigma$, $f_\theta$ | metric ratio; coherent measure; symbol | 6 |
| $\poly(k)$, $o_k(1)$ | polynomial in $k$; $\to0$ uniformly in $\sigma$ | 6 |
| $A\#_pB$, $\mathcal M(p)$ | weighted geometric mean; interpolated root | 7 |
| $m_s,g_s,q_\pm$, $s=\tfrac14$ | Fourier densities; $\int m_s=2s$ | 7 |
| $N(p),v(p)$, $\sigma_{j,u}$, $\Phi_j$ | $\|\mathcal M^{-s}\mathrm{pre}\|$; normalized vector; derivative states; CP maps | 7 |
| $\mathrm{pre}_k$, $\mathrm{post}_k$, $\lambda_k$, $E_{\rm def}$ | filtered input vector, Bell-pinned vector, label, energy defect | 8 |
| $C,R$, $d_*=|E|$, $z$, $w$ | auxiliary Bell pair, typical Schmidt set size/mass/width | 8 |
| $X,U,Y,V$ | four-part partition of the physical system ($P=CXU$, $F=RV$) | 8 |
| $g^{\rm pre},g^{\rm post}$, $\langle\cdot\rangle_{\rm av}$ | entropy combinations; leaf/band average | 8 |
| $n,L,m,K,D,W,a,\kappa,\mu,\nu,\omega$ | scanner scales (D9.2) | 9 |
| $\epsilon=n^{-\nu}$ `[clash]` | window for $p_k$ (§9); $\varepsilon=10^{-5}$ collar exponent (§9 P9.6, §10); $\varepsilon_i$ MI errors (§11); $\varepsilon$ time cutoff (§4 D4.8) | 9, 10, 11 |
| template $(n,s_0)$, $N_0$, $C_{\rm tpl}$ | union of $\le N_0$ convex pieces, $\operatorname{diam}_\infty\le n$, $n\ge C_{\rm tpl}N_0(s_0+1)$ | 9 |
| $X=A\cap T$, $S_0=A\cap T_L$, $Y=S_0\setminus X$ | target, collar set | 9, 10 |
| $\beta,\alpha$ | $1-2\cdot10^{-6}$; $\tfrac p{p+1}>1-10^{-6}$ | 10 |
| $R_0,B_0,M_0$, $t_*$, $r$, $w$ | restoring operator, column operator, norm bound $e^{(\mathcal I+3w)/2}$, clock time, radius | 10 |
| $\mathcal I$ | $I_\Omega(X:\Lambda\setminus S_0)$ | 10 |
| $\delta_0,\zeta,\rho_0,\ell$ | geometry exponents | 11 |
| $s_k,t_k,d(S)$, $f_i\in\{0,1\}$ | pitch, strip width, repair half-side; family label | 11 |
| $n_*$ | threshold in proof of Thm 1.1 | 11 |
| $A$, $B$ `[clash]` | cut region (§1); bipartition part (§3 L3.1); $B=\Lambda\setminus A$ (§11); $\mathcal B$ budget | 1, 3, 11 |
| $Z$ `[clash]` | $Z_A$ endpoints; $Z_r$ harmonic sum (§3); typical-mass $z$ (§8) | 1, 3 |
| $N$ `[clash]` | $N_r$ neighbourhood (§2); $N$ filter norm (§3, §7); $N_i,N_0$ product-term / piece counts | 2, 3, 7, 9 |

---

## 4. Constants and scales

Order of fixing top to bottom. "(U)" = universal numeric; "(Ham)" = depends on $q,R,J,\Delta$ only.

| Quantity | Value | Where fixed | Role |
|---|---|---|---|
| $v_r,\mu_R$ | $1+2r(r+1)$; $2^{v_R-1}$ | §2 D2.7, D2.8 | ball size; terms per site; split terms $\le2v_R\mu_R|\partial_\Lambda D|$ (D2.9) |
| $D_0$ | integer $>2R+10$ | §3 D3.3 | safety factor of boxes and templates |
| $D$ | integer $>2R+2$ | §3 D3.4 | margin between nested regions |
| $C_{\rm pad}$ (Ham) | integer, large; chosen after all $C_{\rm pad}$-independent constants | §3 D3.6, D3.10 | padding of L3.2 |
| $M$ | $\ge\max\{2,16(C_{\rm pad}+2)\}$ | §3 D3.16.5 | scale ratio in box recursion |
| $p_0$, $\lambda$ | $(2C_{\rm pad}+5)^{-2}$; $(1-p_0/4)M^2$ | §3 D3.16 | recursion coefficient |
| $e_0$ (Ham) | $1+\log(1-p_0/4)/\log M\in(0,1)$ | §3 D3.16.7 | initial exponent |
| $1000$ | exponent in $\epsilon_n=\min\{n^{-1000},g/4\}$ | §4 D4.11 | truncation error (any fixed value after enlarging $C_1$) |
| $r_0$ | $\lceil C_1(\log n)^2\rceil$, $C_1=C_1(q,R,J,\Delta,C_0)$ | §4 D4.11 | truncation radius near $S_0$ |
| $\mathcal B_X$ | $\le CnD(\log n)^{12}$ if $b_X\le C_2nD$ | §4 D4.14 | tail parameter of L3.1 for $\widetilde H$ |
| $\widetilde g$, $\widetilde E_0$ | $\ge g/2$, $\le n^{-1000}$ | §4 D4.13 | gap/energy of $\widetilde H$ |
| L3.1 parameters | $u$-range $[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}$, constants $512e,128e,256e$ | §3 D3.1 | tail width $\sqrt{\mathcal B}$ |
| $t<\tfrac14$, $a=2t$, $s=\tfrac14$ | metric exponent, weight, mean-tree power | §6, §7 | $sW=\tfrac14W$; $sW=1$ at $W=4$ |
| gain exponent | $ka[\eta-Ca^{1/4}\log^C]$ | §6 D6.10 | entropy gain per move |
| cost exponent | $\eta^{1/8}$, prefactor $Ca^2\ell_h^4$ | §5 D5.15, §6 D6.12 | energy cost per move |
| $w=n^{3/5}$, $z\ge1-n^{-100}$ | typical Schmidt window and mass (L3.1 with $M=100$) | §8 D8.2, §9 D9.9, §10 D10.5 | typical sets |
| scanner scales (P9.5) | $g_0=\tfrac{1-e_0}2$, $\mu=1-g_0$, $\nu=\tfrac{g_0}{1000}$, $\ell=\tfrac{g_0}{10^5}$, $\kappa=\min(\tfrac\nu{100},\tfrac{e_*}4)$, $W=4$ | §9 D9.20 | exponent improvement $e\mapsto(1-\ell)e$ |
| $e_*$ | $2\cdot10^{-6}$ | §9 D9.19 | final box exponent |
| scanner scales (P9.6) | $\mu=\tfrac14$, $\nu=\tfrac1{1000}$, $\ell=10^{-5}$, $\omega=\tfrac1{20000}$, $\kappa=10^{-6}$, $W=n^\omega$ | §9 D9.26 | collar bound |
| derived (P9.6) | $K\asymp n^{0.74999}$, $a\asymp n^{-0.74994}$, $\delta_n\le n^{-0.18}$, $E_{\rm def}\le Cn^{-0.0005}$, $a\sqrt{\mathcal B}\le Cn^{-0.2499395}(\log n)^C$ | §9 D9.26 | margins |
| collar exponent $\varepsilon$ | $10^{-5}$; output $n^{1-\varepsilon}$; worst error $n^{0.999952}$ | §9 D9.25, D9.29 | sublinearity (margin $0.99999$ vs $0.999952$) |
| scale ordering | $r_0\ll D\ll m\ll L$ | §9 D9.3 | scan consistency |
| $\beta$ | $1-2\cdot10^{-6}$ | §10 D10.1 | $L+2r=o(n^\beta)$ |
| $p,\alpha$ | $p\ge10^6$ integer, $\alpha=\tfrac p{p+1}>1-10^{-6}$ | §10 D10.1 | stretched exponent of constraints |
| $g$ (Ham, depends on $p$) | $\Delta/c_*$ | §4 D4.6 | gap of $H_F$ |
| $K$ (§10) | $\ge4(M+3)$ | §10 D10.5, D10.15 | error $n^{-K}$ |
| $t_*$, $r$ | $C(\mathcal I+w+K\log n)$, $C\ge\max\{6/g,2\}$; $\lceil(C'(t_*+K\log n))^{1/\alpha}\rceil$ | §10 D10.11 | clock time, radius |
| $M=100$ | decay $n^{-100}$ | §11 D11.26.2 | summability against $\sum n_i^{-100}\le Cb$ |
| $\delta_0,\zeta,\rho_0,\ell$ | $2\cdot10^{-7}$; $1-\delta_0/2$; $\tfrac{1+\beta}2=1-10^{-6}$; $10^{-5}$ | §11 D11.2 | geometry; $(1+2\delta_0)\beta<\zeta<1$, $(1+2\delta_0)(1-\ell)<1$, $1-\ell<\beta<\rho_0<1$ |
| $s_k,t_k$ | $2^{\lfloor(1+\delta_0)k\rfloor}$, $2^{\lfloor\zeta k\rfloor}$ | §11 D11.8 | pitch / strip width |
| primary scale | $s_0=r=2^k$, $n=\lceil C_Pr^{1+2\delta_0}\rceil$ | §11 D11.21 | $L=o(r)$, $n^\beta=o(t_k)$ |
| belt / replacement scale | $n=\lceil C_Bu\rceil$, $s_0=u$ resp. $2u$ | §11 D11.22 | $L=o(u)$ |
| $d(S)$, $a_0$, $S_*$ | $2^{\lfloor\rho_0\log_2S\rfloor}$, $\le\tfrac{a_0}{1000}S$; absolute isolation const.; stopping scale | §11 D11.14, D11.24 | repair |
| $n_*$ | large for P9.6, P10.2 ($M=100$), $L+2r<n^\beta$ | §11 D11.26.2 | threshold; enters $C$ of P11.2 |
| Thm 1.1 constant | $C'=C_1\log q+\tfrac C2C_1$ ($S_\Omega(A)\le C'b$) | §1 D1.4.7 | final |

**Pitfall (global).** The margins between $10^{-5},2\cdot10^{-6},10^{-6},2\cdot10^{-7}$ are tight and interlocked ($\varepsilon$ vs $\beta$ vs $\alpha$ vs $\delta_0$). Any change of one exponent in a formalization needs re-checking D9.29, D10.16, D11.2, D11.21, D11.24.

---

## 5. Anchor index

Generated from `grep -n '^#### D'` of each digest file. Format: anchor, kind, paper number, name, `file:line`.


### §1 Introduction  (`01-introduction.md`)

- **D1.1** Def — Domain, graph distance, Hilbert space — `01-introduction.md:11`
- **D1.2** Def — Admissible Hamiltonian (eq:hamiltonian) — `01-introduction.md:27`
- **D1.3** Def — Edge boundary, reduced state, entanglement entropy — `01-introduction.md:47`
- **D1.4** Theorem 1.1 — Area law — `01-introduction.md:62`
- **D1.5** Step — Remarks after Theorem 1.1 — `01-introduction.md:98`
- **D1.6** Def — Inner boundary and endpoint set — `01-introduction.md:112`
- **D1.7** Corollary 1.2 — Rectangles and vertex boundaries — `01-introduction.md:126`
- **D1.8** Step — History and related work — `01-introduction.md:150`
- **D1.9** Def — PEPS and bond dimension — `01-introduction.md:169`
- **D1.10** Step — Tensor-network consequence (companion paper) — `01-introduction.md:181`
- **D1.11** Def — Mutual information — `01-introduction.md:199`
- **D1.12** Step — Reduction of $S_\Omega(A)$ to collar information — `01-introduction.md:212`
- **D1.13** Step — Ambient versus graph locality — `01-introduction.md:234`
- **D1.14** Step — Stage 1: a first exponent below volume — `01-introduction.md:248`
- **D1.15** Step — Stage 2: information and energy in one interpolation — `01-introduction.md:266`
- **D1.16** Step — Stage 3: compare norms and scan a collar — `01-introduction.md:281`
- **D1.17** Step — Stage 4: amplify the information bound — `01-introduction.md:299`
- **D1.18** Step — Stage 5: arrange regions for entropy cancellation — `01-introduction.md:315`

### §2 Entropy and induced-graph locality  (`02-preliminaries.md`)

- **D2.1** Def — Conditional entropy, mutual information, conditional mutual information — `02-preliminaries.md:11`
- **D2.2** Step — Entropy facts used without proof — `02-preliminaries.md:25`
- **D2.3** Def — Binary entropy and trace distance — `02-preliminaries.md:43`
- **D2.4** Lemma 2.1 — Continuity with a fixed controlled system — `02-preliminaries.md:54`
- **D2.5** Step — Pure-state trace distance; usage rule for Lemma 2.1 — `02-preliminaries.md:87`
- **D2.6** Def — Balls, graph neighborhoods, ambient dilations — `02-preliminaries.md:103`
- **D2.7** Step eq:ball-count — Ball cardinality — `02-preliminaries.md:115`
- **D2.8** Step — Term multiplicity and norm budget per site — `02-preliminaries.md:131`
- **D2.9** Step eq:crossing-count — Terms split by a set — `02-preliminaries.md:155`
- **D2.10** Step — Product decomposition across a bipartition — `02-preliminaries.md:174`
- **D2.11** Step — Degenerate cases — `02-preliminaries.md:190`
- **D2.12** Lemma 2.2 — A cut with no crossing edge — `02-preliminaries.md:206`
- **D2.13** Def — Convention for constants $C,c$ — `02-preliminaries.md:226`

### §3 Marginal tails and initial box estimate  (`03-initial-box.md`)

- **D3.1** Lemma 3.1 — Marginal moment and tail bounds — `03-initial-box.md:13`
- **D3.2** Step eq:initial-local-tail-parameter — Lattice specialization of Lemma 3.1 — `03-initial-box.md:56`
- **D3.3** Def — Safe rectangles, size, buffers, local entropy notation — `03-initial-box.md:77`
- **D3.4** Lemma 3.2 — Conditional entropy in a buffered rectangle — `03-initial-box.md:91`
- **D3.5** Step — Nested regions, locality, single split, contour budget (Lemma 3.2, part 1) — `03-initial-box.md:116`
- **D3.6** Step eq:initial-harmonic-weights — Harmonic weights — `03-initial-box.md:139`
- **D3.7** Step eq:initial-filter-commutation — Optimized filters commute with their marginals — `03-initial-box.md:158`
- **D3.8** Step eq:initial-filter-clipping — Clipping bounds log-ratios of filter eigenvalues — `03-initial-box.md:179`
- **D3.9** Step eq:initial-product-energy — The optimized vector has small excitation energy — `03-initial-box.md:197`
- **D3.10** Step eq:initial-weight-range — Final choice of $C_{\rm pad}$ — `03-initial-box.md:223`
- **D3.11** Step eq:initial-norm-lower — First norm comparison (lower bound on $-2\log N$) — `03-initial-box.md:242`
- **D3.12** Step eq:initial-trial-norm — Zero-floor limit and the trial-norm bound — `03-initial-box.md:266`
- **D3.13** Step eq:initial-norm-upper — Schmidt-averaged upper bound on $-2\log N$ — `03-initial-box.md:289`
- **D3.14** Step — Conclusion of Lemma 3.2 — `03-initial-box.md:306`
- **D3.15** Def — $F_{\rm box}(r)$ — `03-initial-box.md:326`
- **D3.16** Proposition 3.3 — Initial safe-box estimate — `03-initial-box.md:341`
- **D3.17** Step — Remarks closing §3 — `03-initial-box.md:370`

### §4 Positive constraints and truncation  (`04-quasilocal.md`)

- **D4.1** Def — Anchored decomposition and graph balls — `04-quasilocal.md:15`
- **D4.2** Def — Conditional expectation onto a ball, $E_{i,l}$ — `04-quasilocal.md:26`
- **D4.3** Step — Counting budget — `04-quasilocal.md:39`
- **D4.4** Lemma 4.1 — Graph-distance propagation — `04-quasilocal.md:61`
- **D4.5** Lemma 4.2 — A compactly supported spectral filter — `04-quasilocal.md:94`
- **D4.6** Proposition 4.3 — Positive replacement of the Hamiltonian — `04-quasilocal.md:128`
- **D4.7** Step — Centered filtered terms $M_i$ — `04-quasilocal.md:156`
- **D4.8** Step — Locality of $M_i$ — `04-quasilocal.md:177`
- **D4.9** Step — Operator Hölder-$\tfrac12$ inequality — `04-quasilocal.md:197`
- **D4.10** Lemma 4.4 — Square roots and local channels — `04-quasilocal.md:217`
- **D4.11** Proposition 4.5 — Truncation near a finite set — `04-quasilocal.md:247`
- **D4.12** Step — Volume-free summation of the truncation error — `04-quasilocal.md:275`
- **D4.13** Step — Ground energy, gap and ground vector of $\widetilde H$ — `04-quasilocal.md:299`
- **D4.14** Step — Crossing supports and the cut budget — `04-quasilocal.md:318`
- **D4.15** Step — Remarks on the application and degenerate cases — `04-quasilocal.md:342`

### §5 Two conditional operator estimates  (`05-conditional.md`)

- **D5.1** Def — Spectral powers, hat, norms — `05-conditional.md:13`
- **D5.2** Step eq:conditional-log-moments — Three moments of $L$ — `05-conditional.md:35`
- **D5.3** Step eq:conditional-log-mgf — Log-moment generating function — `05-conditional.md:59`
- **D5.4** Step eq:conditional-schatten — Conditional Schatten estimate — `05-conditional.md:82`
- **D5.5** Lemma 5.1 — Conditional movement estimate — `05-conditional.md:110`
- **D5.6** Step eq:conditional-slack, eq:conditional-overlap — Left boundary and slack — `05-conditional.md:152`
- **D5.7** Step eq:conditional-hellinger — $\rho$ and $\xi$ are Hellinger-close — `05-conditional.md:175`
- **D5.8** Step eq:conditional-phase-hellinger — Phases are Hellinger-continuous — `05-conditional.md:195`
- **D5.9** Step eq:conditional-state-movement — The state arriving at the right boundary — `05-conditional.md:217`
- **D5.10** Step — Right boundary — `05-conditional.md:246`
- **D5.11** Step — Log-interpolation with harmonic measure — `05-conditional.md:268`
- **D5.12** Lemma 5.2 — Marginal-phase comparison — `05-conditional.md:293`
- **D5.13** Step eq:conditional-resolvent-square, eq:conditional-resolvent-entropy — Resolvent defect and its integral — `05-conditional.md:332`
- **D5.14** Step eq:conditional-resolvent-tail — Resolvent defect bounds — `05-conditional.md:353`
- **D5.15** Lemma 5.3 — Conditional skew estimate — `05-conditional.md:375`
- **D5.16** Step eq:conditional-narrow-strip — Bound on a strip of width $c_0/\ell_h$ — `05-conditional.md:401`
- **D5.17** Step eq:conditional-phase-discrepancy — From $f(iu)$ to phase products — `05-conditional.md:422`
- **D5.18** Step eq:conditional-first-derivative — Imaginary-axis skew and $f'(0)$ — `05-conditional.md:443`
- **D5.19** Step — Gaussian-weighted three-lines and second-order remainder — `05-conditional.md:460`
- **D5.20** Step — Parameter bookkeeping: $\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}$ — `05-conditional.md:482`
- **D5.21** Step — Closing remark — `05-conditional.md:500`

### §6 Symmetric replicas and entropy metrics  (`06-replicas.md`)

- **D6.1** Def — Systems, symmetric subspaces, subsystems — `06-replicas.md:15`
- **D6.2** Step eq:schur-decomposition — Schur–Weyl decomposition and Weyl character — `06-replicas.md:26`
- **D6.3** Def eq:F-definition — Label projectors and the label observable $F_{Q,k}$ — `06-replicas.md:39`
- **D6.4** Lemma 6.1 — Schur-label estimates — `06-replicas.md:52`
- **D6.5** Def eq:w-definition — The label function $w_k$ and $W_{Q,k}$ — `06-replicas.md:110`
- **D6.6** Lemma 6.2 — Integral formula and marked ratios — `06-replicas.md:125`
- **D6.7** Step eq:fixed-factor — Fixed pure factor restriction identity — `06-replicas.md:164`
- **D6.8** Def eq:leaf-metric — The partition metric $A_k(P,Y,F)$ — `06-replicas.md:183`
- **D6.9** Step eq:leaf-floor — Floor of the leaf metric and commutation with copy averages — `06-replicas.md:196`
- **D6.10** Lemma 6.3 — Relative coherent pin — `06-replicas.md:218`
- **D6.11** Def eq:resolution, eq:husimi — Coherent probability measure — `06-replicas.md:251`
- **D6.12** Lemma 6.4 — Marked-copy scalar symbols — `06-replicas.md:266`
- **D6.13** Step — Bounded approximation on symmetric inputs — `06-replicas.md:297`
- **D6.14** Step eq:finite-husimi, eq:uniform-husimi — Coherent measure on a fixed number of copies — `06-replicas.md:320`
- **D6.15** Step eq:injection-product — Products after compression — `06-replicas.md:340`
- **D6.16** Step — Removing clipping; absolute values; closing the lemma — `06-replicas.md:364`
- **D6.17** Step — Closing remark: gain and cost on the same states — `06-replicas.md:385`

### §7 Transport through finite trees of metrics  (`07-transport.md`)

- **D7.1** Def — Weighted geometric mean (`transport:mean-def`) — `07-transport.md:15`
- **D7.2** Def — Weighted binary tree and its root — `07-transport.md:28`
- **D7.3** Lemma 7.1 — Properties of a finite mean tree — `07-transport.md:39`
- **D7.4** Def — Completely positive and unital maps — `07-transport.md:71`
- **D7.5** Lemma 7.2 — Normalized derivative maps — `07-transport.md:82`
- **D7.6** Def — The multipliers $g_s$ and $m_s$ (`transport:fourier-density`) — `07-transport.md:113`
- **D7.7** Lemma 7.3 — The two Fourier multipliers — `07-transport.md:125`
- **D7.8** Def — Band metric and finiteness conventions (`transport:band-metric`) — `07-transport.md:156`
- **D7.9** Def — A round: history tree, choice trees, interpolated root $\mathcal M(p)$ — `07-transport.md:169`
- **D7.10** Def — Entropy of a move, scale $\ell$, smallness (`transport:move-eta`) — `07-transport.md:188`
- **D7.11** Def — Energy terms, designated supports, splits — `07-transport.md:201`
- **D7.12** Step — Replica energy and commutation at unsplit leaves (`transport:replica-energy`) — `07-transport.md:212`
- **D7.13** Def — Coherent vectors and measures (`transport:coherent-measure`) — `07-transport.md:229`
- **D7.14** Proposition 7.4 — Entropy and energy transport — `07-transport.md:246`
- **D7.15** Step — Derivative at an interpolating vertex — `07-transport.md:273`
- **D7.16** Step — Exact formula for $-\partial_p\log N^2$ (part (a)) — `07-transport.md:295`
- **D7.17** Step — Factorization of the relative metric over bands (`transport:relative-factorization`) — `07-transport.md:317`
- **D7.18** Step — Conditional pin (`transport:conditional-pin`) — `07-transport.md:335`
- **D7.19** Step — Operator Jensen for coherent integrals (`transport:log-jensen`) — `07-transport.md:352`
- **D7.20** Step — Entropy gain (part (b), `transport:log-relative`, `transport:entropy-gain`) — `07-transport.md:372`
- **D7.21** Step — Auxiliary positive metric for each energy term — `07-transport.md:393`
- **D7.22** Step — Transport of the commutator through the tree (`transport:block-rotation`) — `07-transport.md:418`
- **D7.23** Step — Bound on $E_{i,\pm}$ (`transport:E-def`, `transport:cp-schwarz`, `transport:block-bound`) — `07-transport.md:439`
- **D7.24** Step — Symbol cost of a split (`transport:symbol-cost`) — `07-transport.md:464`
- **D7.25** Step — Assembly of the energy bound (part (c), `transport:energy-similarity`) — `07-transport.md:483`
- **D7.26** Step — Endpoints, uniformity, finite sequences of rounds — `07-transport.md:504`
- **D7.27** Step — The shared-state remark — `07-transport.md:520`

### §8 Norm comparisons from an auxiliary pair  (`08-comparators.md`)

- **D8.1** Def — Physical data, statuses, nesting — `08-comparators.md:15`
- **D8.2** Def — Typical Schmidt set — `08-comparators.md:32`
- **D8.3** Step — Typical entropies — `08-comparators.md:45`
- **D8.4** Def — Prefix data (rough upper bound only) — `08-comparators.md:61`
- **D8.5** Def — Marginal moment data (sharp bounds only) — `08-comparators.md:74`
- **D8.6** Def — Auxiliary pair, common-dimension metrics, leaf metrics — `08-comparators.md:87`
- **D8.7** Def — Mean tree on bands and the average $\langle\cdot\rangle_{\rm av}$ — `08-comparators.md:103`
- **D8.8** Proposition 8.1 — Upper and lower norm comparisons — `08-comparators.md:120`
- **D8.9** Step — Label remainder — `08-comparators.md:166`
- **D8.10** Step — Signed label moments — `08-comparators.md:178`
- **D8.11** Def — Schmidt vectors, $\psi$, $B_{XC}$, $\mathrm{post}_k$, pin projection — `08-comparators.md:196`
- **D8.12** Step — High label $\lambda_k$ — `08-comparators.md:209`
- **D8.13** Step — $\mathrm{pre}_k$ is a nonzero symmetric mean-energy eigenvector with preserved labels — `08-comparators.md:227`
- **D8.14** Step — Bell pin — `08-comparators.md:244`
- **D8.15** Step — Pin norm — `08-comparators.md:260`
- **D8.16** Step — Pinned metric — `08-comparators.md:277`
- **D8.17** Step — Post marginals — `08-comparators.md:300`
- **D8.18** Step — Rough overlap — `08-comparators.md:318`
- **D8.19** Step — Actual cutoffs — `08-comparators.md:336`
- **D8.20** Step — Proof of the rough upper bound — `08-comparators.md:354`
- **D8.21** Step — Sharp Jensen bound on band logarithms — `08-comparators.md:373`
- **D8.22** Step — Leaf expectation and proof of the sharp upper bound — `08-comparators.md:393`
- **D8.23** Step — Defect mass — `08-comparators.md:419`
- **D8.24** Step — Defect components — `08-comparators.md:437`
- **D8.25** Step — Restriction dimensions — `08-comparators.md:452`
- **D8.26** Step — Whole inverse metric — `08-comparators.md:469`
- **D8.27** Step — Good auxiliary labels — `08-comparators.md:487`
- **D8.28** Step — Merge deficits and decomposition — `08-comparators.md:505`
- **D8.29** Step — Merge moments — `08-comparators.md:526`
- **D8.30** Step — Component inverse — `08-comparators.md:545`
- **D8.31** Step — Inverse compression and lower pin — `08-comparators.md:568`
- **D8.32** Step — Floor and block lower bound — `08-comparators.md:592`
- **D8.33** Step — Tree bound for $\mathcal M_g$ — `08-comparators.md:606`
- **D8.34** Step — Log lower bound for the tree — `08-comparators.md:627`
- **D8.35** Step — Proof of the two lower bounds — `08-comparators.md:646`
- **D8.36** Step — Entropy identity — `08-comparators.md:663`
- **D8.37** Step — Uniformity of the errors — `08-comparators.md:679`

### §9 Scanning collars, improving the entropy bound  (`09-scanner.md`)

- **D9.1** Def — Conventions: depth and metrics — `09-scanner.md:15`
- **D9.2** Def — Target, collar, and scales — `09-scanner.md:26`
- **D9.3** Step — Test geometry and the truncated system — `09-scanner.md:41`
- **D9.4** Def — Bands, offsets, initial partitions — `09-scanner.md:56`
- **D9.5** Def — Fill and charge rounds — `09-scanner.md:69`
- **D9.6** Def — Charge rounds — `09-scanner.md:85`
- **D9.7** Def — History tree, root metric, replica vector — `09-scanner.md:98`
- **D9.8** Lemma 9.1 — Geometry and probabilities of the scan — `09-scanner.md:113`
- **D9.9** Proposition 9.2 — The scanner estimate — `09-scanner.md:165`
- **D9.10** Def — Entropy cost $\mathcal Q(p)$ of the old splits — `09-scanner.md:188`
- **D9.11** Step — Entropy production per round — `09-scanner.md:203`
- **D9.12** Step — Integration over rounds and selection of $(\text{round},p_k)$ — `09-scanner.md:225`
- **D9.13** Step — Energy at the selected point — `09-scanner.md:251`
- **D9.14** Definition 9.3 — A template — `09-scanner.md:278`
- **D9.15** Lemma 9.4 — Rows, coverings, and shell entropy — `09-scanner.md:293`
- **D9.16** Step — One piece: row intervals and dilations — `09-scanner.md:312`
- **D9.17** Step — Mixed squares — `09-scanner.md:330`
- **D9.18** Step — Covering and shell entropy — `09-scanner.md:346`
- **D9.19** Proposition 9.5 — Improved safe-box estimate — `09-scanner.md:369`
- **D9.20** Step — Bootstrap parameters — `09-scanner.md:385`
- **D9.21** Step — Hypotheses of Prop 9.2 for a safe rectangle — `09-scanner.md:399`
- **D9.22** Step — Quantitative output of Prop 9.2 — `09-scanner.md:415`
- **D9.23** Step — Rough comparisons give $S_X\le C_e(nL^e+nD+w+h(\tau)/a+1)$ — `09-scanner.md:432`
- **D9.24** Step — Exponent improvement and iteration — `09-scanner.md:452`
- **D9.25** Proposition 9.6 — A sublinear collar bound — `09-scanner.md:474`
- **D9.26** Step — Hypotheses, parameters and defect energy — `09-scanner.md:493`
- **D9.27** Step — Difference of the sharp comparisons — `09-scanner.md:516`
- **D9.28** Step — Purity identity and monotonicity — `09-scanner.md:538`
- **D9.29** Step — Error table and conclusion for $\widetilde\Omega$ — `09-scanner.md:553`
- **D9.30** Step — Transfer back to $\Omega$ and size/boundary claims — `09-scanner.md:579`

### §10 Amplifying the collar estimate  (`10-amplification.md`)

- **D10.1** Def — Standing exponents and the fresh positive system — `10-amplification.md:15`
- **D10.2** Lemma 10.1 — Local constraint products — `10-amplification.md:36`
- **D10.3** Step — Excited-state decay $\mathbb E\|D(I-P_\Omega)\zeta\|^2\le e^{-gt}\|(I-P_\Omega)\zeta\|^2$ — `10-amplification.md:103`
- **D10.4** Proposition 10.2 — Amplification — `10-amplification.md:126`
- **D10.5** Step — Typical projections — `10-amplification.md:161`
- **D10.6** Def — The vectors $\phi$, $\eta$ and the relabeling isometry $\mathcal R_X$ — `10-amplification.md:182`
- **D10.7** Def — Restoring operator $R_0$ and column operator $B_0$ — `10-amplification.md:201`
- **D10.8** Step — Norm bound $\|R_0\|,\|B_0\|\le M_0=e^{(\mathcal I+3w)/2}$ — `10-amplification.md:222`
- **D10.9** Step — Adjoint identity and adjoint error (no factor $M_0$) — `10-amplification.md:244`
- **D10.10** Step — Ground component of $R_0\phi$ is at most 1 — `10-amplification.md:264`
- **D10.11** Def — Clock time $t_*$ and radius $r$ — `10-amplification.md:283`
- **D10.12** Step — Good trajectory — `10-amplification.md:306`
- **D10.13** Step — Estimates before polar decomposition; direct error — `10-amplification.md:326`
- **D10.14** Step — Local unitary $U'$ via polar decomposition — `10-amplification.md:348`
- **D10.15** Step — Mutual information bound — `10-amplification.md:369`
- **D10.16** Step — Radius bounds and containment in $A$ — `10-amplification.md:391`
- **D10.17** Step — Closing remark — `10-amplification.md:409`

### §11 Two families of regions and the area bound  (`11-geometry.md`)

- **D11.1** Lemma 11.1 — Two-family entropy cancellation — `11-geometry.md:15`
- **D11.2** Def — Exponents $\delta_0,\zeta,\rho_0,\ell$ and their gaps (`geometry:exponents`, `geometry:exponent-gaps`) — `11-geometry.md:42`
- **D11.3** Def — Birth region, actual region, template of a tile — `11-geometry.md:61`
- **D11.4** Proposition 11.2 — Two families with separated birth templates — `11-geometry.md:72`
- **D11.5** Def — Origin and dyadic cells — `11-geometry.md:95`
- **D11.6** Step — Neighbourhoods $N_k$, dummy tile, layers $D_k$ (`geometry:layer-distance`) — `11-geometry.md:106`
- **D11.7** Step — Non-adjacent layers (`geometry:nonadjacent`) — `11-geometry.md:128`
- **D11.8** Def — Scales $s_k,t_k$, belt cells, pitch interiors, primary tiles — `11-geometry.md:143`
- **D11.9** Step — Few belt cells (`geometry:belt-count`) — `11-geometry.md:156`
- **D11.10** Step — Primary tiles: count, pieces, separation (`geometry:primary-pieces`) — `11-geometry.md:176`
- **D11.11** Step — Fans, labels and the point-contact property — `11-geometry.md:200`
- **D11.12** Def — Initial marks — `11-geometry.md:219`
- **D11.13** Lemma 11.3 — Isolated stars of the initial mesh (`geometry:initial-stars`) — `11-geometry.md:230`
- **D11.14** Def — Stopping scale, trim radius, repair rule (`geometry:trim-radius`, `geometry:trim-margins`) — `11-geometry.md:257`
- **D11.15** Lemma 11.4 — Uniform repair induction (`geometry:repair-induction`) — `11-geometry.md:280`
- **D11.16** Step — Edges avoid lattice sites — `11-geometry.md:302`
- **D11.17** Def — Order of tile identifiers — `11-geometry.md:322`
- **D11.18** Lemma 11.5 — Birth-template separation (`geometry:birth-separation`) — `11-geometry.md:333`
- **D11.19** Step — Repair counts (`geometry:descendant-count`, `geometry:total-repairs`) — `11-geometry.md:360`
- **D11.20** Step — Bounded exceptional set (`geometry:bad-sites`) — `11-geometry.md:378`
- **D11.21** Step — Scanner scales of primaries (`geometry:primary-scale`, `geometry:primary-limits`) — `11-geometry.md:394`
- **D11.22** Step — Scanner scales of belt tiles and replacements — `11-geometry.md:412`
- **D11.23** Step — Cut clearance of belt and replacement templates; hypotheses of Lemma 9.4 — `11-geometry.md:428`
- **D11.24** Step — Order of thresholds (`geometry:fine-clearance`) — `11-geometry.md:445`
- **D11.25** Step — Conclusion of Proposition 11.2 — `11-geometry.md:462`
- **D11.26** Theorem 1.1 — Proof of the area law — `11-geometry.md:483`

---

## 6. Standard vs new

**Textbook / literature (formalize via Mathlib or cite as axiom-level inputs).**

| Anchor | Fact | Reference |
|---|---|---|
| D2.2, D2.1 | strong subadditivity; chain rule; purity; $\lvert S(D\vert E)\rvert\le\log\dim D$ | Lieb–Ruskai, J. Math. Phys. 14 (1973) |
| D2.4 (L2.1) | dimension-free continuity of conditional entropy | Alicki–Fannes 2004; Winter, CMP 347 (2016), Thm 1, Lemma 2 |
| D2.5 | pure-state trace distance $\sqrt{1-\lvert\langle\xi,\eta\rangle\rvert^2}\le\|\xi-\eta\|$ | Nielsen–Chuang Ch. 9 |
| D2.7, D2.10, D2.11, D2.12 | lattice counting; matrix-unit expansion; tensor-sum ground space | elementary |
| D3.1 (three-lines step) | Hadamard three-lines, Cauchy coefficient bound, exponential Markov | textbook |
| D3.12 | vector three-lines | Tao, 247A Notes 1, Lemma 5.10 |
| D4.4 (L4.1) | Lieb–Robinson bound in graph metric | Lieb–Robinson 1972; Nachtergaele–Ogata–Sims 2006 |
| D4.5 (L4.2) | Gevrey bump, stretched-exponential Fourier decay | Hörmander I, §1.3 |
| D4.7 | centered filtered terms $M_i$, $M_i\Omega=0$ | Kitaev, Ann. Phys. 321 (2006), App. D.1.2 |
| D4.9 | $\|U^{1/2}-V^{1/2}\|\le\|U-V\|^{1/2}$ | Bhatia, Matrix Analysis Ch. X |
| D4.13 | Weyl/min–max, Davis–Kahan-type ground-vector bound | standard |
| D5.2 | two-eigenbasis log-ratio variable | Nussbaum–Szkoła 2009 |
| D5.4, D5.11 | Stein/Hirschman complex interpolation, Poisson kernel of strip | standard |
| D5.12–D5.14 | resolvent-compression identity; equality case of monotonicity | Carlen–Vershynina 2019; Petz 1986 |
| D6.2, D6.4 (1),(2),(4),(6) | Schur–Weyl, Weyl dimension, branching, Jucys–Murphy | Etingof et al.; Keyl–Werner 2001; Vershik–Okounkov 2005 |
| D6.6 (Gamma estimates) | Stirling, Laguerre simplex integrals | Muttalib–Borodin; Forrester–Ipsen 2018 |
| D6.14, D6.15 | finite de Finetti / coherent measure on $\operatorname{Sym}^k$ | standard |
| D7.3 items 1–4 | Kubo–Ando mean: congruence, monotonicity, homogeneity, Jensen | Kubo–Ando 1980 |
| D7.5 (formula) | Daleckii–Krein derivative of operator powers | standard |
| D7.7 item 1 | Fourier transform of $\sinh(sz)/\sinh(z/2)$ | Bhatia–Parthasarathy |
| D10.2 (mechanism) | dissipative Lieb–Robinson | Barthel–Kliesch, PRL 108 (2012) |
| D11.1 (ingredients) | chain rule, subadditivity, purity | as D2.2 |
| D11.18 (compactness step) | compactness + finite-pattern argument | standard |

**Specific to this paper (the mathematical content to be formalized from scratch).**

- §3: D3.1 (tilting $\rho^{-u/2}$ + analytic interpolation of crossing terms -> MGF/tail, $512e\,\vartheta\mathcal Bu^2$); D3.2; D3.4–D3.14 (nested positive filters with harmonic weights, optimizer commutes with marginal D3.7, clipping D3.8, $\cosh$ bound D3.9, prefix telescoping D3.11, Schmidt pinning D3.12); D3.16 (random-order chain-rule recursion).
- §4: D4.6 (absolute-value positive replacement with gap kept); D4.8; D4.10 (square-root channels); D4.11–D4.14 (variable-radius truncation with volume-free error).
- §5: D5.5 (word of four fractional powers: left boundary D5.6, Hellinger D5.7, phase continuity D5.8–D5.9, right boundary D5.10); D5.15 (Gaussian-weighted three-lines + D5.12).
- §6: D6.4 (3),(5) and polynomial moment bounds; D6.6 integral formula; D6.8–D6.9 leaf metric; D6.10 gain; D6.12 symbols.
- §7: D7.3 items 5, 6; D7.5 CP of normalized derivative along a mean tree; D7.7 item 2; D7.14 (a)(b)(c); shared states D7.27.
- §8: D8.8 whole (Bell pin, defect components, restriction dimensions, merge deficits, entropy identity D8.36).
- §9: D9.8 (scan geometry, split and charge probabilities); D9.9 (entropy production -> energy defect); D9.15 (entropy sum over rows/shells); D9.19 (bootstrap); D9.25 (collar bound).
- §10: D10.2 (expected-norm version with coupled clocks, spectators); D10.4 (typical restoring operator + clock suppression + polar unitary).
- §11: D11.1 two-family cancellation; D11.4 and all of D11.5–D11.25 (layers, belts, fans, repair induction, birth-template separation).
- §1/§2 bookkeeping: eq:hamiltonian convention (one summand per support), D2.8, D2.9, D1.13 (ambient vs graph locality).

**Not in the DAG.** D1.7 (Cor 1.2, leaf), D1.8 (history), D1.9–D1.10 (PEPS corollary of a companion paper), D1.14–D1.18 (outline; each is a pointer to D3.16, D4.6/D7.14, D9.25, D10.4, D11.4).

**Borderline (readable as standard, proof is the paper's own).** D5.2 + D5.3 (sub-exponential tail), D5.8, D8.5 (assumed MGF shape of D3.1), D9.15 (dyadic cover), D4.4 (adapted to $d_\Lambda$ and anchors).
