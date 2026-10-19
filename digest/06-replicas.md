# Digest of §6 — Symmetric replicas and entropy metrics

Source: `paper/sections/05-replicas.tex` (lines 1–853). Label `sec:replicas`. Numbering: Lemma 6.1 (`lem:schur`), Lemma 6.2 (`replicas:metric`), Lemma 6.3 (`lem:relative-pin`), Lemma 6.4 (`lem:symbol`); one shared counter, no other numbered environments. §5 results cited: Lemma 5.1 (`lem:movement`), Lemma 5.3 (`lem:skew`).

## Section in one paragraph

§6 lifts the one-copy estimates of §5 to $k$-copy symmetric states, $k\to\infty$, on a fixed finite system $\mathcal V$ ($d=\dim\mathcal V$). Order: Schur–Weyl labels $\lambda\vdash k$ and the label observable $F_{Q,k}=\sum_\lambda(\log d_\lambda)\pi^\lambda_{Q,k}$ with merge/split/surprisal/branching estimates (D6.1–D6.4) → one label function $w_k(\lambda)$, defined with the full dimension $d$ for every subsystem $Q$, with $W_{Q,k}\asymp e^{-tF_{Q,k}}$, $W_{Q,k}=W_{Q^c,k}$ on $\mathcal S_k$, $W_{Q,k}=\int(\sigma^t)^{\otimes k}d\zeta_Q$ and marked ratios $R_{Q,k}=W_{Q,k}W_{Q,k-1}^{-1}\approx(J_{Q,k})_+^t$ (D6.5–D6.6), fixed-factor identity (D6.7) → leaf metric $A_k(P,Y,F)=(W_P^{-1}W_F^{-1}W_Y)^2$ with $\log A_k=a(F_P+F_F-F_Y)+O(\log k)$, $a=2t$ (D6.8–D6.9) → operator lower bound $C_{x,k}\ge\poly(k)^{-1}e^{ka[\eta_\theta-Ca^{1/4}\log^C]}P_{\theta,k}$ for moving $x$ between parts, from Lemma 5.1 inside the integral for $W$ (D6.10) → scalar symbols: for $O_k=A_k^{-1/2}\bar hA_k^{1/2}$, polynomials in $O_k,O_k^\dagger$ have symbol $q(f_\theta,\bar f_\theta)$ against the coherent measure $\mu_\sigma$, hence $\operatorname{Tr}\sigma\mathcal D_k\le Ca^2\log^C(ed_h)\int\eta_\theta^{1/8}d\mu_\sigma+o_k(1)$ via Lemma 5.3 (D6.11–D6.16). The gain $\eta_\theta$ (D6.10) and cost $\eta_\theta^{1/8}$ (D6.12) are tested against the same symmetric $\sigma$, uniformly in $\sigma$: §7 averages metric changes with both. §8 uses the label dimension inequalities; §9 uses the floor and $\mu_\sigma$.

Conventions (line 29–37). Everything fixed before $k\to\infty$: $\mathcal V$, its tensor factorization, $t$, all exponents, the finite system, the finite family of partitions, any cutoff or polynomial approximation. $\poly(k)$ and constants depend on these. $o_k(1)$ is uniform over all density matrices on $\mathcal S_k$ (also for $\sigma$ depending on an interpolation parameter). Cutoff and polynomial errors are removed only after $k\to\infty$. Not in these lines: $H(p)=-\sum p_i\log p_i$ with $0\log0=0$ (used at 170–172, 393); $\log$ natural (Stirling form $n\log n-n$ at 170, 393).

---

### 6.0 Setup and Schur labels

#### D6.1 Def — Systems, symmetric subspaces, subsystems
*Source: 05-replicas.tex 13–27.*

**Statement.** $\mathcal V$ finite-dim complex Hilbert space with specified tensor factorization (auxiliary factors allowed). $d=\dim\mathcal V$, $\mathcal S_k=\operatorname{Sym}^k\mathcal V$, $D_k=\dim\mathcal S_k=\binom{k+d-1}{d-1}$, $\Pi_k$ orthogonal projector onto $\mathcal S_k$. A subsystem $Q$ is a union of the specified factors; $Q^c$ its complement in $\mathcal V$; $d_Q=\dim\mathcal H_Q$; $\varnothing$ has dimension $1$. Operators on $Q^{\otimes k}$ are extended by the identity. For $\pi\in S_k$: $U_Q(\pi)$ permutes the $k$ copies of $Q$; $U(\pi)=U_{\mathcal V}(\pi)$ permutes whole copies. Hence $U(\pi)=U_Q(\pi)U_{Q^c}(\pi)$.

**Used from.** none.

**Output.** Notation for D6.2–D6.17. $D_k$ is a polynomial of degree $d-1$ in $k$, so $D_k/D_{k+m}=1+O_{d,m}(k^{-1})$ (D6.14.5).

**Standard?** Notation.

#### D6.2 Step eq:schur-decomposition — Schur–Weyl decomposition and Weyl character
*Source: 05-replicas.tex 47–67, `replicas:schur-decomposition` (52–59).*

**Statement.** Partition $\lambda\vdash k$: non-increasing nonnegative integers with sum $k$ (trailing zeros allowed). $[\lambda]$ = irrep of $S_k$, $d_\lambda=\dim[\lambda]$.
$$(\mathbb C^q)^{\otimes k}=\bigoplus_{\lambda\vdash k,\ \ell(\lambda)\le q}[\lambda]\otimes V^{(q)}_\lambda,\qquad \chi^{(q)}_\lambda(x)=\frac{\det[x_i^{\lambda_j+q-j}]}{\det[x_i^{q-j}]}.$$
$V^{(q)}_\lambda$ = irrep of $GL_q$ with character $\chi^{(q)}_\lambda$. The $S_k$ and $GL_q$ actions are mutual centralizers. $V^{(q)}_\lambda$ stays irreducible under the unitary group $U(q)$: a subspace invariant under the differentiated unitary action is invariant under its complex span, which is $\mathfrak{gl}_q$.

**Used from.** none (cited: Etingof et al. 2011, Thm 5.18.4, Cor 5.19.2, Thm 5.22.1).

**Output.** Block structure used in D6.4 (every part), D6.6 (centrality of the $k$-copy integral), D6.10 ($\rho^{\otimes k}=\bigoplus I_{[\lambda]}\otimes M_\lambda$).

**Standard?** Standard (Schur–Weyl duality, Weyl character formula).

#### D6.3 Def eq:F-definition — Label projectors and the label observable $F_{Q,k}$
*Source: 05-replicas.tex 69–77, `replicas:F-definition` (71–73).*

**Statement.** $\pi^\lambda_{Q,k}$ = projector on $Q^{\otimes k}$ onto the $[\lambda]\otimes V_\lambda^{(d_Q)}$ block. 
$$F_{Q,k}=\sum_{\lambda\vdash k}(\log d_\lambda)\,\pi^\lambda_{Q,k}$$
self-adjoint, $\ge0$ (as $d_\lambda\ge1$). $F_{Q,0}=0$ (only the empty partition). Labels on several subsystems/copy groups are *compatible* if their joint spectral projector (product of the commuting label projectors, D6.4(2),(4)) is nonzero.

**Used from.** D6.2.

**Output.** $F$ appears in D6.4(5), D6.6 (`replicas:W-comparison`), D6.9. Compatibility is the hypothesis of D6.4(3),(4),(6).

**Standard?** Specific to this paper (the observable $F$); label projectors standard.

#### D6.4 Lemma 6.1 — Schur-label estimates
*Source: 05-replicas.tex statement 85–151, proof 153–275; equations `replicas:dimensions` (91–96), `replicas:merge-dimensions` (104–107), `replicas:merge-moment` (112–116), `replicas:group-dimensions` (120–123), `replicas:surprisal-moment` (128–131), `replicas:branch-probability` (136–141), `replicas:star-definition` (144–146).*

**Statement.** For the systems of D6.1:

1. $\lambda\vdash k$, $\ell(\lambda)\le q$, $l_i=\lambda_i+q-i$ ($1\le i\le q$):
$$\dim V^{(q)}_\lambda=\prod_{i<j}\frac{l_i-l_j}{j-i},\quad d_\lambda=\frac{k!\prod_{i<j}(l_i-l_j)}{\prod_il_i!},\quad\log d_\lambda=kH(\lambda/k)+O_q(\log(k+2)).$$
 The number of labels and $\sum_\lambda\dim V^{(q)}_\lambda$ are $\le\poly(k)$ ($q$ fixed).
2. Central label functions of $S_k$ commute for nested or disjoint subsystems. On $\mathcal S_k$: $\pi^\lambda_{Q,k}=\pi^\lambda_{Q^c,k}$.
3. $Q,E$ disjoint, labels $\lambda,\mu$ compatible with label $\nu$ on $QE$: $d_\nu\le d_\lambda d_\mu$ and $d_\lambda\le d_\nu d_\mu$. For a tensor product of permutation-invariant densities on $Q^{\otimes k}$, $E^{\otimes k}$: $\Pr(\nu\mid\lambda,\mu)\le\poly(k)\,d_\nu/(d_\lambda d_\mu)$. Hence for $0\le b\le1$, uniformly in the densities,
$$\mathbb E\Bigl(\frac{d_\lambda d_\mu}{d_\nu}\Bigr)^b\le\poly(k).$$
4. Copies split into groups of sizes $k-r$ and $r$; labels $\alpha,\beta$ (on a fixed subsystem, on the two groups) compatible with the full label $\lambda$:
$$d_\alpha d_\beta\le d_\lambda\le\binom kr d_\alpha d_\beta.$$
 The subgroup label projectors commute with the full label projector.
5. $\rho$ permutation-invariant density on $Q^{\otimes k}$, $L_\rho=-\log\rho$ on $\operatorname{supp}\rho$: $[F_Q,\rho]=0$, $0\le F_Q\le L_\rho$ on the support, and
$$\operatorname{Tr}\rho\,e^{b(L_\rho-F_Q)}\le\poly(k)\qquad(0\le b\le1).$$
6. Full $Q$-label $\lambda$ and first-$(k-1)$-copies label $\nu$ are compatible iff $\nu=\lambda-e_i$ is a partition. In any permutation-invariant $Q$ state, conditional on $\lambda$,
$$p_{\lambda,i}=\frac{d_{\lambda-e_i}}{d_\lambda}=\frac{l_i}{k}\frac{\prod_{a<b}(l_a-\delta_{ai}-l_b+\delta_{bi})}{\prod_{a<b}(l_a-l_b)}\le2^q\frac{l_i}{k}.$$
 The star operator $J_{Q,k}=\frac1k\sum_{j<k}U_Q((j\ k))$ has eigenvalue $(\lambda_i-i)/k$ on branch $i$.

Polynomial bounds depend on the fixed subsystem dimensions only.

**Used from.** D6.1, D6.2, D6.3.

**Proof.**
- D6.4.1 *Weyl dimension.* $\dim V_\lambda^{(q)}=\chi^{(q)}_\lambda(1,\dots,1)$, limit of the alternant ratio $\det[x_i^{l_j}]/\det[x_i^{q-j}]$; gives $\prod_{i<j}(l_i-l_j)/(j-i)$.
- D6.4.2 *Coefficient extraction.* Multiply $(x_1+\dots+x_q)^k=\sum_\lambda d_\lambda\chi^{(q)}_\lambda$ by $\det[x_i^{q-j}]$. RHS: $\sum_\lambda d_\lambda\det[x_i^{l_j(\lambda)}]$. Coefficient of $x^{l}=x_1^{l_1}\cdots x_q^{l_q}$ with $l_1>\dots>l_q$: only the identity term of the alternant of $\lambda$ contributes, so the coefficient is $d_\lambda$.
- D6.4.3 *Other side.* Coefficient of $x^l$ in $(\sum x_i)^k\sum_\sigma\operatorname{sgn}\sigma\prod x_i^{q-\sigma(i)}$ is $\sum_\sigma\operatorname{sgn}\sigma\,k!/\prod_i(l_i-q+\sigma(i))!=k!\det[1/(l_i-q+j)!]$ (reciprocal of a negative factorial $=0$).
- D6.4.4 *Vandermonde.* $1/(l_i-q+j)!=(l_i)_{q-j}/l_i!$ ($(u)_m$ falling factorial). Columns of $[(l_i)_{q-j}]$ are monic polynomials in $l_i$ of degree $q-j$ $\Rightarrow$ $\det=\prod_{i<j}(l_i-l_j)$. Hence $d_\lambda=k!\prod_{i<j}(l_i-l_j)/\prod_il_i!$.
- D6.4.5 *Entropy.* $\log n!=n\log n-n+O(\log(n+2))$. $l_i=\lambda_i+O_q(1)$ $\Rightarrow$ $l_i\log l_i-\lambda_i\log\lambda_i=O_q(\log(k+2))$. $\sum\lambda_i=k$ $\Rightarrow$ $k\log k-\sum\lambda_i\log\lambda_i=kH(\lambda/k)$. Linear terms: $-k+\sum_il_i=\binom q2$ ($\sum l_i=k+\binom q2$). The $l_i-l_j$ are distinct-integer differences in $[1,k+q]$, so $0\le\log\prod(l_i-l_j)\le q^2\log(k+q)$.
- D6.4.6 *Counting.* $\le(k+1)^q$ labels. $\dim V_\lambda^{(q)}\le(k+q)^{q(q-1)/2}$ since $1\le j-i$, $0<l_i-l_j\le k+q$.
- D6.4.7 *Central projector.* $\pi^\lambda_{Q,k}=\frac{d_\lambda}{k!}\sum_\pi\chi_\lambda(\pi^{-1})U_Q(\pi)$ (character orthogonality, or Schur on the central sum).
- D6.4.8 *Nested/disjoint commutation.* $Q\subseteq Q'$: $U_{Q'}(\sigma)U_Q(\pi)U_{Q'}(\sigma)^\dagger=U_Q(\sigma\pi\sigma^{-1})$, so a central combination of $U_Q$ commutes with all $U_{Q'}(\sigma)$, hence with every $\pi^\mu_{Q'}$. Disjoint: operators on different tensor factors commute.
- D6.4.9 *Complement.* $z\in\mathcal S_k$: $U(\pi)z=z\Rightarrow U_Q(\pi)z=U_{Q^c}(\pi^{-1})z$. Then $\pi^\lambda_Qz=\frac{d_\lambda}{k!}\sum_\pi\chi_\lambda(\pi^{-1})U_{Q^c}(\pi^{-1})z=\frac{d_\lambda}{k!}\sum_{\pi'}\chi_\lambda(\pi')U_{Q^c}(\pi')z=\pi^\lambda_{Q^c}z$, using $\chi_\lambda(\pi')=\chi_\lambda(\pi'^{-1})$ ($\pi$ conjugate to $\pi^{-1}$). Same fact: all Specht modules self-dual.
- D6.4.10 *Merge, dimensions.* On a block with $(\lambda,\mu)$, $S_k$ acts diagonally on $[\lambda]\otimes[\mu]$; compatibility with $\nu$ means $[\nu]\subseteq[\lambda]\otimes[\mu]$ $\Rightarrow$ $d_\nu\le d_\lambda d_\mu$. $\operatorname{Hom}_{S_k}([\nu],[\lambda]\otimes[\mu])\simeq\operatorname{Hom}_{S_k}([\lambda],[\nu]\otimes[\mu]^*)$ and $[\mu]^*\simeq[\mu]$ $\Rightarrow$ $d_\lambda\le d_\nu d_\mu$.
- D6.4.11 *Merge, probability.* Conditional on $(\lambda,\mu)$ a product of invariant states is $I/(d_\lambda d_\mu)$ on the Specht factors $[\lambda]\otimes[\mu]$. With $g_{\lambda\mu\nu}$ the multiplicity of $[\nu]$ in $[\lambda]\otimes[\mu]$: $\Pr(\nu\mid\lambda,\mu)=g_{\lambda\mu\nu}d_\nu/(d_\lambda d_\mu)$ exactly.
- D6.4.12 *Multiplicity bound.* In $(Q\otimes E)^{\otimes k}$ the $[\nu]$-isotypic block has multiplicity space of dimension $\dim V^{(d_Qd_E)}_\nu$, containing $g_{\lambda\mu\nu}$ copies of $V_\lambda^{(d_Q)}\otimes V_\mu^{(d_E)}$. So $g_{\lambda\mu\nu}\dim V_\lambda\dim V_\mu\le\dim V_\nu^{(d_Qd_E)}$ $\Rightarrow$ $g\le\poly(k)$.
- D6.4.13 *Merge moment.* $R=d_\lambda d_\mu/d_\nu\ge1$ (D6.4.10), $\Pr(\nu\mid\lambda,\mu)=g_{\lambda\mu\nu}/R$. $\mathbb E[R^b\mid\lambda,\mu]=\sum_\nu g_{\lambda\mu\nu}R^{b-1}\le\sum_\nu g_{\lambda\mu\nu}\le\poly(k)$ (at most $(k+1)^{d_Qd_E}$ labels $\nu$, each $g\le\poly$).
- D6.4.14 *Copy groups.* $[\alpha]\otimes[\beta]\subseteq\operatorname{Res}^{S_k}_{S_{k-r}\times S_r}[\lambda]$ $\Rightarrow$ $d_\alpha d_\beta\le d_\lambda$. Fix a copy $W\simeq[\alpha]\otimes[\beta]$ in $[\lambda]$. Translates $gW$ span $[\lambda]$ (irreducible); $gW$ depends only on the coset $g(S_{k-r}\times S_r)$; $\binom kr$ cosets $\Rightarrow$ $d_\lambda\le\binom kr d_\alpha d_\beta$. Central elements of $S_k$ commute with the subgroup algebra $\Rightarrow$ commutation.
- D6.4.15 *Surprisal.* Invariant $\rho$ commutes with $S_k$ $\Rightarrow$ $\rho=\bigoplus_\lambda I_{[\lambda]}\otimes M_\lambda$ (D6.2). Each positive eigenvalue $u$ of $M_\lambda$ occurs $d_\lambda$ times in $\rho$, trace $\le1$ $\Rightarrow$ $ud_\lambda\le1$ $\Rightarrow$ $-\log u\ge\log d_\lambda$: $F_Q\le L_\rho$; $[F_Q,\rho]=0$ since $\pi^\lambda$ are block projectors. $F_Q\ge0$ from $d_\lambda\ge1$.
- D6.4.16 *Moment.* Block $\lambda$, eigenvalue $u$ contributes $d_\lambda\cdot u\cdot(ud_\lambda)^{-b}=(ud_\lambda)^{1-b}\le1$ ($1-b\ge0$). So $\operatorname{Tr}\rho e^{b(L_\rho-F_Q)}=\sum_\lambda\sum_{u>0}(ud_\lambda)^{1-b}\le\sum_\lambda\dim V_\lambda^{(d_Q)}\le\poly(k)$.
- D6.4.17 *Branching.* Multiply a Weyl numerator alternant by $\sum x_i$: sum of alternants with one exponent raised by $1$; equal exponents vanish; the survivors are legal added boxes. So $V^{(q)}_\nu\otimes\mathbb C^q=\bigoplus_{\lambda=\nu+e_i}V^{(q)}_\lambda$, multiplicity one. Comparing the Schur–Weyl decompositions of the first $k-1$ copies and the last copy: the $\nu$-branch in the $\lambda$ block has rank $d_\nu$ on $[\lambda]$ and acts as identity on $V_\lambda^{(q)}$.
- D6.4.18 *Branch probability.* Invariant state is uniform on $[\lambda]$ $\Rightarrow$ $p_{\lambda,i}=d_{\lambda-e_i}/d_\lambda$. Insert the formula of (1) for $(k,l)$ and $(k-1,l-e_i)$: $(k-1)!/k!=1/k$, $l_i!/(l_i-1)!=l_i$, Vandermonde ratio as displayed.
- D6.4.19 *Bound.* In the ratio, a pair $(a,i)$, $a<i$: $(l_a-l_i+1)/(l_a-l_i)\le2$ ($l_a-l_i\ge1$); at most $q-1$ such pairs. A pair $(i,b)$, $b>i$: $(l_i-1-l_b)/(l_i-l_b)\le1$ and $\ge0$ on a legal branch. Hence $p_{\lambda,i}\le2^{q-1}l_i/k\le2^ql_i/k$.
- D6.4.20 *Star, quadratic identity.* $E^{\rm tot}_{ab}=\sum_jE_{ab}^{(j)}$. $\sum_{a,b}E^{\rm tot}_{ab}E^{\rm tot}_{ba}=kqI+2\sum_{j<j'}U_Q((j\,j'))$: terms $j=j'$ give $\sum_{ab}E_{ab}E_{ba}=qI$ per copy; ordered pairs $j\neq j'$ give $\sum_{ab}E^{(j)}_{ab}E^{(j')}_{ba}=U_Q((j\,j'))$.
- D6.4.21 *Star, scalar on block $\lambda$.* The left side is scalar on a Schur block. Evaluate on a highest-weight vector $v$ (lexicographically leading weight $\lambda$); $E^{\rm tot}_{ab}v=0$ for $a<b$ (would raise the weight). $a=b$: $\sum_i\lambda_i^2$. $a<b$: $E_{ab}E_{ba}v=[E_{ab},E_{ba}]v=(\lambda_a-\lambda_b)v$ (using $[E_{ab}^{\rm tot},E_{ba}^{\rm tot}]=E_{aa}^{\rm tot}-E_{bb}^{\rm tot}$); the transposed term $E_{ba}E_{ab}v=0$. $\sum_{a<b}(\lambda_a-\lambda_b)=\sum_i\lambda_i(q+1-2i)$. Scalar $c_\lambda=\sum_i\lambda_i(\lambda_i+q+1-2i)$.
- D6.4.22 *Star, difference.* $\sum_{j<j'\le k}U((j\,j'))-\sum_{j<j'\le k-1}U((j\,j'))=\sum_{j<k}U((j\,k))=kJ_{Q,k}$. On branch $\lambda\to\lambda-e_i$: $kJ=\frac12[(c_\lambda-kq)-(c_{\lambda-e_i}-(k-1)q)]=\frac12[c_\lambda-c_{\lambda-e_i}-q]$. Only the $i$-th summand changes: $c_\lambda-c_{\lambda-e_i}=2\lambda_i+q-2i$. So $kJ=\lambda_i-i$.

**Output.** (1): entropy of $\log d_\lambda$ for D6.6 (`replicas:W-comparison`). (2): complement equality for D6.6, D6.9, commutation for D6.8 and §9. (3): $F_{PF}\le F_P+F_F$ in D6.9; the paper's introduction to §6 (lines 79–83) announces it for the §8 norm comparisons, no later citation by number. (4): subgroup dimension inequalities, 07-comparators.tex 467; commutation in D6.6.11. (5): `replicas:surprisal-moment` used in §8 (`comparator:label-remainder`) and in D6.10.3 (eigenvalue repetition). (6): $p_{\lambda,i}$ and $J$ eigenvalue for D6.6.

**Standard?** (1) standard (Weyl dimension; Frobenius formula for $d_\lambda$; cf. Keyl–Werner 2001 for tensor powers). (2),(4),(6) standard rep theory (branching rule, Vershik–Okounkov 2005 for JM elements). (3),(5) and the polynomial moment bounds: specific to this paper (the extension from tensor powers to arbitrary invariant densities).

**Pitfall.** $Q^c$ is the complement inside $\mathcal V$, equality of labels is only on $\mathcal S_k$. In (6) the $l_i$ use $q=d_Q$; D6.6 later bounds it by the padded $l_i$ with $q=d$ (D6.6.14). (3) needs independent (product) invariant states. The $\poly(k)$ in $\Pr(\nu\mid\lambda,\mu)\le\poly(k)\,d_\nu/(d_\lambda d_\mu)$ is the multiplicity bound $g_{\lambda\mu\nu}\le\poly(k)$ (D6.4.12).

---

### 6.1 A common metric on every subsystem

#### D6.5 Def eq:w-definition — The label function $w_k$ and $W_{Q,k}$
*Source: 05-replicas.tex 279–303, `replicas:w-definition` (290–299).*

**Statement.** Fix $0<t<1/4$, $a=2t$. Pad every label to length $d=\dim\mathcal V$ (for every subsystem, whatever $d_Q$). With $c=d+(1+t)\binom d2$:
$$w_k(\lambda)=\frac{\Gamma(c)}{\Gamma(c+tk)}\prod_{i=1}^d\frac{\Gamma(1+t(\lambda_i+d-i))}{\Gamma(1+t(d-i))},\qquad W_{Q,k}=\sum_\lambda w_k(\lambda)\pi^\lambda_{Q,k}.$$
$W_{Q,0}=I$. For $\dim Q=1$ and $k>0$: $W_{Q,k}=w_k((k))\,I$, positive but $\ne1$.

**Used from.** D6.3.

**Output.** $W$ in D6.6–D6.10 and §7 (`replicas:w-definition`, common padding dimension $d$). The constant $c$ here is a different object from the constant $c$ of Lemma 5.1 (the paper reuses the letter in D6.10).

**Standard?** Specific to this paper (the Gamma-product weight is chosen so that D6.6 holds; cf. Muttalib–Borodin ensembles, Forrester–Ipsen 2018).

**Pitfall.** One function $w_k$ for all subsystems is what makes $W_{Q,k}=W_{Q^c,k}$ on $\mathcal S_k$ possible when $d_Q\ne d_{Q^c}$; hence full $d$, not $d_Q$.

#### D6.6 Lemma 6.2 — Integral formula and marked ratios
*Source: 05-replicas.tex statement 305–335, proof 337–434; equations `replicas:W-comparison` (308–311), `replicas:W-integral` (315–318), `replicas:R-forward` (323–325), `replicas:R-inverse` (329–334), `replicas:ratio-eigenvalue` (402–406).*

**Statement.** $W_{Q,k}$ is positive definite and central. Uniformly in labels,
$$\poly(k)^{-1}e^{-tF_{Q,k}}\le W_{Q,k}\le\poly(k)\,e^{-tF_{Q,k}}.$$
On $\mathcal S_k$: $W_{Q,k}=W_{Q^c,k}$. For each $Q$ there is a probability measure $\zeta_Q$ on positive definite subdensities $\sigma$ on $Q$ ($\operatorname{Tr}\sigma\le1$), independent of $k$, with
$$W_{Q,k}=\int(\sigma^t)^{\otimes k}\,d\zeta_Q(\sigma)\qquad(k\ge0).$$
With $W_{Q,k-1}$ extended by $I$ on the last copy and $R_{Q,k}=W_{Q,k}W_{Q,k-1}^{-1}$:
$$\|R_{Q,k}-(J_{Q,k})_+^t\|\to0\quad\text{on the whole tensor space.}$$
There is $C_{\mathcal V,t}$ with $\|R^{-1}_{Q,k}z\|\le C_{\mathcal V,t}$ for every unit $z\in\mathcal S_k$, and for $0<\delta<1$
$$\limsup_{k\to\infty}\sup_{z\in\mathcal S_k,\|z\|=1}\|(R_{Q,k}^{-1}-\max(J_{Q,k},\delta)^{-t})z\|\le C_{\mathcal V,t}\,\delta^{(1-2t)/2}.$$

**Used from.** D6.2 (irreducibility under $U(d)$); D6.3; D6.4 (1),(2),(4),(6); D6.5.

**Proof.**
- D6.6.1 *Positivity.* $w_k(\lambda)>0$ (Gamma at positive arguments), so $W$ is positive definite; central as a combination of label projectors.
- D6.6.2 *Simplex measure ($Q=\mathcal V$, $d\ge2$).* $s$ on $\{s_i\ge0,\sum s_i=1\}$ with density $\propto\Delta(s)\Delta(s^t)$, $\Delta(s)=\prod_{i<j}(s_i-s_j)$: nonnegative, integrable, positive off collisions (simplex normalization of the Laguerre Muttalib–Borodin weight; Forrester–Ipsen 2018, §2.3 eq. (26)). $d=1$: point mass $s_1=1$. $\sigma=U\operatorname{diag}(s)U^\dagger$, $U$ Haar independent of $s$.
- D6.6.3 *Centrality.* $\int(\sigma^t)^{\otimes k}$ commutes with permutations and with $V^{\otimes k}$-unitaries $U^{\otimes k}$ ($U$ Haar-averaged), so it is scalar on each irreducible $[\lambda]\otimes V_\lambda$. Scalar $=\operatorname{Tr}(\text{block})/(d_\lambda\dim V_\lambda)=\mathbb E[\chi_\lambda^{(d)}(s^t)]/\dim V^{(d)}_\lambda$.
- D6.6.4 *Cancellation.* $l_i=\lambda_i+d-i$. $\chi_\lambda(s^t)=\det[s_i^{tl_j}]/\Delta(s^t)$: the Weyl denominator cancels $\Delta(s^t)$ in the density. Remaining: $\int\det[s_i^{d-j}]\det[s_i^{tl_j}]ds$.
- D6.6.5 *Gamma integral.* $\int_{\sum s_i=1}\prod s_i^{u_i}ds=\prod\Gamma(1+u_i)/\Gamma(d+\sum u_i)$ ($u_i>-1$). Proof: change $x_i=rs_i$ in the product of the defining gamma integrals; Jacobian $r^{d-1}$. Expanding both determinants: exponents $u_i=d-\sigma(i)+tl_{\tau(i)}$, $\sum u_i=\binom d2+t(k+\binom d2)$, so $d+\sum u_i=c+tk$. All $d!$ relabelings give the same term:
$$\int=\frac{d!}{\Gamma(c+tk)}\det[\Gamma(1+tl_i+d-j)]_{i,j=1}^d.$$
- D6.6.6 *Determinant.* Factor $\Gamma(1+tl_i)$ from row $i$: entries become $(1+tl_i)_{d-j}$ (rising factorial), monic of degree $d-j$ in $tl_i$ $\Rightarrow$ $\det=\Delta(tl)=t^{\binom d2}\Delta(l)$. Dividing by $\dim V_\lambda=\Delta(l)/\prod(j-i)$ cancels $\Delta(l)$. Left: $\lambda$- and $k$-independent constant $\times\prod_i\Gamma(1+tl_i)/\Gamma(c+tk)$. Normalizing $\lambda=\varnothing$, $k=0$ (eigenvalue $1$) fixes the constant: $w_k(\lambda)$ of D6.5. The measure does not depend on $k$.
- D6.6.7 *Subsystem $d_Q\le d$.* Isometry $E:\mathcal H_Q\to\mathbb C^d$. $(E^\dagger)^{\otimes k}U_{\mathbb C^d}(\pi)E^{\otimes k}=U_Q(\pi)$. $W_{\mathbb C^d,k}=\frac1{k!}\sum_\pi f_k(\pi)U(\pi)$ with $f_k(\pi)=\sum_\lambda w_k(\lambda)d_\lambda\chi_\lambda(\pi^{-1})$ (D6.4.7), depending on $(k,d)$ only; compressing gives $\frac1{k!}\sum_\pi f_k(\pi)U_Q(\pi)$ with the same $f_k$, i.e. $W_{Q,k}=\sum_\lambda w_k(\lambda)\pi_{Q,k}^\lambda$ (labels with $\ell>d_Q$ vanish). So $W_{Q,k}=\int(E^\dagger\sigma^tE)^{\otimes k}d\zeta(\sigma)$.
- D6.6.8 *Back to subdensities.* $B=E^\dagger\sigma^tE>0$ a.s. ($s_i>0$ in the interior). $\tau=B^{1/t}$. Min–max: eigenvalues of $B$ $\le$ those of $\sigma^t$ $\Rightarrow$ eigenvalues of $\tau\le s_i$ $\Rightarrow\operatorname{Tr}\tau\le1$. $B^{\otimes k}=(\tau^t)^{\otimes k}$; $\zeta_Q$ = law of $\tau$.
- D6.6.9 *Complement.* $W_{Q,k}=W_{Q^c,k}$ on $\mathcal S_k$ from D6.4(2) (same $w_k$, equal projectors).
- D6.6.10 *Comparison.* $\log\Gamma(1+u)=u\log u-u+O(\log(u+2))$ on the fixed number of factors: $\log w_k(\lambda)=-tkH(\lambda/k)+O_{d,t}(\log(k+2))$ ($\Gamma(c+tk)$ contributes $-(tk\log(tk)-tk)$; the $i$-sum contributes $t\sum\lambda_i\log\lambda_i+tk\log t-tk$; the $\log t$ terms cancel). D6.4(1): $kH(\lambda/k)=\log d_\lambda+O(\log(k+2))$. So $w_k(\lambda)=d_\lambda^{-t}\poly(k)^{\pm1}$; spectral calculus gives `replicas:W-comparison`.
- D6.6.11 *Ratio, block structure.* $W_{Q,k-1}\otimes I=\sum_\nu w_{k-1}(\nu)\pi^\nu_{Q,k-1}$ commutes with $W_{Q,k}$ (D6.4(4): central of $S_k$ commutes with the subgroup algebra). Joint blocks $(\lambda,\nu=\lambda-e_i)$: $R_{Q,k}=w_k(\lambda)/w_{k-1}(\lambda-e_i)$ there.
- D6.6.12 *Eigenvalue.* $l_i=\lambda_i+d-i$ (full $d$). Only the $i$-th Gamma and the $\Gamma(c+tk)$ change: $r_{\lambda,i}=\dfrac{\Gamma(c+t(k-1))}{\Gamma(c+tk)}\dfrac{\Gamma(1+tl_i)}{\Gamma(1+t(l_i-1))}$.
- D6.6.13 *Two-sided and limit.* Gamma ratios: $r_{\lambda,i}\asymp_{d,t}((l_i+1)/k)^t$. If $l_i/k\ge\varepsilon$: $r_{\lambda,i}\to(l_i/k)^t$ uniformly (relative error $O(1/(\varepsilon k))$), and $(l_i/k)^t-(\max(l_i-d,0)/k)^t\le(d/k)^t$. If $l_i/k<\varepsilon$: $r_{\lambda,i}\le C(\varepsilon+1/k)^t$ and $\max((l_i-d)/k,0)^t\le\varepsilon^t$. Let $k\to\infty$, then $\varepsilon\downarrow0$. Since $J_{Q,k}=(\lambda_i-i)/k=(l_i-d)/k$ on branch $i$ (D6.4(6)), this is `replicas:R-forward`. Also $\sup\|R_{Q,k}\|<\infty$.
- D6.6.14 *Inverse vector bound.* $z\in\mathcal S_k$ unit; its $Q$-marginal is permutation-invariant ($U_{Q^c}$ is traced out). D6.4(6) with $q=d_Q$: $p_{\lambda,i}\le2^{d_Q}(\lambda_i+d_Q-i)/k\le C_dl_i/k$ (since $\lambda_i+d_Q-i\le l_i$). Conditional on $\lambda$: $\sum_ip_{\lambda,i}r_{\lambda,i}^{-2}\le C_{d,t}\sum_i(l_i/k)^{1-2t}\le C_{d,t}$ ($1-2t>0$, $l_i\le k+d$). Averaging over $\lambda$ gives $\|R_{Q,k}^{-1}z\|^2\le C_{d,t}$.
- D6.6.15 *Clipped inverse.* $R^{-1}$ and $\max(J,\delta)^{-t}$ are diagonal in the joint blocks. On $J\ge\delta$: $l_i/k\ge\delta$, so $r_{\lambda,i}^{-1}-((l_i-d)/k)^{-t}\to0$ uniformly (D6.6.13, inverse map uniformly Lipschitz on $[\delta^t/2,\infty)$): operator-norm error $\to0$. On $J<\delta$: $l_i/k\le\delta+d/k$. True inverse: squared norm of the restriction $\le C_{d,t}(\delta+d/k)^{1-2t}$ (D6.6.14 restricted). Clipped inverse equals $\delta^{-t}$ there: squared norm $\le C_d(\delta+d/k)\delta^{-2t}$. Limsup in $k$ (the two restricted squared norms are each $\le C\delta^{1-2t}$), square root, triangle inequality: error $\le C_{\mathcal V,t}\delta^{(1-2t)/2}$.
- D6.6.16 *Uniformity.* All bounds conditional on $\lambda$ for an arbitrary symmetric vector, so uniform in $z$.

**Output.** (`W-comparison`): D6.9 floor, D6.10 (`replicas:compensator`), §7. (`W-integral`): D6.10.5, §7. (`R-forward`),(`R-inverse`) with $\|R\|\le C$ and $\|R^{-1}z\|\le C$: D6.13 (bounded approximation). Complement equality: D6.8, D6.9, §9 mirror step.

**Standard?** Integral formula: specific to this paper, built on Muttalib–Borodin / Laguerre simplex integrals (Forrester–Ipsen 2018). The Gamma asymptotics and Gamma-ratio estimates are standard (Stirling).

**Pitfall.** $R^{-1}$ has no uniform operator bound ($r_{\lambda,i}\sim k^{-t}$ for $l_i=O(1)$); only the vector bound on symmetric $z$ holds. `replicas:R-inverse` is a $\limsup$ over $k$ at fixed $\delta$, with $C_{\mathcal V,t}\delta^{(1-2t)/2}$ not tending to $0$ at fixed $\delta$. Only $1-2t>0$ is used in the proof; $t<1/4$ is the standing hypothesis. Order of limits inside D6.6.13: $k\to\infty$ first, then $\varepsilon\downarrow0$.

#### D6.7 Step eq:fixed-factor — Fixed pure factor restriction identity
*Source: 05-replicas.tex 436–449, `replicas:fixed-factor` (439–442).*

**Statement.** $B,Q$ disjoint, $\phi$ a fixed vector on $B$, $z$ on $Q$-copies (and other factors):
$$W_{BQ,k}(\phi^{\otimes k}\otimes z)=\phi^{\otimes k}\otimes W_{Q,k}z.$$
Same identity for $F$ and for every real power of $W$ (including $W^{-1}$).

**Used from.** D6.4.7; D6.5; D6.6.7.

**Proof.**
- D6.7.1 $W_{BQ,k}=\frac1{k!}\sum_\pi f_k(\pi)U_{BQ}(\pi)$ with the same central function $f_k(\pi)=\sum_\lambda w_k(\lambda)d_\lambda\chi_\lambda(\pi^{-1})$ as for $W_{Q,k}$ (D6.4.7, D6.6.7).
- D6.7.2 $U_{BQ}(\pi)(\phi^{\otimes k}\otimes z)=\phi^{\otimes k}\otimes U_Q(\pi)z$: simultaneous permutation of the $B$ copies fixes $\phi^{\otimes k}$ for any vector $\phi\in\mathcal H_B$.
- D6.7.3 Same coefficients both sides. $F$, $W^s$ are central functions $\sum g(\lambda)\pi^\lambda$ too.
- D6.7.4 $\phi$ may be a Bell vector between two factors inside $B$: only the whole $B$ factor is permuted.

**Output.** §7 (fixed ancilla vectors, Bell pairs inside $B$).

**Standard?** Specific to this paper.

#### D6.8 Def eq:leaf-metric — The partition metric $A_k(P,Y,F)$
*Source: 05-replicas.tex 451–458, `replicas:leaf-metric` (456–458).*

**Statement.** For a partition $P,Y,F$ of the full one-copy system ($P,F$ outer parts, $Y$ middle part; no geometric condition), on $\mathcal S_k$:
$$A_k(P,Y,F)=\bigl(W_{P,k}^{-1}W_{F,k}^{-1}W_{Y,k}\bigr)^2.$$
The three factors commute (disjoint central label functions, D6.4(2)). $A_k$ is symmetric under $P\leftrightarrow F$.

**Used from.** D6.4(2), D6.6.

**Output.** $A_k$ in D6.10 (as $A_k$, $B_k$), D6.12 ($O_k$), §7–§9 (`replicas:leaf-metric`).

**Standard?** Specific to this paper.

#### D6.9 Step eq:leaf-floor — Floor of the leaf metric and commutation with copy averages
*Source: 05-replicas.tex 459–468, `replicas:leaf-floor` (460–463).*

**Statement.** In operator norm,
$$\log A_k=a(F_P+F_F-F_Y)+O_{\mathcal V,t}(\log(k+2)),\qquad A_k\ge\poly(k)^{-1}I.$$
If a one-copy operator $h$ is contained in one part, its copy average $\bar h=k^{-1}\sum_jh^{(j)}$ commutes with $A_k$.

**Used from.** D6.3; D6.4(2),(3); D6.6 (`W-comparison`); D6.8.

**Proof.**
- D6.9.1 $W_P^{-1}\asymp e^{tF_P}$, $W_F^{-1}\asymp e^{tF_F}$, $W_Y\asymp e^{-tF_Y}$ up to $\poly(k)^{\pm1}$ (D6.6), all commuting; square: $A_k\asymp e^{2t(F_P+F_F-F_Y)}$ up to $\poly(k)^{\pm1}$ (squaring doubles the degree), $a=2t$.
- D6.9.2 $F_Y=F_{PF}$ on $\mathcal S_k$ ($Y=(PF)^c$, D6.4(2)). On compatible labels $\nu$ of $PF$ with $\lambda,\mu$ of $P,F$: $d_\nu\le d_\lambda d_\mu$ (D6.4(3)), i.e. $F_{PF}\le F_P+F_F$. Hence $F_P+F_F-F_Y\ge0$ and $A_k\ge\poly(k)^{-1}I$.
- D6.9.3 $h$ in part $R$: $\bar h$ commutes with $U_R(\pi)$ (symmetric sum), hence with $W_R$; disjoint from the other two parts, so commutes with their $W$.

**Output.** Floor $A_k\ge\poly(k)^{-1}$ used in §9 (initial mean tree; `replicas:leaf-floor` is cited at 08-scanner.tex 460). $[\bar h,A_k]=0$ for $h$ inside a part.

**Standard?** Specific to this paper.

---

### 6.2 An operator lower bound for moving a subsystem

#### D6.10 Lemma 6.3 — Relative coherent pin
*Source: 05-replicas.tex statement 480–505, proof 507–587; equations `replicas:relative-pin` (496–501), `replicas:move-inverse` (518–525), `replicas:compensator` (540–542), `replicas:move-one-copy` (566–570).*

**Statement.** $P,x,Y_0,F$ partition $\mathcal V$, $Y=xY_0$, $0<t<1/4$, $a=2t$,
$$A_k=A_k(P,xY_0,F),\quad B_k=A_k(Px,Y_0,F),\quad C_{x,k}=A_k^{-1/2}B_kA_k^{-1/2}.$$
Assume $a\log(e\dim x)\le c$ ($c$ of Lemma 5.1). For every unit $\theta\in\mathcal V$ put $\eta_\theta=S_\theta(x|P)+S_\theta(x|Y_0)=I_\theta(x:F|P)=I_\theta(x:F|Y_0)\ge0$. There is a polynomial bound uniform in $\theta$ such that on $\mathcal S_k$, with $P_{\theta,k}=|\theta^{\otimes k}\rangle\langle\theta^{\otimes k}|$:
$$C_{x,k}\ge\poly(k)^{-1}\exp\Bigl\{ka\bigl[\eta_\theta-Ca^{1/4}\log^C(e\dim x)\bigr]\Bigr\}P_{\theta,k}.$$
Same for a move to $F$ with the outer parts exchanged. No move ($x=\varnothing$): $C_{x,k}=I$, gain $0$.

**Used from.** D6.1; D6.4(2),(5); D6.6 (`W-comparison`, `W-integral`); D6.8; D5.1; D5.5 = Lemma 5.1 (`lem:movement`): for unit $\theta$ on $P,x,U,F$, $\eta=S(x|P)+S(x|U)=I(x:F|U)=I(x:F|P)$, $\ell=\log(e\dim x)$, universal $c,C$, $0<a\ell\le c$, all densities $\sigma$ on $xP$, $\tau$ on $xU$ (subnormalized ok): $\|\sigma^{a/2}\widehat\rho_P^{-a/2}\tau^{a/2}\widehat\rho_U^{-a/2}\theta\|\le\exp(-\tfrac a2\eta+Ca^{5/4}\ell^2)$.

**Proof.**
- D6.10.1 *Cauchy–Schwarz.* $C>0$, unit $z$: $|\langle z,u\rangle|^2\le\langle z,C^{-1}z\rangle\langle u,Cu\rangle$, i.e. $C\ge\langle z,C^{-1}z\rangle^{-1}|z\rangle\langle z|$. With $z=\theta^{\otimes k}$ it suffices to bound $\langle\theta^{\otimes k},C_{x,k}^{-1}\theta^{\otimes k}\rangle$ above.
- D6.10.2 *Norm identity.* $C^{-1}_{x,k}=A_k^{1/2}B_k^{-1}A_k^{1/2}$, so $\langle\theta^{\otimes k},C_{x,k}^{-1}\theta^{\otimes k}\rangle=\|B_k^{-1/2}A_k^{1/2}\theta^{\otimes k}\|^2$. $A_k^{1/2}=W_P^{-1}W_F^{-1}W_{xY_0}$, $B_k^{-1/2}=W_{Px}W_FW_{Y_0}^{-1}$. $W_F$ is disjoint from everything else and cancels. Move $W_{xY_0}$ left past $W_P^{-1}$ (disjoint) and $W_{Y_0}^{-1}$ (nested). Result (`replicas:move-inverse`): $\|W_{Px}W_{xY_0}W_P^{-1}W_{Y_0}^{-1}\theta^{\otimes k}\|^2$. This is an identity of norms; $A_k$ and $B_k$ are not claimed to commute.
- D6.10.3 *Compensators.* $\rho_R$ = marginal of $\theta$ on $R\in\{P,Y_0\}$, $T_R=W_{R,k}^{-1}(\rho_R^t)^{\otimes k}$ (positive power $0$ on the kernel). $\rho_R^{\otimes k}$ is invariant; in block $\lambda$ its eigenvalues are $\le d_\lambda^{-1}$ (eigenvalue repetition, D6.4.15), so $(\rho_R^t)^{\otimes k}\le d_\lambda^{-t}$ there ($(\rho_R^t)^{\otimes k}$ commutes with the label projectors since it is permutation-invariant). With $W_R^{-1}\le\poly(k)\,d_\lambda^t$ (D6.6): $\|T_R\|\le\poly(k)$ uniformly in $\theta$, including marginals of deficient rank.
- D6.10.4 *Commutation.* $T_P$ commutes with $W_{Px}$: $W_P^{-1}$ is central on the nested $P\subseteq Px$, and $(\rho_P^t)^{\otimes k}$ commutes with every simultaneous permutation on $Px$ (it commutes with $U_P$, $U_x$ is disjoint). $T_P$ commutes with $W_{xY_0}$: disjoint. Same for $T_{Y_0}$ with the roles of the two numerators swapped.
- D6.10.5 *Insertion.* $\widetilde\rho_R=\rho_R$ extended by eigenvalue $1$ on its kernel ($=\widehat\rho_R$ of D5.1). $P,Y_0$ disjoint $\Rightarrow$ the product of the two marginal support projectors fixes $\theta$. So $W_P^{-1}W_{Y_0}^{-1}\theta^{\otimes k}=T_PT_{Y_0}(\widetilde\rho_P^{-t}\widetilde\rho_{Y_0}^{-t})^{\otimes k}\theta^{\otimes k}$. Move $T_P,T_{Y_0}$ left (D6.10.4) and use D6.10.3: the norm squared is $\le\poly(k)\,\|W_{Px}W_{xY_0}(\widetilde\rho_P^{-t}\widetilde\rho_{Y_0}^{-t})^{\otimes k}\theta^{\otimes k}\|^2$ (squares absorbed into the polynomial).
- D6.10.6 *Integrals.* Expand $W_{Px}=\int(\sigma^t)^{\otimes k}d\zeta_{Px}$, $W_{xY_0}=\int(\tau^t)^{\otimes k}d\zeta_{xY_0}$ (both probability measures, D6.6). Triangle inequality (vector-valued integral) and $\|M^{\otimes k}\theta^{\otimes k}\|=\|M\theta\|^k$: bound by `replicas:move-one-copy`, $\poly(k)\sup_{\sigma,\tau}\|\sigma^t_{Px}\tau^t_{xY_0}\widetilde\rho_P^{-t}\widetilde\rho_{Y_0}^{-t}\theta\|^{2k}$.
- D6.10.7 *Reduction to densities.* A subdensity $\sigma=s\sigma'$, $s\le1$: $\sigma^t=s^t\sigma'^t$, so $\|\sigma'^t\cdots\|\ge\|\sigma^t\cdots\|$; the sup may be over density matrices.
- D6.10.8 *The one-copy word.* $P$ disjoint from $xY_0$ $\Rightarrow$ $\widetilde\rho_P^{-t}$ commutes with $\tau^t_{xY_0}$. Word: $\sigma_{Px}^{a/2}\widetilde\rho_P^{-a/2}\tau_{xY_0}^{a/2}\widetilde\rho_{Y_0}^{-a/2}\theta$ ($t=a/2$), the word of Lemma 5.1 with $U=Y_0$.
- D6.10.9 *Apply Lemma 5.1.* $\log\|\text{word}\|\le-a\eta_\theta/2+Ca^{5/4}\ell^2$. Then $\|\text{word}\|^{2k}\le\exp\{ka[-\eta_\theta+2Ca^{1/4}\ell^2]\}$, so $\langle\theta^{\otimes k},C_{x,k}^{-1}\theta^{\otimes k}\rangle\le\poly(k)\exp\{-ka[\eta_\theta-2Ca^{1/4}\ell^2]\}$. D6.10.1 turns this into the claim ($2C\ell^2\le C'\log^{C'}(e\dim x)$).
- D6.10.10 *Exchange.* $A_k(P,Y,F)=A_k(F,Y,P)$, so the move to $F$ follows by exchanging $P$ and $F$. $x=\varnothing$: $B_k=A_k$.

**Output.** Operator inequality tested against any symmetric density (§7: `Lemma 6.3 gives, for every unit θ`). Gain exponent $\eta_\theta$ and error $Ca^{1/4}\log^C(e\dim x)$ per copy.

**Standard?** Specific to this paper. Step D6.10.1 is the standard inverse-form Cauchy–Schwarz for positive operators.

**Pitfall.** Exponent: $C a^{5/4}\ell^2$ in the one-copy word becomes $Ca^{1/4}\ell^2$ after dividing by $a$ (the $ka$ prefactor). The two numerators $W_{Px}$, $W_{xY_0}$ overlap on $x$ and need not commute; only commutations used: nested or disjoint ones, plus $T_R$. Hypothesis is on $a\log(e\dim x)$, not on $a\log(e\dim V)$.

---

### 6.3 Scalar symbols, products and absolute values

#### D6.11 Def eq:resolution, eq:husimi — Coherent probability measure
*Source: 05-replicas.tex 596–613, `replicas:resolution` (599–600), `replicas:husimi` (604–605).*

**Statement.** $d\theta$ invariant probability measure on the unit sphere of $\mathcal V$.
$$\int P_{\theta,k}\,d\theta=D_k^{-1}\Pi_k.$$
Proof: the left side commutes with $U^{\otimes k}$ for all unitary $U$ (invariance of $d\theta$), is supported on $\mathcal S_k$, which is irreducible; so it is scalar there; trace of $P_{\theta,k}$ is $1$, giving $D_k^{-1}$. For a density $\sigma$ on $\mathcal S_k$:
$$d\mu_\sigma(\theta)=D_k\operatorname{Tr}(\sigma P_{\theta,k})\,d\theta,$$
a probability measure ($\int d\mu_\sigma=\operatorname{Tr}\sigma\Pi_k=1$). $\theta$ is a pure one-copy state, $\sigma$ any symmetric replica density; the same $\sigma$ defines the expectation and the mixing measure.

**Used from.** D6.1.

**Output.** $\mu_\sigma$ in D6.12, D6.14 (`replicas:finite-husimi`), D6.16, and §9 (08-scanner.tex 419).

**Standard?** Standard (Husimi/coherent measure of finite quantum de Finetti: Christandl–König–Mitchison–Renner 2007; Lewin–Nam–Rougerie 2015).

#### D6.12 Lemma 6.4 — Marked-copy scalar symbols
*Source: 05-replicas.tex statement 615–658, proof 660–845; equations `replicas:polynomial-symbol` (628–634), `replicas:skew-symbol` (636–641), `replicas:skew-bound` (651–656).*

**Statement.** Fix a partition $P,Y,F$ of $\mathcal V$, $0<t<1/4$, $a=2t$, and a one-copy operator $h$ supported on $PY$. With $A_k$ of D6.8 and $\bar h=k^{-1}\sum_jh^{(j)}$, on $\mathcal S_k$ define
$$O_k=A_k^{-1/2}\bar hA_k^{1/2},\qquad f_\theta=\langle\theta,\rho_P^t\rho_Y^{-t}h\rho_P^{-t}\rho_Y^t\theta\rangle,$$
$\rho_Q$ the $Q$-marginal of $\theta$, powers zero on kernels. Then:
1. $\sup_k\|O_k\|<\infty$ (bound depends on the fixed system and $h$).
2. For every fixed noncommutative polynomial $q$ in two variables:
$$\sup_\sigma\Bigl|\operatorname{Tr}\sigma\,q(O_k,O_k^\dagger)-\int q(f_\theta,\overline{f_\theta})\,d\mu_\sigma(\theta)\Bigr|\to0,$$
 $\sup$ over all density matrices on $\mathcal S_k$.
3. With $\mathcal D_k=|O_k|+|O_k^\dagger|-O_k-O_k^\dagger$, uniformly in $\sigma$:
$$\operatorname{Tr}\sigma\mathcal D_k=2\int(|f_\theta|-\operatorname{Re}f_\theta)\,d\mu_\sigma(\theta)+o_k(1).$$
4. If $0\le h\le I$ with a designated supporting subsystem of dimension $d_h$, $x=Y\cap\operatorname{supp}h$ (designated support may replace the minimal one), $Y_0=Y\setminus x$, $\eta_\theta=S_\theta(x|P)+S_\theta(x|Y_0)=I_\theta(x:F|P)=I_\theta(x:F|Y_0)$, and $a\log(ed_h)\le c$:
$$\operatorname{Tr}\sigma\mathcal D_k\le Ca^2\log^C(ed_h)\int\eta_\theta^{1/8}\,d\mu_\sigma(\theta)+o_k(1).$$
 Same with the outer parts exchanged.

**Used from.** D2.1; D5.1 (bracket powers: $\rho^t$ in $f_\theta$ is $\rho^{[t]}$); D6.4, D6.6, D6.8, D6.9, D6.11; D6.13–D6.16 (the proof stages); D5.15 = Lemma 5.3 (`lem:skew`): $\theta$ unit on $P,x,U,F$, $Y=xU$, $P=P_0P_1$, $0\le h\le I$ supported on $P_0x$, $d_h=\dim P_0\dim x$, $\ell_h=\log(ed_h)$, $\eta=I(x:F|U)=I(x:F|P)$, $f(z)=\langle\theta,\rho_P^{[z]}\rho_Y^{[-z]}h\rho_P^{[-z]}\rho_Y^{[z]}\theta\rangle$; universal $c,C$: for $0<a\ell_h\le c$, $t=a/2$: $|f(t)|-\operatorname{Re}f(t)\le Ca^2\ell_h^4\eta^{1/8}$.

**Proof.** Assembly; the four stages are D6.13–D6.16.
- D6.12.1 Items 1 and the replacement of $O_k$ by polynomial words $B_k$ with $\limsup\|O_k-B_k\|\le\varepsilon$: D6.13.
- D6.12.2 Symbol of words $\mathcal T_k(\text{word})$ on product vectors, uniformly in $\sigma$: D6.14 + D6.15.
- D6.12.3 Item 2 and removal of clipping, continuity and boundedness of $f_\theta$: D6.16.1–D6.16.4. Item 3: D6.16.5–D6.16.7.
- D6.12.4 Item 4: $f_\theta=f(t)$ of Lemma 5.3 with $a=2t$, $x=Y\cap\operatorname{supp}h$, $U=Y_0$ (so $Y=xU$), $P_0=P\cap\operatorname{supp}h$. Purity gives the two expressions for $\eta_\theta$. Enlarging $x$ to the designated support only enlarges $\ell_h$, allowed by Lemma 5.3. $a\log(ed_h)\le c\Rightarrow a\ell_h\le c$. Pointwise $|f_\theta|-\operatorname{Re}f_\theta\le Ca^2\log^4(ed_h)\eta_\theta^{1/8}$; integrate against $\mu_\sigma$ in item 3 (the factor $2$ is absorbed).
- D6.12.5 Exchange: the proof is unchanged after swapping $P,F$ ($A_k$ symmetric, D6.8).

**Output.** `replicas:skew-bound` is the cost $\eta_\theta^{1/8}$ and `replicas:relative-pin` the gain $\eta_\theta$, both against the same symmetric $\sigma$ (§7: 06-transport.tex 591, 721; §9: 08-scanner.tex 419).

**Standard?** Specific to this paper (product calculus for the symbol under a metric similarity transform). The finite-copy coherent-measure approximation and the symmetrization-by-injections idea are standard (D6.14, D6.15).

**Pitfall.** Order of limits: $\delta$ (clip) $\to$ polynomial approximation $\to k\to\infty$ $\to$ $\varepsilon,\delta\downarrow0$. Individual expectations of $O_k$ on product vectors do not control $|O_k|$; the product calculus (D6.15) is needed because $|O_k|=\sqrt{O_k^\dagger O_k}$ is a nonlinear function. $O_k$ is not normal in general. $h$ in items 1–3 is arbitrary on $PY$ (not positive); item 4 needs $0\le h\le I$.

#### D6.13 Step — Bounded approximation on symmetric inputs
*Source: 05-replicas.tex 666–710, `replicas:marked-word` (671–673), `replicas:inverse-innermost` (679–682), `replicas:polynomial-approximation` (703–705).*

**Statement.** (a) $O_k$ is, as a quadratic form on $\mathcal S_k$, the compression of $R_{P,k}R_{Y,k}^{-1}h^{(k)}R_{P,k}^{-1}R_{Y,k}$; $\sup_k\|O_k\|<\infty$. (b) For every $\varepsilon>0$ there are $\delta$, polynomials, and operators $B_k$ (compressions of a fixed polynomial word in marked operators on copy $k$ and stars $J_{Q,k}$), with common $\limsup_k\|B_k\|$ bound and $\limsup_k\|O_k-B_k\|\le\varepsilon$.

**Used from.** D6.4(4); D6.6 (`R-forward`, `R-inverse`, $\|R\|$, $\|R^{-1}z\|$); D6.8; D6.9.3.

**Proof.**
- D6.13.1 *Cancel $F$.* $A_k^{1/2}=W_P^{-1}W_F^{-1}W_Y$; $W_F$ commutes with $\bar h$ ($h$ on $PY$) and with $W_P,W_Y$, so $O_k=W_Y^{-1}W_P\bar hW_P^{-1}W_Y$.
- D6.13.2 *Marked copy.* For symmetric vectors $\langle z',\bar hz\rangle=\langle z',h^{(k)}z\rangle$ ($W^{\pm1}$ preserve $\mathcal S_k$). $W_{Q,k}=R_{Q,k}W_{Q,k-1}$, all commuting. The factors $W_{P,k-1},W_{Y,k-1}$ commute with $h^{(k)}$ (disjoint copies), with $R_P,R_Y$, and with each other: they cancel. Left: the compression of `replicas:marked-word`.
- D6.13.3 *Product decomposition.* $h=\sum c_P\otimes e_Y$, finite, expanding matrix units on the two parts of its support.
- D6.13.4 *Quadratic form.* $R_P,R_Y$ commute (disjoint); $R_Q$ self-adjoint. For symmetric unit $z$: $\langle z,R_PR_Y^{-1}c_Pe_YR_P^{-1}R_Yz\rangle=\langle R_Ye_Y^\dagger R_Y^{-1}z,R_Pc_PR_P^{-1}z\rangle$. Both inverses act directly on $z$.
- D6.13.5 *Bound.* $\|R_Ye_Y^\dagger R_Y^{-1}z\|\le\|R_Y\|\|e_Y\|\|R_Y^{-1}z\|\le C$ (D6.6 forward and vector bounds); same for $P$. Numerical radius $\le C$ (finite sum). $\|T\|\le2\sup_{\|z\|=1}|\langle z,Tz\rangle|$ (polarization) $\Rightarrow\sup_k\|O_k\|<\infty$.
- D6.13.6 *Clip.* Replace each $R_{Q,k}^{-1}$ by $\max(J_{Q,k},\delta)^{-t}$ via D6.6 (`R-inverse`): vector error, $\limsup\le C_{\mathcal V,t,h}\delta^{(1-2t)/2}$ uniformly on symmetric unit vectors. Then each forward ratio by $(J_{Q,k})_+^t$ via `R-forward`: operator-norm error $\to0$ at fixed $\delta$.
- D6.13.7 *Polynomials.* $J_{Q,k}$ has spectrum in $[-1,1]$ ($\|J\|\le(k-1)/k$, as an average of $k-1$ transpositions over $k$). Approximate $u\mapsto u_+^t$ and $u\mapsto\max(u,\delta)^{-t}$ uniformly on $[-1,1]$ by polynomials (Weierstrass). Polarization, applied after summing the finitely many product components, gives compressed polynomial words $B_k$ with `replicas:polynomial-approximation`.
- D6.13.8 *Order.* $\varepsilon$ fixes $\delta$, then the polynomials, then $k\to\infty$. Common $\limsup_k\|B_k\|$ bound: from the sup of the approximated functions on $[-1,1]$. Any $k$-threshold depending on the approximation is irrelevant to the $\limsup$s below.

**Output.** $B_k$ as the object of D6.14–D6.16; boundedness of $O_k$ for D6.16 (interval $[0,M^2]$).

**Standard?** Specific to this paper. Polarization inequality standard.

**Pitfall.** `replicas:R-inverse` is used only on symmetric input vectors (no operator bound for $R^{-1}$, D6.6). The inverses must stay adjacent to $z$ in D6.13.4; this is why the form is written as an inner product of two vectors.

#### D6.14 Step eq:finite-husimi, eq:uniform-husimi — Coherent measure on a fixed number of copies
*Source: 05-replicas.tex 712–747, `replicas:finite-husimi` (722–727), `replicas:uniform-husimi` (741–747).*

**Statement.** For $G$ on $\mathcal V^{\otimes m}$ let $\mathcal T_{k,m}(G)$ be the average over ordered injections $\iota:[m]\to[k]$ of $G$ placed on copies $\iota(1),\dots,\iota(m)$. It preserves $\mathcal S_k$; $k\ge m$: $\operatorname{Tr}\sigma\mathcal T_{k,m}(G)=\operatorname{Tr}\sigma^{(m)}G$ ($\sigma^{(m)}$ the $m$-copy marginal). Then
$$\int\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle d\mu_\sigma=\frac{D_k}{D_{k+m}}\operatorname{Tr}\bigl[(\sigma\otimes G)\Pi_{k+m}\bigr],$$
$$\Bigl|\operatorname{Tr}\sigma\mathcal T_{k,m}(G)-\int\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle d\mu_\sigma\Bigr|\le\frac{C_{d,m}\|G\|}{k},\ \text{uniformly in }\sigma.$$

**Used from.** D6.1; D6.11.

**Proof.**
- D6.14.1 *Identity.* $P_{\theta,k}\otimes|\theta^{\otimes m}\rangle\langle\theta^{\otimes m}|=P_{\theta,k+m}$, so $\int\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle D_k\operatorname{Tr}(\sigma P_{\theta,k})d\theta=D_k\operatorname{Tr}[(\sigma\otimes G)\int P_{\theta,k+m}d\theta]=\frac{D_k}{D_{k+m}}\operatorname{Tr}[(\sigma\otimes G)\Pi_{k+m}]$ by `replicas:resolution` at $k+m$ (Chiribella 2011, eq. (5)).
- D6.14.2 *Good permutations.* $\Pi_{k+m}=\frac1{(k+m)!}\sum_\pi U(\pi)$. Fraction of $\pi$ mapping all of the last $m$ indices into the first $k$: $(k)_m/(k+m)_m=1-O_m(k^{-1})$.
- D6.14.3 *Normal form.* For such $\pi$: write $\pi=\alpha\pi_0\beta$ with $\alpha,\beta\in S_k$ (permuting the first $k$ indices) and $\pi_0$ a product of $m$ disjoint swaps $(i_j\ k{+}j)$, $i_j$ distinct in $[k]$: reorder the old images of the last indices on the left and their old preimages on the right, then eliminate the remaining permutation among old indices. $U(\alpha)$ commutes with $G$ (disjoint copies) and $\sigma U(\alpha)=\sigma$, so $\operatorname{Tr}[(\sigma\otimes G)U(\pi)]=\operatorname{Tr}[(\sigma\otimes G)U(\pi_0)]$ (same for $\beta$).
- D6.14.4 *Value.* Swap trick $\operatorname{Tr}[(A\otimes B)\mathrm{SWAP}]=\operatorname{Tr}[AB]$ per swap: $\operatorname{Tr}[(\sigma\otimes G)U(\pi_0)]=\operatorname{Tr}\sigma^{(m)}G$ (partial trace).
- D6.14.5 *Rest.* Every other term has absolute value $\le\|\sigma\otimes G\|_1\le d^m\|G\|$ ($\|\sigma\|_1=1$, $\|G\|_1\le d^m\|G\|$), total weight $O_m(k^{-1})$. $D_k/D_{k+m}=1+O_{d,m}(k^{-1})$. $|\operatorname{Tr}\sigma^{(m)}G|\le\|G\|$. Sum: error $\le C_{d,m}\|G\|/k$.

**Output.** `replicas:uniform-husimi` is the only link between the replica expectation $\operatorname{Tr}\sigma(\cdot)$ and the scalar integral; used in D6.15 and D6.16.

**Standard?** Standard in finite de Finetti / mean-field arguments (Chiribella 2011; Christandl et al. 2007; Lewin–Nam–Rougerie 2015). The explicit coset normal form is reproduced here.

#### D6.15 Step eq:injection-product — Products after compression
*Source: 05-replicas.tex 749–811, `replicas:injection-product` (766–770).*

**Statement.** $\mathcal T_k(B)=\frac1{k!}\sum_\pi U(\pi)BU(\pi)^\dagger$ commutes with all $U(\pi)$, preserves $\mathcal S_k$, and $\Pi_kB\Pi_k|_{\mathcal S_k}=\mathcal T_k(B)|_{\mathcal S_k}$. For fixed $G,H$ on $m,n$ copies and $k$ large:
$$\bigl\|\mathcal T_{k,m}(G)\mathcal T_{k,n}(H)-\mathcal T_{k,m+n}(G\otimes H)\bigr\|\le C_{m,n}\|G\|\|H\|/k.$$
Consequently, for a polynomial word $B_k$ (D6.13) in marked operators and stars: $B_k^\dagger$ has the complex-conjugate symbol, products multiply symbols, and each star is replaced by the corresponding marginal density $\rho_Q$; uniformly in $\sigma$, for each fixed word.

**Used from.** D6.13, D6.14.

**Proof.**
- D6.15.1 *Averages.* $z\in\mathcal S_k$: $\Pi_kB\Pi_kz=\Pi_kBz=\frac1{k!}\sum U(\pi)Bz=\mathcal T_k(B)z$ since $U(\pi)^\dagger z=z$. Products of compressed words are therefore restrictions of products of their full averages (Raggio–Werner 1989, Lemma IV.1 for mean-field symmetrization).
- D6.15.2 *Injection product.* Independent uniform injections $\iota,\kappa$ of $m,n$ copies. Images intersect with probability $p=O_{m,n}(k^{-1})$. Conditional on disjoint images, $G^\iota H^\kappa=(G\otimes H)^{(\iota,\kappa)}$ and $(\iota,\kappa)$ is a uniform ordered injection of $m+n$ copies. The intersecting terms and the change of normalization each cost $\le p\|G\|\|H\|$.
- D6.15.3 *Star words.* A monomial with $r$ stars (all centered at the marked copy): expand $J_{Q,k}^r=k^{-r}\sum_{j_1,\dots,j_r<k}\prod(j_s\ k)$ interleaved with marked operators. Repeated donor indices carry total weight $O(k^{-1})$: norm $O(k^{-1})$ for that fixed word. Distinct donors: coefficient $(k-1)_r/k^r=1+O_r(k^{-1})$. After $\mathcal T_k$, center and donors form a uniformly relocated block of $1+r$ copies: $\mathcal T_k(\text{word})=\mathcal T_{k,1+r}(G_{\rm word})+O(k^{-1})$ with fixed $G_{\rm word}$.
- D6.15.4 *Several words.* Iterate D6.15.2: a product of words becomes one injection average on disjoint blocks, one separate center per word.
- D6.15.5 *Donor contraction.* On a product vector, a donor entering one partial swap gives $\operatorname{Tr}_{\rm donor}\bigl[(|\theta\rangle\langle\theta|)_{\rm donor}\sum_{a,b}(E_{ab})_{Q,\rm donor}\otimes(E_{ba})_{Q,\rm center}\bigr]=\sum_{ab}\operatorname{Tr}(\rho_QE_{ab})E_{ba}=(\rho_Q)_{\rm center}$. Tracing distinct donors successively keeps the operator order on each center.
- D6.15.6 *Multiplicativity.* $\langle\theta^{\otimes(m+n)},(G\otimes H)\theta^{\otimes(m+n)}\rangle=\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle\langle\theta^{\otimes n},H\theta^{\otimes n}\rangle$: separate centers multiply scalar expectations. Adjoint reverses order and conjugates scalars.
- D6.15.7 *Conclusion.* Apply `replicas:uniform-husimi` (D6.14) to $G_{\rm word}$: uniform-in-$\sigma$ symbols for each fixed polynomial word.

**Output.** Symbol map: star $J_{Q,k}\mapsto\rho_Q$, product $\mapsto$ product, adjoint $\mapsto$ conjugate. Input to D6.16.

**Standard?** Mean-field symmetrization by disjoint blocks: Raggio–Werner 1989; the star-word version and the donor contraction are specific to this paper.

**Pitfall.** Marked operators and stars of one word share one center; different words get separate centers only after averaging each word separately (D6.15.3), then multiplying through D6.15.2. Skipping this is the "expectation of the similarity transform alone" error flagged in the introduction (lines 8–11).

#### D6.16 Step — Removing clipping; absolute values; closing the lemma
*Source: 05-replicas.tex 813–845.*

**Statement.** Remaining proof of D6.12 after D6.13–D6.15: (i) $f_\theta$ is bounded and continuous in $\theta$; (ii) `replicas:polynomial-symbol` holds for every fixed $q$; $O_k^\dagger O_k$ and $O_kO_k^\dagger$ have symbol $|f_\theta|^2$; (iii) `replicas:skew-symbol`; (iv) `replicas:skew-bound`.

**Used from.** D6.12 (statement), D6.13, D6.14, D6.15; D5.15 = Lemma 5.3.

**Proof.**
- D6.16.1 *Tail of inverse powers.* For eigenvalues $p_i$ (with multiplicity) of any marginal density on $Q$: $\sum_{0<p_i<\delta}p_i^{1-2t}\le d_Q\delta^{1-2t}$ (each term $<\delta^{1-2t}$). For a pure $\theta$ with marginal $\rho_Q$: $\|\rho_Q^{-t}\mathbf 1_{(0,\delta)}(\rho_Q)\theta\|^2=\sum_{0<p_i<\delta}p_i^{-2t}\cdot p_i\le d_Q\delta^{1-2t}$, uniformly in $\theta$.
- D6.16.2 *Convergence.* Clipping replaces $\rho_Q^{-t}$ by $\max(\rho_Q,\delta)^{-t}$ (symbol of $\max(J_{Q,k},\delta)^{-t}$). On an eigenvalue $p<\delta$ the difference is $p^{-t}-\delta^{-t}\in(0,p^{-t})$; zero for $p\ge\delta$. So $\|(\rho_Q^{-t}-\max(\rho_Q,\delta)^{-t})\theta\|^2\le d_Q\delta^{1-2t}$ (D6.16.1). The clipped one-copy vectors of `replicas:inverse-innermost` converge uniformly in $\theta$ to the zero-kernel-power vectors as $\delta\to0$, with error $\le\sqrt{d_Q}\,\delta^{(1-2t)/2}$; so do their inner products: clipped symbols converge uniformly to $f_\theta$.
- D6.16.3 *Regularity.* Clipped symbols are continuous in $\theta$ (continuous functions of marginals); uniform limit $\Rightarrow$ $f_\theta$ bounded and continuous.
- D6.16.4 *Polynomial symbol.* Telescope fixed products using `replicas:polynomial-approximation` and the common $\limsup\|B_k\|$ bound: for $\varepsilon\to0$, $\delta\to0$ one gets `replicas:polynomial-symbol`.
- D6.16.5 *Squares.* $q(O,O^\dagger)=O^\dagger O$ and $OO^\dagger$ both have symbol $\overline{f_\theta}f_\theta=|f_\theta|^2$.
- D6.16.6 *Square root.* Choose $M$ with $\sup_k\|O_k\|\le M$ and $|f_\theta|\le M$. Spectra of $O^\dagger O$, $OO^\dagger$ and values $|f_\theta|^2$ lie in $[0,M^2]$. Approximate $\sqrt\cdot$ uniformly on $[0,M^2]$ by polynomials: symbols $|f_\theta|$ for $|O_k|$, $|O_k^\dagger|$ with arbitrarily small uniform expectation errors. No normality of $O_k$ is used.
- D6.16.7 *Skew symbol.* Combine with the linear terms ($O+O^\dagger\mapsto2\operatorname{Re}f_\theta$): `replicas:skew-symbol`.
- D6.16.8 *Skew bound.* D6.12.4.

**Output.** Items 2–4 of D6.12.

**Standard?** Specific to this paper. Uniform polynomial approximation of $\sqrt\cdot$ is Weierstrass.

#### D6.17 Step — Closing remark: gain and cost on the same states
*Source: 05-replicas.tex 847–853.*

**Statement.** The section supplies two compatible one-copy quantities: gain $\eta_\theta$ in `replicas:relative-pin`, cost $\eta_\theta^{1/8}$ in `replicas:skew-bound`. The operator bound can be tested against any symmetric density; the symbol error is uniform over those densities, with the prescribed order of limits. Both apply to the same density matrices when metric changes are averaged.

**Used from.** D6.10 (`relative-pin`); D6.12 (`skew-bound`).

**Output.** Licenses §7 to evaluate gain and cost for the same transported state and then average over histories.

**Standard?** Bookkeeping remark.

---

## Parameters and constants

| Symbol | Value / role | Fixed where |
|---|---|---|
| $\mathcal V$, $d$ | fixed finite-dim space, $d=\dim\mathcal V$; padded label length for every $Q$ | D6.1, D6.5 |
| $D_k$ | $\binom{k+d-1}{d-1}$, $D_k/D_{k+m}=1+O_{d,m}(k^{-1})$ | D6.1, D6.14.5 |
| $q$ | dimension of the tensor system in Lemma 6.1 ($=d_Q$ or $d$); $\le(k+1)^q$ labels | D6.4 |
| $l_i$ | $\lambda_i+q-i$ (D6.4); $\lambda_i+d-i$ (D6.6, full dimension) | D6.4, D6.6.12 |
| $t$ | $0<t<1/4$; only $1-2t>0$ used in D6.6 | D6.5 |
| $a$ | $2t$ | D6.5 |
| $c$ (D6.5) | $d+(1+t)\binom d2$; Gamma offset. Not the $c$ of Lemma 5.1 | D6.5 |
| $c$ (D6.10, D6.12) | universal constant of Lemma 5.1 in $a\log(e\dim x)\le c$, $a\log(ed_h)\le c$ | Lemma 5.1; D6.10, D6.12 |
| $2^q$ | factor in $p_{\lambda,i}\le2^ql_i/k$ | D6.4.19 |
| $\poly(k)$ | polynomial in $k$, degree and constants depend on fixed data only | conventions |
| $o_k(1)$ | uniform over densities on $\mathcal S_k$ | conventions |
| $C_{\mathcal V,t}$ | bound for $\|R^{-1}z\|$ and for the $\limsup$ in `R-inverse` | D6.6 |
| $\delta$ | $0<\delta<1$, clip level, error $C\delta^{(1-2t)/2}$ | D6.6, D6.13.6 |
| $\varepsilon$ | split $l_i/k=\varepsilon$ in D6.6.13; target error in D6.13 (distinct uses) | D6.6.13, D6.13.8 |
| exponent $5/4$ | $Ca^{5/4}\ell^2$, one-copy log-norm error | Lemma 5.1, D6.10.9 |
| exponent $1/4$ | $Ca^{1/4}\log^C(e\dim x)$, per-copy error in the pin | D6.10 |
| exponent $1/8$ | $\eta_\theta^{1/8}$ cost | Lemma 5.3, D6.12 |
| exponent $a^2$, $\log^C$ | $Ca^2\log^C(ed_h)$ prefactor of the skew bound ($\log^4$ from Lemma 5.3) | D6.12.4 |
| $1-2t$, $(1-2t)/2$ | exponents in inverse vector bound and its limsup | D6.6.14, D6.6.15 |
| $d_h$ | dimension of designated support of $h$ | D6.12 |
| $M$ | $\sup_k\|O_k\|$ and $\sup|f_\theta|$ bound | D6.16.6 |
| $m$ | number of copies in a fixed operator $G$; $m,n,r$ fixed | D6.14, D6.15 |

## Dependencies

Consumed:
- §2: D2.1, entropy notation $S_\theta(x|P)$, $I_\theta(x:F|P)$ (conditional entropy/CMI of a pure one-copy $\theta$).
- §5: D5.1 (hat/bracket powers); D5.5 = Lemma 5.1 (`lem:movement`) in D6.10; D5.15 = Lemma 5.3 (`lem:skew`) in D6.12.4/D6.16.8. Lemma 5.2 is not cited in §6.
- External: Schur–Weyl and Weyl characters (Etingof et al. 2011); Keyl–Werner 2001 (spectrum estimation); Vershik–Okounkov 2005 (star operator); Forrester–Ipsen 2018 (Muttalib–Borodin simplex integral); Chiribella 2011 eq. (5), Christandl–König–Mitchison–Renner 2007, Lewin–Nam–Rougerie 2015 (coherent measure / de Finetti); Raggio–Werner 1989 Lemma IV.1 (symmetrization by disjoint blocks); Stirling asymptotics.

Exported:
- §7 (transport): D6.5/D6.6 (`replicas:w-definition`, Lemma 6.2, common padding dimension $d$); D6.10 (Lemma 6.3, used as gain, 06-transport.tex 3, 333, 501); D6.12 (Lemma 6.4 absolute-value expression, 06-transport.tex 591, 721).
- §8 (comparators): D6.4(4),(5) (group dimension inequalities, 07-comparators.tex 467; `comparator:label-remainder` from Lemma 6.1(5), 221); the common-dimension Schur metrics of D6.5 (91); complement equality D6.4(2) (07-comparators.tex 35, 303–304).
- §9 (scanner): D6.4(2) (mirror of central functions to the complement, 08-scanner.tex 268); D6.11/D6.12 ($\mu_\sigma$, 08-scanner.tex 419); D6.9 (`replicas:leaf-floor`, 08-scanner.tex 460).
- §10, §11: not cited directly.
