# Digest of §10 — Amplifying the collar estimate

Source: `paper/sections/09-amplification.tex` (583 lines), label `sec:amplification`. Numbering: Lemma 10.1 (`lem:amplification-local-products`), Proposition 10.2 (`prop:amplification`); one shared counter. Cross-references use the section numbers of the file map: tail lemma = Lemma 3.1 (`lem:tail`, `02-initial.tex` 34–), collar = Proposition 9.6 (`prop:collar`, `08-scanner.tex` 808–).

## Section in one paragraph

Input: the sublinear collar bound $I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-\varepsilon}$ (Proposition 9.6), $\varepsilon=10^{-5}$. Output: for every $M$, $I_\Omega(X:J)\le C_Mn^{-M}$ for all $J$ outside $N_{2r}(S_0)$, with $r\lesssim n^{(1-\varepsilon)/\alpha}=o(n^\beta)$, $\beta=1-2\cdot10^{-6}$, $\alpha=p/(p+1)>1-10^{-6}$. Order: (1) fix exponents and the exact positive system $H_F=\sum k_i$ with $k_i\Omega=0$, gap $g$ (D10.1); (2) Lemma 10.1: products of the random contractions $G_i=(I-k_i)^{1/2}$ (Poisson clocks) can be cut to a ball around $S$ in expected norm, with an $e^{vt}$ light-cone loss; proved through unital channels, Lieb–Robinson-type oscillation propagation and Gronwall (D10.2); (3) the global gap gives $\mathbb E\|D(I-P_\Omega)\zeta\|^2\le e^{-gt}\|(I-P_\Omega)\zeta\|^2$ (D10.3); (4) Proposition 10.2: typical spectral projections give a restoring operator $R_0$ of norm $\le e^{(\mathcal I+3w)/2}$ with exactly computable adjoint action and ground component $\le1$ (D10.5–D10.10); running the constraint clocks for time $t_*\sim\mathcal I+w+K\log n$ kills the excited part, localizes to $N_{2r}(S_0)$, keeps the norm $\le1+3n^{-K}$ (D10.11–D10.13); polar decomposition replaces the result by a local unitary $U'$ with $\|U'\phi-\eta\|\le Cn^{-K/2}$ (D10.14); continuity of mutual information on the reference copy $e'$ costs only $\log\dim e'\le Cn^2$ (D10.15); radii and containment in $A$ (D10.16).

Notation. $\Lambda$ finite, $d_\Lambda$ graph metric of the induced graph ($=\infty$ across components), $N_l(a)=\{y:d_\Lambda(y,a)\le l\}$, $N_r(S)=\{y:d_\Lambda(y,S)\le r\}$. $P_\Omega=|\Omega\rangle\langle\Omega|$. Spectator systems carry the identity for every physical operator. $I_\Omega(X:J)$ is the mutual information in the original ground state $\Omega$ (§2 D2.1). $\log$ natural. $C,c$ generic (§2 D2.13), independent of $|\Lambda|$ and of spectator dimensions in Lemma 10.1.

---

## 10.0 Standing choices

#### D10.1 Def — Standing exponents and the fresh positive system
*Source: 09-amplification.tex 14–30; `eq:amplification-exponents` (15–18), `eq:amplification-positive-system` (22–26).*

**Statement.**
$$\varepsilon=10^{-5},\qquad\beta=1-2\cdot10^{-6},\qquad\alpha=\frac p{p+1}>1-10^{-6}\quad(\text{i.e. }p\ge10^6),$$
$p$ a fixed integer. Apply Proposition 4.3 with this $p$. Then $H_F=\sum_ik_i$ with
$$0\le k_i\le I,\quad k_i\Omega=0,\quad H_F\ge g(I-P_\Omega),$$
$g>0$ independent of $\Lambda$. The scanner's truncated Hamiltonian ($p=1$, §4 D4.11) is not used in this section. All neighborhoods are graph neighborhoods: $N_r(S)=N_r^\Lambda(S)$.

**Used from.** D4.6 (Proposition 4.3: $k_i,g,\alpha=p/(p+1)$, anchors $a_i$, tails $\|k_i-E_{i,l}k_i\|\le Ce^{-cl^\alpha}$); D4.2 ($E_{i,l}$).

**Output.** $\alpha\to1$ gives $r\sim t_*^{1/\alpha}=o(n^\beta)$ (D10.16). $k_i\Omega=0$, $g$: D10.2, D10.3.

**Standard?** Specific to this paper.

**Pitfall.** $p\ge10^6$ is only implicit in "$\alpha>1-10^{-6}$". $C,c,g$ of D4.6 depend on $p$, fixed once for the section.

---

## 10.1 Localizing products of positive constraints

#### D10.2 Lemma 10.1 — Local constraint products
*Source: 09-amplification.tex 42–235. Label `lem:amplification-local-products`. Displays `eq:amplification-product-truncation` (59–62), `eq:amplification-product-omission` (66–69).*

**Statement.** Let $k_i$ be positive contractions anchored at $a_i\in\Lambda$, bounded multiplicity (at most $\mu$ labels per anchor), with
$$\|k_i-E_{i,l}k_i\|\le Ce^{-cl^\alpha}\quad(l\ge0),$$
$E_{i,l}$ the conditional expectation onto $N_l(a_i)$. Put $G_i=(I-k_i)^{1/2}$, $K_i=k_i^{1/2}$. Fix $t\ge0$, integer $r\ge1$, nonempty $S\subseteq\Lambda$. At each label run an independent rate-one Poisson clock on $[0,t]$. In occurrence order, later factors on the left:
- $D$ = product of all $G_i$ over events;
- $D_{\rm ret}$ = product over events with $d_\Lambda(a_i,S)\le r$ only;
- $L$ = product of $G_{i,r}=(I-E_{i,r}k_i)^{1/2}$ over the same retained events.

There are constants $C,c,v>0$, independent of $|\Lambda|$ and of spectator dimensions, with
$$\mathbb E\|D_{\rm ret}-L\|\le Ct|S|(1+r)^2e^{-cr^\alpha}.\tag{A}$$
$L$ is a contraction supported on $N_{2r}(S)$. If $k_i\Omega=0$ and $B$ is supported on $S\cup$ spectators, then for every unit spectator vector $\xi$,
$$\mathbb E\|(D-D_{\rm ret})B(\Omega\otimes\xi)\|\le Ct|S|\,\|B\|\,e^{vt-cr^\alpha}.\tag{B}$$
(A), (B) hold on the same clock space.

**Used from.** D4.2 ($E_{i,l}$: positive, unital, fixes operators on $N_l(a_i)$); D4.10 (Lemma 4.4); D4.9 (Hölder-$\tfrac12$, behind the root tails); D2.7 (ball count $v_l=1+2l(l+1)\le3(1+l)^2$); D2.8 (at most $\mu_R$ labels per anchor). D4.10 applies to abstract $k_i$: its proof uses only $0\le k_i\le I$ and the tail.

**Proof.** Notation: $\mathcal E_i(B)=G_iBG_i+K_iBK_i$, $\mathcal E_{i,l}$ likewise with $G_{i,l},K_{i,l}$ ($K_{i,l}=(E_{i,l}k_i)^{1/2}$). Anchors per radius: $\#\{i:y\in N_l(a_i)\}\le\mu v_l\le C(1+l)^2$.

- D10.2.1 *Channels on the ground vector* (tex 74–91; `eq:amplification-channel-vector` 83–85). $k_i\Omega=0\Rightarrow K_i\Omega=0$, $G_i\Omega=\Omega$ (functional calculus). Hence for every operator $C'$ and spectator $\xi$
$$\mathcal E_i(C')(\Omega\otimes\xi)=G_iC'G_i(\Omega\otimes\xi)+K_iC'K_i(\Omega\otimes\xi)=G_iC'(\Omega\otimes\xi).$$
Iterating along events in order, $(\mathcal E_{i_m}\circ\dots\circ\mathcal E_{i_1})(B)(\Omega\otimes\xi)=G_{i_m}\cdots G_{i_1}B(\Omega\otimes\xi)$. Write $\mathcal E_{\rm full},\mathcal E_{\rm ret}$ for the channel products over all / retained events; on $\Omega\otimes\xi$ they give $D$, $D_{\rm ret}$.
- D10.2.2 *Channel approximation, no dimension factor* (tex 91–99; `eq:amplification-channel-approximation`). D4.10.6: $\|\mathcal E_i-\mathcal E_{i,l}\|_{\rm cb}\le Ce^{-cl^\alpha}$, spectators included.
- D10.2.3 *Shell differences* (tex 101–106). $\mathcal E_{i,-1}=\mathrm{id}$, $\Delta_{i,l}=\mathcal E_{i,l}-\mathcal E_{i,l-1}$. For $l\ge1$: $\|\Delta_{i,l}\|_{\rm cb}\le\|\mathcal E_{i,l}-\mathcal E_i\|_{\rm cb}+\|\mathcal E_i-\mathcal E_{i,l-1}\|_{\rm cb}\le C'e^{-cl^\alpha}$, using $l^\alpha-(l-1)^\alpha\le1$. For $l=0$: both maps are contractions, $\|\Delta_{i,0}\|_{\rm cb}\le2$. Enlarge $C$: $\|\Delta_{i,l}\|_{\rm cb}\le Ce^{-cl^\alpha}$ for all $l\ge0$ (`eq:amplification-channel-shells`). Telescoping: $\mathcal E_i-\mathrm{id}=\sum_{l\ge0}\Delta_{i,l}$ (norm-convergent) and $\mathcal E_i=\mathcal E_{i,m-1}+\sum_{l\ge m}\Delta_{i,l}$ for every $m\ge0$.
- D10.2.4 *Component support* (tex 133–137). Let $\Gamma$ be the component of $a_i$ and $l\ge\operatorname{diam}\Gamma$. Then $N_l(a_i)=\Gamma$, so $E_{i,l}$ is the same map for all such $l$ and $\|k_i-E_{i,l}k_i\|$ is constant in $l$. It is $\le Ce^{-cl^\alpha}\to0$, hence $0$: $k_i=E_{i,l}k_i$ is supported on $\Gamma$. So $k_i,G_i,K_i,\mathcal E_i$ act in $\Gamma$ and cannot change $d_y$ for $y$ in another component.
- D10.2.5 *Oscillation* (tex 107–113). $d_y(B)=\sup_{U_y\ \rm unitary}\|[U_y,B]\|$, $U_y$ on the on-site space at physical $y$. Facts: $d_y(C')\le2\|C'\|$; $d_y=0$ if $B$ commutes with all operators at $y$; $\|B-U_yBU_y^*\|=\|[B,U_y]\|\le d_y(B)$.
- D10.2.6 *Shell oscillation* (tex 107–121; `eq:amplification-shell-oscillation`): $\|\Delta_{i,l}(B)\|\le Ce^{-cl^\alpha}\sum_{z\in N_l(a_i)}d_z(B)$.
  - Both $\mathcal E_{i,l}$, $\mathcal E_{i,l-1}$ fix every operator commuting with the algebra on $N_l(a_i)$ (for $B'$ in the commutant: $G B'G+KB'K=B'(G^2+K^2)=B'$; supports are inside $N_l(a_i)$; $l=0$: identity). So $\Delta_{i,l}$ vanishes on that commutant, also after tensoring with spectators.
  - Let $\mathcal T_z(B)=\int U_zBU_z^*\,dU_z$. For $Q=N_l(a_i)=\{z_1,\dots,z_m\}$ put $\widehat B=\mathcal T_{z_m}\cdots\mathcal T_{z_1}B$, which commutes with the algebra on $Q$. $\mathcal T_{z'}$, $z'\ne z$, commutes with conjugation by $U_z$, so $d_{z_j}(\mathcal T_{z_{j-1}}\cdots\mathcal T_{z_1}B)\le d_{z_j}(B)$, and $\|B-\widehat B\|\le\sum_jd_{z_j}(B)$ (telescoping, each step $\le d_{z_j}$ of the intermediate operator).
  - $\Delta_{i,l}(B)=\Delta_{i,l}(B-\widehat B)$, so $\|\Delta_{i,l}B\|\le\|\Delta_{i,l}\|_{\rm cb}\sum_{z\in Q}d_z(B)$. Spectator factors of $B$ untouched: hence cb norm.
- D10.2.7 *Oscillation increment* (tex 123–137; `eq:amplification-oscillation-increment`): with $m=d_\Lambda(a_i,y)$,
$$d_y(\mathcal E_iB)\le d_y(B)+C\sum_{l\ge m}e^{-cl^\alpha}\sum_{z\in N_l(a_i)}d_z(B).$$
  - $m<\infty$: $\mathcal E_i=\mathcal E_{i,m-1}+\sum_{l\ge m}\Delta_{i,l}$ (D10.2.3). $\mathcal E_{i,m-1}$ has support $N_{m-1}(a_i)\not\ni y$, so $U_y\mathcal E_{i,m-1}(B)U_y^*=\mathcal E_{i,m-1}(U_yBU_y^*)$. With contractivity: $\|[U_y,\mathcal E_{i,m-1}B]\|=\|\mathcal E_{i,m-1}(B-U_yBU_y^*)\|\le\|[U_y,B]\|$, so $d_y(\mathcal E_{i,m-1}B)\le d_y(B)$. Remainder: $d_y(\cdot)\le2\|\cdot\|$ and D10.2.6; absorb $2$ in $C$. $m=0$: $\mathcal E_{i,-1}=\mathrm{id}$.
  - $m=\infty$: other component (D10.2.4), $d_y$ does not increase.
- D10.2.8 *Kernel* (tex 139–160). For retained labels, $A_{yz}=C\sum_{i\ \rm ret}\sum_{l\ge0}e^{-cl^\alpha}\mathbf 1_{\{y,z\in N_l(a_i)\}}$. Since $y\in N_l(a_i)\iff l\ge d_\Lambda(a_i,y)$, D10.2.7 summed over a retained label reads $\le d_y(B)+\sum_zA_{yz}d_z(B)$. Weighted row sum (`eq:amplification-weighted-kernel`): for some $a>0$,
$$\sup_y\sum_{z:\,d_\Lambda(y,z)<\infty}A_{yz}e^{a\,d_\Lambda(y,z)^\alpha}\le v.$$
At radius $l$: $\le C(1+l)^2$ labels with $y\in N_l(a_i)$, $\le C(1+l)^2$ sites $z\in N_l(a_i)$, $d_\Lambda(y,z)\le2l$. So the sum is $\le C\sum_{l\ge0}(1+l)^4e^{-cl^\alpha+a(2l)^\alpha}$, finite for $a2^\alpha<c$ (e.g. $a=c/4$). $v$ is this sum. No entries between components.
- D10.2.9 *Propagation* (tex 162–186; `eq:amplification-propagation`): $\mathbb E\,d_y(B_u)\le2\|B\|e^{vu-a\,d_\Lambda(y,S)^\alpha}$ for $u\in[0,t]$, where $B_u$ is the operator after the retained events up to time $u$ starting from $B$ (events apply $\mathcal E_i$ to the current operator).
  - Jump formula for a pure-jump process with rate one per retained label: $\tfrac d{du}\mathbb E\,d_y(B_u)=\sum_{i\ \rm ret}\mathbb E[d_y(\mathcal E_iB_u)-d_y(B_u)]\le\sum_zA_{yz}\mathbb E\,d_z(B_u)$ (D10.2.7–D10.2.8). Everything is finite for fixed $\Lambda$; $d_y\le2\|B\|$.
  - Initial data: $B$ on $S\cup$ spectators $\Rightarrow d_y(B)\le2\|B\|\mathbf 1_S(y)$.
  - On components meeting $S$ set $f_u=\sup_ye^{a d(y,S)^\alpha}\mathbb E\,d_y(B_u)$. Triangle inequality and $(s+t)^\alpha\le s^\alpha+t^\alpha$ ($0<\alpha<1$): $d(y,S)^\alpha-d(z,S)^\alpha\le d(y,z)^\alpha$. Hence $e^{ad(y,S)^\alpha}\sum_zA_{yz}\mathbb E\,d_z(B_u)\le\sum_zA_{yz}e^{ad(y,z)^\alpha}f_u\le vf_u$. Integrating, $f_u\le f_0+v\int_0^uf_s\,ds$; Gronwall: $f_u\le f_0e^{vu}\le2\|B\|e^{vu}$.
  - Components not meeting $S$: $d_y(B)=0$ initially, no kernel entries link components, stays $0$.
- D10.2.10 *Omitted event* (tex 188–201; `eq:amplification-omitted-event`): for $i$ with $d=d_\Lambda(a_i,S)>r$, $d<\infty$,
$$\mathbb E\|(\mathcal E_i-\mathrm{id})B_u\|\le C\|B\|e^{vu-c'd^\alpha}.$$
By D10.2.3 and D10.2.6, $\|(\mathcal E_i-\mathrm{id})B_u\|\le C\sum_{l\ge0}e^{-cl^\alpha}\sum_{z\in N_l(a_i)}d_z(B_u)$.
  - $l\le d/2$: $z\in N_l(a_i)\Rightarrow d(z,S)\ge d-l\ge d/2$; D10.2.9 gives $\mathbb E\,d_z\le2\|B\|e^{vu-a(d/2)^\alpha}$; at most $C(1+l)^2$ sites; $\sum_l(1+l)^2e^{-cl^\alpha}<\infty$. Contribution $\le C\|B\|e^{vu-a(d/2)^\alpha}$.
  - $l>d/2$: use $d_z(B_u)\le2\|B_u\|\le2\|B\|$ (contractions) and the ball count: $C\|B\|\sum_{l>d/2}(1+l)^2e^{-cl^\alpha}\le C\|B\|e^{-c'd^\alpha}$.
  - Both $\le C\|B\|e^{vu-c'd^\alpha}$ for a smaller $c'>0$. $d=\infty$: left side $0$.
- D10.2.11 *Coupling; omission of distant events* (tex 203–218; `eq:amplification-channel-omission`): $\mathbb E\|\mathcal E_{\rm full}(B)-\mathcal E_{\rm ret}(B)\|\le Ct|S|\|B\|e^{vt-c''r^\alpha}$.
  - Same clocks. Events $e_1,\dots,e_N$ in order, $F_j=\mathcal E_{e_j}$, $R_j=F_j$ if retained else $\mathrm{id}$. Then $F_N\cdots F_1-R_N\cdots R_1=\sum_jF_N\cdots F_{j+1}(F_j-R_j)R_{j-1}\cdots R_1$; only omitted $j$ contribute, with $F_j-R_j=\mathcal E_{e_j}-\mathrm{id}$.
  - Later $F$'s are contractions: term norm $\le\|(\mathcal E_{e_j}-\mathrm{id})(R_{j-1}\cdots R_1B)\|$. The retained history depends only on retained clocks, independent of the omitted clocks. Campbell's formula for the rate-one Poisson process of label $i$: $\mathbb E\sum_{\text{events of }i}f=\int_0^t\mathbb E f(B_u)\,du$.
  - So the expectation is $\le\sum_{i\ \rm omitted,\,d_i<\infty}\int_0^tC\|B\|e^{vu-c'd_i^\alpha}du\le Ct\|B\|e^{vt}\sum_{d>r}\#\{i:d_i=d\}e^{-c'd^\alpha}$ with $\#\{i:d_i=d\}\le C|S|(d+1)^2$ (anchors in $N_d(S)$, ball count, multiplicity). $\sum_{d>r}(d+1)^2e^{-c'd^\alpha}\le Ce^{-c''r^\alpha}$.
  - Bounds $\mathbb E\|\cdot\|$, not $\|\mathbb E\,\cdot\|$.
- D10.2.12 *Proof of (B)* (tex 220–226). Evaluate $\mathcal E_{\rm full}(B)-\mathcal E_{\rm ret}(B)$ on $\Omega\otimes\xi$ ($\|\Omega\otimes\xi\|=1$); D10.2.1 turns it into $(D-D_{\rm ret})B(\Omega\otimes\xi)$. Rename $c''\to c$.
- D10.2.13 *Proof of (A) and support* (tex 228–234). Retained labels: anchors in $N_r(S)$, so $\le C|S|(1+r)^2$ labels; expected number of retained events $\le Ct|S|(1+r)^2$. $D_{\rm ret}$ and $L$ have the same events: $\|\prod G_{i_j}-\prod G_{i_j,r}\|\le\sum_j\|G_{i_j}-G_{i_j,r}\|\le N\cdot Ce^{-cr^\alpha}$ (contractions, telescoping; D4.10 root tail at $l=r$). Take $\mathbb E$. Support: retained $d(a_i,S)\le r$, $G_{i,r}$ supported on $N_r(a_i)\subseteq N_{2r}(S)$; each $G_{i,r}$ is a positive contraction.

**Output.** D10.12 uses (A) and (B) with $S=S_0$, $B=B_0$, $\xi=|00\rangle_{s'e'}$. $L$ ($L'$ there) is polar-decomposed in D10.14.

**Standard?** Mechanism: dissipative Lieb–Robinson, Barthel–Kliesch, PRL 108 (2012), Theorems 1–2. Specific here: expected norm on coupled clock realizations, oscillation $d_y$, weighted Gronwall with stretched-exponential kernel, spectator-independent cb bounds.

**Pitfall.**
- Unitality of $\mathcal E_i$ is essential: $C'\mapsto G_iC'G_i$ alone need not fix operators on a disjoint system (D10.2.6). Vector identity D10.2.1 recovers the non-unital products only on $\Omega\otimes\xi$.
- (B) loses $e^{vt}$ (light cone): need $cr^\alpha\gtrsim vt$, $r\gtrsim t^{1/\alpha}$.
- (A) has no $e^{vt}$: telescoping only, no propagation.
- $\mathcal E_{i,l}$ does not preserve $k_i\Omega=0$; only exact $G_i,K_i$ enter (B).

#### D10.3 Step — Excited-state decay $\mathbb E\|D(I-P_\Omega)\zeta\|^2\le e^{-gt}\|(I-P_\Omega)\zeta\|^2$
*Source: 09-amplification.tex 237–253; `eq:amplification-excited-decay` (242–245).*

**Statement.** Under D10.1, for every vector $\zeta$ including spectators ($P_\Omega\to P_\Omega\otimes I$), with $D$ the product of all $G_i$ over the clocks of D10.2 on $[0,t]$:
$$\mathbb E\|D(I-P_\Omega)\zeta\|^2\le e^{-gt}\|(I-P_\Omega)\zeta\|^2.$$

**Used from.** D10.1 ($k_i\Omega=0$, $H_F\ge g(I-P_\Omega)$); definition of $G_i$ in D10.2.

**Proof.**
- D10.3.1 $G_i=G_i^*$, $G_i\Omega=\Omega\Rightarrow G_i$ preserves $\Omega^\perp$ ($\langle\Omega,G_i\chi\rangle=\langle G_i\Omega,\chi\rangle=0$ for $\chi\perp\Omega$), so $[G_i,P_\Omega]=0$. Then $D(I-P_\Omega)\zeta=D\zeta_\perp$ stays in $\Omega^\perp$; set $\psi_u$ = state after events up to $u$, $\psi_0=\zeta_\perp$.
- D10.3.2 At an event of label $i$: $\|G_i\psi\|^2=\langle\psi,(I-k_i)\psi\rangle=\|\psi\|^2-\langle\psi,k_i\psi\rangle$.
- D10.3.3 Rate one per label: $\tfrac d{du}\mathbb E\|\psi_u\|^2=-\sum_i\mathbb E\langle\psi_u,k_i\psi_u\rangle=-\mathbb E\langle\psi_u,H_F\psi_u\rangle\le-g\,\mathbb E\|\psi_u\|^2$, since $\psi_u\perp\Omega$ and $H_F\ge g(I-P_\Omega)$. Gronwall: $\mathbb E\|\psi_t\|^2\le e^{-gt}\|\zeta_\perp\|^2$.

**Output.** D10.12: with $\zeta=R_0\phi$, $\mathbb E\|D(I-P_\Omega)\zeta\|^2\le M_0^2e^{-gt_*}$.

**Standard?** Mechanism: detectability-lemma products (Anshu–Arad–Vidick 2016, §III). Random-contraction version with global gap $H_F\ge g(I-P_\Omega)$: specific to this paper.

**Pitfall.** All labels (full $D$, not $D_{\rm ret}$) are used; the gap is global, locality comes only from D10.2. $\|\cdot\|^2$ decays, so Markov applies to the squared norm (D10.12).

---

## 10.2 A local unitary from a small collar cost

#### D10.4 Proposition 10.2 — Amplification
*Source: 09-amplification.tex 261–576 (statement 261–296, proof 298–576). Label `prop:amplification`. Displays `eq:amplification-input-information` (271–273), `eq:amplification-radius` (276–279), `eq:amplification-output` (282–284), `eq:amplification-cut-clearance` (290–292).*

**Statement.** Fix $C_0>0$; $\varepsilon,\beta,\alpha$ as in D10.1. Let $n\ge2$, $L=\lfloor n^{1-\varepsilon}\rfloor$, and
$$X=A\cap T,\quad S_0=A\cap T_L,\quad Y=S_0\setminus X,\quad Z'=\Lambda\setminus S_0,\qquad T_L=T+[-L,L]^2_{\mathbb Z}.$$
Assume $|S_0|\le C_0n^2$; the cuts of $X$, $Y$, $S_0$ each have $\le C_0n$ crossing edges; and
$$\mathcal I:=I_\Omega(X:Z')\le C_0n^{1-\varepsilon}.$$
For every integer $M\ge1$ and all sufficiently large $n$ there is an integer $r$ with
$$r\le C_Mn^{(1-\varepsilon)/\alpha},\qquad L+2r=o(n^\beta),$$
and, simultaneously for every physical $J\subseteq\Lambda\setminus N_{2r}(S_0)$,
$$I_\Omega(X:J)\le C_Mn^{-M}.$$
Same for any subset of $X$ in place of $X$. Constants and threshold depend on $C_0,M$ (and the standing data of D2.13, $p$), not on $\Lambda,A,T$. If in addition $\operatorname{dist}_\infty(T,Z)>L+n^\beta$, $Z$ the endpoint set of the original cut, then $N_{2r}(S_0)\subseteq A$; so $J$ may contain all of $\Lambda\setminus A$.

**Used from.** D10.1; D10.2 (Lemma 10.1); D10.3; D3.1 (Lemma 3.1, `lem:tail`; $\mathcal B$ as in D3.1); D2.4 (Lemma 2.1 continuity); D2.5 (pure-state trace distance); D2.2 (SSA consequences, purity); D2.9 (crossing count $\le2v_R\mu_R|\partial_\Lambda D|$); hypotheses from Proposition 9.6 (`prop:collar`); internal steps D10.5–D10.16.

**Proof (skeleton; details in the Steps below).**
- D10.4.1 $X=\varnothing$: $I_\Omega(\varnothing:J)=0$, take $r=1$. Assume $X\ne\varnothing$ below. Constructions keep the physical system fixed; all estimates are uniform in $|\Lambda|$.
- D10.4.2 Fix $K\ge1$; typical projections $P_X,T_Y,Q$ with failure $\le\delta=n^{-2K}$ (D10.5).
- D10.4.3 States $\phi$ (target moved to $e'$) and $\eta$ ($e'$ purified by $s'$, independent of physics) (D10.6).
- D10.4.4 Restoring operator $R_0$ and column operator $B_0$, $R_0\phi=B_0(\Omega\otimes|00\rangle)$ (D10.7).
- D10.4.5 Three facts: $\|R_0\|,\|B_0\|\le M_0=e^{(\mathcal I+3w)/2}$ (D10.8); $R_0^\dagger(L')^\dagger\eta$ exact, error $\le3\sqrt\delta+\|(L')^\dagger\Omega-\Omega\|$, no $M_0$ (D10.9); $\|P_\Omega R_0\phi\|\le1$ (D10.10).
- D10.4.6 Times $t_*$, radius $r$; clocks of Lemma 10.1; good realization with three bounds $\le n^{-K}$ (D10.11, D10.12).
- D10.4.7 $\|L'R_0\phi\|\le1+3n^{-K}$, $\|R'^\dagger\eta-\phi\|\le4n^{-K}$, $\|R'\phi-\eta\|\le Cn^{-K/2}$ for $R'=L'R_0$ (D10.13).
- D10.4.8 Polar decomposition: $\|U'\phi-\eta\|\le Cn^{-K/2}$ (D10.14).
- D10.4.9 Continuity on $e'$: $I_\Omega(X:J)\le Cn^{2-K/4}$; $K\ge4(M+3)$ (D10.15).
- D10.4.10 Radius bounds and $N_{2r}(S_0)\subseteq A$ (D10.16).

**Output.** §11 (`10-geometry.tex` 71, 809–837): radius $r_i$ per tile; $n^{-M}$ bound uniform in $J$ and for subsets of $X$; $L+2r=o(n^\beta)$ keeps enlarged neighborhoods inside $n^\beta$-clearance.

**Standard?** Specific to this paper (typical-subspace restoring operator, constraint-product suppression, polar replacement by a local unitary on a reference copy). Ingredients standard: Schmidt decomposition, spectral concentration of surprisal, polar decomposition, continuity of conditional entropy.

**Pitfall.** Order of quantifiers: $M$ first; then $K:=\lceil4(M+3)\rceil$ (D10.15), which fixes $\delta=n^{-2K}$; then threshold $n_0$ (so that $Ce^{-cn^{1/10}}\le n^{-2K}$ and the three failure probabilities of D10.12 sum $<1$); then $C,C'$ (D10.11) depending on $g,v,c,K$; then $r$, which depends on the actual $\mathcal I\le C_0n^{1-\varepsilon}$. $r$ is not uniform over inputs except through its upper bound.

### Steps inside the proof of Proposition 10.2

#### D10.5 Step — Typical projections
*Source: 09-amplification.tex 304–322; `eq:amplification-typical-error` (317–319).*

**Statement.** Put $w=n^{3/5}$, $\delta=n^{-2K}$. For the three cuts $X$, $Y$, $S_0$ let $P_X$, $T_Y$, $Q_{S_0}$ be the spectral projections of $\rho_X$, $\rho_Y$, $\rho_{S_0}$ onto the positive eigenvalues $p$ with $-\log p\in[S-w,S+w]$ ($S=S(X),S(Y),S(S_0)$ respectively). For $n$ large (given $K$),
$$\|(I-P_X)\Omega\|^2,\ \|(I-T_Y)\Omega\|^2,\ \|(I-Q_{S_0})\Omega\|^2\le\delta,$$
so each is $\le\sqrt\delta=n^{-K}$ in norm. A trivial subsystem has projection $I$. Inverse eigenvalues below are on the selected spectrum only.

**Used from.** D3.1 (Lemma 3.1, `eq:initial-tail-probability`) applied to $H$ ($c_0=J$, $g_0=\Delta$, $\vartheta=J/\Delta$; D3.2); D2.9; D2.8 and D1.2 (support dimensions $d_i\le q^{v_R}$; D3.2).

**Proof.**
- D10.5.1 Crossing terms: $\le2v_R\mu_R\cdot C_0n=Cn$ (D2.9) each cut; $\log^2(ed_i)\le\log^2(eq^{v_R})$. So $\mathcal B\le1+Cn\le Cn$.
- D10.5.2 $\langle\Omega,(I-P_X)\Omega\rangle=\Pr\{|\mathsf K-S|>w\}$ ($\mathsf K$ = surprisal variable of Lemma 3.1, not the integer $K$). Lemma 3.1: $\le2e^{e/2}\exp(-w/(32\sqrt{(1+\vartheta)\mathcal B}))\le C\exp(-cn^{3/5-1/2})=C\exp(-cn^{1/10})$.
- D10.5.3 For fixed $K$ and $n\ge n_0(K)$: $C\exp(-cn^{1/10})\le n^{-2K}$. $\|(I-P)\Omega\|^2=\langle\Omega,(I-P)\Omega\rangle\le\delta$.
- D10.5.4 Non-invertibility: marginals may have kernels; only $p_x>0$ and $x$ selected are inverted.

**Output.** D10.8 (spectral inequalities $p_x^{-1}\le e^{S(X)+w}$, $Q\le e^{S(S_0)+w}\rho_{S_0}$, $T_0\rho_YT_0\le e^{-S(Y)+w}T_0$); D10.9 (the $3\sqrt\delta$); D10.10 is independent of $w$.

**Standard?** Lemma 3.1 (surprisal concentration): specific to this paper. Typical-spectrum projection: standard.

**Pitfall.** Projections are of the original $\rho$'s in $\Omega$, not of $H_F$. $w=n^{3/5}$ exceeds $\sqrt{\mathcal B}=O(n^{1/2})$ polynomially (gives $n^{1/10}$); $w$ enters $M_0$, $t_*$; $w<n^{1-\varepsilon}$, the scale of $\mathcal I$.

#### D10.6 Def — The vectors $\phi$, $\eta$ and the relabeling isometry $\mathcal R_X$
*Source: 09-amplification.tex 324–346, 399–402; `eq:amplification-swapped-state` (337), `eq:amplification-restored-state` (338–340).*

**Statement.** Full eigenbasis $\{|x\rangle\}$ of $\rho_X$, eigenvalues $p_x\ge0$; Schmidt expansion $\Omega=\sum_{y:p_y>0}\sqrt{p_y}|y\rangle_X|\omega_y\rangle_{YZ'}$ ($\omega_y$ orthonormal). Append $s',e'$, each a copy of the Hilbert space on $X$, with fixed unit blank vector $|0\rangle$ on $X,s',e'$. Unit vectors:
$$\phi=|0\rangle_X|0\rangle_{s'}\sum_{y:p_y>0}\sqrt{p_y}\,|y\rangle_{e'}|\omega_y\rangle_{YZ'},\qquad\eta=\Omega\otimes\sum_{x:p_x>0}\sqrt{p_x}\,|x\rangle_{s'}|x\rangle_{e'}.$$
$\mathcal R_X$: isometry relabeling $X$ as $e'$ and inserting blanks on $X,s'$; $\mathcal R_X\Omega=\phi$.

**Used from.** D2.1 (reduced states).

**Proof (properties used later).**
- D10.6.1 $\phi=\mathcal R_X\Omega$, so for every physical $J\subseteq\Lambda\setminus X$ the $(e',J)$-reduction of $\phi$ equals the $(X,J)$-reduction of $\Omega$ with $X\to e'$.
- D10.6.2 In $\eta$, $e'$ is purified by $s'$ and $\Omega$ is a tensor factor: $\rho^\eta_{e'J}=\rho^\eta_{e'}\otimes\rho^\eta_J$, $I(e':J)_\eta=0$.
- D10.6.3 $U'$ (D10.14) acts on $s'\cup N_{2r}(S_0)$; $e'$ untouched.

**Output.** D10.7 ($R_0\phi$), D10.9 ($\mathcal R_X$), D10.15.

**Standard?** Specific to this paper.


#### D10.7 Def — Restoring operator $R_0$ and column operator $B_0$
*Source: 09-amplification.tex 348–369; `eq:amplification-restoring-operator` (350–354), `eq:amplification-column-operator` (359–364), `eq:amplification-column-identity` (367–369).*

**Statement.** $Q=Q_{S_0}$, $T_0=T_Y$. On $s',X,Y$:
$$R_0=\sum_{x\ \rm selected}p_x^{-1/2}\,|x\rangle\langle0|_{s'}\otimes Q\bigl(|x\rangle\langle0|_X\otimes T_0\bigr)$$
(trivial on $e'$, $Z'$), "selected" = range of $P_X$. On $S_0,s',e'$:
$$B_0=\sum_{\substack{x\ \rm selected\\y\ \rm in\ the\ full\ basis}}p_x^{-1/2}\,|x\rangle\langle0|_{s'}\otimes|y\rangle\langle0|_{e'}\otimes Q\bigl(|x\rangle\langle y|_X\otimes T_0\bigr).$$
Then $R_0\phi=B_0\bigl(\Omega\otimes|00\rangle_{s'e'}\bigr)$.

**Used from.** D10.5, D10.6.

**Proof.**
- D10.7.1 $\langle y|_X\Omega=\sqrt{p_y}|\omega_y\rangle$ for $p_y>0$ and $0$ for $p_y=0$. So $(|x\rangle\langle y|_X\otimes T_0)\Omega=\sqrt{p_y}\,|x\rangle_XT_0|\omega_y\rangle$ ($0$ if $p_y=0$).
- D10.7.2 $B_0(\Omega\otimes|00\rangle)=\sum_{x,y}p_x^{-1/2}\sqrt{p_y}|x\rangle_{s'}|y\rangle_{e'}Q(|x\rangle_XT_0|\omega_y\rangle)$. Zero-probability $y$ vanish. This equals $R_0\phi$: apply $R_0$ to $|0\rangle_X|0\rangle_{s'}\sum_y\sqrt{p_y}|y\rangle_{e'}|\omega_y\rangle$.

**Output.** D10.2 (B) needs $B(\Omega\otimes\xi)$, $B$ local; $R_0\phi$ is not of this form ($X$ blank in $\phi$); $B_0$ supplies it (D10.12).

**Standard?** Specific to this paper.

**Pitfall.** Sum over $y$ includes zero-probability eigenvectors (needed for $B_0^\dagger B_0\propto I_X$, D10.8); sum over $x$ is only over selected.

#### D10.8 Step — Norm bound $\|R_0\|,\|B_0\|\le M_0=e^{(\mathcal I+3w)/2}$
*Source: 09-amplification.tex 371–397; `eq:amplification-operator-norm` (392–394).*

**Statement.** With $B_Y=\sum_{x\ \rm sel}p_x^{-1}T_0\langle x|Q|x\rangle T_0\ge0$ (operator on $Y$):
$$R_0^\dagger R_0=|0\rangle\langle0|_{s'}\otimes|0\rangle\langle0|_X\otimes B_Y,\qquad B_0^\dagger B_0=|00\rangle\langle00|_{s'e'}\otimes I_X\otimes B_Y,$$
$$\|R_0\|,\|B_0\|\le M_0:=\exp\bigl((\mathcal I+3w)/2\bigr)\quad(\ge1).$$

**Used from.** D10.6, D10.7 ($R_0$, $B_0$); D10.5 (spectral inequalities); D2.2 item 5 (purity).

**Proof.**
- D10.8.1 *Gram identities.* In $R_0^\dagger R_0=\sum_{x,x'}(p_xp_{x'})^{-1/2}|0\rangle\langle x'|x\rangle\langle0|_{s'}\otimes(|0\rangle\langle x'|_X\otimes T_0)Q^2(|x\rangle\langle0|_X\otimes T_0)$, $\langle x'|x\rangle=\delta_{xx'}$, $Q^2=Q$, giving the first formula. In $B_0^\dagger B_0$ orthogonality in $s'$ and $e'$ forces $(x,y)=(x',y')$; $\sum_y|y\rangle\langle y|_X=I_X$ (full basis).
- D10.8.2 *Spectral inequalities (selected, typical):* $p_x^{-1}\le e^{S(X)+w}$; $Q\le e^{S(S_0)+w}\rho_{S_0}$ ($Q$ commutes with $\rho_{S_0}$, eigenvalues on its range $\ge e^{-S(S_0)-w}$); $T_0\rho_YT_0\le e^{-S(Y)+w}T_0$.
- D10.8.3 $B_Y\le e^{S(X)+w}T_0\bigl(\sum_x\langle x|Q|x\rangle\bigr)T_0\le e^{S(X)+w}T_0(\operatorname{Tr}_XQ)T_0\le e^{S(X)+S(S_0)+2w}T_0\rho_YT_0\le e^{S(X)+S(S_0)-S(Y)+3w}T_0$. (Sum over selected $x\le$ sum over all $x$ since $\langle x|Q|x\rangle\ge0$; $\operatorname{Tr}_XQ\le e^{S(S_0)+w}\operatorname{Tr}_X\rho_{S_0}=e^{S(S_0)+w}\rho_Y$.)
- D10.8.4 Purity of $\Omega$ on $XYZ'$: $S(S_0)=S(Z')$, $S(Y)=S(XZ')$, so $S(X)+S(S_0)-S(Y)=S(X)+S(Z')-S(XZ')=\mathcal I$.
- D10.8.5 $\|R_0\|^2=\|R_0^\dagger R_0\|=\|B_Y\|\le e^{\mathcal I+3w}$; same for $B_0$.

**Output.** $\|\zeta\|,\|B_0\|\le M_0$ in D10.12; $\log M_0\le Ct_*$ in D10.11; $M_0\ge1$ in D10.13.

**Standard?** Specific to this paper (typical-spectrum bound on a Petz-type recovery map; entropy identity D10.8.4).

**Pitfall.** Only $\log M_0=O(\mathcal I+w)$ is available: $R_0$ is exponentially large in $\mathcal I$, which is why $t_*$ and $r$ must scale with $\mathcal I$ (D10.11).

#### D10.9 Step — Adjoint identity and adjoint error (no factor $M_0$)
*Source: 09-amplification.tex 399–415; `eq:amplification-adjoint-identity` (405–408), `eq:amplification-adjoint-error` (412–415).*

**Statement.** For every physical operator $L'$ (acting trivially on $s',e'$):
$$R_0^\dagger(L')^\dagger\eta=\mathcal R_X(P_X\otimes T_0)Q\,(L')^\dagger\Omega,$$
$$\|R_0^\dagger(L')^\dagger\eta-\phi\|\le3\sqrt\delta+\|(L')^\dagger\Omega-\Omega\|.$$

**Used from.** D10.5, D10.6, D10.7.

**Proof.**
- D10.9.1 $(L')^\dagger\eta=((L')^\dagger\Omega)\otimes\sum_x\sqrt{p_x}|x\rangle_{s'}|x\rangle_{e'}$. $R_0^\dagger=\sum_{x'}p_{x'}^{-1/2}|0\rangle\langle x'|_{s'}\otimes(|0\rangle\langle x'|_X\otimes T_0)Q$. Contracting $\langle x'|_{s'}$ picks $x=x'$; $p_{x'}^{-1/2}\sqrt{p_{x'}}=1$ for selected $x'$. Result: $|0\rangle_{s'}\sum_{x'\ \rm sel}|x'\rangle_{e'}\otimes|0\rangle_X\langle x'|_XT_0Q(L')^\dagger\Omega$. This is $\mathcal R_X(P_X\otimes T_0)Q(L')^\dagger\Omega$ (relabel $X\to e'$, insert blanks); exact.
- D10.9.2 $\phi=\mathcal R_X\Omega$, $\mathcal R_X$ isometry: $\|R_0^\dagger(L')^\dagger\eta-\phi\|=\|P_XT_0Q(L')^\dagger\Omega-\Omega\|\le\|P_XT_0Q((L')^\dagger\Omega-\Omega)\|+\|P_XT_0Q\Omega-\Omega\|$. First term $\le\|(L')^\dagger\Omega-\Omega\|$ (projections are contractions).
- D10.9.3 Telescope: $P_XT_0Q\Omega-\Omega=P_XT_0(Q-I)\Omega+P_X(T_0-I)\Omega+(P_X-I)\Omega$; each term $\le\sqrt\delta$ by D10.5 (commutation of the three projections not needed).

**Output.** D10.13: with $L'$ from D10.12, $\|R'^\dagger\eta-\phi\|\le4n^{-K}$.

**Standard?** Specific to this paper.

**Pitfall.** $\sqrt{p_x}$ of $\eta$ cancels $p_x^{-1/2}$ of $R_0$ exactly: adjoint accurate with no $M_0$; the large norm sits only in $R_0\phi$.

#### D10.10 Step — Ground component of $R_0\phi$ is at most 1
*Source: 09-amplification.tex 417–447; `eq:amplification-ground-component` (443–447).*

**Statement.** $\|P_\Omega R_0\phi\|^2\le1$ (with $P_\Omega\otimes I_{s'e'}$).

**Used from.** D10.5, D10.6, D10.7.

**Proof.** $\rho:=\rho_{S_0}$, $M_X=\operatorname{Tr}_Y[(I_X\otimes T_0)\rho Q]$.
- D10.10.1 *Coefficients.* $P_\Omega R_0\phi=\Omega\otimes\sum_{x\ \rm sel,y}c_{xy}|x\rangle_{s'}|y\rangle_{e'}$ with $c_{xy}=p_x^{-1/2}\sqrt{p_y}\langle\Omega|Q(|x\rangle_XT_0|\omega_y\rangle)=p_x^{-1/2}\langle\Omega|Q(|x\rangle\langle y|_X\otimes T_0)|\Omega\rangle=p_x^{-1/2}\operatorname{Tr}[(|x\rangle\langle y|\otimes T_0)\rho Q]=p_x^{-1/2}(M_X)_{yx}$. ($Q$ commutes with $\rho$; trace cyclicity; D10.7.1.)
- D10.10.2 *Operator bounds.* $Q$ projection commuting with $\rho$: $0\le\rho Q\le\rho$. $T_0^2=T_0$ and cyclicity of $\operatorname{Tr}_Y$ for operators on $Y$: $M_X=\operatorname{Tr}_Y[(I\otimes T_0)\rho Q(I\otimes T_0)]$. Hence $0\le M_X\le\operatorname{Tr}_Y[(I\otimes T_0)\rho(I\otimes T_0)]\le\rho_X$; last step: $\rho_X=\operatorname{Tr}_Y[T_0\rho T_0]+\operatorname{Tr}_Y[(I-T_0)\rho(I-T_0)]$ (cross terms have zero partial trace, $T_0(I-T_0)=0$ and cyclicity) and the second term is $\ge0$.
- D10.10.3 $M_X\le\rho_X$, $M_X\ge0\Rightarrow M_X$ vanishes on $\ker\rho_X$. On the support, $A_X=\rho_X^{-1/2}M_X\rho_X^{-1/2}$, $0\le A_X\le I$, $M_X=\rho_X^{1/2}A_X\rho_X^{1/2}$. With $\rho_X^+$ the inverse on the support: $M_X\rho_X^+M_X=\rho_X^{1/2}A_X^2\rho_X^{1/2}\le\rho_X^{1/2}A_X\rho_X^{1/2}=M_X$.
- D10.10.4 $\|P_\Omega R_0\phi\|^2=\sum_{x\ \rm sel,y}|(M_X)_{yx}|^2/p_x\le\sum_{x:p_x>0}\sum_y|(M_X)_{yx}|^2/p_x=\operatorname{Tr}(M_X\rho_X^+M_X)\le\operatorname{Tr}M_X\le\operatorname{Tr}\rho_X=1$ ($M_X$ Hermitian, $\rho_X$ diagonal in $\{|x\rangle\}$).

**Output.** D10.13: $D$ fixes the ground component, so $\|DP_\Omega R_0\phi\|\le1$.

**Standard?** Specific to this paper.

**Pitfall.** $\|R_0\phi\|$ may be $\sim M_0$; only the ground component is controlled; excited part killed in D10.12.

#### D10.11 Def — Clock time $t_*$ and radius $r$
*Source: 09-amplification.tex 449–463; `eq:amplification-time-choice` (457–459). Scale discussion 482–489.*

**Statement.** Run the clocks of Lemma 10.1 with $S=S_0$ for time and radius
$$t_*=C(\mathcal I+w+K\log n),\qquad r=\Bigl\lceil\bigl(C'(t_*+K\log n)\bigr)^{1/\alpha}\Bigr\rceil,$$
$C$ then $C'$ chosen large. $\zeta=R_0\phi$. $D,D_{\rm ret},L'$ denote the full, retained, truncated products. Requirements: $C\ge\max\{6/g,2\}$ (so $gt_*\ge\mathcal I+3w+6K\log n$ and $\log M_0\le t_*$) and $C'$ large enough that
$$c\,C'(t_*+K\log n)\ \ge\ \log M_0+vt_*+3K\log n+\log\mathrm{poly}$$
with $\mathrm{poly}$ the prefactor $Ct_*|S_0|(1+r)^2$ of D10.2 (B) and (A), so $\le Ct_*|S_0|(1+r)^2M_0e^{vt_*-cr^\alpha}\le n^{-3K}$.

**Used from.** D10.2, D10.3, D10.8, D10.1.

**Proof (why such $C,C'$ exist).**
- D10.11.1 $t_*\le Cn^{1-\varepsilon}$ and $r\le C_Mn^{(1-\varepsilon)/\alpha}$: $\mathcal I\le C_0n^{1-\varepsilon}$, $w=n^{3/5}<n^{1-\varepsilon}$, $K\log n=o(n^{1-\varepsilon})$ (constants depend on $K$, through $K=K(M)$).
- D10.11.2 So $t_*,r,|S_0|\le\mathrm{poly}(n)$; $\log\mathrm{poly}\le a\log n+O(\log C')+O_K(1)$, $a$ absolute. $r$ itself contains $C'$, but only through this logarithm.
- D10.11.3 $\log M_0=(\mathcal I+3w)/2\le\tfrac32(\mathcal I+w)\le t_*$ for $C\ge2$.
- D10.11.4 $cr^\alpha\ge cC'(t_*+K\log n)$; the right side of the requirement is $\le(1+v)t_*+(3K+a)\log n+O(\log C')+O_K(1)\le(4+v+a)(t_*+K\log n)$ for $K\ge1$ and $n$ large ($K\log n\to\infty$ absorbs $O(\log C')+O_K(1)$). Take $C'\ge(4+v+a)/c$.

**Output.** D10.12 (explicit decay), D10.16 ($r\le C_Mn^{(1-\varepsilon)/\alpha}$).

**Standard?** Specific to this paper.

**Pitfall.** $r=\lceil(\cdot)^{1/\alpha}\rceil$ is a power $1/\alpha>1$ of $t_*$: price of the stretched exponential $e^{-cl^\alpha}$. $C$ must be fixed before $C'$ (the $C'$-condition contains $t_*$).

#### D10.12 Step — Good trajectory
*Source: 09-amplification.tex 464–499; `eq:amplification-good-trajectory` (493–497).*

**Statement.** For $n$ large there is a clock realization (same for all three) with
$$\|D(I-P_\Omega)\zeta\|\le n^{-K},\quad\|(D-D_{\rm ret})\zeta\|\le n^{-K},\quad M_0\|D_{\rm ret}-L'\|\le n^{-K}.$$

**Used from.** D10.2 (A), (B); D10.3; D10.7; D10.8; D10.11.

**Proof.**
- D10.12.1 *First expectation.* $\|(I-P_\Omega)\zeta\|\le\|\zeta\|\le\|R_0\|\le M_0$. D10.3: $\mathbb E\|D(I-P_\Omega)\zeta\|^2\le M_0^2e^{-gt_*}\le e^{\mathcal I+3w}e^{-(\mathcal I+3w+6K\log n)}=n^{-6K}$. Markov on the square: $\Pr\{\|D(I-P_\Omega)\zeta\|>n^{-K}\}\le n^{-6K}/n^{-2K}=n^{-4K}$.
- D10.12.2 *Second.* $\zeta=B_0(\Omega\otimes|00\rangle_{s'e'})$ with $B_0$ supported on $S_0,s',e'$ (D10.7), $\|B_0\|\le M_0$. D10.2 (B), $B=B_0$, $\xi=|00\rangle$, $S=S_0$: $\mathbb E\|(D-D_{\rm ret})\zeta\|\le Ct_*|S_0|M_0e^{vt_*-cr^\alpha}\le n^{-3K}$ (D10.11). Markov: $\Pr\{>n^{-K}\}\le n^{-2K}$.
- D10.12.3 *Third.* D10.2 (A): $M_0\mathbb E\|D_{\rm ret}-L'\|\le Ct_*|S_0|(1+r)^2M_0e^{-cr^\alpha}\le n^{-3K}$. Markov: $\Pr\{>n^{-K}\}\le n^{-2K}$.
- D10.12.4 Union bound: failure $\le n^{-4K}+2n^{-2K}<1$ for large $n$. All on the same clock space, so one realization satisfies all three.

**Output.** D10.13.

**Standard?** Specific to this paper (first-moment/Markov selection of one realization of the random product).

**Pitfall.** First estimate is for the squared norm ($n^{-6K}\to n^{-4K}$); the other two are first moments ($n^{-3K}\to n^{-2K}$). Realization fixed afterwards; $D,D_{\rm ret},L'$ then ordinary operators.

#### D10.13 Step — Estimates before polar decomposition; direct error
*Source: 09-amplification.tex 501–522; `eq:amplification-before-polar` (506–509), `eq:amplification-direct-error` (520–522).*

**Statement.** With $R'=L'R_0$ on the good realization:
$$\|L'R_0\phi\|\le1+3n^{-K},\quad\|(L')^\dagger\Omega-\Omega\|\le n^{-K},\quad\|(R')^\dagger\eta-\phi\|\le4n^{-K},\quad\|R'\phi-\eta\|\le Cn^{-K/2}.$$

**Used from.** D10.9, D10.10, D10.12, D10.8 ($M_0\ge1$), D10.2.1 ($G_i\Omega=\Omega$).

**Proof.**
- D10.13.1 Every exact factor $G_i$ is self-adjoint with $G_i\Omega=\Omega$: $D\Omega=\Omega$, $D^\dagger\Omega=\Omega$, $D_{\rm ret}^\dagger\Omega=\Omega$; $[D,P_\Omega]=0$.
- D10.13.2 $\|L'\zeta\|\le\|(L'-D_{\rm ret})\zeta\|+\|(D_{\rm ret}-D)\zeta\|+\|D\zeta\|$. First: $\le\|L'-D_{\rm ret}\|\,M_0\le n^{-K}$ ($\|\zeta\|\le M_0$). Second: $\le n^{-K}$. Third: $\|D\zeta\|\le\|DP_\Omega\zeta\|+\|D(I-P_\Omega)\zeta\|\le\|P_\Omega\zeta\|+n^{-K}\le1+n^{-K}$ (D10.10). Sum $\le1+3n^{-K}$.
- D10.13.3 $(L')^\dagger\Omega-\Omega=(L'-D_{\rm ret})^\dagger\Omega$ (using $D_{\rm ret}^\dagger\Omega=\Omega$); norm $\le\|L'-D_{\rm ret}\|\le M_0\|L'-D_{\rm ret}\|\le n^{-K}$ (uses $M_0\ge1$).
- D10.13.4 D10.9 with $\sqrt\delta=n^{-K}$: $\|R'^\dagger\eta-\phi\|=\|R_0^\dagger(L')^\dagger\eta-\phi\|\le3n^{-K}+n^{-K}=4n^{-K}$.
- D10.13.5 $\phi,\eta$ unit: $\operatorname{Re}\langle\eta,R'\phi\rangle=\operatorname{Re}\langle R'^\dagger\eta,\phi\rangle=1+\operatorname{Re}\langle R'^\dagger\eta-\phi,\phi\rangle\ge1-4n^{-K}$.
- D10.13.6 $\|R'\phi-\eta\|^2=\|R'\phi\|^2+1-2\operatorname{Re}\langle\eta,R'\phi\rangle\le(1+3n^{-K})^2+1-2+8n^{-K}=14n^{-K}+9n^{-2K}\le23n^{-K}$. So $\|R'\phi-\eta\|\le Cn^{-K/2}$.

**Output.** D10.14.

**Standard?** Specific to this paper (norm $\le1+\epsilon$ and overlap $\ge1-\epsilon$ give direct error $\sqrt\epsilon$).

**Pitfall.** Loss $n^{-K}\to n^{-K/2}$ from squaring in D10.13.6; origin of $K/4$ in D10.15.

#### D10.14 Step — Local unitary $U'$ via polar decomposition
*Source: 09-amplification.tex 524–545; `eq:amplification-unitary-error` (542–544).*

**Statement.** $R'$ is supported on $s'\cup N_{2r}(S_0)$ and acts trivially on $e'$. There is a unitary $U'$ on $s'\otimes N_{2r}(S_0)$ (tensored with identity elsewhere), $R'=U'H_+$, $H_+=(R'^\dagger R')^{1/2}$, with
$$\|U'\phi-\eta\|\le Cn^{-K/2}.$$

**Used from.** D10.2 (support of $L'$ in $N_{2r}(S_0)$, D10.2.13); D10.7 ($R_0$ on $s',S_0$); D10.13.

**Proof.**
- D10.14.1 Support: $L'$ on $N_{2r}(S_0)$ (D10.2), $R_0$ on $s'\cup S_0\subseteq s'\cup N_{2r}(S_0)$. $R'$ is a square operator on the finite space $\mathcal K=s'\otimes\mathcal H_{N_{2r}(S_0)}$.
- D10.14.2 Polar decomposition $R'=VH_+$, $V$ a partial isometry from $(\ker R')^\perp$ onto $\operatorname{ran}R'$. Extend to a unitary $U'$ on $\mathcal K$: $\dim\ker R'=\dim\mathcal K-\operatorname{rank}R'=\dim(\operatorname{ran}R')^\perp$, so map $\ker R'$ unitarily onto $(\operatorname{ran}R')^\perp$. Holds for singular $R'$.
- D10.14.3 $\xi:=(U')^\dagger\eta$. $R'^\dagger\eta=H_+U'^\dagger\eta=H_+\xi$, so $\|H_+\xi-\phi\|\le4n^{-K}$. $\|R'\phi-\eta\|=\|U'(H_+\phi-\xi)\|$, so $\|H_+\phi-\xi\|\le Cn^{-K/2}$.
- D10.14.4 $(I+H_+)(\xi-\phi)=(H_+\xi-\phi)-(H_+\phi-\xi)$. $H_+\ge0\Rightarrow\|(I+H_+)^{-1}\|\le1$: $\|\xi-\phi\|\le4n^{-K}+Cn^{-K/2}\le C'n^{-K/2}$.
- D10.14.5 $\|U'\phi-\eta\|=\|U'(\phi-\xi)\|=\|\phi-\xi\|\le Cn^{-K/2}$.

**Output.** D10.15.

**Standard?** Polar decomposition, unitary extension of a partial isometry: standard. $(I+H_+)^{-1}$ avoiding any bound on $\|H_+\|$: specific to this paper.

**Pitfall.** $\|H_+\|$ may be $\sim M_0$; no bound on it needed. $U'$ is unitary on the local space: its support is why $J$ must avoid $N_{2r}(S_0)$ and why $e'$ is untouched.

#### D10.15 Step — Mutual information bound
*Source: 09-amplification.tex 547–561; `eq:amplification-output`.*

**Statement.** For every physical $J\subseteq\Lambda\setminus N_{2r}(S_0)$: $I_\Omega(X:J)\le Cn^{2-K/4}$. With $K\ge4(M+3)$: $I_\Omega(X:J)\le C_Mn^{-M}$; also for any subset of $X$.

**Used from.** D2.4 (Lemma 2.1), D2.5, D2.2 item 3; D10.6; D10.14; the hypothesis $|S_0|\le C_0n^2$ of the proposition this step belongs to.

**Proof.**
- D10.15.1 $U'$ acts on $s'\cup N_{2r}(S_0)$, disjoint from $e'$ and $J$. So $\rho^{U'\phi}_{e'J}=\rho^\phi_{e'J}$, which is the $XJ$-reduction of $\Omega$ with $X\to e'$ (D10.6.1): $I(e':J)_{U'\phi}=I_\Omega(X:J)$.
- D10.15.2 $\rho^\eta_{e'J}$ is a product (D10.6.2): $I(e':J)_\eta=0$.
- D10.15.3 Trace distance of the $e'J$-reductions $\le\frac12\||U'\phi\rangle\langle U'\phi|-|\eta\rangle\langle\eta|\|_1\le\|U'\phi-\eta\|\le Cn^{-K/2}=:\delta'$ (D2.5).
- D10.15.4 Lemma 2.1 with $D=e'$, $E=J$ and $I(D:E)=S(D)-S(D|E)$: $|I(e':J)_{U'\phi}-I(e':J)_\eta|\le2C\sqrt{\delta'}\log(e\,d_{e'})$, $d_{e'}=\dim e'$.
- D10.15.5 $\log\dim e'=|X|\log q\le|S_0|\log q\le C_0n^2\log q$. So $I_\Omega(X:J)\le Cn^{-K/4}\cdot Cn^2=Cn^{2-K/4}$.
- D10.15.6 $K\ge4(M+3)$: $n^{2-K/4}\le n^{-M-1}$, so $\le C_Mn^{-M}$ for large $n$. Uniform in $J$ because $C,K,n_0$ do not depend on $J$.
- D10.15.7 Subsets $X'\subseteq X$: $I_\Omega(X':J)\le I_\Omega(X:J)$ (discarding systems, D2.2 item 3).

**Output.** `eq:amplification-output`; §11 uses the uniformity in $J$ and the subset form.

**Standard?** Continuity: standard (Alicki–Fannes–Winter; D2.4). Reference-copy trick: specific to this paper.

**Pitfall.** Lemma 2.1 applied with first argument $e'$: $\log\dim e'\le Cn^2$ enters, $\dim J$ does not.

#### D10.16 Step — Radius bounds and containment in $A$
*Source: 09-amplification.tex 563–575; `eq:amplification-radius`, `eq:amplification-cut-clearance`.*

**Statement.** (i) $r\le C_Mn^{(1-\varepsilon)/\alpha}$ and $L+2r=o(n^\beta)$. (ii) If $\operatorname{dist}_\infty(T,Z)>L+n^\beta$ then $N_{2r}(S_0)\subseteq A$ for large $n$.

**Used from.** D10.11, D10.1, the hypotheses of the proposition this step belongs to.

**Proof.**
- D10.16.1 D10.11.1 gives (i) first part.
- D10.16.2 *Exponents.* $\alpha>1-10^{-6}$ and $\beta=1-2\cdot10^{-6}$: $\beta\alpha>(1-2\cdot10^{-6})(1-10^{-6})=1-3\cdot10^{-6}+2\cdot10^{-12}>1-10^{-5}=1-\varepsilon$. So $(1-\varepsilon)/\alpha<\beta$. Also $1-\varepsilon<\beta$. Hence $r=O(n^{(1-\varepsilon)/\alpha})=o(n^\beta)$ and $L\le n^{1-\varepsilon}=o(n^\beta)$: $L+2r=o(n^\beta)$.
- D10.16.3 *Containment.* $S_0\subseteq A$. Suppose a graph path of length $\le2r$ from $s\in S_0$ reaches $\Lambda\setminus A$. It then contains an edge with one endpoint in $A$, one outside, hence an endpoint of the original cut ($\in Z$). $s\in T_L$: $\operatorname{dist}_\infty(s,T)\le L$. Each graph step changes ambient $\ell_\infty$ position by $\le1$. So that endpoint satisfies $\operatorname{dist}_\infty(T,Z)\le L+2r<L+n^\beta$ for large $n$ (D10.16.2), contradicting the clearance hypothesis. So no such path.

**Output.** $J\supseteq\Lambda\setminus A$ allowed in D10.4; $L+2r=o(n^\beta)$ is the margin §11 needs for disjoint tiles.

**Standard?** Specific to this paper (parameter arithmetic).

**Pitfall.** Gaps are tiny ($\beta-(1-\varepsilon)/\alpha\approx7\cdot10^{-6}$ at $p=10^6$): why $\alpha\to1$ and $\varepsilon,\beta$ are fixed numerically. $X=\varnothing$ ($r=1$) satisfies (ii) the same way.

#### D10.17 Step — Closing remark
*Source: 09-amplification.tex 578–583.*

**Statement.** Global gap enters three times: marginal tail (D10.5, Lemma 3.1), positive constraints (D10.1), excited-state decay (D10.3). Entropy comparison confined to $\log\dim e'\le Cn^2$ (D10.15). §11 builds tiles whose enlarged graph neighborhoods avoid earlier tiles of the same family, so Proposition 10.2 applies repeatedly.

**Used from.** D10.3, D10.5, D10.15.

**Output.** Interface to §11.

**Standard?** Commentary.

---

## Parameters and constants

| Symbol | Value / meaning | Fixed in |
|---|---|---|
| $\varepsilon$ | $10^{-5}$ | D10.1 |
| $\beta$ | $1-2\cdot10^{-6}$ | D10.1 |
| $p$, $\alpha$ | integer $p\ge10^6$ fixed; $\alpha=p/(p+1)>1-10^{-6}$ | D10.1 |
| $g$ | gap of $H_F$, $g=\Delta/c_*$, independent of $\Lambda$ | D10.1 (from D4.6) |
| $k_i$, $a_i$ | positive contractions, anchors, $k_i\Omega=0$ | D10.1 |
| $C,c$ (D10.2) | tail constants of $\|k_i-E_{i,l}k_i\|\le Ce^{-cl^\alpha}$; generic afterwards | D10.2 hypothesis |
| $\mu$ | bound on labels per anchor | D10.2 hypothesis |
| $v$ | $=\sup_y\sum_zA_{yz}e^{a d(y,z)^\alpha}$; light-cone growth rate in $e^{vt}$ | D10.2.8 |
| $a$ | weight exponent, $a2^\alpha<c$ (e.g. $c/4$) | D10.2.8 |
| $c',c''$ | successively smaller decay constants | D10.2.10, D10.2.11 |
| $t,r$ (D10.2) | clock time, retention radius | D10.2 |
| $L$ | $\lfloor n^{1-\varepsilon}\rfloor$ | D10.4 |
| $C_0$ | bound on $|S_0|/n^2$, cut sizes$/n$, $\mathcal I/n^{1-\varepsilon}$ | D10.4 |
| $M$ | target exponent in $n^{-M}$ | D10.4 |
| $K$ | $\ge4(M+3)$ integer; error exponent | D10.5, fixed in D10.15 |
| $w$ | $n^{3/5}$, typical-spectrum window | D10.5 |
| $\delta$ | $n^{-2K}$, failure probability of each projection | D10.5 |
| $P_X,T_Y,Q_{S_0}$ | typical spectral projections | D10.5 |
| $\mathcal I$ | $I_\Omega(X:Z')\le C_0n^{1-\varepsilon}$ | D10.4 |
| $M_0$ | $\exp((\mathcal I+3w)/2)\ge1$, bound on $\|R_0\|,\|B_0\|$ | D10.8 |
| $C$ (D10.11) | $\ge\max\{6/g,2\}$ with $gt_*\ge\mathcal I+3w+6K\log n$ | D10.11 |
| $t_*$ | $C(\mathcal I+w+K\log n)$ | D10.11 |
| $C'$ | large, after $C$; makes (A),(B) errors $\le n^{-3K}$ | D10.11 |
| $r$ | $\lceil(C'(t_*+K\log n))^{1/\alpha}\rceil\le C_Mn^{(1-\varepsilon)/\alpha}$ | D10.11, D10.16 |
| good-trajectory thresholds | $n^{-K}$ (three) | D10.12 |
| failure probabilities | $n^{-4K}$, $2n^{-2K}$, sum $<1$ | D10.12 |
| $\log\dim e'$ | $|X|\log q\le C_0n^2\log q$ | D10.15 |
| clearance | $\operatorname{dist}_\infty(T,Z)>L+n^\beta$ | D10.4 |

Order of choice: $p\to\alpha$; $M\to K\to n_0$; $C\to C'$; $r$ from $\mathcal I$.

## Dependencies

**Consumes.**
- §2: D2.1 (mutual information), D2.2 (SSA consequences, purity, monotonicity), D2.4 Lemma 2.1 (continuity), D2.5 (pure-state trace distance), D2.7 (ball count), D2.9 (crossing count), D2.13 (constants convention).
- §3: D3.1 (Lemma 3.1, `lem:tail`) for the typical projections (D10.5).
- §4: D4.2 ($E_{i,l}$), D4.6 Proposition 4.3 (positive system, $g$, $\alpha$), D4.9 and D4.10 Lemma 4.4 (root tails, unital channels, cb bound).
- §9: Proposition 9.6 (`prop:collar`) supplies $\mathcal I\le Cn^{1-\varepsilon}$, $|S_0|=O(n^2)$, cuts of $X,Y,S_0$ with $O(n)$ edges; $L=\lfloor n^{1-10^{-5}}\rfloor$ matches D10.4.
- External: Barthel–Kliesch (2012, Theorems 1–2) for the mechanism of D10.2; Anshu–Arad–Vidick (2016, §III) for D10.3.

**Exports.**
- D10.4 Proposition 10.2: §11 (`10-geometry.tex` 71, 809–837): radius $r$ with $r\le C_Mn^{(1-\varepsilon)/\alpha}$, $L+2r=o(n^\beta)$; $I_\Omega(X:J)\le C_Mn^{-M}$ uniformly over $J\subseteq\Lambda\setminus N_{2r}(S_0)$ and for subsets of $X$; $N_{2r}(S_0)\subseteq A$ under clearance.
- D10.2 Lemma 10.1 and D10.3: used only inside this section.
