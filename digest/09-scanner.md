# Digest of §9 — Scanning collars and improving the entropy bound

Source: `paper/sections/08-scanner.tex` (lines 1–951). Label `sec:scanner`. Numbering (one shared counter): Lemma 9.1, Proposition 9.2, Definition 9.3, Lemma 9.4, Proposition 9.5, Proposition 9.6.

## Section in one paragraph

§9 turns the replica machinery of §6–§8 into one finite schedule and two entropy bounds for $\Omega$. (i) Scan: $K$ separated bands, each with uniform random offset, each moving a near and a far partition through a depth window by deterministic *fills* and random *charges* (D9.2–D9.7). (ii) Lemma 9.1: nested prefix partitions with $O(nD)$ cuts, commuting bands, split probability $\le CD/m$ per term (offsets), selection probability $\ge c/(nD)$ per split term (charge lottery). (iii) Proposition 9.2: entropy production over all $2nm$ rounds is bounded by the rough upper comparison, so some round and $p_k\in[\epsilon/2,\epsilon]$ has $\mathcal Q/(KnD)\le\delta_n$; there $E_{{\rm def},k}\lesssim n^\ell D^2W^2(\delta_n^{1/8}+\epsilon)$. (iv) Definition 9.3/Lemma 9.4: geometric and shell-entropy inputs for unions of rectangles and triangles. (v) Proposition 9.5: bootstrap $e_0\to e_*=2\cdot10^{-6}$ with $W=4$, rough comparisons only. (vi) Proposition 9.6: $W=n^{1/20000}$, sharp comparisons, $I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-10^{-5}}$ for a template and its collar. §10 amplifies; §11 verifies the template hypotheses.

Notation. $A$ cut region of $\Lambda\subset\mathbb Z^2$, $Z$ endpoints of crossing edges, $q$ local dimension, $g$ gap, $d_i=q^{|\widetilde X_i|}$. $S_\Omega$, $I_\Omega$ entropies/mutual information of $\Omega$; $S$, $I$ without subscript are for $\widetilde\Omega$ unless stated. $\kappa,\mu,\ell,\nu,\omega,e,e_0,e_*$ are real exponents; $\ell$ is *not* the log-dimension bound $\ell$ of §7 (there $\ell\to(\log n)^C$ here). $\epsilon=n^{-\nu}$ in Prop 9.2/9.5; $\varepsilon=10^{-5}$ in Prop 9.6.

---

### 9.0 Setup of the scan

#### D9.1 Def — Conventions: depth and metrics
*Source: 08-scanner.tex 13–17.*

**Statement.** Fix the cut $A$; $Z$ = endpoints of crossing edges. *Depth* of $x$ = $\mathrm{dist}_\infty(x,T)$ (ambient). Interaction supports and their truncations use the graph metric $d_\Lambda$. A *depth row* is the set of sites at one depth; not necessarily a lattice row.

**Used from.** D2.6 (balls, graph neighbourhoods, ambient dilations).

**Output.** $d_\Lambda\ge\mathrm{dist}_\infty$ (edges are unit steps; used in D9.8.2).

**Standard?** Notation.

#### D9.2 Def — Target, collar, and scales
*Source: 08-scanner.tex 19–42, 66–81; `scanner:scales` (33–40).*

**Statement.** $T\subset\mathbb Z^2$ finite. $T_j=T+[-j,j]^2_{\mathbb Z}$, $Q_j=A\cap(T_j\setminus T)$, $X=A\cap T\ne\varnothing$. At integer $n\ge2$ with exponents $0<\ell<1$, $0<\kappa<\mu<1-\ell$ and $W\ge1$:
$$L=\lfloor n^{1-\ell}\rfloor,\quad m=\lfloor n^\mu\rfloor,\quad K=\lfloor L/(8m)\rfloor,\quad D=\lceil n^\kappa\rceil,\quad a=W/K .$$
$n$ large enough that $K\ge1$. Roles: $n$ = padded slots per depth row; $L$ = collar depth; $m$ = window scale and number of offsets; $K$ = bands; $D$ = charge lookahead; $a$ = per-band metric weight; $W=aK$ = total weight; $r_0$ = graph radius of splitting supports. Scalar $W$ is not the operator $W_{Q,k}$ of §6.

**Used from.** D9.1.

**Output.** $K\asymp n^{1-\ell-\mu}$, $mK\asymp n^{1-\ell}$, $a\asymp Wn^{-(1-\ell-\mu)}$. Ordering $r_0\ll D\ll m\ll L$ (D9.3).

**Standard?** Specific to this paper.

**Pitfall.** A safe rectangle (D9.21) has depth rows of size $O(s_0)$, so $n$ is a fixed multiple of $s_0$.

#### D9.3 Step — Test geometry and the truncated system
*Source: 08-scanner.tex 43–64; `scanner:test-geometry` (43–48).*

**Statement.** Assume
$$|T|\le Cn^2,\qquad |T_j\setminus T_{j-1}|\le n\ (1\le j\le L),\qquad \mathrm{dist}_\infty(T,Z)>2L+10r_0,$$
with $r_0$, $S_0=A\cap T_L$ ($|S_0|=O(n^2)$), $\widetilde H,\widetilde\Omega,\widetilde E_0,\widetilde g,\widetilde h_i,\widetilde X_i$ as in D4.11 / D4.15(i); so $\widetilde E_0\le n^{-1000}$, $\widetilde g\ge g/2$. Require $r_0\ll D\ll m\ll L$ for large $n$. The target cut $\partial X$ has $O(n)$ edges: an ambient edge leaving $T$ has its outside endpoint in the first positive-depth row ($\le n$ sites, degree $\le4$), and clearance excludes edges from $X$ to $\Lambda\setminus A$.

**Used from.** D4.11 (Prop 4.5), D4.13, D4.14.

**Output.** All of D9.8, D9.9. The cut bound on $\partial X$ gives the marginal parameter at the target: $\mathcal B\le Cn(\log n)^C$ (D9.9.2).

**Standard?** Specific to this paper.

**Pitfall.** $|T_j\setminus T_{j-1}|\le n$ is the only row-size input; every "$O(nD)$" below is (rows)$\times n$.

#### D9.4 Def — Bands, offsets, initial partitions
*Source: 08-scanner.tex 83–98.*

**Statement.** Order the sites of each positive-depth row and pad to exactly $n$ slots; absent sites and sites outside $A$ are blanks. Slot order is fixed for all rounds. Bands $g'=0,\dots,K-1$: $b_{g'}=8g'm$, independent uniform offset $r_{g'}\in\{0,\dots,m-1\}$. Initial physical partition of band $g'$:
$$P_0=\{x\in A:\mathrm{dist}_\infty(x,T)\le b_{g'}+m+r_{g'}\}=XU,\quad V=(\Lambda\setminus A)\cup\{x\in A:\mathrm{dist}_\infty(x,T)>b_{g'}+5m+r_{g'}\},\quad Y=\Lambda\setminus(P_0\cup V).$$
With the auxiliary systems $C,R$ of Prop 8.1 (same for all bands): full partition $P=CP_0$, $Y$, $F=RV$. Each band's physical partition evolves separately.

**Used from.** D8.6 ($C,R$; $P_{j,g},F_{j,g},A_{j,g}$, index $(j,g)$ = leaf, band); D9.2.

**Output.** Initial $Y$ of band $g'$: $\{b_{g'}+m+r_{g'}<\mathrm{depth}\le b_{g'}+5m+r_{g'}\}$, width $4m$. All activity of band $g'$ stays in depth $[b_{g'}+m,\,b_{g'}+6m)$ ($r_{g'}<m$, fronts move $\le m/2$, D9.8.3). Consecutive windows start $8m$ apart. Max unsigned depth $<b_{K-1}+6m<8Km\le L$.

**Standard?** Specific to this paper.

#### D9.5 Def — Fill and charge rounds
*Source: 08-scanner.tex 100–135; `scanner:fronts` (120–125).*

**Statement.** $2nm$ rounds: $nm$ fills and $nm$ charges, interleaved, fill first. Every round performs one transition in every band. Time $t$ counts all rounds.

*Fill.* Receiving side alternates near, far. A fill consumes one slot of the original middle window: near side in increasing depth, far side in decreasing depth; within a row the fixed slot order, reversed on the far side. If the slot is a site still in $Y$, move it to the receiving side. Blank or already assigned slots are consumed too. A charge never changes the fill schedule.

*Oriented depth.* $\lambda=\mathrm{dist}_\infty(\cdot,T)$ on the near side, $\lambda=-\mathrm{dist}_\infty(\cdot,T)$ on the far side. With $t_P,t_F$ fills already assigned to the near/far side, the next incomplete row depths are
$$j_P=b_{g'}+m+r_{g'}+1+\lfloor t_P/n\rfloor,\qquad j_F=-(b_{g'}+5m+r_{g'})+\lfloor t_F/n\rfloor .$$

**Used from.** D9.4.

**Output.** $j_P,j_F$ are deterministic in the round index, affine with slope $\pm1$ in $r_{g'}$ (D9.8.11). Every site of oriented depth $<j$ is assigned.

**Standard?** Specific to this paper.

#### D9.6 Def — Charge rounds
*Source: 08-scanner.tex 126–135.*

**Statement.** At a charge round pick a uniform side. On that side form the list of labelled term anchors $a_i$ with oriented depth in $[j-r_0,j+D]$, counting anchor multiplicity, and pad it to the fixed length $M_n=\lceil C_1nD\rceil$ ($C_1$ uniform, large enough for every such list). Pick a uniform slot. If its graph $r_0$-ball meets both the receiving physical side and $Y$, move all sites of that ball still in $Y$ to that side. Else no move. Choices are conditionally independent across bands. Every unsigned depth appearing in these lists lies in $[1,L]$.

**Used from.** D9.5, D9.3 (row size $\le n$, bounded anchor multiplicity $\mu_R$ per site from D2.8).

**Output.** A given labelled term whose anchor is in the list on a given side is selected with probability exactly $1/(2M_n)\ge c/(nD)$ (D9.8.16).

**Standard?** Specific to this paper.

**Pitfall.** $C_1$ is a list-length constant, unrelated to $C_1$ of Prop 4.5. $C_1nD$ must dominate the list length $\le\mu_R\cdot n\cdot(D+r_0+1)$.

#### D9.7 Def — History tree, root metric, replica vector
*Source: 08-scanner.tex 137–154, 156–193 (figure).*

**Statement.** A history records offsets and all choices so far; its probability is the classical path probability, before any replica state is transported. At each round form the conditional binary mean trees of the new choices and interpolate every old leaf by one $p\in[0,1]$ common to all old histories and bands (Prop 7.4); at $p=1$ attach the choice trees to the history tree and go to the next round. This yields root metric $\mathcal M$, norm $N$, normalized replica vector $v$ of §7–§8.

**Used from.** D7.9 (round: history tree, choice trees, $\mathcal M(p)$, $\pi_j$), D7.14 (Prop 7.4), D7.3 (Lemma 7.1, mean trees), D9.4–D9.6.

**Output.** $\mathcal M=\prod_g\mathcal M_g$ (commuting factors, D9.8.10); D9.10–D9.13 integrate and average over the per-round $p$-interpolation.

**Standard?** Specific to this paper.

---

### 9.1 Geometry and probabilities of the scan

#### D9.8 Lemma 9.1 — Geometry and probabilities of the scan
*Source: 08-scanner.tex 195–338 (statement 195–221; proof 223–338). Label `scanner:histories`.*

**Statement.** Under `scanner:scales`–`scanner:test-geometry`, for all large $n$:
1. Every splitting designated support is a graph $r_0$-ball wholly in $A$. It splits at most one band, and there it meets $Y$ and exactly one of the two sides. The metric algebras generated by all statuses of distinct bands commute on the symmetric replica space.
2. Every assigned site of $A$ has oriented depth $\le j+D+r_0$ on its side. Each actual set $U$ or $UY$ is comparable by inclusion with a deterministic positive-depth prefix and differs from it by $\le CnD$ sites. The cuts of $U,UY,Y,P_0,V$ have $\le CnD$ edges. At most $CKnD$ terms split in any joint status.
3. For every labelled term $i$, round and common $p$, the total terminal-leaf probability of the leaves on which $i$ splits is $\le CD/m$.
4. An old history is *good* if no side has an assigned site of $A$ of oriented depth $>j+D/2$. For every fixed $M>0$ the probability of ever leaving "good" is $\le n^{-M}$ ($n$ large). At a charge round on a good old history each split term is sampled on its splitting side with probability $\ge c/(nD)$.

All probabilities are classical path probabilities of the history tree.

**Used from.** D9.2–D9.7; D4.11 (Prop 4.5: radii $r_i=\max\{r_0,\lfloor d_i^0/2\rfloor\}$); D6.4 (Lemma 6.1(2): central label functions commute for nested/disjoint subsystems; complementary label projectors agree on $\mathcal S_k$); D8.1 (`comparator:nesting`); D2.7–D2.8 (ball and multiplicity counts).

**Proof.**

*Splitting supports (item 1).*
- D9.8.1 Radius $r_0$. Splitting = meeting $Y$ and one side. $Y\subseteq S_0$ at all times ($Y$ starts inside $A\cap T_L$ and only loses sites), so a splitting support meets $S_0$. If $d:=d_\Lambda(a_i,S_0)>2r_0$, then $r_i=\lfloor d/2\rfloor<d$ and $N_{r_i}(a_i)\cap S_0=\varnothing$. So a support meeting $S_0$ has $d\le2r_0$ hence $r_i=r_0$ (also excludes $d=\infty$, whole-component supports).
- D9.8.2 Inside $A$. If the $r_0$-ball meeting $S_0\subseteq A$ had a site of $\Lambda\setminus A$, a graph path inside the ball (length $\le2r_0$ via the anchor) would contain a cut edge, with endpoint in $Z$ at $\mathrm{dist}_\infty\le L+2r_0$ from $T$ ($S_0\subseteq T_L$; $d_\Lambda\ge\mathrm{dist}_\infty$). Contradicts $\mathrm{dist}_\infty(T,Z)>2L+10r_0$.
- D9.8.3 Front kinematics. A fill assigns sites at depth $\le$ the current front. A charge assigns sites of an $r_0$-ball around an anchor of oriented depth $\le j+D$, so depth $\le j+D+r_0$ (item 2, first claim); $j$ never decreases, so the bound persists. Each side receives $\le\lceil nm/2\rceil$ fills, so its front advances $\le m/2+O(1)$ rows. Lead $D+O(r_0)=o(m)$. Hence near front plus lead and far front minus lead are separated by $\ge3m-2(D+r_0)-O(1)\ge2m$ at all times, and active regions of consecutive bands (start $8m$ apart, width $<6m$) by $\ge3m-O(r_0)$.
- D9.8.4 Consequences. A ball has diameter $\le2r_0\ll m$ and depth changes by $\le1$ per edge, so it meets neither both sides nor $Y$ of two bands. Hence a non-contained support in band $g'$ meets $Y$ and exactly one of $P,F$, and is exceptional in at most one band. Also: an opposite side never consumes a scheduled slot, and all nonblank slots strictly behind a nominal front are assigned to that side.

*Prefixes, cuts, counts (item 2).*
- D9.8.5 Sandwich. Near set $U$: contains the deterministic prefix up to the nominal near front (D9.8.4), is contained in the prefix ending at front $+D+r_0$ rows. Difference $\le(D+r_0+1)n\le CnD$ sites. $UY$ = (original shell prefix) minus (assigned far suffix): contained in the prefix ending at the nominal far front, contains the prefix ending $D+r_0$ rows earlier. Difference $O(D)$ rows $\Rightarrow\le CnD$ sites.
- D9.8.6 Nesting. All comparison prefixes are prefixes of one fixed ordered list of positive-depth slots (by depth, within a row by slot order; far-side consumption runs in reverse, so the assigned far part is a suffix). So they are nested across histories and bands.
- D9.8.7 Cut size. A full depth prefix has $O(n)$ boundary edges: outer boundary $\le4|\text{last row}|\le4n$ (depth changes by $\le1$ per edge); boundary at depth $0$ $\le4|\text{first positive row}|\le4n$; a partial row adds $\le4n$. No edge joins $S_0$-part to the opposite colour (clearance, D9.8.2). Changing $\le CnD$ sites changes the cut by $\le4CnD$. Hence all status cuts, and their differences, are $\le CnD$ ($D\ge1$). Cut of $V$ = cut of $XUY$.
- D9.8.8 Count of split terms. A split support meets a $Y$-site (oriented depth $\ge j$) and a side-site (depth $\le j+D+r_0$), so its anchor has oriented depth in $[j-r_0,\,j+D+2r_0]$: $O(D)$ rows $\times\le n$ sites $\times\le\mu_R$ labels $=O(nD)$ anchors per band. A term splits at most one band (D9.8.4): $\le CnD$ per band, $\le CKnD$ per joint status.

*Cross-band commutation (item 1, last claim).*
- D9.8.9 Inclusion. For $g'<g''$ and every pair of histories: actual $XU_{g'}Y_{g'}\subseteq\{x\in A:\mathrm{depth}\le b_{g'}+5m+r_{g'}\}$ and actual $XU_{g''}\supseteq\{x\in A:\mathrm{depth}\le b_{g''}+m+r_{g''}\}$ (near sets only grow); $b_{g''}+m\ge b_{g'}+9m>b_{g'}+6m$. So $XU_{g'}Y_{g'}\subseteq XU_{g''}$ = `comparator:nesting`, i.e. after adjoining $C$: $P_{g'}Y_{g'}\subseteq P_{g''}$.
- D9.8.10 Commutation. By D6.4 (Lemma 6.1(2)), $W_{F_{g'}}$ equals the same central function of the complement label $P_{g'}Y_{g'}$. So band $g'$'s metric is a function of the labels on $P_{g'}$, $Y_{g'}$, $P_{g'}Y_{g'}$, all contained in $P_{g''}$. Band $g''$'s metric uses labels on $P_{g''}$ (nested with them), $Y_{g''}$ and $F_{g''}$ (disjoint from $P_{g''}$, hence from them). D6.4(2): nested or disjoint central label functions commute.

*Dilution by offsets (item 3).*
- D9.8.11 For a fixed anchor to split, its oriented depth lies in $[j-O(r_0),\,j+D+O(r_0)]$ (D9.8.8). At a fixed round $j_P,j_F$ of band $g'$ are $\pm r_{g'}+\text{const}$ (D9.5). So the event confines $r_{g'}$ to an interval of length $D+O(r_0)$ among $m$ equiprobable values: probability $\le(D+O(r_0)+1)/m$ per band. Windows are $\ge3m-O(r_0)$ apart, so $O(1)$ bands reach the anchor. Total $\le CD/m$. The split event is bounded by an event about the offset alone, valid for old and new leaves (lead $\le D+r_0$ regardless of choices), hence for any $(1-p)\,\text{old}+p\,\text{new}$ mixture. No conditional independence between split event and later charge choices is used.

*Charge ancestry (item 4, tail).*
- D9.8.12 Ancestry inequality. Suppose a side has an assigned site $s\in A$ of oriented depth $>j(t)+D/2$ at time $t$. Trace its first assignment: initial/fill (depth $\le j$ then) or a charge ball; in the latter case pick a previously assigned same-side site in that ball (exists: moves need the ball to meet the side). Two sites of one $r_0$-ball are $\le2r_0$ apart. Iterate until an initial/fill site; a chain with $j'$ charges, first at time $t_1$, gives $\mathrm{depth}(s)\le j(t_1)+O(1)+2r_0j'$. Hence $2r_0j'>D/2+j(t)-j(t_1)-O(1)$. All ancestry sites are in $A$ (charge balls are inside $A$, D9.8.2), also on the far side.
- D9.8.13 Time window. Fills alternate sides, one fill per two rounds, so each side gets one fill per four rounds: $j(t)-j(t_1)\ge(t-t_1)/(4n)-O(1)$. Substituting: $j'\ge cD/r_0$ and $t-t_1\le Cnr_0j'$. All charge times of the ancestry lie in this window.
- D9.8.14 Counting. For fixed endpoint, test time, $j'$: time choices $\le\binom{\lceil Cnr_0j'\rceil}{j'}$. Spatial choices per step: anchor within $O(r_0)$ of the current site ($\le Cr_0^2$ anchors with multiplicity) and predecessor within the ball ($\le Cr_0^2$): $(Cr_0^4)^{j'}$ total. A prescribed hit has conditional probability $\le(cnD)^{-1}$ ($1/(2M_n)$, D9.6). With $\binom{v}{j'}\le(ev/j')^{j'}$:
$$\binom{Cnr_0j'}{j'}(Cr_0^4)^{j'}(cnD)^{-j'}\le\Big(\tfrac{Cnr_0\cdot r_0^4}{nD}\Big)^{j'}=\big(Cr_0^5/D\big)^{j'} .$$
- D9.8.15 Union and tail. Endpoints: charged sites in $S_0$, $O(n^2)$; test times $\le2nm$; bands $\le K$; sides 2 (polynomial in $n$, no far-domain volume). Total $\le\mathrm{poly}(n)\sum_{j'\ge cD/r_0}(Cr_0^5/D)^{j'}$. Since $r_0=\mathrm{polylog}\,n$ and $D\ge n^\kappa$, $Cr_0^5/D\le n^{-\kappa+o(1)}\le\tfrac12$ and the sum is $\le2\exp(-c\,(D/r_0)\kappa\log n)=\exp(-n^{\kappa-o(1)})<n^{-M}$ for every fixed $M$.
- D9.8.16 Availability. On a good history a split anchor has oriented depth $\ge j-r_0$ (its ball meets an unassigned site, depth $\ge j$) and $\le j+D/2+r_0$ (ball meets the side). For large $n$ this lies in $[j-r_0,j+D]$, so the labelled anchor is in the list of its side. Picking that side and slot has probability $1/(2M_n)\ge c/(nD)$; the move is exactly the $Y$-part of the designated support.

**Output.** To Prop 9.2: (1)+(2) nested prefixes, $B_{\rm exc}\le CnD$, status cuts $\le CnD$ (hence $\mathcal B\le CnD(\log n)^C$ via D4.14), commutation (hypothesis of Prop 7.4); (3) split weight $\le CD/m$ and $\le CKnD$ split occurrences (D9.13); (4) availability $c/(nD)$ and bad-history tail $n^{-M}$ (D9.11, D9.13).

**Standard?** Specific to this paper. Ancestry bound: Peierls-type counting of branching chains plus union bound; sliding-front geometry elementary.

**Pitfall.** (a) $r_0\ll D\ll m\ll L$ is used strictly (separation $\ge2m$ needs $D+r_0\ll m$; $D/r_0\to\infty$ polynomially for the tail). (b) "Good" is a property of the old history; availability (4) is claimed only on good histories, bad ones paid by the $n^{-M}$ tail.

---

### 9.2 Selecting a low-energy interpolation

#### D9.9 Proposition 9.2 — The scanner estimate
*Source: 08-scanner.tex 349–533 (statement 349–397; proof 399–533). Label `prop:scanner`.*

**Statement.** Assume `scanner:scales`, `scanner:test-geometry`, $0<e<1$ with $\kappa\le e$, and
$$S_\Omega(X)\le C_en^{1+e},\qquad S_\Omega(Q_j)\le C_e(nL^e+n)\quad(0\le j\le L).$$
Let $\epsilon=n^{-\nu}$, $\nu>0$ fixed; $ar_0^2$ sufficiently small. Build auxiliary systems, label sector and $\mathrm{pre}$ as in Prop 8.1 with width $w=n^{3/5}$. For every sufficiently large replica count $k$ there are a charge round and a common $p_k\in[\epsilon/2,\epsilon]$ such that $v_k=\mathcal M^{-s}\mathrm{pre}/N$, $s=1/4$, has
$$E_{{\rm def},k}=\frac{\langle v_k,\overline{\widetilde H}v_k\rangle-\widetilde E_0}{\widetilde g}\le Cn^{\ell}D^2W^2(\log n)^C\big(\delta_n^{1/8}+\epsilon+n^{-100}\big)+Cn^{-1000}+o_k(1),$$
$$\delta_n=C_e\,\epsilon^{-1}\big(n^{e-\mu}+a^{1/4}(\log n)^C\big).$$
$\overline{\widetilde H}$ = copy mean of $\widetilde H$. All norm comparisons of Prop 8.1 hold at the selected point with $B_{\rm sh}\le C_e(nL^e+n)$, $B_{\rm exc}\le CnD$, $\mathcal B\le CnD(\log n)^C$; the sharp ones further need $a\sqrt{\mathcal B}\le c$. The finite system, $n$, the scan and all auxiliary dimensions are fixed before $k\to\infty$; remainders are uniform over the selected round and $p$ (which may depend on $k$). Constants depend on the exponents and $C_e$.

**Used from.** D9.8 (Lemma 9.1); D9.3, D4.11, D4.13, D4.14; D3.1; D2.4 (Lemma 2.1, continuity); D8.2–D8.5, D8.8 (Prop 8.1: typical set, $B_{\rm sh},B_{\rm exc},\mathcal B$ data, `comparator:rough-upper`); D7.14 (Prop 7.4: `transport:entropy-gain`, `transport:energy`), D7.10 (`transport:move-eta`); D7.3 (Lemma 7.1, mean trees); D6.12 (Lemma 6.4, `lem:symbol`), D7.13 (coherent measure $\mu_\sigma$); D6.9 (`replicas:leaf-floor`).

**Proof.**
- D9.9.1 Transfer $\Omega\to\widetilde\Omega$. Trace distance $\le\sqrt{2\epsilon_n/g}=O(n^{-500})$ (Prop 4.5). Lemma 2.1 ($|\Delta S|\le C\sqrt\delta\log(e\,d_D)$) with $\delta=O(n^{-500})$, $\log d_D\le Cn^2$ ($O(n^2)$ sites) changes every entropy in the hypothesis by $\le C\,n^{-250}\cdot n^2=O(n^{-248})$. A partial last depth row adds $\le n\log q$.
- D9.9.2 Comparator data. Lemma 9.1 (nested prefixes $\mathcal R$ disjoint from $X$; matched pairs differ by $\le CnD$ sites) gives $B_{\rm sh}\le C_e(nL^e+n)+n\log q$ ($n\log q$ absorbed into $C_en$) and $B_{\rm exc}\le1+CnD\log q\le CnD$ (D8.4: $B_{\rm exc}\ge1+\log\dim\mathcal H_{B\triangle Q}$). Marginal moments: each $Q\in\{XU,V,Y,U,UY\}$ has a cut with $\le CnD$ edges (Lemma 9.1(2)); for $V$ use $XUY$ (same spectrum by purity). A crossing support has $\dim\le q^{C(1+r_0)^2}$ and anchor within $r_0$ of a cut edge, so D3.1 ($\vartheta\le2/g$) gives `comparator:mgf-data` with $\mathcal B_X\le C(1+b_X)(r_0+1)^6\le CnD(\log n)^C$ (D4.14, $b_X\le CnD$). At the target $\mathcal B\le Cn(\log n)^C$ (D9.3), so with $w=n^{3/5}$: $w/\sqrt{\mathcal B}\ge n^{1/10}/(\log n)^C$ and $\Pr\{|K-S_X|>w\}\le C\exp[-cn^{1/10}/(\log n)^C]\le n^{-100}$. Typical set $E=\{i:|{-\log p_i}-S_X|\le w\}$ has $z\ge1-n^{-100}$.
- D9.9.3 $\mathcal Q(p)$, charge gain, selection, energy: D9.10–D9.13.

**Output.** Prop 9.5 ($W=4$), Prop 9.6 ($W=n^\omega$). Selected-point comparisons applied in D9.23, D9.27.

**Standard?** Specific to this paper.

**Pitfall.** $\epsilon=n^{-\nu}$ is the selection window $[\epsilon/2,\epsilon]$ for $p$ and the total weight of new leaves; unrelated to $\varepsilon=10^{-5}$ of Prop 9.6 and $\epsilon_n$ of Prop 4.5.

#### D9.10 Def — Entropy cost $\mathcal Q(p)$ of the old splits
*Source: 08-scanner.tex 416–440; `scanner:Q-definition` (424–430).*

**Statement.** At a charge round, $h$ an old joint history (weight $w_h$), $\sigma_{h,u}$ its transported state (Prop 7.4), $\mu_\sigma$ the coherent probability measure (Lemma 6.4),
$$\mathcal Q(p)=\sum_{h\ \rm good}w_h\int_{\mathbb R}m_s(u)\int\sum_{i\ \rm split\ in\ h}\eta_{i,h}(\theta)\,d\mu_{\sigma_{h,u}}(\theta)\,du .$$
$P,Y,F$ is the partition of the unique splitting band. Near side: moved set $x=Y\cap\widetilde X_i$, $\eta_{i,h}=S_\theta(x\mid P)+S_\theta(x\mid Y\setminus x)$; far side: exchange $P,F$. $0\le\eta\le C(\log n)^C$ ($x$ inside an $r_0$-ball). $m_s(u)\,du$ has mass $2s$.

**Used from.** D9.8.1, D9.8.4 (uniqueness of band), D7.10 (`transport:move-eta`: $\eta=I_\theta(x:F\mid P)\ge0$, with $Y=xY_0$), D7.14 ($\sigma_{h,u}$), D6.12/D7.13 ($\mu_\sigma$).

**Output.** D9.11–D9.13.

**Standard?** Specific to this paper.

**Pitfall.** Entropy derivative uses old weights $w_h$; energy estimate uses terminal weights $(1-p)w_h\le w_h$ (D9.13).

#### D9.11 Step — Entropy production per round
*Source: 08-scanner.tex 442–455; `scanner:charge-gain` (446–451).*

**Statement.** At a charge round
$$-\partial_p\log N^2\ \ge\ \frac{cka}{nD}\,\mathcal Q(p)-CkaK\,a^{1/4}(\log n)^C-O_{\rm fixed}(\log(k+2)).$$
At a fill round: $-\partial_p\log N^2\ge-CkaK\,a^{1/4}(\log n)^C-O_{\rm fixed}(\log(k+2))$.

**Used from.** D7.14(b) (`transport:entropy-gain`); D9.10; D9.8.16.

**Proof.**
- D9.11.1 $\eta\ge0$: drop bad histories and unsplit terms.
- D9.11.2 On a good $h$, each term split in $h$ is chosen with $q\ge c/(nD)$ and its move has exactly $\eta_{i,h}$ (D9.8.16). Distinct labelled terms occupy distinct list slots, so distinct choices. Per band $\sum_cq_{c\mid h}\eta_{h,c,g}\ge\frac c{nD}\sum_{i\ \rm split\ in\ g}\eta_{i,h}$.
- D9.11.3 A split term belongs to one band (D9.8.1/4) $\Rightarrow\sum_g\sum_{i\in g}=\sum_{i\ \rm split\ in\ h}$: the $\mathcal Q(p)$ term.
- D9.11.4 Support dimension bound $\ell\le C(1+r_0)^2$ (supports with $\mathcal J_i\ne\varnothing$ are $r_0$-balls) so $\ell^C=(\log n)^C$; smallness of $a\ell$ is the hypothesis $ar_0^2$ small. $\beta_k=O_{\rm fixed}(\log(k+2))$.
- D9.11.5 Fill round: gains $\ge0$, same negative error.

**Output.** D9.12.

**Standard?** Specific to this paper.

**Pitfall.** "Fixed" = one-copy instance and scan fixed. $O_{\rm fixed}(\log(k+2))$ survives $k\to\infty$ only after division by $k$.

#### D9.12 Step — Integration over rounds and selection of $(\text{round},p_k)$
*Source: 08-scanner.tex 457–490; `scanner:selected-density` (483–486).*

**Statement.** There are a charge round and $p_k\in[\epsilon/2,\epsilon]$ with
$$\frac{\mathcal Q(p_k)}{KnD}\le\delta_n+o_k(1),\qquad \delta_n=C_e\epsilon^{-1}\big(n^{e-\mu}+a^{1/4}(\log n)^C\big).$$

**Used from.** D9.11; D7.3 (Lemma 7.1 item 5: mean trees preserve the floor); D6.9 (`replicas:leaf-floor`: $A_k\ge\mathrm{poly}(k)^{-1}I$); D8.8 (`comparator:rough-upper`, proved in D8.20); D8.3.

**Proof.**
- D9.12.1 Telescoping. Adjacent endpoint metrics agree by construction: $\sum_{\rm rounds}\int_0^1(-\partial_p\log N^2)\,dp=-\log N_{\rm end}^2+\log N_{\rm init}^2$.
- D9.12.2 Initial: $\|\mathrm{pre}\|\le1$ and $\mathcal M\ge\mathrm{poly}(k)^{-1}$ (floor passes to the initial mean tree by Lemma 7.1; $K$ bands fixed) give $N_{\rm init}^2\le\mathrm{poly}(k)$, so $\log N^2_{\rm init}\le O_{\rm fixed}(\log(k+2))$.
- D9.12.3 Final: `comparator:rough-upper` (D8.8) with $2sW=W/2$ and $z\ge\frac12$, so $2sW(2B_{\rm sh}/z+2B_{\rm exc})\le W(2B_{\rm sh}+B_{\rm exc})$; with D9.9.2:
$$-\tfrac1k\log N^2_{\rm end}\le2\log d_*-\log z+C_eW(nL^e+nD+n)+o_k(1)\le C_eWn^{1+e}+o_k(1).$$
Last step: $L\le n$, $D\le2n^\kappa\le2n^e$, $W\ge1$, and $\log d_*=S_{\widetilde\Omega}(X)+O(w+|\log z|)\le C_en^{1+e}$ (`comparator:typical-entropies`, D9.9.1, $w\le n$).
- D9.12.4 Lower side. Restrict the nonnegative gain integrals to $p\in[\epsilon/2,\epsilon]$, pay the negative errors on all $2nm$ rounds. With $aK=W$:
$$\frac{cka}{nD}\sum_{\rm charge}\int_{\epsilon/2}^{\epsilon}\mathcal Q\,dp\le kC_eWn^{1+e}+2nm\big[CkWa^{1/4}(\log n)^C+O_{\rm fixed}(\log(k+2))\big]+o(k).$$
- D9.12.5 Normalise. $\frac{cka}{nD}\mathcal Q=ckW\cdot\frac{\mathcal Q}{KnD}$ ($aK=W$). Divide by $ckW$, then by $nm$ (number of charge rounds); $O_{\rm fixed}(\log(k+2))/k=o_k(1)$ ($W$ fixed at fixed $n$):
$$\frac1{nm}\sum_{\rm charge}\int_{\epsilon/2}^{\epsilon}\frac{\mathcal Q(p)}{KnD}dp\le C_e\Big(\frac{n^e}m+a^{1/4}(\log n)^C\Big)+o_k(1).$$
- D9.12.6 Averaging over (uniform charge round) $\times$ (Lebesgue on an interval of length $\epsilon/2$) gives a point with $\mathcal Q/(KnD)\le\frac2\epsilon\cdot$RHS. Factor 2 into $C$; $n^e/m\le Cn^{e-\mu}$ ($m=\lfloor n^\mu\rfloor$). Integrands are bounded at fixed $k$ and continuous in interior $p$, so plain averaging suffices.

**Output.** D9.13 (energy at this point); D9.23, D9.27 (norm comparisons at the same point).

**Standard?** Specific to this paper.

**Pitfall.** Selection depends on $k$; legitimate because all remainders are uniform in replica states and $p$, and $K,n,m,D$ are fixed before $k\to\infty$.

#### D9.13 Step — Energy at the selected point
*Source: 08-scanner.tex 492–532; `scanner:energy-output`.*

**Statement.** At the point of D9.12,
$$\langle v_k,\overline{\widetilde H}v_k\rangle\le2\widetilde E_0+Ca^2\frac DmKnD(\log n)^C\big(\delta_n^{1/8}+\epsilon+n^{-100}\big)+o_k(1),\qquad a^2\tfrac DmKnD=\frac{W^2nD^2}{mK}\le CW^2n^\ell D^2 ,$$
and hence the bound on $E_{{\rm def},k}$ in Prop 9.2.

**Used from.** D7.14(c) (`transport:energy`), $W_i(p)=\sum_{j\in\mathcal J_i}\pi_j$ (D7.12); requires $\bar H\,\mathrm{pre}=E_0\mathrm{pre}$ (D8.8 supplies $E_0=\widetilde E_0$); D9.8 items 2–4; D9.10; D9.12.

**Proof.**
- D9.13.1 Split weight of one term $\le CD/m$ (Lemma 9.1(3)); $\le CKnD$ split occurrences per joint leaf (Lemma 9.1(2)).
- D9.13.2 Pull $W_i(p)\le CD/m$ out of $\sum_iW_i\sum_{j\in\mathcal J_i}\pi_j\int\!\!\int\eta^{1/8}$. Remainder: $\int\eta^{1/8}d\nu$, $\nu=\sum_{\text{split pairs }(i,j)}\pi_j\,m_s(u)du\,d\mu_{\sigma_{j,u}}(\theta)$. Good old leaves: transported states are those of $\mathcal Q$, terminal weight $\pi_j=(1-p_k)w_h\le w_h$. Hölder ($8/7$, $8$): $\int\eta^{1/8}d\nu\le\nu(\text{tot})^{7/8}(\int\eta\,d\nu)^{1/8}$ with $\nu(\text{tot})\le CKnD\cdot2s$ (D9.13.1; $\mu$ probability, $\int m_s=2s$) and $\int\eta\,d\nu\le\mathcal Q(p_k)\le KnD(\delta_n+o_k(1))$. Result $CKnD(\delta_n+o_k(1))^{1/8}\le CKnD(\delta_n^{1/8}+o_k(1))$.
- D9.13.3 Bad old histories: total weight $\le n^{-M}$ (Lemma 9.1(4)); new leaves: total terminal weight $p_k\le\epsilon$. On both use $\eta^{1/8}\le C(\log n)^C$ and $\le CKnD$ terms. After raising the log power: $\epsilon+n^{-100}$.
- D9.13.4 Algebra: $a^2\frac DmKnD=\frac{W^2}{K^2}\cdot\frac DmKnD=\frac{W^2nD^2}{mK}$, and $mK\ge cn^{1-\ell}$ ($K=\lfloor L/8m\rfloor\ge L/16m$, $L\ge n^{1-\ell}/2$), so $\le CW^2n^\ell D^2$.
- D9.13.5 Subtract $\widetilde E_0$, divide by $\widetilde g\ge g/2$; $\widetilde E_0\le n^{-1000}$ gives $Cn^{-1000}$.
- D9.13.6 Only splitting terms carry skew cost (others exactly zero), so no total-volume factor. Symbol remainders are summed over the finite fixed term set before $k\to\infty$.

**Output.** `scanner:energy-output`.

**Standard?** Specific to this paper.

**Pitfall.** Three factors of different origin: $D/m$ (one term splits), $KnD$ (occurrences), $a^2$ (local skew cost). $\delta_n^{1/8}$ arises only through Hölder; in both applications (D9.22, D9.26) $\epsilon$ dominates $\delta_n^{1/8}$.

---

### 9.3 Geometric targets and entropy inputs

#### D9.14 Definition 9.3 — A template
*Source: 08-scanner.tex 546–569. Label `scanner:template`.*

**Statement.** $s_0\ge1$, $n$ positive integers. A template with parameters $(n,s_0)$ is a nonempty finite
$$T=\bigcup_{a=1}^{N_0}(P_a\cap\mathbb Z^2),\qquad n\ge C_{\rm tpl}N_0(s_0+1),\qquad\mathrm{diam}_\infty T\le n,$$
$N_0\ge1$ integer, each $P_a$ a closed convex rectangle or triangle of sup-norm diameter $\le s_0$ with all sides of slope $0,\infty,1$ or $-1$. Empty sampled pieces may be omitted. $T$ is *separated from the cut* if $\mathrm{dist}_\infty(T,Z)>4D_0s_0$. $T_j,X,Q_j$ as in D9.2. $D_0>2R+10$, "safe" (D3.3) and $F_{\rm box}$ (D3.15) as in §3. $C_{\rm tpl}$ is numerical, absorbing the layer-count constant of D9.16.

**Used from.** D3.3 (safe, $D_0>2R+10$), D3.15 ($F_{\rm box}$), D3.16 (Prop 3.3).

**Output.** Lemma 9.4, Prop 9.6, §11 (birth templates of the tiling).

**Standard?** Definition specific to this paper.

**Pitfall.** Only $N_0$ and piece sizes enter, not connectedness. $\mathrm{diam}_\infty T\le n$ only fixes a common size parameter. $n\ge C_{\rm tpl}N_0(s_0+1)\Rightarrow s_0\le n$.

#### D9.15 Lemma 9.4 — Rows, coverings, and shell entropy
*Source: 08-scanner.tex 571–672 (statement 571–592; proof 594–672). Label `scanner:templates`.*

**Statement.** For $C_{\rm tpl}$ large, a template satisfies
$$|T|\le Cns_0,\qquad|T_j\setminus T_{j-1}|\le n\ (1\le j\le s_0),\qquad|\partial_{\mathbb Z^2}T_j|\le Cn\ (0\le j\le s_0).$$
If moreover $T$ is separated from the cut and $F_{\rm box}(r)\le C_er^{1+e}$ for all integers $r\ge1$ ($0<e<1$), then for every integer $1\le L\le s_0$
$$S_\Omega(X)\le C'_en s_0^{e},\qquad S_\Omega(Q_j)\le C'_en L^{e}\quad(0\le j\le L).$$
The same shell bound with an extra $Cn$ holds for any prefix consisting of all depth rows before one row and an arbitrary subset of that last row. All physical cuts of $X$, $Q_j$, $A\cap T_j$ have $O(n)$ edges.

**Used from.** D9.14; D3.3, D3.15 (safe, $F_{\rm box}$, $D_0$); D2.2 (SSA $\Rightarrow$ subadditivity).

**Proof.** D9.16–D9.18.

**Output.** Prop 9.6 (hypotheses `scanner:entropy-input`, `scanner:test-geometry`), Prop 9.5's rectangle case (same covering, D9.21), §11 (birth templates).

**Standard?** Elementary lattice geometry; maximal dyadic (Whitney-type) cover. Entropy sum specific to this paper.

**Pitfall.** Shell squares must be safe at their own size: side $\le L$ and distance from $Z$ $>D_0\cdot$side; this is where separation $4D_0s_0$ (vs. $D_0s_0$ for a single rectangle) is spent.

#### D9.16 Step — One piece: row intervals and dilations
*Source: 08-scanner.tex 595–621.*

**Statement.** For one piece $P$ and its dilation by $j$: (i) every integer row is an integer interval; nonempty rows are consecutive; (ii) the endpoints move by $\le1$ between consecutive nonempty rows; (iii) the layer $|T^P_{j+1}\setminus T^P_j|$ and the edge boundary of $T^P_j$ are $\le C(s_0+j+1)$.

**Used from.** D9.14.

**Proof.**
- D9.16.1 Row formula. Left endpoint $\ell(y)=\max_i(\epsilon_iy+\lceil c_i\rceil)$, right endpoint $r(y)=\min_i(\epsilon'_iy+\lfloor c'_i\rfloor)$, slopes in $\{-1,0,1\}$; rounding independent of $y$ since $\epsilon y\in\mathbb Z$. Horizontal sides restrict $y$ to an integer interval.
- D9.16.2 $\ell-r$ convex (max of affine minus min of affine), so $\{y:\ell(y)\le r(y)\}$ is an interval: nonempty rows consecutive. Max/min of $1$-Lipschitz functions are $1$-Lipschitz $\Rightarrow$ endpoints move $\le1$.
- D9.16.3 Consecutive intervals overlap or are adjacent: $\ell(y+1)\le\ell(y)+1\le r(y)+1$ and symmetrically.
- D9.16.4 Dilation by $j$. Row $y$ of $T^P_j$ is $\bigcup_{|y'-y|\le j}[\ell(y')-j,r(y')+j]$ over nonempty $y'$: an integer interval (chain of overlapping/adjacent intervals). Endpoints = sliding $\min$ of $\ell$ minus $j$, sliding $\max$ of $r$ plus $j$. Index windows of consecutive rows have Hausdorff distance $\le1$ and $\ell,r$ are $1$-Lipschitz, so endpoints again move $\le1$.
- D9.16.5 One more dilation changes each endpoint on an old row by $\le2$ and adds $\le2$ rows of length $O(s_0+j+1)$. Rows $\le s_0+2j+1$. So the layer and the boundary (two row-end edges per row; $\le2$ edges between consecutive rows since endpoints move $\le1$; full top and bottom rows) are $\le C(s_0+j+1)$.

**Output.** D9.17, D9.18.

**Standard?** Elementary.

#### D9.17 Step — Mixed squares
*Source: 08-scanner.tex 623–639; `scanner:mixed-piece` (627–630).*

**Statement.** In the dyadic partition of $\mathbb Z^2$ into side-$u$ integer squares, the number of squares containing a site of a dilated piece and a site outside it is $O\big((s_0+j+1)/u+1\big)$, $u\ge1$. Consequently for $T$, $T_j$ and $T_j\setminus T$ ($j\le s_0$) the number of mixed side-$u$ squares is $\le C(N_0+n/u)$.

**Used from.** D9.16.

**Proof.**
- D9.17.1 Fix a strip of $u$ consecutive rows. If all its rows are nonempty, endpoints vary by $\le u$ (D9.16(ii)), so left endpoints meet $O(1)$ square columns, same for right. A column without an endpoint is all-inside or all-outside. So $O(1)$ mixed squares per strip.
- D9.17.2 First and last strips (some rows empty) count the whole width: $O((s_0+j+1)/u+1)$. Strips meeting nonempty rows $\le(s_0+2j+1)/u+2$.
- D9.17.3 A square mixed for a union contains a site in some constituent and a site outside all, hence is mixed for that constituent. A square mixed for $T_j\setminus T$ is mixed for $T_j$ or $T$. Sum over $N_0$ pieces, $j\le s_0$: $C\sum_a((2s_0+1)/u+1)\le C(N_0s_0/u+N_0)\le C(n/u+N_0)$ by $N_0(s_0+1)\le n/C_{\rm tpl}$.

**Output.** D9.18.

**Standard?** Elementary.

#### D9.18 Step — Covering and shell entropy
*Source: 08-scanner.tex 641–672.*

**Statement.** $S_\Omega(Q_j)\le C_en\sum_{u\le L,\,u\ \rm dyadic}u^e\le C'_enL^e$ and $S_\Omega(X)\le C'_ens_0^e$; prefix, partial-row and cut claims of Lemma 9.4.

**Used from.** D9.17, D9.16; D2.2 (subadditivity); D3.15 ($F_{\rm box}$ hypothesis).

**Proof.**
- D9.18.1 Cover $T_j\setminus T$ by maximal dyadic squares contained in it, side capped at the largest power of two $\le L$. A single site is admissible; dyadic nesting makes distinct maximal squares disjoint. So they partition $T_j\setminus T$.
- D9.18.2 Cap level: $|T_j\setminus T|\le nj\le nL$ and cap side $\ge L/2$, so $\le Cn/L$ squares.
- D9.18.3 Below cap: the parent of a maximal side-$u$ square is mixed (not contained, contains a contained square). Each parent has $4$ children: side-$u$ squares $\le4\cdot C(N_0+n/2u)\le Cn/u$, using $N_0\le n/(C_{\rm tpl}(s_0+1))\le n/u$ ($u\le L\le s_0$).
- D9.18.4 Safety. Sites lie in $T_j$, sides $\le s_0$, and $\mathrm{dist}_\infty(T_j,Z)\ge\mathrm{dist}_\infty(T,Z)-j>4D_0s_0-s_0>D_0s_0\ge D_0\cdot\text{side}$. Hence each square contributes $\le F_{\rm box}(u)\le C_eu^{1+e}$. Subadditivity: $S_\Omega(Q_j)\le C_e\big[\tfrac nL L^{1+e}+\sum_{u<{\rm cap}}\tfrac nuu^{1+e}\big]\le C'_enL^e$ (geometric sum; $C'_e$ depends on $e$ through $(1-2^{-e})^{-1}$).
- D9.18.5 Target: same cover of $T$ with cap comparable to $s_0$: $O(n/s_0)$ squares at the cap ($|T|\le Cns_0$), $O(n/u)$ below ($j=0$ in D9.17) $\Rightarrow S_\Omega(X)\le C'_ens_0^e$.
- D9.18.6 Extra part of a row: subadditivity, $\le n\log q$. Cuts: no $A$-to-$(\Lambda\setminus A)$ edge near these sets, else an endpoint in $Z$ lies within $s_0+1$ of $T$, contradicting $>4D_0s_0$ ($D_0>10$). So physical boundaries are bounded by the ambient template and shell boundaries (D9.16(iii)). Missing lattice edges are not counted as boundary.

**Output.** D9.15; Prop 9.6.

**Standard?** Maximal dyadic cover standard; exponent sum routine.

---

### 9.4 A small safe-box exponent

#### D9.19 Proposition 9.5 — Improved safe-box estimate
*Source: 08-scanner.tex 681–798 (statement 681–689; proof 691–798). Label `prop:small-box`.*

**Statement.** There is $C$ depending only on the Hamiltonian parameters ($q,R,J,\Delta$) with
$$F_{\rm box}(r)\le Cr^{1+e_*}\quad(r\ge1),\qquad e_*=2\cdot10^{-6}.$$

**Used from.** D3.16 (Prop 3.3: $e_0$, $F_{\rm box}(r)\le Cr^{1+e_0}$); D9.9 (Prop 9.2); D9.18 (covering argument); D8.8 (rough comparisons).

**Proof.** If $e_0\le e_*$ done. Else D9.20 (parameters, fixed once), D9.21–D9.24 (one improvement $e\mapsto(1-\ell)e$), D9.24.5 (iterate).

**Output.** Prop 9.6 (entropy input with $e=e_*$); §11 via Lemma 9.4.

**Standard?** Specific to this paper.

**Pitfall.** Rough comparisons only, valid even when $a\sqrt{\mathcal B}$ is large; no sharp marginal-moment condition.

#### D9.20 Step — Bootstrap parameters
*Source: 08-scanner.tex 692–706; `scanner:bootstrap-parameters` (695–702).*

**Statement.** Fixed once for the whole bootstrap:
$$g_0=\tfrac{1-e_0}2,\quad\mu=1-g_0,\quad\nu=\tfrac{g_0}{1000},\quad\ell=\tfrac\nu{100}=\tfrac{g_0}{10^5},\quad\kappa=\min\big(\tfrac\nu{100},\tfrac{e_*}4\big),\quad W=4.$$

**Used from.** D3.16 ($e_0\in(0,1)$).

**Output.** Checks: $0<\kappa<\mu<1-\ell$ ($g_0\in(0,\tfrac12)$ since $e_0\in(0,1)$; $\mu=1-g_0<1-\ell$ since $\ell<g_0$); $\kappa\le e_*/4<e$ for any $e>e_*$; $K\asymp n^{g_0-\ell}$ and $a\asymp n^{-(g_0-\ell)}$; $sW=1$ ($s=\tfrac14$).

**Standard?** Specific to this paper.

**Pitfall.** Parameters depend on $e_0$ only, not on the current $e$ => iteration count and final constants uniform.

#### D9.21 Step — Hypotheses of Prop 9.2 for a safe rectangle
*Source: 08-scanner.tex 707–728.*

**Statement.** Suppose $F_{\rm box}(r)\le C_er^{1+e}$ with $e_*<e\le e_0$. Take a safe integer rectangle $T$ of maximal side $s_0$, $n=\lceil C_2s_0\rceil$ ($C_2$ large fixed), $A\cap T\ne\varnothing$ (else entropy $0$). Then for large $s_0$ the hypotheses of Prop 9.2 hold with this $e$: `scanner:test-geometry`, `scanner:entropy-input`.

**Used from.** D9.20; D9.18.

**Proof.**
- D9.21.1 $L=o(s_0)$. Geometry: $|T|\le s_0^2\le Cn^2$; ring $|T_j\setminus T_{j-1}|\le4s_0+8j\le n$ for $C_2\ge5$, $j\le L$; $\mathrm{dist}_\infty(T,Z)>D_0s_0>2L+10r_0$ ($r_0$ polylog). The safe clearance $D_0s_0$ (not $4D_0s_0$ of Def 9.3) suffices.
- D9.21.2 Shell entropy. $T_j\setminus T$, $j\le L$, has area $O(nL)$ and is a bounded number of rectangular strips; mixed dyadic squares of side $u$ number $O(n/u+1)$ (boundary-line count). D9.18 with cap comparable to $L$ gives $S_\Omega(Q_j)\le C_enL^e$. Squares are safe: side $\le L$, distance from $Z$ $\ge D_0s_0-L>D_0L$ for large $s_0$. Thin rectangles are covered.
- D9.21.3 Target: $S_\Omega(A\cap T)\le F_{\rm box}(s_0)\le C_es_0^{1+e}\le C_en^{1+e}$. A partial row costs $O(n)$.

**Output.** D9.22–D9.23.

**Standard?** Elementary geometry.

#### D9.22 Step — Quantitative output of Prop 9.2
*Source: 08-scanner.tex 730–750; `scanner:bootstrap-energy` (745–748).*

**Statement.** With D9.20 parameters and $e_*<e\le e_0$: $\delta_n\le n^{-0.24g_0}$ and
$$E_{{\rm def},k}\le Cn^{-\nu/2}+o_k(1).$$

**Used from.** D9.9 (`scanner:energy-output`, `scanner:density-output`); D9.20.

**Proof.**
- D9.22.1 Powers in $\delta_n$ (before logs, with $\epsilon^{-1}=n^{\nu}$): $e-\mu+\nu\le e_0-(1-g_0)+\nu=-2g_0+g_0+0.001g_0=-0.999g_0$ ($e_0=1-2g_0$); $-(g_0-\ell)/4+\nu=-0.25g_0+0.0000025g_0+0.001g_0=-0.2489975g_0$. Larger is $<-0.24g_0$; constants and logs absorbed.
- D9.22.2 $\delta_n^{1/8}\le n^{-0.03g_0}$. Prefactor $n^\ell D^2W^2$: power $\ell+2\kappa\le3\cdot10^{-5}g_0=0.00003g_0$. Dominant bracket term $\epsilon=n^{-\nu}=n^{-0.001g_0}$, not $\delta_n^{1/8}$. Product: $n^{-0.00097g_0}\le n^{-\nu/2}=n^{-0.0005g_0}$.
- D9.22.3 $ar_0^2\to0$ and the scale conditions hold at large $n$.

**Output.** D9.23 ($E_{{\rm def},k}/\tau\le Cn^{-\nu/4}$ for $\tau=n^{-\nu/4}$).

**Standard?** Arithmetic.

#### D9.23 Step — Rough comparisons give $S_X\le C_e(nL^e+nD+w+h(\tau)/a+1)$
*Source: 08-scanner.tex 752–773; `scanner:bootstrap-comparison` (763–766).*

**Statement.** With $\tau=n^{-\nu/4}$, $S_X=S_{\widetilde\Omega}(X)$, for $k\to\infty$ then $n$ large:
$$S_X\le C_e\big(nL^e+nD+w+h(\tau)/a+1\big).$$

**Used from.** D8.8 (`comparator:rough-upper`, `comparator:rough-lower`); D9.22; D8.3 (`comparator:typical-entropies`); D9.9.2 ($B_{\rm sh},B_{\rm exc}$, $z$, $w$).

**Proof.**
- D9.23.1 With $s=\frac14$, $W=4$: $2sW=2$. Rough pair (D8.8). Upper: $-\frac{\log N^2}k\le2\log d_*-\log z+4B_{\rm sh}/z+4B_{\rm exc}+o_k(1)$; leading coefficient $2S_X$. Lower: $\ge2[2S'-C(\tau\log d_*+h(\tau)/a)-C\frac{E_{\rm def}}\tau S']-o_k(1)$; leading coefficient $4sWS_X=4S_X$.
- D9.23.2 Replace $\log d_*,S'$ by $S_X$ at cost $O(w+|\log z|)$ (`comparator:typical-entropies`). Use $z\ge\frac12$. Lower $\le$ upper (both bound $-\frac1k\log N^2$): $4S_X(1-C(\tau+E_{\rm def,k}/\tau))\le2S_X+C\big(B_{\rm sh}+B_{\rm exc}+w+|\log z|+h(\tau)/a\big)+o_k(1)$.
- D9.23.3 With $E_{\rm def,k}\le Cn^{-\nu/2}+o_k(1)$ (D9.22) the relative loss is $\le C(\tau+E_{\rm def,k}/\tau)\le Cn^{-\nu/4}+o_k(1)$. After $k\to\infty$ and $n$ large it is below the margin $4-2$: coefficient of $S_X$, left minus right, $\ge1$.
- D9.23.4 $B_{\rm sh}\le C_e(nL^e+n)$ and $nL^e\ge n$ ($L\ge1$) so $B_{\rm sh}\lesssim nL^e$; $B_{\rm exc}\le CnD$; $|\log z|\le2n^{-100}$.

**Output.** D9.24.

**Standard?** Specific to this paper.

**Pitfall.** Order of limits: $n$ fixed in both comparisons, $k\to\infty$ (same $S_X$ for every $k$, remainders vanish uniformly), then the large-$n$ threshold making the coefficient loss smaller than the margin $4-2$.

#### D9.24 Step — Exponent improvement and iteration
*Source: 08-scanner.tex 775–798.*

**Statement.** For $e_*<e\le e_0$ with $F_{\rm box}(r)\le C_er^{1+e}$: $F_{\rm box}(r)\le C''_er^{1+(1-\ell)e}$. After finitely many steps the exponent is $\le e_*$, giving Prop 9.5.

**Used from.** D9.23, D9.21.

**Proof.**
- D9.24.1 $h(\tau)\le C\tau\log(e/\tau)$ for $0<\tau<\frac12$. Then $h(\tau)/a\le Cn^{g_0-\ell-\nu/4}\log n=O(n)$ since $g_0<\tfrac12$.
- D9.24.2 $w=n^{3/5}\le n$. $nD\le2n^{1+\kappa}$ with $\kappa\le e_*/4<(1-\ell)e$ (as $e>e_*$, $1-\ell>\frac14$).
- D9.24.3 $nL^e\le n^{1+(1-\ell)e}$. So every term of D9.23 is $\le Cn^{1+(1-\ell)e}$. Transfer back $\widetilde\Omega\to\Omega$ costs $O(n^{-248})$ (D9.9.1). $S_\Omega(A\cap T)\le C'_en^{1+(1-\ell)e}\le C''_es_0^{1+(1-\ell)e}$ ($n=\lceil C_2s_0\rceil$).
- D9.24.4 Bounded $s_0$: $S\le s_0^2\log q$, absorbed in the constant. Supremum over safe boxes of size $\le r$ (bound monotone in $s_0$): $e\mapsto(1-\ell)e$.
- D9.24.5 Iterate from $e_0$: exponents $e_0,(1-\ell)e_0,\dots$ decrease geometrically; finitely many steps ($\ell=g_0/10^5$ fixed) reach $\le e_*$; then loosen to $e_*$. Each step uses only the current $F_{\rm box}$ bound on shell squares. Parameters and step count depend only on the Hamiltonian parameters => final constant uniform in domain and cut.

**Output.** Prop 9.5 conclusion.

**Standard?** Specific to this paper.

---

### 9.5 The collar mutual information

#### D9.25 Proposition 9.6 — A sublinear collar bound
*Source: 08-scanner.tex 808–944 (statement 808–826; proof 828–944). Label `prop:collar`.*

**Statement.** Let $T$ be a template separated from the cut with parameters $(n,s_0)$ (Def 9.3). Put
$$L=\lfloor n^{1-10^{-5}}\rfloor,\qquad X=A\cap T,\qquad S_0=A\cap T_L,$$
and suppose $L\le s_0$. For all sufficiently large $n$,
$$I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-\varepsilon},\qquad\varepsilon=10^{-5}.$$
Constant and threshold independent of $T,s_0,n,\Lambda,A$. The cuts of $X$, $S_0$, $S_0\setminus X$ have $O(n)$ edges and $|S_0|=O(n^2)$.

**Used from.** D9.19 (Prop 9.5); D9.15 (Lemma 9.4); D9.9 (Prop 9.2); D8.8 (sharp comparisons, `comparator:entropy-identity`); D2.4 (Lemma 2.1); D4.11, D4.13 (trace distance $O(n^{-500})$).

**Proof.** If $X=\varnothing$ trivial. Else D9.26 (hypotheses, parameters, $E_{\rm def}$), D9.27 (comparison difference), D9.28 (entropy identity, monotonicity), D9.29 (error table), D9.30 (transfer back).

**Output.** §10: Prop 10.2 takes $|S_0|\le C_0n^2$, cuts of $X$, $S_0\setminus X$, $S_0$ with $\le C_0n$ edges, $I_\Omega(X:\Lambda\setminus S_0)\le C_0n^{1-\varepsilon}$. §11 verifies the template hypotheses for birth templates. The conclusion is an inequality for $\Omega$ alone; the exponentially large auxiliary operator of §10 never multiplies a truncation or replica error of §9.

**Standard?** Specific to this paper.

**Pitfall.** Same $\varepsilon=10^{-5}$ in $L=\lfloor n^{1-\varepsilon}\rfloor$ and the bound. $L\le s_0$ is a hypothesis, not a consequence (may fail for small templates).

#### D9.26 Step — Hypotheses, parameters and defect energy
*Source: 08-scanner.tex 829–866; `scanner:final-parameters` (839–845), `scanner:final-energy` (856–859).*

**Statement.** Parameters
$$\mu=\tfrac14,\ \nu=\tfrac1{1000},\ \ell=\tfrac1{100000},\ \omega=\tfrac1{20000},\ \kappa=\tfrac1{1000000},\ W=n^\omega.$$
Then Prop 9.2 applies with $e=e_*$, and
$$E_{{\rm def},k}\le Cn^{-0.0005}+o_k(1),\qquad a\sqrt{\mathcal B}\le Cn^{-0.2499395}(\log n)^C\to0 .$$

**Used from.** D9.19, D9.15, D9.9.

**Proof.**
- D9.26.1 Entropy input: $e=e_*$. $S_\Omega(X)\le C'ns_0^{e_*}\le Cn^{1+e_*}$ ($s_0\le n$); $S_\Omega(Q_j)\le C'nL^{e_*}\le C_e(nL^{e}+n)$. $\kappa\le e_*$.
- D9.26.2 Test geometry (D9.3): $|T|\le Cns_0\le Cn^2$; $|T_j\setminus T_{j-1}|\le n$ ($j\le L\le s_0$); $\mathrm{dist}_\infty(T,Z)>4D_0s_0\ge4D_0L>2L+10r_0$ ($D_0>10$, $r_0$ polylog $\ll L$). $0<\kappa<\mu<1-\ell$.
- D9.26.3 $K\asymp L/(8m)=n^{1-\ell-\mu}=n^{0.74999}$; $a=W/K\asymp n^{\omega-0.74999}=n^{-0.74994}$.
- D9.26.4 $\delta_n$ powers (with $\epsilon^{-1}=n^{\nu}$): $e_*-\mu+\nu=0.000002-0.25+0.001=-0.248998$; $-0.74994/4+\nu=-0.186485$. So $\delta_n\le n^{-0.18}$, $\delta_n^{1/8}\le n^{-0.0225}$.
- D9.26.5 Energy prefactor power $\ell+2\kappa+2\omega=0.00001+0.000002+0.0001=0.000112$. $\epsilon=n^{-0.001}$ limits: $0.000112-0.001<-0.0005$, so $E_{{\rm def},k}\le Cn^{-0.0005}+o_k(1)$.
- D9.26.6 $ar_0^2\le Cn^{-0.74994}(\log n)^4\to0$.
- D9.26.7 Sharp condition: $\mathcal B\le CnD(\log n)^C$, $D=\lceil n^{10^{-6}}\rceil$, so $\sqrt{\mathcal B}\le n^{0.5000005}(\log n)^C$ and $a\sqrt{\mathcal B}\le n^{-0.74994+0.5000005}=n^{-0.2499395}\to0$. All fixed multiples of $a$ lie in the marginal-moment interval $|u|\le c_0/\sqrt{\mathcal B}$. Take $\tau=n^{-0.00025}$.

**Output.** D9.27, D9.29.

**Standard?** Arithmetic.

#### D9.27 Step — Difference of the sharp comparisons
*Source: 08-scanner.tex 868–898; `scanner:final-errors` (888–894).*

**Statement.** On $\widetilde\Omega$, with $g_{\rm pre}=S(XU)+S(V)-S(Y)$, $g_{\rm post}=S(U)+S(UY)-S(Y)$:
(a) $0\le g_{\rm pre}\le Cn^{1+e}$ for every status; also $g_{\max}\le Cn^{1+e}$.
(b) With $\langle\cdot\rangle_{\rm leaf}$ the full terminal-path and uniform band average, $2S(X)+\langle g_{\rm pre}-g_{\rm post}\rangle_{\rm leaf}$ is bounded by a constant times
$$\frac{S(X)+1}W+w+\big(\tau+E_{{\rm def},k}/\tau\big)n^{1+e}+\frac{h(\tau)}a+a\mathcal B+\frac{|\log z|}a+o_k(1).$$

**Used from.** D8.8 (`comparator:sharp-upper`, `comparator:sharp-lower`; $g_{\rm pre}\ge0$); D9.26; D9.9.2.

**Proof.**
- D9.27.1 (a) $S(XU)\le S(X)+S(U)\le Cn^{1+e}$ (subadditivity; $S(U)\le B_{\rm sh}+B_{\rm exc}$ from matched prefix). $g_{\rm pre}\le S(XU)+S(V)$ since $S(Y)\ge0$. Purity: $S(V)=S(XUY)\le S(X)+S(UY)\le Cn^{1+e}$ ($S(UY)$ as for $U$). $B_{\rm exc}\le CnD$ absorbed since $\kappa<e$. $g_{\rm pre}\ge0$ from D8.8.
- D9.27.2 (b) Sharp pair (D8.8): lower $\le$ upper (both bound $-\frac1k\log N^2$). Divide by $2sW=W/2$:
$$2S'+(1-\tau)\langle g_{\rm pre}\rangle-\langle g_{\rm post}\rangle\le\tfrac{2\log d_*-\log z}{2sW}+C\Big(a\mathcal B+\tfrac{|\log z|}a\Big)+C\Big(\tau\log d_*+\tfrac{h(\tau)}a+a\mathcal B\Big)+C\tfrac{E_{\rm def}}\tau(S'+g_{\max})+o_k(1).$$
- D9.27.3 $S'=S(X)+O(w+|\log z|)$, $\log d_*=S(X)+O(w+|\log z|)$. First term gives $C(S(X)+1)/W+Cw$. Move $\tau\langle g_{\rm pre}\rangle$ to the right via (a): $\le\tau Cn^{1+e}$; $\tau\log d_*$ and $\frac{E_{\rm def}}\tau(S'+g_{\max})$ are $\le(\tau+E_{\rm def}/\tau)Cn^{1+e}$. $|\log z|\le|\log z|/a$ ($a<1$) absorbs the $|\log z|$ from $S'$.

**Output.** D9.29.

**Standard?** Specific to this paper.

**Pitfall.** $S(\cdot)$ are entropies of $\widetilde\Omega$; transfer to $\Omega$ only at D9.30.

#### D9.28 Step — Purity identity and monotonicity
*Source: 08-scanner.tex 900–911; `scanner:entropy-identity` (901–905); `comparator:entropy-identity`.*

**Statement.** For each leaf, $2S(X)+g_{\rm pre}-g_{\rm post}=I(X:V)+I(X:YV)\ \ge\ I_{\widetilde\Omega}(X:\Lambda\setminus S_0)$, independently of the history. Hence also after the leaf average, whatever the selected round and weights.

**Used from.** D2.1 (mutual information), D2.2 items 3, 5 (monotonicity, purity); D8.8 (`comparator:entropy-identity`, proved in D8.36).

**Proof.**
- D9.28.1 Identity by D8.36 ($X,U,Y,V$ partition $\Lambda$, $\widetilde\Omega$ pure).
- D9.28.2 $\Lambda\setminus S_0=(\Lambda\setminus A)\cup\{x\in A:\mathrm{depth}>L\}\subseteq V$ in every status (far sets only grow from $\{\mathrm{depth}>b+5m+r\}$, $b+5m+r<L$), so $\Lambda\setminus S_0\subseteq V\subseteq YV$. Monotonicity of mutual information in the second argument: $I(X:V)\ge I(X:\Lambda\setminus S_0)$, likewise $YV$.

**Output.** D9.29.

**Standard?** Purity $S(AB)=S(C)$ for pure $ABC$; monotonicity of mutual information (SSA). Identity specific to this use.

#### D9.29 Step — Error table and conclusion for $\widetilde\Omega$
*Source: 08-scanner.tex 913–934.*

**Statement.** After $k\to\infty$ every term of D9.27(b) is $\le n^{0.999952}$ (up to fixed logs), strictly below $1-\varepsilon=0.99999$. Therefore $I_{\widetilde\Omega}(X:\Lambda\setminus S_0)\le Cn^{1-\varepsilon}$.

| Error term | Power of $n$ | Computation |
|---|---|---|
| $(S(X)+1)/W$ | $0.999952$ | $1+2\cdot10^{-6}-5\cdot10^{-5}$ |
| $w$ | $0.6$ | $w=n^{3/5}$ |
| $(\tau+E_{{\rm def},k}/\tau)n^{1+e}$ | $0.999752$ | $1.000002-0.00025$; $E_{\rm def}/\tau\le n^{-0.0005+0.00025}$ |
| $h(\tau)/a$ | $0.74969$ | $0.74994-0.00025$ (log ignored) |
| $a\mathcal B$ | $0.250061$ | $-0.74994+1+10^{-6}$ |
| $\lvert\log z\rvert/a$ | $-99.25006$ | $-100+0.74994$ |

**Used from.** D9.26–D9.28; $z\ge1-n^{-100}$ (D9.9.2); $h(\tau)\le C\tau\log(e/\tau)$ (as D9.24.1).

**Proof.**
- D9.29.1 Chain: $I_{\widetilde\Omega}(X:\Lambda\setminus S_0)\le\langle2S(X)+g_{\rm pre}-g_{\rm post}\rangle_{\rm leaf}\le$ D9.27(b) $\le Cn^{0.999952+o(1)}\le Cn^{0.99999}$.
- D9.29.2 The $E_{{\rm def},k}/\tau$ term ("mass-loss" in the paper) is controlled uniformly before the limit by $E_{{\rm def},k}\le Cn^{-0.0005}+o_k(1)$ (D9.26).

**Output.** D9.30.

**Standard?** Arithmetic.

**Pitfall.** Thin margin: $0.999952$ vs $0.99999$. The $(S(X)+1)/W$ term falls with $\omega=5\cdot10^{-5}$; the energy prefactor $2\omega$ (D9.26.5) rises with it.

#### D9.30 Step — Transfer back to $\Omega$ and size/boundary claims
*Source: 08-scanner.tex 936–951.*

**Statement.** $I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-\varepsilon}$; $|S_0|=O(n^2)$; cuts of $X,S_0,S_0\setminus X$ are $O(n)$.

**Used from.** D2.4 (Lemma 2.1), D4.11, D4.13 (trace distance), D9.15.

**Proof.**
- D9.30.1 $I(X:E)=S(X)-S(X\mid E)$, $E=\Lambda\setminus S_0$. Lemma 2.1 uses only $\log\dim\mathcal H_X\le|X|\log q=O(n^2)$ ($|X|\le|S_0|$), independent of $|E|$. Trace distance $O(n^{-500})$: $S(X)$, $S(X\mid E)$ each change by $\le C\sqrt\delta\log(ed_X)=O(n^{-250}n^2)$. Total $O(n^{-248})\ll n^{1-\varepsilon}$.
- D9.30.2 $|S_0|\le|T|+nL\le Cns_0+nL\le Cn^2$ ($s_0\le n$). Cuts: Lemma 9.4.

**Output.** Prop 9.6.

**Standard?** Alicki–Fannes–Winter continuity, as in D2.4.

---

## Parameters and constants

| Symbol | Value / constraint | Fixed where |
|---|---|---|
| $n$ | integer $\ge2$, large | D9.2 |
| $\ell,\kappa,\mu$ | $0<\ell<1$, $0<\kappa<\mu<1-\ell$ | D9.2 |
| $L$ | $\lfloor n^{1-\ell}\rfloor$ | D9.2 |
| $m$ | $\lfloor n^\mu\rfloor$ | D9.2 |
| $K$ | $\lfloor L/(8m)\rfloor\ge1$; $\asymp n^{1-\ell-\mu}$ | D9.2 |
| $D$ | $\lceil n^\kappa\rceil$ | D9.2 |
| $W$, $a$ | $W\ge1$; $a=W/K$, so $aK=W$ | D9.2 |
| $r_0$ | $\lceil C\log^2n\rceil$, truncation error $n^{-1000}$ | D9.3 (Prop 4.5) |
| scale ordering | $r_0\ll D\ll m\ll L$ | D9.3 |
| $S_0$ | $A\cap T_L$, $|S_0|=O(n^2)$ | D9.3 |
| $b_{g'}$, $r_{g'}$ | $8g'm$; uniform in $\{0,\dots,m-1\}$ | D9.4 |
| windows | $[b+m+r,\ b+5m+r]$ | D9.4 |
| fills / charges | $nm$ each, $2nm$ rounds | D9.5 |
| $j_P,j_F$ | `scanner:fronts` | D9.5 |
| $M_n$ | $\lceil C_1nD\rceil$ | D9.6 |
| $s$ | $1/4$ | Prop 7.4 / 8.1 |
| $w$ | $n^{3/5}$ | D9.9.2 |
| $z$ | $\ge1-n^{-100}$; tail $\le C\exp[-cn^{1/10}/(\log n)^C]$ | D9.9.2 |
| $\epsilon$ | $n^{-\nu}$ (window $[\epsilon/2,\epsilon]$ for $p_k$) | Prop 9.2 |
| $\widetilde E_0$, $\widetilde g$ | $\le n^{-1000}$, $\ge g/2$ | Prop 4.5 |
| $\delta_n$ | $C_e\epsilon^{-1}(n^{e-\mu}+a^{1/4}(\log n)^C)$ | Prop 9.2 |
| $B_{\rm sh},B_{\rm exc},\mathcal B$ | $C_e(nL^e+n)$, $CnD$, $CnD(\log n)^C$ | D9.9.2 |
| $C_{\rm tpl}$, $D_0$ | numerical; $D_0>2R+10$ | Def 9.3, Prop 3.3 |
| Prop 9.5: $g_0,\mu,\nu,\ell,\kappa,W$ | $\frac{1-e_0}2$, $1-g_0$, $\frac{g_0}{1000}$, $\frac\nu{100}$, $\min(\frac\nu{100},\frac{e_*}4)$, $4$ | D9.20 |
| Prop 9.5: $e_*$, $\tau$, $C_2$ | $2\cdot10^{-6}$; $n^{-\nu/4}$; $n=\lceil C_2s_0\rceil$ | D9.19, D9.23, D9.21 |
| Prop 9.5: $\delta_n$, $E_{\rm def}$ | $\le n^{-0.24g_0}$; $\le Cn^{-\nu/2}+o_k(1)$ | D9.22 |
| Prop 9.6: $L$ | $\lfloor n^{1-10^{-5}}\rfloor$ | D9.25 |
| Prop 9.6: $\mu,\nu,\ell,\omega,\kappa,W$ | $\frac14,\frac1{1000},\frac1{10^5},\frac1{20000},\frac1{10^6}$, $W=n^\omega$ | D9.26 |
| Prop 9.6: $a$ | $\asymp n^{-0.74994}$ | D9.26 |
| Prop 9.6: $\delta_n$ powers | $-0.248998$, $-0.186485$; $\delta_n\le n^{-0.18}$ | D9.26 |
| Prop 9.6: energy prefactor power | $\ell+2\kappa+2\omega=0.000112$ | D9.26 |
| Prop 9.6: $\epsilon$, $\tau$ | $n^{-0.001}$, $n^{-0.00025}$ | D9.26 |
| Prop 9.6: $E_{\rm def}$ | $\le Cn^{-0.0005}+o_k(1)$ | D9.26 |
| Prop 9.6: $a\sqrt{\mathcal B}$ | $\le Cn^{-0.2499395}(\log n)^C$ | D9.26 |
| Prop 9.6: $\varepsilon$ | $10^{-5}$; output $Cn^{1-\varepsilon}$ | D9.25 |
| Prop 9.6: worst error power | $0.999952<0.99999$ | D9.29 |

## Dependencies

**Consumed.**
- §2: D2.4 (Lemma 2.1), D2.1–D2.2, D2.6–D2.8.
- §3: D3.1 (Lemma 3.1, `lem:tail`), D3.3, D3.15, D3.16 (Prop 3.3).
- §4: D4.11 (Prop 4.5), D4.13, D4.14, D4.15.
- §6: D6.4 (Lemma 6.1, `lem:schur`), D6.9 (`replicas:leaf-floor`), D6.12 (Lemma 6.4, `lem:symbol`), D7.13.
- §7: D7.3 (Lemma 7.1, `transport:means`), D7.9–D7.12, D7.14 (Prop 7.4: `transport:entropy-gain`, `transport:energy`, `transport:move-eta`).
- §8: D8.1 (`comparator:nesting`), D8.2–D8.3, D8.6, D8.8 (Prop 8.1), D8.36 (`comparator:entropy-identity`).

**Exported.**
- Def 9.3 and Lemma 9.4 (templates, rows, covering, shell entropy) to §11 (birth templates, `scanner:templates`).
- Prop 9.5: $F_{\rm box}(r)\le Cr^{1+e_*}$, $e_*=2\cdot10^{-6}$, uniform in domain and cut, to Prop 9.6 and the rest of the paper.
- Prop 9.6: $I_\Omega(X:\Lambda\setminus S_0)\le Cn^{1-10^{-5}}$ with $|S_0|=O(n^2)$ and $O(n)$ cuts to §10 (Prop 10.2 hypotheses) and §11; cited in §1 (collar bounds).
