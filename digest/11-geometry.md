# Digest of §11 — Two families of regions and the area bound

Source: `paper/sections/10-geometry.tex` (lines 1–857). Label `sec:geometry`. One shared counter: Lemma 11.1, Proposition 11.2, Lemma 11.3, Lemma 11.4, Lemma 11.5; last subsection proves Theorem 1.1. Equation labels quoted as in source (`geometry:...`).

## Section in one paragraph

Prop 10.2 bounds $I_\Omega(X:J)$ for template-shaped $X=A\cap T$ and every $J$ outside the graph $2r$-neighbourhood of $S_0=A\cap T_L$. To chain it, $A$ is cut into a small exceptional set $D$ and two ordered families of tiles $X_i$ such that the collar of $X_i$ misses $\Lambda\setminus A$ and all earlier tiles of the *same* family. Lemma 11.1: two families suffice, summing the chain-rule bounds for $f=0,1$ cancels every $S(X_i)$. Prop 11.2 builds the families in the ambient plane: dyadic distance layers $D_k$ around the cut endpoints $Z$ are grouped into primary tiles (pitch $s_k$) separated by sparse belt strips (width $t_k$); belts are filled by fans of triangles labelled so that every positive-length interface joins opposite labels; remaining same-label point contacts are removed by recursively replacing squares of halfside $d(S)\approx S^{\rho_0}$. Exceptional sites and $\sum n_i^{-100}$ are $O(b)$, $b=|\partial_\Lambda A|$. Lemma 11.5 separates each new *birth* template from earlier *actual* regions, the form the collar estimate needs. Last subsection verifies the hypotheses of Props 9.6, 10.2 for these templates and concludes $S_\Omega(A)\le C'b$ (Theorem 1.1).

Notation. $Z$ = endpoints of cut edges of $\partial_\Lambda A$, $1\le|Z|\le2b$. $\dist_\infty,\diam_\infty$: ambient sup-norm in $\mathbb Z^2$/$\mathbb R^2$. A graph path of length $m$ has ambient displacement $\le m$; ambient closeness is used only as a sufficient condition for graph separation. Family labels $f\in\{0,1\}$ are unrelated to the sides $A,\Lambda\setminus A$. $C,c$ change between occurrences (§2 convention); they depend on $q,R,J,\Delta$ and the fixed template constants, never on $\Lambda,A$.

---

### 11.1 The entropy cancellation

#### D11.1 Lemma 11.1 — Two-family entropy cancellation
*Source: 10-geometry.tex 26–66.*

**Statement.** Let $\psi$ be pure on a finite tensor product with site set $\Lambda$. Let $A=D\mathbin{\dot\cup}\bigcup_{i\in\mathcal I_0}X_i\mathbin{\dot\cup}\bigcup_{i\in\mathcal I_1}X_i\subseteq\Lambda$ be a partition into disjoint sets, each $\mathcal I_f$ finite and ordered, $B=\Lambda\setminus A$. If
$$I_\psi\Bigl(X_i:B\cup\bigcup_{j\in\mathcal I_f,\,j<i}X_j\Bigr)\le\varepsilon_i\qquad(f\in\{0,1\},\ i\in\mathcal I_f),$$
then $S_\psi(A)\le S_\psi(D)+\tfrac12\sum_i\varepsilon_i$ (sum over $\mathcal I_0\sqcup\mathcal I_1$).

**Used from.** D2.1 (mutual information), D2.2 (SSA consequences, purity), D1.12.

**Proof.** $A_f=\bigcup_{i\in\mathcal I_f}X_i$, $E_f=\sum_{i\in\mathcal I_f}\varepsilon_i$.
- D11.1.1 Chain rule adding the $X_i$, $i\in\mathcal I_f$, in order to $B$: $S(BA_f)=S(B)+\sum_iS(X_i\mid B\cup X_{<i})$, $X_{<i}=\bigcup_{j<i,\,j\in\mathcal I_f}X_j$.
- D11.1.2 $S(X_i\mid J)=S(X_i)-I(X_i:J)\ge S(X_i)-\varepsilon_i$ with $J=B\cup X_{<i}$ $\Rightarrow$ $S(BA_f)\ge S(B)+\sum_{i\in\mathcal I_f}S(X_i)-E_f$.
- D11.1.3 Purity, $B=\Lambda\setminus A$: $S(B)=S(A)$ $\Rightarrow$ $S(BA_f)\ge S(A)+\sum_{i\in\mathcal I_f}S(X_i)-E_f$.
- D11.1.4 Purity again: $\Lambda\setminus(B\cup A_f)=D\cup A_{1-f}$ $\Rightarrow$ $S(BA_f)=S(DA_{1-f})\le S(D)+\sum_{i\in\mathcal I_{1-f}}S(X_i)$ (subadditivity).
- D11.1.5 Combine D11.1.3–4 for fixed $f$: $S(A)+\sum_{\mathcal I_f}S(X_i)-E_f\le S(D)+\sum_{\mathcal I_{1-f}}S(X_i)$.
- D11.1.6 Add $f=0$ and $f=1$: $2S(A)+\sum_{\text{all }i}S(X_i)-E_0-E_1\le2S(D)+\sum_{\text{all }i}S(X_i)$. Every $S(X_i)$ cancels $\Rightarrow$ $S(A)\le S(D)+\frac12(E_0+E_1)$.

**Output.** Reduces the area law to (a) $|D|\le Cb$ ($S(D)\le|D|\log q$), (b) ordered separated families, (c) $\sum_i\varepsilon_i\le Cb$: outputs of Prop 11.2 (D11.4) plus Prop 10.2.

**Standard?** Chain rule, subadditivity, purity standard (SSA: Lieb–Ruskai 1973). Two families cancelling the tile entropies: this paper.

**Pitfall.** One family leaves $\sum_iS(X_i)$ uncancelled. Conditioning set is the whole union $B\cup X_{<i}$, so $I(X_i:J_i)$ must be bounded for that union, not piecewise (D11.26.3–4).

---

### 11.2 The geometric statement

#### D11.2 Def — Exponents $\delta_0,\zeta,\rho_0,\ell$ and their gaps (`geometry:exponents`, `geometry:exponent-gaps`)
*Source: 10-geometry.tex 70–87.*

**Statement.** Keep $\beta=1-2\cdot10^{-6}$ from Prop 10.2. Put
$$\delta_0=2\cdot10^{-7},\quad\zeta=1-\frac{\delta_0}2,\quad\rho_0=\frac{1+\beta}2,\quad\ell=10^{-5}.$$
Used inequalities:
$$(1+2\delta_0)\beta<\zeta<1,\qquad(1+2\delta_0)(1-\ell)<1,\qquad1-\ell<\beta<\rho_0<1.$$

**Used from.** D10.1 ($\beta=1-2\cdot10^{-6}$ of Prop 10.2); Prop 9.6 ($L=\lfloor n^{1-10^{-5}}\rfloor$, $\varepsilon=10^{-5}=\ell$).

**Proof (check of the gaps).**
- D11.2.1 $(1+2\delta_0)\beta=(1+4\cdot10^{-7})(1-2\cdot10^{-6})=1-1.6\cdot10^{-6}-8\cdot10^{-13}<1-10^{-7}=\zeta<1$.
- D11.2.2 $(1+2\delta_0)(1-\ell)=1-9.6\cdot10^{-6}-4\cdot10^{-12}<1$.
- D11.2.3 $\rho_0=1-10^{-6}$, so $1-\ell=1-10^{-5}<\beta=1-2\cdot10^{-6}<\rho_0<1$.

**Output.** Roles: $\zeta>(1+2\delta_0)\beta$ gives $n^\beta=o(t_k)$ (D11.21); $\zeta<1$ gives $t_k\ll r$ and adjacent-layer mesh ratio $\le2$ (D11.8, D11.11); $(1+2\delta_0)(1-\ell)<1$ gives $L=o(r)$ (D11.21); $\beta<\rho_0$ gives `geometry:fine-clearance` (D11.24); $\rho_0<1$ gives termination and double-log depth (D11.15, D11.19); $\delta_0/2$ is the decay rate in `geometry:belt-count` (D11.9). Gaps are fixed positive numbers $\Rightarrow$ every threshold independent of $\Lambda,A$.

**Standard?** Specific to this paper (tuned to $e_*=2\cdot10^{-6}$, $\varepsilon=10^{-5}$ of §9–§10).

#### D11.3 Def — Birth region, actual region, template of a tile
*Source: 10-geometry.tex 89–96.*

**Statement.** Birth region of a tile: bounded closed planar region assigned at creation. Later steps only delete points. Actual region: interior of the birth region remaining after all deletions. Pieces with one tile identifier form one region; neither birth nor actual region need be connected. Ambient lattice template $T=\text{birth region}\cap\mathbb Z^2$.

**Used from.** none.

**Output.** $T_i$ in D11.4 is the untrimmed birth template; $X_i=A\cap\text{(actual region)}\subseteq A\cap T_i$. Birth regions feed the collar estimate, actual regions the partition.

**Standard?** Notation of this paper.

#### D11.4 Proposition 11.2 — Two families with separated birth templates
*Source: 10-geometry.tex 98–141. Proof: D11.5–D11.25.*

**Statement.** Fix $D_0,C_{\rm tpl}$ of Def 9.3 and a threshold $n_*\ge1$. There is $C$ (depending on these and $n_*$ only) such that: for every finite induced subgraph $\Lambda$ of $\mathbb Z^2$, $A\subseteq\Lambda$, $b=|\partial_\Lambda A|>0$, $Z$ = endpoints of cut edges, there are $D\subseteq A$, a finite ordered collection of disjoint nonempty $X_i\subseteq A$, labels $f_i\in\{0,1\}$, ambient templates $T_i\subset\mathbb Z^2$, integers $n_i\ge n_*$ with
1. $A=D\mathbin{\dot\cup}\bigcup_iX_i$, $|D|\le Cb$.
2. $X_i\subseteq A\cap T_i$; $T_i$ is a template of Def 9.3 (union of $N_i$ lattice samples of closed convex rectangles/triangles with side slopes $0,\infty,1,-1$, each of sup-diameter $\le s_i$) with $\diam_\infty T_i\le n_i$, $n_i\ge C_{\rm tpl}N_i(s_i+1)$, $\dist_\infty(T_i,Z)>4D_0s_i$; and $L_i=\lfloor n_i^{1-\ell}\rfloor\le s_i$.
3. $\dist_\infty(T_i,Z)>2n_i^\beta$ (`geometry:cut-clearance`) and $\dist_\infty\bigl(T_i,\bigcup_{j<i,\,f_j=f_i}X_j\bigr)>2n_i^\beta$ (`geometry:ordered-clearance`); distance to $\varnothing$ is $\infty$.
4. $\sum_in_i^{-100}\le Cb$.

**Used from.** D11.2; Def 9.3 (template, $D_0$ from §3 "safe", $C_{\rm tpl}$); Lemma 9.4 (D9.15, applied in the assembly D11.25); D1.6 ($Z$).

**Proof.** Staged: layers and strips (D11.5–D11.10), belt filling and marks (D11.11–D11.13), repairs (D11.14–D11.16), separation (D11.17–D11.18), counting and scales (D11.19–D11.24), assembly (D11.25).

**Output.** Items 1, 4 give $|D|\log q$ and $\sum\varepsilon_i$ in D11.26; item 2 the hypotheses of Props 9.6/10.2; item 3 $J_i\subseteq\Lambda\setminus N_{2r_i}(S_i)$.

**Standard?** Specific to this paper.

**Pitfall.** Separation (3) is birth template $T_i$ against actual earlier $X_j$, not birth against birth. Quantifiers: $n_*$ first (D11.26.2, from Props 9.6, 10.2, uniform over templates with the stated bounds), then $C=C(n_*,\dots)$.

---

### 11.3 Layers and sparse strips

#### D11.5 Def — Origin and dyadic cells
*Source: 10-geometry.tex 150–161.*

**Statement.** $o=(\sqrt2,\sqrt3)$; $o_1,o_2,o_1+o_2,o_1-o_2$ non-integral. For $r=2^k$: half-open cells $C_{k,z}=o+r(z+[0,1)^2)$, $z\in\mathbb Z^2$, nested ($C_{k+1,z'}=\bigcup_{e\in\{0,1\}^2}C_{k,2z'+e}$). Half-open cells fix indices; closures fix birth regions. Integer $C_0>100(D_0+1)$ (source: "sufficiently large compared with $D_0$").

**Used from.** none.

**Output.** Irrational $o$ $\Rightarrow$ D11.16 (no lattice point on any edge). $C_0>4D_0$ used in D11.21.

**Standard?** Generic translate of a dyadic grid is standard; choice of $o$ is this paper's.

#### D11.6 Step — Neighbourhoods $N_k$, dummy tile, layers $D_k$ (`geometry:layer-distance`)
*Source: 10-geometry.tex 163–188.*

**Statement.** $\mathcal Z_k=\{z:C_{k,z}\cap Z\ne\varnothing\}$, $N_k=\bigcup_{\dist_\infty(z,\mathcal Z_k)\le C_0}C_{k,z}$ (index distance in sup norm). Then
- $N_k\subseteq N_{k+1}$, $\bigcup_kN_k=\mathbb R^2$;
- for $k\ge k_0$, $D_k=N_{k+1}\setminus N_k$ is a union of $r$-cells, at most $C|Z|\le Cb$ of them;
- $C_0r\le\dist_\infty(x,Z)\le2(C_0+1)r$ for $x\in\overline{D_k}$.
$N_{k_0}$ is one *dummy tile*, label = parity of $k_0-1$; its points are initially exceptional.

**Used from.** D11.5.

**Proof.**
- D11.6.1 Nested. Child indices $z,z'$ with $|z-z'|_\infty\le C_0$ have parents $\lfloor z/2\rfloor,\lfloor z'/2\rfloor$ at index distance $\le\lceil C_0/2\rceil\le C_0$; if $C_{k,z'}$ contains an endpoint so does its parent. So each cell of $N_k$ lies in a parent cell of $N_{k+1}$.
- D11.6.2 Exhaustion. $Z\ne\varnothing$, $C_0\ge2$. For fixed $x$ and large $k$, $x$ and some $w\in Z$ lie in cells whose indices differ by $\le1$.
- D11.6.3 Count. $N_{k+1}$ has $\le(2C_0+1)^2|Z|$ cells of side $2r$, each with four children of side $r$. $D_k\subseteq N_{k+1}$ $\Rightarrow$ $\le4(2C_0+1)^2|Z|$ cells; $|Z|\le2b$.
- D11.6.4 Lower bound. A cell $C_{k,z}\not\subseteq N_k$ has $\dist_\infty(z,\mathcal Z_k)\ge C_0+1$, so differs from every endpoint-occupied index by $\ge C_0+1$ in some coordinate. Cells whose indices differ by $m$ in one coordinate have closures at distance $\ge(m-1)r$. So $\dist_\infty\ge C_0r$.
- D11.6.5 Upper bound. The parent of the cell, side $2r$, in $N_{k+1}$ is within $C_0$ parent-indices of a cell containing some $w\in Z$. Points of the two cells differ by $\le(C_0+1)\cdot2r$ per coordinate.

**Output.** Layer cells count $\le Cb$ (D11.9, D11.10, D11.19). `geometry:layer-distance` gives cut clearance of primaries, belts and descendants (D11.21–D11.23, D11.25). Dummy tile excluded from the order (D11.17); its sites go to $D$ (D11.20).

**Standard?** Whitney-type layering around $Z$; bookkeeping specific.

#### D11.7 Step — Non-adjacent layers (`geometry:nonadjacent`)
*Source: 10-geometry.tex 190–199.*

**Statement.** For $h\ge k+2$: $\dist_\infty(\overline{D_k},\overline{D_h})\ge C_02^h-2(C_0+1)2^k\ge\frac{C_0-1}2\,2^h$.

**Used from.** D11.6.

**Proof.**
- D11.7.1 $x\mapsto\dist_\infty(x,Z)$ is 1-Lipschitz. For $x\in\overline{D_k}$, $y\in\overline{D_h}$: $\|x-y\|_\infty\ge\dist(y,Z)-\dist(x,Z)\ge C_02^h-2(C_0+1)2^k$.
- D11.7.2 $2^k\le2^{h-2}$: $2(C_0+1)2^k\le(C_0+1)2^{h-1}$, so the bound is $\ge2^h(C_0-\frac{C_0+1}2)=\frac{C_0-1}22^h$.

**Output.** Same-label primaries in different layers (same parity $\Rightarrow$ $|h-k|\ge2$) are separated by $\ge\frac{C_0-1}22^{\max(h,k)}$ (D11.10, D11.25). Only $D_{k-1},D_k,D_{k+1}$ occur near a region of size $\ll2^k$ (D11.13).

**Standard?** Elementary.

#### D11.8 Def — Scales $s_k,t_k$, belt cells, pitch interiors, primary tiles
*Source: 10-geometry.tex 201–218.*

**Statement.** In $D_k$: $s_k=2^{\lfloor(1+\delta_0)k\rfloor}$, $t_k=2^{\lfloor\zeta k\rfloor}$. For $k_0$ large: $t_k\mid r\mid s_k$ and $t_k\ll r\ll s_k$ uniformly. $r$ = layer-cell side, $s_k$ = pitch of primaries, $t_k$ = strip width. Fine cells: side $t_k$, origin $o$. Choose two residue classes mod $s_k/t_k$ (one per coordinate). A fine cell is a *belt cell* if either index lies in its class. Remaining fine cells form open *pitch interiors* (squares of side $s_k-t_k$ between successive strips). All fragments of $D_k$ in one pitch interior form one *primary tile*, label $k\bmod2$.

**Used from.** D11.2, D11.6.

**Output.** Belt cells (D11.9, D11.11), primaries (D11.10).

**Standard?** Specific to this paper.

**Pitfall.** $\lfloor\cdot\rfloor$ makes exponents integers $\Rightarrow$ divisibility exact. $\zeta<1$ $\Rightarrow$ $t_{k+1}/t_k\in\{1,2\}$ (mesh ratio $\le2$, D11.11).

#### D11.9 Step — Few belt cells (`geometry:belt-count`)
*Source: 10-geometry.tex 220–235.*

**Statement.** The residue classes can be chosen, layer by layer, with
$$\#\{\text{belt cells in }D_k\}\le Cb\frac{r^2}{s_kt_k}\le Cb\,2^{-k\delta_0/2}.$$

**Used from.** D11.6 (layer has $\le Cb$ cells), D11.8.

**Proof.**
- D11.9.1 $D_k$ has $\le Cb$ $r$-cells, each a union of $(r/t_k)^2$ fine cells $\Rightarrow$ $\le Cb(r/t_k)^2$ fine cells, independent of the shift.
- D11.9.2 Pick the two classes uniformly. A fixed fine cell has index in the class with probability $t_k/s_k$ per coordinate, so is a belt cell with probability $\le2t_k/s_k$.
- D11.9.3 Expected count $\le Cb(r/t_k)^2\cdot2t_k/s_k=2Cb\,r^2/(s_kt_k)$; some shift achieves at most the mean.
- D11.9.4 $s_kt_k\ge2^{-2}2^{k(1+\delta_0)}2^{k\zeta}=2^{-2}2^{k(2+\delta_0/2)}$ and $r^2=2^{2k}$ $\Rightarrow$ $r^2/(s_kt_k)\le4\cdot2^{-k\delta_0/2}$.

**Output.** Geometric decay in $k$ absorbs the power of $k$ from D11.19 (`geometry:descendant-count`); rate $\delta_0/2$ is what beats the $(\log S)^C$ repair count. Shift chosen per layer, a multiple of the fine-cell side $\Rightarrow$ adjacent-layer meshes share a dyadic origin (D11.11).

**Standard?** Averaging (probabilistic method) over a predetermined family of cells.

#### D11.10 Step — Primary tiles: count, pieces, separation (`geometry:primary-pieces`)
*Source: 10-geometry.tex 237–251; figure 253–291.*

**Statement.**
- At most $Cb$ primaries per layer.
- Birth region of a primary = closures of (pitch interior $\cap$ $r$-cell of $D_k$): at most $C(s_k/r+2)^2$ closed rectangles of sup-diameter $\le r$; total sup-diameter $\le s_k$.
- Distinct primaries of one layer are at distance $\ge t_k$ (separated by a belt strip).
- Primaries of adjacent layers have opposite labels; same-label primaries of different layers satisfy D11.7.

**Used from.** D11.6, D11.7, D11.8.

**Proof.**
- D11.10.1 Each $r$-cell ($r\le s_k$) meets $\le4$ pitch interiors $\Rightarrow$ $\le4Cb$ primaries.
- D11.10.2 A square of side $s_k$ meets $\le(s_k/r+2)^2$ cells of side $r$ (at most $s_k/r+2$ per coordinate).
- D11.10.3 Different pitch interiors are separated by a strip of width $t_k$. Labels $k\bmod2$ differ for $k,k+1$.

**Output.** $N_0\le Cr^{2\delta_0}$ pieces (D11.21). Primary-vs-primary part of `geometry:ordered-clearance` (D11.25). A primary may have several components (figure); the template lemma needs no convexity of the union.

**Standard?** Elementary counting.

---

### 11.4 Filling the belts

#### D11.11 Step — Fans, labels and the point-contact property
*Source: 10-geometry.tex 293–323.*

**Statement.** Belt cells get tile identifiers and labels such that every positive-length interface between distinct identifiers joins opposite labels. Hence a same-label contact between distinct tiles is a single point and involves a belt cell.

**Used from.** D11.8, D11.10.

**Proof.**
- D11.11.1 Meshes. Adjacent layers have fine mesh ratio 1 or 2 (D11.8) and common dyadic origin. Divide a belt-cell side at corners of opposing cells; a larger side is divided only at its midpoint. So each belt side has $\le2$ elementary segments, $\le8$ in all. Along a segment the opposing region is one primary, the dummy tile, or one elementary segment of another belt cell. Layer boundaries lie on coarser dyadic grids, so never fall inside a segment.
- D11.11.2 Fan. Join the cell centre to the endpoints of its elementary segments: $\le8$ triangles; edges have slopes $0,\infty,1,-1$ (centre to corners: diagonals; to side midpoints: axes). Each triangle has exactly one outer segment.
- D11.11.3 Labels. Triangle facing a primary or dummy tile: opposite label. On a segment shared by two belt cells: any opposite pair on its two incident triangles, same on both sides. Consistent because each triangle has only one outer segment.
- D11.11.4 Merge each cyclic run of consecutive equal-label triangles of a cell into one identifier; distinct runs stay distinct identifiers.
- D11.11.5 Interfaces. Across a cell side: opposite by D11.11.3. Inside a fan: equal-label neighbours merged, remaining neighbours differ (labels in $\{0,1\}$). Primaries: same layer separated (D11.10); adjacent layers opposite labels; same label in different layers separated (D11.7).
- D11.11.6 So a same-label contact between distinct tiles is a point, and by D11.11.5 one of its tiles is a belt tile.

**Output.** Marks (D11.12) are the only places with same-label contacts.

**Standard?** Specific to this paper.

#### D11.12 Def — Initial marks
*Source: 10-geometry.tex 325–330.*

**Statement.** Mark centre, four corners and four side midpoints of every belt cell (midpoints even when the fan omits them). Deduplicate; mark $v$ gets scale $S_v$ = smallest side of a belt cell that marked it. At most $9\times$(number of belt cells) initial marks.

**Used from.** D11.9, D11.11.

**Output.** Roots of the repair recursion (D11.14); $S_v\in[t_k/2,t_k]$ for marks on a belt cell of $D_k$ (D11.19, D11.23).

**Standard?** Notation.

#### D11.13 Lemma 11.3 — Isolated stars of the initial mesh (`geometry:initial-stars`)
*Source: 10-geometry.tex 332–370.*

**Statement.** There is an absolute $a_0>0$, independent of the layer and of the shifts, such that for $k_0$ large:
1. distinct marks $v,w$: $\|v-w\|_\infty\ge a_0\max(S_v,S_w)$;
2. in $v+[-a_0S_v,a_0S_v]^2$ all active boundaries are straight rays from $v$ in the eight axis and diagonal directions; each sector between consecutive active rays has one tile identifier and consecutive sectors have opposite labels; with no active ray the square lies in one tile.
Active boundary = interface of distinct identifiers (merged seams are not boundaries).

**Used from.** D11.7, D11.8, D11.11, D11.12.

**Proof.** Belt cell of side $t=t_k$.
- D11.13.1 In its $10t$-neighbourhood only layers $k-1,k,k+1$ occur: D11.7 gives separation $\ge\frac{C_0-1}22^h\gg10t$ for $|h-k|\ge2$ since $t_k/2^k\to0$.
- D11.13.2 Fine-cell sides there are $t/2,t,2t$. Corners, fan centres and side midpoints lie on the mesh $o+(t/4)\mathbb Z^2$. Active lines have the four slopes and pass through mesh points.
- D11.13.3 Marks have scale comparable to $t$. Distinct mesh points are $\ge t/4$ apart in sup norm. A supporting line (slopes $0,\infty$: $x_i=\text{const}$; slopes $\pm1$: $x_1\pm x_2=\text{const}$, const in $(t/4)\mathbb Z$ up to the fixed offset) not through a given mesh point has sup-distance $\ge t/8$ from it. Same for the nearest other endpoint of an incident segment.
- D11.13.4 Choose $a_0$ small against these ratios $\Rightarrow$ both assertions near each mark. Pairs of marks outside the local neighbourhood already satisfy item 1.
- D11.13.5 Sectors: two sectors across an active ray have opposite labels by D11.11. Coincident segments and inactive seams are counted once, so this is the actual tile pattern.

**Output.** Base case of D11.15; contact squares of D11.18 live in these stars.

**Standard?** Finite-pattern argument on a mesh; specific to this paper.

**Pitfall.** $a_0$ is independent of $k$ and the shifts because only the finite pattern on $o+(t/4)\mathbb Z^2$ matters. Both properties persist when $a_0$ is decreased, so D11.15 can take one common $a_0$.

---

### 11.5 Removing point contacts at successively smaller scales

#### D11.14 Def — Stopping scale, trim radius, repair rule (`geometry:trim-radius`, `geometry:trim-margins`)
*Source: 10-geometry.tex 374–416; figure 418–464.*

**Statement.** Fix $S_*$ so large that for all $S\ge S_*$, $d(S)=2^{\lfloor\rho_0\log_2S\rfloor}$ satisfies
$$\tfrac12S^{\rho_0}\le d(S)\le S^{\rho_0},\qquad d(S)\le\frac{a_0}{1000}S.$$
($S_*$ is increased later for the collar estimate: D11.24.) Take $k_0$ with all initial mark scales $\ge S_*$. At every generation, simultaneously at every active mark $(v,S)$:
1. remove the closed square $Q_v=v+[-d(S),d(S)]^2$ from every old tile identifier;
2. if $d(S)<S_*$: leave the interior unassigned; terminal exceptional square;
3. else continue the incident active rays through $Q_v$ to its centre; in each sector the new region gets the label opposite to the corresponding exterior sector, with a new identifier per sector (no rays: one opposite-label square); mark centre, corners and side midpoints of $Q_v$, all at scale $d(S)$, for the next generation.
A sector of angle $>\pi$ is a union of $\le8$ of the triangles centre–corner/midpoint, so replacement birth regions keep the finite description. Every old ray meets $\partial Q_v$ at a corner or side midpoint.

**Used from.** D11.2, D11.12, D11.13.

**Proof (first line of the margins).**
- D11.14.1 $x=\rho_0\log_2S$; $2^{\lfloor x\rfloor}\in(2^{x-1},2^x]$ $\Rightarrow$ $\frac12S^{\rho_0}<d(S)\le S^{\rho_0}$.
- D11.14.2 $S^{\rho_0}\le\frac{a_0}{1000}S\iff S^{1-\rho_0}\ge1000/a_0$, true for $S\ge S_*:=(1000/a_0)^{1/(1-\rho_0)}$ and above.

**Output.** Recursion analysed in D11.15; trim radius $d(S)\ge\frac12S^{\rho_0}$ feeds D11.18; $S_{j+1}=d(S_j)$ feeds D11.19.

**Standard?** Specific to this paper.

**Pitfall.** Old identifiers lose $Q_v$ *before* the replacement is born (hence Lemma 11.5 compares with actual earlier regions). $S_*$ is fixed but astronomically large ($\rho_0$ within $10^{-6}$ of 1).

#### D11.15 Lemma 11.4 — Uniform repair induction (`geometry:repair-induction`)
*Source: 10-geometry.tex 471–543.*

**Statement.** For sufficiently small fixed $a_0$ and corresponding $S_*$, at every generation every active mark $(v,S)$ has a terminal-square-free isolated star $v+[-a_0S,a_0S]^2$ with the properties of Lemma 11.3. Distinct active marks satisfy the same separation inequality. The simultaneous removal squares are disjoint. Each replacement has opposite labels across every positive-length interface of distinct identifiers; its same-label contacts with old remnants or peer replacements occur only at marks of the next generation. Every descendant mark and every descendant birth region of $(v,S)$ lies within sup-distance $2d(S)$ of $v$. Each branch terminates after finitely many generations.

**Used from.** D11.13 (base case), D11.14.

**Proof.** Induction on generation; assume the claims for the current generation.
- D11.15.1 Containment and disjointness. By `trim-margins`, $6d(S)\le\frac{6a_0}{1000}S<a_0S$: the square of radius $6d(S)$ lies in the parent star (it contains the radius-$3d(S)$ enlarged box of D11.18). For parents $(v,S),(w,T)$: $\|v-w\|_\infty\ge a_0\max(S,T)$ and $6d(S)+d(T)\le\frac{7a_0}{1000}\max(S,T)<a_0\max(S,T)$. So each modification sees only its own parent's radial boundaries.
- D11.15.2 Labels. Across a new perimeter segment away from ray hits: inside label opposite to outside, by rule 3. Across an interior ray: the two inner labels are the opposites of two exterior labels that were opposite $\Rightarrow$ opposite. All other positive-length interfaces unchanged. Contacts not in the relative interior of one of these segments are at centre, corners or side midpoints of the new square: the next marks.
- D11.15.3 Uniform isolated star. Normalise $Q_v$ to $[-1,1]^2$. After replacement the boundaries are subsets of the original eight rays plus the four lines supporting the square. The new marks are the nine points of $\{-1,0,1\}^2$. Each non-incident supporting line has fixed positive sup-distance from each mark, other endpoints are at distance $\ge1$. So a fixed small $a_0$ gives an isolated radial star at each child, on scale $d(S)$. Take $a_0$ no larger than this and than Lemma 11.3's constant (D11.13 Pitfall).
- D11.15.4 Separation of children. Same parent: $\ge d(S)\ge a_0d(S)$. Different parents (a child lies within $d(S)$ of its parent): $\|\cdot\|_\infty\ge a_0\max(S,T)-d(S)-d(T)\ge\frac{a_0}2\max(S,T)>a_0\max(d(S),d(T))$ using $d\le\frac{a_0}{1000}S$. So the separation invariant holds for children.
- D11.15.5 Terminal squares. Child stars lie inside the parent star, so avoid terminal squares of earlier generations. Terminal squares of other current parents are excluded by D11.15.4.
- D11.15.6 Descendant bound. Each successive child is displaced by at most the preceding removal radius; successive radii shrink by factor $\le\varepsilon:=a_0/1000$ (apply `trim-margins` to $S'=d(S)\ge S_*$). A descendant birth region born at generation $m$ lies within $\sum_{i\le m}d_i\le d(S)\sum_{i\ge0}\varepsilon^i=d(S)/(1-\varepsilon)<2d(S)$ of $v$, where $d_0=d(S)$ and $d_{i+1}\le\varepsilon d_i$. Subtrees of distinct parents are separated by D11.15.4 even if one has terminated.
- D11.15.7 Termination. While a branch continues, $S_{j+1}=d(S_j)\le S_j^{\rho_0}$, $\rho_0<1$; after finitely many steps $d(S_j)<S_*$ and that removal is terminal.

**Output.** Distance $2d(S)$ of descendants from the initial mark (D11.23); isolated stars for Lemma 11.5 (D11.18); termination and recursion shape for D11.19.

**Standard?** Specific to this paper.

**Pitfall.** The finite line arrangement around every new square is *the same* at every generation (nine points, eight rays) $\Rightarrow$ $a_0$ does not degrade with the number of generations.

#### D11.16 Step — Edges avoid lattice sites
*Source: 10-geometry.tex 545–561.*

**Statement.** Every supporting line of every edge has equation $x_1=o_1+m$, $x_2=o_2+m$, $x_1+x_2=o_1+o_2+m$ or $x_1-x_2=o_1-o_2+m$, $m\in\mathbb Z$. None contains a point of $\mathbb Z^2$. So open actual regions and closed birth regions need no convention for lattice sites on an interface. Final open tile regions, the unaltered part of the dummy region, and terminal-square interiors partition all lattice sites.

**Used from.** D11.5 ($o$), D11.14 ($S_*$ increased once so a terminal halfside produced from $S\ge S_*$ is $\ge2$).

**Proof.**
- D11.16.1 Initial vertices lie in $o+\mathbb Z^2$: $r,s_k,t_k$ are dyadic integers, halfsides and midpoints used are integral.
- D11.16.2 In the recursion each new centre, corner and midpoint is the previous centre plus an integer vector; $d(S)$ is an integer.
- D11.16.3 A line through a point of $o+\mathbb Z^2$ with one of the four slopes has one of the four equations. Irrationality of $o_1,o_2,o_1\pm o_2$ excludes lattice points.

**Output.** Partition of $\mathbb Z^2$ (D11.20, D11.25).

**Standard?** Elementary.

---

### 11.6 Separation from earlier actual regions

#### D11.17 Def — Order of tile identifiers
*Source: 10-geometry.tex 565–571.*

**Statement.** Order: all primaries first, all initial belt tiles second, then replacement tiles by generation of birth; ties arbitrary. Dummy tile excluded. Primaries already have the required same-label separation among themselves (D11.10, D11.7). Lemma 11.5 covers all other identifiers.

**Used from.** D11.10, D11.11, D11.14.

**Output.** The index order $i<j$ in D11.4(3); "earlier or peer" in D11.18 refers to it.

**Standard?** Specific to this paper.

#### D11.18 Lemma 11.5 — Birth-template separation (`geometry:birth-separation`)
*Source: 10-geometry.tex 573–661, with remark 663–666.*

**Statement.** There is a fixed $c_1>0$ such that: let $\mathcal B$ be the closed birth region of an initial belt tile of side scale $u=t_k$, or of a replacement tile whose removal square has halfside $u$. Then $\dist_\infty$ from $\mathcal B$ to the *final actual region* of every earlier or peer identifier of the same label is $\ge c_1u^{\rho_0}$. Peer = another initial belt tile, resp. another replacement born in the same generation.

**Used from.** D11.13, D11.14, D11.15, D11.17.

**Proof.**
- D11.18.1 Compared sets. Belt: its closure vs the primary and belt closures at that time. Replacement: vs old remnants *after* that generation's removal squares, and vs peer replacements. Final actual regions are subsets of these. An ancestor is compared after its square was removed; its original birth region need not be disjoint from the new one.
- D11.18.2 Finitely many patterns. Enlarge the tile's cell, resp. removal square, by $2u$ in each direction (box radius $3u$ for a replacement, inside the parent star by `trim-margins`); outside the box, points are $\ge2u$ from $\mathcal B$. Translate to the cell corner/removal centre and divide by $u$. Belt: active lines and endpoints lie on the quarter mesh with four slopes; in a bounded box finitely many; local closures are unions of faces of the arrangement; finitely many identifier groupings. Replacement: the box sees only the old radial layout and the new square and sectors, a fixed finite arrangement; other parents do not enter. So there is a common positive scale for the isolation neighbourhoods.
- D11.18.3 Contacts. The two compared closures have no positive-length interface (D11.11, D11.15), so meet only at contact marks. Belt: mark scale in $[u/2,u]$ (neighbouring belt scales differ by $\le2$). Replacement: mark scale $u$. Choose disjoint open contact squares of radius $\lambda u$ inside the isolated stars, $\lambda>0$ small, fixed.
- D11.18.4 Away from contacts. Pairs $(x,y)$ in the two compared closures not both in the same open contact square form a closed subset of a compact set. $\|x-y\|_\infty$ has a positive minimum there: zero would give a common point $x=y$, a contact, with both points in its open square. Finitely many rescaled patterns $\Rightarrow$ uniform minimum $\ge c_2u$.
- D11.18.5 Angular gap inside a contact star at $v$. Each closure is a union of closed radial sectors; direction sets disjoint (a common direction = common ray segment, excluded in D11.18.3). Boundary directions are multiples of $\pi/4$, so the angle $\theta$ between the direction sets is $\ge\pi/4$. For radial vectors of lengths $a\ge b$: $|x-y|_2^2=(a-b)^2+2ab(1-\cos\theta)$. If $b\le a/2$: $\ge a^2/4$. If $b>a/2$: $\ge a^2(1-\cos\frac\pi4)>a^2/4$. So $|x-y|_2\ge\frac a2$ and $\|x-y\|_\infty\ge|x-y|_2/\sqrt2$, giving (`geometry:angular-gap`)
$$\|x-y\|_\infty\ge c_3\max\{\|x-v\|_\infty,\|y-v\|_\infty\},\qquad c_3=\tfrac1{2\sqrt2}\ \text{works}.$$
- D11.18.6 Trim. At the immediately following trim the compared old/peer identifier loses a square about $v$ of radius $\ge c_4u^{\rho_0}$ ($d(S)\ge\frac12S^{\rho_0}$ with $S\ge u/2$; this removal occurs also if the square is terminal), and only shrinks afterwards. So $y$ in its final actual region has $\|y-v\|_\infty\ge c_4u^{\rho_0}$, and D11.18.5 gives $\|x-y\|_\infty\ge c_3c_4u^{\rho_0}$ for pairs in a contact star.
- D11.18.7 Combine. Contact-star pairs: $c_3c_4u^{\rho_0}$. Other pairs inside the box: $c_2u\ge c_2u^{\rho_0}$ ($u\ge1$). Pairs with a point outside the box: $\ge2u\ge u^{\rho_0}$. So $c_1=\min\{c_2,c_3c_4,1\}$.

**Output.** `geometry:ordered-clearance` for belts and replacements (D11.25), via `geometry:fine-clearance` (D11.24). Remark 663–666: the *entire* new birth region is compared with an older *actual* region, so later deletions from the new tile are irrelevant; the collar estimate applies to the untrimmed template and part of it is discarded.

**Standard?** Compactness plus finite-pattern argument standard; application specific.

**Pitfall.** Rate $u^{\rho_0}$, not $u$: comes only from the trim at the contact (D11.18.6); away from contacts the distance is $\gtrsim u$. Hence the order uses *actual* earlier regions: birth vs birth fails at a point contact (distance $0$).

---

### 11.7 Counting exceptional sites and verifying the templates

#### D11.19 Step — Repair counts (`geometry:descendant-count`, `geometry:total-repairs`)
*Source: 10-geometry.tex 670–692.*

**Statement.** For an initial mark of scale $S$: depth $\le C+C\log\log(e^e+S)$; at most nine children per mark; hence marks and replacements descended from it number $\le C(\log(S+2))^C$. For a mark from layer $k$, $S\asymp t_k$, $\log S\le C(k+1)$. Total number of belt tiles, marks and replacements
$$\le Cb\sum_{k\ge k_0}2^{-k\delta_0/2}(k+1)^C\le C'b .$$

**Used from.** D11.9, D11.11, D11.12, D11.14, D11.15.

**Proof.**
- D11.19.1 Along a branch $S_{j+1}\le S_j^{\rho_0}$, so $\log S_j\le\rho_0^j\log S$. Termination once $S_j^{\rho_0}<S_*$, i.e. when $\rho_0^{j+1}\log S<\log S_*$; holds for $j\ge\log(\log S/\log S_*)/\log(1/\rho_0)$ (a constant times $\log\log S$ plus a constant).
- D11.19.2 $\le9^{\text{depth}}=9^{C+C\log\log(e^e+S)}\le C(\log(S+2))^{C'}$.
- D11.19.3 Per layer: belt cells $\le Cb2^{-k\delta_0/2}$ (D11.9); belt tiles $\le8$ per belt cell (one per fan run); initial marks $\le9$ per belt cell (D11.12). Each initial mark spawns $\le C(\log(S+2))^C\le C(Ck+C)^C$ marks and replacements.
- D11.19.4 Sum over $k\ge k_0$: series converges, total $C'b$, finite even before restricting to the finite domain.

**Output.** $|D|$ bound (D11.20); "number of other tiles $=O(b)$" for $\sum n_i^{-100}$ (D11.25).

**Standard?** Bookkeeping.

#### D11.20 Step — Bounded exceptional set (`geometry:bad-sites`)
*Source: 10-geometry.tex 694–707.*

**Statement.** $D$ := sites of $A$ that remain in the dummy identifier or lie in terminal squares (sites overwritten by a replacement are not dummy sites). $|D|\le Cb$.

**Used from.** D11.6, D11.16, D11.19.

**Proof.**
- D11.20.1 A terminal square has halfside $<S_*$: $\le(2S_*+1)^2\le CS_*^2$ lattice sites. Their number $\le$ total repairs $\le C'b$ (D11.19).
- D11.20.2 Dummy region: $\le(2C_0+1)^2|Z|$ cells of side $2^{k_0}$, i.e. $\le C b$ sites.
- D11.20.3 Count ambient sites, then intersect with $A$. Missing sites, holes, thin parts and extra components of $\Lambda$ only reduce the count.

**Output.** Item 1 of D11.4; $S(D)\le|D|\log q$ in D11.26.

**Standard?** Bookkeeping.

#### D11.21 Step — Scanner scales of primaries (`geometry:primary-scale`, `geometry:primary-limits`)
*Source: 10-geometry.tex 709–731.*

**Statement.** For a primary in layer $k$: $s_0=r=2^k$, $n=\lceil C_Pr^{1+2\delta_0}\rceil$ ($T=\mathcal B\cap\mathbb Z^2$). Then $N_0\le Cr^{2\delta_0}$; with $C_P$ large, $n\ge C_{\rm tpl}N_0(s_0+1)$ and $\diam_\infty T\le s_k\le n$. $T$ is separated from the cut, and
$$L=\lfloor n^{1-\ell}\rfloor=o(r),\qquad n^\beta=o(t_k),\qquad n^\beta=o(r).$$

**Used from.** D11.2, D11.5, D11.6, D11.10, Def 9.3.

**Proof.**
- D11.21.1 $s_k/r=2^{\lfloor(1+\delta_0)k\rfloor-k}\le r^{\delta_0}$, so $N_0\le C(r^{\delta_0}+2)^2\le9Cr^{2\delta_0}$.
- D11.21.2 $C_{\rm tpl}N_0(s_0+1)\le2C_{\rm tpl}\cdot9C\,r^{1+2\delta_0}\le n$ for $C_P\ge18C\,C_{\rm tpl}$. $\diam_\infty T\le s_k\le r^{1+\delta_0}\le r^{1+2\delta_0}\le n$.
- D11.21.3 Separation: $T\subseteq\overline{D_k}$, so $\dist_\infty(T,Z)\ge C_0r>4D_0r=4D_0s_0$ because $C_0>100(D_0+1)$.
- D11.21.4 $n^{1-\ell}\le C r^{(1+2\delta_0)(1-\ell)}=o(r)$ since $(1+2\delta_0)(1-\ell)<1$. $n^\beta\le C r^{(1+2\delta_0)\beta}=o(2^{\lfloor\zeta k\rfloor})$ since $(1+2\delta_0)\beta<\zeta$. $\zeta<1$ gives $n^\beta=o(r)$. In particular $L\le s_0$.

**Output.** Item 2 of D11.4 for primaries. $n^\beta=o(t_k)$ is the same-layer primary gap $t_k>2n^\beta$ (D11.25).

**Standard?** Specific to this paper.

#### D11.22 Step — Scanner scales of belt tiles and replacements
*Source: 10-geometry.tex 732–740.*

**Statement.** Belt tile (side scale $u=t_k$): $s_0=u$, $n=\lceil C_Bu\rceil$; union of $\le8$ closed fan triangles. Replacement with removal halfside $u$: $s_0=2u$, $n=\lceil C_Bu\rceil$; subdivision into the triangles centre–corners/midpoints uses $\le8$ pieces, also for a wide sector or a homogeneous square. $C_B$ large $\Rightarrow$ $n\ge C_{\rm tpl}N_0(s_0+1)$, $\diam_\infty T\le n$. In both cases $L=o(u)$.

**Used from.** D11.11, D11.14, D11.15.

**Proof.**
- D11.22.1 $N_0\le8$; $C_{\rm tpl}N_0(s_0+1)\le8C_{\rm tpl}(2u+1)\le24C_{\rm tpl}u\le n$ for $C_B\ge24C_{\rm tpl}$ ($u\ge1$).
- D11.22.2 Belt tile lies in a cell of side $t_k$; replacement in a square of side $2u$; each $\diam_\infty\le2u\le n$ for $C_B\ge2$.
- D11.22.3 $L=\lfloor n^{1-\ell}\rfloor\le(C_Bu+1)^{1-\ell}=o(u)$.

**Output.** Item 2 of D11.4 for belts and replacements.

**Standard?** Specific to this paper.

#### D11.23 Step — Cut clearance of belt and replacement templates; hypotheses of Lemma 9.4
*Source: 10-geometry.tex 742–758.*

**Statement.** All birth templates of belt tiles and of their descendant replacements have $\dist_\infty(T,Z)\ge(C_0-1)r$, exceeding both $4D_0s_0$ and $2n^\beta$. These checks give the exact hypotheses of Lemma 9.4 for every birth template: dilated layers up to $L$ have the stipulated row and perimeter bounds, and the safe-box estimate gives the core and shell entropy bounds needed by Prop 9.6. The verification uses the finite union of convex pieces; no claim that a primary, a sector run, or its intersection with $A$ is a rectangle is needed.

**Used from.** D11.6, D11.15, D11.22; Lemma 9.4; Prop 9.6.

**Proof.**
- D11.23.1 A belt cell in $D_k$ has $\dist_\infty(\cdot,Z)\ge C_0r$ on its closure, so also at any mark on it.
- D11.23.2 By D11.15, every descendant lies within $2d(S)\le2S^{\rho_0}\le2t_k^{\rho_0}=o(t_k)$ of that mark ($S\le t_k$).
- D11.23.3 Increase $k_0$: $2t_k^{\rho_0}\le r$ $\Rightarrow$ descendant birth templates have $\dist_\infty(T,Z)\ge(C_0-1)r$. Covers replacements extending into the dummy region.
- D11.23.4 Side scales $s_0\le2t_k=o(r)$ so $4D_0s_0<(C_0-1)r$; $n\le C t_k$ gives $n^\beta=o(r)$ so $2n^\beta<(C_0-1)r$.

**Output.** `geometry:cut-clearance` for belts and replacements (D11.25); separation of the templates from the cut (Def 9.3) for D11.26.

**Standard?** Specific to this paper.

#### D11.24 Step — Order of thresholds (`geometry:fine-clearance`)
*Source: 10-geometry.tex 760–775.*

**Statement.** Fix in this order: (i) $C_0,C_P,C_B$ and the absolute isolation constant $a_0$; (ii) increase $S_*$ until `trim-margins` holds, all belt and replacement scanner scales are $\ge n_*$, and
$$c_1u^{\rho_0}>2\lceil C_Bu\rceil^\beta\qquad(u\ge S_*);$$
(iii) increase $k_0$ so that initial belt scales exceed $S_*$, primary scales exceed $n_*$, and all large-scale inequalities used hold: for primaries the same-layer gap $t_k>2n^\beta$, non-adjacent-layer gaps, and `geometry:primary-limits`. Floors and ceilings change only fixed multiplicative constants.

**Used from.** D11.2, D11.14, D11.18, D11.21–D11.23.

**Proof (fine-clearance).** $\lceil C_Bu\rceil\le2C_Bu$, so $2\lceil C_Bu\rceil^\beta\le2(2C_B)^\beta u^\beta$ and $c_1u^{\rho_0}/(2\lceil C_Bu\rceil^\beta)\ge c\,u^{\rho_0-\beta}\to\infty$ since $\rho_0>\beta$. Fix $S_*$ with this ratio $>1$ for $u\ge S_*$.

**Output.** `geometry:ordered-clearance` for belts and replacements (D11.25). Quantifier order behind D11.4 (constants before thresholds).

**Standard?** Specific to this paper.

**Pitfall.** $k_0$ is chosen after $S_*$ and $n_*$; $S_*$ after $a_0,c_1$, which do not depend on $k_0$ (D11.13 Pitfall, D11.18).

#### D11.25 Step — Conclusion of Proposition 11.2
*Source: 10-geometry.tex 777–799.*

**Statement.** Retain the identifiers whose final actual regions meet $A$; $X_i$ = those intersections, in the order of D11.17. All assertions of Prop 11.2 hold.

**Used from.** D11.6, D11.7, D11.10, D11.16–D11.24.

**Proof.**
- D11.25.1 Finiteness and partition. The $X_i$ are pairwise disjoint nonempty subsets of finite $A$, so finitely many. By D11.16 they partition $A\setminus D$; $X_i$ lies in its birth template. Items 1, 2 follow with D11.20–D11.22.
- D11.25.2 Cut clearance (`geometry:cut-clearance`). Primaries: `layer-distance` ($\ge C_0r$) and `primary-limits` ($n^\beta=o(r)$). Belts, replacements: D11.23.
- D11.25.3 Ordered clearance (`geometry:ordered-clearance`). Primaries: earlier same-label primaries are $\ge t_k>2n^\beta$ away in the same layer (D11.10, D11.21); in other layers they are in layers differing by $\ge2$, at distance $\ge\frac{C_0-1}22^{\max(h,k)}>2n^\beta$ (D11.7; with $i$ in layer $k$, $n_i^\beta=o(2^{k})\le o(2^{\max(h,k)})$ from D11.21). Belts, replacements: Lemma 11.5 and `fine-clearance`. Restricting an older actual region to $A$ keeps the lower bounds.
- D11.25.4 Summability. $\le Cb$ primaries per layer with $n\ge c\,2^{(1+2\delta_0)k}$: $Cb\sum_{k\ge k_0}2^{-100(1+2\delta_0)k}\le C'b$. Other tiles: $O(b)$ many (D11.19), each $n\ge1$, so their sum is $O(b)$.

**Output.** Prop 11.2 (D11.4).

**Standard?** Specific to this paper.

---

### 11.8 Proof of the area law

#### D11.26 Theorem 1.1 — Proof of the area law
*Source: 10-geometry.tex 801–857. Authoritative proof; D1.4 points here.*

**Statement.** For every $q,R,J,\Delta$ there is $C=C(q,R,J,\Delta)$ with $S_\Omega(A)\le C|\partial_\Lambda A|$ for every finite induced square-lattice domain $\Lambda$, every admissible $H$ with unique ground vector $\Omega$ and gap $\ge\Delta$, and every $A\subseteq\Lambda$ (D1.4).

**Used from.** D1.4 (statement), D1.6 ($Z=Z_A$), D2.11 (`01-preliminaries.tex` L118–L121: $q=1$, $R=0$), D2.12 (Lemma 2.2), D11.1, D11.4, Prop 9.6 (collar, `08-scanner.tex` L808–L944), D10.4 (Prop 10.2, `09-amplification.tex` L261–L576, $M=100$), Def 9.3.

**Proof.** $b=|\partial_\Lambda A|$.
- D11.26.1 Trivial cases. $\Lambda=\varnothing$ or $A\in\{\varnothing,\Lambda\}$: $S_\Omega(A)=0$ (purity, $S_\Omega(\Lambda)=0$; tex 804). $q=1$, $R=0$: $S_\Omega(A)=0$ by D2.11. $b=0$: Lemma 2.2 gives $S_\Omega(A)=0$. Afterwards $q\ge2$, $R\ge1$, $\Lambda\ne\varnothing$, $b>0$.
- D11.26.2 Choose $n_*$ so that Props 9.6 and 10.2 with $M=100$ apply to all templates of Prop 11.2 uniformly in the stated template bounds, and every radius $r$ supplied by Prop 10.2 at scale $n\ge n_*$ has $L+2r<n^\beta$. Take $D,X_i,T_i,n_i,f_i$ from Prop 11.2 with $Z=Z_A$; its constant $C_1$ is independent of $\Lambda,A$. Set
$$S_i=A\cap\bigl(T_i+[-L_i,L_i]^2_{\mathbb Z}\bigr),\qquad J_i=(\Lambda\setminus A)\cup\bigcup_{j<i,\,f_j=f_i}X_j .$$
Item 2 of Prop 11.2 gives $L_i\le s_i$ and cut separation, so Prop 9.6 ($L=\lfloor n^{1-10^{-5}}\rfloor$, $X=A\cap T$, $S_0=A\cap T_L$) applies for $n_i\ge n_*$: $I_\Omega(A\cap T_i:\Lambda\setminus S_i)\le Cn_i^{1-\varepsilon}$, $\varepsilon=10^{-5}=\ell$; $|S_i|\le Cn_i^2$; the cuts of $A\cap T_i$, $S_i$, $S_i\setminus(A\cap T_i)$ have $O(n_i)$ edges. These are the hypotheses of Prop 10.2 with uniform $C_0$; with $X=A\cap T_i$, $S_0=S_i$ it gives $r_i\le C_Mn_i^{(1-\varepsilon)/\alpha}$, $L_i+2r_i=o(n_i^\beta)$, and $I_\Omega(A\cap T_i:J)\le Cn_i^{-100}$ for every $J\subseteq\Lambda\setminus N^\Lambda_{2r_i}(S_i)$.
- D11.26.3 $J_i\subseteq\Lambda\setminus N^\Lambda_{2r_i}(S_i)$, for the whole $J_i$ at once:
  - a graph path of length $\le2r_i$ from $S_i$ stays within ambient distance $L_i+2r_i<n_i^\beta$ of $T_i$ (start within $L_i$ of $T_i$; each graph step moves $\le1$);
  - `ordered-clearance` $\dist_\infty(T_i,\bigcup_{j<i,f_j=f_i}X_j)>2n_i^\beta>n_i^\beta$ $\Rightarrow$ the path meets no earlier same-family $X_j$;
  - a path reaching $\Lambda\setminus A$ contains, at its first cut crossing, an endpoint of a cut edge, a point of $Z$, within $<n_i^\beta$ of $T_i$; contradicts `cut-clearance` $\dist_\infty(T_i,Z)>2n_i^\beta$. Alternatively $2n_i^\beta>L_i+n_i^\beta$ is the cut-clearance hypothesis of Prop 10.2, which then states $N_{2r_i}(S_i)\subseteq A$.
- D11.26.4 Prop 10.2 (holds for every such $J$, and for any subset of $X$ in place of $X$) and monotonicity under discarding part of the first system, $X_i\subseteq A\cap T_i$: $I_\Omega(X_i:J_i)\le I_\Omega(A\cap T_i:J_i)\le Cn_i^{-100}$. $J_i$ is one set. All estimates concern the same $\Omega$; the auxiliary construction inside each may differ.
- D11.26.5 Lemma 11.1 with $\psi=\Omega$, $\varepsilon_i=Cn_i^{-100}$, $S(D)\le|D|\log q$: $S_\Omega(A)\le|D|\log q+\frac C2\sum_in_i^{-100}\le C_1b\log q+\frac C2C_1b=:C'b$ by items 1, 4 of Prop 11.2.
- D11.26.6 All thresholds and constants depend only on $q,R,J,\Delta$ (and fixed template constants, $n_*$); none on size, shape, connectedness or holes of $\Lambda$, or on $A$. Quantifiers: $\forall(q,R,J,\Delta)\ \exists C\ \forall(\Lambda,H,A)$.

**Output.** Theorem 1.1, eq. `eq:area-law`. Corollary 1.2 (D1.7) is deduced from it in §1.

**Standard?** Assembly specific to this paper; final step is the entropy-decomposition argument enabled by D11.1.

**Pitfall.** $n_*$ is fixed *before* the radii $r_i$ (they exist only for $n_i\ge n_*$), and $n_*$ enters Prop 11.2's constant $C_1$. Amplification gives $I(X:J)$ for $J$ outside $N_{2r}(S_0)$ with $S_0$ the *dilated* set, hence the margin $L_i+2r_i<n_i^\beta$.

---

## Parameters and constants

| Symbol | Value / meaning | Fixed where |
|---|---|---|
| $\beta$ | $1-2\cdot10^{-6}$ | §10 `eq:amplification-exponents`; D11.2 |
| $\varepsilon$ (collar) | $10^{-5}$ ($=\ell$); distinct from the $\varepsilon_i$ of D11.1 | §9 Prop 9.6; D11.26.2 |
| $\delta_0$ | $2\cdot10^{-7}$ | D11.2 (`geometry:exponents`) |
| $\zeta$ | $1-\delta_0/2$ | D11.2 |
| $\rho_0$ | $(1+\beta)/2=1-10^{-6}$ | D11.2 |
| $\ell$ | $10^{-5}$; $L_i=\lfloor n_i^{1-\ell}\rfloor$ | D11.2, D11.4(2) |
| $M$ | $100$ (decay $n_i^{-M}$) | D11.26.2 |
| $D_0$ | $>2R+10$, safety factor of a template | §3 (`02-initial.tex` 225); D11.4 |
| $C_{\rm tpl}$ | template constant ($n\ge C_{\rm tpl}N_0(s_0+1)$) | Def 9.3 |
| $n_*$ | threshold from Props 9.6, 10.2 and $L+2r<n^\beta$ | D11.26.2 |
| $o$ | $(\sqrt2,\sqrt3)$ | D11.5 |
| $r$ | $2^k$, layer-cell side | D11.5 |
| $C_0$ | integer $>100(D_0+1)$ (needs $\ge2$ and $>4D_0$) | D11.5 |
| $k_0$ | lower layer index; large, chosen last | D11.8, D11.24 |
| $N_k,D_k,\mathcal Z_k$ | cell neighbourhoods, layers, endpoint cells | D11.6 |
| $s_k$ | $2^{\lfloor(1+\delta_0)k\rfloor}$, pitch | D11.8 |
| $t_k$ | $2^{\lfloor\zeta k\rfloor}$, strip width, fine-cell side | D11.8 |
| belt count | $\le Cb\,r^2/(s_kt_k)\le Cb\,2^{-k\delta_0/2}$ | D11.9 |
| primary pieces | $\le C(s_k/r+2)^2$ | D11.10 |
| marks per belt cell | $9$ (centre, 4 corners, 4 midpoints) | D11.12 |
| triangles per fan | $\le8$ | D11.11 |
| $a_0$ | absolute isolation constant; small, common to D11.13 and D11.15 | D11.13, D11.15.3 |
| $d(S)$ | $2^{\lfloor\rho_0\log_2S\rfloor}$, trim halfside | D11.14 |
| margins | $\frac12S^{\rho_0}\le d(S)\le S^{\rho_0}$, $d(S)\le\frac{a_0}{1000}S$ | D11.14 |
| $S_*$ | stopping scale; first from margins, then enlarged for $\ge2$ terminal halfside, $\ge n_*$ scales and `fine-clearance` | D11.14, D11.16, D11.24 |
| depth, descendants | $C+C\log\log(e^e+S)$; $\le C(\log(S+2))^C$; $\le9$ children | D11.19 |
| $\lambda$ | contact-square radius factor, small, fixed | D11.18.3 |
| $c_1,c_2,c_3,c_4$ | separation constants ($c_1=\min\{c_2,c_3c_4,1\}$; $c_3=1/(2\sqrt2)$ works; $c_4=\frac14$ works) | D11.18 |
| $C_P$ | primary scale constant, $n=\lceil C_Pr^{1+2\delta_0}\rceil$ | D11.21 |
| $C_B$ | belt/replacement scale constant, $n=\lceil C_Bu\rceil$ | D11.22 |
| $L_i,S_i,J_i,r_i$ | collar width, dilated set, remote set, amplification radius ($r_i\le C_Mn_i^{(1-\varepsilon)/\alpha}$) | D11.26.2 |
| $b$, $Z$ | $|\partial_\Lambda A|$; endpoint set ($|Z|\le2b$) | D11.4 |
| $C$, $C_1$ | depend on $q,R,J,\Delta$, template constants, $n_*$; not on $\Lambda,A$; $C_1$ = Prop 11.2's constant | D11.4, D11.26.6 |

## Dependencies

Consumed:
- §1: Theorem 1.1 statement (D1.4); endpoint set $Z$ (D1.6); reduction note (D1.12, D1.18).
- §2: entropy and mutual-information definitions, purity, SSA (D2.1, D2.2); $q=1$, $R=0$ cases (`01-preliminaries.tex` L118–L121); Lemma 2.2 (D2.12); constants convention (D2.13).
- §3: $D_0>2R+10$, "safe" (`02-initial.tex` 225).
- §9 (scanner): Def 9.3 (template, $C_{\rm tpl}$), Lemma 9.4 (rows, coverings, shell entropy), Prop 9.6 (collar bound, $\varepsilon=\ell=10^{-5}$).
- §10 (amplification): exponents $\beta,\varepsilon,\alpha$; Prop 10.2 (decay $n^{-M}$ for $J$ outside $N_{2r}(S_0)$; $r\le C_Mn^{(1-\varepsilon)/\alpha}$, $L+2r=o(n^\beta)$).
- External: SSA (Lieb–Ruskai 1973); chain rule and subadditivity of von Neumann entropy.

Exported:
- Theorem 1.1 (the area law, `eq:area-law`) and, through §1, Corollary 1.2.
- Nothing is consumed by a later section.
