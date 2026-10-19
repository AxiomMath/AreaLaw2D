# Digest of §1 — Introduction

Sources: `paper/sections/00-introduction.tex` (216 lines), `paper/sections/00-history.tex` (117 lines, `\input` at introduction line 89). Paper numbering throughout: §2 = `01-preliminaries`, §3 = `02-initial`, §4 = `03-quasilocal`, §5 = `04-conditional`, §6 = `05-replicas`, §7 = `06-transport`, §8 = `07-comparators`, §9 = `08-scanner`, §10 = `09-amplification`, §11 = `10-geometry`.

## Section in one paragraph

§1 fixes the setting (finite induced subgraph $\Lambda\subset\mathbb Z^2$, local dimension $q$, Hamiltonians with supports of $d_\Lambda$-diameter $\le R$ and term norms $\le J$, global gap $\Delta$) and states Theorem 1.1: $S_\Omega(A)\le C|\partial_\Lambda A|$, $C=C(q,R,J,\Delta)$ independent of $\Lambda$, $A$, $H$. Corollary 1.2 converts to the two vertex-boundary conventions and covers rectangles. Then a tensor-network consequence proved in a companion paper, and a five-stage outline reducing the area law to one analytic statement (mutual information of a region with everything beyond a collar is $O(n^{-100})$) and one geometric statement (cover $A$ minus $O(|\partial_\Lambda A|)$ sites by two ordered families of well-separated templates). Only Cor 1.2 is proved in §1; Theorem 1.1 is proved at the end of §11 from §2–§11. Conventions exported: $d_\Lambda$, $\partial_\Lambda$, $Z_A$, $I_\Omega$, natural logarithms, $C=C(q,R,J,\Delta)$.

---

#### D1.1 Def — Domain, graph distance, Hilbert space

Source: `00-introduction.tex` L12–L18.

**Statement.**
- $\Lambda\subset\mathbb Z^2$ finite. Edges: pairs $\{x,y\}\subseteq\Lambda$ with $|x-y|_2=1$ (equivalently $|x-y|_1=1$). $\Lambda$ carries the induced graph.
- $d_\Lambda$ = graph distance in this graph; $d_\Lambda(x,y)=+\infty$ for $x,y$ in different components.
- $\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}\mathbb C^q$. An operator supported on $X\subseteq\Lambda$ acts as the identity on the factors outside $X$.

**Used from.** none.
**Output.** $d_\Lambda$ (not the ambient metric) controls support, propagation and neighborhoods; $N_r^\Lambda$, $B_\Lambda(x,r)$ of §2 are built on it.
**Standard?** Convention.
**Pitfall.** Holes and thin necks: sites at ambient distance 2 across a missing site can have $d_\Lambda=\infty$. $d_\Lambda\ge|\cdot|_1\ge|\cdot|_\infty$, so graph neighborhoods of radius $r$ sit inside ambient neighborhoods of radius $r$ (D11.26.3).

---

#### D1.2 Def — Admissible Hamiltonian (eq:hamiltonian)

Source: `00-introduction.tex` L18–L27.

**Statement.** Fix integers $q\ge1$, $R\ge0$ and a real $J>0$. $H$ is admissible if
$$H=\sum_{\substack{\varnothing\neq X\subseteq\Lambda\\ \operatorname{diam}_{d_\Lambda}X\le R}}h_X,\qquad h_X=h_X^*,\qquad\|h_X\|\le J,$$
with $h_X$ supported on $X$. One summand per support $X$; $h_X=0$ allowed.

**Used from.** D1.1.
**Output.** The counting constants of §2: $|B_\Lambda(x,r)|\le v_r=1+2r(r+1)$ (D2.7); at most $\mu_R=2^{v_R-1}$ terms contain a site, norms summing to $\le J\mu_R$ (D2.8); $\#\{\text{terms split by }D\}\le2v_R\mu_R|\partial_\Lambda D|$ (D2.9).
**Standard?** Bookkeeping choice of the paper.
**Pitfall.**
- One summand per support makes $\mu_R$ depend on $R$ only. Several physical terms on one support must be merged first; the merged norm bound is $J$.
- $\operatorname{diam}_{d_\Lambda}X\le R$: all pairs in $X$ within graph distance $R$; for $R=0$ only singletons. A support meeting two components has diameter $\infty$ and is excluded.

---

#### D1.3 Def — Edge boundary, reduced state, entanglement entropy

Source: `00-introduction.tex` L29–L37.

**Statement.**
- $\partial_\Lambda A=\{\{x,y\}: x\in A,\ y\in\Lambda\setminus A,\ |x-y|_1=1\}$ for $A\subseteq\Lambda$.
- For a unit vector $\Omega\in\mathcal H_\Lambda$: $\rho_A=\operatorname{Tr}_{\Lambda\setminus A}|\Omega\rangle\langle\Omega|$, $S_\Omega(A)=-\operatorname{Tr}\rho_A\log\rho_A$, $0\log0=0$. Logarithms natural.

**Used from.** D1.1.
**Output.** $b:=|\partial_\Lambda A|$. $S_\Omega(A)=S_\Omega(\Lambda\setminus A)$ (purity); $S_\Omega(\varnothing)=0$; $S_\Omega(A)\le|A|\log q$ (§1 L3–L6; D11.26.5).
**Standard?** Standard.
**Pitfall.** $\partial_\Lambda$ counts only edges of the induced graph: $\partial_\Lambda\Lambda=\varnothing$.

---

#### D1.4 Theorem 1.1 — Area law

Source: `00-introduction.tex` L39–L53 (statement). Proof: `10-geometry.tex` L801–L857.

**Statement.** For all integers $q\ge1$, $R\ge0$ and reals $J>0$, $\Delta>0$ there is a finite $C=C(q,R,J,\Delta)$ such that the following holds. Let $\Lambda\subset\mathbb Z^2$ be a finite induced square-lattice domain and $H$ an admissible Hamiltonian (D1.2) on $\mathcal H_\Lambda$ with a unique normalized ground vector $\Omega$ (up to phase), ground energy $E_0$, and
$$H-E_0\,\mathrm{id}\ \ge\ \Delta\bigl(\mathrm{id}-|\Omega\rangle\langle\Omega|\bigr).$$
Then for every $A\subseteq\Lambda$
$$S_\Omega(A)\le C\,|\partial_\Lambda A|\qquad\text{(eq:area-law)}.$$
The same $C$ serves all such $\Lambda$, $A$, $H$.

**Used from.** D1.1, D1.2, D1.3, D1.6 ($Z=Z_A$), D1.11, D1.12 (Lemma 11.1), D1.16 (Prop 9.6), D1.17 (Prop 10.2), D1.18 (Prop 11.2); Lemma 2.2 (§2).
**Proof.** D11.26.

**Output.** Cor 1.2 (D1.7); D1.10.
**Standard?** Specific to this paper. Context: D1.8.
**Pitfall.**
- Quantifier order: $\forall(q,R,J,\Delta)\ \exists C\ \forall(\Lambda,H,A)$. $C$ is uniform in the domain, its shape, holes, connectedness, and $H$.
- Gap hypothesis is the operator inequality. Given $H\Omega=E_0\Omega$ it forces uniqueness: for $\varphi\perp\Omega$ with $H\varphi=E_0\varphi$, $0=\langle\varphi,(H-E_0)\varphi\rangle\ge\Delta\|\varphi\|^2$ gives $\varphi=0$.

---

#### D1.5 Step — Remarks after Theorem 1.1

Source: `00-introduction.tex` L55–L58.

**Statement.**
- The diameter bound in eq:hamiltonian uses $d_\Lambda$ of the induced graph; matters for holes or several components.
- The spectral hypothesis concerns the full $H$ on $\Lambda$; no gap for restrictions of $H$ to smaller regions.

**Used from.** D1.2, D1.4.
**Output.** Induced-graph locality only (§4 propagation, Lemma 4.1); gap of $H$ itself (Prop 4.3; Lemma 3.2).
**Standard?** Specific to this paper (contrast: local-gap hypotheses in D1.8).

---

#### D1.6 Def — Inner boundary and endpoint set

Source: `00-introduction.tex` L60–L67.

**Statement.** For $A\subseteq\Lambda$:
$$\partial_{\rm in}A=\{x\in A:\ \exists y\notin A,\ \{x,y\}\in\partial_\Lambda A\},\qquad Z_A=\bigcup_{e\in\partial_\Lambda A}e .$$
$Z_A=\partial_{\rm in}A\ \dot\cup\ \partial_{\rm out}A$ with $\partial_{\rm out}A\subseteq\Lambda\setminus A$ the outer endpoints (notation of this digest, not of the paper).

**Used from.** D1.3.
**Output.** $Z_A$ (written $Z$ in §3, §9, §11) is the reference set for all clearances: safe boxes (D3.3, $D_0>2R+10$), templates (D9.14, clearance $4D_0s_0$), Prop 11.2.
**Standard?** Standard.

---

#### D1.7 Corollary 1.2 — Rectangles and vertex boundaries

Source: `00-introduction.tex` L69–L86.

**Statement.**
(a) The conclusion of Theorem 1.1 holds for every subset of a finite rectangular square lattice with bounded on-site and nearest-neighbor interactions and a unique ground state separated by a fixed global gap.
(b) For every domain covered by Theorem 1.1 and with $C$ its constant:
$$S_\Omega(A)\le4C|\partial_{\rm in}A|,\qquad S_\Omega(A)\le2C|Z_A|.$$

**Used from.** D1.4, D1.6.
**Proof.**
- D1.7.1 (a): $\Lambda=\{1,\dots,L_1\}\times\{1,\dots,L_2\}$ is an induced domain. Supports $\{x\}$ and $\{x,y\}$ with $|x-y|_1=1$ have $d_\Lambda$-diameter $\le1$. Merge terms on equal supports (norm $\le J$ after merging); $H$ is admissible with $R=1$, $C=C(q,1,J,\Delta)$.
- D1.7.2 $|\partial_{\rm in}A|\le|\partial_\Lambda A|$: $e\mapsto$ (its endpoint in $A$) maps $\partial_\Lambda A$ onto $\partial_{\rm in}A$.
- D1.7.3 $|\partial_\Lambda A|\le4|\partial_{\rm in}A|$: each $x\in\partial_{\rm in}A$ has between 1 and 4 crossing edges (degree $\le4$ in $\mathbb Z^2$). So $S_\Omega(A)\le C|\partial_\Lambda A|\le4C|\partial_{\rm in}A|$.
- D1.7.4 $|Z_A|\le2|\partial_\Lambda A|$: union of $|\partial_\Lambda A|$ two-element sets.
- D1.7.5 $|\partial_\Lambda A|\le2|Z_A|$: $c(v)$ = number of crossing edges at $v\in Z_A$; $1\le c(v)\le4$ and $\sum_{v\in Z_A}c(v)=2|\partial_\Lambda A|$ (each edge counted at both endpoints). So $2|\partial_\Lambda A|\le4|Z_A|$ and $S_\Omega(A)\le C|\partial_\Lambda A|\le2C|Z_A|$.
- D1.7.6 Empty boundary: $\partial_\Lambda A$, $\partial_{\rm in}A$, $Z_A$ empty simultaneously; inequalities read $0\le0$.

**Output.** Not used by §2–§11.
**Standard?** Elementary counting.
**Pitfall.** The paper writes $|\partial_{\rm in}A|\le|\partial_\Lambda A|\le4|\partial_{\rm in}A|$ and $|Z_A|\le2|\partial_\Lambda A|\le4|Z_A|$. Factor 2 in $S_\Omega(A)\le2C|Z_A|$ needs the double count over both endpoints (D1.7.5); $|\partial_\Lambda A|\le4|\partial_{\rm in}A|\le4|Z_A|$ would give 4.

---

#### D1.8 Step — History and related work

Source: `00-history.tex` L1–L117.

**Statement.**
- Area-law question: field-theory origin (Bombelli–Koul–Lee–Sorkin 1986; Srednicki 1993); lattice gap-to-area conjecture (Hastings 2007; Arad–Landau–Vazirani 2012).
- $d=1$: Hastings 2007 (finite-range, bounded interactions, fixed local dimension, gap); ALV 2012 improve inverse-gap dependence for frustration-free chains via approximate ground-state projectors; AKLV 2013 general chains; Brandão–Horodecki 2015 area law for pure 1D states from exponential decay of correlations between arbitrary separated regions. Exponential clustering (Nachtergaele–Sims 2006) gives only decay of connected correlations of separated observables; Anshu–Harrow–Soleimanifar 2022 bound smooth entanglement spread, not entropy.
- $d\ge2$: strict area law only for special classes (Cramer–Eisert–Plenio–Dreißig 2006, harmonic lattices; Cho 2014 with extra compatibility), or with log corrections under extra hypotheses (Masanes 2009; Brandão–Cramer 2015).
- $d=2$ spins: Anshu–Arad–Gosset 2022 subvolume bounds, $O(b^{5/3}\log^{7/3}(2+b))$ for rectangles and $n^{1+O((\log n)^{-1/5})}$ across a vertical cut; need frustration-free plaquette projectors, unique ground state, local gap.
- Arad–Firanko–Jain 2026: approximate-projector methods for maximally mixed ground states, mutual-information bound, 2D application under frustration-freeness and local gap.
- This paper: frustration allowed, gap only for the full $H$, arbitrary regions of arbitrary finite induced domains.
- Tools cited (no new statements): Lieb–Robinson (Nachtergaele–Ogata–Sims), Kitaev's centered spectral filter, Swingle–McGreevy positive constraints (absolute values retain the full-system gap), products of contractions as in detectability lemmas (Anshu–Arad–Vidick), dissipative Lieb–Robinson (Barthel–Kliesch), Van Acoleyen–Marien–Verstraete (logarithmic commutators), strong subadditivity, Alicki–Fannes–Winter continuity, Schur–Weyl duality (Keyl–Werner), finite quantum de Finetti, weighted operator geometric means, Carlen–Vershynina resolvent-compression identity.

**Used from.** D1.4.
**Output.** none.
**Standard?** Literature survey; references in `paper/references.bib`.

---

#### D1.9 Def — PEPS and bond dimension

Source: `00-introduction.tex` L93–L98.

**Statement.** PEPS: one tensor per site, one physical index (dimension of the local space), one virtual index per incident edge; contracting paired virtual indices gives a vector in the many-body space. Bond dimension of an edge = dimension of its index. Approximation problem: how large must bond dimensions be to approximate the ground vector on the original lattice.

**Used from.** D1.1.
**Output.** D1.10 only.
**Standard?** Standard (Verstraete–Cirac PEPS).

---

#### D1.10 Step — Tensor-network consequence (companion paper)

Source: `00-introduction.tex` L100–L119. External result: `\cite[Theorem 1.1]{OpenAI2026PolynomialPEPS}`.

**Statement.** Companion Theorem 1.1: for the open $L\times L$ square grid, $L\ge2$, on-site and nearest-neighbor interactions, local dimension $q\ge2$, term-norm bound $J>0$, global gap $\Delta>0$, every unique ground vector has a PEPS approximation with maximum bond dimension $\le CL^c$ and global vector error $\le L^{-1}$ after normalization and phase choice. $C,c$ depend only on $q,J,\Delta$. Existence only; no efficient construction or contraction claimed.

Supplied by this paper (the companion also needs compression and routing arguments not here):
- Positive operators annihilating $\Omega$ with rapidly decaying tails: Prop 4.3.
- Collar information bounds: Prop 9.6, Prop 10.2.
- Two families of separated regions with specified shapes and clearances: Prop 11.2.

**Used from.** D1.4 (via Prop 4.3, 9.6, 10.2, 11.2), D1.9.
**Output.** none inside this paper.
**Standard?** Specific to the companion paper (OpenAI 2026, "Polynomial PEPS approximation of gapped square-grid ground states").
**Pitfall.** Not a corollary of Theorem 1.1 alone; uses the by-products listed.

---

#### D1.11 Def — Mutual information

Source: `00-introduction.tex` L123–L130.

**Statement.** For disjoint $B,C\subseteq\Lambda$:
$$I_\Omega(B:C)=S_\Omega(B)+S_\Omega(C)-S_\Omega(B\cup C).$$

**Used from.** D1.3.
**Output.** Analytic target of §3–§10: $I_\Omega(B:C)$ small for $B\subseteq A$, $C$ beyond a collar of $B$, even when $C\supseteq\Lambda\setminus A$. Strong subadditivity (§2, `01-preliminaries.tex` L15–L21): $I\ge0$; $I(B':C')\le I(B:C)$ for $B'\subseteq B$, $C'\subseteq C$.
**Standard?** Standard.

---

#### D1.12 Step — Reduction of $S_\Omega(A)$ to collar information

Source: `00-introduction.tex` L131–L138. Exact statement and proof: Lemma 11.1, `10-geometry.tex` L26–L66 (D11.1).

**Statement.** Let $\psi$ be pure on a finite system with site set $\Lambda$. Let $A=D\,\dot\cup\bigcup_{i\in\mathcal I_0}X_i\,\dot\cup\bigcup_{i\in\mathcal I_1}X_i$, each $\mathcal I_f$ finite and ordered, $B=\Lambda\setminus A$. If
$$I_\psi\Bigl(X_i:\ B\cup\bigcup_{j\in\mathcal I_f,\,j<i}X_j\Bigr)\le\varepsilon_i\qquad(f\in\{0,1\},\ i\in\mathcal I_f),$$
then $S_\psi(A)\le S_\psi(D)+\tfrac12\sum_i\varepsilon_i$, hence $S_\psi(A)\le|D|\log q+\tfrac12\sum_i\varepsilon_i$ (the intro's "sum of the information errors", with factor $\tfrac12$).

**Used from.** D1.11; §2 entropy identities (`01-preliminaries.tex` L8–L24: chain rule, subadditivity, purity).
**Proof.** D11.1; then $S(D)\le|D|\log q$.

**Output.** Separation requirement: each $X_i$ far from $B$ and from earlier tiles of its own family only, not from the other family. Prop 11.2 produces such families; Prop 10.2 supplies each $\varepsilon_i$. Used in D11.26.5.
**Standard?** Chain rule, subadditivity, purity standard (SSA, Lieb–Ruskai 1973, enters only through $I\ge0$ in D1.11). Two-family cancellation specific to this paper.
**Pitfall.** The conditioning set contains all of $B=\Lambda\setminus A$ and all earlier same-family tiles at once; the analytic estimate must bound $I(X_i:J_i)$ for the whole union $J_i$, not piece by piece.

---

#### D1.13 Step — Ambient versus graph locality

Source: `00-introduction.tex` L140–L144.

**Statement.**
- Analytic estimates concern $A\cap Q$ for ambient boxes $Q$ or finite unions of rectangles and triangles (templates, Def 9.3). Clearance is ambient, from $Z_A$. These sets may meet holes or the edge of the domain.
- Hamiltonian locality and propagation use $N_r^\Lambda$ in the induced graph.

**Used from.** D1.1, D1.6.
**Output.** $\operatorname{dist}_\infty$ (ambient) in Prop 11.2 versus $N_{2r}^\Lambda$ in Prop 10.2; bridged by $d_\Lambda\ge|\cdot|_\infty$ (D11.26.3).
**Standard?** Specific to this paper.

---

#### D1.14 Step — Stage 1: a first exponent below volume

Source: `00-introduction.tex` L146–L155. Proved in §3 (`02-initial.tex`).

**Statement.** §3 uses the global gap to bound fluctuations of the negative logarithms of positive marginal eigenvalues, then optimizes products of positive operators on nested rectangles. Two bounds on the optimized norm, one using the energy estimate and global gap, give a conditional-entropy discount, hence
$$S_\Omega(A\cap Q)\le Cr^{1+e_0},\qquad e_0<1,$$
for a box $Q$ of side at most $r$ sufficiently far from $Z_A$. Exact form: D3.16 (Prop 3.3); ingredients D3.1 (Lemma 3.1), D3.4 (Lemma 3.2).

**Used from.** D1.2, D1.4 (hypotheses), D1.6 ($Z$), D1.11.
**Output.** Starting exponent for the bootstrap in Prop 9.5 (D9.19).
**Standard?** Specific to this paper.

---

#### D1.15 Step — Stage 2: information and energy in one interpolation

Source: `00-introduction.tex` L157–L172. Proved in §4–§7.

**Statement.** §4 replaces $H$ by a sum of positive operators that annihilate $\Omega$ separately, retain a global gap, and have rapidly decaying graph-local tails (D4.6 Prop 4.3; truncation D4.11 Prop 4.5). §5–§7 attach positive operators to partitions of the full system and interpolate between them as a small subsystem changes parts; they act on symmetric tensor powers. Applying an inverse power of the interpolating operator to a vector built from ground-state copies and an auxiliary entangled pair defines the filtered vector. As the copy number grows, logarithmic norms per copy compare with combinations of marginal entropies: the decrease of a logarithmic squared norm is bounded below by averaged conditional mutual information up to a small error, and the same transported states bound the energy cost (D7.14 Prop 7.4).

**Used from.** D1.2, D1.4, D1.11.
**Output.** Entropy-gain and energy bounds for §8–§9.
**Standard?** Ingredients standard (Schur–Weyl, de Finetti, weighted operator geometric means: D1.8); their use in one interpolation specific to this paper.

---

#### D1.16 Step — Stage 3: compare norms and scan a collar

Source: `00-introduction.tex` L174–L195. Proved in §8 and §9.

**Statement.** §8 gives two bounds on $-\log$ of the filtered vector's norm: upper from auxiliary dimensions chosen in a high-probability part of the target's Schmidt spectrum and projection of target and auxiliary system onto an entangled pair; lower from the global gap, low physical energy forcing most copies into the ground state (D8.8 Prop 8.1). §9 moves the partitions through a collar by a finite randomized schedule; each interaction is rarely split by a moving boundary and the schedule supplies a low-energy interpolation (D9.9 Prop 9.2). The two norm bounds first improve the box exponent repeatedly (D9.19 Prop 9.5), then give
$$I_\Omega\bigl(A\cap T:\Lambda\setminus(A\cap T_L)\bigr)\le Cn^{1-\varepsilon},$$
$T$ a template (D9.14 Def 9.3), $\varepsilon>0$ fixed, $T_L$ the ambient sup-norm enlargement by $L=\lfloor n^{1-\varepsilon}\rfloor$; targets and enlargements have $O(n)$ boundary edges. Exact form: D9.25 (Prop 9.6).

**Used from.** D1.6, D1.11, D1.14, D1.15.
**Output.** Prop 9.6 is the input of §10.
**Standard?** Specific to this paper.
**Pitfall.** Order of limits: finite physical and auxiliary system and schedule fixed first, then copy number $k\to\infty$ (bound has an $o_k(1)$ remainder). The intro's "$\varepsilon>0$ fixed" is $\varepsilon=10^{-5}$.

---

#### D1.17 Step — Stage 4: amplify the information bound

Source: `00-introduction.tex` L197–L206. Proved in §10.

**Statement.** Typical spectral subspaces give a candidate operator restoring a target moved to an auxiliary reference; its norm is controlled by the collar information. A localized product of contractions from the positive constraints suppresses the excited component; polar decomposition yields a unitary comparison near the target. The unitary leaves reference and remote physical system untouched, so comparison with a state where they are independent bounds the original mutual information. Enlarging the collar by a sublinear radius makes the bound smaller than any prescribed inverse power of $n$. Exact form: D10.4 (Prop 10.2; constants $\varepsilon,\beta,\alpha$ in the table below; containment $N_{2r}(S_0)\subseteq A$ under cut clearance: D10.16).

**Used from.** D1.15 (Prop 4.3), D1.16 (Prop 9.6).
**Output.** Used with $M=100$ in D11.26.
**Standard?** Specific to this paper (related: detectability lemmas, Anshu–Arad–Vidick 2016; dissipative Lieb–Robinson, Barthel–Kliesch 2012).

---

#### D1.18 Step — Stage 5: arrange regions for entropy cancellation

Source: `00-introduction.tex` L208–L215. Proved in §11.

**Statement.** §11 builds the two ordered families of D1.12. The collar around each region avoids $\Lambda\setminus A$ and all earlier regions of its own family. Narrow strips and recursive repairs at point contacts produce these separations for arbitrary cuts, leaving $O(|\partial_\Lambda A|)$ sites uncovered. Information errors are summable over the regions, so the two entropy chains prove eq:area-law. Exact form: D11.4 (Prop 11.2); assembly D11.26.

**Used from.** D1.12, D1.16 (templates), D1.17.
**Output.** Theorem 1.1 (D11.26).
**Standard?** Specific to this paper.

---

## Parameters and constants

All "C" depend only on $q,R,J,\Delta$ unless noted; none on $\Lambda$, $A$, $H$.

| Symbol | Value / range | Where fixed |
|---|---|---|
| $q$ | integer $\ge1$ (reduce to $\ge2$) | D1.2; §2 L118–L122 |
| $R$ | integer $\ge0$ (reduce to $\ge1$) | D1.2; §2 |
| $J$ | real $>0$, $\|h_X\|\le J$ | D1.2 |
| $\Delta$ | real $>0$, gap of full $H$ | D1.4 |
| $C(q,R,J,\Delta)$ | finite | D1.4 |
| $v_r$ | $1+2r(r+1)$, bound on $\lvert B_\Lambda(x,r)\rvert$ | §2, eq:ball-count |
| $\mu_R$ | $2^{v_R-1}$, terms per site | §2 L94–L103 |
| split count | $2v_R\mu_R\lvert\partial_\Lambda D\rvert$ | §2, eq:crossing-count |
| $D_0$ | $>2R+10$ | §3, `02-initial.tex` L225 |
| $e_0$ | $\in(0,1)$ | Prop 3.3 |
| $g=\Delta/c_*$, $p$, $\alpha$ | $p\ge1$ integer, $\alpha=p/(p+1)$ | Prop 4.3; $p$ chosen in §10 |
| $e_*$ | $2\cdot10^{-6}$ | Prop 9.5 |
| $C_{\rm tpl}$ | large constant (absorbs layer-count constant) | §9, `08-scanner.tex` L542 |
| $\varepsilon$ | $10^{-5}$ | §10 eq:amplification-exponents; Prop 9.6 |
| $L$ | $\lfloor n^{1-\varepsilon}\rfloor$ ($=\lfloor n^{1-\ell}\rfloor$ in §11 with $\ell=10^{-5}$) | Prop 9.6; Prop 11.2 |
| $\beta$ | $1-2\cdot10^{-6}$ | §10 eq:amplification-exponents |
| $\alpha>1-10^{-6}$ | $p$ large enough | §10 eq:amplification-exponents |
| $M$ | arbitrary in Prop 10.2; $M=100$ in the proof of Thm 1.1 | §11 L810 |
| $\delta_0,\zeta,\rho_0,\ell$ | $2\cdot10^{-7}$; $1-\delta_0/2$; $(1+\beta)/2$; $10^{-5}$ | §11 eq:geometry:exponents |
| $n_*$ | threshold, large enough for Prop 9.6, Prop 10.2 at $M=100$, and $L+2r<n^\beta$ | §11 L808–L813 |
| exponent in $\sum_in_i^{-100}$ | 100 | Prop 11.2(4) |
| $\partial_{\rm in}$ factor, $Z_A$ factor | 4, 2 | D1.7 |

## Dependencies

**Consumed by §1:** nothing.

**Exported by §1:**
- Conventions (D1.1–D1.3, D1.6, D1.11): $d_\Lambda$, admissible $H$, $\partial_\Lambda$, $\partial_{\rm in}$, $Z_A$, $I_\Omega$, natural logs, constant dependence.
- Theorem 1.1 (D1.4): proved by the last proof of the paper (D11.26).

**Dependency list of the proof of Theorem 1.1:**
1. Theorem 1.1 $\Leftarrow$ Lemma 2.2 ($b=0$) $+$ §2 degenerate cases $+$ Lemma 11.1 $+$ Prop 11.2 $+$ Prop 10.2 (at $M=100$) $+$ Prop 9.6.
2. Lemma 11.1 $\Leftarrow$ chain rule, subadditivity, purity (§2 L8–L24, D1.12).
3. Prop 11.2 $\Leftarrow$ Def 9.3 (templates, $D_0$, $C_{\rm tpl}$); purely geometric, no operator input.
4. Prop 10.2 $\Leftarrow$ Prop 4.3 ($H_F$, $p$, $\alpha$), Lemma 4.4 (square roots and local channels), Lemma 10.1 (local constraint products), Lemma 2.1 (continuity), Lemma 3.1 (tails); input information bound from Prop 9.6.
5. Prop 9.6 $\Leftarrow$ Prop 9.5 (improved box exponent), Lemma 9.4 (rows, coverings, shell entropy), Prop 9.2 (scanner), Prop 8.1 (comparators).
6. Prop 9.5 $\Leftarrow$ Prop 3.3 (initial exponent $e_0$), Prop 9.2, Prop 8.1.
7. Prop 9.2 $\Leftarrow$ Prop 8.1 (norm comparisons), Prop 7.4 (transport), Lemma 9.1 (scan geometry and probabilities); §9 works with the Hamiltonian truncated by Prop 4.5 (`08-scanner.tex` L50).
8. Prop 8.1 $\Leftarrow$ Lemma 6.1 (Schur labels), Lemma 3.1 (marginal tails), eq transport:vector-jensen of §7.
9. Prop 7.4 $\Leftarrow$ Lemmas 7.1–7.3 (mean trees, derivative maps, Fourier multipliers), Lemma 5.3 (skew), Lemmas 6.2–6.4 (integral formula, relative pin, marked-copy symbols); Lemma 6.3 uses Lemma 5.1 (movement).
10. Prop 3.3 $\Leftarrow$ Lemma 3.2 (buffered rectangle) $\Leftarrow$ Lemma 3.1 (marginal tails) and §2 counting bounds.

Items 4–10 read off `\ref` cross-references in the tex files.

**Sections consumed by the proof of Thm 1.1:** §2–§11.
