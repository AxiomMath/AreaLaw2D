# Digest of §1 — Introduction

Sources: `paper/sections/00-introduction.tex` (216 lines), `paper/sections/00-history.tex` (117 lines, `\input` at introduction line 89). Paper numbering is used throughout: §2 = `01-preliminaries`, §3 = `02-initial`, §4 = `03-quasilocal`, §5 = `04-conditional`, §6 = `05-replicas`, §7 = `06-transport`, §8 = `07-comparators`, §9 = `08-scanner`, §10 = `09-amplification`, §11 = `10-geometry`. Digest anchors of other sections are not fixed yet; cross-references below cite paper numbers (e.g. Prop 9.6) and tex files.

## Section in one paragraph

§1 fixes the setting (finite induced subgraph $\Lambda\subset\mathbb Z^2$, local dimension $q$, Hamiltonians with supports of $d_\Lambda$-diameter $\le R$ and term norms $\le J$, global gap $\Delta$) and states the only theorem of the paper: Theorem 1.1, $S_\Omega(A)\le C|\partial_\Lambda A|$ with $C=C(q,R,J,\Delta)$ independent of $\Lambda$, $A$, $H$. Corollary 1.2 converts the edge boundary to the two vertex-boundary conventions and covers rectangles. §1 then records a tensor-network consequence proved elsewhere (a companion paper), and a five-stage proof outline. The outline reduces the area law to one analytic statement (mutual information of a region with everything beyond a collar is $O(n^{-100})$) and one geometric statement (cover $A$ minus $O(|\partial_\Lambda A|)$ sites by two ordered families of well-separated templates). Only Cor 1.2 is proved in §1 (edge counting); the proof of Theorem 1.1 sits at the end of §11 and consumes §2–§11. All later sections use the §1 conventions: $d_\Lambda$, $\partial_\Lambda$, $Z_A$, $I_\Omega$, natural logarithms, and the constant dependence $C=C(q,R,J,\Delta)$.

---

#### D1.1 Def — Domain, graph distance, Hilbert space

Source: `00-introduction.tex` L12–L18.

**Statement.**
- $\Lambda\subset\mathbb Z^2$ finite. Edges: pairs $\{x,y\}\subseteq\Lambda$ with $|x-y|_2=1$ (equivalently $|x-y|_1=1$). $\Lambda$ carries the induced graph.
- $d_\Lambda$ = graph distance in this graph; $d_\Lambda(x,y)=+\infty$ for $x,y$ in different components.
- $\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}\mathbb C^q$. An operator supported on $X\subseteq\Lambda$ acts as the identity on the factors outside $X$.

**Used from.** none.
**Output.** Every later section: induced-graph metric (not the ambient metric of $\mathbb Z^2$) controls support, propagation and neighborhoods; $N_r^\Lambda$, $B_\Lambda(x,r)$ of §2 are built on $d_\Lambda$.
**Standard?** Convention.
**Pitfall.** Holes and thin necks: sites at ambient distance 2 across a missing site can have $d_\Lambda=\infty$. $d_\Lambda\ge|\cdot|_1\ge|\cdot|_\infty$, so graph neighborhoods of radius $r$ sit inside ambient neighborhoods of radius $r$ (used in D1.4.5 below).

---

#### D1.2 Def — Admissible Hamiltonian (eq:hamiltonian)

Source: `00-introduction.tex` L18–L27.

**Statement.** Fix integers $q\ge1$, $R\ge0$ and a real $J>0$. $H$ is admissible if
$$H=\sum_{\substack{\varnothing\neq X\subseteq\Lambda\\ \operatorname{diam}_{d_\Lambda}X\le R}}h_X,\qquad h_X=h_X^*,\qquad\|h_X\|\le J,$$
with $h_X$ supported on $X$. One summand per support $X$; $h_X=0$ allowed. The paper notes this convention bounds the sum of interaction norms at every site in terms of $R,J$ alone.

**Used from.** D1.1.
**Output.**
- Ball count (§2, `01-preliminaries.tex` L85–L87, eq:ball-count): $|B_\Lambda(x,r)|\le v_r=1+2r(r+1)$.
- Per-site count (§2, L94–L103): each nonzero term gets an anchor in its support. Supports containing $x$ are subsets of $B_\Lambda(x,R)$ containing $x$. So at most $\mu_R=2^{v_R-1}$ terms contain $x$, and their norms sum to $\le J\mu_R$.
- Split-term count (§2, L105–L113, eq:crossing-count). A term is split by $D$ if its support meets $D$ and $\Lambda\setminus D$. A graph path of length $\le R$ from its anchor to the other side crosses $\partial_\Lambda D$, so the anchor is within $d_\Lambda\le R$ of $Z_D$. At most $v_R|Z_D|\le2v_R|\partial_\Lambda D|$ sites qualify, each anchors $\le\mu_R$ terms. Hence $\#\{\text{terms split by }D\}\le2v_R\mu_R|\partial_\Lambda D|$.
**Standard?** Specific bookkeeping choice of the paper.
**Pitfall.**
- One summand per support is what makes $\mu_R$ depend on $R$ only. Several physical terms on one support must be merged first; the merged norm bound is then $J$.
- $\operatorname{diam}_{d_\Lambda}X\le R$ means all pairs in $X$ are within graph distance $R$; for $R=0$, only singletons. A support meeting two components has diameter $\infty$ and is excluded.

---

#### D1.3 Def — Edge boundary, reduced state, entanglement entropy

Source: `00-introduction.tex` L29–L37.

**Statement.**
- $\partial_\Lambda A=\{\{x,y\}: x\in A,\ y\in\Lambda\setminus A,\ |x-y|_1=1\}$ for $A\subseteq\Lambda$.
- For a unit vector $\Omega\in\mathcal H_\Lambda$: $\rho_A=\operatorname{Tr}_{\Lambda\setminus A}|\Omega\rangle\langle\Omega|$, $S_\Omega(A)=-\operatorname{Tr}\rho_A\log\rho_A$, $0\log0=0$. Logarithms natural.

**Used from.** D1.1.
**Output.** $b:=|\partial_\Lambda A|$ is the area in Theorem 1.1. $S_\Omega(A)=S_\Omega(\Lambda\setminus A)$ (purity); $S_\Omega(\varnothing)=0$. Volume bound $S_\Omega(A)\le|A|\log q$ (dimension bound, §1 L3–L6; cf. D1.12.5); Theorem 1.1 replaces $|A|$ by $|\partial_\Lambda A|$.
**Standard?** Standard definitions.
**Pitfall.** $\partial_\Lambda$ counts only edges of the induced graph. The physical edge of $\Lambda$ contributes nothing: $\partial_\Lambda\Lambda=\varnothing$.

---

#### D1.4 Theorem 1.1 — Area law

Source: `00-introduction.tex` L39–L53 (statement). Proof: `10-geometry.tex` L801–L857 ("Proof of the area law").

**Statement.** For all integers $q\ge1$, $R\ge0$ and reals $J>0$, $\Delta>0$ there is a finite $C=C(q,R,J,\Delta)$ such that the following holds. Let $\Lambda\subset\mathbb Z^2$ be a finite induced square-lattice domain and $H$ an admissible Hamiltonian (D1.2) on $\mathcal H_\Lambda$ with a unique normalized ground vector $\Omega$ (up to phase), ground energy $E_0$, and
$$H-E_0\,\mathrm{id}\ \ge\ \Delta\bigl(\mathrm{id}-|\Omega\rangle\langle\Omega|\bigr).$$
Then for every $A\subseteq\Lambda$
$$S_\Omega(A)\le C\,|\partial_\Lambda A|\qquad\text{(eq:area-law)}.$$
The same $C$ serves all such $\Lambda$, $A$, $H$.

**Used from.** D1.1, D1.2, D1.3, D1.6 ($Z=Z_A$), D1.11, D1.12 (Lemma 11.1), D1.16 (Prop 9.6), D1.17 (Prop 10.2), D1.18 (Prop 11.2); Lemma 2.2 (§2).
**Proof.** Not given in §1. It is the proof of Theorem 1.1 in §11 (`10-geometry.tex` L803–L857); the steps use results of later sections.
- D1.4.1 Trivial cases. $\Lambda=\varnothing$ or $A\in\{\varnothing,\Lambda\}$: $S_\Omega(A)=0$ (`10-geometry.tex` L804; purity, $S_\Omega(\Lambda)=0$). §2 (`01-preliminaries.tex` L118–L121): $q=1$ gives $\dim\mathcal H_\Lambda=1$, so all entropies vanish. $R=0$: $H$ is a sum of on-site operators, its ground eigenspace is the tensor product of on-site ground eigenspaces, uniqueness makes each one-dimensional, so $\Omega$ is a product vector and $S_\Omega(A)=0$. Afterwards assume $q\ge2$, $R\ge1$, $\Lambda\ne\varnothing$.
- D1.4.2 $b:=|\partial_\Lambda A|=0$: Lemma 2.2 (`01-preliminaries.tex` L123–L133) gives $S_\Omega(A)=0$. $A$ is a union of graph components; every support of finite $d_\Lambda$-diameter lies in one component; $H$ is the tensor sum of component Hamiltonians; its ground eigenspace is the tensor product of the component ground eigenspaces; one-dimensional $\Rightarrow$ each factor one-dimensional; $\Omega$ factors over the components, hence over the cut.
- D1.4.3 $b>0$: fix $D_0$, $C_{\rm tpl}$ (Def 9.3) and a threshold $n_*$ chosen as in D1.4.5. Prop 11.2 (`10-geometry.tex` L98–L141) with $Z=Z_A$ gives $C_1$ independent of $\Lambda$, $A$ and:
  - $D\subseteq A$, $|D|\le C_1b$, disjoint nonempty $X_i\subseteq A\cap T_i$, $A=D\,\dot\cup\,\dot\bigcup_iX_i$, labels $f_i\in\{0,1\}$, integers $n_i\ge n_*$;
  - $T_i$ a template with parameters $(n_i,s_i)$: $\operatorname{diam}_\infty T_i\le n_i$, $n_i\ge C_{\rm tpl}N_i(s_i+1)$, $\operatorname{dist}_\infty(T_i,Z)>4D_0s_i$, $L_i=\lfloor n_i^{1-\ell}\rfloor\le s_i$, $\ell=10^{-5}$;
  - (geometry:cut-clearance) $\operatorname{dist}_\infty(T_i,Z)>2n_i^\beta$; (geometry:ordered-clearance) $\operatorname{dist}_\infty\bigl(T_i,\bigcup_{j<i,f_j=f_i}X_j\bigr)>2n_i^\beta$; $\beta=1-2\cdot10^{-6}$;
  - $\sum_in_i^{-100}\le C_1b$.
- D1.4.4 Put $S_i=A\cap(T_i+[-L_i,L_i]^2_{\mathbb Z})$ and $J_i=(\Lambda\setminus A)\cup\bigcup_{j<i,f_j=f_i}X_j$. $T_i$ is separated from the cut and $L_i\le s_i$, so Prop 9.6 (`08-scanner.tex` L808–L944; $L=\lfloor n^{1-10^{-5}}\rfloor$, $X=A\cap T$, $S_0=A\cap T_L$) applies for $n_i\ge n_*$: $I_\Omega(A\cap T_i:\Lambda\setminus S_i)\le Cn_i^{1-\varepsilon}$, $\varepsilon=10^{-5}$; $|S_i|=O(n_i^2)$; the cuts of $A\cap T_i$, $S_i$, $S_i\setminus(A\cap T_i)$ have $O(n_i)$ edges. These are the hypotheses of Prop 10.2 with $C_0$ uniform.
- D1.4.5 Prop 10.2 (`09-amplification.tex` L261–L576) with $M=100$, $X=A\cap T_i$, $S_0=S_i$ gives a radius $r_i\le C_Mn_i^{(1-\varepsilon)/\alpha}$ with $L_i+2r_i=o(n_i^\beta)$ and $I_\Omega(A\cap T_i:J)\le Cn_i^{-100}$ for every $J\subseteq\Lambda\setminus N_{2r_i}^\Lambda(S_i)$. $n_*$ is taken large enough for Prop 9.6, Prop 10.2 at $M=100$ on the templates of Prop 11.2, and so that $L_i+2r_i<n_i^\beta$ for $n_i\ge n_*$. Claim $J_i\subseteq\Lambda\setminus N^\Lambda_{2r_i}(S_i)$, for the whole set $J_i$ at once:
  - a graph path of length $\le2r_i$ from $S_i$ stays within ambient distance $L_i+2r_i<n_i^\beta$ of $T_i$ (start within $L_i$ of $T_i$; each graph step moves ambient position by $\le1$);
  - $\operatorname{dist}_\infty(T_i,\bigcup_{j<i,f_j=f_i}X_j)>2n_i^\beta>n_i^\beta$ (ordered clearance) $\Rightarrow$ the path meets no earlier same-family $X_j$;
  - a path reaching $\Lambda\setminus A$ contains, at its first crossing of the cut, an endpoint of a cut edge, i.e. a point of $Z$, within ambient distance $<n_i^\beta$ of $T_i$; contradicts $\operatorname{dist}_\infty(T_i,Z)>2n_i^\beta$ (cut clearance). Alternatively: $2n_i^\beta>L_i+n_i^\beta$ is the cut-clearance hypothesis of Prop 10.2, which states $N_{2r_i}(S_i)\subseteq A$.
- D1.4.6 Monotonicity (§2: discarding systems cannot increase mutual information) with $X_i\subseteq A\cap T_i$: $I_\Omega(X_i:J_i)\le I_\Omega(A\cap T_i:J_i)\le Cn_i^{-100}$. All these estimates concern the same state $\Omega$, although the auxiliary construction behind each may differ.
- D1.4.7 Lemma 11.1 (D1.12) with $\psi=\Omega$, $\varepsilon_i=Cn_i^{-100}$: $S_\Omega(A)\le S_\Omega(D)+\tfrac12\sum_i\varepsilon_i\le|D|\log q+\tfrac C2\sum_in_i^{-100}\le C_1b\log q+\tfrac C2C_1b=:C'b$. $C'$ depends only on $q,R,J,\Delta$ (and fixed template constants, $n_*$): not on the size, shape, connectedness or holes of $\Lambda$, nor on $A$.

**Output.** Final result. Cor 1.2 (D1.7), the companion paper (D1.10).
**Standard?** Specific to this paper. Context: D1.8.
**Pitfall.**
- Quantifier order: $\forall(q,R,J,\Delta)\ \exists C\ \forall(\Lambda,H,A)$. $C$ is uniform in the domain, its shape, holes, connectedness, and $H$.
- Gap hypothesis is the operator inequality. Given $H\Omega=E_0\Omega$ it already forces uniqueness: for $\varphi\perp\Omega$ with $H\varphi=E_0\varphi$, $0=\langle\varphi,(H-E_0)\varphi\rangle\ge\Delta\|\varphi\|^2$ gives $\varphi=0$.
- The gap is a gap of the whole $H$ on $\Lambda$. No gap is assumed for restrictions of $H$ to subregions (D1.5).

---

#### D1.5 Step — Remarks after Theorem 1.1

Source: `00-introduction.tex` L55–L58.

**Statement.**
- The diameter bound in eq:hamiltonian is measured in $d_\Lambda$ of the induced graph. This matters for domains with holes or several components.
- The spectral hypothesis concerns the full $H$ on $\Lambda$; there is no gap assumption on Hamiltonians restricted to smaller regions.

**Used from.** D1.2, D1.4.
**Output.** Justifies using only induced-graph locality (§4 propagation, Lemma 4.1) and a gap of $H$ itself (Prop 4.3; Lemma 3.2).
**Standard?** Specific to this paper (contrast: local-gap hypotheses in D1.8).

---

#### D1.6 Def — Inner boundary and endpoint set

Source: `00-introduction.tex` L60–L67.

**Statement.** For $A\subseteq\Lambda$:
$$\partial_{\rm in}A=\{x\in A:\ \exists y\notin A,\ \{x,y\}\in\partial_\Lambda A\},\qquad Z_A=\bigcup_{e\in\partial_\Lambda A}e .$$
$Z_A$ is the set of endpoints of crossing edges: $Z_A=\partial_{\rm in}A\ \dot\cup\ \partial_{\rm out}A$ with $\partial_{\rm out}A\subseteq\Lambda\setminus A$ the outer endpoints (notation of this digest, not of the paper).

**Used from.** D1.3.
**Output.** $Z_A$ (written $Z$ in §3, §9, §11) is the reference set for all clearances: safe boxes (§3: $\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q)$, $D_0>2R+10$), templates separated from the cut (Def 9.3: $\operatorname{dist}_\infty(T,Z)>4D_0s_0$), Prop 11.2.
**Standard?** Standard vertex-boundary notions.

---

#### D1.7 Corollary 1.2 — Rectangles and vertex boundaries

Source: `00-introduction.tex` L69–L86.

**Statement.**
(a) The conclusion of Theorem 1.1 holds for every subset of a finite rectangular square lattice with bounded on-site and nearest-neighbor interactions and a unique ground state separated by a fixed global gap.
(b) For every domain covered by Theorem 1.1 and with $C$ its constant:
$$S_\Omega(A)\le4C|\partial_{\rm in}A|,\qquad S_\Omega(A)\le2C|Z_A|.$$

**Used from.** D1.4, D1.6.
**Proof.**
- D1.7.1 (a): $\Lambda=\{1,\dots,L_1\}\times\{1,\dots,L_2\}$ is an induced domain. Supports $\{x\}$ and $\{x,y\}$ with $|x-y|_1=1$ have $d_\Lambda$-diameter $\le1$. Merging terms on equal supports (norm $\le J$ after merging), $H$ is admissible with $R=1$, so Theorem 1.1 applies with $C=C(q,1,J,\Delta)$.
- D1.7.2 $|\partial_{\rm in}A|\le|\partial_\Lambda A|$: the map $e\mapsto$ (its endpoint in $A$) from $\partial_\Lambda A$ onto $\partial_{\rm in}A$ is surjective by definition of $\partial_{\rm in}A$.
- D1.7.3 $|\partial_\Lambda A|\le4|\partial_{\rm in}A|$: each $x\in\partial_{\rm in}A$ has between 1 and 4 crossing edges (degree $\le4$ in $\mathbb Z^2$). Then Thm 1.1 gives $S_\Omega(A)\le C|\partial_\Lambda A|\le4C|\partial_{\rm in}A|$.
- D1.7.4 $|Z_A|\le2|\partial_\Lambda A|$: $Z_A$ is the union of $|\partial_\Lambda A|$ two-element sets.
- D1.7.5 $|\partial_\Lambda A|\le2|Z_A|$: let $c(v)$ be the number of crossing edges at $v\in Z_A$; $1\le c(v)\le4$ and $\sum_{v\in Z_A}c(v)=2|\partial_\Lambda A|$ (each edge counted at both endpoints). So $2|\partial_\Lambda A|\le4|Z_A|$. Then $S_\Omega(A)\le C|\partial_\Lambda A|\le2C|Z_A|$.
- D1.7.6 Empty boundary: all of $\partial_\Lambda A$, $\partial_{\rm in}A$, $Z_A$ are empty simultaneously; the inequalities read $0\le0$.

**Output.** Vertex-boundary forms of the area law. Not used by §2–§11.
**Standard?** Elementary counting.
**Pitfall.** The paper writes $|\partial_{\rm in}A|\le|\partial_\Lambda A|\le4|\partial_{\rm in}A|$ and $|Z_A|\le2|\partial_\Lambda A|\le4|Z_A|$. Factor 2 in $S_\Omega(A)\le2C|Z_A|$ needs the double count over both endpoints (D1.7.5); $|\partial_\Lambda A|\le4|\partial_{\rm in}A|\le4|Z_A|$ would give factor 4.

---

#### D1.8 Step — History and related work

Source: `00-history.tex` L1–L117.

**Statement.**
- Area-law question: field-theory origin (Bombelli–Koul–Lee–Sorkin 1986; Srednicki 1993); lattice gap-to-area conjecture (Hastings 2007; Arad–Landau–Vazirani 2012).
- $d=1$ proved: Hastings 2007 (finite-range, bounded interactions, fixed local dimension, gap); ALV 2012 improve the dependence on the inverse gap for frustration-free chains via approximate ground-state projectors; AKLV 2013 extend to general chains; Brandão–Horodecki 2015 derive an area law for pure 1D states from exponential decay of correlations between arbitrary separated regions. Exponential clustering (Nachtergaele–Sims 2006) only gives decay of connected correlations of separated observables; Anshu–Harrow–Soleimanifar 2022 bound smooth entanglement spread, not entropy.
- $d\ge2$, strict area law only for special classes (Cramer–Eisert–Plenio–Dreißig 2006, harmonic lattices; Cho 2014 with extra compatibility), or with log corrections under extra hypotheses (Masanes 2009; Brandão–Cramer 2015).
- $d=2$ spins: Anshu–Arad–Gosset 2022 subvolume bounds, $O(b^{5/3}\log^{7/3}(2+b))$ for rectangles and $n^{1+O((\log n)^{-1/5})}$ across a vertical cut; both need frustration-free plaquette projectors, unique ground state and a local gap.
- Arad–Firanko–Jain 2026: approximate-projector methods for maximally mixed ground states, mutual-information bound, 2D application under frustration-freeness and local gap.
- This paper: frustration allowed, gap only for the full $H$, arbitrary regions of arbitrary finite induced domains.
- Tools cited in the text (no new statements): Lieb–Robinson (Nachtergaele–Ogata–Sims), Kitaev's centered spectral filter, Swingle–McGreevy positive constraints (taking absolute values retains the full-system gap), products of contractions as in detectability lemmas (Anshu–Arad–Vidick), dissipative Lieb–Robinson (Barthel–Kliesch), Van Acoleyen–Marien–Verstraete (logarithmic commutators), strong subadditivity, Alicki–Fannes–Winter continuity, Schur–Weyl duality (Keyl–Werner), finite quantum de Finetti, weighted operator geometric means, Carlen–Vershynina resolvent-compression identity.

**Used from.** D1.4.
**Output.** none (literature context).
**Standard?** Literature survey; external references listed in `paper/references.bib`.

---

#### D1.9 Def — PEPS and bond dimension

Source: `00-introduction.tex` L93–L98.

**Statement.** A PEPS on a lattice has one tensor per site with one physical index (dimension of the site's local space) and one virtual index per incident edge. Contracting paired virtual indices gives a vector in the many-body space. The dimension of an edge index is the bond dimension of the edge. The approximation problem asks how large these dimensions must be to approximate the ground vector on the original lattice.

**Used from.** D1.1.
**Output.** Terminology for D1.10 only.
**Standard?** Standard (Verstraete–Cirac PEPS).

---

#### D1.10 Step — Tensor-network consequence (companion paper)

Source: `00-introduction.tex` L100–L119. External result: `\cite[Theorem 1.1]{OpenAI2026PolynomialPEPS}`.

**Statement.** Companion Theorem 1.1, quoted: for the original open $L\times L$ square grid, $L\ge2$, with on-site and nearest-neighbor interactions, fixed local dimension $q\ge2$, term-norm bound $J>0$ and global gap $\Delta>0$, every unique ground vector has a PEPS approximation with maximum bond dimension $\le CL^c$ and global vector error $\le L^{-1}$ after normalization and phase choice. $C,c$ depend only on $q,J,\Delta$. Existence only; no efficient construction or contraction is claimed.

What this paper supplies to it (the companion also needs compression and routing arguments not in this paper):
- Positive operators annihilating $\Omega$ with rapidly decaying tails: Prop 4.3.
- Collar information bounds: Prop 9.6 and Prop 10.2.
- Two families of separated regions with specified shapes and clearances: Prop 11.2.

**Used from.** D1.4 (indirectly: Prop 4.3, 9.6, 10.2, 11.2), D1.9.
**Output.** none inside this paper.
**Standard?** Specific to the companion paper (OpenAI 2026, "Polynomial PEPS approximation of gapped square-grid ground states").
**Pitfall.** The PEPS bound is not a corollary of Theorem 1.1 alone. It uses the stronger by-products listed above.

---

#### D1.11 Def — Mutual information

Source: `00-introduction.tex` L123–L130.

**Statement.** For disjoint physical regions $B,C\subseteq\Lambda$:
$$I_\Omega(B:C)=S_\Omega(B)+S_\Omega(C)-S_\Omega(B\cup C).$$

**Used from.** D1.3.
**Output.** Analytic target of §3–§10: make $I_\Omega(B:C)$ small for $B\subseteq A$, $C$ beyond a collar of $B$, even when $C\supseteq\Lambda\setminus A$. Strong subadditivity (§2, `01-preliminaries.tex` L15–L21) gives $I\ge0$ and monotonicity: discarding systems cannot increase $I$, i.e. $I(B':C')\le I(B:C)$ for $B'\subseteq B$, $C'\subseteq C$.
**Standard?** Standard.

---

#### D1.12 Step — Reduction of $S_\Omega(A)$ to collar information

Source: `00-introduction.tex` L131–L138. Exact statement and proof: Lemma 11.1, `10-geometry.tex` L26–L66.

**Statement.** Let $\psi$ be pure on a finite system with site set $\Lambda$. Let $A=D\,\dot\cup\bigcup_{i\in\mathcal I_0}X_i\,\dot\cup\bigcup_{i\in\mathcal I_1}X_i$, with each $\mathcal I_f$ finite and ordered, $B=\Lambda\setminus A$. If
$$I_\psi\Bigl(X_i:\ B\cup\bigcup_{j\in\mathcal I_f,\,j<i}X_j\Bigr)\le\varepsilon_i\qquad(f\in\{0,1\},\ i\in\mathcal I_f),$$
then $S_\psi(A)\le S_\psi(D)+\tfrac12\sum_i\varepsilon_i$. With $|D|=O(b)$ this gives $S_\psi(A)\le|D|\log q+\tfrac12\sum_i\varepsilon_i$ (the intro's "sum of the information errors" is this, with factor $\tfrac12$).

**Used from.** D1.11; §2 entropy identities (`01-preliminaries.tex` L8–L24: chain rule, subadditivity, purity).
**Proof.** Write $A_f=\bigcup_{i\in\mathcal I_f}X_i$, $E_f=\sum_{i\in\mathcal I_f}\varepsilon_i$.
- D1.12.1 Chain rule within family $f$, adding $X_i$ in order: $S(BA_f)=S(B)+\sum_iS(X_i\mid BX_{<i})$, and $S(X_i\mid J)=S(X_i)-I(X_i:J)$. Hence $S(BA_f)\ge S(B)+\sum_{i\in\mathcal I_f}S(X_i)-E_f$, since $I(X_i:J)\le\varepsilon_i$ for $J=B\cup\bigcup_{j<i}X_j$.
- D1.12.2 Purity: $S(B)=S(A)$.
- D1.12.3 Purity again: the complement of $B\cup A_f$ is $D\cup A_{1-f}$, so $S(BA_f)=S(DA_{1-f})\le S(D)+\sum_{i\in\mathcal I_{1-f}}S(X_i)$ (subadditivity).
- D1.12.4 Add D1.12.1–D1.12.3 over $f=0,1$: $2S(A)+\sum_{\text{all }i}S(X_i)-E_0-E_1\le2S(D)+\sum_{\text{all }i}S(X_i)$. Every $S(X_i)$ cancels. So $S(A)\le S(D)+\tfrac12(E_0+E_1)$.
- D1.12.5 $S(D)\le|D|\log q$ (dimension bound).

**Output.** Separation requirement on the geometry: each $X_i$ must be far from $B$ and from earlier tiles of its own family only, not from the other family. Prop 11.2 produces such ordered families; Prop 10.2 supplies each $\varepsilon_i$. Used in D1.4.7.
**Standard?** Chain rule, subadditivity, purity (Schmidt decomposition) are standard (SSA, Lieb–Ruskai 1973, enters only through $I\ge0$ in D1.11). The two-family cancellation is specific to this paper.
**Pitfall.** The conditioning set contains all of $B=\Lambda\setminus A$ and all earlier same-family tiles at once. The analytic estimate must therefore bound $I(X_i:J_i)$ for the whole union $J_i$, not piece by piece.

---

#### D1.13 Step — Ambient versus graph locality

Source: `00-introduction.tex` L140–L144.

**Statement.**
- Analytic estimates concern $A\cap Q$ for ambient boxes $Q$ or finite unions of rectangles and triangles (templates, Def 9.3). Clearance is ambient, measured from $Z_A$. These sets may meet holes or the edge of the domain.
- Hamiltonian locality and propagation always use neighborhoods in the induced graph, $N_r^\Lambda$.

**Used from.** D1.1, D1.6.
**Output.** $\operatorname{dist}_\infty$ (ambient) in Prop 11.2 versus $N_{2r}^\Lambda$ in Prop 10.2; bridged by $d_\Lambda\ge|\cdot|_\infty$ (D1.4.5).
**Standard?** Specific to this paper.

---

#### D1.14 Step — Stage 1: a first exponent below volume

Source: `00-introduction.tex` L146–L155. Proved in §3 (`02-initial.tex`).

**Statement.** There is an exponent $e_0<1$ such that $S_\Omega(A\cap Q)\le Cr^{1+e_0}$ for every box $Q$ of side at most $r$ that is sufficiently far from $Z_A$. Exact form: Prop 3.3 (`02-initial.tex` L596–L668), $F_{\rm box}(r)\le Cr^{1+e_0}$ for $r\ge1$, $e_0\in(0,1)$, $C,e_0$ depending on $q,R,J,\Delta$ only. $F_{\rm box}(r)$ is the supremum of $S_\Omega(A\cap Q)$ over admissible $H$ with fixed $q,R,J,\Delta$, cuts $A$, and safe integer rectangles $Q$ of size $\le r$. Integer rectangle: product of two finite nonempty integer intervals; $\operatorname{size}(Q)$ = larger number of sites along an axis; safe: $\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q)$, $D_0>2R+10$ (`02-initial.tex` L225).

**Used from.** D1.2, D1.4 (hypotheses), D1.6 ($Z$), D1.11.
**Proof (route).**
- D1.14.1 The global gap bounds fluctuations of $-\log$ of positive marginal eigenvalues (Lemma 3.1).
- D1.14.2 Products of positive operators on nested rectangles are optimized; the norm of the optimized product is bounded in two ways, one from an energy estimate plus the global gap (Lemma 3.2). The two bounds give a conditional-entropy discount for a buffered rectangle.
- D1.14.3 Split a safe parent of size $\le Mr$ into $\le M^2$ safe children $Q_i$ of size $\le r$ (chunks of $r$ sites per axis), $X_i=A\cap Q_i$. A child is interior if its $C_{\rm pad}r$ padding lies in the parent; at most $B_M=4(C_{\rm pad}+2)M$ children are noninterior. An interior child's padded rectangle meets $\le(2C_{\rm pad}+5)^2-1$ other children. Order the children by a uniform random permutation. An interior child comes after all of them with probability $\ge p_0=(2C_{\rm pad}+5)^{-2}$; then its preceding sites contain the buffer of Lemma 3.2 and its chain-rule term is $\le S(X_i)/2+C_{\rm buf}r$. Otherwise, and for noninterior children, the term is $\le S(X_i)$. Expected chain rule gives $F_{\rm box}(Mr)\le[(1-p_0/2)M^2+(p_0/2)B_M]F_{\rm box}(r)+CM^2r$ (eq:initial-box-recursion).
- D1.14.4 For $M\ge\max(2,16(C_{\rm pad}+2))$: $B_M\le M^2/2$, so $(p_0/2)B_M\le(p_0/4)M^2$ and the coefficient is $\le\lambda=(1-p_0/4)M^2\in(M,M^2)$. Iterate along $r=M^j$: $F_{\rm box}(M^{j+1})\le\lambda F_{\rm box}(M^j)+CM^{j+2}$, inhomogeneous terms form a geometric series of ratio $M/\lambda<1$, so $F_{\rm box}(M^j)\le C\lambda^j$. Then $1+e_0=\log_M\lambda\in(1,2)$, monotonicity covers general $r$ (Prop 3.3). Trivial bound: $F_{\rm box}(r)\le r^2\log q$.

**Output.** Starting exponent for the bootstrap in Prop 9.5.
**Standard?** Specific to this paper.

---

#### D1.15 Step — Stage 2: information and energy in one interpolation

Source: `00-introduction.tex` L157–L172. Proved in §4–§7.

**Statement (what each section delivers).**
- §4 (Prop 4.3, `03-quasilocal.tex` L220–L329). Assume $H\Omega=E_0\Omega$, $\|\Omega\|=1$, $H-E_0\ge\Delta(I-P_\Omega)$. For each integer $p\ge1$, $\alpha=p/(p+1)$, there are $k_i$ indexed by the original supports (keeping their anchors $a_i$) and $c_*>0$ with $0\le k_i\le I$, $k_i\Omega=0$, $H_F=\sum_ik_i\ge c_*^{-1}(H-E_0)\ge g(I-P_\Omega)$, $g=\Delta/c_*$; $k_{i,l}=E_{i,l}(k_i)\in[0,I]$, $\|k_i-k_{i,l}\|\le Ce^{-cl^\alpha}$ for $l\in\mathbb Z_{\ge0}$; $k_i$ is supported in the component of $a_i$. $c_*,g$ depend on $p$ but not on the system size. Prop 4.5 (L405–L455): with $p=1$ ($\alpha=1/2$), for $n\ge2$ and nonempty $S_0$, $|S_0|\le C_0n^2$, replace $k_i$ by $k_{i,r_i}$, $r_i=\max\{r_0,\lfloor d_\Lambda(a_i,S_0)/2\rfloor\}$, $r_0=\lceil C_1(\log n)^2\rceil$ (if $d_\Lambda(a_i,S_0)=\infty$ keep $k_i$).
- §5–§7: attach positive operators to partitions of the full system; interpolate between partitions while a small subsystem changes parts. They act on symmetric tensor powers (vectors fixed by every permutation of the copies). Applying an inverse power of the interpolating operator to a vector built from ground-state copies and an auxiliary entangled pair defines the filtered vector. As the copy number grows, logarithmic norms per copy compare to combinations of marginal entropies.
- Output of §7 (Prop 7.4): decrease of a logarithmic squared norm is bounded below by averaged conditional mutual information, up to a small error; the same transported states bound the energy cost. Information gained is thereby compared with excitation energy spent.

**Used from.** D1.2, D1.4, D1.11.
**Output.** Entropy-gain and energy bounds for §8–§9.
**Standard?** Ingredients standard (Schur–Weyl, de Finetti, weighted operator geometric means: D1.8); the use in one interpolation is specific to this paper.

---

#### D1.16 Step — Stage 3: compare norms and scan a collar

Source: `00-introduction.tex` L174–L195. Proved in §8 and §9.

**Statement.**
- §8 (Prop 8.1): two bounds on $-\log$ of the filtered vector's norm. Upper: auxiliary dimensions chosen from a high-probability part of the target's Schmidt spectrum; project target and auxiliary system onto an entangled pair. Lower: uses the global gap; low physical energy forces most copies into the ground state.
- §9: partitions move through a collar by a finite randomized schedule (Prop 9.2). A moving boundary rarely splits any given interaction; the schedule gives an interpolation of low energy. The two norm bounds first improve the box exponent repeatedly (Prop 9.5: $F_{\rm box}(r)\le Cr^{1+e_*}$, $e_*=2\cdot10^{-6}$). Their sharper form then gives, for the collar (Prop 9.6):
$$I_\Omega\bigl(A\cap T:\Lambda\setminus(A\cap T_L)\bigr)\le Cn^{1-\varepsilon},\qquad\varepsilon=10^{-5}.$$
- $T$: finite union of controlled rectangles and triangles (Def 9.3), separated from the cut; $L=\lfloor n^{1-\varepsilon}\rfloor\le s_0$; $T_L$ is the ambient sup-norm enlargement by $L$. Cuts of $A\cap T$, $A\cap T_L$, $(A\cap T_L)\setminus(A\cap T)$ have $O(n)$ edges, $|A\cap T_L|=O(n^2)$.
- The finite physical and auxiliary system and the schedule are fixed before the copy number tends to infinity.

**Used from.** D1.6, D1.11, D1.14, D1.15.
**Output.** Prop 9.6 (collar information $\le Cn^{1-\varepsilon}$ with size and boundary bounds) is the input of §10.
**Standard?** Specific to this paper.
**Pitfall.** Order of limits: the schedule and finite system are fixed first, then the copy number $k\to\infty$ (the bound has an $o_k(1)$ remainder). The intro's "$\varepsilon>0$ fixed" is $\varepsilon=10^{-5}$.

---

#### D1.17 Step — Stage 4: amplify the information bound

Source: `00-introduction.tex` L197–L206. Proved in §10.

**Statement.**
- Typical spectral subspaces give a candidate operator restoring a target moved to an auxiliary reference. Its norm is controlled by the collar information.
- A localized product of contractions from the positive constraints suppresses the excited component. Polar decomposition gives a unitary near the target comparing the states. The unitary leaves the reference and the remote physical system untouched, so comparison with a state where they are independent bounds the original mutual information.
- Exact form (Prop 10.2, `09-amplification.tex` L261–L576). Fix $C_0>0$, $\varepsilon=10^{-5}$, $\beta=1-2\cdot10^{-6}$, $\alpha=p/(p+1)>1-10^{-6}$. Let $n\ge2$, $L=\lfloor n^{1-\varepsilon}\rfloor$, $X=A\cap T$, $S_0=A\cap T_L$, $Y=S_0\setminus X$. Assume $|S_0|\le C_0n^2$, the cuts of $X$, $Y$, $S_0$ have $\le C_0n$ edges each, and $I_\Omega(X:\Lambda\setminus S_0)\le C_0n^{1-\varepsilon}$. Then for every integer $M\ge1$ and all large $n$ there is an integer $r\le C_Mn^{(1-\varepsilon)/\alpha}$, $L+2r=o(n^\beta)$, such that $I_\Omega(X:J)\le C_Mn^{-M}$ simultaneously for every $J\subseteq\Lambda\setminus N_{2r}(S_0)$; same for any subset of $X$. Constants and threshold depend on $C_0,M$ only, not on $\Lambda,A,T$.
- Addendum: if $\operatorname{dist}_\infty(T,Z)>L+n^\beta$, then $N_{2r}(S_0)\subseteq A$, so $J$ may contain all of $\Lambda\setminus A$. (Proof: a path of length $\le2r$ from $S_0$ reaching $\Lambda\setminus A$ contains a point of $Z$ within ambient distance $L+2r$ of $T$.)

**Used from.** D1.15 (Prop 4.3), D1.16 (Prop 9.6).
**Output.** Collar information smaller than any inverse power of $n$ at the price of a sublinear extra radius. Used with $M=100$ in D1.4.5.
**Standard?** Specific to this paper (related: products of projections in detectability lemmas, Anshu–Arad–Vidick 2016; dissipative Lieb–Robinson, Barthel–Kliesch 2012).

---

#### D1.18 Step — Stage 5: arrange regions for entropy cancellation

Source: `00-introduction.tex` L208–L215. Proved in §11.

**Statement.** Prop 11.2 builds two ordered families $\{X_i\}$ with $A\setminus D=\dot\bigcup X_i$, $|D|\le Cb$. The collar around each tile avoids $\Lambda\setminus A$ and all earlier tiles of its own family. Narrow strips and recursive repairs at point contacts achieve this for arbitrary cuts while leaving $O(b)$ uncovered sites. Information errors are summable, $\sum_in_i^{-100}\le Cb$, so two applications of D1.12 prove eq:area-law.

**Used from.** D1.12, D1.16 (templates), D1.17.
**Output.** Theorem 1.1 (D1.4.3–D1.4.7).
**Standard?** Specific to this paper.

---

## Parameters and constants

Constants fixed in or used by §1 and their fixing points in the proof chain. All "C" depend only on $q,R,J,\Delta$ unless noted; none depends on $\Lambda$, $A$, $H$.

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

**Consumed by §1:** nothing. §1 statements use only conventions defined in D1.1–D1.3, D1.6, D1.11.

**Exported by §1:**
- Conventions (D1.1–D1.3, D1.6, D1.11): $d_\Lambda$, admissible $H$, $\partial_\Lambda$, $\partial_{\rm in}$, $Z_A$, $I_\Omega$, natural logs, constant dependence.
- Theorem 1.1 (D1.4): target; proved by the last proof of the paper.

**Dependency list of the proof of Theorem 1.1 (from D1.14–D1.18 and §11):**
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

Items 4–10 are read off `\ref` cross-references in the tex files and the stage descriptions D1.14–D1.17.

**Sections consumed by the proof of Thm 1.1:** §2, §3, §4, §5, §6, §7, §8, §9, §10, §11.
