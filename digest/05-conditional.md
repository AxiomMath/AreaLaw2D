# Digest of §5 — Two conditional operator estimates

Source: `paper/sections/04-conditional.tex` (lines 1–621). Label `sec:conditional`. Numbering: Lemma 5.1 (`lem:movement`), Lemma 5.2 (`lem:conditional-phases`), Lemma 5.3 (`lem:skew`); one shared theorem counter, no other numbered environments.

## Section in one paragraph

Fix an arbitrary finite-dimensional pure state $\theta$ on $P,x,U,F$. §5 proves two operator estimates whose constants depend only on $d=\dim x$ (resp. the support dimension of a local operator), never on $\dim P,U,F$. Order: (i) a relative log-moment bound for the pair $(\rho_{xU},\,I_x\otimes\widehat\rho_U)$, giving a conditional Schatten estimate (D5.2–D5.4); (ii) Lemma 5.1: a word of four fractional powers applied to $\theta$ has norm $\le\exp(-\tfrac a2\eta+Ca^{5/4}\ell^2)$, $\eta=I(x:F|U)$, proved by complex interpolation between a left boundary controlled by (i) and a right boundary controlled by (i) plus entropy continuity (D5.5–D5.11); (iii) Lemma 5.2: the product of marginal imaginary powers $\widehat\rho_U^{-iu}\widehat\rho_{xU}^{iu}$ moves $\theta$ by at most $C|\sinh\pi u|\mathcal R_\eta$ when $F$ is appended, proved by a resolvent-compression identity whose integral is $\eta$ (D5.12–D5.14); (iv) Lemma 5.3: for $0\le h\le I$ supported on $P_0x$, the scalar $f(z)=\langle\theta,\rho_P^{[z]}\rho_Y^{[-z]}h\rho_P^{[-z]}\rho_Y^{[z]}\theta\rangle$ satisfies $|f(a/2)|-\Re f(a/2)\le Ca^2\ell_h^4\eta^{1/8}$, by three-lines on $f$ plus (iii) (D5.15–D5.20). §6 lifts (ii) to symmetric tensor powers as the entropy gained when a subsystem $x$ changes side; §6–§7 use (iv) as the energy spent for a local term.

---

### 5.0 Notation and a relative log-moment bound

#### D5.1 Def — Spectral powers, hat, norms
*Source: 04-conditional.tex 14–29.*

**Statement.** For a density matrix $\rho$ with spectral projections $\Pi_p$:
$$\rho^{[z]}=\sum_{p>0}p^z\,\Pi_p\quad(z\in\mathbb C),\qquad \widehat\rho=\rho+\Pi_{\ker\rho}.$$
- $\rho^{[z]}=0$ on $\ker\rho$ for every $z$, including $z=0$: $\rho^{[0]}=\Pi_{\supp\rho}$.
- $\widehat\rho>0$; $\widehat\rho^{\,iu}$ is unitary, equal to $1$ on $\ker\rho$. Likewise $\widehat\rho^{-a}=1$ on $\ker\rho$.
- Brackets are omitted for positive real powers ($\rho^a=\rho^{[a]}$, $a>0$).
- On a purification of $\rho$, $\rho^{[s]}$ and $\widehat\rho^{\,s}$ ($s\in i\mathbb R$) give the same vector when applied innermost (the vector lies in $\supp\rho$).
- Operators are tensored with $I$ on unmentioned factors.
- $\|T\|_p=(\operatorname{Tr}|T|^p)^{1/p}$, $1\le p<\infty$; $\|T\|_\infty=\|T\|$; $\|\cdot\|_2$ = Hilbert–Schmidt. Faithful = positive definite.

**Used from.** none.

**Output.** Hat vs bracket convention in D5.2–D5.20. Facts used repeatedly:
- (F1) For $T$ on $D$ and $\theta$ pure on $D\otimes D'$ with marginal $\rho_D$: $\|T\theta\|=\|T\sqrt{\rho_D}\|_2$.
- (F2) Schmidt mirroring: $\rho_D^{[s]}\theta=\rho_{D'}^{[s]}\theta$ for all $s\in\mathbb C$ (same non-zero spectrum, matched eigenvectors).

**Standard?** Notation. (F1), (F2) standard (Schmidt decomposition); stated by the paper only as "Schmidt mirroring" at line 540.

**Pitfall.** $\rho^{[0]}\ne I$ but $\widehat\rho^{\,0}=I$. In Lemma 5.3 the function $f$ uses brackets (entire in $z$); Lemmas 5.1, 5.2 use hats (unitary phases).

#### D5.2 Step eq:conditional-log-moments — Three moments of $L$
*Source: 04-conditional.tex 31–67; display `eq:conditional-log-moments` (51–55).*

**Statement.** Let $\rho$ be a density matrix on $xU$, $d=\dim x$, $Q=I_x\otimes\widehat\rho_U$ ($Q>0$). Choose eigenbases $\{|i\rangle\}$ of $\rho$ (eigenvalues $p_i$) and $\{|j\rangle\}$ of $Q$ (eigenvalues $q_j>0$), the $Q$-basis adapted to $x\otimes\supp\rho_U\ \oplus\ x\otimes\ker\rho_U$. On pairs $(i,j)$ with $p_i>0$ put probability $p_i|\langle i,j\rangle|^2$ (total mass $\sum_ip_i=1$). Define the real random variable
$$L=\log p_i-\log q_j.$$
Then
$$\mathbb E\,L=-S(x|U)_\rho,\qquad \mathbb E\,e^{L}\le d,\qquad \mathbb E\,e^{-L}\le d .$$
Constants do not involve $\dim U$. Companion operator inequality: $\rho\le d\,(I_x\otimes\rho_U)\le dQ$.

**Used from.** D5.1; D2.1 (definition of $S(x|U)$).

**Proof.**
- D5.2.1 *Domination $\rho\le d(I_x\otimes\rho_U)$.* Write $v=\sum_{b=1}^d|b\rangle v_b$, $\rho_{bb'}=\langle b|\rho|b'\rangle$ (operators on $U$). Positivity of $\rho$ (Cauchy–Schwarz for the form $\langle\cdot,\rho\,\cdot\rangle$) gives $|\langle v_b,\rho_{bb'}v_{b'}\rangle|\le\langle v_b,\rho_{bb}v_b\rangle^{1/2}\langle v_{b'},\rho_{b'b'}v_{b'}\rangle^{1/2}$. Sum over $b,b'$, then Cauchy–Schwarz in $b$:
$$\langle v,\rho v\rangle\le\Big(\sum_b\langle v_b,\rho_{bb}v_b\rangle^{1/2}\Big)^2\le d\sum_b\langle v_b,\rho_{bb}v_b\rangle\le d\sum_b\langle v_b,\rho_Uv_b\rangle,$$
the last since $\rho_{bb}\le\sum_{b'}\rho_{b'b'}=\rho_U$. So $\rho\le d(I_x\otimes\rho_U)\le dQ$ ($\widehat\rho_U\ge\rho_U$).
- D5.2.2 *Support.* $\operatorname{Tr}[(I_x\otimes\Pi_{\ker\rho_U})\rho]=\operatorname{Tr}[\Pi_{\ker\rho_U}\rho_U]=0\Rightarrow\supp\rho\subseteq x\otimes\supp\rho_U$. So $\langle i,j\rangle=0$ whenever $p_i>0$ and $|j\rangle\in x\otimes\ker\rho_U$. Only $j$ with $q_j$ an eigenvalue of $\rho_U|_{\supp}$ carry weight.
- D5.2.3 *Mean.* $\mathbb E\log p_i=\sum_ip_i\log p_i=-S(xU)$. $\mathbb E\log q_j=\sum_j\langle j,\rho j\rangle\log q_j=\operatorname{Tr}\rho\,(I_x\otimes\log\widehat\rho_U)=\operatorname{Tr}\rho_U\log\rho_U=-S(U)$. Hence $\mathbb EL=-S(xU)+S(U)=-S(x|U)$.
- D5.2.4 *$\mathbb E\,e^L$.* $\mathbb Ee^L=\sum p_i^2|\langle i,j\rangle|^2/q_j=\operatorname{Tr}\rho^2Q^{-1}$. From $\rho\le dQ$: $Q^{-1/2}\rho Q^{-1/2}\le dI$, i.e. $\|Q^{-1/2}\rho^{1/2}\|^2\le d$, i.e. $\rho^{1/2}Q^{-1}\rho^{1/2}\le dI$. Then $\operatorname{Tr}\rho^2Q^{-1}=\operatorname{Tr}\rho^{1/2}(\rho^{1/2}Q^{-1}\rho^{1/2})\rho^{1/2}\le d\operatorname{Tr}\rho=d$.
- D5.2.5 *$\mathbb E\,e^{-L}$.* $\mathbb Ee^{-L}=\sum_{p_i>0,j}q_j|\langle i,j\rangle|^2=\operatorname{Tr}(\Pi_{\supp\rho}Q)$. By D5.2.2 $\Pi_{\supp\rho}\le\Pi_{x\otimes\supp\rho_U}$, and $Q\ge0$, so $\operatorname{Tr}(\Pi_{\supp\rho}Q)\le\operatorname{Tr}(\Pi_{x\otimes\supp\rho_U}Q)=d\operatorname{Tr}\rho_U=d$.

**Output.** D5.3 (tails); D5.4 (the identity $\operatorname{Tr}\rho^rQ^{-2ar}=\mathbb Ee^{(r-1)L}$); D5.7 ($\mathbb Ee^{aL}=\operatorname{Tr}\rho^{1+a}Q^{-a}$ and $\mathbb E L=-d_U$ for Jensen); D5.9 ($\mathbb E L^2\le C\ell^2$ via D5.3); D5.14 (the operator inequality D5.2.1 applied to $\rho_{xUF}$ with $UF$ in the role of $U$: $\rho_f\le d(I_x\otimes\rho_{UF})=d^2\sigma_f$).

**Standard?** The two-eigenbasis variable is that of Nussbaum–Szkoła, Ann. Statist. 37 (2009), §3 eq. (11), after restricting $Q$ to $x\otimes\supp\rho_U$ and normalising by $d$ (their log ratio is $L+\log d$). The paper proves the dimension bounds directly. $\rho_{xU}\le d\,(I_x\otimes\rho_U)$ is standard.

#### D5.3 Step eq:conditional-log-mgf — Log-moment generating function
*Source: 04-conditional.tex 69–82; display `eq:conditional-log-mgf` (78–81).*

**Statement.** Put $\ell=\log(ed)$ ($\ell\ge1$). There are universal $c,C>0$ with
$$\Pr(|L|>v)\le2de^{-v},\qquad \mathbb E\big[L^2e^{|bL|}\big]\le C\ell^2\ \ (|b|\ell\le c),$$
$$\log\mathbb Ee^{bL}\le-bS(x|U)_\rho+Cb^2\ell^2,\qquad|b|\ell\le c .$$
Constants independent of $\dim U$.

**Used from.** D5.2.

**Proof.**
- D5.3.1 Markov on D5.2: $\Pr(L>v)=\Pr(e^L>e^v)\le de^{-v}$ and $\Pr(L<-v)=\Pr(e^{-L}>e^v)\le de^{-v}$.
- D5.3.2 *Second moment with exponential weight* (expansion; paper: "splitting at $2\ell$ and integrating this tail"). Take $c\le1/2$, so $|b|\le1/2$. Let $g(s)=s^2e^{|b|s}$, increasing. On $|L|\le2\ell$: $g\le4\ell^2e^{2|b|\ell}\le4e\ell^2$. On $|L|>2\ell$: layer-cake
$$\mathbb E[g(|L|)1_{|L|>2\ell}]=g(2\ell)\Pr(|L|>2\ell)+\int_{2\ell}^\infty g'(s)\Pr(|L|>s)\,ds,$$
with $g(2\ell)\Pr(|L|>2\ell)\le4e\ell^2\cdot2de^{-2\ell}\le C\ell^2$ ($de^{-2\ell}=e^{-2}/d$) and $g'(s)\le(2s+s^2)e^{s/2}$, so the integral is $\le2d\int_{2\ell}^\infty(2s+s^2)e^{-s/2}ds\le C\,d\,\ell^2e^{-\ell}=C\ell^2/e$.
- D5.3.3 *Taylor.* $e^{bL}\le1+bL+\tfrac{b^2}2L^2e^{|bL|}$ (Lagrange remainder). Take $\mathbb E$, use $\mathbb EL=-S(x|U)$: $\mathbb Ee^{bL}\le1-bS(x|U)+\tfrac C2b^2\ell^2$. Apply $\log(1+y)\le y$.

**Output.** D5.4 with $b=r-1$; D5.9.2 ($b=0$: $\mathbb EL^2\le C\ell^2$).

**Standard?** Standard sub-exponential-tail computation; specific here is the $\dim U$-free tail from D5.2.

**Pitfall.** The hypothesis is $|b|\ell\le c$, not $|b|\le c$: the exponent is only controlled up to $1/\ell$.

#### D5.4 Step eq:conditional-schatten — Conditional Schatten estimate
*Source: 04-conditional.tex 84–114; display `eq:conditional-schatten` (91–94).*

**Statement.** For $0<a<1/4$ put $K=Q^{-a}\rho Q^{-a}$, $r=(1-2a)^{-1}\in(1,2)$, $Z=(\operatorname{Tr}K^r)^{1/r}=\|K\|_r$. After reducing the universal $c$:
$$\log Z\le-2aS(x|U)_\rho+Ca^2\ell^2,\qquad a\ell\le c .$$
Identities: $r-1=2ar$; the dual exponent of $r$ satisfies $2a\,r'=1$ ($r'=r/(r-1)$).

**Used from.** D5.2, D5.3.

**Proof.**
- D5.4.1 $K=T^*T$ with $T=\rho^{1/2}Q^{-a}$, so $Z=\|T\|_{2r}^2$.
- D5.4.2 *Analytic family* $T(z)=\rho^{[z/2]}Q^{-az}$, $0\le\Re z\le r$. At $\Re z=0$: $T(iu)=\rho^{[iu/2]}Q^{-iau}$, product of a partial isometry and a unitary, $\|T(iu)\|\le1$. At $\Re z=r$: $\|T(r+iu)\|_2^2\le\|\rho^{r/2}Q^{-ar}\|_2^2=\operatorname{Tr}\rho^rQ^{-2ar}=\mathbb Ee^{(r-1)L}$ (eigenbasis sum $\sum p_i^r q_j^{-(r-1)}|\langle i,j\rangle|^2$, and $2ar=r-1$).
- D5.4.3 *Interpolation* between $p_0=\infty$ and $p_1=2$ at $\theta=1/r$ (the point $z=1$ in $[0,r]$): $1/p_\theta=\tfrac1r\cdot\tfrac12=\tfrac1{2r}$. So $\|T(1)\|_{2r}\le1^{1-1/r}\big(\mathbb Ee^{(r-1)L}\big)^{(1/2)(1/r)}$, hence
$$Z=\|\rho^{1/2}Q^{-a}\|_{2r}^2\le\big(\mathbb Ee^{(r-1)L}\big)^{1/r}.$$
- D5.4.4 *Scalar form of D5.4.3.* Let $B=V|B|$ (polar), $\|B\|_{(2r)'}=1$, $(2r)'=2r/(2r-1)$. Consider the scalar function $z\mapsto\operatorname{Tr}\big(T(z)\,|B|^{(2r)'(1-z/(2r))}V^*\big)$. Test matrix $W(z)=|B|^{(2r)'(1-z/(2r))}V^*$: at $\Re z=0$, $\|W\|_1=\operatorname{Tr}|B|^{(2r)'}=1$; at $\Re z=r$, $\|W\|_2^2=\operatorname{Tr}|B|^{(2r)'}=1$; at $z=1$ the exponent is $(2r)'(1-\tfrac1{2r})=1$, $W(1)=|B|V^*=B^*$. Hölder bounds the scalar by $\|T\|_\infty\|W\|_1\le1$ on the first line and by $\|T\|_2\|W\|_2$ on the second; Hadamard three-lines at $z=1$ gives $|\operatorname{Tr}T(1)B^*|\le(\mathbb Ee^{(r-1)L})^{1/(2r)}$; duality $\|T(1)\|_{2r}=\sup_B|\operatorname{Tr}T(1)B^*|$. Singular test matrices: approximate.
- D5.4.5 *Insert D5.3* with $b=r-1=2ar\le4a$ (as $r<2$); need $|b|\ell\le c_3$, ensured by $a\ell\le c_3/4$:
$$\log Z\le\tfrac1r\big[-(r-1)S(x|U)+C(r-1)^2\ell^2\big]=-2aS(x|U)+4Ca^2r\ell^2\le-2aS(x|U)+8Ca^2\ell^2.$$

**Output.** Left boundary of Lemma 5.1 (D5.6); right boundary (D5.10) with $(x,U)\to(x,P)$; $\xi=K^r/\operatorname{Tr}K^r$ (D5.6); $\xi^{1-2a}=K/Z$.

**Standard?** Standard method (Stein complex interpolation of an analytic family between $L^\infty$ and $L^2$; Hadamard three-lines), applied here to the conditioned pair. The constant bookkeeping is specific to this paper.

**Pitfall.** $a<1/4$ is needed for $r<2$ (so $b\le4a$) and later for $2a\le1/2$ in D5.7. $a\ell\le c$ with $\ell\ge1$ already forces $a\le c$.

---

### 5.1 Moving a subsystem

#### D5.5 Lemma 5.1 — Conditional movement estimate
*Source: 04-conditional.tex 118–308; display `eq:conditional-movement` (129–133).*

**Statement.** Let $\theta$ be a unit pure vector on finite-dimensional $P,x,U,F$; $\rho_D$ its marginals. Set $d=\dim x$, $\ell=\log(ed)$,
$$\eta=S(x|P)_\theta+S(x|U)_\theta=I(x:F|U)_\theta=I(x:F|P)_\theta .$$
There are universal $c,C>0$ such that for $0<a\ell\le c$ and all density matrices $\sigma$ on $xP$, $\tau$ on $xU$:
$$\Big\|\sigma^{a/2}\,\widehat\rho_P^{-a/2}\,\tau^{a/2}\,\widehat\rho_U^{-a/2}\,\theta\Big\|\le\exp\Big(-\frac a2\eta+Ca^{5/4}\ell^2\Big).$$
The same bound holds for positive subnormalised $\sigma,\tau$.

**Used from.** D2.2 (items 1, 5: SSA, purity), D2.4 (Lemma 2.1), D2.5 (pure-state trace distance), D5.1, D5.2, D5.4, and D5.6–D5.11 (listed in the roadmap).

**Proof (roadmap; "→D" means the claim is proved in that anchor, listed in order of use in the paper's proof).**
- D5.5.1 *Identities.* Purity and SSA give $\eta\ge0$ and the three expressions (expansion in D5.5.A below).
- D5.5.2 *Reduction.* Take $\sigma,\tau$ faithful (removed in D5.5.9). Write $d_U=S(x|U)_\theta$, $d_P=S(x|P)_\theta$. These are entropies, not dimensions.
- D5.5.3 *Analytic function.* For $0\le\Re z\le1$,
$$G(z)=\sigma^{az}\widehat\rho_P^{-az}\,\tau^{a(1-z)}\widehat\rho_U^{-a(1-z)}\theta .$$
$G(1/2)$ is the vector of the statement. All imaginary powers are unitary, so $G$ is bounded on the closed strip (bound may depend on the fixed faithful factors).
- D5.5.4 *Left boundary.* $\|G(iu)\|=M(u)=\|\tau_u^aQ^{-a}\theta\|$, $\tau_u=Q^{-iau}\tau Q^{iau}$, $M(u)^2\le Z$, $\log\|G(iu)\|=-ad_U+C_0a^2\ell^2-\lambda(u)$, $\lambda\ge0$ →D5.6.
- D5.5.5 *Hellinger closeness* of $\rho$ and $\xi=K^r/\operatorname{Tr}K^r$: $\|\sqrt\rho-\sqrt\xi\|_2\le C\sqrt a\,\ell$ →D5.7.
- D5.5.6 *Phase vs Hellinger* (general inequality) →D5.8.
- D5.5.7 *State movement* $\theta_u=\tau^{-iau}Q^{iau}\theta$: $\|\theta_u-\theta\|\le C(1+|u|)(\sqrt{\lambda(u)}+\sqrt a\,\ell)$ →D5.9.
- D5.5.8 *Right boundary* $\log\|G(1+iu)\|\le-ad_P+Ca^2\ell^2+Ca\ell(1+|u|)^{1/2}(\lambda(u)^{1/4}+a^{1/4}\ell^{1/2})$ →D5.10.
- D5.5.9 *Interpolation.* Evaluate at the midpoint with harmonic measure →D5.11:
$$\log\|G(\tfrac12)\|\le\int_{\mathbb R}\big[\log\|G(iu)\|+\log\|G(1+iu)\|\big]\frac{du}{2\cosh\pi u}.$$
- D5.5.10 *Sum.* Insert D5.5.4 and D5.5.8 at the same $u$. Entropy terms: $\tfrac12(-ad_U-ad_P)=-\tfrac a2\eta$. The $\lambda$-terms: for $\lambda\ge0$, $B>0$, Young gives $-\lambda+B\lambda^{1/4}\le CB^{4/3}$ (maximum at $\lambda^{3/4}=B/4$); with $B=Ca\ell(1+|u|)^{1/2}$ this is $\le C\,a^{4/3}\ell^{4/3}(1+|u|)^{2/3}$. Since $\int(1+|u|)^{s}\frac{du}{2\cosh\pi u}<\infty$ for every fixed $s$, after integration:
 - Young term $\le Ca^{4/3}\ell^{4/3}\le Ca^{5/4}\ell^2$ ($a<1$, $\ell\ge1$);
 - quadratic terms $a^2\ell^2\le a^{5/4}\ell^2$;
 - leftover $Ca\ell(1+|u|)^{1/2}a^{1/4}\ell^{1/2}\to Ca^{5/4}\ell^{3/2}\le Ca^{5/4}\ell^2$.
 Total: $\log\|G(\tfrac12)\|\le-\tfrac a2\eta+Ca^{5/4}\ell^2$.
- D5.5.11 *Remove faithfulness.* Replace $\sigma,\tau$ by $(1-\epsilon)\sigma+\epsilon I/\dim$, $\epsilon\to0$; positive powers (exponent $a/2>0$) are continuous. Subnormalised: $\sigma=s\sigma'$, $s\le1$, gives $\sigma^{a/2}=s^{a/2}\sigma'^{a/2}$, which only decreases the norm; the zero case is trivial.

*D5.5.A (identities, expansion).* $\theta$ pure on $PxUF$: $S(xUF)=S(P)$, $S(UF)=S(xP)$, $S(U)=S(xPF)$, $S(xU)=S(PF)$. Then
$$I(x:F|U)=S(xU)+S(UF)-S(U)-S(xUF)=S(PF)+S(xP)-S(U)-S(P)=S(x|P)+S(x|U),$$
$$I(x:F|P)=S(xP)+S(PF)-S(P)-S(xPF)=S(xP)+S(PF)-S(P)-S(U),$$
equal to the previous line. SSA (D2.2 item 1) gives $I\ge0$.

**Output.** §6 lifts the one-copy word to $\mathcal S_k=\operatorname{Sym}^k\mathcal V$ (`05-replicas.tex` 488, 580: "exactly the word in Lemma 5.1"; log norm $\le-a\eta_\theta/2+Ca^{5/4}\log^C(e\dim x)$). The hypothesis $a\log(e\dim x)\le c$ with this $c$ is imported there.

**Standard?** Specific to this paper. Tools standard: Stein–Hirschman log-interpolation on a strip, Hölder, Alicki–Fannes–Winter continuity (D2.4).

**Pitfall.** (1) $d_U,d_P$ denote conditional entropies. (2) The constant $C_0$ in D5.6 is chosen after the Schatten constant of D5.4 fixes the left-boundary slack; $c$ must be small enough for D5.3 ($|b|\ell\le c_3$), D5.4 ($a<1/4$, $a\ell\le c_3/4$) and D5.7 ($2a\le1/2$). (3) $\widehat\rho_P$ is the $P$-marginal of $\theta$; it equals the $P$-marginal of $\theta_u$ (D5.9), which is what allows D5.4 on the right boundary. (4) Only $\dim x$ enters constants; $\dim P,U,F$ never do.

#### D5.6 Step eq:conditional-slack, eq:conditional-overlap — Left boundary and slack
*Source: 04-conditional.tex 151–174; displays `eq:conditional-slack` (167–170), `eq:conditional-overlap` (172–174).*

**Statement.** With $\rho=\rho_{xU}$, $Q=I_x\otimes\widehat\rho_U$, $\tau_u=Q^{-iau}\tau Q^{iau}$, for all real $u$:
$$\|G(iu)\|=M(u):=\|\tau_u^aQ^{-a}\theta\|,\qquad M(u)^2=\operatorname{Tr}\tau_u^{2a}K\le Z,\qquad\log Z\le-2ad_U+Ca^2\ell^2 .$$
Fix universal $C_0\ge\tfrac12C$. Define
$$\lambda(u)=-ad_U+C_0a^2\ell^2-\log M(u)\ge0,\qquad\xi=K^r/\operatorname{Tr}K^r .$$
Then $\operatorname{Tr}\tau_u^{2a}\xi^{1-2a}=M(u)^2/Z\ge e^{-2\lambda(u)}$, and $\log\|G(iu)\|=-ad_U+C_0a^2\ell^2-\lambda(u)$ exactly.

**Used from.** D5.4, D5.2.

**Proof.**
- D5.6.1 $G(iu)=\sigma^{iau}\widehat\rho_P^{-iau}\ \tau^{a}\tau^{-iau}\ Q^{-a}Q^{iau}\ \theta$. Drop the two leftmost unitaries. $Q^{iau}$ commutes with $Q^{-a}$; $\tau^{a-iau}Q^{iau}=Q^{iau}\,\tau_u^{a}\tau_u^{-iau}$. Drop $Q^{iau}$ and $\tau_u^{-iau}$ (the latter commutes with $\tau_u^a$): $\|G(iu)\|=\|\tau_u^aQ^{-a}\theta\|=M(u)$.
- D5.6.2 $M(u)^2=\langle\theta,Q^{-a}\tau_u^{2a}Q^{-a}\theta\rangle=\operatorname{Tr}_{xU}\tau_u^{2a}Q^{-a}\rho Q^{-a}=\operatorname{Tr}\tau_u^{2a}K$ (the $xU$-marginal of $\theta$ is $\rho$). Hölder with exponents $r',r$: $\le\|\tau_u^{2a}\|_{r'}\|K\|_r=(\operatorname{Tr}\tau_u^{2ar'})^{1/r'}Z=Z$, since $2ar'=1$ and $\operatorname{Tr}\tau_u=1$.
- D5.6.3 $\lambda\ge0$: $\log M=\tfrac12\log M^2\le\tfrac12\log Z\le-ad_U+C_0a^2\ell^2$.
- D5.6.4 $\xi^{1-2a}=\xi^{1/r}=K/Z$, so $\operatorname{Tr}\tau_u^{2a}\xi^{1-2a}=\operatorname{Tr}\tau_u^{2a}K/Z=M^2/Z$. Insert $M^2=e^{2(-ad_U+C_0a^2\ell^2-\lambda)}$ and $Z\le e^{-2ad_U+2C_0a^2\ell^2}$: ratio $\ge e^{-2\lambda}$.

**Output.** $\lambda(u)$ enters D5.9 and D5.10; $\xi$ enters D5.7, D5.9. Left boundary value enters D5.5.9.

**Standard?** Specific to this paper (the slack device). Hölder standard.

**Pitfall.** "We retain the slack": large $\lambda$ already improves the left boundary; small $\lambda$ forces $\tau_u^{2a}$ to overlap $\xi^{1-2a}$ (hence $\theta_u\approx\theta$, D5.9). The sum $-\lambda+(\dots)\lambda^{1/4}$ in D5.5.10 is where the two uses balance.

#### D5.7 Step eq:conditional-hellinger — $\rho$ and $\xi$ are Hellinger-close
*Source: 04-conditional.tex 176–199; display `eq:conditional-hellinger` (197–199).*

**Statement.** $H:=\|\sqrt\rho-\sqrt\xi\|_2\le C\sqrt a\,\ell$ (for $0<a\ell\le c$).

**Used from.** D5.2 (Jensen step), D5.4, D5.6.2.

**Proof.**
- D5.7.1 *Lower bound on the self-overlap.* $\|\rho^aQ^{-a}\theta\|\ge\langle\theta,\rho^aQ^{-a}\theta\rangle=\operatorname{Tr}\rho^{1+a}Q^{-a}=\mathbb Ee^{aL}\ge e^{a\mathbb EL}=e^{-ad_U}$ (Cauchy–Schwarz with $\|\theta\|=1$; trace is real and positive since it equals $\mathbb Ee^{aL}$; Jensen; D5.2). Squaring and using D5.6.2 with $\tau_u\to\rho$: $\operatorname{Tr}\rho^{2a}K=\|\rho^aQ^{-a}\theta\|^2\ge e^{-2ad_U}$.
- D5.7.2 Divide by $Z\le e^{-2ad_U+C_Za^2\ell^2}$ (D5.4): $\operatorname{Tr}\rho^{2a}\xi^{1-2a}=\operatorname{Tr}\rho^{2a}K/Z\ge e^{-C_Za^2\ell^2}\ge1-C_Za^2\ell^2$.
- D5.7.3 *Concavity.* $\phi(b)=1-\operatorname{Tr}\rho^{[b]}\xi^{[1-b]}$ on $[0,1]$. In eigenbases, $\operatorname{Tr}\rho^{[b]}\xi^{[1-b]}=\sum_{p,s>0}p^bs^{1-b}|\langle p,s\rangle|^2$; each $b\mapsto p^bs^{1-b}$ is convex, so $\phi$ is concave. $\phi\ge0$: Hölder, $\operatorname{Tr}\rho^{[b]}\xi^{[1-b]}\le\|\rho^{[b]}\|_{1/b}\|\xi^{[1-b]}\|_{1/(1-b)}=(\operatorname{Tr}\rho)^b(\operatorname{Tr}\xi)^{1-b}=1$ (endpoints: $\operatorname{Tr}\Pi_{\supp\rho}\xi\le1$).
- D5.7.4 For $2a\le\tfrac12$: concavity on $0\le2a\le\tfrac12$ gives $\phi(2a)\ge(1-4a)\phi(0)+4a\phi(\tfrac12)\ge4a\phi(\tfrac12)$. So $1-\operatorname{Tr}\sqrt\rho\sqrt\xi=\phi(\tfrac12)\le\phi(2a)/(4a)\le C_Za\ell^2/4$.
- D5.7.5 $H^2=\operatorname{Tr}\rho+\operatorname{Tr}\xi-2\operatorname{Tr}\sqrt\rho\sqrt\xi=2\phi(\tfrac12)\le\tfrac12C_Za\ell^2$.

**Output.** D5.9 (cost $2H$ and $C(1+|u|)H$).

**Standard?** Specific. The Hellinger-affinity inequality $1-\operatorname{Tr}\sqrt\rho\sqrt\xi\le\frac{1-\operatorname{Tr}\rho^{b}\xi^{1-b}}{2b}$ ($b\le\tfrac12$) is the standard concavity argument for Rényi-type affinities.

**Pitfall.** The gain from the divide-by-$4a$ in D5.7.4 turns a $a^2\ell^2$ deficit into $a\ell^2$, i.e. $H\sim\sqrt a\,\ell$, not $a\ell$. This $\sqrt a$ feeds the $a^{1/4}\ell^{1/2}$ term of D5.10 (after the square root from Lemma 2.1), hence the $a^{5/4}\ell^{3/2}$ leftover in D5.5.10.

#### D5.8 Step eq:conditional-phase-hellinger — Phases are Hellinger-continuous
*Source: 04-conditional.tex 219–231; display `eq:conditional-phase-hellinger` (221–224).*

**Statement.** For density matrices $A,B$ (same dimension) and real $b$,
$$\big\|(\widehat A^{ib}-\widehat B^{ib})\sqrt B\big\|_2\le C(1+|b|)\,\|\sqrt A-\sqrt B\|_2,$$
$C$ universal.

**Used from.** D5.1.

**Proof.** Expand in eigenbases $|\alpha\rangle$ of $A$, $|\beta\rangle$ of $B$ ($\widehat\alpha=1$ if $\alpha=0$):
$$\text{LHS}^2=\sum_{\alpha,\beta}|\langle\alpha,\beta\rangle|^2\,\beta\,|\widehat\alpha^{ib}-\widehat\beta^{ib}|^2,\qquad\|\sqrt A-\sqrt B\|_2^2=\sum_{\alpha,\beta}|\langle\alpha,\beta\rangle|^2(\sqrt\alpha-\sqrt\beta)^2 .$$
It suffices to bound each term: $\beta|\widehat\alpha^{ib}-\widehat\beta^{ib}|^2\le C(1+|b|)^2(\sqrt\alpha-\sqrt\beta)^2$.
- D5.8.1 $\beta=0$: LHS term is $0$.
- D5.8.2 $\alpha,\beta>0$, $v=\alpha/\beta$: need $|1-v^{ib}|\le C(1+|b|)|1-\sqrt v|$. If $\tfrac14\le v\le4$: $|1-v^{ib}|\le|b||\log v|$ and $|\log v|=2|\log\sqrt v|\le4|\sqrt v-1|$ (mean value, $\tfrac{d}{ds}\log s\le2$ on $[\tfrac12,2]$). If $v\notin[\tfrac14,4]$: $|1-v^{ib}|\le2\le4|1-\sqrt v|$ (since $|1-\sqrt v|>\tfrac12$ there).
- D5.8.3 $\alpha=0<\beta$: $|1-\beta^{ib}|\le2$, $|\sqrt0-\sqrt\beta|=\sqrt\beta$, so $\beta|\cdot|^2\le4\beta=4(\sqrt\alpha-\sqrt\beta)^2$.

**Output.** D5.9 (with $b=-au$, applied to $(A,B)=(\xi,\rho)$).

**Standard?** Elementary; specific as stated (the version with $\sqrt B$ on the right and kernel phases extended by one).

**Pitfall.** $\sqrt B$, not $\sqrt A$, sits on the right: zero eigenvalues of $B$ contribute nothing, zero eigenvalues of $A$ contribute the bound $2$. The convention $\widehat\alpha=1$ at $\alpha=0$ is exactly D5.1.

#### D5.9 Step eq:conditional-state-movement — The state arriving at the right boundary
*Source: 04-conditional.tex 201–258; display `eq:conditional-state-movement` (209–212).*

**Statement.** Define $\theta_u=\tau^{-iau}Q^{iau}\theta=Q^{iau}\tau_u^{-iau}\theta$ (unit vector, same $P$-marginal as $\theta$ since the acting unitary lives on $xU$). Then for $0<a\ell\le c$, all $u\in\mathbb R$:
$$\|\theta_u-\theta\|\le C(1+|u|)\big(\sqrt{\lambda(u)}+\sqrt a\,\ell\big).$$

**Used from.** D5.2 ($\mathbb EL^2\le C\ell^2$ via D5.3), D5.6, D5.7, D5.8.

**Proof.** ("All kernel phases extended by one", i.e. hats.)
- D5.9.1 *Reduction.* $\|\theta_u-\theta\|=\|\tau_u^{-iau}\theta-Q^{-iau}\theta\|\le\|(\widehat\rho^{-iau}-Q^{-iau})\theta\|+\|(\tau_u^{-iau}-\widehat\rho^{-iau})\theta\|$, $\widehat\rho=\widehat\rho_{xU}$.
- D5.9.2 *First term.* By (F1) and eigenbases $\{i\},\{j\}$ of $\rho,Q$: $\|(Q^{-iau}-\widehat\rho^{-iau})\theta\|^2=\sum p_i|\langle i,j\rangle|^2|q_j^{-iau}-p_i^{-iau}|^2\le a^2u^2\,\mathbb EL^2\le Ca^2u^2\ell^2$ ($|e^{ix}-e^{iy}|\le|x-y|$; $\mathbb EL^2\le C\ell^2$ from D5.3 at $b=0$).
- D5.9.3 *Second term, insert $\xi$.* By (F1) it equals $\|(\tau_u^{-iau}-\widehat\rho^{-iau})\sqrt\rho\|_2$. Split $\tau_u^{-iau}-\widehat\rho^{-iau}=(\tau_u^{-iau}-\widehat\xi^{-iau})+(\widehat\xi^{-iau}-\widehat\rho^{-iau})$:
 - (a) $\|(\widehat\xi^{-iau}-\widehat\rho^{-iau})\sqrt\rho\|_2\le C(1+a|u|)H$ by D5.8 with $(A,B)=(\xi,\rho)$;
 - (b) $\|(\tau_u^{-iau}-\widehat\xi^{-iau})\sqrt\rho\|_2\le\|(\tau_u^{-iau}-\widehat\xi^{-iau})\sqrt\xi\|_2+2H$ (the operator has norm $\le2$).
- D5.9.4 *The $\xi,\tau_u$ phase difference.* Eigenvalues $p$ of $\xi$, $q$ of $\tau_u$ (faithful, so $q>0$), probability $p|\langle p,q\rangle|^2$, $v=\log(q/p)$, only $p>0$. Then
$$\|(\tau_u^{-iau}-\widehat\xi^{-iau})\sqrt\xi\|_2^2=\mathbb E|1-e^{-iauv}|^2,$$
$$\mathbb Ee^v=\operatorname{Tr}\Pi_{\supp\xi}\tau_u\le1,\qquad\mathbb Ee^{2av}=\operatorname{Tr}\xi^{1-2a}\tau_u^{2a}\ge e^{-2\lambda(u)}\ \ (\text{D5.6}).$$
- D5.9.5 *On $\{v\le0\}$.* Claim $|1-e^{-iauv}|^2\le C(1+u^2)(1-e^{2av})$. Put $w=-v\ge0$: $|1-e^{i\phi}|^2\le\min(4,\phi^2)$ with $\phi=auw$. If $2aw\le1$: $1-e^{-2aw}\ge(1-e^{-1})2aw$ and $a^2u^2w^2\le\tfrac12u^2\,aw$. If $2aw>1$: $1-e^{-2aw}\ge1-e^{-1}$ and use $4$. Next
$$\mathbb E[(1-e^{2av})1_{v\le0}]=\Pr(v\le0)-\mathbb E[e^{2av}1_{v\le0}]\le1-e^{-2\lambda}+\mathbb E[(e^{2av}-1)1_{v>0}]\le2\lambda+2a,$$
using $\Pr(v\le0)=1-\Pr(v>0)$, $\mathbb E[e^{2av}1_{v\le0}]=\mathbb Ee^{2av}-\mathbb E[e^{2av}1_{v>0}]\ge e^{-2\lambda}-\mathbb E[e^{2av}1_{v>0}]$, $1-e^{-2\lambda}\le2\lambda$, and for $v>0$: $e^{2av}-1\le2a(e^v-1)\le2ae^v$ (concavity of $x\mapsto x^{2a}$ at $x=1$), $\mathbb Ee^v\le1$.
- D5.9.6 *On $\{v>0\}$.* $|1-e^{-iauv}|^2\le a^2u^2v^2\le a^2u^2e^v$ ($v^2\le e^v$), so contributes $\le a^2u^2\mathbb Ee^v\le a^2u^2$.
- D5.9.7 *Sum.* D5.9.5–6: $\mathbb E|1-e^{-iauv}|^2\le C(1+u^2)(\lambda+a)$ ($a^2u^2\le au^2$). So the $\xi,\tau_u$ term is $\le C(1+|u|)(\sqrt\lambda+\sqrt a)$. Add D5.9.2, D5.9.3 (a),(b), and $H\le C\sqrt a\,\ell$ (D5.7); use $a\le\sqrt a\le\sqrt a\,\ell$ ($a<1$, $\ell\ge1$).

**Output.** D5.10 (entropy continuity along $u$).

**Standard?** Specific to this paper.

**Pitfall.** $\theta_u$ is defined with $\tau$ (not $\tau_u$) in the first form; the two forms agree because $\tau_u^{-iau}=Q^{-iau}\tau^{-iau}Q^{iau}$. The bound degrades like $(1+|u|)$; the harmonic-measure density $1/(2\cosh\pi u)$ absorbs any polynomial in $u$ (D5.5.10).

#### D5.10 Step — Right boundary
*Source: 04-conditional.tex 260–279.*

**Statement.** For $0<a\ell\le c$ and all real $u$:
$$\log\|G(1+iu)\|\le-ad_P+Ca^2\ell^2+Ca\ell(1+|u|)^{1/2}\big(\lambda(u)^{1/4}+a^{1/4}\ell^{1/2}\big).$$
(Left boundary, for comparison: exactly $-ad_U+C_0a^2\ell^2-\lambda(u)$, D5.6.)

**Used from.** D5.4 (with $U\to P$), D5.9, D2.4 (Lemma 2.1 with $D=x$, $E=P$), D2.5.

**Proof.**
- D5.10.1 *Reduce to a conjugated $\sigma$.* $G(1+iu)=\sigma^{a+iau}\widehat\rho_P^{-a-iau}\tau^{-iau}\widehat\rho_U^{iau}\theta=\sigma^{a+iau}\widehat\rho_P^{-a-iau}\theta_u$. Put $\sigma'=\widehat\rho_P^{\,iau}\sigma\,\widehat\rho_P^{-iau}$ (density on $xP$). Then $\sigma^{a+iau}\widehat\rho_P^{-iau}=\widehat\rho_P^{-iau}\sigma'^{a+iau}$; drop the unitaries $\widehat\rho_P^{-iau}$, $\sigma'^{iau}$: $\|G(1+iu)\|=\|\sigma'^a\widehat\rho_P^{-a}\theta_u\|$.
- D5.10.2 *Schatten.* The $P$-marginal of $\theta_u$ equals that of $\theta$, so $\widehat\rho_P$ is the correct marginal operator for the state $\theta_u$. D5.4 and Hölder on $xP$ (as in D5.6.2) give $\log\|G(1+iu)\|\le-aS(x|P)_{\theta_u}+Ca^2\ell^2$.
- D5.10.3 *Continuity.* Lemma 2.1 with $D=x$, $E=P$: $|S(x|P)_{\theta_u}-S(x|P)_\theta|\le C\sqrt\delta\,\ell$, $\delta=\tfrac12\|\rho_{xP}[\theta_u]-\rho_{xP}[\theta]\|_1\le\|\theta_u-\theta\|$ (D2.5). By D5.9 and $\sqrt{s+t}\le\sqrt s+\sqrt t$:
$$\sqrt{\|\theta_u-\theta\|}\le C(1+|u|)^{1/2}\big(\lambda^{1/4}+a^{1/4}\ell^{1/2}\big).$$
So $-aS(x|P)_{\theta_u}\le-ad_P+Ca\ell(1+|u|)^{1/2}(\lambda^{1/4}+a^{1/4}\ell^{1/2})$.

**Output.** D5.5.10.

**Standard?** Specific. Uses continuity only through $\dim x$ (controlled system $x$ is the first argument).

**Pitfall.** The entropy that Lemma 2.1 must control is $S(x|P)$, not $S(P|x)$: the cost would otherwise carry $\log\dim P$ (D2.4 Pitfall).

#### D5.11 Step — Log-interpolation with harmonic measure
*Source: 04-conditional.tex 281–293.*

**Statement.** Let $G$ be vector-valued, analytic in $0<\Re z<1$, bounded and continuous on the closed strip, with $\log\|G\|$ integrable on both boundary lines. Then
$$\log\|G(\tfrac12)\|\le\int_{\mathbb R}\log\|G(iu)\|\frac{du}{2\cosh\pi u}+\int_{\mathbb R}\log\|G(1+iu)\|\frac{du}{2\cosh\pi u},$$
each line carrying total mass $\int\frac{du}{2\cosh\pi u}=\tfrac12$.

**Used from.** none (D5.5.3 supplies the hypotheses).

**Proof.**
- D5.11.1 $z\mapsto e^{\pi iz}$ maps the strip onto the upper half-plane ($|e^{\pi iz}|=e^{-\pi\Im z}$, $\arg=\pi\Re z$), $z=\tfrac12\mapsto i$, $\Re z=0\mapsto(0,\infty)$, $\Re z=1\mapsto(-\infty,0)$. Harmonic measure at $i$ is $\frac{dx}{\pi(1+x^2)}$; with $x=\pm e^{-\pi u}$, $|dx|=\pi e^{-\pi u}du$: density $\frac{du}{e^{\pi u}+e^{-\pi u}}=\frac{du}{2\cosh\pi u}$.
- D5.11.2 Scalar case: sub-mean value property for $\log|\varphi|$, $\varphi$ analytic, first on bounded subdomains then by exhaustion.
- D5.11.3 Vector case: if $G(\tfrac12)\ne0$ put $\varphi(z)=\langle e,G(z)\rangle$ with $e=G(\tfrac12)/\|G(\tfrac12)\|$. Then $\log\|G(\tfrac12)\|=\log|\varphi(\tfrac12)|\le\int\log|\varphi|\,d\mu\le\int\log\|G\|\,d\mu$.
- D5.11.4 Legitimacy: for faithful $\sigma,\tau$ all boundary norms are bounded above and away from zero (unitaries and invertible factors), so the integrals are finite and the limit in D5.11.2 is justified.

**Output.** D5.5.9.

**Standard?** Standard (Hirschman / Stein interpolation with the Poisson kernel of the strip). Here at the midpoint, weights $\tfrac12,\tfrac12$ — equivalent to three-lines in log form but with the explicit $u$-dependence kept.

**Pitfall.** Plain three-lines would only give $\sup_u$ of the two boundary bounds; pairing them at the same $u$ is what lets $-\lambda(u)$ pay for the $\lambda(u)^{1/4}$ term.

---

### 5.2 Comparing marginal phases

#### D5.12 Lemma 5.2 — Marginal-phase comparison
*Source: 04-conditional.tex 310–479; lemma 321–339; display `eq:conditional-modular-bound` (331–336).*

**Statement.** Let $\theta$ be a unit pure vector on finite-dimensional $P,x,U,F$; $\rho_D$ its marginals; $d=\dim x$, $\eta=I(x:F|U)_\theta$. For $\eta>0$ set
$$y=\min(1,\eta),\qquad\mathcal R_\eta=\sqrt y+\sqrt{\eta\log(ed/y)},\qquad\mathcal R_0=0 .$$
There is a universal $C$ such that for every $u\in\mathbb R$
$$\Big\|\big(\widehat\rho_U^{-iu}\widehat\rho_{xU}^{\,iu}-\widehat\rho_{UF}^{-iu}\widehat\rho_{xUF}^{\,iu}\big)\theta\Big\|\le C|\sinh(\pi u)|\,\mathcal R_\eta .$$
In particular the two phase products agree on $\theta$ if $\eta=0$. Constants independent of $\dim P,U,F$.

**Used from.** D5.1 (F1), D5.2.1 (domination), D2.1, D5.13, D5.14.

**Proof.** Idea: $\eta$ is the integral of a non-negative resolvent defect; two $d$-only moment bounds control the ends, entropy controls the middle.
- D5.12.1 *Faithful case set-up* ($\rho_f=\rho_{xUF}>0$, hence all marginals $>0$). $\sigma_f=\tfrac{I_x}d\otimes\rho_{UF}$, $\rho_s=\rho_{xU}$, $\sigma_s=\tfrac{I_x}d\otimes\rho_U$. On the Hilbert–Schmidt spaces $\mathcal H_f$ (operators on $xUF$) and $\mathcal H_s$ (on $xU$): $A=L_{\sigma_f}R_{\rho_f^{-1}}$, $B=L_{\sigma_s}R_{\rho_s^{-1}}$ ($L,R$ left/right multiplication; commuting positive definite). $V(X\sqrt{\rho_s})=(X\otimes I_F)\sqrt{\rho_f}$.
- D5.12.2 *$V$ is an isometry:* $\|V(X\sqrt{\rho_s})\|_2^2=\operatorname{Tr}(X^*X\otimes I)\rho_f=\operatorname{Tr}X^*X\rho_s$.
- D5.12.3 *$V^*AV=B$:* $\langle V(X\sqrt{\rho_s}),AV(Y\sqrt{\rho_s})\rangle=\operatorname{Tr}\big[\sqrt{\rho_f}(X^*\otimes I)\sigma_f(Y\otimes I)\sqrt{\rho_f}\rho_f^{-1}\big]=\operatorname{Tr}(X^*\otimes I)\sigma_f(Y\otimes I)=\operatorname{Tr}X^*\sigma_sY$, and $\langle X\sqrt{\rho_s},BY\sqrt{\rho_s}\rangle=\operatorname{Tr}X^*\sigma_sY$ too ($\operatorname{Tr}_F\sigma_f=\sigma_s$).
- D5.12.4 $b_0=\sqrt{\rho_s}$, $a_0=Vb_0=\sqrt{\rho_f}$. For $v>0$: $\delta_v=(A+v)^{-1}a_0-V(B+v)^{-1}b_0$, $h(v)$ as in D5.13.
- D5.12.5 *Resolvent identity and entropy:* $h(v)\ge0$, $\int_0^\infty h=\eta$ →D5.13. *Tails:* $0\le h(v)\le\min(d^2,v^{-2})$, $\|\delta_v\|_2\le\sqrt{h(v)/v}$ →D5.14.
- D5.12.6 *Fractional powers by the resolvent integral.* For $-1<\Re z<0$ and $x>0$: $\int_0^\infty\frac{v^z}{x+v}dv=-\frac{\pi}{\sin\pi z}x^z$ (the integral $\int_0^\infty\frac{v^{s-1}}{x+v}dv=\frac\pi{\sin\pi s}x^{s-1}$, $s=z+1$). Spectral calculus gives
$$A^za_0-VB^zb_0=-\frac{\sin\pi z}\pi\int_0^\infty v^z\delta_v\,dv .$$
- D5.12.7 *Boundary value $z=-iu$.* For $-\tfrac14\le\Re z<0$: $\|v^z\delta_v\|_2\le v^{\Re z}\sqrt{h/v}$, majorised by $d\,v^{-3/4}$ on $(0,1]$ (use $h\le d^2$) and $v^{-3/2}$ on $[1,\infty)$ (use $h\le v^{-2}$). Dominated convergence lets $\Re z\uparrow0$; $|\sin(-i\pi u)|=|\sinh\pi u|$:
$$\|A^{-iu}a_0-VB^{-iu}b_0\|_2\le C|\sinh\pi u|\int_0^\infty\sqrt{h(v)/v}\,dv .$$
- D5.12.8 *Split $\eta>0$* at $y/d^2\le1/y$ ($y\le1\le d$):
 - $\int_0^{y/d^2}\sqrt{h/v}\le\int_0^{y/d^2}d\,v^{-1/2}dv=2\sqrt y$;
 - $\int_{1/y}^\infty\sqrt{h/v}\le\int_{1/y}^\infty v^{-3/2}dv=2\sqrt y$;
 - middle, Cauchy–Schwarz: $\le(\int h)^{1/2}\big(\int_{y/d^2}^{1/y}\frac{dv}v\big)^{1/2}\le\sqrt{\eta\cdot2\log(d/y)}\le C\sqrt{\eta\log(ed/y)}$.
 Total $\le C\mathcal R_\eta$.
- D5.12.9 *$\eta=0$.* $h\ge0$ continuous, $\int h=0\Rightarrow h\equiv0\Rightarrow\|(A+v)^{1/2}\delta_v\|=0\Rightarrow\delta_v=0\Rightarrow$ the discrepancy vanishes.
- D5.12.10 *Identify the vectors.* $A^{-iu}a_0=\sigma_f^{-iu}\rho_f^{iu}\sqrt{\rho_f}$, $VB^{-iu}b_0=(\sigma_s^{-iu}\rho_s^{iu}\otimes I_F)\sqrt{\rho_f}$. $\sigma_f^{-iu}=d^{iu}\rho_{UF}^{-iu}$, $\sigma_s^{-iu}=d^{iu}\rho_U^{-iu}$: cancel the common phase $d^{iu}$ (norm one), flip the sign of the difference. Hilbert–Schmidt norm becomes $\|(\rho_U^{-iu}\rho_{xU}^{iu}-\rho_{UF}^{-iu}\rho_{xUF}^{iu})\sqrt{\rho_f}\|_2$. By (F1) ($\theta$ purifies $\rho_f$ with $P$): $\|T\theta\|=\|T\sqrt{\rho_f}\|_2$ for $T$ on $xUF$. Faithful case done.
- D5.12.11 *Singular $\rho_f$.* Replace by $\rho_{f,\epsilon}=(1-\epsilon)\rho_f+\epsilon I/\dim(xUF)$ and use its reductions in D5.12.1–10 (the proof lives on Hilbert–Schmidt spaces, so no purifier of $\rho_{f,\epsilon}$ on $P$ is needed). Then:
 - $\eta_\epsilon\to\eta$ (finite dimension); $\mathcal R_{\eta_\epsilon}\to\mathcal R_\eta$ (continuity of $\mathcal R$ on $(0,\infty)$, and $\mathcal R_\eta\to0$ as $\eta\to0$).
 - Convergence of phase products on $\sqrt{\rho_{f,\epsilon}}$ in Hilbert–Schmidt norm, in the order of application: the innermost $\widehat\rho_{xU,\epsilon}^{\,iu}$ acts on $\sqrt{\rho_{f,\epsilon}}$; the limit lies in $\supp\rho_{xU}\otimes F$ since $\supp\rho_f\subseteq\supp\rho_{xU}\otimes F$ and the square-root mass outside tends to $0$; on that space the inner phase converges (the mollified marginal commutes with its limit); its output lies in $x\otimes\supp\rho_U\otimes F$, so the outer $\widehat\rho_{U,\epsilon}^{-iu}$ converges there. Same for the pair $(xUF,UF)$.
 - All phases have norm one, which controls the vanishing complementary pieces. The limit is the product of support phases = the unitary extensions in the statement. No operator-norm convergence of phases on a limiting kernel is used.

**Output.** D5.17 ($Y=xU$, same lemma). §6/§7 only via Lemma 5.3.

**Standard?** Quantitative form is specific to this paper. Qualitative statement (equality of phase products iff relative entropy is preserved on the subalgebra): Petz 1986, Thm 4(iii),(iv), as cited by the paper. Resolvent compression identity: Carlen–Vershynina 2019, Lemma 2.1.

**Pitfall.** (1) $\mathcal R_\eta$ uses $d=\dim x$ only; in Lemma 5.3 it is inherited unchanged although the support dimension there is $d_h\ge d$. (2) $\log(ed/y)$ with $y=\min(1,\eta)$: for $\eta\ge1$, $y=1$ and $\mathcal R_\eta=1+\sqrt{\eta\log(ed)}$. (3) The faithful proof needs $\rho_f>0$ and all marginals $>0$; the limit argument is where hats (not brackets) are essential.

#### D5.13 Step eq:conditional-resolvent-square, eq:conditional-resolvent-entropy — Resolvent defect and its integral
*Source: 04-conditional.tex 366–390; displays `eq:conditional-resolvent-square` (374–379), `eq:conditional-resolvent-entropy` (381–385).*

**Statement.** In the set-up of D5.12 (faithful $\rho_f$):
$$\|(A+v)^{1/2}\delta_v\|_2^2=\langle a_0,(A+v)^{-1}a_0\rangle-\langle b_0,(B+v)^{-1}b_0\rangle=:h(v)\ge0,$$
$$\int_0^\infty h(v)\,dv=D(\rho_f\|\sigma_f)-D(\rho_s\|\sigma_s)=\eta,\qquad D(\rho\|\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma).$$

**Used from.** D5.12.1–4, D2.1.

**Proof.**
- D5.13.1 *Compression identity.* $g=(A+v)^{-1}a_0$, $k=(B+v)^{-1}b_0$, $\delta_v=g-Vk$:
$$\langle\delta_v,(A+v)\delta_v\rangle=\langle g,(A+v)g\rangle-2\Re\langle(A+v)g,Vk\rangle+\langle k,V^*(A+v)Vk\rangle .$$
$(A+v)g=a_0$; $V^*a_0=b_0$ ($V^*V=I$); $V^*(A+v)V=B+v$ (D5.12.3). So the three terms are $\langle a_0,(A+v)^{-1}a_0\rangle$, $-2\langle b_0,k\rangle$, $+\langle b_0,k\rangle$, giving $h(v)$. $h\ge0$ as the left side is a squared norm.
- D5.13.2 *Log formula.* $\log x=\int_0^\infty\big(\tfrac1{1+v}-\tfrac1{x+v}\big)dv$, $x>0$. So $-\langle a_0,\log A\,a_0\rangle=\int_0^\infty\big(\langle a_0,(A+v)^{-1}a_0\rangle-\tfrac{\|a_0\|^2}{1+v}\big)dv$, same for $B$. $\|a_0\|^2=\operatorname{Tr}\rho_f=1=\|b_0\|^2$: the $\tfrac1{1+v}$ terms cancel in the difference, and $\int_0^\infty h=-\langle a_0,\log A\,a_0\rangle+\langle b_0,\log B\,b_0\rangle$ (each integral converges separately).
- D5.13.3 *Relative entropy.* $L,R$ commute, so $\log(L_\sigma R_{\rho^{-1}})=L_{\log\sigma}-R_{\log\rho}$ and $-\langle\sqrt\rho,\log(L_\sigma R_{\rho^{-1}})\sqrt\rho\rangle=-\operatorname{Tr}\rho\log\sigma+\operatorname{Tr}\rho\log\rho=D(\rho\|\sigma)$.
- D5.13.4 *Four entropies.* $D(\rho_f\|\sigma_f)=-S(xUF)+\log d+S(UF)$; $D(\rho_s\|\sigma_s)=-S(xU)+\log d+S(U)$. Difference $=S(xU)+S(UF)-S(U)-S(xUF)=I(x:F|U)=\eta$.

**Output.** D5.12.5, D5.12.8 (middle range), D5.12.9 ($\eta=0$).

**Standard?** Standard: Carlen–Vershynina 2019, Lemma 2.1 (resolvent form of monotonicity), integral log formula as in Petz-type proofs of data processing.

#### D5.14 Step eq:conditional-resolvent-tail — Resolvent defect bounds
*Source: 04-conditional.tex 392–408; display `eq:conditional-resolvent-tail` (405–408).*

**Statement.** $0\le h(v)\le\min(d^2,\,v^{-2})$ and $\|\delta_v\|_2\le\sqrt{h(v)/v}$ for all $v>0$.

**Used from.** D5.2.1, D5.12.1–3, D5.13.

**Proof.**
- D5.14.1 *Local domination.* $\rho_f\le d(I_x\otimes\rho_{UF})=d^2\sigma_f$ (D5.2.1 with $UF$ for $U$). So $\sigma_f^{-1/2}\rho_f\sigma_f^{-1/2}\le d^2$, i.e. $\rho_f^{1/2}\sigma_f^{-1}\rho_f^{1/2}\le d^2$.
- D5.14.2 $\langle a_0,A^{-1}a_0\rangle=\operatorname{Tr}\sqrt{\rho_f}\,\sigma_f^{-1}\rho_f^{3/2}=\operatorname{Tr}\rho_f^2\sigma_f^{-1}\le d^2\operatorname{Tr}\rho_f=d^2$. $\langle b_0,Bb_0\rangle=\operatorname{Tr}\sigma_s=1$.
- D5.14.3 *Bound $d^2$.* $(A+v)^{-1}\le A^{-1}$ and $\langle b_0,(B+v)^{-1}b_0\rangle\ge0$: $h(v)\le d^2$.
- D5.14.4 *Bound $v^{-2}$.* $(A+v)^{-1}\le v^{-1}$: first term $\le v^{-1}$. For $x\ge0$: $\tfrac1{x+v}\ge\tfrac1v-\tfrac x{v^2}$ (equivalent to $x^2\ge0$), so $(B+v)^{-1}\ge v^{-1}-v^{-2}B$ and the second term is $\ge v^{-1}-v^{-2}$. Hence $h(v)\le v^{-1}-v^{-1}+v^{-2}$.
- D5.14.5 $\|(A+v)^{1/2}\delta_v\|^2\ge v\|\delta_v\|^2$ gives $\|\delta_v\|_2\le\sqrt{h/v}$.

**Output.** Integrable majorant and split ends in D5.12.7–8. This is the only place the domination of D5.2.1 enters §5.2.

**Standard?** Elementary; the $d^2$ bound is specific (it is where $\dim x$, not $\dim UF$, enters).

---

### 5.3 A local conjugation estimate

#### D5.15 Lemma 5.3 — Conditional skew estimate
*Source: 04-conditional.tex 481–613; lemma 487–507; display `eq:conditional-skew` (503–505).*

**Statement.** Let $\theta$ be a unit pure vector on $P,x,U,F$; $Y=xU$; $\rho_D$ marginals. Suppose $P=P_0P_1$ and $0\le h\le I$ is supported on $P_0x$. Set
$$d_h=(\dim P_0)(\dim x),\quad\ell_h=\log(ed_h),\quad\eta=I(x:F|U)_\theta=I(x:F|P)_\theta .$$
Define the entire function
$$f(z)=\big\langle\theta,\ \rho_P^{[z]}\rho_Y^{[-z]}\,h\,\rho_P^{[-z]}\rho_Y^{[z]}\,\theta\big\rangle .$$
There are universal $c,C>0$ such that for $0<a\ell_h\le c$ and $t=a/2$:
$$|f(t)|-\Re f(t)\le Ca^2\ell_h^4\,\eta^{1/8}.$$
In particular the left side vanishes if $\eta=0$.

**Used from.** D5.1 (F1, F2), D5.12 (Lemma 5.2) with $d=\dim x$, D2.2 (item 4, for $\eta\le2\log d$), D5.16–D5.20 (listed in the roadmap).

**Proof (roadmap).** Put $p=\langle\theta,h\theta\rangle\in[0,1]$, so $f(0)=p$.
- D5.15.1 *Strip bound.* $|f|\le C$ on $|\Re z|\le b=c_0/\ell_h$ →D5.16.
- D5.15.2 *Imaginary axis.* $f(iu)=\langle w_u,hw_u\rangle$, $w_u=\widehat\rho_Y^{iu}\widehat\rho_{YF}^{-iu}\theta$; compare with $w_u^0=\widehat\rho_U^{iu}\widehat\rho_{UF}^{-iu}\theta$ →D5.17.
- D5.15.3 *Phases to skew.* $|f(iu)-p|\le2\sqrt p\|w_u-w_u^0\|+\|w_u-w_u^0\|^2$; $f'(0)\in i\mathbb R$, $|f'(0)|\le C\sqrt p\,\mathcal R_\eta$ →D5.18.
- D5.15.4 *Remainder* $|f(t)-p-tf'(0)|\le C(t/b)^2m^{1/2}$, $m=\min(1,\mathcal R_\eta)$, $0\le t\le b/8$ →D5.19.
- D5.15.5 *Conclude.* $|f(t)|-\Re f(t)\le Ca^2(\ell_h^2m^{1/2}+\mathcal R_\eta^2)$ (D5.19.4) and $\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}$ (D5.20). Shrink $c$ so that $a\ell_h\le c$ implies $t=a/2\le b/8$, i.e. $c\le c_0/4$.

**Output.** §6 (`05-replicas.tex` 8, 840): applied pointwise to $f_\theta$ for the symbol of a local similarity transform (with $x$ enlarged to the designated supporting subsystem; $P$ and $F$ exchangeable); §7 (`06-transport.tex` 333, 721): the symbol cost $\operatorname{Tr}(\sigma\mathsf D_{i,j})$ at a split leaf, $a\ell$ small enough as in Lemma 5.3.

**Standard?** Specific to this paper (the combination of Lemma 5.2 with Gaussian-weighted three-lines and a second-order Cauchy remainder).

**Pitfall.** Notation clashes inside the proof: $b=c_0/\ell_h$ (strip half-width) is unrelated to $b$ of D5.3 and to $b_1\in\mathbb R$ with $f'(0)=ib_1$. $\eta=I(x:F|U)$ involves only $x$ (not $P_0x$), so $\mathcal R_\eta$ uses $d=\dim x\le d_h$; all other constants use $d_h$. $f(t)$, $t>0$ real, is the quantity whose phase is controlled; $|f(t)|-\Re f(t)\ge0$ measures departure from $[0,\infty)$.

#### D5.16 Step eq:conditional-narrow-strip — Bound on a strip of width $c_0/\ell_h$
*Source: 04-conditional.tex 509–538; display `eq:conditional-narrow-strip` (534–538).*

**Statement.** There are a small universal $c_0\le\tfrac14$ and a universal $C$ with $|f(z)|\le C$ for $|\Re z|\le b=c_0/\ell_h$. On the imaginary axis $0\le f(iu)\le1$; on $|\Re z|\le\tfrac14$, $|f(z)|\le d_h^2$.

**Used from.** D5.1.

**Proof.**
- D5.16.1 *Decompose $h$.* With matrix units on $P_0$: $h=\sum_{jk}|j\rangle\langle k|\otimes h_{jk}$, $h_{jk}$ operators on $x$, $\|h_{jk}\|\le\|h\|\le1$. At most $(\dim P_0)^2\le d_h^2$ terms $c\otimes d'$, each $\|c\|\|d'\|\le1$.
- D5.16.2 *Single term, $0\le\Re z\le\tfrac14$.* $c$ and $\rho_P^{[\pm z]}$ act on $P$; $d'$ and $\rho_Y^{[\pm z]}$ on $Y$; these commute across. So the term is $\big\langle\rho_Y^{[\bar z]}(d')^*\rho_Y^{[-\bar z]}\theta,\ \rho_P^{[z]}c\,\rho_P^{[-z]}\theta\big\rangle$.
- D5.16.3 *Norms.* By (F1), $\|\rho^{[z]}c\rho^{[-z]}\theta\|=\|\rho^{[z]}c\rho^{[1/2-z]}\|_2$. For $0\le\Re z\le\tfrac12$ Hölder with $\|\rho^{[z]}\|_{1/\Re z}=\|\rho^{[1/2-z]}\|_{1/(1/2-\Re z)}=1$ gives $\le\|c\|$. Endpoints $\Re z\in\{0,\tfrac12\}$: same with $\|\rho^{[z]}\|_\infty\le1$ and $\|\rho^{[1/2-z]}\|_2=1$ (support powers). Same for $d'$ and $\rho_Y$. So each term has modulus $\le1$ and $|f(z)|\le d_h^2$ on $0\le\Re z\le\tfrac14$.
- D5.16.4 *Reflection.* $f(-\bar z)=\overline{f(z)}$ (take adjoint of the operator in $f$, $h=h^*$, $(\rho^{[z]})^*=\rho^{[\bar z]}$, $P$- and $Y$-factors commute). So $|f(z)|\le d_h^2$ on $|\Re z|\le\tfrac14$.
- D5.16.5 *Imaginary axis.* $f(iu)=\langle V\theta,hV\theta\rangle$, $V=\rho_P^{[-iu]}\rho_Y^{[iu]}$ a partial isometry, so $0\le f(iu)\le\|V\theta\|^2\le1$ (reality also from D5.16.4: $f(iu)=\overline{f(iu)}$).
- D5.16.6 *Three-lines on $0\le\Re z\le\tfrac14$* ($f$ entire, bounded there): $|f(z)|\le1^{1-4\Re z}(d_h^2)^{4\Re z}=d_h^{8\Re z}$. At $\Re z\le b=c_0/\ell_h$: $d_h^{8b}=e^{8c_0\log d_h/\ell_h}\le e^{8c_0}$ ($\log d_h\le\ell_h$). Negative side by D5.16.4.

**Output.** D5.19 (outer lines of the Gaussian-weighted strip).

**Standard?** Specific. Hadamard three-lines standard.

**Pitfall.** The strip half-width shrinks as $1/\ell_h$; this is the source of the factor $\ell_h^2$ in $(t/b)^2$ (D5.19) and hence of the $\ell_h$ powers in the final bound.

#### D5.17 Step eq:conditional-phase-discrepancy — From $f(iu)$ to phase products
*Source: 04-conditional.tex 540–560; display `eq:conditional-phase-discrepancy` (553–557).*

**Statement.** $f(iu)=\langle w_u,hw_u\rangle$ with $w_u=\widehat\rho_Y^{\,iu}\widehat\rho_{YF}^{-iu}\theta$ (unit). With $w_u^0=\widehat\rho_U^{\,iu}\widehat\rho_{UF}^{-iu}\theta$: $\langle w_u^0,hw_u^0\rangle=p$, and
$$\|w_u-w_u^0\|=\big\|(\widehat\rho_U^{-iu}\widehat\rho_Y^{\,iu}-\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu})\theta\big\|\le C|\sinh(\pi u)|\,\mathcal R_\eta ,$$
with $\mathcal R_\eta$ of D5.12 for $d=\dim x$.

**Used from.** D5.1 (F2), D5.12 with $xU=Y$.

**Proof.**
- D5.17.1 $f(iu)=\langle W\theta,hW\theta\rangle$, $W=\rho_P^{[-iu]}\rho_Y^{[iu]}$. $\theta$ is pure on $P\otimes YF$, so (F2): $\rho_P^{[-iu]}\theta=\widehat\rho_{YF}^{-iu}\theta$. $\rho_Y^{[iu]}$ commutes with $P$-operators, and the vector $\widehat\rho_{YF}^{-iu}\theta$ lies in $\supp\rho_{YF}\subseteq\supp\rho_Y\otimes F$, where $\rho_Y^{[iu]}=\widehat\rho_Y^{\,iu}$. So $W\theta=w_u$.
- D5.17.2 $w_u^0$ is a unitary on $UF$ applied to $\theta$; $h$ acts on $P_0x$ and commutes with it: $\langle w_u^0,hw_u^0\rangle=\langle\theta,h\theta\rangle=p$.
- D5.17.3 *Equality of norms.* Multiply both vectors by the unitary $\widehat\rho_P^{\,iu}$, then by $\widehat\rho_U^{-iu}$. By (F2) $\widehat\rho_P^{\,iu}\theta=\widehat\rho_{YF}^{\,iu}\theta$, hence $\widehat\rho_P^{\,iu}w_u=\widehat\rho_Y^{\,iu}\widehat\rho_{YF}^{-iu}\widehat\rho_{YF}^{\,iu}\theta=\widehat\rho_Y^{\,iu}\theta$, and $\widehat\rho_P^{\,iu}w_u^0=\widehat\rho_U^{\,iu}\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu}\theta$. After $\widehat\rho_U^{-iu}$: $\widehat\rho_U^{-iu}\widehat\rho_Y^{\,iu}\theta$ and $\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu}\theta$. Their difference has norm $\|w_u-w_u^0\|$.
- D5.17.4 Lemma 5.2 with $xU\to Y$ (same operator, $Y=xU$) gives the bound.

**Output.** D5.18.

**Standard?** Specific; Schmidt mirroring standard.

**Pitfall.** The first mirroring changes $\rho_P$ to $\rho_{YF}$, not to $\rho_{UF}$: $w_u^0$ keeps $\widehat\rho_{YF}^{\,iu}$ after $\widehat\rho_P^{\,iu}$, which is exactly what produces $\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu}$ in Lemma 5.2.

#### D5.18 Step eq:conditional-first-derivative — Imaginary-axis skew and $f'(0)$
*Source: 04-conditional.tex 562–574; display `eq:conditional-first-derivative` (570–572).*

**Statement.**
$$|f(iu)-p|\le2\sqrt p\,\|w_u-w_u^0\|+\|w_u-w_u^0\|^2,\qquad f'(0)\in i\mathbb R,\quad|f'(0)|\le C\sqrt p\,\mathcal R_\eta .$$

**Used from.** D5.17, D5.12, D5.16.4.

**Proof.**
- D5.18.1 $h\ge0$: $\langle w,hw\rangle=\|h^{1/2}w\|^2$. With $\Delta=w_u-w_u^0$: $\big|\|h^{1/2}w_u\|-\|h^{1/2}w_u^0\|\big|\le\|h^{1/2}\Delta\|\le\|\Delta\|$ ($h\le I$), $\|h^{1/2}w_u^0\|=\sqrt p$. So $|\|h^{1/2}w_u\|^2-p|\le2\sqrt p\|\Delta\|+\|\Delta\|^2$.
- D5.18.2 *Derivative.* $f$ entire, $f(0)=p$: $f(iu)-p=iuf'(0)+O(u^2)$. By D5.17, RHS of D5.18.1 $\le2\sqrt pC|\sinh\pi u|\mathcal R_\eta+C^2\sinh^2(\pi u)\mathcal R_\eta^2$. Divide by $|u|$, let $u\to0$: $|f'(0)|\le2\pi C\sqrt p\,\mathcal R_\eta$.
- D5.18.3 $f'(0)\in i\mathbb R$: $f(iu)$ is real for real $u$ (D5.16.4/5), so $\tfrac d{du}f(iu)=if'(iu)$ is real at $u=0$.

**Output.** D5.19.4 (the $b_1$-term).

**Standard?** Elementary.

#### D5.19 Step — Gaussian-weighted three-lines and second-order remainder
*Source: 04-conditional.tex 576–600.*

**Statement.** Let $m=\min(1,\mathcal R_\eta)$, $F(z)=(f(z)-p)e^{z^2}$. Then $|F|\le Cm$ on $\Re z=0$, $|F|\le C$ on $\Re z=\pm b$, $|F|\le Cm^{1/2}$ on $|\Re z|\le b/2$, and for $0\le t\le b/8$
$$|f(t)-p-tf'(0)|\le C(t/b)^2m^{1/2},\qquad |f(t)|-\Re f(t)\le Ca^2\big(\ell_h^2m^{1/2}+\mathcal R_\eta^2\big)\quad(t=a/2).$$

**Used from.** D5.16, D5.17, D5.18.

**Proof.**
- D5.19.1 *Imaginary axis.* $|e^{(iu)^2}|=e^{-u^2}$. If $\mathcal R_\eta\le1$ ($m=\mathcal R_\eta$): by D5.18.1 and D5.17, $|F(iu)|\le e^{-u^2}\big(C|\sinh\pi u|+C^2\sinh^2(\pi u)\big)\mathcal R_\eta\le Cm$ ($e^{-u^2}\sinh^2\pi u$ bounded). If $\mathcal R_\eta>1$ ($m=1$): $|f(iu)-p|\le1\le2$ (both in $[0,1]$), so $|F|\le2e^{-u^2}\le2$.
- D5.19.2 *Outer lines.* $|e^{z^2}|=e^{(\Re z)^2-(\Im z)^2}\le e^{b^2}\le e^{1/16}$ and $|f|\le C$ (D5.16): $|F|\le C$ on $\Re z=\pm b$.
- D5.19.3 *Three-lines on each half-strip $0\le\Re z\le b$* (and symmetrically on $-b\le\Re z\le0$): $|F(z)|\le(Cm)^{1-\Re z/b}C^{\Re z/b}$, which for $\Re z\le b/2$ is $\le C'm^{1/2}$ ($m\le1$). If $m=0$, then $\eta=0$, $F\equiv0$ on the imaginary axis, so $F\equiv0$ (identity theorem) and $f\equiv p$.
- D5.19.4 *Cauchy.* Let $g=f-p=Fe^{-z^2}$. On $|z|\le b/2$: $|g|\le Cm^{1/2}e^{b^2/4}\le C'm^{1/2}$ (the disc $|z|\le b/2$ lies in $|\Re z|\le b/2$). Cauchy's estimates on this disc, $R=b/2$: $|g^{(k)}(0)|/k!\le C'm^{1/2}R^{-k}$. $g(0)=0$, $g'(0)=f'(0)$. For $t\le b/8$, $t/R\le\tfrac14$:
$$|g(t)-tg'(0)|\le C'm^{1/2}\sum_{k\ge2}(t/R)^k\le\tfrac43C'm^{1/2}(t/R)^2=C(t/b)^2m^{1/2}.$$
Write $f(t)=p+itb_1+\epsilon$, $f'(0)=ib_1$, $|\epsilon|\le C(t/b)^2m^{1/2}$. If $p>0$: $|p+itb_1|-p=\frac{t^2b_1^2}{|p+itb_1|+p}\le\frac{t^2b_1^2}{2p}\le Ct^2\mathcal R_\eta^2$ (D5.18: $b_1^2\le C^2p\mathcal R_\eta^2$). If $p=0$: $b_1=0$ by D5.18. $\Re(p+itb_1)=p$. Then $|f(t)|-\Re f(t)\le(|p+itb_1|-p)+2|\epsilon|\le Ct^2\mathcal R_\eta^2+C(t\ell_h/c_0)^2m^{1/2}$, i.e. with $t=a/2$ the stated bound.

**Output.** D5.15.5.

**Standard?** Specific; Gaussian factor $e^{z^2}$ is the usual device to make a strip bound integrable along the imaginary axis.

**Pitfall.** Two different small scales: Gaussian damping handles $u\to\infty$; the strip width $b$ handles $\Re z$. The $m^{1/2}$ (a square root of the phase size) is what finally limits the exponent in $\eta$ to $1/8$.

#### D5.20 Step — Parameter bookkeeping: $\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}$
*Source: 04-conditional.tex 601–612.*

**Statement.** With $d=\dim x\le d_h$: for $0<\eta\le1$, $\mathcal R_\eta\le C\sqrt{\eta\log(ed_h/\eta)}$; for $\eta\ge1$, $\eta\le2\ell_h$ and $\mathcal R_\eta\le C\ell_h$. Consequently
$$\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}.$$

**Used from.** D5.12 (definition of $\mathcal R_\eta$), D2.2 item 4 ($S(x|\cdot)\le\log d$ in modulus).

**Proof.**
- D5.20.1 *$0<\eta\le1$.* $y=\eta$. $\sqrt\eta\le\sqrt{\eta\log(ed_h/\eta)}$ ($\log(ed_h/\eta)\ge1$) and $d\le d_h$: $\mathcal R_\eta\le C\sqrt{\eta\log(ed_h/\eta)}$. Now $\eta\log(ed_h/\eta)=\eta\ell_h+\eta\log(1/\eta)\le\ell_h\eta+C\eta^{1/2}\le C\ell_h\eta^{1/2}$. Hence $\mathcal R_\eta^2\le C\ell_h\eta^{1/2}\le C\ell_h\eta^{1/8}$ and $m^{1/2}\le\mathcal R_\eta^{1/2}\le C\ell_h^{1/4}\eta^{1/8}$. Sum $\le C\ell_h^{9/4}\eta^{1/8}\le C\ell_h^4\eta^{1/8}$.
- D5.20.2 *$\eta\ge1$.* $\eta=S(x|P)+S(x|U)\le2\log d\le2\ell_h$ (D2.2 item 4 applied twice). $y=1$: $\mathcal R_\eta=1+\sqrt{\eta\log(ed)}\le1+\sqrt{2\ell_h\cdot\ell_h}\le C\ell_h$. With $m\le1$: sum $\le C\ell_h^2\le C\ell_h^4\eta^{1/8}$.

**Output.** D5.15.5. Absorbing $\log(1/\eta)$ by a smaller power of $\eta$ is why the exponent is $1/8$ rather than $1/4$.

**Standard?** Elementary.

**Pitfall.** For $\eta\ge1$ the bound comes from $\eta\le2\ell_h$, not from smallness; this case requires $\eta\le2\log d$, valid because $\eta$ is a sum of two conditional entropies of $x$.

#### D5.21 Step — Closing remark
*Source: 04-conditional.tex 615–621.*

**Statement.** Lemmas 5.1 and 5.3 hold without Hamiltonian assumptions. A local change of partition has non-negative conditional information cost $\eta$. The departure of a conjugated local positive expectation from the non-negative real axis is bounded by a fractional power ($\eta^{1/8}$) of the same cost. One-copy constants depend only on the moved/supporting dimension ($\dim x$, resp. $d_h$); the remaining systems are arbitrary.

**Used from.** D5.5, D5.15.

**Output.** Interpretation used in §6–§7: $\eta$ = entropy gained (movement), $\eta^{1/8}$-skew = energy spent (local term), when a small subsystem changes sides.

**Standard?** Remark.

---

## Parameters and constants

| Symbol | Value / meaning | Fixed in |
|---|---|---|
| $d$, $\ell$ | $\dim x$; $\ell=\log(ed)\ge1$ | D5.3, Lemma 5.1 statement |
| $d_h$, $\ell_h$ | $(\dim P_0)(\dim x)$; $\log(ed_h)$ | Lemma 5.3 statement |
| $L$ | $\log p_i-\log q_j$ under $p_i\lvert\langle i,j\rangle\rvert^2$ | D5.2 |
| $\mathbb EL$, $\mathbb Ee^{\pm L}$ | $-S(x\|U)$; both $\le d$ | D5.2 |
| $c$ (D5.3) | universal, $\le\tfrac12$ (expansion) with $\lvert b\rvert\ell\le c$ | D5.3 |
| $a$ | $0<a<\tfrac14$, $a\ell\le c$ (Lemma 5.1); $a\ell_h\le c$ (Lemma 5.3) | D5.4, D5.5, D5.15 |
| $r$ | $(1-2a)^{-1}\in(1,2)$; $r-1=2ar$; $2ar'=1$ | D5.4 |
| $K$, $Z$ | $Q^{-a}\rho Q^{-a}$; $\lVert K\rVert_r$; $\log Z\le-2aS(x\|U)+Ca^2\ell^2$ | D5.4 |
| $c$ (Lemma 5.1) | universal; small enough for D5.3, D5.4 ($a\ell\le c/4$ there), D5.7 ($a<\tfrac14$) | D5.5 |
| $C_0$ | universal, $\ge\tfrac12\times$ constant in $\log Z$ bound | D5.6 |
| $M(u)$, $\lambda(u)$, $\xi$ | $\lVert\tau_u^aQ^{-a}\theta\rVert$; $-ad_U+C_0a^2\ell^2-\log M(u)\ge0$; $K^r/\operatorname{Tr}K^r$ | D5.6 |
| $H$ | $\lVert\sqrt\rho-\sqrt\xi\rVert_2\le C\sqrt a\,\ell$ | D5.7 |
| $\theta_u$ | $\tau^{-iau}Q^{iau}\theta$; $\lVert\theta_u-\theta\rVert\le C(1+\lvert u\rvert)(\sqrt\lambda+\sqrt a\ell)$ | D5.9 |
| Exponent $5/4$ | $a^{5/4}\ell^2$ in Lemma 5.1; from $a^{4/3}\ell^{4/3}$ (Young), $a^2\ell^2$, $a^{5/4}\ell^{3/2}$ | D5.5.10 |
| Young exponents | $\lambda^{1/4}$ with conjugate $4/3$ | D5.5.10 |
| Interpolation density | $du/(2\cosh\pi u)$, mass $\tfrac12$ per line | D5.11 |
| $\mathcal H_f,\mathcal H_s,A,B,V$ | HS spaces; $L_{\sigma_f}R_{\rho_f^{-1}}$, $L_{\sigma_s}R_{\rho_s^{-1}}$; isometry $V$ | D5.12 |
| $y$, $\mathcal R_\eta$ | $\min(1,\eta)$; $\sqrt y+\sqrt{\eta\log(ed/y)}$, $\mathcal R_0=0$ | D5.12 |
| Split points | $y/d^2$ and $1/y$ | D5.12.8 |
| $h(v)$ | $\le\min(d^2,v^{-2})$, $\int_0^\infty h=\eta$ | D5.13, D5.14 |
| Majorant | $d\,v^{-3/4}$ near $0$, $v^{-3/2}$ near $\infty$, for $\Re z\in[-\tfrac14,0)$ | D5.12.7 |
| $b$, $c_0$ | $c_0/\ell_h$; $c_0\le\tfrac14$ universal | D5.16 |
| Strip half-width $\tfrac14$ | for $\lvert f\rvert\le d_h^2$ | D5.16 |
| $p$, $m$ | $\langle\theta,h\theta\rangle$; $\min(1,\mathcal R_\eta)$ | D5.15, D5.19 |
| $t$ | $a/2$, with $t\le b/8$ | D5.15.5, D5.19 |
| Exponent $1/8$, power $\ell_h^4$ | final skew bound $Ca^2\ell_h^4\eta^{1/8}$ | D5.20 |

## Dependencies

**Consumes.**
- §2: D2.1 (entropies), D2.2 (SSA; $\lvert S(x\|\cdot)\rvert\le\log\dim x$; purity), D2.4 (Lemma 2.1, `lem:continuity`, used in D5.10 with $D=x$), D2.5 (pure-state trace distance).
- External: Hölder and Schatten norms; Hadamard three-lines; Stein–Hirschman interpolation / Poisson kernel of the strip; Nussbaum–Szkoła 2009 (the two-eigenbasis construction); Petz 1986 (context for D5.12); Carlen–Vershynina 2019, Lemma 2.1 (resolvent compression, D5.13).
- §3, §4 (Hamiltonian, quasi-local filters): not used; §5 is purely about finite-dimensional pure states.

**Exports.**
- Lemma 5.1 (D5.5), with its smallness hypothesis $a\log(e\dim x)\le c$: §6 (`05-replicas.tex` 488, 580), lifted to symmetric powers.
- Lemma 5.3 (D5.15): §6 (`05-replicas.tex` 8, 840) and §7 (`06-transport.tex` 333, 721).
- Internal-only: D5.2–D5.4 (log-moment/Schatten estimates), Lemma 5.2 (D5.12), used only through D5.15–D5.17.
