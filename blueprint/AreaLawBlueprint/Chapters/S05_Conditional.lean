import Verso
import VersoManual
import VersoBlueprint
import AreaLawBlueprint.TexPrelude
import AreaLawRefactored

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Two conditional operator estimates" =>

$`\theta` pure on finite-dimensional $`P,x,U,F`. Constants depend only on $`d=\dim x` (resp. support dimension of a local operator), never on $`\dim P,U,F`. Order: (i) relative log-moment bound for $`(\rho_{xU},\,I_x\otimes\widehat\rho_U)` => conditional Schatten estimate ({bpref "D5.2"}[D5.2]–{bpref "D5.4"}[D5.4]); (ii) Lemma 5.1: word of four fractional powers on $`\theta` has norm $`\le\exp(-\tfrac a2\eta+Ca^{5/4}\ell^2)`, $`\eta=I(x:F|U)`; complex interpolation, left boundary from (i), right boundary from (i) plus entropy continuity ({bpref "D5.5"}[D5.5]–{bpref "D5.11"}[D5.11]); (iii) Lemma 5.2: $`\widehat\rho_U^{-iu}\widehat\rho_{xU}^{iu}` moves $`\theta` by $`\le C|\sinh\pi u|\mathcal R_\eta` when $`F` is appended; resolvent-compression identity whose integral is $`\eta` ({bpref "D5.12"}[D5.12]–{bpref "D5.14"}[D5.14]); (iv) Lemma 5.3: for $`0\le h\le I` on $`P_0x`, $`f(z)=\langle\theta,\rho_P^{[z]}\rho_Y^{[-z]}h\rho_P^{[-z]}\rho_Y^{[z]}\theta\rangle` satisfies $`|f(a/2)|-\Re f(a/2)\le Ca^2\ell_h^4\eta^{1/8}`; three-lines on $`f` plus (iii) ({bpref "D5.15"}[D5.15]–{bpref "D5.20"}[D5.20]). §6 lifts (ii) to symmetric tensor powers (entropy gained when $`x` changes side); §6–§7 use (iv) as energy spent for a local term.

# 5.0 Notation and a relative log-moment bound

:::definition "D5.1" (lean := "AreaLaw.bracketPow, AreaLaw.hatPow, AreaLaw.hat, AreaLaw.marg, AreaLaw.ℓ")
*D5.1* — Def: Spectral powers, hat, norms

_Source: 04-conditional.tex 14–29._

For a density matrix $`\rho` with spectral projections $`\Pi_p`: $$`\rho^{[z]}=\sum_{p>0}p^z\,\Pi_p\quad(z\in\mathbb C),\qquad \widehat\rho=\rho+\Pi_{\ker\rho}.`

$`\rho^{[z]}=0` on $`\ker\rho` for every $`z`, including $`z=0`: $`\rho^{[0]}=\Pi_{\supp\rho}`.

$`\widehat\rho>0`; $`\widehat\rho^{\,iu}` unitary, $`=1` on $`\ker\rho`. Likewise $`\widehat\rho^{-a}=1` on $`\ker\rho`.

Brackets omitted for positive real powers ($`\rho^a=\rho^{[a]}`, $`a>0`).

On a purification of $`\rho`, $`\rho^{[s]}` and $`\widehat\rho^{\,s}` ($`s\in i\mathbb R`) give the same vector when applied innermost (vector lies in $`\supp\rho`).

Operators tensored with $`I` on unmentioned factors.

$`\|T\|_p=(\operatorname{Tr}|T|^p)^{1/p}`, $`1\le p<\infty`; $`\|T\|_\infty=\|T\|`; $`\|\cdot\|_2` = Hilbert–Schmidt. Faithful = positive definite.

_Used from._ none.

:::

:::lemma_ "D5.2" (lean := "AreaLaw.step_5_2")
*D5.2* — Step eq:conditional-log-moments: Three moments of $`L`

_Source: 04-conditional.tex 31–67; display `eq:conditional-log-moments` (51–55)._

$`\rho` density matrix on $`xU`, $`d=\dim x`, $`Q=I_x\otimes\widehat\rho_U` ($`Q>0`). Eigenbases $`\{|i\rangle\}` of $`\rho` (eigenvalues $`p_i`), $`\{|j\rangle\}` of $`Q` (eigenvalues $`q_j>0`), the $`Q`-basis adapted to $`x\otimes\supp\rho_U\ \oplus\ x\otimes\ker\rho_U`. On pairs $`(i,j)` with $`p_i>0` put probability $`p_i|\langle i,j\rangle|^2` (total mass $`\sum_ip_i=1`). Real random variable $$`L=\log p_i-\log q_j.` Then $$`\mathbb E\,L=-S(x|U)_\rho,\qquad \mathbb E\,e^{L}\le d,\qquad \mathbb E\,e^{-L}\le d .` Constants free of $`\dim U`. Also $`\rho\le d\,(I_x\otimes\rho_U)\le dQ`.

:::

:::proof "D5.2" (uses := "D5.1, D2.1")
*D5.2.1* _Domination $`\rho\le d(I_x\otimes\rho_U)`._ $`v=\sum_{b=1}^d|b\rangle v_b`, $`\rho_{bb'}=\langle b|\rho|b'\rangle` (operators on $`U`). Positivity of $`\rho` (Cauchy–Schwarz for $`\langle\cdot,\rho\,\cdot\rangle`): $`|\langle v_b,\rho_{bb'}v_{b'}\rangle|\le\langle v_b,\rho_{bb}v_b\rangle^{1/2}\langle v_{b'},\rho_{b'b'}v_{b'}\rangle^{1/2}`. Sum over $`b,b'`, Cauchy–Schwarz in $`b`: $$`\langle v,\rho v\rangle\le\Big(\sum_b\langle v_b,\rho_{bb}v_b\rangle^{1/2}\Big)^2\le d\sum_b\langle v_b,\rho_{bb}v_b\rangle\le d\sum_b\langle v_b,\rho_Uv_b\rangle,` last since $`\rho_{bb}\le\sum_{b'}\rho_{b'b'}=\rho_U`. So $`\rho\le d(I_x\otimes\rho_U)\le dQ` ($`\widehat\rho_U\ge\rho_U`).

*D5.2.2* _Support._ $`\operatorname{Tr}[(I_x\otimes\Pi_{\ker\rho_U})\rho]=\operatorname{Tr}[\Pi_{\ker\rho_U}\rho_U]=0\Rightarrow\supp\rho\subseteq x\otimes\supp\rho_U`. So $`\langle i,j\rangle=0` whenever $`p_i>0` and $`|j\rangle\in x\otimes\ker\rho_U`.

*D5.2.3* _Mean._ $`\mathbb E\log p_i=\sum_ip_i\log p_i=-S(xU)`. $`\mathbb E\log q_j=\sum_j\langle j,\rho j\rangle\log q_j=\operatorname{Tr}\rho\,(I_x\otimes\log\widehat\rho_U)=\operatorname{Tr}\rho_U\log\rho_U=-S(U)`. Hence $`\mathbb EL=-S(xU)+S(U)=-S(x|U)`.

*D5.2.4* _$`\mathbb E\,e^L`._ $`\mathbb Ee^L=\sum p_i^2|\langle i,j\rangle|^2/q_j=\operatorname{Tr}\rho^2Q^{-1}`. From $`\rho\le dQ`: $`Q^{-1/2}\rho Q^{-1/2}\le dI`, i.e. $`\|Q^{-1/2}\rho^{1/2}\|^2\le d`, i.e. $`\rho^{1/2}Q^{-1}\rho^{1/2}\le dI`. Then $`\operatorname{Tr}\rho^2Q^{-1}=\operatorname{Tr}\rho^{1/2}(\rho^{1/2}Q^{-1}\rho^{1/2})\rho^{1/2}\le d\operatorname{Tr}\rho=d`.

*D5.2.5* _$`\mathbb E\,e^{-L}`._ $`\mathbb Ee^{-L}=\sum_{p_i>0,j}q_j|\langle i,j\rangle|^2=\operatorname{Tr}(\Pi_{\supp\rho}Q)`. By D5.2.2 $`\Pi_{\supp\rho}\le\Pi_{x\otimes\supp\rho_U}`, $`Q\ge0`, so $`\operatorname{Tr}(\Pi_{\supp\rho}Q)\le\operatorname{Tr}(\Pi_{x\otimes\supp\rho_U}Q)=d\operatorname{Tr}\rho_U=d`.

_Formal route_ (RefactoringResult.md §5, D5.2.1): the complementary Weyl twirl `d⁻² ∑_{a,b} W_{ab} ρ W_{ab}* = d⁻¹ ρ_U ⊗ I` (library `WeylTwirl.lean`, from §4) contains the term `W_{00} = 1`, so `ρ ≤ d (ρ_U ⊗ I)` (`step_5_2_1`, AreaLawRefactored/S05\_Conditional.lean:85). Reason: the twirl identity was already in the library; same constant `d`.

_Used from._ {bpref "D5.1"}[D5.1]; {bpref "D2.1"}[D2.1] ($`S(x|U)`).

:::

:::lemma_ "D5.3" (lean := "AreaLaw.step_5_3")
*D5.3* — Step eq:conditional-log-mgf: Log-moment generating function

_Source: 04-conditional.tex 69–82; display `eq:conditional-log-mgf` (78–81)._

$`\ell=\log(ed)` ($`\ell\ge1`). Universal $`c,C>0` with $$`\Pr(|L|>v)\le2de^{-v},\qquad \mathbb E\big[L^2e^{|bL|}\big]\le C\ell^2\ \ (|b|\ell\le c),` $$`\log\mathbb Ee^{bL}\le-bS(x|U)_\rho+Cb^2\ell^2,\qquad|b|\ell\le c .` Constants free of $`\dim U`.

:::

:::proof "D5.3" (uses := "D5.2")
*D5.3.1* Markov on {bpref "D5.2"}[D5.2]: $`\Pr(L>v)=\Pr(e^L>e^v)\le de^{-v}`, $`\Pr(L<-v)=\Pr(e^{-L}>e^v)\le de^{-v}`.

*D5.3.2* _Second moment with exponential weight_ (paper: "splitting at $`2\ell` and integrating this tail"). $`c\le1/2`, so $`|b|\le1/2`. $`g(s)=s^2e^{|b|s}`, increasing. On $`|L|\le2\ell`: $`g\le4\ell^2e^{2|b|\ell}\le4e\ell^2`. On $`|L|>2\ell`: layer-cake $$`\mathbb E[g(|L|)1_{|L|>2\ell}]=g(2\ell)\Pr(|L|>2\ell)+\int_{2\ell}^\infty g'(s)\Pr(|L|>s)\,ds,` with $`g(2\ell)\Pr(|L|>2\ell)\le4e\ell^2\cdot2de^{-2\ell}\le C\ell^2` ($`de^{-2\ell}=e^{-2}/d`) and $`g'(s)\le(2s+s^2)e^{s/2}`, so integral $`\le2d\int_{2\ell}^\infty(2s+s^2)e^{-s/2}ds\le C\,d\,\ell^2e^{-\ell}=C\ell^2/e`.

*D5.3.3* _Taylor._ $`e^{bL}\le1+bL+\tfrac{b^2}2L^2e^{|bL|}` (Lagrange remainder). Take $`\mathbb E`, $`\mathbb EL=-S(x|U)`: $`\mathbb Ee^{bL}\le1-bS(x|U)+\tfrac C2b^2\ell^2`. Apply $`\log(1+y)\le y`.

_Formal route_ (RefactoringResult.md §5, D5.3.2): direct split at `|L| ≤ 2ℓ` with `L² ≤ 8ℓ² + 16e^{|L|/2−ℓ}` (port of old `tilted_second_moment`; `step_5_3`, AreaLawRefactored/S05\_Conditional/LogMoments.lean:94). Reason: shorter for finite sums.

_Used from._ {bpref "D5.2"}[D5.2].

:::

:::lemma_ "D5.4" (lean := "AreaLaw.step_5_4_of")
*D5.4* — Step eq:conditional-schatten: Conditional Schatten estimate

_Source: 04-conditional.tex 84–114; display `eq:conditional-schatten` (91–94)._

For $`0<a<1/4` put $`K=Q^{-a}\rho Q^{-a}`, $`r=(1-2a)^{-1}\in(1,2)`, $`Z=(\operatorname{Tr}K^r)^{1/r}=\|K\|_r`. After reducing the universal $`c`: $$`\log Z\le-2aS(x|U)_\rho+Ca^2\ell^2,\qquad a\ell\le c .` Identities: $`r-1=2ar`; dual exponent $`r'=r/(r-1)` satisfies $`2a\,r'=1`.

:::

:::proof "D5.4" (uses := "D5.2, D5.3")
*D5.4.1* $`K=T^*T` with $`T=\rho^{1/2}Q^{-a}`, so $`Z=\|T\|_{2r}^2`.

*D5.4.2* _Analytic family_ $`T(z)=\rho^{[z/2]}Q^{-az}`, $`0\le\Re z\le r`. At $`\Re z=0`: $`T(iu)=\rho^{[iu/2]}Q^{-iau}`, partial isometry times unitary, $`\|T(iu)\|\le1`. At $`\Re z=r`: $`\|T(r+iu)\|_2^2\le\|\rho^{r/2}Q^{-ar}\|_2^2=\operatorname{Tr}\rho^rQ^{-2ar}=\mathbb Ee^{(r-1)L}` (eigenbasis sum $`\sum p_i^r q_j^{-(r-1)}|\langle i,j\rangle|^2`, $`2ar=r-1`).

*D5.4.3* _Interpolation_ between $`p_0=\infty` and $`p_1=2` at $`\theta=1/r` (point $`z=1` in $`[0,r]`): $`1/p_\theta=\tfrac1r\cdot\tfrac12=\tfrac1{2r}`. So $`\|T(1)\|_{2r}\le1^{1-1/r}\big(\mathbb Ee^{(r-1)L}\big)^{(1/2)(1/r)}`, hence $$`Z=\|\rho^{1/2}Q^{-a}\|_{2r}^2\le\big(\mathbb Ee^{(r-1)L}\big)^{1/r}.`

*D5.4.4* _Scalar form of D5.4.3._ $`B=V|B|` (polar), $`\|B\|_{(2r)'}=1`, $`(2r)'=2r/(2r-1)`. Scalar function $`z\mapsto\operatorname{Tr}\big(T(z)\,|B|^{(2r)'(1-z/(2r))}V^*\big)`. Test matrix $`W(z)=|B|^{(2r)'(1-z/(2r))}V^*`: at $`\Re z=0`, $`\|W\|_1=\operatorname{Tr}|B|^{(2r)'}=1`; at $`\Re z=r`, $`\|W\|_2^2=\operatorname{Tr}|B|^{(2r)'}=1`; at $`z=1` exponent is $`(2r)'(1-\tfrac1{2r})=1`, $`W(1)=|B|V^*=B^*`. Hölder bounds the scalar by $`\|T\|_\infty\|W\|_1\le1` on the first line, $`\|T\|_2\|W\|_2` on the second; Hadamard three-lines at $`z=1`: $`|\operatorname{Tr}T(1)B^*|\le(\mathbb Ee^{(r-1)L})^{1/(2r)}`; duality $`\|T(1)\|_{2r}=\sup_B|\operatorname{Tr}T(1)B^*|`. Singular test matrices: approximate.

*D5.4.5* _Insert {bpref "D5.3"}[D5.3]_ with $`b=r-1=2ar\le4a` ($`r<2`); need $`|b|\ell\le c_3`, ensured by $`a\ell\le c_3/4`: $$`\log Z\le\tfrac1r\big[-(r-1)S(x|U)+C(r-1)^2\ell^2\big]=-2aS(x|U)+4Ca^2r\ell^2\le-2aS(x|U)+8Ca^2\ell^2.`

_Formal route_ (RefactoringResult.md §5, D5.4.2–4): Araki–Lieb–Thirring `Tr(Q^sAQ^s)^r ≤ Tr A^r Q^{2sr}` proved once by a three-lines/test-matrix argument (`araki_lieb_thirring`, AreaLawRefactored/S05\_Conditional/Movement/ArakiLiebThirring.lean:217), specialised to `s = −a` (`step_5_4_of`, Movement/Schatten.lean:174). Reason: Mathlib has no Schatten norms or matrix interpolation.

_Used from._ {bpref "D5.2"}[D5.2], {bpref "D5.3"}[D5.3].

:::

# 5.1 Moving a subsystem

:::lemma_ "D5.5" (lean := "AreaLaw.lemma_5_1")
*D5.5* — Lemma 5.1: Conditional movement estimate

_Source: 04-conditional.tex 118–308; display `eq:conditional-movement` (129–133)._

$`\theta` unit pure vector on finite-dimensional $`P,x,U,F`; $`\rho_D` its marginals. $`d=\dim x`, $`\ell=\log(ed)`, $$`\eta=S(x|P)_\theta+S(x|U)_\theta=I(x:F|U)_\theta=I(x:F|P)_\theta .` Universal $`c,C>0` such that for $`0<a\ell\le c` and all density matrices $`\sigma` on $`xP`, $`\tau` on $`xU`: $$`\Big\|\sigma^{a/2}\,\widehat\rho_P^{-a/2}\,\tau^{a/2}\,\widehat\rho_U^{-a/2}\,\theta\Big\|\le\exp\Big(-\frac a2\eta+Ca^{5/4}\ell^2\Big).` Same bound for positive subnormalised $`\sigma,\tau`.

:::

:::proof "D5.5" (uses := "D2.2, D2.4, D2.5, D5.1, D5.2, D5.4, D5.6, D5.7, D5.8, D5.9, D5.10, D5.11")
_roadmap; →D = proved there; order as in the paper._

*D5.5.1* _Identities._ Purity and SSA give $`\eta\ge0` and the three expressions (D5.5.A).

*D5.5.2* _Reduction._ $`\sigma,\tau` faithful (removed in D5.5.11). $`d_U=S(x|U)_\theta`, $`d_P=S(x|P)_\theta`.

*D5.5.3* _Analytic function._ For $`0\le\Re z\le1`, $$`G(z)=\sigma^{az}\widehat\rho_P^{-az}\,\tau^{a(1-z)}\widehat\rho_U^{-a(1-z)}\theta .` $`G(1/2)` is the vector of the statement. Imaginary powers unitary, so $`G` bounded on the closed strip (bound may depend on the fixed faithful factors).

*D5.5.4* _Left boundary._ $`\|G(iu)\|=M(u)=\|\tau_u^aQ^{-a}\theta\|`, $`\tau_u=Q^{-iau}\tau Q^{iau}`, $`M(u)^2\le Z`, $`\log\|G(iu)\|=-ad_U+C_0a^2\ell^2-\lambda(u)`, $`\lambda\ge0` →{bpref "D5.6"}[D5.6].

*D5.5.5* _Hellinger closeness_ of $`\rho` and $`\xi=K^r/\operatorname{Tr}K^r`: $`\|\sqrt\rho-\sqrt\xi\|_2\le C\sqrt a\,\ell` →{bpref "D5.7"}[D5.7].

*D5.5.6* _Phase vs Hellinger_ (general inequality) →{bpref "D5.8"}[D5.8].

*D5.5.7* _State movement_ $`\theta_u=\tau^{-iau}Q^{iau}\theta`: $`\|\theta_u-\theta\|\le C(1+|u|)(\sqrt{\lambda(u)}+\sqrt a\,\ell)` →{bpref "D5.9"}[D5.9].

*D5.5.8* _Right boundary_ $`\log\|G(1+iu)\|\le-ad_P+Ca^2\ell^2+Ca\ell(1+|u|)^{1/2}(\lambda(u)^{1/4}+a^{1/4}\ell^{1/2})` →{bpref "D5.10"}[D5.10].

*D5.5.9* _Interpolation._ Midpoint, harmonic measure →{bpref "D5.11"}[D5.11]: $$`\log\|G(\tfrac12)\|\le\int_{\mathbb R}\big[\log\|G(iu)\|+\log\|G(1+iu)\|\big]\frac{du}{2\cosh\pi u}.`

*D5.5.10* _Sum._ Insert D5.5.4 and D5.5.8 at the same $`u`. Entropy terms: $`\tfrac12(-ad_U-ad_P)=-\tfrac a2\eta`. $`\lambda`-terms: for $`\lambda\ge0`, $`B>0`, Young gives $`-\lambda+B\lambda^{1/4}\le CB^{4/3}` (maximum at $`\lambda^{3/4}=B/4`); with $`B=Ca\ell(1+|u|)^{1/2}` this is $`\le C\,a^{4/3}\ell^{4/3}(1+|u|)^{2/3}`. $`\int(1+|u|)^{s}\frac{du}{2\cosh\pi u}<\infty` for every fixed $`s`, so after integration:

Young term $`\le Ca^{4/3}\ell^{4/3}\le Ca^{5/4}\ell^2` ($`a<1`, $`\ell\ge1`);

quadratic terms $`a^2\ell^2\le a^{5/4}\ell^2`;

leftover $`Ca\ell(1+|u|)^{1/2}a^{1/4}\ell^{1/2}\to Ca^{5/4}\ell^{3/2}\le Ca^{5/4}\ell^2`. Total: $`\log\|G(\tfrac12)\|\le-\tfrac a2\eta+Ca^{5/4}\ell^2`.

*D5.5.11* _Remove faithfulness._ Replace $`\sigma,\tau` by $`(1-\epsilon)\sigma+\epsilon I/\dim`, $`\epsilon\to0`; positive powers (exponent $`a/2>0`) continuous. Subnormalised: $`\sigma=s\sigma'`, $`s\le1`, gives $`\sigma^{a/2}=s^{a/2}\sigma'^{a/2}`, which only decreases the norm; zero case trivial.

_D5.5.A (identities)._ $`\theta` pure on $`PxUF`: $`S(xUF)=S(P)`, $`S(UF)=S(xP)`, $`S(U)=S(xPF)`, $`S(xU)=S(PF)`. Then $$`I(x:F|U)=S(xU)+S(UF)-S(U)-S(xUF)=S(PF)+S(xP)-S(U)-S(P)=S(x|P)+S(x|U),` $$`I(x:F|P)=S(xP)+S(PF)-S(P)-S(xPF)=S(xP)+S(PF)-S(P)-S(U),` equal to the previous line. SSA ({bpref "D2.2"}[D2.2] item 1) gives $`I\ge0`.

_Formal route_ (RefactoringResult.md §5, D5.5.9–{bpref "D5.11"}[D5.11]): paired Gaussian three-lines on `g(z) = f(z)·conj f(1−z̄)·e^{B(z−1/2)²}` (reflection `z ↦ 1−z̄` pairs `iu` with `1+iu` at the same `u`), `u`-growth bounded pointwise by `(3+u²)/2` (`step_5_11`, AreaLawRefactored/S05\_Conditional/Interpolation.lean:118; `step_5_5_10` :142). Reason: Mathlib has three-lines but no Poisson kernel/harmonic measure for the strip.

_Formal route_ (RefactoringResult.md §5, D5.5.11): only `τ` regularised (`lemma_5_1_of_faithful`, Movement/Regularise.lean:49). Reason: `σ^{[az]}` is entire and `σ^{[iau]}` a contraction, faithfulness of `σ` not needed.

_Used from._ {bpref "D2.2"}[D2.2] (items 1, 5: SSA, purity), {bpref "D2.4"}[D2.4] (Lemma 2.1), {bpref "D2.5"}[D2.5] (pure-state trace distance), {bpref "D5.1"}[D5.1], {bpref "D5.2"}[D5.2], {bpref "D5.4"}[D5.4], {bpref "D5.6"}[D5.6]–{bpref "D5.11"}[D5.11].

:::

:::lemma_ "D5.6" (lean := "AreaLaw.step_5_6")
*D5.6* — Step eq:conditional-slack, eq:conditional-overlap: Left boundary and slack

_Source: 04-conditional.tex 151–174; displays `eq:conditional-slack` (167–170), `eq:conditional-overlap` (172–174)._

With $`\rho=\rho_{xU}`, $`Q=I_x\otimes\widehat\rho_U`, $`\tau_u=Q^{-iau}\tau Q^{iau}`, for all real $`u`: $$`\|G(iu)\|=M(u):=\|\tau_u^aQ^{-a}\theta\|,\qquad M(u)^2=\operatorname{Tr}\tau_u^{2a}K\le Z,\qquad\log Z\le-2ad_U+Ca^2\ell^2 .` Fix universal $`C_0\ge\tfrac12C`. Define $$`\lambda(u)=-ad_U+C_0a^2\ell^2-\log M(u)\ge0,\qquad\xi=K^r/\operatorname{Tr}K^r .` Then $`\operatorname{Tr}\tau_u^{2a}\xi^{1-2a}=M(u)^2/Z\ge e^{-2\lambda(u)}`, and $`\log\|G(iu)\|=-ad_U+C_0a^2\ell^2-\lambda(u)` exactly.

:::

:::proof "D5.6" (uses := "D5.4, D5.2")
*D5.6.1* $`G(iu)=\sigma^{iau}\widehat\rho_P^{-iau}\ \tau^{a}\tau^{-iau}\ Q^{-a}Q^{iau}\ \theta`. Drop the two leftmost unitaries. $`Q^{iau}` commutes with $`Q^{-a}`; $`\tau^{a-iau}Q^{iau}=Q^{iau}\,\tau_u^{a}\tau_u^{-iau}`. Drop $`Q^{iau}` and $`\tau_u^{-iau}` (latter commutes with $`\tau_u^a`): $`\|G(iu)\|=\|\tau_u^aQ^{-a}\theta\|=M(u)`.

*D5.6.2* $`M(u)^2=\langle\theta,Q^{-a}\tau_u^{2a}Q^{-a}\theta\rangle=\operatorname{Tr}_{xU}\tau_u^{2a}Q^{-a}\rho Q^{-a}=\operatorname{Tr}\tau_u^{2a}K` ($`xU`-marginal of $`\theta` is $`\rho`). Hölder with exponents $`r',r`: $`\le\|\tau_u^{2a}\|_{r'}\|K\|_r=(\operatorname{Tr}\tau_u^{2ar'})^{1/r'}Z=Z`, since $`2ar'=1` and $`\operatorname{Tr}\tau_u=1`.

*D5.6.3* $`\lambda\ge0`: $`\log M=\tfrac12\log M^2\le\tfrac12\log Z\le-ad_U+C_0a^2\ell^2`.

*D5.6.4* $`\xi^{1-2a}=\xi^{1/r}=K/Z`, so $`\operatorname{Tr}\tau_u^{2a}\xi^{1-2a}=\operatorname{Tr}\tau_u^{2a}K/Z=M^2/Z`. Insert $`M^2=e^{2(-ad_U+C_0a^2\ell^2-\lambda)}` and $`Z\le e^{-2ad_U+2C_0a^2\ell^2}`: ratio $`\ge e^{-2\lambda}`.

_Formal route_ (RefactoringResult.md §5, D5.6.2): Hölder on eigenvalue sums weighted by eigenvector overlaps (`step_5_6`, Movement/Schatten.lean:140). Reason: no Schatten norms in Mathlib.

_Used from._ {bpref "D5.4"}[D5.4], {bpref "D5.2"}[D5.2].

:::

:::lemma_ "D5.7" (lean := "AreaLaw.step_5_7")
*D5.7* — Step eq:conditional-hellinger: $`\rho` and $`\xi` are Hellinger-close

_Source: 04-conditional.tex 176–199; display `eq:conditional-hellinger` (197–199)._

$`H:=\|\sqrt\rho-\sqrt\xi\|_2\le C\sqrt a\,\ell` (for $`0<a\ell\le c`).

:::

:::proof "D5.7" (uses := "D5.2, D5.4, D5.6")
*D5.7.1* _Lower bound on the self-overlap._ $`\|\rho^aQ^{-a}\theta\|\ge\langle\theta,\rho^aQ^{-a}\theta\rangle=\operatorname{Tr}\rho^{1+a}Q^{-a}=\mathbb Ee^{aL}\ge e^{a\mathbb EL}=e^{-ad_U}` (Cauchy–Schwarz with $`\|\theta\|=1`; trace real positive since it equals $`\mathbb Ee^{aL}`; Jensen; {bpref "D5.2"}[D5.2]). Square, {bpref "D5.6"}[D5.6.2] with $`\tau_u\to\rho`: $`\operatorname{Tr}\rho^{2a}K=\|\rho^aQ^{-a}\theta\|^2\ge e^{-2ad_U}`.

*D5.7.2* Divide by $`Z\le e^{-2ad_U+C_Za^2\ell^2}` ({bpref "D5.4"}[D5.4]): $`\operatorname{Tr}\rho^{2a}\xi^{1-2a}=\operatorname{Tr}\rho^{2a}K/Z\ge e^{-C_Za^2\ell^2}\ge1-C_Za^2\ell^2`.

*D5.7.3* _Concavity._ $`\phi(b)=1-\operatorname{Tr}\rho^{[b]}\xi^{[1-b]}` on $`[0,1]`. In eigenbases, $`\operatorname{Tr}\rho^{[b]}\xi^{[1-b]}=\sum_{p,s>0}p^bs^{1-b}|\langle p,s\rangle|^2`; each $`b\mapsto p^bs^{1-b}` convex, so $`\phi` concave. $`\phi\ge0`: Hölder, $`\operatorname{Tr}\rho^{[b]}\xi^{[1-b]}\le\|\rho^{[b]}\|_{1/b}\|\xi^{[1-b]}\|_{1/(1-b)}=(\operatorname{Tr}\rho)^b(\operatorname{Tr}\xi)^{1-b}=1` (endpoints: $`\operatorname{Tr}\Pi_{\supp\rho}\xi\le1`).

*D5.7.4* For $`2a\le\tfrac12`: concavity on $`0\le2a\le\tfrac12` gives $`\phi(2a)\ge(1-4a)\phi(0)+4a\phi(\tfrac12)\ge4a\phi(\tfrac12)`. So $`1-\operatorname{Tr}\sqrt\rho\sqrt\xi=\phi(\tfrac12)\le\phi(2a)/(4a)\le C_Za\ell^2/4`.

*D5.7.5* $`H^2=\operatorname{Tr}\rho+\operatorname{Tr}\xi-2\operatorname{Tr}\sqrt\rho\sqrt\xi=2\phi(\tfrac12)\le\tfrac12C_Za\ell^2`.

_Used from._ {bpref "D5.2"}[D5.2] (Jensen step), {bpref "D5.4"}[D5.4], {bpref "D5.6"}[D5.6.2].

:::

:::lemma_ "D5.8" (lean := "AreaLaw.step_5_8")
*D5.8* — Step eq:conditional-phase-hellinger: Phases are Hellinger-continuous

_Source: 04-conditional.tex 219–231; display `eq:conditional-phase-hellinger` (221–224)._

Density matrices $`A,B` (same dimension), real $`b`: $$`\big\|(\widehat A^{ib}-\widehat B^{ib})\sqrt B\big\|_2\le C(1+|b|)\,\|\sqrt A-\sqrt B\|_2,` $`C` universal.

:::

:::proof "D5.8" (uses := "D5.1")
Eigenbases $`|\alpha\rangle` of $`A`, $`|\beta\rangle` of $`B` ($`\widehat\alpha=1` if $`\alpha=0`): $$`\text{LHS}^2=\sum_{\alpha,\beta}|\langle\alpha,\beta\rangle|^2\,\beta\,|\widehat\alpha^{ib}-\widehat\beta^{ib}|^2,\qquad\|\sqrt A-\sqrt B\|_2^2=\sum_{\alpha,\beta}|\langle\alpha,\beta\rangle|^2(\sqrt\alpha-\sqrt\beta)^2 .` Suffices termwise: $`\beta|\widehat\alpha^{ib}-\widehat\beta^{ib}|^2\le C(1+|b|)^2(\sqrt\alpha-\sqrt\beta)^2`.

*D5.8.1* $`\beta=0`: LHS term $`0`.

*D5.8.2* $`\alpha,\beta>0`, $`v=\alpha/\beta`: need $`|1-v^{ib}|\le C(1+|b|)|1-\sqrt v|`. If $`\tfrac14\le v\le4`: $`|1-v^{ib}|\le|b||\log v|` and $`|\log v|=2|\log\sqrt v|\le4|\sqrt v-1|` (mean value, $`\tfrac{d}{ds}\log s\le2` on $`[\tfrac12,2]`). If $`v\notin[\tfrac14,4]`: $`|1-v^{ib}|\le2\le4|1-\sqrt v|` ($`|1-\sqrt v|>\tfrac12` there).

*D5.8.3* $`\alpha=0<\beta`: $`|1-\beta^{ib}|\le2`, $`|\sqrt0-\sqrt\beta|=\sqrt\beta`, so $`\beta|\cdot|^2\le4\beta=4(\sqrt\alpha-\sqrt\beta)^2`.

_Used from._ {bpref "D5.1"}[D5.1].

:::

:::lemma_ "D5.9" (lean := "AreaLaw.step_5_9_of")
*D5.9* — Step eq:conditional-state-movement: The state arriving at the right boundary

_Source: 04-conditional.tex 201–258; display `eq:conditional-state-movement` (209–212)._

$`\theta_u=\tau^{-iau}Q^{iau}\theta=Q^{iau}\tau_u^{-iau}\theta` (unit vector, same $`P`-marginal as $`\theta`: the unitary lives on $`xU`). For $`0<a\ell\le c`, all $`u\in\mathbb R`: $$`\|\theta_u-\theta\|\le C(1+|u|)\big(\sqrt{\lambda(u)}+\sqrt a\,\ell\big).`

:::

:::proof "D5.9" (uses := "D5.2, D5.3, D5.6, D5.7, D5.8")
(Hats throughout: "all kernel phases extended by one".)

*D5.9.1* _Reduction._ $`\|\theta_u-\theta\|=\|\tau_u^{-iau}\theta-Q^{-iau}\theta\|\le\|(\widehat\rho^{-iau}-Q^{-iau})\theta\|+\|(\tau_u^{-iau}-\widehat\rho^{-iau})\theta\|`, $`\widehat\rho=\widehat\rho_{xU}`.

*D5.9.2* _First term._ (F1), eigenbases $`\{i\},\{j\}` of $`\rho,Q`: $`\|(Q^{-iau}-\widehat\rho^{-iau})\theta\|^2=\sum p_i|\langle i,j\rangle|^2|q_j^{-iau}-p_i^{-iau}|^2\le a^2u^2\,\mathbb EL^2\le Ca^2u^2\ell^2` ($`|e^{ix}-e^{iy}|\le|x-y|`; $`\mathbb EL^2\le C\ell^2` from {bpref "D5.3"}[D5.3] at $`b=0`).

*D5.9.3* _Second term, insert $`\xi`._ By (F1) it equals $`\|(\tau_u^{-iau}-\widehat\rho^{-iau})\sqrt\rho\|_2`. Split $`\tau_u^{-iau}-\widehat\rho^{-iau}=(\tau_u^{-iau}-\widehat\xi^{-iau})+(\widehat\xi^{-iau}-\widehat\rho^{-iau})`:

(a) $`\|(\widehat\xi^{-iau}-\widehat\rho^{-iau})\sqrt\rho\|_2\le C(1+a|u|)H` by {bpref "D5.8"}[D5.8] with $`(A,B)=(\xi,\rho)`;

(b) $`\|(\tau_u^{-iau}-\widehat\xi^{-iau})\sqrt\rho\|_2\le\|(\tau_u^{-iau}-\widehat\xi^{-iau})\sqrt\xi\|_2+2H` (operator norm $`\le2`).

*D5.9.4* _The $`\xi,\tau_u` phase difference._ Eigenvalues $`p` of $`\xi`, $`q` of $`\tau_u` (faithful, so $`q>0`), probability $`p|\langle p,q\rangle|^2`, $`v=\log(q/p)`, only $`p>0`. Then $$`\|(\tau_u^{-iau}-\widehat\xi^{-iau})\sqrt\xi\|_2^2=\mathbb E|1-e^{-iauv}|^2,` $$`\mathbb Ee^v=\operatorname{Tr}\Pi_{\supp\xi}\tau_u\le1,\qquad\mathbb Ee^{2av}=\operatorname{Tr}\xi^{1-2a}\tau_u^{2a}\ge e^{-2\lambda(u)}\ \ (\text{D5.6}).`

*D5.9.5* _On $`\{v\le0\}`._ Claim $`|1-e^{-iauv}|^2\le C(1+u^2)(1-e^{2av})`. Put $`w=-v\ge0`: $`|1-e^{i\phi}|^2\le\min(4,\phi^2)` with $`\phi=auw`. If $`2aw\le1`: $`1-e^{-2aw}\ge(1-e^{-1})2aw` and $`a^2u^2w^2\le\tfrac12u^2\,aw`. If $`2aw>1`: $`1-e^{-2aw}\ge1-e^{-1}` and use $`4`. Next $$`\mathbb E[(1-e^{2av})1_{v\le0}]=\Pr(v\le0)-\mathbb E[e^{2av}1_{v\le0}]\le1-e^{-2\lambda}+\mathbb E[(e^{2av}-1)1_{v>0}]\le2\lambda+2a,` using $`\Pr(v\le0)=1-\Pr(v>0)`, $`\mathbb E[e^{2av}1_{v\le0}]=\mathbb Ee^{2av}-\mathbb E[e^{2av}1_{v>0}]\ge e^{-2\lambda}-\mathbb E[e^{2av}1_{v>0}]`, $`1-e^{-2\lambda}\le2\lambda`, and for $`v>0`: $`e^{2av}-1\le2a(e^v-1)\le2ae^v` (concavity of $`x\mapsto x^{2a}` at $`x=1`), $`\mathbb Ee^v\le1`.

*D5.9.6* _On $`\{v>0\}`._ $`|1-e^{-iauv}|^2\le a^2u^2v^2\le a^2u^2e^v` ($`v^2\le e^v`), contributes $`\le a^2u^2\mathbb Ee^v\le a^2u^2`.

*D5.9.7* _Sum._ D5.9.5–6: $`\mathbb E|1-e^{-iauv}|^2\le C(1+u^2)(\lambda+a)` ($`a^2u^2\le au^2`). So the $`\xi,\tau_u` term is $`\le C(1+|u|)(\sqrt\lambda+\sqrt a)`. Add D5.9.2, D5.9.3 (a),(b), and $`H\le C\sqrt a\,\ell` ({bpref "D5.7"}[D5.7]); use $`a\le\sqrt a\le\sqrt a\,\ell` ($`a<1`, $`\ell\ge1`).

_Formal route_ (RefactoringResult.md §5, D5.9.5–6): one pointwise bound `φ ≤ 16(1+u²)(1−e^{2av}+4ae^v)`, summed (`step_5_9_of`, Movement/StateMovement.lean:220). Reason: simpler.

_Used from._ {bpref "D5.2"}[D5.2] ($`\mathbb EL^2\le C\ell^2` via {bpref "D5.3"}[D5.3]), {bpref "D5.6"}[D5.6], {bpref "D5.7"}[D5.7], {bpref "D5.8"}[D5.8].

:::

:::lemma_ "D5.10" (lean := "AreaLaw.step_5_10_1, AreaLaw.step_5_10_3")
*D5.10* — Step: Right boundary

_Source: 04-conditional.tex 260–279._

For $`0<a\ell\le c` and all real $`u`: $$`\log\|G(1+iu)\|\le-ad_P+Ca^2\ell^2+Ca\ell(1+|u|)^{1/2}\big(\lambda(u)^{1/4}+a^{1/4}\ell^{1/2}\big).`

:::

:::proof "D5.10" (uses := "D5.4, D5.9, D2.4, D2.5")
*D5.10.1* _Reduce to a conjugated $`\sigma`._ $`G(1+iu)=\sigma^{a+iau}\widehat\rho_P^{-a-iau}\tau^{-iau}\widehat\rho_U^{iau}\theta=\sigma^{a+iau}\widehat\rho_P^{-a-iau}\theta_u`. Put $`\sigma'=\widehat\rho_P^{\,iau}\sigma\,\widehat\rho_P^{-iau}` (density on $`xP`). Then $`\sigma^{a+iau}\widehat\rho_P^{-iau}=\widehat\rho_P^{-iau}\sigma'^{a+iau}`; drop the unitaries $`\widehat\rho_P^{-iau}`, $`\sigma'^{iau}`: $`\|G(1+iu)\|=\|\sigma'^a\widehat\rho_P^{-a}\theta_u\|`.

*D5.10.2* _Schatten._ $`P`-marginal of $`\theta_u` equals that of $`\theta`, so $`\widehat\rho_P` is the marginal operator of $`\theta_u`. {bpref "D5.4"}[D5.4] and Hölder on $`xP` (as {bpref "D5.6"}[D5.6.2]): $`\log\|G(1+iu)\|\le-aS(x|P)_{\theta_u}+Ca^2\ell^2`.

*D5.10.3* _Continuity._ Lemma 2.1 with $`D=x`, $`E=P`: $`|S(x|P)_{\theta_u}-S(x|P)_\theta|\le C\sqrt\delta\,\ell`, $`\delta=\tfrac12\|\rho_{xP}[\theta_u]-\rho_{xP}[\theta]\|_1\le\|\theta_u-\theta\|` ({bpref "D2.5"}[D2.5]). By {bpref "D5.9"}[D5.9] and $`\sqrt{s+t}\le\sqrt s+\sqrt t`: $$`\sqrt{\|\theta_u-\theta\|}\le C(1+|u|)^{1/2}\big(\lambda^{1/4}+a^{1/4}\ell^{1/2}\big).` So $`-aS(x|P)_{\theta_u}\le-ad_P+Ca\ell(1+|u|)^{1/2}(\lambda^{1/4}+a^{1/4}\ell^{1/2})`.

_Used from._ {bpref "D5.4"}[D5.4] (with $`U\to P`), {bpref "D5.9"}[D5.9], {bpref "D2.4"}[D2.4] (Lemma 2.1 with $`D=x`, $`E=P`), {bpref "D2.5"}[D2.5].

:::

:::lemma_ "D5.11" (lean := "AreaLaw.step_5_11")
*D5.11* — Step: Log-interpolation with harmonic measure

_Source: 04-conditional.tex 281–293._

$`G` vector-valued, analytic in $`0<\Re z<1`, bounded and continuous on the closed strip, $`\log\|G\|` integrable on both boundary lines. Then $$`\log\|G(\tfrac12)\|\le\int_{\mathbb R}\log\|G(iu)\|\frac{du}{2\cosh\pi u}+\int_{\mathbb R}\log\|G(1+iu)\|\frac{du}{2\cosh\pi u},` each line carrying mass $`\int\frac{du}{2\cosh\pi u}=\tfrac12`.

:::

:::proof "D5.11" (uses := "D5.5")
*D5.11.1* $`z\mapsto e^{\pi iz}` maps the strip onto the upper half-plane ($`|e^{\pi iz}|=e^{-\pi\Im z}`, $`\arg=\pi\Re z`), $`z=\tfrac12\mapsto i`, $`\Re z=0\mapsto(0,\infty)`, $`\Re z=1\mapsto(-\infty,0)`. Harmonic measure at $`i` is $`\frac{dx}{\pi(1+x^2)}`; with $`x=\pm e^{-\pi u}`, $`|dx|=\pi e^{-\pi u}du`: density $`\frac{du}{e^{\pi u}+e^{-\pi u}}=\frac{du}{2\cosh\pi u}`.

*D5.11.2* Scalar case: sub-mean value property for $`\log|\varphi|`, $`\varphi` analytic, on bounded subdomains then by exhaustion.

*D5.11.3* Vector case: if $`G(\tfrac12)\ne0` put $`\varphi(z)=\langle e,G(z)\rangle`, $`e=G(\tfrac12)/\|G(\tfrac12)\|`. Then $`\log\|G(\tfrac12)\|=\log|\varphi(\tfrac12)|\le\int\log|\varphi|\,d\mu\le\int\log\|G\|\,d\mu`.

*D5.11.4* Legitimacy: for faithful $`\sigma,\tau` all boundary norms are bounded above and away from zero (unitaries and invertible factors), so integrals are finite and the limit in D5.11.2 is justified.

_Formal route_ (RefactoringResult.md §5, {bpref "D5.5"}[D5.5.9]–D5.11): paired Gaussian three-lines on `g(z) = f(z)·conj f(1−z̄)·e^{B(z−1/2)²}` (reflection `z ↦ 1−z̄` pairs `iu` with `1+iu` at the same `u`), `u`-growth bounded pointwise by `(3+u²)/2` (`step_5_11`, AreaLawRefactored/S05\_Conditional/Interpolation.lean:118; `step_5_5_10` :142). Reason: Mathlib has three-lines but no Poisson kernel/harmonic measure for the strip.

_Used from._ none ({bpref "D5.5"}[D5.5.3] supplies the hypotheses).

:::

# 5.2 Comparing marginal phases

:::lemma_ "D5.12" (lean := "AreaLaw.lemma_5_2")
*D5.12* — Lemma 5.2: Marginal-phase comparison

_Source: 04-conditional.tex 310–479; lemma 321–339; display `eq:conditional-modular-bound` (331–336)._

$`\theta` unit pure vector on finite-dimensional $`P,x,U,F`; $`\rho_D` its marginals; $`d=\dim x`, $`\eta=I(x:F|U)_\theta`. For $`\eta>0` set $$`y=\min(1,\eta),\qquad\mathcal R_\eta=\sqrt y+\sqrt{\eta\log(ed/y)},\qquad\mathcal R_0=0 .` Universal $`C` such that for every $`u\in\mathbb R` $$`\Big\|\big(\widehat\rho_U^{-iu}\widehat\rho_{xU}^{\,iu}-\widehat\rho_{UF}^{-iu}\widehat\rho_{xUF}^{\,iu}\big)\theta\Big\|\le C|\sinh(\pi u)|\,\mathcal R_\eta .` In particular the two phase products agree on $`\theta` if $`\eta=0`. Constants independent of $`\dim P,U,F`.

:::

:::proof "D5.12" (uses := "D5.1, D5.2, D2.1, D5.13, D5.14")
*D5.12.1* _Faithful case set-up_ ($`\rho_f=\rho_{xUF}>0`, hence all marginals $`>0`). $`\sigma_f=\tfrac{I_x}d\otimes\rho_{UF}`, $`\rho_s=\rho_{xU}`, $`\sigma_s=\tfrac{I_x}d\otimes\rho_U`. On Hilbert–Schmidt spaces $`\mathcal H_f` (operators on $`xUF`), $`\mathcal H_s` (on $`xU`): $`A=L_{\sigma_f}R_{\rho_f^{-1}}`, $`B=L_{\sigma_s}R_{\rho_s^{-1}}` ($`L,R` left/right multiplication; commuting positive definite). $`V(X\sqrt{\rho_s})=(X\otimes I_F)\sqrt{\rho_f}`.

*D5.12.2* _$`V` isometry:_ $`\|V(X\sqrt{\rho_s})\|_2^2=\operatorname{Tr}(X^*X\otimes I)\rho_f=\operatorname{Tr}X^*X\rho_s`.

*D5.12.3* _$`V^*AV=B`:_ $`\langle V(X\sqrt{\rho_s}),AV(Y\sqrt{\rho_s})\rangle=\operatorname{Tr}\big[\sqrt{\rho_f}(X^*\otimes I)\sigma_f(Y\otimes I)\sqrt{\rho_f}\rho_f^{-1}\big]=\operatorname{Tr}(X^*\otimes I)\sigma_f(Y\otimes I)=\operatorname{Tr}X^*\sigma_sY`, and $`\langle X\sqrt{\rho_s},BY\sqrt{\rho_s}\rangle=\operatorname{Tr}X^*\sigma_sY` too ($`\operatorname{Tr}_F\sigma_f=\sigma_s`).

*D5.12.4* $`b_0=\sqrt{\rho_s}`, $`a_0=Vb_0=\sqrt{\rho_f}`. For $`v>0`: $`\delta_v=(A+v)^{-1}a_0-V(B+v)^{-1}b_0`, $`h(v)` as in {bpref "D5.13"}[D5.13].

*D5.12.5* _Resolvent identity and entropy:_ $`h(v)\ge0`, $`\int_0^\infty h=\eta` →{bpref "D5.13"}[D5.13]. _Tails:_ $`0\le h(v)\le\min(d^2,v^{-2})`, $`\|\delta_v\|_2\le\sqrt{h(v)/v}` →{bpref "D5.14"}[D5.14].

*D5.12.6* _Fractional powers by the resolvent integral._ For $`-1<\Re z<0`, $`x>0`: $`\int_0^\infty\frac{v^z}{x+v}dv=-\frac{\pi}{\sin\pi z}x^z` (from $`\int_0^\infty\frac{v^{s-1}}{x+v}dv=\frac\pi{\sin\pi s}x^{s-1}`, $`s=z+1`). Spectral calculus: $$`A^za_0-VB^zb_0=-\frac{\sin\pi z}\pi\int_0^\infty v^z\delta_v\,dv .`

*D5.12.7* _Boundary value $`z=-iu`._ For $`-\tfrac14\le\Re z<0`: $`\|v^z\delta_v\|_2\le v^{\Re z}\sqrt{h/v}`, majorised by $`d\,v^{-3/4}` on $`(0,1]` ($`h\le d^2`) and $`v^{-3/2}` on $`[1,\infty)` ($`h\le v^{-2}`). Dominated convergence, $`\Re z\uparrow0`; $`|\sin(-i\pi u)|=|\sinh\pi u|`: $$`\|A^{-iu}a_0-VB^{-iu}b_0\|_2\le C|\sinh\pi u|\int_0^\infty\sqrt{h(v)/v}\,dv .`

*D5.12.8* _Split $`\eta>0`_ at $`y/d^2\le1/y` ($`y\le1\le d`):

$`\int_0^{y/d^2}\sqrt{h/v}\le\int_0^{y/d^2}d\,v^{-1/2}dv=2\sqrt y`;

$`\int_{1/y}^\infty\sqrt{h/v}\le\int_{1/y}^\infty v^{-3/2}dv=2\sqrt y`;

middle, Cauchy–Schwarz: $`\le(\int h)^{1/2}\big(\int_{y/d^2}^{1/y}\frac{dv}v\big)^{1/2}\le\sqrt{\eta\cdot2\log(d/y)}\le C\sqrt{\eta\log(ed/y)}`. Total $`\le C\mathcal R_\eta`.

*D5.12.9* _$`\eta=0`._ $`h\ge0` continuous, $`\int h=0\Rightarrow h\equiv0\Rightarrow\|(A+v)^{1/2}\delta_v\|=0\Rightarrow\delta_v=0\Rightarrow` discrepancy vanishes.

*D5.12.10* _Identify the vectors._ $`A^{-iu}a_0=\sigma_f^{-iu}\rho_f^{iu}\sqrt{\rho_f}`, $`VB^{-iu}b_0=(\sigma_s^{-iu}\rho_s^{iu}\otimes I_F)\sqrt{\rho_f}`. $`\sigma_f^{-iu}=d^{iu}\rho_{UF}^{-iu}`, $`\sigma_s^{-iu}=d^{iu}\rho_U^{-iu}`: cancel the common phase $`d^{iu}`, flip the sign of the difference. Hilbert–Schmidt norm becomes $`\|(\rho_U^{-iu}\rho_{xU}^{iu}-\rho_{UF}^{-iu}\rho_{xUF}^{iu})\sqrt{\rho_f}\|_2`. (F1) ($`\theta` purifies $`\rho_f` with $`P`): $`\|T\theta\|=\|T\sqrt{\rho_f}\|_2` for $`T` on $`xUF`. Faithful case done.

*D5.12.11* _Singular $`\rho_f`._ Replace by $`\rho_{f,\epsilon}=(1-\epsilon)\rho_f+\epsilon I/\dim(xUF)` and its reductions in D5.12.1–10 (proof lives on Hilbert–Schmidt spaces: no purifier of $`\rho_{f,\epsilon}` on $`P` needed). Then:

$`\eta_\epsilon\to\eta` (finite dimension); $`\mathcal R_{\eta_\epsilon}\to\mathcal R_\eta` ($`\mathcal R` continuous on $`(0,\infty)`, $`\mathcal R_\eta\to0` as $`\eta\to0`).

Phase products on $`\sqrt{\rho_{f,\epsilon}}` converge in Hilbert–Schmidt norm, in order of application: innermost $`\widehat\rho_{xU,\epsilon}^{\,iu}` acts on $`\sqrt{\rho_{f,\epsilon}}`; the limit lies in $`\supp\rho_{xU}\otimes F` since $`\supp\rho_f\subseteq\supp\rho_{xU}\otimes F` and the square-root mass outside tends to $`0`; on that space the inner phase converges (mollified marginal commutes with its limit); its output lies in $`x\otimes\supp\rho_U\otimes F`, so the outer $`\widehat\rho_{U,\epsilon}^{-iu}` converges there. Same for the pair $`(xUF,UF)`.

All phases have norm one, which controls the vanishing complementary pieces. Limit is the product of support phases = the unitary extensions in the statement. No operator-norm convergence of phases on a limiting kernel is used.

_Used from._ {bpref "D5.1"}[D5.1] (F1), {bpref "D5.2"}[D5.2.1] (domination), {bpref "D2.1"}[D2.1], {bpref "D5.13"}[D5.13], {bpref "D5.14"}[D5.14].

:::

:::lemma_ "D5.13" (lean := "AreaLaw.step_5_13")
*D5.13* — Step eq:conditional-resolvent-square, eq:conditional-resolvent-entropy: Resolvent defect and its integral

_Source: 04-conditional.tex 366–390; displays `eq:conditional-resolvent-square` (374–379), `eq:conditional-resolvent-entropy` (381–385)._

In the set-up of {bpref "D5.12"}[D5.12] (faithful $`\rho_f`): $$`\|(A+v)^{1/2}\delta_v\|_2^2=\langle a_0,(A+v)^{-1}a_0\rangle-\langle b_0,(B+v)^{-1}b_0\rangle=:h(v)\ge0,` $$`\int_0^\infty h(v)\,dv=D(\rho_f\|\sigma_f)-D(\rho_s\|\sigma_s)=\eta,\qquad D(\rho\|\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma).`

:::

:::proof "D5.13" (uses := "D5.12, D2.1")
*D5.13.1* _Compression identity._ $`g=(A+v)^{-1}a_0`, $`k=(B+v)^{-1}b_0`, $`\delta_v=g-Vk`: $$`\langle\delta_v,(A+v)\delta_v\rangle=\langle g,(A+v)g\rangle-2\Re\langle(A+v)g,Vk\rangle+\langle k,V^*(A+v)Vk\rangle .` $`(A+v)g=a_0`; $`V^*a_0=b_0` ($`V^*V=I`); $`V^*(A+v)V=B+v` ({bpref "D5.12"}[D5.12.3]). Three terms: $`\langle a_0,(A+v)^{-1}a_0\rangle`, $`-2\langle b_0,k\rangle`, $`+\langle b_0,k\rangle`, giving $`h(v)`. $`h\ge0`: left side is a squared norm.

*D5.13.2* _Log formula._ $`\log x=\int_0^\infty\big(\tfrac1{1+v}-\tfrac1{x+v}\big)dv`, $`x>0`. So $`-\langle a_0,\log A\,a_0\rangle=\int_0^\infty\big(\langle a_0,(A+v)^{-1}a_0\rangle-\tfrac{\|a_0\|^2}{1+v}\big)dv`, same for $`B`. $`\|a_0\|^2=\operatorname{Tr}\rho_f=1=\|b_0\|^2`: the $`\tfrac1{1+v}` terms cancel in the difference, and $`\int_0^\infty h=-\langle a_0,\log A\,a_0\rangle+\langle b_0,\log B\,b_0\rangle` (each integral converges separately).

*D5.13.3* _Relative entropy._ $`L,R` commute, so $`\log(L_\sigma R_{\rho^{-1}})=L_{\log\sigma}-R_{\log\rho}` and $`-\langle\sqrt\rho,\log(L_\sigma R_{\rho^{-1}})\sqrt\rho\rangle=-\operatorname{Tr}\rho\log\sigma+\operatorname{Tr}\rho\log\rho=D(\rho\|\sigma)`.

*D5.13.4* _Four entropies._ $`D(\rho_f\|\sigma_f)=-S(xUF)+\log d+S(UF)`; $`D(\rho_s\|\sigma_s)=-S(xU)+\log d+S(U)`. Difference $`=S(xU)+S(UF)-S(U)-S(xUF)=I(x:F|U)=\eta`.

_Used from._ {bpref "D5.12"}[D5.12.1]–4, {bpref "D2.1"}[D2.1].

:::

:::lemma_ "D5.14" (lean := "AreaLaw.step_5_14")
*D5.14* — Step eq:conditional-resolvent-tail: Resolvent defect bounds

_Source: 04-conditional.tex 392–408; display `eq:conditional-resolvent-tail` (405–408)._

$`0\le h(v)\le\min(d^2,\,v^{-2})` and $`\|\delta_v\|_2\le\sqrt{h(v)/v}` for all $`v>0`.

:::

:::proof "D5.14" (uses := "D5.2, D5.12, D5.13")
*D5.14.1* _Local domination._ $`\rho_f\le d(I_x\otimes\rho_{UF})=d^2\sigma_f` ({bpref "D5.2"}[D5.2.1] with $`UF` for $`U`). So $`\sigma_f^{-1/2}\rho_f\sigma_f^{-1/2}\le d^2`, i.e. $`\rho_f^{1/2}\sigma_f^{-1}\rho_f^{1/2}\le d^2`.

*D5.14.2* $`\langle a_0,A^{-1}a_0\rangle=\operatorname{Tr}\sqrt{\rho_f}\,\sigma_f^{-1}\rho_f^{3/2}=\operatorname{Tr}\rho_f^2\sigma_f^{-1}\le d^2\operatorname{Tr}\rho_f=d^2`. $`\langle b_0,Bb_0\rangle=\operatorname{Tr}\sigma_s=1`.

*D5.14.3* _Bound $`d^2`._ $`(A+v)^{-1}\le A^{-1}` and $`\langle b_0,(B+v)^{-1}b_0\rangle\ge0`: $`h(v)\le d^2`.

*D5.14.4* _Bound $`v^{-2}`._ $`(A+v)^{-1}\le v^{-1}`: first term $`\le v^{-1}`. For $`x\ge0`: $`\tfrac1{x+v}\ge\tfrac1v-\tfrac x{v^2}` (equivalent to $`x^2\ge0`), so $`(B+v)^{-1}\ge v^{-1}-v^{-2}B` and second term $`\ge v^{-1}-v^{-2}`. Hence $`h(v)\le v^{-1}-v^{-1}+v^{-2}`.

*D5.14.5* $`\|(A+v)^{1/2}\delta_v\|^2\ge v\|\delta_v\|^2` gives $`\|\delta_v\|_2\le\sqrt{h/v}`.

_Used from._ {bpref "D5.2"}[D5.2.1], {bpref "D5.12"}[D5.12.1]–3, {bpref "D5.13"}[D5.13].

:::

# 5.3 A local conjugation estimate

:::lemma_ "D5.15" (lean := "AreaLaw.lemma_5_3")
*D5.15* — Lemma 5.3: Conditional skew estimate

_Source: 04-conditional.tex 481–613; lemma 487–507; display `eq:conditional-skew` (503–505)._

$`\theta` unit pure vector on $`P,x,U,F`; $`Y=xU`; $`\rho_D` marginals. $`P=P_0P_1` and $`0\le h\le I` supported on $`P_0x`. Set $$`d_h=(\dim P_0)(\dim x),\quad\ell_h=\log(ed_h),\quad\eta=I(x:F|U)_\theta=I(x:F|P)_\theta .` Entire function $$`f(z)=\big\langle\theta,\ \rho_P^{[z]}\rho_Y^{[-z]}\,h\,\rho_P^{[-z]}\rho_Y^{[z]}\,\theta\big\rangle .` Universal $`c,C>0` such that for $`0<a\ell_h\le c` and $`t=a/2`: $$`|f(t)|-\Re f(t)\le Ca^2\ell_h^4\,\eta^{1/8}.` In particular the left side vanishes if $`\eta=0`.

:::

:::proof "D5.15" (uses := "D5.1, D5.12, D2.2, D5.16, D5.17, D5.18, D5.19, D5.20")
_roadmap._

$`p=\langle\theta,h\theta\rangle\in[0,1]`, so $`f(0)=p`.

*D5.15.1* _Strip bound._ $`|f|\le C` on $`|\Re z|\le b=c_0/\ell_h` →{bpref "D5.16"}[D5.16].

*D5.15.2* _Imaginary axis._ $`f(iu)=\langle w_u,hw_u\rangle`, $`w_u=\widehat\rho_Y^{iu}\widehat\rho_{YF}^{-iu}\theta`; compare with $`w_u^0=\widehat\rho_U^{iu}\widehat\rho_{UF}^{-iu}\theta` →{bpref "D5.17"}[D5.17].

*D5.15.3* _Phases to skew._ $`|f(iu)-p|\le2\sqrt p\|w_u-w_u^0\|+\|w_u-w_u^0\|^2`; $`f'(0)\in i\mathbb R`, $`|f'(0)|\le C\sqrt p\,\mathcal R_\eta` →{bpref "D5.18"}[D5.18].

*D5.15.4* _Remainder_ $`|f(t)-p-tf'(0)|\le C(t/b)^2m^{1/2}`, $`m=\min(1,\mathcal R_\eta)`, $`0\le t\le b/8` →{bpref "D5.19"}[D5.19].

*D5.15.5* _Conclude._ $`|f(t)|-\Re f(t)\le Ca^2(\ell_h^2m^{1/2}+\mathcal R_\eta^2)` ({bpref "D5.19"}[D5.19.4]) and $`\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}` ({bpref "D5.20"}[D5.20]). Shrink $`c` so $`a\ell_h\le c` implies $`t=a/2\le b/8`, i.e. $`c\le c_0/4`.

_Used from._ {bpref "D5.1"}[D5.1] (F1, F2), {bpref "D5.12"}[D5.12] (Lemma 5.2) with $`d=\dim x`, {bpref "D2.2"}[D2.2] (item 4, for $`\eta\le2\log d`), {bpref "D5.16"}[D5.16]–{bpref "D5.20"}[D5.20].

:::

:::lemma_ "D5.16" (lean := "AreaLaw.step_5_16")
*D5.16* — Step eq:conditional-narrow-strip: Bound on a strip of width $`c_0/\ell_h`

_Source: 04-conditional.tex 509–538; display `eq:conditional-narrow-strip` (534–538)._

Small universal $`c_0\le\tfrac14` and universal $`C` with $`|f(z)|\le C` for $`|\Re z|\le b=c_0/\ell_h`. On the imaginary axis $`0\le f(iu)\le1`; on $`|\Re z|\le\tfrac14`, $`|f(z)|\le d_h^2`.

:::

:::proof "D5.16" (uses := "D5.1")
*D5.16.1* _Decompose $`h`._ Matrix units on $`P_0`: $`h=\sum_{jk}|j\rangle\langle k|\otimes h_{jk}`, $`h_{jk}` operators on $`x`, $`\|h_{jk}\|\le\|h\|\le1`. At most $`(\dim P_0)^2\le d_h^2` terms $`c\otimes d'`, each $`\|c\|\|d'\|\le1`.

*D5.16.2* _Single term, $`0\le\Re z\le\tfrac14`._ $`c`, $`\rho_P^{[\pm z]}` act on $`P`; $`d'`, $`\rho_Y^{[\pm z]}` on $`Y`; commute across. Term $`=\big\langle\rho_Y^{[\bar z]}(d')^*\rho_Y^{[-\bar z]}\theta,\ \rho_P^{[z]}c\,\rho_P^{[-z]}\theta\big\rangle`.

*D5.16.3* _Norms._ (F1): $`\|\rho^{[z]}c\rho^{[-z]}\theta\|=\|\rho^{[z]}c\rho^{[1/2-z]}\|_2`. For $`0\le\Re z\le\tfrac12` Hölder with $`\|\rho^{[z]}\|_{1/\Re z}=\|\rho^{[1/2-z]}\|_{1/(1/2-\Re z)}=1` gives $`\le\|c\|`. Endpoints $`\Re z\in\{0,\tfrac12\}`: same with $`\|\rho^{[z]}\|_\infty\le1`, $`\|\rho^{[1/2-z]}\|_2=1` (support powers). Same for $`d'`, $`\rho_Y`. Each term has modulus $`\le1`, so $`|f(z)|\le d_h^2` on $`0\le\Re z\le\tfrac14`.

*D5.16.4* _Reflection._ $`f(-\bar z)=\overline{f(z)}` (adjoint of the operator in $`f`, $`h=h^*`, $`(\rho^{[z]})^*=\rho^{[\bar z]}`, $`P`- and $`Y`-factors commute). So $`|f(z)|\le d_h^2` on $`|\Re z|\le\tfrac14`.

*D5.16.5* _Imaginary axis._ $`f(iu)=\langle V\theta,hV\theta\rangle`, $`V=\rho_P^{[-iu]}\rho_Y^{[iu]}` partial isometry, so $`0\le f(iu)\le\|V\theta\|^2\le1` (reality also from D5.16.4: $`f(iu)=\overline{f(iu)}`).

*D5.16.6* _Three-lines on $`0\le\Re z\le\tfrac14`_ ($`f` entire, bounded there): $`|f(z)|\le1^{1-4\Re z}(d_h^2)^{4\Re z}=d_h^{8\Re z}`. At $`\Re z\le b=c_0/\ell_h`: $`d_h^{8b}=e^{8c_0\log d_h/\ell_h}\le e^{8c_0}` ($`\log d_h\le\ell_h`). Negative side by D5.16.4.

_Formal route_ (RefactoringResult.md §5, D5.16.3): eigenbasis computation with weighted AM–GM `|t^{[z]}|²|t'^{[−z]}|²t' ≤ 2s t + (1−2s)t'` (`step_5_16`, AreaLawRefactored/S05\_Conditional/SkewStrip.lean:436). Reason: no Schatten norms.

_Used from._ {bpref "D5.1"}[D5.1].

:::

:::lemma_ "D5.17" (lean := "AreaLaw.step_5_17")
*D5.17* — Step eq:conditional-phase-discrepancy: From $`f(iu)` to phase products

_Source: 04-conditional.tex 540–560; display `eq:conditional-phase-discrepancy` (553–557)._

$`f(iu)=\langle w_u,hw_u\rangle` with $`w_u=\widehat\rho_Y^{\,iu}\widehat\rho_{YF}^{-iu}\theta` (unit). With $`w_u^0=\widehat\rho_U^{\,iu}\widehat\rho_{UF}^{-iu}\theta`: $`\langle w_u^0,hw_u^0\rangle=p`, and $$`\|w_u-w_u^0\|=\big\|(\widehat\rho_U^{-iu}\widehat\rho_Y^{\,iu}-\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu})\theta\big\|\le C|\sinh(\pi u)|\,\mathcal R_\eta ,` $`\mathcal R_\eta` of {bpref "D5.12"}[D5.12] for $`d=\dim x`.

:::

:::proof "D5.17" (uses := "D5.1, D5.12")
*D5.17.1* $`f(iu)=\langle W\theta,hW\theta\rangle`, $`W=\rho_P^{[-iu]}\rho_Y^{[iu]}`. $`\theta` pure on $`P\otimes YF`, so (F2): $`\rho_P^{[-iu]}\theta=\widehat\rho_{YF}^{-iu}\theta`. $`\rho_Y^{[iu]}` commutes with $`P`-operators, and $`\widehat\rho_{YF}^{-iu}\theta` lies in $`\supp\rho_{YF}\subseteq\supp\rho_Y\otimes F`, where $`\rho_Y^{[iu]}=\widehat\rho_Y^{\,iu}`. So $`W\theta=w_u`.

*D5.17.2* $`w_u^0` is a unitary on $`UF` applied to $`\theta`; $`h` acts on $`P_0x` and commutes with it: $`\langle w_u^0,hw_u^0\rangle=\langle\theta,h\theta\rangle=p`.

*D5.17.3* _Equality of norms._ Multiply both vectors by the unitary $`\widehat\rho_P^{\,iu}`, then by $`\widehat\rho_U^{-iu}`. (F2): $`\widehat\rho_P^{\,iu}\theta=\widehat\rho_{YF}^{\,iu}\theta`, hence $`\widehat\rho_P^{\,iu}w_u=\widehat\rho_Y^{\,iu}\widehat\rho_{YF}^{-iu}\widehat\rho_{YF}^{\,iu}\theta=\widehat\rho_Y^{\,iu}\theta`, and $`\widehat\rho_P^{\,iu}w_u^0=\widehat\rho_U^{\,iu}\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu}\theta`. After $`\widehat\rho_U^{-iu}`: $`\widehat\rho_U^{-iu}\widehat\rho_Y^{\,iu}\theta` and $`\widehat\rho_{UF}^{-iu}\widehat\rho_{YF}^{\,iu}\theta`. Difference has norm $`\|w_u-w_u^0\|`.

*D5.17.4* Lemma 5.2 with $`xU\to Y` gives the bound.

_Used from._ {bpref "D5.1"}[D5.1] (F2), {bpref "D5.12"}[D5.12] with $`xU=Y`.

:::

:::lemma_ "D5.18" (lean := "AreaLaw.step_5_18")
*D5.18* — Step eq:conditional-first-derivative: Imaginary-axis skew and $`f'(0)`

_Source: 04-conditional.tex 562–574; display `eq:conditional-first-derivative` (570–572)._

$$`|f(iu)-p|\le2\sqrt p\,\|w_u-w_u^0\|+\|w_u-w_u^0\|^2,\qquad f'(0)\in i\mathbb R,\quad|f'(0)|\le C\sqrt p\,\mathcal R_\eta .`

:::

:::proof "D5.18" (uses := "D5.17, D5.12, D5.16")
*D5.18.1* $`h\ge0`: $`\langle w,hw\rangle=\|h^{1/2}w\|^2`. $`\Delta=w_u-w_u^0`: $`\big|\|h^{1/2}w_u\|-\|h^{1/2}w_u^0\|\big|\le\|h^{1/2}\Delta\|\le\|\Delta\|` ($`h\le I`), $`\|h^{1/2}w_u^0\|=\sqrt p`. So $`|\|h^{1/2}w_u\|^2-p|\le2\sqrt p\|\Delta\|+\|\Delta\|^2`.

*D5.18.2* _Derivative._ $`f` entire, $`f(0)=p`: $`f(iu)-p=iuf'(0)+O(u^2)`. By {bpref "D5.17"}[D5.17], RHS of D5.18.1 $`\le2\sqrt pC|\sinh\pi u|\mathcal R_\eta+C^2\sinh^2(\pi u)\mathcal R_\eta^2`. Divide by $`|u|`, $`u\to0`: $`|f'(0)|\le2\pi C\sqrt p\,\mathcal R_\eta`.

*D5.18.3* $`f'(0)\in i\mathbb R`: $`f(iu)` real for real $`u` ({bpref "D5.16"}[D5.16.4]/5), so $`\tfrac d{du}f(iu)=if'(iu)` is real at $`u=0`.

_Used from._ {bpref "D5.17"}[D5.17], {bpref "D5.12"}[D5.12], {bpref "D5.16"}[D5.16.4].

:::

:::lemma_ "D5.19" (lean := "AreaLaw.step_5_19")
*D5.19* — Step: Gaussian-weighted three-lines and second-order remainder

_Source: 04-conditional.tex 576–600._

$`m=\min(1,\mathcal R_\eta)`, $`F(z)=(f(z)-p)e^{z^2}`. Then $`|F|\le Cm` on $`\Re z=0`, $`|F|\le C` on $`\Re z=\pm b`, $`|F|\le Cm^{1/2}` on $`|\Re z|\le b/2`, and for $`0\le t\le b/8` $$`|f(t)-p-tf'(0)|\le C(t/b)^2m^{1/2},\qquad |f(t)|-\Re f(t)\le Ca^2\big(\ell_h^2m^{1/2}+\mathcal R_\eta^2\big)\quad(t=a/2).`

:::

:::proof "D5.19" (uses := "D5.16, D5.17, D5.18")
*D5.19.1* _Imaginary axis._ $`|e^{(iu)^2}|=e^{-u^2}`. If $`\mathcal R_\eta\le1` ($`m=\mathcal R_\eta`): by {bpref "D5.18"}[D5.18.1] and {bpref "D5.17"}[D5.17], $`|F(iu)|\le e^{-u^2}\big(C|\sinh\pi u|+C^2\sinh^2(\pi u)\big)\mathcal R_\eta\le Cm` ($`e^{-u^2}\sinh^2\pi u` bounded). If $`\mathcal R_\eta>1` ($`m=1`): $`|f(iu)-p|\le1\le2` (both in $`[0,1]`), so $`|F|\le2e^{-u^2}\le2`.

*D5.19.2* _Outer lines._ $`|e^{z^2}|=e^{(\Re z)^2-(\Im z)^2}\le e^{b^2}\le e^{1/16}` and $`|f|\le C` ({bpref "D5.16"}[D5.16]): $`|F|\le C` on $`\Re z=\pm b`.

*D5.19.3* _Three-lines on each half-strip $`0\le\Re z\le b`_ (symmetrically on $`-b\le\Re z\le0`): $`|F(z)|\le(Cm)^{1-\Re z/b}C^{\Re z/b}`, for $`\Re z\le b/2` $`\le C'm^{1/2}` ($`m\le1`). If $`m=0`, then $`\eta=0`, $`F\equiv0` on the imaginary axis, so $`F\equiv0` (identity theorem) and $`f\equiv p`.

*D5.19.4* _Cauchy._ $`g=f-p=Fe^{-z^2}`. On $`|z|\le b/2`: $`|g|\le Cm^{1/2}e^{b^2/4}\le C'm^{1/2}` (disc $`|z|\le b/2` lies in $`|\Re z|\le b/2`). Cauchy's estimates on this disc, $`R=b/2`: $`|g^{(k)}(0)|/k!\le C'm^{1/2}R^{-k}`. $`g(0)=0`, $`g'(0)=f'(0)`. For $`t\le b/8`, $`t/R\le\tfrac14`: $$`|g(t)-tg'(0)|\le C'm^{1/2}\sum_{k\ge2}(t/R)^k\le\tfrac43C'm^{1/2}(t/R)^2=C(t/b)^2m^{1/2}.` Write $`f(t)=p+itb_1+\epsilon`, $`f'(0)=ib_1`, $`|\epsilon|\le C(t/b)^2m^{1/2}`. If $`p>0`: $`|p+itb_1|-p=\frac{t^2b_1^2}{|p+itb_1|+p}\le\frac{t^2b_1^2}{2p}\le Ct^2\mathcal R_\eta^2` ({bpref "D5.18"}[D5.18]: $`b_1^2\le C^2p\mathcal R_\eta^2`). If $`p=0`: $`b_1=0` by {bpref "D5.18"}[D5.18]. $`\Re(p+itb_1)=p`. Then $`|f(t)|-\Re f(t)\le(|p+itb_1|-p)+2|\epsilon|\le Ct^2\mathcal R_\eta^2+C(t\ell_h/c_0)^2m^{1/2}`, i.e. with $`t=a/2` the stated bound.

_Formal route_ (RefactoringResult.md §5, D5.19): three lines with bound 0 already gives 0 (`step_5_19`, AreaLawRefactored/S05\_Conditional/SkewAnalytic.lean:198). Reason: no separate case.

_Used from._ {bpref "D5.16"}[D5.16], {bpref "D5.17"}[D5.17], {bpref "D5.18"}[D5.18].

:::

:::lemma_ "D5.20" (lean := "AreaLaw.step_5_20")
*D5.20* — Step: Parameter bookkeeping: $`\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}`

_Source: 04-conditional.tex 601–612._

With $`d=\dim x\le d_h`: for $`0<\eta\le1`, $`\mathcal R_\eta\le C\sqrt{\eta\log(ed_h/\eta)}`; for $`\eta\ge1`, $`\eta\le2\ell_h` and $`\mathcal R_\eta\le C\ell_h`. Consequently $$`\ell_h^2m^{1/2}+\mathcal R_\eta^2\le C\ell_h^4\eta^{1/8}.`

:::

:::proof "D5.20" (uses := "D5.12, D2.2")
*D5.20.1* _$`0<\eta\le1`._ $`y=\eta`. $`\sqrt\eta\le\sqrt{\eta\log(ed_h/\eta)}` ($`\log(ed_h/\eta)\ge1`) and $`d\le d_h`: $`\mathcal R_\eta\le C\sqrt{\eta\log(ed_h/\eta)}`. Now $`\eta\log(ed_h/\eta)=\eta\ell_h+\eta\log(1/\eta)\le\ell_h\eta+C\eta^{1/2}\le C\ell_h\eta^{1/2}`. Hence $`\mathcal R_\eta^2\le C\ell_h\eta^{1/2}\le C\ell_h\eta^{1/8}` and $`m^{1/2}\le\mathcal R_\eta^{1/2}\le C\ell_h^{1/4}\eta^{1/8}`. Sum $`\le C\ell_h^{9/4}\eta^{1/8}\le C\ell_h^4\eta^{1/8}`.

*D5.20.2* _$`\eta\ge1`._ $`\eta=S(x|P)+S(x|U)\le2\log d\le2\ell_h` ({bpref "D2.2"}[D2.2] item 4 twice). $`y=1`: $`\mathcal R_\eta=1+\sqrt{\eta\log(ed)}\le1+\sqrt{2\ell_h\cdot\ell_h}\le C\ell_h`. With $`m\le1`: sum $`\le C\ell_h^2\le C\ell_h^4\eta^{1/8}`.

_Used from._ {bpref "D5.12"}[D5.12] ($`\mathcal R_\eta`), {bpref "D2.2"}[D2.2] item 4 ($`|S(x|\cdot)|\le\log d`).

:::
