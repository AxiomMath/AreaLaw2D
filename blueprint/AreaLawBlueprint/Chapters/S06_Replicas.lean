import Verso
import VersoManual
import VersoBlueprint
import AreaLawBlueprint.TexPrelude
import AreaLawRefactored

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Symmetric replicas and entropy metrics" =>

§6 lifts §5 one-copy estimates to $`k`-copy symmetric states, $`k\to\infty`, fixed finite $`\mathcal V` ($`d=\dim\mathcal V`). Order: Schur–Weyl labels $`\lambda\vdash k`, label observable $`F_{Q,k}=\sum_\lambda(\log d_\lambda)\pi^\lambda_{Q,k}`, merge/split/surprisal/branching estimates ({bpref "D6.1"}[D6.1]–{bpref "D6.4"}[D6.4]) → one label function $`w_k(\lambda)` padded to $`d` for every $`Q`, with $`W_{Q,k}\asymp e^{-tF_{Q,k}}`, $`W_{Q,k}=W_{Q^c,k}` on $`\mathcal S_k`, $`W_{Q,k}=\int(\sigma^t)^{\otimes k}d\zeta_Q`, marked ratios $`R_{Q,k}=W_{Q,k}W_{Q,k-1}^{-1}\approx(J_{Q,k})_+^t` ({bpref "D6.5"}[D6.5]–{bpref "D6.6"}[D6.6]), fixed-factor identity ({bpref "D6.7"}[D6.7]) → leaf metric $`A_k(P,Y,F)=(W_P^{-1}W_F^{-1}W_Y)^2`, $`\log A_k=a(F_P+F_F-F_Y)+O(\log k)`, $`a=2t` ({bpref "D6.8"}[D6.8]–{bpref "D6.9"}[D6.9]) → $`C_{x,k}\ge\poly(k)^{-1}e^{ka[\eta_\theta-Ca^{1/4}\log^C]}P_{\theta,k}` for moving $`x` between parts, Lemma 5.1 inside the integral for $`W` ({bpref "D6.10"}[D6.10]) → symbols: for $`O_k=A_k^{-1/2}\bar hA_k^{1/2}`, polynomials in $`O_k,O_k^\dagger` have symbol $`q(f_\theta,\bar f_\theta)` against $`\mu_\sigma`, hence $`\operatorname{Tr}\sigma\mathcal D_k\le Ca^2\log^C(ed_h)\int\eta_\theta^{1/8}d\mu_\sigma+o_k(1)` via Lemma 5.3 ({bpref "D6.11"}[D6.11]–{bpref "D6.16"}[D6.16]). Gain $`\eta_\theta` ({bpref "D6.10"}[D6.10]), cost $`\eta_\theta^{1/8}` ({bpref "D6.12"}[D6.12]): same symmetric $`\sigma`, uniform in $`\sigma` => §7 averages metric changes with both. §8: label dimension inequalities; §9: floor, $`\mu_\sigma`.

Conventions (tex 29–37). Fixed before $`k\to\infty`: $`\mathcal V`, its tensor factorization, $`t`, all exponents, the finite family of partitions, any cutoff or polynomial approximation. $`\poly(k)` and constants depend on these. $`o_k(1)` uniform over all densities on $`\mathcal S_k` (also $`\sigma` depending on an interpolation parameter). Cutoff and polynomial errors removed only after $`k\to\infty`. Digest-only: $`H(p)=-\sum p_i\log p_i`, $`0\log0=0` (tex 170–172, 393); $`\log` natural (Stirling $`n\log n-n`, tex 170, 393).

# 6.0 Setup and Schur labels

:::definition "D6.1" (lean := "AreaLaw.Replicas.Config, AreaLaw.Replicas.U, AreaLaw.Replicas.S, AreaLaw.Replicas.projS, AreaLaw.Replicas.D")
*D6.1* — Def: Systems, symmetric subspaces, subsystems

_Source: 05-replicas.tex 13–27._

$`\mathcal V` finite-dim complex Hilbert space with specified tensor factorization (auxiliary factors allowed). $`d=\dim\mathcal V`, $`\mathcal S_k=\operatorname{Sym}^k\mathcal V`, $`D_k=\dim\mathcal S_k=\binom{k+d-1}{d-1}`, $`\Pi_k` orthogonal projector onto $`\mathcal S_k`. A subsystem $`Q` is a union of the specified factors; $`Q^c` its complement in $`\mathcal V`; $`d_Q=\dim\mathcal H_Q`; $`\varnothing` has dimension $`1`. Operators on $`Q^{\otimes k}` are extended by the identity. For $`\pi\in S_k`: $`U_Q(\pi)` permutes the $`k` copies of $`Q`; $`U(\pi)=U_{\mathcal V}(\pi)` permutes whole copies. Hence $`U(\pi)=U_Q(\pi)U_{Q^c}(\pi)`.

_Used from._ none.

:::

:::lemma_ "D6.2" (lean := "AreaLaw.Replicas.eq_replicas_schur_decomposition")
*D6.2* — Step eq:schur-decomposition: Schur–Weyl decomposition and Weyl character

_Source: 05-replicas.tex 47–67, `replicas:schur-decomposition` (52–59)._

Partition $`\lambda\vdash k`: non-increasing nonnegative integers with sum $`k` (trailing zeros allowed). $`[\lambda]` = irrep of $`S_k`, $`d_\lambda=\dim[\lambda]`. $$`(\mathbb C^q)^{\otimes k}=\bigoplus_{\lambda\vdash k,\ \ell(\lambda)\le q}[\lambda]\otimes V^{(q)}_\lambda,\qquad \chi^{(q)}_\lambda(x)=\frac{\det[x_i^{\lambda_j+q-j}]}{\det[x_i^{q-j}]}.` $`V^{(q)}_\lambda` = irrep of $`GL_q` with character $`\chi^{(q)}_\lambda`. $`S_k`, $`GL_q` actions mutual centralizers. $`V^{(q)}_\lambda` irreducible under $`U(q)`: a subspace invariant under the differentiated unitary action is invariant under its complex span $`\mathfrak{gl}_q`.

_Used from._ none (cited: Etingof et al. 2011, Thm 5.18.4, Cor 5.19.2, Thm 5.22.1).

:::

:::definition "D6.3" (lean := "AreaLaw.Replicas.π, AreaLaw.Replicas.F") (uses := "D6.2")
*D6.3* — Def eq:F-definition: Label projectors and the label observable $`F_{Q,k}`

_Source: 05-replicas.tex 69–77, `replicas:F-definition` (71–73)._

$`\pi^\lambda_{Q,k}` = projector on $`Q^{\otimes k}` onto the $`[\lambda]\otimes V_\lambda^{(d_Q)}` block. $$`F_{Q,k}=\sum_{\lambda\vdash k}(\log d_\lambda)\,\pi^\lambda_{Q,k}` self-adjoint, $`\ge0` ($`d_\lambda\ge1`). $`F_{Q,0}=0`. Labels on several subsystems/copy groups _compatible_ iff their joint spectral projector (product of the commuting label projectors, {bpref "D6.4"}[D6.4](2),(4)) is nonzero.

_Used from._ {bpref "D6.2"}[D6.2].

:::

:::lemma_ "D6.4" (lean := "AreaLaw.Replicas.lemma_6_1")
*D6.4* — Lemma 6.1: Schur-label estimates

_Source: 05-replicas.tex statement 85–151, proof 153–275; equations `replicas:dimensions` (91–96), `replicas:merge-dimensions` (104–107), `replicas:merge-moment` (112–116), `replicas:group-dimensions` (120–123), `replicas:surprisal-moment` (128–131), `replicas:branch-probability` (136–141), `replicas:star-definition` (144–146)._

For the systems of {bpref "D6.1"}[D6.1]:

(1) $`\lambda\vdash k`, $`\ell(\lambda)\le q`, $`l_i=\lambda_i+q-i` ($`1\le i\le q`): $$`\dim V^{(q)}_\lambda=\prod_{i<j}\frac{l_i-l_j}{j-i},\quad d_\lambda=\frac{k!\prod_{i<j}(l_i-l_j)}{\prod_il_i!},\quad\log d_\lambda=kH(\lambda/k)+O_q(\log(k+2)).` The number of labels and $`\sum_\lambda\dim V^{(q)}_\lambda` are $`\le\poly(k)` ($`q` fixed).

(2) Central label functions of $`S_k` commute for nested or disjoint subsystems. On $`\mathcal S_k`: $`\pi^\lambda_{Q,k}=\pi^\lambda_{Q^c,k}`.

(3) $`Q,E` disjoint, labels $`\lambda,\mu` compatible with label $`\nu` on $`QE`: $`d_\nu\le d_\lambda d_\mu` and $`d_\lambda\le d_\nu d_\mu`. For a tensor product of permutation-invariant densities on $`Q^{\otimes k}`, $`E^{\otimes k}`: $`\Pr(\nu\mid\lambda,\mu)\le\poly(k)\,d_\nu/(d_\lambda d_\mu)`. Hence for $`0\le b\le1`, uniformly in the densities, $$`\mathbb E\Bigl(\frac{d_\lambda d_\mu}{d_\nu}\Bigr)^b\le\poly(k).`

(4) Copies split into groups of sizes $`k-r` and $`r`; labels $`\alpha,\beta` (on a fixed subsystem, on the two groups) compatible with the full label $`\lambda`: $$`d_\alpha d_\beta\le d_\lambda\le\binom kr d_\alpha d_\beta.` The subgroup label projectors commute with the full label projector.

(5) $`\rho` permutation-invariant density on $`Q^{\otimes k}`, $`L_\rho=-\log\rho` on $`\operatorname{supp}\rho`: $`[F_Q,\rho]=0`, $`0\le F_Q\le L_\rho` on the support, and $$`\operatorname{Tr}\rho\,e^{b(L_\rho-F_Q)}\le\poly(k)\qquad(0\le b\le1).`

(6) Full $`Q`-label $`\lambda` and first-$`(k-1)`-copies label $`\nu` are compatible iff $`\nu=\lambda-e_i` is a partition. In any permutation-invariant $`Q` state, conditional on $`\lambda`, $$`p_{\lambda,i}=\frac{d_{\lambda-e_i}}{d_\lambda}=\frac{l_i}{k}\frac{\prod_{a<b}(l_a-\delta_{ai}-l_b+\delta_{bi})}{\prod_{a<b}(l_a-l_b)}\le2^q\frac{l_i}{k}.` The star operator $`J_{Q,k}=\frac1k\sum_{j<k}U_Q((j\ k))` has eigenvalue $`(\lambda_i-i)/k` on branch $`i`.

Polynomial bounds depend on the fixed subsystem dimensions only.

:::

:::proof "D6.4" (uses := "D6.1, D6.2, D6.3")
*D6.4.1* _Weyl dimension._ $`\dim V_\lambda^{(q)}=\chi^{(q)}_\lambda(1,\dots,1)`, limit of the alternant ratio $`\det[x_i^{l_j}]/\det[x_i^{q-j}]`; gives $`\prod_{i<j}(l_i-l_j)/(j-i)`.

*D6.4.2* _Coefficient extraction._ Multiply $`(x_1+\dots+x_q)^k=\sum_\lambda d_\lambda\chi^{(q)}_\lambda` by $`\det[x_i^{q-j}]`. RHS: $`\sum_\lambda d_\lambda\det[x_i^{l_j(\lambda)}]`. Coefficient of $`x^{l}=x_1^{l_1}\cdots x_q^{l_q}` with $`l_1>\dots>l_q`: only the identity term of the alternant of $`\lambda` contributes, so the coefficient is $`d_\lambda`.

*D6.4.3* _Other side._ Coefficient of $`x^l` in $`(\sum x_i)^k\sum_\sigma\operatorname{sgn}\sigma\prod x_i^{q-\sigma(i)}` is $`\sum_\sigma\operatorname{sgn}\sigma\,k!/\prod_i(l_i-q+\sigma(i))!=k!\det[1/(l_i-q+j)!]` (reciprocal of a negative factorial $`=0`).

*D6.4.4* _Vandermonde._ $`1/(l_i-q+j)!=(l_i)_{q-j}/l_i!` ($`(u)_m` falling factorial). Columns of $`[(l_i)_{q-j}]` are monic polynomials in $`l_i` of degree $`q-j` $`\Rightarrow` $`\det=\prod_{i<j}(l_i-l_j)`. Hence $`d_\lambda=k!\prod_{i<j}(l_i-l_j)/\prod_il_i!`.

*D6.4.5* _Entropy._ $`\log n!=n\log n-n+O(\log(n+2))`. $`l_i=\lambda_i+O_q(1)` $`\Rightarrow` $`l_i\log l_i-\lambda_i\log\lambda_i=O_q(\log(k+2))`. $`\sum\lambda_i=k` $`\Rightarrow` $`k\log k-\sum\lambda_i\log\lambda_i=kH(\lambda/k)`. Linear terms: $`-k+\sum_il_i=\binom q2` ($`\sum l_i=k+\binom q2`). The $`l_i-l_j` are distinct-integer differences in $`[1,k+q]`, so $`0\le\log\prod(l_i-l_j)\le q^2\log(k+q)`.

*D6.4.6* _Counting._ $`\le(k+1)^q` labels. $`\dim V_\lambda^{(q)}\le(k+q)^{q(q-1)/2}` since $`1\le j-i`, $`0<l_i-l_j\le k+q`.

*D6.4.7* _Central projector._ $`\pi^\lambda_{Q,k}=\frac{d_\lambda}{k!}\sum_\pi\chi_\lambda(\pi^{-1})U_Q(\pi)` (character orthogonality, or Schur on the central sum).

*D6.4.8* _Nested/disjoint commutation._ $`Q\subseteq Q'`: $`U_{Q'}(\sigma)U_Q(\pi)U_{Q'}(\sigma)^\dagger=U_Q(\sigma\pi\sigma^{-1})`, so a central combination of $`U_Q` commutes with all $`U_{Q'}(\sigma)`, hence with every $`\pi^\mu_{Q'}`. Disjoint: operators on different tensor factors commute.

*D6.4.9* _Complement._ $`z\in\mathcal S_k`: $`U(\pi)z=z\Rightarrow U_Q(\pi)z=U_{Q^c}(\pi^{-1})z`. Then $`\pi^\lambda_Qz=\frac{d_\lambda}{k!}\sum_\pi\chi_\lambda(\pi^{-1})U_{Q^c}(\pi^{-1})z=\frac{d_\lambda}{k!}\sum_{\pi'}\chi_\lambda(\pi')U_{Q^c}(\pi')z=\pi^\lambda_{Q^c}z`, using $`\chi_\lambda(\pi')=\chi_\lambda(\pi'^{-1})` ($`\pi` conjugate to $`\pi^{-1}`). Same fact: all Specht modules self-dual.

*D6.4.10* _Merge, dimensions._ On a block with $`(\lambda,\mu)`, $`S_k` acts diagonally on $`[\lambda]\otimes[\mu]`; compatibility with $`\nu` means $`[\nu]\subseteq[\lambda]\otimes[\mu]` $`\Rightarrow` $`d_\nu\le d_\lambda d_\mu`. $`\operatorname{Hom}_{S_k}([\nu],[\lambda]\otimes[\mu])\simeq\operatorname{Hom}_{S_k}([\lambda],[\nu]\otimes[\mu]^*)` and $`[\mu]^*\simeq[\mu]` $`\Rightarrow` $`d_\lambda\le d_\nu d_\mu`.

*D6.4.11* _Merge, probability._ Conditional on $`(\lambda,\mu)` a product of invariant states is $`I/(d_\lambda d_\mu)` on the Specht factors $`[\lambda]\otimes[\mu]`. With $`g_{\lambda\mu\nu}` the multiplicity of $`[\nu]` in $`[\lambda]\otimes[\mu]`: $`\Pr(\nu\mid\lambda,\mu)=g_{\lambda\mu\nu}d_\nu/(d_\lambda d_\mu)` exactly.

*D6.4.12* _Multiplicity bound._ In $`(Q\otimes E)^{\otimes k}` the $`[\nu]`-isotypic block has multiplicity space of dimension $`\dim V^{(d_Qd_E)}_\nu`, containing $`g_{\lambda\mu\nu}` copies of $`V_\lambda^{(d_Q)}\otimes V_\mu^{(d_E)}`. So $`g_{\lambda\mu\nu}\dim V_\lambda\dim V_\mu\le\dim V_\nu^{(d_Qd_E)}` $`\Rightarrow` $`g\le\poly(k)`.

*D6.4.13* _Merge moment._ $`R=d_\lambda d_\mu/d_\nu\ge1` (D6.4.10), $`\Pr(\nu\mid\lambda,\mu)=g_{\lambda\mu\nu}/R`. $`\mathbb E[R^b\mid\lambda,\mu]=\sum_\nu g_{\lambda\mu\nu}R^{b-1}\le\sum_\nu g_{\lambda\mu\nu}\le\poly(k)` (at most $`(k+1)^{d_Qd_E}` labels $`\nu`, each $`g\le\poly`).

*D6.4.14* _Copy groups._ $`[\alpha]\otimes[\beta]\subseteq\operatorname{Res}^{S_k}_{S_{k-r}\times S_r}[\lambda]` $`\Rightarrow` $`d_\alpha d_\beta\le d_\lambda`. Fix a copy $`W\simeq[\alpha]\otimes[\beta]` in $`[\lambda]`. Translates $`gW` span $`[\lambda]` (irreducible); $`gW` depends only on the coset $`g(S_{k-r}\times S_r)`; $`\binom kr` cosets $`\Rightarrow` $`d_\lambda\le\binom kr d_\alpha d_\beta`. Central elements of $`S_k` commute with the subgroup algebra $`\Rightarrow` commutation.

*D6.4.15* _Surprisal._ Invariant $`\rho` commutes with $`S_k` $`\Rightarrow` $`\rho=\bigoplus_\lambda I_{[\lambda]}\otimes M_\lambda` ({bpref "D6.2"}[D6.2]). Each positive eigenvalue $`u` of $`M_\lambda` occurs $`d_\lambda` times in $`\rho`, trace $`\le1` $`\Rightarrow` $`ud_\lambda\le1` $`\Rightarrow` $`-\log u\ge\log d_\lambda`: $`F_Q\le L_\rho`; $`[F_Q,\rho]=0` since $`\pi^\lambda` are block projectors. $`F_Q\ge0` from $`d_\lambda\ge1`.

*D6.4.16* _Moment._ Block $`\lambda`, eigenvalue $`u` contributes $`d_\lambda\cdot u\cdot(ud_\lambda)^{-b}=(ud_\lambda)^{1-b}\le1` ($`1-b\ge0`). So $`\operatorname{Tr}\rho e^{b(L_\rho-F_Q)}=\sum_\lambda\sum_{u>0}(ud_\lambda)^{1-b}\le\sum_\lambda\dim V_\lambda^{(d_Q)}\le\poly(k)`.

*D6.4.17* _Branching._ Multiply a Weyl numerator alternant by $`\sum x_i`: sum of alternants with one exponent raised by $`1`; equal exponents vanish; the survivors are legal added boxes. So $`V^{(q)}_\nu\otimes\mathbb C^q=\bigoplus_{\lambda=\nu+e_i}V^{(q)}_\lambda`, multiplicity one. Comparing the Schur–Weyl decompositions of the first $`k-1` copies and the last copy: the $`\nu`-branch in the $`\lambda` block has rank $`d_\nu` on $`[\lambda]` and acts as identity on $`V_\lambda^{(q)}`.

*D6.4.18* _Branch probability._ Invariant state is uniform on $`[\lambda]` $`\Rightarrow` $`p_{\lambda,i}=d_{\lambda-e_i}/d_\lambda`. Insert the formula of (1) for $`(k,l)` and $`(k-1,l-e_i)`: $`(k-1)!/k!=1/k`, $`l_i!/(l_i-1)!=l_i`, Vandermonde ratio as displayed.

*D6.4.19* _Bound._ In the ratio, a pair $`(a,i)`, $`a<i`: $`(l_a-l_i+1)/(l_a-l_i)\le2` ($`l_a-l_i\ge1`); at most $`q-1` such pairs. A pair $`(i,b)`, $`b>i`: $`(l_i-1-l_b)/(l_i-l_b)\le1` and $`\ge0` on a legal branch. Hence $`p_{\lambda,i}\le2^{q-1}l_i/k\le2^ql_i/k`.

*D6.4.20* _Star, quadratic identity._ $`E^{\rm tot}_{ab}=\sum_jE_{ab}^{(j)}`. $`\sum_{a,b}E^{\rm tot}_{ab}E^{\rm tot}_{ba}=kqI+2\sum_{j<j'}U_Q((j\,j'))`: terms $`j=j'` give $`\sum_{ab}E_{ab}E_{ba}=qI` per copy; ordered pairs $`j\neq j'` give $`\sum_{ab}E^{(j)}_{ab}E^{(j')}_{ba}=U_Q((j\,j'))`.

*D6.4.21* _Star, scalar on block $`\lambda`._ The left side is scalar on a Schur block. Evaluate on a highest-weight vector $`v` (lexicographically leading weight $`\lambda`); $`E^{\rm tot}_{ab}v=0` for $`a<b` (would raise the weight). $`a=b`: $`\sum_i\lambda_i^2`. $`a<b`: $`E_{ab}E_{ba}v=[E_{ab},E_{ba}]v=(\lambda_a-\lambda_b)v` (using $`[E_{ab}^{\rm tot},E_{ba}^{\rm tot}]=E_{aa}^{\rm tot}-E_{bb}^{\rm tot}`); the transposed term $`E_{ba}E_{ab}v=0`. $`\sum_{a<b}(\lambda_a-\lambda_b)=\sum_i\lambda_i(q+1-2i)`. Scalar $`c_\lambda=\sum_i\lambda_i(\lambda_i+q+1-2i)`.

*D6.4.22* _Star, difference._ $`\sum_{j<j'\le k}U((j\,j'))-\sum_{j<j'\le k-1}U((j\,j'))=\sum_{j<k}U((j\,k))=kJ_{Q,k}`. On branch $`\lambda\to\lambda-e_i`: $`kJ=\frac12[(c_\lambda-kq)-(c_{\lambda-e_i}-(k-1)q)]=\frac12[c_\lambda-c_{\lambda-e_i}-q]`. Only the $`i`-th summand changes: $`c_\lambda-c_{\lambda-e_i}=2\lambda_i+q-2i`. So $`kJ=\lambda_i-i`.

_Formal route_ (RefactoringResult.md §5, D6.4.15): for a `u`-eigenvector `w` in block `λ`, the images `e^λ_{j i₀} e^λ_{i₀ i₀} w` of the Wedderburn matrix units are `d_λ` linearly independent `u`-eigenvectors, so `d_λ u ≤ Tr ρ` (`dim_mul_le_trace`, AreaLawRefactored/S06\_Replicas/Surprisal.lean:138). Reason: the Wedderburn matrix units are not adjoint-compatible; linear independence suffices.

_Formal route_ (RefactoringResult.md §5, D6.4.16): `∑_λ Tr π^λ / d_λ` (= `∑_λ dim V_λ` by Schur–Weyl) `≤ dim` of the commutant of the `S_k` action `≤ (k+1)^{q²}` (orbits of `S_k` on pairs of configurations), `finrank_commutant_le`, `sum_trace_π_div_le` (Surprisal.lean:402, :512). Reason: needs neither the partition labels nor D6.4 (1).

_Formal route_ (RefactoringResult.md §5, D6.4 (1), (3), {bpref "D6.6"}[D6.6.2], {bpref "D6.6"}[D6.6.8]): the old routes, ported unchanged (Pieri recursions for the dimension formulas; general copy-invariant ρ in (3); orthant law instead of the simplex measure; `TraceCompression` instead of min–max). Reason: port first, golf later (RefactoringResult Next steps).

_Used from._ {bpref "D6.1"}[D6.1], {bpref "D6.2"}[D6.2], {bpref "D6.3"}[D6.3].

:::

# 6.1 A common metric on every subsystem

:::definition "D6.5" (lean := "AreaLaw.Replicas.w, AreaLaw.Replicas.W") (uses := "D6.3")
*D6.5* — Def eq:w-definition: The label function $`w_k` and $`W_{Q,k}`

_Source: 05-replicas.tex 279–303, `replicas:w-definition` (290–299)._

Fix $`0<t<1/4`, $`a=2t`. Labels padded to length $`d=\dim\mathcal V` for every $`Q`. $`c=d+(1+t)\binom d2`: $$`w_k(\lambda)=\frac{\Gamma(c)}{\Gamma(c+tk)}\prod_{i=1}^d\frac{\Gamma(1+t(\lambda_i+d-i))}{\Gamma(1+t(d-i))},\qquad W_{Q,k}=\sum_\lambda w_k(\lambda)\pi^\lambda_{Q,k}.` $`W_{Q,0}=I`. For $`\dim Q=1` and $`k>0`: $`W_{Q,k}=w_k((k))\,I`, positive but $`\ne1`.

_Used from._ {bpref "D6.3"}[D6.3].

:::

:::lemma_ "D6.6" (lean := "AreaLaw.Replicas.lemma_6_2")
*D6.6* — Lemma 6.2: Integral formula and marked ratios

_Source: 05-replicas.tex statement 305–335, proof 337–434; equations `replicas:W-comparison` (308–311), `replicas:W-integral` (315–318), `replicas:R-forward` (323–325), `replicas:R-inverse` (329–334), `replicas:ratio-eigenvalue` (402–406)._

$`W_{Q,k}` is positive definite and central. Uniformly in labels, $$`\poly(k)^{-1}e^{-tF_{Q,k}}\le W_{Q,k}\le\poly(k)\,e^{-tF_{Q,k}}.` On $`\mathcal S_k`: $`W_{Q,k}=W_{Q^c,k}`. For each $`Q` there is a probability measure $`\zeta_Q` on positive definite subdensities $`\sigma` on $`Q` ($`\operatorname{Tr}\sigma\le1`), independent of $`k`, with $$`W_{Q,k}=\int(\sigma^t)^{\otimes k}\,d\zeta_Q(\sigma)\qquad(k\ge0).` With $`W_{Q,k-1}` extended by $`I` on the last copy and $`R_{Q,k}=W_{Q,k}W_{Q,k-1}^{-1}`: $$`\|R_{Q,k}-(J_{Q,k})_+^t\|\to0\quad\text{on the whole tensor space.}` There is $`C_{\mathcal V,t}` with $`\|R^{-1}_{Q,k}z\|\le C_{\mathcal V,t}` for every unit $`z\in\mathcal S_k`, and for $`0<\delta<1` $$`\limsup_{k\to\infty}\sup_{z\in\mathcal S_k,\|z\|=1}\|(R_{Q,k}^{-1}-\max(J_{Q,k},\delta)^{-t})z\|\le C_{\mathcal V,t}\,\delta^{(1-2t)/2}.`

:::

:::proof "D6.6" (uses := "D6.2, D6.3, D6.4, D6.5")
*D6.6.1* _Positivity._ $`w_k(\lambda)>0` (Gamma at positive arguments) => $`W` positive definite; central as a combination of label projectors.

*D6.6.2* _Simplex measure ($`Q=\mathcal V`, $`d\ge2`)._ $`s` on $`\{s_i\ge0,\sum s_i=1\}`, density $`\propto\Delta(s)\Delta(s^t)`, $`\Delta(s)=\prod_{i<j}(s_i-s_j)`: nonnegative, integrable, positive off collisions (Laguerre Muttalib–Borodin weight on the simplex; Forrester–Ipsen 2018, §2.3 eq. (26)). $`d=1`: point mass $`s_1=1`. $`\sigma=U\operatorname{diag}(s)U^\dagger`, $`U` Haar independent of $`s`.

*D6.6.3* _Centrality._ $`\int(\sigma^t)^{\otimes k}` commutes with permutations and with $`U^{\otimes k}` ($`U` Haar-averaged) => scalar on each irreducible $`[\lambda]\otimes V_\lambda`. Scalar $`=\operatorname{Tr}(\text{block})/(d_\lambda\dim V_\lambda)=\mathbb E[\chi_\lambda^{(d)}(s^t)]/\dim V^{(d)}_\lambda`.

*D6.6.4* _Cancellation._ $`l_i=\lambda_i+d-i`. $`\chi_\lambda(s^t)=\det[s_i^{tl_j}]/\Delta(s^t)`: the Weyl denominator cancels $`\Delta(s^t)` in the density. Remaining: $`\int\det[s_i^{d-j}]\det[s_i^{tl_j}]ds`.

*D6.6.5* _Gamma integral._ $`\int_{\sum s_i=1}\prod s_i^{u_i}ds=\prod\Gamma(1+u_i)/\Gamma(d+\sum u_i)` ($`u_i>-1`). Proof: change $`x_i=rs_i` in the product of the defining gamma integrals; Jacobian $`r^{d-1}`. Expanding both determinants: exponents $`u_i=d-\sigma(i)+tl_{\tau(i)}`, $`\sum u_i=\binom d2+t(k+\binom d2)`, so $`d+\sum u_i=c+tk`. All $`d!` relabelings give the same term: $$`\int=\frac{d!}{\Gamma(c+tk)}\det[\Gamma(1+tl_i+d-j)]_{i,j=1}^d.`

*D6.6.6* _Determinant._ Factor $`\Gamma(1+tl_i)` from row $`i`: entries $`(1+tl_i)_{d-j}` (rising factorial), monic of degree $`d-j` in $`tl_i` $`\Rightarrow` $`\det=\Delta(tl)=t^{\binom d2}\Delta(l)`. Dividing by $`\dim V_\lambda=\Delta(l)/\prod(j-i)` cancels $`\Delta(l)`. Left: $`\lambda`-, $`k`-independent constant $`\times\prod_i\Gamma(1+tl_i)/\Gamma(c+tk)`. Normalizing at $`\lambda=\varnothing`, $`k=0` (eigenvalue $`1`): $`w_k(\lambda)` of {bpref "D6.5"}[D6.5]. Measure $`k`-independent.

*D6.6.7* _Subsystem $`d_Q\le d`._ Isometry $`E:\mathcal H_Q\to\mathbb C^d`. $`(E^\dagger)^{\otimes k}U_{\mathbb C^d}(\pi)E^{\otimes k}=U_Q(\pi)`. $`W_{\mathbb C^d,k}=\frac1{k!}\sum_\pi f_k(\pi)U(\pi)`, $`f_k(\pi)=\sum_\lambda w_k(\lambda)d_\lambda\chi_\lambda(\pi^{-1})` ({bpref "D6.4"}[D6.4.7]), depends on $`(k,d)` only; compression gives $`\frac1{k!}\sum_\pi f_k(\pi)U_Q(\pi)=\sum_\lambda w_k(\lambda)\pi_{Q,k}^\lambda=W_{Q,k}` (labels with $`\ell>d_Q` vanish). So $`W_{Q,k}=\int(E^\dagger\sigma^tE)^{\otimes k}d\zeta(\sigma)`.

*D6.6.8* _Back to subdensities._ $`B=E^\dagger\sigma^tE>0` a.s. ($`s_i>0` in the interior). $`\tau=B^{1/t}`. Min–max: eigenvalues of $`B` $`\le` those of $`\sigma^t` $`\Rightarrow` eigenvalues of $`\tau\le s_i` $`\Rightarrow\operatorname{Tr}\tau\le1`. $`B^{\otimes k}=(\tau^t)^{\otimes k}`; $`\zeta_Q` = law of $`\tau`.

*D6.6.9* _Complement._ {bpref "D6.4"}[D6.4](2): same $`w_k`, equal projectors on $`\mathcal S_k`.

*D6.6.10* _Comparison._ $`\log\Gamma(1+u)=u\log u-u+O(\log(u+2))` on the fixed number of factors: $`\log w_k(\lambda)=-tkH(\lambda/k)+O_{d,t}(\log(k+2))` ($`\Gamma(c+tk)`: $`-(tk\log(tk)-tk)`; $`i`-sum: $`t\sum\lambda_i\log\lambda_i+tk\log t-tk`; $`\log t` terms cancel). {bpref "D6.4"}[D6.4](1): $`kH(\lambda/k)=\log d_\lambda+O(\log(k+2))`. So $`w_k(\lambda)=d_\lambda^{-t}\poly(k)^{\pm1}`; spectral calculus gives `replicas:W-comparison`.

*D6.6.11* _Ratio, block structure._ $`W_{Q,k-1}\otimes I=\sum_\nu w_{k-1}(\nu)\pi^\nu_{Q,k-1}` commutes with $`W_{Q,k}` ({bpref "D6.4"}[D6.4](4)). Joint blocks $`(\lambda,\nu=\lambda-e_i)`: $`R_{Q,k}=w_k(\lambda)/w_{k-1}(\lambda-e_i)` there.

*D6.6.12* _Eigenvalue._ $`l_i=\lambda_i+d-i` (full $`d`). Only the $`i`-th Gamma and the $`\Gamma(c+tk)` change: $`r_{\lambda,i}=\dfrac{\Gamma(c+t(k-1))}{\Gamma(c+tk)}\dfrac{\Gamma(1+tl_i)}{\Gamma(1+t(l_i-1))}`.

*D6.6.13* _Two-sided and limit._ Gamma ratios: $`r_{\lambda,i}\asymp_{d,t}((l_i+1)/k)^t`. If $`l_i/k\ge\varepsilon`: $`r_{\lambda,i}\to(l_i/k)^t` uniformly (relative error $`O(1/(\varepsilon k))`), and $`(l_i/k)^t-(\max(l_i-d,0)/k)^t\le(d/k)^t`. If $`l_i/k<\varepsilon`: $`r_{\lambda,i}\le C(\varepsilon+1/k)^t` and $`\max((l_i-d)/k,0)^t\le\varepsilon^t`. Let $`k\to\infty`, then $`\varepsilon\downarrow0`. Since $`J_{Q,k}=(\lambda_i-i)/k=(l_i-d)/k` on branch $`i` ({bpref "D6.4"}[D6.4](6)), this is `replicas:R-forward`. Also $`\sup\|R_{Q,k}\|<\infty`.

*D6.6.14* _Inverse vector bound._ $`z\in\mathcal S_k` unit; its $`Q`-marginal is permutation-invariant. {bpref "D6.4"}[D6.4](6) with $`q=d_Q`: $`p_{\lambda,i}\le2^{d_Q}(\lambda_i+d_Q-i)/k\le C_dl_i/k` ($`\lambda_i+d_Q-i\le l_i`). Conditional on $`\lambda`: $`\sum_ip_{\lambda,i}r_{\lambda,i}^{-2}\le C_{d,t}\sum_i(l_i/k)^{1-2t}\le C_{d,t}` ($`1-2t>0`, $`l_i\le k+d`). Average over $`\lambda`: $`\|R_{Q,k}^{-1}z\|^2\le C_{d,t}`.

*D6.6.15* _Clipped inverse._ $`R^{-1}`, $`\max(J,\delta)^{-t}` diagonal in the joint blocks. On $`J\ge\delta`: $`l_i/k\ge\delta`, so $`r_{\lambda,i}^{-1}-((l_i-d)/k)^{-t}\to0` uniformly (D6.6.13; inverse map uniformly Lipschitz on $`[\delta^t/2,\infty)`): operator-norm error $`\to0`. On $`J<\delta`: $`l_i/k\le\delta+d/k`. True inverse: restricted squared norm $`\le C_{d,t}(\delta+d/k)^{1-2t}` (D6.6.14 restricted). Clipped inverse $`=\delta^{-t}` there: squared norm $`\le C_d(\delta+d/k)\delta^{-2t}`. Limsup in $`k` (both $`\le C\delta^{1-2t}`), square root, triangle inequality: error $`\le C_{\mathcal V,t}\delta^{(1-2t)/2}`.

*D6.6.16* _Uniformity._ All bounds conditional on $`\lambda` for arbitrary symmetric $`z`.

_Formal route_ (RefactoringResult.md §5, {bpref "D6.4"}[D6.4] (1), (3), D6.6.2, D6.6.8): the old routes, ported unchanged (Pieri recursions for the dimension formulas; general copy-invariant ρ in (3); orthant law instead of the simplex measure; `TraceCompression` instead of min–max). Reason: port first, golf later (RefactoringResult Next steps).

_Formal route_ (RefactoringResult.md §5, D6.6 (`W-integral`)): the law of a random positive-definite subdensity on a probability space (`lemma_6_2_4`, Metric.lean:124). Reason: avoids a measurable structure on matrix space; same content.

_Used from._ {bpref "D6.2"}[D6.2] (irreducibility under $`U(d)`); {bpref "D6.3"}[D6.3]; {bpref "D6.4"}[D6.4] (1),(2),(4),(6); {bpref "D6.5"}[D6.5].

:::

:::lemma_ "D6.7" (lean := "AreaLaw.Replicas.eq_replicas_fixed_factor")
*D6.7* — Step eq:fixed-factor: Fixed pure factor restriction identity

_Source: 05-replicas.tex 436–449, `replicas:fixed-factor` (439–442)._

$`B,Q` disjoint, $`\phi` a fixed vector on $`B`, $`z` on $`Q`-copies (and other factors): $$`W_{BQ,k}(\phi^{\otimes k}\otimes z)=\phi^{\otimes k}\otimes W_{Q,k}z.` Same identity for $`F` and for every real power of $`W` (including $`W^{-1}`).

:::

:::proof "D6.7" (uses := "D6.4, D6.5, D6.6")
*D6.7.1* $`W_{BQ,k}=\frac1{k!}\sum_\pi f_k(\pi)U_{BQ}(\pi)`, same $`f_k(\pi)=\sum_\lambda w_k(\lambda)d_\lambda\chi_\lambda(\pi^{-1})` as for $`W_{Q,k}` ({bpref "D6.4"}[D6.4.7], {bpref "D6.6"}[D6.6.7]).

*D6.7.2* $`U_{BQ}(\pi)(\phi^{\otimes k}\otimes z)=\phi^{\otimes k}\otimes U_Q(\pi)z`: permuting the $`B` copies fixes $`\phi^{\otimes k}`.

*D6.7.3* Same coefficients both sides. $`F`, $`W^s` are central functions $`\sum g(\lambda)\pi^\lambda` too.

*D6.7.4* $`\phi` may be a Bell vector between two factors inside $`B`: only the whole $`B` factor is permuted.

_Formal route_ (RefactoringResult.md §5, D6.7): the identity for every element of `ℂ[S_k]` (`groupAlgebraRep_fixFactor`, AreaLawRefactored/S06\_Replicas/Labels.lean:105), hence for every central label function; disjointness of `B, Q` is not needed once `z` does not depend on the `B` factors. Reason: same steps D6.7.1–3, stated before `W` exists.

_Used from._ {bpref "D6.4"}[D6.4.7]; {bpref "D6.5"}[D6.5]; {bpref "D6.6"}[D6.6.7].

:::

:::definition "D6.8" (lean := "AreaLaw.Replicas.A, AreaLaw.Replicas.eq_replicas_leaf_metric") (uses := "D6.4, D6.6")
*D6.8* — Def eq:leaf-metric: The partition metric $`A_k(P,Y,F)`

_Source: 05-replicas.tex 451–458, `replicas:leaf-metric` (456–458)._

Partition $`P,Y,F` of $`\mathcal V` ($`P,F` outer, $`Y` middle; no geometric condition), on $`\mathcal S_k`: $$`A_k(P,Y,F)=\bigl(W_{P,k}^{-1}W_{F,k}^{-1}W_{Y,k}\bigr)^2.` Factors commute (disjoint, {bpref "D6.4"}[D6.4](2)). $`A_k` symmetric under $`P\leftrightarrow F`.

_Used from._ {bpref "D6.4"}[D6.4](2), {bpref "D6.6"}[D6.6].

:::

:::lemma_ "D6.9" (lean := "AreaLaw.Replicas.eq_replicas_leaf_floor")
*D6.9* — Step eq:leaf-floor: Floor of the leaf metric and commutation with copy averages

_Source: 05-replicas.tex 459–468, `replicas:leaf-floor` (460–463)._

In operator norm, $$`\log A_k=a(F_P+F_F-F_Y)+O_{\mathcal V,t}(\log(k+2)),\qquad A_k\ge\poly(k)^{-1}I.` One-copy $`h` inside one part => $`\bar h=k^{-1}\sum_jh^{(j)}` commutes with $`A_k`.

:::

:::proof "D6.9" (uses := "D6.3, D6.4, D6.6, D6.8")
*D6.9.1* $`W_P^{-1}\asymp e^{tF_P}`, $`W_F^{-1}\asymp e^{tF_F}`, $`W_Y\asymp e^{-tF_Y}` up to $`\poly(k)^{\pm1}` ({bpref "D6.6"}[D6.6]), commuting; square: $`A_k\asymp e^{2t(F_P+F_F-F_Y)}` up to $`\poly(k)^{\pm1}`, $`a=2t`.

*D6.9.2* $`F_Y=F_{PF}` on $`\mathcal S_k` ($`Y=(PF)^c`, {bpref "D6.4"}[D6.4](2)). Compatible $`\nu` of $`PF`, $`\lambda,\mu` of $`P,F`: $`d_\nu\le d_\lambda d_\mu` ({bpref "D6.4"}[D6.4](3)), i.e. $`F_{PF}\le F_P+F_F`. Hence $`F_P+F_F-F_Y\ge0`, $`A_k\ge\poly(k)^{-1}I`.

*D6.9.3* $`h` in part $`R`: $`\bar h` commutes with $`U_R(\pi)` (symmetric sum), hence with $`W_R`; disjoint from the other two $`W`.

_Used from._ {bpref "D6.3"}[D6.3]; {bpref "D6.4"}[D6.4](2),(3); {bpref "D6.6"}[D6.6] (`W-comparison`); {bpref "D6.8"}[D6.8].

:::

# 6.2 An operator lower bound for moving a subsystem

:::lemma_ "D6.10" (lean := "AreaLaw.Replicas.lemma_6_3")
*D6.10* — Lemma 6.3: Relative coherent pin

_Source: 05-replicas.tex statement 480–505, proof 507–587; equations `replicas:relative-pin` (496–501), `replicas:move-inverse` (518–525), `replicas:compensator` (540–542), `replicas:move-one-copy` (566–570)._

$`P,x,Y_0,F` partition $`\mathcal V`, $`Y=xY_0`, $`0<t<1/4`, $`a=2t`, $$`A_k=A_k(P,xY_0,F),\quad B_k=A_k(Px,Y_0,F),\quad C_{x,k}=A_k^{-1/2}B_kA_k^{-1/2}.` Assume $`a\log(e\dim x)\le c` ($`c` of Lemma 5.1). Unit $`\theta\in\mathcal V`: $`\eta_\theta=S_\theta(x|P)+S_\theta(x|Y_0)=I_\theta(x:F|P)=I_\theta(x:F|Y_0)\ge0`. Polynomial bound uniform in $`\theta`; on $`\mathcal S_k`, $`P_{\theta,k}=|\theta^{\otimes k}\rangle\langle\theta^{\otimes k}|`: $$`C_{x,k}\ge\poly(k)^{-1}\exp\Bigl\{ka\bigl[\eta_\theta-Ca^{1/4}\log^C(e\dim x)\bigr]\Bigr\}P_{\theta,k}.` Same for a move to $`F` with the outer parts exchanged. No move ($`x=\varnothing`): $`C_{x,k}=I`, gain $`0`.

:::

:::proof "D6.10" (uses := "D6.1, D6.4, D6.6, D6.8, D5.1, D5.5")
*D6.10.1* _Cauchy–Schwarz._ $`C>0`, unit $`z`: $`|\langle z,u\rangle|^2\le\langle z,C^{-1}z\rangle\langle u,Cu\rangle`, i.e. $`C\ge\langle z,C^{-1}z\rangle^{-1}|z\rangle\langle z|`. $`z=\theta^{\otimes k}`: suffices to bound $`\langle\theta^{\otimes k},C_{x,k}^{-1}\theta^{\otimes k}\rangle` above.

*D6.10.2* _Norm identity._ $`C^{-1}_{x,k}=A_k^{1/2}B_k^{-1}A_k^{1/2}` => $`\langle\theta^{\otimes k},C_{x,k}^{-1}\theta^{\otimes k}\rangle=\|B_k^{-1/2}A_k^{1/2}\theta^{\otimes k}\|^2`. $`A_k^{1/2}=W_P^{-1}W_F^{-1}W_{xY_0}`, $`B_k^{-1/2}=W_{Px}W_FW_{Y_0}^{-1}`. $`W_F` disjoint from all else, cancels. Move $`W_{xY_0}` left past $`W_P^{-1}` (disjoint), $`W_{Y_0}^{-1}` (nested). `replicas:move-inverse`: $`\|W_{Px}W_{xY_0}W_P^{-1}W_{Y_0}^{-1}\theta^{\otimes k}\|^2`. Norm identity only; $`A_k,B_k` need not commute.

*D6.10.3* _Compensators._ $`\rho_R` marginal of $`\theta` on $`R\in\{P,Y_0\}`, $`T_R=W_{R,k}^{-1}(\rho_R^t)^{\otimes k}` (positive power $`0` on the kernel). $`\rho_R^{\otimes k}` invariant, commutes with label projectors; in block $`\lambda` eigenvalues $`\le d_\lambda^{-1}` ({bpref "D6.4"}[D6.4.15]) => $`(\rho_R^t)^{\otimes k}\le d_\lambda^{-t}` there. $`W_R^{-1}\le\poly(k)\,d_\lambda^t` ({bpref "D6.6"}[D6.6]) => $`\|T_R\|\le\poly(k)` uniformly in $`\theta`, deficient-rank marginals included.

*D6.10.4* _Commutation._ $`T_P` with $`W_{Px}`: $`W_P^{-1}` central on nested $`P\subseteq Px`; $`(\rho_P^t)^{\otimes k}` commutes with $`U_P`, $`U_x` disjoint. $`T_P` with $`W_{xY_0}`: disjoint. $`T_{Y_0}`: same with numerators swapped.

*D6.10.5* _Insertion._ $`\widetilde\rho_R=\widehat\rho_R` ({bpref "D5.1"}[D5.1]). $`P,Y_0` disjoint $`\Rightarrow` product of the two marginal support projectors fixes $`\theta`. So $`W_P^{-1}W_{Y_0}^{-1}\theta^{\otimes k}=T_PT_{Y_0}(\widetilde\rho_P^{-t}\widetilde\rho_{Y_0}^{-t})^{\otimes k}\theta^{\otimes k}`. Move $`T_P,T_{Y_0}` left (D6.10.4), D6.10.3: norm squared $`\le\poly(k)\,\|W_{Px}W_{xY_0}(\widetilde\rho_P^{-t}\widetilde\rho_{Y_0}^{-t})^{\otimes k}\theta^{\otimes k}\|^2`.

*D6.10.6* _Integrals._ $`W_{Px}=\int(\sigma^t)^{\otimes k}d\zeta_{Px}`, $`W_{xY_0}=\int(\tau^t)^{\otimes k}d\zeta_{xY_0}` (probability measures, {bpref "D6.6"}[D6.6]). Triangle inequality (vector-valued integral), $`\|M^{\otimes k}\theta^{\otimes k}\|=\|M\theta\|^k`: `replicas:move-one-copy`, $`\poly(k)\sup_{\sigma,\tau}\|\sigma^t_{Px}\tau^t_{xY_0}\widetilde\rho_P^{-t}\widetilde\rho_{Y_0}^{-t}\theta\|^{2k}`.

*D6.10.7* _Reduction to densities._ Subdensity $`\sigma=s\sigma'`, $`s\le1`: $`\sigma^t=s^t\sigma'^t` => $`\|\sigma'^t\cdots\|\ge\|\sigma^t\cdots\|`; sup over densities.

*D6.10.8* _One-copy word._ $`P` disjoint from $`xY_0` $`\Rightarrow` $`\widetilde\rho_P^{-t}` commutes with $`\tau^t_{xY_0}`. Word: $`\sigma_{Px}^{a/2}\widetilde\rho_P^{-a/2}\tau_{xY_0}^{a/2}\widetilde\rho_{Y_0}^{-a/2}\theta` ($`t=a/2`), Lemma 5.1 with $`U=Y_0`.

*D6.10.9* _Apply Lemma 5.1._ $`\log\|\text{word}\|\le-a\eta_\theta/2+Ca^{5/4}\ell^2` => $`\|\text{word}\|^{2k}\le\exp\{ka[-\eta_\theta+2Ca^{1/4}\ell^2]\}` => $`\langle\theta^{\otimes k},C_{x,k}^{-1}\theta^{\otimes k}\rangle\le\poly(k)\exp\{-ka[\eta_\theta-2Ca^{1/4}\ell^2]\}`. D6.10.1 ($`2C\ell^2\le C'\log^{C'}(e\dim x)`).

*D6.10.10* _Exchange._ $`A_k(P,Y,F)=A_k(F,Y,P)`. $`x=\varnothing`: $`B_k=A_k`.

_Used from._ {bpref "D6.1"}[D6.1]; {bpref "D6.4"}[D6.4](2),(5); {bpref "D6.6"}[D6.6] (`W-comparison`, `W-integral`); {bpref "D6.8"}[D6.8]; {bpref "D5.1"}[D5.1]; {bpref "D5.5"}[D5.5] (Lemma 5.1) at $`U=Y_0`, $`\sigma` on $`Px`, $`\tau` on $`xY_0` (subnormalized ok), $`a=2t`, $`\ell=\log(e\dim x)`, hypothesis $`0<a\ell\le c` ($`c` of {bpref "D5.5"}[D5.5]): $`\|\sigma^{a/2}\widehat\rho_P^{-a/2}\tau^{a/2}\widehat\rho_{Y_0}^{-a/2}\theta\|\le\exp(-\tfrac a2\eta_\theta+Ca^{5/4}\ell^2)`.

:::

# 6.3 Scalar symbols, products and absolute values

:::definition "D6.11" (lean := "AreaLaw.Replicas.dθ, AreaLaw.Replicas.eq_replicas_resolution, AreaLaw.Replicas.μ, AreaLaw.Replicas.eq_replicas_husimi")
*D6.11* — Def eq:resolution, eq:husimi: Coherent probability measure

_Source: 05-replicas.tex 596–613, `replicas:resolution` (599–600), `replicas:husimi` (604–605)._

$`d\theta` invariant probability measure on the unit sphere of $`\mathcal V`. $$`\int P_{\theta,k}\,d\theta=D_k^{-1}\Pi_k.` Proof: LHS commutes with all $`U^{\otimes k}` (invariance of $`d\theta`), supported on irreducible $`\mathcal S_k` => scalar; $`\operatorname{Tr}P_{\theta,k}=1` gives $`D_k^{-1}`. Density $`\sigma` on $`\mathcal S_k`: $$`d\mu_\sigma(\theta)=D_k\operatorname{Tr}(\sigma P_{\theta,k})\,d\theta,` probability measure ($`\int d\mu_\sigma=\operatorname{Tr}\sigma\Pi_k=1`). Same $`\sigma` defines expectation and mixing measure.

:::

:::proof "D6.11" (uses := "D6.1")
_Formal route_ (RefactoringResult.md §5, D6.11): `dθ` = pushforward of Haar measure on the unitary group under `U ↦ U e_a` (Coherent.lean:74), on the subtype sphere of `Ω → ℂ`; uniqueness not proved. Reason: matches the ported functional `coherentIntegral`, bridged by `coherentIntegral_eq_integral_μ` (:163).

_Used from._ {bpref "D6.1"}[D6.1].

:::

:::lemma_ "D6.12" (lean := "AreaLaw.Replicas.lemma_6_4")
*D6.12* — Lemma 6.4: Marked-copy scalar symbols

_Source: 05-replicas.tex statement 615–658, proof 660–845; equations `replicas:polynomial-symbol` (628–634), `replicas:skew-symbol` (636–641), `replicas:skew-bound` (651–656)._

Fix a partition $`P,Y,F` of $`\mathcal V`, $`0<t<1/4`, $`a=2t`, and a one-copy operator $`h` supported on $`PY`. With $`A_k` of {bpref "D6.8"}[D6.8] and $`\bar h=k^{-1}\sum_jh^{(j)}`, on $`\mathcal S_k` define $$`O_k=A_k^{-1/2}\bar hA_k^{1/2},\qquad f_\theta=\langle\theta,\rho_P^t\rho_Y^{-t}h\rho_P^{-t}\rho_Y^t\theta\rangle,` $`\rho_Q` the $`Q`-marginal of $`\theta`, powers zero on kernels. Then:

(1) $`\sup_k\|O_k\|<\infty` (bound depends on the fixed system and $`h`).

(2) Every fixed noncommutative polynomial $`q` in two variables: $$`\sup_\sigma\Bigl|\operatorname{Tr}\sigma\,q(O_k,O_k^\dagger)-\int q(f_\theta,\overline{f_\theta})\,d\mu_\sigma(\theta)\Bigr|\to0,` $`\sup` over all densities on $`\mathcal S_k`.

(3) With $`\mathcal D_k=|O_k|+|O_k^\dagger|-O_k-O_k^\dagger`, uniformly in $`\sigma`: $$`\operatorname{Tr}\sigma\mathcal D_k=2\int(|f_\theta|-\operatorname{Re}f_\theta)\,d\mu_\sigma(\theta)+o_k(1).`

(4) If $`0\le h\le I` with a designated supporting subsystem of dimension $`d_h`, $`x=Y\cap\operatorname{supp}h` (designated support may replace the minimal one), $`Y_0=Y\setminus x`, $`\eta_\theta=S_\theta(x|P)+S_\theta(x|Y_0)=I_\theta(x:F|P)=I_\theta(x:F|Y_0)`, and $`a\log(ed_h)\le c`: $$`\operatorname{Tr}\sigma\mathcal D_k\le Ca^2\log^C(ed_h)\int\eta_\theta^{1/8}\,d\mu_\sigma(\theta)+o_k(1).` Same with the outer parts exchanged.

:::

:::proof "D6.12" (uses := "D2.1, D5.1, D6.4, D6.6, D6.8, D6.9, D6.11, D6.13, D6.14, D6.15, D6.16, D5.15")
Assembly of {bpref "D6.13"}[D6.13]–{bpref "D6.16"}[D6.16].

*D6.12.1* Item 1; $`O_k` replaced by polynomial words $`B_k`, $`\limsup\|O_k-B_k\|\le\varepsilon`: {bpref "D6.13"}[D6.13].

*D6.12.2* Symbol of $`\mathcal T_k(\text{word})` on product vectors, uniformly in $`\sigma`: {bpref "D6.14"}[D6.14], {bpref "D6.15"}[D6.15].

*D6.12.3* Item 2, removal of clipping, continuity and boundedness of $`f_\theta`: {bpref "D6.16"}[D6.16.1]–{bpref "D6.16"}[D6.16.4]. Item 3: {bpref "D6.16"}[D6.16.5]–{bpref "D6.16"}[D6.16.7].

*D6.12.4* Item 4: $`f_\theta=f(t)` of Lemma 5.3, $`a=2t`, $`x=Y\cap\operatorname{supp}h`, $`U=Y_0` ($`Y=xU`), $`P_0=P\cap\operatorname{supp}h`. Purity gives the two expressions for $`\eta_\theta`. Enlarging $`x` to the designated support only enlarges $`\ell_h`, allowed by Lemma 5.3. $`a\log(ed_h)\le c\Rightarrow a\ell_h\le c`. Pointwise $`|f_\theta|-\operatorname{Re}f_\theta\le Ca^2\log^4(ed_h)\eta_\theta^{1/8}`; integrate against $`\mu_\sigma` in item 3 (factor $`2` absorbed).

*D6.12.5* Exchange: swap $`P,F` ($`A_k` symmetric, {bpref "D6.8"}[D6.8]).

_Used from._ {bpref "D2.1"}[D2.1]; {bpref "D5.1"}[D5.1] (bracket powers: $`\rho^t` in $`f_\theta` is $`\rho^{[t]}`); {bpref "D6.4"}[D6.4], {bpref "D6.6"}[D6.6], {bpref "D6.8"}[D6.8], {bpref "D6.9"}[D6.9], {bpref "D6.11"}[D6.11]; {bpref "D6.13"}[D6.13]–{bpref "D6.16"}[D6.16] (the proof stages); {bpref "D5.15"}[D5.15] (Lemma 5.3) at $`U=Y_0`, $`x=Y\cap\operatorname{supp}h`, $`P_0=P\cap\operatorname{supp}h`, $`t=a/2`, $`f_\theta=f(t)`, hypothesis $`0<a\ell_h\le c` ($`c` of {bpref "D5.15"}[D5.15], $`\ell_h=\log(ed_h)`): $`|f_\theta|-\operatorname{Re}f_\theta\le Ca^2\ell_h^4\eta_\theta^{1/8}`.

:::

:::lemma_ "D6.13" (lean := "AreaLaw.Replicas.step_6_13")
*D6.13* — Step: Bounded approximation on symmetric inputs

_Source: 05-replicas.tex 666–710, `replicas:marked-word` (671–673), `replicas:inverse-innermost` (679–682), `replicas:polynomial-approximation` (703–705)._

(a) $`O_k`, as a quadratic form on $`\mathcal S_k`, is the compression of $`R_{P,k}R_{Y,k}^{-1}h^{(k)}R_{P,k}^{-1}R_{Y,k}`; $`\sup_k\|O_k\|<\infty`. (b) Every $`\varepsilon>0`: there are $`\delta`, polynomials, operators $`B_k` (compressions of a fixed polynomial word in marked operators on copy $`k` and stars $`J_{Q,k}`) with common $`\limsup_k\|B_k\|` bound and $`\limsup_k\|O_k-B_k\|\le\varepsilon`.

:::

:::proof "D6.13" (uses := "D6.4, D6.6, D6.8, D6.9")
*D6.13.1* _Cancel $`F`._ $`A_k^{1/2}=W_P^{-1}W_F^{-1}W_Y`; $`W_F` commutes with $`\bar h` ($`h` on $`PY`), $`W_P`, $`W_Y` => $`O_k=W_Y^{-1}W_P\bar hW_P^{-1}W_Y`.

*D6.13.2* _Marked copy._ Symmetric $`z,z'`: $`\langle z',\bar hz\rangle=\langle z',h^{(k)}z\rangle` ($`W^{\pm1}` preserve $`\mathcal S_k`). $`W_{Q,k}=R_{Q,k}W_{Q,k-1}`, commuting. $`W_{P,k-1},W_{Y,k-1}` commute with $`h^{(k)}` (disjoint copies), $`R_P`, $`R_Y`, each other: cancel. Left: compression of `replicas:marked-word`.

*D6.13.3* _Product decomposition._ $`h=\sum c_P\otimes e_Y`, finite (matrix units on the two parts of its support).

*D6.13.4* _Quadratic form._ $`R_P,R_Y` commute (disjoint); $`R_Q` self-adjoint. Symmetric unit $`z`: $`\langle z,R_PR_Y^{-1}c_Pe_YR_P^{-1}R_Yz\rangle=\langle R_Ye_Y^\dagger R_Y^{-1}z,R_Pc_PR_P^{-1}z\rangle`. Both inverses act directly on $`z`.

*D6.13.5* _Bound._ $`\|R_Ye_Y^\dagger R_Y^{-1}z\|\le\|R_Y\|\|e_Y\|\|R_Y^{-1}z\|\le C` ({bpref "D6.6"}[D6.6]); same for $`P`. Numerical radius $`\le C` (finite sum). $`\|T\|\le2\sup_{\|z\|=1}|\langle z,Tz\rangle|` (polarization) $`\Rightarrow\sup_k\|O_k\|<\infty`.

*D6.13.6* _Clip._ Replace each $`R_{Q,k}^{-1}` by $`\max(J_{Q,k},\delta)^{-t}` (`R-inverse`): vector error, $`\limsup\le C_{\mathcal V,t,h}\delta^{(1-2t)/2}` uniformly on symmetric unit vectors. Then each $`R_{Q,k}` by $`(J_{Q,k})_+^t` (`R-forward`): operator-norm error $`\to0` at fixed $`\delta`.

*D6.13.7* _Polynomials._ $`\operatorname{spec}J_{Q,k}\subseteq[-1,1]` ($`\|J\|\le(k-1)/k`, average of $`k-1` transpositions over $`k`). Approximate $`u\mapsto u_+^t`, $`u\mapsto\max(u,\delta)^{-t}` uniformly on $`[-1,1]` by polynomials (Weierstrass). Polarization after summing the finitely many product components: compressed polynomial words $`B_k`, `replicas:polynomial-approximation`.

*D6.13.8* _Order._ $`\varepsilon` fixes $`\delta`, then the polynomials, then $`k\to\infty`. Common $`\limsup_k\|B_k\|` bound: sup of the approximated functions on $`[-1,1]`. Any $`k`-threshold depending on the approximation is irrelevant to the $`\limsup`s below.

_Formal route_ (RefactoringResult.md §5, D6.13 (b)): `B_k` an `IsInjectionPoly` (`step_6_13`, Symbol.lean:302), the class {bpref "D6.15"}[D6.15.1] identifies with compressed words. Reason: the literal word exists only inside the ported proof (`HasMarkedSymbol.compress (polyWord …)`); open, see Next steps.

_Used from._ {bpref "D6.4"}[D6.4](4); {bpref "D6.6"}[D6.6] (`R-forward`, `R-inverse`, $`\|R\|`, $`\|R^{-1}z\|`); {bpref "D6.8"}[D6.8]; {bpref "D6.9"}[D6.9.3].

:::

:::lemma_ "D6.14" (lean := "AreaLaw.Replicas.eq_replicas_uniform_husimi, AreaLaw.Replicas.eq_replicas_finite_husimi")
*D6.14* — Step eq:finite-husimi, eq:uniform-husimi: Coherent measure on a fixed number of copies

_Source: 05-replicas.tex 712–747, `replicas:finite-husimi` (722–727), `replicas:uniform-husimi` (741–747)._

$`G` on $`\mathcal V^{\otimes m}`; $`\mathcal T_{k,m}(G)` = average over ordered injections $`\iota:[m]\to[k]` of $`G` on copies $`\iota(1),\dots,\iota(m)`. Preserves $`\mathcal S_k`; $`k\ge m`: $`\operatorname{Tr}\sigma\mathcal T_{k,m}(G)=\operatorname{Tr}\sigma^{(m)}G` ($`\sigma^{(m)}` the $`m`-copy marginal). Then $$`\int\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle d\mu_\sigma=\frac{D_k}{D_{k+m}}\operatorname{Tr}\bigl[(\sigma\otimes G)\Pi_{k+m}\bigr],` $$`\Bigl|\operatorname{Tr}\sigma\mathcal T_{k,m}(G)-\int\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle d\mu_\sigma\Bigr|\le\frac{C_{d,m}\|G\|}{k},\ \text{uniformly in }\sigma.`

:::

:::proof "D6.14" (uses := "D6.1, D6.11")
*D6.14.1* _Identity._ $`P_{\theta,k}\otimes|\theta^{\otimes m}\rangle\langle\theta^{\otimes m}|=P_{\theta,k+m}`, so $`\int\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle D_k\operatorname{Tr}(\sigma P_{\theta,k})d\theta=D_k\operatorname{Tr}[(\sigma\otimes G)\int P_{\theta,k+m}d\theta]=\frac{D_k}{D_{k+m}}\operatorname{Tr}[(\sigma\otimes G)\Pi_{k+m}]` by `replicas:resolution` at $`k+m` (Chiribella 2011, eq. (5)).

*D6.14.2* _Good permutations._ $`\Pi_{k+m}=\frac1{(k+m)!}\sum_\pi U(\pi)`. Fraction of $`\pi` mapping all of the last $`m` indices into the first $`k`: $`(k)_m/(k+m)_m=1-O_m(k^{-1})`.

*D6.14.3* _Normal form._ Such $`\pi=\alpha\pi_0\beta`, $`\alpha,\beta\in S_k` (first $`k` indices), $`\pi_0` a product of $`m` disjoint swaps $`(i_j\ k{+}j)`, $`i_j` distinct in $`[k]`: reorder old images of the last indices on the left, their old preimages on the right, eliminate the remaining permutation among old indices. $`U(\alpha)` commutes with $`G` (disjoint copies), $`\sigma U(\alpha)=\sigma` => $`\operatorname{Tr}[(\sigma\otimes G)U(\pi)]=\operatorname{Tr}[(\sigma\otimes G)U(\pi_0)]` (same for $`\beta`).

*D6.14.4* _Value._ $`\operatorname{Tr}[(A\otimes B)\mathrm{SWAP}]=\operatorname{Tr}[AB]` per swap: $`\operatorname{Tr}[(\sigma\otimes G)U(\pi_0)]=\operatorname{Tr}\sigma^{(m)}G`.

*D6.14.5* _Rest._ Other terms: absolute value $`\le\|\sigma\otimes G\|_1\le d^m\|G\|` ($`\|\sigma\|_1=1`, $`\|G\|_1\le d^m\|G\|`), total weight $`O_m(k^{-1})`. $`D_k/D_{k+m}=1+O_{d,m}(k^{-1})`. $`|\operatorname{Tr}\sigma^{(m)}G|\le\|G\|`. Sum: error $`\le C_{d,m}\|G\|/k`.

_Used from._ {bpref "D6.1"}[D6.1]; {bpref "D6.11"}[D6.11].

:::

:::lemma_ "D6.15" (lean := "AreaLaw.Replicas.eq_replicas_injection_product_symbol, AreaLaw.Replicas.eq_replicas_injection_product")
*D6.15* — Step eq:injection-product: Products after compression

_Source: 05-replicas.tex 749–811, `replicas:injection-product` (766–770)._

$`\mathcal T_k(B)=\frac1{k!}\sum_\pi U(\pi)BU(\pi)^\dagger` commutes with all $`U(\pi)`, preserves $`\mathcal S_k`, and $`\Pi_kB\Pi_k|_{\mathcal S_k}=\mathcal T_k(B)|_{\mathcal S_k}`. For fixed $`G,H` on $`m,n` copies and $`k` large: $$`\bigl\|\mathcal T_{k,m}(G)\mathcal T_{k,n}(H)-\mathcal T_{k,m+n}(G\otimes H)\bigr\|\le C_{m,n}\|G\|\|H\|/k.` Hence for a polynomial word $`B_k` ({bpref "D6.13"}[D6.13]) in marked operators and stars: $`B_k^\dagger` has the conjugate symbol, products multiply symbols, each star $`J_{Q,k}\mapsto\rho_Q`; uniformly in $`\sigma`, each fixed word.

:::

:::proof "D6.15" (uses := "D6.13, D6.14")
*D6.15.1* _Averages._ $`z\in\mathcal S_k`: $`\Pi_kB\Pi_kz=\Pi_kBz=\frac1{k!}\sum U(\pi)Bz=\mathcal T_k(B)z` ($`U(\pi)^\dagger z=z`). Products of compressed words = restrictions of products of full averages (Raggio–Werner 1989, Lemma IV.1).

*D6.15.2* _Injection product._ Independent uniform injections $`\iota,\kappa` of $`m,n` copies. Images intersect with probability $`p=O_{m,n}(k^{-1})`. Disjoint images: $`G^\iota H^\kappa=(G\otimes H)^{(\iota,\kappa)}`, $`(\iota,\kappa)` a uniform ordered injection of $`m+n` copies. Intersecting terms and renormalization each cost $`\le p\|G\|\|H\|`.

*D6.15.3* _Star words._ Monomial with $`r` stars (all centered at the marked copy): $`J_{Q,k}^r=k^{-r}\sum_{j_1,\dots,j_r<k}\prod(j_s\ k)` interleaved with marked operators. Repeated donor indices: total weight $`O(k^{-1})`, norm $`O(k^{-1})` for that fixed word. Distinct donors: coefficient $`(k-1)_r/k^r=1+O_r(k^{-1})`. After $`\mathcal T_k`, center and donors form a uniformly relocated block of $`1+r` copies: $`\mathcal T_k(\text{word})=\mathcal T_{k,1+r}(G_{\rm word})+O(k^{-1})`, fixed $`G_{\rm word}`.

*D6.15.4* _Several words._ Iterate D6.15.2: product of words = one injection average on disjoint blocks, one center per word.

*D6.15.5* _Donor contraction._ On a product vector, a donor in one partial swap: $`\operatorname{Tr}_{\rm donor}\bigl[(|\theta\rangle\langle\theta|)_{\rm donor}\sum_{a,b}(E_{ab})_{Q,\rm donor}\otimes(E_{ba})_{Q,\rm center}\bigr]=\sum_{ab}\operatorname{Tr}(\rho_QE_{ab})E_{ba}=(\rho_Q)_{\rm center}`. Tracing distinct donors successively keeps operator order on each center.

*D6.15.6* _Multiplicativity._ $`\langle\theta^{\otimes(m+n)},(G\otimes H)\theta^{\otimes(m+n)}\rangle=\langle\theta^{\otimes m},G\theta^{\otimes m}\rangle\langle\theta^{\otimes n},H\theta^{\otimes n}\rangle`. Adjoint reverses order, conjugates scalars.

*D6.15.7* _Conclusion._ `replicas:uniform-husimi` ({bpref "D6.14"}[D6.14]) on $`G_{\rm word}`.

_Used from._ {bpref "D6.13"}[D6.13], {bpref "D6.14"}[D6.14].

:::

:::lemma_ "D6.16" (lean := "AreaLaw.Replicas.step_6_16")
*D6.16* — Step: Removing clipping; absolute values; closing the lemma

_Source: 05-replicas.tex 813–845._

Rest of {bpref "D6.12"}[D6.12] after {bpref "D6.13"}[D6.13]–{bpref "D6.15"}[D6.15]: (i) $`f_\theta` bounded, continuous in $`\theta`; (ii) `replicas:polynomial-symbol` for every fixed $`q`; $`O_k^\dagger O_k`, $`O_kO_k^\dagger` have symbol $`|f_\theta|^2`; (iii) `replicas:skew-symbol`; (iv) `replicas:skew-bound`.

:::

:::proof "D6.16" (uses := "D5.15, D6.13, D6.14, D6.15")
*D6.16.1* _Tail of inverse powers._ Eigenvalues $`p_i` (with multiplicity) of any marginal density on $`Q`: $`\sum_{0<p_i<\delta}p_i^{1-2t}\le d_Q\delta^{1-2t}`. Pure $`\theta`, marginal $`\rho_Q`: $`\|\rho_Q^{-t}\mathbf 1_{(0,\delta)}(\rho_Q)\theta\|^2=\sum_{0<p_i<\delta}p_i^{-2t}\cdot p_i\le d_Q\delta^{1-2t}`, uniformly in $`\theta`.

*D6.16.2* _Convergence._ Clipping: $`\rho_Q^{-t}\to\max(\rho_Q,\delta)^{-t}` (symbol of $`\max(J_{Q,k},\delta)^{-t}`). Difference on eigenvalue $`p<\delta`: $`p^{-t}-\delta^{-t}\in(0,p^{-t})`; zero for $`p\ge\delta`. So $`\|(\rho_Q^{-t}-\max(\rho_Q,\delta)^{-t})\theta\|^2\le d_Q\delta^{1-2t}` (D6.16.1). Clipped one-copy vectors of `replicas:inverse-innermost` converge uniformly in $`\theta` to the zero-kernel-power vectors as $`\delta\to0`, error $`\le\sqrt{d_Q}\,\delta^{(1-2t)/2}`; so do their inner products: clipped symbols $`\to f_\theta` uniformly.

*D6.16.3* _Regularity._ Clipped symbols continuous in $`\theta` (continuous functions of marginals); uniform limit $`\Rightarrow` $`f_\theta` bounded, continuous.

*D6.16.4* _Polynomial symbol._ Telescope fixed products via `replicas:polynomial-approximation` and the common $`\limsup\|B_k\|` bound; $`\varepsilon\to0`, $`\delta\to0`: `replicas:polynomial-symbol`.

*D6.16.5* _Squares._ $`O^\dagger O`, $`OO^\dagger` have symbol $`\overline{f_\theta}f_\theta=|f_\theta|^2`.

*D6.16.6* _Square root._ $`M` with $`\sup_k\|O_k\|\le M`, $`|f_\theta|\le M`. Spectra of $`O^\dagger O`, $`OO^\dagger` and values $`|f_\theta|^2` in $`[0,M^2]`. Approximate $`\sqrt\cdot` uniformly on $`[0,M^2]` by polynomials: symbols $`|f_\theta|` for $`|O_k|`, $`|O_k^\dagger|`, arbitrarily small uniform expectation errors. No normality of $`O_k` used.

*D6.16.7* _Skew symbol._ Linear terms $`O+O^\dagger\mapsto2\operatorname{Re}f_\theta`: `replicas:skew-symbol`.

*D6.16.8* _Skew bound._ {bpref "D6.12"}[D6.12.4].

_Used from._ the statement of the lemma this step belongs to; {bpref "D6.13"}[D6.13], {bpref "D6.14"}[D6.14], {bpref "D6.15"}[D6.15]; {bpref "D5.15"}[D5.15] = Lemma 5.3.

:::
