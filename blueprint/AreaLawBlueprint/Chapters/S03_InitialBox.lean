import Verso
import VersoManual
import VersoBlueprint
import AreaLawBlueprint.TexPrelude
import AreaLawRefactored

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Marginal tails and an initial box estimate" =>

(i) Lemma 3.1 ({bpref "D3.1"}[D3.1]): surprisal $`K=-\log p_j` of a marginal across a cut has MGF $`\le e^{uS+512e\vartheta\mathcal Bu^2}` on $`|u|\le[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}`, tail of width $`\sqrt{\mathcal B}`; proof tilts $`\Omega` by $`\rho^{-u/2}`, compares tilted energy with gap. Lattice: $`\mathcal B\le C(1+|\partial_\Lambda B|)` ({bpref "D3.2"}[D3.2]). (ii) Lemma 3.2 ({bpref "D3.4"}[D3.4]): $`S(X|T)\le\frac12S(X)+C_{\rm buf}r` for $`X=A\cap Q_0` buffered inside a safe rectangle; proof maximizes $`\|L_m\cdots L_1\Omega\|` over positive filters on nested $`X_1\subset\dots\subset X_m`, $`\operatorname{Tr}L_j^{2/a_j}=1`, $`a_j\propto1/(r+d_j)`, $`\sum a_j=2`; gap + Lemma 3.1 bound $`-2\log N` below by $`\sum a_jS(X_j)`, Schmidt-pinned trials bound it above by $`S(X)+\sum a_jS(T_j)`; SSA gives $`\frac12`. (iii) Proposition 3.3 ({bpref "D3.16"}[D3.16]): chain rule averaged over random orders of $`\le M^2` children of size $`\le r` => $`F_{\rm box}(Mr)\le\lambda F_{\rm box}(r)+CM^2r`, $`\lambda=(1-p_0/4)M^2<M^2` => $`F_{\rm box}(r)\le Cr^{1+e_0}`, $`e_0\in(0,1)`. Downstream uses: Exports.

:::lemma_ "D3.1" (lean := "AreaLaw.lemma_3_1")
*D3.1* — Lemma 3.1: Marginal moment and tail bounds

Lines 34–200 (statement 34–69, proof 71–200). Label `lem:tail`; displayed claims `eq:initial-tail-mgf` (53–59), `eq:initial-tail-probability` (61–68); intermediate labels `eq:initial-exact-tilt` (83–86), `eq:initial-support-conjugation` (109–112), `eq:initial-narrow-strip` (144–148), `eq:initial-real-quadratic` (158–163), `eq:initial-tilted-energy` (172–176).

Let $`\mathcal H=\bigotimes_{v\in V}\mathcal H_v`, finite, finite-dimensional factors. Let $`\mathsf H=\sum_{i\in\mathcal I}h_i`, $`\mathcal I` finite, $`h_i=h_i^*`, $`\|h_i\|\le c_0` ($`c_0\ge0` fixed), $`h_i` with designated support $`D_i\subseteq V`. Unique unit ground vector $`\Psi`, $`\mathsf H\Psi=E_0\Psi`, $`g_0>0` with $`\mathsf H-E_0\ge g_0(\mathrm{id}-|\Psi\rangle\langle\Psi|)`. Fix a bipartition $`B\sqcup B^c=V`; $`\mathcal I_\times=\{i:D_i\cap B\ne\varnothing\ne D_i\cap B^c\}`. Put $$`\rho=\operatorname{Tr}_{B^c}|\Psi\rangle\langle\Psi|,\quad d_i=\prod_{v\in D_i}\dim\mathcal H_v,\quad \mathcal B=1+\sum_{i\in\mathcal I_\times}\log^2(e\,d_i),\quad \vartheta=c_0/g_0 .` Let $`p_j` be the positive eigenvalues of $`\rho`, $`K=-\log p_j` with probability $`p_j`, $`S=S(\rho)`. Then $$`\log\mathbb E\,e^{uK}\le uS+512e\,\vartheta\,\mathcal B\,u^2,\qquad |u|\le\frac1{32\sqrt{(1+\vartheta)\mathcal B}},` and for every $`w\ge0` $$`\Pr\{|K-S|>w\}\le\min\Big\{1,\;2e^{e/2}\exp\Big(-\frac{w}{32\sqrt{(1+\vartheta)\mathcal B}}\Big)\Big\}.`

:::

:::proof "D3.1"
Notation: $`M(u)=\sum_jp_j^{1-u}=\mathbb Ee^{uK}`, $`L(u)=\log M(u)`. Then $`L(0)=0`, $`L'(0)=\sum_jp_j(-\log p_j)=S`.

*D3.1.1* _Tilted vector._ $`P` = support projection of $`\rho` on $`\mathcal H_B`. $`F=\rho^{-u/2}` on $`P\mathcal H_B`, $`F=\mathrm{id}` on $`\ker\rho`; acts on $`B` only, invertible. Schmidt form $`\Psi=\sum_j\sqrt{p_j}\,a_j\otimes b_j`: $`\|F\Psi\|^2=\sum_jp_j^{1-u}=M(u)`. $`\Theta=F\Psi/\sqrt{M(u)}` unit, marginal $`\sigma=\operatorname{Tr}_{B^c}|\Theta\rangle\langle\Theta|=\rho^{1-u}/M(u)` (power $`0` on $`\ker\rho`); $`[F,\sigma]=0`.

*D3.1.2* _Exact tilted eigenequation_ (eq:initial-exact-tilt). $`F\mathsf HF^{-1}\Theta=E_0\Theta` ($`\mathsf H\Psi=E_0\Psi`, $`F` invertible). Hence $`E_0=\langle\Theta,F\mathsf HF^{-1}\Theta\rangle` and $$`\langle\Theta,(\mathsf H-E_0)\Theta\rangle=\sum_i\operatorname{Re}\langle\Theta,(h_i-Fh_iF^{-1})\Theta\rangle .`

*D3.1.3* _Only crossing terms contribute._ $`D_i\subseteq B^c`: $`F` commutes with $`h_i`, term $`=0`. $`D_i\subseteq B`: $`\langle\Theta,Fh_iF^{-1}\Theta\rangle=\operatorname{Tr}\sigma Fh_iF^{-1}=\operatorname{Tr}F^{-1}\sigma Fh_i=\operatorname{Tr}\sigma h_i` (cyclicity, $`[F,\sigma]=0`), term $`=0`. Remains $`i\in\mathcal I_\times`.

*D3.1.4* _Analytic interpolation of a crossing term._ For $`i\in\mathcal I_\times`, $`z\in\mathbb C`: $`\sigma^z:=P\exp(z\log(\sigma|_{P\mathcal H_B}))P`, $`f_i(z)=\langle\Theta,\sigma^zh_i\sigma^{-z}\Theta\rangle`, entire. $`\sigma^0=P`, $`\Theta\in\operatorname{ran}P`, so $`f_i(0)=\langle\Theta,h_i\Theta\rangle` (real). At $`z_u=-u/[2(1-u)]`: on the support $`\sigma^{z_u}=M(u)^{-z_u}\rho^{(1-u)z_u}=M(u)^{-z_u}F` since $`(1-u)z_u=-u/2`; likewise $`\sigma^{-z_u}=M(u)^{z_u}F^{-1}`. Scalars cancel: $`f_i(z_u)=\langle\Theta,Fh_iF^{-1}\Theta\rangle` (eq:initial-support-conjugation). So $$`\langle\Theta,(\mathsf H-E_0)\Theta\rangle=\sum_{i\in\mathcal I_\times}\operatorname{Re}\big(f_i(0)-f_i(z_u)\big).`

*D3.1.5* _Imaginary axis._ $`\sigma^{iy}` unitary on $`\operatorname{ran}P\ni\Theta`: $`|f_i(iy)|\le\|h_i\|\le c_0`.

*D3.1.6* _Crude strip bound $`|f_i(z)|\le2c_0d_i^2` for $`|\operatorname{Re}z|\le\frac14`._ Matrix units of $`\operatorname{End}(\mathcal H_{D_i\cap B})`: $`h_i=\sum_{a,b}E_{ab}\otimes h_{ab}`, $`h_{ab}=(\langle a|\otimes\mathrm{id})h_i(|b\rangle\otimes\mathrm{id})`; relabel $`h_i=\sum_{\alpha=1}^{N_i}c_\alpha\otimes d_\alpha`, $`c_\alpha=E_{ab}` on $`D_i\cap B`, $`d_\alpha=h_{ab}` on $`D_i\cap B^c`. $`N_i=(\dim\mathcal H_{D_i\cap B})^2\le d_i^2`, $`\|c_\alpha\|=1`, $`\|d_\alpha\|\le c_0`. Schmidt form $`\Theta=\sum_j\sqrt{s_j}\,e_j\otimes g_j`: $`f_i(z)=\sum_\alpha\sum_{j,k}s_j^{1/2+z}s_k^{1/2-z}(c_\alpha)_{jk}(d_\alpha)_{jk}` (matrix elements in Schmidt bases). $`x=\operatorname{Re}z\in[-\frac14,\frac14]`: $`|s_j^{1/2+z}s_k^{1/2-z}|=s_j^{1/2+x}s_k^{1/2-x}\le s_j+s_k` (weighted AM–GM). Cauchy–Schwarz: $`\sum_k|(c_\alpha)_{jk}(d_\alpha)_{jk}|\le\|c_\alpha\|\|d_\alpha\|` (row $`\ell^2` norm $`\le` operator norm), same for columns. $`s_j` over rows, $`s_k` over columns, $`\sum s=1`: per $`\alpha` $`\le2\|c_\alpha\|\|d_\alpha\|\le2c_0`. Sum over $`\alpha`: $`|f_i(z)|\le2c_0d_i^2`, uniform in $`\operatorname{Im}z`.

*D3.1.7* _Narrow strip_ (eq:initial-narrow-strip). $`c_0=0`: trivial; else apply to $`f_i/c_0`. Three-lines on $`0\le\operatorname{Re}z\le\frac14`, bounds $`c_0` (D3.1.5), $`2c_0d_i^2` (D3.1.6): $`|f_i(x+iy)|\le c_0(2d_i^2)^{4x}`. $`\ell_i=\log(ed_i)`, $`\log(2d_i^2)\le2\ell_i` ($`\log2\le2`). $`x\le\delta_i:=1/(8\ell_i)`: $`(2d_i^2)^{4x}\le e^{8\ell_i\delta_i}=e`. Same on $`-\delta_i\le\operatorname{Re}z\le0`. So $`|f_i|\le ec_0` for $`|\operatorname{Re}z|\le\delta_i` ($`\ell_i\ge1` => $`\delta_i\le\frac18<\frac14`).

*D3.1.8* _Real quadratic bound_ (eq:initial-real-quadratic). Hermiticity: $`f_i(-\bar z)=\overline{f_i(z)}` (write $`f_i(z)=\langle\sigma^{\bar z}\Theta,h_i\sigma^{-z}\Theta\rangle` and use $`h_i=h_i^*`). With $`f_i=\sum a_nz^n`: $`(-1)^na_n=\bar a_n`, so even $`a_n` real, odd $`a_n` imaginary. For real $`x`: $`\operatorname{Re}(f_i(x)-f_i(0))=\sum_{n\ge2\text{ even}}a_nx^n`. Cauchy on the disk of radius $`\delta_i` with sup $`\le ec_0` (D3.1.7): $`|a_n|\le ec_0\delta_i^{-n}`. For $`|x|\le\delta_i/2`: sum $`\le ec_0(x/\delta_i)^2/(1-(x/\delta_i)^2)\le\frac43ec_0x^2\delta_i^{-2}\le2ec_0x^2\delta_i^{-2}=128\,ec_0\ell_i^2x^2`. $`f_i'(0)=0` not claimed; only $`\operatorname{Re}` of the linear term vanishes.

*D3.1.9* _Tilted excitation energy_ (eq:initial-tilted-energy). $`|u|\le[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}` => $`|u|\le\frac1{32}`, $`|z_u|=|u|/(2|1-u|)\le|u|`. $`\mathcal B\ge1+\sum_{\mathcal I_\times}\ell_i^2` => $`\ell_i\le\sqrt{\mathcal B}`, $`|z_u|\le\frac1{32\ell_i}\le\delta_i/2`: D3.1.8 applies to every crossing term at $`x=z_u`. By D3.1.4: $$`0\le\langle\Theta,(\mathsf H-E_0)\Theta\rangle\le128\,e\,c_0\sum_{\mathcal I_\times}\ell_i^2u^2\le128\,e\,c_0\,\mathcal B\,u^2 .`

*D3.1.10* _Gap converts energy to overlap._ $`\langle\Theta,(\mathsf H-E_0)\Theta\rangle\ge g_0(1-|\langle\Psi,\Theta\rangle|^2)` and $`\langle\Psi,\Theta\rangle=\sum_jp_j^{1-u/2}/\sqrt{M(u)}=M(u/2)/\sqrt{M(u)}`. Hence $$`\frac{M(u/2)^2}{M(u)}=|\langle\Psi,\Theta\rangle|^2\ge1-v,\qquad v:=128\,e\,\vartheta\,\mathcal B\,u^2 .`

*D3.1.11* _Halving inequality._ $`v\le128e\vartheta\mathcal B/[1024(1+\vartheta)\mathcal B]=e\vartheta/[8(1+\vartheta)]<e/8<\frac12`. Take logs: $`2L(u/2)-L(u)\ge\log(1-v)\ge-2v` ($`-\log(1-v)\le2v` on $`[0,\frac12]`). So $`L(u)\le2L(u/2)+\kappa u^2`, $`\kappa=256\,e\,\vartheta\,\mathcal B`.

*D3.1.12* _Iteration_ (eq:initial-tail-mgf). $`u/2^i` stays admissible, either sign. $`L(u)\le2^jL(u/2^j)+\kappa u^2\sum_{i<j}2^i4^{-i}`. $`j\to\infty`: $`2^jL(u/2^j)\to uL'(0)=uS` ($`L` smooth, $`L(0)=0`); $`\sum_i2^{-i}\le2`. So $`L(u)\le uS+2\kappa u^2=uS+512\,e\,\vartheta\,\mathcal B\,u^2`.

*D3.1.13* _Tail_ (eq:initial-tail-probability). $`u_*=[32\sqrt{(1+\vartheta)\mathcal B}]^{-1}`; quadratic term at $`u_*`: $`512e\vartheta\mathcal Bu_*^2=e\vartheta/[2(1+\vartheta)]\le e/2`. Exponential Markov, $`u=+u_*`: $`\Pr\{K-S>w\}\le e^{-u_*w}\mathbb Ee^{u_*(K-S)}\le e^{e/2}e^{-u_*w}`; $`u=-u_*`: $`\Pr\{K-S<-w\}\le e^{e/2}e^{-u_*w}`. Add; $`\min` with $`1` trivial.

_Formal route_ (RefactoringResult.md §5, D3.1.8): Mathlib's higher-order Schwarz lemma on k(z) = f\_i(z) + f\_i(−z) − 2f\_i(0), which vanishes to second order at 0 and is bounded by 4ec₀ on the disk of radius δ\_i: `|Re(f_i(x) − f_i(0))| = |Re k(x)|/2 ≤ 2 e c₀ x² δ_i⁻²` (`AreaLaw.step_3_1_8`, AreaLawRefactored/S03\_InitialBox/MarginalTails.lean:162). Reason: no Mathlib Taylor-coefficient bound; same constant 128 e c₀ ℓ\_i² x².

_Formal route_ (RefactoringResult.md §5, D3.1.3): f\_i is constant for terms A ⊗ 1 and 1 ⊗ A (`modF_kronecker_one`, `modF_one_kronecker`, AreaLawRefactored/S03\_InitialBox/MarginalTails.lean:352, :360), so every term enters through the D3.1.4 identity and the one-sided ones contribute 0. Reason: same content in the Schmidt coordinates already used for D3.1.4.

_Formal route_ (RefactoringResult.md §5, D3.1.1): explicit unitary (V\* ⊗ 1) ∘ glue⁻¹, V the eigenvector unitary of ρ (`step_3_1_1`, `isSchmidt_cut`, AreaLawRefactored/S03\_InitialBox/MarginalTails.lean:900, :865). Reason: encoding only.

_Used from._ none. Textbook: three-lines, Cauchy coefficient estimate, exponential Markov.

:::

:::lemma_ "D3.2" (lean := "AreaLaw.step_3_2_3, AreaLaw.step_3_2_4")
*D3.2* — Step eq:initial-local-tail-parameter: Lattice specialization of Lemma 3.1

Lines 202–212.

Admissible lattice $`H` ({bpref "D1.2"}[D1.2]), $`B\subseteq\Lambda`, $`b'=|\partial_\Lambda B|`; Lemma 3.1 with $`c_0=J`, $`g_0=\Delta`, $`D_i=` support $`X` of $`h_X`, $`\vartheta=J/\Delta`: $$`\mathcal B\le C(1+b').` Hence for every $`n\ge1` and fixed $`M>0` there is $`C_M=C_M(q,R,J,\Delta,M)` with $$`\Pr\{|K-S|>C_M\sqrt{1+b'}\,\log(n+2)\}\le(n+2)^{-M}.`

:::

:::proof "D3.2" (uses := "D3.1, D2.8, D2.7, D2.9")
*D3.2.1* Crossing indices = supports split by $`B`; count $`\le2v_R\mu_R\,b'` ({bpref "D2.9"}[D2.9]).

*D3.2.2* $`d_i=q^{|X|}`, $`|X|\le v_R` ({bpref "D2.8"}[D2.8.4]), so $`\log(ed_i)=1+|X|\log q\le1+v_R\log q`.

*D3.2.3* $`\mathcal B\le1+2v_R\mu_R(1+v_R\log q)^2b'\le C_1(1+b')`, $`C_1=\max\{1,2v_R\mu_R(1+v_R\log q)^2\}`.

*D3.2.4* _Tail (digest expansion; paper states only constant dependence)._ Take $`C_M=32(M+2)\sqrt{(1+\vartheta)C_1}` and $`w=C_M\sqrt{1+b'}\log(n+2)`. Then $`w/[32\sqrt{(1+\vartheta)\mathcal B}]\ge(M+2)\log(n+2)`. Since $`2e^{e/2}<8<9\le(n+2)^2` for $`n\ge1`, eq:initial-tail-probability gives $`\le2e^{e/2}(n+2)^{-(M+2)}\le(n+2)^{-M}`.

_Used from._ {bpref "D3.1"}[D3.1]; {bpref "D2.8"}[D2.8] ($`|X|\le v_R`, {bpref "D2.8"}[D2.8.4]; ball bound {bpref "D2.7"}[D2.7]); {bpref "D2.9"}[D2.9] (terms split by $`B` number $`\le2v_R\mu_R|\partial_\Lambda B|`); D2.13.

:::

:::definition "D3.3" (lean := "OpenAI.IsIntRect, OpenAI.boxSize, OpenAI.IsSafe") (uses := "D1.3, D1.6, D2.6")
*D3.3* — Def: Safe rectangles, size, buffers, local entropy notation

Lines 219–238.

Fix $`A\subseteq\Lambda`; $`Z=Z_A` ({bpref "D1.6"}[D1.6]) = endpoints of edges of $`\partial_\Lambda A`. Integer rectangle $`Q` = product of two finite nonempty integer intervals; $`\operatorname{size}(Q)` = larger side length in sites. Fix $`D_0>2R+10`. $`Q` _safe_ iff $$`\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q),\qquad\operatorname{dist}_\infty(Q,\varnothing)=\infty .` Integer $`d\ge0`: $`Q^{+d}=Q+([-d,d]^2\cap\mathbb Z^2)` (ambient; as $`T_j` in {bpref "D2.6"}[D2.6]). Physical regions: $`A\cap Q^{+d}`. Unit vector $`\xi`: $`\rho_{\xi,D}` marginal on $`D`, $`S_\xi(D)` its entropy.

_Used from._ {bpref "D1.3"}[D1.3], {bpref "D1.6"}[D1.6], {bpref "D2.6"}[D2.6].

:::

:::lemma_ "D3.4" (lean := "AreaLaw.lemma_3_2")
*D3.4* — Lemma 3.2: Conditional entropy in a buffered rectangle

Lines 240–586 (statement 240–256, proof 258–586). Label `lem:initial-buffer`; displayed claim `eq:initial-buffer-discount` (252–255). Proof is split below into anchors {bpref "D3.5"}[D3.5]–{bpref "D3.14"}[D3.14].

There are an integer $`C_{\rm pad}\ge1` and $`C_{\rm buf}`, both depending only on $`q,R,J,\Delta` ($`D_0>2R+10`, $`D>2R+2` fixed), such that for every safe $`Q`, integer $`r\ge1`, integer rectangle $`Q_0` with $`\operatorname{size}(Q_0)\le r` and $`Q_0^{+C_{\rm pad}r}\subseteq Q`, $$`X=A\cap Q_0,\qquad T=(A\cap Q_0^{+C_{\rm pad}r})\setminus X,` in $`\Omega`: $$`S(X\mid T)\le\tfrac12S(X)+C_{\rm buf}\,r .`

:::

:::proof "D3.4" (uses := "D3.1, D3.2, D3.3, D2.2, D2.7, D2.8, D2.9, D2.10, D1.4")
$`X=\varnothing`: both sides $`0`. Else {bpref "D3.5"}[D3.5]–{bpref "D3.14"}[D3.14] in order. Constants chosen: $`D_0`, $`D` (depend on $`R`) $`\to` $`C_{\rm pad}` ({bpref "D3.6"}[D3.6], enlarged {bpref "D3.10"}[D3.10]) $`\to` $`\epsilon` (floor, removed {bpref "D3.12"}[D3.12]) $`\to` $`C_{\rm buf}` ({bpref "D3.14"}[D3.14]).

*D3.4.1* {bpref "D3.5"}[D3.5]: nested regions, locality; contour budget independent of $`C_{\rm pad}`.

*D3.4.2* {bpref "D3.6"}[D3.6]: harmonic weights, $`\mathcal E=4/Z_r` small uniformly in $`r`.

*D3.4.3* {bpref "D3.7"}[D3.7]–{bpref "D3.8"}[D3.8]: stationarity of optimized filters.

*D3.4.4* {bpref "D3.9"}[D3.9]–{bpref "D3.10"}[D3.10]: excitation energy of optimized vector $`\le C\mathcal E`; fix $`C_{\rm pad}`.

*D3.4.5* {bpref "D3.11"}[D3.11]: lower bound on $`-2\log N`.

*D3.4.6* {bpref "D3.12"}[D3.12]–{bpref "D3.13"}[D3.13]: upper bound on $`-2\log N` by Schmidt pinning.

*D3.4.7* {bpref "D3.14"}[D3.14]: combine, SSA.

_Used from._ {bpref "D3.1"}[D3.1], {bpref "D3.2"}[D3.2], {bpref "D3.3"}[D3.3]; {bpref "D2.2"}[D2.2] item 2 (SSA); {bpref "D2.7"}[D2.7]–{bpref "D2.10"}[D2.10]; D2.13; {bpref "D1.4"}[D1.4] (gap, uniqueness).

:::

:::lemma_ "D3.5" (lean := "AreaLaw.step_3_5")
*D3.5* — Step: Nested regions, locality, single split, contour budget (Lemma 3.2, part 1)

Lines 269–301. Label `eq:initial-contour-budget` (295–299).

Fix an integer $`D>2R+2` and an integer $`C_{\rm pad}>D+1` (still free). Put $$`m=\Big\lfloor\frac{(C_{\rm pad}-1)r}{D}\Big\rfloor,\quad d_j=r+jD,\quad X_j=A\cap Q_0^{+d_j}\ (1\le j\le m),\quad X_0=X .` Then (a) $`1\le m\le C_{\rm pad}r/D`, $`X_0\subset X_1\subset\dots\subset X_m`, $`Q_0^{+d_m}\subseteq Q`; (b) every interaction meeting some $`X_j` has support in $`A`; no edge of $`\partial_\Lambda A` is incident with any $`X_j`; (c) $`|\partial_\Lambda X_j|\le4(r+2d_j)`; (d) support $`S_h` split by $`X_j` is disjoint from $`X_i` for $`i<j`, contained in $`X_i` for $`i>j`: each support split by at most one $`X_j`; (e) constants independent of $`C_{\rm pad}`: $$`\#\{\text{interactions split by }X_j\}\le C(r+d_j),\qquad\mathcal B_j\le C(r+d_j),` where $`\mathcal B_j` is the $`\mathcal B` of Lemma 3.1 for the bipartition $`X_j\mid X_j^c` of $`\Omega` ($`c_0=J`, $`g_0=\Delta`).

:::

:::proof "D3.5" (uses := "D3.3, D2.6, D2.7, D2.8, D2.9, D3.2")
*D3.5.1* _(a)._ $`(C_{\rm pad}-1)r\ge C_{\rm pad}-1>D` ($`r\ge1`, $`C_{\rm pad}>D+1`) => $`m\ge1`. $`d_m=r+mD\le r+(C_{\rm pad}-1)r=C_{\rm pad}r` => $`Q_0^{+d_m}\subseteq Q_0^{+C_{\rm pad}r}\subseteq Q`. Nesting: $`d_j` increasing; $`X_0=A\cap Q_0\subseteq A\cap Q_0^{+d_1}`.

*D3.5.2* _(b)._ $`h_S` meets $`X_j` at $`x`, $`S\ni y\notin A`. Shortest $`\Lambda`-path $`x\to y`: length $`\le R`, from $`A` to $`A^c`, so contains $`\{z,z'\}\in\partial_\Lambda A`; $`z\in Z`, $`|z-x|_\infty\le|z-x|_1\le R`. Then $`\operatorname{dist}_\infty(Q,Z)\le R<D_0\le D_0\operatorname{size}(Q)`, contradicting safety. Edge of $`\partial_\Lambda A` at $`x\in X_j\subseteq Q` puts $`x\in Z\cap Q`: same contradiction.

*D3.5.3* _(c)._ $`\{x,y\}\in\partial_\Lambda X_j`, $`x\in X_j`, $`y\in\Lambda\setminus X_j`. $`y\in Q_0^{+d_j}` => $`y\notin A` => $`\{x,y\}\in\partial_\Lambda A`, excluded by (b). So $`y\notin Q_0^{+d_j}`: edge crosses the ambient perimeter; $`\le r+2d_j` sites per axis => $`\le2\cdot2(r+2d_j)` perimeter edges. Missing sites of $`\Lambda` only remove edges.

*D3.5.4* _(d)._ Split: $`S_h\cap X_j\ne\varnothing\ne S_h\setminus X_j`; by (b) $`S_h\subseteq A`. Ambient diameter $`\le` graph diameter $`\le R` ($`d_\Lambda\ge|\cdot|_1\ge|\cdot|_\infty`). Take $`p\in S_h\cap Q_0^{+d_j}`, $`p'\in S_h\setminus Q_0^{+d_j}`. Every $`s\in S_h`: $`|s-p|_\infty\le R<D`, so $`s\in Q_0^{+d_j+R}\subseteq Q_0^{+d_{j+1}}`; with $`S_h\subseteq A`, $`S_h\subseteq X_i` for $`i>j`. For $`i<j`: suppose $`s\in S_h\cap Q_0^{+e_i}`, $`e_0=0`, $`e_i=d_i` ($`i\ge1`). $`|p'-s|_\infty\le R` => $`p'\in Q_0^{+e_i+R}`. $`e_i+R<d_j`: $`i\ge1`: $`d_i+R\le d_{j-1}+R<d_{j-1}+D=d_j`; $`i=0`: $`R<D<d_1\le d_j`. So $`p'\in Q_0^{+d_j}`, contradiction.

*D3.5.5* _(e)._ {bpref "D2.9"}[D2.9] with (c): $`\#\{\text{split by }X_j\}\le2v_R\mu_R\cdot4(r+2d_j)\le16v_R\mu_R(r+d_j)`. Crossing indices for $`X_j\mid X_j^c` = split ones; {bpref "D3.2"}[D3.2.1]–{bpref "D3.2"}[D3.2.3]: $`\mathcal B_j\le1+2v_R\mu_R(1+v_R\log q)^2\cdot4(r+2d_j)\le C(r+d_j)` ($`r+d_j\ge1`). Constants depend on $`q,R` only.

_Used from._ {bpref "D3.3"}[D3.3]; {bpref "D2.6"}[D2.6]–{bpref "D2.9"}[D2.9], {bpref "D3.2"}[D3.2].

:::

:::lemma_ "D3.6" (lean := "AreaLaw.eq_initial_harmonic_weights")
*D3.6* — Step eq:initial-harmonic-weights: Harmonic weights

Lines 303–333. Labels `eq:initial-harmonic-weights` (315–320), `eq:initial-harmonic-lower` (323–326).

Put $`Z_r=\sum_{j=1}^m\frac1{r+d_j}`, $`a_j=\frac{2}{Z_r(r+d_j)}`, $`\mathcal E=\sum_j(r+d_j)a_j^2`. Then $`\sum_ja_j=2`, $`\mathcal E=4/Z_r`, $`\mathcal E=\min\{\sum_j(r+d_j)b_j^2:\sum b_j=2\}`, and $$`Z_r\ge\frac1D\log\frac{C_{\rm pad}+1}{2+D}.` Hence $`\mathcal E\le4D/\log\frac{C_{\rm pad}+1}{2+D}\to0` as $`C_{\rm pad}\to\infty`, uniformly in $`r\ge1`. Choose $`C_{\rm pad}` so large that $`a_j\le\frac12` for all $`j`; enlarged once more in {bpref "D3.10"}[D3.10].

:::

:::proof "D3.6" (uses := "D3.5")
*D3.6.1* Cauchy–Schwarz: $`4=(\sum_jb_j)^2\le\big(\sum_j(r+d_j)b_j^2\big)\big(\sum_j\frac1{r+d_j}\big)`, equality iff $`b_j\propto\frac1{r+d_j}`. For $`a_j`: $`\sum a_j=\frac2{Z_r}Z_r=2`; $`\mathcal E=\sum_j\frac{4}{Z_r^2(r+d_j)}=\frac4{Z_r}`.

*D3.6.2* $`r+d_j=2r+jD`; summand decreasing: $`\frac1{2r+jD}\ge\int_j^{j+1}\frac{dx}{2r+Dx}`, so $`Z_r\ge\frac1D\log\frac{2r+D(m+1)}{2r+D}`. $`m+1>(C_{\rm pad}-1)r/D` => $`2r+D(m+1)>(C_{\rm pad}+1)r`; $`r\ge1` => $`2r+D\le(2+D)r`. Ratio $`>(C_{\rm pad}+1)/(2+D)`, positive since $`C_{\rm pad}>D+1`.

*D3.6.3* $`r+d_j\ge2r+D\ge D+2`, so $`a_j\le\frac{2}{Z_r(D+2)}\le\frac{2D}{(D+2)\log\frac{C_{\rm pad}+1}{2+D}}\to0`.

_Formal route_ (RefactoringResult.md §5, D3.6.2): `log((2r+(j+1)D)/(2r+jD)) ≤ D/(2r+jD)` from `log x ≤ x − 1`, telescoped (`eq_initial_harmonic_weights`). Reason: same inequality, no integrals.

_Used from._ {bpref "D3.5"}[D3.5].

:::

:::lemma_ "D3.7" (lean := "AreaLaw.step_3_7")
*D3.7* — Step eq:initial-filter-commutation: Optimized filters commute with their marginals

Lines 335–382. Labels `eq:initial-filter-constraints` (341–344), `eq:initial-filter-commutation` (355–358).

Fix $`\epsilon>0` with $`(\dim\mathcal H_{X_j})\epsilon^{2/a_j}<1` for all $`j`. Maximize $`N=\|L_m\cdots L_1\Omega\|` over positive operators $`L_j` on $`\mathcal H_{X_j}` with $$`L_j\ge\epsilon\,\mathrm{id},\qquad\operatorname{Tr}L_j^{2/a_j}=1 .` A maximizer exists, $`N>0`. With $`K=L_m\cdots L_1`, $`\phi=K\Omega/N`: $`[L_j,\rho_{\phi,X_j}]=0` for $`1\le j\le m`.

:::

:::proof "D3.7" (uses := "D3.5, D3.6")
*D3.7.1* _Existence._ Feasible set of each $`L_j` nonempty (raise one eigenvalue above $`\epsilon` until trace $`1`; slack allows it), compact ($`L_j\le1` since $`\operatorname{Tr}L_j^{2/a_j}=1`); $`N` continuous. Feasible products invertible => $`N>0`.

*D3.7.2* _Descending induction on $`j`._ Assume claim for indices $`>j`. Anti-Hermitian $`B` on $`X_j`: $`L_j(t)=e^{tB}L_je^{-tB}` keeps both constraints (same spectrum). $`\frac d{dt}L_j(t)|_0=(B-L_jBL_j^{-1})L_j`, so with $`K_{>j}=L_m\cdots L_{j+1}` $$`\frac d{dt}\log N\Big|_0=\operatorname{Re}\langle\phi,K_{>j}(B-L_jBL_j^{-1})K_{>j}^{-1}\phi\rangle=0 .`

*D3.7.3* _Peeling outer filters._ Operator inside, conjugated by $`L_m`, is supported on $`X_m` (inner filters and $`B` live on regions $`\subseteq X_m`). $`\langle\phi,L_mWL_m^{-1}\phi\rangle=\operatorname{Tr}(\rho_{\phi,X_m}L_mWL_m^{-1})=\operatorname{Tr}(L_m^{-1}\rho_{\phi,X_m}L_mW)=\operatorname{Tr}(\rho_{\phi,X_m}W)` by induction hypothesis. Repeat down to $`L_{j+1}`. Left: $`\operatorname{Re}\operatorname{Tr}\rho_{\phi,X_j}(B-L_jBL_j^{-1})=0`.

*D3.7.4* $`\operatorname{Tr}(\rho B)` imaginary ($`\rho=\rho^*`, $`B=-B^*`), so $`\operatorname{Re}\operatorname{Tr}(L_j^{-1}\rho_{\phi,X_j}L_jB)=0` for all anti-Hermitian $`B`. $`Y=L_j^{-1}\rho L_j=Y_h+Y_a` (Hermitian + anti-Hermitian). $`\operatorname{Tr}(Y_hB)` imaginary; $`B=Y_a`: $`\operatorname{Re}\operatorname{Tr}Y_a^2=-\|Y_a\|_2^2=0`. So $`Y=Y^*`: $`L_j^{-1}\rho L_j=L_j\rho L_j^{-1}`, $`\rho L_j^2=L_j^2\rho`, $`L_j=(L_j^2)^{1/2}` commutes with $`\rho`.

_Used from._ {bpref "D3.5"}[D3.5], {bpref "D3.6"}[D3.6].

:::

:::lemma_ "D3.8" (lean := "AreaLaw.step_3_8")
*D3.8* — Step eq:initial-filter-clipping: Clipping bounds log-ratios of filter eigenvalues

Lines 384–405. Label `eq:initial-filter-clipping` (397–403).

In a common eigenbasis of $`L_j` and $`\rho_{\phi,X_j}` with eigenvalues $`l_i` and $`p_i`: for $`p_i,p_k>0`, $$`\Big|\log\frac{l_i}{l_k}\Big|\le\frac{a_j}2\Big|\log\frac{p_i}{p_k}\Big| .`

:::

:::proof "D3.8" (uses := "D3.7")
*D3.8.1* $`x_i=l_i^{2/a_j}`. Diagonal variation of $`L_j` and the peeling of {bpref "D3.7"}[D3.7.3] give $`d\log N=\sum_ip_i\,dl_i/l_i=\frac{a_j}2\sum_ip_i\frac{dx_i}{x_i}`, subject to $`\sum x_i=1`, $`x_i\ge\epsilon^{2/a_j}`.

*D3.8.2* KKT at the maximizer on $`\{\sum x_i=1,\ x_i\ge\epsilon^{2/a_j}\}` (necessary only; no concavity): $`p_i/x_i=\lambda` on free coordinates, $`\le\lambda` on floored. Free coordinate exists: all floored => $`\sum x_i=\dim\cdot\epsilon^{2/a_j}<1`. $`\lambda\ge0` as $`p_i\ge0`. $`\lambda>0`: if $`\lambda=0`, free coordinates have $`p_i=0`; $`\sum p_i=1` => some floored $`k` has $`p_k>0`; moving mass from a free coordinate to $`k` raises $`d\log N`; contradiction.

*D3.8.3* Hence $`x_i=\max\{\epsilon^{2/a_j},p_i/\lambda\}`. $`s\mapsto\log\max\{\epsilon^{2/a_j},e^s\}` is 1-Lipschitz => $`|\log(x_i/x_k)|\le|\log(p_i/p_k)|`. Multiply by $`a_j/2` ($`l=x^{a_j/2}`).

_Used from._ {bpref "D3.7"}[D3.7].

:::

:::lemma_ "D3.9" (lean := "AreaLaw.step_3_9")
*D3.9* — Step eq:initial-product-energy: The optimized vector has small excitation energy

Lines 407–442. Label `eq:initial-product-energy` (437–440).

With $`a_j\le\frac12` ({bpref "D3.6"}[D3.6]): $$`0\le\langle\phi,(H-E_0)\phi\rangle\le C\,\mathcal E,` $`C=C(q,R,J)`, independent of $`m`, of $`C_{\rm pad}`, of the floor and of the dimensions of the $`X_j`.

:::

:::proof "D3.9" (uses := "D3.5, D3.7, D3.8, D3.6, D2.10, D3.1")
*D3.9.1* $`KHK^{-1}\phi=E_0\phi` ($`H\Omega=E_0\Omega`, $`K` invertible). So $`\langle\phi,(H-E_0)\phi\rangle=\sum_h\operatorname{Re}\langle\phi,(h-KhK^{-1})\phi\rangle`.

*D3.9.2* _Reduction for fixed $`h`, support $`S_h`._ $`I_{\rm in}=\{i:X_i\cap S_h=\varnothing\}`, $`I_{\rm out}=\{i:X_i\supseteq S_h\}`. By {bpref "D3.5"}[D3.5](d) and nesting: $`I_{\rm in}=\{1,\dots,j-1\}`, $`I_{\rm out}=\{j+1,\dots,m\}`, at most one $`j` in neither (split). $`I_{\rm in}` filters commute with $`h`, innermost in $`KhK^{-1}`. $`I_{\rm out}` filters: peel in descending order by {bpref "D3.7"}[D3.7] and cyclicity (operator inside supported in $`X_i\supseteq S_h\cup X_{i-1}`). No split index: contribution $`0`. Else $`\operatorname{Re}\langle\phi,(h-L_jhL_j^{-1})\phi\rangle`.

*D3.9.3* _Split term in Schmidt bases._ $`h=\sum_\alpha c_\alpha\otimes d_\alpha` ($`c_\alpha` on $`S_h\cap X_j`). Schmidt form of $`\phi` for $`X_j\mid X_j^c`: $`\phi=\sum_i\sqrt{p_i}\,e_i\otimes g_i`, $`e_i` common eigenbasis of $`\rho_{\phi,X_j}` and $`L_j` ({bpref "D3.7"}[D3.7]). $`H_{ik}=\sum_\alpha(c_\alpha)_{ik}(d_\alpha)_{ik}` ($`(ii,kk)` matrix element of $`h`; $`H_{ki}=\overline{H_{ik}}`): $$`\operatorname{Re}\langle\phi,(h-L_jhL_j^{-1})\phi\rangle=-\sum_{i,k}\sqrt{p_ip_k}\Big(\cosh\log\frac{l_i}{l_k}-1\Big)\operatorname{Re}H_{ik},` pairing $`(i,k)` with $`(k,i)`: $`\operatorname{Re}[(\tfrac{l_i}{l_k}-1)H_{ik}+(\tfrac{l_k}{l_i}-1)\overline{H_{ik}}]=(\tfrac{l_i}{l_k}+\tfrac{l_k}{l_i}-2)\operatorname{Re}H_{ik}`, $`t+1/t-2=2(\cosh\log t-1)`. Terms with $`p_ip_k=0` vanish.

*D3.9.4* _Coefficient bound._ $`p_i,p_k>0`, $`z=\frac12\log(p_i/p_k)`. {bpref "D3.8"}[D3.8]: $`\cosh\log\frac{l_i}{l_k}\le\cosh(a_jz)`. Taylor termwise: $`\cosh t-1\le\frac12t^2\cosh t`. $`\sqrt{p_ip_k}=\frac{p_i+p_k}{2\cosh z}`. With $`a_j\le\frac12`: $$`\sqrt{p_ip_k}\,(\cosh(a_jz)-1)\le\frac{a_j^2}4(p_i+p_k)\frac{z^2\cosh(z/2)}{\cosh z}\le C a_j^2(p_i+p_k),` since $`\sup_z z^2\cosh(z/2)/\cosh z\le\sup_z2z^2e^{-|z|/2}=32/e^2<4.4`.

*D3.9.5* _Row/column sums._ As {bpref "D3.1"}[D3.1.6]: $`\sum_{i,k}(p_i+p_k)|(c_\alpha)_{ik}(d_\alpha)_{ik}|\le2\|c_\alpha\|\|d_\alpha\|`; {bpref "D2.10"}[D2.10]: $`\sum_\alpha\|c_\alpha\|\|d_\alpha\|\le q^{2v_R}J`. Split term $`\le Ca_j^2`, $`C=C(q,R,J)`.

*D3.9.6* _Sum._ Each support split by at most one $`X_j` ({bpref "D3.5"}[D3.5](d)); $`\le C(r+d_j)` split by $`X_j` ({bpref "D3.5"}[D3.5](e)). Total $`\le C\sum_j(r+d_j)a_j^2=C\mathcal E`.

_Used from._ {bpref "D3.5"}[D3.5], {bpref "D3.7"}[D3.7], {bpref "D3.8"}[D3.8], {bpref "D3.6"}[D3.6]; {bpref "D2.10"}[D2.10] (product decomposition, $`\sum_\alpha\|c_\alpha\|\|d_\alpha\|\le q^{2v_R}J`); row/column Cauchy–Schwarz of {bpref "D3.1"}[D3.1.6].

:::

:::lemma_ "D3.10" (lean := "AreaLaw.eq_initial_weight_range")
*D3.10* — Step eq:initial-weight-range: Final choice of $`C_{\rm pad}`

Lines 444–459. Label `eq:initial-weight-range` (448–453).

Fix $`C_{\rm pad}=C_{\rm pad}(q,R,J,\Delta)` so large that for all $`r\ge1`, $`m`, $`j`: (i) $`C\mathcal E/\Delta\le\frac14` ($`C` of {bpref "D3.9"}[D3.9]), hence $`|\langle\Omega,\phi\rangle|^2\ge1-C\mathcal E/\Delta\ge\frac34`; (ii) $`a_j\le\frac12`; (iii) $`\dfrac{a_j}{1-a_j}\le\dfrac1{32\sqrt{(1+J/\Delta)\mathcal B_j}}`.

:::

:::proof "D3.10" (uses := "D3.5, D3.6, D3.9, D3.1")
*D3.10.1* (i): $`\mathcal E\le4D/\log\frac{C_{\rm pad}+1}{2+D}` ({bpref "D3.6"}[D3.6]), $`C` independent of $`C_{\rm pad}` ({bpref "D3.9"}[D3.9]).

*D3.10.2* (iii): LHS $`\le2a_j\le\frac4{Z_r(r+d_j)}\le\frac{4D}{\log\frac{C_{\rm pad}+1}{2+D}}\cdot\frac1{r+d_j}`. RHS $`\ge c\,(r+d_j)^{-1/2}` since $`\mathcal B_j\le C(r+d_j)` ({bpref "D3.5"}[D3.5](e)), $`c=c(q,R,J,\Delta)>0`. $`r+d_j\ge1` => $`(r+d_j)^{-1}\le(r+d_j)^{-1/2}`, so $`\frac{4D}{\log((C_{\rm pad}+1)/(2+D))}\le c` suffices.

_Used from._ {bpref "D3.5"}[D3.5](e), {bpref "D3.6"}[D3.6], {bpref "D3.9"}[D3.9], {bpref "D3.1"}[D3.1] (range of $`u`).

:::

:::lemma_ "D3.11" (lean := "AreaLaw.step_3_11")
*D3.11* — Step eq:initial-norm-lower: First norm comparison (lower bound on $`-2\log N`)

Lines 461–495. Label `eq:initial-norm-lower` (491–494).

For the floor-$`\epsilon` maximizer, $$`-2\log N\ \ge\ \sum_{j=1}^ma_jS(X_j)-C(m+1)\mathcal E,` $`C` independent of the floor $`\epsilon`.

:::

:::proof "D3.11" (uses := "D3.7, D3.9, D3.10, D3.1, D3.2, D3.5")
*D3.11.1* _Prefix problems._ $`N_j` = optimum with filters $`1,\dots,j` only (same floor, constraints), $`N_0=1`, $`N=N_m`. {bpref "D3.7"}[D3.7]–{bpref "D3.10"}[D3.10] apply to each prefix (cost $`\sum_{i\le j}(r+d_i)a_i^2\le\mathcal E`): prefix maximizer $`\phi_j` has $`|\langle\Omega,\phi_j\rangle|\ge\sqrt{1-C\mathcal E}`, $`C\mathcal E\le\frac14` (rename $`C\to C/\Delta`).

*D3.11.2* _Telescoping._ $`L_1,\dots,L_j` prefix maximizer, $`K_{<j}=L_{j-1}\cdots L_1`, $`\phi_j=L_jK_{<j}\Omega/N_j`: $$`\sqrt{1-C\mathcal E}\,N_j\le|\langle\Omega,L_jK_{<j}\Omega\rangle|=|\langle L_j\Omega,K_{<j}\Omega\rangle|\le\|L_j\Omega\|\,N_{j-1},` by $`L_j=L_j^*` and feasibility of $`K_{<j}` for prefix $`j-1`.

*D3.11.3* _Hölder._ $`\|L_j\Omega\|^2=\operatorname{Tr}\rho_{\Omega,X_j}L_j^2\le(\operatorname{Tr}\rho_{\Omega,X_j}^{1/(1-a_j)})^{1-a_j}`: Schatten Hölder, exponents $`1/(1-a_j)`, $`1/a_j`; $`\|L_j^2\|_{1/a_j}=(\operatorname{Tr}L_j^{2/a_j})^{a_j}=1`.

*D3.11.4* _Lemma 3.1 at $`u=-a_j/(1-a_j)`._ $`1-u=\frac1{1-a_j}`, so $`\operatorname{Tr}\rho^{1/(1-a_j)}=\mathbb Ee^{uK}`; $`u` admissible by {bpref "D3.10"}[D3.10](iii). $`\log\|L_j\Omega\|^2\le(1-a_j)[uS(X_j)+512e\vartheta\mathcal B_ju^2]=-a_jS(X_j)+\frac{512e\vartheta\mathcal B_ja_j^2}{1-a_j}\le-a_jS(X_j)+C(r+d_j)a_j^2` ($`a_j\le\frac12`, $`\vartheta=J/\Delta`, {bpref "D3.5"}[D3.5](e)).

*D3.11.5* _Sum._ $`\log N=\sum_j\log(N_j/N_{j-1})\le\sum_j\big[\tfrac12\log\|L_j\Omega\|^2-\tfrac12\log(1-C\mathcal E)\big]`. Multiply by $`-2`, use $`\sum_j(r+d_j)a_j^2=\mathcal E` and $`-\log(1-v)\le2v` for $`v=C\mathcal E\le\frac14`: $$`-2\log N\ge\sum_ja_jS(X_j)-C\mathcal E-2mC\mathcal E\ge\sum_ja_jS(X_j)-C'(m+1)\mathcal E .`

_Used from._ {bpref "D3.7"}[D3.7], {bpref "D3.9"}[D3.9], {bpref "D3.10"}[D3.10], {bpref "D3.1"}[D3.1] (at $`u=-a_j/(1-a_j)`), {bpref "D3.2"}[D3.2]/{bpref "D3.5"}[D3.5](e).

:::

:::lemma_ "D3.12" (lean := "AreaLaw.eq_initial_trial_norm")
*D3.12* — Step eq:initial-trial-norm: Zero-floor limit and the trial-norm bound

Lines 497–562. Label `eq:initial-trial-norm` (524–527).

(a) As $`\epsilon\downarrow0`, $`N_\epsilon` converges to $`N`, the maximum of $`\|L_m\cdots L_1\Omega\|` over $`L_j\ge0` on $`X_j` with $`\operatorname{Tr}L_j^{2/a_j}=1`; {bpref "D3.11"}[D3.11] holds for this $`N`. (b) Schmidt form $`\Omega=\sum_i\sqrt{p_i}\,u_i\otimes w_i` at $`X\mid X^c`, $`p_i>0`; $`T_j=X_j\setminus X`. For each $`i`: $`N\ge\sqrt{p_i}\,N_i`, $`N_i:=\sup\|M_m\cdots M_1w_i\|` over $`M_j\ge0` on $`T_j`, $`\operatorname{Tr}M_j^{2/a_j}=1`. (c) $$`\log N_i\ \ge\ -\frac12\sum_ja_jS_{w_i}(T_j).`

:::

:::proof "D3.12" (uses := "D3.5, D3.7, D3.11")
*D3.12.1* _(a)._ Feasible sets shrink as $`\epsilon` grows: $`N_\epsilon` increases as $`\epsilon\downarrow0`, bounded by $`N`. Each feasible $`L_j\ge0` is a limit of strictly positive trace-normalized operators; their minimal eigenvalues as floors give $`\liminf N_\epsilon\ge N`. RHS of {bpref "D3.11"}[D3.11] is $`\epsilon`-independent => passes to the limit.

*D3.12.2* _(b)._ $`L_j=|u_i\rangle\langle u_i|\otimes M_j` feasible: $`\operatorname{Tr}L_j^{2/a_j}=\operatorname{Tr}|u_i\rangle\langle u_i|\cdot\operatorname{Tr}M_j^{2/a_j}=1`. Projector on $`X`, $`M_j` on $`T_j\subseteq X^c`: $`L_m\cdots L_1\Omega=\sqrt{p_i}\,u_i\otimes M_m\cdots M_1w_i`. Take sup.

*D3.12.3* _(c), interpolation._ Fix strictly positive feasible $`M_j`. $`F_i(z)=M_m^z\cdots M_1^zw_i` bounded analytic on $`0\le\operatorname{Re}z\le1`; norm $`1` on $`\operatorname{Re}z=0` (unitaries).

*D3.12.4* _Boundary $`\operatorname{Re}z=1`._ $`U_j=M_j^{iy}`, $`V_j=U_j\cdots U_1`, $`V_0=\mathrm{id}`. Move unitaries left ($`U_2M_2U_1M_1=U_2U_1\cdot U_1^*M_2U_1\cdot M_1`): $$`M_m^{1+iy}\cdots M_1^{1+iy}=(U_m\cdots U_1)\,(V_{m-1}^*M_mV_{m-1})\cdots(V_0^*M_1V_0).` $`V_{j-1}` supported in $`T_{j-1}\subseteq T_j`, so $`V_{j-1}^*M_jV_{j-1}` positive on $`T_j`, same spectrum, feasible. Leftmost unitary isometric: $`\|F_i(1+iy)\|\le N_i`.

*D3.12.5* _Three lines, derivative._ Vector three-lines (test against unit vectors): $`\log\|F_i(x)\|\le x\log N_i`, $`x\in[0,1]`, equality at $`x=0` ($`\|w_i\|=1`). Right derivative: $`\frac d{dx}\log\|F_i(x)\|\big|_{0^+}=\sum_j\langle w_i,\log M_j\,w_i\rangle\le\log N_i`.

*D3.12.6* _Choice of $`M_j`._ $`M_j=\big((1-\delta)\rho_{w_i,T_j}+\frac\delta{\dim\mathcal H_{T_j}}\mathrm{id}\big)^{a_j/2}`, $`0<\delta<1`: strictly positive, $`\operatorname{Tr}M_j^{2/a_j}=1`. $`\langle w_i,\log M_jw_i\rangle=\frac{a_j}2\sum_kp_k\log\big((1-\delta)p_k+\frac\delta{\dim}\big)\to\frac{a_j}2\sum_{p_k>0}p_k\log p_k=-\frac{a_j}2S_{w_i}(T_j)` as $`\delta\downarrow0` (zero weight on kernel). Gives (c).

_Formal route_ (RefactoringResult.md §5, D3.12.5): `‖F(x)‖² ≤ B^{2x}` on (0,1), equality at 0, so the right slope of `‖F‖² − B^{2x}` at 0 is ≤ 0: `2 Re⟨ξ, ∑ log M_j ξ⟩ ≤ 2 log B` (`step_3_12_5`, AreaLawRefactored/S03\_InitialBox/ThreeLines.lean:206). Reason: same inequality; avoids `log` of a possibly vanishing norm.

_Formal route_ (RefactoringResult.md §5, D3.12.6): the lower bound `⟨w, log M_j w⟩ ≥ (a_j/2)(log(1−δ) − S_w(T_j))` for each δ (`step_3_12_6`, AreaLawRefactored/S03\_InitialBox/TrialNorm.lean:31), then δ ↓ 0 in `eq_initial_trial_norm` (:98). Reason: only the inequality is needed.

_Used from._ {bpref "D3.5"}[D3.5](a) ($`T_1\subseteq\dots\subseteq T_m`), {bpref "D3.7"}[D3.7], {bpref "D3.11"}[D3.11]; vector three-lines \[Tao, 247A Notes 1, Lemma 5.10\].

:::

:::lemma_ "D3.13" (lean := "AreaLaw.eq_initial_norm_upper")
*D3.13* — Step eq:initial-norm-upper: Schmidt-averaged upper bound on $`-2\log N`

Lines 564–573. Label `eq:initial-norm-upper` (570–573).

$$`-2\log N\ \le\ S(X)+\sum_{j=1}^ma_jS(T_j) .`

:::

:::proof "D3.13" (uses := "D3.12")
*D3.13.1* From $`N\ge\sqrt{p_i}N_i` and {bpref "D3.12"}[D3.12](c): $`-2\log N\le-\log p_i+\sum_ja_jS_{w_i}(T_j)` for every $`i`.

*D3.13.2* Average with weights $`p_i`: $`\sum_ip_i(-\log p_i)=S(X)`; concavity: $`\sum_ip_iS_{w_i}(T_j)\le S(\sum_ip_i\rho_{w_i,T_j})`; $`\sum_ip_i|w_i\rangle\langle w_i|=\operatorname{Tr}_X|\Omega\rangle\langle\Omega|` => $`\sum_ip_i\rho_{w_i,T_j}=\rho_{\Omega,T_j}`, entropy $`S(T_j)`.

_Formal route_ (RefactoringResult.md §5, D3.13.2): all `i`, with `ξ_i = φ_i/‖φ_i‖` for `φ_i = (|u_i⟩⟨u_i| ⊗ 1)Ω` and `ξ_i = Ω` where `p_i = 0` (weight 0) (`eq_initial_norm_upper`, AreaLawRefactored/S03\_InitialBox/TrialNorm.lean:138). Reason: avoids a subtype of positive eigenvalues.

_Used from._ {bpref "D3.12"}[D3.12].

:::

:::lemma_ "D3.14" (lean := "AreaLaw.step_3_14")
*D3.14* — Step: Conclusion of Lemma 3.2

Lines 574–586.

$`S(X\mid T)\le\frac12S(X)+C_{\rm buf}r` for $`C_{\rm buf}=C_{\rm buf}(q,R,J,\Delta)`.

:::

:::proof "D3.14" (uses := "D3.11, D3.12, D3.13, D3.5, D3.6, D2.2")
*D3.14.1* {bpref "D3.11"}[D3.11] (limit form) and {bpref "D3.13"}[D3.13]: $`\sum_ja_jS(X_j)-C(m+1)\mathcal E\le-2\log N\le S(X)+\sum_ja_jS(T_j)`.

*D3.14.2* $`X_j=X\sqcup T_j` so $`S(X_j)-S(T_j)=S(XT_j)-S(T_j)=S(X|T_j)`. Hence $$`\sum_ja_jS(X\mid T_j)\le S(X)+C(m+1)\mathcal E .`

*D3.14.3* $`T_1\subseteq\dots\subseteq T_m`, SSA ({bpref "D2.2"}[D2.2] item 2): $`S(X|T_j)\ge S(X|T_m)`. $`a_j>0`, $`\sum a_j=2`: $`\sum_ja_jS(X|T_j)\ge2S(X|T_m)` (also when $`S(X|T_m)<0`).

*D3.14.4* $`T_m\subseteq T` ($`d_m\le C_{\rm pad}r`) => $`S(X|T)\le S(X|T_m)` (SSA). So $`S(X|T)\le\frac12S(X)+\frac12C(m+1)\mathcal E`.

*D3.14.5* $`m+1\le(C_{\rm pad}/D+1)r` ($`r\ge1`), $`\mathcal E\le4/Z_r` bounded ({bpref "D3.6"}[D3.6]), all parameters fixed: error $`\le C_{\rm buf}r`.

_Used from._ {bpref "D3.11"}[D3.11], {bpref "D3.12"}[D3.12](a), {bpref "D3.13"}[D3.13], {bpref "D3.5"}[D3.5](a), {bpref "D3.6"}[D3.6]; {bpref "D2.2"}[D2.2] item 2 (SSA).

:::

:::definition "D3.15" (lean := "AreaLaw.F_box")
*D3.15* — Def: $`F_{\rm box}(r)`

Lines 588–594.

For an integer $`r\ge1`, $$`F_{\rm box}(r)=\sup S_\Omega(A\cap Q),` sup over admissible $`H` (unique ground vector, gap $`\Delta`), domains $`\Lambda`, cuts $`A\subseteq\Lambda`, safe ({bpref "D3.3"}[D3.3], relative to $`A`) integer rectangles $`Q` of size $`\le r`; $`q,R,J,\Delta` fixed. $`F_{\rm box}` nondecreasing, $`0\le F_{\rm box}(r)\le r^2\log q`.

:::

:::proof "D3.15" (uses := "D3.3, D1.2, D1.3, D1.4")
$`|A\cap Q|\le r^2`, $`S\le|A\cap Q|\log q`; larger $`r` allows more rectangles.

_Formal route_ (RefactoringResult.md §5, D3.15): sup also over `D₀ > 2R+10` (`AreaLaw.F_box`, S03\_InitialBox.lean:165). Reason: the frozen `InitialBoxEstimate` puts `∃ C e₀` before `∀ D₀`, and `D₀` is real.

_Used from._ {bpref "D3.3"}[D3.3], {bpref "D1.2"}[D1.2]–{bpref "D1.4"}[D1.4].

:::

:::proposition "D3.16" (lean := "AreaLaw.prop_3_3")
*D3.16* — Proposition 3.3: Initial safe-box estimate

Lines 596–668 (statement 596–604, proof 606–668). Label `prop:initial-box`; claim `eq:initial-box-bound` (600–603); recursion `eq:initial-box-recursion` (637–642).

There are $`C<\infty` and $`e_0\in(0,1)`, depending only on $`q,R,J,\Delta`, with $$`F_{\rm box}(r)\le C\,r^{1+e_0}\qquad(r\ge1).`

:::

:::proof "D3.16" (uses := "D3.4, D3.15, D3.3, D2.1, D2.2")
*D3.16.1* _Children._ Integer $`M\ge2` (chosen D3.16.5). $`Q` safe parent, size $`\le Mr`. $`\operatorname{size}(Q)\le r`: $`S_\Omega(A\cap Q)\le F_{\rm box}(r)`. Else cut each axis into chunks of $`r` sites plus possibly one shorter final chunk: $`\le M` chunks per axis, $`\le M^2` children $`Q_i` (chunk products), $`\operatorname{size}(Q_i)\le r`, $`\operatorname{dist}_\infty(Q_i,Z)\ge\operatorname{dist}_\infty(Q,Z)>D_0\operatorname{size}(Q)\ge D_0\operatorname{size}(Q_i)`: safe. $`X_i=A\cap Q_i` partition $`A\cap Q`.

*D3.16.2* _Noninterior children._ $`Q_i` interior iff $`Q_i^{+C_{\rm pad}r}\subseteq Q`. Chunk position $`a\in\{1,\dots,n\}` on an axis, $`n\le M`: left containment needs $`a\ge C_{\rm pad}+1`; right holds if $`a\le n-C_{\rm pad}-1` (parent has $`\ge(n-1)r+1` sites). Violating positions per axis: $`a\le C_{\rm pad}` or $`a\ge n-C_{\rm pad}`, $`\le2(C_{\rm pad}+2)`. Noninterior $`\le2\cdot2(C_{\rm pad}+2)\cdot M=B_M:=4(C_{\rm pad}+2)M`. Thin parent ($`n\le2(C_{\rm pad}+2)` on an axis): all $`\le M^2` children may be noninterior; still counted, that axis contributing $`\le2(C_{\rm pad}+2)` positions times $`\le M` on the other.

*D3.16.3* _Random order._ Interior child: $`Q_i^{+C_{\rm pad}r}` meets $`\le(2C_{\rm pad}+5)^2-1` other children. Uniform random permutation of children. $`E_i`: $`Q_i` after all children meeting its padded rectangle; $`\Pr(E_i)\ge p_0:=(2C_{\rm pad}+5)^{-2}>0` ($`i` last among $`\le(2C_{\rm pad}+5)^2`). On $`E_i`: $`T=(A\cap Q_i^{+C_{\rm pad}r})\setminus X_i\subseteq X_{<i}` (union of earlier children). Chain rule, any order: $`S(A\cap Q)=\sum_iS(X_i|X_{<i})`. On $`E_i`: $`S(X_i|X_{<i})\le S(X_i|T)\le\frac12S(X_i)+C_{\rm buf}r` (SSA; Lemma 3.2, $`Q_0=Q_i`, parent $`Q` safe). Otherwise and for noninterior $`i`: $`S(X_i|X_{<i})\le S(X_i)`.

*D3.16.4* _Recursion_ (eq:initial-box-recursion). Average over orders. Interior $`i`: $`\mathbb E\,S(X_i|X_{<i})\le S(X_i)-\Pr(E_i)\big(\tfrac12S(X_i)-C_{\rm buf}r\big)\le(1-\tfrac{p_0}2)S(X_i)+C_{\rm buf}r`, by $`\Pr(E_i)\ge p_0` on the negative term (needs $`S(X_i)\ge0`), $`\Pr(E_i)\le1` on the error; no equality of $`\Pr(E_i)` across children needed. With $`S(X_i)\le F_{\rm box}(r)`, $`n_{\rm non}\le B_M`, $`n_{\rm int}+n_{\rm non}\le M^2`: $$`S(A\cap Q)\le\big[(1-\tfrac{p_0}2)(M^2-n_{\rm non})+n_{\rm non}\big]F_{\rm box}(r)+C_{\rm buf}M^2r\le\big[(1-\tfrac{p_0}2)M^2+\tfrac{p_0}2B_M\big]F_{\rm box}(r)+CM^2r .` Parents of size $`\le r`: same inequality since coefficient $`\ge(1-p_0/2)M^2\ge1` for $`M\ge2`. Sup over $`Q`: eq:initial-box-recursion for $`F_{\rm box}(Mr)`.

*D3.16.5* _Choice of $`M`._ $`M\ge2`, $`M\ge16(C_{\rm pad}+2)`. Then $`B_M=4(C_{\rm pad}+2)M\le M^2/4`, coefficient $`\le(1-\frac{3p_0}8)M^2\le\lambda:=(1-p_0/4)M^2`; $`M<\lambda<M^2` ($`p_0\le\frac1{49}`, $`M\ge48`). So $`F_{\rm box}(Mr)\le\lambda F_{\rm box}(r)+CM^2r`.

*D3.16.6* _Iteration._ $`f_j=F_{\rm box}(M^j)`: $`f_{j+1}\le\lambda f_j+CM^{2+j}`. Divide by $`\lambda^{j+1}`, sum: $`f_j/\lambda^j\le f_0+\frac{CM^2}\lambda\sum_{i<j}(M/\lambda)^i\le f_0+\frac{CM^2}{\lambda-M}`, $`f_0=F_{\rm box}(1)\le\log q`. So $`F_{\rm box}(M^j)\le C\lambda^j`.

*D3.16.7* _Exponent._ $`1+e_0:=\log_M\lambda=2+\frac{\log(1-p_0/4)}{\log M}\in(1,2)`; $`e_0=1+\frac{\log(1-p_0/4)}{\log M}\in(0,1)` since $`0<-\log(1-p_0/4)<\log M`. $`\lambda^j=(M^j)^{1+e_0}`.

*D3.16.8* _General $`r`._ $`j\ge0` with $`M^{j-1}<r\le M^j`. Monotone: $`F_{\rm box}(r)\le F_{\rm box}(M^j)\le C(M^j)^{1+e_0}\le C(Mr)^{1+e_0}\le CM^2r^{1+e_0}`.

_Formal route_ (RefactoringResult.md §5, D3.16 (old code, now fixed)): (Step 1) the paper route, `AreaLaw.step_3_16_4` (S03\_InitialBox.lean:351); the old deterministic colour rotations (OpenAI/RotatedChainRule.lean, ChildColoring.lean) are not used. Reason: old route was drift.

_Used from._ {bpref "D3.4"}[D3.4] ($`C_{\rm pad}`, $`C_{\rm buf}`), {bpref "D3.15"}[D3.15], {bpref "D3.3"}[D3.3]; {bpref "D2.1"}[D2.1] (chain rule $`S(AB)=S(A)+S(B|A)`); {bpref "D2.2"}[D2.2] item 2 (SSA).

:::
