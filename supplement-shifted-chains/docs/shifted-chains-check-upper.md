# Verification note: the uniform upper bound with the arity ramp (key "upper")

Date: 18 October 2026. Nothing under `manuscript/`, `upstream/`, `formalization/`,
or any existing file was changed. New files: this note and
[`experiments/shifted_chains_check_upper.py`](../experiments/shifted_chains_check_upper.py).

## 1. Verdict

The uniform resource theorem of
[round11-ramp-bounds](round11-ramp-bounds.md) is correct as stated, given the
local stage relation (S) of Section 3, which comes from the shifted-chain
map construction and is **not** re-verified here (it belongs to the map
topic). I re-derived every step from scratch:

- (a) the legality condition and the smallest-parent formula with slack
  $0\le e<d$;
- (b) the zero-slack ramp, the identity $F_R=F(R,R)$ with v5's least profile
  $F$, and $F(R,R)^3\ge R^4$ with its polynomial certificate;
- (c) the centered potential bound $s<(19R/8)\mu^L$ and the geometric
  defect bound (6);
- (d) the ideal exponent $\omega_D$ and the gap estimate
  $\omega_D-9/4\le 27/(32(D+1)^2)$, plus a sharper bound with an equally
  short proof;
- (e) the full parameter theorem, including every paid charge and the
  resource bounds $B\le A^2$, $m_*\le A^6$, $r_*<A^{20}$ (in fact
  $r_*<A^{17}$).

No false claim was found. The problems are minor: missing explanations
(what $\Phi$ is relative to v5's pooled exponent, and why $\varepsilon/2$),
one wording slip in a review, a notation clash between the two round-11
notes, and very conservative constants. Section 9 lists them with fixes.

Status labels used below:

- **proved here**: I wrote and checked a complete proof.
- **checked numerically**: confirmed by the script with exact or
  outward-rounded arithmetic on finite cases.
- **taken from the notes unchecked**: used as an input, not verified here.

## 2. Inputs from v5 and from the notes

From v5 (`manuscript/preliminaries.tex`, `maps.tex`, `algorithm-bounds.tex`,
`profile.tex`), cited, not re-proved:

- the tensors $\mathrm{MM}_d$, $B_X(d)$, $C(r,b)$, $S^\sigma_{r,b}$ and
  $Q_{r,b}=S^+_{r,b}S^-_{r,b}$; the facts $Q_{r,b}\cong Q_{b,r}$,
  $Q_{1,1}\cong\mathrm{MM}_1$, $\mathrm R(Q_{r,b})\le(r+b-1)^6$
  (eqs. `balanced`, `balanced-properties`), and
  $\bigotimes_{\pi\in S_3}B_X(d)^\pi\cong\mathrm{MM}_{d^2}$ (eq.
  `coset-dot-products`);
- Lemma `composition`, Lemma `exactification`, and its rational form
  Lemma `rational-interpolation`(a)–(c) (rational convolution decomposition,
  Lü's separator with $2M-1$ copies and degree $\le M-1$, exactification at
  integer nodes);
- Definition `relative-scheme` and Lemma `batch` (pooled recursion,
  exponent $p=\log(r_*/m_*)/\log(B/A)$);
- the least profile $F(m,n)=s_{\min}\bigl(\max+\tfrac{\min-1}{2}\bigr)$,
  $s_m=\prod_{h=1}^{m-1}(1+\tfrac1{3h})$, so $F(R,R)=s_R(3R-1)/2$.

From the notes, **taken unchecked** (map topic):

**(S) Stage relation.** Let $d\ge2$ and let the level $(r,b)\to(c,r)$ be legal
(Definition 1 below). For every $n\ge1$ and every type $(\ell,o,m)$ with
$\ell+o+m=n$, put $M=\frac{n!}{\ell!\,o!\,m!}(d-1)^\ell2^o$. There is a
degeneration with rational coefficients
$$
(2M-1)^6\,Q_{r,b}^{\otimes n}\,\mathrm{MM}_{d^{2n}}
\;\trianglerighteq\;
M^6\,Q_{c,r}^{\otimes n}\,\mathrm{MM}_{M^2},
$$
whose polynomial has degree at most $6(M-1)$.

This is round-8's relation (5) in [round8-multiscale-construction](round8-multiscale-construction.md):
the shifted-chain split of $C(r,b)\otimes B_X(d)$ into $d-1$ kernel
sectors $C(r,c)$ and a quotient $C(r,db-(d-1)c)$, cropped to
$C(r,3c+r-1)$ and tripled into two $C(r,c)$ and one $C(r,c)^{(23)}$;
a type restriction with the same type in all six orientations; Lü's
separator (degree $M-1$) in each orientation; and the swap
$Q_{r,c}\cong Q_{c,r}$. I checked only the bookkeeping. The six oriented
auxiliaries $B_X(d)^{\otimes n}$ give $\mathrm{MM}_{d^{2n}}$, the six separator dot
products give $\mathrm{MM}_{M^2}$, and the six middle-sector parity flips cancel
because $\pi\mapsto\pi(23)$ permutes $S_3$. The degrees add over the six
orientations under one parameter (Lemma `composition`).

## 3. Definitions and the chain scheme

**Definition 1 (legal level).** Let $d\ge2$. A *level of arity $d$* takes
the pair $(r,b)$ to the pair $(c,r)$, where
$$1\le c<b,\qquad (d+2)c\le db-r+1. \tag{L}$$
Here $c<b$ makes the shift $h=b-c\ge1$ possible, and $(d+2)c\le db-r+1$
says that the quotient length $db-(d-1)c$ is at least the tripling width
$3c+r-1$.

**Proposition A (counts of a chain).** *(proved here, given (S))* Let
$x_0,\dots,x_J$ be pairs with $x_J=(1,1)$. Suppose each step
$x_{i-1}\to x_i$ is a legal level of arity $d_i$. Fix integers
$n,k\ge1$, and at level $i$ fix a type of size $n$ with sector count $M_i$.
Write $x_0=(r_0,b_0)$, $s=r_0+b_0-1$, $E_i=1+6k(M_i-1)$, and
$$
A=\prod_i d_i^{2nk},\quad B=\prod_i M_i^{2k},\quad
r_*=s^{6nk}\prod_i(2M_i-1)^{6k}E_i,\quad m_*=\prod_i M_i^{6k}.
$$
Then $r_*\mathrm{MM}_A\trianglerighteq m_*\mathrm{MM}_B$ by maps with
rational coefficients. If $B>A$, this is a relative scheme in v5's sense.

*Proof.* Fix $i$. Apply exactification with power $k$ (v5 Lemma
`exactification`, rational form Lemma `rational-interpolation`(c)) to (S).
The source of (S) is the direct sum $T=(2M_i-1)^6\,Q_{x_{i-1}}^{\otimes n}\mathrm{MM}_{d_i^{2n}}$.
Tensor products distribute over direct sums, and
$\mathrm{MM}_a\mathrm{MM}_b\cong\mathrm{MM}_{ab}$. Hence, with
$\alpha_i=E_i(2M_i-1)^{6k}$ and $\beta_i=M_i^{6k}$,
$$
\alpha_i\,Q_{x_{i-1}}^{\otimes nk}\,\mathrm{MM}_{d_i^{2nk}}
\trianglerighteq
\beta_i\,Q_{x_i}^{\otimes nk}\,\mathrm{MM}_{M_i^{2k}}. \tag{A.1}
$$
Put $A_i=\prod_{j>i}d_j^{2nk}$ and $B_i=\prod_{j\le i}M_j^{2k}$. We show by
induction on $i=0,\dots,J$ that
$$
\Bigl(\prod_{j}\alpha_j\Bigr)Q_{x_0}^{\otimes nk}\mathrm{MM}_A
\trianglerighteq
\Bigl(\prod_{j\le i}\beta_j\Bigr)\Bigl(\prod_{j>i}\alpha_j\Bigr)
Q_{x_i}^{\otimes nk}\,\mathrm{MM}_{A_iB_i}.
$$
The case $i=0$ is the identity. For the step from $i-1$ to $i$, use
$\mathrm{MM}_{A_{i-1}}\cong\mathrm{MM}_{d_i^{2nk}}\mathrm{MM}_{A_i}$.
The right side for $i-1$ is then a direct sum of
$(\prod_{j<i}\beta_j)(\prod_{j>i}\alpha_j)$ groups. Each group consists of
$\alpha_i$ copies of
$Q_{x_{i-1}}^{\otimes nk}\mathrm{MM}_{d_i^{2nk}}\otimes\mathrm{MM}_{A_iB_{i-1}}$.
Apply (A.1), tensored with the identity on $\mathrm{MM}_{A_iB_{i-1}}$,
inside each group. Each group becomes
$\beta_i\,Q_{x_i}^{\otimes nk}\mathrm{MM}_{A_iB_i}$. At $i=J$ we have
$A_J=1$, $B_J=B$, and $Q_{1,1}^{\otimes nk}\cong\mathrm{MM}_1$. So
$(\prod\alpha_j)\,Q_{x_0}^{\otimes nk}\mathrm{MM}_A\trianglerighteq m_*\mathrm{MM}_B$.

Finally, $\mathrm R(Q_{x_0})\le s^6$, and Lemma
`rational-interpolation`(a) gives a rational decomposition. Hence
$s^{6nk}\mathrm{MM}_1\trianglerighteq Q_{x_0}^{\otimes nk}$, and therefore
$r_*\mathrm{MM}_A\trianglerighteq(\prod\alpha_j)Q_{x_0}^{\otimes nk}\mathrm{MM}_A$.
Composing these restrictions proves the claim. $\square$

Every separator copy, the separate exactification at every level, the
source evaluation, and the terminal restriction are inside $r_*$. There is
no catalyst.

**The exponents.** Write $p=\log(r_*/m_*)/\log(B/A)$ for v5's pooled exponent.
If each batch is recursed on its own, without pooling, the exponent is
$p_{\rm fix}=\log\lceil r_*/m_*\rceil/\log(B/A)$. Every factor of $r_*/m_*$
is at least one, so $\lceil r_*/m_*\rceil\le 2r_*/m_*$. Define
$$
\Phi=\frac{\log(2r_*/m_*)}{\log(B/A)}
=\frac{3\log s+\frac3n\sum_i\log(2-\frac1{M_i})+\frac1{2nk}\sum_i\log E_i+\frac{\log2}{2nk}}
{\sum_i\bigl(\frac1n\log M_i-\log d_i\bigr)} .\tag{$\Phi$}
$$
The second form divides the numerator and the denominator by $2nk$. Then
$$p\le p_{\rm fix}\le\Phi,\qquad \Phi=p+\frac{\log 2}{\log(B/A)}.$$
The round-11 notes call $\Phi$ the "complete paid exponent". It is an upper
bound for v5's pooled exponent, and also for the exponent without pooling.
The $\log2$ term is not needed for v5's Lemma `batch`, which removes the
ceiling, but it costs almost nothing.

## 4. Geometry

**Lemma 1 (smallest parent).** *(proved here; checked numerically on
215,600 triples $1\le r,b\le70$, $2\le d\le45$)* Let $d\ge2$ and let $(r,b)$
be a pair. Put
$$\hat b=\Bigl\lceil\frac{(d+2)r+b-1}{d}\Bigr\rceil,\qquad e=d\hat b-(d+2)r-b+1 .$$
Then $0\le e\le d-1$. The level of arity $d$ from $(b,\hat b)$ to $(r,b)$ is
legal, and $\hat b$ is the least integer with this property. Moreover
$\max(b,\hat b)\le\frac52\max(r,b)$.

*Proof.* The range $0\le e\le d-1$ is the definition of the ceiling. With
parent $(b,\hat b)$ and child length $c=r$, condition (L) reads
$1\le r<\hat b$ and $(d+2)r\le d\hat b-b+1$. The second condition is $e\ge0$.
It is equivalent to $\hat b\ge((d+2)r+b-1)/d$, which proves minimality.
Also $d\hat b\ge(d+2)r+b-1\ge(d+2)r>dr$, so $\hat b>r$. For the growth
bound, let $m=\max(r,b)$. Then
$\hat b\le((d+2)r+b-1+d-1)/d\le m+1+(3m-2)/d\le m+1+(3m-2)/2=5m/2$. $\square$

**Lemma 2 (zero-slack ramp).** *(proved here; checked for $R\le300$)* Let
$R\ge1$. Start at $(1,1)$. For $j=1,\dots,R-1$, apply Lemma 1 with arity
$3j-1$ and then with arity $3j$. This produces
$$(j,j)\xleftarrow{\,3j-1\,}(j,j+1)\xleftarrow{\,3j\,}(j+1,j+1),$$
with $e=0$ at every step. Read forwards, it is a chain of $2(R-1)$ legal
levels from $(R,R)$ to $(1,1)$, with largest arity $3R-3$. Its total gain is
$$
F_R:=\prod_{\text{levels}}\frac{d_i+2}{d_i}
=\prod_{j=1}^{R-1}\frac{(3j+1)(3j+2)}{(3j-1)\,3j}
=\frac{3R-1}{2}\,s_R=F(R,R),
$$
and $F(R,R)^3\ge R^4$. Consequently $3\log(2R-1)-\frac94\log F_R<3\log2$.

*Proof.* With $d=3j-1$ and child $(j,j)$:
$\hat b=\lceil((3j+1)j+j-1)/(3j-1)\rceil=\lceil(3j-1)(j+1)/(3j-1)\rceil=j+1$,
and $e=0$. With $d=3j$ and child $(j,j+1)$:
$\hat b=\lceil((3j+2)j+j)/(3j)\rceil=j+1$, and $e=0$. In the product,
$\prod_{j<R}\frac{3j+2}{3j-1}=\prod_{j<R}\frac{3(j+1)-1}{3j-1}$ telescopes
to $(3R-1)/2$, and $\prod_{j<R}\frac{3j+1}{3j}=s_R$.

For the inequality, $F_1=1$. Since $[(3j-1)\,3j]^3=27j^3(3j-1)^3$, the step
$F_{j+1}^3/F_j^3\ge((j+1)/j)^4$ is equivalent, after division by $j^3$, to
$j[(3j+1)(3j+2)]^3-27(j+1)^4(3j-1)^3\ge0$. With $j=u+1$ this polynomial is
$$4544+17936u+27324u^2+20007u^3+7074u^4+972u^5,$$
which is positive for $u\ge0$. The script recomputes these coefficients by
exact polynomial multiplication. It also checks the identity against the
unsubstituted form for $1\le j<200$.

The last claim follows from $F_R\ge R^{4/3}$ and $2R-1<2R$. $\square$

*Remark (link to v5).* The ramp alone, with no bulk, has source $2R-1$ and
gain exactly $F(R,R)$. Its ideal exponent is therefore
$3\log(2R-1)/\log F(R,R)=\tau_R$, v5's profile exponent. The ramp realizes
v5's diagonal profile value exactly, by integer chains, without a
catalyst or a rounding of flows. Used alone, it still needs
$\log R\gtrsim1/\varepsilon$, as in v5. The bulk is what gives a
polynomial source.

**Lemma 3 (bulk potential).** *(proved here; the identity is checked
symbolically in $\mathbb Q(\mu)$ for $D\le30$, $r,b\le25$)* Let $D\ge2$. Let
$\mu>0$ be the root of $D\mu^2-\mu-(D+2)=0$, and put $\eta=\mu-1/D$. Then
$1+1/D<\mu<5/4+1/D$, so $1<\eta<5/4$. Define
$V(r,b)=\eta(r-\tfrac13)+(b-\tfrac13)$. If $(b,\hat b)$ is the smallest
parent of $(r,b)$ for arity $D$, with slack $e$, then
$$V(b,\hat b)=\mu\,V(r,b)+e/D,\qquad 0\le e/D<1.$$
Consequently, let $(r_L,b_L)$ be obtained from $(R,R)$ by $L\ge0$
smallest-parent steps of arity $D$. Then
$$s_L:=r_L+b_L-1<\mu^L\Bigl(\tfrac94R+D\Bigr),$$
and in particular $s_L<\frac{19R}{8}\mu^L$ when $R=8D$.

*Proof.* Put $p(t)=Dt^2-t-(D+2)$. Then $p(1+1/D)=-1$ and
$p(5/4+1/D)=(9D-12)/16>0$, and $p(0)<0$, so the positive root lies in
$(1+1/D,\,5/4+1/D)$. By definition,
$V(b,\hat b)=\eta(b-\tfrac13)+((D+2)r+b-1+e)/D-\tfrac13$. Compare
coefficients with $\mu V(r,b)+e/D$:

- for $b$: $\eta+1/D=\mu$;
- for $r$: $(D+2)/D=\mu\eta=\mu^2-\mu/D$, which is the defining quadratic;
- constants: $-\eta/3-1/D-1/3=-\mu/3-2/(3D)-1/3=-\mu\eta/3-\mu/3$.

Iterating gives
$V_L=\mu^LV(R,R)+\sum_{i=1}^{L}\mu^{L-i}e_i/D<\mu^LV(R,R)+\mu^L/(\mu-1)$.
Here $V(R,R)=(1+\eta)(R-\tfrac13)<\tfrac94R$ and $1/(\mu-1)<D$. Finally,
$\eta>1$ and $r_L\ge1$ give $V_L>r_L+b_L-\tfrac23>s_L$. $\square$

*Why this potential.* The affine reverse map
$(r,b)\mapsto(b,((D+2)r+b-1)/D)$ has fixed point $(\tfrac13,\tfrac13)$.
Its linear part $\begin{psmallmatrix}0&1\\(D+2)/D&1/D\end{psmallmatrix}$ has
Perron root $\mu$ and left Perron vector $(\eta,1)$. So $V$ is the centered
left-eigenvector potential, and the only error is the ceiling, $e/D<1$ per
step. No eigenvector attraction is assumed.

**Lemma 4 (ideal exponent and gap).** *(proved here; checked numerically for
$2\le D\le2000$ and $D=10^4,10^6,10^9$)* Let $D\ge2$, $g_D=\log\frac{D+2}{D}$,
$y=g_D/2$, $t=1/(D+1)$, and $\omega_D=3\log\mu/g_D$. Then
$$\log\mu=y+\operatorname{asinh}\bigl(\tfrac12\sinh y\bigr),$$
and

1. $\omega_D\ge9/4$;
2. $\omega_D\le\frac94+\frac{27}{32(D+1)^2}$ (the notes' estimate);
3. (sharper) $0\le h_D:=3\log\mu-\frac94g_D\le\frac32(\sinh y-y)$. Hence
   $\omega_D-\frac94\le\frac{y^2}8\cosh y<\frac1{7D^2}$, and
   $h_D\le\frac{\cosh y}{4D^3}$.

*Proof.* We have $e^y=\sqrt{(D+2)/D}$, so
$\sinh y=\frac12(e^y-e^{-y})=1/\sqrt{D(D+2)}$. Then
$\tfrac12\sinh y+\sqrt{1+\tfrac14\sinh^2y}=\frac{1+\sqrt{4D^2+8D+1}}{2\sqrt{D(D+2)}}$.
Multiplying by $e^y$ gives $\frac{1+\sqrt{4D^2+8D+1}}{2D}=\mu$. This proves
the identity.

(1) $\operatorname{asinh}(\tfrac12\sinh y)\ge y/2$ is equivalent to
$\tfrac12\sinh y\ge\sinh(y/2)$, that is, to
$\sinh(y/2)\cosh(y/2)\ge\sinh(y/2)$. Hence $3\log\mu\ge\frac92y=\frac94g_D$.

(2) Since $D(D+2)=(D+1)^2-1$, we have $\sinh y=t/\sqrt{1-t^2}$. Also
$g_D=2\operatorname{atanh}t\ge2t$. Using
$\operatorname{asinh}z\le z$, we get
$\omega_D=\frac32+\frac{3\operatorname{asinh}(\sinh y/2)}{g_D}\le\frac32+\frac{3\sinh y}{2g_D}\le\frac32+\frac{3}{4\sqrt{1-t^2}}$.
Next, $1/\sqrt{1-t^2}\le1/(1-t^2)=1+t^2/(1-t^2)\le1+\frac98t^2$ for $t\le1/3$.
Together these give item 2.

(3) $h_D=3\operatorname{asinh}(\tfrac12\sinh y)-\tfrac32y\le\tfrac32(\sinh y-y)$.
Termwise, $(2k+1)!\ge6(2k-2)!$, so
$\sinh y-y=\sum_{k\ge1}y^{2k+1}/(2k+1)!\le\frac{y^3}6\cosh y$. Dividing by
$g_D=2y$ gives $\omega_D-\frac94\le\frac{y^2}8\cosh y$. Finally
$y\le\frac12\cdot\frac2D=\frac1D$ and $y\le\frac12\log2<\frac12$, and
$\cosh\frac12<\frac87$. $\square$

*Why $\omega_D$ is the ideal exponent.* In the bulk, each level contributes
$\log(q/d)=g_D$ to the denominator of ($\Phi$) when type losses are
ignored. By Lemma 3, $3\log s=3L\log\mu+O(\log R)$. Indeed
$V_L\ge\mu^LV(R,R)$ and $s\ge\frac25V$, since $V\le\frac54r+b\le\frac52s$.
So $3\log s/G\to3\log\mu/g_D=\omega_D$ as $L\to\infty$. Numerically,
$\omega_D-\frac94\approx\frac{3y^2}{32}\approx\frac3{32D^2}$, because
$\operatorname{asinh}(\tfrac12\sinh y)=\tfrac y2+\tfrac{y^3}{16}+O(y^5)$.
The notes' $27/(32(D+1)^2)$ is about nine times too large, and item 3
is about $4/3$ times too large. Both are valid.

**Lemma 5 (geometric defect).** *(proved here; checked on 40 integer chains,
including the ten chains $D=2,\dots,1024$, $L=4D$ of the notes)* Let $D\ge2$,
$R=8D$ and $L\ge0$. Build the chain of Lemma 2 from $(1,1)$ to $(R,R)$, then
$L$ further smallest-parent steps of arity $D$. Read forwards, it has
$J=16D-2+L$ legal levels, all arities $d_i\le24D-3$, source $s=r_0+b_0-1$,
and gain
$G:=\sum_i\log\frac{d_i+2}{d_i}=\log F(R,R)+Lg_D$. Moreover
$$
3\log s-\tfrac94G<3\log\tfrac{19}8+Lh_D\le3+\frac{27L}{16D(D+1)^2}.\tag{6}
$$

*Proof.* By Lemma 3, $3\log s<3\log\frac{19R}8+3L\log\mu$. By Lemma 2,
$\frac94\log F(R,R)\ge3\log R$. Subtracting gives the first inequality. For
the second: $19/8<e$, and by Lemma 4(2),
$Lh_D=Lg_D(\omega_D-\frac94)\le\frac{2L}D\cdot\frac{27}{32(D+1)^2}$, using
$g_D\le2/D$. $\square$

The constant startup term $3\log(19/8)$ is what the ramp buys. Without the
ramp, starting the bulk at $(1,1)$ gives $s<\mu^L(\frac32+D)$ by Lemma 3,
and a startup defect of $3\log(D+\frac32)$. That defect is what forces the
extra logarithm in the fixed-arity family.

**Lemma 6 (types).** *(proved here; the exact inequality is checked for every
arity used in the four end-to-end instances)* For $d\ge2$, $n\ge1$, let
$M(n,d)$ be the largest value of $\frac{n!}{\ell!o!m!}(d-1)^\ell2^o$ over
$\ell+o+m=n$. Then
$$\frac{(d+2)^n}{(n+1)^2}\le M(n,d)\le(d+2)^n .$$

*Proof.* By the multinomial theorem these values sum to $(d-1+2+1)^n$.
There are $\binom{n+2}2\le(n+1)^2$ types. $\square$

The maximizer is the greedy choice of the $n$ largest marginals $w_c/j$,
with weights $(d-1,2,1)$. Each category's marginals decrease, so a selection
of the $n$ largest marginals maximizes the product. The script certifies
optimality by the exchange condition. Only the inequality is needed.

## 5. The main theorem (paper-ready)

**Theorem.** *(proved here, given (S); all inequalities checked
numerically on 823 rational allowances and on four complete instances)*
Let $0<\varepsilon\le1$ be rational, and put
$$
D=\bigl\lceil\sqrt{4/\varepsilon}\,\bigr\rceil,\quad R=8D,\quad
L=\lceil 64D/\varepsilon\rceil,\quad x=\frac{128D}\varepsilon,
$$
$$
H=\text{number of binary digits of }\lceil x\rceil,\qquad n=k=\lceil 256DH/\varepsilon\rceil .
$$
Build the chain of Lemma 5. At each level, use a type of maximal sector
count $M_i=M(n,d_i)$. Let $r_*\mathrm{MM}_A\trianglerighteq m_*\mathrm{MM}_B$
be the rational restriction of Proposition A. Then $B>A$, and
$$
p\;\le\;\Phi\;<\;\frac94+\frac{719}{1988}\,\varepsilon\;<\;\frac94+\frac\varepsilon2,
\qquad
\log A<3\cdot10^9\,\varepsilon^{-9/2}\log^3\frac{4096}{\varepsilon},
$$
$$
B\le A^2,\qquad m_*\le A^6,\qquad r_*<A^{17}.
$$
All parameters are computed from $\varepsilon$ by integer arithmetic. For
example, $D$ is the least integer with $D^2\varepsilon\ge4$, found by an
integer square root and one exact comparison.

*Proof.* Write $q_i=d_i+2$.

*Step 0 (parameter facts).* We have $D\ge2$, $D^2\varepsilon\ge4$, and
$x\ge256$. From $2^{H-1}\le\lceil x\rceil<2^H$ we get
$H>\log_2x\ge\log x$, and also $H\le x$. Next, $n\ge2xH$ and
$n+1\le2xH+2\le2x^2+2\le x^3$. So $k=n\ge3$, and $\log(6k)<k$. Since
$L\ge64D$, $J=16D-2+L\le\frac54L$. Every $d_i\le24D-3$, so
$\log q_i<\log(24D)<\log x<H$.

*Step 1 (denominator, and $B>A$).* Let $a=2\log(n+1)/n$. By Lemma 6,
$\frac1n\log M_i\ge\log q_i-a$, so the denominator of ($\Phi$) is at least
$G-Ja$. We also have $a\le6\log x/n\le6H/(2xH)=3/x=\frac{3\varepsilon}{128D}$.
Since $\log(1+u)\ge u/(1+u)$, we get $g_D\ge2/(D+2)$. Hence
$G\ge Lg_D\ge\frac{2L}{D+2}\ge\frac{128D}{(D+2)\varepsilon}\ge\frac{64}\varepsilon$
and $\frac JG\le\frac{5L}4\cdot\frac{D+2}{2L}\le\frac{5D}4$. So
$\theta:=\frac{Ja}G\le\frac{15}{512}\varepsilon<1$. The denominator is at
least $(1-\theta)G>0$, which is $\log(B/A)>0$.

*Step 2 (numerator).* Write the numerator as
$3\log s+C_{\rm sep}+C_{\rm ex}+C_{\rm pool}$. Then:

- $C_{\rm sep}=\frac3n\sum\log(2-\frac1{M_i})\le\frac{3J\log2}n$;
- $C_{\rm ex}=\frac1{2nk}\sum\log E_i\le\frac{J\log(6k)}{2nk}+\frac1{2k}\sum\log q_i$,
  because $E_i\le6kM_i\le6kq_i^n$;
- $C_{\rm pool}=\frac{\log2}{2nk}$.

*Step 3 (reduction).* The numerator is positive and the denominator is at
least $(1-\theta)G$. Hence
$$\Phi-\frac94\le\frac1{1-\theta}\Bigl(\frac{3\log s-\frac94G}{G}+\frac{C_{\rm sep}+C_{\rm ex}+C_{\rm pool}}G+\frac94\theta\Bigr).$$

*Step 4 (each charge, divided by $G$).*

| Charge | Bound | Reason |
| --- | --- | --- |
| geometric, by (6) | $<\frac{33}{128}\varepsilon$ | $\frac3G\le\frac{3\varepsilon}{64}$; $\frac{27L}{16D(D+1)^2G}\le\frac{27(D+2)}{32D(D+1)^2}<\frac{27}{32D^2}\le\frac{27\varepsilon}{128}$, using $D(D+2)<(D+1)^2$ |
| type loss $\frac94\theta$ | $\le\frac{135}{2048}\varepsilon$ | Step 1 |
| separator copies | $<\frac{15}{1024}\varepsilon$ | $\frac{3\log2}n\cdot\frac{5D}4\le\frac{15\log2\,\varepsilon}{1024H}$ |
| exactification, $\log(6k)$ part | $\le\frac{5}{2048}\varepsilon$ | $\frac{J}{2nG}\le\frac{5D}{8n}\le\frac{5\varepsilon}{2048H}$ |
| exactification, $\log q_i$ part | $\le\frac{5}{2048}\varepsilon$ | $\frac{J\log(24D)}{2kG}\le\frac{5DH}{8k}\le\frac{5\varepsilon}{2048}$ |
| pooling ceiling | $<\frac1{128}\varepsilon$ | $\frac{\log2}{2nkG}\le\frac{\log 2\,\varepsilon}{128nk}$ |

The bounds sum to $\frac{719}{2048}\varepsilon$, and
$1-\theta\ge\frac{497}{512}$. So
$\Phi-\frac94<\frac{719}{2048}\cdot\frac{512}{497}\varepsilon=\frac{719}{1988}\varepsilon<\frac\varepsilon2$.

*Step 5 (source size).* Put $\Lambda=\log(4096/\varepsilon)$. We have:

- $D\le2\varepsilon^{-1/2}+1\le3\varepsilon^{-1/2}$;
- $J\le16D+64D/\varepsilon-1\le240\,\varepsilon^{-3/2}$;
- $x\le384\,\varepsilon^{-3/2}$;
- $H\le\log_2(2x)+1\le\frac32\log(2x)+1\le2\log(2x)\le2\log768+3\log\frac1\varepsilon\le3\Lambda$,
  using $\log(2x)\ge\log512>2$ and $768^2<4096^3$;
- $n=k\le2304\,\varepsilon^{-3/2}\Lambda+1\le2305\,\varepsilon^{-3/2}\Lambda$;
- $\log d_i<\log(24D)\le\log(72\varepsilon^{-1/2})\le\Lambda$.

Therefore
$$\log A=2nk\sum_i\log d_i\le2n^2J\Lambda\le2\cdot2305^2\cdot240\,\varepsilon^{-9/2}\Lambda^3=2{,}550{,}252{,}000\,\varepsilon^{-9/2}\Lambda^3 .$$

*Step 6 (other resources).* Let $P=\prod d_i$, so $A=P^{2nk}$ and
$P\ge2^J$. Since $d_i\ge2$, $q_i\le d_i^2$, so $M_i\le d_i^{2n}$. This gives
$B\le A^2$ and $m_*\le A^6$.

By Lemma 1, the larger coordinate grows by at most a factor $\frac52<3$
per reverse step, starting from $(1,1)$. So $s<2\cdot3^J\le6^J<P^3$, and
$s^{6nk}<A^9$.

Next, $2M_i-1<2q_i^n\le d_i^{2n+1}$, so
$\prod(2M_i-1)^{6k}\le P^{6k(2n+1)}=A^{6+3/n}\le A^7$.

Finally, $6k<e^k<4^k\le d_i^{2k}$, so
$E_i\le6kq_i^n<d_i^{2k+2n}$ and $\prod E_i<P^{2k+2n}=A^{1/n+1/k}\le A$.

Hence $r_*<A^{9+7+1}=A^{17}<A^{20}$. $\square$

(The notes prove $r_*<A^{20}$ with the coarser bounds
$\prod(2M_i-1)^{6k}\le A^{9}$ and $\prod E_i<A^2$. Both versions are
correct. The script checks $\log r_*<17\log A$ on actual counts; the
actual ratios are $5.8$ and $4.8$ at $\varepsilon=1,\frac12$.)

**Corollary (allowance $\varepsilon$ instead of $\varepsilon/2$).** For
rational $0<\varepsilon\le\frac12$, apply the theorem to $2\varepsilon$.
This gives $p<\frac94+\varepsilon$ and
$\log A<3\cdot10^9(2\varepsilon)^{-9/2}\log^3\frac{2048}\varepsilon<1.4\cdot10^8\,\varepsilon^{-9/2}\log^3\frac{2048}{\varepsilon}$.
*(proved here; the constant comparison $9\cdot10^{18}<1.96\cdot10^{16}\cdot2^9$ is checked)*

**Robustness to the separator.** With v5's Fourier separator (degree
$(M-1)^2$ per orientation) instead of Lü's, $E_i=1+6k(M_i-1)^2$. Then
$\log E_i\le\log(6k)+2n\log q_i$, and only the $\log q_i$ row doubles, to
$\frac{10}{2048}\varepsilon$. The total becomes
$\frac{724}{1988}\varepsilon<\frac\varepsilon2$. *(proved here, by the same
arithmetic)* The theorem therefore does not depend on the smaller degree of
Lü's separator. It uses Lü's separator only for rationality.

## 6. What $\Phi$ means, and why $\varepsilon/2$

- $\Phi=\log(2r_*/m_*)/\log(B/A)$ is an upper bound. It bounds v5's pooled
  exponent $p$ (Lemma `batch`, $O(n^p)$ operations), and also the exponent
  $\log\lceil r_*/m_*\rceil/\log(B/A)$ of recursion without pooling. The
  difference $\Phi-p=\log2/\log(B/A)$ is below $\varepsilon/128$. The paper
  should state the theorem for $p$, and note that it holds for $\Phi$.
- The notes give no reason for $\varepsilon/2$. It matches v5's use of the
  allowance. v5's Theorem `bounded-seed` and Corollary `seed` need
  $p<\frac94+\varepsilon'/2$: the factor $\Xi$ of the unrolled pooled
  recursion is absorbed into $d_0^{\varepsilon'/2}$, which yields a single
  rational seed with fewer than $d_0^{9/4+\varepsilon}$ products. With
  $p<\frac94+\varepsilon/2$, the same unrolling argument applies verbatim
  to the new scheme. If the paper only wants an algorithm with exponent
  $\frac94+\varepsilon$, it should use the Corollary above instead.
- The proof actually gives $p<\Phi<\frac94+0.3617\,\varepsilon$.

## 7. Numerical checks

Script: `python -I experiments/shifted_chains_check_upper.py` (full run
about 35 s; `--quick` about 2 s). It imports no repository code. Identities
use `int` and `Fraction`. Logarithms are rational intervals: argument
reduction to $[1,2)$, the series $2\operatorname{atanh}z$ with $z\le1/3$, an
explicit tail bound, and outward rounding to 256 bits. No floating point
enters any assertion. Floats appear only in the printed summary.

| Check | Scope | Result |
| --- | --- | --- |
| Lemma 1: slack range, legality, minimality, forward floor returns $r$, growth factor $\le5/2$ | $r,b\le70$, $2\le d\le45$ (215,600 cases) | pass |
| Lemma 2: zero slacks, $F_R=F(R,R)=s_R(3R-1)/2$ exactly, $F_R^3\ge R^4$, $(2R-1)^{12}<2^{12}F_R^9$ | $R\le300$ | pass |
| Polynomial certificate | exact expansion; identity rechecked for $j<200$ | coefficients `4544, 17936, 27324, 20007, 7074, 972` |
| Lemma 3 identity in $\mathbb Q(\mu)$; $p(1+\frac1D)=-1$, $p(\frac54+\frac1D)=\frac{9D-12}{16}$ | $D\le30$, $r,b\le25$ (18,125 cases) | pass |
| Lemma 4 (items 1–3, and the review's $h_D\le3/(8(D+1)^3)$) | $2\le D\le2000$; $D=10^4,10^6,10^9$ | pass; $\max_D(D+1)^3h_D<0.2092$ |
| Lemma 3 bound and (6) on actual integer chains; ramp defect $<3\log2$ | 40 chains, including $R\ne8D$ and $L=0$ | pass; max total defect at $L=4D$ is $1.0933<1.1$ (the notes' claim) |
| Theorem, Steps 0–5, with every row against its stated fraction of $\varepsilon$ | 823 rational $\varepsilon$, including $1/m$ for $m\le400$, $m/400$, $2^{-80}$, $3^{-50}$, $10^{-30}$ | pass; largest computed excess bound $0.2418\varepsilon$; largest ratio of $2n^2J\log(24D)$ to the stated $\log A$ bound $0.056$ |
| End-to-end: actual chain, actual maximal types, exact $M_i$ (up to $1.3\cdot10^6$ bits), Lemma 6 exactly, actual $\Phi$ | $\varepsilon=1,\frac12,\frac14,\frac19$ | see next table |
| $B\le A^2$, $m_*\le A^6$, $r_*<A^{17}$ by logarithms of the actual counts | $\varepsilon=1,\frac12$ | ratios $\log r_*/\log A=5.77,4.84$ |
| Reproduce the first row of the arity-ramp table ($D=2$, $L=100$, $n=512$, $k=256$) | | $\Phi<2.3371327<2.337133$ (published) |

End-to-end instances (actual enclosures of ($\Phi$), not the proof's bounds):

| $\varepsilon$ | $D$ | $L$ | $J$ | $n=k$ | actual $\Phi<$ | proved bound $\frac94+\frac{719}{1988}\varepsilon$ | actual $3\log s-\frac94G<$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 128 | 158 | 4,608 | 2.27992 | 2.61167 | 2.03 |
| 1/2 | 3 | 384 | 430 | 15,360 | 2.26434 | 2.43084 | 2.19 |
| 1/4 | 4 | 1,024 | 1,086 | 49,152 | 2.25758 | 2.34042 | 2.58 |
| 1/9 | 6 | 3,456 | 3,550 | 179,712 | 2.25350 | 2.29019 | 2.90 |

The true excess is about $0.03\,\varepsilon$, about twelve times smaller than
the proved $0.36\,\varepsilon$. The proof is valid but very conservative.

## 8. What was not verified

- The stage relation (S): the shifted-chain maps, the crop and tripling, the
  type restriction removing all cross terms, the six-orientation pairing,
  and the degree $6(M-1)$ with Lü's separator. It is taken from the notes
  (round 8 and its review). Proposition A and the theorem are proved
  *given (S)*.
- Coefficient heights, bit complexity, precision, and preprocessing cost for
  this family. The notes also do not claim them.
- The lower-bound half of "$\log A=\Theta(\varepsilon^{-9/2}\log^3)$" within
  the framework (round-11 variable-arity lower bound). That is a separate topic.

## 9. Problems found and fixes

All are minor. None changes a stated result.

1. **$\Phi$ is not related to v5's exponent in the notes.** The theorem is
   stated for $\Phi$, the "complete paid exponent". *Fix:* state the theorem
   for v5's pooled exponent $p$, and add $p\le\Phi=p+\log2/\log(B/A)$
   (Section 3).
2. **$\varepsilon/2$ is unexplained.** *Fix:* say that it leaves room for
   v5's seed unrolling (Section 6), or state the Corollary with allowance
   $\varepsilon$.
3. **Dependence on the separator degree is implicit.** *Fix:* say that the
   counts use Lü's separator for rationality, and that the bound survives
   the Fourier separator ($724/1988<1/2$).
4. **Wording slip in [round11-review-ramp-bounds](round11-review-ramp-bounds.md).**
   It says the largest dimension increases "by at most three". It should say
   "by at most a factor three"; the proof gives a factor $5/2$ (Lemma 1).
5. **Notation clash between the two round-11 notes.** The arity-ramp note
   uses $H_d$ for the sector count; the ramp-bounds note uses $M_i$ for the
   sector count and $H$ for a bit length. *Fix:* use $M_i$ for sector counts
   throughout.
6. **Weak but valid estimates.**
   - The gap estimate $27/(32(D+1)^2)$ is about nine times the true
     $\approx3/(32D^2)$. Lemma 4(3) gives a sharper bound with an equally
     short proof.
   - $r_*<A^{20}$ can be stated as $r_*<A^{17}$ (Step 6).
   - The excess bound $0.36\varepsilon$ compares with about $0.03\varepsilon$
     in practice.

   None of these needs to change. The paper may use the simpler or sharper
   forms.
7. **Terse argument in the notes.** "$H\le2\log(2x)$" is justified only
   briefly. Step 5 gives the complete chain of inequalities.

## 10. Recommendation for the paper (item f)

- **Do not present a constant-arity theorem first.** Starting the bulk at
  $(1,1)$ by smallest parents, with no ramp, has the same proof minus
  Lemma 2. It gives $\log A=O(\varepsilon^{-9/2}\log^4(1/\varepsilon))$,
  because of the startup defect $3\log(D+\frac32)$. Round 8's real-orbit
  start, with its quadratic-ring ceilings and $R=8q^2$, is more complicated
  and gives $O(\varepsilon^{-9})$. The ramp costs one short lemma (Lemma 2)
  and removes a logarithm. Present the ramp version directly. Mention the
  constant-arity variant in one sentence, to explain where the logarithm
  goes.
- **Main theorem:** the Theorem of Section 5, stated for $p$, with the
  notes' schedule and constants: $p<\frac94+\frac\varepsilon2$ and
  $\log A<3\cdot10^9\varepsilon^{-9/2}\log^3(4096/\varepsilon)$. Add
  $B\le A^2$, $m_*\le A^6$, $r_*<A^{20}$ (or $A^{17}$). Add the Corollary
  ($p<\frac94+\varepsilon$, $\log A<1.4\cdot10^8\varepsilon^{-9/2}\log^3(2048/\varepsilon)$
  for $\varepsilon\le\frac12$) if the introduction compares with v5's
  $p<\frac94+\varepsilon$.
- **Constants.** Optimizing them is not worth the space. The proof already
  has about twelve-fold slack in practice, and tightening the schedule only
  improves a constant that is irrelevant at these sizes.
- **Structure:**
  - Definition 1 and Proposition A, citing the map section for (S);
  - Lemmas 1–3, plus Lemma 4 in either form;
  - Lemma 5;
  - Lemma 6;
  - the Theorem with Steps 0–6;
  - remarks: (i) the ramp alone realizes v5's $\tau_R$, which links the new
    construction to v5's profile; (ii) the constant-arity variant and its
    extra logarithm; (iii) $\Phi$ versus $p$, and $\varepsilon/2$.

  This is about 4–5 pages.

## Adversarial review

Reviewer role: adversarial referee for topic "upper", 18 October 2026.
I did not delete or edit the checker's text above. New file:
[`experiments/shifted_chains_skeptic_upper.py`](../experiments/shifted_chains_skeptic_upper.py)
(`python -I experiments/shifted_chains_skeptic_upper.py`, about 25 s;
`--quick` about 3 s). It imports nothing from the repository and shares no
code with the checker's script.

### Verdict

**Confirmed, with minor corrections.** Given the stage relation (S), the
main theorem of Section 5 is correct as stated, including every constant:
$719/2048$, $1-\theta\ge497/512$, $719/1988<1/2$, $2305$, $240$,
$2{,}550{,}252{,}000<3\cdot10^9$, $r_*<A^{17}$, and the Corollary's
$9\cdot10^{18}<1.96\cdot10^{16}\cdot2^9$. I found no wrong constant, no
off-by-one error in $J$, $L$, $H$ or $n$, and no step that needs more than
it states. The problems are one wrong justification (Step 3), one citation
issue that the paper must handle (the tripling inside (S) is not v5's), one
inaccurate sentence in the recommendation, one labelling slip, and one
bound left as "checked numerically" that has a short proof. I also
give a three-line lemma (Lemma P) that the paper should add: it proves
$p>9/4$ for every scheme of Proposition A and closes the Step 3 gap.

### What I re-derived by hand

I re-derived these independently rather than re-reading the note:

- Lemma 1: the ceiling range, the reduction of (L) to $e\ge0$, $\hat b>r$,
  and the bound $\hat b\le r+1+(2r+b-2)/d\le\frac52\max(r,b)$. The factor
  $5/2$ is attained ($d=2$, $r=b$ even).
- Lemma 2: both zero slacks, the telescoping to $\frac{3R-1}2s_R$, and
  $F(R,R)=s_R(R+\frac{R-1}2)$ from v5 eq. `profile-formula`.
- Lemma 3: all three coefficient comparisons, the root bracket
  $p(1+\frac1D)=-1$, $p(\frac54+\frac1D)=\frac{9D-12}{16}$, the geometric sum
  $\sum_{i<L}\mu^i<\mu^L/(\mu-1)$, and $V>r+b-\frac23>s$.
- Lemma 4: the identity
  $\mu=e^y\bigl(z+\sqrt{1+z^2}\bigr)$ with $z=\frac12\sinh y$,
  $\sinh y=1/\sqrt{D(D+2)}$, and all three bounds. I also re-derived the
  review's derivative (see finding 5).
- Proposition A: the per-level exactification (A.1), the
  "groups of $\alpha_i$ copies" induction (it needs no rounding between
  levels because all $\alpha_j$ are supplied at the start), and the source
  supply $s^{6nk}\mathrm{MM}_1\trianglerighteq Q_{x_0}^{\otimes nk}$.
- The formula ($\Phi$), $\lceil r_*/m_*\rceil\le2r_*/m_*$, and Steps 0–6 line
  by line, including $n+1\le2xH+2\le x^3$, $a\le3\log x/(xH)<3/x$,
  $J/G\le5(D+2)/8\le5D/4$, $H\le\log_2(2x)+1\le2\log(2x)\le3\Lambda$, and
  the three factors $A^9$, $A^{6+3/n}$, $A^{1/n+1/k}$ of $r_*$.
- The Fourier-separator remark: only the $\log q_i$ row doubles, and the
  total is $724/1988<1/2$.

### Independent exact checks (new script)

Logarithms use a different method from the checker's. $\ln2$ comes from
$\sum1/(k2^k)$. $\ln y$ for $y\in[\frac23,\frac43)$ comes from the
alternating series of $\ln(1+u)$ with an explicit tail bound. Intervals are
integer pairs at scale $2^{-288}$, rounded outward. Sector-count maxima use
a separate hill-climbing routine, valid because the log-weight is separably
concave. No floating point enters an assertion. Results:

| Check | Scope | Result |
| --- | --- | --- |
| Lemma 1, with **exhaustive** minimality (every smaller second coordinate rejected) | $r,b\le45$, $2\le d\le30$ (58,725 cases) | pass; max growth exactly $5/2$ |
| Ramp: zero slacks, $F_R=F(R,R)$, $F_R^3\ge R^4$ | $R\le400$ | pass |
| Certificate, by **interpolation** at 9 points (not expansion); the identity "induction difference $=j^3f(j-1)$" holds at 29 points, more than the degree bound 10 | exact | coefficients `4544,17936,27324,20007,7074,972` |
| Lemma 3 identity, as affine forms in $(r,b,e)$: all four coefficients vanish in $\mathbb Q(\mu)$ | $2\le D\le200$, all $r,b,e$ | pass |
| Lemma 4: $h_D\ge0$, notes' bound, review's $h_D\le\frac3{8(D+1)^3}$, checker's $\frac1{7D^2}$ | $2\le D\le1500$; $10^5,10^8,10^{12}$ | pass; $\max(D+1)^3h_D<0.2092$ |
| Lemma 3 bound, (6), and $s\le2(5/2)^J-1$ on actual chains | 54 chains: $R=8D$ with $L\in\{0,1,2,4D,64D\}$, and 4 with $R\ne8D$ | pass; defects in $[0.88,2.03]$ |
| Bulk started at $(1,1)$ without the ramp: $s<\mu^L(\frac32+D)$; defect $-3\ln D$ | $D=4,\dots,512$ | pass; defect $=3\ln D-c$ with $c\to2.94$ |
| **Lemma P** (below): $dF(r,b)\ge(d+2)F(c,r)$ on every legal level; equality on ramp levels; $e^G\le F(x_0)$ and $F(x_0)^3\le s^4$ on chains | 718,397 levels ($r,b\le40$, $d\le30$, all legal $c$); 400 chains, 300 of them random | pass |
| Lemma 6 by brute force over all types; hill-climb equals true maximum | $n\le30$, $d\le25$ | pass |
| Flattening-rank necessary condition for the counts of (S), every type | 88 distinct levels, $n\in\{1,2,3,5,8\}$ | pass |
| Theorem rows, Steps 0, 1, 4, 5, Corollary constant | 1,586 allowances (below) | pass; max excess bound $0.2417\varepsilon$ |
| Same with Fourier separator ($E_i=1+6k(M_i-1)^2$) | every 7th allowance | pass; $\le0.2419\varepsilon<\frac{724}{1988}\varepsilon$ |
| End-to-end: actual chain, types, $\Phi$, $p$, $B\le A^2$, $m_*\le A^6$, $r_*<A^{17}$, $r_*A^2\ge m_*B^2$ | $\varepsilon=1,\frac12,\frac14$ | pass; $\Phi$ equal to the checker's to all printed digits |

The allowance grid targets the places where floors and ceilings could
break the proof:

- every $D$-breakpoint $\varepsilon=4/D^2$ ($D\le399$), where
  $D^2\varepsilon\ge4$ is tight;
- $H$-breakpoints, where $x=128D/\varepsilon$ lies within $\frac12$ of a
  power of two, for every $D\le119$;
- $\frac{4}{9}\pm10^{-12}$ and $\frac{999}{1000}$, where $D/\varepsilon^{-1/2}$
  is close to 3;
- $1/m$, $m/1000$, and 400 pseudo-random rationals;
- $\varepsilon$ down to $10^{-118}$, $2^{-200}$ and $3^{-150}$.

The checker's grid stops near $10^{-30}$. My first run gave two failures,
at $\varepsilon\approx10^{-61}$ and $10^{-118}$. Both came from my script's
fixed absolute precision: there $a$ and $g_D-2/(D+2)$ are below $2^{-288}$.
They were not errors in the proof. After switching to relative precision
for these two quantities (exact division; $\ln(1+u)\ge u-u^2/2$), all
assertions pass.

End-to-end values: $\Phi<2.2799154$, $2.2643361$, $2.2575792$ at
$\varepsilon=1,\frac12,\frac14$, and $\Phi-p<2\cdot10^{-10}$. The actual
excess is about $0.03\varepsilon$, as the checker says. I also reran the
checker's script: it passes in 28 s with the reported output.

### Findings

**1. Step 3 gives the wrong reason (minor; fixed by Lemma P).** Step 3
says "the numerator is positive and the denominator is at least
$(1-\theta)G$; hence $\Phi-\frac94\le\frac1{1-\theta}(\dots)$". What matters
is the sign of
$X=N-\frac94\,\mathrm{Den}\le(3\log s-\frac94G)+C_{\rm sep}+C_{\rm ex}+C_{\rm pool}+\frac94Ja$,
not the sign of $N$. If $X<0$, dividing by the smaller $(1-\theta)G$ makes
the right side *more* negative, so the displayed inequality could fail.
The final claim would still hold, since then $\Phi<9/4$. Fix: write
$\Phi-\frac94\le\max(X,0)/((1-\theta)G)$, or use Lemma P, which gives
$3\log s-\frac94G\ge0$ and hence $X\ge0$ always. On the instances,
$X\ge2.77$.

**2. Missing lower bound $p>9/4$ (recommended addition; proved here).**
v5's Theorem `main-relative` states $9/4<p<9/4+900/\log a$. The new
theorem states only the upper bound. A short proof of the lower bound
follows from v5's least profile.

> **Lemma P (v5's least profile is a potential for legal levels).** Let
> $F$ be v5's least profile. For every legal level of arity $d$ from
> $(r,b)$ to $(c,r)$,
> $$d\,F(r,b)\;\ge\;(d+2)\,F(c,r),$$
> with equality on every level of the ramp. Consequently, every chain of
> legal levels from $(r_0,b_0)$ to $(1,1)$ satisfies
> $$G=\sum_i\log\frac{d_i+2}{d_i}\le\log F(r_0,b_0)\le\tfrac43\log s,
> \qquad s=r_0+b_0-1,$$
> so $3\log s-\frac94G\ge0$. Every relative scheme of Proposition A (any
> arities, types, $n$, $k$) with $B>A$ has $p>9/4$.
>
> *Proof.* Let $B'=db-(d-1)c$ be the quotient length. Then $c<b<B'$ and
> $b=\frac{(d-1)c+B'}{d}$. Row $r$ of $F$ is a concave sequence (v5,
> Theorem `least-profile`, Step 1). The chord inequality therefore gives
> $dF(r,b)\ge(d-1)F(r,c)+F(r,B')$.
>
> Row $r$ is increasing. By v5 eq. `row-affine` its increments from
> column $r-1$ on equal $s_r>0$, and the increments of a concave sequence
> do not increase. Legality gives $B'\ge3c+r-1$. So
> $F(r,B')\ge F(r,3c+r-1)\ge3F(r,c)$, by the tripling axiom, which v5
> proves for $F$ at every column. Hence $dF(r,b)\ge(d+2)F(r,c)=(d+2)F(c,r)$.
>
> On the ramp, $F(j,j)=s_j\frac{3j-1}2$, $F(j,j+1)=s_j\frac{3j+1}2$ and
> $F(j+1,j+1)=s_j\frac{(3j+1)(3j+2)}{6j}$. These give equality for both
> arities $3j-1$ and $3j$.
>
> Telescoping from $F(1,1)=1$ gives $e^G\le F(r_0,b_0)$, and v5 eq.
> `profile-upper` gives $F(m,n)\le(m+n-1)^{4/3}$.
>
> For $p$: every factor of $r_*/m_*$ other than $s^{6nk}$ is at least 1,
> so $\log(r_*/m_*)\ge6nk\log s$. Lemma 6 gives $M_i\le(d_i+2)^n$, so
> $0<\log(B/A)\le2nkG$. Hence $p\ge3\log s/G\ge9/4$. Since $B>A$, some
> $M_i\ge2$, so $(2M_i-1)/M_i>1$ and the inequality is strict. $\square$

Lemma P also explains why $F_R=F(R,R)$ exactly. On a ramp level the child
column is $c\in\{r-1,r\}$ and the slack is zero. There $F$ is affine
(v5 eq. `row-affine`) and tripling is an equality. So the ramp is the
equality case of Lemma P at every level. In the bulk, Lemma P gives
$\omega_D\ge9/4$ again. Round 14
([round14-hankel-flattening](round14-hankel-flattening.md)) claims a
stronger barrier, $p>9/4$ even with arbitrary auxiliary compression, by a
longer route. I did not check that note. Lemma P suffices for the paper's
upper-bound section.

**3. The tripling inside (S) is not v5's (citation; the paper must
handle it).** v5 realizes tripling only at column $c=r\ge2$. v5's
`profile.tex` says "our tensor maps realize only $b=r$", and Corollary
`oriented-relations`(b) assumes $r\ge2$. The chain of the theorem needs
more:

- every ramp level of arity $3j$, from $(j+1,j+1)$ to $(j,j+1)$, has
  $c=r-1$;
- every bulk level after the first has $c<r$;
- the last level, from $(1,2)$ to $(1,1)$, has $r=1$.

So the paper cannot cite v5's Lemma `tripling` for (S). It needs the
general-column reset with $r=1$ included, as the maps check
([shifted-chains-check-maps](shifted-chains-check-maps.md), item 2) also
says. The upper note correctly marks (S) as unchecked. The task background
("tripling and separator in `maps.tex`") understates what must be proved.

**4. Inaccurate sentence in the recommendation (minor).** Section 10 says
that round 8's real-orbit start "is more complicated and gives
$O(\varepsilon^{-9})$". In fact
[round9-optimized-multiscale](round9-optimized-multiscale.md) keeps round
8's real-orbit start and proves
$\log A<2\cdot10^9\varepsilon^{-9/2}\log^4(1600/\varepsilon)$. The
$\varepsilon^{-9}$ came from round 8's choice $n\sim\varepsilon^{-3}$, not
from the start. The comparison the paper should make is:

- fixed arity, with either start: $\varepsilon^{-9/2}\log^4$;
- with the ramp: $\varepsilon^{-9/2}\log^3$.

My numerics show that the loss without the ramp is real for this proof
technique, not an artifact of the bound: the startup defect from $(1,1)$
is $3\ln D-2.94+o(1)$. With the ramp it stays near $0.97$.

**5. Labels and an unproved-but-provable bound (minor).**

- The JSON gives the remark "constant arity without ramp" status
  "proved-here", but its consequence ($L\asymp D\log D/\varepsilon$,
  $\log^4$) is only an outline. Label it "outline".
- The checker lists the review's bound $h_D\le3/(8(D+1)^3)$ as
  numerically checked only. It has a short proof. With $x=1/(D+1)$,
  $$h=3\operatorname{asinh}\frac{x}{2\sqrt{1-x^2}}-\frac32\operatorname{atanh}x,
  \qquad
  h'(x)=\frac{9x^2}{2(1-x^2)\sqrt{4-3x^2}\,(2+\sqrt{4-3x^2})}.$$
  I re-derived $h'$. For $0\le x\le\frac13$ the denominator is at least
  $2\cdot\frac89\cdot\sqrt{11/3}\cdot(2+\sqrt{11/3})>13>8$, and $h(0)=0$,
  so $h\le3x^3/8$. With $g_D=2\operatorname{atanh}x\ge2x$ this gives
  $$\omega_D-\tfrac94\le\frac3{16(D+1)^2}.$$
  This is the cleanest sharp form. Either it or Lemma 4(3) may replace the
  notes' $27/(32(D+1)^2)$; all three are valid.

**Checked and found correct:**

- the $\varepsilon/2$ explanation. v5's Theorem `bounded-seed` also caps
  $\varepsilon'\le\frac12$ so that $p<\frac52$. The new theorem at
  $\varepsilon'\le\frac12$ gives $p<\frac94+\frac{\varepsilon'}2\le\frac52$,
  which is consistent.
- $\Phi=p+\log2/\log(B/A)$.
- the robustness to the Fourier separator.
- the wording slip in the round-11 review (factor, not additive three).

### What I could not verify

- The stage relation (S) itself. It belongs to the maps topic. My only
  check of it is a *necessary* condition: no flattening rank may increase
  under a degeneration. The counts of (S) pass that test on every level
  and type tried. It is far from a proof.
- Coefficient heights, bit cost and precision. Neither the notes nor the
  checker claim them.
- The lower bound $\log A=\Omega(\varepsilon^{-9/2}\log^3)$ within the
  framework, and round 14's compression barrier.

### Final statements I endorse

All are conditional on (S), which must be stated as its own proposition
with the general-column reset, including $r=1$.

- Definition 1, Proposition A, and Lemmas 1–6 as written in Sections 3–4,
  with Lemma 4 in any of its three forms.
- **Lemma P** above.
- **Main Theorem.** Let $0<\varepsilon\le1$ be rational, and put
  $D=\lceil\sqrt{4/\varepsilon}\rceil$, $R=8D$,
  $L=\lceil64D/\varepsilon\rceil$, $H$ the bit length of
  $\lceil128D/\varepsilon\rceil$, and $n=k=\lceil256DH/\varepsilon\rceil$.
  The ramp-plus-bulk chain with maximal types gives a rational relative
  scheme $r_*\mathrm{MM}_A\trianglerighteq m_*\mathrm{MM}_B$ with
  $$\tfrac94<p\le\Phi<\tfrac94+\tfrac{719}{1988}\varepsilon<\tfrac94+\tfrac\varepsilon2,
  \qquad
  \log A<3\cdot10^9\,\varepsilon^{-9/2}\log^3(4096/\varepsilon),$$
  $$B\le A^2,\qquad m_*\le A^6,\qquad r_*<A^{17}.$$
  The proof is Steps 0–6 of Section 5. In Step 3, use $\max(X,0)$ or
  Lemma P.
- **Corollary.** For rational $0<\varepsilon\le\frac12$, $p<\frac94+\varepsilon$
  and $\log A<1.4\cdot10^8\varepsilon^{-9/2}\log^3(2048/\varepsilon)$.
- **Remark.** With v5's Fourier separator, the same schedule gives
  $\Phi<\frac94+\frac{724}{1988}\varepsilon$ over a cyclotomic field.
