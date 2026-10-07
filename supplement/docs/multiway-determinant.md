# A determinant filtration with more than two sectors

The proposed local relation is valid. Tensoring \(C(r,b)\) with
\(B_X(h+1)\), for \(b\ge h+1\), gives a filtration whose diagonal blocks
are exactly

\[
C(r,b+h),\ C(r,b+h-2),\ \ldots,\ C(r,b-h).
\]

There is an explicit integer basis, and no additional degeneration is needed
to extract fixed types: equal total filtration order removes every
off-diagonal term. The auxiliary size is genuinely \(h+1\), rather than
the \(2^h\) consumed by \(h\) repeated binary steps. This changes finite
costs but does not strengthen the scalar discrete-concavity axioms. It is
not a practical matrix multiplication algorithm or a new exponent claim.

This note is an original calculation from the local tensor maps. No
literature research or global flow optimization was performed.

## Filtration and an explicit integer basis

Write \(d=b-1\), \(\ell=r-1\), and

\[
W_{d,h}=\mathbb Q[u,v]_d\otimes\mathbb Q[s,t]_h,
\qquad \Delta=ut-vs.
\]

The source bilinear map is multiplication by a degree-\(\ell\) polynomial
in \(u,v\), with the auxiliary \(\mathbb Q[s,t]_h\) unchanged. Define

\[
F^jW_{d,h}=\Delta^jW_{d-j,h-j}\quad(0\le j\le h),
\qquad F^{h+1}=0.
\]

After removing the displayed \(\Delta^j\), diagonal substitution
\((s,t)=(u,v)\) identifies

\[
F^j/F^{j+1}\cong\mathbb Q[u,v]_{d+h-2j}.
\tag{1}
\]

For a representation-theoretic identification under \(GL_2\), include the
factor \((\det V)^j\). That twist does not change the fixed-coordinate
multiplication map used here.

An explicit lift of quotient monomial index \(i\), for bidegree \((p,q)\), is

\[
L_{p,q}(i)=
\begin{cases}
u^{p-i}v^i s^q,&0\le i\le p,\\
v^p s^{q-(i-p)}t^{i-p},&p<i\le p+q.
\end{cases}
\]

Use the basis

\[
B_{j,i}=\Delta^jL_{d-j,h-j}(i),
\quad 0\le j\le h,\quad0\le i\le d+h-2j.
\tag{2}
\]

To prove (1) and construct coordinates, repeatedly replace \(ut\) by
\(vs+\Delta\). Modulo \(\Delta\), every monomial reduces to the displayed
lift with the same total exponent of \(v,t\). Subtract those quotient
lifts and divide the remainder by \(\Delta\); repeat at bidegree
\((d-1,h-1)\). This uses integer coefficients and terminates after \(h\)
divisions. At each step the kernel is exactly the multiples of \(\Delta\).
The number of basis vectors is

\[
\sum_{j=0}^{h}(d+h-2j+1)=(d+1)(h+1)=\dim W_{d,h}.
\]

Multiplication commutes with \(\Delta\). It therefore maps \(F^jW_{d,h}\)
into \(F^jW_{d+\ell,h}\), never to a smaller filtration index. On quotient
\(j\), multiplying by \(u^{\ell-a}v^a\) sends monomial index \(i\) to
\(i+a\), with coefficient 1. The diagonal tensor is precisely
\(C(r,b+h-2j)\).

These statements concern the basis of the input polynomial space and the
coordinates in the output polynomial basis. The third tensor leg uses the
dual output coordinates. Applying the same basis matrix indiscriminately
to the second and third tensor legs would not implement this change.

## An independent small check

For \(h=2,b=3,r=2\), take input groups

\[
q=(u^2s^2,uvs^2,v^2s^2,v^2st,v^2t^2),\quad
k=\Delta(us,vs,vt),\quad l=\Delta^2.
\]

The output groups are

\[
Q=(u^3s^2,u^2vs^2,uv^2s^2,v^3s^2,v^3st,v^3t^2),
\]
\[
K=\Delta(u^2s,uvs,v^2s,v^2t),\qquad L=\Delta^2(u,v).
\]

All diagonal terms are the ordinary index shifts. The complete list of
extra terms, using zero-based indices, is

\[
u q_3=Q_3+K_2,\qquad
u q_4=Q_4+K_3,\qquad
u k_2=K_2+L_1.
\]

A separate rational polynomial calculation verified these formulas. It also
checked \(r=3,b=3\), where
\(u^2q_4=Q_4+2K_3+L_2\). Thus higher-degree multiplication can jump more
than one level, but still cannot decrease the level. The last sector at
\(b=h+1\) is \(C(r,1)\), not a zero sector.

## Exact fixed-type restriction and auxiliary cost

In \(w\) tensor factors, keep words with prescribed frequencies
\(n_0,\ldots,n_h\) on both affected legs, where \(\sum_jn_j=w\).
Every supported term weakly increases each factor's filtration index.
Equal total index \(\sum_jjn_j\) on the two legs forces equality in every
factor. Hence all off-diagonal terms vanish exactly. There are

\[
M=\frac{w!}{\prod_{j=0}^{h}n_j!}
\tag{3}
\]

matched sectors. Each has the factors
\(\prod_j C(r,b+h-2j)^{\otimes n_j}\), in the word's order.
The first leg remains shared. Reordering its factors separately for different
words is allowed only after the existing sector separator has made their
first legs independent. Equation (3) is not a free direct-sum extraction.

The auxiliary \(B_X(h+1)\) has one exceptional first leg and an identity
on its other two legs. Three cyclic orientations therefore consume

\[
B_X(h+1)B_Y(h+1)B_Z(h+1)\cong T_{h+1}.
\]

The existing six-permutation balance instead consumes
\(T_{(h+1)^2}\). Threefold balance needs the signed orientation ledger
proved in [the cyclic construction](cyclic-profile-extraction.md); the
local filtration alone does not justify replacing six permutations globally.

For comparison, \(h\) repeated binary steps consume \(B_X(2^h)\) and
produce the same possible convolution lengths with binomial multiplicities
\(\binom hj\). At \(h=2\), they have two middle blocks and auxiliary
dimension 4. The new filtration has one middle block and dimension 3.
It amounts to using the symmetric auxiliary rather than retaining the entire
tensor power of the two-dimensional auxiliary. This requires the stated
projection or a direct choice of \(B_X(h+1)\); deleting an arbitrary middle
path from the old calculation does not supply its maps.

There is no immediate rank improvement for the unsplit local source: its
rank is exactly \((h+1)(r+b-1)\), by the output flattening lower bound and
the explicit convolution-rank upper bound. Its scalar inequality
\((h+1)P(r,b)\ge\sum_jP(r,b+h-2j)\) already follows from discrete
concavity by pairing columns equidistant from \(b\). The benefit is a
different finite tensor realization of longer jumps.

## A smaller exact index-2 chain

Write \(S_b=S^+_{2,b}\) for the three-cyclic tensors. The following fixed
counts use normalization \(K=15\):

| Source tensor | Auxiliary dimension | Source factors | Child tensors | Child counts |
| --- | ---: | ---: | --- | --- |
| \(S_2\) | 2 | 30 | \(S_1,S_3\) | \(9,21\) |
| \(S_3\) | 3 | 42 | \(S_1,S_3,S_5\) | \(6,14,22\) |
| \(S_5\) | 3 | 33 | \(S_3,S_5,S_7\) | \(7,11,15\) |
| \(S_7\), tripling | 1 | 15 | \(S_2\) | 15 |

The table orders child lengths increasingly, opposite the filtration index
\(j\). In the basis convention (2), the three frequency vectors
\((n_0,\ldots,n_h)\) are \((21,9)\), \((22,14,6)\), and \((15,11,7)\).

Direct collection gives source minus output
\(15S_2-15S_1\). The common factors remain the catalyst

\[
\mathcal C=S_2^{15}S_3^{42}S_5^{33}S_7^{15}.
\]

Here \(S_1\cong T_2\). Tripling outputs the diagonal tensor \(S_2\),
whose opposite cyclic orientation is isomorphic to itself. Thus the middle
tripling sector is compatible with this threefold ledger after separation.
No non-diagonal orientation identification is being assumed.

At type scale \(N\), the charged source auxiliary side is

\[
u=2^{30N}3^{75N},
\]

instead of \(2^{230N}\) for the earlier index-2 binary chain with the
same threefold balance. Its base-2 logarithm per \(N\) is about 148.872,
a reduction of about 35.3%. Sixfold balance squares both sides, retaining
the same percentage change. These are dimension comparisons, not speedups.

The exact sector counts are

\[
M_1=\binom{30N}{9N},\quad
M_2=\frac{(42N)!}{(6N)!(14N)!(22N)!},\quad
M_3=\frac{(33N)!}{(7N)!(11N)!(15N)!}.
\]

Using the independently verified middle-count-only tripling restriction gives
\(M_4=\binom{15N}{5N}2^{10N}\), without fixing the two outer frequencies.
At \(N=1\), these four counts are respectively
14,307,150; 19,914,562,703,599,200; 33,006,526,375,680; and 3,075,072.
Even this small ledger therefore describes large separated sectors.

For \(M=\prod_iM_i\), every remaining charge can use the existing formulas:

\[
v=2^{15N}M,\quad
\mathscr S=\prod_i(2M_i-1)^3,\quad \mathscr H=M^3,
\quad D=3\sum_i(M_i-1)^2,
\]

\[
\kappa_N=3^{45N}4^{126N}6^{99N}8^{45N}.
\]

With \(E=kD+1\), exactification and catalyst reuse give the same counted
relative recipe with

\[
r_* = \kappa_N^k E^j\mathscr S^{kj}3^{45Nkj},\qquad
m_* = \mathscr H^{kj},\qquad A=u^{kj},\quad B=v^{kj}.
\]

The normalized row weights are \(2,14/5,11/5\), with tripling weight 1.
Their child proportions equal \(F_b/(dF_{\rm parent})\), where
\(F_b=(4b+2)/3\) and \(d\) is the auxiliary dimension. Exact rational
arithmetic verifies

\[
\frac{2^{15}3^{15}}{2^{30}3^{75}}
\prod_{\text{three split rows}}
\frac{w^w}{\prod_c n_c^{n_c}}
=\left(\frac{10}{3}\right)^{15}.
\]

Thus the entropy-limit exponent remains
\(3\log3/\log(10/3)\approx2.737468\). This does not remove finite type,
separator, interpolation, or catalyst costs. The earlier binary-only size
floors must not be transferred to this changed multiway recipe without a
new argument.

## Checks and limits

```sh
python -m experiments.multiway_determinant > results/multiway-determinant.json
python -m pytest tests/test_multiway_determinant.py -q
```

All 10 focused tests pass. They check exact integer basis reconstruction,
the independent \(h=2\) expansion, an order-two jump, agreement with the
existing binary formula, removal of off-diagonal two-factor terms,
\(h=3\) and boundary cases, and the chain's exact ledger and entropy
identity. The [saved report](../results/multiway-determinant.json) records
the small map and count results. An independent agent verified the two
\(h=2\) examples directly over the rationals.

The [component implementation](../experiments/multiway_determinant.py)
generates only small local maps for these checks. The full composed recursive
maps, numerical stability, and useful finite runtime remain unverified.
Integer basis coefficients can grow with \(h\); exactness is not a
floating-point stability certificate. No global parameter optimization or
large multiplication benchmark was performed here.

Subsequent work gives a [general rational flow family](multiway-profile-flows.md)
with a smaller normalized auxiliary cost, and a separate
[small-size screen](multiway-small-flow-screen.md) for every conserved
integer type on the displayed index-2 graph. Those results retain their
own normalization and execution limitations.
