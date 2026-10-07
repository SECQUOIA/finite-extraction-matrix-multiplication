# An explicit finite extraction from the smallest profile case

Date: 2026-10-06. This is an original derivation from the supplied manuscript
and the local [separator construction](constructive-analysis.md), without
literature research. Novelty against existing work has not been established.

The smallest profile argument can be converted into a specified finite tensor
recipe, using fixed rational types, explicit separators, interpolation,
catalyst reuse, and a batched recursive algorithm. One parameter choice gives
an arithmetic exponent below **2.79**. Its padded target block dimension is
an integer with **21,665,218,118 decimal digits**. This is not a practical
algorithm, a materialized rank decomposition, or a solution to the requested
practical exponent of 2.25. The construction identifies and counts a finite
route previously hidden by the character argument.

This is not a new best asymptotic matrix multiplication bound: the
[literature review](literature-review.md) documents existing lower exponents.
The purpose here is a counted finite extraction from this particular proof.

The exponent here belongs to an algorithm specified by finite compositions of
linear maps. The accompanying program verifies the small maps, resource
counts, and cost bounds; it does not expand the enormous composed maps.

## Notation and fixed rational types

Write \(C_b=C(2,b)\), and let

\[
Q_b=\bigotimes_{\pi\in S_3} C_b^\pi.
\]

There is an explicit rank decomposition of \(C_b\) with \(b+1\) products:
evaluate both input polynomials at the \((b+1)\)-th roots of unity and
interpolate their product. Consequently

\[
R(Q_b)\le(b+1)^6,\qquad R(Q_2)\le729,
\qquad Q_1\cong T_4.
\]

Throughout this note, an integer multiple of a tensor denotes a full direct
sum. No integer direct-sum multiplicity is silently canceled.

The extremal row in the [profile calculation](profile-analysis.md) is
\(p_b=(4b+2)/3\), for \(1\le b\le7\). Fix the following type counts:

| \(b\) | Input factors \(w_b\) | Factors \(C_{b+1}\): \(u_b\) | Factors \(C_{b-1}\): \(d_b\) |
|---:|---:|---:|---:|
| 2 | 50 | 35 | 15 |
| 3 | 56 | 36 | 20 |
| 4 | 54 | 33 | 21 |
| 5 | 44 | 26 | 18 |
| 6 | 26 | 15 | 11 |

Here \(u_b+d_b=w_b\), and
\(u_b/w_b=p_{b+1}/(2p_b)\). Add 15 tripling factors of \(C_7\), with
five copies of each of its three sectors. The exact entropy identity is

\[
\frac{3^{15}}{2^{215}}
\prod_{b=2}^6\frac{w_b^{w_b}}{u_b^{u_b}d_b^{d_b}}
=\left(\frac{10}{3}\right)^{15}.
\tag{1}
\]

Thus the entropy probabilities and their multiplicities are fixed rational
numbers. They do not depend on an unknown character.

## The initial type extractions are exact restrictions

For \(b=2,\ldots,6\), the determinant basis change in the manuscript turns
\(C_b\otimes B_X(2)\) into two diagonal blocks \(C_{b+1}\), \(C_{b-1}\),
plus a quotient-to-kernel block. There is no kernel-to-quotient block. More
explicitly, the quotient lifts at degree \(e\) are
\(s_i=u^{e-i}v^i s\) for \(0\le i\le e\), followed by \(w_e=v^e w\).
The kernel basis is \(w_i-s_{i+1}\), for \(0\le i<e\). For multiplication
by \(u,v\), the only off-diagonal term is multiplication by \(u\) from
the last quotient lift into the last output kernel coordinate.

Take \(w_bN\) factors, for an integer \(N\ge1\), and retain exactly
\(d_bN\) kernel coordinates on both the second and third tensor legs.
Every off-diagonal choice increases the kernel count by one. Equal counts
therefore exclude every off-diagonal term. This is an **exact type
restriction**, with

\[
M_b=\binom{w_bN}{u_bN}
\]

matched sectors. Each sector has tensor
\(C_{b+1}^{\otimes u_bN}\otimes C_{b-1}^{\otimes d_bN}\), up to a
permutation of factors. The first leg remains shared.

Likewise the tripling decomposition of \(C_7\) has two outer \(C_2\)
sectors and a middle \(C_2\) with its second and third legs exchanged.
The only unwanted terms have a middle second-leg label and an outer
third-leg label. Retain sector frequencies \((5N,5N,5N)\) on both legs
of \(C_7^{\otimes15N}\). Equality of the middle-label counts removes every
unwanted term. The number of matched sectors is

\[
M_7=\frac{(15N)!}{(5N)!^3}.
\]

These two observations remove the determinant and tripling degenerations
from this finite construction. Only the subsequent separator still needs
interpolation. Fixed-type restrictions do not themselves make the first-leg
variables independent.

## A fully counted catalytic degeneration

For each of the six constructions indexed by \(b=2,\ldots,7\), apply the
smaller separator with \(L_b=2M_b-1\) copies and auxiliary dimension
\(M_b\). Apply it independently to every leg permutation. Define

\[
B=\prod_{b=2}^7M_b,\qquad
S=\prod_{b=2}^7(2M_b-1)^6,\qquad H=B^6,
\]

\[
\mathcal C_N=
Q_2^{\otimes35N}Q_3^{\otimes56N}Q_4^{\otimes54N}
Q_5^{\otimes44N}Q_6^{\otimes26N}Q_7^{\otimes15N}.
\tag{2}
\]

Products of tensors are abbreviated by juxtaposition. The word types above
give the exact factor ledger:

| Tensor | Source exponent divided by \(N\) | Output exponent divided by \(N\) |
|---|---:|---:|
| \(Q_1\) | 0 | 15 |
| \(Q_2\) | 50 | 35 |
| \(Q_3\) | 56 | 56 |
| \(Q_4\) | 54 | 54 |
| \(Q_5\) | 44 | 44 |
| \(Q_6\) | 26 | 26 |
| \(Q_7\) | 15 | 15 |

For tripling, each permutation contributes \(10N\) factors in its original
orientation and \(5N\) in the exchanged orientation. Multiplying over all
six permutations gives exactly \(Q_2^{\otimes15N}\). No identification of
different first-leg maps before separation is used.

The product over six permutations of \(B_X(m)\) is \(T_m^{\otimes2}\).
The determinant inputs use \(230N\) such dot-product factors. Together
with \(Q_1^{\otimes15N}\cong T_{2^{30N}}\), the ledger yields

\[
S\,\mathcal C_N Q_2^{\otimes15N}T_s
\ \rightsquigarrow\ H\,\mathcal C_N T_t,
\qquad
s=2^{460N},\quad t=2^{30N}B^2.
\tag{3}
\]

In particular, the source still has \(S\) direct-sum copies and the target
still has \(H\) copies. The inequality \(S/H<2^{36}\) is only a cost ratio;
it is not an asserted tensor cancellation.

All 36 separators can use a common parameter. Every surviving exponent is
nonnegative, and a valid degree bound for (3) is

\[
D=6\sum_{b=2}^7(M_b-1)^2.
\tag{4}
\]

There are no remaining filtration-parameter degrees to add. For fixed \(N\),
the tensor coefficients, Fourier phases, bases, coordinate projections, and
variable weights specifying (3) are all given by finite formulas.

## Interpolation first, then exact catalyst reuse

Take the \(k\)-th tensor power of (3). Its polynomial degree is at most
\(kD\). Averaging at all \(E=kD+1\) roots of unity extracts the constant
coefficient exactly. Hence

\[
E S^k\,\mathcal C_N^{\otimes k}Q_2^{\otimes15Nk}T_{s^k}
\ \ge\ H^k\,\mathcal C_N^{\otimes k}T_{t^k}.
\tag{5}
\]

Replace the displayed \(Q_2\) factors by their explicit rank-729
decompositions. With

\[
\alpha=ES^k729^{15Nk},\qquad \beta=H^k,
\]

this is an **exact** restriction
\(\alpha\mathcal C_N^{\otimes k}T_{s^k}
\ge\beta\mathcal C_N^{\otimes k}T_{t^k}\).
Exactness matters: repeatedly composing an unexactified degeneration could
increase its interpolation degree without the bound claimed here.

Now reuse the same catalyst \(j\) times. Induction gives

\[
\alpha^j\mathcal C_N^{\otimes k}T_{s^{kj}}
\ \ge\beta^j\mathcal C_N^{\otimes k}T_{t^{kj}}.
\tag{6}
\]

For the induction, tensor the previous restriction by \(\alpha T_{s^k}\),
then apply the exact one-step restriction to the single retained catalyst.
The catalyst exponent stays \(k\), rather than growing to \(kj\).

An explicit rank bound for that catalyst is \(R(\mathcal C_N)\le\kappa\),
where

\[
\kappa=3^{210N}4^{336N}5^{324N}6^{264N}7^{156N}8^{90N}.
\tag{7}
\]

Pay for its rank decomposition on the source, and restrict its nonzero output
to a scalar. This yields the finite relative multiplication scheme

\[
r\,T_a\ge m\,T_b,
\tag{8}
\]

with the following explicit integers:

\[
\begin{aligned}
a&=s^{kj},&b&=t^{kj},\\
r&=\kappa^k E^jS^{kj}729^{15Nkj},&m&=H^{kj}.
\end{aligned}
\tag{9}
\]

No low-rank decomposition of \(T_a\) has been assumed or looked up. It
remains the recursive multiplication operation in (8).

## Removing the simultaneous-output factor by an algorithm

Here is a general constructive batching lemma. Suppose an explicit relative
scheme \(rT_a\ge mT_b\) is given, with integers \(b>a\), and set
\(K=\lceil r/m\rceil\).

To multiply a batch of \(m\) pairs of \(n\)-square matrices, pad each to
size \(b\lceil n/b\rceil\), partition into \(b\)-by-\(b\) blocks, and
apply the scheme to those blocks. Its central scalar coefficients preserve
the order of the left and right matrix factors. It requires \(r\) products
of dimension \(a\lceil n/b\rceil\). Partition these products into \(K\)
batches of size \(m\), filling the last batch with zeros, and recurse.
All linear transformations and recombinations cost \(O(n^2)\) at each
node, with a fixed, potentially enormous constant.

The recursive dimension satisfies

\[
n'\le\frac ab n+a.
\]

Put \(c=ab/(b-a)\). Then \(n'-c\le(a/b)(n-c)\). Stop at any fixed
threshold exceeding \(c\). This proves that the recursion has arithmetic
exponent

\[
\max\left(2,\frac{\log\lceil r/m\rceil}{\log(b/a)}\right),
\tag{10}
\]

with the usual logarithmic qualification if the second term equals 2.
For the parameter choice below it is strictly greater than 2. A single
matrix product is obtained by setting the other \(m-1\) input pairs to
zero. This costs a fixed factor; it does not assume a tensor comparison
\((r/m)T_a\ge T_b\).

This lemma explicitly accounts for the large simultaneous-output count.
It also avoids defining an exponent through an unknown optimal rank of
\(T_a\). The price is a vast batch size and vast fixed linear maps.

## A certified finite bound, and its practical scale

Since \(r/m\ge1\), use \(\lceil r/m\rceil\le2r/m\). Equations (9)–(10)
then give the following upper expression for the exponent:

\[
\tau_{N,k,j}\le
\frac{
90N\log3+\log(S/H)+\frac{\log E}{k}
+\frac{\log\kappa}{j}+\frac{\log2}{kj}
}{\log(t/s)}.
\tag{11}
\]

For fixed \(N\), taking \(k\) and then \(j\) large removes the interpolation
and catalyst costs. Equation (1) and elementary fixed-frequency counting
give, as \(N\) grows,

\[
\frac1N\log(t/s)\longrightarrow30\log(10/3),\qquad
\frac1N\log(S/H)\longrightarrow0.
\]

Thus these explicit formulas approach
\(3\log3/\log(10/3)\). No general spectral comparison is needed in this
last deduction. Every finite use must retain all terms in (11).

The concrete choice

\[
(N,k,j)=(300,125,3750)
\]

makes the right side of (11) lie strictly between
\(2.78918\) and \(2.78919\), hence below \(2.79\). The exact input and
output dimensions in (9) are represented symbolically, rather than expanded.
The padded target dimension \(b\) has **21,665,218,118 decimal digits**.
Even the recursive input dimension \(a\) has more than 19 billion digits.
The simultaneous-output multiplicity is larger still. The arithmetic
exponent is therefore an existence and construction result with prohibitive
constants; it gives no usable improvement on the implemented rank-48 scheme.

The cost program forms the six finite sector counts and the interpolation
degree as integers. It conservatively replaces \(\log(S/H)\) in (11) by
\(36\log2\). All logarithm bounds are rational: write an integer as
\(2^e y\), enclose \(y\in[1,2]\) between adjacent 80-bit mantissas, and use
\(z=(y-1)/(y+1)\) in

\[
2\sum_{h=0}^{39}\frac{z^{2h+1}}{2h+1}
\le\log y\le
2\sum_{h=0}^{39}\frac{z^{2h+1}}{2h+1}
+\frac{2z^{81}}{81(1-z^2)}.
\]

The same bounds compute \(\log2\). Interval arithmetic then uses exact
fractions; only display conversion uses decimal rounding. The assertion that
the upper expression is below the rational number \(279/100\), and the
decimal digit counts, therefore do not rely on floating-point logarithms.
This certifies the scalar cost calculation. It does not substitute for
expansion and independent coefficient verification of the full relative scheme.

## Why a coordinate-only shortcut does not reach the same bound

There is a separate, limited obstruction to avoiding the linear mixing in
the construction. Each \(C_2\) is an induced coordinate subtensor of the
group tensor of \(\mathbb Z_3\). A product of \(N\) permuted factors is
therefore an induced subtensor of the group tensor of
\(G=(\mathbb Z_3)^N\).

Suppose injective coordinate selections and relabelings, possibly followed
by a diagonal degeneration, retain the intended matrix multiplication terms.
Group labels satisfying all intended equations must have the form

\[
x_{ij}=A_i+B_j,\qquad
y_{jk}=-B_j+C_k,\qquad
z_{ki}=-C_k-A_i.
\]

A collision \(A_i+B_j+C_k=A_{i'}+B_{j'}+C_{k'}\) creates the two supported
mixed monomials

\[
x_{ij}y_{j'k}z_{k'i'},\qquad x_{i'j'}y_{jk'}z_{ki}.
\]

If the triples differ, these are unwanted terms. The same additive
decomposition applies to variable weights whose totals vanish on every
intended term. The two mixed monomials consequently have opposite weights.
They cannot both receive positive weight; if their weights are zero, both
survive. Thus the triples must inject into \(G\), forcing \(n^3\le|G|\)
for a retained \(T_n\). This prevents a subcubic rank bound charged at the
available source rank bound \(3^N\) in this restricted class.

Also \(T_r\) is an induced coordinate subtensor of the group tensor on
\((\mathbb Z_r)^3\), using labels
\(x_{ij}=(i,j,0)\), \(y_{jk}=(0,-j,k)\), and \(z_{ki}=(-i,0,-k)\).
It follows that a coordinate/diagonal reduction
\(Q_2^{\otimes k}T_{9^k}\to T_n\) requires \(n\le81^k\), and cannot
reach \(n=100^k\).

This obstruction does **not** cover general linear changes, coordinate
identifications, or cancellations. The Fourier separator deliberately uses
linear mixing, so the obstruction does not apply to (3)–(9). It is not a
claim that the desired unrestricted reduction or a practical algorithm is
impossible.

## Reproduction

```sh
python experiments/small_profile_extraction.py
python -m pytest tests/test_small_profile_extraction.py
```

The default cost report is saved in
[results/small-profile-extraction.json](../results/small-profile-extraction.json).
An [independent review](small-profile-review.md) checked the tensor ledger,
interpolation degree, catalyst reuse, batched recursion, and rational intervals.

The tests check the exact entropy identity and resource ledger, determinant
basis changes for every used degree, removal of off-diagonal terms by equal
type frequencies, tripling sector frequencies, logarithmic interval
consistency, and the stated finite bound. The separate separator tests check
its coefficient identities over exact finite fields.

The next practical research question is how to replace the enormous type,
catalyst, and batch constructions with a small explicit tensor map. Merely
making the existing asymptotic argument finite has not achieved that.
