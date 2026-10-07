# Independent audit of the revised finite construction

Date: 2026-10-07.

This review concerns the revised construction using multiway types,
threefold balancing, conserved rounding, and pooled recursion. It does
not reuse the conclusions of the earlier binary-construction audit.
I read `extraction.tex`, `quantitative.tex`, and `preliminaries.tex`,
and checked their dependencies in `rounding.tex`, `flows.tex`, `maps.tex`,
and `appendix-composition.tex`. I did not conduct literature research,
rerun experiments, or edit the TeX files.

**Verdict:** no blocking mathematical error found. The stated finite
algorithm and the two quantitative bounds follow from the displayed maps
and estimates. The report gives the independent checks, including the
constants in those bounds. There is one minor terminology issue, listed
at the end.

The reviewed file hashes are:

| File | SHA-256 prefix |
| --- | --- |
| `extraction.tex` | `5580490b2e699c29` |
| `quantitative.tex` | `b3e3a50d6c0d6f21` |
| `preliminaries.tex` | `02bd1d3674a721ea` |
| `rounding.tex` | `3ecece927f76c77d` |
| `flows.tex` | `43dd05f0127985b6` |
| `maps.tex` | `ff0b30bbb37f67bf` |
| `appendix-composition.tex` | `fcd30052c2dfe504` |

Line references below concern this snapshot.

## 1. Exact types and threefold balancing

The determinant basis in `maps.tex:36` is valid over the integers.
Reducing a monomial by the relation \(ut=vs+\Delta\) leaves the
unique specified lift modulo \(\Delta\); division of the remainder
by \(\Delta\) reduces both degrees. Iterating gives the displayed
basis and proves that the associated diagonal blocks are exactly
\(C(r,b+h-2j)\). Multiplication cannot decrease the filtration
index. Equal retained index totals therefore force equality at every
tensor position, even when some type counts are zero. The type
projection introduces no parameter degree.

The row actions meet the map's dimension hypothesis. Their source column
is \(b=r-1+x\), while \(h\le x\) and \(r\ge2\), so
\(b\ge h+1\). Their children run from columns \(r-1\) to
\(4r-1\), all of which are positive.

The partial-middle restriction in `maps.tex:108` is also exact. Every
unmatched term has a middle label on the second leg and an outer label
on the third. Retaining the same number of middle labels on both legs
eliminates every such term. With the outer labels unrestricted there
are precisely

\[
\binom nm2^{n-m}
\]

matched sectors. The ratio of consecutive counts is
\((n-m)/(2m+2)\), so \(m=\lfloor(n+1)/3\rfloor\) is a mode.
Since the counts sum to \(3^n\), its count is at least
\(3^n/(n+1)\). Neither divisibility by three nor separate fixed
counts for the two outer labels are needed.

Threefold balancing is consistent with the mixed orientation of a
tripling sector. The three factors in one sign coset each put the shared
leg in a different global position. Their auxiliary dot products give
one matrix multiplication factor. An odd permutation of the native
tripling tensor exchanges the two sign cosets, so the middle positions
produce the opposite sign. The diagonal isomorphism
\(S^+_{r,r}\cong S^-_{r,r}\) then returns them to the prescribed
sign. This is a coordinate isomorphism of the full balanced product;
it does not exchange two global legs on an isolated tensor factor.

The signs of adjacent rows must alternate. With that choice,
\(S^{\sigma}_{r,r-1}\cong S^{-\sigma}_{r-1,r}\), exactly matching
the positive boundary of the row below. The signed resource ledger is
therefore compatible with actual tensor isomorphisms.

## 2. Composition on the full spaces

The composition lemma in `preliminaries.tex:29` asserts only the rules
needed here: exact parameter-independent pre- and post-maps preserve
the degree bound, and tensor products add the degrees of polynomials
having nonnegative exponents. It makes no unjustified additive-degree
claim for arbitrary compositions of degenerations.

The separator's polynomial, including its nonconstant terms, is stated
explicitly in `appendix-composition.tex:55`. Fourier cancellation forces
\(u-v+g-s=0\), and the exponent becomes \((g-s)^2\). The first-leg
reindexing uses the word indexed by \(g\), while the other two maps
use the word indexed by \(s\). These are valid linear maps even when
\(g\ne s\). Only the constant term needs the canonical sector
interpretation.

Tensoring the three orientations creates full direct-sum block labels on
every global leg. The final regrouping is defined independently on each
such block, so it is also defined when the three block labels in a
positive-degree monomial differ. This closes the potential gap between
a map defined only on the desired constant term and a map defined on
the whole polynomial.

Consequently each relation contributes three separator degrees, giving
\(D=3\sum_i(M_i-1)^2\), and the copy counts are precisely
\(S=\prod_i(2M_i-1)^3\) and \(H=\prod_iM_i^3\).

## 3. Occupations, conserved rounding, and the boundary catalyst

The occupation bounds used by the quantitative theorem can be derived
from the displayed drift estimate without assuming absorption first.
For the uniform excursion, summing the stopped nonnegative drift gives

\[
\mathbb E_i\sum_{t<\tau}\sqrt{h(X_t)}
\le \frac{\sqrt i}{\gamma},
\qquad \gamma=1-\frac{2\sqrt2}{3}.
\]

Both the visit count and the sum of \(\log(1+h)\) are bounded by
this charge. The harmonic change of probabilities multiplies path
weights by at most three. Accounting for resets gives the constants

\[
\frac6\gamma=54+36\sqrt2<105,
\qquad
\frac{3(\sqrt2+2)}\gamma=90+63\sqrt2<180.
\]

The exit probabilities give precisely the reset occupations in
`flows.tex:58`, and in particular \(\mu_r\le2\). Absorption from
every state makes the transient linear system nonsingular. Its rational
coefficients therefore give rational occupations by exact elimination.

The rounding algorithm in `rounding.tex:10` has the correct balance
signs. If the floored counts have incoming-minus-outgoing balance
\(b_v\), their increments need outgoing-minus-incoming balance
\(b_v\). The added source and sink edges impose exactly that
condition. The original fractional parts prove feasibility, and the
integer augmenting-path algorithm produces integer increments.
Keeping self-loops at their floors does not affect any balance.
Integer-target edges remain fixed, including the added return edge of
value \(K\).

After removal of that return edge, the resource identity has residual
source \(K S^+_{a,a}\) and residual output \(K\mathsf M_2\).
Its common multiplicity is \(U+T-K\). The boundary-catalyst assertion
at `extraction.tex:96` is correct: every source convolution factor has
both indices at least two. The only factor with an index equal to one
is the output at \(r=2,x=0\), namely \(S^{\sigma_2}_{2,1}\cong
\mathsf M_2\). Its source multiplicity is zero, so its coordinatewise
minimum is zero. There are no other boundary matrix factors to charge
in the catalyst rank product.

The entropy identity has the correct sign. Each action contributes

\[
w\log F_{\rm source}-\sum_y n_y\log F_y
=w(H(p)-\log d)+wD(p\Vert q).
\]

The reset contributes exactly \(z\log3\). Summing the conserved
ledger gives \(G=K\log F(a,a)-\mathcal L\). The lower bound
\(q_y\ge1/(3d)\) and strict edge errors imply
\(p_y/q_y<1+4d/w\), hence \(wD(p\Vert q)\le4d\).
Summing over all candidate coordinates gives \(\mathcal L\le4J_a\),
without requiring a lower bound on positive occupations.

## 4. Finite source dimensions and all overheads

The threefold rather than sixfold construction gives

\[
u=\prod_i d_i^{Nw_i},\qquad v=2^{NK}\prod_iM_i.
\]

The first factor is the product of the source auxiliary dimensions.
The second includes both the residual boundary \(\mathsf M_{2^{NK}}\)
and the separator auxiliaries. The source rank charge for
\(S^+_{a,a}\) is \((2a-1)^{3NK}\), with exponent three.

Exactification of the \(k\)-th power costs \(E=kD+1\) copies.
The exact restriction may then be reused \(j\) times with catalyst
exponent \(k\). Supplying that catalyst costs \(\kappa_N^k\),
not \(\kappa_N^{kj}\); interpolation costs \(E^j\). This gives
the stated source and target counts

\[
r_* = \kappa_N^k E^j S^{kj}(2a-1)^{3NKkj},
\qquad m_*=H^{kj}.
\]

No direct-sum multiplicity or catalyst has been canceled from a
restriction. The output catalyst can be restricted to coefficient one
in its natural convolution coordinates.

The multinomial bound applies after omitting zero child counts. For a
one-child action it reads \(1=1\), and the separator also remains
valid with \(M_i=1\). The reset's modal bound yields the single
\(\log(Nz_r+1)\) penalty. Therefore

\[
NG-\mathcal T_N\le\log(v/u)\le NG.
\]

Every source or output convolution index satisfies \(r+b-1<5a\),
including reset sources. Together with the common count \(U+T-K\),
this proves the catalyst rank bound used in `extraction.tex:245`.
The bound on interpolation follows from
\(M_i\le\exp(NH_i)\), and hence
\(E\le(3kI+1)\exp(2B_N)\). All three overhead bounds remain
valid when some actions have zero entropy or are omitted.

## 5. Pooled recursion

The pooled recursion in `extraction.tex:138` removes the repeated
rounding of the branching factor. Let \(q=r/m\). Flattening rank
gives \(q\ge(B/A)^2>1\). Pooling all products at one depth gives

\[
v_{\ell+1}=r\lceil v_\ell/m\rceil\le qv_\ell+r,
\qquad
v_\ell\le q^\ell\left(1+\frac r{q-1}\right).
\]

The grouping is algebraically valid across different parents. Input
transformations use only left inputs or only right inputs, and do not
depend on computed products. Thus all input transformations can be
performed forwards and all output combinations backwards through the
stored layered dependency graph. Grouping independent tasks into a
common batch does not change the restriction identity, even if their
input linear forms happen to be dependent.

For fixed scheme, each batch uses a fixed number of linear combinations
of blocks. There are \(\lceil v_\ell/m\rceil\le v_\ell\) batches,
so all additions and constant multiplications at that depth cost at most
\(C v_\ell n_\ell^2\). This includes output combinations as well as
input transformations. Scalar bilinear identities remain valid for
matrix blocks because every product retains the left-before-right
order and all coefficients are central scalars.

With \(\rho=A/B\), \(c=A/(1-\rho)\), and
\(n_*=\lceil c\rceil+1\), dimensions obey

\[
n_{\ell+1}-c\le\rho(n_\ell-c).
\]

They strictly decrease above the leaf threshold. For \(n>n_*\), at
most

\[
\left\lceil\log_{1/\rho}
\frac{n-c}{n_*-c}\right\rceil
=\log_{1/\rho}n+O(1)
\]

levels are needed. Summing
\(q^\ell(1+n^2\rho^{2\ell})\), including constant-size leaves,
gives \(O(n^p)\) for \(p=\log q/\log(1/\rho)>2\) and
\(O(n^2\log n)\) for \(p=2\). This verifies the coefficient
of the recursion depth as well as its order.

Dividing \(\log(r_*/m_*)\) by \(\log(B/A)\) gives exactly
the displayed pooled exponent. The additional \(\log2/(kj)\)
in \(\Phi\) belongs only to the comparison with the unpooled
schedule. It is not needed by the pooled algorithm.

## 6. Independent check of the explicit constants

For the prescribed family, set \(t=\log a\),
\(\ell=\lceil\log_2a\rceil\), \(K=a^3\ell^2\),
\(N=k=1\), and \(j=a\ell\). For \(a\ge2^{16}\),
\(t>8\), \(\ell\ge16\), \(\ell\le a\), and
\(\log K\le5t\).

The bounds \(J_a\le2a^3\), \(I\le2a^2\),
\(w_i\le180K+2a\), and \(z_r\le2K+1\) give

\[
\frac{4J_a+\mathcal T_1}{K}
\le\frac{41/2+(45/4)t}{\ell^2}
<\frac{41}{4t^2}+\frac{45}{8t}
\le\frac{221}{256}.
\]

The numerator constants come from three contributions:
\(8\) for \(4J_a/K\), \(12+10t\) for the action type
penalty, and at most \(1/2+5t/4\) for the resets. The last
display follows from \((\log2)^2<1/2\) and monotonicity of the
right side for \(t\ge8\).

The elementary lower bound
\(\log s_a\ge(\log a)/3-1/9\), together with
\(F(a,a)\ge a s_a\), gives

\[
\frac{\log(v/u)}K>\frac43t-1>0,
\]

because \(1/9+221/256<1\). Thus the relative dimensions really
contract in this specified family.

The normalized copy charge is at most one. For interpolation,
\(H_i\le180K+2a\log(2a)\) bounds every action, and also
dominates the reset entropy. Therefore

\[
\frac{\log E}K
\le360+\frac5{a\ell^2}\le361.
\]

Here \(\log(6a^2+1)\le2a\) and \(\log(2a)\le a\)
give respectively at most \(1/(a\ell^2)\) and
\(4/(a\ell^2)\) for the remaining terms.

The rounded count bound gives
\(U+T-K<184aK\). Hence

\[
\frac{\log\kappa_1}{jK}
\le552\frac{\log(5a)}\ell
<552\cdot\frac7{10}\left(1+\frac28\right)=483.
\]

Together with \(3\log(2a-1)<3t+3\), these bounds give a
normalized numerator less than \(3t+848\). The manuscript's
\(3t+850\) bound has room even for the unpooled ceiling charge.
Consequently

\[
p<\frac{3t+850}{4t/3-1}
=\frac94+\frac{850+9/4}{4t/3-1}
<\frac94+\frac{900}{t}.
\]

For the source dimension, \(\log A=jW\) and the rounded auxiliary
bound give

\[
\log A
\le a^5\ell^3
\left(180+\frac{2\log(2a)}{a\ell^2}\right)
\le181a^5\ell^3.
\]

The last step uses \(\log(2a)\le a\) and \(\ell\ge16\).
Thus both constants in Theorem `thm:quantitative` are justified, with
substantial slack.

The lower bound \(p\ge\tau_a>9/4\) uses only the nonnegative
overheads and \(\log(v/u)\le K\log F(a,a)\). The upper and
lower bounds therefore prove convergence to the stated endpoint, rather
than only an upper limit.

## 7. Effective parameter selection, field, and rational seed

The explicit selection

\[
\ell=\max\{16,\lceil1800/\varepsilon\rceil\},\qquad a=2^\ell
\]

uses exact integer and rational operations. Since \(\log2>1/2\),
it guarantees \(900/\log a<1800/\ell\le\varepsilon\).
The remaining four parameters are the displayed integer formulas.
The use of \(\lceil\log_2a\rceil\) for a general index is also
effective from integer bit lengths; it does not require a real-number
comparison oracle.

The occupation systems have proved unique rational solutions. The
rounding graph is finite and its integer augmenting-path procedure
terminates. Every subsequent type list, tensor product, separator, and
evaluation has a finite explicitly known size. The deterministic ordering
conventions are enough to specify a generator, although its runtime and
output size need not be useful.

The stated common field order includes the interpolation order \(E\),
the source evaluation order \(2a-1\), every separator order
\(2M_i-1\), and every catalyst evaluation order \(r+b-1\).
The determinant basis changes are integral and the other coordinate maps
are rational. Tensor reuse, padding, pooling, and recursion introduce no
new roots. Thus one fixed cyclotomic field contains all coefficients for
every input dimension after the allowance has been fixed.

The coefficient descent is valid coefficientwise and produces at most
\(d^2\) rational rank-one terms per original term, where \(d\)
is that fixed field degree. The pooled recursion remains separately
linear in the two inputs. Unrolling it therefore gives an explicit
bilinear decomposition, with length bounded by its arithmetic cost.
Applying the effective theorem at allowance \(\varepsilon/2\)
and descending coefficients leaves a fixed constant times
\(n^{9/4+\varepsilon/2}\) terms. The exact test
\(R_n^q<n^p\), for \(p/q=9/4+\varepsilon\), must eventually
hold. Enumeration of the generated identities thus terminates.

The quantitative bound on \(A\) is not a bound on this final rational
seed dimension. The manuscript states this distinction at
`quantitative.tex:155`; it is necessary and correct.

## Findings and limits

- **Fatal or major mathematical findings:** none.
- **Minor mathematical findings:** none.
- **Minor terminology:** `extraction.tex:348` says “unroll its batched
  recursion” after the lemma and section have been changed to “pooled
  recursion.” The statement is mathematically valid, since pooling still
  uses batches, but using “pooled” there would keep the terminology
  consistent. “Set the unused initial input pairs to zero” refers to the
  zero-filled first batch and is harmless.
- **Scope:** this review does not establish priority, validate numerical
  archives, or formally verify the complete proof. It checks the revised
  finite-algorithm argument and its stated quantitative bounds directly.

No unresolved mathematical objection from this review blocks the revised
finite-construction theorem.
