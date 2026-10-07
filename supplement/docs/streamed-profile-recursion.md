# What streaming changes in the relative matrix recursion

Date: 2026-10-07. Original derivation from the local tensor constructions;
no literature research or parameter search.

Streaming can avoid allocating a dense auxiliary matrix. It does not by
itself reduce the arithmetic charged for multiplying that matrix. The source
side in the [rounded recipe](rounded-profile-flows.md) is a floor for its
unchanged recursive calls, not an invariant minimum input size for every
algorithm that might be extracted from the tensor relation.

This distinction permits a real counterexample to an overly broad size
claim, a precise tiling tradeoff, and a storage-independent obstruction for
the prescribed full-source-call execution. None rules out a new compiler
that simplifies the particular transformed operands.

## A large source side is not a tensor invariant

Write the exact relative relation as

\[
rT_A\ge mT_B,\qquad B>A,\qquad q=r/m,
\qquad c=B/A.
\tag{1}
\]

The inequality includes specified linear maps, rather than just ranks.
For the existing batch execution, an input side \(n\) gives source calls
of side

\[
n'=A\lceil n/B\rceil\ge A.
\tag{2}
\]

Thus this unchanged recursion cannot contract an input below \(A\).
It can still accept such an input by using a leaf algorithm. Changing
finitely many input sizes to use a practical leaf leaves its asymptotic
exponent unchanged, but supplies no finite speed improvement from (1).

There is no general theorem that the displayed \(A\) must be retained.
For a concrete counterexample, tensor the repository's
[verified rank-48 relation](rank48-execution.md)
\(48T_1\ge T_4\) with an arbitrary \(T_C\). This gives

\[
48T_C\ge T_{4C}
\]

with an arbitrarily large source side. Its maps are the original maps
tensored with the identity. Restricting the common \(T_C\) to one scalar
coordinate recovers the original small rank-48 algorithm. The huge source
side was redundant in those particular maps.

In the profile recipe, the auxiliary factors enter determinant maps that
use them to enlarge the output convolution. They are not displayed as a
common identity on source and target. Already in
\(C(r,b)\otimes B_X(2)\), keeping the up block \(C(r,b+1)\) needs a
second-leg flattening rank of \(b+1\). Fixing \(B_X(2)\) to a scalar
leaves that source leg with dimension \(b\), so this simple local
restriction cannot preserve the up block. Every rounded split has a
positive up count. This identifies why deleting auxiliary coordinates does
not commute with the stated determinant step. It is not a proof against
joint simplifications after composing many maps.

## Streaming full source calls retains their arithmetic charge

One can generate transformed entries on demand, run scalar or tiled loops,
and immediately accumulate requested outputs. With suitable coefficient
access, no dense \(A\times A\) temporary must be resident. Repeated
coefficient evaluation and input scans can instead increase the work. The
stored coefficient maps may also remain large.

Consider the specific execution model that retains complete exact bilinear
circuits for unrestricted source matrix products. The flattening rank of
\(T_A\) is \(A^2\), so each such circuit has at least \(A^2\) bilinear
scalar products. A circuit solving \(r\) unrestricted independent source
products has flattening rank \(rA^2\), even if it shares work between those
products. Hence the optimistic charge per useful target product in (1) is
at least

\[
qA^2.
\tag{3}
\]

Using fewer than \(m\) useful outputs, retaining zero-filled calls, or
rounding a batch upwards cannot reduce this average charge. Padding an
input with \(n<B\) still gives side \(A\) in (2); larger block sizes only
increase it.

For the prescribed subcubic profile counts, the
[conservation bound](rounded-profile-practical-size.md) gives \(A\ge2^{32}\),
while the exact count formula gives
\(q\ge(2a-1)^{6NKkj}\ge729\). Thus (3) is at least

\[
729\cdot2^{64}=13\,447\,676\,429\,734\,263\,128\,064.
\tag{4}
\]

In particular,

\[
23\,780\,213^3 <729\cdot2^{64}<23\,780\,214^3.
\]

For every \(n\le23,780,213\), this retained full-call charge exceeds
classical multiplication's \(n^3\) scalar-product count. It is a necessary
count screen for this execution model, not a runtime lower bound or a
predicted crossover. It needs no assumption that dense source arrays are
allocated. The exact arithmetic is reproducible with:

```python
assert 23780213**3 < 729 * 2**64 < 23780214**3
```

The qualification about retained unrestricted circuits is essential.
Actual source operands are correlated linear forms in the target inputs.
Their composed function need not have the full source flattening rank.
Removing zero products, discarding unused outputs, exploiting those
correlations, or sharing work only on the reachable operands changes the
charged computation. Equation (3) is not a lower bound on such a new
specialized circuit.

## Classical tiling lowers the child side at a counted cost

Let \(P\mid A\), and set \(L=A/P\). Partitioning a full source product
into \(L\times L\) blocks and using the classical block formula requires
\(L^3\) products of side \(P\). Therefore (1) gives the exact relation

\[
rL^3T_P\ge mT_B.
\tag{5}
\]

The fixed-batch recursion now has child side
\(P\lceil n/B\rceil\), branch count \(\lceil qL^3\rceil\), and
arithmetic exponent

\[
\theta_P=
\frac{\log\lceil qL^3\rceil}{\log(B/P)}
=\frac{\log\lceil qL^3\rceil}{\log c+\log L}.
\tag{6}
\]

As usual, take the maximum with 2 and a logarithmic factor in the equality
case. Flattening (1) gives \(rA^2\ge mB^2\), so \(q\ge c^2>1\).
Put \(p_* = \log q/\log c\) and \(t=\log L/\log c\). Retaining the
ceiling in (6) gives the exact bounds

\[
\frac{p_*+3t}{1+t}\le\theta_P
\le\frac{p_*+3t}{1+t}
   +\frac{\log2}{\log c+\log L}.
\tag{7}
\]

The left expression is a relaxed lower bound for this fixed-batch recipe,
not its exact exponent. When \(p_*<3\), it increases towards 3 as
\(A/P\) grows relative to \(B/A\). Thus classical source tiling can
remove the large child-size floor, but does not preserve the original
raw-ratio exponent.

For a desired exponent \(\rho<3\), a necessary condition for
\(\theta_P<\rho\) is

\[
\frac{\log(A/P)}{\log(B/A)}
 <\frac{\rho-p_*}{3-\rho}.
\tag{8}
\]

This applies in particular to the verified rank-40 exponent
\(\rho=3\log40/\log54\). The right side must be positive.
A sufficient condition for the count comparison adds the ceiling allowance:

\[
(3-\rho)\log(A/P)
 <\rho\log(B/A)-\log q-\log2.
\]

Using another specified rank algorithm for the block-index multiplication
replaces \(L^3\) by its actual rank count \(R_L\) in (5)-(6).
If that count behaves like \(L^\sigma\), the corresponding relaxed
weighted average uses \(\sigma\) in place of 3, with any multiplicative
constant still charged. Accordingly, (8) excludes only the classical
tiling proposal. It is not an obstruction to all possible source algorithms.

Tiling leaves the target side \(B\), interpolation evaluations, catalyst
copies, and tensor maps unchanged. When \(P<n<B\), applying (5) still
means using the \(B\)-block template with mostly zero scalar blocks and
paying its retained source calls. Its vast fixed work is absent from an
exponent considered by itself. A small \(P\) and an improved asymptotic
exponent therefore do not demonstrate finite speed.

## Pooling batches removes only the rounding overhead

There is a constructive scheduling refinement to the original batch lemma.
At each recursion depth, all source tasks have the same matrix side. Pool
them across parents before forming batches of size \(m\). If their number
is \(v_\ell\), then

\[
v_{\ell+1}=r\left\lceil\frac{v_\ell}{m}\right\rceil
\le qv_\ell+r,
\qquad
v_\ell\le q^\ell\left(v_0+\frac r{q-1}\right).
\tag{9}
\]

Thus the task count grows with \(q\), not \(\lceil q\rceil\). All
linear preprocessing at a level precedes its source products; after the
leaves, process the output recombinations in reverse order. These
dependencies permit level pooling, though storage or recomputation can be
substantial.

For \(h=AB/(B-A)\), the usual padding bound gives
\(n_\ell\le h+c^{-\ell}(n-h)\). Stop above a fixed threshold exceeding
\(h\). The linear-map cost per level is
\(O(v_\ell n_\ell^2)\), with fixed map-dependent constants. Summing over
levels gives exponent

\[
\max\{2,\log q/\log c\},
\]

with the usual logarithmic factor at equality. Under this revised scheduler,
the relaxed expression on the left of (7) is an attainable exponent for
the tiled relation. The improvement removes the ceiling penalty, not the
source side, target side, copy counts, or the charges in (3)-(5).

The integer conservation, type restriction, and interpolation formulas
therefore still lack a useful finite implementation. A meaningful escape
would require an explicit simplification of the composed reachable source
forms, with its new bilinear count and linear-map cost verified. Streaming
alone does not supply that simplification, and the source-size argument
alone cannot rule it out.

Independent reviews checked the tensor-inflation counterexample, local
determinant flattening argument, fixed-batch tiling inequalities, full-call
scalar-product charge, and pooled scheduling with its linear-map costs.
No blocking issue was found. These reviews establish the stated execution
results; they do not supply or exclude a specialized circuit for the
composed profile maps.
