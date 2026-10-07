# Maximal-width profile flows have bounded auxiliary cost per row

Date: 2026-10-07. Original derivation using the local tensor relations;
no literature research.

The maximal-width multiway relation reduces the normalized auxiliary
logarithm from order $a^2$ to order $a$ over rows $2,\ldots,a$.
Its rational occupation weights conserve every tensor resource, and their
entropy identity has the same limiting exponent as the binary construction.
This note concerns rational frequencies. The subsequent
[conserved rounding algorithm](multiway-rounded-flow.md) supplies integer
counts at every positive scale, with a
[separate entropy-loss bound](multiway-rounding-analysis.md).
The [finite-cost analysis](multiway-finite-costs.md) combines these results
with type selection, separation, interpolation, and catalyst reuse.
No practical multiplication algorithm follows from the normalized cost
bound alone. Increasing the relation arity also increases the number of
type coordinates that must be controlled.

## The row and its exact occupation ledger

For row $r\ge2$, put $L=4r-1$. At each interior column $r\le b<L$, use

\[
h_b=\min(b-r+1,L-b),\qquad
C(r,b)B_X(h_b+1)\longrightarrow
\{C(r,b+h_b-2j):0\le j\le h_b\}.
\]

The arrow denotes the diagonal blocks of the determinant filtration,
followed by its fixed-type restriction; it does not assert a direct sum
restriction before separating the sectors. The condition $b\ge h_b+1$
holds because $r\ge2$. Every child lies in $[r-1,L]$.
The local filtration and its finite costs are checked in
[the multiway determinant note](multiway-determinant.md).

Shift to $x=b-r+1$, write $n=3r$, and put

\[
f(x)=c+x,\quad c=\tfrac32(r-1),\quad h(x)=\min(x,n-x).
\]

The profile is $F(r,b)=s_r f(x)$, including the boundary $x=0$.
The harmonic probabilities are

\[
q(x,y)=\frac{f(y)}{(h(x)+1)f(x)},\qquad
y=x-h(x),x-h(x)+2,\ldots,x+h(x).
\tag{1}
\]

They sum to one. State zero absorbs, while state $n$ resets to state one
by the tripling relation. Inject one unit at $i=1$ in the final row,
or $i=2$ in a lower row. Let $\lambda_x$ be the expected number of visits
to interior state $x$, and let $\mu$ count terminal visits. The finite
expectations proved below give the exact rational ledger

\[
\sum_{x=1}^{n-1}\lambda_x
 \left(e_x-\sum_yq(x,y)e_y\right)+\mu(e_n-e_1)=e_i-e_0.
\tag{2}
\]

Rationality follows by solving the finite nonsingular system
$(I-P^T)\lambda=e_i$, including the reset state. Zero occupation at
unreachable states is allowed. Alternating the threefold orientations by
row, as proved in [the cyclic construction](cyclic-profile-extraction.md),
then gives exactly $S^+_{a,a}-T_2$. No tensor catalyst is canceled.

## Finite absorption and a uniform cost bound

First consider the *uniform* walk $P_0(x,y)=1/(h(x)+1)$, killed at
either endpoint. It is a martingale. For

\[
g(x)=\sqrt{x}+\sqrt{n-x}-\sqrt n,\qquad
\gamma=1-\frac{2\sqrt2}{3}>0,
\]

one step obeys

\[
g(x)-\mathbb E_0[g(Y)\mid x]\ge\gamma\sqrt{h(x)}.
\tag{3}
\]

For $x\le n/2$, the children are $0,2,\ldots,2x$. Concavity and
the trapezoidal bound give

\[
\sum_{k=0}^x\sqrt k\le\tfrac23x^{3/2}+\tfrac12\sqrt x,
\quad
\mathbb E_0\sqrt Y\le\frac{2\sqrt2}{3}\sqrt x.
\]

Jensen's inequality handles $\sqrt{n-Y}$; the other half is symmetric.
Stopping (3) at a finite number of steps and using $g\ge0$ proves

\[
\mathbb E_{0,i}\sum_{t<\tau}\sqrt{h(X_t)}
 \le\frac{g(i)}\gamma\le\frac{\sqrt i}\gamma.
\tag{4}
\]

Because $h\ge1$ in the interior, absorption has finite expected time.
Also $\log(1+h)\le\sqrt h$: the derivative of
$\sqrt h-\log(1+h)$ is nonnegative. Thus (4) bounds both the number
of relation uses and the auxiliary logarithm of one excursion.

Equation (1) is a Doob transform of this killed walk. For a path ending
at time $t<\tau$, its probability is multiplied by $f(X_t)/f(i)$.
For every interior entry $i\ge1$, this factor is at most
$f(n)/f(i)\le3$. Therefore the
expected charge $C_i$ during one excursion satisfies

\[
C_i:=\mathbb E_{q,i}\sum_{t<\tau}\log(h(X_t)+1)
 \le\frac{3\sqrt i}\gamma.
\tag{5}
\]

The uniform walk exits at $n$ with probability $i/n$. Transforming its
exit distribution gives

\[
p_i=\frac{i f(n)}{n f(i)},\qquad p_1=\frac1r.
\]

After a terminal exit, the reset starts at state one. The total expected
charge is consequently $A_i=C_i+p_i C_1/(1-p_1)$, not a single
geometric multiplier based on the initial lower-row probability.
In particular,

\[
A_1\le\frac6\gamma<105,
\qquad
A_2\le\frac{3(\sqrt2+2)}\gamma<180.
\tag{6}
\]

These same bounds hold for the total number of interior relation uses.
They establish finite absorption for the walk with resets, the existence
of the occupation ledger, and the uniform bound claimed above. Equation (5)
and the same reset formula give finite expectation from every other
interior entry as well, proving that the full transient matrix is
nonsingular. Moreover,
the tripling occupations are **exactly** the old binary weights:

\[
\mu_1=\frac1{r-1},\qquad
\mu_2=\frac{2(3r-1)}{(r-1)(3r+1)}.
\tag{7}
\]

## What improves, and what remains charged

Over all rows, (6) gives

\[
\sum_{r,b}\lambda_{r,b}\log(h_b+1)
 \le105+180(a-2)=O(a).
\]

The old binary weights have sum $\Theta(r)$ in each row, hence
$\Theta(a^2)$ over all rows. For example, their explicit formulas are
bounded below by a positive constant on $2r\le b<3r$, and above by six
everywhere. This is a reduction in the **normalized source auxiliary
logarithm**, before integer scaling and the other finite costs.

For the exact harmonic probabilities,

\[
\log2+\sum_{r,b}\lambda_{r,b}
 \bigl(H(q_{r,b})-\log(h_b+1)\bigr)
 +\sum_r\mu_r\log3=\log F(a,a).
\tag{8}
\]

This follows directly from (1), (2), and $f(n)=3f(1)$.
Thus the limiting profile exponent remains
$3\log(2a-1)/\log F(a,a)\to9/4$. At an integer scale $K$, the
threefold source side would contain
$u=\prod_{r,b}(h_b+1)^{NK\lambda_{r,b}}$ if all exact target frequencies
were integral. No small-denominator claim is made for these rational
weights. Conserved integer rounding instead changes the frequencies and
charges their entropy loss. Separation, interpolation, catalyst reuse,
and their arithmetic costs also remain.

There are at most $3r-1$ actions in a row and at most
$(3r-1)(\lfloor3r/2\rfloor+1)$ type coordinates. Summed over rows,
these are $O(a^2)$ actions and $O(a^3)$ type coordinates. The smaller
expected auxiliary charge therefore does not by itself bound the finite
type loss or prove a practical-size improvement.

## Small exact checks

The [reproducible experiment](../experiments/multiway_profile_flows.py)
solves both injection cases for $2\le r\le12$ over rational numbers.
It checks all 22 row ledgers, exact agreement of a separate binary solve
with the previous closed formulas, the unchanged tripling weights, and
11 alternating signed global ledgers. Entropy residuals are diagnostic
floating-point checks; they are not used to certify the proof.

| Final index | Multiway auxiliary log charge | Binary charge | Active actions | Active type coordinates |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 6.879356 | 10.628257 | 3 | 8 |
| 4 | 23.287148 | 50.483119 | 17 | 61 |
| 8 | 60.421470 | 210.317409 | 72 | 396 |
| 12 | 99.535379 | 479.885439 | 163 | 1217 |

All charges use natural logarithms and normalization $K=1$, with rational
frequencies rather than an integer tensor recipe.

```sh
python -m experiments.multiway_profile_flows > results/multiway-profile-flows.json
```

Exact occupation weights and the checks are saved in
[the result](../results/multiway-profile-flows.json).
An [independent review](multiway-profile-review.md) reproduces all 22
occupation vectors by solving the uniform killed chain first, then
applying the change of measure and reset formula. It found no blocking
defect in the global flow argument, conditional on the separately checked
local tensor relation.
