# The scalar profile axioms have an exact least solution

The scalar axioms in the preserved manuscript determine a sharp lower bound,
including away from the diagonal. An explicit profile attains that bound and
satisfies the manuscript's scalar upper bound with `t = 3/4`. Therefore these
axioms alone cannot improve the diagonal growth exponent beyond `4/3` or force
`t < 3/4`. This closes one possible route to a stronger exponent. It does not
give a matrix multiplication algorithm or establish that the profile arises
from an actual tensor character.

This is an original calculation from the equations in
[the local manuscript](../upstream/build/paper.tex), not a literature result.
The mathematical proof below is independent of the numerical experiments.
It does not verify the manuscript's derivation of the scalar axioms from
tensors.

Let `P` be positive and symmetric on pairs of positive integers, and assume

\[
P(1,b)=b,\qquad
2P(a,b)\ge P(a,b-1)+P(a,b+1)\quad(b\ge2),
\]

\[
P(a,3h+a-1)\ge3P(a,h)\quad(h\ge1).
\]

Define the rational sequence

\[
s_1=1,\qquad
s_a=\prod_{j=1}^{a-1}\left(1+\frac1{3j}\right),
\]

and, with `m = min(a,b)` and `n = max(a,b)`, define

\[
F(a,b)=s_m\left(n+\frac{m-1}{2}\right).
\tag{1}
\]

**Exact result.** The function `F` satisfies every displayed axiom. Every
function `P` satisfying those axioms obeys `P(a,b) >= F(a,b)` at every pair.
Moreover,

\[
F(a,b)\le(a+b-1)^{4/3}.
\tag{2}
\]

To verify feasibility, positivity, symmetry, and `F(1,b)=b` follow directly
from (1). For fixed `a`, the row is affine in `b` once `b >= a`, with slope
`s_a`. Substitution of

\[
\frac{s_{b+1}}{s_b}=\frac{3b+1}{3b},\qquad
\frac{s_{b-1}}{s_b}=\frac{3b-3}{3b-2}
\]

gives the exact concavity slack

\[
2F(a,b)-F(a,b-1)-F(a,b+1)=
\begin{cases}
\displaystyle\frac{2(a-b)s_b}{3b(3b-2)},&2\le b\le a,\\[6pt]
0,&b>a.
\end{cases}
\tag{3}
\]

At `b=a`, the recurrence for `s_a` makes the two branches meet with the same
increment, so (3) also covers that boundary. Every slack is nonnegative.

Concavity and the affine tail show that the extension of the tail lies above
the whole row:

\[
F(a,h)\le s_a\left(h+\frac{a-1}{2}\right).
\tag{4}
\]

For `h<a`, sum the increments between `h` and `a`: each is at least the tail
slope `s_a`. For `h>=a`, (4) is equality. Since `3h+a-1 >= a`,

\[
F(a,3h+a-1)
=3s_a\left(h+\frac{a-1}{2}\right)
\ge3F(a,h).
\]

This proves shifted tripling.

To prove minimality, first retain the stronger finite recurrence from the
manuscript instead of replacing it by a power. Set

\[
D_a=P(a,a),\qquad K_a=\frac{2D_a}{3a-1},\qquad
\Delta_{a,h}=P(a,h+1)-P(a,h).
\]

Tripling at `h=a` and decreasing row increments imply

\[
2D_a\le P(a,4a-1)-P(a,a)
\le(3a-1)\Delta_{a,a},
\]

so `Delta_(a,a) >= K_a`. Symmetry and concavity then give, for `a>=2`,

\[
D_a-D_{a-1}
=\Delta_{a-1,a-1}+\Delta_{a,a-1}
\ge K_{a-1}+K_a.
\]

Substitution of `D_a=(3a-1)K_a/2` yields

\[
K_a\ge\frac{3a-2}{3a-3}K_{a-1}.
\]

Because `K_1=1`, induction gives `K_a>=s_a` and therefore

\[
P(a,a)\ge\frac{3a-1}{2}s_a=F(a,a).
\tag{5}
\]

For an off-diagonal pair `m<n`, take tripling landmarks

\[
x_0=m,\qquad x_{j+1}=3x_j+m-1,
\]

until `x_j>=n`. Iteration gives

\[
x_j-m=(3^j-1)\frac{3m-1}{2},\qquad
P(m,x_j)\ge3^jP(m,m).
\]

A discrete concave sequence lies above the chord between any two of its
points. Applying this between `m` and `x_j` yields

\[
\begin{aligned}
P(m,n)
&\ge P(m,m)
 +\frac{n-m}{x_j-m}\bigl(P(m,x_j)-P(m,m)\bigr)\\
&\ge\frac{2P(m,m)}{3m-1}
 \left(n+\frac{m-1}{2}\right)\\
&\ge s_m\left(n+\frac{m-1}{2}\right)=F(m,n).
\end{aligned}
\tag{6}
\]

This proves pointwise minimality. Each bound uses only finitely many original
constraints; no limiting interchange or assumption about slopes at infinity
is needed. For the diagonal target `(a,a)`, a square grid through `4a-1`
suffices. For a general target `(m,n)`, a grid through
`max(4m-1,x_j)` suffices, where `x_j` is the first landmark at least `n`.

For the upper bound (2), the recurrence also gives

\[
s_a^3\le\frac{3a-1}{2}.
\tag{7}
\]

The base case is equality. The induction step is equivalent to

\[
(3a+2)(3a)^3-(3a-1)(3a+1)^3=6a+1>0.
\]

Writing `S=m+n-1`, both `(3m-1)/2 <= S` and
`n+(m-1)/2 <= S`, since `n>=m>=1`. Thus

\[
F(m,n)^3
=s_m^3\left(n+\frac{m-1}{2}\right)^3
\le S^4,
\]

which is (2). Consequently the same explicit model meets the manuscript's
additional scalar condition `P(a,b) <= (a+b-1)^(1/t)` at `t=3/4`.

The exact finite diagonal bound is

\[
F(a,a)=\frac{3a-1}{2}
\frac{\Gamma(a+1/3)}{\Gamma(4/3)\Gamma(a)}
\sim\frac{3}{2\Gamma(4/3)}a^{4/3}
\approx1.6797697826\,a^{4/3}.
\]

It improves the constant over `a^(4/3)` but has the same exponent. The first
nontrivial values are `F(2,2)=10/3`, `F(3,3)=56/9`, and `F(4,4)=770/81`.
The profile (1) attains every inequality used in the diagonal recurrence.
Taking more instances of the same scalar axioms, optimizing their weights,
or enlarging the linear program cannot give a stronger pointwise lower bound.
Additional tensor structure could impose constraints absent from this scalar
relaxation; this result does not rule out that possibility.

[The experiment](../experiments/profile_bounds.py) checks all constraints on
a finite grid with exact rational arithmetic. Optional SciPy linear programs
minimize individual entries over symmetric, nonnegative finite profiles with
the specified boundary, concavity, and tripling constraints. Strict
positivity is relaxed to nonnegativity in the LP. The upper bound (2) is
omitted there; adding it cannot change the optimum because (1) satisfies it.
The proof above supplies exact optimality; solver output is only numerical
corroboration.

Reproduce the saved experiment from the repository root:

```sh
python experiments/profile_bounds.py --max-index 64 \
  --lp-target 2,2 --lp-target 3,3 --lp-target 4,4 \
  --lp-target 8,8 --lp-target 16,16 --lp-target 2,10 \
  --lp-target 7,30 --output results/profile-extremal.json
python -m pytest -q tests/test_profile_bounds.py
```

[The saved result](../results/profile-extremal.json) records exact checks on
all 4,096 entries of the `64` by `64` grid, including 3,968 concavity and 672
tripling inequalities. All seven finite LP objectives agree with the proved
minimum within `2.2e-13`; their largest reported constraint violation is below
`4.9e-11`. The largest LP has 3,828 variables and 8,642 inequalities. The nine
tests in the initial experiment passed, covering exact axiom checks, recurrence equality, independent LP
objectives, and index validation. These measurements are verification of the
scalar calculation, not matrix multiplication benchmarks.

The practical research consequence is specific: stop searching for a better
exponent by strengthening only the existing scalar-profile optimization.
The next useful work must provide additional valid tensor constraints or an
explicit rank decomposition with controlled finite costs. Neither is supplied
by the extremal profile.

The sharp finite bound also exposes the scale of the scalar argument before
any tensor-power construction. Comparing (5) with the manuscript's upper
bound gives, at each `a>=2`,

\[
\tau=3t\le\tau_a:=\frac{3\log(2a-1)}{\log F(a,a)}.
\]

Here `tau_a` is an inferred bound from a single scalar comparison. It is not
the exponent of an implemented algorithm. Since (2) is strict on the diagonal
for `a>1`, every finite `tau_a` is strictly greater than `9/4`.

Put `c=3/(2 Gamma(4/3))` and `y=log a`. Then

\[
\tau_a-\frac94
=\frac{3\log2-(9/4)\log c}{(4/3)y+\log c}
 +O\!\left(\frac1{ay}\right)
\sim\frac{0.6843478909}{\log a}.
\]

For a target `tau>9/4`, neglecting the vanishing finite-`a` corrections gives
the explicit estimate

\[
\log a\approx
\frac{3\log2-\tau\log c}{(4/3)\tau-3}.
\tag{8}
\]

The resulting profile indices are:

- For a bound of `2.5`, the smallest index is **10**, certified by exact
  rational comparisons for all indices from 2 through 10.
- For `2.4`, the smallest index is **63**, certified in the same way.
- For `2.3`, the numerical crossing occurs between **595,974 and 595,975**.
  A stable direct logarithmic sum gives respective bounds
  `2.300000003321948` and `2.299999997192370`. This is a numerical crossing,
  not an exact minimality certificate for the full integer sequence.
- For `2.26`, the scale estimate is **3.564 times 10^29**.
- For `2.251`, the scale estimate is **1.095 times 10^297**.

These are profile indices in this particular proof. They are neither matrix
multiplication seed dimensions nor lower bounds on the resources needed by
other constructions. They exclude the cost of finding a rank decomposition
and every subsequent tensor-power or interpolation cost.

To control the approximation without subtracting nearly equal large
`lgamma` values, log-convexity of the Gamma function gives

\[
a^{1/3}\left(1+\frac1{3a}\right)^{-2/3}
\le\frac{\Gamma(a+1/3)}{\Gamma(a)}\le a^{1/3}.
\]

The upper inequality follows by interpolating between `Gamma(a)` and
`Gamma(a+1)` in logarithms. For the lower inequality, interpolate between
`Gamma(a+1/3)` and `Gamma(a+4/3)` to bound `Gamma(a+1)`, then use
`Gamma(a+4/3)=(a+1/3)Gamma(a+1/3)`. Thus the exact logarithm of the diagonal
lies between

\[
\frac43y+\log c+\log\left(1-\frac1{3a}\right)
 -\frac23\log\left(1+\frac1{3a}\right)
\]

and the same expression without the last term. Combining these inequalities
with

\[
\log(2a-1)=y+\log2+\log\left(1-\frac1{2a}\right)
\]

provides analytic lower and upper bounds for `tau_a`. They remain stable
when evaluated as functions of `y` using `log1p` and `exp(-y)`. The finite
correction to `log F` is of order `1/a`; this is negligible at the two very
large scales above. Binary64 evaluation of these formulas is not certified
interval arithmetic, so those scales are explicitly estimates, reported to
four significant figures. Evaluating the envelopes at (8) plus or minus
`0.001` in `log a` places the target between them, giving a numerically checked
localization of about 0.1 percent around each large scale. The saved results
include these checks.

For the first two targets, no numerical logarithms are needed to certify the
minimum: for a rational target `p/q`, the exact criterion is
`F(a,a)^p >= (2a-1)^(3q)`. The implementation scans the finite index ranges
using rational arithmetic.

Reproduce [the finite-scale results](../results/profile-finite-costs.json):

```sh
python experiments/profile_bounds.py --max-index 64 --finite-costs \
  --output results/profile-finite-costs.json
python -m pytest -q tests/test_profile_bounds.py
```

All 11 tests pass after this extension. The additional tests check the exact
finite thresholds and compare the analytic envelopes with direct product
evaluations, including an index logarithm too large for direct binary64
representation of the index itself.
