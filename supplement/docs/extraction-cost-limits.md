# Parameter tuning cannot make the prescribed small-profile extraction practical

For the exact counts and full-batch recursion in
[the small-profile construction](small-profile-extraction.md), every choice
of positive integers `N,k,j` whose branch-count exponent beats
`rho = log(48)/log(4)` requires a recursive input block dimension `a` with
**more than 11.37 billion decimal digits**. Already one separator needs more
than `10^1206` Fourier coordinates. These are necessary bounds, not the
outcome of a numerical parameter search.

The conclusion concerns the actual prescribed counts
`p_batch = log(ceil(r/m))/log(b/a)`, not merely the program's conservative
sufficient upper expression for them. It applies to materializing and
executing that full-batch schedule, with its specified interpolation and
catalyst decomposition. It does not cover a compiler that reduces those
counts, prunes zero branches, fuses tensor maps, replaces the catalyst rank
decomposition, or uses a different exactification. It is not a lower bound
for arbitrary matrix multiplication algorithms or all uses of the same
tensor relation.

This is an original analysis of the local construction. No literature search
was performed. A second agent independently checked the inequalities and
the exact rational numerical certificates.

Keep the construction's notation. In particular,

\[
a=2^{460Nkj},\qquad b=t^{kj},\qquad
E=kD+1,\qquad D=6\sum_{i=2}^7(M_i-1)^2,
\]

\[
\frac rm=\kappa^k E^j(S/H)^{kj}729^{15Nkj},\qquad
\Delta_N=\log(t/s)>0.
\]

All logarithms below are natural unless a base is written. Define

\[
\begin{aligned}
\rho&=\frac{\log48}{\log4},\\
\delta&=30\rho\log(10/3)-90\log3
       \approx1.9870384806,\\
\gamma&=6\bigl(35\log3+56\log4+54\log5
               +44\log6+26\log7+15\log8\bigr)
       \approx2181.6975914653,\\
\mu&=\log\binom{56}{36}\approx34.2974861363.
\end{aligned}
\]

Thus `log kappa = N gamma`. Since `ceil(r/m) >= r/m`, a necessary condition
for `p_batch < rho` is

\[
\frac{\log E}{k}+\frac{N\gamma}{j}
<\rho\Delta_N-90N\log3-\log(S/H)
\le\rho\Delta_N-90N\log3.
\tag{1}
\]

Dropping the positive copy-ratio charge and the ceiling loss makes this a
more permissive condition. A lower bound derived from (1) therefore cannot
be an artifact of overestimating either cost.

The fixed-type sector counts have a finite entropy loss. Let

\[
(w_i)=(50,56,54,44,26),\quad
(u_i)=(35,36,33,26,15),\quad
(d_i)=(15,20,21,18,11).
\]

Set

\[
C_0=\frac12\sum_{i=1}^5\log\left(\frac{6u_id_i}{w_i}\right)
       +\log6+\frac32\log5-\frac12\log15
       \approx13.1660140749,
\]

\[
\eta=\sum_{i=1}^5\frac1{12w_i}+\frac1{180}
       \approx0.01535259494.
\]

The standard one-sided Stirling bound

\[
\log(n!)=(n+\tfrac12)\log n-n+\tfrac12\log(2\pi)+r_n,
\qquad0<r_n<\frac1{12n}
\]

gives, for each binomial sector count,

\[
\log\binom{w_iN}{u_iN}
\le N(w_i\log w_i-u_i\log u_i-d_i\log d_i)
 -\tfrac12\log N
 -\tfrac12\log(2\pi u_id_i/w_i)
 +\frac1{12w_iN}.
\]

For the three-sector count `(15N)!/(5N)!^3`, the corresponding correction
is at most

\[
-\log N-\log(2\pi)+\tfrac12\log15
 -\tfrac32\log5+\frac1{180N}.
\]

Replacing `2 pi` by the smaller number 6 weakens these upper bounds.
Summing them and using the construction's exact entropy identity gives

\[
\Delta_N
\le30N\log(10/3)-7\log N-2C_0+\frac{2\eta}{N}.
\tag{2}
\]

Combining (1) and (2), its right-hand side is at most

\[
F(N)=\delta N-\rho\left(7\log N+2C_0-\frac{2\eta}{N}\right).
\]

The function is convex for all real `N>=1`, because

\[
F''(N)=\rho\left(\frac7{N^2}+\frac{4\eta}{N^3}\right)>0.
\]

Exact rational logarithm enclosures give

\[
F(1)<-71.4589,\qquad F(80)<-0.224635.
\]

A convex function is at most the chord between two endpoints. Consequently
`F(N)<0` throughout `[1,80]`, whereas the left side of (1) is positive.
Every successful integer choice must therefore have **N>=81**.

For `N>=81`, the finite entropy penalty in parentheses increases with `N`.
Define

\[
\beta=\rho\left(7\log81+2C_0-\frac{2\eta}{81}\right)
       \approx159.4305544189.
\]

Then (1) requires

\[
\frac{\log E}{k}+\frac{N\gamma}{j}<\delta N-\beta.
\tag{3}
\]

It remains to charge even an optimistic interpolation cost. Selecting 36
positions independently in each of `N` blocks of 56 positions proves

\[
M_3=\binom{56N}{36N}\ge\binom{56}{36}^{N}.
\]

Because `M_3>=2`,

\[
E=kD+1\ge6(M_3-1)^2+1\ge M_3^2,
\qquad\log E\ge2N\mu.
\tag{4}
\]

Use (4) in (3). The arithmetic-geometric mean inequality gives

\[
\frac{2N\mu}{k}+\frac{N\gamma}{j}
\ge2N\sqrt{\frac{2\mu\gamma}{kj}},
\]

so

\[
Nkj>
\frac{8\mu\gamma N^3}{(\delta N-\beta)^2}.
\]

The denominator must be positive in (3). For every `x>1`,
`4x^3-27(x-1)^2=(x-3)^2(4x-3)>=0`. Substituting `x=delta N/beta`
therefore eliminates all three free parameters:

\[
Nkj>
\frac{54\mu\gamma\beta}{\delta^3}
>82{,}111{,}374.98.
\tag{5}
\]

In particular,

\[
\log_{10}a
=460Nkj\frac{\log2}{\log10}
>11{,}370{,}273{,}954.02.
\tag{6}
\]

The lower bounds deliberately ignore several positive costs. Tuning `N,k,j`
cannot make the prescribed schedule practical while retaining its actual
branch exponent below the rank-48 exponent. This is a stopping criterion for
parameter tuning of this recipe, not for research on different maps.

There is an earlier materialization problem as well. From `N>=81` and the
same elementary binomial bound,

\[
\log_{10}M_3\ge81\frac\mu{\log10}>1206.
\]

Thus even one separator's length `L_3=2M_3-1` exceeds `10^1206`.
Representing the integers or linear maps symbolically is possible;
materializing their arrays is not.

The Fourier transformations themselves do have much smaller linear circuits
than their dense coefficient matrices suggest. In the smaller separator,
the three families of coefficients are

\[
\zeta^{rg},\qquad
\zeta^{r(u-h)},\qquad
L^{-1}\zeta^{-rv},\qquad L=2M-1.
\]

For each internal coordinate, these are a zero-padded discrete Fourier
transform, a Fourier transform followed by a diagonal phase, and an inverse
Fourier transform with a scale factor. A dense implementation uses `O(LM)`
scalar operations per internal coordinate. Fourier circuits reduce this to
`O(L log L)`. This remains possible when `L` is inconvenient for direct
radix decomposition: take a primitive `2L`th root `xi` with `xi^2=zeta` and
use

\[
\zeta^{rg}=\xi^{r^2}\xi^{g^2}\xi^{-(r-g)^2}.
\]

After diagonal scalings, the transform is a convolution, which can be
embedded in a power-of-two Fourier transform of length `O(L)`. This is an
explicit factorization of the linear maps; no dense `L` by `M` matrix needs
to be stored.

The determinant basis changes are sparse two-term maps. Their tensor powers,
the small convolution evaluation maps, and the separator transforms can
likewise be applied factor by factor and streamed. Those changes reduce
linear work and temporary storage. They do **not** change the number of
independent bilinear source calls counted by `r`, the required batch size
`m`, or the huge source dimensions in (6). A linear circuit implementing a
Fourier transform and a tensor-rank reduction are different resources.

The first step that requires mixing many coordinates is the separator's
Fourier filter, which makes a shared first leg distinguish the sector label.
The preceding equal-type restrictions are coordinate projections after
sparse basis changes. The later interpolation uses another family of phase
evaluations. Improving those two mixing steps so that their bilinear work
can be shared, finding a much cheaper catalyst decomposition, or replacing
the simultaneous-output batch reduction would change the proof's cost
model. Those are actionable mathematical changes. Generating the existing
dense linear maps more efficiently is insufficient.

The following short calculation reproduces the essential numerical
certificates using the exact rational logarithm bounds already implemented
by the construction. It does not enumerate parameter choices or retest the
original map code.

```python
from fractions import Fraction
from math import comb
from experiments.small_profile_extraction import (
    Interval as I, WEIGHTS, UP_COUNTS, DOWN_COUNTS, CATALYST, sum_intervals,
)

l2, l3, l10 = (I.log_integer(n) for n in (2, 3, 10))
rho = I.log_integer(48).divide_positive(I.log_integer(4))
x = l10 - l3
delta = I(30*rho.lower*x.lower - 90*l3.upper,
          30*rho.upper*x.upper - 90*l3.lower)
gamma = sum_intervals(I.log_integer(b+1).scale(6*c)
                      for b, c in CATALYST.items())
mu = I.log_integer(comb(56, 36))
C0 = sum_intervals(
    (I.log_integer(6*u*d) - I.log_integer(w)).scale(1, 2)
    for w, u, d in zip(WEIGHTS, UP_COUNTS, DOWN_COUNTS)
) + I.log_integer(6) + I.log_integer(5).scale(3, 2) \
  - I.log_integer(15).scale(1, 2)
eta = sum((Fraction(1, 12*w) for w in WEIGHTS), Fraction(1, 180))

def penalty(n):
    return I.log_integer(n).scale(7) + C0.scale(2) \
        - I.exact(1).scale(2*eta.numerator, n*eta.denominator)

def endpoint_upper(n):
    return n*delta.upper - rho.lower*penalty(n).lower

assert endpoint_upper(1) < 0 and endpoint_upper(80) < 0
beta_lower = rho.lower*penalty(81).lower
nkj_lower = 54*mu.lower*gamma.lower*beta_lower / delta.upper**3
digits_lower = 460*nkj_lower*l2.lower/l10.upper
assert digits_lower > 11_370_000_000
assert 81*mu.lower/l10.upper > 1206
print(digits_lower.numerator // digits_lower.denominator)
# 11370273954
```
