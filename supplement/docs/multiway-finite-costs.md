# Complete finite costs for rounded multiway flows

The conserved maximal-width flows admit a single explicit integer parameter
family whose fully charged exponent upper expression tends to \(9/4\):

\[
L=\lceil\log_2 a\rceil,\qquad K=a^3L^2,\qquad
N=k=1,\qquad j=aL.
\tag{1}
\]

Its recursive source side \(A\) satisfies
\(\log A=O(a^5(\log a)^3)\), improving the previous rounded family's
\(O(a^8)\) bound. This is a smaller symbolic construction, not a practical
algorithm. A fixed comparison at index 12 with additional catalyst reuse
certifies a fully charged exponent upper bound below **2.675820359**, but its
recursive source side has **234,905,651,862 decimal digits**. The practical
target remains unmet.

This derivation combines the
[maximal-width occupation bounds](multiway-profile-flows.md),
[conserved rounding and entropy analysis](multiway-rounding-analysis.md),
[exact multiway tensor maps](multiway-determinant.md), and
[threefold orientation ledger](cyclic-profile-extraction.md). No literature
research, large parameter search, or large tensor-map construction was used.

## The exact finite recipe

Fix \(a\ge2\), normalization \(K\), type scale \(N\), interpolation
power \(k\), and catalyst reuse \(j\), all positive integers. A rounded
action at row \(r\), column \(b\), has auxiliary arity \(d=h+1\),
nonnegative child counts \(n_0,\ldots,n_{d-1}\), and weight
\(w=\sum_qn_q\). Omit zero-weight actions. For an active action, let
\(s=|\{q:n_q>0\}|\) be its used support size. The auxiliary still costs
\(d^w\), including when \(s<d\).

Every positive reset count \(z_r\) uses the middle-count-only tripling
type. The exact sector counts are

\[
M_i=\frac{(Nw_i)!}{\prod_q(Nn_{i,q})!},\qquad
M_r^{\rm trip}=\binom{Nz_r}{m_r}2^{Nz_r-m_r},\qquad
m_r=\left\lfloor\frac{Nz_r+1}{3}\right\rfloor.
\tag{2}
\]

Zero frequencies are allowed and \(0!=1\). No tripling divisibility by
three is required. Let \(I\) count the active actions and positive resets,
and write \(M\) for the product of all their sector counts. Then

\[
u=\prod_i d_i^{Nw_i},\qquad v=2^{NK}M,
\]
\[
\mathscr S=\prod_i(2M_i-1)^3,\qquad
\mathscr H=M^3,\qquad D=3\sum_i(M_i-1)^2.
\tag{3}
\]

The products and sums in (3) include both kinds of sector in (2).
The powers of three charge all cyclic orientations. The fixed-type
restrictions are exact; only the existing sector separators contribute
to the degree \(D\).

Use the actual alternating signed source/output ledger to retain common
factors \(c_{\sigma,r,b}\) in the catalyst. With
\(U=\sum_iw_i\) and \(T=\sum_rz_r\), their sum is \(U+T-K\).
An explicit catalyst rank charge is

\[
\kappa_N=\prod_{\sigma,r,b}(r+b-1)^{3Nc_{\sigma,r,b}}.
\tag{4}
\]

No factor is canceled as a tensor restriction. Exactifying power \(k\)
with \(E=kD+1\) evaluations, then reusing the exact catalyst \(j\) times,
gives

\[
r_*T_A\ge m_*T_B,\qquad A=u^{kj},\quad B=v^{kj},
\]
\[
r_*=\kappa_N^k E^j\mathscr S^{kj}(2a-1)^{3NKkj},
\qquad m_*=\mathscr H^{kj}.
\tag{5}
\]

The fixed-batch recursion charges \(\lceil r_*/m_*\rceil\). Its exponent
upper expression, whenever \(\log(v/u)>0\), is

\[
\Phi=
\frac{3NK\log(2a-1)+\log(\mathscr S/\mathscr H)
 +\log E/k+\log\kappa_N/j+\log2/(kj)}{\log(v/u)}.
\tag{6}
\]

As usual, take the maximum with 2 to include the linear transforms, with
the logarithmic factor at equality. The pooled scheduler can omit the final
ceiling allowance; the bounds and records here retain it.

## Logarithmic bounds without factorials

Use natural logarithms and the convention \(0\log0=0\). Define

\[
H_i=w_i\log w_i-\sum_qn_{i,q}\log n_{i,q},
\]
\[
G=K\log2-\sum_iw_i\log d_i+\sum_iH_i+T\log3.
\tag{7}
\]

For an action with support size \(s_i\), the exact-type bound gives

\[
NH_i-(s_i-1)\log(Nw_i+1)\le\log M_i\le NH_i.
\]

Using the support size is valid because the zero-count categories contribute
neither probability nor additional types. It does not replace \(d_i\)
in the source auxiliary charge. The maximizing middle count in (2) gives

\[
Nz_r\log3-\log(Nz_r+1)
\le\log M_r^{\rm trip}\le Nz_r\log3.
\]

Consequently,

\[
\log(v/u)\ge NG-\mathcal T_N,
\]
\[
\mathcal T_N=\sum_i(s_i-1)\log(Nw_i+1)
               +\sum_{r:z_r>0}\log(Nz_r+1).
\tag{8}
\]

Let \(B_N=\max\{NH_i,Nz_r\log3\}\) over the active sectors. Then

\[
0\le\log(\mathscr S/\mathscr H)<3I\log2,
\qquad
\log E\le\log(3kI+1)+2B_N.
\tag{9}
\]

Indeed, \(M_i\le e^{B_N}\) and
\(1+3k\sum_i(M_i-1)^2\le(3kI+1)e^{2B_N}\).
One-point action types have \(M_i=1\); including them in \(I\) makes
the upper bounds weaker but valid. Equations (7)-(9) require only logarithms
of the integer counts and small rank bases, not the enormous factorials
or separator arrays.

### Elementary sharpening for the finite evaluations

The records use tighter factorial-free bounds in addition to (8)-(9).
Put \(c_0=(1+\log2)/2\). For every integer \(t\ge1\),

\[
(t+\tfrac12)\log t-t+c_0
\le\log(t!)\le(t+\tfrac12)\log t-t+1.
\tag{9a}
\]

The upper bound follows by comparing the integral of the concave function
\(\log x\) on \([1,t]\) with its trapezoidal sum. For the lower bound,
Jensen's inequality on each interval \([i-1/2,i+1/2]\) bounds its integral
by \(\log i\). Sum these intervals and use
\((t+1/2)\log(1+1/(2t))\ge1/2\), which follows from
\(\log(1+x)\ge x/(1+x)\). No asymptotic factorial formula is needed.

For a positive support of size \(s\), write
\(C=\tfrac12\log(Nw)-\tfrac12\sum_{q:n_q>0}\log(Nn_q)\).
Then

\[
NH+C+c_0-s\le\log M\le NH+C+1-sc_0.
\tag{9b}
\]

The evaluator takes the maximum of the lower expression, the old type
lower bound, and zero; it takes the minimum of the upper expression and
the entropy bound. A zero-weight or one-point-support multinomial has
logarithm exactly zero and is handled directly.

For tripling, apply (9b) to the actual binary counts
\((m,Nz-m)\), then add \((Nz-m)\log2\). Intersect its lower bound with
\(Nz\log3-\log(Nz+1)\) and its upper bound with \(Nz\log3\).
This uses the exact rounded mode \(m=\lfloor(Nz+1)/3\rfloor\), without
assuming \(m=Nz/3\). In (8), replace each penalty by its entropy minus
the improved sector lower bound. In (9), replace each sector entropy upper
bound by its improved upper bound before taking the maximum.
The original inequalities remain valid, so the asymptotic proof below is
unchanged. A separate proof and checks of (9a)-(9b) are also recorded in
[the rounding analysis](multiway-rounding-analysis.md).

## Bounds uniform in tiny occupation weights

Let \(\lambda_i\) and \(q_{i,q}\) be the exact harmonic occupation
weights and child probabilities. The conserved edge rounding gives
\(|n_{i,q}-K\lambda_iq_{i,q}|<1\), and keeps an exactly zero target edge
at zero. Write

\[
J_a=\sum_{r=2}^{a}\sum_{x=1}^{3r-1}
       (1+\min(x,3r-x))=O(a^3),
\qquad C_a=105+180(a-2).
\]

The occupation and rounding proofs give

\[
G=K\log F(a,a)-\mathcal L,\quad0\le\mathcal L\le4J_a,
\]
\[
\log u\le N\bigl(KC_a+J_a\log(2a)\bigr),\qquad
U\le KC_a+J_a,\qquad T\le2K(a-1)+(a-1).
\tag{10}
\]

For completeness, the uniform entropy-loss estimate does not divide by
\(\lambda_i\). Since \(q_{i,q}\ge1/(3d_i)\), edge rounding implies
\(n_{i,q}/(w_iq_{i,q})\le1+4d_i/w_i\) for an active action. Therefore
\(w_iD(n_i/w_i\Vert q_i)\le4d_i\). Summing proves the bound in (10).
There is no assumption of a positive minimum occupation weight.

There are \(O(a^2)\) possible actions and resets, and \(d_i\le2a\).
The per-row ideal auxiliary charge is at most 180, so each action obeys

\[
w_i\log d_i\le180K+d_i\log d_i
               \le180K+2a\log(2a).
\tag{11}
\]

This per-action bound is necessary for the next interpolation estimate;
using only the total auxiliary charge would lose a factor of \(a\).
The reset bound \(z_r\le2K+1\) also controls every tripling sector.

Finally, all catalyst rank bases are below \(5a\), and hence

\[
\log\kappa_N\le3N(U+T-K)\log(5a)
                 =O\bigl(N(Ka+a^3)\log a\bigr).
\tag{12}
\]

These are upper bounds on charged resources. The finite evaluator uses the
actual signed catalyst in (4), rather than substituting (12).

## One integer family charges every term

Use (1), with \(L=(a-1).\mathrm{bit\_length}()\), so selecting the
parameters requires no numerical logarithm. Then \(L=\Theta(\log a)\).
The rounding and type losses satisfy

\[
\mathcal L=O(a^3),\qquad
\mathcal T_1=O(a^3\log K)=O(a^3\log a),
\]

because there are \(J_a=O(a^3)\) type coordinates and
\(w_i\le180K+2a\). In particular,

\[
\frac{G-\mathcal T_1}{K}
=\log F(a,a)-O(1/\log a).
\tag{13}
\]

The known diagonal formula gives
\(\log F(a,a)=(4/3)\log a+O(1)\), so the contraction lower bound
is positive for sufficiently large \(a\).

At \(k=1\), (11) gives \(B_1=O(K)\): both the determinant entropies
and the reset charges satisfy this bound. Thus \(\log E=O(K)\).
Equation (12), divided by \(j=aL\), gives
\(\log\kappa_1/j=O(K)\). The copy charge is \(O(a^2)\), and the
ceiling allowance is smaller still. The complete sufficient upper expression
therefore satisfies

\[
\Phi\le
\frac{3K\log(2a-1)+O(K)}
     {K\log F(a,a)-O(a^3\log a)}
\longrightarrow\frac94.
\tag{14}
\]

No factorial or interpolation count has been omitted in deriving this limit.
The corresponding recursive source scale obeys

\[
\log A=j\log u
\le aL\bigl(KC_a+J_a\log(2a)\bigr)
=O(a^5(\log a)^3).
\tag{15}
\]

The extra \(J_a\log(2a)\) rounding term is retained; an
\(O(a^3)\) bound for it alone has not been assumed. Equation (15) is
an upper bound on the logarithm of an enormous dimension, not a polynomial
bound on the matrix side itself.

For each fixed positive exponent allowance, a sufficiently large fixed
index gives the corresponding asymptotic arithmetic upper bound. This does
not assert a single fixed recursion of exponent exactly \(9/4\), a uniform
construction-time bound, or a useful finite implementation.

## Fixed interval evaluations

The evaluator uses the conserved rounded counts at indices 4, 8, and 12,
with the parameters (1). It also records the single fixed comparison
power \(k=32\) to show the interpolation tradeoff. Increasing \(k\)
reduces that normalized charge but multiplies \(\log A\) by 32.
After the component charges showed catalyst reuse dominating these finite
bounds, one further fixed comparison retained \(k=32\) and multiplied
\(j\) by 128. No grid search or larger index was used.

| Index | \(K\) | \(j\) | Upper expression, \(k=1\) | Source-side decimal digits, \(k=1\) | Upper expression, \(k=32\) | Source-side decimal digits, \(k=32\) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 256 | 8 | 16.825272 | 20,620 | 12.500725 | 659,816 |
| 8 | 4,608 | 24 | 10.174927 | 2,899,778 | 7.628287 | 92,792,890 |
| 12 | 27,648 | 48 | 8.096981 | 57,350,013 | 6.008930 | 1,835,200,406 |

The additional reuse comparison gives:

| Index | \(k\) | \(j\) | Sufficient exponent upper bound | Recursive source-side decimal digits |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 32 | 1,024 | 3.628926097 | 84,456,434 |
| 8 | 32 | 3,072 | 2.848599165 | 11,877,489,885 |
| 12 | 32 | 6,144 | **2.675820359** | **234,905,651,862** |

Every displayed exponent is rounded upwards from its certified interval.
Only the last row certifies improvement over the rank-40 exponent
\(3\log40/\log54\). It is a formal finite tensor recipe with all the stated
charges, not an executable improvement at useful sizes. These upper bounds
are not lower bounds on the recipe's exact exponent; the estimates may
still be loose. The source digit counts are certified from the actual
product \(A=u^{kj}\).

The [earlier basic-type report](../results/multiway-finite-costs-basic-type.json)
preserves the first comparison before (9a)-(9b). At unchanged parameters
and \(k=32\), sharpening reduced its upper expressions from approximately
16.917559, 8.350375, and 6.293827 to the first table's values.

The fixed runs took about 0.02, 0.10, and 0.27 seconds for rounded counts and
their logarithm bounds on this host. This measures only the small evaluator,
not constructing or executing the represented tensor maps.

```sh
python -m experiments.multiway_finite_costs > results/multiway-finite-costs.json
python -m pytest tests/test_multiway_finite_costs.py -q
```

The [evaluator](../experiments/multiway_finite_costs.py) reuses the existing
proved rational logarithm enclosures, accumulated with outward dyadic
rounding. It directly evaluates (7), subtracts the support-aware type loss,
and charges the actual signed catalyst. The
[saved report](../results/multiway-finite-costs.json) includes every active
integer type, reset count, catalyst exponent, separate charge interval,
parameter, source digit count, and code hash. It never materializes the
factorials in (2). The fixed precision suffices for these cases; an
arbitrary-allowance compiler would need adaptive precision.

All six focused evaluator tests pass. They check the integer parameter
selection, zero and one-point supports, bound directions against tiny exact
sector counts, the nonpositive-contraction guard, exact rounded tripling
modes, and the fixed power/reuse cost and dimension tradeoffs.
Independent review confirmed (10)-(15), including the small-occupation and
reset cases, and reproduced every interval and digit count in all three
fixed reports. The complete large
coefficient maps, numerical stability, and practical runtime remain open.
