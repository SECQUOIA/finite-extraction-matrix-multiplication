# Necessary source dimensions near exponent 9/4

Status note (18 October 2026): this is a working note from the research
repository, written before version 5 of the paper. Section 11.2 of version 5
(Proposition 11.1 and Corollary 11.2) gives the final statements, with an
analytic proof that does not need the searches below. The scripts named here
are in `experiments/`; run them from `supplement/`.

This note strengthens the all-flow subcubic dimension obstruction. It does
not change the paper. It proves a quantitative tradeoff for **every conserved
nonnegative integer flow and every legal split width**, when the paper's
prescribed source and catalyst rank decompositions and pooled exponent are
retained. Choosing better rounding parameters cannot evade this tradeoff.
It does not give a rank lower bound for arbitrary specialized circuits or
for different source or catalyst decompositions.

If the pooled exponent is at most `9/4 + epsilon`, the required row index
is at least exponential in `1/epsilon`, and the source side is at least
**doubly exponential in `1/epsilon`**. The constants below are explicit.
These are necessary bounds, not feasible parameter choices or wall-clock
crossover estimates.

## Definitions

Retain the notation and all-flow inequalities from
[multiway-general-flow-lower-bound.md](multiway-general-flow-lower-bound.md):

```
F(a,a) = s_a (3a-1)/2,
s_a = product_{h=1}^{a-1} (1 + 1/(3h)),
t_a = F(a,a)/(2a-1),
S_a = sum_{r=2}^{a-1} log(2r-1),
W = sum_i w_i log(d_i).
```

All logarithms in the proofs are natural. The pooled exponent `p`, source
side `A`, and positive integer parameters satisfy

```
p >= 3 log(2a-1)/log F(a,a),
log A = N k j W,
W >= K [log 2 + (a-2) log 3].                         (1)
```

For `p<3`, the prescribed catalyst supply also forces

```
j > S_a / log t_a.                                  (2)
```

Equation (2) drops a further positive reset contribution, so it gives the
algorithm generous credit. The statements below concern `a>=2` and
`0<epsilon<=1/4`, which implies `p<3`.

## An explicit deficit from the limiting profile

For every `a>=2`,

```
s_a^3 <= (128/135) (3a-1)/2.                         (3)
```

At `a=2`, both sides equal `64/27`. The induction follows from

```
(3a+2)(3a)^3 - (3a-1)(3a+1)^3 = 6a+1 > 0.
```

The fixed constant `128/135` therefore remains valid at every larger
index. Put

```
R_a = (135/128) [(4a-2)/(3a-1)]^4,
c_a = (1/4) log R_a.
```

Cubing `F` in (3) gives

```
F(a,a)^3 <= (2a-1)^4 / R_a,
log F(a,a) <= (4/3) [log(2a-1)-c_a].                 (4)
```

The sequence `R_a` is increasing, since

```
(4a+2)(3a-1) - (4a-2)(3a+2) = 2 > 0.
```

Its first value and limit are particularly simple:

```
R_2 = 2187/1000,
lim R_a = 10/3.
```

Write `L=log(2a-1)`. Combining (1), (4), and `p<=9/4+epsilon`
gives

```
L >= (1 + 9/(4 epsilon)) c_a
  >= [(4 epsilon+9)/(16 epsilon)] log(2187/1000).     (5)
```

In particular,

```
a >= [1 + (2187/1000)^((4 epsilon+9)/(16 epsilon))]/2. (6)
```

This is an explicit index lower bound for arbitrary conserved flows.
For `epsilon<=1/4`, (6) already implies `a>=5`. For example, at the
largest epsilon the required exact comparison is
`(2187/1000)^5 > 7^2`, which forces `2a-1>7`.

One can improve (6) without a flow search. If a previous bound gives
`a>=m`, monotonicity gives `R_a>=R_m`, so replace `2187/1000` in (5),
(6) by `R_m`. Each iteration remains a valid necessary bound even if
iteration stops before it stabilizes.

## Catalyst reuse is at least linear in the index

Let

```
Q_a = product_{r=2}^{a-1}(2r-1),  so S_a=log Q_a.
```

For `a>=3`, pair each index `r` with `a+1-r`. Their odd factors obey

```
(2r-1)(2a+1-2r) >= 3(2a-3) > 2a-1.
```

The first inequality holds because the quadratic product is concave in
`r`, and its endpoints `r=2,a-1` give `3(2a-3)`. Multiplying over all
`r=2,...,a-1` counts each factor twice, so

```
Q_a^2 > (2a-1)^(a-2),
S_a > [(a-2)/2] log(2a-1).                           (7)
```

The paper's profile upper bound gives
`log t_a <= (1/3)log(2a-1)`. Thus (2), (7) imply

```
j > 3(a-2)/2,
j >= floor(3(a-2)/2)+1.                             (8)
```

The accuracy target gives a stronger reuse bound. The pooled numerator
contains the main rank term and `log(kappa_N)/j`, while the prescribed
catalyst supply obeys `log(kappa_N)>=3NK S_a`. Consequently,

```
3 S_a/j <= (9/4+epsilon) log F(a,a) - 3 log(2a-1)
         < epsilon log F(a,a)
         < (4 epsilon/3) log(2a-1).
```

Here the first strict inequality uses the strict profile bound
`log F(a,a)<(4/3)log(2a-1)`. With (7), this yields

```
j > 9(a-2)/(8 epsilon),
j >= floor(9(a-2)/(8 epsilon))+1.                   (9)
```

Combining (1), (9), and `N,k,K>=1`,

```
log A > [9/(8 epsilon)](a-2)[log 2 + (a-2)log 3]
      > [9 log 3/(8 epsilon)](a-2)^2.               (10)
```

Unlike bounds that use only `j>=1`, (9) charges both the row flow and the
catalyst reuse needed to sustain a subcubic pooled exponent.

## Exact numerical consequences

The script bootstraps (5) at most eight times and checks the resulting
integer thresholds without evaluating a floating-point logarithm. The
following bounds are deliberately conservative. The finite iteration
count is not an optimality claim.

| Target pooled exponent | Necessary index `a` at least | Necessary source side |
| --- | ---: | ---: |
| `2.50` | `9` | `A > 2^368` |
| `2.35` | `587` | `A > 2^5782287` |
| `2.30` | `515312` | `A > 2^8962135735816` |
| `2.26` | `174429169363903877246844517002` | `A > 2^(5.1343 × 10^60)` |

The last displayed exponent is rounded downward. Its exact integer lower
bound is

```
5134309052340621871212113107198754745805984457443695293688001.
```

To derive each binary bound, let `m` be the certified index lower bound
and `J=floor(9(m-2)/(8 epsilon))+1`. Equations (1), (9) give the stronger,
factorized integer bound

```
A >= 2^J 3^(J(m-2)).
```

Since `log_2 3 > 3/2`, as certified by `9>8`, it follows that

```
log_2 A > floor(J(3m-4)/2).
```

There is no claim that any displayed index admits the stated exponent.
The profile, entropy, copy, interpolation, and integrality losses can
require much larger dimensions. The row-index bound `a>=9` for exponent
`2.50`, for example, does not claim a scheme at index nine.

## Double exponential growth, with constants

For `epsilon<=1/4`, the preceding index bound ensures `a>=4`, so
`a-2>=a/2`. Equations (6), (10) give the closed bound

```
log A > [9 log 3 / (128 epsilon)]
        (2187/1000)^((4 epsilon+9)/(8 epsilon)).     (11)
```

The right side is exponential in `1/epsilon`, and `A` is its exponential.
Thus the double exponential statement concerns the source side itself,
not merely a loose upper bound from the rounded construction.

There is a slightly stronger asymptotic consequence that does not depend
on a finite numerical search. For any fixed `m`, (6) eventually forces
`a>=m`; then (5) holds with `R_m`. Repeating (11) with `R_m` and letting
`m` tend to infinity proves the necessary tradeoff

```
liminf_{epsilon -> 0+} epsilon log log A
    >= (9/8) log(10/3) > 1.35.                       (12)
```

This statement means: along any family of prescribed schemes with
`p<=9/4+epsilon` and `epsilon->0+`, the indicated lower limit holds.
It is vacuous if such a family is unavailable; the paper independently
supplies families with exponents tending to `9/4`.
The constant `1.35` is a rounded description, while the exact bound in
(12) is `(9/8)log(10/3)`.

## The growth order is attained by the paper's existing upper bound

The paper's explicit parameter theorem gives, for `a>=2^64`,

```
p < 9/4 + 900/log a,
log A <= 181 a^5 ceil(log_2 a)^2.
```

For `0<epsilon<=1/4`, choose `a=ceil(exp(900/epsilon))`.
This index exceeds `2^64`, gives `p<9/4+epsilon`, and satisfies

```
log log A <= 5 log a + 2 log ceil(log_2 a) + log 181
           = O(1/epsilon).
```

Together with (11), this establishes the best achievable **growth order**
within the prescribed scheme and cost model:

```
log log A = Theta(1/epsilon),
A = exp(exp(Theta(1/epsilon))).
```

Precisely, the smallest achievable source side at allowance `epsilon`
has this asymptotic order; the statement does not constrain someone from
choosing a much larger scheme. The constants in the upper and lower
bounds are far apart. The upper bound is the paper's existing theorem,
not a new algorithm discovered here.

This answers the paper's question about polynomial `log A` negatively
**for the prescribed source and catalyst decompositions, arbitrary legal
widths, and arbitrary conserved integer flows**. The broader question in
the discussion, which permits a different finite construction or a
variant that changes those choices, remains open.

## Verification and scope

Run

```
python experiments/exponent_dimension_tradeoff.py
```

The script writes [the exact report](../results/exponent-dimension-tradeoff.json).
For rational `epsilon=u/v`, each bootstrap boundary uses only the integer
comparison

```
(2a-1)^(16u) R_m.denominator^(4u+9v)
    >= R_m.numerator^(4u+9v).
```

Binary search checks the passing boundary and its immediately preceding
integer. The script also checks the induction and factor-pair identities
through index 256; these finite checks supplement the proofs for all
indices above, rather than replacing them.

The theorem resolves the qualitative dependence of required dimensions
on exponent accuracy within this prescribed cost model: a single
exponential source side in `1/epsilon` is impossible. The exact smallest
index, reuse count, and source side remain unoptimized. Changing source
or catalyst decompositions, exploiting correlated inputs in the composed
maps, or using other tensor identities remains outside this theorem.
