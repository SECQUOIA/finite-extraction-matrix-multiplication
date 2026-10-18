# Dimension lower bound for arbitrary conserved multiway flows

Status note (18 October 2026): this is a working note from the research
repository, written before version 5 of the paper. Section 11.2 of version 5
(Proposition 11.1 and Corollary 11.2) gives the final statements, with an
analytic proof that does not need the searches below. The scripts named here
are in `experiments/`; run them from `supplement/`.

This note concerns the paper's prescribed three-orientation split/tripling
extraction, with the stated convolution rank decomposition, separator,
interpolation, catalyst supply, and relative-scheme recursion. It allows
**every nonnegative integer conserved flow**, rather than just the paper's
rounded occupation flow. It also allows every split width that stays within
the row, and different widths at the same state. It does not modify the paper.

**Result. Every scheme in this class whose pooled exponent is below three
has source side `A >= 12^18 = 26,623,333,280,885,243,904 > 2^64`.** Bounds
by index are `A >= 2^96` at `a=2`, `A >= 12^18` at `a=3`,
`A >= 18^20` at `a=4`, `A >= 54^13` at `a=5`, and `A >= 162^9`
for every `a>=6`.
The bound for `a>=4` can be strengthened using its individual index.

These are necessary dimension bounds, not estimates of practical crossover.
They rule out a subcubic certificate in this class with source side below
`12^18`. They do not rule out a different extraction, different source or
catalyst rank decomposition, tensor identities outside these rows, or a
useful finite algorithm whose exponent certificate is at least three.

## Definitions and facts retained from the paper

Row `r` has states `x=0,...,3r`. A split at an interior state `x` has width
`1 <= h <= min(x,3r-x)`, auxiliary dimension `d=h+1`, and children
`x-h,x-h+2,...,x+h`. A tripling is the edge `3r -> 1`.
There are `K>=1` units of net flow from injection state one in the top row
and state two in every lower row to state zero in that row. Its tripling
count is `z_r`. Let `z=sum z_r`, and let

```
W = sum_over_splits w_i log(d_i),
S_a = sum_{r=2}^{a-1} log(2r-1),
t_a = F(a,a)/(2a-1).
```

The empty sum `S_2` is zero. The type scale, interpolation power, and reuse
count `N,k,j` are positive integers. The prescribed source side and pooled
exponent satisfy

```
log A = N k j W,
p = [3NK log(2a-1) + copy + interpolation + log(kappa_N)/j] / Delta,
Delta <= NK log F(a,a).
```

Both omitted overhead terms are nonnegative. The entropy-potential proof
of the bound on `Delta` applies to arbitrary empirical flows and all these
widths: the row profile is affine, so the child profile values sum to
`d` times the parent value, and relative entropy is nonnegative.
The catalyst supply is the paper's **prescribed** decomposition, with
`log(kappa_N)=3N sum c_{r,b} log(r+b-1)`; no claim that this decomposition
has optimal rank is used or made.

## Flow costs that do not depend on rounding

A conserved integral row flow decomposes into `K` paths from its injection
to state zero and nonnegative directed cycles. Every top-row path contains
a split, with product of split dimensions at least two. Every lower-row
path starts at state two and has product at least three: a path containing
two splits already has product at least four, while a path with a single
split can reach zero only with width at least two. A reset cannot precede
that single split, since the injection is not state `3r`.
Cycles have nonnegative cost. Consequently,

```
W >= K [log 2 + (a-2) log 3],
A >= [2 * 3^(a-2)]^(N k j K).                         (1)
```

Cut a row flow at every tripling edge. There are `K+z_r` split-only
excursions, beginning at injection or reset and ending at zero or `3r`.
Every excursion has at least one split. Thus the total number of splits
in that row is at least `K+z_r`.

Every lower-row consumed split factor is catalytic and has decomposition
base `r+b-1 >= 2r-1`. In the top row only the `K` net source factors are
removed from the catalyst count. Every tripling consumes a catalytic
factor with base `5r-2`. Hence

```
log(kappa_N) >= 3N [K S_a
                    + sum_{r=2}^a z_r log((2r-1)(5r-2))]
             >= 3N [K S_a + z log 24].                (2)
```

This statement also follows by summing source multiplicities in each row;
the adjacent-row boundary identifications introduce no duplicate consumed
factor, because state zero is never consumed by a row operation.

The split sector count is at most `d^(Nw)`, and the tripling sector count
is at most `3^(Nz_r)`. Therefore

```
Delta <= NK log 2 + Nz log 3.                         (3)
```

If `p<3`, its main term requires `Delta>NK log(2a-1)`. Equations (2), (3),
and the profile upper bound give two necessary inequalities:

```
z/K > log((2a-1)/2) / log 3,                          (4)
j > [S_a + (z/K) log 24] / log t_a.                 (5)
```

Here `t_a>1`, as follows directly from the product formula for `F`.
Equation (5) is deliberately generous to the algorithm: it drops positive
type, copy, and interpolation costs.

A second split potential, found in the parallel current-family
investigation, improves the small-index case. Set `D(0)=2` and `D(x)=x`
at positive states, separately in every row. For a positive child `y`,
`(h+1)D(x)>=(x+h)>=D(y)`, because
`(h+1)x-(x+h)=h(x-1)>=0`. For child zero, `x=h`, so
`(h+1)D(x)=x(x+1)>=2=D(0)`. Summing with row flow balance gives

```
W >= K log 2 + sum_{r=2}^a z_r log(3r)
  >= K log 2 + z log 6.                              (6)
```

The top-row injection contributes `K(log D(0)-log D(1))=Klog2`, while
each lower-row injection contributes `K(log D(0)-log D(2))=0`.
Every tripling contributes `z_r(log D(3r)-log D(1))=z_rlog(3r)`.
Since (4) implies the integer `z>=1` and `K>=1`, (6) implies
`A>=12^(Nkj)>=12^j`. This argument holds for all legal widths.

## Target index two: every legal width

For row two define the positive multiplicative potential

```
x       0  1  2  3  4   5   6
P(x)    2  1  2  4  6  12  16.
```

For every legal width and child, `(h+1)P(x) >= P(y)`. This is a finite
integer certificate checked by the accompanying script. Summing its
logarithm with the conserved split-edge counts gives

```
W >= K log 2 + z log 16.
```

The split divergence is `K(e_1-e_0)+z(e_1-e_6)`, so the two contributions
are `K(log P(0)-log P(1))` and `z(log P(6)-log P(1))`.
At `a=2`, `F=10/3`, `t=10/9`, and (4), (5) imply

```
3^z 2^K > 3^K,
10^(jK) > 9^(jK) 24^z.
```

An exhaustive integer check of these *necessary inequalities* gives
`j(K+4z)>=96`. This search is complete: if the objective were below 96,
then `K<=95`, `z<=23`, and `j<=95/(K+4z)`. The relaxed minimum is attained
at `(K,z,j)=(2,1,16)`; it is not a claimed feasible scheme.
It follows that `log_2 A >= Nk j(K+4z) >=96`.

## Target index three

Here `F=56/9`, `t=56/45`, and `S=log3`.
Equation (4) implies `z/K>5/6`, since `(5/2)^6>3^5`.
The exact inequality

```
3^6 24^5 > (56/45)^102
```

and (5) then imply `j>17`, hence `j>=18`.
Equation (6) gives `A>=12^18>2^64`.

## Every target index at least four

Put `Q_a=product_{r=2}^{a-1}(2r-1)`. Dropping the tripling contribution
in (5) gives `j>log Q_a/log t_a`. In fact `Q_a>t_a^8` for every `a>=4`.
For the base case this is the exact inequality

```
15 > (770/567)^8.
```

The product formula for `F` gives

```
t_(a+1)/t_a = [(3a+1)(3a+2)(2a-1)] / [3a(3a-1)(2a+1)]
             < (a+1)/a.
```

After clearing positive denominators, the latter inequality is
`12a^2+5a-1>0`. Since `((a+1)/a)^8 <= (5/4)^8 <7<=2a-1`, the induction
follows from `Q_(a+1)/Q_a=2a-1`. Therefore `j>8`, so `j>=9`.
Equation (1) gives `A>=18^9>2^32`.

For `a>=5`, the same conclusion gives `A>=54^9>6^18`.
For `a=4`, (4) gives `z/K>1`, since `(2a-1)/2=7/2>3`.
Equation (5) and the exact inequality `360>(770/567)^19` give
`j>19`, hence `A>=18^20>54^9>6^18`.

For the stronger uniform `12^18` bound, handle the remaining indices as
follows. At `a=5`, `Q_5=105`, `t_5=3185/2187`, and the exact inequality
`105>(3185/2187)^12` gives `j>=13`. Hence `A>=54^13>12^18`.
For `a>=6`, (1) and `j>=9` give `A>=162^9>12^18`.
The already proved bounds `2^96` and `18^20` for `a=2,4` also exceed
`12^18`. Thus every target index is covered.

## Verification and interpretation

Run `python experiments/multiway_general_flow_bound.py`. It checks every
row-two potential edge, the complete bounded integer search, and all
numerical inequalities above using integers and exact fractions.
No floating-point comparison enters the certificate.

The obstruction applies to the prescribed execution and its reported
subcubic exponent. Reducing only rounding denominators, type scale,
interpolation power, or catalyst reuse cannot create a subcubic scheme of
this class with source side below `12^18`. A practical replacement must
change at least one of the retained structural choices, or demonstrate
finite savings by a different analysis rather than the pooled exponent.
