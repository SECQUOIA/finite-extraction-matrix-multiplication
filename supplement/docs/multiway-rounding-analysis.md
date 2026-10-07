# Entropy and auxiliary costs of conserved multiway rounding

Date: 2026-10-07. Original derivation; no literature research or parameter
search.

Conserved rounding of the maximal-width flows loses at most \(4E(a)\)
in absolute entropy gain, where

\[
E(a)=\frac{12a^3+42a^2+12a-65+(-1)^a}{16}
\]

is the number of candidate transition coordinates. This bound does not
depend on a smallest positive occupation weight or a denominator-clearing
scale. It includes actions rounded to zero. The rounded auxiliary logarithm
is at most

\[
K[105+180(a-2)]+E(a)\log(\lfloor3a/2\rfloor+1).
\]

These bounds control rounding and finite-type accounting. They do not by
themselves give a finite exponent certificate or a practical multiplication
algorithm.

## Exact hypotheses and a sharper probability bound

Use the rational occupations of
[the maximal-width construction](multiway-profile-flows.md). In row
\(r\ge2\), put

\[
n=3r,\quad c=\tfrac32(r-1),\quad f(x)=c+x,
\quad h=\min(x,n-x),\quad d=h+1.
\]

At interior state \(1\le x<n\), the children are
\(y=x-h,x-h+2,\ldots,x+h\), and

\[
q_y=\frac{f(y)}{d f(x)}.
\]

For an ideal occupation \(\lambda\ge0\), let \(W=K\lambda\) and
suppose the conserved integer rounding supplies nonnegative counts \(n_y\)
such that

\[
|n_y-Wq_y|<1,\qquad w=\sum_y n_y.
\tag{1}
\]

Reset counts \(z_r\) satisfy \(|z_r-K\mu_r|<1\). The entire signed
resource ledger, including the source supply \(K\), is preserved exactly.
The [circulation-rounding implementation](../experiments/multiway_rounded_flow.py)
provides these hypotheses. Self-loops are included; unreachable edges have
zero target and remain zero.

The suggested global bound \(q_y\ge1/(5d)\) is valid, but the allowed
child range gives the stronger bound

\[
q_y\ge\frac{r-1}{(2r-1)d}\ge\frac1{3d}.
\tag{2}
\]

Indeed, \(f(y)/f(x)\) is minimized at the smallest child \(x-h\).
For \(x\le n/2\), this ratio is \(c/(c+x)\), decreasing to
\(c/(c+n/2)\). For \(x\ge n/2\), it is
\((c+2x-n)/(c+x)\), which is increasing. Their common minimum is
\(c/(c+n/2)=(r-1)/(2r-1)\). This argument also covers odd \(n\),
when the continuous midpoint is not a state.

## A uniform bound even for tiny occupations

If \(w>0\), define \(p_y=n_y/w\), with zero terms in entropy interpreted
as zero. Equation (1) gives \(|w-W|<d\). For every positive \(n_y\),

\[
\frac{p_y}{q_y}
\le\frac{W}{w}+\frac1{wq_y}
\le1+\frac{4d}{w}.
\]

Consequently,

\[
wD(p\Vert q)
\le w\log(1+4d/w)\le4d.
\tag{3}
\]

This proof uses neither \(W\gg d\) nor a lower bound on \(\lambda\).
If \(w=0\), define the action's loss to be zero and omit its entropy
expression. If \(W=0\), integrality and (1) force every \(n_y=0\).
Thus zero ideal occupations do not introduce a division by zero or a
rounding loss.

There is also a useful additional bound for \(W>0\). With
\(\delta_y=n_y-Wq_y\), the generalized relative-entropy identity is

\[
\sum_y\left[n_y\log\frac{n_y}{Wq_y}-n_y+Wq_y\right]
=wD(p\Vert q)+w\log(w/W)-w+W.
\]

The last three terms are nonnegative. The elementary inequality
\(t\log t-t+1\le(t-1)^2\), including its limit at \(t=0\), gives

\[
wD(p\Vert q)
\le\sum_y\frac{\delta_y^2}{Wq_y}
\le\frac{3d^2}{W}.
\tag{4}
\]

One can therefore use
\(\min\{4d,3d^2/(K\lambda)\}\) at each positive ideal action,
without imposing a global minimum occupation. The second bound improves
large actions; the first remains safe for arbitrarily small ones.

Under just these local hypotheses, an absolute loss uniformly decreasing
with \(K\) is unavailable. For example, take even \(d\), uniform \(q\),
\(W=d/2\), and round half of the coordinates to one and half to zero.
Every error has magnitude \(1/2\), the total weight is unchanged, and the
loss is \((d/2)\log2\). Setting \(\lambda=d/(2K)\) makes this example
consistent with any scale. This is a limit on deductions from the local
error and probability bounds alone, not an obstruction for this specific
occupation graph or for matrix multiplication.

## The exact conserved potential identity

Define

\[
G=K\log2+\sum_{\rm actions}w\bigl(H(p)-\log d\bigr)
       +\sum_r z_r\log3,
\quad
\mathcal L=\sum_{\rm actions}wD(p\Vert q).
\]

The exact rounded ledger implies

\[
G=K\log F(a,a)-\mathcal L.
\tag{5}
\]

To prove it, use \(q_y=F(r,b_y)/(dF(r,b))\) to write each action's
logarithmic potential difference as

\[
w\log F(r,b)-\sum_y n_y\log F(r,b_y)
=w\bigl(H(p)-\log d\bigr)+wD(p\Vert q).
\]

Each reset contributes precisely \(z_r\log3\), because
\(F(r,4r-1)=3F(r,r)\). Exact conservation and the alternating row
isomorphisms telescope the left side to
\(K\log F(a,a)-K\log2\). This proves (5).
Rounding a deterministic reset creates no separate entropy error; its
actual integer count already participates in the exact potential ledger.
The accuracy of the reset rounding is needed for count bounds, not for
this identity.

The number of candidate coordinates in row \(r\) is

\[
E_r=\sum_{x=1}^{3r-1}(\min(x,3r-x)+1)
   =\lfloor9r^2/4\rfloor+3r-1.
\]

Summing \(r=2,\ldots,a\) gives the displayed formula for \(E(a)\).
There are \((a-1)(3a+4)/2\) candidate actions, and their maximum arity is
\(d_{\max}=\lfloor3a/2\rfloor+1\). Counting only ideal-positive actions
can sharpen the bounds, but is unnecessary. Equations (3) and (5) imply

\[
0\le\mathcal L\le4E(a),\qquad
G/K\ge\log F(a,a)-4E(a)/K.
\tag{6}
\]

For a rational permitted loss \(\delta>0\), the explicit choice
\(K\ge\lceil4E(a)/\delta\rceil\) suffices. This is polynomial in the
profile index and inverse loss allowance, with no LCM.

For an extra limiting exponent allowance \(0<\eta\le1\) above
\(\tau_a=3\log(2a-1)/\log F(a,a)\), a sufficient entirely rational
choice is

\[
K\ge\left\lceil\frac{16E(a)}\eta\right\rceil.
\tag{7}
\]

Indeed \(\log F(a,a)>1\), \(\tau_a<3\), and a denominator loss
\(\delta\le\eta/4\) increases that ratio by at most
\(3\delta/(1-\delta)\le\eta\). This statement charges rounding only;
the other finite costs must still be included.

## Auxiliary counts and finite types remain explicit

Let \(C_a=105+180(a-2)\). The proved occupation bounds give
\(\sum\lambda\log d\le C_a\) and \(\sum\lambda\le C_a\).
Since \(w<W+d\), the rounded source auxiliary logarithm obeys

\[
\mathcal A:=\sum w\log d
\le KC_a+\sum d\log d
\le KC_a+E(a)\log d_{\max}.
\tag{8}
\]

Likewise, for total determinant weight \(V=\sum w\),

\[
V\le KC_a+E(a).
\tag{9}
\]

Each individual action has
\(w\log d\le180K+d\log d\), since its nonnegative ideal charge is at
most the entire row's charge. This is stronger for interpolation estimates
than bounding \(\lambda\) and then multiplying by \(\log d\).

The exact reset occupations also give the optional count bound

\[
Z:=\sum_rz_r
\le K\left(2H_{a-2}+\frac1{a-1}\right)+(a-1),
\tag{10}
\]

where \(H_0=0\). It uses
\(\mu_r<2/(r-1)\) in lower rows and \(\mu_a=1/(a-1)\) in the
final row. The signed catalyst has \(V+Z-K\) factors. At type scale
\(N\), the source matrix side is \(u=\prod d^{Nw}\), so
\(\log u=N\mathcal A\); these are actual charged auxiliaries.

For an action with \(s\) positive rounded coordinates, its exact type has

\[
M=\frac{(Nw)!}{\prod_y(Nn_y)!},\qquad
\log M\ge NwH(p)-(s-1)\log(Nw+1).
\]

Actions of weight zero have \(M=1\) and are omitted. A one-coordinate
type has no finite-type penalty. For each reset, the
[partial-middle tripling type](cyclic-profile-extraction.md) gives
\(M\ge3^{Nz}/(Nz+1)\), also valid for \(z=0\). Thus the complete
finite-type loss can be bounded by

\[
\mathcal E_N=
\sum_{w>0}(s-1)\log(Nw+1)+\sum_r\log(Nz_r+1).
\tag{11}
\]

In the threefold construction, \(v=2^{NK}\prod M\), so

\[
\log(v/u)\ge N\bigl(K\log F(a,a)-4E(a)\bigr)-\mathcal E_N.
\tag{12}
\]

Nothing in (12) removes separator copies, interpolation evaluations,
catalyst rank charges, or the costs of the final batch scheduler. Those
remain part of a complete finite algorithm. The present result supplies
uniform bounds for that accounting without assuming tiny occupations away.

An optional sharper finite-type enclosure uses only elementary factorial
bounds. Put \(c_0=(1+\log2)/2\). For every integer \(t\ge1\),

\[
(t+\tfrac12)\log t-t+c_0\le\log(t!)
\le(t+\tfrac12)\log t-t+1.
\tag{13}
\]

For the upper bound, the concave-log trapezoid inequality gives
\(\log(t!)-\tfrac12\log t\le\int_1^t\log x\,dx\).
For the lower bound, Jensen's inequality on each unit interval centered at
an integer gives \(\log(t!)\ge\int_{1/2}^{t+1/2}\log x\,dx\).
Evaluating this integral and using
\((t+1/2)\log(1+1/(2t))\ge1/2\) proves the stated constant.
The last inequality follows from \(\log(1+u)\ge u/(1+u)\).
At \(t=1\), the upper bound is exactly zero and the lower is \(c_0-1<0\).

For positive coordinates \(n_1,\ldots,n_s\) summing to \(w\), let
\(J=wH(p)+\tfrac12\log w-\tfrac12\sum_i\log n_i\). Applying (13)
to the numerator and denominators with opposite bound directions yields

\[
J+c_0-s\le\log\frac{w!}{\prod_i n_i!}\le J+1-sc_0.
\tag{14}
\]

Intersect this interval with \([0,wH(p)]\), and optionally with the mode
bound used in (11). Zero coordinates are omitted; a zero-weight action has
logarithmic sector count zero. For one positive coordinate the intersection
is exactly zero. Scaling all counts by \(N\) multiplies the entropy term
by \(N\) and adds \(-\tfrac12(s-1)\log N\) to the half-log correction.
This enclosure avoids factorial materialization, a value of \(\pi\), or
an unstated asymptotic error term.

## Reproduction and independent check

The following small exact check uses the implemented conserved rounding.
It checks the denominator-free pointwise inequality behind (3), including
zero actions; it does not estimate logarithms or search parameters.

```sh
python - <<'PY'
from fractions import Fraction
from experiments.multiway_rounded_flow import rounded_profile

for a in (2, 3, 4, 6):
    E = (12*a**3 + 42*a**2 + 12*a - 65 + (-1)**a)//16
    for K in (1, 7):
        rows = rounded_profile(a, K)
        assert sum(t.arity for row in rows for t in row.actions) == E
        for row in rows:
            for t in row.actions:
                W, w, d = t.target_weight, t.weight, t.arity
                if W == 0:
                    assert w == 0
                    continue
                for n, target in zip(t.counts, t.target_counts):
                    q = target/W
                    assert q >= Fraction(1, 3*d)
                    assert abs(n-target) < 1
                    if w:
                        assert n/(w*q) <= 1 + Fraction(4*d, w)
print('All exact probability and rounding inequalities passed.')
PY
```

An independent derivation verified (2)-(6), the generalized relative-entropy
bound, and the auxiliary inequalities. A separate count derivation agreed
with \(E(a)\); exact checks covered probability bounds through row 100 and
coordinate counts through index 50. No blocking issue was found.
The proof uses exact inequalities; it introduces no numerical precision
assumption. A finite cost evaluator must still enclose its logarithms and
reject undecided comparisons. No composed coefficient maps or useful
finite-size algorithm are claimed here.
