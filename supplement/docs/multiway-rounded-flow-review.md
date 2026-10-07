# Independent review of conserved multiway rounding

Date: 2026-10-07. Original reasoning and local checks only; no literature
research. This review covers
[the rounding implementation](../experiments/multiway_rounded_flow.py)
and its integer counts and metadata. It assumes the previously checked
rational occupation flow and local tensor relations.

No blocking defect was found. Every nonnegative rational circulation
admits the rounding implemented here: each edge stays between its floor
and ceiling, integral edges stay fixed, and all vertex balances remain
zero. The implementation correctly handles parallel edges, opposing
edges, self-loops, and residual paths that change earlier choices.

## Why the rounding always succeeds

Let $B$ denote outflow minus inflow, let $t$ be the target circulation,
and put $\ell=\lfloor t\rfloor$ coordinatewise. The code's imbalance
is $b=-B\ell$. The fractional vector $f=t-\ell$ satisfies

\[
Bf=b,\qquad 0\le f_e<1.
\]

Each fractional nonloop edge gets capacity one. A vertex with $b_v>0$
receives a source edge of capacity $b_v$, while a vertex with $b_v<0$
gets an edge to the sink of capacity $-b_v$. These signs are correct:
the source supplies the positive outgoing balance of $f$. The vector
$f$, together with those source and sink edges at full capacity, is an
explicit feasible fractional flow of the required value. Self-loops
have zero incidence and can be omitted.

All capacities are integers. Starting from zero, each augmenting path
therefore changes the flow by a positive integer. If the algorithm
stopped without delivering the required amount, the vertices reachable
from the source would define a saturated cut with capacity below that
amount, contradicting the feasible fractional flow. It therefore
terminates successfully with integral increments, each zero or one.
Adding these increments to $\ell$ gives the desired circulation.

The reverse arcs are indexed separately for every insertion, so parallel
and opposing edges retain their own capacities and rounding bounds.
Self-loops are floored without entering this residual graph. Every
integral target is unchanged; each nonintegral target has absolute
rounding error strictly below one.

## Why the tensor counts conserve resources

For a row with injection $i$, the rational split and reset edges have
balance $K(e_i-e_0)$. Adding the integral edge $0\to i$ of value $K$
makes a circulation. That edge stays exactly $K$ under rounding, so
removing it restores the required row balance. This works for every
integer $K\ge1$ and both entries $i=1,2$.

The returned action children are ascending columns. Their targets are
exactly $K\lambda_xq(x,y)$, and their integer counts are the corresponding
rounded edges. Reversing the child order recovers the stated filtration
index order. The reset count has the same strict error bound and need
not be divisible by three. That flexibility assumes the separately
proved partial-middle tripling restriction.

The alternating row signs give global residual
$K S^+_{a,a}-K T_2$. At each signed tensor key, the catalyst count is the
minimum of the source and output multiplicities. Consequently its total
is $U+T-K$, where $U$ counts split factors and $T$ counts reset factors.
These are nonnegative integer resource ledgers, with no cancellation of
a tensor restriction. The row and action records are immutable.

## Verification

- All 18 tests in `tests/test_multiway_rounded_flow.py` pass, and all ten
  cases in `results/multiway-rounded-flow.json` reproduce exactly.
- Independent checks passed for 600 cycle-generated circulations,
  including 529 with parallel edges, 493 with opposing edges, and 575
  with self-loops; 64 exhaustive two-vertex circulations also passed.
- A separate reviewer checked 666 exhaustive three-vertex circulations
  after splitting edges into parallel pieces, adding fractional loops,
  assigning sparse integer labels, and shuffling edge order. All passed.
- Thirteen matching circulations with three through fifteen left
  vertices defeat ordered greedy selection and require changing an
  earlier choice. The residual solver rounds every one successfully.
- Seventy profiles, covering every index from two through fifteen at
  scales $1,2,3,7,41$, independently reproduce the positions, arities,
  rational targets, strict error bounds, row balances, alternating
  global balances, and catalyst counts. Both record types reject mutation.

The proof establishes the count construction for arbitrary integer
scale; the bounded experiments provide regression evidence. This review
does not establish entropy-loss bounds, finite rank costs, numerical
stability, or a practical multiplication algorithm.
