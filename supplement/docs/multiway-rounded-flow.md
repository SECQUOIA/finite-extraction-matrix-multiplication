# Conserved integer rounding for every positive scale

Date: 2026-10-07. Original construction using local files; no literature
research.

The maximal-width rational flows now have an exact integer rounding
algorithm for **every integer $K\ge1$**. Every transition and terminal
reset changes by strictly less than one from its scaled rational target.
The row and alternating global resource ledgers remain exact. The
algorithm does not clear the rational occupation denominators.

This note certifies counts and conservation. The
[rounding analysis](multiway-rounding-analysis.md) separately charges
the entropy loss. Finite multiplication costs and numerical execution
still require their own evidence.

## Rounding a circulation

For a row, use all rational transition counts $K\lambda_xq(x,y)$ and the
terminal reset count $K\mu$. Add the boundary return edge $0\to i$ with
fixed count $K$, where $i=1$ for the final row and $i=2$ for a lower row.
The [exact occupation ledger](multiway-profile-flows.md) says that this
is a nonnegative circulation.

The following procedure applies to any finite nonnegative rational
circulation, including parallel and opposing edges.

1. Floor each edge count: $\ell_e=\lfloor\phi_e\rfloor$.
2. At vertex $v$, set
   $b_v=\sum_{e\text{ entering }v}\ell_e-\sum_{e\text{ leaving }v}\ell_e$.
3. For every nonintegral, non-loop edge, retain its original direction
   with residual capacity one. Add a super-source edge of capacity $b_v$
   when $b_v>0$, or a super-sink edge of capacity $-b_v$ when $b_v<0$.
4. Find an integral maximum flow and add its zero-or-one edge values to
   the floors. Self-loops stay at their floors.

The fractional parts $\phi_e-\ell_e$ give a feasible residual flow:
their outgoing-minus-incoming imbalance is exactly $b_v$. Thus the
super-source demand can be saturated. Integer capacities and ordinary
augmenting paths give an integer solution. All final edge counts lie
between their target's floor and ceiling; integral targets remain
unchanged. In particular,

\[
|n_e-\phi_e|<1,
\]

and target-zero edges remain zero. Self-loops have no incidence and may
be floored independently. Opposing original edges and residual reverse
arcs are distinct objects in the implementation.

The fixed boundary return edge is integral, so it stays at $K$.
Removing it recovers exactly the desired row residual. The amount sent
through the residual network is at most the number of fractional edges,
so the number of augmentations does not grow with $K$. Arithmetic on
the original rational targets and integer counts remains exact.

## Tensor bookkeeping and interface

For each original parent column, the integer action weight is the sum
of its outgoing child counts. Some actions and reset counts can be zero.
Zero-weight actions are retained in the metadata and skipped when
executing or charging a relation.

The reset count $z$ need not be divisible by three. The partial-middle
tripling type in [the cyclic construction](cyclic-profile-extraction.md)
accepts arbitrary $z\ge0$. Alternating row signs then give the exact
global residual

\[
K S^+_{a,a}-K T_2.
\]

Common input and output factors remain an actual catalyst. If $U$ is
the sum of all action weights and $T$ is the sum of reset counts, its
factor count is exactly $U+T-K$.

The [implementation](../experiments/multiway_rounded_flow.py) uses only
the Python standard library and the existing rational occupation solver:

- `rounded_row(row, scale, entry_position=1)` returns an immutable row.
- `rounded_profile(index, scale)` returns all rows with the required
  lower-row and final-row injections.
- Each action exposes `row`, `column`, `children`, `counts`,
  `target_counts`, `weight`, `arity`, and `target_weight`.
- Each row exposes `reset_count` and its exact rational `reset_target`.
- `profile_ledger(rows)` returns the signed residual and exact catalyst
  counts obtained by taking input/output minima.

Children and counts use **ascending child columns**. The local
[filtration](multiway-determinant.md) uses decreasing columns
$b+h-2j$; reverse these tuples when assigning its index $j$.
The true auxiliary arity is `arity`, including children with zero
retained count. It must not be replaced by the number of positive counts
when charging the source auxiliary.

## Validation and bounded examples

All 18 focused tests pass. They check exact conservation and strict
edge-error bounds, self-loops, parallel and opposing edges, a residual
matching that requires changing an earlier choice, fixed integer edges,
invalid non-circulations, zero targets, zero actions, arbitrary reset
counts, the signed catalyst, and a scale of $10^{50}+3$.
The [independent review](multiway-rounded-flow-review.md) found no blocking
defect. Its additional checks cover 1,330 circulations, 13 cases requiring
rerouting, and 70 profiles; the general guarantee rests on the incidence
and integral-flow proof above.

The [saved reports](../results/multiway-rounded-flow.json) cover indices
2, 3, 4, 8, and 12, each at $K=1$ and $K=a^3$. Selected count totals are:

| Index | $K$ | Split factors $U$ | Reset factors $T$ | Catalyst factors | Active actions |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 1 | 4 | 1 | 4 | 3 |
| 4 | 1 | 11 | 1 | 11 | 6 |
| 8 | 1 | 16 | 1 | 16 | 11 |
| 12 | 1 | 20 | 1 | 20 | 15 |
| 12 | 1728 | 121092 | 8418 | 127782 | 163 |

Small counts alone say nothing about contraction or the final exponent.
In particular, the $K=1$ cases can lose much of the harmonic entropy.
No tensor sectors or large coefficient maps are materialized here.
The subsequent [finite-cost evaluator](multiway-finite-costs.md) charges
the full recipe using these integer flows and rigorous logarithm bounds.

```sh
python -m pytest tests/test_multiway_rounded_flow.py -q
python -m experiments.multiway_rounded_flow > results/multiway-rounded-flow.json
```
