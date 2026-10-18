# Final algorithm bounds: resolution

Version 4 of the paper supplies the bounds that version 3 left open. Section 9
of [finite-extraction.pdf](../../finite-extraction.pdf) adds a
rational variant of the construction, an explicit seed side, bounds on the
coefficients and the preprocessing cost, integer bit complexity, a
sufficient precision for a normwise forward error, and one algorithm for
all input sizes.

These are proofs about the paper's construction. They do not construct
the enormous seed or establish practical performance. Symbols and result
numbers below are those of the paper.

## Rational coefficients (Section 9.1)

The construction uses roots of unity in three places: the rank
decompositions of convolution tensors, the separators, and exactification.
Lemma 9.1 replaces each by interpolation at the integer nodes `1, 2, ...`:

- (a) `C(r,b)` keeps rank `r+b-1`, with nodes `1,...,r+b-1`.
- (b) A separator with `M` sectors has phase exponents between `-(2M-2)` and
  `2M-2`. Interpolation at `1,...,4M-3` keeps exactly the zero phase, so
  `4M-3` source copies (instead of `2M-1`) give the same polynomial and the
  same degree bound `(M-1)^2`. Fewer positive nodes cannot work.
- (c) Exactification keeps its `E` copies, with weights `(-1)^(l-1) binom(E,l)`.

Only the copy overhead changes: each ratio `(4M_i-3)/M_i` lies in `[1,4)`,
so `log(L^Q/M^3) < 3I log 4`, and divided by `K` this is below
`12/(a ell_a) <= 1`. Step 5 of the proof of Theorem 8.1 uses only this
bound from Step 2, so the rational variant satisfies
`9/4 < tau_a <= p < 9/4 + 900/log(a)` and `log(A) <= 181 a^5 ceil(log2(a))^2`.
The cyclotomic construction and the finite examples of Section 10 are
unchanged; the rational construction is a second variant.

## An explicit seed (Theorem 9.2)

For a positive rational allowance `eps`, put `eps' = min(eps, 1/2)`,
`ell_a = ceil(3600/eps')` and `a = 2^ell_a`; this is the index that
Corollary 8.2 assigns to `eps'/2`, so `p < 9/4 + eps'/2`. With the leaf
threshold `n_* = ceil(AB/(B-A)) + 1` of the pooled recursion, put

```
Xi  = r_*^Q (1 + r_*^Q m_*) n_*^3,
d_0 = (Xi + 1)^ceil(2/eps').
```

Unrolling the pooled recursion at side `d_0` gives a rational seed with
`R <= Xi d_0^p < d_0^(9/4+eps') <= d_0^(9/4+eps)` products. No search for a
seed side is needed. The search of Corollary 8.7 remains in the paper for
the cyclotomic construction.

## Coefficients and preprocessing (Theorem 9.3)

Theorem 9.3 defines integers `T, F, W, H, Q, S` (fraktur in the paper) from
the input length `b_eps`, the rounded counts, the copy counts, the
dimensions and `d_0`, with `S = Q^50`. A fixed dense implementation computes
the seed in at most `S` steps and writes at most `3 Xi d_0^5` coefficients.
Every reduced numerator and denominator has at most `2^(2S)` bits, and the
whole computation takes `O(2^(8S))` bit operations. The proof counts the
primitive data, the dense assembly, the unrolling, and the growth of bit
lengths (at most `2t+1` bits after one operation on `t`-bit operands). The
[size derivation](final-size-derivation.md) gives the factor counts behind
the dense-assembly step.

## Recursion with a fixed rational seed (Sections 9.4 and 9.5)

For any fixed rational seed of side `d_0` with `R` products, write
`p_seed = log_{d_0}(R)` and `ell = ceil(log_{d_0}(n))`.

- **Lemma 9.4.** `R > d_0^2`, and block recursion costs at most
  `c_seed n^p_seed` operations, with `c_seed = (1 + 6 R d_0^2) R`.
- **Proposition 9.5.** Clearing all seed denominators by `c_den` gives an
  integer recursion whose result is `c_den^(3 ell) XY`, divided exactly at
  the end. For integer entries below `2^b_in`, intermediate integers have
  at most `2 b_in + ell(2 c_in + c_out) + 2` bits, and the cost is
  `O_seed(n^p_seed (b_in + log n)^2)` bit operations.
- **Proposition 9.6.** With unit roundoff `u`, recursive summation in a
  fixed order, rounded nonzero coefficients and no underflow or overflow,
  `||XY_computed - XY||_max <= gamma_chi Upsilon^ell ||X||_max ||Y||_max`,
  where `chi = ell(2 d_0^2 + R + 3) + 1` and `Upsilon` is the product of
  the three maximal absolute row sums. A normwise target `theta` needs
  `O_seed(log n + log(1/theta))` significand bits. This is a sufficient
  condition; it says nothing about backward stability or binary64 accuracy.
- **Corollary 9.7.** Trying allowances `1/v` with a budget of `n`
  Turing-machine steps each, and using the largest `v` with
  `c_seed^v <= n`, gives one algorithm that multiplies `n x n` matrices
  over any field of characteristic zero in `n^(9/4+o(1))` steps. Steps are
  Turing-machine steps during preprocessing and field operations
  (including divisions) afterwards. Below an astronomically large `n` the
  algorithm multiplies classically. It does not give `O(n^(9/4))`.

## Verification

- [Independent review](final-algorithm-bounds-review.md) of the commit that
  added these results.
- [Second check and revision](final-algorithm-bounds-check.md): six
  independent checkers recomputed every new result with their own exact
  arithmetic. They found no fatal or major error. The minor problems and the
  exposition changes are listed there and were fixed in the paper.
- [Interpolation audit](../experiments/rational_interpolation_audit.py):
  separator moments for `M=1,...,9`, full label checks through `M=6`,
  exactification through `E=20`, 20 convolution identities, and 600
  pooled-recursion cases. The pooled check verifies the leaf count against
  `r(1+rm) n_*^3 (r/m)^depth`, the step before the exponent `p` enters.
- [Arithmetic checks](../experiments/rational_seed_arithmetic_checks.py) and
  their [saved report](../results/rational-seed-arithmetic-checks.json): 16
  seed identities, 12 integer-scaling trials, 24 rounded recursion trials
  and 4,854 exact rounding checks on a rescaled Strassen seed. The observed
  errors are below 1% of the proved bound, so these trials confirm that the
  bound holds, not that it is tight.
- Version 3 is preserved in [archive/v3](../../archive/v3/).

Small checks support the formulas; they do not run the enormous seed
construction and do not replace peer review.
