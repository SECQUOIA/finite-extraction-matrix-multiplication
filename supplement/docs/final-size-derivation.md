# Explicit final seed size, coefficient height, and construction time

This note records the size analysis requested on 2026-10-17. Status: incorporated into Theorems 9.2 and 9.3 of the paper. The notation here differs from the paper's: `s`, `C` and `d` here are `n_*`, `Xi` and `d_0` there. The bounds are deliberately loose. Their purpose is to replace an unbounded termination statement by explicit finite resource bounds, rather than to suggest a practical algorithm.

## 1. What already follows from the existing pooled recursion

Write `r = r_*`, `m = m_*`, `rho = A/B`, `q = r/m`, and

\[
 s=\left\lceil\frac{A}{1-A/B}\right\rceil+1.
\]

Suppose the scheme has pooled exponent `p > 2`. At the final pooled depth `h`, the proof of Lemma `lem:batch` gives

\[
 \nu_h\le\left(1+\frac{rm}{r-m}\right)q^h,
 \qquad \rho^h n>\rho.
\]

Since `q = rho^{-p}`, the second inequality implies `q^h < q n^p`. The number of classical leaf products, and thus of rank-one terms before coefficient descent, is at most `nu_h s^3`. Consequently

\[
 R_n^{\mathrm{field}}
 <r(1+rm)s^3n^p.
\tag{1}
\]

Here we used `r-m >= 1`, `q <= r`, and deliberately discarded the factor `1/m`. No constant hidden by big-O remains.

For the original cyclotomic scheme of degree `g = phi(Lambda)`, rational descent gives the equally explicit bound

\[
 R_n^{\mathbb Q}\le C_gn^p,
 \qquad C_g=g^2r(1+rm)s^3.
\tag{2}
\]

If that scheme was constructed with allowance `epsilon/2`, then

\[
 d=(C_g+1)^{\lceil2/\epsilon\rceil}
\tag{3}
\]

already satisfies `R_d < d^{9/4+epsilon}`. Indeed, `d^{epsilon/2} >= C_g+1 > C_g` and `p < 9/4+epsilon/2`. Therefore the first-success search in the original seed corollary stops at a side no larger than (3). One can also skip that search and use (3) directly. This resolves the missing upper bound for final side and rank even without changing the cyclotomic construction.

## 2. A rational variant avoids coefficient descent

The parent investigation found a simpler route for bounding all resources. Replace only the Fourier and interpolation choices; retain the determinant filtration, types, catalyst, and pooled recursion.

* In a separator with `M` sectors, the phase exponent is `delta = g' + e - g - e'`, which lies in `[-2(M-1), 2(M-1)]`. Extract the Laurent coefficient of exponent zero by rational interpolation at `1,...,4M-3`, after multiplying by the variable to the power `2(M-1)`. Thus use `L_i' = 4M_i-3` source copies. The desired phase condition is still exactly `delta = 0`, and its surviving degeneration degree is still `(M_i-1)^2`.
* At exactification use `1,...,E` instead of roots of unity. Constant-term interpolation has integer weights `(-1)^{ell-1} binom(E,ell)` for `1 <= ell <= E`.
* For each convolution use ordinary evaluation at `1,...,r+b-1` and inverse Vandermonde interpolation. Its rank remains `r+b-1` over the rationals.

These choices produce rational maps. With `L' = product_i (4M_i-3)^3`, the definitions of `r` and `m` remain the same except for replacing `L` by `L'`. The only exponent-bound change is

\[
 0\le\log(L'/M^3)<3I\log4.
\]

At the stated enormous parameter family this is still less than `K`: `I <= 2a^2`, `K=a^3 ell_a`, and `log 4 < 2`. Thus the original copy-overhead allowance of one unit after division by `K` still holds. The `900/log a` bound is unchanged. This variant needs neither a cyclotomic field nor rational descent.

## 3. Fully specified bounds for the rational variant

For arbitrary positive rational input `epsilon`, put

\[
 \delta=\min(\epsilon,1/2).
\]

Construct the rational scheme above with allowance `delta/2`. Thus its parameters can be fixed as

\[
 \ell=\max\{64,\lceil3600/\delta\rceil\},\quad
 a=2^\ell,\quad K=a^3\ell,\quad j=a\ell,\quad N=k=1.
\]

In particular `p < 9/4+delta/2 <= 5/2 < 3`. Define the following integers from the rounded counts:

\[
 \begin{split}
 C&=r(1+rm)s^3,\\
 d&=(C+1)^{\lceil2/\delta\rceil},\\
 W&=2+b+a+K+j+\bar w+\bar z+I+E+\kappa+r+m+A+B
       +\sum_i(M_i+L_i'),\\
 F&=100(j+1)(\bar w+\bar z+K+I+1),\\
 H&=W^F,\qquad Q=H+d+2,\qquad S=Q^{50}.
 \end{split}
\tag{4}
\]

Here `b` is the bit length of the rational input, `kappa = kappa_1`, and `s` is the integer leaf threshold above. Every integer in (4) is determined by the stated rational linear systems, deterministic rounding, factorial formulas, and integer powers. Neither a seed search nor a search over coefficient identities occurs in these definitions.

A direct dense implementation described below produces a rational decomposition with

\[
 \boxed{\quad
 R<d^{9/4+\delta}\le d^{9/4+\epsilon},\qquad
 R\le Cd^3,\qquad
 \operatorname{bits}(\text{each numerator or denominator})\le2^{2S},\qquad
 \text{construction bit operations}\le2^{8S}.
 \quad}
\tag{5}
\]

The runtime convention in (5) is ordinary binary integer arithmetic using schoolbook multiplication and Euclidean gcd, with a fixed conventional Turing implementation; a fixed startup constant can be absorbed in the enormous displayed bound. The arithmetic operation count is at most `S`. There are at most `3Cd^5` rational entries in the three dense coefficient arrays. A finite description of a recursion consists of those arrays together with the fixed blocking rule.

## 4. Counting the construction operations

The following deliberately inefficient implementation suffices for (5).

1. Compute row occupations with rational Gaussian elimination, and circulation rounding with the shortest-augmenting-path rule. Each row has at most `3a+1` vertices and at most `O(a^2)` edges, and there are fewer than `a` rows. The number of rational operations, integer divisions, and comparisons is bounded by a fixed polynomial of degree below 20 in `W`. Count comparisons and floors as elementary integer operations in the final bit-cost calculation. Factorials, sector counts, and the dimensions and multiplicities in (4) can be computed by repeated multiplication, and powers by binary exponentiation. Their arithmetic-operation counts also fit this bound. No factorization is required.
2. Generate determinant-basis matrices by expanding powers of `uv'-vu'` and invert the needed square matrices by rational Gaussian elimination. Generate inverse Vandermonde matrices for integer convolution evaluation and the separator interpolation weights in the same way. Evaluate Laurent monomials by repeated multiplication and division. The largest exponent needed at a single separator is bounded by a fixed multiple of `W^2`; the number of nodes in any interpolation is at most `W`. Thus all these primitive arrays are generated with a number of rational operations polynomial in `W` of degree below 20.
3. Form the scheme maps by direct sums, Kronecker products, coordinate selections/permutations, and ordinary dense matrix products. Expand after every such operation; exploit no sparsity. The following count makes the exponent in `H` explicit. Set `T = bar w+bar z+K+I+1`.

   * A single catalytic use has `3(bar w+bar z)` convolution positions and `3 bar w` dot-product positions, hence at most `6T` primitive factors. Each primitive leg has dimension at most `W^3`; this also covers a combined determinant-basis space. Even counting all the source separator-copy labels (`3I`), target sector and auxiliary labels (`6I`), and the exactification label (`1`) simultaneously adds at most `10T` labels, each with range at most `W`. Thus every local intermediate leg dimension is at most `W^{18T+10T}=W^{28T}`. Counting labels from both source and target simultaneously deliberately overestimates every actual stage.
   * The source and catalyst rank decompositions contain at most `3(bar w+bar z) <= 3T` convolution positions in total, with at most one rank-summand label per position. Their ambient leg dimensions are bounded by `W^{9T+3T}=W^{12T}`. The external matrix factor and direct-sum copy label add at most three more powers of `W`. This is below the preceding local bound.
   * In a reuse step, the induction in Proposition `prop:relative` applies the one-step map once to the existing catalyst, tensored with matrix identities. At most two such matrix identities need be included in an intermediate expression. Their sides are bounded by `A` and `B`, so their legs add at most four powers of `W`. The direct-sum multiplicities have the form `alpha^u beta^v` with `0 <= u,v <= j`; their product is at most `alpha^j beta^j <= rm <= W^2`. This adds at most two powers. Thus every intermediate leg throughout reuse has dimension at most `W^{28T+6} <= W^{34T}`. There is one one-step occurrence at each of the `j` reuse steps along a fixed branch; reuse never tensors two catalysts together.
   * Before expanding labels, a local assembly needs at most `40T` matrix-assembly stages: two stages per primitive factor for basis changes and coordinate selection (at most `12T`), at most `3I` oriented separators, at most `3I` canonical reindexings, at most `16T` tensor/direct-sum combinations, and at most three exactification/ledger stages. These sum to at most `37T+3 <= 40T`. Expanding all labels multiplies this count by at most `W^{34T}`. Including all reuse steps and source decompositions therefore requires at most `40(j+1)T W^{34T}` stages. Since `W >= 40` and `j,T <= W`, this is at most `W^{40(j+1)T}`. This remains far below `H=W^{100(j+1)T}`.

   Every intermediate matrix dimension and the stage count are consequently bounded by `H`. Each dense matrix product uses at most a fixed multiple of `H^3` rational operations. Even allowing an extra `H` factor for generation and copying of primitive entries, the total dense assembly uses fewer than `H^20` rational scalar operations.
4. Unroll the pooled recursion at side `d`. Above its leaf threshold the integer side strictly decreases, because `A ceil(n/B) < (A/B)n+A < n` whenever `n > A/(1-A/B)`. Hence the number of depths is at most `d`. At every depth the same estimate used in (1), or its prefix version, bounds the number of active products by

   \[
   \nu_h\le r(1+rm)d^p\le r(1+rm)d^3<Q^6.
   \]

   Every recursive matrix side is at most `d`. A padded side is at most `d+B`, and the number of padded products in a partly filled batch adds at most `m`. The temporary source products number at most `r(nu_h+m)+m`. Using `nu_h < Q^6`, their total entry count is at most `4Q^7(2Q)^2 = 16Q^9 < Q^{14}`. Thus all full vector spaces used to propagate the linear forms have dimensions below `Q^{14}`. Retain these vectors as dense linear forms in the original `d^2` inputs. Apply the scheme by dense linear maps, separately for the two inputs, and form the upward dense output map. Matrix multiplication of dimensions at most `Q^{14}` costs fewer than a fixed multiple of `Q^{42}` rational operations per depth. Replacing each classical leaf product by its rank-one term and writing its coefficients costs less than this bound: a rank-one leaf contribution simply selects two downward forms and one column of the upward map. With at most `d <= Q` depths and the prior `H^{20}` work, the total is below `Q^{50}`.

The numerical powers here intentionally absorb fixed factors, including the three tensor legs. They are not estimates of a good implementation. In particular the enormous envelope `H` is used to avoid assuming that a low-rank intermediate tensor has a small ambient coordinate space.

## 5. Rational height and bit cost

For a reduced rational `x=u/v`, with positive `v`, define its height in bits to be

\[
 h(x)=\max\{\lceil\log_2(|u|+1)\rceil,
                 \lceil\log_2(v+1)\rceil\}.
\]

If `h(x), h(y) <= t`, each defined sum, difference, product, or quotient has height at most `2t+1`. Reduction by gcd cannot increase this bound. Every initial integer literal in the construction can be chosen with bit height at most `Q`; larger factorials, binomial coefficients, integer powers, and interpolation constants are built by the operations already counted. The input numerator and denominator also have bit length at most `b <= Q`.

After at most `S` scalar operations every rational value consequently has height at most

\[
 2^S(Q+1)-1\le2^{2S}.
\]

Classical arithmetic on integers of this bit length, including gcd and exact division, takes at most a fixed multiple of the cube of the bit length. There are at most `S` rational arithmetic steps and a smaller number of loop-control, comparison, indexing, and copying operations. Thus `2^{8S}` bit operations bounds the complete construction, including output. This argument covers the occupation denominators as well: they need no separate a priori denominator estimate.

## 6. Scope and remaining issue

The side/rank bound in Section 1 is available for the manuscript's existing construction as written. The stronger all-rational resource theorem in Sections 2–5 depends on adding and checking the rational interpolation variant. It does not prove numerical stability or a useful floating-point running time. Exact rational maps make bit-complexity analysis possible, but that is a separate issue from conditioning. The bounds here are upper bounds for exact synthesis, not evidence of computational feasibility.

The potentially fragile point in transplanting this note into a formal theorem is the dense assembly count in Section 4: it must accompany a stated implementation (direct sums, tensor products, dense products and coefficient propagation), rather than be claimed for every possible implementation of the proof. The construction described here is such an implementation; a sharper practical estimate would require writing and auditing the assembler itself.
