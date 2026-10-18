# Independent review of the final-algorithm bounds

Reviewed 17 October 2026. Scope: `manuscript/algorithm-bounds.tex`, the quantitative rate proof and pooled recursion it uses, and `docs/exact-arithmetic-resolution.md`. This review concerns the new caveat-resolution arguments; it is not a new verification of every earlier tensor relation in the paper. It reviews the text of commit `e9aaa8b`; a later revision moved these results into Section 9 and renamed several symbols (see [final-algorithm-bounds-check.md](final-algorithm-bounds-check.md)).

## Rational construction

The rational separator is valid. With `Q=2M-2` and `L=4M-3`, every shifted exponent `delta+Q` lies in `[0,L-1]`. Lagrange interpolation at `1,...,L` therefore gives exactly the required Laurent moment identity, including `M=1`. On retained terms, the exponent of the degeneration parameter is `(g'-g)^2`, so the polynomial and degree are the same as for the original separator. Negative exponents occur in individual maps but cancel in their image before exactification; evaluations take place only at nonzero points.

The exactification weights `(-1)^(s-1) binom(E,s)` are correct for recovering `P(0)` from `P(1),...,P(E)` when `degree(P)<E`. Moving each weight to one leg of its direct-sum source copy preserves the tensor restriction. Rational evaluation/interpolation also realizes the stated convolution rank bound.

Replacing the separator copy count by `4M-3` changes only the copy overhead. Each ratio `(4M-3)/M` lies in `[1,4)`, so the overhead divided by `K` is below `12/(a ell_a)`, still below the allowance `1` in Step 2 of the quantitative proof. Thus its final constant `900` is unchanged. The source and target sides, and the lower bound `p>=tau_a>9/4`, are unaffected except that the new copy overhead can increase `p`. In particular, the proof does not silently assume that `p>2` follows from flattening alone.

## Explicit seed side and rank

The threshold `s=ceil(AB/(B-A))+1` equals the pooled recursion's threshold. For `q=r/m` and `rho=A/B`, the recursion estimates imply

`nu_h <= (1+rm/(r-m)) q^h`, and `q^h < q n^p`.

Using the integer inequalities `r-m>=1` and `q<=r` gives the advertised conservative constant `C=r(1+rm)s^3`. Counting classical scalar products gives a bilinear rank bound, independently of the cost of the linear maps. This includes a starting side already below the threshold.

The parameter choice gives `900/log a < 1800/ell <= delta/2`. Consequently `p<9/4+delta/2`, and with `d=(C+1)^ceil(2/delta)`, the inequality `d^(delta/2)>=C+1>C` proves `R<=C d^p<d^(9/4+delta)`. No real-number comparison or seed-side search is needed.

## Exact integer arithmetic

The denominator-clearing identity and the recursion scaling `D^(3k)` are correct. Keeping all divisions until the end avoids rational-height growth inside the recursion. The input, leaf-product and output-transform estimates bound intermediate partial sums as well as completed sums. The divisor estimate follows by applying the cleared seed identity to all-one matrices.

The proof that every side-`d>=2` full matrix-multiplication seed has `R>d^2` is sound: equality would make the left linear forms a basis, and a nonzero input selecting one form would make `B -> AB` have rank at most one, contradicting its rank `d rank(A)>=d`. This justifies geometric summation of the recursive linear-map costs, without an unproved strictness assumption about tensor flattening.

The bit bound `O_seed(n^p(b+log n)^2)` is valid using schoolbook integer arithmetic. The document correctly limits its sharper bound to integers or common-denominator representations and does not apply it unchanged to arbitrary separately encoded rational denominators.

## Finite precision

The path count `T=k(2q+R+3)+1` accounts for coefficient storage, multiplication by coefficients, sequential additions, both input paths, all output paths, and the scalar leaf multiplication. Reusing a stored rounded coefficient can repeat its error factor along a path; the count already allows this. Expansion into bilinear monomials and the absolute-sum bound `Gamma^k` give the claimed normwise error bound under the stated relative-error and exponent-range assumptions.

The sufficient condition on `u` implies `Tu<=1/2` because `eta<=1` and `Gamma>=d>=1`. Hence `gamma_T<=2Tu`, giving the stated target error and logarithmic significand precision for a fixed seed. This is a conditional forward-error theorem, not a claim of binary64 practicality or backward stability. Those distinctions are preserved.

## Construction-resource review

The new `thm:construction-resources` gives a valid conservative route from a rational gate count to coefficient and bit-cost bounds. It correctly includes the bit length of the rational allowance, which cannot be bounded by that allowance's numerical value. Its bound `s<=AB+2<=W^3` gives `C<=W^13<=H`; hence both the final scalar multiplication count and every active-product count are below `Q^4`. The depth bound follows from strict decrease of the integer side above the leaf threshold. Padding, batching, all downward linear forms, and the upward coefficient map fit safely within the stated `Q^14` coordinate bound. The resulting `Q^50` gate envelope has ample slack.

For reduced rational numbers, the height recurrence `t -> 2t+1` is valid for addition, subtraction, multiplication and defined division. Starting from at most `Q` bits and at most `S` gates therefore gives `2^S(Q+1)-1<=2^(2S)` bits per numerator or denominator. Schoolbook arithmetic and Euclidean gcd give the advertised `O(2^(8S))` total bit cost after loop control and output are included. Counting `3R d^2<=3C d^5` coefficient entries is correct.

The initial proof-presentation concern about the assembly envelope has been resolved by the explicit tally in `docs/final-size-derivation.md`, Section 4, item 3. For `T=barw+barz+K+I+1`, a catalytic use has at most `6T` primitive factors, each with leg dimension at most `W^3`, and at most `10T` extra labels. Its ambient leg dimension is therefore at most `W^(28T)`. Source and catalyst decompositions together have `3(barw+barz)` convolution positions, since the `3K` source positions and `3(barw+barz-K)` catalyst positions add to that count. Their dimensions fit the same envelope. Catalyst reuse adds at most four powers of `W` for identity matrix factors and two for copy labels, giving `W^(34T)`. It preserves one catalyst factor. The explicit expanded stage bound `W^(40(j+1)T)` fits inside `H=W^(100(j+1)T)`. The tally supports the stated dense implementation and removes reliance on an unspecified constant hidden inside `F`.

The manuscript transcriptions in `manuscript/arithmetic-bounds.tex` preserve the integer and finite-precision results reviewed above. They correctly distinguish the seed exponent from the pooled exponent.

## Uniform counted-setup algorithm

The integrated assembly tally preserves the resource proof reviewed above. The new `cor:uniform-setup` also has a valid selection argument. For a fixed side-`d` rank-`R` seed, the ordinary dense recursion on side `d^h` uses at most

`R^h [1 + 6d^2 R/(R-d^2)] <= (1+6Rd^2) R^h`

scalar operations. Padding to `d^h<dn` introduces the further factor `R`, so the stated integer `G=(1+6Rd^2)R` suffices without an unspecified seed-dependent constant.

At dimension `n`, simulating each allowance-`1/t` constructor for a budget of `n` bit steps and including the test `G^t<=n` is effective. For every fixed `t`, that construction and test have a fixed finite cost, and `G` is fixed. The candidate therefore succeeds for all sufficiently large `n`. Taking the largest successful candidate among `1,...,floor(log_2 n)` gives `t(n)->infinity`, even if constructor time is highly nonmonotone in `t`. The chosen seed obeys `p_seed<9/4+1/t(n)` and `G<=n^(1/t(n))`, hence the scalar cost is below `n^(9/4+2/t(n))`.

A straightforward bit clock gives total preprocessing `O(n(log n)^2)`; this overhead is negligible in the claimed mixed model, which charges bit operations for coefficient setup and scalar operations for matrix evaluation. The corollary proves a single uniform `n^(9/4+o(1))` upper bound. It proves neither that one fixed finite seed has exponent exactly `9/4` nor an `O(n^(9/4))` upper bound. The introduction's scope wording was returned for tightening so that strict pooled-exponent bounds are not read as a separate lower-bound theorem about every possible finite seed rank.

## Scope of the conclusion

The reviewed additions remove the specific absence of final side, rank, coefficient-height and preprocessing-time bounds, conditional on the paper's earlier tensor construction. They also supply bit complexity and a conditional finite-precision forward-error theorem. This review has not independently re-proved the earlier determinant filtration, occupation estimates or complete catalytic tensor construction, and does not certify practical feasibility or fixed-precision performance.
