# Resolving the exact-arithmetic qualification

Status: proved from the rational seed identity; independent analysis, 17 October 2026. Incorporated into Section 9.4 of the paper, where `D`, `k`, `p`, `b`, `A` and `B` of this note are written `c_den`, `ell`, `p_seed`, `b_in`, `X` and `Y`. The bounds on seed construction mentioned as a separate question below are now Theorems 9.2 and 9.3.

The paper's exact rational seed already implies bounds on integer bit complexity and on the precision sufficient for a normwise error target. These bounds do not imply useful binary64 performance. They also do not bound seed construction as a function of the allowance: that is a separate question.

## What the current manuscript supplies

Corollary `cor:seed` in `manuscript/quantitative.tex` constructs, for each fixed positive rational allowance, a fixed rational bilinear seed of side `d >= 2` and rank `R`, with exponent `p = log_d R` below the requested bound. Every such full matrix-multiplication seed has `R > d^2`, as justified below. A seed is three arrays

- `U,V` of shape `R × d^2`;
- `W` of shape `d^2 × R`.

Its identity is `vec(AB) = W ((U vec(A)) ⊙ (V vec(B)))`. Here `⊙` denotes entrywise multiplication. The identity is exact over the rationals; the inputs can be scalars or matrices over a commutative ring containing those coefficients.

Everything below is a deterministic consequence of this finite identity. No unproved numerical behavior of the paper's tensor extraction is needed.

For completeness, the first tensor flattening has rank `d^2`, hence `R>=d^2`. If equality held, the `d^2` left linear forms would be independent. Choose a nonzero matrix `A` on which exactly one form is nonzero. The seed would make the linear map `B -> AB` have rank at most one. Its actual rank is `d rank(A)>=d>=2`, a contradiction. Thus `R>d^2`; this argument does not rely on the seed exponent being strictly above `9/4`.

## Exact integer evaluation with controlled intermediate sizes

Choose a positive integer `D` divisible by the denominators of every seed coefficient. Define integer arrays `U' = DU`, `V' = DV`, `W' = DW`, put `q=d^2`, and let

`H = max(1, max |U'|, max |V'|, max |W'|)`.

The integer arrays satisfy

`W' ((U' vec(A)) ⊙ (V' vec(B))) = D^3 vec(AB)`.

For an input side `n >= 2`, pad by zeros to side `N=d^k`, where `k=ceil(log_d n)`, so `n <= N < dn`. Recurse with the integer arrays, perform integer multiplication at scalar leaves, and perform no division inside the recursion. The resulting root array is exactly `D^(3k) AB`. Divide each entry by `D^(3k)` once at the end. The divisions are exact for integer inputs.

This scaling assertion follows by induction on the remaining recursion depth: a child with remaining depth `h-1` contributes `D^(3(h-1))` times its intended block product, and the parent application of the three integer arrays contributes the additional factor `D^3`.

Suppose every input entry has absolute value strictly less than `2^b`, with `b >= 1`. Put

`c_in = ceil(log_2(qH))`, `c_out = ceil(log_2(RH))`,

`L = 2b + k(2c_in + c_out) + 2`.

Every intermediate integer has at most `L` bits including a sign bit. Indeed:

1. After `j` input-transform levels, every entry has magnitude below `2^b(qH)^j`.
2. A scalar leaf product has magnitude below `2^(2b)(qH)^(2k)`.
3. Each output-transform level increases the maximum magnitude by at most `RH`, and there are at most `k` such levels.

Partial sums obey the same estimates because replacing the full sum of absolute values by a partial sum cannot increase the bound. The final divisor fits too: since the unscaled integer identity computes the product of all-one `d × d` inputs, `D^3 d <= Rq^2 H^3`; in particular `D^(3k) <= ((qH)^2 RH)^k`.

The number of scalar operations is `O_seed(N^p)`. For example, each internal node of side `m` performs at most `(4Rq+2qR)(m/d)^2` integer additions and multiplications by seed coefficients, plus its `R` recursive calls. Summing the geometric series gives `O_seed(N^p)` because `R>d^2`. Leaf products, all final divisions, and forming the divisor fit within the same bound.

Using ordinary schoolbook multiplication and division, each operation on `L`-bit integers costs `O(L^2)` bit operations. Consequently,

`bit_cost(n,b) = O_seed(n^p (b+log n)^2)`.

The constants depend on the fixed seed, hence on the fixed allowance. This is a fully specified bit bound, not a unit-cost arithmetic statement. Faster integer arithmetic can improve the logarithmic factors, but is unnecessary for this conclusion.

For constant-bit integer input, the bit cost is `O_seed(n^p log^2 n)`. For every fixed `delta>0`, `log^2 n=O_delta(n^delta)`, so the seed family also gives integer bit exponent at most `9/4`: choose a seed with exponent below `9/4+delta/2` and absorb the logarithmic factors into the remaining allowance. The seed is fixed before `n` grows, and setup is not included in the displayed per-input bound.

## Inputs whose representation matters

The preceding bound extends directly to rational inputs supplied with one common denominator per matrix: clear those two denominators, multiply the integer numerators, and restore their product in the output. The parameter `b` must bound the bit sizes after clearing those denominators. Bounded-precision dyadic inputs with bounded exponent range are an important special case.

Arbitrary independently encoded rational entries require care. If each of `n^2` input denominators has `b` bits, their product can have `n^2 b` bits. A common-denominator reduction is valid but may replace `b` by `O(n^2 b)`. The sharper integer bound must not be quoted unchanged for that representation. Similarly, arbitrary real inputs need an accuracy model or an oracle; they are not finite exact bit strings.

The rational identity also reduces modulo every prime not dividing `D`. For primes dividing `D`, reducing those coefficients is invalid. Integer lifting followed by reduction remains valid for prime-field inputs, using the integer algorithm above, with integer input bit size `O(log ell)` for characteristic `ell`. This observation does not assert an equally efficient arbitrary extension-field implementation.

## A conservative finite-precision bound

A fixed seed also gives an explicit, possibly very poor, normwise forward-error bound. This is distinct from a practical stability certification.

Write

`s_U = max_r sum_i |U_ri|`,

`s_V = max_r sum_i |V_ri|`,

`s_W = max_i sum_r |W_ir|`,

`Gamma = s_U s_V s_W`.

The seed identity on all-one input matrices gives `Gamma >= d`, so `Gamma` is positive and at least one. These are computable rational numbers after the seed is known.

Consider the usual recursive implementation: form each input linear combination with a sequential dot product, recursively multiply the resulting blocks, and combine the outputs with sequential dot products. Assume represented input entries are the reference inputs. Assume each addition, subtraction, multiplication, and each stored nonzero coefficient obeys the relative-error model with error at most `u`, and that no operation underflows or overflows. Zeros are represented exactly. Rational coefficients can be rounded once when stored; those rounding factors are included below.

Let

`T = k(2q+R+3)+1`, and `gamma_T = Tu/(1-Tu)` when `Tu<1`.

Then the computed product obeys

`||C_hat - AB||_max <= gamma_T Gamma^k ||A||_max ||B||_max`.

Here `|| · ||_max` is the largest absolute entry, and the padded product is cropped to the original side. The bound is valid for the chosen simple dot-product evaluation order; a different implementation needs its own operation-path count.

Proof: fully expand one computed output into its signed bilinear monomials in the original input entries. Each monomial follows one coefficient at each input-transform level on the left and on the right, one scalar product, and one coefficient at each output-transform level. At one input-transform level its factor includes at most one coefficient-storage error, one coefficient-multiplication error, and `q-1` addition errors; that is `q+1` factors. The two input paths together contribute at most `2k(q+1)` factors. Each of the `k` output levels contributes at most `R+1` factors, and the leaf multiplication contributes one. This gives `T` factors, even when a coefficient-storage error is reused at several levels. Their product differs from one by at most `gamma_T`.

The sum of the absolute values of the exact monomials is at most `Gamma^k ||A||_max ||B||_max`: each input-transform layer contributes `s_U` or `s_V`, and each output layer contributes `s_W`. The triangle inequality finishes the proof. Cancellation is allowed throughout; it is why the bound scales by input norms rather than the magnitude of the true answer.

For `0<eta<=1`, the explicit sufficient condition

`u <= eta / (2T Gamma^k)`

implies `||C_hat-AB||_max <= eta ||A||_max ||B||_max`. In a binary rounding model this can be achieved with at most

`ceil(log_2(2T/eta)) + k ceil(log_2 Gamma) + 2`

significand bits. For a fixed seed this is `O_seed(log n + log(1/eta))`. Exponent range must also be sufficient for the inputs and all intermediate values; a significand bound alone does not prevent underflow or overflow.

This is a concrete answer to whether exact arithmetic inherently prevents approximate evaluation: it does not. The displayed `Gamma` and `T` can nevertheless be enormous. The bound does not establish a useful binary64 recursion depth, a small error constant, componentwise relative error, backward stability, or speed relative to BLAS.

## Relation to established numerical analysis

The generic conclusion is consistent with [Demmel, Dumitriu, Holtz and Kleinberg, *Fast matrix multiplication is stable*](https://arxiv.org/abs/math/0603207), which analyzes recursive bilinear algorithms and establishes the compatibility of fast arithmetic exponents with normwise stability. The derivation above is supplied directly so the paper's finite rational seed has explicit parameters without relying on an unspecified implementation of that general theorem.

## Suggested scope statement

A precise replacement for an unqualified “all results concern exact arithmetic” is:

> The tensor identities and arithmetic-operation bounds are exact. After the rational seed is fixed, integer inputs of bit length `b` can be multiplied in `O_eps(n^p(b+log n)^2)` bit operations with schoolbook integer arithmetic, where `p<9/4+eps`. The seed also gives a computable normwise forward-error bound with precision growing logarithmically in `n` for any fixed error target. These statements do not establish useful fixed-precision performance, backward stability, or practical feasibility.

Any final manuscript statement about the allowance dependence of the hidden constants must be reconciled with the separate quantitative construction analysis. The results here isolate input-size dependence and make no unsupported assertion about practical seed sizes.

## Verification record

- Read the rational-descent lemma, rational-seed corollary, seed-size remark, arithmetic-cost convention, and current scope and discussion.
- Derived denominator scaling by induction and intermediate heights by absolute-value bounds.
- Derived the operation count from the actual block recursion, including the condition `R>d^2`.
- Checked the numerical bound by expansion of each rounded arithmetic path, explicitly including rounded coefficients and both input branches of the scalar multiplication.
- Verified the primary literature entry for the existing stability theorem; no claim here rests on secondary descriptions.
- As a supplemental check of the scaling and height argument, evaluated a rationally rescaled Strassen seed (`U/2`, `V/3`, `6W`, common denominator `D=6`) on four deterministic random integer matrix pairs at each side 2, 4 and 8. The integer recursion returned exactly `6^(3k) AB` in all 12 cases. Last-trial peak sizes were 20, 29 and 37 bits, below the proved bounds 36, 60 and 84 bits. This checks the scaling mechanism, not the astronomically large paper seed. These checks are now reproducible with `python experiments/rational_seed_arithmetic_checks.py --check`; the saved artifact is `results/rational-seed-arithmetic-checks.json`. The script additionally certifies the seed on all 16 matrix-unit pairs, checks 24 recursive rounded products using exact simulated binary rounding at 12 and 20 significand bits, and verifies tie breaking and the rounding relative-error condition.

The manuscript-ready statements and proofs are in `manuscript/arithmetic-bounds.tex`. The section compiled independently to two pages using the repository preamble; final cross-references and bibliography are resolved when the section is included in the main manuscript.
