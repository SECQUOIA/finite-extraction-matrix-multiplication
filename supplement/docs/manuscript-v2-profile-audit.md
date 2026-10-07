# Independent audit of the v2 profile, flow, rounding, and cost arguments

Reviewed on 2026-10-07 against the authored TeX in `manuscript/profile.tex`,
`flows.tex`, `rounding.tex`, `quantitative.tex`, `extraction.tex`, and
`costs.tex`. The exact binary certificate in
`appendix-exact-certificate.tex` was also checked for consistency with the
new construction. The review used the definitions in `preliminaries.tex`
and the stated interfaces of the tensor maps in `maps.tex`.

The review was adversarial and symbolic. No experiments, numerical
certificates, or literature searches were rerun. Saved numerical intervals
were accepted as supplied evidence. The tensor-map and recursion proofs
were assigned a separate independent review; this audit checks their
parameter interfaces and the scalar cost chain, rather than replacing that
review.

## Conclusion and findings

No major mathematical error was found in the reviewed chain. In particular,
the occupation estimates are uniform in the row length, circulation
rounding preserves all required balances, zero occupations cause no
division problem, and the explicit convergence constants follow from the
stated bounds.

The following integration issues were found during the audit:

1. **Resolved during review:** the initial `costs.tex` still used the old
   sixfold formulas and duplicated the exact-normalization theorem and
   equation labels in `appendix-exact-certificate.tex`. The rewritten
   `costs.tex` instead analyzes the rounded threefold construction and
   refers to the exact certificate only as a comparison. The duplicate
   theorem and the incompatible reference to the new finite-exponent
   formula are gone.
2. **Resolved during review:** the exact-certificate appendix now explicitly
   scopes its `K,U,T` and counts to the binary benchmark, writes its
   catalyst as `Cat^ex`, and describes `2^(2NU)` as the sixfold binary
   source dimension. Its exponential denominator result is not presented
   as a lower bound for the rounded construction.
3. **Remaining exposition issue at the time of review:** `discussion.tex`
   still referred to the removed obstruction appendix and described
   controlled approximate frequencies and different convolution relations
   as future alternatives, although the new main construction supplies
   both. The author was notified and was revising these surrounding
   sections. This does not invalidate the new proofs, but should be
   corrected before the final document is built.
4. **Minor:** the new finite-example table in `costs.tex` declares six
   right-aligned columns and contains five columns of entries. Use five
   alignment specifiers.
5. **Minor clarification:** when applying the finite-multinomial bound to
   the reset counts `(m_r,Nz_r-m_r)`, explicitly discard zero counts.
   When `Nz_r=1`, the modal count is `m_r=0`; the positive-support
   convention already used in the formula handles this correctly, but
   restating it prevents a reader from substituting `log 0`.

No manuscript TeX was edited by this reviewer.

## Least-profile argument

The proof in `profile.tex` remains valid after moving the exact certificate
to the appendix. The concavity slack formula includes the boundary
`b=a`. Its affine tail extends to `b=a-1`, and concavity puts the tail's
extension above every earlier entry. This proves the tripling axiom for
the proposed profile.

The diagonal recurrence follows from tripling at the row index and
decreasing increments. The off-diagonal argument uses a finite tripling
landmark beyond the desired column and the chord inequality for a discrete
concave sequence. This includes the case in which the smaller index is one.
The cubic upper bound, strict diagonal inequality, and logarithmic
asymptotic all follow as written.

The added distinction between scalar tripling at all offsets and the
diagonal tripling instances realized by the tensor maps is correct. The
off-diagonal theorem needs the larger scalar axiom family; the diagonal
construction does not assert tensor maps for the unused instances.

## Occupation flows and their uniform charges

### State interval and probabilities

The affine formula at state zero is correct:

\[
F(r,r-1)=s_{r-1}(3r-2)/2=3(r-1)s_r/2.
\]

For every interior state, `h=min(x,n-x)` is a positive integer. The
children form an arithmetic progression with mean `x`, so
`q_(x,y)=f(y)/(d f(x))` is a positive rational probability distribution.
The filtration index `(x+h-y)/2` is integral and lies between zero and
`h`. The map's condition `b>=h+1` follows from `r>=2` and `h<=x`.
The child columns stay between `r-1` and `4r-1`.

### Absorption and the square-root drift

For the uniform child walk, the trapezoidal inequality for the concave
square root gives

\[
\sum_{k=0}^{x}\sqrt{k}
\le \frac23x^{3/2}+\frac12\sqrt{x}.
\]

After division by `x+1` and multiplication by `sqrt(2)`, this is at most
`(2 sqrt(2)/3) sqrt(x)`. Jensen's inequality bounds the other square-root
term, proving the stated drift on the left half of the interval;
reflection proves it on the right half.

Stopping at `tau` truncated by a finite time uses only bounded finite sums.
The nonnegative potential then bounds the expected sum of `sqrt(h)` before
absorption. Monotone convergence proves finite expected absorption because
`sqrt(h)>=1` on the interior. There is no assumption of absorption hidden
in this argument. The inequality `log(1+h)<=sqrt(h)` has the stated
derivative proof and bounds the auxiliary charge by the same estimate.

### Harmonic transform and resets

The path likelihood ratio under the harmonic probabilities telescopes to
`f(x_t)/f(i)`, including endpoint paths. For an interior starting state
`i>=1`, this ratio is at most `f(n)/f(1)=3`. Thus both excursion charges
are at most `3 sqrt(i)/gamma`.

The bounded stopped martingale gives uniform exit probability `i/n` at
the right endpoint. Multiplication by the endpoint likelihood ratio gives

\[
p_i=\frac{i f(n)}{n f(i)},\qquad
p_1=\frac1r,\qquad
p_2=\frac{2(3r-1)}{r(3r+1)}.
\]

Renewal after each reset yields total charge
`C_i+p_i C_1/(1-p_1)` and reset expectation `p_i/(1-p_1)`.
These prove both displayed reset formulas. The constants are correct:

\[
\frac6\gamma=54+36\sqrt2<105,
\qquad
\frac{3(\sqrt2+2)}\gamma=90+63\sqrt2<180.
\]

Both the number of interior visits and the logarithmic auxiliary charge
obey these row bounds. The reset occupations are at most two. Other
initial states also have finite expectation, including the reset state.
Consequently the transient matrix has a finite fundamental matrix and the
rational linear system is nonsingular. Exact Gaussian elimination gives
rational occupations. The full row identity follows by summing expected
successive state differences.

These arguments accommodate unreachable states. They do not require every
occupation to be positive.

## Conserved rounding, signed ledger, and entropy

### Circulation rounding

The imbalance of the floor vector has the stated sign: the fractional
parts have outgoing minus incoming balance equal to `b_v`. Source edges
at vertices with positive `b_v` and sink edges at vertices with negative
`b_v` therefore make those fractional parts a feasible flow. An integral
maximum flow of the same value exists by the given augmenting-path and
cut argument.

Loops have zero incidence and can stay at their floors. Integral-target
edges remain fixed. Treating original edges and residual reverse arcs as
distinct preserves the argument for parallel and opposing edges. Removing
the fixed return edge of value `K` leaves precisely the required signed
row balance. Each edge error is strictly less than one, each action error
is strictly less than its number of children, and every zero target stays
zero.

### Signed tensor ledger

The final row injects at column `a`, while each lower row injects at column
`r+1`. Alternating signs identify its positive boundary with the preceding
row's negative boundary under the actual input-swap isomorphism. The only
residual symbols are `K[+;a,a]` and `-K[MM_2]`.

Both uncollected totals equal `U+T`. Since the residual symbols are
distinct, the sum of common multiplicities is `U+T-K`. The boundary
`MM_2` has no source occurrences and therefore no catalyst multiplicity,
as used in the rank formula in `extraction.tex`.

### Uniform relative-entropy loss

The probability lower bound is valid on both halves of a row. Comparing
the smallest-child ratio with its continuous midpoint value gives

\[
q_y\ge\frac{r-1}{(2r-1)d}\ge\frac1{3d}.
\]

For an active action write `V=K lambda` and `w=sum n_y`. The edge errors
give `n_y<Vq_y+1` and `V<w+d`. Thus every positive coordinate satisfies

\[
\frac{p_y}{q_y}<1+\frac{4d}{w},
\qquad
wD(p\Vert q)\le w\log(1+4d/w)\le4d.
\]

The only divisor is the positive integer `w`. There is no lower bound on
`lambda` hidden in the estimate. Zero occupations have all-zero counts;
inactive actions have zero contribution. The proof of nonnegativity of
relative entropy remains valid when `p` has zero coordinates.

Summing the coordinate count gives exactly

\[
J_a=\sum_{r=2}^{a}
\left(\left\lfloor\frac{9r^2}{4}\right\rfloor+3r-1\right)
=\frac{12a^3+42a^2+12a-65+(-1)^a}{16}.
\]

In particular, `J_2=14`; the closed expression has the correct parity
term and lower endpoint. Consequently the loss is at most `4J_a` for
every positive integer `K`.

The local potential identity has the correct signs. Applying `log F` to
the rounded ledger proves `G=K log F(a,a)-L`. The reset identity is tight
for every integer reset count, so rounding the resets causes no separate
entropy error.

The total and per-action charge bounds follow independently from the two
occupation bounds. In particular, the individual bound
`w_i log d_i <=180K+2a log(2a)` uses a single row's charge. It does not
mistakenly import the larger total bound of order `aK`.

## Finite types and extraction-cost interfaces

For active actions, the multinomial support consists only of children
with positive counts; a one-child action has entropy and sector logarithm
zero. The auxiliary dimension remains the full `d_i`, so unused children
are not credited with an unwarranted source saving.

The partial-middle reset count uses the actual mode
`floor((Nz+1)/3)`. Its coefficient lies between `3^(Nz)/(Nz+1)` and
`3^(Nz)`, including `Nz=1` and the tied-mode cases. It imposes no
divisibility condition on `z`.

These bounds give

\[
NG-\mathcal T_N\le\log(v/u)\le NG.
\]

The direct-sum counts, interpolation degree, and rank charges use three
orientations consistently:

\[
S=\prod_i(2M_i-1)^3,
\quad H=\left(\prod_iM_i\right)^3,
\quad D=3\sum_i(M_i-1)^2.
\]

The finite bounds follow from `M_i<=exp(NH_i)`:

\[
0\le\log(S/H)<3I\log2,
\quad
\log E\le\log(3kI+1)+2B_N,
\quad
\log\kappa_N\le3N(U+T-K)\log(5a).
\]

All candidate rank bases are below `5a`. The quotient of the displayed
relative counts gives exactly the stated pooled-exponent formula after
division by `kj`. The optional fixed-batch ceiling term appears only in
`Phi`, not in that formula. The upper bound on contraction and the
nonnegative charges imply `p>=tau_a>9/4` whenever `B>A`.

## Explicit parameter family and constants

For `a>=2^16`, `t=log a`, and `ell=ceil(log_2 a)`, the elementary
estimates `t>8`, `ell>=t/log 2`, `ell<=a`, and `log K<=5t` hold.
The candidate bounds `J_a<=2a^3` and `I<=2a^2` are valid.

The type and rounding losses satisfy

\[
\frac{4J_a+\mathcal T_1}{K}
\le\frac{41/2+(45/4)t}{\ell^2}
<\frac{41}{4t^2}+\frac{45}{8t}
\le\frac{221}{256}.
\]

The coefficient `41/2` is `8+12+1/2`, and `45/4` is `10+5/4`, from
the rounding loss, action type loss, and reset type loss respectively.
The elementary profile lower bound loses at most `1/9`. Since
`1/9+221/256<1`, the contraction is strictly larger than
`K((4/3)t-1)>0`.

The numerator bounds also check:

- The normalized copy charge is at most one.
- The per-action entropy bound gives `log E/K<=361`. In particular,
  `log(6a^2+1)+4a log(2a)<=5a^2` is valid for `a>=2`.
- The catalyst count is less than `184aK`, so its normalized amortized
  charge is less than `552(log(5a))/ell<483`.
- The main rank charge is less than `3t+3`. The sum is below `3t+850`,
  even with the optional fixed-batch ceiling allowance.

Consequently

\[
p<\frac{3t+850}{(4/3)t-1}<\frac94+\frac{900}{t}.
\]

The lower bound `p>9/4` proves convergence to the endpoint, rather than
only an upper-limit assertion. The source calculation gives

\[
\log A\le a^5\ell^3
\left(180+\frac{2\log(2a)}{a\ell^2}\right)
\le181a^5\ell^3.
\]

Finally, `ell=max(16,ceil(1800/eps))` and `a=2^ell` imply
`900/log a<1800/ell<=eps`. This is an entirely integer and rational
parameter-selection rule. The bounds concern the relative source side,
as the text states; they do not bound the rational seed side after
coefficient descent or the time needed to expand coefficients.

## New finite examples and exact-certificate benchmark

The new elementary factorial enclosure follows from the trapezoidal upper
bound and the midpoint-integral lower bound for `log x`. Its constant
`c_0=(1+log 2)/2` is correct. Subtracting factorial enclosures gives the
displayed finite-multinomial interval with constants `c_0-s` and
`1-sc_0`. The intersection with the mode bounds is legitimate.

The table's saved numerical values were not recomputed. Their described
use is appropriate: a sufficient upper bound for `Phi` also bounds the
pooled exponent, while a source digit count makes no claim about the final
rational seed or measured performance.

With identical underlying types, replacing sixfold balancing at power
`k` by threefold balancing at power `2k` preserves the scalar counts:
source and target dimensions, catalyst rank bounds, and copy multiplicities
are squared between the two balancing choices, while the interpolation
degree is doubled. The interpolation count is consequently the same.
The manuscript correctly avoids claiming that threefold balancing alone
halves the exponent.

The exact binary certificate's telescoping, entropy identity, denominator
gcd computation, divisibility relations, and exponential lower bound agree
with the independently reviewed v1 arguments. Its new local notation and
scope separate these valid benchmark statements from the rounded
construction's polynomial bound on `log A`.
