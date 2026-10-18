# Rational interpolation and effective coefficient bounds

Work log, 2026-10-17. This note audits a direct way to remove the algebraic coefficient field from the finite construction. It also supplies coefficient-height estimates that can be combined with an explicit operation count for the construction. Status: incorporated into Lemma 9.1 and Section 9.1 of the paper. The paper interpolates convolutions at the nodes `1,...,r+b-1`; this note sometimes uses `0,...,q-1`, which works equally well. `H=4M-3` here is the separator copy count `L^Q_i` there.

## Finding

All three uses of roots of unity can be replaced by rational interpolation. For the separator this changes its source-copy count from `2M-1` to `4M-3`. Its target, parameter degree, and sector multiplicity stay the same. The additional copy overhead fits inside the existing quantitative proof's constants, including its bound `900/log(a)`.

This route is simpler than reconstructing an algebraic witness by quantifier elimination and subsequently applying rational descent. It also avoids needing a general bounded-height theorem for rational points.

## 1. A rational separator

Let `Q=2M-2` and `H=2Q+1=4M-3`. For `s=1,...,H`, define the ordinary Lagrange basis polynomial

\[
 \ell_s(z)=\prod_{1\le j\le H,\ j\ne s}\frac{z-j}{s-j},
 \qquad
 w_s=s^Q[z^Q]\ell_s(z).
\]

For every integer `delta` between `-Q` and `Q`, Lagrange interpolation applied to the polynomial `z^(Q+delta)` gives

\[
 \sum_{s=1}^{H}w_s s^\delta
 =[z^Q]z^{Q+\delta}=\mathbf1_{\{\delta=0\}}.
\]

These are finite rational identities; they also cover `M=1`, when `Q=0`, `H=1`, and `w_1=1`.

In source copy `s`, use the following substitutions in the notation of the manuscript's separator:

\[
 \begin{aligned}
 x_\alpha&\longmapsto\sum_{g'=0}^{M-1}
       s^{g'}t^{g'^2}X_{\alpha,g'},\\
 y_{g,\beta}&\longmapsto\sum_{e=0}^{M-1}
       s^{e-g}t^{2ge-g^2}Y_{g,\beta,e},\\
 z_{g,\gamma}&\longmapsto w_s\sum_{e'=0}^{M-1}
       s^{-e'}t^{-2ge'}Z_{g,\gamma,e'}.
 \end{aligned}
\]

Sum the images of the `H` source copies. The coefficient of a term with labels `(g,g',e,e')` contains

\[
 \sum_{s=1}^H w_s s^{g'+e-g-e'}.
\]

The exponent is in `[-Q,Q]`. Thus exactly the terms satisfying `g'+e-g-e'=0` survive. On these terms the exponent of `t` is

\[
 g'^2+2g(e-e')-g^2=(g'-g)^2.
\]

Consequently the result is the same separated polynomial as in the Fourier proof. In particular,

\[
 (4M-3)T\ \unrhd\ \bigoplus_{g=0}^{M-1}T_gB_X(M)
\]

is a degeneration defined over the rationals, of degree at most `(M-1)^2`. Negative powers in individual map entries cause no problem: all evaluations below use nonzero parameters, and the summed image has only the nonnegative square exponents just proved.

**Effect on the finite construction.** Replace `L_i=2M_i-1` by `L_i=4M_i-3`; leave `M_i`, `D`, `E`, `A_1`, `B_1`, and the catalyst counts unchanged. The copy estimate becomes

\[
 0\le\log(L/M^3)<3I\log4.
\]

At the quantitative parameters `K=a^3 ceil(log_2 a)`, `I<=2a^2`, and `a>=2^64`,

\[
 \frac{3I\log4}{K}<\frac{12}{a\lceil\log_2a\rceil}<1.
\]

The existing quantitative proof had reserved an upper bound of `1` for precisely this normalized copy term. Every other bound used there is unchanged. Therefore the same `900/log(a)` pooled-exponent allowance and the same source-side bound hold for this rational variant. In fact the copy-count increase is always less than a factor `2` per oriented separator.

## 2. Rational exactification with integer weights

Let `P(t)` be a polynomial with coefficients in any rational vector space, of degree at most `E-1`. Evaluating its Lagrange formula at zero gives

\[
 P(0)=\sum_{s=1}^{E}(-1)^{s-1}\binom Es P(s).
\]

Indeed the Lagrange weight at zero for node `s` is

\[
 \prod_{1\le j\le E,\ j\ne s}\frac{-j}{s-j}
 =(-1)^{s-1}\binom Es.
\]

Apply this to the polynomial produced by the `k`th tensor power of the catalytic degeneration, with `E=kD+1`. Each evaluation uses the original maps at a positive integer `s`, so all Laurent entries are defined. Absorb the displayed integer weight into one leg of copy `s`. This proves the exactification restriction with exactly the same `E` source copies, entirely over the rationals. The interpolation weights have at most `E+1` bits because `binom(E,s)<=2^E`.

The same argument permits the global parameter to be evaluated first in the primitive separator maps, then the map compositions and tensor products to be formed over the rationals. There is no need to store symbolic Laurent polynomials of the full construction.

## 3. Rational convolution decompositions

For `C(r,b)`, put `q=r+b-1`. Evaluate the two input polynomials at `q` distinct rational nodes, for example `0,...,q-1`; interpolate their product, whose degree is at most `q-1`. This is a rational rank-`q` decomposition. Tensoring the three orientations gives the existing rational rank bound `(r+b-1)^3` for each symmetrized convolution tensor. Replacing Fourier evaluation in the catalyst supply therefore changes neither its stated rank bound nor the rank bound of the target convolution tensor.

All other primitive maps in the manuscript are rational already: the determinant-basis maps are integral, and type restrictions, reindexings, symmetry maps, and monomial projections have coefficients zero or one.

## 4. Explicit primitive coefficient heights

For a reduced rational number `u/v`, with `v>0`, define its bit height as

\[
 h(u/v)=\max\{1,\lceil\log_2(|u|+1)\rceil,
                    \lceil\log_2(v+1)\rceil\}.
\]

The following estimates concern individual primitive maps. A tensor power or matrix composition can increase height; Section 5 accounts for that increase.

### Separator interpolation weights

The denominator of `ell_s` is `(s-1)! (-1)^(H-s) (H-s)!`. Its bit length is at most `1+H log_2(H+1)`. Every coefficient of its numerator has absolute value at most

\[
 \prod_{j\ne s}(1+j)\le(H+1)^{H-1}.
\]

Multiplication by `s^Q` therefore gives

\[
 h(w_s)\le2+2H\lceil\log_2(H+1)\rceil.
\]

This bound does not assume cancellation and so remains valid after reducing the fraction.

### Determinant bases and their inverses

In every row of the construction, `h<=floor(3a/2)<2a`, and the largest basis matrix has dimension

\[
 n=(r+b-1)(h+1)\le10a^2.
\]

Each entry of a determinant-basis matrix is zero or a signed binomial coefficient with top index at most `h`, and hence has absolute value at most `2^(2a)`. Both the matrix and its inverse are integral, as proved in the manuscript. The determinant is therefore `+1` or `-1`. By the cofactor formula and Leibniz's determinant expansion, each inverse entry has absolute value at most

\[
 (n-1)!\,2^{2a(n-1)}.
\]

Since `log_2(10a^2)<=3a` for every integer `a>=2`, its bit height is at most `51a^3`; the convenient common bound `100a^3` is safe. This estimate is independent of the dimensions of later tensor powers.

### Convolution interpolation

At nodes `0,...,q-1`, Lagrange output-polynomial coefficients are ratios with numerator coefficients bounded by `(q+1)^(q-1)` and denominator bounded by `q!`. Input evaluation entries are bounded by `q^(q-1)`. Thus height at most `2+q ceil(log_2(q+1))` suffices. Here `q<=5a`, so `200a^3` is a conservative common bound. This estimate also follows from the Vandermonde adjugate formula without assuming that its inverse is integral.

### Parameter evaluations

Set

\[
 U=\max\{2,10a^2,E,4\max_i M_i\}.
\]

At a separator copy node `s<=4M_i-3` and an exactification node `t<=E`, every primitive phase exponent has absolute value at most `2M_i`, and every primitive parameter exponent has absolute value at most `2M_i^2`. Hence an evaluated monomial has height at most

\[
 2+2M_i\lceil\log_2U\rceil+
       2M_i^2\lceil\log_2U\rceil.
\]

Combining this with the weight bounds above, the binomial exactification weights, and the determinant and convolution bounds, a single uniform bound for the rational scalar constants appearing in the evaluated primitive maps is

\[
 h_0=100U^4.
\]

Permutations and projections also satisfy this bound. Multiplying several primitive constants in a composed map should be counted as arithmetic operations, rather than silently included in this primitive-height assertion.

## 5. From a rational operation count to a bit-time bound

Suppose a specified implementation uses at most `S` scalar operations `+,-,*,/` on rationals, starts with constants of bit height at most `h_0`, and never divides by zero. Write every intermediate result as a reduced fraction. For either addition/subtraction or multiplication/division, the next height is at most twice the previous maximum height plus one. Induction gives the uniform intermediate and output bound

\[
 h_{\mathrm{out}}\le2^S(h_0+1).
\]

Using ordinary integer multiplication and the Euclidean algorithm, a rational operation on arguments of height `h` takes `O((h+1)^3)` bit operations. Consequently a rigorous coarse preprocessing bound is

\[
 O\!\left((S+1)\,2^{3S}(h_0+1)^3\right),
\]

plus the time to write any output entries which were represented by references rather than by arithmetic gates. A dense rational bilinear decomposition of side `d` and rank `R` has `3Rd^2` coefficient entries. Its encoding length is therefore at most

\[
 O\!\left(3Rd^2\bigl(1+2^S(h_0+1)\bigr)\right).
\]

These bounds deliberately ignore cancellations. They turn any proved scalar-operation budget for the fully specified rational construction and its finite unrolling into coefficient-size, output-size, and bit-preprocessing bounds. They do not require a coefficient-height estimate for the enormous composed matrices themselves.

The input allowance also has an encoding length: if its reduced numerator and denominator have maximum bit length `L`, use `max(h_0,L)` for the initial-height bound, or charge the computation of the integer index separately in polynomial time in `L`. A bit-time bound in the numerical value of `1/eps` alone cannot pay for reading arbitrarily long rational inputs.

The operation budget must include constructing the row probabilities and occupations, balanced rounding, factorial and sector counts, primitive interpolation coefficients, map assembly, and finite recursion unrolling. It must also state whether the requested output is a rational arithmetic circuit or a dense coefficient list. A circuit-size bound alone is not a bound on the dense list unless its expansion is counted.

## 6. Why real quantifier elimination is unnecessary here

Real quantifier elimination can reconstruct algebraic witnesses for the polynomial equations defining a complex restriction: split each unknown into its real and imaginary parts. It does not directly reconstruct a rational point, even when the equations have rational coefficients. Rational solvability must not be substituted for real solvability. One can apply the manuscript's field-descent argument to an algebraic witness, at a rank cost depending on the witness-field degree, but the direct rational interpolation above avoids that cost and the extra algebraic-geometry machinery.

For the separate algebraic-witness route, the applicable standard reference is Basu, Pollack, and Roy, *Algorithms in Real Algebraic Geometry*, second edition (2006), Chapter 13; the sampling theorem has singly exponential degree and complexity estimates with absolute constants. Basu's [author-hosted survey](https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf), Theorem 2.4, separately states the doubly exponential CAD bound. Neither fact alone should be quoted as an explicit numerical rational coefficient-height bound.

## Validation record

The identities in Sections 1 and 2 are exact polynomial interpolation identities, so their proofs cover all positive `M` and `E`. An independent executable check in `experiments/rational_interpolation_audit.py` checks the separator moments for `M=1,...,9`, all surviving separator-label exponents for `M=1,...,6`, and exactification moments for `E=1,...,20`, using Python's exact rational arithmetic. It also checks the claimed separator-weight height bound.
