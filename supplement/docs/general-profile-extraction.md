# Finite extraction for a general profile index

Date: 2026-10-06. Original mathematical derivation from the supplied tensor
maps and the [exact extremal profile](profile-analysis.md). No literature
research was performed for this derivation.

The finite extraction extends beyond index 2. A positive rational certificate
can be written down for every finite index, converted into integer tensor
types, and used in the same counted interpolation and batched recursion.
Its limiting exponent is

\[
\tau_a=\frac{3\log(2a-1)}{\log F(a,a)}\longrightarrow\frac94.
\]

This removes the unspecified character and finite dual from this particular
construction. It does **not** provide a materialized rank certificate or a
practical algorithm. Its exact type normalization grows at least
exponentially with the profile index, before interpolation or catalyst reuse.
At index 63, that normalization alone is a 61-digit integer. The result is a
finite tensor recipe and a candidate constructive derivation of the
manuscript's claimed asymptotic bound, with its costs exposed; the composed
coefficient identities have not been expanded into an independently checked
matrix multiplication seed.

The statements below concern a separate fixed arithmetic algorithm for each
positive exponent allowance. No uniform \(n^{9/4+o(1)}\) running-time claim,
including construction time, is made. Attaching practical leaves to these
astronomical recursions would not make them practical algorithms with an
exponent near 2.25.

## A finite rational certificate

Let

\[
s_m=\prod_{h=1}^{m-1}\left(1+\frac1{3h}\right),\qquad
F(m,n)=s_{\min(m,n)}\left(\max(m,n)+\frac{\min(m,n)-1}{2}\right).
\]

The [profile proof](profile-analysis.md) establishes that \(F\) is feasible
and is the pointwise least scalar profile. Only its affine rows are needed
here. Define normalized logarithms

\[
y_{r,b}=\log(P(r,b)/F(r,b)).
\]

For every row \(2\le r\le a\), use columns \(r\le b\le4r-2\). At these
columns the concavity inequality is tight at \(F\), including \(b=r\).
Choose fixed probabilities

\[
q^\pm_{r,b}=\frac{2b+r-1\pm2}{2(2b+r-1)}.
\]

The entropy form of concavity then reads

\[
y_{r,b}-q^-_{r,b}y_{r,b-1}-q^+_{r,b}y_{r,b+1}\ge0.
\tag{1}
\]

Tripling at \(h=r\) gives
\(y_{r,4r-1}-y_{r,r}\ge0\), since
\(F(r,4r-1)=3F(r,r)\).

Put \(L=4r-1\), \(D=3r-1\). In the final row \(r=a\), assign weights

\[
\lambda_{r,b}=\frac{2(2b+r-1)(L-b)}{3(r-1)D},\qquad
\mu_r=\frac1{r-1}.
\tag{2}
\]

The \(\lambda\)-weighted sum of (1), plus \(\mu_r\) times tripling,
is exactly
\(y_{r,r}-y_{r,r-1}\ge0\).

For each lower row \(2\le r<a\), use

\[
\lambda_{r,r}=\frac{2D}{3(r-1)},\qquad
\lambda_{r,b}=\frac{4(2b+r-1)(L-b)}{3(r-1)(3r+1)}\quad(b>r),
\]

\[
\mu_r=\frac{2D}{(r-1)(3r+1)}.
\tag{3}
\]

Its weighted sum is exactly
\(y_{r,r+1}-y_{r,r-1}\ge0\). These identities follow by collecting
coefficients: interior columns cancel, the terminal column cancels against
tripling, and the displayed endpoints remain. All weights are positive
rational numbers. Symmetry identifies
\(y_{r,r+1}=y_{r+1,r}\), so summing rows leaves

\[
y_{a,a}-y_{2,1}\ge0.
\]

Since \(P(2,1)=F(2,1)=2\), this is the desired bound
\(P(a,a)\ge F(a,a)\). No probability or multiplier depends on an
unknown tensor character.

## Integer types and the exact tensor ledger

Let \(K=K_a\) be the least common multiple of the denominators of all
\(\lambda q^+\), \(\lambda q^-\), and \(\mu/3\). For each concavity
relation define positive integers

\[
w=K\lambda,\qquad u=K\lambda q^+,\qquad d=K\lambda q^-,\qquad w=u+d.
\]

For each tripling relation put \(z=K\mu\), so \(3\mid z\). Write
\(U=\sum w\) and \(T=\sum z\). At an additional type scale \(N\),
concavity uses \(Nw\) input factors and counts \((Nu,Nd)\); tripling
uses \(Nz\) factors and counts \((Nz/3,Nz/3,Nz/3)\).

Define the balanced tensors

\[
Q_{r,b}=\bigotimes_{\pi\in S_3} C(r,b)^\pi.
\]

They satisfy \(Q_{r,b}\cong Q_{b,r}\),
\(R(Q_{r,b})\le(r+b-1)^6\), and \(Q_{1,2}\cong T_4\). The rational
certificate gives the integer resource residual

\[
\text{source factors}-\text{output factors}
=KQ_{a,a}-KQ_{1,2}.
\tag{4}
\]

Here (4) is a bookkeeping identity of formal exponent vectors, not an
additive tensor identity or a license to cancel tensor factors. Retain every
common factor in a catalyst
\(\mathcal C=\prod Q_{r,b}^{\otimes c_{r,b}}\), where \(c_{r,b}\) is the
minimum of that factor's source and output counts. It has
\(\sum c_{r,b}=U+T-K\) factors. At scale \(N\), the catalyst is
\(\mathcal C_N=\mathcal C^{\otimes N}\).

The small exact ledgers are:

| Profile index \(a\) | Integer scale \(K\) | Concavity factors \(U\) | Tripling factors \(T\) | Catalyst factors \(U+T-K\) |
|---:|---:|---:|---:|---:|
| 2 | 15 | 230 | 15 | 230 |
| 3 | 84 | 3,316 | 162 | 3,394 |
| 4 | 3,465 | 252,362 | 8,877 | 257,774 |

There are \(I_c=(3a^2+a-4)/2\) concavity relations and \(I_t=a-1\)
tripling relations, for a total \(I=3(a+2)(a-1)/2\).

As an independent arithmetic check, the fixed types obey

\[
2^{K-U}3^T\prod_{\text{concavity types}}
\frac{w^w}{u^u d^d}=F(a,a)^K.
\tag{5}
\]

The experiment checks this through exact prime valuations at indices 2, 3,
and 4; it does not evaluate approximate entropies to assert equality.

## The tensor maps for arbitrary first-input length

The extension of the determinant step must be checked for \(r>2\). Here is
that check. In degree \(e\), let \(s_i=u^{e-i}v^i s\) and
\(w_i=u^{e-i}v^i w\). Take quotient lifts
\(s_0,\ldots,s_e,w_e\), and kernel basis
\(w_i-s_{i+1}\), \(0\le i<e\). These are bases: the diagonal images of
the lifts form the output monomial basis, and the kernel vectors are
independent and span its kernel.

For \(C(r,b)\otimes B_X(2)\), the input degree is \(b-1\) and output
degree is \(r+b-2\). Multiplication by first-input monomial
\(u^{r-1-i}v^i\) shifts the index by \(i\). The diagonal blocks are
exactly \(C(r,b+1)\) and \(C(r,b-1)\). The only off-diagonal terms are

\[
x_i\,q_b\,k^*_{b-1+i},\qquad 0\le i<r-1,
\tag{6}
\]

where \(q_b\) is the last input quotient lift and \(k^*\) an output
kernel dual coordinate. There is no kernel-to-quotient term.

In \(Nw\) factors, project both the second and third legs onto words
with exactly \(Nd\) kernel labels. Every term in (6) increases the output
kernel count by one, while a diagonal term preserves it. Equal counts
therefore remove **every** off-diagonal term. The remaining tensor has
\(\binom{Nw}{Nu}\) matched sectors, each a copy of
\(C(r,b+1)^{\otimes Nu}C(r,b-1)^{\otimes Nd}\). Its first leg is still
shared. This is an exact coordinate restriction after the fixed basis change,
not a further degeneration with an omitted interpolation cost.

For tripling, use \(C(r,4r-1)\). Its second-leg sectors have lengths
\((r,2r-1,r)\), and its third-leg sectors have lengths
\((2r-1,r,2r-1)\), in the manuscript's order. A term with an outer
second-leg label must have the same outer third-leg label. Unmatched terms
therefore have a middle second-leg label and an outer third-leg label.
Retaining \(Nz/3\) middle labels on both legs removes all unmatched terms.
Retaining the full frequency vector \((Nz/3,Nz/3,Nz/3)\) leaves
\((Nz)!/(Nz/3)!^3\) matched sectors.

Both outer sectors are \(C(r,r)\). The middle sector is the same tensor
with its second and third legs exchanged and first-input indices reversed:
its monomials are
\(x_{r-1-i}y_{r+i+j}z_{2r-1+j}\), for \(0\le i,j<r\).
After full separation, each block can use its own leg isomorphisms.
Multiplying over all six permutations makes the exchanged factors telescope
exactly into \(Q_{r,r}^{\otimes Nz}\).

Thus the exact type restrictions used at index 2 work for every relation
above. The tests verify these basis changes and sector identifications for
several first-input lengths greater than 2. The formulas provide the general
argument; the finite tests are implementation checks.

## All finite copy and interpolation costs

Let the type-sector counts be

\[
M_i=\binom{Nw_i}{Nu_i}
\quad\text{or}\quad
M_i=\frac{(Nz_i)!}{(Nz_i/3)!^3},
\]

according to the relation. Define

\[
M=\prod_iM_i,\quad S=\prod_i(2M_i-1)^6,\quad H=M^6,
\quad D=6\sum_i(M_i-1)^2.
\]

Applying the [explicit separator](constructive-analysis.md) independently to
every relation and leg permutation gives

\[
S\,\mathcal C_N Q_{a,a}^{\otimes NK}T_u
\ \rightsquigarrow\ H\,\mathcal C_N T_v,
\tag{7}
\]

\[
u=2^{2NU},\qquad v=(2^{NK}M)^2.
\]

Both copy multiplicities remain present. Their ratio obeys
\(S/H<2^{6I}\), but no restriction is asserted by canceling them.
All separators can use a common parameter with degree at most \(D\).
No extra determinant or tripling degree is required, by the exact type
argument above.

Choose an integer tensor-power parameter \(k\). Averaging the \(k\)-th
power of (7) at \(E=kD+1\) roots of unity gives an exact restriction.
Only after this exactification, reuse the fixed catalyst
\(\mathcal C_N^{\otimes k}\) for \(j\) consecutive applications, as in
the [small-index derivation](small-profile-extraction.md).

Use the explicit rank bound

\[
\kappa_N=\prod_{r,b}(r+b-1)^{6Nc_{r,b}}
\]

to supply the source catalyst; restrict the nonzero output catalyst to a
scalar. The resulting exact relative scheme is

\[
R_{\rm calls}\,T_{u^{kj}}\ge m_{\rm outputs}\,T_{v^{kj}},
\tag{8}
\]

\[
R_{\rm calls}=\kappa_N^k E^j S^{kj}(2a-1)^{6NKkj},
\qquad m_{\rm outputs}=H^{kj}.
\]

The source tensor \(T_{u^{kj}}\) remains a recursive operation; no unknown
fast rank decomposition for it is assumed. The batched recursion computes
\(m_{\rm outputs}\) products at once and groups the
\(R_{\rm calls}\) resulting products into
\(\lceil R_{\rm calls}/m_{\rm outputs}\rceil\) recursive batches.
Its padded dimension contracts according to
\(n'\le(u/v)^{kj}n+u^{kj}\), with a fixed leaf threshold. This gives,
whenever the right side is above 2, the exponent upper expression

\[
\frac{6NK\log(2a-1)+\log(S/H)+\log(E)/k
+\log(\kappa_N)/j+\log2/(kj)}{\log(v/u)}.
\tag{9}
\]

The last term bounds the ceiling by
\(\lceil R_{\rm calls}/m_{\rm outputs}\rceil
\le2R_{\rm calls}/m_{\rm outputs}\). Equation (9) retains every source
copy, exactification cost, catalyst rank charge, and output-batching cost.

## The limit and what it does not imply

For fixed \(a\), equation (5) gives

\[
\frac1N\log(v/u)\longrightarrow2K\log F(a,a).
\]

This has a quantitative elementary version. The multinomial coefficient of
an exact type with \(s\) categories is at least its entropy exponential
divided by \((n+1)^{s-1}\). To see this, use the type frequencies as the
multinomial probabilities. That type has maximal probability, and there are
at most \((n+1)^{s-1}\) types. Comparing each factorial factor also verifies
maximality directly. Consequently,

\[
\log(v/u)\ge2NK\log F(a,a)-2\mathcal E_N,
\]

\[
\mathcal E_N=\sum_{\rm concavity}\log(Nw_i+1)
+2\sum_{\rm tripling}\log(Nz_i+1).
\tag{10}
\]

The loss is \(O_a(\log N)\), while the main term is linear in \(N\).
Also \(\log(S/H)<6I\log2\). Choose \(N\) sufficiently large first;
then choose \(k\) large enough to make \(\log(kD+1)/k\) small, and
choose \(j\) large enough to amortize \(\log\kappa_N\). Every choice can
be made by exact integer construction and certified rational logarithm
bounds. There is no unspecified spectral point or rank-minimization oracle
in this selection.

That selection procedure is a mathematical recipe, not an implemented
epsilon-to-algorithm compiler. Arbitrarily small exponent allowances would
require increasing the mantissa precision and series length in the rational
logarithm bounds. The current experiment uses fixed 80-bit mantissas and 40
series terms, emits finite cost reports only for indices 2, 3, and 4, and
does not generate the full composed tensor maps.

For each fixed index, (9) approaches
\(\tau_a=3\log(2a-1)/\log F(a,a)\). The product formula for \(F\) gives
\(\log F(a,a)=(4/3)\log a+O(1)\), so \(\tau_a\to9/4\).
At the level of the specified finite maps, this supplies a route to a fixed
\(O_\varepsilon(n^{9/4+\varepsilon})\) arithmetic algorithm for every
positive \(\varepsilon\). It does not give a single fixed recursion whose
exponent is exactly \(9/4\), a competitive finite-size algorithm, or a
uniform construction-time bound. The stored experiments verify counts and
small component maps, not the entire expanded family of coefficient identities.

The first limiting scalar values and a diagnostic finite cost are:

| \(a\) | Limit \(\tau_a\) | \(N=1\) upper expression after arbitrarily amortizing interpolation and catalyst costs |
|---:|---:|---:|
| 2 | 2.737468 | 13.298548 |
| 3 | 2.641126 | 4.100242 |
| 4 | 2.592310 | 2.646647 |

The last column includes the conservative copy bound \(6I\log2\), but
excludes the positive finite interpolation and catalyst charges. It is not
an implemented exponent. Even before those charges, the source matrix
dimensions at \(N=1\) are respectively
\(2^{460}\), \(2^{6632}\), and \(2^{504724}\).

## An obstruction intrinsic to this exact certificate

Clearing the particular rational types above already has a substantial cost.
Their minimal scale has the closed form

\[
K_a=\operatorname{lcm}\left(
\frac{3(a-1)(3a-1)}{\gcd(3a-1,4)},
\left\{\frac{3t(3t+4)}{\gcd(t,2)^2}:1\le t\le a-2\right\}
\right).
\tag{11}
\]

For completeness, in the final row set \(t=a-1\), \(D=3t+2\).
The common split-count denominator is \(3tD\). Its numerators include
\(D\) from \(\mu/3\) and
\((D+2h\pm2)(D-h)\). Their joint gcd with the denominator is
\(\gcd(D,4)\): modulo \(D\), these products are
\(-2h(h\pm1)\), and \(h=1\) supplies a multiple congruent to \(-4\).
For a lower row the common denominator is \(3t(3t+4)\); the relevant
numerators include \((3t+4)^2\) and \(2(3t+2)\). Their joint gcd is 1
for odd \(t\) and 4 for even \(t\), and every other numerator shares
exactly that required factor. This proves (11).

Each row denominator in (11) is either
\(3\operatorname{lcm}(t,3t+c)\) or half that number, with \(c=2\) or 4.
Therefore

\[
2K_a\text{ is divisible by }3\operatorname{lcm}(1,\ldots,a-1),
\qquad
K_a\text{ divides }3\operatorname{lcm}(1,\ldots,3a-1).
\]

In particular,

\[
K_a\ge\frac32\operatorname{lcm}(1,\ldots,a-1)
\ge\frac{3\,2^{a-2}}{a}.
\tag{12}
\]

For the last elementary bound, every binomial coefficient
\(\binom{n}{h}\) divides \(\operatorname{lcm}(1,\ldots,n)\): at each
prime power, its factorial valuation has at most one contribution, giving
valuation at most \(\lfloor\log_p n\rfloor\). At least one binomial
coefficient is \(2^n/(n+1)\) or larger. Set \(n=a-1\).

Since \(U\ge K_a\), the source dimension \(2^{2NU}\) is already
prohibitive as the profile index grows. At \(a=63\), the exact integer
\(K_a\) has 61 digits, before any type expansion, interpolation, or reuse.
The full-batch index-2 recipe also has an independent
[quantitative cost obstruction](extraction-cost-limits.md).

This is a lower bound on the integer types of this **specific exact tangent
certificate**, not on arbitrary matrix multiplication algorithms. Different
probabilities, tensor maps, cancellations, or rank decompositions might
behave differently. The calculation gives a concrete reason to seek such
changes instead of repeatedly tuning the enormous parameters of this recipe.

## Verification and remaining work

```sh
python -m experiments.general_profile_extraction
python -m pytest tests/test_general_profile_extraction.py
```

The narrow experiment checks rational telescoping through index 10, verifies
the minimal scale formula against the actual denominators, reproduces the
index-3 and index-4 integer ledgers and entropy identities, and checks general
determinant and tripling component maps. All 20 tests pass. Its numerical
reports use the same exact rational logarithm intervals as the small-index
experiment. No enormous final matrix dimension or rank decomposition is
expanded.

The [saved raw report](../results/general-profile-extraction.json) contains
the exact counts and interval endpoints.
An [independent review](general-profile-review.md) found no blocking objection
and additionally checked all 6,045 relations at index 63 with exact arithmetic.

There is no identified missing spectral or dual-existence step in these
formulas. Independent verification of the composed finite tensor maps,
generator complexity, numerical behavior, and a useful finite matrix regime
remain separate requirements. The practical target is still unmet.
