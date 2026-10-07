# Explicit finite separator constructions

Date: 2026-10-06. Mathematical input: the supplied
`upstream/build/paper.tex`, Proposition 3.1 and its interpolation lemma.
This note contains new local derivations, not a literature review. Novelty
against the literature has not been established.

The finite separator can be made smaller and exact two-power separation can
use substantially fewer evaluations than a general polynomial interpolation
bound. These are explicit tensor reductions. They do **not** supply a matrix
multiplication rank decomposition or a practical algorithm with exponent 2.25.
The spectral proof's missing finite matrix multiplication seed remains missing.

## A smaller separator with an adjustable auxiliary dimension

Let

\[
A=\sum_{h=0}^{M-1} A_h,\qquad A_h\in X\otimes Y_h\otimes Z_h,
\]

with disjoint matched sectors on the last two legs. Fix integers \(K,c\ge1\)
and set \(L=K+c(M-1)\). In \(L\) independent source copies, substitute

\[
\begin{aligned}
x_a^{(r)}&\mapsto\sum_{g=0}^{M-1}\zeta^{rcg}X_{a,g},\\
y_{h,b}^{(r)}&\mapsto\sum_{u=0}^{K-1}\zeta^{r(u-ch)}Y_{h,b,u},\\
z_{h,d}^{(r)}&\mapsto L^{-1}\sum_{v=0}^{K-1}\zeta^{-rv}Z_{h,d,v},
\end{aligned}
\]

where \(\zeta\) is a primitive \(L\)-th root of unity. The Fourier sum
retains exactly the terms satisfying

\[
u-v+c(g-h)=0.
\]

There is no modular alias: the absolute value of the left side is at most
\(K-1+c(M-1)=L-1\). Give the three variables the respective weights

\[
cg^2,\qquad 2hu-ch^2,\qquad -2hv.
\]

Every surviving term has total weight \(c(g-h)^2\). Weight zero means
\(g=h\) and \(u=v\). Hence

\[
A^{\oplus L}\rightsquigarrow
D:=\bigoplus_{h=0}^{M-1}(A_h\otimes B_X(K)).
\]

All mismatches \(d=|g-h|\) lie in

\[
0\le d\le d_*:=\min(M-1,\lfloor(K-1)/c\rfloor).
\]

The transformed tensor therefore has the sparse form
\(F(\varepsilon)=\sum_{d=0}^{d_*}\varepsilon^{cd^2}G_d\), with
\(G_0=D\). Individual variable weights may be negative, but every surviving
term has nonnegative weight. Evaluations are always at nonzero parameters.

For \(K=M,c=1\), the source has \(2M-1\) copies instead of the paper's
\(5M\). For the paper's original slope \(c=2,K=M\), a sufficient source
count is \(3M-2\), and the maximum mismatch is only
\(\lfloor(M-1)/2\rfloor\). The paper's larger stated costs are valid upper
bounds; these refinements do not identify an error in them.

## Sparse exact interpolation

For any finite exponent support \(E\subset\mathbb Z_{\ge0}\) containing
zero, form

\[
Q(z)=\prod_{s\in E\setminus\{0\}}\frac{z-2^s}{1-2^s}
     =\sum_{j=0}^{|E|-1}\alpha_jz^j.
\]

Then \(\sum_j\alpha_jF(2^j)=G_0\), because \(Q(1)=1\) and
\(Q(2^s)=0\) for every positive supported exponent. This gives a rational,
fully specified exactification using \(|E|\) evaluations. At one power,
\(|E|=d_*+1\), rather than the degree bound \(cd_*^2+1\).

The rational coefficients can require many bits, while the evaluations at
\(2^j\) can have enormous magnitudes and suffer cancellation. Large coefficient
magnitudes are not required for this problem. There is a different exact
projection using parameters of modulus one. If \(q>d_*\)
is prime and does not divide \(c\), averaging \(F\) over the \(q\)-th roots
of unity kills every positive exponent \(cd^2\). All phases have modulus one,
and the averaging coefficient is \(1/q\). This observation does not prove
numerical stability of a complete recursive algorithm; summation costs,
cancellation, and linear-map norms still need analysis.

Neither exactification creates a useful one-step copy saving by itself.
Indeed,

\[
L(d_*+1)\ge MK.
\]

If \(d_*=M-1\), this follows from \(L\ge K\). Otherwise
\(d_*+1=\lceil K/c\rceil\), so
\(c(d_*+1)\ge K\) and
\(L(d_*+1)\ge K(d_*+1)+K(M-1)\ge MK\).
There is already a direct restriction \(A^{\oplus MK}\ge D\): use one
source copy for each pair \((h,u)\), delete other sectors, and identify its
first-leg variables with the corresponding block. This comparison concerns
copy costs of these particular constructions, not a lower bound on arbitrary
exact algorithms or tensor rank.

## Two tensor powers admit a cheaper exact projection

Choose a prime \(q>d_*\) such that \(q\equiv3\pmod4\) and \(q\nmid c\).
Let \(\eta\) be a primitive \(q\)-th root of unity. Then

\[
\frac1q\sum_{r=0}^{q-1}F(\eta^r)^{\otimes2}=D^{\otimes2}.
\]

To prove the identity, a term indexed by mismatches \(d_1,d_2\) has exponent
\(c(d_1^2+d_2^2)\). A nonzero coefficient survives the average only if
\(d_1^2+d_2^2\equiv0\pmod q\). If \(d_2\ne0\pmod q\), this would make
\(-1\) a square modulo \(q\), impossible for \(q\equiv3\pmod4\).
Thus both mismatches are zero modulo \(q\), and their bounds make them
exactly zero. Tensoring the source restrictions and summing yields

\[
A^{\oplus L}\otimes A^{\oplus L}\text{ in }q\text{ copies}
\ \ge\ D^{\otimes2},\qquad
R(D^{\otimes2})\le qL^2R(A)^2.
\]

These are scalar-copy costs, not operation counts of a matrix algorithm.
For \(K=M,c=1\), some exact values are:

| \(M\) | \(L\) | \(q\) | Copies of \(A^{\otimes2}\): \(qL^2\) | Direct copying: \(M^4\) |
|---:|---:|---:|---:|---:|
| 2 | 3 | 3 | 27 | 16 |
| 4 | 7 | 7 | 343 | 256 |
| 8 | 15 | 11 | 2,475 | 4,096 |
| 16 | 31 | 19 | 18,259 | 65,536 |
| 32 | 63 | 43 | 170,667 | 1,048,576 |

For \(M=8\), degree interpolation in the effective parameter would use up
to \(2(8-1)^2+1=99\) evaluations; this projection uses 11. A prime merely
larger than \(d_*\) is insufficient: with \(q=5,d_*=4\), the mismatches
\((3,4)\) satisfy \(3^2+4^2\equiv0\pmod5\) and contaminate the output.

For a general power \(j\), the effective exponent support consists of sums
of \(j\) squares from \(\{0^2,\ldots,d_*^2\}\). It has size at most
\(jd_*^2+1\). One can always average over any order
\(q>jd_*^2\) coprime to \(c\), giving the exact finite bound

\[
R(D^{\otimes j})\le qL^jR(A)^j.
\]

With a fixed separator, \(q\) grows at most linearly in \(j\), so its
\(j\)-th root tends to one. This explains the interpolation limit
constructively. It does not specify the separate tensor power, parameters,
or restriction that extracts a low-rank square matrix multiplication tensor.

## What remains nonconstructive in the supplied exponent argument

The supplied proof bounds all characters, invokes a detecting-character
existence statement, and uses an infimum over exact ranks to assert that for
each \(\delta>0\) some \(u,r\) and rank decomposition satisfy
\(r<u^{9/4+\delta}\). It does not output \(u,r\), their bounds, a decomposition,
or its linear-map cost. Making the finite separator explicit does not fill
those gaps automatically. The stated asymptotic conclusion also permits an
arbitrarily small positive exponent loss; it does not assert a single fixed
recursion with exponent at most exactly \(9/4\).

Conditional on a valid existence proof, an exhaustive symbolic search over
algebraic coefficient decompositions and matrix sizes could eventually find
a seed for any positive exponent allowance. That is a computability route,
not a practical construction: the proof gives no useful stopping bound, and
the rank equations have \(3ru^2\) scalar unknowns and \(u^6\) coefficient
constraints before normalization. Neither finite exact interpolation nor
root-of-unity projection supplies the missing solution to those equations.

The useful next artifact is an explicit matrix multiplication seed with
verified coefficient identities and acceptable transform costs. The present
construction is instead a smaller, exact, testable reduction that could be
used as a component of a future seed construction.

## Reproduction and scope of checks

`experiments/finite_constructions.py` uses integer arithmetic, rational
arithmetic, and exact prime-field roots of unity. It verifies Fourier
cancellation, absence of modular aliases, the square-weight identity, target
support, and constant extraction for one, two, and three tensor powers.
Internal coefficients of arbitrary \(A_h\) factor out of every check.
The mathematical proofs above establish the general identities; the finite
experiments check implementation and realistic boundary cases.

Run:

```sh
python experiments/finite_constructions.py --max-blocks 8
python -m pytest tests/test_finite_constructions.py
```

The script reports 576 checked configurations for the first command, plus
rational sparse-interpolation checks and the displayed two-power costs.
The captured output is in
[results/finite-constructions.json](../results/finite-constructions.json).
No multiplication exponent is measured or claimed by this experiment.
