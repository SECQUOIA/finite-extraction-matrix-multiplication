**Matrix multiplication algorithms with exponent approaching 9/4**

This repository contains two **AI-produced research papers** and their
supporting materials. AI agents developed the mathematical arguments,
manuscripts, supporting calculations, and review records.

- [finite-extraction.pdf](finite-extraction.pdf): *A finite construction of
  matrix multiplication algorithms with exponent approaching 9/4*, version 5
  (18 October 2026). It turns the OpenAI preprint's existence proof into
  explicit algorithms.
- [shifted-chains.pdf](shifted-chains.pdf): *A singly exponential
  construction of matrix multiplication algorithms with exponent approaching
  9/4* (19 October 2026). A follow-up paper whose construction makes the
  sizes singly exponential in `1/epsilon` rather than doubly exponential.

## A finite construction (version 5)

OpenAI's preprint
[An Upper Bound of 9/4 for the Matrix Multiplication Exponent](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf)
announced the bound `omega <= 9/4`. Its proof ends with an existence argument
and does not specify an algorithm. This paper builds on the preprint's
convolution relations and shared-leg separator, and gives a self-contained
construction by explicit tensor maps. For each positive rational allowance
epsilon, a terminating procedure outputs an exact bilinear algorithm with
rational coefficients and exponent below `9/4 + epsilon`, so that two
`n x n` matrices can be multiplied with `O_epsilon(n^(9/4 + epsilon))`
arithmetic operations.

For every integer `a >= 2^64`, an explicit scheme computes several products
of `B x B` matrices from products of smaller `A x A` matrices. Its recursive
use has exponent below `9/4 + 900/log(a)`, and its source side satisfies
`log(A) <= 181 a^5 ceil(log2(a))^2`. Here `log` is the natural logarithm.
A rational variant of the construction gives the side of the final
algorithm by a formula, and bounds the bit lengths of its coefficients and
the bit cost of computing them. For any fixed rational algorithm, the paper
bounds the bit cost of exact integer multiplication and a precision that
suffices for a prescribed normwise error. Counting the preprocessing, one
algorithm multiplies `n x n` matrices in `n^(9/4+o(1))` steps for every `n`.
Within the construction, every scheme with exponent below 3 has source side
`A >= 12^18`, and the least source side for exponent at most `9/4 + epsilon`
is `exp(exp(Theta(1/epsilon)))`, so these sizes cannot be made small without
changing the construction. A Lean 4 formalization of a simpler rational
variant, included in the supplement, proves `omega <= 9/4` over every field
of characteristic zero, without explicit constants.
The paper does not give an algorithm with exponent exactly 9/4, an expanded
coefficient certificate, or a practical implementation. All its dimensions
and constants are astronomically large.

### Version 5

Version 5 (18 October 2026) makes these changes:

- **Related work.** The paper cites and positions the work that appeared
  after the OpenAI preprint:
  - Lü's polynomial separator;
  - Filmus's block-identity proof over every field, with Lean code;
  - the Lean proofs of Navot and Zuiddam over every field;
  - Navot's extension to associative rings;
  - Uznański's rectangular bounds;
  - later laser-method bounds.
- **Section 9.1.** The rational variant now uses Lü's separator, with
  `2M-1` rational copies and degree at most `M-1`. It therefore has
  exactly the counts of the main construction.
- **Remark 9.8.** A proof sketch that, for a suitable implementation, the
  `o(1)` in the uniform algorithm is `O(1/log log n)`.
- **Section 11.2, "Limits of the construction".** Proves the source-side
  lower bounds stated above. A computer-assisted remark adds `A >= 2^24`
  for arbitrary decompositions of the source and catalyst.
- **Section 11.3.** Describes the Lean formalization. Its 65 modules,
  build files and axiom check are in
  [supplement/formalization/](supplement/formalization/).

The paper has 79 pages. See the
[revision record](supplement/docs/manuscript-v5-revision.md).

### Version 4

Version 4 (17 October 2026) added Section 9, "Explicit bounds for a rational
seed": the rational variant, the explicit seed side, the cost of computing
the seed, bit complexity and sufficient precision for recursion with a fixed
seed, and one algorithm for all sizes. It had 71 pages. See the
[resolution record](supplement/docs/final-algorithm-bounds.md) and the
[second check](supplement/docs/final-algorithm-bounds-check.md).

### Version 3

Version 3 rewrote the paper for clarity. Its mathematics
is that of version 2. The fixes made in
version 3 concern citations, attribution to the OpenAI preprint, one
justification in the flows section, the statement of the rounding rule
behind the finite examples, and notation. The rewritten paper explains where
9/4 comes from, gives every symbol one meaning (Appendix D), and adds worked
examples and figures. It had 62 pages; version 2 had 35. The
[revision record](supplement/docs/manuscript-v3-revision.md) gives the
details.

## A singly exponential construction

The follow-up paper answers the second open question of version 5 (v5
below), which asks for a construction in which `log(A)` is bounded by a
polynomial in `1/epsilon`.
The source side `A` alone is not a robust measure, because composition with
the classical algorithm reduces it to 1. The robust measures are the numbers
`r` and `m` of source and target matrix products and the side `n_0` of the
seed, all doubly exponential in `1/epsilon` within v5's construction. Here
all three are singly exponential.

The main ingredient is a *shifted sum* of polynomials. It splits a
polynomial multiplication tensor times a dot product into equal kernel parts
and one quotient part, which a reset (the partition behind the OpenAI
preprint's shifted tripling) turns into shorter polynomial
multiplications. The resulting *stages* shorten the polynomial
multiplication and enlarge a matrix multiplication tensor. They run in
sequence, and each is made exact separately, so no catalyst is needed. The
main results are:

- For rational `0 < epsilon <= 1`, an explicit rational scheme of at most
  `240 epsilon^(-3/2)` stages computes `m` products of `B x B` matrices
  from `r` products of `A x A` matrices, with exponent between `9/4` and
  `9/4 + epsilon/2`. Each of `log(m)`, `log(r)` and `log(A)` is below
  `2.7e10 epsilon^(-9/2) log^3(4096/epsilon)`.
- Rational seeds of side `n_0` with
  `log(n_0) = O(epsilon^(-11/2) log^3(1/epsilon))`, and one algorithm for
  all `n` with exponent `9/4 + O((log log n)^(6/11) (log n)^(-2/11))`.
- Certified finite examples: schemes with exponent below 2.5, 2.3 and 2.26
  have source sides of 33,379, 12,371,380 and 48,859,824,830 decimal digits.
  Near v5's computed examples, the source sides have 280 and 4,653 digits
  instead of about 1.2e10 and 2.3e11 digits.
- Limits within the construction: the exponent always exceeds `9/4`;
  `log(r)` and `log(m)` have the least possible order
  `epsilon^(-9/2) log^3(1/epsilon)`; and every scheme with exponent below 3
  has more than `2^494` target products (computer-assisted).

All sizes are still astronomically large, and no algorithm here is shown to
use `O(n^(9/4))` operations. The relations are proved over the rationals, so
they hold in characteristic zero; positive characteristic is not treated.
The paper has 47 pages. Its
[README](manuscript-shifted-chains/README.md) states the results with their
statement numbers, and the
[paper record](supplement-shifted-chains/docs/shifted-chains-paper-record.md)
describes how it was checked and written.

## Files

- [finite-extraction.pdf](finite-extraction.pdf): the finite-construction
  paper, version 5.
- [manuscript/](manuscript/): its LaTeX sources, bibliography, Makefile, and
  build instructions.
- [supplement/](supplement/): its supporting scripts, saved reports, component
  tests, the Lean formalization, derivations, and review records, unpacked
  for browsing and reproduction.
- [finite-extraction-supplement-v5.zip](finite-extraction-supplement-v5.zip):
  the same supplement as one archive, with checksums.
- [archive/v4/](archive/v4/): version 4 of the paper (PDF and LaTeX source)
  and its supplement.
- [archive/v3/](archive/v3/): version 3 of the paper (PDF and LaTeX source)
  and its supplement.
- [archive/v2/](archive/v2/): version 2 of the paper (PDF and LaTeX source)
  and its supplement, dated 7 October 2026.
- [shifted-chains.pdf](shifted-chains.pdf): the follow-up paper.
- [manuscript-shifted-chains/](manuscript-shifted-chains/): its LaTeX
  sources, bibliography, Makefile, and build instructions.
- [supplement-shifted-chains/](supplement-shifted-chains/): its scripts,
  saved reports, test, and review records.

The supplements' research notes record earlier stages of the project. The
papers supersede their statements about the completed construction. The
complete coefficient maps are specified mathematically rather than stored as
expanded arrays.

## Build and reproduce

To build the papers, use TeX Live with pdfLaTeX, BibTeX, latexmk, Latin
Modern, microtype, natbib, xurl, hyperref, mathtools, booktabs, and TikZ:

```sh
make -C manuscript
make -C manuscript-shifted-chains
```

To reproduce the supporting calculations of version 5, use Python 3.11 or
later from `supplement/`. The finite-cost evaluator and the scripts that check the
paper's quoted numbers need only the standard library, except that
`flows_row_maxima.py` needs NumPy. The component tests need pytest, NumPy,
and SciPy.

```sh
cd supplement
python -m experiments.multiway_finite_costs
python -I experiments/finite_table_checks.py
python -I experiments/rational_interpolation_audit.py
python -I experiments/rational_seed_arithmetic_checks.py --check
python -I experiments/source_side_bounds.py --check
python -m pytest -q tests
```

The follow-up paper's scripts need only the standard library, and its test
needs pytest. From `supplement-shifted-chains/`:

```sh
cd supplement-shifted-chains
python -I experiments/shifted_chain_certificates.py --check
python -m pytest -q tests
python -I -B experiments/shifted_chains_check_small_sources.py
python -I -B experiments/shifted_chains_check_recycling.py
```

To check the Lean formalization, install `elan` and run, from
`supplement/formalization/`:

```sh
lake exe cache get
lake build
lake env lean PrintAxioms.lean
```

During preparation of version 5, a copy of exactly the files in this
repository built without warnings into the included 79-page PDF. In that
copy:
- all 125 component tests passed;
- the seven scripts that check the paper's quoted numbers passed, and the
  saved reports regenerated;
- the finite-cost evaluator's output matched the saved report except for
  its timing field.

The Lean project was built from an empty directory, fetching the pinned
dependencies from GitHub (with Mathlib's prebuilt files from its cache). It
built all modules, and the endpoint theorems depend only on Lean's standard
axioms.

During preparation of the follow-up paper, a copy of exactly its files in
this repository built without warnings into the included 47-page PDF. From a
standalone copy of `supplement-shifted-chains/`, the certificate check and
the three tests passed, and all 20 check and skeptic scripts ran without
failure, each in at most about two and a half minutes.
