**A finite construction of matrix multiplication algorithms with exponent approaching 9/4**

This repository contains an **AI-produced research paper** and its supporting
materials. AI agents developed the mathematical arguments, manuscript,
supporting calculations, and review records.

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
This bounds the scheme's source side, not the size of the final rational
algorithm or the time needed to construct it. The paper does not give a fixed
algorithm with exponent exactly 9/4, an expanded coefficient certificate, or
a practical implementation. Its dimensions and constants are enormous, and
all results concern exact arithmetic.

## Version 3

Version 3 (17 October 2026) rewrites the paper for clarity. Its mathematics
is that of version 2. Before the rewrite, independent AI reviewers checked
every section of version 2, recomputing its claims with their own
exact-arithmetic code. They found no mathematical error. The fixes made in
version 3 concern citations, attribution to the OpenAI preprint, one
justification in the flows section, the statement of the rounding rule
behind the finite examples, and notation. The rewritten paper explains where
9/4 comes from, gives every symbol one meaning (Appendix D), and adds worked
examples and figures. It has 62 pages; version 2 had 35. The
[revision record](supplement/docs/manuscript-v3-revision.md) and the
[verification reports](supplement/docs/manuscript-v3-verification.md) give
the details. These are AI reviews, not journal peer review.

## Files

- [finite-extraction.pdf](finite-extraction.pdf): the paper, version 3.
- [manuscript/](manuscript/): LaTeX sources, bibliography, Makefile, and build
  instructions.
- [supplement/](supplement/): supporting scripts, saved reports, component
  tests, derivations, and review records, unpacked for browsing and
  reproduction.
- [finite-extraction-supplement-v3.zip](finite-extraction-supplement-v3.zip):
  the same supplement as one archive, with checksums.
- [archive/v2/](archive/v2/): version 2 of the paper (PDF and LaTeX source)
  and its supplement, dated 7 October 2026.

The supplement's research notes record earlier stages of the project. The
paper supersedes their statements about the completed construction. The
complete coefficient maps are specified mathematically rather than stored as
expanded arrays.

## Build and reproduce

To build the paper, use TeX Live with pdfLaTeX, BibTeX, latexmk, Latin
Modern, microtype, natbib, xurl, and TikZ:

```sh
make -C manuscript
```

To reproduce the supporting calculations, use Python 3.11 or later from
`supplement/`. The finite-cost evaluator and the scripts that check the
paper's quoted numbers need only the standard library, except that
`flows_row_maxima.py` needs NumPy. The component tests need pytest, NumPy,
and SciPy.

```sh
cd supplement
python -m experiments.multiway_finite_costs
python -I experiments/finite_table_checks.py
python -m pytest -q tests
```

During preparation of version 3, the source built without warnings into the
included 62-page PDF, and all 125 component tests passed. The four scripts
added for version 3 ran from `supplement/` and printed the numbers quoted in
the paper. The finite-cost evaluator's output matched
the saved report except for its timing field.
