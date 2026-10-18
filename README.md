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

## Version 5

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

## Version 4

Version 4 (17 October 2026) added Section 9, "Explicit bounds for a rational
seed": the rational variant, the explicit seed side, the cost of computing
the seed, bit complexity and sufficient precision for recursion with a fixed
seed, and one algorithm for all sizes. It had 71 pages. See the
[resolution record](supplement/docs/final-algorithm-bounds.md) and the
[second check](supplement/docs/final-algorithm-bounds-check.md).

## Version 3

Version 3 rewrote the paper for clarity. Its mathematics
is that of version 2. The fixes made in
version 3 concern citations, attribution to the OpenAI preprint, one
justification in the flows section, the statement of the rounding rule
behind the finite examples, and notation. The rewritten paper explains where
9/4 comes from, gives every symbol one meaning (Appendix D), and adds worked
examples and figures. It had 62 pages; version 2 had 35. The
[revision record](supplement/docs/manuscript-v3-revision.md) gives the
details.

## Files

- [finite-extraction.pdf](finite-extraction.pdf): the paper, version 5.
- [manuscript/](manuscript/): LaTeX sources, bibliography, Makefile, and build
  instructions.
- [supplement/](supplement/): supporting scripts, saved reports, component
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
python -I experiments/rational_interpolation_audit.py
python -I experiments/rational_seed_arithmetic_checks.py --check
python -I experiments/source_side_bounds.py --check
python -m pytest -q tests
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
