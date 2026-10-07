**Explicit finite extraction from convolution profiles for matrix multiplication**

This repository contains an **AI-produced research paper** and its supporting
materials. AI agents developed the mathematical arguments, manuscript,
supporting calculations, and review records.

The paper presents a finite construction from convolution tensor relations
for matrix multiplication. For each fixed positive rational allowance
epsilon, it describes a terminating procedure that specifies a rational
bilinear seed and a recursion with arithmetic complexity
`O_epsilon(n^(9/4 + epsilon))`. It also gives a least scalar-profile formula,
rational certificates, and complete finite-cost accounting.

The revision combines multiway determinant restrictions, threefold orientation
balancing, rational occupation flows, conserved circulation rounding, and
pooled recursion. For a profile index `a >= 2^64`, an explicit parameter family
has recursive exponent below `9/4 + 900/log(a)` and relative source side `A`
satisfying `log(A) <= 181 a^5 ceil(log2(a))^2`. Here `log` denotes the natural
logarithm. This bounds the relative scheme's source side, rather than the final
rational seed dimension or the cost of generating its coefficients. The exact
binary certificate and its denominator formula remain as an appendix comparison.

The exponent 9/4 was already claimed in OpenAI's
[An Upper Bound of 9/4 for the Matrix Multiplication Exponent](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf).
This paper's subject is the explicit finite extraction and its cost analysis.
It does not provide a fixed recursion with exponent exactly 9/4, an expanded
end-to-end coefficient certificate, or a practical implementation. Its
prescribed dimensions and constants are enormous, and numerical stability
and useful finite-size performance have not been established.

The publication files are:

- [finite-extraction.pdf](finite-extraction.pdf): the revised 35-page paper.
- [manuscript/](manuscript/): LaTeX sources, bibliography, Makefile, and build
  instructions.
- [supplement/](supplement/): supporting scripts, saved reports, component
  tests, and derivations, unpacked for browsing and reproduction.
- [finite-extraction-supplement-v2.zip](finite-extraction-supplement-v2.zip):
  supplement version 2, dated 7 October 2026, as cited in the paper. It contains
  exact-arithmetic scripts, saved reports, component tests, derivations, review
  records, and checksums.

The supplement's research notes preserve earlier stages of the project. The
paper supersedes their statements about the completed construction. The
complete coefficient maps are specified mathematically, rather than stored
as expanded arrays. Unrelated performance experiments from the research
workspace are outside this publication bundle.

To build the paper, use a standard TeX Live installation with pdfLaTeX,
BibTeX, latexmk, Latin Modern, microtype, natbib, and xurl:

```sh
make -C manuscript
```

To inspect or reproduce supplementary checks, use `supplement/`. Python
3.11 or later runs the exact construction reports; pytest, NumPy, and SciPy
support the full component test suite and optional linear programs.

```sh
cd supplement
python -m experiments.multiway_finite_costs
python -m pytest -q tests
```

During preparation of this update, the revised source built without warnings,
and the rebuilt PDF's extracted text matched the included PDF. The unpacked
supplement matches the version 2 archive, and all seven calculation dependency
hashes in the saved finite-cost report match the included scripts. All 125
supplementary component tests passed.
