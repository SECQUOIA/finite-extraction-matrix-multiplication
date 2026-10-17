# A finite construction of matrix multiplication algorithms with exponent approaching 9/4

This directory contains the LaTeX source of version 3 of the paper. For every positive rational allowance `eps`, the paper gives a terminating procedure that outputs an exact rational bilinear algorithm with exponent below `9/4 + eps`. For every integer `a >= 2^64`, an explicit relative scheme has pooled exponent `p` with `9/4 < p < 9/4 + 900/log(a)` and source side `A` with `log(A) <= 181 a^5 ceil(log2 a)^2`. Here `log` is the natural logarithm. The bound on `A` is not a bound on the final rational seed, its coefficients, or the construction time. The results concern exact arithmetic only.

Version 3 (17 October 2026) rewrites version 2 for clarity; the mathematics is unchanged. The changes are:

- A new title.
- An introduction that explains where `9/4` comes from and how the finite construction works.
- One notation table (Appendix D), with no symbol carrying two meanings.
- Worked examples and figures.
- Credit to the OpenAI preprint at each point of use.
- Corrected citations.
- An explicit rounding rule for the finite examples.

The revision record is `supplement/docs/manuscript-v3-revision.md`.

## Files and build

`main.tex` is the entry point. It inputs `abstract.tex`, the section files and the appendices. Keep them in the same directory as `references.bib`. No author names are included.

Build with TeX Live containing pdfLaTeX, BibTeX, latexmk, Latin Modern, microtype, natbib, xurl and TikZ:

```sh
make -C manuscript
```

The PDF is written to `manuscript/finite-extraction.pdf`; intermediate files stay in the ignored `manuscript/build/` directory. From inside this directory, use `make`. The published copy is `finite-extraction.pdf` at the repository root.

## Evidence and scope

The main theorems are symbolic proofs and do not depend on any computation. The finite examples of Section 9 are computer-assisted. Their bounds and digit counts come from the exact rational interval arithmetic saved in `supplement/results/multiway-finite-costs.json`.

The paper's supporting files are in `supplement/experiments/` and `supplement/results/`; `supplement/README.md` explains how to run them. There is no implementation that expands the full coefficient arrays. The review records supplement the proofs and do not replace journal peer review.
