# A finite construction of matrix multiplication algorithms with exponent approaching 9/4

This directory contains the LaTeX source of version 4 of the paper. For every positive rational allowance `eps`, the paper gives a terminating procedure that outputs an exact rational bilinear algorithm with exponent below `9/4 + eps`. For every integer `a >= 2^64`, an explicit relative scheme has pooled exponent `p` with `9/4 < p < 9/4 + 900/log(a)` and source side `A` with `log(A) <= 181 a^5 ceil(log2 a)^2`. Here `log` is the natural logarithm. All sizes are astronomically large.

Version 4 (17 October 2026) adds Section 9 (`algorithm-bounds.tex` and `arithmetic-bounds.tex`):

- A rational variant of the construction, with the same exponent bounds (Section 9.1).
- A formula for the seed side, replacing the search of Corollary 8.7 for this variant (Theorem 9.2).
- Bounds on the coefficient bit lengths and the bit cost of computing the seed (Theorem 9.3).
- For any fixed rational seed: the block-recursion cost (Lemma 9.4), integer bit complexity (Proposition 9.5) and a sufficient precision for a normwise forward error (Proposition 9.6).
- One algorithm for all input sizes, with the preprocessing counted (Corollary 9.7).

The abstract, introduction, discussion and notation table cover the new results; the finite examples are now Section 10. The records are `supplement/docs/final-algorithm-bounds.md` and `supplement/docs/final-algorithm-bounds-check.md`.

Version 3 rewrote version 2 for clarity, without changing its mathematics; its record is `supplement/docs/manuscript-v3-revision.md`.

## Files and build

`main.tex` is the entry point. It inputs `abstract.tex`, the section files and the appendices. Keep them in the same directory as `references.bib`. No author names are included.

Build with TeX Live containing pdfLaTeX, BibTeX, latexmk, Latin Modern, microtype, natbib, xurl and TikZ:

```sh
make -C manuscript
```

The PDF is written to `manuscript/finite-extraction.pdf`; intermediate files stay in the ignored `manuscript/build/` directory. From inside this directory, use `make`. The published copy is `finite-extraction.pdf` at the repository root.

## Evidence and scope

The main theorems are symbolic proofs and do not depend on any computation. The finite examples of Section 10 are computer-assisted. Their bounds and digit counts come from the exact rational interval arithmetic saved in `supplement/results/multiway-finite-costs.json`.

The paper's supporting files are in `supplement/experiments/` and `supplement/results/`; `supplement/README.md` explains how to run them. There is no implementation that expands the full coefficient arrays. The review records supplement the proofs and do not replace journal peer review.
