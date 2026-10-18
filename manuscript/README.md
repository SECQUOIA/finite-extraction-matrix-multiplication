# A finite construction of matrix multiplication algorithms with exponent approaching 9/4

This directory contains the LaTeX source of version 5 of the paper. For every positive rational allowance `eps`, the paper gives a terminating procedure that outputs an exact rational bilinear algorithm with exponent below `9/4 + eps`. For every integer `a >= 2^64`, an explicit relative scheme has pooled exponent `p` with `9/4 < p < 9/4 + 900/log(a)` and source side `A` with `log(A) <= 181 a^5 ceil(log2 a)^2`. Here `log` is the natural logarithm. Within the construction, the least source side for exponent at most `9/4 + eps` is `exp(exp(Theta(1/eps)))`. All sizes are astronomically large.

Version 5 (18 October 2026) makes these changes:

- **Related work.** The paper cites the work that appeared after the OpenAI preprint (Sections 1.1, 1.4, 1.5 and 3):
  - Lü's polynomial separator;
  - Filmus's block-identity criterion, his proof over every field and his Lean code;
  - the Lean proofs of Navot and Zuiddam over every field, and Navot's extension to associative rings;
  - Uznański's rectangular bounds;
  - later laser-method bounds.
- **Section 9.1.** The rational variant now uses Lü's separator: `2M-1` rational source copies, degree at most `M-1`. It therefore has the same counts as the main construction. Remark 4.7 credits Lü and explains why Proposition 4.6 is kept in the main construction.
- **Remark 9.8.** A proof sketch that, for a suitable implementation of the preprocessing, the `o(1)` of Corollary 9.7 is `O(1/log log n)`.
- **Section 11.2, "Limits of the construction"** (Proposition 11.1, Corollary 11.2, Remarks 11.3–11.5):
  - every scheme with `p < 3` has `A >= 12^18`;
  - the least source side at allowance `eps` is `exp(exp(Theta(1/eps)))`, even with a free catalyst;
  - with arbitrary decompositions of the source and catalyst, `A >= 2^24` (computer-assisted).
- **Section 11.3.** A Lean 4 formalization of a simpler rational variant proves `omega <= 9/4` over every field of characteristic zero, without explicit constants. The Lean files are in `supplement/formalization/`.

The record of the revision is `supplement/docs/manuscript-v5-revision.md`.

Version 4 added Section 9 (rational seeds and their resources); its records are `supplement/docs/final-algorithm-bounds.md` and `supplement/docs/final-algorithm-bounds-check.md`. Version 3 rewrote version 2 for clarity, without changing its mathematics; its record is `supplement/docs/manuscript-v3-revision.md`.

## Files and build

`main.tex` is the entry point. It inputs `abstract.tex`, the section files and the appendices. Keep them in the same directory as `references.bib`. No author names are included.

Build with TeX Live containing pdfLaTeX, BibTeX, latexmk, Latin Modern, microtype, natbib, xurl and TikZ:

```sh
make -C manuscript
```

The PDF is written to `manuscript/finite-extraction.pdf`; intermediate files stay in the ignored `manuscript/build/` directory. From inside this directory, use `make`. The published copy is `finite-extraction.pdf` at the repository root. If an editor has run LaTeX in place and left `main.aux` and similar files in this directory, delete them before running `make`; otherwise latexmk may reuse a stale bibliography.

## Evidence and scope

The main theorems are symbolic proofs and do not depend on any computation. The finite examples of Section 10 and Remark 11.5 are computer-assisted, in exact arithmetic. Their numbers come from the scripts and reports in `supplement/experiments/` and `supplement/results/`; `supplement/README.md` explains how to run them and how to build the Lean formalization. There is no implementation that expands the full coefficient arrays.
