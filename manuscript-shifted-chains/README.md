# A singly exponential construction of matrix multiplication algorithms with exponent approaching 9/4

This paper follows *A finite construction of matrix multiplication algorithms with exponent approaching 9/4* (version 5, called "v5" below; see [Preceding paper](#preceding-paper)). For every rational `eps > 0`, v5 constructs exact rational bilinear algorithms with exponent below `9/4 + eps`. Their sizes are doubly exponential in `1/eps`, and v5's Corollary 11.2 shows that this is necessary within v5's construction. v5's second open question (v5 Section 11.5) asks for a construction in which `log A`, for the source side `A`, is bounded by a polynomial in `1/eps`. But `A` alone is not a robust measure: composition with the classical algorithm reduces it to 1 (Remark 7.3). The robust measures are the copy counts `r_*` and `m_*` and the seed side `n_0`, all doubly exponential within v5. Here all three are singly exponential:

- `log r_*` and `log m_*` are `O(eps^{-9/2} log^3(1/eps))`, the least possible order within the construction, and they do not depend on how the auxiliaries are supplied;
- `log n_0 = O(eps^{-11/2} log^3(1/eps))`. The seed depends on the supply only through the leaf threshold `n_*`, which lies between `A` and `2A+1` for these schemes, and the seed built from the recycled scheme has `log n_0` smaller by a factor below 1.34 (Remark 7.14).

The source side also satisfies `log A = O(eps^{-9/2} log^3(1/eps))`, which answers the question as posed.

The main ingredient is the *shifted sum* of `d` polynomials. For an arity `d >= 2` and a child length `1 <= c < b`, it splits `C(r,b) B_X(d)` block-triangularly into `d-1` kernel parts `C(r,c)` and one quotient part `C(r, db-(d-1)c)`. A crop and the reset (the partition behind OpenAI's shifted tripling) turn the quotient part into three copies of `C(r,c)`, one of them with legs 2 and 3 exchanged. Fixing the class counts of a type removes every cross term. A *stage* `(r,b) -> (c,r)` then trades an auxiliary `MM_{d^{2N}}` for `MM_{M^2}`, where `M` is about `(d+2)^N`. Stages run in sequence from a source pair down to a terminal pair `(1,t)`. Each stage is made exact separately, and no catalyst is needed.

Main results:

- **Main theorem** (Theorem 4.8, Corollary 4.9). Let `0 < eps <= 1` be rational. An explicit chain of at most `240 eps^{-3/2}` stages gives a relative scheme over Q with `9/4 < p < 9/4 + eps/2`, `log m_* < 1.8e10 eps^{-9/2} log^3(4096/eps)` and `log r_* < 2.7e10 eps^{-9/2} log^3(4096/eps)`. It also has `m_* = B^3`, `r_* < A^{35/4}`, `B <= A^2` and `log A < 3e9 eps^{-9/2} log^3(4096/eps)`.
- **Seeds and one algorithm** (Theorems 5.2 and 5.8, Proposition 5.4):
  - a rational seed of side `n_0` with `log n_0 < 2.1e11 eps^{-11/2} log^3(4096/eps)`;
  - coefficients with singly exponential bit lengths, generated with at most `A^46` bit operations from `eps = u/v` with `u, v <= A`;
  - one algorithm for all `n >= 2` with `n^{9/4 + delta(n)}` steps, where `delta(n) = O((log log n)^{6/11} (log n)^{-2/11})`.
- **Finite examples** (Proposition 6.1, Table 2; computer-assisted). Schemes with `Phi < 2.5`, `2.3` and `2.26` have source sides of 33,379, 12,371,380 and 48,859,824,830 decimal digits. Near v5's computed examples (`Phi < 2.84063` and `2.67283`), the source sides have 280 and 4,653 digits.
- **Limits within the construction** (Section 7, Appendix A):
  - `p > 9/4` for every chain scheme and supply, also with compressed auxiliaries (Corollary 7.9, from a Hankel-flattening bound).
  - The copy counts and `log(B/A)` have the optimal orders `eps^{-9/2} log^3(1/eps)` and `eps^{-4} log^2(1/eps)` (Theorem 7.12 and Remark 7.14).
  - The source side depends on how the auxiliaries are supplied. Forward recycling keeps `r_*` and `m_*` and gives `log A' < 5.32e6 eps^{-3} log^3(4096/eps)` (Corollary 7.13), and composition with the classical algorithm gives source side 1 (Remark 7.3).
  - Every chain scheme with `p < 3`, also after composition and tensor products, has more than `2^494` target copies, and the least such count is attained (Proposition 7.15; computer-assisted).

All sizes are astronomically large, and no algorithm here is shown to use `O(n^{9/4})` operations. The local maps hold over every field. The relations that use the separator and exactification are proved over Q, so they hold in characteristic zero; positive characteristic is not treated. The paper has no author names, like v5.

## Files and build

`main.tex` is the entry point. It inputs `abstract.tex`, the section files (`introduction.tex`, `preliminaries.tex`, `stages.tex`, `chains.tex`, `seeds.tex`, `examples.tex`, `limits.tex`, `open-questions.tex`) and the appendices (`appendix-lower.tex`, `appendix-coefficients.tex`). `references.bib` contains exactly the cited entries.

You need TeX Live with pdfLaTeX, BibTeX, latexmk, Latin Modern, microtype, natbib, xurl, hyperref, mathtools and booktabs. From the repository root, build with:

```sh
make -C manuscript-shifted-chains          # writes manuscript-shifted-chains/shifted-chains.pdf
make -C manuscript-shifted-chains clean    # removes the intermediate files in build/
```

The PDF has 47 pages. The published copy is `shifted-chains.pdf` at the repository root. Intermediate files stay in `build/`, which git ignores. If an editor ran LaTeX in place, it may have left `main.aux` and related files in this directory; delete them before running `make`, so that latexmk does not reuse a stale bibliography.

## Evidence and scope

The theorems are proved symbolically and do not depend on computation. The computer-assisted statements are:

- the witnesses of Proposition 6.1 (Table 2);
- the two finite checks and the sharp example in the proof of Proposition 7.15 (Appendix A.7);
- the decimal digit counts of the source sides `A` and `A'` at `eps = 1`, quoted after Corollary 7.13.

The scripts behind them, their reports and the review records are in `supplement-shifted-chains/`; its `README.md` explains how to run them. There is no implementation that expands the full coefficient arrays.

## Preceding paper

The paper cites v5 as `[FinCon26]`, with v5's own theorem, section and equation numbers:

> A finite construction of matrix multiplication algorithms with exponent approaching 9/4. Version 5, 18 October 2026. Versions 1 and 2 (7 October 2026) have the title *Explicit finite extraction from convolution profiles for matrix multiplication*.

In this repository, the v5 PDF is `finite-extraction.pdf` and its source is in `manuscript/`. The v5 numbers cited here were checked against the v5 build.
