# Manuscript version 5: revision record

Date: 18 October 2026. Version 5 of
[finite-extraction.pdf](../../finite-extraction.pdf) (79 pages)
replaces version 4 (71 pages, preserved in
[archive/v4](../../archive/v4/)). Sections 2–8 and 10
and the appendices are unchanged except for the edits listed below.

## What changed

- **Related work (Sections 1.1, 1.4, 1.5, 3).** These works appeared after
  the OpenAI preprint and are now cited:
  - Lü's polynomial separator (arXiv:2610.18914);
  - Filmus's block-identity criterion, all-field proof and Lean code
    (GitHub, commit `8e38460c`). Filmus's optimal profile is `F/2` in his
    normalization, and he cites an earlier version of this paper;
  - the Lean proofs over every field by Navot (Zenodo 10.5281/zenodo.23219128)
    and Zuiddam (GitHub, commit `615b591c`);
  - Navot's extension to associative rings (Zenodo 10.5281/zenodo.23268534);
  - Uznański's rectangular bounds (arXiv:2610.10494);
  - Zadeh's laser-method bound (arXiv:2610.10593);
  - OpenAI's two companion preprints dated 24 September 2026 and OpenAI's
    Lean code over the complex numbers;
  - Lean 4 and Mathlib.

  Two further corrections:
  - The OpenAI preprint is now described as dated 2 October and released
    6 October 2026.
  - The novelty statement no longer presents the existence of rational seeds
    as new, since Navot's ring result gives integer decompositions. What is
    new is the construction and its bounds.
- **Section 9.1.** The rational variant uses Lü's separator: `2M-1` rational
  copies, degree at most `M-1`. It is written in coordinates as Lemma 9.1(b),
  with a short proof. The variant now has exactly the counts of Section 7, so
  Theorem 8.1 applies verbatim. All `4M-3` material is removed (weights,
  counts, the `3I log 4` overhead and the `r_*^Q` notation). Theorems 9.2 and
  9.3 change in notation, and in the preprocessing steps that compute Lü's
  coefficients.
- **Remark 4.7.** Credits Lü, and also Filmus's `6M-5` interpolation
  separator. It explains why Proposition 4.6 stays in the main construction:
  Appendices B–C and Section 10 use its phases and degree bound.
- **Remark 9.8.** Sketches that, for a suitable implementation of the
  preprocessing, the index of Corollary 9.7 satisfies
  `log2 log2 n / 273600 <= v(n) < log2 log2 n / 3600`. The upper bound holds
  for every implementation, so the double-log order is optimal for this
  argument. Theorem 9.3 as stated gives only a triple-log rate. Remark 9.8 uses an
  order-independent bit-length inequality and states the Turing-machine cost
  model.
- **Section 11.2, "Limits of the construction".**
  - Proposition 11.1: `p < 3` implies `A >= 12^18`; `p <= 9/4 + eps` implies
    an index bound, a reuse bound and `log A > (1/2)(6/5)^(9/(2 eps))`.
  - Corollary 11.2: the least source side is `exp(exp(Theta(1/eps)))`, with
    `0.6/eps < log log A_min < 6300/eps`; and dense seeds have sides doubly
    exponential in `1/eps`.
  - The double exponential does not depend on the catalyst.
  - Remark 11.3: what the construction can certify.
  - Remark 11.4: the scope, extended to every conserved integer flow and
    every legal width.
  - Remark 11.5: `A >= 2^24` with arbitrary joint decompositions of source
    and catalyst, by flattening ranks and an exact search.

  The proofs are analytic, so the exhaustive search of the original notes is
  not needed for Proposition 11.1.
- **Section 11.3.** Describes the Lean formalization: its endpoint theorems,
  what it covers, how it differs from the paper, and what is not formalized.
- **Section 11.** Retitled "Limits, formalization and open questions";
  open questions 2–4 revised.
- **Supporting files.** New `experiments/source_side_bounds.py` and
  `results/source-side-bounds.json`. `experiments/rational_interpolation_audit.py`
  now checks Lü's separator in place of the `4M-3` weights. The three Lean
  separator modules now credit Lü. The supplement adds the Lean project in
  `formalization/` (65 modules, with build instructions).

## Sources of the new material

The new results were first worked out in research notes of the private
research repository. Two of them are included here, with their scripts:
[exponent-dimension-tradeoff.md](exponent-dimension-tradeoff.md) and
[multiway-general-flow-lower-bound.md](multiway-general-flow-lower-bound.md),
for Proposition 11.1 and Corollary 11.2. The others, for Remark 11.5,
Remark 9.8, the use of Lü's separator and the Lean work, are not needed:
the paper's text is a fresh write-up with its own proofs and constants, and
the Lean files are in [formalization](../formalization/).

## How the material was selected

The research checkpoint of 18 October 2026 and the round reports of the
research repository were sorted by relevance to this paper. Included:

- results about the construction's own limits;
- improvements of Section 9;
- related work;
- the Lean formalization.

Left out on purpose:

- **The program on the source tensor `S^+_{2,2}`:**
  - border rank `21`/`20 <= border rank <= rank <= 27`;
  - the Borel-profile exclusions;
  - the catalyst restrictions such as `S^+_{2,2} MM_3 -> MM_10`;
  - the budget-nineteen and small-characteristic results.

  It is a separate subject and heavily computer-dependent. The one-step
  restrictions at `a = 2` concern restrictions, not the degenerations the
  construction uses.
- **Other limits and examples:** the retained-work bound, the
  separator-module counterexample, the "moderate exponents" table and the
  small subcubic examples. Each is either model-dependent or adds length
  without changing the paper's conclusions.
- **Practical kernels:** the rank-40 and rank-48 kernels, which are
  unrelated to the construction.
- **Unreviewed AI-generated repositories** found in the literature search:
  Cassidy, acprk, Hugin-Hilbert and Tilloy. They are not cited.

## Checks of the final state

- The clean build has no LaTeX, natbib or BibTeX warnings and every
  citation resolves.
- `source_side_bounds.py --check`, `rational_interpolation_audit.py`,
  `rational_seed_arithmetic_checks.py --check` and `finite_table_checks.py`
  pass.
- The component tests pass.
- The Lean project builds, and its endpoint theorems depend only on Lean's
  standard axioms.

## Open items

- **Length.** The paper grew from 71 to 79 pages, mainly from Section 11.2
  (about 3.3 pages), Remark 9.8 with its sketch (about 1.5 pages) and the
  related work.
- **Remark 9.8** is a sketch. Its lower bound assumes that each assembly
  stage of Theorem 9.3 is carried out as one dense operation, and it argues
  the bit-length bounds of the primitive data at sketch level.
- **Remark 11.5** rests on an exact computer search
  (`source_side_bounds.py`), and the paper says so.
- **Historical notes.** Notes in `docs/` that describe the `4M-3` separator
  refer to version 4.
- **License.** The supplement has no license file; the Lean dependency
  (fetched at build time, not copied) is Apache-2.0.
