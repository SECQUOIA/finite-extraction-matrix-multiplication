# Manuscript version 3: verification and rewrite for clarity

Date: 17 October 2026.

Version 3 rewrites the finite-extraction paper so that an expert can read and check it. The mathematics of version 2 is unchanged. The new title is *A finite construction of matrix multiplication algorithms with exponent approaching 9/4*.

The version 2 PDF, LaTeX source and supplement are preserved in `archive/v2/` at the repository root. The current PDF is `finite-extraction.pdf` (62 pages; version 2 had 35). Paths below are relative to this supplement unless stated otherwise.

## 1. Independent verification of version 2

Before any rewriting, separate agents checked the version 2 mathematics. Each covered one area, and each recomputed results independently with exact arithmetic rather than relying on the supplement code. Where needed, review agents tried to refute serious findings. Their full reports are in `docs/manuscript-v3-verification.md`.

| Area | Main checks | Verdict |
|---|---|---|
| Tensor conventions and maps | Every identity rebuilt with explicit coordinate permutations under both leg-permutation conventions. Unimodular determinant bases. Lemma multiway on 24 parameter sets (138 type classes). Lemma tripling. Separator degeneration exact for 12 parameter sets, including general `K_0` and `c`. | Sound, minor issues |
| Least profile and occupation flows | Second-difference formula (sympy). Profile axioms for `m, n <= 80`. LP minimum on truncated grids. Exact occupations for rows up to 120. Drift inequality for `n <= 600`. | Sound, minor issues |
| Rounding, ledger, entropy loss | Own max-flow rounding on 342 real row circulations and 3000 random multigraphs. Ledger exact. `G = K log F(a,a) - L` to 1e-73. `L/(4 J_a) <= 0.0287`. | Sound, minor issues |
| Construction, constants, seeds | Independent re-implementation. Every constant of the quantitative theorem re-derived. Cyclotomic order, descent and seed termination. | Sound, minor issues |
| Appendices | Exact certificate and `K_a` closed form for `a = 2..60`. Composed maps on small instances. Separator refinements. | Sound, minor issues |
| Finite examples | Supplement pipeline re-run (byte-identical report). Independent 80-digit evaluation reproduces the types and bounds of the table. | Sound, minor issues |
| Citations | All 29 citations checked against sources, with Crossref for every DOI. | One wrong pinpoint and missing local credit |
| End-to-end logic (adversarial) | Directions of all maps, separator, orientation bookkeeping, catalyst, exactification, relative scheme, pooled recursion. | Sound |
| Monotone invariants (adversarial) | Flattening ranks and quantum functionals on every gadget. No violation. These tests cannot refute `omega <= 9/4` by themselves. | Sound |

No fatal, major or minor mathematical error was found. The problems fixed in version 3 are:

- **Citations and attribution:**
  - The CVZ21 pinpoint is Section 3.2, not 3.3.
  - Credit to OAI26 is now given at each reuse: the profile axioms (its eqs. 4.5, 4.6, 4.9), the diagonal bound (its Lemma 5.1), the width-one determinant step (Lemma 4.1), the tripling partition (Lemma 4.2), and the separator with 5M copies (Proposition 3.1).
  - The abstract now credits the preprint.
  - Bibliography metadata is corrected.
- **Reasoning:** one non sequitur in the flows section, and imprecise wording about monotone increments and chords.
- **Reproducibility:** the finite-cost table depends on which valid rounding is used. The paper now states the rule (breadth-first augmenting paths in a fixed arc order) and says that the table entries bound a sufficient upper expression for the fixed-batch exponent, not the exponent itself.
- **Exposition:** many overloaded symbols, ambiguous fractions, and terms that were never defined.

## 2. Research on writing

**Reader reaction.** Readers widely described the October 2026 OpenAI manuscripts as hard to read. Sources include Quanta, Scientific American, Scott Aaronson's blog, the Proofs and Prompts roundup and Hacker News. The recurring complaints were:

- the key idea is never explained;
- proofs are compressed;
- the structure is jumbled and repetitive;
- terminology is coined or strange;
- citations are decorative;
- the prose is bloated and defensive;
- the scope is unclear.

**Writing guidance.** The candidate writing skills were checked one by one:

- labarba/sciwrite;
- Master-cai/Research-Paper-Writing-Skills;
- blader/humanizer;
- Orchestra ml-paper-writing;
- stop-slop;
- K-Dense scientific-writing;
- obra/the-elements-of-style;
- WenyuChiou/academic-writing-skills.

The classic sources were also read: Halmos, Knuth–Larrabee–Roberts, Tao's writing pages, Gopen–Swan, and Wikipedia's "Signs of AI writing". None of the skills was installed. The ML-oriented skills and stop-slop contain rules that damage mathematical prose, such as bans on adverbs, quantifiers and passive definitions. The rules adopted for the rewrite were:

- state the result and the key idea first;
- open each section with its purpose;
- give an idea sentence before each long proof;
- one name per concept and one meaning per symbol, with a notation table;
- state each explanation once, in a fixed place;
- state the scope once;
- mark the status of every claim;
- remove AI-writing tells.

## 3. The rewrite

- **Draft (v3):** twelve writers (ten for sections, one for the bibliography and notation table, one for the introduction) worked from a shared brief. The brief contained:
  - the style rules;
  - a global notation table;
  - a glossary;
  - the list of allowed mathematical changes;
  - the verification fixes;
  - a written account of where 9/4 comes from.
- **Review:** six math-preservation reviewers compared every statement with version 2. Two cold-read referees (one specialist, one generalist), a style auditor, a notation auditor and a length editor also reviewed the draft. No reviewer found a mathematical error; all found the draft much clearer than version 2 but too long at 83 pages.
- **Edit (v4):** twelve editors removed repetition, keeping each explanation in one place and replacing the others by cross-references. They shortened section openers and routine proofs and applied the review items. The paper came down to 62 pages.
- **Final check:** six math-preservation checkers compared version 4 against version 2. A fresh cold-read referee and a notation and style sweep checked it as a whole. No mathematical error was found, and the referee rated the exposition as needing minor revision only. All of their concrete items were applied in the final text.

### Mathematical changes (all allowed by the brief)

**Notation.** Every symbol now has one meaning, as listed in Appendix D:

| Old | New |
|---|---|
| sector index `omega` | `g` |
| copy count `S` | `L` |
| `H` (= `M^3`) | `M^3` |
| dimensions `u`, `v` | `A_1`, `B_1` |
| totals `U`, `T` | `w-bar`, `z-bar` |
| `C_a` | `Gamma_a` |
| `L_*` | `Lambda` |
| empirical distributions `p` | `q-hat` |

**Moves:**
- Lemma batch moved to Section 2.
- Theorem effective, Lemma descent and Corollary seed moved to Section 8.
- The fixed-batch bound moved to Section 9.
- The comparison with exact normalization moved to Appendix A.
- The general separator with parameters `(K_0, c)` moved to Appendix C. The main text uses `K_0 = M`, `c = 1`.

**Statements:**
- The quantitative theorem now states the lower bound `p > 9/4`, which its proof already established.
- Theorem 1.2 cites a new remark (Remark 8.5) that identifies the field for every `a >= 2^64`.

**Added material.** Worked examples (determinant basis, row walk of row 2, ledger for `a = 2`), two figures, an overhead table, and a section on where 9/4 comes from.

## 4. New supporting scripts

Each script runs in seconds from the supplement root, uses only files in this supplement and the Python standard library (NumPy for one floating-point evaluation), and prints the numbers that the paper quotes:

- `experiments/finite_table_checks.py`: every number of Section 9, from `results/multiway-finite-costs.json`.
- `experiments/extraction_a2_small_scale.py`: `Delta_1 < 0` for `a = 2`, `N = 1`, `K <= 7` over all allowed roundings (exact integers), and Example 7.2.
- `experiments/flows_row_maxima.py`: Example 5.2 (exact) and Remark 5.4 (floating point).
- `experiments/rounding_observed_loss.py`: Remark 6.4. It also confirms that its rounding reproduces `experiments/multiway_rounded_flow.py`.

## 5. Open items

- The paper itself has no author names, and it does not state that AI produced it; only the repository README does. Readers criticized exactly this in the October release, so it should be decided before any public posting.
- These reviews were done by AI agents. They supplement the proofs but are not journal peer review.
