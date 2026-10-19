# Follow-up paper on shifted chains: record

Date: 19 October 2026. The paper *A singly exponential construction of
matrix multiplication algorithms with exponent approaching 9/4* is in
[manuscript-shifted-chains](../../manuscript-shifted-chains/) (47 pages,
`shifted-chains.pdf`). Its [README](../../manuscript-shifted-chains/README.md)
states the results, the build and the supplementary scripts. The v5 paper in
`manuscript/` is unchanged.

## How the content was fixed

1. **Verification of the research claims** (rounds 8–14). Each topic was
   re-derived from scratch with exact-arithmetic checks, then attacked by a
   separate referee. The notes end with an "Adversarial review" section, whose
   corrections take precedence:
   [maps](shifted-chains-check-maps.md),
   [upper bound](shifted-chains-check-upper.md),
   [lower bound](shifted-chains-check-lower.md),
   [Hankel limit](shifted-chains-check-hankel.md),
   [seeds](shifted-chains-check-seeds.md),
   [certificates](shifted-chains-check-certificates.md),
   [finite gate](shifted-chains-check-gate.md),
   [literature](shifted-chains-check-literature.md).
   No mathematical error was found in the research claims. The corrections
   concerned scope, credit (OpenAI's Lemmas 4.1, 4.2 and Proposition 3.1;
   Maakestad's filtration) and notation.
2. **Two points resolved before drafting**:
   [recycling and robust lower bounds](shifted-chains-check-recycling.md) and
   [small sources](shifted-chains-check-small-sources.md).
   - Supplying a stage's auxiliary from an earlier stage's output (forward
     recycling), or composing with the classical algorithm, changes the source
     side `A`, down to `A = 1`. The robust measures are the copy counts
     `r_*`, `m_*` and the seed side. The paper's lower bound is stated for
     them; the bound on `A` is stated only when the source supplies every
     auxiliary.
   - The research notes' barrier "`A <= 2^128` forces `p >= 2.97696`" is an
     accounting artifact and was dropped. It is replaced by a certified bound
     that survives recycling and composition: every subcubic chain scheme has
     `m_* > 2^494`.
3. **Drafting** from the [brief](shifted-chains-paper-brief.md), with
   [draft bibliography](shifted-chains-references-draft.bib).
4. **Review** by eight reviewers (four on the mathematics, one on numbers,
   one cold-read referee, one on citations, one editor). Serious findings were
   verified independently before revision. None was fatal. The confirmed one
   was the separator credit. The rest concerned framing (lead with copy counts
   and seed side rather than `A`), the term "chain scheme", the order of
   Sections 6–7, notation and length (51 to 46 pages).
5. **Final round** on the regression check and a fresh read. The build is
   clean: no warnings, undefined references or overfull boxes.

## Decisions to revisit

- v5 is cited without a URL or authors, as v5 itself avoids identifying its
  repository. Its public repository is already cited by Filmus's manuscript.
  `docs/shifted-chains-references-draft.bib` also has a variant with the
  pinned repository URL (`FinCon26pub`).
- Equation numbers use v5's style (`\numberwithin{equation}{section}`), so
  equation and statement numbers can coincide.
- The paper is 47 pages, against an initial target of 30–38. Every proof that
  a later statement uses is kept.
- Not covered: positive characteristic, a Lean formalization, precision and
  integer bit complexity of the recursive algorithm.

## Checks of the final state

```sh
make -C manuscript-shifted-chains
python -I experiments/shifted_chain_certificates.py --check
python -m pytest -q tests/test_shifted_chain_certificates.py
python -I experiments/shifted_chains_check_small_sources.py
python -I experiments/shifted_chains_check_recycling.py --quick
```

All pass. The full recycling run takes about two minutes. The other
`shifted_chains_check_*` and `shifted_chains_skeptic_*` scripts are the
verification records. They pass, but the paper relies only on the scripts
listed above.
