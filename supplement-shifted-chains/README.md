# Supplement to the shifted-chains paper

This supplement contains the scripts, saved reports, tests and review records for *A singly exponential construction of matrix multiplication algorithms with exponent approaching 9/4* (`shifted-chains.pdf` at the repository root, source in `manuscript-shifted-chains/`). The paper contains the proofs. The scripts certify its computer-assisted statements in exact arithmetic and check its other statements on small cases.

Run all commands from this directory, with Python 3.11 or later. The scripts use only the standard library; the test needs pytest.

## Scripts the paper relies on

The computer-assisted statements of the paper are:

- the witnesses of Proposition 6.1 (Table 2);
- the two finite checks and the sharp example in the proof of Proposition 7.15 (Appendix A.7);
- the decimal digit counts of the source sides `A` and `A'` at `eps = 1`, quoted after Corollary 7.13.

The scripts behind them certify every quoted number with exact integers or with rational intervals rounded outward; floating-point numbers appear only in their informational printouts.

```sh
python -I experiments/shifted_chain_certificates.py --check
python -m pytest -q tests
python -I -B experiments/shifted_chains_check_small_sources.py
python -I -B experiments/shifted_chains_check_recycling.py
```

- `experiments/shifted_chain_certificates.py` certifies every row of Table 2. Its report is `results/shifted-chain-certificates.json`. For each row the script:
  - builds the chain backwards by smallest parents;
  - checks that every stage is legal and that every type has the largest sector count;
  - encloses `Phi`, `p`, `Phi - p` and the decimal digit counts of `A` and `B` in rational intervals with outward rounding;
  - also checks that `Phi` is at least the target at power `k - 1` (the paper does not use this).

  It never forms the large integers. Without options it rewrites the report. With `--check` it recomputes the report and compares it byte for byte with the saved file. The run takes under a second.
- `tests/test_shifted_chain_certificates.py` has three tests:
  - the closed-form counts against stage-by-stage products on a two-stage chain;
  - the witness below 3 in exact integers, with no logarithms;
  - the `--check` mode.
- `experiments/shifted_chains_check_small_sources.py` (about 13 seconds). Part C runs the exact checks (i) and (ii) in the proof of Proposition 7.15 (5,792 and 31,677 cases) and the sharp example of its part (c). Its other parts check related claims that the paper no longer states, such as a composite example with source side `2^128`.
- `experiments/shifted_chains_check_recycling.py` checks forward recycling on the chains of Theorem 4.8 at `eps = 1, 1/2, 1/4, 1/9`. For each chain it prints the exact numbers of decimal digits of the source sides `A` (source supply) and `A' = 4JD^{2Nk}` (recycling supply), their ratio, and an enclosure of `log A / log A'`, all rounded outward. The paper quotes the counts at `eps = 1` after Corollary 7.13: `A` has 3,250,941,263 digits and `A'` has 12,783,943. The ratios of digit counts, which the paper does not quote, lie in `[254.2987, 254.2988]`, `[522.7171, 522.7172]`, `[1184.7501, 1184.7502]` and `[3665.4511, 3665.4512]`. A full run takes about two to two and a half minutes; `--quick` covers only `eps = 1` and `1/2`.

## Verification records

The other `experiments/shifted_chains_check_<topic>.py` scripts, and all `experiments/shifted_chains_skeptic_<topic>.py` scripts, are verification records; the paper does not cite them. Each check script tests the statements of one topic on small cases and recomputes its constants. Each skeptic script is an adversarial re-check of the same topic, written independently of the check script. The topics are:

- `maps`: the shifted basis, its inverse, the coordinate form of `C(r,b) B_X(d)`, the reset, the type restriction and the chain counts (Section 3);
- `upper`: the ramp, the bulk potential, the ideal gap and the constants of Theorem 4.8 (Section 4);
- `seeds`: the resource bounds, the seed and the uniform algorithm (Section 5);
- `certificates`: the cost model of Proposition 3.8 and the witnesses of Table 2;
- `gate`: an earlier finite barrier at source side `2^128`, which the paper does not state because composition defeats it (Remark 7.3);
- `hankel`: the Hankel flattening bound and the potential (Section 7.2);
- `lower`, and the skeptic script for `recycling`: the resource lower bound, supplies and recycling (Section 7.3, Appendix A);
- `small_sources` (skeptic only): Proposition 7.15 and composition (Remark 7.3);
- `literature`: the identifications with published maps in the credits (Sections 1.3 and 3.1).

Run them like the scripts above, for example `python -I -B experiments/shifted_chains_check_maps.py`. Each takes at most about two and a half minutes. They were written while the mathematics was being checked, and some of them use the statement numbers of earlier drafts. Four of them read saved reports from the research that preceded the paper, included in `results/`:

- `results/round11-arity-ramp.json` (read by `shifted_chains_check_maps.py`);
- `results/round11-variable-finite-gate.json` and `results/round11-blocked-finite-gate.json` (read by both `gate` scripts);
- `results/multiway-finite-costs.json`, a copy of the v5 report `supplement/results/multiway-finite-costs.json` (read by `shifted_chains_check_certificates.py`, which prints v5's Table 2 values for comparison).

`shifted_chains_check_certificates.py` and `shifted_chains_skeptic_certificates.py` each recompute every point of `results/shifted-chain-certificates.json` by their own method and compare the result with the report. The authoritative certificate run is `shifted_chain_certificates.py --check`.

## Notes

`docs/` contains the records of how the paper was checked and written:

- `shifted-chains-paper-record.md`: how the content was fixed, the decisions to revisit and the checks of the final state. Start here.
- `shifted-chains-check-<topic>.md`: one note per topic above, plus `recycling` and `small-sources`. Each re-derives the research claims of its topic from scratch and ends with an "Adversarial review" section, whose corrections take precedence.
- `shifted-chains-paper-brief.md`: the brief from which the paper was drafted.
- `shifted-chains-references-draft.bib`: the draft bibliography. It also has a variant of the v5 entry with the pinned URL of this repository (`FinCon26pub`), which the paper does not use.

The notes may describe earlier versions of results; the paper's statements are final. Paths such as `docs/...`, `experiments/...` and `results/...` in the notes and scripts are relative to this directory, and paths such as `manuscript/...` are relative to the repository root. The notes also cite research notes and scripts that are not included: `docs/round<N>-...`, `experiments/round<N>_...` and `tests/test_round<N>_...` files, `upstream/` (a copy of the OpenAI preprint's source) and `all-field-formalization/` (with a checkout of Filmus's Lean code). They are in the research repository in which the work was done, and commit hashes in the notes refer to that repository or, for v5, to this one.

`SHA256SUMS` covers every file of this supplement.

## Scope

No script expands or executes the coefficient maps of the construction or the seed of Theorem 5.2. The scripts measure symbolic counts with exact arithmetic and check the paper's identities and bounds on small cases. There is no Lean formalization of this paper.
