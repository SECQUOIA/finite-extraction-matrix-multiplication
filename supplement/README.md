# Supplement to the finite-extraction manuscript (v5)

This supplement contains the supporting code, saved reports, component tests, Lean formalization, derivations and review records for version 5 of the paper, *A finite construction of matrix multiplication algorithms with exponent approaching 9/4*. The paper contains the proofs. The numerical reports are exact-arithmetic certificates that support it. The research notes in `docs/` record the development history and may describe earlier versions of results; the paper's statements are final. Paths such as `manuscript/...` in these notes are relative to the repository root, and commit hashes refer to the research repository in which the work was done.

## New in version 5

- `formalization/`: the Lean 4 project of Section 11.3. It has 65 modules, the build files and an axiom check. `formalization/README.md` states the theorems, the model and the relation to the paper, and gives the build instructions.
- `experiments/source_side_bounds.py` and its report `results/source-side-bounds.json`. They check:
  - the potentials and every fixed-number inequality of Section 11.2 (Proposition 11.1, Corollary 11.2, open question 3);
  - the flattening ranks;
  - the exact search behind Remark 11.5 (`A >= 2^24`).
- `experiments/rational_interpolation_audit.py`, updated. It now checks Lemma 9.1(b), Lü's separator in coordinates, in place of the `4M-3` weights of version 4.
- Working notes for Section 11.2: `docs/exponent-dimension-tradeoff.md` and `docs/multiway-general-flow-lower-bound.md`. Their scripts are `experiments/exponent_dimension_tradeoff.py` and `experiments/multiway_general_flow_bound.py`, with reports in `results/`. The paper's proofs are analytic and do not need these searches.
- `docs/manuscript-v5-revision.md`: the record of the revision, covering what changed, how the material was selected and how it was checked.

## From earlier versions

Version 4 added the Section 9 checks:
- `rational_seed_arithmetic_checks.py` and its report;
- the derivations `final-algorithm-bounds*.md`, `final-size-derivation.md`, `effective-search-bounds.md` and `exact-arithmetic-resolution.md`.

Version 3 added the four scripts that reproduce the numbers quoted in Sections 5–7 and 10, and the records `manuscript-v3-revision.md` and `manuscript-v3-verification.md`.

The other scripts, reports, tests and notes date from version 2, apart from section numbers in comments. The source hashes embedded in `results/multiway-finite-costs.json` match the included calculation dependencies. `SHA256SUMS` covers every file.

## Running the checks

Run all commands from this directory, with Python 3.11 or later. The finite-cost evaluator and its calculation dependencies use only the standard library:

```sh
python -m experiments.multiway_finite_costs
```

It prints the report to standard output in under a second. The printed report matches `results/multiway-finite-costs.json` except for the timing field `flow_and_log_bound_seconds`. The following scripts each run in a few seconds; `source_side_bounds.py` takes about 20 seconds:

```sh
python -I experiments/finite_table_checks.py
python -I experiments/extraction_a2_small_scale.py
python -I experiments/flows_row_maxima.py
python -I experiments/rounding_observed_loss.py
python -I experiments/rational_interpolation_audit.py
python -I experiments/rational_seed_arithmetic_checks.py --check
python -I experiments/source_side_bounds.py --check
```

- `finite_table_checks.py`: every number of Section 10, from `results/multiway-finite-costs.json`.
- `extraction_a2_small_scale.py`: the sign of `Delta_1` for `a = 2` (Section 7.4) and Example 7.2.
- `flows_row_maxima.py`: Example 5.2 and Remark 5.4. Needs NumPy.
- `rounding_observed_loss.py`: Remark 6.4. It also checks that its rounding matches `experiments/multiway_rounded_flow.py`.
- `rational_interpolation_audit.py`: the three parts of Lemma 9.1 and the leaf count behind Theorem 9.2, on small cases.
- `rational_seed_arithmetic_checks.py --check`: recomputes the checks of Section 9.4 and compares them with the saved report. Without `--check` it rewrites the report.
- `source_side_bounds.py --check`: recomputes the checks of Section 11.2 and Remark 11.5 and compares them with the saved report. Without `--check` it rewrites the report.

The working-note scripts reproduce their saved reports. `exponent_dimension_tradeoff.py` rewrites `results/exponent-dimension-tradeoff.json`, and `multiway_general_flow_bound.py` prints `results/multiway-general-flow-bound.json` to standard output.

The component tests require pytest, NumPy and SciPy:

```sh
python -m pytest -q tests
```

The Lean formalization builds with `elan` and an internet connection. Run these from `formalization/`; see `formalization/README.md` for details:

```sh
lake exe cache get
lake build
lake env lean PrintAxioms.lean
```

## Scope

This is not an implementation that expands or executes the complete coefficient maps of the construction or the seed of Theorem 9.2. The reports measure symbolic counts and logarithmic bounds, and they check the paper's identities and bounds on small cases. The Lean formalization proves `omega <= 9/4` over fields of characteristic zero for a simpler rational variant, without explicit constants. It does not formalize the quantitative results of Sections 8–11.
