# Supplement to the finite-extraction manuscript (v3)

This supplement contains the supporting code, saved reports, component tests, mathematical derivations and review records for version 3 of the paper, *A finite construction of matrix multiplication algorithms with exponent approaching 9/4*. The paper contains the proofs. The numerical reports are supporting exact-arithmetic certificates. The research notes in `docs/` record the development history and may describe earlier versions of results; the paper's statements are final.

Version 3 rewrites the paper for clarity; its mathematics is that of version 2. Compared with supplement version 2, this version adds:

- four scripts that reproduce the numbers quoted in the paper (listed below);
- `docs/manuscript-v3-verification.md`: the independent verification reports on the version 2 mathematics;
- `docs/manuscript-v3-revision.md`: the revision record, with a summary of the verification, the fixes and the rewrite process.

The other scripts, reports, tests and notes are unchanged from version 2. The source hashes embedded in `results/multiway-finite-costs.json` match the included calculation dependencies. `SHA256SUMS` covers every file.

## Running the checks

Run all commands from this directory. The finite-cost evaluator and its calculation dependencies use only Python's standard library (Python 3.11 or later):

```sh
python -m experiments.multiway_finite_costs
```

It prints the report to standard output in under a second. The printed report matches `results/multiway-finite-costs.json` except for the timing field `flow_and_log_bound_seconds`. The scripts added in version 3 each run in a few seconds and print the numbers that the paper quotes:

```sh
python -I experiments/finite_table_checks.py
python -I experiments/extraction_a2_small_scale.py
python -I experiments/flows_row_maxima.py
python -I experiments/rounding_observed_loss.py
```

- `finite_table_checks.py`: every number of Section 9, from `results/multiway-finite-costs.json`.
- `extraction_a2_small_scale.py`: the sign of `Delta_1` for `a = 2` (Section 7.4) and Example 7.2.
- `flows_row_maxima.py`: Example 5.2 and Remark 5.4. Needs NumPy.
- `rounding_observed_loss.py`: Remark 6.4. It also checks that its rounding matches `experiments/multiway_rounded_flow.py`.

The component tests require pytest, NumPy and SciPy:

```sh
python -m pytest -q tests
```

## Scope

This is not an implementation that expands or executes the complete coefficient maps of the construction. The reports measure symbolic counts and logarithmic bounds, not the execution of the represented matrix multiplication algorithms.
