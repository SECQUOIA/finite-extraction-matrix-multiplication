# Supplement to the finite-extraction manuscript (v4)

This supplement contains the supporting code, saved reports, component tests, mathematical derivations and review records for version 4 of the paper, *A finite construction of matrix multiplication algorithms with exponent approaching 9/4*. The paper contains the proofs. The numerical reports are supporting exact-arithmetic certificates. The research notes in `docs/` record the development history and may describe earlier versions of results; the paper's statements are final. Paths such as `manuscript/...` in these notes are relative to the repository root, and commit hashes refer to the research repository in which the work was done.

Compared with supplement version 3, this version adds, for the new Section 9:

- `experiments/rational_interpolation_audit.py`: exact checks of the interpolation identities of Lemma 9.1 and of the pooled-recursion counts used in Theorem 9.2;
- `experiments/rational_seed_arithmetic_checks.py` and its report `results/rational-seed-arithmetic-checks.json`: exact checks of denominator clearing, intermediate bit lengths and the forward-error bound of Section 9.4 on a rescaled Strassen seed;
- `docs/final-algorithm-bounds.md`: summary of the new results;
- `docs/final-algorithm-bounds-review.md` and `docs/final-algorithm-bounds-check.md`: the independent review and the second check, with the fixes made;
- `docs/final-size-derivation.md`, `docs/effective-search-bounds.md` and `docs/exact-arithmetic-resolution.md`: the working derivations behind Section 9.

Supplement version 3 added the four scripts that reproduce the numbers quoted in Sections 5-7 and 10, and the records `docs/manuscript-v3-verification.md` and `docs/manuscript-v3-revision.md`. The other scripts, reports, tests and notes are unchanged from version 2, apart from section numbers in comments. The source hashes embedded in `results/multiway-finite-costs.json` match the included calculation dependencies. `SHA256SUMS` covers every file.

## Running the checks

Run all commands from this directory, with Python 3.11 or later. The finite-cost evaluator and its calculation dependencies use only the standard library:

```sh
python -m experiments.multiway_finite_costs
```

It prints the report to standard output in under a second. The printed report matches `results/multiway-finite-costs.json` except for the timing field `flow_and_log_bound_seconds`. The following scripts each run in a few seconds:

```sh
python -I experiments/finite_table_checks.py
python -I experiments/extraction_a2_small_scale.py
python -I experiments/flows_row_maxima.py
python -I experiments/rounding_observed_loss.py
python -I experiments/rational_interpolation_audit.py
python -I experiments/rational_seed_arithmetic_checks.py --check
```

- `finite_table_checks.py`: every number of Section 10, from `results/multiway-finite-costs.json`.
- `extraction_a2_small_scale.py`: the sign of `Delta_1` for `a = 2` (Section 7.4) and Example 7.2.
- `flows_row_maxima.py`: Example 5.2 and Remark 5.4. Needs NumPy.
- `rounding_observed_loss.py`: Remark 6.4. It also checks that its rounding matches `experiments/multiway_rounded_flow.py`.
- `rational_interpolation_audit.py`: Lemma 9.1 and the leaf count behind Theorem 9.2, on small cases.
- `rational_seed_arithmetic_checks.py --check`: recomputes the checks of Section 9.4 and compares them with the saved report. Without `--check` it rewrites the report.

The component tests require pytest, NumPy and SciPy:

```sh
python -m pytest -q tests
```

## Scope

This is not an implementation that expands or executes the complete coefficient maps of the construction or the seed of Theorem 9.2. The reports measure symbolic counts and logarithmic bounds, and check the new identities and bounds on small cases.
