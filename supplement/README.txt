Supplement to Explicit finite extraction from convolution profiles for matrix multiplication
Version 1, 7 October 2026

This bundle preserves the existing scripts, reports, component tests, and
research derivations supporting the manuscript. No numerical or timing
experiments were rerun to prepare the manuscript or this bundle.

The main proof is in the manuscript. The supplementary notes record earlier
stages of the project and can contain older statements about what was then
unimplemented or unresolved. The manuscript supersedes their exposition,
including its exact integer parameter selection and rational seed corollary.

Contents:
- experiments/: exact tensor-map and rational-count calculations.
- results/: archived outputs, including rational logarithm enclosures.
- docs/: derivations and the recorded exact-interval calculation for the
  small-index schedule lower bound (extraction-cost-limits.md).
- tests/: existing component checks; these do not expand the composed maps.
- SHA256SUMS: integrity hashes for every included repository file.

Python 3.11 or later is sufficient for the exact construction reports.
Optional profile linear programs require NumPy and SciPy; component tests
require pytest. These are reproduction instructions, not a claim that the
experiments were rerun for the paper. From this directory, examples are:

  python -m experiments.general_profile_extraction
  python experiments/small_profile_extraction.py
  python experiments/finite_constructions.py --max-blocks 8
  python experiments/profile_bounds.py --max-index 64

Use the included raw reports to inspect the stored results without running
anything. The astronomical final coefficient maps are specified by the
paper's finite construction and are not expanded in this supplement.
