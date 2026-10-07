# Supplement to the revised finite-extraction manuscript (v2)

This archive preserves supporting code, saved reports, component tests, mathematical derivations, and review records for the revised paper. The paper contains the proofs; the numerical reports are supporting exact-arithmetic certificates. The research notes preserve the development history and may describe earlier versions of results. Read the manuscript for the final statements.

No experiments were rerun for this revision. The source hashes embedded in results/multiway-finite-costs.json match the included local calculation dependencies. SHA256SUMS covers each archived file.

The finite-cost evaluator and its calculation dependencies use Python's standard library. From this archive's root, `python -m experiments.multiway_finite_costs` reproduces that report. This command is documented for reproducibility and was not run during revision. Component tests require pytest. Some older comparison scripts may have additional research dependencies; their original source files state their imports.

This is not an implementation that expands or executes the complete coefficient maps in the claimed asymptotic construction. The archived reports measure symbolic counts and logarithmic bounds, not the execution of the represented matrix multiplication algorithms.
