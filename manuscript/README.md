# Explicit finite extraction from convolution profiles for matrix multiplication

The revised manuscript gives a self-contained finite construction from convolution tensor relations. For every positive rational allowance above exponent 9/4, it specifies integer parameters, an exact relative multiplication scheme, a coefficient field, and a terminating construction of a rational bilinear seed. It does not claim a fixed seed of exponent exactly 9/4 or practical performance.

The revision integrates multiway determinant restrictions, threefold orientation balancing, tripling with only the middle count fixed, rational occupation flows, circulation rounding, and pooled recursion. An explicit rate theorem gives exponent less than `9/4 + 900/log(a)` for `a >= 2^64`, with `log(A) <= 181 a^5 ceil(log2(a))^2`. Here `log` denotes the natural logarithm. The dimension bound concerns the relative scheme's source side `A`, rather than the final rational seed dimension or coefficient-generation complexity. The exact binary certificate and its denominator bound are retained as an appendix comparison.

## Files and build

`main.tex` is the entry point. The section files and `references.bib` must be kept in the same directory.

The repository root contains [finite-extraction.pdf](../finite-extraction.pdf) and [finite-extraction-supplement-v2.zip](../finite-extraction-supplement-v2.zip), the versioned supplement cited by the revised paper. The supplement is also unpacked in [supplement/](../supplement/). It includes supporting scripts, raw reports, component tests, derivations, review records, and integrity hashes. Its research notes preserve earlier project stages; the manuscript supersedes their presentation of the completed construction.

Build with a standard TeX Live installation containing pdfLaTeX, BibTeX, latexmk, Latin Modern, microtype, natbib, and xurl:

```sh
make -C manuscript
```

The PDF is written to `manuscript/finite-extraction.pdf`; intermediate files stay in the ignored `manuscript/build/` directory. From inside this directory, use `make`.

## Scope of the evidence

The finite examples use saved exact-arithmetic interval certificates; no research experiments were rerun during manuscript revision.

Relevant supporting files in the repository are:

- `supplement/experiments/multiway_determinant.py` and `supplement/results/multiway-determinant.json` for determinant bases and exact type maps.
- `supplement/experiments/cyclic_profile_extraction.py` and `supplement/results/cyclic-profile-extraction.json` for orientation bookkeeping and partial-middle tripling.
- `supplement/experiments/multiway_profile_flows.py` and `supplement/results/multiway-profile-flows.json` for rational occupation flows.
- `supplement/experiments/multiway_rounded_flow.py` and `supplement/results/multiway-rounded-flow.json` for conserved integer counts.
- `supplement/experiments/multiway_finite_costs.py` and `supplement/results/multiway-finite-costs.json` for finite examples and their rational interval certificates.
- `supplement/experiments/general_profile_extraction.py` and `supplement/results/general-profile-extraction.json` for the exact binary certificate.

The paper specifies complete maps as mathematical algorithms. There is no implementation that expands the full coefficient arrays at the claimed exponent allowances.

The mathematical and editorial reports, Opus reviews, literature audit, and responses are included under `supplement/docs/manuscript-v2-*.md`.
