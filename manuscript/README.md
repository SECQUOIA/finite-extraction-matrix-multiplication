# Explicit finite extraction from convolution profiles for matrix multiplication

The manuscript gives a self-contained finite construction from the repository's convolution relations. It includes an exact integer procedure for selecting the parameters, an explicit coefficient field, and a construction of rational bilinear seeds for every fixed positive allowance above exponent 9/4. It does not claim a fixed seed of exponent exactly 9/4 or practical performance.

## Files and build

`main.tex` is the entry point. The section files and `references.bib` must be kept in the same directory.

The repository root contains `finite-extraction-supplement-v1.zip`, the versioned supplement cited by the paper. Its contents are also unpacked in [supplement/](../supplement/). It includes supporting scripts, raw reports, component tests, derivations, and integrity hashes. Its research notes preserve earlier project stages; the manuscript supersedes their presentation of the completed construction.

Build with a standard TeX Live installation containing pdfLaTeX, BibTeX, latexmk, Latin Modern, microtype, natbib, and xurl:

```sh
make -C manuscript
```

The PDF is written to `manuscript/finite-extraction.pdf`; intermediate files stay in the ignored `manuscript/build/` directory. From inside this directory, use `make`.

## Scope of the evidence

The finite example and cost bounds use the existing exact-arithmetic calculations; no research experiments were rerun during manuscript preparation.

Relevant supporting files in the repository are:

- `supplement/experiments/general_profile_extraction.py` and `supplement/results/general-profile-extraction.json` for the rational certificate and type counts.
- `supplement/experiments/small_profile_extraction.py` and `supplement/results/small-profile-extraction.json` for the finite example and rational logarithm enclosures.
- `supplement/experiments/finite_constructions.py` and `supplement/results/finite-constructions.json` for the separator calculations.
- `supplement/experiments/profile_bounds.py`, `supplement/results/profile-extremal.json`, and `supplement/results/profile-finite-costs.json` for the scalar profile.
- `supplement/docs/extraction-cost-limits.md` for the recorded exact-interval calculation behind the small-index schedule obstruction.

The new integer selection procedure and rational-seed corollary are mathematical algorithms specified in the paper. There is no implementation that expands the complete coefficient maps.
