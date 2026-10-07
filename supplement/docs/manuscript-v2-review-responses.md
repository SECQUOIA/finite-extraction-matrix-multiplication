# Revision and review record for the finite-extraction manuscript, v2

Date: 7 October 2026.

The revision replaces the main exact-denominator binary construction with a multiway construction using rational occupation flows and conserved integer rounding. The previous PDF and source archive are preserved in `manuscript/archive/v1/`; the v1 supplement is unchanged. Existing research files and saved experiments were preserved.

## Mathematical development

The paper now includes:

- Integral determinant bases and exact multiway fixed-type restrictions, including zero child frequencies.
- Tripling that fixes only the middle count, with sector count `binomial(t,m) 2^(t-m)` and no divisibility requirement.
- Threefold balancing with alternating row orientations and full-space post-separation maps.
- Rational occupation flows with both total visit count and logarithmic auxiliary cost bounded by `105 + 180(a-2)`.
- Integral circulation rounding at any positive integer scale, exact signed resource conservation, and a uniform weighted relative-entropy loss at most `4 J_a`.
- Complete copy, auxiliary, catalyst, and interpolation charges, followed by pooled recursion with exponent `log(r/m)/log(B/A)`.
- A new explicit convergence theorem: for `a >= 2^64`, `ell = ceil(log2 a)`, `K=a^3 ell`, `N=k=1`, `j=a ell`, the exponent lies strictly between `9/4` and `9/4 + 900/log(a)`, while `log(A) <= 181 a^5 ell^2`.
- A prescribed integer choice for any rational exponent allowance, followed by coefficient descent and a terminating rational-seed construction.

The last two quantitative statements were developed during this revision. Their constants were independently checked before inclusion. The relative source bound does not bound the final rational seed dimension, coefficient sizes, or preprocessing time. The exact binary certificate and its minimal denominator remain an appendix benchmark.

## Independent reviews and responses

The authoring agents for maps, flows, rounding, and quantitative bounds each used a separate mathematical checker. Three further cross-section audits reviewed the actual TeX:

- `manuscript-v2-maps-audit.md`: determinant and tripling maps, cyclic orientations, full target spaces, separator degrees, ledger, and copy/dimension counts. Two additional child reviews checked orientation and resource interfaces. No blocking issue found.
- `manuscript-v2-profile-audit.md`: least profile, absorption and occupation estimates, zero support, conserved rounding, entropy loss, coordinate count, finite costs, explicit constants, and the binary comparison. No major mathematical issue found.
- `manuscript-v2-finite-audit.md`: exactification, fixed-catalyst reuse, pooled padding recursion and all linear work, explicit constants, coefficient field, rational descent, and terminating seed generation. No fatal, major, or minor mathematical error found.
- `manuscript-v2-exposition-audit.md`: structure, definitions, claims, attribution, and explanation for an expert reader. No substantial exposition blocker after the corrections below.

The integration and exposition corrections are resolved:

1. The obsolete main binary cost section was replaced. Duplicate normalization labels and references to the omitted small-index obstruction were removed.
2. The binary appendix explicitly scopes its counts and uses a distinct catalyst notation. Denominator growth is not described as a barrier for the rounded construction.
3. The finite example table has five columns; the reset factorial bound explicitly omits zero counts.
4. The quantitative theorem calls `I` the number of active relations, not the number of sectors.
5. The abstract identifies the linear occupation bound as logarithmic auxiliary cost before integer scaling.
6. Parameter-selection statements explicitly take a positive rational allowance. The relative source dimension is consistently distinguished from the final rational seed dimension.
7. “Pooled recursion” is used consistently. The preprocessing limitation concerns time and coefficient bit size, not the proved parameter bound.
8. The introduction and discussion describe rounding and multiway relations as results already established in the paper, not as unresolved proposals.

Claude Opus 5.5 completed a fresh independent adversarial review of the revised mathematical chain, separate from both v1 review rounds and without reading the native v2 audits. Its report is `manuscript-v2-opus-review-round1.md`. It found no fatal or major error and checked all twelve requested bridges, including the explicit constants and rational seed. It reported four minor findings and one archival note, all addressed:

- **M1:** The historical comparison with unpooled batching now includes its recurrence and the corresponding exponent argument. The main pooled theorem does not depend on this comparison.
- **M2:** Composed maps use `Psi`, leaving `Phi` for the scalar cost bound; the composition appendix uses `nu_i` for type length, leaving `t` for the degeneration parameter; the rational seed test uses `alpha_eps/beta_eps` rather than reusing `p/q`.
- **M3:** Padding now produces a `B x B` array of blocks of side `ceil(n/B)`, stated explicitly.
- **M4:** The scalar-profile discussion now says that off-diagonal minimality uses shifted tripling beyond the row index, rather than claiming every shift is needed.
- **M5:** The unused obstruction file is marked as a legacy v1 appendix; its complete reference context is preserved in the v1 source archive and it is excluded from the v2 source package.

The finite-algorithm reviewer then checked the restored recurrence and all notation renames. No correction was needed: the unpooled exponent is at least the pooled exponent, which is strictly above 9/4 here, so its quadratic boundary case does not arise.

Opus suggested optional exact component computations. No additional experiments were run: the user authorized trusting the existing computational records, and the reviewers established no gap requiring a new experiment. The archived component checks remain in the supplement. Opus did not verify the literature, novelty claims, or archived numerical examples; those evidence scopes remain separate.

## Final parameter refinement

After the first Opus round, a further simplification reduced the rounding scale from `K=a^3 ell^2` to `K=a^3 ell`. The main theorem now uses `a >= 2^64`, retains `p < 9/4 + 900/log(a)`, and improves the relative source bound from `181 a^5 ell^3` to `181 a^5 ell^2`. The explicit allowance becomes `ell=max(64,ceil(1800/eps))`, `a=2^ell`. The finite examples retain their saved, larger rounding scales; the general construction allows either choice.

The changed loss estimate, with `t=log(a)>32`, is

```
(4J_a + T_1)/K
 <= [20 + 8t + (4t+2)/a^2]/ell
 <= [41/2 + 9t]/ell
 < 41/128 + 63/10.
```

Together with the profile loss `1/9`, this gives `Delta/K > 4t/3 - 7 >= t`. The numerator remains below `3t+850`, and subtraction of `9/4` leaves numerator `850+63/4=865.75<900`. The source bound is `a^5 ell^2 [180 + 2 log(2a)/(a ell)] <=181 a^5 ell^2`.

The quantitative author, its independent constant checker, and the profile/cost auditor each checked the refinement and found no remaining dependence on the larger normalization. A fresh, targeted Opus round checked these changed estimates and the responses to M1–M5. Its report, `manuscript-v2-opus-review-round2.md`, concludes that no mathematical fix is needed and that no step relies on the former scale. The general maps, ledger, entropy bound, and algorithm are unchanged. No numerical experiment was required or run.

The remaining editorial and release findings from that round are resolved:

- **R1:** The position index in the composition appendix is now `theta`, distinct from the type length `nu_i`.
- **R2:** The discussion now gives the same precise shifted-tripling scope as the profile section.
- **P1:** Both current archives were regenerated after the final edits. Every archived source file matches the working manuscript; the source package builds in a fresh directory.
- **O1–O2:** The unpooled recurrence uses `cost(n)`, avoiding the reset-total symbol `T`. The repository README records the improved logarithmic bound while preserving the historical research-note bound.

The Opus reports record the snapshots they reviewed. Their observations about stale archives and wording describe those snapshots; this response record documents the final corrections.

## Literature attribution

All literature research for the revision was assigned to GPT Luna with maximum reasoning, using the local `$lit` workflow. The literature review identified direct antecedents for the integral determinant filtration (Maakestad), circulation integrality (Hoffman–Kruskal), algorithmic flow rounding (Kang–Payor), absorbing-chain occupation systems (Grinstead–Snell), the Doob transform (Levin–Peres), cyclic balancing (Christandl–Vrana–Zuiddam), and relative-entropy bounds for fixed-total probability quantization (Böcherer–Geiger). The paper credits those ingredients and limits its claims to the concrete convolution maps, signed resource accounting, quantitative estimates, and complete finite construction. The Le Gall 2014 DOI was corrected to the actual tensor-powers paper. Inspection of Böcherer–Geiger's original Eq. (42) also corrected an initial attribution: that inequality bounds the relative-entropy minimizing fixed-total approximation, not every floor/ceiling approximation. The manuscript now states that scope explicitly and distinguishes its own potentially nonoptimal, unequal-total flow counts.

The detailed search scope, acquisition limitations, source notes, and knowledge-base checks are documented in the v2 literature report. No first-general-construction claim or novelty claim for classical tools is made.

## Verification and production

No research experiment or existing computational test was rerun. The three finite examples are taken from `results/multiway-finite-costs.json`. All seven source hashes recorded in that report were checked against the current files and matched.

The 35-page paper compiled with pdfLaTeX/BibTeX through latexmk without warnings, missing references, or overfull boxes. All 105 labels are unique and resolve. The layout was inspected as rendered pages. The source ZIP was extracted into a fresh temporary directory and built there successfully, also without warnings. Archive integrity checks cover every included file with SHA-256 hashes. These checks concern document production and artifact integrity; the mathematical reviews are detailed above and are not formal verification or journal peer review.
