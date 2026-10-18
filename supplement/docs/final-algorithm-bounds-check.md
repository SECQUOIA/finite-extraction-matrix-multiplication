# Second check and revision of the version 4 additions

Date: 17 October 2026. Scope: the new paper text of commit `e9aaa8b`
("Bound final algorithm resources and arithmetic"), its docs and its two
scripts. Result numbers refer to the revised paper (Section 9).

## Verdict

No fatal or major error was found. Every new theorem holds as stated,
with its proof correct up to the minor gaps listed below, all of which are
now fixed. Six checkers worked independently, each with its own exact
arithmetic rather than the repository scripts:

| Area | Main checks | Verdict |
|---|---|---|
| Rational interpolation and rational variant | Separator applied literally to random sector tensors, `M = 1..6`: same polynomial, degree `(M-1)^2`, same constant term. `4M-4` nodes provably insufficient. Exactification on tensor powers. `C(r,b)` decompositions for `r, b <= 4`. Copy overhead against Steps 1-6 of Theorem 8.1. All roots of unity of `eq:cyclotomic-order` replaced. | Sound, minor issues |
| Explicit seed and uniform algorithm | Parameters against Theorem 8.1 and Corollary 8.2. Pooled recursion simulated exactly for 10 toy schemes and all `n <= 20000` (largest leaf-count ratio to the bound 0.24). Block-recursion operation counts for 7 `(d, R)` pairs, `n < 5000` (largest ratio 0.84). Selection argument. | Sound, minor issue |
| Preprocessing cost | Hostile-referee pass over every count: envelopes, factorial arguments, leg dimensions, stage count, unrolling, bit growth (`2t+1` rule tested exhaustively up to 6-bit heights), `O(2^(8S))`. | Sound, minor issue |
| Bit complexity and precision | `R > d_0^2`, integer scaling, bit lengths, factor count `chi`, `Upsilon >= d_0`, significand formula. Strassen, rescaled and conjugated rational seeds, classical seeds: exact integer runs and simulated 8- to 24-bit rounding; the per-path factor counter reached exactly `chi`. | Sound, minor issue |
| Docs, scripts, build | All doc numbers against the paper. Both scripts pass and reproduce the saved report byte for byte. Full test suite of the research repository: 617 passed, 60 subtests. Clean build. | Sound, two minor issues |
| Writing and notation | New text against the style and notation rules of the version 3 rewrite. | Many exposition items |

A revised draft was then checked by a math-preservation reviewer, who
confirmed every change, and by a cold-read referee.

## Minor problems found and fixed

- **Step 2 of Theorem 8.1.** The text said Step 2 "still holds" for the
  rational variant. Its chain uses `L_i/M_i < 2`, which fails for
  `4M_i - 3`. Only its conclusion (at most 1) carries over, and that is all
  Step 5 uses. The text now says so.
- **Rate of the rational variant.** It stated only `2 < p`; the bound
  `9/4 < tau_a <= p` still holds and is now stated, with `B > A`.
- **Cost model of Corollary 9.7.** The seed's coefficients depend on `n`, so
  the model must count operations on them, needs characteristic zero
  (rational denominators), and must allow divisions. All three are now
  stated, with the `O(n)` conversion of the coefficients.
- **Dense-assembly count in Theorem 9.3.** The stage count and the leg
  bound were asserted without derivation. The stage tally is now written
  out, the leg bound is `10a^2`, and the circulation step cites the paper's
  own augmentation count instead of an uncited capacity-independent bound.
  The tally is safe because of its enormous slack; no implementation
  checks it.
- **Hypotheses in Section 9.4.** The integer and precision propositions now
  state `n x n` inputs and cropping; the integer proposition names the
  scaled integer recursion it analyses.
- **Notation.** The new text reused global symbols: `omega_s` (the
  exponent), `C` (the convolution tensor), `delta` (three meanings), `q`
  (two), `s` (three), `r, m` (row index and counts), `A, B` (scheme sides
  and input matrices), `L`, `H`, `D`, `beta_eps` (already used in
  Corollary 8.7). They are now `varpi`, `Xi`, `eps'`, `n_*`, `r_*^Q`,
  `X, Y`, `c_den`, `c_coef`, `b_eps`, `b_in` and similar, listed in
  Appendix D.
- **Stale statements.** The paper said in several places that the
  construction's coefficients lie in a cyclotomic field, or that no seed
  or preprocessing bound is given. Those places now mention the rational
  variant and Theorems 9.2-9.3.
- **Build artifacts (research repository).** LaTeX build files tracked in `manuscript/`
  (`main.aux`, `main.bbl`, ...) make `latexmk` reuse a stale bibliography,
  so a new citation can stay undefined while `make` succeeds. They are now
  untracked and ignored.

## Exposition changes

The new material is one section, "Explicit bounds for a rational seed",
ordered so that every result comes after what it uses: the rational
variant (9.1), the explicit seed (9.2), the preprocessing cost (9.3), a new
Lemma 9.4 collecting `R > d_0^2` and the block-recursion cost (previously
proved twice), the integer and precision propositions, and the algorithm
for all sizes (9.5). Proofs start with their idea. The scope caveats are
stated once, in Section 1.6. The abstract and introduction state the new
results directly. `Bini and Lotti (1980)` is now cited where the
precision bound is compared with earlier work; both it and `DDHK07` were
checked against Crossref.

## Not done

- No one checked the dense-assembly stage tally against an implementation.
- The suggested closed-form bound of `d_0` in terms of `eps` was not added;
  instead the abstract and introduction no longer call the bounds closed
  functions of `eps`. They are computable from `eps`.
- The fraktur names of Theorem 9.3 were kept.
