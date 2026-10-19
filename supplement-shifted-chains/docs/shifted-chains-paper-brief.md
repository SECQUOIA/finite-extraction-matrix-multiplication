# Brief for the follow-up paper on shifted chains

Date: 18 October 2026. This brief fixes the content, structure, notation
and statements of the follow-up paper. Writers must follow it. If a
statement here turns out to be wrong or unprovable as written, do not
silently change it: fix it in your section, and report the change and the
reason in your return value.

## 1. The paper

- **Title:** *A singly exponential construction of matrix multiplication
  algorithms with exponent approaching 9/4*.
- **Directory:** `manuscript-shifted-chains/`. `main.tex` (already written)
  inputs `abstract.tex`, `introduction.tex`, `preliminaries.tex`,
  `stages.tex`, `chains.tex`, `seeds.tex`, `examples.tex`, `limits.tex`,
  `open-questions.tex`, `appendix-lower.tex`, `appendix-coefficients.tex`
  and uses `references.bib`. Build with `make` in that directory (PDF
  `shifted-chains.pdf`). Macros available: `\Q \C \N \R \MM \eps \restr`
  (restriction, ⪰) `\degen` (degeneration, ⊵) `\nK \nO \nmid \diag`;
  theorem environments as in v5. Add macros only to `main.tex`, and only
  if needed.
- **No author names**, like v5.
- **Predecessor ("v5")**: *A finite construction of matrix multiplication
  algorithms with exponent approaching 9/4*, version 5, 18 October 2026,
  LaTeX in `manuscript/*.tex`, PDF `manuscript/finite-extraction.pdf`
  (79 pages). Bib key `FinCon26` (no URL; the paper does not identify its
  authors). Cite it as "[FinCon26]" via `\citep{FinCon26}` or "the
  preceding paper~\citep{FinCon26}"; never `\citet{FinCon26}` (it would
  print "Anonymous"). When citing a v5 result, use v5's numbers, e.g.
  "\citep[Lemma~2.4]{FinCon26}". Look the numbers up in
  `manuscript/build/main.aux` or the PDF; do not guess.
- **Length target:** 30–38 pages in total. The paper must be readable on
  its own for a reader who knows tensor rank and the laser-method
  literature, and who has v5 at hand for the cited lemmas.

## 2. The story (what the paper says)

v5 constructs, for every rational ε > 0, an exact rational bilinear
algorithm with exponent below 9/4 + ε, but its source side is doubly
exponential in 1/ε, and doubly exponential is necessary within its
construction (v5 Corollary 11.2). v5's open question 2 asks for a finite
construction with log A polynomial in 1/ε. This paper gives one.

The new ingredient is the **shifted chain**: for an arity d ≥ 2 and a
child length 1 ≤ c < b, put h = b − c and
Q(F_0, …, F_{d−1}) = Σ_j z^{jh} F_j on d polynomials of length b. It
splits C(r,b) ⊗ B_X(d) into d − 1 equal kernel sectors C(r,c) and one
quotient sector C(r, b⁺), b⁺ = db − (d−1)c, block-triangularly. A crop
and the reset (OpenAI's shifted tripling) turn the quotient into two
ordinary copies of C(r,c) and one middle copy C(r,c)^{(23)}. Fixing the
class counts deletes all cross terms. With both cyclic signs paired, a
stage maps Q_{r,b} to Q_{c,r} with gain about (d+2)/d per factor and
auxiliary MM_{d^{2N}}. Stages run in sequence, each exactified
separately, with no catalyst, from a source pair down to a terminal
(1, t). The dimensions shrink geometrically. An exact **arity ramp**
(arities 3j−1, 3j along the diagonal) reproduces v5's diagonal profile
F(R,R) with zero rounding slack, and a constant-arity **bulk** follows.

Results:

1. **Main theorem** (Section 4): for rational 0 < ε ≤ 1, an explicit
   relative scheme over Q with 9/4 < p < 9/4 + ε/2 and
   log A < 3·10^9 ε^{−9/2} log^3(4096/ε), B ≤ A², m_* ≤ A⁶, and
   r_* ≤ A^{35/4} (if the writer cannot verify 35/4 from the seeds note,
   use A^{17}). Corollary: p < 9/4 + ε with
   log A < 1.4·10^8 ε^{−9/2} log^3(2048/ε) for ε ≤ 1/2.
2. **Seeds and one algorithm** (Section 5): an exact rational bilinear
   algorithm for n × n matrices with fewer than n^{9/4+ε} products for
   every n ≥ n_0, with log n_0 < 2.1·10^{11} ε^{−11/2} log^3(4096/ε);
   coefficient bit lengths and preprocessing cost singly exponential; one
   algorithm for all n with n^{9/4+δ(n)} steps,
   δ(n) = O((log log n)^{6/11} (log n)^{−2/11}), against v5's
   O(1/log log n).
3. **Finite examples** (Section 6): certified witnesses, e.g. below 2.5
   with 33,379 decimal digits of A, below 2.3 with 12,371,380 digits,
   below 2.26 with 48,859,824,830 digits, against v5's 2.35·10^{11}
   digits for 2.6728. The advantage is near 9/4, not at moderate quality.
4. **Limits** (Section 7): within the construction (a) p > 9/4 always,
   even with arbitrary preserving per-stage auxiliary compression (Hankel
   flattening); (b) the resource order is optimal (exact form to be fixed
   by the limits writer from the Phase A results; see §6 below).

**Credit, stated plainly** (from the literature check):
- for h = 1 the map is known: for d = 2 it is the determinant sequence in
  the proof of OAI26 Lemma 4.1; for general d its kernel is the first step
  F¹ of the determinant (Clebsch–Gordan) filtration (Maakestad23 Lemma 2.5;
  v5 Section 4.1, which requires b ≥ d). For h ≥ 2 it is the substituted
  form (u′,v′) = (u^h, v^h); we found no source for it ("to our knowledge").
  What is new is keeping F¹ whole as d − 1 equal sectors, the shift h ≥ 2,
  the acyclic catalyst-free schedule, the ramp, and all finite bounds;
- the reset is the partition in the proof of OAI26 Lemma 4.2 with
  (a,h) = (r,c) (also Uzn26 Lemma 2.1(3)); v5 Lemma 4.5 covers only c = r;
- the separator with 2M−1 copies and degree ≤ M−1 is Lü's (Lu26
  Proposition 2.1; v5 Lemma 9.1(b));
- the ramp gain equals v5's F(R,R), and each ramp pair is a step of
  OAI26's diagonal recursion (5.1); F(R,R) ≥ R^{4/3} is OAI26 Lemma 5.1;
- every stage identity fits Filmus's block-identity criterion (Fil26
  Theorem 1.1, identity (1.2)), which gives exponents but no sizes;
- OAI26Comp (auxiliary group tensors, ω < 2.258) is a different method;
- apart from v5, no work gives explicit sizes near 9/4; OAI26, Nav26a/b,
  Zui26, Lu26, Uzn26 and Fil26 prove existence only.
Do not cite Sun's arXiv 2610.13971, Stockham 1966 or Kowalski 2014.

## 3. Notation (use exactly this)

| Symbol | Meaning |
|---|---|
| C(r,b), B_X(d), MM_d, S^±_{r,b}, Q_{r,b} = S^+_{r,b} S^−_{r,b} | as in v5 Section 2 |
| ⪰ (`\restr`), ⊵ (`\degen`) | restriction, degeneration (v5) |
| d (or d_i) | arity of a stage (level) |
| (r,b) → (c,r) | a stage: parent C(r,b), child length c; next pair is (c,r) |
| h = b − c, b⁺ = db − (d−1)c | shift and quotient length |
| (\nK, \nO, \nmid) | class counts of a type: kernel, outer, middle |
| N | number of factors per sign at each stage (type width) |
| k | tensor power used for exactification |
| M (or M_i) | number of sectors of a stage type |
| E = 1 + 6k(M−1) | exactification charge of a stage (Lü's separator) |
| J | number of stages; i = 1..J |
| (r_1, b_1) | source pair; s = r_1 + b_1 − 1 its evaluation size |
| (1, t) | terminal pair |
| A, B, r_*, m_*, p | source side, target side, copy counts, pooled exponent (v5 Def. 2.3) |
| Φ = log(2 r_*/m_*)/log(B/A) | certified fixed-batch quantity (v5 (10.1)); p ≤ Φ |
| D, R = 8D, L | bulk arity, ramp diagonal, number of bulk stages |
| μ, g_D = log((D+2)/D), ω_D = 3 log μ / g_D | bulk ray, gain, ideal exponent |
| F | v5's least profile |
| Ψ(r,b) = r² + 4rb + b² − 2r − 2b − 1/6 | potential of the compression limit |
| n_0 | seed side; n is the input side of the final algorithm |
| \mathcal D | common denominator of coefficients |

Do not use P for anything except a v5 profile if needed. Do not use L for
the quotient length. Use "stage" for one application of the relation
(the notes also say "level"); use "sector" as in v5.

## 4. Section plan, labels and owners

Labels must be exactly these so that cross-references resolve across
files. Add further labels with the same prefixes as needed.

1. `introduction.tex` (`sec:intro`) — 3–4 pages. Results (Theorems 1.1–1.4
   stated informally with references to the formal statements), comparison
   with v5, the idea in one page, relation to other work with the credits
   above, organization. Also `abstract.tex` (≤ 200 words).
2. `preliminaries.tex` (`sec:prelim`) — 1.5–2.5 pages. What is used from
   v5, recalled briefly with exact v5 numbers: tensors and restrictions,
   (2.1)–(2.8) (MM, B_X, coset products, C(r,b) and its rank, S^±, Q),
   degenerations, Lemma 2.1 (composition), Lemma 2.2 (exactification),
   Definition 2.3 (relative scheme), Lemma 2.4 (pooled recursion), sectors
   sharing the first leg and the separator (v5 Section 4, Proposition 4.6,
   Remark 4.7), Lemma 9.1 (rational interpolation incl. Lü's separator),
   and type restrictions (v5 Lemma 4.3).
3. `stages.tex` (`sec:stages`) — 3.5–4.5 pages. `lem:shifted-chain`
   (Lemma A, with explicit unimodular bases and the off-diagonal formula,
   a small example, the h = 1 credit), `lem:reset` (Lemma B, all r,c ≥ 1,
   credited to OAI26 Lemma 4.2's proof), `lem:stage-types` (Lemma C,
   weights 2/1/0, sector count M, crop caveat remark), `prop:stage`
   (Proposition D: six orientations, paired inventory Q, degree ≤ 6(M−1)
   with Lü's separator over Q), `cor:exact-stage` (E = 1+6k(M−1), over Q
   via v5 Lemma 9.1(c)), `prop:chain-counts` (Proposition E: A, B, r_*, m_*
   for a chain with terminal (1,t); general (N_i,k_i) with N_i k_i constant
   may be remarked), `rem:field-scope`. Source: `docs/shifted-chains-check-maps.md`
   (incl. its adversarial review) and `docs/shifted-chains-check-certificates.md`
   §2.
4. `chains.tex` (`sec:chains`) — 4.5–5.5 pages. `def:legal-stage`,
   `lem:smallest-parent`, `lem:ramp` (zero slack; gain = F(R,R); cite OAI26
   Lemma 5.1 for F(R,R) ≥ R^{4/3}), `lem:bulk-potential`, `lem:ideal-gap`
   (asinh/sinh form), `lem:defect`, `lem:types`, `lem:profile-potential`
   (Lemma P: for every legal stage, d F(r,b) ≥ (d+2) F(c,r), with equality
   on ramp stages; hence p > 9/4 for every chain scheme; this also fixes the
   sign issue in Step 3), `thm:main` (with all charges in a table),
   `cor:main-eps`, remarks: Φ versus p and why ε/2; robustness to v5's
   Fourier separator; constant arity without the ramp loses a log.
   Source: `docs/shifted-chains-check-upper.md` (incl. adversarial review).
5. `seeds.tex` (`sec:seeds`) — 4–5 pages. `lem:resources` (m_* = B³,
   2A ≤ B ≤ A², r_* ≤ A^{35/4}, n_* and Ξ bounds), `thm:seed` (explicit seed,
   n_0 = (Ξ+1)^{⌈2/ε⌉}), `prop:depth`, `prop:coefficients` (common
   denominator, bit lengths ≤ A^{24}, generation ≤ A^{700} bit operations;
   proof uses the layer list written out in `appendix-coefficients.tex`,
   `sec:coefficients`), `rem:precision` (one batch only; recursion needs
   more), `lem:pooled-constants`, `thm:uniform` (Algorithm U, δ(n) rate),
   remarks: the 1/ε factor of unrolling (restricted to ε ≤ 3/4 and to the
   number of executed leaf products), seed route gives only 2/13, comparison
   with v5 Remark 9.8. Source: `docs/shifted-chains-check-seeds.md` (incl.
   adversarial review).
6. `examples.tex` (`sec:examples`) — 1.5–2.5 pages. `tab:witnesses`, the
   comparison with v5 Table 2 using v5's computed Φ (fair points: 280 and
   4,653 digits; include digits of B), the remark that at moderate quality
   other constructions are smaller, Φ − p values, and the small-source
   statement `prop:small-sources` if Phase A keeps it. Source:
   `docs/shifted-chains-check-certificates.md`, `docs/shifted-chains-check-gate.md`,
   Phase A results, `results/shifted-chain-certificates.json`.
7. `limits.tex` (`sec:limits`) — 4–6 pages, with long proofs moved to
   `appendix-lower.tex` (`sec:lower-proof`). `def:class` (the class of
   chain schemes, block form, explicit list of what is fixed),
   `thm:hankel`, `cor:compression-limit` (p > 9/4 with arbitrary preserving
   per-stage auxiliaries), `rem:ordinary-only` (u = 1 case: p ≥ 3 without
   middle sectors), the resource lower bound `thm:lower` in the form fixed
   by Phase A, `lem:recycling` and its consequences (if confirmed), scope
   paragraph. Source: `docs/shifted-chains-check-hankel.md`,
   `docs/shifted-chains-check-lower.md` (incl. R.3–R.4), Phase A results.
8. `open-questions.tex` (`sec:open`) — ≤ 1 page. Smaller finite sizes
   (compression, recycling, cheaper sources); auxiliaries coupling
   orientations or stages; removing the 1/ε factor of seeds; positive
   characteristic (local maps work over every field; separators and
   exactification are charged over Q); practical sizes; formalization.

## 5. Style

- Follow v5's style: precise, plain, short sentences, every symbol defined
  before use, each proof complete or an explicit citation of a proved v5
  result. No "sketch" for any stated theorem; if something can only be
  sketched, make it a remark and say so.
- Do not mention AI agents, review rounds, "Sol", research notes or the
  repository's round numbers in the paper.
- No overclaiming: say "within the construction" for every limit, "to our
  knowledge" for novelty of the h ≥ 2 map, and "astronomically large" for
  sizes. State fields precisely: local maps over every field; paid
  relations over Q (characteristic zero).
- Numbers quoted in the paper must come from a proof in the paper or from
  `results/shifted-chain-certificates.json`; give the supplement script
  name when a number is computer-certified.
- Use `\citep` with v5's own result numbers. BibTeX keys: see
  `docs/shifted-chains-references-draft.bib` (the integrator builds
  `references.bib` from it).

## 6. Open decisions handled in Phase A

- The source side A depends on accounting: produced MM factors can supply
  later auxiliaries ("forward recycling"), which leaves r_*, m_*, p
  unchanged and shrinks A and B. Phase A fixes the robust form of the
  lower bound (on m_* or r_*, and on log(B/A)) and whether recycling is
  presented as a lemma.
- Whether the small-source barrier (A ≤ 2^128 ⇒ p ≥ 2.97696…) survives
  recycling; if not, the paper states it only under explicit accounting or
  drops it.
