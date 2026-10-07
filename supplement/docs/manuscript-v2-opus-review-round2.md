# Opus review of manuscript v2, round 2: refined parameters and responses

Reviewer: Claude Opus 5.5, as an independent, adversarial review sub-agent.
Date: 2026-10-07.

## Verdict

**I have no remaining mathematical objection.**

- The refined family in Theorem 7.5 (`K = a^3 ell`, `a >= 2^64`) is
  correct as written. I re-derived every changed inequality by hand.
- No step needs the old scale `K = a^3 ell^2`. Every general result that
  the proof uses holds for any positive integer `K`.
- The upper bound `p < 9/4 + 900/log a`, the lower bound `p > 9/4`, and
  the explicit index `ceil(1800/eps)` are unchanged. The source bound
  improves to `log A <= 181 a^5 ell^2`.
- The responses to round-1 findings M1-M5 are correct. The M2 and M4
  responses each leave one small residue (R1 and R2 below).

No mathematical fix is needed. I recommend two small text corrections and
one release step:

- **R1 (notation; introduced by the M2 rename).** In
  `appendix-composition.tex:72-96`, the position index `nu` now runs up to
  the type length `nu_i`, as in `\prod_{\nu=1}^{\nu_i}`.
- **R2 (wording; left over from M4).** `discussion.tex:27-28` still says
  that off-diagonal minimality "uses all shifted tripling inequalities".
- **P1 (release; not mathematical).** `finite-extraction-source.zip`
  (14:36:59) predates the responses and the refinement. It still states
  `a >= 2^16` and `K = a^3 ell^2`. Regenerate it before release.

Section 4 gives the repairs and two optional notes.

## Scope and constraints

**Reviewed:**

- the changed proof and statements in `quantitative.tex` (Theorem 7.5 and
  Corollary 7.6);
- the hypotheses of these changed steps, and the earlier results they use;
- the places that restate the result: the abstract (`main.tex`), Theorem
  1.2 and the allowance paragraph (`introduction.tex`), `costs.tex`,
  `discussion.tex`, and `manuscript/README.md`;
- the text changed in response to round-1 findings M1-M5.

**Not re-audited:** the unchanged tensor maps, flows, rounding, ledger, and
algorithm; the literature; the saved finite examples in Table 1.

**Constraints followed:**

- I checked everything by hand. I ran no experiments, tests, or
  computations on the mathematics. My commands only listed, hashed,
  diffed, and searched files, unpacked the two source archives into
  `/tmp`, and extracted text from the built PDF to see which statements
  it contains.
- I edited no TeX or source file. This report is the only file I wrote.
- I did no literature research.
- I read `docs/manuscript-v2-review-responses.md` to check the responses.
  I did not read the native audit reports.

## Snapshot

`finite-extraction-source.zip` (14:36:59) matches my round-1 snapshot
exactly: its 14 TeX files have the hashes recorded in the round-1 report.
I diffed the current tree against it.

| File | SHA-256 prefix | Modified | Change since round 1 |
|---|---|---|---|
| `quantitative.tex` | `53cf0385a601c23b` | 14:52:45 | refinement |
| `extraction.tex` | `67147479f769310d` | 14:44:57 | M1, M2(b), M2(c), M3 |
| `preliminaries.tex` | `1ccac1ddbcd1af1e` | 14:44:30 | M2(b) |
| `appendix-composition.tex` | `ac66e60e4db59d2f` | 14:44:30 | M2(a), M2(b) |
| `profile.tex` | `4f758baf3d3c20be` | 14:44:30 | M4 |
| `appendix-obstruction.tex` | `238ea5efaa45f769` | 14:44:30 | M5: two comment lines |
| `rounding.tex` | `c8985cb242e3c3ec` | 14:43:03 | citation paragraph, `:156-165` |
| `introduction.tex` | `4f54fa133277a6cd` | 14:52:38 | Theorem 1.2, allowance, one citation word |
| `costs.tex` | `4adde60a78ca5d2b` | 14:52:38 | table scale wording, `O(a^5 (log a)^2)` |
| `discussion.tex` | `a6ef72b62dc60da0` | 14:52:38 | `O(a^5 (log a)^2)` |
| `main.tex` | `fd74f86b2a698730` | 14:52:38 | abstract |
| `manuscript/README.md` | `5c98876e1dc40c3a` | 14:52:38 | rate statement |

Unchanged since round 1: `maps.tex`, `flows.tex`,
`appendix-exact-certificate.tex`, `appendix-separator.tex`, and
`references.bib`.

I re-hashed all files at the end of the review; none had changed. The
rebuilt `finite-extraction.pdf` (14:55:12) contains the new statements and
proof constants. Theorem and equation numbers below are from the current
`build/main.aux`.

The `rounding.tex` change rewrites only the paragraph on Böcherer-Geiger.
It changes no proof step. Its one arithmetic consequence is correct: a
bound `D <= 1/(M q_min)` with `q_min >= 1/(3d)` gives `M D <= 3d`. I did
not check the citation itself.

## 1. The refined family (Theorem 7.5 and Corollary 7.6)

### 1.1 Hypotheses (`quantitative.tex:27-28`)

Let `a >= 2^64`, `t = log a`, `ell = ceil(log2 a)`, and `K = a^3 ell`.
Then:

- `t >= 64 log 2 > 44 > 32`, and `ell >= 64`;
- `t/log 2 = log2 a <= ell <= a`;
- `log K = 3t + log ell <= 3t + log a = 4t`.

### 1.2 The general results allow any positive `K`

The proof uses the following results. Each is stated and proved for an
arbitrary positive integer `K`. None assumes a lower bound on `K` or a
relation between `K` and `a`.

- **Rounding.** Lemma 6.1 and its setup (`rounding.tex:59`: "any integer
  `K >= 1`"), with the error bounds (28).
- **Ledger.** Proposition 6.2, with catalyst count `U + T - K`.
- **Entropy loss.** Proposition 6.3: `L <= 4 J_a` "for every positive
  integer `K`".
- **Count bounds (34).** They follow from `w < K lambda + d` and
  `|z - K mu| < 1`.
- **Occupations.** Proposition 5.1 gives the per-row bounds
  `sum_x lambda < 180` and `mu_r <= 2`, which do not involve `K`. So the
  bounds `w_i <= 180K + 2a` and `z_r <= 2K + 1` at `quantitative.tex:32-35`
  hold for every `K`.
- **Finite construction.** Section 7 (`extraction.tex:4` and `:17-18`:
  "the choice of `K` is unrestricted"): Propositions 7.1 and 7.2, Lemma
  7.3, and formulas (42), (45), and (46).

So the size of `K` matters only where the proof of Theorem 7.5 absorbs
lower-order terms. The table lists every such step.

| Step | Line | What it needs from `K` | Status for `K = a^3 ell` |
|---|---|---|---|
| `180K + 2a + 1 <= 181K` | `:43` | `K >= 2a + 1` | holds |
| `log(2K + 2) < 2 + log K` | `:43` | `K >= 1` | holds |
| `log K <= 4t` | `:28` | `ell <= a` | holds |
| `U + T - K < 184 a K` | `:94` | `2a^3 + a < 2aK` | holds |
| `log 2 / j < K` | `:105-106` | `K >= 1` | holds |
| copy, interpolation, and source bounds | `:72-75`, `:84-88`, `:122-131` | none; `K` only divides | recomputed in 1.3 |

### 1.3 Each changed inequality

**Type loss (`:36-51`).** Use `J_a <= 2a^3`, at most `a - 1` resets,
`log 181 < 6`, `log 4 < 2`, and `log K <= 4t`:

```
4 J_a + T_1 <= J_a (4 + log 181 + log K) + (a-1)(log 4 + log K)
            <  2a^3 (10 + 4t) + (a-1)(2 + 4t).
```

Divide by `K = a^3 ell`, and use `(a-1)/a^3 <= 1/a^2 <= 1/4`:

```
(4 J_a + T_1)/K <= [20 + 8t + (4t+2)/a^2] / ell
                <= [41/2 + 9t] / ell
                <  41/128 + 63/10  =  6.6203125
                                    (ell >= 64, t/ell <= log 2 < 7/10).
```

All three inequalities in the display at `:44-49` are correct.

**Contraction (`:63-69`).** By (45) at `N = 1` and Proposition 6.3,
`Delta_1 >= K log F(a,a) - 4 J_a - T_1`. The unchanged profile bound gives
`log F(a,a) >= (4/3)t - 1/9`. Since `1/9 + 41/128 + 63/10 = 6.7314... < 7`,

```
Delta_1 / K > (4/3)t - 7 >= t > 0      (the middle step needs only t >= 21).
```

So `B > A`.

The bound on the relative loss no longer tends to zero; it stays below
about 6.73. This does not change the order of the rate, because the
numerator already contains bounded multiples of `K` (interpolation and
catalyst). The bound on `p - 9/4` remains of order `1/t`.

**Numerator (`:71-106`).** Each term, divided by `K`:

- **Copies.** By (46),
  `log(S/H)/K < 3 I log 2 / K <= 6 a^2 log 2/(a^3 ell) < 6/(a ell) <= 1`.
- **Interpolation.** Every action has
  `H_i <= w_i log d_i <= 180K + 2a log(2a)`. Every reset has
  `z_r log 3 <= 2K log 3`, which is smaller. Using
  `log(6a^2 + 1) <= 2a` and `log(2a) <= a`:

  ```
  log E / K <= [log(6a^2 + 1) + 360K + 4a log(2a)] / K
            <= 360 + (2a + 4a^2)/(a^3 ell)
            =  360 + (4 + 2/a)/(a ell)
            <= 360 + 5/(a ell)  <=  361.
  ```

- **Catalyst.** With `C_a = 180a - 255`, `J_a <= 2a^3`, and
  `T <= (2K+1)(a-1)`,

  ```
  U + T - K <= K(182a - 258) + 2a^3 + a < 184 a K.
  ```

  So `log kappa_1/(jK) <= 552 log(5a)/ell < 552 (7/10)(1 + 2/8) = 483`.
  Here `K` cancels; this step is unchanged from round 1.
- **Rank of `S^+_{a,a}`.** `3 log(2a - 1) < 3t + 3`.

The total is less than `3t + 3 + 1 + 361 + 483 = 3t + 848`. With the
optional ceiling charge, `log 2/(jK) < 1`, it is less than `3t + 849`. So
the bound `K(3t + 850)` at `:104` holds in both cases.

**Exponent (`:107-113`).** Since `(9/4)((4/3)t - 7) = 3t - 63/4`,

```
p < (3t + 850)/((4/3)t - 7)  =  9/4 + (850 + 63/4)/((4/3)t - 7)
                             <= 9/4 + 865.75/t  <  9/4 + 900/t.
```

**Lower bound (`:114-119`).** This step does not depend on `K`. Since
`L >= 0` and `T_1 >= 0`, we have `Delta_1 <= K log F(a,a)`, so
`p >= tau_a > 9/4`.

**Source dimension (`:122-131`).** With `k = 1`,
`log A = j log u = a ell W`. By (34), with `C_a <= 180a` and
`J_a <= 2a^3`,

```
log A <= a ell (180 a K + 2 a^3 log(2a))
      =  a^5 ell^2 (180 + 2 log(2a)/(a ell))
      <= a^5 ell^2 (180 + 2/ell)  <=  181 a^5 ell^2.
```

**Corollary 7.6 (`:134-153`).** For `a = 2^ell` with `ell >= 64`, we have
`ell_a = ell` and `a >= 2^64`. Then
`900/log a = 900/(ell log 2) < 1800/ell <= eps`. For every
`eps <= 1800/64 = 28.125`, the index is `ell = ceil(1800/eps)`, as in
round 1. Only the floor changed, from 16 to 64. The bound
`log A <= 181 * 2^(5 ell) ell^2` follows from (48).

**Slack.** Every strict inequality has room to spare:

- `6.73 < 7`;
- `t > 44`, where `t >= 21` is needed;
- `3t + 849 < 3t + 850`;
- `865.75 < 900`.

The threshold `2^64` is sufficient; nothing depends on it being minimal.

## 2. No hidden dependence on the old scale

- **Later results.** Theorem 7.7 (`extraction.tex:289-295`) takes its
  parameters from Corollary 7.6 and Theorem 7.5, and it uses no constant
  tied to the old scale. Corollary 7.9 applies Theorem 7.7 with `eps/2`.
  Lemma 7.3 is stated for any relative scheme.
- **Restatements.** The following all state `a >= 2^64`, `ell^2`, and
  `O(a^5 (log a)^2)`:
  - the abstract;
  - Theorem 1.2 and the allowance paragraph in the introduction;
  - `costs.tex:121` and `discussion.tex:20`;
  - `manuscript/README.md`.

  Theorem 1.2 matches Theorem 7.5, including the lower bound proved at
  `quantitative.tex:114-119`.
- **Search.** In the TeX files included by `main.tex`, none of `2^16`,
  `ell^3`, `(log a)^3`, `221/256`, or `(4/3)t - 1` remains. The only
  `a^3 ceil(log2 a)^2` left is the intended scale of Table 1.
- **Table 1.** `costs.tex:57-62` now says that the saved certificates use
  "the larger rounding scale" `K = a^3 ceil(log2 a)^2`, with `k = 32` and
  `j = 128 a ceil(log2 a)`.
  - The listed `(K, j)` match these formulas: `(256, 1024)`,
    `(4608, 3072)`, and `(27648, 6144)` for `a = 4, 8, 12`.
  - Section 7 allows any positive `K`, and the table does not claim that
    its examples belong to the Theorem 7.5 family. So keeping them
    unchanged is consistent.
  - I did not check their certified values.
- **"t > 8".** `quantitative.tex:102` still says `t > 8`. This is still
  valid, since it follows from `t > 32`, and it is all that step needs.

## 3. Responses to round-1 findings

**M1. Resolved** (`extraction.tex:200-208`).

The new recurrence is correct:

- **Recurrence.** One batch of `m_*` products of side `n` is padded and
  restricted to `r_*` products of side `A ceil(n/B)`. Grouping only within
  the parent gives `b_0 = ceil(r_*/m_*)` child batches, with `O(n^2)`
  linear work. So `T(n) <= b_0 T(A ceil(n/B)) + O(n^2)`.
- **Exponent.** The dimension estimate of Lemma 7.3 gives `O(n^{p_0})`
  with `p_0 = log b_0 / log(B/A)`, provided `p_0 > 2`. This holds here,
  because `p_0 >= p >= tau_a > 9/4` (`extraction.tex:270-272`). I agree
  with the finite-algorithm reviewer that the quadratic case cannot occur.
- **Comparison with `Phi`.** Since `r_*/m_* >= 1`, `b_0 <= 2 r_*/m_*`.
  Dividing `log(2 r_*/m_*)` by `log(B/A) = kj Delta_N` gives exactly
  `Phi`, formula (43).

**M2. Resolved, with one new collision.**

- **(a)** `t_i` is now `nu_i`, and no `t_i` remains. However, `nu` was
  already the position index in the same passage. Lines 76 and 92 now
  read `\prod_{\nu=1}^{\nu_i}`. See R1.
- **(b)** `Psi` now names the maps, in `preliminaries.tex:30,37`,
  `extraction.tex:63`, and `appendix-composition.tex:135,140`. `Phi`
  remains only for the exponent bound (`extraction.tex:197,207` and
  `costs.tex:51,68`).
- **(c)** The seed test uses positive integers `alpha_eps` and `beta_eps`
  with `alpha_eps/beta_eps = 9/4 + eps` (`extraction.tex:362-365`).
  - Such integers exist because `eps` is rational.
  - The test `R_n^{beta_eps} < n^{alpha_eps}` is equivalent to
    `R_n < n^{9/4+eps}`.
  - The subscript keeps them distinct from `alpha` and `beta` in
    Proposition 7.2 and from `alpha_s` and `beta_t` in Lemma 7.8.

**M3. Resolved** (`extraction.tex:155-157`). The text now says "a
`B x B` array of blocks of side `ceil(n_l/B)`". This is consistent with
`n_{l+1} = A ceil(n_l/B)`.

**M4. Resolved in `profile.tex`, with one leftover elsewhere.**

- **Fixed.** `profile.tex:94-95` now says that off-diagonal minimality
  "uses shifted tripling instances with `h` beyond the row index". This
  matches the proof (`:66-77`), which uses `h = x_j`, with `x_0 = m` and
  `x_{j+1} = 3x_j + m - 1`.
- **Leftover.** The same overstatement remains in `discussion.tex:27-28`.
  See R2.
- **Accurate as is.** The introduction (`introduction.tex:110-111`) says
  that the theorem "allows" all shifted inequalities.

**M5. Resolved** (`appendix-obstruction.tex:1-2`).

- After the two new comment lines, the file body is byte-identical to the
  v1 file in `archive/v1/finite-extraction-source.zip`.
- Every label it references is defined in that v1 archive:
  - `eq:small-kappa` and `eq:log-enclosure` in `costs.tex`;
  - `eq:relative-counts`, `eq:finite-exponent`, and `lem:batch` in
    `extraction.tex`.
- The v1 `main.tex` includes the file.
- The v2 `main.tex` does not include it, and the 14:36 v2 source ZIP
  omits it.

**Correction to my round-1 report.** It called the composition appendix
"Appendix A". In the build, it is Appendix B (`sec:composed-maps`); the
exact certificate is Appendix A.

## 4. Remaining items

No mathematical fix is necessary.

**Recommended:**

- **R1. Notation, `appendix-composition.tex:72-96`.** Rename the position
  index, for example to `theta`, which the manuscript does not use
  elsewhere:

  ```
  \prod_{\theta=1}^{\nu_i}\mathbf1_{\{\gamma_\theta=\alpha_\theta+\beta_\theta\}},
  q=\omega_i(s)_\theta,\quad 0\le\alpha_\theta<r_i,\ \ldots
  ```

  Apply this in both displays (lines 76 and 92) and at lines 79-84 and
  96.
- **R2. Wording, `discussion.tex:27-28`.** Replace "off-diagonal
  minimality uses all shifted tripling inequalities" with "off-diagonal
  minimality also uses shifted tripling instances beyond the row index".

**Release (not mathematical):**

- **P1. Stale source package.** `finite-extraction-source.zip` (14:36:59)
  predates the edits made between 14:43 and 14:52.
  - Eleven of its 17 files differ from the current tree. They include
    `quantitative.tex`, which still has `a >= 2^16` and `K = a^3 ell^2`.
  - `manuscript/README.md` calls this ZIP the "current source package".
  - Regenerate it, keep `appendix-obstruction.tex` out, and repeat the
    clean-directory build. The PDF has already been rebuilt (14:55:12).

**Optional:**

- **O1.** In `extraction.tex:200-204`, the cost function `T(n)` reuses
  `T`, which in the same section is the reset total in `U + T - K`
  (`:256`, `:262`). A name such as `\operatorname{cost}(n)` would avoid
  this.
- **O2.** The top-level `README.md:44-46` (14:15) still says that the
  multiway research note reduces the source log dimension to
  `O(a^5 (log a)^3)`. That is true at the note's scale, but the
  manuscript now proves `O(a^5 (log a)^2)`. Update it if that README
  should follow the manuscript.

## Limits

- This is a careful hand check, not a formal verification.
- It covers only:
  - the changed inequalities;
  - their hypotheses and the earlier results they use;
  - the restatements;
  - the M1-M5 responses.
- I relied on my round-1 audit for the unchanged results listed in
  Section 1.2. I did not re-audit them.
- I did not check the literature, the saved finite certificates, or any
  build log.
