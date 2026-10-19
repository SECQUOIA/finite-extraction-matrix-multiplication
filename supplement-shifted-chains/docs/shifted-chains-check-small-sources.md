# Verification note: does the small-source barrier survive recycling?

Date: 18 October 2026. Topic key: `small sources`.

Question. [The gate note](shifted-chains-check-gate.md) (with its adversarial
review) proves that a chain scheme whose auxiliaries all come from the source
(`A = prod_i d_i^(2Nk)`) and has `A <= 2^128` has pooled exponent
`p >= p_w = 2.97696088251553944...`, with equality for a one-stage chain.
[The lower note](shifted-chains-check-lower.md), Section R.3 (Lemma R), shows
that the matrix multiplication factor produced by one stage can supply the
auxiliary of the next stage ("forward recycling"). Does recycling break the
barrier, and what should the paper say?

New files: this note and `experiments/shifted_chains_check_small_sources.py`
(standard library only, about 15 s, exact arithmetic). No other file was
changed.

## 1. Verdict

1. **Recycling inside one chain cannot break the barrier.** In a chain, every
   stage acts on all paired factors, and the first stage's auxiliary
   `MM_{d_1^{2Nk}}` must come from the source, because nothing has been
   produced yet. So `A' >= d_1^{2Nk} >= 4^{Nk}`, and `A' <= 2^128` forces
   `Nk <= 64`. I prove (Theorem 1, certified) that **every chain scheme with
   `Nk <= 64` has `p >= p_w`, whatever its source side, depth, arities, blocks
   and types.** Hence every recycled chain with `A' <= 2^128` has `p >= p_w`.
   The bound is attained by the gate witness `W`.
2. **Recycling across chains breaks it completely.** The same mechanism
   (an earlier output supplies a later auxiliary) composes two relative
   schemes (Lemma C). Running `W` and then a second one-stage chain `T` that
   takes its auxiliary `MM_{2^920}` from `W`'s output gives a relative scheme
   with **source side `2^128` and `2.866 <= p < 2.87`**, certified by exact
   integer comparison. Preceding `T` by the classical algorithm gives
   **source side 1 and `p < 2.875`**. In general, for every chain scheme `T`
   and every `delta > 0` there is a composite with source side 1 and
   `p < p_T + delta`. So the infimum of `p` at source side `<= 2^128` (or 1)
   is `9/4`.
3. **So the barrier is an accounting artifact.** It holds for the accounting
   in which every auxiliary is a factor of the source (hypothesis
   `(H_src)` of the lower note's review), and for single chains, but not for
   the algorithms. The source side is not a size measure: the classical
   algorithm is a relative scheme with source side 1.
4. **A recycling-invariant replacement (certified, sharp).** The number of
   copies `m_*` is unchanged by recycling and multiplies under composition.
   I prove (Theorem 2): **every chain scheme with `p < 3` has
   `m_* >= M_0^12 > 2^494`, where `M_0 = 23!/(6! 11! 6!) 2^11 =
   2,558,607,507,456`.** The same holds for every scheme built from chain
   schemes and classical algorithms by recycling, composition and tensor
   products. The bound is attained by the one-stage chain
   `(361,182) -> (1,361)` of arity 2 with `N = 23`, `k = 2`. Since the linear
   maps of a relative scheme have at least `m_* B^2` nonzero coefficients on
   each leg, no subcubic scheme of the construction has fewer than `2^496`
   coefficients.
5. **Recommendation.** Drop the source-side barrier from the paper. State
   Theorem 2 as `prop:small-sources` (Section 6 gives a paper-ready
   statement and proof), and add a short remark on composition next to
   `lem:recycling`. Theorem 1 need not appear in the paper.

## 2. Setting

All logarithms are natural. I use the paper's notation (brief, Section 3) and
the block form of the lower note, Section 2.3.

**Chain schemes.** A stage of arity `d >= 2` maps a pair `(r,b)` to `(c,r)`
with `1 <= c < b` and `(d+2)c <= db - r + 1`. A chain scheme has a source pair
with `s = r_1 + b_1 - 1`, stages `i` with arities `d_i`, optional swaps and
free crops between stages, and a terminal entry `t` at most the larger entry
of the last pair. It has a global number of paired factors, written `P` here
(the lower note's symbol; the brief reserves `P`, so the paper should write
`Nk` in the common case). Stage `i` splits the `P` factors into blocks `j`
with `sum_j N_ij k_ij = P`; block `j` has a type with sector count `M_ij` and
`E_ij = 1 + 6 k_ij (M_ij - 1)`. The counts are

```
A   = prod_i d_i^(2P),                 B   = t^(2P) prod_ij M_ij^(2k_ij),
r_* = s^(6P) prod_ij (2M_ij-1)^(6k_ij) E_ij,
m_* = prod_ij M_ij^(6k_ij),            p   = log(r_*/m_*) / log(B/A)   (B > A).
```

The common model of the certificates note is the case of one block per stage
and `P = Nk`. The stage relation behind these counts (maps topic) is taken as
given, as in the gate and lower notes.

**Margin.** For a threshold `p0`, put `Gamma(p0) = (log(r_*/m_*) - p0 log(B/A))/(2P)`.
Then `p < p0` if and only if `Gamma(p0) < 0`, and

```
Gamma(p0) = 3 log s - p0 log t + sum_i C_i(p0),     C_i = sum_j w_ij c(N_ij, d_i, k_ij, M_ij; p0),
c(N,d,k,M;p0) = p0 log d - (p0/N) log M + (3/N) log((2M-1)/M) + log(E)/(2Nk),
```

with weights `w_ij = N_ij k_ij / P` summing to 1 over `j`. At `p0 = 3`,

```
c(N,d,k,M;3) = log( d^(6Nk) (2M-1)^(6k) E / M^(12k) ) / (2Nk).          (2.1)
```

**Facts used (all proved in earlier notes).**

- (F1) *Gain needs width.* If `M > d^N` then `N >= 3` and `d <= 2N` (lower
  note, Lemma 4(b); gate note, Lemma 6). A block with `M <= d^N` has
  `c >= 0` for every `p0 >= 0`, because its first two terms are
  `p0 (log d - log M / N) >= 0` and the others are nonnegative.
- (F2) *Largest type.* For a block with `M > d^N`, `c(N,d,k,M;p0) >=
  c(N,d,k,M_max(N,d);p0)` when `p0 >= 2` (gate note, Lemma 8).
- (F3) *Potential.* Every chain satisfies
  `s >= alpha z t + (4/3 - alpha) z - 1/3` with `alpha = 40/49` and
  `z = prod_i lambda_{d_i}^{-1}`, where `lambda_d` is the positive root of
  `(d+2)x^2 + x - d` (gate note, Lemma 3; it covers swaps, crops and every
  arity `d >= 1`). Because `(4/3 - alpha) z >= 76/147 > 1/3`, this gives
  `s/t >= alpha z`. Put `a_d = -log lambda_d`.
- (F4) *Endpoint minimum.* For `a, C > 0` and `p0 < 3`, the minimum over real
  `t >= 1` of `3 log(at + C) - p0 log t` is at
  `t* = max(1, p0 C/((3-p0)a))` (gate note, Lemma 5).

**Extended one-stage bound (proved here).** *Every chain that contains a
stage of arity `d` satisfies `s >= (1 + 1/d) t + 1/d`.*

*Proof.* Spans do not increase along a chain (a stage maps span `r+b-1` to
`c+r-1 < r+b-1`, and swaps and crops do not increase it), and neither does
the larger entry (the new entries are `c < b` and `r`). Let the stage of
arity `d` map `(r,b)` to `(c,r)`. Then `s >= r + b - 1` and
`t <= max(c, r)`. If `t <= r`: `db >= (d+2)c + r - 1 >= r + d + 1`, so
`s >= r + b - 1 >= (1+1/d) r + 1/d >= (1+1/d) t + 1/d`. If `t <= c`:
`s >= b >= (d+2)c/d >= (1+1/d) c + 1/d >= (1+1/d) t + 1/d`, using `c >= 1`.
`square`

The gate note's Lemma 4 is the special case of one stage. The script checks
the extended bound on all 817,248 chain endpoints of depth at most 3 with
`r_1, b_1 <= 12` and arities 2 to 5.

**Recycling and composition.**

- *Lemma R* (lower note, R.3). In one chain, a bank `beta_0 = S` funds stage
  `i` from `beta_{i-1} >= U_i = d_i^(2P)` and becomes
  `beta_i = floor(beta_{i-1}/U_i) V_i`, `V_i = prod_j M_ij^(2k_ij)`. The result
  is `r_* MM_S |> m_* MM_{t^(2P) beta_L}` with the same `r_*, m_*`. Writing
  `A' = S` and `B'` for the new sides, `B'/A' <= B/A`, so `p' >= p`. The
  first stage has `U_1 = d_1^(2P)`, so `A' >= d_1^(2P)`.
- *Lemma C (composition; proved here).* If `r_1 MM_{A_1} |> m_1 MM_{B_1}` and
  `r_2 MM_{A_2} |> m_2 MM_{B_2}` with `B_1 >= A_2`, then
  `r_1 r_2 MM_{A_1} |> m_1 m_2 MM_{B_2 f}` with `f = floor(B_1/A_2)`.

  *Proof.* Take `r_2` copies of the first restriction:
  `r_1 r_2 MM_{A_1} |> r_2 m_1 MM_{B_1}`. Restrict each `MM_{B_1}` to a
  principal block of side `A_2 f`, which is `MM_{A_2} MM_f` (v5 (2.1)). Then
  `r_2 m_1 MM_{A_2} MM_f = m_1 (r_2 MM_{A_2}) MM_f |> m_1 m_2 MM_{B_2} MM_f`,
  the second restriction tensored with the identity on `MM_f`, and
  `MM_{B_2} MM_f = MM_{B_2 f}`. Restrictions compose. `square`

  Lemma R is the same argument applied stage by stage, with the paired
  factors carried along. Only exact restrictions are composed, so no
  parameter is shared and v5 Lemma 2.1 is not needed.
- *Exponent of a composite.* If both are relative schemes with exponents
  `p_1, p_2`, then `log(B_2 f / A_1) <= log(B_1/A_1) + log(B_2/A_2)`, so the
  composite has `p >= (p_1 G_1 + p_2 G_2)/(G_1 + G_2) >= min(p_1, p_2)` with
  `G_i = log(B_i/A_i)`, and `m_* = m_1 m_2`. Tensor products behave the same
  way, without the floor.

## 3. Recycling inside one chain: the barrier survives

**Theorem 1.** *Every chain scheme with `P <= 64` (and `B > A`) has
`p >= p_w`. Equality holds for the one-stage chain `W`:
`(43,23) -> (1,43)`, `d = 2`, `N = 32`, `k = 2`, type `(8,16,8)`.*

**Corollary.** Every recycled chain (Lemma R) with source side `A' <= 2^128`
has `p' >= p_w`. Indeed `A' >= d_1^(2P) >= 4^P` gives `P <= 64`, and
`p' >= p`.

So recycling inside one chain changes the source side but not the barrier:
the gate's hypothesis `A <= 2^128` acted only through `P <= 64`.

*Proof.* Let `p_hi = 2976961/10^6`, so `p_w < p_hi`
(`p_w` lies in `(2.976960882, 2.976960883)`). Suppose `p < p_w`. Since
`Gamma` decreases in `p0`, `Gamma(p_w) < 0` and `Gamma(p_hi) < 0`. Call stage
`i` *kept* if `C_i(p_hi) < 0`, and let `K` be the set of kept stages. Dropping
the other stages from the sum only lowers `Gamma(p_hi)`.

1. *Local costs.* For each arity `d`, let `c*(d)` be the least
   `c(N,d,k,M_max(N,d);p_hi)` over all `N, k` with `Nk <= 64` and
   `M_max(N,d) > d^N`. By (F1) and (F2), every block of a stage of arity `d`
   has cost at least `min(0, c*(d))`, so `C_i >= min(0, c*(d_i))`. Gain is
   impossible for `d > 128` (F1). Certified values:

   | `d` | `c*(d)` | at `(N,k)` | `eta(d) = 3a_d + c*(d)` |
   | ---: | --- | --- | ---: |
   | 2 | `-1.326216262...` | (32,2) | `> 0.241111` |
   | 3 | `-0.726674717...` | (32,2) | `> 0.425794` |
   | 4 | `-0.373253578...` | (32,2) | `> 0.540601` |
   | 5 | `-0.147520641...` | (21,3) | `> 0.610433` |
   | 6 to 128 | `>= 0` (least `0.008518` at `d = 6`) | | |

   So every kept stage has arity 2, 3, 4 or 5, and `C_i >= c*(d_i)`.
2. *No kept stage.* `Gamma(p_hi) >= 3 log s - p_hi log t >= (3 - p_hi) log t >= 0`,
   since `t <= s`.
3. *Two kept stages.* By (F3) applied with `z >= z_K = prod_{i in K}
   lambda_{d_i}^{-1}` (the bound increases in `z`) and (F4),
   `Gamma(p_hi) >= R(d_1, d_2) := min_t [3 log(alpha z_K t + (4/3-alpha) z_K - 1/3)
   - p_hi log t] + c*(d_1) + c*(d_2)`. Certified lower bounds of `R` are
   positive for the nine pairs other than `(2,2)` (the least is `0.175740`,
   at `(2,3)`); for `(2,2)` the bound is only `R > -0.007919`. For
   `(2,2)` I use the exact least source. Every chain with two stages of
   arity 2 satisfies `s >= kappa t + kappa_0` for one of the four affine forms
   `(kappa, kappa_0) = (5/2, 3/2), (11/4, 3/4), (3, 1/2), (4, 0)`. They come
   from the backward recursion `b >= ((d+2)c + r - 1)/d` over the two
   orientations at each kept stage, because every bound is increasing in `c`
   and `r`, and other stages, swaps and crops only replace a pair by a
   dominated pair. With (F4) this gives `Gamma(p_hi) > 0.219802`. (The script
   checks the four forms on 42,304 small chain endpoints with two arity-2
   stages.)
4. *Three or more kept stages.* Adding a stage of arity `d` to the relaxed
   bound adds at least `eta(d)`: if `z' = z/lambda_d`, then
   `alpha z' t + (4/3-alpha) z' - 1/3 >= (z'/z)(alpha z t + (4/3-alpha) z - 1/3)`.
   So `Gamma(p_hi) >= min R + min eta > -0.007919 + 0.241111 > 0.2331`.
5. *One kept stage*, of arity `d in {2,...,5}`. Then
   `Gamma(p_hi) >= sum_j w_j [3 log s - p_hi log t + c_j]` over its blocks.
   A block with `M <= d^N` gives a positive bracket (`c_j >= 0` and `s > t`).
   For a block with `M > d^N`, (F2) and the extended one-stage bound with
   `s` an integer give a bracket at least the margin of the *one-stage datum*
   `(N,k,d,t)`: `3 log s_min(t) - p_hi log t + c(N,d,k,M_max;p_hi)` with
   `s_min(t) = ceil(((d+1)t+1)/d)`. The script certifies that every datum with
   `Nk <= 64` and `d <= 5` has a positive margin except `(32,2,2,43)`, which
   is `W`'s. (618 of the 619 blocks are closed by the real-`t` minimum (F4);
   the block `(32,2)` at `d = 2` is scanned for `t <= 600`, and its tail
   `t > 600` is positive because the real-`t` margin increases beyond
   `t* <= 600` and is positive at 600. The closest other data are
   `(32,2,2,45)` and `(32,2,2,41)`, with margins `2.1e-5` and `2.8e-5`.)
   If no block has `W`'s datum, `Gamma(p_hi) > 0`. Otherwise that block has
   `Nk = 64 = P`, so it is the only block of its stage, and
   `t = 43`, `s >= 65`. At `p_w`, its bracket is at least `W`'s own margin,
   which is 0. Every dropped stage has `C_i(p_w) >= 0`: write
   `C_i(p0) = p0 alpha_i + beta_i` with `beta_i >= 0`; if `alpha_i <= 0` then
   `C_i(p_w) >= C_i(p_hi) >= 0`, and otherwise `C_i(p_w) > 0`. So
   `Gamma(p_w) >= 0`.

Each case contradicts `p < p_w`. `square`

The theorem contains the gate's sharp statement (since `A <= 2^128` implies
`P <= 64`) and extends it to every source side. The gate's "forced
one-level" step is replaced by step 5, which allows any number of
non-kept stages.

**Arithmetic.** All logarithms are rational intervals (2 artanh series, tail
bound, 256-bit outward rounding); `lambda_d` is enclosed by `isqrt` and
certified by the sign of `(d+2)x^2 + x - d`; modes are certified by the
exchange conditions and checked exhaustively for `N <= 40`.

## 4. Recycling across chains: the barrier fails

**Witness 1 (source side `2^128`).** Run `W` (source side `2^128`, target side
`B_w = 43^128 M_W^4` with 280 digits, `log2 B_w = 929.82`). Its output
`MM_{B_w}` contains `MM_{2^920} MM_{904}`. Use `MM_{2^920}` as the auxiliary
of the one-stage chain `T`: `(7,5) -> (1,7)`, `d = 2`, `N = 92`, `k = 5`, type
`(23,46,23)`, which alone has `A_T = 2^920`, `B_T` with 1,312 digits and
`p_T in [2.840669415719, 2.840669415720]`. By Lemma C:

| Scheme | Source side | Digits of `B` | `log2 m_*` | Pooled exponent |
| --- | ---: | ---: | ---: | --- |
| `W` | `2^128` | 280 | 705.78 | `[2.976960882515, 2.976960882516]` |
| `W` then `T` | `2^128` | 1,315 | 6,025.17 | `[2.866457549119, 2.866457549120]` |
| classical `MM_{2^920}` then `T` | 1 | 1,312 | 5,319.40 | `[2.874321288647, 2.874321288648]` |

The bounds `2866/1000 <= p < 287/100` for `W` then `T`, and
`p < 2875/1000` for the classical composite, are certified by exact integer
comparison
(`p < u/v` iff `r_*^v A^u < m_*^v B^u`). The classical algorithm is the
relative scheme `(2^920)^3 MM_1 |> MM_{2^920}`.

**Witness 2 (the exponent tends to `p_T`).** Applying `T` again and again to
the bank (exact floors) gives, for `j = 1, ..., 6` applications,
`p < 2.866458, 2.854911, 2.850506, 2.848183, 2.846747, 2.845772`.

**Bootstrapping (proved here).** Let `S` be any relative scheme (the seed)
and `T` any relative scheme with exponent `p_T`. Put `rho = B_T/A_T > 1` and
`X = B_T/(rho - 1)`, and suppose `B_S >= 2X` (note `X > A_T`). Apply `S`,
then `T` repeatedly `j` times on the bank (Lemma C). The bank starts at
`beta_0 = B_S` and satisfies
`beta_{i+1} = floor(beta_i/A_T) B_T >= rho beta_i - B_T`, that is,
`beta_{i+1} - X >= rho (beta_i - X)`. So `beta_i >= X + rho^i X`, and the floor
loss at step `i`, `-log(1 - A_T/beta_i) <= 2A_T/beta_i <= 2 rho^{-i}`, sums to
at most `2rho/(rho - 1)`, independently of `j`.
Hence the composite has source side `A_S` and exponent
`(L_S + j L_T)/(G_S + j G_T - O(1)) -> p_T` as `j -> infinity`, where
`L = log(r_*/m_*)` and `G = log(B/A)`. With the classical seed
`N_S^3 MM_1 |> MM_{N_S}` for a large enough `N_S`, the source side is 1. The chain schemes of
the main theorem reach `p < 9/4 + eps` for every `eps > 0`, and every
composite has `p >= min` of its parts `> 9/4` (Lemma P; the classical part
has `p = 3`). So:

> *The infimum of the pooled exponent over composites of chain schemes with
> source side 1 (or `2^128`) is `9/4`, and it is not attained.*

**How `T` was chosen.** `python -I -B experiments/shifted_chains_check_small_sources.py --screen`
reruns the floating-point screen over all one-stage arity-2 chains `T` with
`A_T <= B_w` and `t <= 200`, composed after `W`. The best is `(N,k,t) =
(92,5,7)` with `p = 2.866457549`; next are `(91,5,7)` and `(92,5,9)`. This is
a selection, not a theorem; the witnesses above are certified exactly, and
by bootstrapping there is no minimum.

**Scope remark (not checked).** Stages of arity 1 (crop and reset only, as
v5's tripling) consume no auxiliary. If the class admitted them, a single
chain could start without any auxiliary. The paper's stages have `d >= 2`,
and composition already settles the question, so I did not pursue this.

## 5. A recycling-invariant small-size statement

**Why `m_*`.** Of the four counts, only `r_*` and `m_*` are unchanged by
Lemma R. Under composition and tensor products, `r_*` and `m_*` multiply,
while `A` can drop to 1 and `B` changes with the floors. `m_*` is also what
an algorithm must handle: a relative scheme turns `m_*` products of side `B`
into `r_*` products of side `A`, so the pooled recursion of v5 Lemma 2.4
processes products in batches of `m_*`. Moreover the scheme's linear maps
have at least `m_* B^2` nonzero coefficients on each leg: in v5's convention
(Section 2.1) every variable of `r_* MM_A` is replaced by a linear form in the
`m_* B^2` variables of `m_* MM_B` on the same leg, and each of those variables
must occur in some form, because `m_* MM_B` contains all of them. Since
`r_* >= m_* (B/A)^2` (v5 Lemma 2.4, Step 1), a lower bound on `m_*` is also
one on `r_*`. The "size" `r_* A^2 + m_* B^2` suggested in the task is not
recycling-invariant (its main term `r_* A^2` drops with `A`), but it is at
least `m_* B^2`, so a bound on `m_*` bounds it too.

**Theorem 2.** *Let `M_0 = 23!/(6! 11! 6!) 2^11 = 2,558,607,507,456`, the
largest sector count for `N = 23`, `d = 2` (attained by the types `(5,12,6)`,
`(6,11,6)` and `(6,12,5)`). Every chain scheme with `p < 3` has
`m_* >= M_0^12`; here `2^494 < M_0^12 < 2^495`. The bound is attained by the
one-stage chain `(361,182) -> (1,361)` with `d = 2`, `N = 23`, `k = 2` and
type `(6,11,6)`: its `m_* = M_0^12` and `p < 2.9999985`.*

**Corollary.** The same bound holds for every relative scheme built from
chain schemes and classical algorithms by forward recycling (Lemma R),
composition (Lemma C) and tensor products, if its exponent is below 3. Such
a scheme's linear maps have more than `2^496` nonzero coefficients.

*Proof of the corollary.* Lemma R leaves `m_*` unchanged and gives
`p' >= p`. Composition and tensor products multiply `m_*`, and the exponent
of the result is at least the smallest exponent of the parts with `B > A`
(Section 2; every part has `r_* >= m_*`, so a part with `B <= A` only raises
the exponent). Classical algorithms have `p = 3` and `m_* = 1`. So a
composite with `p < 3` has a chain scheme part with `p < 3`, hence
`m_* >= M_0^12`. Finally `B >= 2`. `square`

*Proof of Theorem 2.* Suppose `p < 3`, so `Gamma(3) < 0`. Call stage `i`
kept if `C_i(3) < 0`, and let `K` be the set of kept stages. For a kept
stage, let its *representative* be a block of least cost `c(...;3)`; then
`C_i(3)` is at least that cost, the cost is negative, so the representative
has `M > d^N` by (F1), and `m_* >= prod_{i in K} M_rep(i)^(6 k_rep(i))`.
Suppose, for a contradiction, that every representative satisfies
`M^(6k) < M_0^12`.

1. *No kept stage.* `Gamma(3) >= 3 log(s/t) >= 0`.
2. *One kept stage*, of arity `d`. By the extended one-stage bound,
   `s > (1 + 1/d) t`, so `0 > Gamma(3) > 3 log((d+1)/d) + c_rep`. By (2.1)
   this says `(d+1)^(6Nk) (2M-1)^(6k) E < M^(12k)` for the representative.
   It forces `M > (d+1)^N`, hence `N >= 3` and `d <= 2N` (F1), and with
   `M^(6k) < M_0^12` it leaves finitely many blocks. The script checks all
   5,792 of them, every type included, by exact integer comparison: none
   satisfies the inequality.
3. *Two or more kept stages.* By (F3), `3 log(s/t) >= 3 log(40/49) +
   sum_{i in K} 3 a_{d_i}`, so
   `Gamma(3) >= 3 log(40/49) + sum_{i in K} (3 a_{d_i} + c_rep(i))`.
   The script checks that every block with `M > d^N` and
   `M^(6k) < M_0^12` (31,677 blocks, every type) satisfies
   `3 a_d + c(N,d,k,M;3) >= log(34/25)`, in the exact form
   `d^(6Nk) (2M-1)^(6k) E 25^(2Nk) v^(6Nk) >= 34^(2Nk) u^(6Nk) M^(12k)` with a
   certified rational `u/v >= lambda_d`. (The least value is about `0.35772`,
   at `N = 23`, `d = 2`, `k = 2`.) Since `34^2 40^3 = 73,984,000 >
   73,530,625 = 25^2 49^3`, `2 log(34/25) + 3 log(40/49) > 0`, so
   `Gamma(3) > 0`.

Each case is a contradiction, so some representative has
`M^(6k) >= M_0^12`, and `m_* >= M_0^12`. For sharpness, the script finds
the least terminal `t` for which the one-stage chain with `N = 23`, `k = 2`,
`d = 2`, `M = M_0` and least source `s = ceil((3t+1)/2)` is subcubic, by
exact comparison of `r_* A^3` with `m_* B^3`: it is `t = 361` (`s = 542`,
source pair `(361,182)`, `A = 2^92`, `B` with 285 digits,
`log2 r_* = 3058.1`), with `p` in `[2.999998425472, 2.999998425473]`. `square`

**Size of the enumeration.** Gain needs `N >= 3` and `d <= 2N`, and each
budget bounds `N k log_2 d` (case 3) or `N k log_2(d+1)` (case 2) by
`log_2(M_0^12)/6 < 82.5`. So `N <= 52`, `d <= 32` in case 2 and `N <= 82`,
`d <= 32` in case 3; the whole check takes under a second.

**Context (floating point, not certified).** The same relaxation does not
close thresholds below 3 directly, because two stages with the whole budget
each can beat the endpoint loss `3 log(40/49)`. A floating-point screen of
one-stage chains suggests that the least `m_*` below `2.977` is `W`'s
(`2^705.8`), and below `2.9` it is about `2^2085`. These numbers are not
claimed; they only show that `m_*` grows quickly as `p` drops, while `A` can
be made 1 at every exponent.

## 6. Recommendation for the paper

**Drop the source-side barrier.** Do not state "`A <= 2^128` implies
`p >= 2.97696`" as a property of the construction. It is true only for single
chains with source-supplied auxiliaries, and a two-line composition with the
classical algorithm (source side 1) or with `W` (source side `2^128`) gives
`p < 2.9`. Stating it, even with the hypothesis, invites a misreading.
Theorem 1 is recorded here for completeness; the paper does not need it.

**Add a remark on composition** in `limits.tex`, right after
`lem:recycling` (suggested label `rem:composition`):

> **Remark (composition).** The argument of Lemma `lem:recycling` also
> composes any two relative schemes: if `r_1 MM_{A_1} ⪰ m_1 MM_{B_1}` and
> `r_2 MM_{A_2} ⪰ m_2 MM_{B_2}` with `B_1 >= A_2`, then
> `r_1 r_2 MM_{A_1} ⪰ m_1 m_2 MM_{B_2 ⌊B_1/A_2⌋}`, by restricting each
> `MM_{B_1}` to a principal block `MM_{A_2} MM_{⌊B_1/A_2⌋}`
> \citep[(2.1)]{FinCon26}. The composite has source side `A_1`, `m_* =
> m_1 m_2`, and pooled exponent at least the smaller of the two. The
> classical algorithm is the relative scheme `N^3 MM_1 ⪰ MM_N`, with source
> side 1; preceding a scheme by it and iterating the scheme brings the
> exponent arbitrarily close to the scheme's own. So the source side alone
> does not measure the size of an algorithm: a lower bound on `A`, such as
> Theorem `thm:lower` in its source-side form, describes the accounting in
> which every auxiliary is a factor of the source, not the size of the
> resulting algorithm. For example, the one-stage chain `(43,23) -> (1,43)`
> (`d=2`, `N=32`, `k=2`; `A = 2^128`, `p = 2.97696...`) followed by the
> one-stage chain `(7,5) -> (1,7)` (`d=2`, `N=92`, `k=5`), whose auxiliary
> `MM_{2^920}` it takes from the first chain's output, is a relative scheme
> with `A = 2^128` and `2.866 < p < 2.87` (script
> `shifted_chains_check_small_sources.py`).

**Replace `prop:small-sources` by Theorem 2** in `examples.tex` (keep the
label so that cross-references resolve). Paper-ready statement:

```latex
\begin{proposition}[Small batches]\label{prop:small-sources}
Let \(M_0=\frac{23!}{6!\,11!\,6!}\,2^{11}=2\,558\,607\,507\,456\).
Every chain scheme of Definition~\ref{def:class} with pooled exponent
\(p<3\) has \(m_*\ge M_0^{12}>2^{494}\). The same holds for every relative
scheme with \(p<3\) obtained from chain schemes and classical algorithms
by forward recycling (Lemma~\ref{lem:recycling}), composition
(Remark~\ref{rem:composition}) and tensor products; the linear maps of
such a scheme have more than \(2^{496}\) nonzero coefficients. The bound
is attained by the one-stage chain \((361,182)\to(1,361)\) of arity \(2\)
with \(N=23\), \(k=2\) and type \((6,11,6)\), which has
\(m_*=M_0^{12}\) and \(p<2.9999985\).
\end{proposition}
```

Proof for the paper (about 0.75 page; computer-assisted, script
`shifted_chains_check_small_sources.py`, Part C):

1. Recycling keeps `m_*` and does not lower `p`; composition and tensor
   products multiply `m_*` and give `p >=` the least exponent of the parts;
   classical algorithms have `p = 3`. So it suffices to treat one chain
   scheme.
2. Write `p < 3` as `3 log(s/t) + sum_i C_i < 0` with the costs (2.1). A
   stage with `C_i >= 0` is dropped; a kept stage has a block with negative
   cost, which forces `M > d^N`, hence `N >= 3` and `d <= 2N`. Its cheapest
   block bounds `C_i` from below and contributes `M^{6k}` to `m_*`.
3. One kept stage: `s >= (1+1/d)t + 1/d` (prove it in two lines as above)
   reduces `p < 3` to `(d+1)^{6Nk}(2M-1)^{6k}E < M^{12k}`; a finite exact
   check shows that this forces `M^{6k} >= M_0^{12}`.
4. Two or more kept stages: the potential bound `s >= (40/49) z t` (from the
   contraction lemma of `appendix-lower.tex`, as in the gate note's
   Lemma 3) and a finite exact check `3 a_d + c >= log(34/25)` for every
   block below the budget, with `2 log(34/25) + 3 log(40/49) > 0`.
5. Sharpness by exact comparison of `r_* A^3` and `m_* B^3`.

Display the counts of Definition `def:class` in or before the proposition,
as the gate review asked: the bound depends on the separator charge
`(2M-1)^6`, the per-stage exactification `E = 1 + 6k(M-1)`, the source charge
`s^6` per paired factor and uncompressed auxiliaries. Compressed auxiliaries,
joint exactification and cheaper sources are outside its scope, and
composition with schemes outside the construction (for example Strassen's,
with `m_* = 1` and exponent `log_2 7`) is not covered.

If the authors prefer not to add a computer-assisted proposition, omit
`prop:small-sources` and keep only the remark on composition. Do not keep
the source-side form.

**Consequences for other sections (for the integrator).**

- `thm:lower`: the composition remark gives a second, simpler reason why its
  source-side form depends on accounting (the first is Lemma R; lower note
  R.3). The lower note's review already recommends Proposition T
  (`log(B/A)`) as the main resource bound.
- `examples.tex` and the introduction: comparisons with v5 by digits of `A`
  (including v5 Corollary 11.2(a),(b), which bound the source side of v5's
  schemes) compare two constructions in the same accounting (all
  auxiliaries from the source). They are fair only under that convention;
  composition with the classical algorithm makes either source side 1. Keep
  the `B` column, as the certificates review asks, and say so in one
  sentence. v5 Corollary 11.2(c), on the seed side, is not affected. The
  witnesses' `m_*` could also be reported, since it is the invariant
  measure.
- The brief's open question "smaller finite sizes (compression, recycling,
  cheaper sources)" should speak of `B` and `m_*`, not of `A`.

## 7. Reproduction

```sh
python -I -B experiments/shifted_chains_check_small_sources.py            # parts A-D, about 15 s
python -I -B experiments/shifted_chains_check_small_sources.py --screen   # plus the selection screen
```

Part A certifies the witnesses of Section 4, Part B every step of Theorem 1,
Part C every step of Theorem 2, and Part D the geometric facts on small
chains (Lemma 3 of the gate note, the extended one-stage bound, the four
`(2,2)` forms) and the mode certificate against exhaustive enumeration for
`N <= 40`. Every check raises an exception on failure (no `assert`
statements). The script imports nothing from the repository.

## 8. What I did not verify

- The stage relation behind the counts (maps topic), as in the gate and lower
  notes. Theorems 1 and 2 are statements about these counts.
- Facts (F1)–(F4) are taken from the gate and lower notes, where they are
  proved and adversarially reviewed; the script rechecks them only on small
  cases.
- Whether stages of arity 1 inside one chain would break Theorem 1's
  conclusion at source side 1 (outside the paper's class).
- Thresholds below 3 for Theorem 2 (Section 5, "Context").

## Adversarial review

Date: 18 October 2026. Role: adversarial referee for the topic `small sources`.
I tried to refute the note above. I reran the checker's script, re-derived
every proof step, and wrote a separate check,
`experiments/shifted_chains_skeptic_small_sources.py` (run
`python -I -B experiments/shifted_chains_skeptic_small_sources.py`, about
30 s). It imports nothing from the repository and shares no code with the
checker's script. Exact claims are exact integer comparisons. Real values use
`decimal` at 100 digits, and every sign must clear a padding of `1e-50`.
Nothing above this section was changed.

### R.1 Verdict

The certified mathematics is correct: Lemma C, the composite witnesses, the
bootstrapping argument, Theorem 1 (as a statement about chains with
`P <= 64`) and Theorem 2. I reproduced every number by an independent path
(R.2).

There is **one substantive error, in the interpretation of Theorem 1**.
Verdict item 1, the corollary of Theorem 1 and the second item of the issue
list claim that within one chain the source side is at least `d_1^(2P)`, so
that recycling inside one chain cannot beat `p_w` at source side `<= 2^128`.
That is true only when a whole stage is funded at once (Lemma R, and the
"supply" of the recycling note). The blocks of one stage act on disjoint
tensor factors, so they can be funded one after another from the bank. Then
**a single one-stage chain of the class has source side `2^128` and
`p < 2.9`, or source side 64 and `p < 2.85`** (R.3, certified exactly). So
the barrier fails even for single chains.

This strengthens the note's final recommendation (drop the source-side
barrier) but changes its stated reason. It also limits a source-side lower
bound proposed in the recycling note (R.3, last paragraph).

Theorem 2 survives every way of supplying the auxiliaries that I found.
I endorse it for the paper as `prop:small-sources`, with the small wording
changes in R.4 and R.6.

### R.2 What I re-derived and reran

- **Checker's script.** `python -I -B experiments/shifted_chains_check_small_sources.py`
  passes in 13.7 s, and its output matches the note.
- **Lemma C and the exponent of a composite.** Re-derived. The parts used
  (chain schemes and classical algorithms) all have `r_* >= m_*`, so a part
  with `B <= A` only raises the exponent. Composites of such parts also have
  `r_* >= m_*`.
- **Bootstrapping.** Re-derived: `beta_{i+1} - X >= rho (beta_i - X)` and
  `beta_i >= X(1 + rho^i)` when `beta_0 >= 2X`. The floor losses in fact sum
  to at most 2, since `2A_T/beta_i <= 2(rho-1)/rho^(i+1)`; the note's
  `2 rho/(rho-1)` is also valid. The hypothesis `B_w >= 2X` holds for the
  `W`-then-`T` iterates (checked exactly).
- **Witnesses (Part A).** Sector counts by exhaustive type enumeration,
  counts recomputed, and the thresholds re-proved by my own exact
  comparisons: `2.866 <= p < 2.87` for `W` then `T` (`B` has 1,315 digits),
  `p < 2.875` for the classical composite, and the decreasing iterates
  `2.866458, ..., 2.845772`. Decimal values: `p_w = 2.976960882515539...`,
  `p_T = 2.840669415720...`.
- **Extended one-stage bound.** Re-derived; it is correct. Spans and largest
  entries do not increase. In the case `t <= c`, `c >= 1` gives
  `(1+2/d)c >= (1+1/d)c + 1/d`.
- **Theorem 1, every step.** Re-derived: the dropping of stages with
  `C_i >= 0`, the pointwise `eta` argument for three or more stages, the four
  `(2,2)` forms (I recomputed all four by hand from the backward recursion),
  and the final step at `p_w`, which uses `C_i(p0) = p0 alpha_i + beta_i` with
  `beta_i >= 0`. Part D recomputes every number in decimal and matches the
  note: `c*(2..5)`, `eta`, the ten pair margins, the `(2,2)` margin
  `0.219802`, the three-stage margin `0.233192`, the least `c* = 0.008518` at
  `d = 6`, and the one-stage scan (`t <= 700` with tails; nearest data
  `(32,2,2,45)` and `(32,2,2,41)`). For `d <= 6` the local costs are minimized
  over **all** types, not only the largest. So the table at those arities
  does not rely on the largest-type lemma. For the kept arities 2–5 the
  minimizers are the largest types, as the lemma predicts.
- **Geometry (Part E).** A dynamic programme computes the least source span
  of every (pair, arity word) reachable in at most 4 stages from sources with
  entries at most 10, arities 2–7, **with free crops of both entries** (the
  checker's walk had no free crops of the kept entry). On all 47,638
  (state, terminal) cases it confirms `t <= s`, the potential bound with `alpha = 40/49`,
  the extended one-stage bound and the four `(2,2)` forms. The least span is
  the binding case for all of them. The potential bound uses `z` computed
  from certified upper bounds of `lambda_d`, so `z` is a lower bound.
- **Theorem 2 (Part C).** Re-derived (R.4). Both enumerations were redone
  with different loops (all `d <= 200`, `N <= 200`, with explicit breaks
  justified by `M > (d+1)^N` or `M > d^N`; `d >= 201` is excluded because a
  gaining block then has `N > 100` and `d^(6N) > M0^12`). A different
  rational upper bound for `lambda_d` was used (Newton from above, rounded up
  to `2^-80`). Results: 5,792 and 31,677 blocks, no counterexample, least
  `3a_d + c = 0.357723` at `(N,d,k) = (23,2,2)`, the three modes of `M_0`,
  `2^494 < M0^12 < 2^495`, and the sharp terminal `t = 361`.

### R.3 Major: recycling block by block inside one chain

**Lemma (block-level supply; proved here).** Take a chain scheme of the
class. List its blocks `(i,j)` so that all blocks of stage `i` come before
those of stage `i+1`. Put `U_ij = d_i^(2 N_ij k_ij)` and
`V_ij = M_ij^(2 k_ij)`. Start a bank at `beta = S`. At each block in turn,
require `beta >= U_ij` and replace `beta` by `floor(beta/U_ij) V_ij`. Then
`r_* MM_S |> m_* MM_{t^(2P) beta}`, with the class's `r_*` and `m_*`, and
`t^(2P) beta / S <= B/A`, so `p' >= p`.

*Proof.* This is the induction of Lemma S of the recycling note, done one
block at a time. The exact relation (D') of block `(i,j)` acts on its
`N_ij k_ij` factors of `Q_{pi_{i-1}}` and on a principal sub-block
`MM_{U_ij}` of the bank. It is tensored with the identity on the other `Q`
factors and on `MM_{floor(beta/U_ij)}`, and the copies are grouped as in
Lemma S. All blocks of a stage use the same child, so after the last block
of stage `i` every factor is `Q_{(c_i, r_i)}`, and then the crop to `pi_i` is
applied. The ratio bound follows from `floor(y) <= y`. `square`

Lemma R and the recycling note's supplies fund all blocks of a stage at
once, from one cut of side `d_i^(2P)`. The bound `A' >= d_1^(2P)` holds only
for that granularity. With block-level funding, only the first funded block must fit in
`S`.

**Witnesses (Part B; exact bank, exact thresholds).** Both are one-stage
chains of arity 2 with child 1 and largest types. The blocks are listed in
funding order:

| Source side `S` | Chain | Blocks `(N,k)` | `P` | Recycled `p'` | Exact | Source supply |
| --- | --- | --- | ---: | --- | --- | --- |
| `2^128` | `(9,6) -> (1,9)`, `s = 14` | (32,2), (39,3), (54,4), (82,5) | 807 | 2.883996931... | `p' < 29/10` | `A = 2^1614`, `p = 2.8837163...` |
| 64 | `(7,5) -> (1,7)`, `s = 11` | (3,1), (3,1), (4,1), (5,1), (7,1), (11,1), (18,1), (16,2), (27,2), (33,3), (60,3), (86,4), (110,6), (160,8) | 2,700 | 2.844273606... | `p' < 57/20` | `A = 2^5400`, `p = 2.8439904...` |

Every block is funded (the script checks `beta >= U_ij` before each block).
Both chains are in the block form of `def:class`: one stage, several blocks
with `sum N_j k_j = P`. The schedules came from a floating-point greedy
search, so they are selections, not optima. A longer schedule from source
side 64 reaches about 2.74 (floating point only, not certified).

**Least source side.** With block-level funding, **the least source side
of a subcubic chain scheme is exactly 64**. A subcubic chain has a block with
`M > d^N`, since otherwise every cost is nonnegative at `p0 = 3`. Blocks with
`M <= d^N` never raise the bank, because `floor(beta/U) V <= beta` when
`V <= U`. The first gaining block needs `U >= 2^6`: gain forces `N >= 3`,
and for `d >= 3` already `d^6 > 64`. The second witness attains 64.

**Consequences.**

1. Verdict item 1, the corollary of Theorem 1, the sentence "the gate's
   hypothesis `A <= 2^128` acted only through `P <= 64`" and the issue
   "within one chain the source side can never go below `d_1^{2Nk}`" are
   true only for stage-level funding. Correct them to say so. Theorem 1
   itself, a statement about chains with `P <= 64`, is unaffected.
2. The recommendation to drop the source-side barrier stands, for a stronger
   reason: the barrier fails for single chains of the class, not only for
   compositions.
3. **Recycling note (cross-topic).** Theorem C(6) (`log S >= 2P log d_1`) and
   the lower end of Remark 7.5 ("the source side under the best supply lies
   between `eps^-3 log^2` and `eps^-3 log^3`") hold only for stage-level
   supplies. The paper should not state any lower bound on the source side
   except under the source supply. I did not check how small block-level
   funding makes the source side of the main construction as `eps -> 0`. The
   statements on `r_*`, `m_*` and `log(B/A)` (Theorem C(1)–(5), Proposition T)
   are unaffected, because block-level funding keeps `r_*` and `m_*` and still
   gives `B'/S <= B/A`.

### R.4 Theorem 2: confirmed, with three remarks

I re-derived the proof. Case 1 uses `t <= s`. Case 2 uses
`s > (1+1/d)t` and (2.1), which turn the margin into
`log((d+1)^(6Nk)(2M-1)^(6k)E / M^(12k))/(2Nk)`. Blocks with
`M <= (d+1)^N` satisfy the reverse inequality trivially. Case 3 uses
`s >= alpha z t`, because `(4/3 - alpha) z - 1/3 >= 9/49 > 0`, together
with `lambda_d <= u/v`, monotonicity in the number of kept stages and
`34^2 40^3 > 25^2 49^3`. The hypothesis "every representative has
`M^(6k) < M0^12`" follows from `m_* < M0^12`. The corollary survives
block-level funding, because `m_*` is unchanged and `p' >= p`. The
`2^496` coefficient bound is valid (each leg map must be onto, since
`m_* MM_B` is concise, and `B >= 2`), but it is weak: it ignores `B`.

1. **Discarding copies.** `r_* MM_A |> m' MM_B` is a restriction for every
   `m' <= m_*`. For the block `(23,2)` with largest type at terminal
   `t = 10^6`, the least `m'` that keeps `p < 3` is about `2^494.25`, below
   `M0^12 = 2^494.62` (certified exactly; `2^494.28` at `t = 10^4`). So the
   bound concerns the copies *produced* by the listed operations, and
   "sharp" is relative to that list. The proposition's wording ("obtained
   ... by forward recycling, composition and tensor products") is already
   exact. Do not describe `m_*` as invariant under all restrictions. The
   effect is a factor below `2^0.4` in this example; I did not bound it in
   general.
2. **Per-block arities.** If `def:class` allows different arities for
   different blocks of one stage (lower note, Remark 8(b)), the proof still
   works. Take `d` to be the arity of the representative block: the stage's
   step is legal at every arity it uses, so the extended one-stage bound and
   the contraction hold at that `d`.
3. **Scope.** As the note says, the bound depends on the charges `s^6`,
   `(2M-1)^6` and `E = 1 + 6k(M-1)` and on uncompressed auxiliaries. Rerun
   Part C if the paper changes any of them.

### R.5 Minor issues

1. **Remark `rem:composition`, floor-loss sentence.** "The floor losses sum
   to at most `2 rho/(rho-1)`" needs the seed to be large enough, namely
   `B_S >= 2B/(rho-1)`, where `B` and `rho` are those of the iterated scheme.
   State this hypothesis, or drop the parenthetical; "arbitrarily close"
   then needs a large classical seed, which the sentence already allows.
2. **"Keep the `B` column".** `B` and `m_*` are not invariant under
   composition either: bootstrapping multiplies them. The fair sentence for
   `examples.tex` is that digits of `A` and `B` are those of the schemes as
   constructed, with every auxiliary supplied by the source, and that
   recycling and composition change both (Remark `rem:composition`).
3. **Composition remark, one optional sentence.** "The same argument applies
   block by block within one stage; for example, a one-stage chain of arity 2
   with source side 64 has `p < 2.85`." This needs the supplement script
   `shifted_chains_skeptic_small_sources.py` (Part B) as its certificate.
   Omit it if the paper states no source-side bound beyond the source supply.
4. **Notation in the notes.** The recycling note proposes `W` for the global
   power, and this note calls the gate witness `W`. Neither name should reach
   the paper together; with Theorem 1 dropped, the witness needs no name.
5. **Issue list.** The second issue ("Within one chain the source side can
   never go below `d_1^{2Nk}`") must read "with stage-level funding". The
   tenth issue (arity-1 stages) is moot: block-level funding already gives a
   single chain with source side 64 without arity-1 stages.

### R.6 Final recommendation for the paper

1. **Drop** "`A <= 2^128` implies `p >= 2.97696...`" from the paper, in every
   form, including the source-supply form. It fails for compositions and for
   single chains funded block by block, so even a correctly hypothesized
   statement would mislead.
2. **Add `rem:composition`** after `lem:recycling`, with the note's text and
   the fix of R.5.1. Optionally add the block-level sentence of R.5.3.
3. **State Theorem 2 as `prop:small-sources`** in `examples.tex` (keep the
   label), with the note's statement and proof outline, and these two edits:
   in the closure list write "by forward recycling (Lemma `lem:recycling`,
   also when the blocks of a stage are funded one after another), composition
   (Remark `rem:composition`) and tensor products"; and display the count formulas of `def:class` with it.
   The proof needs the potential bound `s >= (40/49) z t` from the
   contraction lemma in `appendix-lower.tex`. If the authors prefer no
   computer-assisted proposition, omit it; the paper loses nothing else.
4. **Do not include Theorem 1** or its corollary.
5. **Lower bounds on the source side** (lower note Theorem 5, recycling note
   Theorem C(6) and Remark 7.5) may appear only under the source supply,
   named as such. The robust resource statements are those on `r_*`, `m_*`
   and `log(B/A)`.

### R.7 Not verified here

- The stage relation (D') and the count formulas (maps topic). As in the note,
  Theorems 1 and 2 are statements about these counts.
- The contraction lemma and the gain and largest-type lemmas (F1–F3) beyond
  re-reading their proofs and the small exhaustive checks of Part E. The
  largest-type lemma is used only for `d >= 7` in Part D and in the
  one-stage scan.
- `decimal`'s correct rounding, on which the real-valued checks of Parts A, B
  and D rely. Every threshold claim of Parts A–C is also exact.
- How far block-level funding lowers the source side of near-`9/4` chains.
