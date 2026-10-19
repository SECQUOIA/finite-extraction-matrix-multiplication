# Verification note: the finite barrier at source side 2^128 ("gate")

Date: 18 October 2026. Scope: verification of the round-11 finite gates for
the shifted-chain construction. Nothing under `manuscript/`, `upstream/`,
`formalization/`, or any existing file was changed.

Sources checked:
[variable gate](round11-variable-finite-gate.md) and its
[review](round11-review-variable-finite-gate.md),
[blocked gate](round11-blocked-finite-gate.md) and its
[review](round11-review-blocked-finite-gate.md),
`experiments/round11_variable_finite_gate.py`,
`experiments/round11_blocked_finite_gate.py`, their receipts in `results/`,
and the construction notes they rely on
([round 8](round8-multiscale-construction.md),
[round 9](round9-multiscale-finite-gate.md),
[round 10](round10-orientation-control.md),
[arity ramp](round11-arity-ramp.md)).

New checker: `experiments/shifted_chains_check_gate.py`. Run it from the
repository root with

```sh
python -I -B experiments/shifted_chains_check_gate.py
```

It takes about two minutes and does not import the round-11 producers.

## 1. Verdict

The two claimed barriers are correct, with one framing correction:

- **Common inventory and power.** In the uncompressed paired shifted-chain
  recipe with a common inventory `n` and power `k`, every relative scheme
  with source side `A <= 2^128` has pooled exponent at least `29/10`.
- **Blocked extension.** The same holds when level `i` uses its own
  `(n_i,k_i)` with `n_i k_i | P` for a global power `P`.
- **The 2.95 claim.** The claim that the common-inventory relaxation
  *by itself* cannot establish `59/20` is also correct. Exactly 17 relaxed
  gates are negative (21 in the blocked screen), and each is certified
  negative by a rigorous upper bound.

I reproduced every count and the SHA-256 census digests with independent
code. Every margin was recomputed with independent outward-rounded
logarithms. For the common gate, every sign was confirmed a second time by
an exact comparison of two integers, which uses no logarithms.

The main new finding is that 2.9 is far from the best barrier this method
gives:

- **All open cases are one-level chains.** At 59/20, and even at 2.9765,
  every case the relaxation leaves open has arity multiset `(2)` and a
  source power that admits no second level. So the physical chain has
  exactly one level of arity 2.
- **A one-level bound closes them.** For one-level chains a short exact
  argument gives `s >= (1+1/d)t + 1/d`. This closes every open case.
- **Result: an almost tight bracket.** Both models (common and blocked)
  satisfy pooled exponent `>= 119/40 = 2.975`, and also `>= 5953/2000 = 2.9765`.
  An explicit one-level chain with `A = 2^128` has pooled exponent in
  `(2.976960882, 2.976960883)`. So for `A <= 2^128` the best exponent of
  these families lies in `[2.9765, 2.97697)`.

One framing point must change for the paper. The notes state the result
for the exponent with a ceiling, `log ceil(r*/m*) / log(B/A)`. v5's
pooled exponent (Definition `def:relative-scheme`, Lemma `lem:batch` in
`manuscript/preliminaries.tex`) has no ceiling. The computation in fact
bounds the ceiling-free quantity `log(r*/m*)/log(B/A)`, so it proves the
stronger, v5-compatible statement. The paper should state it that way.

## 2. The model, and what is taken from the notes

**Chains.** A state is a pair `(r,b)` of positive integers, the
convolution tensor `C(r,b)`. A level with arity `d >= 2`:

1. optionally swaps the two coordinates,
2. chooses a child `c` with
   ```
   1 <= c < b,        (d+2) c <= d b - r + 1,
   ```
3. moves to `(c,r)`.

An output swap is the same as the next level's input swap; a final swap
chooses which coordinate is the terminal. Write

- `s = r_0 + b_0 - 1`, the rank of the initial convolution tensor;
- `t`, the retained terminal coordinate (the "second input" after the
  terminal first-input projection).

At level `i` a retained three-class type `(l_i,o_i,m_i)` with sum `n`
has sector count

```
M_i = n!/(l_i! o_i! m_i!) * (d_i - 1)^l_i * 2^o_i.
```

**Counts, common model.** Let `E_i = 1 + 6k(M_i - 1)`. The recipe yields
the relative scheme `r* MM_A >= m* MM_B` (a restriction) with

```
A  = (prod_i d_i)^(2nk)
B  = t^(2nk) (prod_i M_i)^(2k)
r* = s^(6nk) prod_i (2M_i - 1)^(6k) E_i
m* = (prod_i M_i)^(6k)
```

**Counts, blocked model.** Fix a global `P`. Level `i` uses `n_i, k_i` with
`n_i k_i | P` and repeats its block `P/(n_i k_i)` times. Then

```
A  = prod_i d_i^(2P)
B  = t^(2P) prod_i M_i^(2P/n_i)
r* = s^(6P) prod_i (2M_i - 1)^(6P/n_i) E_i^(P/(n_i k_i))
m* = prod_i M_i^(6P/n_i)
```

where `E_i = 1 + 6 k_i (M_i - 1)`.

**Taken from the notes, unchecked here.** The per-level stage relation
(round 8, eq. (5)):

```
(2M-1)^6 Q_{r,b}^{(x)n} (x) MM_{d^{2n}}   restricts to   M^6 Q_{r,c}^{(x)n} (x) MM_{M^2}
```

with parameter degree `6(M-1)`. Its separator charge `(2M-1)^6` and the
`s^6` source rank per paired factor `Q` are taken from the notes and
verified in other topics.

**Checked here for consistency only:**

- the formulas above match round 8 eq. (11), round 9 eq. (3), and arity
  ramp eq. (7) (with `t = 1`);
- `E = kD + 1` with `D = 6(M-1)` is v5's exactification lemma
  (`lem:exactification`);
- repeating a block `h = P/(nk)` times multiplies the multiplicities and
  sides as stated. In the blocked formulas every exponent is an integer
  because `n_i | P`.

**Coverage of the paper's construction.** The arity-ramp construction uses
a common `n` per sign and a common `k`, and terminal `C(1,1)` (so `t=1`).
Its finite instances are therefore inside the common model.

**Pooled exponent** (v5): `p = log(r*/m*) / log(B/A)`, defined when `B > A`.

## 3. Statements and proofs

Throughout, `2 <= p0 < 3` is a proposed threshold and
`lambda_d = (sqrt(1+4d(d+2)) - 1) / (2(d+2))` is the positive root of
`(d+2)x^2 + x - d`.

### Lemma 1 (normalized quality form). Proved here.

In the common model with `B > A`, `p < p0` holds if and only if

```
Phi := 3 log s - p0 log t + sum_i C(n, d_i, k, M_i; p0) < 0,

C(n,d,k,M;p0) = p0 log d - (p0/n) log M + (3/n) log((2M-1)/M)
                + log(1 + 6k(M-1)) / (2nk).
```

The blocked model gives the same form with `(n_i, k_i)` at level `i`.

*Proof.* Expand `log(r*/m*) - p0 log(B/A)` and divide by `2nk` (blocked
model: by `2P`). No ceiling or factor two appears. If `log ceil(r*/m*)`
is used instead, the expression can only increase. So any lower bound on
`Phi` bounds both exponents.

### Lemma 2 (quadratic contraction). Proved here; also checked exactly.

Put `q = d+2`, `T_d(R,B) = ((dB - R)/q, R)`, `Q(R,B) = R^2 + 4RB + B^2`
and `beta = lambda_d + 1/q`. Then for all real `R, B`

```
lambda_d^2 Q(R,B) - Q(T_d(R,B)) = (1 - beta^2) (R - lambda_d B)^2,
```

and `0 < beta < 1`.

*Proof.* Multiply by `q^2`. The difference is a polynomial in
`R, B, lambda, d`. It equals `G` times

```
2q R^2 + (4q - 2 - 2q lambda) R B + (q lambda^2 + lambda + d) B^2,
```

where `G = q lambda^2 + lambda - d`. The checker verifies this as an exact
polynomial identity for symbolic `d`.

For `beta < 1`: `q x^2 + x - d` is increasing on `x >= 0` and equals 1 at
`1 - 1/q`. Hence `lambda_d < 1 - 1/q`.

The round-11 review states different quotient factors `(q, 2(2q-1),
lambda+d)`. That is not an error: its script replaces `q^2(1-beta^2)` by
the representative `H = 2d + 3 - q lambda`, which agrees with it modulo
`G`, so its quotient differs. The review text does not say this.

### Lemma 3 (source–endpoint bound for every chain). Proved here.

Every legal chain with arities `d_1, ..., d_L`, optional swaps and extra
crops satisfies

```
s >= alpha z t + (4/3 - alpha) z - 1/3,     z = prod_i lambda_{d_i}^(-1),
```

for `alpha = 40/49`. The bound increases in `z`.

*Proof.*

1. **Centering.** With `R = r - 1/3`, `B = b - 1/3`, `C = c - 1/3`, the
   crop condition is exactly `C <= (dB - R)/q`. All centered coordinates
   are at least `2/3`.
2. **One step.** `Q` is symmetric and increasing in each coordinate on the
   positive quadrant. So Lemma 2 gives `Q(C,R) <= Q(T_d(R,B)) <=
   lambda_d^2 Q(R,B)`. This holds for every crop and both orientations.
3. **Iterate.** `Q(final) <= z^(-2) Q(initial)`.
4. **Initial value.** At fixed centered sum `s + 1/3`,
   `Q <= (3/2)(s + 1/3)^2`.
5. **Final value.** `r_final >= 1` gives
   `Q(final) >= Q(2/3, t - 1/3) = t^2 + 2t - 1/3`.
6. **Combine.** `s + 1/3 >= z sqrt((2/3)(t^2 + 2t - 1/3))`.
7. **Affine form.** With `u = t - 1`,
   `(2/3)(t^2 + 2t - 1/3) - (4/3 + alpha u)^2 = (2/7203) u^2 + (24/49) u >= 0`.

Note that `(4/3 - alpha) z - 1/3 > 0` for `z >= 1`.

### Lemma 4 (exact one-level bound). Proved here; new.

A legal chain with exactly one level of arity `d` (swaps and extra crops
allowed) satisfies `s >= (1 + 1/d) t + 1/d`.

*Proof.* After the optional input swap the state is `(r,b)`, the child is
`c`, and `t` is `r` or `c`.

- **Case `t = r`.** `d b >= (d+2)c + r - 1 >= r + d + 1`, so
  `s = r + b - 1 >= (1 + 1/d) r + 1/d`.
- **Case `t = c`.** `d b >= (d+2) c`, so
  `s >= b >= (1 + 2/d) c >= (1 + 1/d) c + 1/d`.

The bound is attained, for example by `(43,23)`, `d = 2`, `c = 1`.
It equals round 9's backward-weight bound at `L = 1`
(`v_1 = 1 + 1/d`, `C_1 = 1/d`).

### Lemma 5 (endpoint minimum). Proved here.

For `a, C > 0` and `2 <= p0 < 3`, the minimum over real `t >= 1` of
`3 log(a t + C) - p0 log t` is attained at

```
t* = max(1, p0 C / ((3 - p0) a)).
```

*Proof.* The derivative has the sign of `(3 - p0) a t - p0 C`.

No integrality of `t`, and no cutoff on the initial or terminal
dimensions, is used.

### Lemma 6 (no-gain levels). Proved here.

Let `M_max(n,d)` be the maximum of `M` over all types. Then
`M_max(n,d) <= d^n` in each of these cases:

- **`n = 1`.** The counts are `d - 1`, 2 and 1.
- **`n = 2`.** The counts are `(d-1)^2`, `4(d-1) <= d^2`, `2(d-1)`, 4, 4
  and 1.
- **`d >= 2n + 1`.** `M / (d-1)^n <= (2n/(d-1))^o (n/(d-1))^m / (o! m!) <= 1`,
  so `M_max = (d-1)^n < d^n`.

If `M_max(n,d) <= d^n`, then `C(n,d,k,M) >= 0` for every type and every
`k`.

The checker confirms `M_max` by exhaustive type enumeration on 598 small
cases and 320 large-arity cases. The proof covers all cases.

### Lemma 7 (pruning). Proved here.

Remove from the lower bound every level whose `M_max <= d^n`. In the
blocked model each level uses its own `n_i`.

This weakens the bound in two ways, both favorable to a candidate chain:

- it removes a factor `lambda_d^(-1) > 1` from `z`, which lowers the
  right side of Lemma 3;
- it removes a nonnegative cost.

The kept levels have source power at most `A`. No claim is made that the
shortened chain is legal.

If no level is kept, the actual chain gives `p >= 3`. Each level keeps the
maximum coordinate from increasing (`c < b`), so `t <= max(r_0,b_0) <= s`.
Also `B/A <= t^(2nk)` and `r*/m* >= s^(6nk)`, so `p >= 3`. This case
includes `n <= 2` and chains with no levels.

### Lemma 8 (largest sector count is favorable). Proved here.

Let `h(M) = 3 log((2M-1)/M) - p0 log M + log(1 + 6k(M-1))/(2k)`. Then
`C = p0 log d + h(M)/n`.

- **`M >= 2`, `p0 >= 2`, `k >= 1`.** The derivative satisfies
  `h'(M) <= 6/(2M-1) + 3/(6M-5) - 5/M`, which equals
  `-((M-2)(18M-11) + 3) / (M(2M-1)(6M-5)) < 0`.
- **`M = 1`.** A kept level has `M_max > d^n >= 8`, so `M_max >= 9`. Then
  `h(M_max) <= h_{2,1}(9) < 0 = h(1)`, because `17^6 * 49 < 9^10`.

Hence `C(n,d,k,M_i) >= C(n,d,k,M_max)` for every type at a kept level.

### Lemma 9 (power monotonicity, blocked model). Proved here.

For fixed `n, d` and `M >= 2`, the term `log(1 + a k)/k` with
`a = 6(M-1)` decreases in `k`, because `log(1+x) > x/(1+x)`. So
`k = floor(P/n)` is favorable for every block with `n k <= P`. The screen
then takes, for each arity independently, the minimum of the local cost
over all `3 <= n <= P` with `M_max(n,d) > d^n`.

### Census completeness. Proved here; enumeration reproduced.

After pruning, a nonempty kept multiset in the common model satisfies

```
3 <= n <= 64,   1 <= k <= floor(64/n),   d <= 2n,   M_max(n,d) > d^n,
(prod d)^(2nk) <= 2^128.
```

In the blocked model it satisfies

```
3 <= P <= 64,   d <= 2P,   d has some n <= P with gain,
(prod d)^(2P) <= 2^128.
```

The lower bound depends only on the multiset of kept arities (and on `n,k`
or `P`), not on their order or realizability.

My enumeration works differently from the producer's. It:

- builds multiplicity vectors under the integer bound
  `prod d <= x_max(e) = max{x : x^e <= 2^128}`;
- sorts them lexicographically, which is the producer's depth-first order;
- recomputes the census digest.

| Quantity | Common model | Blocked model |
| --- | ---: | ---: |
| `(n,d)` or `(P,d)` pairs with gain | 219 | 219 |
| eligible `(P,d,n)` choices | — | 3,744 |
| kept multisets | **1,752** | **1,326** |
| maximum depth | 21 | 21 |
| census SHA-256 | `030a70bd…77d6` (matches) | `91167745…9c1c` (matches) |
| counts per `(n,k)` / per `P` | match receipt | match receipt |

### Arithmetic

The checker computes the margins three ways.

- **Interval margins.** The checker uses its own `2*atanh` series in 240-bit
  fixed point, with directed rounding and an explicit tail bound, rounded
  outward to `2^-200`.
  - `lambda_d` is enclosed with 128-bit `isqrt`, and both ends are
    certified by the sign of `(d+2)x^2 + x - d`.
  - `z` is rounded to a 64-bit dyadic, downward for lower bounds and
    upward for upper bounds.
  - A lower bound uses `z_lo` and the exact minimizer `t*` from Lemma 5.
  - To certify that a *relaxed* margin is negative, it uses `z_hi` at
    `t*(z_hi)`. This is valid because the relaxed minimum is at most the
    value at any `t`, and that value increases in `z`.
- **Log-free integer signs (common model).** For `p0 = u/v`, multiply the
  margin by `2nkv`. Its sign is then the sign of

  ```
  S^(6nkv) prod d^(2nku) (2M-1)^(6kv) E^v  -  t^(2nku) prod M^(2ku + 6kv),
  ```

  with rationals `S = a t* + C` and `t*`. The checker evaluates this
  integer difference exactly for every multiset at 29/10, 59/20 and
  119/40, and for the one-level supplement.
- **Producer arithmetic.** The producer's 40-term exact atanh sum has a
  correct tail bound (about `1e-40`) and outward dyadic rounding. My values
  agree with it. With a finer rounding of `z`, my 2.9 minimum is
  `0.02156040020673011202679774…`, inside the producer's interval.

I did not line-audit every helper in the producer. Its conclusions are
reproduced independently, which is the stronger check.

## 4. Results

The relaxation alone (Lemmas 1–3 and 5–9) gives:

| Threshold | Common: open / 1,752 | Blocked: open / 1,326 | Minimum relaxed margin (both) | Exact integer signs (common) |
| --- | ---: | ---: | --- | --- |
| 29/10 | 0 | 0 | `+0.0215604002067301120268` at `n=32,k=2,(2)` / `P=64,(2)` | 1,752 positive |
| 59/20 | 17 | 21 | `-0.1446855244053638130` (certified `< -0.14468552440536381292`) | 1,735 positive, 17 negative |
| 119/40 | 48 | 29 | `-0.24545587207587150` | 1,704 positive, 48 negative |
| 5953/2000 | 51 | 31 | `-0.25213416082781039` | (intervals only) |

The open cases at 59/20 are:

- common model: `(n,k) = (16,4)`, `(17..21, 3)` and `(22..32, 2)`, all with
  arity multiset `(2)`;
- blocked model: `P = 44..64`, all with `(2)`.

At every listed threshold, every open case has the following form:

- **Forced one level.** The kept multiset is `(2)`, and `4nk > 128`
  (resp. `4P > 128`). A second level of any arity would make
  `A >= 2^(4nk) > 2^128`. So the physical chain has exactly one level, of
  arity 2.
- **Closed by Lemma 4.** Using Lemma 4 in place of Lemma 3 (same local
  costs and endpoint minimization) gives smallest margins
  - `+0.105206` at 59/20,
  - `+0.008435` at 119/40,
  - `+0.001997` at 5953/2000,

  all at `n=32, k=2` (resp. `P=64`).

The 119/40 value matches round 9's fixed-arity minimum `0.0084355975…`,
as it should.

A realized chain shows near-tightness: `(r_0,b_0) = (43,23)`, `d = 2`,
`c = 1`, `n = 32`, `k = 2`, type `(8,16,8)`. Its count is
`M = 506,980,245,130,444,800 = M_max(32,2)`, and `A = 2^128`, `t = 43`,
`s = 65`. Its exact pooled exponent lies in `(2.976960882, 2.976960883)`.
This is round 9's witness, recomputed.

The checker also confirms Lemmas 2–4 numerically:

- Lemma 2 on all 412,177 legal single steps with `r, b <= 60` and
  `2 <= d <= 8` (exact rationals);
- Lemmas 3 and 4 on all 102,712 (chain, terminal orientation) cases of
  legal chains of depth at most 3, with `r_0, b_0 <= 10`, arities
  `{2,3,4}` and all swaps and crops.

## 5. Problems found and fixes

1. **Wrong exponent in the statement (minor; fix in the paper's wording).**
   The notes call `log ceil(r*/m*)/log(B/A)` the "actual paid exponent".
   v5 pools all products of one depth, so its exponent has no ceiling.
   The screen never uses the ceiling, so it proves the ceiling-free
   bound. Fix: state the result for v5's pooled exponent.
2. **Threshold far from sharp (substantive improvement).** The 2.9 barrier
   is correct, but the method gives much more. The relaxation fails at
   59/20 only on forced one-level chains of arity 2. These are exactly the
   chains where Lemma 3 loses most: slope `alpha*z ≈ 1.376` against the
   exact `1.5` for `d = 2`. With Lemma 4 both models satisfy `p >= 119/40`
   (indeed `>= 5953/2000`), and a realized chain reaches `< 2.97697`.

   The note's sentence that "the present result does not infer either
   failure or success of those stronger thresholds" was accurate for the
   relaxation alone. It is superseded. The statement "the common-inventory
   relaxation fails to establish 2.95" is true as a statement about that
   relaxation, and only about it.
3. **Review description of the identity (documentation only).** The review
   lists quotient factors for a reduced representative of `1 - beta^2`
   without saying so. The identity itself is correct (Lemma 2).
4. **Scope that the paper must state.** The barrier concerns the count
   formulas of one recipe:
   - the source rank `s^6` per paired factor;
   - separator copies `(2M-1)^6` per level;
   - separate exactification at every level;
   - uncompressed auxiliaries `MM_{d^{2n}}`;
   - one retained type per level (or per block);
   - terminal first-input projection.

   It does not cover compressed auxiliaries, joint exactification, other
   source circuits, other terminal recipes, or levels that mix different
   block sizes. If the paper's construction changes any charge, the
   screen must be rerun.
5. **Wording of "realistic sizes".** `A <= 2^128` bounds the source side
   only. The witness's target side `B` has about 280 decimal digits. Say
   "source side at most `2^128`", not "realistic sizes".

No error was found in the census, the pruning, the mode replacement, the
endpoint minimization or the rounding.

## 6. Recommendation for the paper

State a short computer-assisted proposition in the section on finite
behavior, about half a page plus a one-paragraph proof sketch. Put the
census details in the supplement. Suggested statement:

> **Proposition (finite barrier).** Consider the paired shifted-chain
> recipe with uncompressed auxiliaries, separate exactification at each
> level, and terminal first-input projection. Allow any depth, arities
> `d_i >= 2`, positive initial dimensions, optional input/output swaps,
> legal extra crops, and any retained type at each level. Allow either a
> common inventory `n` and power `k`, or per-level `(n_i,k_i)` with
> `n_i k_i | P` and block repetition. If the resulting relative scheme
> has source side `A <= 2^128`, then its pooled exponent is at least
> `119/40`. Conversely, a one-level chain with `A = 2^128` has pooled
> exponent below `2.97697`.

*Proof sketch.*

1. A common quadratic potential (Lemma 2) gives, for every chain, the
   source bound of Lemma 3. One-level chains satisfy the exact bound of
   Lemma 4.
2. Levels with no possible sector gain have nonnegative normalized cost
   and can be dropped from the lower bound. If all are dropped,
   `t <= s` forces exponent at least 3.
3. Kept levels have `n >= 3` and `d <= 2n`. Replacing their types by the
   largest one, and their power by `floor(P/n)`, is favorable.
4. This leaves 1,752 (common) and 1,326 (blocked) arity multisets under
   the source cap. For each, the minimum over the real endpoint is
   explicit (Lemma 5).
5. Outward-rounded rational logarithms, and for the common model exact
   integer comparisons, show that every margin is positive. Lemma 4 is
   used for the forced one-level cases.

If the authors prefer not to add Lemma 4, state `p >= 29/10` instead. That
version needs only Lemmas 1–3 and 5–9. In either case, cite v5 for:

- relative schemes and the pooled exponent (`def:relative-scheme`,
  `lem:batch`);
- exactification (`lem:exactification`).

## Adversarial review

Date: 18 October 2026. Role: adversarial referee for this topic. I tried
to refute the note above. I re-derived the fragile steps myself, reran
every script, and wrote a separate check,
`experiments/shifted_chains_skeptic_gate.py` (run with
`python -I -B experiments/shifted_chains_skeptic_gate.py`, about 45
seconds). It does not import the round-11 producers. I did not delete or
change anything above this section.

### Verdict

I found no mathematical error in the note. Every lemma holds as stated,
and every count, open-case list and margin is reproduced by a second,
independent arithmetic path. The 2.95 claim is also confirmed: the
round-11 relaxation, used alone, cannot prove 59/20.

The main correction is that the note's final result is weaker than what its
own ingredients prove. With the same relaxation, the same forced-one-level
observation and the same Lemma 4, plus a finite search over one-level
chains, the bracket `[2.9765, 2.97697)` collapses to an exact value. **The
minimum pooled exponent of both models at `A <= 2^128` is attained by the
round-9 witness**:

```
p_w = log(r_w/m_w) / log(B_w/A_w) = 2.97696088251553944749816701...,

A_w = 2^128,             B_w = 43^128 M^4,
r_w = 65^384 (2M-1)^12 (12M-11),   m_w = M^12,
M   = 32!/(8! 16! 8!) 2^16 = 506,980,245,130,444,800.
```

The other points are minor wording and documentation fixes, listed below.

### What I re-derived (not by re-reading the note)

- **Lemma 1.** Direct expansion of `log(r*/m*) - p0 log(B/A)`, divided by
  `2nk` (or `2P`). Since `B > A`, `p < p0` is equivalent to `Phi < 0`.
  The ceiling never enters. v5's `def:relative-scheme` defines the pooled
  exponent without a ceiling, and `lem:batch` explains why. The note's
  framing correction is right.
- **Lemma 2, by hand.** Write `q = d+2`, and use only `q lambda^2 + lambda = d`
  and `beta = lambda + 1/q`. Compare the coefficients of
  `lambda^2 Q(R,B) - Q((dB-R)/q, R)` and
  `(1-beta^2)(R^2 - 2 lambda RB + lambda^2 B^2)`:
  - `B^2`: equality is `beta lambda = d/q`, which is
    `lambda^2 + lambda/q = d/q`.
  - `R^2`: equality is `lambda^2 + lambda/q + 2/q - 1 = 0`, the same
    relation.
  - `RB`: equality reduces to `lambda (q - 2 - d) = 0`.

  The script also checks the identity exactly in
  `Q(d)[lambda]/(q lambda^2 + lambda - d)` for `d = 2..400`. That
  `beta < 1` follows from `f(1 - 1/q) = 1` for `f(x) = q x^2 + x - d`.
- **Lemma 3.** The centering, the monotonicity of `Q` on the positive
  quadrant, the initial bound `(3/2)(s+1/3)^2`, the endpoint value
  `t^2 + 2t - 1/3`, and the residual `(2/7203)u^2 + (24/49)u` all check
  out. The bound also holds for chains with no levels.
- **Lemma 4, with realizability.** For a one-level chain of arity `d`
  with terminal `t`, the least source is exactly
  `s_min(t) = ceil(((d+1)t + 1)/d)`. It is attained by `(r,b) = (t, s-t+1)`
  with `c = 1`. The case `t = c` always needs `s >= ceil((d+2)t/d)`, which
  is never smaller.
- **Lemmas 5–9, pruning, and the all-dropped case.** These agree with
  the note. The numerator of the bound on `h'` is
  `-18M^2 + 47M - 25 = -((M-2)(18M-11) + 3)`.
- **Forced one level.** If the kept multiset is `(2)` and `4nk > 128`
  (blocked model: `4P > 128`), then any second level, kept or dropped, has
  arity at least 2 and would give `A >= 2^(4nk) > 2^128`. So the physical
  chain has exactly one level, and that level is the kept arity-2 level.
- **New observation (used below).** A one-level blocked chain with block
  `(n_1, k_1)` and `h = P/(n_1 k_1)` has `(r*, m*, A, B)` equal to the
  `h`-th powers of the common-model one-level scheme with `(n,k) = (n_1,k_1)`.
  So it has the same pooled exponent. The blocked one-level cases
  therefore reduce to common one-level chains with `nk <= 64`.

### Reruns

- `python -I -B experiments/shifted_chains_check_gate.py` passes in
  1 min 52 s, and its printed output matches the note.
- `python -m experiments.round11_variable_finite_gate --check`,
  `python -m experiments.round11_blocked_finite_gate --check`, and the nine
  round-11 gate tests all pass.

### Independent computation

**Arithmetic.** The skeptic script uses Python's `decimal` module at 90
significant digits. Its `ln`, `exp`, `sqrt` and basic operations are
documented to be correctly rounded. Every sign decision must clear a
padding of `1e-50`, which is at least 30 orders of magnitude above the
accumulated rounding error.

**Census.** The census is counted twice, by dynamic programming over
products and by recursion. Gaining `(n,d)` pairs are searched up to
`d = 4n+10` without assuming `n >= 3` or `d <= 2n`. The script asserts
that every gaining pair found has `n >= 3` and `d <= 2n`. It reproduces:

- 219 pairs and 1,752 multisets in the common model;
- 219 actions, 3,744 choices and 1,326 multisets in the blocked model;
- depth 21 in both models;
- the per-`(n,k)` and per-`P` counts of both receipts.

**Exhaustive checks on small cases.** All exact, except the local-cost
checks, which use the decimal arithmetic above:

- Lemmas 3 and 4 and `t <= s` on 1,830,516 chain endpoints: depth at
  most 3, `r_0, b_0 <= 10`, arities 2–7, all crops and swaps.
- Lemma 4 on 23,705,888 one-level cases with `r_0, b_0 <= 120` and
  `d <= 12`.
- Lemmas 6 and 8 on every type for `n <= 12`, five values of `k` and five
  thresholds: 196,400 cases.
- Every physical block `n k | P` (`P <= 14`, every type) against the
  blocked screen's local value: 12,768 cases.

**Margins.** The relaxed margins below use the exact `z`. "Lemma-4 margin"
is the smallest margin of the open cases after Lemma 4 replaces Lemma 3.

| Threshold | Open: common / blocked | Smallest relaxed margin | All open cases forced one-level | Smallest Lemma-4 margin |
| --- | ---: | --- | --- | --- |
| 29/10 | 0 / 0 | `+0.0215604002067301120268` | – | – |
| 59/20 | 17 / 21 | `-0.1446855244053638129468` | yes | `0.105206414490` |
| 119/40 | 48 / 29 | `-0.2454558720758715031782` | yes | `0.008435597576` |
| 5953/2000 | 51 / 31 | `-0.2521341608278103941362` | yes | `0.001997280670` |
| 2.9769 | 51 / 31 | `-0.2539310919385586207789` | yes | `0.000264342051` |
| 2.976961 | 51 / 31 | – | yes | closed exactly (below) |

The open lists at 59/20 match the note: common `(16,4)`, `(17..21,3)`,
`(22..32,2)`; blocked `P = 44..64`; all with arity multiset `(2)`.

### Findings

1. **The bracket is not sharp. The minimum is exact (major; this changes
   the recommended statement).** I prove the following.

   > **Proposition (sharp finite barrier).** In both the common and the
   > blocked count models, every relative scheme with `A <= 2^128` has
   > pooled exponent `p >= p_w = 2.97696088251553944749816701...`, with
   > equality for the one-level chain `(43,23) -> (1,43)`, `d = 2`,
   > `c = 1`, `n = 32`, `k = 2`, type `(8,16,8)`.

   *Proof.*

   - **(a) Multi-level and unforced cases.** Take `p_hi = 2976961/10^6`,
     so `p_w < p_hi`. At `p_hi` the relaxation leaves exactly 51 common
     and 31 blocked multisets open. All are forced one-level cases. If a
     chain had `p <= p_hi`, then `Phi(p_hi) <= 0`, and its kept multiset
     would be open. So every chain whose kept multiset is not open has
     `p > p_hi`.
   - **(b) Forced cases, `t <= 400`.** A forced case is a one-level chain.
     By the observation above, the blocked one-level cases reduce to
     common one-level chains with `nk <= 64`. For these, the largest type
     is optimal (Lemma 8 applied at `p0` equal to the exponent itself), and
     the exponent increases with `s`. So it suffices to check
     `s = s_min(t)`. A complete search covers every gaining `(n,k,d)` with
     `d^(2nk) <= 2^128` and every `t <= 400`. Its minimum is the witness.
     The runner-up is `2.976965805` (`n=32, k=2, d=2, t=45, s=68`).
   - **(c) Forced cases, `t > 400`.** For every gaining `(n,k,d)`, the
     real-`t` minimizer of the Lemma-4 margin at `p_hi` satisfies
     `t* <= 400`. The margin at `t = 400` is positive. So all chains with
     `t > 400` have `p > p_hi`.
   - **No kept levels.** Chains with no kept level have `p >= 3`
     (Lemma 7).

   *Certification.* Parts (a)–(c) are certified twice: by the decimal
   path, and by outward-rounded 200-bit intervals. For the intervals, the
   script loads the checker's logarithm code by file path. I audited that
   code line by line: `_two_atanh`, `log_int`, `iscale`, `isub`,
   `z_bounds`, `endpoint`. The witness interval is
   `(2.976960882, 2.976960883)`. Every other one-level datum has a
   certified exponent above `2.976965805`.

   *Consequences.*

   - **The stronger thresholds are decided.** The round-11 note left
     thresholds above 2.9 undecided. They are now decided: the family
     cannot reach 2.95, and its exact minimum at this cap is `p_w`. Only
     the round-11 relaxation, used alone, fails at 59/20.
   - **The weakness is local.** In windows, realized chains of depth 2
     and 3 are not even subcubic. The best depth-2 chain has exponent
     3.094, at `t = 299`, the edge of the window `t <= 300`; the best
     depth-3 chain has 3.265 (`t <= 150`).
     These come from the exact least source for every ordered word
     (smallest parent at each step, checked against brute force on 283
     cases). So below the cap, only one-level chains matter. This is why
     the quadratic relaxation fails exactly there. These depth-2 and
     depth-3 figures are window-limited evidence, not a theorem.

2. **The printed margins are lower bounds, not the quoted values (minor,
   documentation).** The checker's script rounds `z` down to 64 bits and
   prints certified lower bounds. At 29/10 it prints
   `0.0215604002067301119463…`, while the note's table quotes
   `…1120268`. The table's value is the exact-`z` value (my decimal path
   gives `0.0215604002067301120268`). Likewise, at 59/20 the note's
   `-0.1446855244053638130` is the `z_lo` lower bound; the exact value is
   `-0.1446855244053638129468`. Both are correct, but the note should say
   which number it prints.

3. **Ambiguous "resp." in the theorem statement (minor).** The note's
   T2 statement says "margins >= 0.008435 (resp. 0.001997)". There the
   "resp." refers to the thresholds 119/40 and 5953/2000, not to the two
   models; both models have the same smallest margin. Also, the exact
   integer-sign confirmation exists only for the common model. The
   blocked model rests on intervals, now confirmed by the decimal path as
   well.

4. **The proposition should state its charges as formulas (minor).**
   The suggested proposition names the scope in words. It does not show
   the source charge `s^6` per paired factor or the separator charge
   `(2M-1)^6`. The computer-assisted part is a statement about the four
   integers `A, B, r*, m*`. The paper should display them in the
   proposition, for both models, and let the construction section supply
   the restriction. This also makes clear that any change of charge
   (joint exactification, compressed auxiliaries, a cheaper source
   circuit, other terminals) requires rerunning the screen. The sharp
   value `p_w` depends on every charge.

5. **No other problems found.** The census is complete. The pruning is
   sound. The `M = 1` case and the blocked relaxation are correct. The
   outward rounding is correct. The claim that the relaxation fails at
   2.95 holds exactly as stated (17 common and 21 blocked negative gates).

### What I could not verify

- **The count model.** The stage relation with `(2M-1)^6` copies and
  degree `6(M-1)`, the source rank `s^6` per paired factor, and the
  terminal `MM_{t^2}` per factor are still taken from the notes. I checked
  only that they agree with round 8, equations (4)–(6) and (11), with
  round 9, equation (3), and with arity-ramp equation (7). I also checked
  by hand that `C(1,t)` symmetrized over the six orientations gives
  `MM_{t^2}`.
- **Library correctness.** The decimal path relies on the documented
  correct rounding of Python's `decimal` module. The interval path relies
  on the checker's code, which I audited but did not write.
- **Other caps.** Only the cap `2^128` was run.

### Statements I endorse

- **Lemmas 1–9, census completeness, and T1** (`p >= 29/10` in both
  models), as stated in the note.
- **R1:** the round-11 relaxation, used alone, cannot prove 59/20. It has
  17 common and 21 blocked negative gates, with minimum
  `-0.14468552440536381294…`.
- **T2** (`p >= 119/40`, and `>= 5953/2000`) is correct, and implied by
  the sharp proposition above.
- **Recommended for the paper: the sharp proposition.** Display the
  count formulas, cite v5 for `def:relative-scheme`, `lem:batch` and
  `lem:exactification`, and use this proof sketch:
  1. the common quadratic potential gives Lemma 3;
  2. no-gain levels are dropped, or `t <= s` gives `p >= 3`;
  3. the largest type and the largest power are favorable;
  4. the 1,752 / 1,326 multisets are screened at `2976961/10^6`;
  5. all open cases are forced one-level chains;
  6. the one-level chains are settled exactly by Lemma 4 and a search
     over `t <= 400`, with a monotone tail.

  If the authors want the shortest proof, state `p >= 29/10` (no Lemma 4
  needed). If they want a round number, state `p >= 119/40` with the
  witness. Either way, describe the 2.95 failure as a weakness of the
  relaxation, not of the construction.
