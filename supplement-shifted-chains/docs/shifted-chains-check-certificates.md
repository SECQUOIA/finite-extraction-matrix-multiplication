# Verification note: finite certificates in one cost model

Date: 18 October 2026. Topic key: `certificates`.

This note fixes one cost model for the finite certificates of the shifted-chain
construction, derives it from the cited v5 lemmas, and supplies a canonical
script, report and table for the follow-up paper. It also checks every finite
certificate tabulated in the round-8, round-10 and round-11 notes against this
model.

**Verdict.** The cost model used by the notes is correct, given the
single-orientation local relation of the shifted chain (checked in the separate
`maps` topic, not here). All 34 documented certificates that fit the model
reproduce exactly: digit counts agree, and the exponent intervals overlap
to 12 decimals. I found no numerical error in the notes. The problems are
in presentation. The notes use at least six different cost models under
similar names, and some headline comparisons mix them. They describe selected
witnesses in a way that could be read as minimal; at least one is not minimal
in its own model. The value of the v5 `a=4` bound quoted in the task (2.6289)
is wrong: v5 gives 3.628926097.

New files:

- `experiments/shifted_chain_certificates.py`: the canonical producer (standard
  library only, exact integers, outward-rounded rational logarithms).
- `results/shifted-chain-certificates.json`: its report.
- `tests/test_shifted_chain_certificates.py`: two narrow tests.
- `experiments/shifted_chains_check_certificates.py`: the verification run used
  for this note. It prints a report and writes no file.

## 1. What I checked and how

1. I re-derived the counts `A, B, r_*, m_*` of a chain from v5 Lemma 2.1
   (composition), Lemma 2.2 (exactification), Lemma 9.1 (rational
   interpolation, Lü's separator, rational exactification), Remark 4.7,
   equations (2.2), (2.6)–(2.8), and Lemma 2.4 (pooled recursion) with the
   fixed-batch bound (10.1). I compared the result with the formulas of
   `docs/round8-multiscale-construction.md` (5), (6), (11), (12),
   `docs/round8-terminal-inventory.md`, `docs/round10-adaptive-chain.md`,
   `docs/round11-arity-ramp.md` (7) and
   `docs/round11-finite-ramp-search.md` (1), (2).
2. I listed every variant of the model used in rounds 8–11 (Section 4) and
   chose one for the paper.
3. I wrote a new certificate script that does not import any earlier repository
   code. It has its own logarithm enclosure, chain builder, mode certificate and
   digit counter. It recomputes six witnesses from their parameters alone.
4. A separate verification script recomputes each witness again, this time
   with an independent logarithm (Python `decimal`, 80 digits) and with
   brute-force modes for `n <= 300`. It then rebuilds every documented
   certificate from the parameters stored in the round-8, round-10 and round-11
   receipts, using the canonical model functions, and compares the results with
   the receipts (Section 7).
5. A bounded floating-point screen selected two extra points at exactly the
   quality of v5's Table 2 rows `a=8` and `a=12`. The script then certified
   these points exactly (Section 8).

## 2. The cost model

### 2.1 Chains

A *level* is a quadruple `(r, b, d, c)` of positive integers with

```
d >= 2,    1 <= c < b,    (d+2) c <= d b - r + 1.                     (L)
```

Its parent pair is `(r, b)` and its child pair is `(c, r)`. The second
inequality says that the quotient width `d b - (d-1) c` is at least `3c+r-1`,
so the quotient can be cropped to the three-block reset. A *chain* is a list
of levels `(r_i, b_i, d_i, c_i)`, `i = 0, ..., J-1`, with
`(r_{i+1}, b_{i+1}) = (c_i, r_i)`. Put

```
s = r_0 + b_0 - 1   (source evaluation length),
t = b_J             (terminal side),  where (r_J, b_J) = (c_{J-1}, r_{J-1}).
```

**Lemma 1 (smallest parent; proved here).** Let `(r, b)` be a child pair and
`d >= 2`. The pair `(b, b')` with `b' = ceil(((d+2) r + b - 1)/d)` is the
parent with the smallest second entry such that `(b, b', d, r)` is a level. Its
slack `e = d b' - b + 1 - (d+2) r` satisfies `0 <= e < d`. Hence the forward
largest-child rule `c = floor((d b' - b + 1)/(d+2))` applied to `(b, b')`
returns `c = r`.

*Proof.* Condition (L) for the level `(b, b', d, r)` reads
`d b' >= (d+2) r + b - 1`, and `b'` is the least integer with this property,
so `0 <= e < d`. Also `b' >= ((d+2) r + b - 1)/d > r`, so `r < b'`. Finally
`(d b' - b + 1)/(d+2) = r + e/(d+2)` with `0 <= e/(d+2) < 1`. ∎

So a chain built backward from a terminal pair by smallest parents equals the
forward largest-child chain from its source. The script checks this for every
witness. Rounds 10–11 specify chains backward; round 8's terminal inventory
specifies them forward. Both are covered. Explicit smaller crops, as in
round 8's two-stage cycle, are legal levels too.

### 2.2 Types and sector counts

At each level the retained type is `(K, O, Mid)` with `K + O + Mid = n`:
`K` kernel positions (`d-1` labels each), `O` outer positions (2 labels) and
`Mid` middle positions (1 label). The sector count is

```
H = n!/(K! O! Mid!) * (d-1)^K * 2^O.
```

**Lemma 2 (mode certificate; proved here).** Let `w = (d-1, 2, 1)`. A type `a`
maximizes `H` over all types with sum `n` if and only if
`w_i a_j <= w_j (a_i + 1)` for all `i != j` with `a_j > 0`.

*Proof.* `log H = log n! + sum_i g_i(a_i)` with `g_i(a) = a log w_i - log a!`,
whose increments `log w_i - log(a+1)` decrease. Let
`Λ = max_i (log w_i - log(a_i+1))` and `λ = min_{j: a_j>0} (log w_j - log a_j)`.
The condition says `Λ <= λ`. For another type `b`, concavity gives
`g_i(b_i) - g_i(a_i) <= (b_i - a_i) Λ` if `b_i > a_i`, and
`<= -(a_i - b_i) λ` if `b_i < a_i`. The latter case needs `a_i > 0`. Since both
types sum to `n`, the total is at most `(Λ - λ) Δ <= 0`, where `Δ` is the
total increase. Conversely, if the condition fails for some `i, j`, moving one
position from `j` to `i` increases `H`. ∎

The script computes the type greedily and then asserts the exchange
conditions. This proves that the type is a mode. The counts depend only on
`H`, so tie-breaking between modes does not affect any certificate.

### 2.3 The stage relation

Write `Q_{r,b} = S^+_{r,b} S^-_{r,b}`, the six-orientation product of v5
(2.7). Here `n` is the number of factors **per sign**.

**Proposition 3 (stage relation; proved here, given the local maps).** Let
`(r, b, d, c)` be a level, `n >= 1`, a type with sector count `H`, and `k >= 1`.
Over `Q`, there is a degeneration (in the sense of v5 Section 2.3; the symbol
`⊵` below denotes a degeneration in the first display and a restriction in
the second) of degree at most `6(H-1)`:

```
(2H-1)^6 Q_{r,b}^{⊗n} MM_{d^{2n}}  ⊵  H^6 Q_{c,r}^{⊗n} MM_{H^2},
```

and a restriction, with `E = 1 + 6k(H-1)`:

```
E (2H-1)^{6k} Q_{r,b}^{⊗nk} MM_{d^{2nk}}  ⊵  H^{6k} Q_{c,r}^{⊗nk} MM_{H^{2k}}.
```

*Proof outline.* Fix `π ∈ S_3` and put `U = C(r,b) B_X(d)`. The input to this
proof is taken from `docs/round8-multiscale-construction.md`; it is examined in
the separate `maps` topic, and I did not re-verify it. It says the following. The shifted-chain basis change, the quotient
crop to width `3c+r-1`, the three-block reset and the retained-type
restriction are fixed maps that do not depend on `t`. They restrict
`(U^{⊗n})^π` to a sum of `H` sectors that share leg `π(1)`. After
word-dependent reindexing, every sector is `V^π`, with
`V = C(r,c)^{⊗(n-Mid)} (C(r,c)^{(23)})^{⊗Mid}`.

1. Lü's separator, v5 Lemma 9.1(b) with shared leg `π(1)`, gives
   `(2H-1) (U^{⊗n})^π ⊵ H (V B_X(H))^π` with degree at most `H-1`. The
   reindexing acts after separation, on all target variables, as in v5
   Corollary 4.8.
2. Tensor the six orientations with one parameter (v5 Lemma 2.1). The copies
   multiply to `(2H-1)^6` and `H^6`, and the degrees add to at most `6(H-1)`.
3. Identify the factors. For each sign class, the three oriented copies of
   `B_X(d^n)` and of `B_X(H)` give `MM_{d^n}` and `MM_H` (v5 (2.2)). Two
   classes give `MM_{d^{2n}}` and `MM_{H^2}`. In a class `A_σ`, each middle
   factor `(C^{(23)})^π = C^{π(23)}` lies in the opposite class. With the same
   `Mid` in all six orientations, the sector is `S^+` to the power `n` times
   `S^-` to the power `n`, that is, `Q_{r,c}^{⊗n} ≅ Q_{c,r}^{⊗n}` (v5 (2.8)).
4. Exactification (v5 Lemma 2.2, or Lemma 9.1(c) over `Q`) with `D = 6(H-1)`
   multiplies the source by `kD + 1 = E` and raises both sides to the power
   `k`. ∎

With the Fourier separator of v5 Proposition 4.6, the degree would be
`6(H-1)^2` and `E = 1 + 6k(H-1)^2`. All notes use Lü's separator. The
certificates are over `Q`: rational interpolation for the source (v5
Lemma 9.1(a)), the separator with nodes `1..2H-1`, and exactification with
nodes `1..E`.

### 2.4 The relative scheme of a chain

**Proposition 4 (chain counts; proved here, given Proposition 3).** Let a chain
have levels `i = 0..J-1` with arities `d_i`, common `n` and `k`, and sector
counts `H_i`. Put `E_i = 1 + 6k(H_i - 1)`. Then `r_* MM_A ⊵ m_* MM_B` over `Q`,
with

```
A   = prod_i d_i^(2nk),            B   = t^(2nk) * prod_i H_i^(2k),
r_* = s^(6nk) * prod_i (2H_i - 1)^(6k) E_i,
m_* = prod_i H_i^(6k).
```

If `B > A`, this is a relative scheme (v5 Definition 2.3).

*Proof.* Source supply: `Q_{r_0,b_0}` is a product of six oriented copies of
`C(r_0,b_0)`, each of rank at most `s` over `Q` (v5 Lemma 9.1(a)). Hence
`s^(6nk) MM_1 ⊵ Q_{r_0,b_0}^{⊗nk}`. Tensor this with the identity on
`MM_A ≅ ⊗_i MM_{d_i^{2nk}}`. Induction on `j`: suppose
`R_j MM_A ⊵ m_j [Q_{r_j,b_j}^{⊗nk} ⊗_{i>=j} MM_{d_i^{2nk}} MM_{B_j}]`. Multiply
the source by `α_j = E_j (2H_j-1)^{6k}`. Each of the `m_j` summands becomes
`α_j` copies, and Proposition 3, tensored with identities on the other
factors, turns them into `H_j^{6k}` summands. Then `R_{j+1} = R_j α_j`,
`m_{j+1} = m_j H_j^{6k}` and `B_{j+1} = B_j H_j^{2k}`. At the end, restrict
each `C(r_J, b_J)` to its first-leg variable `x_0`, giving
`C(1, b_J) = B_X(b_J)`. Then `Q_{1,t} ≅ MM_{t^2}` (v5 (2.6)), and the remaining
factor is `MM_{t^{2nk}}`. Each level is exactified before its output is
consumed. No degeneration parameter is shared between levels, and there is
no catalyst. ∎

The counts depend on the chain only through `s`, `t`, the multiset of
arities with their types, `n` and `k`. The intermediate pairs matter only for
legality (L).

### 2.5 Exponents and the batch ceiling

Put `x = r_*/m_*` and `G = log(B/A)`. Define

```
p      = log x / G                    (pooled exponent, v5 (7.9) and Lemma 2.4)
p_ceil = log ceil(x) / G              ("actual ceiling" in rounds 9-11)
Phi    = (log x + log 2) / G          (fixed-batch bound, v5 (10.1))
```

**Lemma 5 (proved here).** If `B > A`, then `2 <= p <= p_ceil <= Phi` and
`Phi - p = log 2 / G`. Also `p_ceil - p <= s^(-6nk)/G`.

*Proof.* Step 1 of v5 Lemma 2.4 gives `x >= (B/A)^2 > 1`. So
`ceil(x) <= 2x`, and `p >= 2`. Every factor of `x` other than `s^(6nk)` is at
least 1, so `x >= s^(6nk)` and `log ceil(x) - log x <= log(1 + 1/x) <= s^(-6nk)`.
∎

v5 Lemma 2.4 turns the scheme into an `O(n^p)` algorithm by pooling. Grouping
the products of one batch only among themselves gives exponent `p_ceil`, and
`Phi` bounds both (v5 Section 10.1). For every witness, `p_ceil` equals `p` to
more than a hundred digits. So the "actual ceiling" variant is the pooled
exponent in practice.

**Lemma 6 (least power; proved here).** For a fixed chain, types and `n`,
`Phi` strictly decreases in `k`, and `log A` increases in `k`. Hence, if `Phi`
at power `k` is below a target and `Phi` at `k-1` is not, then `k` is the least
qualifying power and gives the least `A` for that chain, types and `n`.

*Proof.* Divide the numerator and the denominator of `Phi` by `2k`. The
denominator `n log t + sum_i (log H_i - n log d_i)` does not depend on `k`. The
numerator is
`3n log s + sum_i [3 log((2H_i-1)/H_i) + log(1 + 6k(H_i-1))/(2k)] + log 2/(2k)`,
and `log(1 + a k)/k` decreases for `a > 0`, because `y/(1+y) < log(1+y)`. ∎

### 2.6 The model for the paper

I recommend one model:

- paired inventory with `n` factors per sign, the same type in all six
  orientations, and a common `n` and `k` at all levels;
- legal levels (L), with terminal side `t = b_J` (terminal `(1,1)` and `(1,t)`
  are special cases);
- Lü's separator and separate exactification at every level,
  `E_i = 1 + 6k(H_i-1)`;
- certified quantity `Phi`, exactly v5's (10.1) convention. A statement
  `Phi < q` then holds for both pooled and unpooled recursion.

Finite barriers, by contrast, should be stated for `p`, the smallest of the
three quantities. The round-9 and round-11 gates state theirs for `p_ceil`, but
their necessary inequality uses `log(r_*/m_*)`. Their barriers therefore also
hold for `p`, and the wording should say so.

## 3. Certified logarithms

The script encloses `log ν` for a positive integer `ν` as follows. Write
`ν = 2^e θ` with `1 <= θ < 2`. If `e > 192`, keep the top 193 bits:
`θ⁻ = floor(ν/2^{e-192})/2^{192} <= θ <= θ⁺ = θ⁻ + 2^{-192}`. Use
`log θ = 2 artanh(ρ)`, with `ρ = (θ-1)/(θ+1) ∈ [0, 1/3]`. Sum 110 terms of the
series with directed integer rounding at scale `2^{320}`: floors for the lower
bound, ceilings for the upper bound. Then add the tail bound
`2ρ^{221}/(221(1-ρ^2))` to the upper bound. The same routine gives
`log 2 = 2 artanh(1/3)`, and `log ν = e log 2 + log θ`. Every enclosure is a
pair of multiples of `2^{-320}`. All further operations are interval
arithmetic in exact rationals, and printed decimals are rounded outward to 12
places.

The integers `d_i`, `H_i`, `2H_i - 1`, `E_i`, `s` and `t` are formed exactly.
The largest are `H` and `E` for arity 30 in the 2.26 witness, with about
141,700 bits.
The numbers `A`, `B`, `r_*` and `m_*` are never formed; their logarithms are
sums with exact integer multipliers.

The digit count of `X = prod base^exponent` is `floor(log10 X) + 1`. If the
enclosure of `log10 X` contains an integer `m`, the script writes
`X/10^m = 2^(α-m) 5^(β-m) Q`, with `Q` coprime to 10, and decides the sign
exactly. This case occurs: the round-8 `d=100` certificate has
`A = 10^(4.08·10^16)` exactly.

On ten test integers of up to 300,000 bits, including `2`, `10^50` and `3^1000`,
the enclosures contain the `decimal` reference values. Their widths are about
`10^{-94}` for small integers and `10^{-58}` for large ones. One unit test
compares a certified `Phi` interval with exact integer inequalities
`(2r_*)^v A^u < m_*^v B^u` on a tiny chain.

## 4. Variants of the model used in the notes

| Variant | Where | Difference from the paper model | Decision |
| --- | --- | --- | --- |
| Terminal `(1,1)` | round 8 construction, round 11 | `t = 1` | special case |
| Terminal `(1,t)` | round 10 adaptive | factor `t^(2nk)` in `B` | special case |
| Terminal `(r_f, b_f)` with first-input projection | round 8 terminal inventory, round 9/11 gates | `t = b_f`, `r_f > 1` | included (`t = b_J`) |
| Explicit types `((d-1)t, 2t, t)`, explicit crops | round 8 construction | not modes; second crop smaller than the maximum | included (any type, any legal crop) |
| `p_ceil` ("actual ceiling") | round 10 terminal parity, round 9/11 gates | `log ceil(x)` instead of `log x + log 2` | not used for certificates; equals `p` in practice |
| Ceiling charge `2^(-3Nk)` | round 10 unpaired | a valid upper bound for `p_ceil` | not used |
| Single sign at the terminal step, odd effective powers | round 10 terminal parity | `E = 1+3k(M-1)`; `single(N,2k) = paired(N,k)` | outside the model |
| Unpaired inventories | round 10 unpaired | `E = 1+3k(M_+ + M_- - 2)`, separate types per sign | outside the model |
| Different `(n_i, k_i)` per level, replicated blocks | round 11 blocked gate | exponents `2P`, `6P/n_i`, `P/(n_i k_i)` | outside the model |
| Direct asymmetric controls (`A = 1`) | round 8 row skipping, round 10 | a single tripling to matrix tensors, not a chain | outside the model |
| Compressed auxiliaries | rounds 10, 12–14 | changes `A` | outside the model |

Some headline numbers in the notes belong to different rows of this table. For
example, the 1,290-digit point "below 2.77429" (round 10) uses a single sign
with the odd power `k = 21`, which a paired chain cannot have (it would be
paired `k = 10.5`). It is certified only with `p_ceil`; its `Phi` is above the
target. In the paper model the same threshold needs 1,295 digits. Within the
round-10 grid, the paired chain with `p_ceil` also needs 1,295 digits, so the
saving needs both the odd power and the dropped `log 2` term. The round-10
notes say this. The summary table in `docs/round10-alternative-constructions.md`
lists both numbers side by side without saying that they come from different
models.

## 5. The witnesses

Each witness is given by a strict target, a terminal pair, the arities from
source to terminal (run-length notation `d^m`), and `n` and `k`. The chain is
built backward by smallest parents, and the type at each level is a certified
mode. The ramp suffix `R` stands for the forward arities `3R-3, 3R-4, ..., 6,
5, 3, 2` of the zero-slack ramp from `(R,R)` to `(1,1)` (round 11 (3)). All
values below were recomputed from these parameters.

| Strict target | Terminal | Arities, source first | `J` | Source pair | `n` | `k` | `Phi <` | `p <` | Digits of `A` | Digits of `B` |
| --- | --- | --- | ---: | --- | ---: | ---: | --- | --- | ---: | ---: |
| 3 | (1,128) | 2 | 1 | (128, 66) | 24 | 2 | 2.999745128438 | 2.998409790289 | 29 | 255 |
| 2.77429 | (1,5) | 2 | 1 | (5, 4) | 215 | 10 | 2.774233389609 | 2.774162598476 | 1,295 | 5,547 |
| 2.7 | (1,3) | 2^5 | 5 | (18, 27) | 147 | 8 | 2.699881286935 | 2.699814165503 | 3,541 | 8,025 |
| 2.5 | (1,3) | 2^16 | 16 | (5205, 8798) | 248 | 14 | 2.499900050612 | 2.499891610132 | 33,446 | 69,111 |
| 2.3 | (1,1) | 2^121, ramp `R=3` | 125 | 28-digit pair | 1,999 | 80 | 2.299993369880 | 2.299993344449 | 12,371,380 | 24,208,459 |
| 2.26 | (1,1) | 4^1244, ramp `R=11` | 1,264 | 166-digit pair | 28,336 | 1,118 | 2.259999981185 | 2.259999981163 | 48,859,824,830 | 62,827,651,353 |

The source sides are

```
2^96,  2^4300,  2^11760,  2^111104,
2^39020480 * (3*5*6)^319840,
4^78818964224 * prod_{d in {2,3,5,6,8,9,...,29,30}} d^63359296.
```

Here `2nk` is 319,840 and 63,359,296 in the last two rows. The modes are
`(6,12,6)`, `(54,108,53)`, `(37,74,36)` and `(62,124,62)` for the first four
rows. For the 2.3 witness they are `(500,1000,499)` at `d=2`, `(800,800,399)` at
`d=3`, `(1143,571,285)` at `d=5` and `(1250,500,249)` at `d=6`. The 21 modes
of the 2.26 witness are in the report; at the bulk arity `d=4` the mode is
`(14169,9445,4722)`. For every row, `Phi` at `k-1` is certified to be at least
the target, so `k` is the least power for that chain, types and `n` (Lemma 6).
For every row, the lower end of the `p` interval exceeds 2, as v5 Lemma 2.4
requires.

The 2.77429 threshold lies just below `3 log 40 / log 54 = 2.7742999804...`,
the exponent of a rank-40 scheme for `3×3` by `3×6` products.

**Provenance.** The first four rows are the round-10 adaptive witnesses. The
last two are the round-11 finite-ramp witnesses. They are the smallest
**documented** sources in this model at their thresholds. I compared each with
all other documented certificates that fit the model: round 8 (2,312 /
12,947 / 16,184 / 84,154 / 28,841,545 / 146,801,351,550 digits), the round-10
nonconstant-arity and `C(3,3)` controls (234 / 2,055 / 4,444 / 35,787 and
80 / 1,444 digits), and round 11's finite-search rows at 2.77429, 2.7 and 2.5
(5,549 / 8,969 / 57,275 digits). Round 11's ramp table has no row below 2.26.
The witnesses are not minimal in the model. The
screen of Section 8, with `n` up to 700 instead of the round-10 cap of 256,
finds a smaller point below 2.5: terminal `(1,3)`, 15 levels of arity 2,
`n = 264`, `k = 14`, source `(3098, 5205)`, `A = 2^110880`. It has
`Phi < 2.499903515815`, 33,379 digits of `A` (documented: 33,446) and 69,247
digits of `B`. I kept the documented witness in the table, because it is
traceable to the notes. The paper should call the witnesses "selected", not
"smallest".

## 6. Statements and their status

| Statement | Status |
| --- | --- |
| Lemma 1 (smallest parent = forward largest child) | proved here |
| Lemma 2 (exchange characterization of modes) | proved here |
| Proposition 3 (stage relation, degree `6(H-1)`, `E = 1+6k(H-1)`) | proved here from v5 lemmas, **given** the single-orientation local relation of round 8, which I took from the notes (checked in the `maps` topic) |
| Proposition 4 (chain counts `A, B, r_*, m_*`) | proved here, given Proposition 3 |
| Lemma 5 (`2 <= p <= p_ceil <= Phi`, `Phi - p = log 2/G`) | proved here (uses v5 Lemma 2.4, Step 1) |
| Lemma 6 (least power) | proved here |
| Logarithm enclosure (Section 3) | proved here; checked against `decimal` on test values |
| Six witnesses (Section 5) | computer-assisted, exact rational certificates; independently recomputed with `decimal` logarithms; modes brute-forced for `n <= 300` |
| Agreement of the 34 documented certificates with the model | checked (Section 7) |
| v5 comparison points (Section 8) | computer-assisted, exact; selection by a bounded float screen |
| Minimality of any witness | **not** claimed; disproved for the documented 2.5 witness |

## 7. Comparison with the notes

`python -I experiments/shifted_chains_check_certificates.py` rebuilds each
documented certificate from the parameters in its receipt and evaluates it in
the canonical model. These are round 8's construction table (4 rows, explicit
types and crops), round 8's terminal inventory (11 rows, forward chains, `t =
b_f`), round 10's adaptive, nonconstant-arity and `C(3,3)` certificates (10
rows), round 11's ramp table (4 rows, `R = 8D`) and round 11's finite search
(5 rows), 34 certificates in all; the six witnesses of Section 5 are among
them. The receipts' chain endpoints, initial sides and source pairs are also
checked. **All 34 agree.** Every documented digit count of `A` and `B` is equal
(round 8's construction table lists only `A`), and each exponent interval
overlaps the receipt's interval (they differ only
beyond the 12th decimal, where both are rounded outward). The ratios of digit
counts 2.3313 and 3.0045 quoted in `docs/round11-finite-ramp-search.md` are
also correct.

Discrepancies and problems found:

1. **Task text, not the notes.** The task quotes the v5 `a=4` bound as
   2.6289. v5's Table 2 in Section 10 (the PDF numbers it Table 2, not 10.1)
   and `results/multiway-finite-costs.json` give `3.628926097`, which is
   above 3. The `a=8` and `a=12` bounds are 2.848599165 and 2.675820359.
2. **Several cost models under one name** (Section 4). The paper must use one
   model and state it.
3. **Wording about the ceiling.** `docs/round11-finite-ramp-search.md` says
   that the extra `log 2` "charges the integer ceiling in the pooled
   algorithm", and `docs/round9-multiscale-finite-gate.md` speaks of
   "`ceil(r_*/m_*)` pooled calls". The pooled recursion of v5 Lemma 2.4 has no
   ceiling; the `log 2` term pays for the ceiling of the *unpooled* fixed-batch
   recursion.
4. **Selected is not minimal.** See the 2.5 example in Section 5.
5. **Notation.** `N` means inventory per sign in rounds 8 and 10 adaptive, but
   total inventory in the round-10 unpaired table, where "paired `N=56`" means
   28 per sign. `M` denotes both the sector count and the middle population
   (`M_d^{pop}`). `L` denotes bulk levels in round 11 and all levels in round 8.
   The paper should use `n` per sign, `H` for the sector count, `Mid` for the
   middle count and `J` for the number of levels.
6. **Barrier quantity.** See Section 2.6: the round-9 and round-11 finite gates
   prove more than they state, namely bounds on `p`.

No discrepancy affects a certified number.

## 8. Comparison with the v5 Table

v5's Table 2 bounds the same fixed-batch quantity (v5 (10.1)), relaxed to the
sufficient expression (10.5), for the v5 construction with `N = 1`, `k = 32`
and `j = 128 a ℓ_a`. A bounded float screen selected shifted-chain points
below the `a=8` and `a=12` bounds: terminal `(1,t)` with `t <= 40`, at most 40
levels of arity 2, `n <= 700`, least `k`, minimizing `A`. These points are
certified exactly in the canonical report under `comparisons_with_v5`:

| v5 row | v5 bound | v5 digits of `A` | Shifted chain | `Phi <` | Digits of `A` | Digits of `B` |
| --- | --- | ---: | --- | --- | ---: | ---: |
| `a=4` | 3.628926097 | 84,456,434 | the 3 witness | 2.999745128438 | 29 | 255 |
| `a=8` | 2.848599165 | 11,877,489,885 | terminal (1,7), one level `d=2`, `n=81`, `k=5`, source (7,5), `A=2^810` | 2.847987609862 | 244 | 1,153 |
| `a=12` | 2.675820359 | 234,905,651,862 | terminal (1,3), 7 levels `d=2`, `n=153`, `k=7`, source (49,78), `A=2^14994` | 2.675700755750 | 4,514 | 9,831 |

At equal or better certified quality, the shifted chain's source has about
`4.9·10^7` times fewer digits than v5's `a=8` example and `5.2·10^7` times
fewer than the `a=12` example. The 2.5 witness (33,446 digits, `Phi < 2.4999`) also
dominates `a=12` in both quality and size.

v5's examples were chosen to illustrate its overheads, not to minimize `A`.
A fairer statement uses v5 Corollary 11.2(a): every scheme of the v5
construction with `p < 3` satisfies `p > 9/4 + (9/2) log(6/5)/log(2 log A)`.
For `p < 2.26`, this forces `log A > 2.14·10^35`, that is, more than
`9.29·10^34` digits, while the 2.26 witness has `4.89·10^10` digits. At
`p < 2.3`, the same bound only forces about `2.9·10^6` digits, so it does not
exclude a v5 scheme smaller than the 12.4-million-digit witness. No such v5
example is documented. At 2.5 and above, the bound is trivial.

## 9. Recommendation for the paper and reproduction

The paper should have a section "Finite examples" of about 1.5–2 pages:

- Proposition 4, with the proof of Sections 2.3–2.4, citing v5 Lemmas 2.1, 2.2,
  2.4 and 9.1 and the shifted-chain local relation;
- the definition of `Phi` as v5 (10.1), with one sentence from Lemma 5;
- the witness table of Section 5 (the `p` column may be dropped), with the
  types and source sides in a footnote or in the supplementary report;
- one paragraph comparing with v5's Table 2 and Corollary 11.2(a), as in
  Section 8;
- one sentence that the witnesses are selected, not minimal, and that the
  certificates are over `Q`.

Reproduction, from the repository root:

```sh
python -I experiments/shifted_chain_certificates.py --check   # about 0.5 s
python -I experiments/shifted_chains_check_certificates.py    # about 4 s
python -I experiments/shifted_chains_check_certificates.py --screen   # +26 s
python -m pytest -q tests/test_shifted_chain_certificates.py
```

The first command recomputes the report and compares it byte for byte. Without
`--check`, it rewrites `results/shifted-chain-certificates.json`. The two
tests check the closed-form counts of a two-level chain with mixed arities
against a composition from the v5 primitives (brute-force sector counts, six
orientations, per-level exactification), check the certified `Phi` interval
against exact integer comparisons, and run `--check`.

What I did not verify: the local maps and the parity bookkeeping of the shifted
chain (`maps` topic); the asymptotic resource bounds (other topics); whether
any witness is close to the minimum in the model.

## Adversarial review

Reviewer: adversarial referee for topic `certificates`, 18 October 2026.
I tried to refute the note above. I re-derived the fragile steps on my
own, reran the checker's scripts, and wrote an independent check,
`experiments/shifted_chains_skeptic_certificates.py`. It shares no code
with the canonical producer, except in its last part, which also passes
the new comparison points through the canonical `certificate` function.

**Verdict.** The cost model, the six witnesses, the least-power claims,
the comparison with 34 documented certificates, and the smaller 2.5 point
all hold. I found no numerical error in any certified number. I found
six small problems, listed in "Problems found" below. The most important
one is the comparison with v5's Table 2: the two chain points beat v5's
relaxed bound `Phi-bar`, but not the exponent of v5's actual schemes.
Points that do beat those schemes need 280 and 4,653 digits, not 244 and
4,514. No conclusion of the note changes.

### What I reran

- `python -I experiments/shifted_chain_certificates.py --check`: OK, 0.4 s.
- `python -I experiments/shifted_chains_check_certificates.py`: ALL
  CONSISTENT, 2.8 s. I checked that it reads the receipts from `results/`
  (the notes' own files), not the canonical report. The printed "doc"
  values are truncated for display only.
- `python -m pytest -q tests/test_shifted_chain_certificates.py`: 2 passed.
- `python -I experiments/shifted_chains_skeptic_certificates.py --screen`:
  ALL CHECKS PASSED, about 4 minutes. Most of that time goes to the exact
  integer certificate for the 2.7 witness.

### Independent re-derivations

1. **Model against v5.** I read v5's Lemmas 2.1, 2.2 and 2.4, Definition
   2.3, Proposition 4.6, Lemma 9.1(a)-(c), equations (2.1), (2.2) and
   (2.6)-(2.8), equation (10.1), and Lemma 10.2. The equation and theorem
   numbers cited in the note match `manuscript/build/main.aux`. Table 2 is
   indeed numbered 2. In v5's notation, `Phi` is exactly (10.1):
   `(log(r_*/m_*) + log 2)/log(B/A)`. Lemma 9.1(b) is Lü's separator. It
   uses `2M-1` source copies, has degree `M-1`, and outputs
   `⊕_g T_g B_X(M)`, that is, `M` copies of `V B_X(M)` when every sector
   is isomorphic to `V`. Tensoring six orientations gives `(2H-1)^6 -> H^6`
   with degree `6(H-1)`. Lemma 9.1(c) gives `E = kD+1` rational nodes.
   Hence `E = 1 + 6k(H-1)`, and Proposition 3 follows from Proposition 3a
   as the note says.
2. **Separate exactification is the right model, not just a safe one.**
   v5 Lemma 2.1 covers two things: `t`-free maps before and after one
   degeneration, and tensor products of degenerations with one parameter.
   It does not cover two `t`-dependent degenerations applied one after
   the other. The separator's Laurent maps contain `t^{-e}`, so applying
   level `i+1` to the nonconstant coefficients of level `i` produces
   negative powers. A joint exactification across levels would need a
   substitution `t -> t^a` and a new lemma; the degrees would not simply
   add. So the per-level factors `E_i`, which round 11 (7) also states
   explicitly, are what v5's lemmas support.
3. **One step of Proposition 3a (maps topic, checked here only in part).**
   I re-derived the three-block reset of the cropped quotient
   `C(r, 3c+r-1)`. The outer input blocks `[0,c)` and `[r+2c-1, r+3c-1)`
   produce outputs in `[0, r+c-1)` and `[r+2c-1, 2r+3c-2)`. The middle
   input block `[c, r+2c-1)`, restricted to the output gap
   `[r+c-1, r+2c-1)`, is `C(r,c)^{(23)}` after the reversal
   `α -> r-1-α`. The only cross terms go from the middle input to the
   outer outputs. This holds for every `r, c >= 1`, including `r > c`.
   For example, the 3-witness level `(128, 66, 2, 1)` has `B = 131 >= 130`
   and sectors `C(128,1)`. I did not re-verify the kernel maps or the
   tensor-power cross terms; they stay with the `maps` topic.
4. **Lemmas 1, 2, 5, 6 and 7.** I re-derived each proof and found no gap.
   For Lemma 7, I checked the directed rounding line by line: floors and
   ceilings at scale `2^320`, the tail bound
   `ceil(high_power * q^2/(221(q^2-p^2)))`, and the top 193 bits taken
   with `θ+ = θ- + 2^-192 <= 2`.
5. **A complete mode search that does not use the exchange certificate.**
   Every maximizer `a` of `H` satisfies
   `n w_i/W - 1 <= a_i <= n w_i/W + 2`, where `W = d+2`. For the lower
   bound: if `a_j > 0`, then `w_i/(a_i+1) <= w_j/a_j`. The minimum of
   these ratios is at most `(sum of w_j over a_j>0)/n <= W/n`. The upper
   bound follows because the entries sum to `n`. My script searches this
   box completely, about 16 points per arity, for every `n`. It returns
   the same sector counts as the canonical modes for all 21 arities of
   the 2.26 witness and for all other rows.

### Independent recomputation

My script builds each chain backward. It tests legality in round 8's
original form: `h = b-c >= 1`, and quotient width `b+(d-1)h >= 3c+r-1`.
It checks that `b'-1` is illegal at every step and replays the chain
forward. It uses complete-box modes. For logarithms it uses Python
`decimal` `ln` at 90 digits, which the module documents as correctly
rounded. Each result is widened by two ulps, and all further operations
use interval arithmetic with `ROUND_FLOOR`/`ROUND_CEILING` contexts. This
method is rigorous and differs from the canonical artanh enclosure.
Results:

- All eight report entries (six witnesses and two v5 comparison points)
  match the report. The digit counts of `A` and `B` are equal. The `Phi`
  interval lies inside the canonical one. The source pairs and modes
  agree. Each entry passes, and its `k` is least.
- The smaller in-model point below 2.5 (terminal `(1,3)`, `2^15`,
  `n=264`, `k=14`) is confirmed: `Phi < 2.4999035159`, 33,379 digits of
  `A` and 69,247 of `B`.
- The largest sector count in the 2.26 witness has 141,668 bits, and its
  `E` has 141,680 bits. This matches the note's "about 141,700 bits".
- **Exact certificates that use no logarithms.** For `q = u/v`,
  `Phi < q` holds if and only if `(2r_*)^v A^u < m_*^v B^u`. I chose a
  simple rational between the certified bound and the target, then
  compared the full integers. All of the following hold:

  | Point | `Phi(k) <` (exact) | `Phi(k-1) >=` (exact) |
  | --- | --- | --- |
  | below 3 | 11771/3924 | 52/17 |
  | below v5 `a=8` bound | 94/33 | 20/7 |
  | below 2.77429 | 971/350 | 111/40 |
  | below 2.7 | 2276/843 | 46/17 |
  | below v5 `a=12` bound | 586/219 | 35/13 |

  So for these five points, both the certificate and the least-power
  claim are proved by integer comparison alone. For the 2.5, 2.3 and 2.26
  witnesses the integers are too large for CPython without `gmpy2`. They
  rest on the two independent rigorous logarithm methods.
- The quoted arithmetic is correct: `3 log 40/log 54 = 2.7742999804`.
  v5 Corollary 11.2(a) forces `log A > 2.1406e35`, that is, more than
  `9.296e34` digits, for `p < 2.26`. It forces more than `2.90e6` digits
  for `p < 2.3`.

### Problems found

1. **Minor, but it affects a headline claim: the v5 comparison points are
   tuned to v5's relaxed bound, not to v5's schemes.** Table 2 of v5 has
   two exponent columns. One is the certified relaxed bound `Phi-bar`
   (2.848599165 and 2.675820359). The other is the computed `Phi`, a
   floating-point value: 2.8406393 and 2.6728401. The chain points of
   Section 8 have `Phi < 2.84799` and `Phi < 2.67571`. Both are **worse**
   than the exponents of v5's actual `a=8` and `a=12` schemes. The note's
   phrase "at equal or better certified quality" is literally true, but
   the summary's "at the quality of v5's a=8 and a=12 rows" overstates
   it. My screen covered terminals `(1,t)` with `t <= 64`, up to 60
   levels of arity 2, and `n <= 1500`; floating point was used only to
   select points. Every selected point is certified both by my method and
   by the canonical `certificate` function, and its `k` is least:

   | Target (below v5's computed `Phi`) | Chain | `Phi <` | Digits of `A` | Digits of `B` |
   | --- | --- | --- | ---: | ---: |
   | 2.84063 (`a=8`, v5 `Phi` 2.8406393) | terminal `(1,5)`, one level `d=2`, `n=93`, `k=5`, `A = 2^930` | 2.840553213477 | 280 | 1,190 |
   | 2.67283 (`a=12`, v5 `Phi` 2.6728401) | terminal `(1,3)`, 7 levels `d=2`, `n=138`, `k=8`, `A = 2^15456` | 2.672186713007 | 4,653 | 10,114 |

   The targets lie about `1e-5` below v5's computed `Phi`. v5 states that
   pooling lowers `Phi` by less than `1e-7`, so these targets are also
   below v5's pooled exponents `p`, provided v5's floating-point values
   are accurate to `1e-6`. The ratios become about `4.2·10^7` (`a=8`) and
   `5.0·10^7` (`a=12`). The conclusion does not change. **Fix:** in the
   paper, compare at v5's computed `Phi` using the two points above, or
   keep the old points and state explicitly that they beat only v5's
   relaxed bound.
2. **Minor: the size measure.** At moderate quality, digits of `A` alone
   are not a robust measure of size. The round-10 direct asymmetric
   controls are relative schemes with `A = 1`. They reach 2.77429 with a
   414-digit `B` (407 digits with the actual ceiling), and 2.7 with a
   3,236-digit `B`. They beat the chain in both `A` and `B` at those
   targets (round 10, reproduced in the note's Section 4 table as
   "outside the model"). The paper's table should keep the `B` column,
   and the v5 paragraph should mention `B` too. From v5's report,
   `log(B/A) = kj Delta_N` with `Delta_N` at least 13,779.05 for `a=8`
   and 100,856.04 for `a=12`. So v5's `B` has more than `1.24·10^10`
   and `2.43·10^11` digits, and the comparison by `B` is just as
   lopsided. The paper should add one sentence: at qualities of 2.7 and
   above, the chain is not the smallest known scheme of this kind; its
   advantage is near 9/4.
3. **Minor: a wrong statement in the open points.** "`Phi - p` is below
   `1e-4` for all witnesses" is false. It is `1.34e-3` for the 3 witness
   and `3.3e-4` for the `a=8` comparison point (and `7.1e-5`, `6.7e-5`,
   `8.4e-6`, `2.5e-8`, `2.2e-11` for the others). The choice of `Phi` for
   the certificates is still sound. **Fix:** state the actual differences,
   or say "below `1.4e-3`".
4. **Minor: a rounding error in the summary and recommendation.** "More
   than 9.3e34 digits" does not follow from v5 Corollary 11.2(a). The
   bound gives more than `9.296·10^34`. Section 8 of the note correctly
   says `9.29·10^34`; use that.
5. **Minor: status labels.** In the checker's JSON statements, Proposition
   3, Proposition 4, the six-witness theorem, the v5 comparison points
   and the 2.5 remark are labelled `proved-here`. Each depends on
   Proposition 3a, which was taken from round 8 unchecked. Section 6 of
   the note states this condition correctly. The labels should read
   "proved here, conditional on Proposition 3a (maps topic)". The paper
   must cite the local relation as a proved lemma before the table.
6. **Minor wording and code robustness.**
   - "Ramp `R=11` (30,29,...,3,2)" in the JSON summary and the witness
     statement reads as all of 30 down to 2. The actual arities are
     `3j, 3j-1` for `j = 10, ..., 1`; they skip 28, 25, ..., 4. Section 5
     of the note gives the correct set; the paper should write the
     formula.
   - "The pooled recursion of v5 Lemma 2.4 has no ceiling" is loose. v5
     (2.9) contains `ceil(ν_ℓ/m_*)`; pooling removes the ceiling from the
     exponent, not from the recursion.
   - The canonical producer's checks are `assert` statements, including
     the mode exchange certificate, legality in `backward_chain`, and
     `p > 2`. Under `python -O` these checks are silently removed.
     Explicit exceptions would be safer for a shipped certificate script.
     The results are not affected under `python -I`.
   - `composed_counts` in the test re-types the same per-level formulas
     in product form. It guards the bookkeeping of multiplicities and
     exponents, but not the model itself. The model check that matters is
     the tensor-level local relation in the `maps` topic. The test should
     be described as a bookkeeping check.

### Final statements I endorse

The status markers below come from this review.

- **Model (proved here, conditional on Proposition 3a).** Proposition 3,
  Proposition 4 and Lemmas 1, 2, 5, 6 and 7 as stated in Sections 2-3.
  This means: paired inventory, common `n` and `k`, legal levels (L),
  `t = b_J`, Lü's separator over `Q`, per-level `E_i = 1+6k(H_i-1)`, and
  certified quantity `Phi = (log(r_*/m_*) + log 2)/log(B/A)` (v5 (10.1)),
  with `2 <= p <= p_ceil <= Phi` and `Phi - p = log 2/log(B/A)`.
- **Witnesses (computer-assisted, conditional on Proposition 3a).** The
  table of Section 5 is correct as printed. I certified it independently,
  and the 3, 2.77429 and 2.7 rows also exactly, without logarithms. In
  each row `k` is the least power for its chain, `n` and modes. The rows
  are selected, not minimal. The 2.5 row can be replaced by terminal
  `(1,3)`, `2^15`, `n=264`, `k=14`: `Phi < 2.499903515815`, 33,379 and
  69,247 digits.
- **Comparison with v5 (computer-assisted).** Below v5's computed `Phi`
  for `a=8` and `a=12`, the shifted chain needs 280 and 4,653 digits of
  `A` (1,190 and 10,114 of `B`). v5's examples have 11,877,489,885 and
  234,905,651,862 digits of `A`. Below v5's certified bounds `Phi-bar`,
  244 and 4,514 digits suffice. v5's `a=4` bound is 3.628926097. v5
  Corollary 11.2(a) forces more than `9.29·10^34` digits for `p < 2.26`,
  against 48,859,824,830 for the 2.26 witness.
- **Scope (from the notes, unchecked here).** At qualities of 2.7 and
  above, schemes with `A = 1` and smaller `B` exist (round-10 direct
  controls). The chain's advantage is near 9/4.

Reproduction:

```sh
python -I experiments/shifted_chains_skeptic_certificates.py            # parts 1-5, about 4 min
python -I experiments/shifted_chains_skeptic_certificates.py --screen   # plus the fair v5 comparison, about +10 s
```
