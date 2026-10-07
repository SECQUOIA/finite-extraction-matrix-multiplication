# Opus review of manuscript v2, round 1: mathematical audit

Reviewer: Claude Opus 5.5, as an independent, adversarial review sub-agent.
Date: 2026-10-07.

Scope: the proofs in the revised (v2) manuscript, in these files:

- `preliminaries.tex`, `profile.tex`, `maps.tex`, `flows.tex`, `rounding.tex`;
- `extraction.tex`, `quantitative.tex`;
- `appendix-composition.tex`, `appendix-exact-certificate.tex`,
  `appendix-separator.tex`.

I read `introduction.tex`, `costs.tex`, and `discussion.tex` only to check
that their theorem statements match the proofs. Those sections are being
rewritten.

Constraints followed:

- I checked everything by hand. I ran no experiments or tests and no
  computation on the mathematics. Apart from editing this report, my
  commands only listed, hashed, copied, diffed, and searched files. I also
  read the theorem and equation numbers from the authors' 14:36 build
  (`build/main.aux`), and unpacked the archived v1 source to compare one
  lemma.
- I did no literature research. In particular, I did not check the new
  citations or any novelty statement.
- I edited no TeX or source file.
- To keep this review independent, I did not read the other v2 audit
  reports (`docs/manuscript-v2-*-audit.md`, `...-review-responses.md`).
  I read the two v1 Opus reports only to learn their scope.

## Verdict

**I found no fatal error and no major error.**

I found four minor findings and one note (M1-M5 below):

- M1 is a missing proof of a side remark. No theorem depends on it.
- M2-M4 concern notation and wording.
- M5 concerns a file that the v2 build does not include.

No finding is a false mathematical claim.

I checked every v2 bridge named in the brief, and each argument is correct
as written. The bridges are:

1. the integral determinant filtration and the fixed-type multiway
   restriction with a shared first leg;
2. partial-middle tripling;
3. the shared-leg separator;
4. threefold balancing with alternating row signs;
5. maximal-width occupation flows;
6. circulation rounding and the uniform relative-entropy bound;
7. the signed ledger;
8. the counted degeneration;
9. exactification before catalyst reuse;
10. pooled recursion;
11. the explicit parameter family and allowance;
12. the cyclotomic field, rational descent, and the rational seed.

Each overhead is retained in the counted exponent:

- the copy multiplicities `S` and `H`;
- the separator degree `D`;
- interpolation `E`;
- the rank `(2a-1)^3` of `S^+_{a,a}`;
- the catalyst supply `kappa_N^k`;
- the rounding loss `L`;
- the type penalty `T_N`.

I found no unproved cancellation of a tensor factor or of a direct-sum
multiplicity.

The construction implies `omega <= 9/4`. Not finding an error is evidence,
not proof, and this review is not a formal verification. Before anyone
relies on the result, I recommend the exact checks under
[Recommended checks](#recommended-checks). They target the locations
identified in
[Where a fatal error would have to be](#where-a-fatal-error-would-have-to-be).

## Snapshot reviewed

I first read every file at 14:11. Authors were editing during the review,
so I re-read every changed file in full. The table gives the final state.
I confirmed that all files except `maps.tex` were byte-identical to this
state at 14:38. The `maps.tex` hash is its state after the 14:36 edit.

| File | SHA-256 prefix | Modified |
|---|---|---|
| `main.tex` | `e07e61d34c82a0b0` | 14:18 |
| `preliminaries.tex` | `02bd1d3674a721ea` | 14:04 |
| `profile.tex` | `f647ce69abde1ad0` | 14:03 |
| `maps.tex` | `80c80fcced5e727e` | 14:36 |
| `flows.tex` | `acc83604c2151555` | 14:19 |
| `rounding.tex` | `54bbab2c3ee2bcf3` | 14:28 |
| `extraction.tex` | `202e8479b3769fae` | 14:16 |
| `quantitative.tex` | `ec060da8acd7b00b` | 14:16 |
| `appendix-composition.tex` | `fcd30052c2dfe504` | 14:08 |
| `appendix-exact-certificate.tex` | `1c1849d0f3896c68` | 14:12 |
| `appendix-separator.tex` | `626525d56a8763fe` | 01:00 |

For the statement check only: `introduction.tex` `6a9fe1d11abc6c5a`
(14:42), `costs.tex` `5f68abff51f04ba1` (14:16), and `discussion.tex`
`62a196c32124004e` (14:21). The 14:42 edit of `introduction.tex` changed
only related-work sentences; Theorems 1.1 and 1.2 are unchanged.

Changes made after my first reading:

- **Citations and literature sentences** were added in `maps.tex:16-19`,
  `maps.tex:215-219`, `flows.tex:7-12`, `rounding.tex:10-17`, and
  `rounding.tex:156-162`.
- **Wording changes:**
  - the abstract;
  - `extraction.tex:348` ("pooled recursion") and `:367-369`;
  - `quantitative.tex:30` ("active relations").
- **The exact-certificate appendix** gained a disclaimer that its
  quantities are distinct from the main ones (`:10-12`), renamed its
  catalyst `Cat^ex`, and now says "sixfold binary source dimension"
  (`:203-204`).

No change touched a proof step that I had checked. I checked the one new
mathematical sentence, `rounding.tex:158-159`. It says that with a fixed
total, `q_min >= 1/(3d)` gives a weighted loss of at most `3d`. This is
right: with `w = V` exactly, `p_y/q_y < 1 + 3d/w`, so
`wD(p||q) <= w log(1 + 3d/w) <= 3d`. I did not check the cited source.

Line numbers below refer to this final state.

## Where a fatal error would have to be

The following reduction is not part of the manuscript. I used it to decide
where to look hardest. It also tests whether the finite accounting claims
more than its relations support.

Let `f` be any point of Strassen's asymptotic spectrum: a real function on
tensors that is monotone under restriction and degeneration, multiplicative
under tensor product, additive under direct sum, and equal to 1 on the
rank-one unit tensor. Then `f(M_n) = n^{omega_f}`. Set

```
P_f(r,b) = f(S^{sigma_r}_{r,b})^{1/omega_f},   sigma_r = (-1)^{a-r}.
```

**Multiway relation.** Apply `f` to one width-`h` relation in its three
orientations: Lemma 4.1 and Proposition 4.3, with the separator dimension
equal to the sector count `M`. This gives

```
(2M-1)^3 f(S_{r,b})^n (h+1)^{n omega_f}
    >= M^3 * M^{omega_f} * prod_j f(S_{r,b+h-2j})^{n_j}.
```

The factor `(2M-1)^3/M^3 < 8` disappears under `n`-th roots, and
`M = exp(nH(q) - O(log n))`. So the relation gives exactly

```
(h+1) P_f(r,b) >= e^{H(q)} prod_j P_f(r,b+h-2j)^{q_j},
```

and, maximizing over `q`, exactly the multiway concavity
`(h+1)P >= sum_j P_j`. It gives no more. The `M^3` output copies only pay
for the `(2M-1)^3` source copies.

**The other axioms.**

- Tripling gives `P_f(r,4r-1) >= 3 P_f(r,r)`.
- Normalization: `S^sigma_{1,b} ~ M_b` gives `P_f(1,b) = b`.
- Symmetry between adjacent rows: `S^sigma_{r,b} ~ S^{-sigma}_{b,r}`
  gives `P_f(r,r+1) = P_f(r+1,r)`.

**Diagonal bound.** The diagonal part of the proof of Theorem 3.2 uses
only these facts: concavity with `h=1`, tripling at the row index, and
symmetry between adjacent rows. So `P_f(a,a) >= F(a,a)`. Since
`f(S^+_{a,a}) <= R(S^+_{a,a}) <= (2a-1)^3`, it follows that
`omega_f <= tau_a`.

The reduction has two consequences:

- **No overclaim.** The finite accounting tends to `tau_a`, which is what
  the relations support.
- **Location of any fatal error.** A fatal error would have to be in one
  of these places:
  - Lemma 4.1 (`lem:multiway`);
  - Lemma 4.2 (`lem:tripling`);
  - Proposition 4.3 (`prop:separator`);
  - the threefold identities (5) (`eq:cyclic-identities`) and (17)
    (`eq:cyclic-tripling-balance`);
  - the diagonal part of Theorem 3.2;
  - the finite composition and accounting.

I audited each of these completely. Items 1-4 below cover the local maps
and identities, item 16 covers the diagonal bound, and items 5-15 cover
the composition and accounting.

One consistency check uses the flattening ranks `zeta_X`, `zeta_Y`, and
`zeta_Z`. These are spectral points that are not symmetric under
permuting legs. They are consistent with a single oriented relation:

- **X leg:** the check reduces to `2M-1 >= M`.
- **Y leg:** the check follows from `2M-1 >= M` and
  `M * prod_j (b+h-2j)^{n_j} <= (b(h+1))^n`, which holds because the
  left side is one term of the multinomial expansion.
- **Z leg:** the same argument as the Y leg applies.

## Audit of the requested bridges

### 1. Determinant filtration and exact multiway types (`maps.tex:14-109`)

Correct.

- **Filtration quotients.** Diagonal substitution
  `W_{p,q} -> V_{p+q}` is onto. Its kernel contains `Delta W_{p-1,q-1}`,
  and the dimensions agree: `(p+1)(q+1) - (p+q+1) = pq`. Since
  `Q[u,v,s,t]` is a domain, multiplication by `Delta^j` is injective. So
  `F^j/F^{j+1} ~ V_{d+h-2j}`.
- **Lifts.** `L_{p,q}(i)` maps to `u^{p+q-i} v^i`. Replacing `ut` by
  `vs + Delta` is integral, and it ends at the lift with the same total
  `(v,t)` exponent. The count `sum_j (d+h-2j+1) = (d+1)(h+1)` holds.
- **Blocks.** Multiplication by `f in V_{r-1}` preserves `F^j`. Modulo
  `F^{j+1}`, multiplication by `u^{r-1-alpha} v^alpha` sends lift `i` to
  lift `i+alpha` with coefficient 1, because both sides have the same
  image under diagonal substitution. So the matrix in the adapted bases
  (with the dual basis on the third leg) is block upper-triangular. Its
  diagonal blocks are `C(r,b+h-2j)`.
- **Type restriction.** On a supported term, `j'_nu >= j_nu` in every
  position. If both words have the same type, the totals are equal, so
  `j'_nu = j_nu` in every position. Off-diagonal terms vanish exactly, and
  the sectors are coordinate blocks on legs 2 and 3. The first leg
  `(C^r)^{(x) n}` is untouched.
- **Worked case `r=b=2`, `h=1`.** Use the basis `us, vs, vt, Delta`. Then
  `u*vt = v^2 s + Delta v`. The single off-diagonal term is
  `x_0 y_{(0,2)} z_{(1,1)}`, and the type restriction removes it.
- **Worked case `r=2`, `b=3`, `h=2`.** Here `W_{2,2}` (dimension 9) has
  quotients `V_4, V_2, V_0`, and `W_{3,2}` (dimension 12) has quotients
  `V_5, V_3, V_1`. The blocks are `C(2,5)`, `C(2,3)`, `C(2,1)`. With
  `n=2` and type `(1,0,1)`, a term with input word `(0,2)` is forced to
  output word `(0,2)`.
- **Hypothesis in the flows.** `b = r-1+x >= h+1`, since `h <= x` and
  `r >= 2` (`flows.tex:40-42`).

### 2. Partial-middle tripling (`maps.tex:111-165`)

Correct for all `r >= 2`, `n >= 1`, and `0 <= m <= n`.

- **Forced labels.**
  - A left `Y` index forces a left `Z` index, and a right `Y` index forces
    a right `Z` index.
  - A middle `Z` index `z in [2r-1, 3r-2]` comes only from
    `y = z-i in [r, 3r-2]`.
- **Matching.** In the retained words, the number of middle `Y` labels
  `#MM + #ML + #MR` equals `m`, and so does the number of middle `Z`
  labels `#MM`. So `#ML = #MR = 0`, and the labels match position by
  position. This gives `binom(n,m) 2^{n-m}` sectors.
- **Blocks.**
  - Each outer block is a translate of `C(r,r)`.
  - The middle block `x_{r-1-i} y_{r+i+j} z_{2r-1+j}` becomes
    `X'_i Y'_{i+j} Z'_j` after relabeling. This is `C(r,r)^{(23)}`, with
    `Y` of dimension `2r-1` and `Z` of dimension `r`.
  - Both outer labels give the same block dimensions, `(r, r, 2r-1)`. So
    the canonical sector tensor does not depend on the outer labels.
- **Mode.** The ratio `M(m+1)/M(m) = (n-m)/(2(m+1))` is at least 1 exactly
  when `m <= (n-2)/3`. So the maximum is at `floor((n+1)/3)`. The `n+1`
  counts sum to `3^n`.

### 3. Shared-leg separator (`maps.tex:167-211`)

Correct.

- **Copy sum.** The phases sum to
  `L * [u - v + c(g-h) = 0 mod L]`. Since
  `|u - v + c(g-h)| <= (K_0 - 1) + c(M-1) = L - 1`, the congruence is an
  equality.
- **Degree.** The weight is `cg^2 + 2h(u-v) - ch^2 = c(g-h)^2 >= 0`.
- **Constant term.** The `t^0` part has `g = h` and `u = v`. It is a
  direct sum on all three legs. Each `y` substitution depends on its
  sector, which is legitimate because the `Y_h` are disjoint coordinate
  blocks.
- **Worked case `M = K_0 = 2`, `c = 1`, `L = 3`.** The only positive-degree
  terms are `t X_{a,1} Y_{0,b,0} Z_{0,d,1}` and
  `t X_{a,0} Y_{1,b,1} Z_{1,d,0}`.

### 4. Threefold balancing and alternating signs

Locations: `preliminaries.tex:84-106` and `maps.tex:213-260`. Correct.

**Convention.** Write `T^pi` for `T` with native leg `k` placed at global
leg `pi(k)`. Then `(T^tau)^pi = T^{pi tau}`, and right multiplication by
an odd permutation exchanges `A_+` and `A_-`.

**Identities.**

- `C(b,r) = C(r,b)^{(12)}`, which gives `S^sigma_{r,b} ~ S^{-sigma}_{b,r}`.
- `C(r,r)^{(12)} = C(r,r)` after renaming, which gives `S^+_{r,r} = S^-_{r,r}`.
- In either coset, the images `pi(1)` cover all three global legs, which
  gives `S^sigma_{1,b} ~ M_b` and `B_X B_Y B_Z ~ M_d`. I checked this
  last isomorphism directly: `B_X B_Y B_Z` equals `sum x_{jk} y_{ik} z_{ij}`,
  which is `M_d` after transposing the `y` index.

**Tripling.** The canonical sector is `C^{(x)(n-m)} (C^tau)^{(x)m}`. Its
product over `A_sigma` is
`(S^sigma_{r,r})^{(x)(n-m)} (S^{-sigma}_{r,r})^{(x)m}`, which is
`(S^sigma_{r,r})^{(x)n}`. Only factors within one global leg are
reordered.

**Signs.** Rows interact only through adjacent boundaries:

- `[sigma_r; r, b] = [sigma_{r'}; r', b']` with `r < r'` forces
  `b = r'`, `b' = r`, `r' - r` odd, and `r' in [r+1, 4r-1]`, with
  `r >= r'-1`. So `r' = r+1`.
- The identified classes are exactly:
  - `{[+;r,b], [-;b,r]}`;
  - the diagonal classes;
  - the boundary class of each `M_b`.

  The potential `log F` is well defined on these classes, and no
  unintended identification occurs.
- I agree that a single sign for all rows would not give the boundary
  identification by the actual coordinate isomorphism.

### 5. Independent sector choices, normalizers on positive-degree terms, and degree count

Locations: `extraction.tex:41-83` and `appendix-composition.tex`. Correct.

**The map `R_i`.**

- `R_i` applies the word-`g` permutation to X-block `g`, and the word-`s`
  permutations to the Y and Z sectors `s`. It does this even on
  positive-degree monomials with `g != s`.
- The word-`g` permutation includes, for tripling, the reversal of the
  first index at middle positions and the interval shifts.
- So `R_i` is one linear map on the whole target, independent of `t`, and
  Lemma 2.1 applies.

**The three-orientation product.**

- Each block of a global leg is indexed by a triple of independently
  chosen labels.
- After `R_i`, every such block is the same canonical product space,
  because the word-specific maps are bijections onto canonical
  coordinates.
- The regroupings act blockwise as fixed coordinate isomorphisms of that
  space. These are `eq:cyclic-tripling-balance`, the `S^sigma`
  identifications, and `B_X B_Y B_Z ~ M`. So they are defined on cross
  terms whose three labels differ, and they add no degree.

**Degree.** Each (relation, orientation) separator has exponents
`(g-s)^2` with `|g-s| <= M_i - 1`. The `3|J|` separators share one
parameter and are only tensored, never composed in sequence. So
`D = 3 sum_i (M_i - 1)^2`.

**Multiplicities.** `prod_i L_i^3 = S` and `prod_i M_i^3 = H`. The
auxiliary factors are:

- the sources: `prod_i M_{d_i^{N w_i}} = M_u`;
- the separator outputs: `M_M`;
- the boundary: `[M_2]^{NK}`.

Together these give `M_v`, with `v = 2^{NK} M`.

### 6. Maximal-width flows: drift bound, Doob transform, and absorption

Location: `flows.tex:15-197`. Correct.

**Affine row.** `F(r, r-1+x) = s_r f_r(x)` holds for `0 <= x <= 3r`. The
case `x = 0` uses `s_{r-1} = s_r (3r-3)/(3r-2)`. The probabilities `q`
sum to 1 because the children average to `x`.

**Drift bound.** For `x <= n/2`, the children are `0, 2, ..., 2x`. The
trapezoid bound gives
`sum_{k<=x} sqrt(k) <= (2/3) x^{3/2} + sqrt(x)/2`. Hence
`E sqrt(X') <= sqrt(2) sqrt(x) ((2/3)x + 1/2)/(x+1) <= (2 sqrt(2)/3) sqrt(x)`.
Jensen's inequality handles the other term, and reflection handles
`x > n/2`. Here `gamma = 1 - 2 sqrt(2)/3 ~ 0.057191`.

**Stopping argument.** It is the standard supermartingale argument at
`tau ^ T`, followed by monotone convergence. It does not presuppose
`E tau < infinity`. I verified `log(1+h) <= sqrt(h)`: the derivative of
the difference is `(sqrt(h) - 1)^2 / (...) >= 0`.

**Doob transform.** `f > 0` and `f` is affine, hence harmonic for the
uniform walk. The likelihood ratio of a path is `f(x_t)/f(i)`, and
`f(n)/f(1) = 3`. This gives
`C_i <= 3 sqrt(i)/gamma`. It also gives
`P_q(tau < infinity) = E_0 f(X_tau)/f(i) = 1`.

**Exit probabilities.**

- `p_i = i f(n)/(n f(i))`.
- `p_1 = 1/r`.
- `p_2 = 2(3r-1)/(r(3r+1)) < 2/r`.

**Reset counts.** The expected number of resets is `p_i/(1-p_1)`. This
gives `mu_a = 1/(a-1)` and `mu_r = 2(3r-1)/((r-1)(3r+1))`, which match the
weights of the exact certificate. Both are at most `10/7`.

**Row totals.**

- From entry 1: at most `6/gamma = 54 + 36 sqrt(2) ~ 104.91 < 105`.
- From entry 2: at most `3(sqrt(2)+2)/gamma = 90 + 63 sqrt(2) ~ 179.10 < 180`.

**Linear system.** The matrix `P` on states `{1, ..., n}`, including the
reset state, has `sum_t P^t` finite. So `(I - P^T) v = e_i` is
nonsingular and rational. Telescoping `e_{X_t} - e_{X_{t+1}}` gives
`eq:row-flow`, with absorbed mass exactly 1.

**Zero occupations really occur.** For even `r`, every child of every
interior state is even, and the reset enters at state 1. So odd states
`x >= 3` are never visited and have `lambda = 0`. The construction
handles them (item 8).

### 7. Circulation rounding (`rounding.tex:19-88`)

Correct.

**Signs and the network.**

- With `b_v = in(floor) - out(floor)`, the fractional parts have net
  outflow `b_v`. So the source and sink edges are oriented correctly.
- Edges with integral targets get no capacity.
- Loops have zero incidence and stay at their floor.

**Augmenting paths.** Integral augmenting paths reach the value `B`; this
is max-flow/min-cut against the feasible fractional flow. Adding the
0/1 increments gives a balance of zero.

**Self-loops occur.** When `h_{r,x}` is even, `y = x` is a child.

**Return edge.** The return edge `0 -> i_r` has integral target `K`, so it
stays `K`. Removing it gives `eq:rounded-row-flow` exactly.

**Error bounds.** The edge errors are below 1. The action-total error is
below `d_{r,x}`, which is the sum of `d_{r,x}` edge errors.

### 8. Tiny and zero occupations

Location: `rounding.tex:85-88`, `:200-216`, and `extraction.tex:6-8`.
Correct.

- **Zero targets.** Edges with zero target stay zero, so unreachable
  actions get `w = 0`.
- **Positive occupation that rounds to zero.** An action with
  `lambda > 0` may still get `w = 0`. Vertex balance then forces zero
  inflow. (This cannot happen at `i_r`, whose outflow is at least `K`
  because of the return edge.) So no omitted action leaves an orphaned
  output in the ledger.
- **Relative-entropy bound.** The bound divides only by the integer
  `w >= 1`. It uses `n_y < V q_y + 1`, `V < w + d`, and
  `q_y >= (r-1)/((2r-1)d) >= 1/(3d)`.
- **Minimum child.** I re-derived that the smallest child probability is
  at least `c/(c + n/2)`. The ratio `c/(c+x)` decreases in `x`, and the
  ratio `(c+2x-n)/(c+x)` increases in `x`. Both are compared at the
  continuous midpoint.

### 9. Signed ledger, diagonal identifications, and catalyst count

Location: `rounding.tex:90-144`. Correct.

- **What each row leaves.**
  - The final row leaves `K([+;a,a] - [+;a,a-1])`.
  - A lower row leaves `K([s_r; r, r+1] - [s_r; r, r-1])`, where
    `s_r = sigma_r`.
  - The adjacent boundaries cancel.
- **Residual.** `[sigma_2; 2, 1] = [-sigma_2; 1, 2] = [M_2]`.
- **Sources and outputs.** All source symbols have column at least 2, so
  `i_{M_2} = 0` and `c_{M_2} = 0`. Both totals are `U+T`. The only
  positive excess is `K` at `[a,a]`, so `sum c = U + T - K`.
- **Diagonal identification.** `[+;r,r] = [-;r,r]` is needed only for
  the `m` middle factors of each reset.

### 10. Entropy identity and the count `J_a`

Location: `rounding.tex:164-260`. Correct.

- **Per-action identity.** For each action,
  `w log F(b(x)) - sum_y n_y log F(b(y)) = w(H(p) - log d) + w D(p||q)`.
  The tripling identity is `F(r,4r-1) = 3F(r,r)`. Applying `log F` to the
  ledger gives `K log F(a,a) - K log 2`.
- **`J_a` formula.** `sum_{x=1}^{n-1} min(x, n-x) = floor(n^2/4)`. The
  closed form is right at `a = 2, 3, 4, 5`, giving `14, 42, 89, 159`.
- **Count bounds.**
  - `d <= floor(3a/2) + 1 <= 2a`.
  - `W <= K C_a + J_a log(2a)`.
  - `U <= K C_a + J_a`.
  - `z_r < 2K + 1`.
  - `w log d <= 180K + 2a log(2a)`.

### 11. Exactification before catalyst reuse

Location: `extraction.tex:88-134` and `preliminaries.tex:127-145`.
Correct.

**Exactification.** `G(t)^{(x)k}` has degree at most `kD < E`, and every
evaluation point is a nonzero root of unity. Reading the proof as "the
lemma with this `k`" or as "the lemma with `k=1` applied to the `k`-th
power" gives the same `E = kD + 1`.

**Catalyst bookkeeping.** At the tensor level,
`Cat (x) (alpha M) = alpha (Cat (x) M)`. So every summand carries one
catalyst. Then:

- the induction (tensor with `alpha M_{u^k}`, regroup into `beta^{j'}`
  groups of `alpha`, apply one step) is valid;
- the supply `kappa_N^k` per final summand is exact;
- the output catalyst restricts to `x_0 y_0 z_0`, which has coefficient 1.

**Counts.**

- `r_* = kappa_N^k E^j S^{kj} (2a-1)^{3NKkj}`.
- `m_* = H^{kj}`.
- The pooled exponent formula `eq:pooled-exponent` follows by division.

### 12. Pooled recursion after ceiling padding

Location: `extraction.tex:136-204`. Correct.

- **`p >= 2`.** It follows from the first-leg flattening ranks,
  `rA^2 >= mB^2`.
- **Recurrences.**
  - `v_{l+1} = r ceil(v_l/m) <= q v_l + r`.
  - `v_l <= q^l (1 + r/(q-1))`.
  - `n_{l+1} = A ceil(n_l/B) <= rho n_l + A`, which gives
    `n_l <= c + rho^l (n - c)`.
- **Uniform sizes.** All products at one depth have the same side.
- **Ordering.** Computing all input maps top-down and all output maps
  bottom-up justifies pooling across parents.
- **Cost.** The work is at most a constant times
  `sum_l q^l (1 + rho^{2l} n^2)` over
  `log_{1/rho} n + O(1)` levels. This gives `O(n^p)` when `p > 2`. The
  leaves number `O(q^L) = O(n^p)`.
- **Bilinearity.** It is preserved.

### 13. Type bounds and the `Delta_N` sandwich

Location: `extraction.tex:206-267`. Correct.

- **Lemma 7.4.** The type is a multinomial mode because each factor
  `n_i^h/h!` is maximized at `h = n_i`. There are
  `binom(n+s-1, s-1) <= (n+1)^{s-1}` types.
- **Resets.** `3^n/(n+1) <= M_r <= 3^n`.
- **Sandwich.** Hence `NG - T_N <= Delta_N <= NG`.
- **Finite cost bounds.**
  - `(2M-1)/M` lies in `[1, 2)`.
  - `E = 1 + 3k sum (M_i - 1)^2 <= (3kI + 1) e^{2B_N}`.
  - Every rank base `r+b-1 <= 5a-2`.
- **Lower bound for `p`.** `p >= tau_a > 9/4` follows from
  `Delta_N <= NK log F(a,a)` and the strict diagonal bound.

### 14. Constants in Theorem 7.5 and Corollary 7.6

Location: `quantitative.tex`. Correct.

I re-derived every inequality:

- **Basic bounds.** `t >= 16 log 2 > 8`, `log K <= 5t`, `J_a <= 2a^3`,
  and `I <= (3a^2 + 3a - 6)/2 <= 2a^2`.
- **Type loss.** `(4J_a + T_1)/K <= (41/2 + 45t/4)/l^2`. The terms are
  - `8a^3 + 2a^3 (6 + 5t)` from `J_a`;
  - `(a-1)(2 + 5t)` from the resets, with `(a-1)/a^3 <= 1/4`.

  Then `< 41/(4t^2) + 45/(8t) <= 221/256`.
- **Profile lower bound.**
  `log s_a >= (1/3) H_{a-1} - (1/18) sum 1/h^2 >= (1/3) log a - 1/9`.
  So `Delta_1/K > (4/3)t - 1`.
- **Numerator terms per `K`.**
  - Copies: at most `6/(a l^2)`.
  - Interpolation: `(2a + 4a log(2a))/(a^3 l^2) <= 5/(a l^2)`, giving at
    most 361 in total.
  - Catalyst: `U + T - K <= K(182a - 258) + 2a^3 + a < 184aK`, so the
    catalyst term is at most `552 log(5a)/l < 552 * 0.7 * 1.25 = 483`.
- **Numerator total.** It is less than
  `K(3t + 3 log 2 + 1 + 361 + 483) < K(3t + 848)`. The allowance
  `log 2/j < K` is covered.
- **Final bound.**
  `(3t + 850)/((4/3)t - 1) = 9/4 + 852.25/((4/3)t - 1) < 9/4 + 900/t`.
- **Source dimension.**
  `log A = jW <= a l (180aK + 2a^3 log(2a)) <= 181 a^5 l^3`.
- **Corollary.** `l_{2^l} = l` and `log a = l log 2 > l/2`.

### 15. Effective theorem, cyclotomic field, rational descent, and seed

Location: `extraction.tex:271-369`. Correct.

**Cyclotomic order.** `L_*` covers every root of unity used:

- `E` for exactification;
- `2a-1` for `S^+_{a,a}`;
- `2M_i - 1` for the separators;
- `r+b-1` for the supplied catalyst.

Everything else is integral or rational: the determinant bases, the 0/1
type maps, the coordinate permutations, and the factors `1/L` and `1/E`.

**Descent.** Write each linear form over the number field as
`sum_s e_s alpha_s` with rational `alpha_s`. Applying the `e_1`-coordinate map coefficientwise
fixes the rational target and expands each summand into at most `d^2`
rational rank-one terms.

**Seed.**

- The unrolled pooled recursion is a bilinear decomposition of `M_n`. Its
  leaf count is at most its arithmetic cost, `O(n^{9/4 + eps/2})`.
- Descent multiplies the length by at most `phi(L_*)^2`, a fixed number.
- So the test `R_n^q < n^p` eventually succeeds.

### 16. Least profile, exact certificate, and separator refinements

**Least profile** (`profile.tex:26-88`). Correct.

- **Second difference.** I re-derived the formula
  `2F(a,b) - F(a,b-1) - F(a,b+1) = 2(a-b) s_b/(3b(3b-2))` for
  `2 <= b <= a`. The coefficient of `a` in the numerator is 4, and the
  constant term is `-4b`. The formula also holds at `b = a`.
- **Diagonal minimality.** `k_a (3a-3) >= k_{a-1} (3a-2)`.
- **Off-diagonal case.** It uses `x_j - m = (3^j - 1)(3m-1)/2` and the
  chord argument.
- **Upper bound.** `s_a^3 <= (3a-1)/2`, since
  `(x+2)x^3 - (x-1)(x+1)^3 = 2x + 1` with `x = 3a`.

**Exact certificate** (`appendix-exact-certificate.tex`). Correct.

- **Coefficients.** I recomputed every telescoping coefficient:
  - final row: `-1`, `r/(r-1) - 1/(r-1) = 1`, interior `0`, terminal
    `-1/(r-1) + mu = 0`;
  - lower rows: offset `2/(3r+1)`, coefficient 1 at `r+1`, `mu_r` at `r`
    (cancelled), terminal `0`.
- **Denominator scale.** I checked the gcd analysis and the lcm
  identity `lcm_i d/g_i = d/gcd_i g_i`.
- **Divisibility.** I checked `eq:scale-divisibility`.
- **Spot values.** `K_2 = 15`, `K_3 = 84`, and `K_4 = 3465`.
- **Entropy identity.** I checked `eq:entropy-identity`.

**Separator refinements** (`appendix-separator.tex`). Correct.

- **Interpolation.** `sum_j alpha_j G(2^j) = sum_s G_s P(2^s) = G_0`.
- **Copy-count bound.** I checked `eq:one-power-limit` in both cases.
- **Two-power projection.** `q = 3 mod 4` excludes `d_1^2 + d_2^2 = 0 mod q`
  unless both `d_i` vanish. The example gives `11 * 15^2 = 2475 < 4096`.

## Findings

All findings are minor. "Missing proof" means a true statement whose
proof is not in v2. "Wording" means a correct proof whose text can
mislead.

**M1. Minor, missing proof of a side remark: the fixed-batch bound `Phi`**
(`extraction.tex:194-204`).

- **Issue.** The text says that `Phi` "is the bound obtained by grouping
  children separately within each parent and using
  `ceil(r_*/m_*) <= 2 r_*/m_*`". That recursion is not stated or proved in
  v2. Lemma 7.3 (`:138-186`) now proves only the pooled recursion. The
  fixed-batch version was Lemma 4.3 of v1, which I compared in the
  archived source.
- **Status.** Not a false claim, and no result depends on it. Since
  `Phi >= p`, every upper bound given for `Phi` is also an upper bound for
  the pooled exponent `p`, which is what Theorem 7.7 uses. Such bounds
  appear in `quantitative.tex:105-106`, in `costs.tex:47-51`, and in its
  table.
- **Repair.** Do one of the following:
  - add the one-line recurrence: each batch of `m` products becomes `r`
    products, regrouped into `ceil(r_*/m_*)` batches, so the cost `T(n)`
    of one batch of `m_*` products of side `n` satisfies
    `T(n) <= ceil(r_*/m_*) T(A ceil(n/B)) + Cn^2`;
  - present `Phi` only as "an upper bound for `p`".

**M2. Minor, notation: symbol collisions in proof text.**

The collisions most likely to mislead a referee:

- **(a) `t` in Appendix A.** `t_i = N w_i`
  (`appendix-composition.tex:16-17`, `:21-24`, `:72`, `:76`) appears next
  to the degeneration parameter `t` (`:56-69`, `:91`, `:131`, `:142`).
- **(b) `Phi` in Section 7.** It is both the composed map
  `Phi_{i,pi}(t)` (`extraction.tex:63`) and the exponent bound `Phi`
  (`:197`). `Phi_i(t)` also appears in Lemma 2.1
  (`preliminaries.tex:30`).
- **(c) `p` and `q` in Corollary 7.9.** `p/q = 9/4 + eps`
  (`extraction.tex:358`) reuses `p` (the pooled exponent, `:142`, `:191`)
  and `q` (`= r/m` at `:142`; the transition probabilities elsewhere).
- **(d) `t`, `u`, `v`, `s` in Section 4 and later.**
  - In `maps.tex:21-24`, `s, t, u, v` are polynomial variables.
  - The separator in the same section (`:189-206`) uses `u, v` as
    auxiliary indices and `t` as the degeneration parameter.
  - `extraction.tex:34-35` uses `u, v` as matrix dimensions.
  - `quantitative.tex:27` sets `t = log a`.

Other collisions:

- `H`: the multiplicity `M^3`, the entropy `H(p)`, and `H_i`.
- `D`: the degree, `D(p||q)`, `D_a`, and `D_r`.
- `r`: the row index, and the copy count in Lemma 7.3.
- `j`: the filtration index, and the reuse count.
- `c`: the phase slope, `3(r-1)/2`, `A/(1-rho)`, and `c_{sigma,r,b}`.
- `B`: the source side, `B_N`, the max-flow value, and `B_{j,i}`.

Repair: rename at least (a)-(c).

**M3. Minor, wording: "divide it into `B`-by-`B` blocks"**
(`extraction.tex:155-157`).

- **Issue.** Read literally, this means blocks of side `B`. The intended
  and correct meaning is a `B x B` array of blocks, each of side
  `ceil(n_l/B)`. This is consistent with `n_{l+1} = A ceil(n_l/B)`.
- **Repair.** "view it as a `B x B` matrix of blocks of side
  `ceil(n_l/B)`".

**M4. Minor, wording: "The off-diagonal minimality uses tripling at all
`h`"** (`profile.tex:94`).

- **Issue.** The proof (`:66-77`) uses tripling only along the sequence
  `x_0 = m`, `x_{j+1} = 3x_j + m - 1`, that is, at
  `h = m, 4m-1, 13m-4, ...`. The sentence overstates what is used, though
  it is not false as a statement about which axioms are needed.
- **Repair.** "uses tripling beyond the row index, along the sequence
  `x_j`".

**M5. Note, outside the v2 build.** `appendix-obstruction.tex:14`
references the undefined label `eq:small-kappa`. That file is not
included by `main.tex`, so the build is unaffected. Fix the reference if
the file is reinstated.

There is one optional clarity improvement, not a finding.
`rounding.tex:85-88` could add the converse case from item 8: if an
action with `lambda > 0` rounds to `w = 0`, vertex balance forces zero
inflow, so omitting it leaves the ledger unchanged.

## Precise checks and limitations

**Checked by hand:**

- every displayed identity and inequality in the listed files, including
  every numerical constant in Section 7.4;
- the worked cases in items 1 and 3;
- the spectral reduction and the flattening-rank consistency checks;
- that `introduction.tex` Theorems 1.1 and 1.2 match Theorem 7.5,
  Corollary 7.6, Theorem 7.7, and Corollary 7.9.

**Not checked:**

- every citation, and every statement about prior work or novelty;
- the certified numbers in the `costs.tex` table and
  `results/multiway-finite-costs.json`;
- the archived tests;
- any build log.

**Limits of this review:**

- **Hand-checking only.** Every argument above was checked by hand, so
  this is not a formal verification, and a gap in a long but routine
  bookkeeping step could escape it.
- **Coverage of the composed map.** I verified the composed relation map
  in general form (Appendix A) and in the small cases above. I did not
  expand the full composed tensor of any instance.

## Recommended checks

These checks are computational, so I leave them to the agent that runs
experiments. Each one targets a location where a fatal error would have
to be.

1. **Per-relation end-to-end check.** For small parameters, build the
   complete composed polynomial
   `(x)_{pi in A_sigma} Phi_{i,pi}(t)(L_i U_i^pi)` exactly over
   `Q(zeta_{2M-1})`, including the regrouping isomorphisms. Check that:
   - its constant term is `M^3` copies of the canonical product;
   - all other exponents are positive;
   - its degree is at most `3(M-1)^2`.

   Suitable cases:
   - split relations with `h = 1, 2, 3`, `n = 2, 3`, and every type;
   - tripling with `n = 1, ..., 4` and both signs.
2. **Ledger check.** For `a = 2, ..., 8` and several values of `K`, check
   `eq:rounded-ledger` and `sum c = U + T - K` with the actual rounded
   integer counts.
3. **Formalization.** The scalar chain (items 6, 7, 10, and 14) is
   self-contained real analysis and combinatorics. Formalizing it would be
   comparatively cheap.
