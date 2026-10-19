# Verification note: the 9/4 limit with arbitrary auxiliary compression

Date: 18 October 2026. Topic key: `hankel`.

This note checks the general Hankel flattening theorem from round 14, and
its consequence: arbitrary per-stage auxiliary matrices that preserve the
target cannot push the paid exponent of the shifted-chain construction
below 9/4. It is written to be read without the round notes. Nothing under
`manuscript/`, `upstream/`, `formalization/`, and no existing file, was
changed. The only new files are this note and the checker
[`experiments/shifted_chains_check_hankel.py`](../experiments/shifted_chains_check_hankel.py).

## Verdict

The round-14 claims are **correct**. I re-derived every step and found no
mathematical error, no wrong constant and no off-by-one. The rank
inequality, the parity reduction, the integer monotonicity proof with its
bridge polynomial, the endpoint constants `15/8` and `2`, the telescoping
bound `(4/3) log s0 + (2/3) log(15/16)`, the strict paid bound `p > 9/4`,
and the replication extension all check out.

The proof gives more than the notes state. I recommend three changes for
the paper:

1. **State the theorem more generally.** It holds for *every* pair of
   linear maps on the second and third legs that fixes the first leg, not
   only for the fixed physical maps. It holds for every sum of sectors
   sharing the first leg, including incomplete types and sectors with
   different numbers of middle factors. This makes the separate notion of
   a "preserving auxiliary matrix" a special case.
2. **Use a shifted potential.** With `Phi = P - 1/6` the derivative is
   positive everywhere, with a one-line certificate, so the integer bridge
   polynomial is not needed. Both endpoint constants become `11/6`, and
   the chain bound is exactly `< (4/3) log s0`.
3. **State the hypotheses of the paid conclusion explicitly**: identity on
   the shared first leg; independent auxiliaries per orientation and per
   stage, with the same rank in all six orientations; the source charged
   at `s0^6` per factor; and a terminal of the form `Q_{1,b_f}`. Section 9
   lists these as minor issues.

The ordinary-only cubic barrier of round 12 is the case `u = 1` of the
same theorem. It deserves a short remark, because it shows why middle
sectors are needed and why the intermediate Hankel lifts are the new
ingredient.

## 1. What was checked, and how

Sources read: `docs/round14-hankel-flattening.md`,
`docs/round14-review-hankel-flattening.md`,
`docs/round14-alternative-constructions.md`,
`experiments/round14_hankel_flattening.py`, the ordinary-only barrier in
`docs/round12-alternative-constructions.md` and
`docs/round12-review-bulk-auxiliary.md`, `docs/round12-bulk-auxiliary.md`,
`docs/round13-terminal-gain.md`, `docs/round13-no-outer-auxiliary.md` (for
the definition of a preserving auxiliary), the shifted-chain maps in
`docs/round8-multiscale-construction.md`, the ramp in
`docs/round11-arity-ramp.md`, and v5 `manuscript/preliminaries.tex` and
`manuscript/maps.tex`.

Status labels used below:

- **proved here**: I re-derived the proof completely.
- **checked**: exact computer verification on finite ranges, with no
  floating point in any assertion.
- **from notes, unchecked**: taken from the round notes without
  independent verification.

The checker is self-contained. It uses only the standard library and
imports no project code. It runs in about 5 seconds:

```sh
python -I experiments/shifted_chains_check_hankel.py          # full run
python -I experiments/shifted_chains_check_hankel.py --quick  # under 1 s
```

I also replayed the authors' and reviewer's receipts in read-only mode.
Both pass, and they modified no files:
`python -m experiments.round14_hankel_flattening --check` and
`python -m experiments.round14_review_hankel_flattening --check`.

## 2. Setting and definitions (item a)

Conventions follow v5 Section 2. A tensor is a trilinear form with legs
`x, y, z`. A restriction `S ⊵ T` substitutes, for each variable of `S`, a
linear form in the variables of the same leg of `T`. In the bilinear
reading, maps act on the two inputs and on the output. `B_X(q) = x Σ_{k<q}
y_k z_k` is the dot-product tensor with a one-dimensional first leg. As a
matrix between legs 2 and 3, it is the `q × q` identity. The convolution
tensor is

\[
C(r,b)=\sum_{\alpha<r,\ \beta<b} x_\alpha y_\beta z_{\alpha+\beta}.
\]

**Ordinary and middle children.** For `r, c >= 1`, the ordinary child is
`C(r,c)`. The *middle child* is

\[
C^{\rm mid}(r,c)=\sum_{x<r}\sum_{z<c} x_x\,y_{r-1-x+z}\,z_z ,
\]

with legs of sizes `r`, `r+c-1`, `c`. This is `C(r,c)^{(23)}` after the
first index is reversed. Crucially, it is written in the *unreversed*
shared first-leg coordinates. This is exactly the middle block of the v5
tripling (Lemma `lem:tripling`, with `c = r`) and of the shifted-chain
reset. I checked the identification by hand from the interval labels. The
checker also confirms it against the actual maps (Part C).

**Sector tensors.** Fix a field `K` and `X = (K^r)^{⊗N}`, with first-leg
coordinates indexed by words `x ∈ [r]^N`. A tensor `T ∈ X ⊗ Y ⊗ Z` is an
*`(r,c;N)` sector tensor with `M` sectors* if the following hold:

- `Y = ⊕_{g=1}^M Y_g`, `Z = ⊕_g Z_g`, `T = Σ_g T_g` and
  `T_g ∈ X ⊗ Y_g ⊗ Z_g`. These are the "sectors sharing the first leg" of
  v5 Section 4. In particular, every coefficient between `Y_g` and
  `Z_{g'}` with `g ≠ g'` is zero; these are the *cross-sector zeros*.
- For each `g`, invertible maps on `Y_g` and `Z_g`, *with the identity on
  `X`*, carry `T_g` to a product `⊗_{θ=1}^N L_{g,θ}`. Here
  `L_{g,θ} ∈ {C(r,c), C^mid(r,c)}`, and position `θ` of the first-leg word
  is the first leg of `L_{g,θ}`.

Write `J_g` for the number of middle factors of sector `g`.

**Restriction fixing the first leg.** We write `S ⊵_X T` when `S` and `T`
have the same first leg `X`, and `T` arises from `S` by linear
substitutions on legs 2 and 3 and the identity on leg 1.

**The physical stage maps.** One position of a shifted-chain stage has
arity `d >= 2` and integers `1 <= c < b` with `(d+2)c <= db - r + 1`. Set
`h = b - c` and `m = r + b - 1`. The source is `C(r,b) B_X(d)`. Its old
input coordinates are `(j, β)` with `j < d`, `β < b`, and its old output
coordinates are `(j, γ)` with `γ < m`.

- *Input substitution.* For a quotient exponent `e < 3c+r-1` (the crop),
  take the first component `j` with `0 <= e - jh < b`, and lift `e` to
  `(j, e-jh)`. The kernel vector `(k, i)`, with `k < d-1` and `i < c`, is
  `-(k, i+h) + (k+1, i)`.
- *Output coordinates.* Use the inverse of the unimodular basis that
  consists of the quotient lifts (first component containing the exponent)
  and the output kernel vectors `-(k, i+h) + (k+1, i)`, `i < c+r-1`. Keep
  the quotient exponents `e' < 3c+2r-2`.
- *Reset labels.* The quotient input exponents are split into left
  `[0,c)`, middle `[c, 2c+r-1)` and right `[2c+r-1, 3c+r-1)`. The output
  exponents are split into left `[0, c+r-1)`, middle `[c+r-1, 2c+r-1)` and
  right `[2c+r-1, 3c+2r-2)`.

The classes are K (`d-1` labels), O (labels left and right) and M, with
weights 2, 1 and 0. The diagonal blocks are `C(r,c)` for K and O and
`C^mid(r,c)` for M.

Every off-diagonal coefficient strictly increases the weight. A left
input reaches only left outputs, with no kernel part. A kernel input
reaches only the same kernel label. A right input reaches only right
outputs and kernel outputs. A middle input reaches all classes.

Retaining a fixed type `ν = (n_K, n_O, n_M)` on both legs 2 and 3 of the
`N`-th power kills all off-diagonal terms. This is the v5 type-restriction
argument: per-position weights cannot decrease, and the totals are equal.
The result is an `(r,c;N)` sector tensor with

\[
M=\frac{N!}{n_K!\,n_O!\,n_M!}(d-1)^{n_K}2^{n_O}
\]

sectors and `J_g = n_M` for every sector. The first leg is untouched
throughout.

*Status: proved here (local block analysis) and checked.* Part C of the
checker builds these maps for 10 parameter sets at width one and 7 at
width two, including `(d,r,b,c) = (2,7,12,4)` and `(5,3,7,2)`. It confirms
that the maps are unimodular, that all cross terms increase the weight
(cross terms M→O, M→K and O→K are present, so the type restriction is
really needed), and that every retained tensor equals the canonical sum of
sectors exactly, including all cross-sector zeros. The general
correctness of the round-8 maps belongs to another topic. I used only the
local facts above.

**Preserving auxiliary matrix** (rounds 12–14). Fix the stage maps above
for `C(r,b)^{⊗N} B_X(d^N)` and a type `ν`. A matrix `E ∈ K^{d^N × d^N}` is
*preserving* if the same maps, applied to `C(r,b)^{⊗N} ⊗ E` with `E` in
place of the identity matrix of `B_X(d^N)`, produce exactly the same
retained tensor `T_ν`. Its *rank* `q` is `rank_K E`.

If `E = Σ_{k<q} ℓ_k ρ_k^T`, then `C(r,b)^{⊗N} ⊗ E` is a restriction of
`C(r,b)^{⊗N} B_X(q)` fixing the first leg: substitute
`y_k ↦ Σ_α ℓ_k[α] y_α` and `z_k ↦ Σ_β ρ_k[β] z_β`. Hence every preserving
`E` of rank `q` gives `C(r,b)^{⊗N} B_X(q) ⊵_X T_ν`. The theorem below needs
only this weaker hypothesis. It does not need the fixed maps, a square
`E`, or any structure of `E`.

## 3. The Hankel flattening theorem (item b)

Fix positive integers `u, v` with `u + v = r + 1`. For `x < r` let
`F_x ∈ K^{u×v}` have entries `F_x[a,β] = [a + β = x]`, a Hankel 0/1 matrix.
For words, let `F_x = F_{x_1} ⊗ ... ⊗ F_{x_N}`. For `T ∈ X ⊗ Y ⊗ Z`, define
the matrix

\[
\Psi(T)_{(z,a),(y,\beta)}=\sum_{x}T[x,y,z]\,F_x[a,\beta],
\qquad a\in[u]^N,\ \beta\in[v]^N .
\]

A one-dimensional first leg is lifted to the `1 × 1` matrix `[1]`.

Three facts are immediate:

- (i) If `T' = (id_X, β, γ)T`, then `Ψ(T') = (Γ ⊗ I) Ψ(T) (B ⊗ I)`, where
  `B` and `Γ` are the coefficient matrices of the substitutions. Hence the
  rank cannot increase.
- (ii) `Ψ(T ⊗ T') = Ψ(T) ⊗ Ψ(T')`, up to permuting rows and columns.
- (iii) `Ψ(B_X(q)) = I_q`.

The rank of a Kronecker product is the product of the ranks, over every
field.

**Lemma 1 (local ranks).** Over every field,
`rank Ψ(C(r,b)) = b + v - 1` and `rank Ψ(C^mid(r,c)) = c + u - 1`.

*Proof.* For the ordinary child,
`Ψ(C(r,b))[(z,a),(y,β)] = [z = a+y+β] = Σ_{t=0}^{b+v-2} [z = a+t][t = y+β]`,
so the rank is at most `b+v-1`. Rows `(t, 0)` and columns
`(min(t,b-1), t - min(t,b-1))`, for `0 <= t <= b+v-2`, form an identity
submatrix. The rows exist because `v <= r`.

For the middle child, put `A = u-1-a` and `B = v-1-β`. Since
`r - 1 = (u-1) + (v-1)`, the entry `[y = r-1-a-β+z]` equals
`[y = z+A+B] = Σ_{t=0}^{c+u-2} [t = z+A][y = t+B]`. Rows
`(z, A) = (min(t,c-1), t - min(t,c-1))` and columns `(y, B) = (t, 0)` give
an identity submatrix. The columns exist because `u <= r`.

All factors and minors are 0/1 matrices, so both ranks hold over every
field. ∎

*Status: proved here; checked.* Part A of the checker certifies the
factorizations and minors for all `r, b <= 8` and all `u`. It also
computes the ranks directly over Q, GF(2), GF(3) and GF(5): 288 cases.

**Theorem 2 (Hankel flattening bound).** Let `T` be an `(r,c;N)` sector
tensor with `M` sectors and middle counts `J_g`. If
`C(r,b)^{⊗N} B_X(q) ⊵_X T`, then for all positive integers `u, v` with
`u + v = r + 1`,

\[
q\,(b+v-1)^N\ \ge\ \sum_{g=1}^{M}(c+v-1)^{N-J_g}(c+u-1)^{J_g}.
\tag{H}
\]

*Proof.* By (ii), (iii) and Lemma 1, the source has
`rank Ψ = q (b+v-1)^N`. Because `T_g ∈ X ⊗ Y_g ⊗ Z_g`, `Ψ(T)` is block
diagonal, with blocks `Ψ(T_g)` on rows `Z_g × [u]^N` and columns
`Y_g × [v]^N`. Block ranks add. Invertible maps on `Y_g` and `Z_g` do not
change `rank Ψ(T_g)`, so by (ii) and Lemma 1 this rank is
`(c+v-1)^{N-J_g} (c+u-1)^{J_g}`. Now apply (i). ∎

*Status: proved here; checked.* Part B checks (H) with equality on the
target side for sector sums with *mixed* middle counts (all words in
`{O,M}^N`, with `N = 2, 3`), over Q, GF(2) and GF(3). A negative control
shows that identifying two sectors (writing them on the same `Y`, `Z`
coordinates) halves the rank. The cross-sector zero hypothesis is
therefore necessary. Part C checks (H) on the actual stage targets: 216
target ranks over three fields. It also checks direct source ranks
`q (b+v-1)^N`, including rectangular `E`, the zero matrix, and two
matrices whose rank drops in characteristic 2. It verifies that the
round-12 binary upper-tail projections, of rank `q < d^N`, really preserve
the full target and satisfy (H).

**Remarks on Theorem 2.**

- *What is new relative to the notes.* Round 14 states (H) for complete
  types, with all `J_g` equal, and for the fixed physical maps. The proof
  needs neither condition. Allowing mixed `J_g` matters only for even `r`
  (Corollary 3).
- *Degenerations.* (H) also holds when `T` is the constant term of a
  degeneration whose legs 2 and 3 carry Laurent-polynomial maps and whose
  first-leg map is the identity. All `(R+1)`-minors of `Ψ(T(t))` vanish
  as polynomials in `t`, hence also at `t = 0`. This works over every
  field. So removing off-diagonal blocks by `t`-scaling on legs 2 and 3,
  as in OAI26, would not escape the bound.
- *The first-leg identity is essential for `2 <= u <= r-1`.* For `u = 1`,
  `Ψ` is the ordinary flattening along leg 3 (rows `z`, columns `(y,x)`).
  For `u = r` it is the flattening along leg 2. Both are monotone under
  *all* restrictions. The intermediate lifts use the Hankel structure of
  the shared leg, so they survive only maps that fix it. A first-leg
  restriction to a prefix `x < r'` is harmless: it turns `C(r,b)` into
  `C(r',b)` with unused output coordinates, and the potential below is
  increasing in `r`. General first-leg maps are not covered.

## 4. Parity-free gain bound (item c, first half)

Let `A_r(t) = (r + 2t - 1)^2 - 1 = (r+2t)(r+2t-2)` and
`h = log(M/q)/N`.

**Corollary 3.** Under Theorem 2 with `b >= c`,
`h <= (1/2) log(A_r(b)/A_r(c))`. For odd `r`, also
`h <= log((r+2b-1)/(r+2c-1))`, which is the stronger bound.

*Proof.* For odd `r`, take `u = v = (r+1)/2`. Then
`c+u-1 = c+v-1 = (r+2c-1)/2`, so `J_g` drops out of (H). The odd bound
follows. With `X = r+2b-1 >= Y = r+2c-1 >= 2`, we have
`X^2/Y^2 <= (X^2-1)/(Y^2-1)`, so the odd bound implies the parity-free
one.

For even `r`, write (H) for `(u,v) = (r/2, r/2+1)` and
`(u,v) = (r/2+1, r/2)`. Put `α = c + r/2` and `α' = c + r/2 - 1`. The
right sides are `Σ_g α^{N-J_g} α'^{J_g}` and `Σ_g α'^{N-J_g} α^{J_g}`. By
Cauchy–Schwarz, their product is at least `M^2 (αα')^N`. The left sides
multiply to `q^2 ((b+r/2)(b+r/2-1))^N`. Finally
`4 (t+r/2)(t+r/2-1) = A_r(t)`. ∎

*Status: proved here; checked* (Part B checks the Cauchy–Schwarz step).
For complete types, as in the notes, the two exponents simply swap and
cancel. The `-1` terms matter. On the efficient ray `r = λb`, `c = λ^2 b`,
with `(d+2)λ^2 + λ - d = 0`, the homogeneous ratio `(r+2b)/(r+2c)` equals
`(d+2)/d` exactly, which is the construction's ideal gain. The finite
ratio is slightly larger.

## 5. Potentials (item c, second half)

All three potentials below are symmetric and work in the centred variables
`x = r - 1/3`, `w = b - 1/3`, `t = x + 2w = r + 2b - 1` and `δ = x - w`.
Then `A_r(b) = t^2 - 1`, and

\[
P(r,b)=r^2+4rb+b^2-2r-2b = x^2+4xw+w^2-\tfrac23 .
\]

For `Φ_κ = x^2 + 4xw + w^2 - κ` and fixed `x`, I derived

\[
\frac{d}{dw}\Bigl[\tfrac23\log\Phi_\kappa-\tfrac12\log(t^2-1)\Bigr]
=\frac{\tfrac23\bigl(t\delta^2-2\delta+(3\kappa-2)t\bigr)}{\Phi_\kappa\,(t^2-1)} .
\tag{D}
\]

The checker verifies (D) as a polynomial identity in `x`, `w` and `κ`.
On the domain `r, b >= 1`, that is `x, w >= 2/3`, we have `t >= 2`,
`t^2 - 1 >= 3`, and `Φ_κ >= 8/3 - κ > 0` for `κ < 8/3`.

**Lemma 4 (the notes' potential, κ = 2/3).** For integers `r >= 1` and
`b > c >= 1`,
`(1/2) log(A_r(b)/A_r(c)) < (2/3) log(P(r,b)/P(r,c))`.

*Verification of the notes' proof.* With `κ = 2/3`, the numerator of (D)
is `(2/3) δ (tδ - 2)`, which is the notes' (7).

- For `w >= x` (`δ <= 0`), both factors are `<= 0`, so the derivative is
  `>= 0`, with a zero only at `δ = 0`.
- For `w <= x - 1`, we have `δ >= 1` and `t >= 3`, so `tδ > 2`.

Integer `b` gives `δ ∈ Z`, so the only integer step that crosses the bad
interval `(x-1, x)` is `b = r-1 → r`. I recomputed the bridge:

\[
P(r,r)^4A_r(r-1)^3-P(r,r-1)^4A_r(r)^3=r^3(3r-2)^3V(r),
\]

with `V = 2592r^5 - 14040r^4 + 28944r^3 - 28128r^2 + 12776r - 2187`. The
coefficients of `V(t+2)` are `709, 5672, 15936, 20304, 11880, 2592`, all
positive. So `V(r) > 0` for `r >= 2`. For `r = 1`, every allowed `w`
satisfies `w >= x`.

The bridge really is needed. The `κ = 2/3` derivative is negative at
interior points of `(x-1, x)`; the checker exhibits one. The endpoint
bounds also hold:

- `P(r0,b0) <= (15/8) s0^2` for `s0 = r0 + b0 - 1 >= 2`.
- `P(rf,bf) >= P(1,bf) = bf^2 + 2bf - 1 >= 2 bf^{3/2}`. Exactly,
  `P(1,b)^2 - 4b^3 = 4τ + 8τ^2 + 4τ^3 + τ^4` with `τ = b - 1`.

*Status: proved here; checked* by symbolic identities and 1.44 million
exact integer monotonicity steps for `r, b <= 1200`.

**Lemma 5 (recommended potential, κ = 5/6).** Let

\[
\Phi(r,b)=P(r,b)-\tfrac16 = r^2+4rb+b^2-2r-2b-\tfrac16 .
\]

Then, for *real* `r >= 1` and `b > c >= 1`,

\[
\tfrac12\log\frac{A_r(b)}{A_r(c)}<\tfrac23\log\frac{\Phi(r,b)}{\Phi(r,c)} .
\]

In addition:

- `Φ(r,b) = Φ(b,r)`.
- `Φ(r,b) <= (11/6)(r+b-1)^2` whenever `r + b >= 3`.
- `Φ(r,b) >= (11/6) b^{3/2}` for all `r, b >= 1`.

*Proof.* With `κ = 5/6`, the numerator of (D) is
`(1/3)(2tδ^2 - 4δ + t)`, and

\[
t\,(2t\delta^2-4\delta+t)=2(t\delta-1)^2+t^2-2>0\qquad(t\ge2).
\]

So the function is strictly increasing in `w`. For the source bound, write
`s = r + b - 1`. Then `Φ = s^2 - 7/6 + 2rb <= (3/2)s^2 + s - 2/3`, and
`(11/6)s^2 - ((3/2)s^2 + s - 2/3) = (s-1)(s-2)/3 >= 0`. For the terminal
bound, `Φ` increases in `r` (since `∂_r Φ = 2r + 4b - 2 > 0`). With
`τ = b - 1 >= 0`,
`(6Φ(1,b))^2 - 121 b^3 = 165τ + 345τ^2 + 167τ^3 + 36τ^4`. ∎

*Status: proved here; checked* (symbolic identities and the same grid).
This proof is shorter than Lemma 4, needs no integer case analysis, and
has equal endpoint constants. The review's potential `P - 1/12`
(`κ = 3/4`) also works. Its numerator is `2D` with the review's `D`, and
the review's identities
`12D - (4δ^3 + 8δ^2 - 7δ + 2) = (3w-2)(4δ^2+1)` and
`32(8δ^2 - 7δ + 2) = (16δ-7)^2 + 15` are verified. In general, (D) shows
that every `κ > 3/4` gives a positive derivative: the discriminant
`4 - 4t^2(3κ-2)` is negative for `t >= 2`. Using `rb <= (s+1)^2/4`, the
source constant `(49/6 - κ)/4` (attained at `s0 = 2`) is at most the
terminal constant `8/3 - κ` exactly when `κ <= 5/6`, with equality at
`κ = 5/6`. Every `κ` in `(3/4, 5/6]` therefore gives a bridge-free proof.
At `κ = 5/6` both constants are `11/6`, which makes the statement
cleanest.

## 6. Chains and the paid exponent (item d)

**Theorem 6 (chain gain bound).** Consider stages `i = 1, ..., L`, with
`L >= 1`. Stage `i` has positive integers `r_i, b_i, c_i, N_i, q_i` with
`c_i < b_i`, and an `(r_i,c_i;N_i)` sector tensor `T_i` with `M_i` sectors
such that `C(r_i,b_i)^{⊗N_i} B_X(q_i) ⊵_X T_i`. Stage `i+1` reads the pair
`(c_i, r_i)` in either order. The pair after the last stage is
`(r_f, b_f)`, in either order. Put `s0 = r_1 + b_1 - 1`. Then

\[
\log b_f+\sum_{i}\frac{\log(M_i/q_i)}{N_i}\ <\ \tfrac43\log s_0
\quad\Bigl(\text{and also}\ <\tfrac43\log s_0+\tfrac23\log\tfrac{15}{16}\Bigr).
\]

*Proof.* Corollary 3 and Lemma 5 give, per stage,
`h_i < (2/3) log(Φ(r_i,b_i)/Φ(c_i,r_i))`, using `Φ(r_i,c_i) = Φ(c_i,r_i)`.
By symmetry, the denominator is `Φ` of the next pair in either order, so
the sum telescopes:
`Σ h_i < (2/3) log(Φ(r_1,b_1)/Φ(r_f,b_f))`. Since `b_1 >= 2`, we have
`s0 >= 2`, and the endpoint bounds of Lemma 5 give the first form.
Lemma 4, with the notes' endpoints `15/8` and `2`, gives the second. ∎

This uses no arity, no legality inequality `(d+2)c <= db - r + 1`, no
common width, no Perron-ray approximation and no sign condition on the
local gains. Crops change only the actual integer `c_i`. Input and output
swaps do not matter because `Φ` and `P` are symmetric.

*Status: proved here; checked.* Part E checks 3,000 random legal chains,
with arities from 2 to 1000, extra crop slack, random swaps and terminals
up to `(3,6)`. Each chain is checked with exact integer per-step
inequalities for `P`, `6P - 1` and `12P - 1`, and with the exact
telescoped inequality `b_f^6 Π (A_{r_i}(b_i)/A_{r_i}(c_i))^3 < s0^8`,
including the `15/16` form. The round-11 ramp chains with `D = 2, ..., 16`
are checked step by step.

**The paid ledger.** I re-derived the ledger from v5. In each of the six
orientations, the auxiliary of a stage is `B_X(q)^π`. The three
orientations of one sign give `MM_q` (v5 `eq:coset-dot-products`), and the
two signs give `MM_{q^2}`. The separator dot products give `MM_{M^2}`.
`S^σ_{1,b} ≅ MM_b`, so `Q_{1,b} ≅ MM_{b^2}`, and `R(Q_{r,b}) <= s^6`.

With global power `P`, stage width `N_i`, stage power `k_i`, and
`N_i k_i | P`, the counts are:

\[
A=\prod_i q_i^{2P/N_i},\quad
B=b_f^{2P}\prod_i M_i^{2P/N_i},\quad
m_*=\prod_i M_i^{6P/N_i},\quad
r_*=s_0^{6P}\prod_i(2M_i-1)^{6P/N_i}E_i^{P/(N_ik_i)},
\]

with `E_i >= 1`. For the common-`N`, common-`k` case, take `N_i = N` and
`P = Nk`. This reproduces round-8 (11), round-11 (7) and round-14 (11).

**Corollary 7 (paid exponent).** Under this ledger, if `B > A`, then

\[
p=\frac{\log(r_*/m_*)}{\log(B/A)}\ \ge\
\frac{3\log s_0}{\log b_f+\sum_i N_i^{-1}\log(M_i/q_i)}\ >\ \frac94 ,
\]

and the same holds with `⌈r_*/m_*⌉` in place of `r_*/m_*`.

*Proof.* `log(B/A) = 2P (log b_f + Σ_i log(M_i/q_i)/N_i)`. Since
`2M - 1 >= M` and `E_i >= 1`, `log(r_*/m_*) >= 6P log s0`. Apply
Theorem 6. ∎

*Status: proved here, given the ledger.* The ledger formulas come from the
notes. I re-derived them against the v5 identities listed above, but did
not re-verify the separator degrees or exactification counts. Only their
nonnegativity is used.

## 7. Replication (item e)

The review's extension allows different `N_i` and `k_i`, with
`a_i = P/(N_i k_i)` independent copies of stage `i`. The proof needs
nothing new, because Theorem 2 holds at every width and Theorem 6 already
allows different `N_i`.

In fact the theorem gives more. Apply Theorem 2 at width `P` to the whole
replicated stage. Its retained tensor is again a sector tensor, with
`M_i^{P/N_i}` sectors. So even a *joint* auxiliary matrix across all
replicas of one stage satisfies the same bound.

What remains outside is anything that is not a restriction of
`C^{⊗N} B_X(q)` fixing the first leg at one stage and one orientation:
joint auxiliaries across levels, joint cyclic auxiliaries across
orientations (round 15), and different source decompositions.

*Status: proved here.* I replayed the review's replicated integer
controls only through its check mode.

## 8. Corollaries and remarks for the paper

**Ordinary-only barrier (round 12) — worth a short remark.** Take `u = 1`
in (H). If no middle sector is retained (`J_g = 0`), then
`h <= log((r+b-1)/(r+c-1))`. Since `r_i + c_i - 1` is the span of the
next pair, the bounds telescope exactly to `log(s0/s_f)`. Then
`log b_f + G <= log s0 - log(s_f/b_f) <= log s0`, so `p >= 3`.

With `u = 1`, `Ψ` is just the leg-3 flattening, so this remark needs no
first-leg hypothesis. It explains two things:

- Middle sectors are what make subcubic exponents possible.
- The classical flattenings (`u = 1` or `u = r`) cannot see 9/4. On the
  efficient ray, with the modal middle fraction `1/(d+2)`, they give
  exponent floors of about 2.05 and 1.95 (a floating-point computation,
  display only). The balanced Hankel lift reproduces the construction's
  ideal gain exactly in the homogeneous limit.

The intermediate lifts are therefore the essential new ingredient. The
exact telescoping identity `Π (s_i/t_i) = s0/s_f` is checked on all
random chains.

**Terminal special case (round 13).** With `r = b = 3`, `c = 1` and
`u = v = 2`, (H) is `M <= 2^N q`. This is the round-13 terminal theorem,
which gives `p >= 3 log 5 / log 6` for that one-step recipe. It need not
appear separately in the paper.

**Sharpness.** In the homogeneous limit the bound is tight on the
efficient ray. Two identities show this:

- `(r+2b)/(r+2c) = (d+2)/d`.
- For `Φ_0 = r^2 + 4rb + b^2`,
  `d/db[(2/3) log Φ_0 - log(r+2b)] = (2/3)(r-b)^2/(Φ_0 (r+2b))`, which
  vanishes on the diagonal.

That uncompressed constructions approach 9/4 with all costs paid is
*from notes, unchecked* here (round 8 and round 11). For the round-11 ramp
geometries, the any-auxiliary floor `3 log s0 / (log b_f + Σ bound)` is
about 2.2684, 2.2569, 2.2526 and 2.2517 for `D = 2, 4, 8, 16`. These are
floating-point display values. The certified uncompressed exponents in
the notes are 2.3371, 2.2882, 2.2677 and 2.2601. Compression could improve
those chains at most to these floors, and only if preserving auxiliaries
attaining the bound exist, which is unknown.

**Dependence on the source model.** The strict inequality `p > 9/4` uses
the charge `s0^6` per source factor. Suppose instead that the initial
tensor is evaluated in any way of the form
`R_src MM_A ⊵ Q_{r0,b0}^{⊗P} MM_A`. The leg-1 flattening rank of
`Q_{r,b}` is `(r b s)^2`, so `R_src >= (r0 b0 s0)^{2P}`, and Theorem 6
gives `p > (3/4)(1 + log(r0 b0)/log s0)`. For sources with
`max(r0,b0) <= K min(r0,b0)`, this is
`p > 9/4 - (3/2) log(1+K)/log s0`.

So the *limit* 9/4 for long chains with balanced sources does not depend
on the source model, but the strict inequality for each finite chain
does. For very unbalanced sources, the flattening gives much less. *Status:
proved here* (short flattening argument).

## 9. Problems found and fixes

No mathematical error was found. All issues are minor, concerning scope or
presentation:

1. **Narrower statement than the proof gives.** The notes state (H) for
   complete types with a single `J`, and for the fixed physical maps.
   *Fix:* state Theorem 2 for every sector tensor and every restriction
   fixing the first leg, with the Cauchy–Schwarz step for even `r`. The
   notion of a "preserving auxiliary" then becomes a one-line special case.
2. **Bridge polynomial.** The integer potential needs a separate
   polynomial certificate on one integer step. *Fix:* use
   `Φ = P - 1/6` (Lemma 5). It has a one-line positivity certificate,
   works for real arguments, and gives the chain bound exactly
   `< (4/3) log s0`. Keep `15/16` only as an optional refinement.
3. **Terminal form in the ledger.** `B = b_f^{2P} ...` assumes that the
   terminal tensor is `Q_{1,b_f} ≅ MM_{b_f^2}`. If `r_f > 1`, one must
   first restrict `C(r_f,b_f)` to `C(1,b_f)`. The gain bound already
   allows any `r_f >= 1`, so nothing breaks. *Fix:* say so in the
   statement.
4. **Equal auxiliary rank in all six orientations.** The ledger
   `A = Π q_i^{2P/N_i}` uses one rank per stage. Ranks that depend on the
   orientation lead to rectangular auxiliary tensors that v5's square
   relative schemes do not cover directly, although (H) holds in each
   orientation. *Fix:* state the hypothesis.
5. **Source charge as a hypothesis.** "Paid exponent > 9/4" is conditional
   on the `s0^6` source charge. *Fix:* state it as a hypothesis, and add
   the robustness remark of Section 8.
6. **Scope.** The theorem requires the identity on the shared first leg
   and independent per-stage, per-orientation auxiliaries. It also
   requires children no longer than the parent: Corollary 3 needs
   `c <= b`, so v5-style splits with longer children are not covered.
   *Fix:* one scope sentence.

## 10. Checker summary

[`experiments/shifted_chains_check_hankel.py`](../experiments/shifted_chains_check_hankel.py)
uses exact `int` and `Fraction` arithmetic throughout.

| Part | What it checks | Size (full run) |
| --- | --- | --- |
| A | Factorization and identity-minor certificates; direct ranks over Q, GF(2), GF(3), GF(5) | 288 `(r,b,u)` cases, `r, b <= 8` |
| B | Mixed-`J` sector sums, Cauchy–Schwarz step, non-additivity control | 23 cases over 3 fields |
| C | Actual stage maps: unimodularity, weight rule, exact sector targets, target ranks, inequality, tail auxiliaries, direct source ranks (char-2 drops) | 17 parameter sets, 216 target ranks, 12 tail preservations, 16 source ranks |
| D | Identity (D) in `x, w, κ`; `κ = 2/3, 5/6, 3/4` certificates; bridge `V`; endpoint polynomials; integer monotonicity of `P`, `6P-1`, `12P-1`; endpoint inequalities | 4.3 million exact comparisons, 1.44 million endpoint pairs |
| E/F | Random legal chains; ramp chains; ordinary-only telescoping | 3,000 chains and 4 ramps |

## 11. What I could not verify

- The general correctness of the round-8 shifted-chain maps beyond the
  local facts used here, and beyond the 17 parameter sets checked.
- The separator degree and exactification counts in the paid ledger. Only
  their nonnegativity is used.
- Whether 9/4 is approached with all costs paid (rounds 8 and 11).
- Whether preserving auxiliaries attaining (H) exist at large widths. This
  affects finite sizes, not the limit.
- The review's KKKM rank-30 replicated control, which I replayed only
  through its check mode.

## 12. Recommendation for the paper

Write one section, "A limit for per-stage auxiliary compression", of about
2.5 to 3 pages:

1. A definition of sector tensors with ordinary and middle children, and
   of restrictions fixing the first leg. Cite v5 Section 4 for sectors
   sharing the first leg and for the tripling middle block.
2. Lemma 1, with the four-line factorization and minor proof.
3. Theorem 2, with the half-page proof via the Hankel lift.
4. Corollary 3, with Cauchy–Schwarz.
5. Lemma 5 (`Φ = P - 1/6`), with identity (D) at `κ = 5/6` and the two
   endpoint polynomials.
6. Theorem 6 and Corollary 7, with the ledger hypotheses stated
   explicitly. Cite v5 for `B_X`, `MM` identities, the separator,
   exactification, relative schemes and pooled recursion.
7. Three short remarks: the ordinary-only case `u = 1` (two lines);
   degenerations and the role of the first leg; the source model and
   scope.

## Adversarial review

Date: 18 October 2026. This is a referee pass on the note above and its
checker. I did not change the text above. The only new file is
[`experiments/shifted_chains_skeptic_hankel.py`](../experiments/shifted_chains_skeptic_hankel.py).
It uses only the standard library and imports neither project code nor the
checker's code. All its assertions use exact integer or `Fraction`
arithmetic. It runs in about 35 seconds:

```sh
python -I experiments/shifted_chains_skeptic_hankel.py
```

I also reran the checker (`python -I experiments/shifted_chains_check_hankel.py`,
which passes in about 4 s). I replayed the round-14 author and reviewer
receipts in `--check` mode. Both match, and neither changed any file.

### Verdict

**Confirmed, with minor corrections.** I tried to break every load-bearing
step and found no mathematical error. The steps I attacked were the local
Hankel ranks, the monotonicity and block-diagonality argument, the
Cauchy–Schwarz parity step, both potentials with their endpoint constants,
the telescoping and the paid ledger. The theorem and its consequence hold
as the checker states them. A preserving per-stage, per-orientation
auxiliary of any rank cannot bring the paid exponent of the shifted-chain
recipe down to 9/4 or below. The problems I found are two checks that do
not test what the note says they test, three imprecise sentences, and one
hypothesis that is presented as a restriction but loses no generality.
I also add two small strengthenings and one new consequence.

### Steps re-derived by hand (proved here)

- **Lemma 1.** The ordinary lifted entry is `[z = a+y+β]`; it factors
  through `t = y+β`, which takes `b+v-1` values. The middle entry is
  `[y = r-1-a-β+z] = [y = z+A+B]` with `A = u-1-a`, `B = v-1-β`; it factors
  through `t = z+A`, which takes `c+u-1` values. The identity minors need
  `v <= r` (rows `z = t <= b+v-2`) and `u <= r` (columns `y = t <= c+u-2`).
  The middle child written with reversed first index (`[y = x+z]`) has the
  same rank `c+u-1`. So the rank does not depend on that convention.
- **Theorem 2.** For a substitution that fixes leg 1,
  `Ψ(T') = (Γ ⊗ I) Ψ(T) (B ⊗ I)`. The lift is multiplicative, the rank of
  a Kronecker product is the product of the ranks over every field, and
  `T_g ∈ X ⊗ Y_g ⊗ Z_g` makes `Ψ(T)` block diagonal.
- **Corollary 3.** For even `r`, Cauchy–Schwarz gives
  `(Σ α^{N-J_g} α'^{J_g})(Σ α'^{N-J_g} α^{J_g}) >= M^2 (αα')^N`, and
  `4(t+r/2)(t+r/2-1) = A_r(t)`.
- **Identity (D).** Substitute `x = (t+2δ)/3` and `w = (t-δ)/3`. Then
  `4x+2w = 2(t+δ)` and `Q = (2t^2+2tδ-δ^2)/3`, and the numerator
  `(2/3)(4x+2w)(t^2-1) - 2t(Q-κ)` reduces to
  `(2/3)(tδ^2 - 2δ + (3κ-2)t)`. To avoid logarithms, the script checks the
  equivalent rational statement: `(t^2-1)^4 · d/dw[(Q-κ)^4/(t^2-1)^3]`
  equals `6(Q-κ)^3` times this numerator.
- **Endpoints.** I expanded `(6τ^2+24τ+11)^2 - 121(τ+1)^3` and
  `(τ^2+4τ+2)^2 - 4(τ+1)^3` by hand. I re-derived the constants `15/8`,
  `2` and `11/6`, and the admissible range `κ ∈ (3/4, 5/6]`.
- **Paid ledger against v5.** The pooled exponent is
  `log(r_*/m_*)/log(B/A)` (v5 Definition `def:relative-scheme`). Six
  orientations of `B_X(q)` give `MM_{q^2}` (v5 `eq:coset-dot-products`,
  second identity). `Q_{1,b} ≅ MM_{b^2}` and
  `R(S^σ_{r,b}) <= s^3` (v5 `eq:cyclic-identities`). With `2M-1 >= M` and
  `E_i >= 1`, this gives `p >= 3 log s0 / (log b_f + G) > 9/4`.

### Independent exact checks (checked)

| Part | What it tests | Size |
| --- | --- | --- |
| 1 | Hankel ranks of the ordinary child, the middle child and the reversed middle child, by an independent dense elimination | 405 `(r,c,u)` with `r,c <= 9`, over Q, GF(2), GF(3), GF(7) |
| 2 | A negative control that really has correct diagonal blocks and nonzero cross blocks; block-triangular junk | rank 4 instead of 8; 40 random patterns over 3 fields |
| 3 | Stage maps rebuilt from the round-8 description: unimodularity (`U U^{-1} = I`, integral inverse), the weight rule, canonical targets; **exact minimum rank of a preserving auxiliary**, by enumerating the whole affine space of preserving matrices | 10 width-one sets, 8 width-two sets; 79 (stage, type, field) minima, all `>=` the bound from (H), with equality in 20 |
| 4 | Identity (D) for all `κ`, the `κ = 5/6` and `κ = 2/3` certificates, endpoints, bridge `V`, by polynomial identity testing on grids larger than the degree; Lemma 5 at real (rational) points | 24,752 exact rational steps |
| 5 | **Every** legal chain in a bounded family, not a random sample | 849,091 chains: depth `<= 3`, arities 2, 3, 4, 6, 9, crop slacks 0, 1, 3, both orders, 6 terminals |
| 6 | The crop-slack identities used below; (H) for identity auxiliaries | 126,672 legal tuples; 6,375 cases |
| 7 | v5's separator applied to a single cross-sector term | `M <= 8` |

The minima in Part 3 are the strongest new evidence. The checker only
tested (H) against a few fixed tail projections. Here, for each stage
and type, every preserving matrix over GF(2) (and over GF(3) when the
space is small enough) was enumerated. Examples:

- `d = 3`, `(r,b,c) = (3,3,1)`, `N = 2`, type `(K,O,M) = (1,1,0)`:
  `M = 8`, minimum rank 7, bound 3, identity rank 9.
- `d = 4`, `(4,4,2)`, `N = 1`, type `K`: minimum rank 3, which equals the
  bound.
- `d = 2`, `(3,3,1)`: the binary tails of rank 3 and 1 from round 12 are
  optimal.

At these small widths the bound is often far from tight. Whether it is
approached at large width remains open, as the checker says.

Part 5 shows that in the bounded family the largest value of
`(log b_f + Σ bound)/((4/3) log s0)` is about 0.931. This is a display
value, not an assertion; the exact assertions are the integer
inequalities.

### Problems found

**P1 (minor; a check that does not test its claim).** Section 3 says
Part B's negative control "shows that identifying two sectors ... halves
the rank. The cross-sector zero hypothesis is therefore necessary." The
control (`coupled`) writes two copies of the word `OM` on the *same* `Y`
and `Z` coordinates. That tensor is `2·T_OM`, a scalar multiple of one
sector. It has no cross-sector block, and its diagonal blocks are not the
two target blocks. So it says nothing about the hypothesis. The conclusion
is still true. *Fix:* use a control with exact diagonal blocks and nonzero
cross blocks. Part 2 of my script takes `T_OM ⊗ J_2`, where the
sector-label pattern is the all-ones `2 × 2` matrix. Its diagonal blocks
are exactly `T_OM`, but its lifted rank is 4, not 8. The round-14
review's all-ones example makes the same point.

**P2 (minor; a claim that is not asserted, and a missing caveat).**
Section 2 says that Part C "confirms ... cross terms M→O, M→K and O→K are
present". `check_stage` counts cross terms but never asserts that they
exist or what kind they are. My Part 3 asserts that all three kinds
occur. The weight rule also needs a caveat. It holds for the **identity**
auxiliary, that is, for the sum over `j` of the pieces `E_{jj}`. Single
pieces, even diagonal ones, do lower the weight. For example, at
`(d,r,b,c) = (2,3,3,1)` the piece `E_{00}` has three weight-lowering
terms. They cancel only in the sum. So a diagonal projection auxiliary
is not automatically preserving either. Preservation is a real condition
that must be checked, as the round-12 tails do type by type. Nothing in
the proof depends on this, because the proof assumes preservation. The
note should still say it, so that a reader does not infer preservation
from the weight rule.

**P3 (minor; the wrong step is named).** Scope item 6 says that
"Corollary 3 needs `c <= b`, so v5-style splits with longer children are
not covered." In fact (H) holds for every `c`. For even `r`, the
Cauchy–Schwarz bound `h <= (1/2) log(A_r(b)/A_r(c))` needs no order
between `b` and `c`. What fails for a longer child is the **potential
step**. The function `(2/3) log Φ(r,w) - (1/2) log A_r(w)` is increasing,
so for `c > b` the inequality reverses. Example: `r = b = 1`, `c = 2`.
The odd bound gives `h <= log(2/4) ≈ -0.693`. The potential would need
`h <= (2/3) log(Φ(1,1)/Φ(1,2)) = (2/3) log(11/41) ≈ -0.877`, which is
false. So the telescoping breaks at a growing stage, even though such a
stage has negative gain. *Fix:* "The potential argument needs
`c_i < b_i` at every stage." This always holds for the shifted chain:
legality gives `c <= db/(d+2) < b`.

**P4 (minor; wording of the sharpness remark).** Section 8 says: "In the
homogeneous limit the bound is tight on the efficient ray." Only the
per-stage Hankel bound is. For each `d`, `(r+2b)/(r+2c) = (d+2)/d` on
the ray. The potential step is not tight there. Its homogeneous derivative
is `(2/3)(r-b)^2/(Φ_0 (r+2b))`, which vanishes only on the diagonal. On
the ray with `λ < 1`, the potential allows `λ^{-4/3}` per stage, against
the Hankel value `(d+2)/d`. At `d = 2` these are about 2.0070 and 2
(display only). So 9/4 is approached only as `λ → 1`, that is, with
growing arity, as in rounds 8 and 11. *Fix:* "The Hankel step is tight on
the efficient ray. The potential is tight only to first order as `λ → 1`,
so the limit 9/4 needs growing arity."

**P5 (minor; numbers that cannot be reproduced).** The remark gives
classical-flattening floors "about 2.05 and 1.95" but does not say for
which `d`, and the checker's script does not compute them. They are the
`d → ∞` limits on the efficient ray. Here `λ = 1 - 3/(2d) + O(d^{-2})`
and the middle fraction is `μ = 1/(d+2)`. For `u = 1` the floor tends to
`9/(2(3/2 + log 2)) ≈ 2.0518`, and for `u = r` to
`9/(2(3 - log 2)) ≈ 1.9507`. My script prints both as display values.
*Fix:* say "`d → ∞` limits". Also note that a floor below 2 is vacuous.

**P6 (minor; a hypothesis that loses no generality).** Issue 4 treats
"the same auxiliary rank in all six orientations" as a restriction. For
the barrier it is not one. `B_X(q') ⊵ B_X(q)` for `q <= q'` (set the extra
coordinates to zero). So a recipe with orientation-dependent ranks `q_π`
runs unchanged with `q = max_π q_π` in every orientation. Moreover, (H)
holds for each `q_π` separately. So any accounting, whether by the maximum
or by a geometric mean in a hypothetical rectangular ledger, obeys the
same chain bound. *Fix:* present the uniform rank as the form in which
v5's square ledger applies, not as a limit on the theorem.

### Strengthenings and a new consequence (proved here; checked)

**S1 (block-triangular cross terms).** Suppose that the target equals a
sector tensor plus cross terms only from `Y_g` to `Z_{g'}` with `g < g'`,
for some order of the sectors. Then `Ψ` is block triangular with the same
diagonal blocks. The rank of a block-triangular matrix is at least the sum
of the ranks of its diagonal blocks, over every field. So (H) still holds.
This complements the degeneration remark. It does not give a working
recipe, because v5's separator needs exact cross-sector zeros. Part 7
checks this for the separator weights of v5 Proposition `prop:separator`:

- A single cross term from `Y_g` to `Z_{g2}` with `g2 > g` gets a negative
  `t`-exponent (for example `g' = g+1`, `e = 0`, `e' = 1` gives `-1`).
- With `g2 < g`, a cross term survives at `t = 0`.

So the definition of "preserving" (exact targets, including cross-sector
zeros) is exactly what the recipe needs.

**S2 (long chains have large sources).** The next span is
`c_i + r_i - 1 <= s_i - 1`, so a chain with `L` stages has `s0 >= L+1`.
This justifies the words "long chains" in the source-model remark.

**S3 (how much compression can save at one stage).** Let
`σ = db - (d+2)c - r + 1 >= 0` be the crop slack. Then exactly:

- `d(2b+r-1) - (d+2)(2c+r-1) = 2σ`;
- `d^2 A_r(b) - (d+2)^2 A_r(c) = 4(d+2)(σ(r+2c) - σ + 1) + 4σ^2 - 4`.

Together with (H), these give the following for every preserving
auxiliary of a legal stage, with type `ν` and `M_ν` sectors:

- For odd `r`:
  `d^N/q <= ((d+2)^N/M_ν) · (1 + 2σ/((d+2)(2c+r-1)))^N`.
- For even `r`:
  `d^N/q <= ((d+2)^N/M_ν) · (1 + Δ/((d+2)^2 A_r(c)))^{N/2}`, where
  `Δ = 4(d+2)(σ(r+2c) - σ + 1) + 4σ^2 - 4`; at `σ = 0` this is
  `Δ = 4(d+1)`.

All round-11 ramp stages have zero slack. At such a stage with odd `r`,
compression can recover at most the type loss `(d+2)^N/M_ν`. For the
modal type this is at most `(N+1)^2`, by the round-8 estimate, which I
took from the notes without checking. This partly answers the checker's
first open point: preserving auxiliaries that attain (H) would remove
only type losses and the slack and parity factors. They could not change
the per-position gain by more than these factors.

### What I could not verify

- The checker's own list in Section 11 still applies.
- My exact minima cover only widths `N <= 2`. Over GF(2) they cover
  kernel dimension up to 17, and over GF(3) up to 9 or 10. Most arity-3,
  width-2 types were skipped; the script lists them.
- The modal type-loss estimate `M >= (d+2)^N/(N+1)^2` is taken from
  round 8, unchecked.

### Statements I endorse for the paper

1. **Definition.** An `(r,c;N)` sector tensor, and the relation `⊵_X`
   (restriction with the identity on the shared first leg), exactly as in
   Section 2. The middle child is `C^mid(r,c) = Σ x_x y_{r-1-x+z} z_z`.
2. **Lemma 1.** As stated, over every field.
3. **Theorem 2 (H).** As stated. It extends to degenerations with the
   identity on leg 1, and to block-triangular cross terms (S1).
4. **Corollary 3.** As stated (with `b >= c`).
5. **Lemma 5.** `Φ = P - 1/6`, for real `r >= 1` and `b > c >= 1`, with
   both endpoint constants `11/6`. The integer bridge for `P` is correct
   but unnecessary. Keep `15/16` only as an optional refinement.
6. **Theorem 6.** As stated, for chains with `c_i < b_i`. The next pair
   may also be any coordinatewise smaller pair (a crop), in either order,
   because `Φ` is symmetric and increasing.
7. **Corollary 7.** `p > 9/4`, with these hypotheses stated explicitly:
   identity on the shared leg; an independent auxiliary per stage and per
   orientation, with uniform rank without loss of generality (P6); the
   `s0^6` source charge; the terminal restricted to
   `Q_{1,max(r_f,b_f)} ≅ MM_{max^2}`; and the replication model
   `N_i k_i | P`.
8. **Remarks.**
   - The ordinary-only case `u = 1` gives `p >= 3` with no first-leg
     hypothesis.
   - Source-model robustness, as stated, using S2.
   - Scope: joint cyclic auxiliaries, auxiliaries coupling levels, general
     first-leg maps, and growing children (P3) are all outside the
     theorem.
   - Optionally, S3 on the finite-size effect of compression.
