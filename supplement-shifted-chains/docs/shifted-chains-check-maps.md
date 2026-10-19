# Verification: shifted-chain local maps, one-stage relation and chain counts

Date: 18 October 2026. Topic key: `maps`.

This note checks the local construction of
[round8-multiscale-construction.md](round8-multiscale-construction.md),
its review [round8-review-arbitrary-jump.md](round8-review-arbitrary-jump.md),
and the legal steps (1)–(3) and counts (7) of
[round11-arity-ramp.md](round11-arity-ramp.md) against the definitions and
lemmas of v5 (`manuscript/*.tex`, 79-page PDF). All statements were
re-derived from scratch. The only new files are this note and
[`experiments/shifted_chains_check_maps.py`](../experiments/shifted_chains_check_maps.py),
which imports nothing from earlier rounds. No other file was changed.

Status labels used below:

- **proved here**: a complete proof is given in this note;
- **checked**: confirmed by the script with exact integers or fractions on
  the stated small cases;
- **from notes, unchecked**: taken from the notes and not verified here.

## Verdict

The mathematics is correct. I found no error in the maps, the triangular
structure, the weights, the sector count, the orientation bookkeeping, the
stage relation, the separator degree, the exactification charge or the
chain counts. The script reproduces all of these exactly on small cases. It
also reproduces, independently, the source pairs, level counts and
source-side digit counts of all four round-11 certificates. Its 60-digit
pooled exponents fall inside the four certified intervals of the round-11
receipt.

All corrections concern how the results are stated and cited:

1. The note's `T_{d^{2N}}` is v5's matrix multiplication tensor
   `\MM_{d^{2N}}`. Likewise `T_{M^2}` is `\MM_{M^2}`.
2. The reset is **not** v5 Lemma 4.5 unless `c = r`. It is the label
   partition of OAI26 Lemma 4.2 with `(a,h) = (r,c)`. It needs its own
   short lemma, which must also cover `r = 1`, a case v5 excludes.
3. v5 states its oriented relations (Corollary 4.8) only for three
   orientations. The six-orientation stage relation needs its own
   proposition. The proof follows Corollary 4.8 line by line.
4. Before separation, the retained tensor is a sum of `M` sectors that
   share the first leg, not a direct sum. It becomes a direct sum only after
   the separator.
5. v5's pooled recursion (Lemma 2.4) gives the exponent
   `log(r_*/m_*)/log(B/A)` with no ceiling. The fixed-batch expressions with
   `ceil(r_*/m_*)`, or an added `log 2`, are valid but weaker than
   necessary.
6. The degree bound `6(M-1)` and the charge `E = 1+6k(M-1)` require Lu's
   polynomial separator (v5 Lemma 9.1(b)). With v5 Proposition 4.6 they
   become `6(M-1)^2` and `1+6k(M-1)^2`.
7. The notes reuse several letters: `B`, `c`, `M`, `n`/`N` and `T` each
   have two meanings. Section 1 fixes one name for each quantity.

## 1. Notation

This note uses v5 notation: `\restr` for restriction, `\degen` for
degeneration, juxtaposition for tensor product, `mT` for a full direct
sum, `T^\pi`, `\mathcal A_\pm`, `C(r,b)`, `B_X(d)`, `\MM_d`,
`S^\sigma_{r,b}` and `Q_{r,b}=S^+_{r,b}S^-_{r,b}`. To avoid clashes:

| Quantity | This note | Notes |
| --- | --- | --- |
| quotient (image) length `db-(d-1)c` | `L` | `B` |
| reset length `3c+r-1` | `L'` | — |
| sector count of one stage | `M` | `M` (round 8), `H_d` (round 11) |
| middle class and its count | "mid", `n_mid` | `M`, `n_M` |
| copies per sign in one stage | `N` (= chain `n`) | `N`, `n` |
| number of stages of arity `d` | `\ell_d` | `c_d` |
| auxiliary tensor | `\MM_{d^{2N}}` | `T_{d^{2N}}` |
| relative scheme | `r_*\MM_A \restr m_*\MM_B` | same |

The paper should use one fixed name for each of these quantities.

The *physical tensor* of a stage is

$$
U = U_{r,b,d} = C(r,b)\,B_X(d)
  = \sum_{\alpha<r}\sum_{\beta<b}\sum_{p<d} x_\alpha\, y_{p,\beta}\, z_{p,\alpha+\beta}.
$$

As a bilinear map, it multiplies a polynomial `P` with `r` coefficients by
`d` polynomials `F_0,…,F_{d-1}` with `b` coefficients each. The first leg
of `B_X(d)` is one-dimensional, so `U` has legs of dimensions `r`, `db`
and `d(b+r-1)`. This is the same physical tensor as v5's split
`C(r,b)B_X(h+1)` (v5 §4.1, "Binary forms"), with `d` in place of `h+1`.

## 2. Statements and proofs

### Lemma A (shifted chain) — proved here; checked

Let `r ≥ 1`, `d ≥ 2`, `1 ≤ c < b`, `h = b-c`, and `L = db-(d-1)c =
b+(d-1)h`. For a length `ℓ ≥ h+1`, let `W_ℓ = (F[z]_{<ℓ})^d` have
components `e_0,…,e_{d-1}`. Define

$$
\mathcal Q_\ell(F_0,\dots,F_{d-1})=\sum_{p=0}^{d-1} z^{ph}F_p\ \in F[z]_{<\ell+(d-1)h}.
$$

**(i)** `\mathcal Q_ℓ` is surjective. Its kernel is the direct sum of the
`d-1` subspaces `κ_j(F[z]_{<ℓ-h})`, `0 ≤ j ≤ d-2`, where
`κ_j(K) = -z^hK\,e_j + K\,e_{j+1}`.

**(ii)** For `0 ≤ e < ℓ+(d-1)h`, let `p_ℓ(e)` be the least `p` with
`ph ≤ e ≤ ph+ℓ-1`, and put `λ_ℓ(e) = z^{e-p_ℓ(e)h} e_{p_ℓ(e)}`. The
vectors `λ_ℓ(e)` and `κ_j(z^i)` (`j ≤ d-2`, `i < ℓ-h`) form a basis of
`W_ℓ`. Its matrix has entries in `{0, ±1}`. Its inverse is given by

$$
z^m e_p=\lambda_\ell(ph+m)+\sum_{j=p_\ell(ph+m)}^{p-1}\kappa_j\bigl(z^{\,m+(p-1-j)h}\bigr)
\qquad(\star)
$$

and has entries in `{0,1}`. Both matrices are therefore integral and
unimodular.

**(iii)** Use the basis of (ii) with `ℓ = b` on leg 2 and with
`ℓ = b+r-1` on the output space. Leg 3 changes contragrediently, as in v5
§4.1, "The tensor in the determinant bases". Keep the monomial basis on
leg 1. Then the coefficient of `x_α y'_u z'_v` in `U` is the coordinate
along output basis vector `v` of `z^α` times input basis vector `u`:

| input `u` | output `v` | coefficient |
| --- | --- | --- |
| quotient `λ_b(e)` | quotient `λ_{b+r-1}(e')` | `[e' = e+α]` |
| kernel `κ_j(z^i)` | kernel `κ_{j'}(z^{i'})` | `[j'=j][i'=i+α]` |
| kernel | quotient | `0` |
| quotient `λ_b(e)` | kernel `κ_j(z^{i'})` | `1` if `p_{b+r-1}(e+α) ≤ j < p_b(e)` and `i' = e+α-(j+1)h`, else `0` |

Thus `U` has diagonal blocks `C(r,L)` and `d-1` copies of `C(r,c)`, all
sharing leg 1. Every off-diagonal coefficient goes from a quotient input
to a kernel output. All maps are defined over `Z`, so the lemma holds over
every field.

*Proof.* (i) The intervals `[ph, ph+ℓ-1]` cover `[0, ℓ+(d-1)h-1]`, because
consecutive left endpoints differ by `h < ℓ`. Hence `\mathcal Q_ℓ` is
surjective. Next, `\mathcal Q_ℓ κ_j(K) = -z^{(j+1)h}K + z^{(j+1)h}K = 0`.
Suppose `\sum_j κ_j(K_j) = 0`. Component `0` gives `-z^hK_0 = 0`, and for
`p ≥ 1` component `p` gives `K_{p-1} - z^hK_p = 0`, so by induction every
`K_j` is zero. The kernel has dimension
`dℓ-(ℓ+(d-1)h) = (d-1)(ℓ-h)`, which equals the dimension of the sum, so the
sum is the whole kernel.

(ii) The number of vectors is `(ℓ+(d-1)h)+(d-1)(ℓ-h) = dℓ`, the dimension
of `W_ℓ`. The terms `κ_j(z^{m+(p-1-j)h}) = z^{m+(p-1-j)h}e_{j+1} -
z^{m+(p-j)h}e_j` telescope. Their sum over `j = p_0,…,p-1` is
`z^me_p - z^{m+(p-p_0)h}e_{p_0}`, and the last monomial is `λ_ℓ(ph+m)`.
The exponents satisfy `0 ≤ m+(p-1-j)h ≤ (ph+m)-p_0h-h ≤ ℓ-1-h`, so every
`κ_j` in `(⋆)` is defined. Hence every monomial is a `0/1` combination of
the `dℓ` vectors, so they form a basis with an integral inverse.

(iii) Multiplication by `z^α` commutes with the two quotient maps:
`\mathcal Q_{b+r-1}(z^αF) = z^α\mathcal Q_b(F)`. On kernels,
`z^ακ_j(z^i) = κ_j(z^{i+α})` in `W_{b+r-1}`, with `i+α < c+r-1`. On lifts,
`z^αλ_b(e)` is the single monomial `z^{α+e-p_b(e)h}e_{p_b(e)}` of
`W_{b+r-1}`. Applying `(⋆)` with `ℓ = b+r-1` gives quotient coordinate
`e+α` and the stated kernel coordinates, each with coefficient one. ∎

The off-diagonal block vanishes when `r = 1`. For `r ≥ 2` it is nonzero in
every case the script checked (300 of 300). So a type restriction, or some
other removal, is genuinely needed.

### Lemma B (crop and reset) — proved here; checked

Let `r, c ≥ 1` and `L' = 3c+r-1`.

**(i)** If `L ≥ L'`, setting `y_β = 0` for `β ≥ L'` and `z_γ = 0` for
`γ ≥ L'+r-1` restricts `C(r,L)` to `C(r,L')`.

**(ii)** Label the indices of `C(r,L')` as follows, with endpoints included:

| | left | middle | right |
| --- | --- | --- | --- |
| `β` (leg 2) | `[0, c-1]` | `[c, 2c+r-2]` | `[2c+r-1, 3c+r-2]` |
| `γ` (leg 3) | `[0, c+r-2]` | `[c+r-1, 2c+r-2]` | `[2c+r-1, 3c+2r-3]` |

In every term `x_α y_β z_{α+β}`, either the two labels are equal, or `β`
is middle and `γ` is outer. The left-left terms form `C(r,c)`. The
right-right terms form `C(r,c)` after subtracting `2c+r-1` from `β` and
`γ`. The middle-middle terms form `C(r,c)^{(23)}` after
`α ↦ r-1-α`, `β ↦ β-c` and `γ ↦ γ-(c+r-1)`.

**(iii)** `L ≥ L'` if and only if `(d+2)c ≤ db-r+1`.

*Proof.* (i) If `β < L'`, then `γ = α+β ≤ L'+r-2`, so no surviving term
uses a zeroed `z`.

(ii) If `β ≤ c-1`, then `γ ≤ c+r-2`, which is left. If `β ≥ 2c+r-1`, then
`γ ≥ β` is right. If `γ` is middle, then `β = γ-α ∈ [c, 2c+r-2]` is
middle. Hence unequal labels force a middle `β` and an outer `γ`.

The left block consists of all terms with `β < c`, which is `C(r,c)`. The
right block is a translate of it. For the middle block, put
`α' = r-1-α` and `γ' = γ-(c+r-1) ∈ [0, c-1]`. Then `β-c = α'+γ'`, so the
block is `\sum_{α'<r,γ'<c} x_{r-1-α'}y_{c+α'+γ'}z_{c+r-1+γ'}`. After the
stated reindexing this is `\sum x_{α'}y_{α'+γ'}z_{γ'} = C(r,c)^{(23)}`.

(iii) `L - L' = db-r+1-(d+2)c`. ∎

**Correspondence with earlier results.** For `c = r` we get `L' = 4r-1`,
and the intervals are exactly those of v5 Lemma 4.5. v5 states that lemma
only for `r ≥ 2` and fixes only the middle count. For general `c`, the
partition is that of OAI26 Lemma 4.2 (shifted tripling) with
`(a,h) = (r,c)`, where OAI26 writes `B = 3h+a-1`. OAI26 removes the cross
terms by a degeneration. v5 removes them by a type restriction. Here they
are removed together with the chain's cross terms (Lemma C). The general-`c`
version, including `r = 1`, needs the short proof above. It is a variant of
v5's lemma, not that lemma itself.

### Lemma C (stage type restriction) — proved here; checked

Assume `r ≥ 1`, `d ≥ 2`, `1 ≤ c < b` and `(d+2)c ≤ db-r+1`. Use the bases
of Lemma A, and label the coordinates on legs 2 and 3 of `U` as follows:

- kernel copy `j` gets the letter `K_j`;
- quotient coordinate `e` gets left, mid or right by Lemma B, or the letter
  "cropped" if `e ≥ L'` on leg 2 or `e ≥ L'+r-1` on leg 3.

The letters fall into three classes with weights: kernel
(`K_0,…,K_{d-2}`), weight 2; outer (left, right), weight 1; middle (mid),
weight 0.

Let `N ≥ 1` and `τ = (n_K, n_O, n_mid)` with sum `N`. In `U^{⊗N}`, use
product bases on legs 2 and 3. Set to zero every coordinate whose word
contains "cropped" or whose class counts differ from `τ`. Then:

1. This is a restriction defined over `Z`, and it does not depend on `t`.
2. Every surviving term has the same word on legs 2 and 3.
3. The result is `T = \sum_w T_w`, summed over the

   $$
   M=\frac{N!}{n_K!\,n_O!\,n_{\rm mid}!}\,(d-1)^{n_K}\,2^{n_O}
   $$

   words `w` of type `τ`. Here `T_w ∈ X ⊗ Y_w ⊗ Z_w`, with shared first leg
   `X = (F^r)^{⊗N}`, `Y = ⊕_w Y_w` and `Z = ⊕_w Z_w`. In v5's terms
   (§4, opening), these are `M` sectors sharing the first leg. **This is
   not a direct sum.**
4. `T_w = ⊗_θ D_{w_θ}`, where `D_λ` is the diagonal block of letter `λ`.
   Reorder the positions so that the non-middle positions come first and
   the middle positions last, each group in its original order, and
   reverse the first index (`α ↦ r-1-α`) at middle positions. Then `T_w`
   becomes exactly

   $$
   V = C(r,c)^{\otimes(N-n_{\rm mid})}\bigl(C(r,c)^{(23)}\bigr)^{\otimes n_{\rm mid}} .
   $$

   On the shared first leg, this word-dependent reindexing is applied only
   after separation (v5 §4, Lemma 4.5 and (B.6)).

*Proof.* Setting coordinates to zero is a restriction. Consider one
position, with uncropped letters `λ` on leg 2 and `μ` on leg 3 and a
nonzero coefficient. By Lemmas A(iii) and B(ii), either `μ = λ`, or
`w(μ) > w(λ)`:

- quotient to kernel raises the weight from at most 1 to 2;
- mid to outer raises it from 0 to 1;
- a kernel input reaches only the same kernel copy;
- left reaches only left or kernel, and right reaches only right or kernel.

In a product term, the coefficient is the product of the positionwise
coefficients. Hence `w(μ_θ) ≥ w(λ_θ)` at every position `θ`, with equality
only if `μ_θ = λ_θ`. If both words have class counts `τ`, both weight sums
equal `2n_K+n_O`. So equality holds at every position, and the two words
coincide.

To count the words, choose the class pattern (a multinomial coefficient),
then one of `d-1` kernel copies at each kernel position and one of left or
right at each outer position. Claim 4 follows from the product basis
together with Lemmas A(iii) and B(ii). ∎

This is the proof pattern of v5 Lemma 4.3: positionwise monotonicity plus
equal sums. The weights replace the filtration index.

### Proposition D (one-stage relation) — proved here from cited v5 results

Under the hypotheses of Lemma C, there is over `Q` a degeneration

$$
(2M-1)^6\,Q_{r,b}^{\otimes N}\,\MM_{d^{2N}}\ \degen\ M^6\,Q_{r,c}^{\otimes N}\,\MM_{M^2}
$$

whose polynomial has degree at most `6(M-1)`. In each of the six
orientations `π ∈ S_3`, it is built from three pieces: the restriction of
Lemma C, the separator of v5 Lemma 9.1(b) with shared leg `π(1)`, and fixed
coordinate permutations.

**Corollary D′ (exact stage).** For every `k ≥ 1`, with
`E = 1+6k(M-1)`,

$$
E\,(2M-1)^{6k}\,Q_{r,b}^{\otimes Nk}\,\MM_{d^{2Nk}}\ \restr\ M^{6k}\,Q_{c,r}^{\otimes Nk}\,\MM_{M^{2k}}
\quad\text{over } Q .
$$

Over `C`, v5 Proposition 4.6 may replace Lemma 9.1(b). The degree bound
then becomes `6(M-1)^2`, and `E = 1+6k(M-1)^2`.

*Proof.* First,
`U^{⊗N} = (C(r,b)B_X(d))^{⊗N} ≅ C(r,b)^{⊗N} B_X(d^N)`.

Fix `π ∈ S_3`. Apply the following to `(U^{⊗N})^π`, which is allowed by
the second part of v5 Lemma 2.1:

1. the restriction of Lemma C;
2. the separator of v5 Lemma 9.1(b) with shared leg `π(1)`;
3. the reindexing on the full target spaces, defined as in v5 (B.6): copy
   `g'` of `X` is reindexed by word `g'`, and sector `g` by word `g`.

This gives `(2M-1)(U^{⊗N})^π \degen M(VB_X(M))^π`, of degree at most
`M-1`. The reindexing does not depend on `t` and is defined on all target
variables, as Lemma 2.1 requires.

Tensor the six orientations with one parameter `t` (Lemma 2.1). This gives

`(2M-1)^6 ⊗_π (U^{⊗N})^π \degen M^6 ⊗_π (VB_X(M))^π`,

of degree at most `6(M-1)`. It remains to identify both sides by
coordinate permutations within each global leg:

- **Source.** Reordering factors gives
  `⊗_π (C(r,b)^{⊗N})^π ≅ Q_{r,b}^{⊗N}` (v5 (2.7)). By the second
  identity of v5 (2.2), `⊗_{π∈S_3} B_X(d^N)^π ≅ \MM_{d^{2N}}`.
- **Target.** Likewise `⊗_π B_X(M)^π ≅ \MM_{M^2}`. Also
  `⊗_π V^π = ⊗_π (C(r,c)^π)^{⊗(N-n_mid)} (C(r,c)^{π(23)})^{⊗n_mid}`,
  because `(T^{(23)})^π = T^{π(23)}`. Since `π ↦ π(23)` is a bijection of
  `S_3`, each orientation of `C(r,c)` occurs exactly `N` times. Hence
  `⊗_π V^π ≅ Q_{r,c}^{⊗N}` for every choice of the six sectors.

As in v5 Appendix B.4, these identifications are the same fixed maps on
every block, so they are also defined on the terms of positive degree.

For Corollary D′, apply v5 Lemma 2.2 (over `Q`, Lemma 9.1(c)) to the
`k`-th power. Use `(mT)^{⊗k} = m^kT^{⊗k}`, and `Q_{r,c} ≅ Q_{c,r}` from
v5 (2.8). ∎

**Remark (why both signs are needed).** For one sign `σ`,
`⊗_{π∈\mathcal A_σ} V^π ≅ (S^σ_{r,c})^{⊗(N-n_mid)} (S^{-σ}_{r,c})^{⊗n_mid}`,
because `π(23) ∈ \mathcal A_{-σ}`. For `c = r`, v5 closes this with
`S^+_{r,r} ≅ S^-_{r,r}` (v5 (4.6)). For `r ≠ c` with `r, c ≥ 2`, v5 has no
identity relating the two signs. The paired inventory `Q` avoids the
question, at the price of squaring every auxiliary dimension and raising
the separator copy factor to the sixth power. v5 Appendix A.4 makes the
same trade in its "sixfold construction".

### Proposition E (chain counts) — proved here; bookkeeping checked

Let `ℓ ≥ 1`, and let stages `i = 0,…,ℓ-1` have integers
`(r_i, b_i, c_i, d_i)` satisfying the hypotheses of Lemma C. Assume
`(r_{i+1}, b_{i+1}) = (c_i, r_i)` for `i < ℓ-1`, and
`(c_{ℓ-1}, r_{ℓ-1}) = (1,1)`.

Fix `n, k ≥ 1`, the same for every stage. For each `i`, fix a type `τ_i`
with sum `n`. Let `M_i` be its sector count (with `d = d_i`), put
`E_i = 1+6k(M_i-1)`, and let `s = r_0+b_0-1`. Then, over `Q`,

$$
r_*\MM_A\restr m_*\MM_B,\qquad
A=\prod_i d_i^{2nk},\quad B=\prod_i M_i^{2k},\quad
r_*=s^{6nk}\prod_i E_i(2M_i-1)^{6k},\quad m_*=\prod_i M_i^{6k}.
$$

If `B > A`, this is a relative scheme in the sense of v5 Definition 2.3.
v5 Lemma 2.4 (pooled recursion) then gives an `O(n^p)` algorithm with

$$
p=\frac{\log(r_*/m_*)}{\log(B/A)}\qquad(\ge 2),
$$

so `ω ≤ p`. No ceiling is needed. The fixed-batch bound
`log ceil(r_*/m_*)/log(B/A)` is weaker.

Grouping the stages by arity, with `τ_i` depending only on `d_i`, gives
round-11 (7), with `H_d = M_i` and `c_d` the number of stages of arity `d`.
Taking a constant `d` and `τ` with `(r_0, b_0) = (a, a)` gives round-8 (11).

*Proof.* Put `X_i = Q_{r_i,b_i}^{⊗nk}`, and let `X_ℓ = Q_{1,1}^{⊗nk} =
\MM_1`, since `C(1,1) = x_0y_0z_0`. Write `a_i = d_i^{2nk}`,
`h_i = M_i^{2k}`, `ρ_i = E_i(2M_i-1)^{6k}` and `μ_i = M_i^{6k}`.
Corollary D′ gives `ρ_i X_i \MM_{a_i} \restr μ_i X_{i+1} \MM_{h_i}`.
Restrictions survive tensoring with a fixed tensor, taking multiples, and
composition. By induction on `j`,

$$
\Bigl(\prod_{i<\ell}\rho_i\Bigr)X_0\MM_A\ \restr\
\Bigl(\prod_{i<j}\mu_i\Bigr)\Bigl(\prod_{i\ge j}\rho_i\Bigr)
X_j\,\MM_{h_0\cdots h_{j-1}}\MM_{a_j\cdots a_{\ell-1}},
$$

using v5 (2.1). At `j = ℓ`, the right side is `m_*\MM_B`.

For the source, v5 (2.8) with Lemma 9.1(a) gives `R(Q_{r_0,b_0}) ≤ s^6`
over `Q`, so `s^{6nk}\MM_1 \restr X_0` (a rank decomposition is a
restriction from the unit tensor). Tensoring with `\MM_A` and composing
gives the claim. The final statement is v5 Lemma 2.4. ∎

Three points about the chain:

- **Same `n` and `k` throughout.** These must be equal at every stage, so
  that each target is literally the next source. No catalyst, residual
  tensor or sign bookkeeping appears.
- **Exactify each stage separately.** v5 Lemma 2.1 covers tensor products,
  and fixed maps before or after a degeneration. It does not cover
  composing two degenerations in sequence. So the per-stage factor `E_i`
  is the correct charge under v5's lemmas. A single combined degeneration
  would need an additional reparametrization argument, which the notes do
  not claim.
- **Source evaluation charge.** `s^{6nk}` is the rational rank
  decomposition of the source `Q_{r_0,b_0}^{⊗nk}`. It comes from v5 (2.8)
  together with Lemma 9.1(a): Lagrange interpolation at the nodes
  `1,…,s` for each of the `6nk` convolution factors.

### Remark F (field scope) — proved here

- **Lemmas A–C** use integer matrices of determinant `±1` and coordinate
  selections or permutations. They hold over `Z`, hence over every field
  of every characteristic.
- **Proposition D, Corollary D′ and Proposition E** are proved over `Q`,
  hence over every field of characteristic zero. They use v5 Lemma 9.1:
  Lagrange weights on the nodes `1..M` and `1..2M-1` in the separator, the
  nodes `1..s` in the source decomposition, and the nodes `1..E_i` with
  binomial weights in exactification. Over `C`, v5 Proposition 4.6 and
  Lemma 2.2 with roots of unity also work, with the larger degree bound
  noted above.
- **Positive characteristic.** All denominators in the composed scheme
  have prime factors at most `max(s, max_i E_i)`, and Laurent entries are
  evaluated only at the nonzero nodes `ℓ ≤ E_i`. So reducing modulo a prime
  `p > max(s, max_i E_i)` gives the same counts over `F_p` (proof outline
  only). Because the `E_i` are astronomically large, the paper should
  simply state characteristic zero.

## 3. Answers to the checklist

**(a) Shifted-chain lemma.** Correct as stated in the notes. The formula
`\mathcal Q`, the image length `L = db-(d-1)c`, the `d-1` kernel copies of
length `c`, and the kernel-preserving property of multiplication are
Lemma A(i) and (iii). The diagonal sectors `(d-1)C(r,c)` and `C(r,L)` are
Lemma A(iii). The triangular structure, with only quotient-to-kernel
off-diagonal coefficients (all equal to 1, explicit formula in the table),
is Lemma A(iii). The forward basis has entries `0, ±1`, with
`db+(d-1)c` nonzero entries; the inverse has entries `0, 1` (Lemma A(ii)).
*Proved here; checked* for all 360 cases with `d = 2..5`, `r = 1..6`,
`b = 2..6` and every `c`, including the binary jump `(r,b,c,d) = (3,5,1,2)`
with `h = 4 > r`.

**(b) Crop and reset.** The crop is Lemma B(i). The crop condition
`L ≥ 3c+r-1` is equivalent to `(d+2)c ≤ db-r+1` (Lemma B(iii); checked on
143,550 tuples). The reset is Lemma B(ii). It is **not** v5's tripling
lemma except when `c = r`. It is OAI26 Lemma 4.2's partition with
`(a,h) = (r,c)`, used with a type restriction, and it needs its own
statement and proof (given above). That statement must include `r = 1`,
which v5 Lemma 4.5 excludes and which the last stages of every chain use,
for example `(r,b,c) = (1,2,1)`.

**(c) Weights and the retained tensor.** The weights 2, 1, 0, the strict
increase along every cross coefficient, the deletion of every cross term
by fixing `(n_K, n_O, n_mid)`, and the count
`M = N!/(n_K!n_O!n_mid!)(d-1)^{n_K}2^{n_O}` are all correct (Lemma C).
The retained tensor is a sum of `M` sectors sharing the first leg, not a
direct sum. Each sector equals
`V = C(r,c)^{⊗(N-n_mid)}(C(r,c)^{(23)})^{⊗n_mid}` after a word-dependent
reordering and first-index reversal. These are the 2,259 tensor-power
checks below.

The auxiliary dimension `d` enters as the dot product `B_X(d)` in each
tensor position and each orientation. That is, the physical tensor is
`C(r,b)B_X(d)` in v5's notation. Per copy of `S^σ_{r,b}`, the three
orientations of one sign turn it into `\MM_d`. Per copy of `Q_{r,b}`, the
six orientations give `\MM_{d^2}`. A stage with `N` copies per sign
therefore consumes `\MM_{d^{2N}}`, which is what "`T_{d^{2N}}`" denotes.
So "auxiliary dimension `d`" means a matrix multiplication factor of
side `d` per copy per sign, or side `d^2` per copy of `Q`.

**(d) Orientations and pairing.** Correct (Proposition D and the remark
after it). In one sign class, middle sectors flip the sign of `n_mid`
factors. Over all six orientations, every orientation of `C(r,c)` occurs
`N` times, so every sector gives `Q_{r,c}^{⊗N}`. The script checks the
permutation identities, `(T^{(23)})^π = T^{π(23)}`, and the multiset
counts for `N ≤ 4`.

**(e) Stage relation.** Correct, with `T` read as `\MM`. The separator has
degree at most `M-1` per orientation using v5 Lemma 9.1(b), so at most
`6(M-1)` in total. The exactification charge at tensor power `k` is
`E = 1+6k(M-1)`. The script checks the Lemma 9.1(b) coefficient identity
for `M = 1..16`, with maximal degree exactly `M-1`. It also applies the
separator to three actual retained stage tensors (`M = 2, 4, 12`) and
confirms degree `M-1` and constant term `⊕_g T_gB_X(M)`.

**(f) Composition and counts.** Correct (Proposition E). Each stage is
exactified separately, there is no catalyst, and the terminal is
`Q_{1,1} = \MM_1`. Round-11 (7) and round-8 (11) are special cases. The
result is a relative scheme in exactly v5's sense once `B > A`, which
holds for every reported certificate. v5 Lemma 2.4 gives
`ω ≤ log(r_*/m_*)/log(B/A)` without a ceiling. The source charge
`s^{6nk}` is explained in Proposition E.

**(g) Field scope.** See Remark F: the local maps hold over every field;
the stage relation and counts hold over `Q`, hence in characteristic zero.

## 4. Problems found and fixes

None of the problems below changes any count or exponent.

1. **Undefined `T_{d^{2N}}`, `T_{M^2}`** (round 8 (5), review).
   *Fix:* write `\MM_{d^{2N}}` and `\MM_{M^2}`, and derive them from v5
   (2.2) as in Proposition D.
2. **Reset cited as "the" tripling.** v5 Lemma 4.5 covers only `c = r`,
   only `r ≥ 2`, and a fixed middle count.
   *Fix:* state Lemma B (general `r, c ≥ 1`). Cite OAI26 Lemma 4.2 for
   the partition and v5 Lemma 4.5 for the case `c = r`.
3. **Six-orientation relation not in v5.** Corollary 4.8 is threefold, and
   its tripling case uses `S^+_{r,r} ≅ S^-_{r,r}`.
   *Fix:* state Proposition D. Cite v5 Appendix A.4 as precedent for the
   sixfold product.
4. **"Direct sum" before separation.** The retained tensor is a sum of
   sectors sharing the first leg. The notes themselves handle this
   correctly; only paraphrases (including the task wording) blur it.
   *Fix:* use v5's term "sectors sharing the first leg".
5. **Ceiling in the exponent.** Round-8 (12) and the fixed-batch columns
   use `ceil(r_*/m_*) ≤ 2r_*/m_*`.
   *Fix:* use v5 Lemma 2.4 directly, which removes the ceiling. The
   round-11 receipt already reports the pooled ("relative") interval.
6. **Which separator.** The degree `6(M-1)` and `E = 1+6k(M-1)` hold only
   with Lu's separator (v5 Lemma 9.1(b)). With v5 Proposition 4.6, the
   degree is `6(M-1)^2`.
   *Fix:* state the separator explicitly in Proposition D.
7. **Notation clashes** (`B`, `c`/`c_d`, `M`/`n_M`, `H_d`, `n`/`N`).
   *Fix:* the table in Section 1.
8. **Implicit hypotheses.** These are not errors, but the paper must state
   them: `d ≥ 2` and `1 ≤ c < b` (so `b ≥ 2`); the same `n` and `k` at
   every stage; terminal `(c_{ℓ-1}, r_{ℓ-1}) = (1,1)`; `B > A` before
   invoking v5 Lemma 2.4; exactification per stage.

## 5. Script and results

Run from the repository root (about 150 seconds):

```sh
python -I experiments/shifted_chains_check_maps.py
```

The script uses only the standard library. All identity checks use Python
integers or `Fraction`; it compares sparse coefficient dictionaries
exactly. It reads `results/round11-arity-ramp.json` only to compare
numbers; all quantities are recomputed independently. Results of the run:

| Check | Range | Result |
| --- | --- | --- |
| Lemma A: bases, integer inverses, `\mathcal Q`-sequence, full coefficient table | `d=2..5`, `r=1..6`, `b=2..6`, all `c` (360 cases) | all pass; nonzero quotient-to-kernel block in all 300 cases with `r ≥ 2`, none for `r = 1` |
| Lemmas B, C at one position: crop, labels, weights, diagonal blocks equal `C(r,c)` / `C(r,c)^{(23)}` | all 193 legal cases above | all pass; cross coefficients mid→outer 1,832, mid→kernel 724, outer→kernel 495, all strictly weight-increasing |
| Tensor powers: restricted `U^{⊗N}` equals `\sum_w ⊗_θ D_{w_θ}`; words equal on legs 2 and 3; number of words equals `M`; disjoint sector coordinates; every sector reindexes to `V` | legal cases with `d ≤ 4`, `N = 1, 2` and every type, `N = 3` and every type when `rc ≤ 6` | 2,259 checks pass; largest `M = 54`; largest retained tensor 11,664 terms |
| Independent route: expand the physical power `(C(r,b)B_X(d))^{⊗N}`, transform with Kronecker powers of the basis matrices, restrict, compare | 10 cases, `N = 2, 3`, mixed types including `(1,1,1)` | all equal the claimed sum |
| v5 Lemma 9.1(a): rational rank decomposition of `C(r,b)` | `r, b ≤ 6` | exact |
| v5 Lemma 9.1(b): separator coefficient identity | `M = 1..16` | exact; maximal degree exactly `M-1` |
| Separator applied to retained stage tensors | `M = 2, 4, 12` | degree `M-1`; constant term `⊕ T_gB_X(M)` |
| v5 Lemma 9.1(c): finite-difference identity | `E ≤ 40` | exact |
| Orientations: `(T^{π'})^π = T^{ππ'}`, `(T^{(23)})^π = T^{π(23)}`, `C(c,r) = C(r,c)^{(12)}`, multiset counts | `S_3`, `N ≤ 4` | pass |
| Legal step (1) ⇔ `L ≥ 3c+r-1` | `d ≤ 12`, `r, b ≤ 30` | 143,550 pass |
| Smallest parent (2): slack in `[0, d)`, legality, minimality | `d ≤ 20`, `r, b ≤ 40` | 30,400 pass |
| Zero-slack ramp (3); ramp gain identity (4), first equality | `j ≤ 500`; `R ≤ 60` | pass |
| Round-8 two-stage cycle (7) and reverse recurrence (8) | `d = 3..60`, `a ≤ 2000`, 60 cycles | 115,942 pass |
| Composition bookkeeping equals closed forms (7) and (11) | 12 chains, `(n,k) ∈ {(1,1),(2,1),(3,2)}` | exact equality |
| Round-8 row 1 (`d=5`, 200 cycles, `t=30`, `k=500`) | fixed-batch (12) at 60 digits | 2.758668184196361544…, inside the reported interval; `A` has 58,713,481 digits; `M > d^N` |
| Round-8 row 4 | `A = 100^{20400000000000000}` | 40,800,000,000,000,001 digits |
| Round-11 rows `D = 2, 4, 8, 16` | chains regenerated from (2)–(3) | source pairs, level counts (130, 462, 1,726, 3,454) and digits of `A` (17,857,969; 1,416,018,955; 112,670,650,787; 4,724,998,039,558) match; the receipt's types are exchange-local modes; pooled exponents 2.3371325979…, 2.2881849806…, 2.2677060500…, 2.2601117314… lie inside the receipt's certified intervals; fixed-batch values lie below the table's thresholds; `B > A` in all four |

The exponent values in the last two rows are 60-digit decimal
computations. They confirm that the count formulas were applied
correctly, but they are not new interval certificates.

## 6. v5 results to cite

Numbers refer to the 79-page v5 PDF.

- §2.1: conventions (`\restr`, `\cong`, `mT`, juxtaposition, `T^π`,
  `\mathcal A_±`, global legs).
- (2.1) `\MM_d\MM_{d'} ≅ \MM_{dd'}`; (2.2), second identity,
  `⊗_{π∈S_3} B_X(d)^π ≅ \MM_{d^2}`; (2.3) `C(r,b)`.
- (2.5)–(2.6) `S^σ_{r,b}` and its identities (for the remark on signs);
  (2.7)–(2.8) `Q_{r,b}`, `Q_{r,b} ≅ Q_{b,r}`, `R(Q_{r,b}) ≤ (r+b-1)^6`.
- §2.3: definition of degeneration; Lemma 2.1 (Composition); Lemma 2.2
  (Exactification).
- Definition 2.3 (Relative scheme); Lemma 2.4 (Pooled recursion).
- §4, opening paragraph: sectors sharing the first leg. §4.1:
  contragredient change of basis ("The tensor in the determinant bases")
  and "Words, types and sectors". Lemma 4.3, as the proof pattern for
  Lemma C.
- Lemma 4.5 (Type restriction for a tripling): the case `c = r` of
  Lemma B.
- Proposition 4.6 (Separator): the input form and the constant term.
  Remark 4.7 (Lu's polynomial separator).
- §4.4 and Corollary 4.8: the template for Proposition D; (4.6) for the
  single-sign comparison.
- Appendix B: (B.5)–(B.8), reindexing on the full target spaces and the
  complete relation map.
- Appendix A.2 and A.4: precedent for the sixfold product, with
  auxiliaries `\MM_{d^{2Nw}}` and doubled degree.
- Lemma 9.1 (Rational interpolation): (a) source rank decomposition,
  (b) separator with `2M-1` copies and degree `≤ M-1`, (c) rational
  exactification.
- External: OAI26 Lemma 4.2 (shifted tripling, partition for general
  `(a,h)`) and Proposition 3.1; Lu26 Proposition 2.1; Bini80.

v5 §§3 and 5–8 (profiles, flows, rounding, extraction) are not needed for
the shifted-chain construction.

## 7. Not verified here

- The allowance and source-size theorems: round-8 bounds packet,
  round-11 (5)–(6), `log A = Θ(ε^{-9/2}\log^3(1/ε))`.
- The ideal limits: round-8 (10), `p_d → 9/4` and its `9/(8d)` correction.
- The type estimate `M ≥ (d+2)^N/((N+1)(3t+1))`.
- `F_R ≥ R^{4/3}` and the identity `F_R = F(R,R)` with v5's profile.
- The rigour of the rational interval enclosures. I only reproduced the
  values at 60 digits.
- The round-14 Hankel limit and the coefficient and precision bounds.

All of these are from the notes and unchecked here; they belong to other
topics.

## Adversarial review

Date: 18 October 2026. Role: adversarial referee for this note. New file:
[`experiments/shifted_chains_skeptic_maps.py`](../experiments/shifted_chains_skeptic_maps.py).
It imports nothing from the checker's script or from earlier rounds, uses
only integers and `Fraction`, and runs in about 12 seconds:

```sh
python -I experiments/shifted_chains_skeptic_maps.py
```

### Verdict

**The mathematics of this note holds.** I re-derived the most fragile steps
on my own and found no error in any map, identity, interval endpoint, weight,
sector count, degree bound, exactification charge or chain count. I also
checked every v5 citation against the 79-page PDF. I endorse Lemmas A–C,
Proposition D, Corollary D′, Proposition E and Remark F, subject to the
corrections below. All of them are minor: notation and wording in the
paper-ready statements, two gaps in what the checker's script actually
tests (both now closed), and a few precise refinements. None changes a
count or an exponent.

### What I did

1. **Reran the checker's script.** It passes in 110 seconds and prints the
   numbers reported in Section 5.
2. **Re-derived independently:**
   - the inverse formula `(⋆)` and its index range;
   - the quotient-to-kernel formula `p_{b+r-1}(e+α) ≤ j < p_b(e)`,
     `i' = e+α-(j+1)h`;
   - the crop thresholds `L'` and `L'+r-1`, and the six interval endpoints
     of Lemma B;
   - the weight monotonicity in Lemma C, including the facts that left never
     reaches right, right never reaches left, and distinct kernel copies
     never meet;
   - `(T^{(23)})^π = T^{π(23)}` under v5's convention
     `(T^{π'})^π = T^{ππ'}`;
   - the source identification `⊗_π B_X(d^N)^π ≅ \MM_{d^{2N}}`;
   - the bookkeeping that turns per-stage restrictions
     `ρ_i X_i\MM_{a_i} \restr μ_i X_{i+1}\MM_{h_i}` into
     `r_*\MM_A \restr m_*\MM_B`;
   - formula (12) of round 8 from (11).
3. **Checked the citations.**
   - v5 equation numbers, from the PDF text: (2.1)–(2.8), (4.6) and
     (B.5)–(B.8).
   - v5 statement numbers: Lemma 2.1, Lemma 2.2, Definition 2.3,
     Lemma 2.4, Lemma 4.3, Lemma 4.5, Proposition 4.6, Remark 4.7,
     Corollary 4.8 and Lemma 9.1.
   - v5 Appendix sections A.2 ("Integer types and their entropy
     identity"), A.4 ("Comparison with the main construction") and B.4.
   - The OAI26 claim, against the source in `upstream/build/paper.tex`.
     Its Lemma 4.2 ("Shifted tripling") proves `P(a,3h+a-1) ≥ 3P(a,h)`.
     Its proof uses exactly the partition of Lemma B with `(a,h) = (r,c)`
     and removes the cross terms by a weight degeneration (weight `+1` on
     middle `Y`, `-1` on middle `Z`). Its Proposition 3.1 is "Finite
     separation". The checker's correspondence is correct.
4. **Wrote new exact checks** for what the checker's script does not test
   (table below).

| Check | Range | Result |
| --- | --- | --- |
| Lemma A(iii) by the bilinear-map route (multiply each basis vector by `z^α`, read coordinates with `(⋆)`), **including the explicit quotient-to-kernel formula** | `d = 2..7`, `r = 1..6`, `b = 2..8`, all `c` (1,008 cases) | exact; off-diagonal block nonzero in exactly the 840 cases with `r ≥ 2` |
| After the crop, quotient-to-kernel coefficients survive iff `b ≤ 3c+r-2` (`r ≥ 2`, legal) | same range | holds; 108 legal cases with `b ≥ 3c+r-1`, where the crop already removes them |
| Smallest-parent stages (round 11 (2)) never have `b̂ ≥ 3r+b-1` | `d ≤ 30`, `r, b ≤ 60` (102,660) | holds (also proved below) |
| Round-8 two-stage cycle: whenever `r ≥ 2`, `b < 3c+r-1` | `d = 3..60`, `a ≤ 2000` (231,884 stages) | holds (also proved below) |
| One orientation end to end from the **physical** `U^{⊗N}`: basis change, crop and type restriction summed over physical terms; no cross-word term reaches the separator; Lemma 9.1(b) on `2M-1` copies; **word-dependent reindexing on all target variables**; constant term compared with `M(VB_X(M))` built independently from `C(r,c)` | 12 cases, `N ≤ 3`, `M ∈ {1,2,3,4,12}`, mixed types incl. `(1,1,1)`, `r = 1, 2, 3` | exact; no negative power of `t`; maximal degree exactly `M-1` in every case |
| **Exactified restriction**, by literal evaluation of the full composite leg maps at `t = 1..E` with weights `(-1)^{ℓ-1}\binom Eℓ` (v5 Lemma 9.1(c)): `E(2M-1)^k U^{⊗Nk} \restr M^k(VB_X(M))^{⊗k}`, `E = 1+k(M-1)` | 5 cases, `k = 1` (`M = 2, 4, 4`) and `k = 2` (`M = 2`, two cases) | exact equality with the target |
| Negative control: fix only the middle count (as v5 Lemma 4.5 does) | `(r,b,c,d) = (2,3,1,2)`, `N = 1, 2` | cross-word terms survive (1, 13 and 4 of them), so the word-equality test can fail and the full type is needed there |
| Six orientations on **actual tensors**: `⊗_π V^π` equals `Q_{r,c}^{⊗N}` after the explicit slot permutation `(π,s) ↦ π` (ordinary) or `π(23)` (middle) | `(r,c) ∈ {(2,3),(3,2),(2,2),(1,3)}` with `N = 1`; `(1,2),(2,1)` with `N = 2`; all `n_mid` (14 checks) | exact |
| `⊗_{π∈S_3} B_X(m)^π = \MM_{m^2}` after grouping the slot indices by `π(1)` | `m = 2, 3` | exact |
| Denominators in Lemma 9.1(a) and (b): all primes are at most `n-1` and at most `2M-2`, respectively | `n ≤ 14`, `M ≤ 12` | holds |
| Round-11 digit counts of `A`, with a margin from the integer boundary | `D = 2, 4, 8, 16` | all four match; `log10 A` is at least 0.14 away from an integer |

The full six-orientation degeneration is too large to expand, even for
the smallest cases. It is covered in two pieces: one orientation end to
end, and the orientation identification on actual tensors. Lemma 2.1
combines the two.

### Findings

All findings are minor.

**F1. Wrong restriction symbol in the JSON statements.** The JSON
statements of Corollary D′ and Proposition E write the restriction with
`\trianglerighteq`, which prints as `⊵`. In v5, `⊵` (`\unrhd`, macro
`\degen`) means *degeneration*. v5's restriction symbol is `⪰`
(`\succeq`, macro `\restr`); see Definition 2.3 in the PDF. The body of
this note uses the macros correctly.
*Fix:* write `\restr` in every paper statement of a restriction.

**F2. Over `Q`, only Lemma 9.1(c) applies.** The JSON proof of Corollary
D′ says "Apply v5 Lemma 2.2, or Lemma 9.1(c)". v5 Lemma 2.2 uses `ζ_E`, so
on its own it gives the restriction over `Q(ζ_E)`, not over `Q`. The note
body says this correctly ("over `Q`, Lemma 9.1(c)").
*Fix:* for the rational statement, cite Lemma 9.1(c) alone.

**F3. "Same `n` and `k` … must be equal" is too strong.** Composition
needs only that each target equals the next source, that is,
`N_i k_i = N_{i+1} k_{i+1}`. With stage-dependent `(N_i, k_i)` and a common
product `P = N_i k_i`, the same proof gives:

$$
A=\prod_i d_i^{2P},\quad B=\prod_i M_i^{2k_i},\quad
r_*=s^{6P}\prod_i E_i(2M_i-1)^{6k_i},\quad m_*=\prod_i M_i^{6k_i},\quad
E_i=1+6k_i(M_i-1).
$$

A common `(n,k)` is a valid simplifying hypothesis.
*Fix:* drop "must", or state the general form.

**F4. The remark on "why both signs are needed" overstates the cost.** The
remark says pairing comes "at the price of squaring every auxiliary
dimension and raising the separator copy factor to the sixth power". By v5
Appendix A.4, a sixfold construction with power `k` has the same `r_*`,
`m_*`, `A` and `B` as a threefold construction with power `2k`. The same
holds here: `E = 1+6k(M-1)` equals `1+(2k)·3(M-1)`. So pairing costs
nothing in the pooled exponent, and nothing in `A` at matched counts. It
only coarsens the smallest available size.
*Fix:* say that the paired form has the counts of a threefold form at
doubled power, and that no threefold form is available when `c ≠ r`.

**F5. The checker's script does not test the explicit off-diagonal
formula.** Its `check_shifted_chain` checks only that quotient-to-kernel
coefficients equal 1 and point from quotient to kernel. Yet Section 5 lists
"full coefficient table" as checked. The formula in row 4 of the Lemma
A(iii) table was proved but not tested.
*Closed:* the new script checks the exact formula in 1,008 cases. It holds.

**F6. The checker's script does not test the last step of the stage.** It
applies the separator to the retained tensor and compares only the
constant term. It does not check three things:

- the word-dependent reindexing on all target variables (the hypothesis of
  v5 Lemma 2.1 used in Proposition D);
- that the restriction, computed from the physical tensor, gives the
  separator only same-word terms;
- the exactified restriction itself.

*Closed for small cases:* see the table. The degree `M-1` is attained in
every tested case, so for Lu's separator the charge `E = 1+6k(M-1)` cannot
be lowered within v5's Lemma 9.1(c).

**F7. Lemma A's nonvanishing claim can be proved, and the crop needs a
caveat.** The note says the off-diagonal block is nonzero for `r ≥ 2` "in
every case the script checked". This holds in general. Take `e = b` and
`α = 0`. Then `p_b(b) = 1` and `p_{b+r-1}(b) = 0`, so the coefficient of
`x_0 y'_{λ_b(b)} z'_{κ_0(z^c)}` is 1.

After the crop, however, a kept quotient input `e ≤ 3c+r-2` reaches the
kernel only if `e ≥ b`. So for `r ≥ 2` the quotient-to-kernel coefficients
survive the crop exactly when `b ≤ 3c+r-2`. If `b ≥ 3c+r-1`, only the
reset's mid-to-outer cross terms remain. Then fixing `n_mid` alone
suffices, and it gives more sectors: `\binom{N}{n_mid}(d+1)^{N-n_mid} ≥ M`.

This never happens in the construction, so Lemma C's full type is the
right restriction there:

- *Smallest parent* (round 11 (2)). Here `b̂ ≥ 3r+b-1` together with the
  slack bound `d b̂ ≤ (d+2)r+b-1+(d-1)` gives `(d-1)(2r+b) ≤ 2(d-1)`.
  This is impossible.
- *Round-8 cycle.* Stage `(a,a,c)` would need `c ≤ 1/3`. Stage `(c,a,c)`
  would need `a ≥ 4c-1`. Combine this with `(d+2)c ≥ (d-1)a-d` and, when
  `c ≥ 2`, with `a ≥ (2d+3)/(d-1)`. This is impossible for `d ≥ 5`
  because `(2d+3)(3d-6)-(5d+2)(d-1) = d^2-16 > 0`. For `d = 4` the two
  inequalities leave no `a`. For `d = 3` they leave only `a = 5`, where
  `c = 2` and `4c-1 = 7 > 5`. (Stages with `c = 1` have `r = 1` and no
  off-diagonal block.)

Both cases are also checked in the script.
*Fix:* replace "in every case the script checked" by the one-line proof,
and add the crop caveat as a remark.

**F8. Make the OAI26 citation precise.** OAI26 Lemma 4.2 is a profile
inequality. The partition occurs in its proof. (I confirmed the
correspondence `(a,h) = (r,c)` from the source.)
*Fix:* cite "the partition in the proof of [OAI26, Lemma 4.2]".

**F9. State the algorithm bound with its `p = 2` case.** v5 Lemma 2.4
gives `O(n^p)` only for `p > 2`, and `O(n^2 log n)` when `p = 2`.
Proposition E should conclude `ω ≤ p`, or quote both cases.

### Points checked and found correct

These are the points where I expected errors and found none:

- **Off-by-one points.** The `(⋆)` kernel index range `0 ≤ m+(p-1-j)h ≤
  ℓ-1-h`. The crop thresholds `β < L'` and `γ < L'+r-1`. The right block
  of leg 3 ending at `3c+2r-3 = L'+r-2`. The middle block's leg-2 length
  `c+r-1` and leg-3 length `c`.
- **Lemma C's monotonicity.** It does not depend on the crop: cropped
  inputs are zeroed, and no kept input reaches a cropped quotient output.
- **Exactification of each stage separately** is what v5 Lemmas 2.1–2.2
  support. v5's definition of degeneration does not compose sequentially
  without reparametrization.
- **Remark F's characteristic-`p` outline.** Its sufficient condition
  `p > max(s, max_i E_i)` is correct. The denominators are bounded as
  checked above, `E_i ≥ 6M_i-5 ≥ 2M_i-1`, and the exactification weights
  are integers. The condition can be relaxed by using other nodes in
  larger fields. I agree that the paper should state characteristic zero.

### Final statements I endorse

- **Lemma A (shifted chain).** As stated, over `Z`. Replace the "checked"
  sentence on nonvanishing by the proof in F7. *Proved; checked on 1,008
  cases.*
- **Lemma B (crop and reset).** As stated, for all `r, c ≥ 1`, with the
  citation fix F8. *Proved; checked.*
- **Lemma C (stage type restriction).** As stated: `M` sectors sharing
  the first leg, not a direct sum. Optionally add the F7 remark on when
  `n_mid` alone suffices. *Proved; checked, including from the physical
  tensor.*
- **Proposition D (one-stage relation).** Over `Q`:
  `(2M-1)^6 Q_{r,b}^{⊗N}\MM_{d^{2N}} \degen M^6 Q_{r,c}^{⊗N}\MM_{M^2}`,
  with degree at most `6(M-1)` using Lu's separator (v5 Lemma 9.1(b)), or
  at most `6(M-1)^2` over `C` using v5 Proposition 4.6. *Proved from v5
  results. One orientation checked end to end; the orientation
  identification checked on actual tensors.*
- **Corollary D′ (exact stage).** Over `Q`, for every `k ≥ 1`, with
  `E = 1+6k(M-1)`:
  `E(2M-1)^{6k} Q_{r,b}^{⊗Nk}\MM_{d^{2Nk}} \restr M^{6k} Q_{c,r}^{⊗Nk}\MM_{M^{2k}}`,
  via v5 Lemma 9.1(c). *Proved. The single-orientation analogue was checked
  as an exact restriction for `k = 1, 2`.*
- **Proposition E (chain counts).** As stated with `\restr`, optionally
  with the stage-dependent `(N_i, k_i)` form of F3. If `B > A`, v5
  Definition 2.3 and Lemma 2.4 give `ω ≤ p = log(r_*/m_*)/log(B/A)`, with
  no ceiling. *Proved; bookkeeping checked by the checker.*
- **Remark F (field scope).** As stated: the local maps hold over every
  field; the stage relation and the counts hold over `Q`, hence in
  characteristic zero. The characteristic-`p` statement is a correct
  sufficient outline. *Proved over `Q`.*

### Not verified here

- Lu26 itself is not in the repository. I relied on v5 Lemma 9.1(b),
  which v5 proves. Both scripts verify its coefficient identity
  (`M ≤ 16`) and its action on retained stage tensors.
- The full six-orientation degeneration was not expanded as one tensor;
  see the remark after the table.
- I did not re-certify the round-8 and round-11 exponent intervals. I
  checked only the digit counts of `A` with a margin, and I repeated the
  checker's 60-digit comparison.
- Out of scope, as listed in Section 7: allowance theorems, ideal limits,
  type estimates and the Hankel limit.
