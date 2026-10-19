# Shifted-chain follow-up: novelty and related work

Date: 18 October 2026 (US Eastern; the web checks ran near 00:50 UTC on
19 October). Topic key: `literature`. Companion files:
[draft bibliography](shifted-chains-references-draft.bib) and
[exact checks](../experiments/shifted_chains_check_literature.py).

This note checks what the follow-up paper on shifted polynomial chains can
claim as new, which published results it must credit, and how to cite the
works involved. It covers the five tasks (a)–(e). It does not re-verify the
finite counts of rounds 8–14; other topic checks do that.

## Summary

- **(a) The shifted map is partly known.** For shift `h = 1` and two
  components it is the determinant exact sequence of OpenAI's Lemma 4.1.
  For shift 1 and `d` components, its kernel is the first step of the
  determinant (Clebsch–Gordan) filtration: Maakestad's Lemma 2.5 and
  v5's filtration `F^1` in Section 4.1. For shifts `h >= 2` I found no
  source. Its kernel decomposition is an elementary syzygy fact, the
  substituted form of the shift-1 sequence. The "reset" applied after each
  split is OpenAI's Lemma 4.2 ("shifted tripling"), which treats every
  column, and also Uznański's Lemma 2.1(3). The round-8 notes credit
  neither. The scalar inequalities that the stages imply follow from the
  profile axioms. The 9/4 limit at the level of scalar values is therefore
  already a consequence of v5's Remark 3.3 and Filmus's Section 4.3.
- **OAI26Comp is not related** to shifted chains, apart from general
  themes. It separates labels with an auxiliary finite abelian group tensor
  in the Coppersmith–Winograd setting and uses no convolution tensors or
  polynomial maps.
- **(b) No other work bounds seed sizes near 9/4.** v5 is the only work that
  gives explicit sizes, and they are doubly exponential in `1/eps`. The other
  works either prove existence only or say explicitly that they do not bound
  sizes. A proof that `log A` is polynomial in `1/eps` would be new. That
  conclusion depends on the other topic checks confirming the bound.
- **(c)** [The draft bibliography](shifted-chains-references-draft.bib)
  has 38 entries, with v5's keys reused. Its metadata was checked against
  arXiv, Crossref, Zenodo and the GitHub API, and it compiles with
  `plainnat`.
- **(d) v5 is less anonymous than intended.** The paper has no byline and
  no URL. However, its repository is public, and Filmus's manuscript cites
  version 2 with the repository URL. I propose an `Anonymous` entry without
  a URL and give a pinned public variant.
- **(e)** Section 6 lists exact dates. Every OpenAI preprint is unchanged
  since its release on 6 October 2026. No later arXiv paper, through the
  announcements of 16 October 2026, touches shifted chains or seed sizes.

## 1. What was checked and how

Sources read locally:

- v5: `manuscript/introduction.tex` (Sections 1.4–1.5),
  `manuscript/maps.tex`, `manuscript/profile.tex`,
  `manuscript/discussion.tex`, and `manuscript/references.bib`.
  Theorem numbers come from `manuscript/build/main.aux`.
- The OpenAI preprint in `upstream/` (`paper.tex` and `paper.pdf`). Page
  numbers come from `pdftotext`.
- Filmus's manuscript, bibliography and `CITATION.cff` at commit `8e38460c`,
  from the vendored copy in
  `all-field-formalization/.lake/packages/blockIdentities/source/`.
  This copy also contains Uznański's arXiv v2 source, with its own
  provenance record.
- The literature knowledge base under `literature/`. Maakestad's full text
  supplied the locators for his Lemma 2.5 and Section 2.
- The round 8, 11 and 14 notes, to see what they claim and credit.

Sources fetched into `/tmp`, which is not kept in the repository:

- The OAI26Comp sources (`build/*.tex`) and PDF, the Staggered-extraction
  PDF, and the "Finite tensor savings" PDF, all from `openai/math` `main`.
- Lü's arXiv source.
- The v5 PDF at the public commit `6562ac60`. Its `pdftotext` output is
  identical to the local `manuscript/finite-extraction.pdf`; only the build
  time stamps differ.
- The `main.tex` title of every public version of v5.

Metadata services: the arXiv API, abstract pages and listing pages; Crossref;
the Zenodo API; and the GitHub API for commit histories.

Search coverage, which is necessarily incomplete:

- arXiv API keyword queries for "matrix multiplication exponent", "convolution
  tensor", "shared leg", "polynomial multiplication" with "tensor", "laser
  method", "asymptotic rank", "border rank", "bilinear algorithm",
  "Coppersmith-Winograd", "asymptotic spectrum", "Toom-Cook", "overlap-add" and
  "9/4".
- Complete title lists of the October 2026 submissions in cs.CC (161), cs.DS
  (307), cs.SC, math.AG (409), math.RT (164) and math.CO (734), filtered by
  keyword.
- The "recent" listing pages of cs.CC, cs.DS, cs.SC, math.AG, math.CO,
  math.RT, math.NA, math.RA, cs.IT and quant-ph. They run through the
  announcements of Friday 16 October 2026. Papers submitted after about
  11:30 UTC on 16 October will be announced on 19 October and were not
  visible.
- Web search for 9/4 constructions and seed sizes, the Zenodo full-text
  search, and the GitHub repositories that the search found.

The [script](../experiments/shifted_chains_check_literature.py) runs with
`python -B -m experiments.shifted_chains_check_literature` or
`python -I experiments/shifted_chains_check_literature.py` in about two
seconds. It uses only integers and `Fraction`. It checks the identifications
in Section 2 on small cases:

- 90 parameter sets for the kernel and block structure;
- the identification for shift 1;
- the overlap-add endpoint;
- the reset against OpenAI's Lemma 4.2;
- 18,480 instances of the concavity implication;
- the ramp-product identity for `R <= 300`.

The proofs in Section 2 cover all parameters. The script guards against
slips in indexing.

## 2. Task (a): is the shifted-chain map known?

Notation follows v5: `C(r,b)` is the convolution tensor, `B_X(d)` is the dot
product with a one-dimensional first leg, and `V_n` is the space of binary
forms in `u,v` with `n` coefficients. Write `c = b - h` and
`B = b + (d-1)h`.

### 2.1 The kernel decomposition (proved here)

**Statement L1.** Let `d >= 2` and `1 <= h <= b-1`. The map
`Q(F_0,...,F_{d-1}) = sum_j z^{jh} F_j` on `d` polynomials of length `b`
has the following properties.

1. It is onto the polynomials of length `B`.
2. Its kernel has the basis `kappa_{j,k} = (-z^h z^k)` in component `j`
   plus `(z^k)` in component `j+1`, for `0 <= j <= d-2` and `0 <= k < c`.
3. The lifts "first component containing exponent `i`", together with the
   vectors `kappa_{j,k}`, form a basis of determinant ±1.
4. Multiplication by a fixed polynomial `P` of length `r` is block lower
   triangular in these bases on the input and output sides. Its diagonal
   blocks are `C(r,B)` and `d-1` copies of `C(r,c)` sharing the first leg.
   The only off-diagonal block maps the quotient part of the input to the
   kernel part of the output.

*Proof.*

1. Because `h <= b`, the blocks `[jh, jh+b)` cover `[0,B)`, so `Q` is onto.
2. Each `kappa_{j,k}` lies in the kernel. Their number is
   `(d-1)c = db - B`, which equals the dimension of the kernel. They are
   independent: component `d-1` determines the coefficients with
   `j = d-2`, and peeling off one component at a time determines the rest.
3. Each lift is a standard basis vector of `K^{db}`. Each lift is unchanged
   on the components it uses, and each `kappa` is a ±1 combination of
   standard basis vectors. The script checks unimodularity with exact
   determinants on 90 cases.
4. `Q` is `K[z]`-linear, so `P * kappa_{j,k}(K) = kappa_{j,k}(PK)`. The
   output vector `Q(PF) = P Q(F)` gives the quotient block. ∎

The script checks the block structure exactly for `r <= 3`, `b <= 5`,
`d <= 4` and every `h < b`. It also checks that the quotient-to-kernel
block is nonzero exactly when `r >= 2`. This agrees with the round-8 claims
for these maps. Their finite counts are not checked here.

### 2.2 Shift one is the first step of the determinant filtration (proved here; sources read)

**Statement L2.** Identify component `j` with `v'^j u'^{d-1-j}`, so that the
input space is `V_b ⊗ V'_d`, and dehomogenize with `u = 1`, `v = z`. Put
`Delta = u v' - v u'`. Then the following hold.

1. For `h = 1`, `Q` is the substitution `(u',v') = (u,v)`.
2. For `h = 1`, `kappa_{j,k} = Delta * (u^{c-1-k} v^k ⊗ u'^{d-2-j} v'^j)`.
3. For `h = 1`, `ker Q = Delta (V_{b-1} ⊗ V'_{d-1})`. This is exactly
   v5's filtration step `F^1(V_b ⊗ V'_{h'+1})` with `h' = d-1`, from v5
   Section 4.1 (`maps.tex`, display before Lemma 4.1).
4. For `d = 2` and `h = 1`, `Q(F,G) = F + zG` is the map in the proof of
   OpenAI's Lemma 4.1 (p. 7). There, `D = uw - vs` and the substitution
   `(s,w) = (u,v)` gives the exact sequence
   `0 -> D V_{e-1} -> V_e ⊗ W_1 -> V_{e+1} -> 0`.

*Proof.* Expand `Delta * (g ⊗ m')` with `m' = u'^{d-2-j} v'^j`. The term
`u v' g m'` puts `u g`, that is `g(z)`, in component `j+1`. The term
`-v u' g m'` puts `-z g(z)` in component `j`. Both spaces have dimension
`(b-1)(d-1)`, so they are equal. The script checks the rank equality for
`b <= 6` and `d <= 5`. ∎

**Sources.**

- OpenAI, Lemma 4.1 (p. 7), for `d = 2`. Filmus restates the same
  degeneration in his Proposition 3.1(1), and Uznański in his Lemma 2.1(2)
  and Appendix A.
- Maakestad, Lemma 2.5 (p. 7), for general `d`, as an exact sequence of
  modules. It gives `0 -> S^{n-1}(V) ⊗ S^{m-1}(V) -> S^n(V) ⊗ S^m(V) -> S^{n+m}(V) -> 0`
  over every commutative ring, with the first map given by
  multiplication by `e_1 ⊗ e_2 - e_2 ⊗ e_1`. Its proof writes kernel
  elements as sums of adjacent differences. Maakestad does not consider
  multiplication by a third polynomial or tensors.
- v5, Section 4.1 and Lemma 4.1. v5 already cites Maakestad there.

**What differs.** v5's split of width `h'` refines `F^1` further, into the
children `C(r, b+h'-2j)` for `j >= 1`. The shifted chain stops after one
step and keeps `F^1 ≅ V_{b-1} ⊗ V'_{d-1}` whole. Multiplication by `P` acts
only on `V_{b-1}`, so this step gives the tensor `C(r,b-1) ⊗ B_X(d-1)`,
which is `d-1` copies of `C(r,b-1)` sharing the first leg. For shift 1 the
new map is therefore a coarsening of a known filtration, not a new map. The
round-8 note says the new map "is not that earlier map with its auxiliary
ledger edited". That is correct for `h >= 2` and as a statement about the
auxiliary cost. Still, the follow-up should state the shift-1
identification.

### 2.3 General shift is the substituted sequence (proved here; no source found)

**Statement L3.** For `1 <= h < b`, `Q` is the substitution
`(u',v') = (u^h, v^h)`. Its kernel is `Delta_h (V_{b-h} ⊗ V'_{d-1})` with
`Delta_h = u^h v' - v^h u'`, and the vectors `kappa_{j,k}` are exactly
`Delta_h` times monomials.

*Proof.* The proof is the expansion in Section 2.2 with `u, v` replaced by
`u^h, v^h` in `Delta`. The script checks the coefficients for every case of
Section 2.1. Unlike the case `h = 1`, this is not a `GL_2`-equivariant
statement. The proof uses only `K[z]`-linearity. ∎

I found no source that states the case `h >= 2` as a tensor relation. The
screened sources are OpenAI, Filmus, Uznański (including the replication
lemma `C(mr,ms) ⊵ m C(r,s)`, his Lemma 2.2, which is a different
relation), Lü, Maakestad, OAI26Comp and every arXiv paper of Section 1.
As linear algebra the decomposition is elementary: the syzygy module of
`(1, z^h, ..., z^{(d-1)h})` over `K[z]` is free with the adjacent relations
as a basis. I did not look for a textbook that states it. The follow-up
should present it as an elementary generalization and should not claim it
as a discovery.

### 2.4 The endpoint `h = b` is sectioned convolution (proved here)

**Statement L4.** For `h = b`, `Q` is bijective on inputs, and the output
map adds overlapping blocks. Hence `C(r, db)` is a restriction of
`C(r,b) ⊗ B_X(d)`. The script checks this for `r <= 3`, `b <= 4`,
`d <= 4`.

This is the tensor form of the "overlap-add" or sectioned convolution
method of signal processing, which is usually credited to Stockham (1966).
I checked only the metadata of Stockham's paper; the attribution comes from
secondary sources. The splitting of integers and polynomials into
nonoverlapping pieces, as in Karatsuba, Toom–Cook and Schönhage–Strassen,
has the same input structure. That statement is from general knowledge and
was not checked against sources. None of these methods uses overlapping
input blocks or the kernel sectors that the shifted chain keeps.
Toom–Cook evaluation and interpolation supplies only the source rank bound
`R(C(r,b)) <= r+b-1`, which is v5's (2.4).

### 2.5 The reset is OpenAI's "shifted tripling" (sources read; checked)

**Statement L5.** The reset of the round-8 note restricts the quotient to
`C(r, 3c+r-1)` and splits it into two copies of `C(r,c)` and one copy of
`C(r,c)^{(23)}` with the first index reversed. This reset is the
construction in the proof of OpenAI's Lemma 4.2 (p. 8) with `(a, h) = (r, c)`.
That lemma gives `P(a, 3h+a-1) >= 3P(a,h)` for all `a, h >= 1`. It uses the
`Y` intervals `[0,h-1]`, `[h,2h+a-2]`, `[2h+a-1,3h+a-2]` and matching `Z`
intervals, and removes the middle-to-outer terms by weights. Uznański's
Lemma 2.1(3) and Appendix B state the same degeneration. The script checks
the partition, the weights and the three identifications for `a, h <= 5`.

v5 does not cover this case. Its Lemma 4.5 is the type-restriction version
only for `C(r, 4r-1)`, that is `c = r`. Its introduction says that "the
tensor maps supply only the case `b = r`". That sentence describes v5's own
maps; OpenAI's Lemma 4.2 supplies the map for every column. The follow-up
must cite OpenAI's Lemma 4.2 for the reset. It must also state the
type-restriction form for general `c`, which takes v5's proof of Lemma 4.5
with OpenAI's general intervals.

The same applies to the type restriction itself. v5's Lemma 4.3 is stated
for determinant bases in which different labels have different weights. The
shifted chain gives the same weight 2 to its `d-1` kernel labels and weight
1 to its two outer labels. It also uses only the absence of coefficients
between different labels of one class. The follow-up needs this class
version. Its proof is v5's proof plus that observation.

### 2.6 The scalar content is implied by the profile axioms (proved here)

**Statement L6.** Let `P` be discretely concave in its second argument,
with `c = b - h` and `B = b + (d-1)h`. Then
`d P(r,b) >= P(r,B) + (d-1) P(r,c)`.

If `P` is also a profile (v5 Definition 3.1) and `B >= 3c + r - 1`, then
`P(r,b) >= ((d+2)/d) P(r,c)`.

*Proof.* Concavity makes the average slope on `[c,b]`, of length `h`, at
least the average slope on `[b,B]`, of length `(d-1)h`. This gives
`(d-1)(P(b) - P(c)) >= P(B) - P(b)`. A positive concave function on the
positive integers is nondecreasing. Then `P(B) >= P(r, 3c+r-1) >= 3P(r,c)`
by the tripling axiom. ∎

The script checks the first inequality on 18,480 instances, which cover
every concave integer sequence of length 7 with increments in `[-3,3]`.

**Consequence.** v5's least profile `F` satisfies every scalar inequality
that a shifted-chain stage yields. Any argument that passes the stages
through a scalar value therefore gives at best `3 log(2a-1) / log F(a,a)`
for the source `C(a,a)`. That is v5's profile exponent `tau_a > 9/4`. For a
general source `C(r_0,b_0)`, v5's bound `F(m,n) <= (m+n-1)^{4/3}` keeps the
result at or above `9/4`. Examples of such arguments are worth, tensor
value, characters, or Filmus's criterion.

This is v5's Remark 3.3 and Filmus's Section 4.3 ("Tightness") applied to
the new relations. The follow-up should cite them for the scalar barrier.
Round 14 claims more: a 9/4 limit even with arbitrary compression of the
per-stage auxiliaries, which is a statement about finite resources. That
claim is not checked here.

### 2.7 The arity ramp follows OpenAI's diagonal growth (proved here; checked)

**Statement L7.** The ideal gain of the round-11 ramp,
`F_R = prod_{j=1}^{R-1} (3j+1)(3j+2) / ((3j-1)(3j))`, equals v5's
`F(R,R) = s_R (3R-1)/2` with `s_R = prod_{m<R} (1 + 1/(3m))`. Moreover,
`F(R,R) >= R^{4/3}`.

*Proof.* The factors `(3j+2)/(3j-1)` telescope to `(3R-1)/2`. The factors
`(3j+1)/(3j)` give `s_R`. The lower bound is the last step of OpenAI's proof
of Lemma 5.1 (p. 9): `(1 + 1/(3m))^3 >= 1 + 1/m` and `(3R-1)/2 >= R`. ∎

The script checks the identity and the inequality exactly for `R <= 300`.
The two ramp levels at diagonal `j` multiply the gain by
`F(j+1,j+1) / F(j,j)`. That is the factor of OpenAI's recursion (5.2), so
the ramp makes OpenAI's diagonal-growth estimate tight. Round 11 proves
`F_R >= R^{4/3}` again by a polynomial-positivity certificate. The
follow-up can cite OpenAI's Lemma 5.1 and v5's Theorem 3.2 instead.

### 2.8 Relation to Filmus's criterion (proved here by matching definitions)

Each shifted-chain stage has the form of a "shared-leg block identity" in
Filmus's Theorem 1.1, `A_{sigma(e)} ⊗ D_e ⊵ sum_i T_{e,i}`, with:

- the source `A = C(r,b)` and the auxiliary `D_e = <1,1,d>`;
- blocks independent on the second and third legs;
- each block degenerating to `C(r,c)` or to its transpose `C(r,c)^{(23)}`.

Filmus notes this generality in his Section 2.4: "more general initial
overlap patterns can be treated once an appropriate sector extraction is
supplied".

His criterion would therefore turn a nonnegative certificate on the
shifted-chain labels into an exponent bound. By Section 2.6, that bound is
no better than `tau_a`. His paper gives no finite sizes; its Appendix B.3
says it does "not reproduce these source-size estimates". The follow-up
should say that the asymptotic exponent of shifted chains also follows from
Filmus's criterion, and that its contribution is the finite construction
and its resource bounds.

### 2.9 OAI26Comp is not a shifted-chain construction (sources read)

OAI26Comp, "Complex Matrix Multiplication Below 2.258 and Rectangular
Bounds" (dated 24 September 2026), works with the six-term
Coppersmith–Winograd tensor, which has border rank 3. Its main tool is
Lemma 3.3 ("Pairwise label separation"). For `K` labels readable on two
sides, `U ⊗ A_G ⊵ ⊕_s U_s ⊗ <1,m,1>`, where `A_G` is the multiplication
tensor of a finite abelian group with `log|G| = log K + O(sqrt(log K))` and
`m = K`, built from Behrend-type tags. On top of this it uses:

- completions and conditional label trees;
- a comparison argument of viscosity-solution type;
- an exact numerical certificate.

Its elementary bound is `omega <= 9 log 3 / log 75 < 2.290108`
(Theorem 3.7). Its sources contain no convolution tensors, no polynomial
maps and no shifted or overlapping decompositions; a search for
"convolution", "shifted" and "overlap" in all its `.tex` files finds only
unrelated uses.

It shares three general themes with the shifted chain:

- an auxiliary tensor that separates a shared leg and supplies dot-product
  factors, which become matrix factors over the three orientations;
- fixed-type multinomial counting;
- charging the full rank of the auxiliary.

Its separator costs `|G|/K = exp(O(sqrt(log K)))` per sector. That factor
grows with `K`, whereas Lü's separator costs fewer than 2 copies per
sector, so it would not help the shifted chain. OAI26Comp also proves an
exponent above 9/4. The follow-up can cite it as related work on auxiliary
separation and nothing more.

### 2.10 Other works screened

- **OAI26 and OAI26Stag:** no shifted maps. OAI26Stag proves
  `omega < 2.371054886006746` over every field.
- **Lü:** proves a separator with `M+n-1` copies, which is `2M-1` copies for
  `n = M`, and checks the characteristic-independence of OpenAI's other
  steps. No new convolution relations.
- **Uznański v2:** gives the splits of width one, the general tripling
  (Lemma 2.1(3)), replication (Lemma 2.2) and a separator with `2M` copies,
  and proves rectangular bounds. No shifted chains and no sizes.
- **Filmus:** gives the general criterion, the neighbor and `C(r,4r-1)`
  identities (Proposition 3.1), the explicit certificate and tightness. No
  sizes.
- **Navot (two Zenodo records) and Zuiddam (GitHub):** Lean formalizations
  of the bound over every field and every associative unital ring. No new
  relations and no sizes. Navot's ring record says it claims no "efficient
  uniform circuit generator".
- **Laser-method papers (AD25, Dup26, Zad26):** Coppersmith–Winograd
  framework, unrelated.
- **Other October 2026 arXiv papers:** among them the rank of 3×3
  multiplication over `F_2`, flattening barriers, min-plus and APSP results,
  and a "carrier compression" paper on integer multiplication. None is
  related.
- **Zenodo 10.5281/zenodo.23440229 (Winston, "The Profile Calculus", 17
  October 2026):** a reconstruction and audit of OAI26. It lists "the
  missing finite-size certificate" as an open problem and gives no sizes.
  Not worth citing.
- **GitHub projects `jackal092927/matrix-mult-exponent` (created 13
  October) and `nickedfrc/matrix-multiplication-paper-reproduction`
  (9 October):** no seeds and no shifted chains. Not citable.
- **arXiv 2610.13971 (Z.-W. Sun, math.GM, submitted 14 September 2026):**
  claims `R(M_{2^n}) <= 2^{2n+1}` and hence `omega = 2`. This is an
  extraordinary, uncorroborated claim that I did not check. The follow-up
  should not cite it.

### 2.11 Conclusion for (a)

| Component | Status | Credit |
| --- | --- | --- |
| `F + zG` (`d = 2`, `h = 1`) | known | OAI26 Lemma 4.1; v5 Lemma 4.3 with `h = 1`; Fil26 Prop. 3.1(1); Uzn26 Lemma 2.1(2) |
| shift 1, `d` components, kernel `F^1` | known as linear algebra; its use as `d-1` sectors sharing the first leg is not found | Maakestad Lemma 2.5; v5 Section 4.1 |
| shift `h >= 2`, `d >= 2` | not found; elementary | present as an elementary generalization |
| `h = b` endpoint | classical | overlap-add (Stockham 1966; attribution not checked) |
| reset `C(r,3c+r-1) -> 3` sectors | known | OAI26 Lemma 4.2; Uzn26 Lemma 2.1(3) |
| type restriction | known pattern | v5 Lemma 4.3, with the class version stated anew |
| separator | known | Lü Proposition 2.1; v5 Remark 4.7 and Section 9.1 |
| scalar 9/4 barrier | follows from known results | v5 Remark 3.3; Fil26 Section 4.3 |
| exponent via a general criterion | follows from known results | Fil26 Theorem 1.1 |
| acyclic schedule without a catalyst, arity ramp, finite counts, `log A` polynomial in `1/eps` | not found anywhere | the follow-up's contribution, subject to the other checks |

## 3. Task (b): explicit seed sizes near 9/4

| Work | What it says about sizes |
| --- | --- |
| OAI26 | Existence only. Remark 5.2 (p. 9): the coefficients can be algebraic, so exhaustive search terminates. No size is given. |
| Nav26b | Exponent bound for exact integer-coefficient rank, so search terminates. No size; "no ... efficient uniform circuit generator ... is claimed". |
| Nav26a, Zui26, Lü, Uzn26 | Existence only. |
| Fil26 | Existence only, with a cost constant. Appendix B.3: does "not reproduce these source-size estimates"; "neither argument supplies a single finite seed of exponent exactly 9/4". |
| OAI26Comp | A fixed finite construction is chosen before the asymptotic sum inequality is applied; no sizes. Its exponent is 2.258, not near 9/4. |
| v5 | Explicit sizes. Theorem 1.2: `log A <= 181 a^5 l_a^2` with `a = 2^l` and `l >= 1800/eps`, which is doubly exponential in `1/eps`. Theorem 9.2 gives the seed side by a formula. Corollary 11.2 shows that `exp(exp(Theta(1/eps)))` is necessary within v5's construction. |
| Winston (Zenodo), GitHub projects | No sizes; the Zenodo record lists the gap as open. |

For context on realistic sizes: the best exponent known with a base case
below 1000 is 2.773203 (Schwartz–Zwecher, ISSAC 2026). Pan's 2018 survey
says that every known algorithm with exponent below 2.7733 helps only at
infeasible sizes.

**Conclusion.** In the sources screened, v5 is the only work with explicit
seed or source sizes near 9/4, and they are doubly exponential. A bound with
`log A` polynomial in `1/eps` would be the first singly exponential bound
in `1/eps` for exponents near 9/4. This conclusion depends on the other
topic checks confirming the bound itself. It comes from a bounded screen,
not an exhaustive one, so the follow-up should write "to our knowledge".

## 4. Task (c): the draft bibliography

[`docs/shifted-chains-references-draft.bib`](shifted-chains-references-draft.bib)
has 38 entries, grouped by role. Of these, 29 reuse v5 entries with the same
keys: OAI26, OAI26Stag, OAI26Comp, OAI26Lean, Lu26, Fil26, Nav26a, Nav26b,
Zui26, Uzn26, AD25, Dup26, Zad26, AW21, Str69, Bini80, Sch81, Str86, Str87,
Str88, CW90, LG14, CVZ, CVZ21, Maakestad23, Lean4, Mathlib, DDHK07 and BL80.
Two more reuse existing keys: BCS97 comes from Fil26's bibliography, and
Robbins55 comes from v5's obstruction appendix, which `main.tex` does not
include and whose citation `references.bib` lacks. The new entries are:

- `FinCon26` and `FinCon26pub`: v5 itself; see Section 5.
- `Kow14` (optional): OpenAI's source for the determinant sequence. Not read
  here.
- `Sto66` (optional): overlap-add.
- `Pan18` and `SZ26` (optional): context for realistic sizes.
- `WZ26` (optional): background on asymptotic spectra.

Changes to reused entries:

- `OAI26`: the note now records that commit `1581d4c` was still the latest
  on 18 October 2026.
- `Dup26`: an arXiv DOI was added.

Everything else is copied from v5.

How the metadata was verified:

- **arXiv entries:** titles, authors, version dates and categories from the
  arXiv API and abstract pages. DataCite DOIs exist for all of them.
- **DOIs:** resolved through Crossref.
- **Zenodo records:** read through the Zenodo API.
- **GitHub entries:** pinned commits and their dates from the GitHub API.

The file compiles with `natbib` and `plainnat` without BibTeX warnings. The
test document lacked `amssymb`, which the `OAI26Lean` note needs.

Keys to cite for the shared components, with v5 numbering:

- convolution tensors and rank: (2.3) and (2.4);
- exactification: Lemma 2.2;
- relative schemes: Definition 2.3;
- pooled recursion: Lemma 2.4;
- profile: Definition 3.1, Theorem 3.2 and Remark 3.3;
- determinant basis: Lemma 4.1;
- type restriction: Lemma 4.3;
- tripling for `c = r`: Lemma 4.5;
- separator: Proposition 4.6 and Remark 4.7 (Lü);
- oriented relations: Corollary 4.8;
- descent and seeds: Lemma 8.6 and Corollary 8.7;
- rational variant: Section 9.1 and Lemma 9.1;
- bounded seed: Theorem 9.2;
- source-size limits: Proposition 11.1 and Corollary 11.2;
- open question 2: Section 11.5.

These numbers belong to version 5. A later revision may renumber them, so
the follow-up should name the version.

## 5. Task (d): citing v5

Facts:

- v5 has an empty `\author{}` and `\date{}`. Its sources contain no URL of
  its own and no name (checked with grep).
- The paper is public in the repository
  `github.com/SECQUOIA/finite-extraction-matrix-multiplication`. Its README
  calls it "an AI-produced research paper", and its commit history shows the
  committer's name.
- Versions and UTC commit times:
  - v1, `40b19a75`, 7 October 05:36;
  - v2, `71e92d89`, 7 October 20:01;
  - v3, `d3914835`, 17 October 21:00;
  - v4, `75e7663e`, 18 October 00:03;
  - v5, `6562ac60`, 18 October 19:51.
- Versions 1–2 have the title "Explicit finite extraction from convolution
  profiles for matrix multiplication". Versions 3–5 have the title "A finite
  construction of matrix multiplication algorithms with exponent approaching
  9/4".
- Filmus's manuscript cites version 2 as `@misc{Extraction, key={SECQUOIA},
  ..., url={https://github.com/SECQUOIA/finite-extraction-matrix-multiplication}, note={... revision 71e92d89 ... No author byline is given}}`.
  The repository is therefore already publicly linked to the paper.

Proposal:

- **Entry.** Use `FinCon26` with `author = {{Anonymous}}`, the v5 title,
  "version 5, 18 October 2026, 79 pages", and the earlier title. The earlier
  title lets readers match Filmus's citation. A `key` field is not used,
  because `plainnat` prints it in place of the author. In the text, cite it
  with `\citep`, because `\citet` prints "Anonymous". Write in the third
  person, for example "the construction of [n]".
- **If the follow-up need not be anonymous,** use `FinCon26pub`, which adds
  the pinned URL `.../tree/6562ac60...`. Without a URL, readers can find v5
  only by searching for the title or through Filmus's bibliography.
- **For double-blind review,** keep `FinCon26` and supply the v5 PDF as
  anonymous supplementary material.
- **Either way, cite version 5 by number,** because the theorem numbers in
  Section 4 refer to it.

## 6. Task (e): dates for time-sensitive claims

All times are UTC.

| Item | Date | Evidence |
| --- | --- | --- |
| OAI26 | dated 2 Oct 2026; public 6 Oct 2026 21:58 (`openai/math` initial commit `adc7f12`) | title page; GitHub API; the path history has only this commit |
| OAI26Stag and OAI26Comp | dated 24 Sep 2026; public 6 Oct 2026 (same commit) | title pages; GitHub API |
| `openai/math` later commits | 8 Oct 2026 05:03 (`3014888`, 297 Lean files); 12 Oct 2026 21:55 (`1581d4c`, latest); no preprint changed | GitHub API |
| Zad26 | arXiv v1 6 Oct 2026 18:36 | arXiv |
| v5, version 1 (with the `2M-1` separator) | 7 Oct 2026 05:36 | public commit `40b19a75`; v1 `maps.tex` line 122 |
| Zui26 | 7 Oct 2026 07:40 (commit `615b591`) | GitHub API |
| Nav26a | Zenodo v1.0.0, 7 Oct 2026 (record created 17:03) | Zenodo API |
| Uzn26 | v1 7 Oct 2026 17:46 ("...from shared-leg entropy"); v2 11 Oct 2026 13:47 (title page dated 9 Oct 2026) | arXiv |
| Nav26b | Zenodo v0.1.0, 9 Oct 2026 (record created 23:17) | Zenodo API |
| Lü | arXiv v1 12 Oct 2026 13:34; no later version | arXiv |
| Fil26 | commits 17 Oct 2026 03:27–04:14; `8e38460c` at 04:14; `CITATION.cff` date-released 2026-10-17; no later commit as of 18 Oct | GitHub API; vendored copy |
| v5 | public commit `6562ac60`, 18 Oct 2026 19:51; the README dates version 5 to 18 October 2026 | GitHub API |
| Round-8 shifted-chain note | dated 2026-10-18 | `docs/round8-multiscale-construction.md` |
| Dup26 | arXiv v1 17 Aug 2026 17:59 | arXiv |
| arXiv screen | announcements through Fri 16 Oct 2026 | listing pages |

For priority statements, use the public release dates, not the dates printed
on title pages. OAI26 is dated 2 October but became public on 6 October.
v5 version 1 used `2M-1` separator copies on 7 October, before Lü's arXiv
submission on 12 October. That is consistent with v5's statement that Lü
obtained the count independently.

## 7. Problems found and fixes

1. **The round-8 note gives no credit for shift 1 (major, attribution).** It
   presents the shifted map as different from the determinant construction
   without noting the following:
   - for `d = 2` and `h = 1` it is OpenAI's Lemma 4.1;
   - for `h = 1` its kernel is the first filtration step `F^1` (Maakestad
     Lemma 2.5; v5 Section 4.1).

   *Fix:* state Statements L2 and L3. Claim novelty only for using the
   coarse filtration as `d-1` equal sectors, for the substituted shift
   `h >= 2`, and for what is built on these.
2. **The reset is not credited (major, attribution).** The round-8 note
   does not cite OpenAI's Lemma 4.2, which already proves the general-column
   map (also Uznański's Lemma 2.1(3)). v5 proves the type-restriction version
   only for `c = r`. *Fix:* cite OpenAI's Lemma 4.2. State and prove the
   general-`c` type restriction, adapting v5's proof of Lemma 4.5.
3. **v5's type restriction does not apply verbatim (minor).** v5's
   Lemma 4.3 assumes determinant bases with one weight per label. The
   shifted chain needs weights per class. *Fix:* state the class version.
   The proof is unchanged, plus the vanishing of coefficients between
   different labels of one class.
4. **One v5 sentence is misleading (minor).** "The tensor maps supply only
   the case `b = r`" in v5's introduction refers to v5's maps; OpenAI's
   tensor map covers every column. *Fix:* the follow-up should not repeat
   the sentence.
5. **The round-11 positivity proof is redundant (minor).** Its proof of
   `F_R >= R^{4/3}` is correct but unnecessary. *Fix:* cite OpenAI's
   Lemma 5.1 and v5's Theorem 3.2, together with the identity of
   Statement L7.
6. **The scalar 9/4 barrier is not new (minor).** It follows from v5's
   Remark 3.3 and Filmus's Section 4.3 through Statement L6. *Fix:* cite
   them. Present round 14's compression result separately, as a statement
   about finite resources.
7. **Anonymity (minor).** v5's anonymity does not survive a search, because
   Filmus cites the public repository. *Fix:* choose an entry from Section 5
   deliberately.
8. **Unchecked attributions (minor).** The overlap-add credit to Stockham
   and the Kowalski locator are not checked against the originals. *Fix:*
   read them before citing, or drop the optional entries.

I found no error in v5's related-work text. Its dates, titles and
descriptions of OAI26, OAI26Stag, OAI26Comp, Lü, Filmus, Navot, Zuiddam,
Uznański, Zadeh and Dupont et al. match the sources as of 18 October 2026.
v5's `OAI26Stag` note gives `omega < 2.371054887`; the preprint states
`2.371054886006746`, and v5 rounds it up correctly.

## 8. What I could not verify

- **Search completeness:** arXiv submissions after about 11:30 UTC on
  16 October 2026, journals outside arXiv, the signal-processing and
  computer-algebra literature on overlapped block convolution, and
  non-English sources.
- **The original texts of Stockham (1966) and Kowalski (2014).**
- **OAI26Comp's proofs:** I read its introduction, Lemma 3.3 and the
  structure of the paper, not the proofs.
- **Sun's arXiv 2610.13971:** the claim was not checked.
- **The finite counts and the bounds of rounds 8–14:** for example
  `log A = Theta(eps^{-9/2} log^3(1/eps))` and the Hankel theorem of
  round 14. Other topic checks cover them. Section 3's novelty statement
  depends on them.

## Reproduction

```sh
python -B -m experiments.shifted_chains_check_literature
```

The last line of the output is `all checks passed`.

## Adversarial review

Reviewer: adversarial referee for the `literature` topic, 18 October 2026
(web checks near 01:30 UTC on 19 October). Companion script:
[`experiments/shifted_chains_skeptic_literature.py`](../experiments/shifted_chains_skeptic_literature.py).
It was written independently of the checker's script and uses only
integers and `Fraction`. Run it from the repository root with
`python -I experiments/shifted_chains_skeptic_literature.py`; it takes about
two seconds and ends with `all skeptic checks passed`. I also reran the
checker's script, which passes.

### Verdict

The checker's main conclusions hold:

- For shift 1 the map is known (OAI26 Lemma 4.1; Maakestad Lemma 2.5; v5 Section 4.1).
- The reset is OAI26 Lemma 4.2 with `(a,h) = (r,c)`.
- The scalar 9/4 barrier follows from the profile axioms.
- OAI26Comp is unrelated to shifted chains.
- No screened work other than v5 gives explicit sizes near 9/4.

I found no fatal or major error. I found several minor errors: two factual
errors in time-sensitive claims, one wrong equation number, one citation
that does not support the claim made, a proof step that is incomplete as
written, and some wording that attributes the checker's own inferences to
the sources. Each is listed below with a fix.

### What I checked and how

**Sources, read directly:**

- OAI26 `build/paper.tex` and `paper.pdf`. Lemmas 4.1, 4.2 and 5.1,
  equations (4.7), (5.1) and (5.2), and Remark 5.2 are on pp. 7–9, as stated.
- v5 `maps.tex`, `profile.tex` and `introduction.tex`, and the labels in
  `main.aux`.
- Filmus's vendored manuscript: Theorem 1.1, Proposition 3.1, Sections 2.4
  and 4.3, Appendix B.3, and his bibliography entry for v5.
- Uznański v2: Lemma 2.1, Lemma 2.2, and Appendices A and B.
- Maakestad: Lemma 2.5 on p. 7 of arXiv v8.
- Lü: Proposition 2.1, from the arXiv source.
- OAI26Comp: Lemma 3.3, Theorem 3.7 and Section 8, from the sources and PDF
  at `openai/math` commit `1581d4c`.
- OAI26Stag: the introduction and Section 3 ("staggering"), which concerns
  stage schedules for the CW tensor and contains no polynomial maps.
- The OpenAI preprint "Integer multiplication below n log n", which the
  checker did not list. It is unrelated: Fourier and multitape circuits,
  with no convolution-tensor degenerations.

**Metadata, checked independently:**

- arXiv API: Zad26, Uzn26 (both versions, and the v1 title), Lu26, Dup26,
  SZ26, Pan18, and Sun's 2610.13971.
- Crossref: every non-arXiv DOI in the draft bibliography. All 22 resolve,
  with matching titles, authors, volumes and pages.
- Zenodo API: Nav26a, Nav26b and Winston. The quoted phrases are present.
- GitHub API: commit histories of `openai/math`, Filmus, Zuiddam and the v5
  repository, plus the v1 `maps.tex` (line 122: `2M-1` copies) and the v1
  title.
- Every pinned URL in the draft bibliography returns HTTP 200.
- I compiled the draft bibliography with `natbib`/`plainnat` and
  `\nocite{*}`. It produces 38 entries without warnings.

**Search.** arXiv API queries sorted by submission date ("matrix
multiplication", "tensor rank", "border rank", "polynomial multiplication",
and `cat:cs.CC`) show nothing related through the latest visible
submission, 16 October 2026 at 11:31 UTC. This agrees with the checker's
cutoff. A web search found two repositories the checker did not list,
discussed in finding 2.

**Exact checks** (all in the companion script):

1. *Fibers (unimodularity for all parameters).* For every exponent `i`,
   the components containing `i` form a contiguous range `j_min..j_max`.
   The kernel vectors at exponent `i` are exactly
   `kappa_{j, i-(j+1)h}` for `j_min <= j < j_max`. The change of basis is
   therefore block diagonal over fibers. Each block is `e_{j_min}` together
   with adjacent differences, a unitriangular matrix. This proves
   `det = ±1` for all parameters. Checked structurally for `b <= 8`,
   `d <= 6` and all `h < b` (140 cases).
2. *Block structure through the explicit inverse.* I used
   `e_{(j,β)} = lift(i) + Σ_{j'=j_min}^{j-1} kappa_{j', i-(j'+1)h}`, which
   has all coefficients 1, instead of Gaussian elimination. Checked for
   `r <= 4` (560 cases). The only off-diagonal block maps the quotient to
   the kernel, and it is nonzero exactly when `r >= 2`.
3. *Forms.* `kappa_{j,k} = Delta_h · (u^{c-1-k} v^k ⊗ u'^{d-2-j} v'^j)`,
   computed by multiplying forms in four variables, for all 140 cases.
4. *Class-weighted restriction of the whole stage* (split, crop, reset
   with OAI26's intervals and `(a,h) = (r,c)`). Neither v5 nor the checker
   tested this combination. With weights `K = 2`, `L = R = 1` and `M = 0`:
   - every coefficient between different labels strictly increases the
     weight;
   - coefficients between different labels of one class vanish;
   - every diagonal block has `rc` terms.

   This holds for 212 stages (`r <= 3`, `b <= 8`, `d <= 5`,
   `B >= 3c+r-1`). Brute force on tensor squares (5 stages) and cubes
   (2 stages), 50 class types in all, confirms that fixing the class type
   on both legs leaves only matched words. The number of words equals the
   round-8 formula (4), `N!/(n_K! n_O! n_M!) (d-1)^{n_K} 2^{n_O}`. Mutating
   the weights (K=1, or M=1) is detected, so the test is not vacuous.
5. *Uznański v2, Appendix A.* His coordinates `p = a + tb` and
   `h = b - p_{e+1} t^e`, and his multiplication rule
   `(p,h) ↦ (fp, fh + p_s t^{s-1}(f - f_{r-1} t^{r-1}))`, coincide exactly
   with the shifted map's quotient and kernel coordinates for `d = 2` and
   `h = 1`. Checked for `r <= 4` and `s <= 5`. Filmus's substitution
   (3.5) uses the same lifts and kernel vectors. So does OAI26's proof of
   Lemma 4.1: its lifts `u^{e-i}v^i s`, followed by `v^e w`, are the
   "first component" lifts. The credit for `d = 2`, `h = 1` is therefore
   exact, down to the bases.
6. *A direct proof of L6's first inequality.* It is a nonnegative
   combination of second differences:
   `d P(b) - P(B) - (d-1) P(c) = Σ_{t=c+1}^{B-1} λ_t (2P(t) - P(t-1) - P(t+1))`,
   with `λ_t = (d-1)(t-c)` for `t <= b` and `λ_t = B - t` for `t >= b`.
   This identity was checked exactly for `b <= 30`, `d <= 10` and all `h`
   (3,915 cases). It proves the inequality for every concave row, which is
   stronger than the checker's enumeration of sequences.
7. *v5's least profile `F` satisfies every legal round-11 stage
   inequality,* `d F(r,b) >= (d+2) F(r,c)` whenever `(d+2)c <= db - r + 1`.
   Checked for `r <= 10`, `b <= 36`, `d <= 10` (39,623 cases). The check
   includes children with `c < r-1`. Every ramp step of round 11 is tight
   for `F`.
8. *Ramp.* The product equals `F(R,R)` for `R <= 120`. `F` satisfies
   OAI26's (5.1) with equality. The round-11 positivity coefficients are
   exactly `4544, 17936, 27324, 20007, 7074, 972`.
9. `F(m,n)^3 <= (m+n-1)^4` for `m, n <= 60`.

### Findings

1. **Wrong commit description in Section 6 and the summary (minor,
   factual).** The note says commit `3014888` (8 October) changed
   "297 Lean files" and that "no preprint changed". The summary says "Every
   OpenAI preprint is unchanged since its release". In fact the commit
   changed 1,185 files:
   - 762 files under `lean/`;
   - 418 files under `preprints/`: 381 added, 31 removed and 6 modified,
     in the Kuga–Satake, Weil-eightfold and K3-Hodge preprints;
   - `README.md`, `CONTENTS.md`, `history.md` and `overview.tex/pdf`.

   The checker read only the first of the four pages of the GitHub API file
   list. Checking all four pages, I confirmed that no file of the three
   matrix-multiplication preprints, or of the matrix-multiplication Lean
   family, changed after `adc7f12`. The citation conclusion stands.
   *Fix:* restrict the claim to OAI26, OAI26Stag and OAI26Comp.
2. **Out-of-date context claim (minor, factual).** "The best exponent known
   with a base case below 1000 is 2.773203 (Schwartz–Zwecher)" repeats the
   August 2025 abstract of SZ26. The public repository LITA
   (`github.com/khoruzhii/lita`, created June 2026) lists
   `<32,32,32>` with rank 14,196, an exponent of about 2.75864, and says
   explicitly that this improves the 2.77320 of Schwartz and Zwecher.
   `github.com/AntoineTilloy/explicit-matmul-schemes` lists the same rank
   at size 32. Neither is refereed. *Fix:* drop the sentence, or write "SZ26
   reported 2.773203 as the best exponent for base cases below 1000;
   unrefereed 2026 repositories report about 2.7586 at size 32". Neither
   repository gives sizes near 9/4; their best entries are at least 2.649.
   So Statement L10 is unaffected.
3. **Wrong equation numbers in L7, Section 2.7 and L8 (minor).** OAI26's
   diagonal recursion is (5.1), `D_a - D_{a-1} >= H_{a-1} + H_a`, together
   with the unnumbered line that follows it. Equation (5.2) is the iterated
   product bound `H_a >= Π(1 + 1/(3m))`. Each ramp pair realizes (5.1)
   with equality (check 8). *Fix:* cite (5.1). Similarly, L8 cites
   Filmus eq. (1.1) for the form of a block identity. In his PDF, (1.1) is
   `S(<a,b,c>) ≅ M_abc`; the identity system is (1.2).
4. **Filmus Section 4.3 does not cover shifted-chain stages (minor,
   citation).** Filmus's tightness LP (4.5) contains only:
   - neighbor inequalities for `r <= b < 4r-1`;
   - tripling at `b = r`, on rows `2..a`.

   His profile `z*` is shown feasible only for that system, and he writes
   that it "does not rule out a different extraction". Shifted-chain
   stages produce children with `c < r-1`; for example
   `(a,a) -> (c,a)` with `c ≈ (d-1)a/(d+2)`. The barrier for shifted
   chains therefore rests on three things:
   - v5 Theorem 3.2, Step 1 (`F` is a profile on all columns);
   - Statement L6, or checks 6–7;
   - v5 Remark 3.3.

   *Fix:* cite those, and mention Filmus Section 4.3 only as the analogous
   argument for his system.
5. **Unimodularity proof in L1 is incomplete as written (minor).** Item 3
   says the lifts are standard vectors and each kappa is a ±1 combination.
   That does not imply a determinant of ±1, so as written the claim rests
   on 90 computed determinants. *Fix:* use the fiber argument of check 1,
   which is round 8's own argument ("each exponent block is unimodular").
6. **Inferences attributed to sources (minor, wording).** The Section 3
   table says that OAI26 Remark 5.2 implies "exhaustive search
   terminates", and similarly for Nav26b. Remark 5.2 says only that
   algebraic coefficients suffice, by the Nullstellensatz. Navot's record
   says only that no "efficient uniform circuit generator" is claimed.
   That a search terminates is the checker's inference. It is true by
   decidability, but the sources do not state it. *Fix:* reword.
7. **Sun's claim misstated (minor).** arXiv 2610.13971 claims a
   *border-rank* bound, `R_underline(M_{2^n}) <= 2^{2n+1}` for `n >= 5`,
   not a rank bound. The advice not to cite it stands.
8. **Internal inconsistency about v5 (minor).** Issue 4 calls v5's sentence
   "the tensor maps supply only the case `b = r`" misleading, while
   Section 7 finds no error in v5's related-work text. v5 Section 3, after
   Theorem 3.2, already says "tripling proved there at every column
   `b >= 1` [OAI26, Lemma 4.2]; our tensor maps realize only `b = r`", and
   the introduction repeats the credit (Section 1.4). In context the
   sentence is accurate. *Fix:* downgrade issue 4 to a style note for the
   follow-up.
9. **Status labels (minor).** L9 and L10 are marked
   "checked-small-cases", but they are a reading of sources and a bounded
   screen. L1 item 3 is "checked numerically" unless the fiber proof is
   added.
10. **L2 range (minor).** v5 defines `F^1(V_c ⊗ V'_{h+1})` only for
    `c >= h+1`, that is, `b >= d`. For `b < d` the identification is with
    Maakestad's Lemma 2.5, which has no such restriction, not with v5's
    `F^1`. Also, L2(4) quotes OAI26's degree-indexed `V_e`, while the rest
    of L2 uses v5's dimension-indexed `V_n`. The follow-up should state one
    convention.
11. **Anonymity proposal partly defeats itself (minor).** The anonymous
    entry `FinCon26` tells readers that Filmus cites version 2 under the old
    title. Filmus's entry carries the repository URL and the key
    `SECQUOIA`, so the pointer undoes the omission of the URL. Moreover, a
    plain web search for the v5 topic and title returns the public
    repository as the first hit; I tried this. *Fix:* either use
    `FinCon26pub`, or, for double-blind review, drop the Filmus pointer and
    accept that v5 is discoverable. Citing it in the third person remains
    standard practice either way.
12. **"Would not help the shifted chain" is unproven (minor).**
    OAI26Comp's Lemma 3.3 is a *zeroing-out*. It needs no degeneration,
    hence no interpolation charge, which is the one feature that could
    matter for finite sizes. Its per-sector cost `|G|/K = exp(O(sqrt log K))`
    is paid in every copy of the `k`-th power. Round 8's exactification
    charge `1+6k(M-1)` is only polynomial in `k`. So the group separator is
    plausibly worse, but this is a quantitative judgment that was not
    checked. *Fix:* write "more expensive per sector; no evident benefit".
13. **One unscreened area for `h >= 2` (minor, screen gap).** In
    characteristic `p` with `h = p^e`, `Delta_h = u^h v' - v^h u'` is
    `SL_2`-invariant when `(u',v')` carries the Frobenius-twisted action.
    The substituted sequence is then the Frobenius twist of the
    Clebsch–Gordan sequence. So "not `GL_2`-equivariant" holds only in
    characteristic zero, or for `h` that is not a power of `p`. The modular
    representation theory of `SL_2` (symmetric powers in positive
    characteristic, Steinberg tensor products) and the literature on
    Kronecker substitution and segmentation in computer algebra were not
    screened. *Fix:* keep "to our knowledge" and "elementary" for `h >= 2`,
    as the checker already recommends.
14. **Simplification for the paper (suggestion).** The paper
    recommendation asks for two lemmas: a general-`c` tripling with a type
    restriction, and a class-weighted type restriction. One lemma
    suffices: the class-weighted restriction of the whole stage (check 4).
    It covers the general-`c` reset without a separate tripling lemma.
    Credit the intervals to OAI26 Lemma 4.2 and the method to v5
    Lemmas 4.3 and 4.5. Round 8 already sketches its proof: positionwise
    nondecreasing weights with equal sums are equal positionwise, and
    labels within a class cannot change.

### Statements I endorse

- **L1**, with `1 <= h <= b-1` and `d >= 2`, as stated. Use the fiber proof
  for unimodularity. The off-diagonal block is nonzero if and only if
  `r >= 2`.
- **L2.** For `h = 1`, `ker Q = Delta (V_{b-1} ⊗ V'_{d-1})`. This is
  v5's `F^1` when `b >= d`, and Maakestad's Lemma 2.5 for all `b, d`. For
  `d = 2` the bases coincide exactly with those of OAI26's proof of
  Lemma 4.1, Filmus's Proposition 3.1(1) and Uznański's Appendix A.
- **L3** as stated, with "not `GL_2`-equivariant" restricted to
  characteristic zero, or to `h` not a power of `p`. The novelty of
  `h >= 2` holds to our knowledge only and is elementary.
- **L4** as stated. The attribution to Stockham is unchecked.
- **L5** as stated: the interval partition, the weights and the middle
  branch match OAI26 p. 8 and Uznański's Appendix B exactly.
- **The class-weighted stage restriction (new, from check 4).** For
  `B >= 3c + r - 1`, fix the class counts `(n_K, n_O, n_M)` on legs 2
  and 3 of the `N`-th power of the cropped stage, in adapted bases. This
  is a restriction to
  `N!/(n_K! n_O! n_M!) · (d-1)^{n_K} · 2^{n_O}` sectors sharing the first
  leg. Each sector has `N - n_M` factors `C(r,c)` and `n_M` factors
  `C(r,c)^{(23)}`, the latter with the first index reversed.
- **L6.** The first inequality is proved by the tent identity of check 6.
  The second follows from monotonicity of positive concave rows and the
  tripling axiom. The barrier consequence is to be cited to v5 Theorem 3.2
  and Remark 3.3 (finding 4).
- **L7**, citing OAI26 (5.1), not (5.2).
- **L8** as stated. Each stage is a single-copy degeneration of Filmus's
  form (1.2), using weights by powers of `t` on legs 2 and 3; his
  criterion needs a terminal with `d >= 2`, for example `C(1,2)`.
- **L9.** Corrected per finding 12.
- **L10** as stated: a bounded screen through arXiv submissions of
  16 October 2026, 11:31 UTC. Later repositories (LITA, Tilloy) give
  explicit schemes only at exponents of at least 2.649.

### What I could not verify

- arXiv submissions after 16 October 2026 at 11:31 UTC.
- Journals outside arXiv, the modular representation theory literature,
  and the computer-algebra literature on Kronecker substitution and
  segmentation.
- The originals of Stockham (1966) and Kowalski (2014). OAI26 and
  Uznański give consistent locators for Kowalski: Section 2.6, and
  Theorem 2.6.3 on pp. 56–57 of the author version.
- The proofs of OAI26Comp.
- The finite counts of rounds 8–14. The novelty claim about `log A`
  depends on the other topic checks.
