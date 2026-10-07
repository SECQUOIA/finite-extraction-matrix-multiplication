# V2 audit of tensor maps and their resource accounting

Date: 7 October 2026.

No blocking error or unresolved mathematical objection was found in the
audited maps, their composition, or their interface with the signed resource
ledger. In particular, the new multiway filtration, partial-middle tripling,
and threefold balancing support the counts used in the revised extraction.

This review used direct mathematical derivations. No experiments or tests
were run, no literature was consulted, and no manuscript files were edited.
Two independent child reviews checked the cyclic orientations and full-space
normalizers, and the signed ledger and extraction counts, respectively.

## Scope and snapshot

The review covers the following files. SHA-256 prefixes identify the
reviewed snapshot:

| File | SHA-256 prefix |
|---|---|
| `manuscript/maps.tex` | `ff0b30bbb37f67bf` |
| `manuscript/appendix-composition.tex` | `fcd30052c2dfe504` |
| `manuscript/preliminaries.tex` | `02bd1d3674a721ea` |
| `manuscript/rounding.tex` | `3ecece927f76c77d` |
| `manuscript/extraction.tex` | `5580490b2e699c29` |

The principal scope is the tensor construction, including boundary cases,
zero counts, target-space maps, dimensions, degrees, and multiplicities.
The row-state definitions in `manuscript/flows.tex` were read to check that
every action satisfies the tensor lemmas' hypotheses. The occupation bounds,
the quantitative parameter theorem, and novelty claims are outside this
review. The signed ledger was checked from its displayed exact row balances;
this report does not replace the separate audit of the occupation and
rounding analysis.

## 1. The determinant basis is an integer basis

Reference: `maps.tex:16–71`.

For a monomial of bidegree \((p,q)\), replacing each occurrence of
\(ut\) by \(vs+\Delta\) expresses it as a sum of a monomial with no
factor \(ut\), plus \(\Delta\) times polynomials of bidegree
\((p-1,q-1)\). The monomials with no factor \(ut\) are exactly the
displayed lifts \(L_{p,q}(i)\): either the auxiliary \(t\)-exponent is
zero, or the \(u\)-exponent is zero. Their diagonal substitutions are
the distinct binary monomials of degree \(p+q\).

Consequently a combination of these lifts divisible by \(\Delta\) must
have every coefficient zero. Reduction therefore gives both spanning and
uniqueness. Repeating it after division by \(\Delta\) proves that
\(B_{j,i}=\Delta^jL_{d-j,h-j}(i)\) is the claimed basis. Both the
basis vectors and the coordinates of monomials in this basis are integral;
no division by a scalar is needed. Equivalently, its matrix relative to
the monomial basis is unimodular. The dimension sum is
\[
 \sum_{j=0}^h(d+h-2j+1)=(d+1)(h+1).
\]

The same argument proves the quotient identification
\(F^j/F^{j+1}\cong V_{d+h-2j}\). The boundary \(j=h\) is valid:
the remaining auxiliary degree is zero and the quotient is an ordinary
binary-form space. The hypothesis \(d\ge h\) ensures all degrees are
nonnegative.

Multiplication by a first-input monomial commutes with \(\Delta\), so
the image of filtration level \(j\) lies in levels at least \(j\).
On its quotient, the index changes from \(i\) to \(i+\alpha\),
with coefficient exactly one. Hence every diagonal block is
\(C(r,b+h-2j)\). These assertions remain valid for \(r=1\) and for
the smallest allowed \(b=h+1\), where the final input length is one.

The instruction to use the dual output basis on the third tensor leg is
essential and correct. It makes the trilinear tensor represent the
structure constants of multiplication in the chosen input and output
bases.

## 2. Fixed types remove every off-diagonal term

Reference: `maps.tex:73–104`.

For a supported tensor-power term, each output filtration index satisfies
\(j'_{\nu}\ge j_{\nu}\). Both retained words have the same fixed
counts \((n_0,\ldots,n_h)\), so
\[
 \sum_\nu(j'_\nu-j_\nu)=0.
\]
Every summand is nonnegative; all are therefore zero. This removes all
off-diagonal blocks exactly, without interpolation or cancellation of
coefficients. The labels agree positionwise and give precisely
\(n!/\prod_jn_j!\) sectors.

The proof does not require positive counts in every class. Classes with
\(n_j=0\) are simply absent, and \(0!=1\) gives the correct count.
If only one class is used, there is one sector. The first space remains
shared until the separator is applied, so the stated postponement of
word-specific first-leg reorderings is necessary and sufficient.

The row construction supplies
\(b=r-1+x\), \(h=\min(x,3r-x)\), and \(r\ge2\). Thus
\(b\ge h+1\), and its child \(y\) has filtration index
\((x+h-y)/2\). Substitution gives
\[
 b+h-2((x+h-y)/2)=r-1+y,
\]
exactly the child column recorded by the ledger. No unsupported slice or
fractional filtration index is introduced.

## 3. Partial-middle tripling is exact

Reference: `maps.tex:108–160`.

The interval endpoints give complete, disjoint partitions of the second
and third index sets. A left second-leg label forces a left third-leg
label, and a right label forces a right label. A mismatched term therefore
has a middle input label and an outer output label. The middle count can
only decrease. Retaining the same middle count \(m\) on both legs
forces every position to match, even though the left and right counts
were not fixed separately.

There are \(\binom nm\) choices of middle positions and
\(2^{n-m}\) choices of their outer complements. Every outer block is
a translated \(C(r,r)\). The middle block has exactly the terms
\[
 x_{r-1-i}y_{r+i+j}z_{2r-1+j},\qquad 0\le i,j<r.
\]
Reversing the first index and translating the interval labels identifies
it with \(C(r,r)^{(23)}\). This is an identification with a tensor
having the appropriate permuted dimensions, not an operation exchanging
two global legs inside a tensor product.

The cases \(m=0\), \(m=n\), and \(n=1\) are valid. The modal
count follows from
\[
 \frac{M_{\mathrm t}(n,m+1)}{M_{\mathrm t}(n,m)}
 =\frac{n-m}{2(m+1)}.
\]
Thus \(\lfloor(n+1)/3\rfloor\) is a maximizer, including the possible
tie. The \(n+1\) counts sum to \(3^n\), proving the stated lower
bound. There is no remaining divisibility-by-three requirement.

## 4. Threefold orientations and independent sector choices

References: `preliminaries.tex:84–106`; `maps.tex:208–246`.

Swapping the two native inputs identifies \(C(r,b)\) with
\(C(b,r)^{(12)}\). This changes the permutation parity and proves
\[
 S^\sigma_{r,b}\cong S^{-\sigma}_{b,r}.
\]
On the diagonal, the native input symmetry gives
\(S^+_{r,r}\cong S^-_{r,r}\). These are coordinate identifications
within each global leg, after the factors are matched by their
permutations. They do not assume that global legs of selected factors can
be exchanged independently. Since either parity coset places the native
first leg in each global position once,
\(S^\sigma_{1,b}\cong\mathsf M_b\), and the rank bound is
\((r+b-1)^3\).

After separation, every partial-middle sector normalizes to the same
mixed tensor
\[
 C(r,r)^{\otimes(n-m)}
 (C(r,r)^{(23)})^{\otimes m}.
\]
The numbers of left and right labels do not affect its dimensions or its
canonical coefficients. Therefore the three orientations may choose
sector words independently. Tensoring their sectors gives
\[
 (S^\sigma_{r,r})^{\otimes(n-m)}
 (S^{-\sigma}_{r,r})^{\otimes m}
 \cong(S^\sigma_{r,r})^{\otimes n}.
\]
The diagonal sign isomorphism is used only after forming this threefold
product. This is the correct replacement for sixfold balancing.

The independent orientation reviewer checked this point separately and
found no mismatch or hidden assumption that the three sector words agree.

## 5. Separator and whole-target composition

References: `maps.tex:167–206`; `appendix-composition.tex`;
`preliminaries.tex:29–48` and `127–145`.

The Fourier phase is \(u-v+c(g-h)\). Its magnitude is at most
\(K_0-1+c(M-1)=L-1\), so Fourier averaging modulo \(L\) imposes
the exact equality. On every surviving monomial the total Laurent
exponent is
\[
 cg^2+2h(u-v)-ch^2=c(g-h)^2\ge0.
\]
This proves that negative powers are absent from the combined tensor,
although some individual substitutions contain them. The constant term
has \(g=h\) and \(u=v\), separating all three legs. The support and
degree bounds follow from \(c|g-h|\le K_0-1\).

The appendix's composed coefficient formula follows by applying this
calculation to the exact type tensor. For a split action, its coefficients
are the displayed products of indicators
\(\gamma_\nu=\alpha_\nu+\beta_\nu\), with exactly the stated
slice-dependent ranges. For tripling, the same indicators are valid when
the original interval coordinates are used, before shifts and reversals.

The normalizer is defined on the entire target spaces:
the first-leg block indexed by \(g\) uses the normalizer of word
\(g\), while the other blocks use their own word \(s\). Thus it is
well defined even on positive-degree monomials with \(g\ne s\).
All retained words have identical canonical leg dimensions. The map is
an actual block-diagonal coordinate permutation, not a rule defined only
on the constant coefficient.

After tensoring three orientations, every global leg is a direct sum of
coordinate blocks indexed by triples of words. The canonical cyclic
regrouping applies to each entire block, including when the three legs of
a positive-degree monomial have different block labels. The final signed
ledger identifications also extend over the complete spaces. These
operations are independent of the degeneration parameter.

The composition lemma makes exactly the needed claim: constant pre- and
post-restrictions preserve the polynomial degree bound, and degrees add
under tensor products of polynomials with nonnegative exponents. It does
not assert an invalid additive degree rule for general composition of
degenerations. Root averaging uses only nonzero points and retains every
required source copy. The edge case \(M=1\) gives \(L=1\), degree
zero, and a valid separator; if the overall degree is zero, exactification
likewise uses the single root of unity of order one.

The independent composition reviewer confirmed these whole-space
definitions and found no additional dependence on matching sector labels.

## 6. Signed ledger and catalyst interface

References: `rounding.tex:50–134`; `extraction.tex:4–12` and `90–97`.

The alternating row signs are necessary off the diagonal and are used
correctly. The negative boundary of row \(r+1\) is
\[
 [\sigma_{r+1};r+1,r]
 =[-\sigma_{r+1};r,r+1]
 =[\sigma_r;r,r+1],
\]
which is precisely the positive boundary of row \(r\). The remaining
symbols are \(K[+;a,a]\) and \(-K[\mathsf M_2]\).

Each action and reset has equal total source and output convolution
multiplicity. Both complete totals are \(U+T\). Coordinatewise minima
therefore give a catalyst of multiplicity \(U+T-K\), retained on both
sides. There is no cancellation of a tensor factor from a restriction.

No source column is one: action sources have \(b\ge r\ge2\), and
reset sources have \(b=4r-1\). The only output with a dimension
parameter one is the boundary \((r,b)=(2,1)\). Thus its representative
\(\mathsf M_2\) has zero catalyst multiplicity. All remaining catalyst
factors are covered by the displayed convolution evaluation rank bound,
with exponent \(3Nc_{\sigma,r,b}\).

The active index sets omit actions with \(w_i=0\) and resets with
\(z_r=0\). Consequently every applied type map has positive tensor
power, as its lemma requires. Zero child counts remain allowed within an
active action. Omitting inactive maps changes neither the ledger nor its
auxiliary charges.

The independent resource reviewer confirmed the signs, both residual
symbols, the catalyst cardinality, and the absence of a boundary rank
charge.

## 7. Dimensions, degrees, and copy counts

Reference: `extraction.tex:20–134`.

For each active relation there are three orientations. Each consumes
\(2M_i-1\) full source copies and produces \(M_i\) independent
target sectors. Therefore
\[
 S=\prod_i(2M_i-1)^3,\qquad H=\prod_iM_i^3,
 \qquad D=3\sum_i(M_i-1)^2.
\]
An action's three auxiliaries have dimension \(d_i^{Nw_i}\), one
in each dot-product orientation, giving a matrix factor of that dimension.
All actions together supply
\[
 u=\prod_{i\in\mathcal I_c}d_i^{Nw_i}.
\]
Each relation's three separator auxiliaries give \(\mathsf M_{M_i}\).
Their product and the \(NK\) residual boundary factors give
\[
 v=2^{NK}\prod_iM_i.
\]
These are matrix dimensions, not leg dimensions; the latter are their
squares. No square or additional factor of two has been omitted in the
transition from sixfold to threefold balancing.

Exactification supplies \(E=kD+1\) copies. Evaluation of the endpoint
tensor costs \((2a-1)^{3NKk}\) in one step. Repeating the resulting
exact restriction \(j\) times keeps the catalyst exponent \(k\),
so its initial supply costs \(\kappa_N^k\). The stated relative
scheme consequently has exactly
\[
 r_* =\kappa_N^k E^j S^{kj}(2a-1)^{3NKkj},
 \qquad m_*=H^{kj},\qquad A=u^{kj},\quad B=v^{kj}.
\]

All these charges remain valid when some \(M_i=1\): such a relation
contributes one copy and zero separator degree, while its source auxiliary
dimension is still charged in full.

## Findings and disposition

No correction is required on the audited points. In particular, this
review found no invalid basis change, omitted filtration block, failure at
zero counts, premature first-leg normalization, illicit partial leg swap,
loss of independence between sectors, missing root evaluation, negative
degree, sign mismatch, or uncharged multiplicity.

The result of this review is confined to the tensor maps and their
resource accounting. It supplies no independent conclusion about the
occupation bounds, quantitative parameter choices, literature coverage,
or originality of the resulting theorem.
