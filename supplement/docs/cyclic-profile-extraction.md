# Alternating threefold profile extraction

Date: 2026-10-07. Original derivation from the existing local tensor maps;
no literature research.

Three cyclic copies suffice for the finite profile construction if adjacent
rows use opposite orientations. This is an exact change to the tensor
recipe, including its catalysts, not just a scalar-profile argument.
At fixed parameters it halves the logarithms of the source and target
matrix dimensions. It does not automatically improve the finite exponent:
threefold power \(2k\) has exactly the same charged scalar counts as
sixfold power \(k\). No practical multiplication seed is supplied.

## The orientation identities

Let \(\mathcal A\subset S_3\) be the three even permutations, and define

\[
S^+_{r,b}=\bigotimes_{\pi\in\mathcal A}C(r,b)^\pi,
\qquad
S^-_{r,b}=\bigotimes_{\pi\notin\mathcal A}C(r,b)^\pi.
\]

The native first-two-leg swap changes \(C(r,b)\) to \(C(b,r)\): its
coefficient identity is \(i+j=j+i\). Multiplication by this odd
permutation exchanges the two cosets. Reordering tensor factors separately
within each global leg therefore gives actual legwise isomorphisms

\[
S^\sigma_{r,b}\cong S^{-\sigma}_{b,r},\qquad
S^+_{r,r}\cong S^-_{r,r}.
\tag{1}
\]

No global leg exchange is needed when applying these isomorphisms to a
block in a direct sum. Moreover, \(C(1,m)=B_X(m)\), and each coset sends
its exceptional leg to each global leg once. Thus

\[
S^+_{1,m}\cong S^-_{1,m}\cong B_X(m)B_Y(m)B_Z(m)\cong T_m,
\quad R(S^\sigma_{r,b})\le(r+b-1)^3.
\tag{2}
\]

These identities are what replace the sixfold symmetry.

## Determinant and tripling maps remain exact

Retain the integer counts \(w=u+d\) and the current equal-frequency
tripling count \(z\in3\mathbb Z_{>0}\) from
[the conserved flow](rounded-profile-flows.md). At type scale \(N\), the
determinant restriction on each orientation retains \(Nu\) up labels and
\(Nd\) down labels on both affected legs. The proof that equal counts
remove every off-diagonal term is unchanged. Combining the three
orientations consumes \(T_2^{\otimes Nw}\) and produces the balanced
factors

\[
(S^\sigma_{r,b+1})^{\otimes Nu}
(S^\sigma_{r,b-1})^{\otimes Nd}.
\]

The sector count for each orientation is \(\binom{Nw}{Nu}\).

For tripling \(C(r,4r-1)\), the two outer sectors are \(C(r,r)\).
The middle sector is its odd second/third-leg permutation, after reversing
the first-input index. Equal frequencies give, across the three
orientations,

\[
(S^\sigma_{r,r})^{\otimes 2Nz/3}
(S^{-\sigma}_{r,r})^{\otimes Nz/3}
\cong(S^\sigma_{r,r})^{\otimes Nz},
\tag{3}
\]

using the diagonal identity in (1). The first-input reversals and
block-specific isomorphisms are applied **after separation**, when each
block has independent first-leg coordinates. They need not be made
compatible on the previously shared first leg. The sector count per
orientation is \((Nz)!/(Nz/3)!^3\).

This argument uses only the diagonal tripling relations \(h=r\).
It does not assert that threefold averaging handles every non-diagonal
tripling relation in the manuscript.

## A larger tripling type with only the middle count fixed

There is a further exact improvement. For supported terms
\(x_i y_j z_{i+j}\), the left input sector has \(0\le j<r\), so
\(i+j\le2r-2\) lies in the left output sector. The right input sector
has \(j\ge3r-1\), so its output is also in the right sector. Thus
there are no outer-to-outer cross terms. Every mismatched term has a
middle input label and an outer output label.

In \(t\) tripling factors, retain only a prescribed number \(h\) of
middle labels on both affected legs; allow either outer label freely.
For each supported term, the indicator of a middle input is at least the
indicator of a middle output, with equality exactly for matching labels.
Equal total counts therefore remove all off-diagonal terms. The number
of retained matched sectors is

\[
M_{\rm middle}(t,h)=\binom th2^{t-h}.
\tag{3a}
\]

Each word has \(t-h\) outer blocks and \(h\) middle blocks. Across
the three orientations its tensor is
\((S^\sigma_{r,r})^{t-h}(S^{-\sigma}_{r,r})^h\cong(S^\sigma_{r,r})^t\).
As before, the block-dependent first-leg reversals are made only after
separation. The differing numbers of left and right outer labels do not
change this balanced output.

The ratio between consecutive values in (3a) is
\((t-h)/(2(h+1))\). A maximizing choice is
\(h=\lfloor(t+1)/3\rfloor\). Since their sum over \(h\) is \(3^t\),

\[
M_{\rm middle}(t,\lfloor(t+1)/3\rfloor)
\ge\frac{3^t}{t+1}.
\tag{3b}
\]

This removes the tripling divisibility condition. For any nonnegative
integer \(z\), set \(t=Nz\); no integer \(Nz/3\) is required.
It also replaces the previous tripling finite-type penalty
\(2\log(Nz+1)\) by \(\log(Nz+1)\). At \(t=3\), for example,
there are 12 matched sectors rather than the six sectors of the equal
three-frequency type. This improvement is independent of the row sign
choice; it could also be used with sixfold balance.

## Alternating rows telescope into an actual catalyst

Choose the final row's sign positive and put
\(\sigma_r=(-1)^{a-r}\). The exact integer current equations give
the final-row residual

\[
K(S^+_{a,a}-S^+_{a,a-1}),
\]

and each lower row's residual

\[
K(S^{\sigma_r}_{r,r+1}-S^{\sigma_r}_{r,r-1}).
\]

Since \(\sigma_{r+1}=-\sigma_r\), identity (1) matches the positive
boundary of row \(r\) to the negative boundary of row \(r+1\).
Their sum leaves exactly

\[
K S^+_{a,a}-K T_2.
\tag{4}
\]

Constant row orientation would fail: already at index 3 it leaves the
additional residual \(K(S^+_{2,3}-S^-_{2,3})\).

To implement the accounting, use signed tensor keys. Swapping \(r,b\)
flips the sign, while diagonal and boundary signs can be identified by
(1)-(2). After these explicit isomorphisms, put every common source and
output factor into the catalyst \(\mathcal C_N\). Its exponents sum to
\(N(U+T-K)\), as before. No source or target tensor is canceled as a
restriction. A supplied rank bound is

\[
\kappa_N=\prod_{r,b,\sigma}(r+b-1)^{3Nc_{\sigma,r,b}}.
\tag{5}
\]

The signed exponents have the same counts as the previous unsigned
ledger, with orientations chosen so that every claimed identification is
an isomorphism.

## Complete finite cost

Let \(M_i\) be the determinant binomial counts and the sector counts of
the chosen tripling variant,
and let \(M=\prod_iM_i\). Three separators per relation give

\[
\mathscr S=\prod_i(2M_i-1)^3,
\qquad \mathscr H=M^3,
\qquad D=3\sum_i(M_i-1)^2.
\]

The exact type maps followed by separation produce the degeneration

\[
\mathscr S\,\mathcal C_N(S^+_{a,a})^{\otimes NK}T_u
\rightsquigarrow\mathscr H\,\mathcal C_NT_v,
\qquad
u=2^{NU},\quad v=2^{NK}M.
\tag{6}
\]

Here the separator auxiliaries also balance into one \(T_{M_i}\), rather
than its square. No other degree appears: the determinant and tripling
type restrictions were already exact.

Exactify power \(k\) with \(E=kD+1\) evaluations, then reuse the exact
catalyst \(j\) times. The resulting relative computation is

\[
r_*T_A\ge m_*T_B,
\quad A=u^{kj},\quad B=v^{kj},
\]

\[
r_*=\kappa_N^k E^j\mathscr S^{kj}(2a-1)^{3NKkj},
\qquad m_*=\mathscr H^{kj}.
\tag{7}
\]

The fixed-batch upper expression is consequently

\[
\frac{3NK\log(2a-1)+\log(\mathscr S/\mathscr H)
 +\log E/k+\log\kappa_N/j+\log2/(kj)}{\log(v/u)}.
\tag{8}
\]

The [pooled scheduler](streamed-profile-recursion.md) removes only the
last ceiling allowance. All interpolation evaluations and catalyst costs
remain. For the rounded flow, the exact same entropy quantity
\(\mathcal G=K\log F(a,a)-\mathcal L\) gives
\(\log(v/u)\ge N\mathcal G-\mathcal E_N\). Thus the limiting exponent
is still \(3\log(2a-1)/\log F(a,a)\), and the all-cost polynomial
parameter family still tends to \(9/4\).

Denote sixfold quantities by subscript 6 and threefold quantities by 3.
At the same type scale, flow counts, and chosen sector selections,

\[
u_6=u_3^2,\quad v_6=v_3^2,\quad
\mathscr S_6=\mathscr S_3^2,\quad
\mathscr H_6=\mathscr H_3^2,\quad
\kappa_6=\kappa_3^2,\quad D_6=2D_3.
\]

Therefore setting \(k_3=2k_6\), with the same \(j\), reproduces
\(A,B,r_*,m_*,E\) exactly. This is an equality of the **charged scalar
counts**, not a claim that all catalyst tensors or linear maps are identical.
Odd threefold powers provide additional finite choices. At equal power,
the dimension logarithms halve, but the normalized interpolation and ceiling
charges do not; a better finite exponent cannot be inferred from the smaller
source side alone.

## Scope of the smaller size floors and verification

With the current equal-frequency tripling types, the previous conservation
bounds now give source-side floors \(2^{16}\) for any prescribed subcubic
nonnegative flow, \(2^{30}\) for the implemented positive rounded family,
and \(2^{96}\) for a rounded-family count beating rank 40. The corresponding
sixfold floors were their squares. These are scoped count statements from
[the materialization note](rounded-profile-practical-size.md), not lower
bounds for every changed construction or streamed implementation.

In particular, the general nonnegative-flow floor is much smaller; it does
not prove that its smallest flow has any matrix-dimension gain. This change
justifies a separate small exact count screen, rather than carrying the
sixfold floor over to the new construction.

These floors must not be transferred unchanged to the partial-middle
construction with arbitrary integer tripling counts. Divisibility by three
was used to derive them. The partial-middle lemma and the complete cost
formulas above apply without it; a different finite count screen is needed
for that enlarged family. The reproducible rounded ledgers below retain
the old divisible counts, while the separate partial-type checks cover
arbitrary counts.

That [separate finite screen](profile-flow-screen.md) is now complete. It
allows every integer tripling count and the optimistic sector bound `3^z`,
and excludes subcubic prescribed counts for every effective binary-flow
budget `U <= 32`. Thus the partial-middle construction also has no such
count at recursive source sides at most `2^32` under the stated execution.

```sh
python -m experiments.cyclic_profile_extraction > results/cyclic-profile-extraction.json
python -m pytest tests/test_cyclic_profile_extraction.py -q
```

All 25 tests pass. They check exact sparse tensor supports for both signs,
both boundary identifications with matrix multiplication, signed ledgers
through index 63, the failure of constant signs, and exact equality of
threefold-power-2 and sixfold-power-1 scalar counts in two small cases.
They also project the actual local tripling supports onto equal middle
counts, verify every sector's size, and check the exact mode and type bound.
The [saved report](../results/cyclic-profile-extraction.json) contains the
finite ledgers. Independent verification also checked 27 signed ledgers
and 33 sparse-coordinate cases, including the tripling orientation and
post-separation first-leg reversal. The partial-middle extension received
an independent 140-case restriction check and exact mode checks through
count 500. No blocking issue was found.

The composed large coefficient maps, finite numerical precision, and useful
runtime remain unverified. This is a valid reduction in the required tensor
balance, not a practical exponent-2.25 algorithm.
