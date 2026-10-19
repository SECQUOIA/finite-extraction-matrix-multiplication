# Verification note: the resource lower bound for shifted chains

Topic key: `lower`. Date: 18 October 2026.

This note checks the claimed lower bound

\[
\log A>10^{-7}\,\varepsilon^{-9/2}\log^3(1/\varepsilon)
\qquad(0<\varepsilon\le 2^{-40})
\]

for variable-arity paired shifted chains, and its replication corollary.
It gives a precise definition of the class of schemes covered, a complete
proof that I endorse, the constants and the allowance range, and a list of
what the bound does not cover.

Sources read: `docs/round11-variable-arity-bound.md` and its review,
`docs/round10-resource-lower-bound.md` and its review,
`docs/round10-orientation-control.md` and its review,
`experiments/round11_variable_arity_bound.py`,
`tests/test_round11_variable_arity_bound.py`; for the framework,
`docs/round8-multiscale-construction.md`, `docs/round10-adaptive-chain.md`,
`docs/round11-arity-ramp.md`, and the statement of
`docs/round11-ramp-bounds.md`; from v5, `manuscript/preliminaries.tex`
(relative schemes, pooled recursion, exactification) and
`manuscript/maps.tex` (tripling, separator, orientations).

New files: this note and
[`experiments/shifted_chains_check_lower.py`](../experiments/shifted_chains_check_lower.py).
No existing file was changed.

Status labels used below:

- **proved here**: I re-derived the statement and give the proof.
- **checked numerically**: verified with exact or rational-interval
  arithmetic on finite cases only.
- **taken from the notes unchecked**: used as an input; not re-derived here.

## 1. Verdict

The round-11 proof is correct. I re-derived every step and found no
mathematical error, no wrong constant, and no off-by-one error. The
bound holds as stated, and the replication corollary is correct.

The issues are presentational or make the statement weaker than it needs
to be:

1. The notes define the exponent with a ceiling,
   \(\log\lceil r_*/m_*\rceil/\log(B/A)\). v5 defines the pooled exponent
   without it (Definition `def:relative-scheme`). Because the ceiling only
   raises the exponent, the bound holds for the pooled exponent. That is
   the stronger statement, and it matches v5.
2. The cutoff \(\varepsilon\le2^{-40}\) comes from the fixed-arity
   proof. The variable-arity proof needs only \(\varepsilon<1/36864\).
3. The proof of the arity gap already gives \(1/(96d^2)\). The notes then
   weaken this to \(1/(192d^2)\). With \(1/(96d^2)\), the same proof gives
   the coefficient \(10^{-6}\) for \(\varepsilon\le2^{-14}\).
4. Some hypotheses can be dropped. The condition \(c<b\) follows from
   the crop inequality. Complete types are not needed; any nonempty subset
   of one type class works. The divisibility \(n_ik_i\mid P\) in the
   corollary is also unnecessary: any partition of the \(P\) factors into
   blocks works, with the same proof and constant.

Sections 2 and 3 give the statement I recommend for the paper (Theorem 5).
It covers the common-batch theorem and the replication corollary as
special cases.

The bound depends on the construction's count formulas (Section 2.2).
I take those formulas from the construction notes and do not re-prove
them here.

## 2. The class of schemes

### 2.1 Notation from v5

All logarithms are natural. The macros \(\MM\), \(\restr\), and \(\R\) are
v5's (matrix multiplication tensor, restriction, rank). \(\MM_N\) is the
matrix multiplication tensor of side \(N\). \(C(r,b)\) is the convolution tensor. For the paired symmetrized
tensor, write
\(Q_{r,b}=S^+_{r,b}S^-_{r,b}=\bigotimes_{\pi\in S_3}C(r,b)^\pi\). Then
\(Q_{r,b}\cong Q_{b,r}\), \(Q_{1,t}\cong\MM_{t^2}\), and
\(\R(Q_{r,b})\le(r+b-1)^6\) (v5, eqs. `balanced`, `balanced-properties`).
A relative scheme is a restriction \(r_*\MM_A\restr m_*\MM_B\) with
\(B>A\). Its pooled exponent is \(p=\log(r_*/m_*)/\log(B/A)\), and pooled
recursion turns it into an \(O(n^p)\) algorithm (v5, Lemma `lem:batch`).

### 2.2 Local stage relation (taken from the notes unchecked)

Fix an arity \(d\ge2\) and put \(q=d+2\). A **type** of size \(n\) is a triple
\(\tau=(\ell,o,m)\) of nonnegative integers with sum \(n\). Its sector count
is

\[
M(d,\tau)=\frac{n!}{\ell!\,o!\,m!}(d-1)^{\ell}2^{o}.
\]

A **legal step** at arity \(d\) splits an entry \(b\) of the current pair
and keeps the other entry \(r\). It produces a child \(c\) with

\[
c\ge1,\qquad (d+2)c\le db-r+1 .
\tag{2.1}
\]

The condition \(c<b\) follows from (2.1) because \(r\ge1\). Condition
(2.1) says that the quotient width \(db-(d-1)c\) is at least
\(3c+r-1\), which is what the cropped three-block reset needs.

The construction notes
(`docs/round8-multiscale-construction.md`, eq. (5)) give the stage
relation

\[
(2M-1)^6\,Q_{r,b}^{\otimes n}\,\MM_{d^{2n}}
\ \unrhd\ M^6\,Q_{c,r}^{\otimes n}\,\MM_{M^2},
\qquad M=M(d,\tau)\ge1,
\]

as a degeneration of degree at most \(6(M-1)\). It is built from the
shifted-chain map, the reset (a cropped generalization of v5's tripling),
type restriction in all six orientations, and Lü's polynomial separator
(v5, Remark `rem:polynomial-separator`). By v5 Lemma `lem:exactification`,
its exactified \(k\)-th power is the restriction

\[
E\,(2M-1)^{6k}\,Q_{r,b}^{\otimes nk}\,\MM_{d^{2nk}}
\ \restr\ M^{6k}\,Q_{c,r}^{\otimes nk}\,\MM_{M^{2k}},
\qquad E=1+6k(M-1).
\tag{2.2}
\]

I checked that these counts agree with v5's separator (\(2M-1\) copies
per orientation, degree \(M-1\) for Lü's version) and with v5's
exactification. I did not re-prove the shifted-chain maps; that belongs
to the construction topic.

### 2.3 Definition (paired shifted-chain scheme)

**Data.**

- Integers \(L\ge1\) (levels) and \(P\ge1\) (global paired power).
- A source pair \(\{r_0,b_0\}\) of positive integers, with source span
  \(s=r_0+b_0-1\).
- For each level \(i=1,\dots,L\), an arity \(d_i\ge2\) and a transition
  \(\pi_{i-1}\to\pi_i\) between unordered pairs. The transition is a legal
  step (2.1) that splits either entry of \(\pi_{i-1}\) (the choice of
  entry is the "input swap"), optionally followed by a **free crop**
  that replaces each entry by a smaller positive integer. A smaller child
  than the largest legal one is a special case.
- For each level \(i\), a partition of the \(P\) tensor factors into
  **blocks** \(j\in J_i\). Block \(j\) has a batch size \(n_{ij}\), a power
  \(k_{ij}\), and a type \(\tau_{ij}\) of size \(n_{ij}\) with
  \(M_{ij}=M(d_i,\tau_{ij})\ge1\). The sizes satisfy
  \(\sum_{j}n_{ij}k_{ij}=P\).
- A terminal entry \(t\), a positive integer at most the larger entry of
  \(\pi_L\).

**Scheme.** The scheme composes four kinds of restrictions:

1. The source evaluation
   \(s^{6P}\MM_A\restr Q_{r_0,b_0}^{\otimes P}\MM_A\), which tensors \(P\)
   copies of the rank decomposition of \(Q_{r_0,b_0}\).
2. At each level, the tensor product over its blocks of the separately
   exactified relations (2.2). Each block uses its own auxiliary
   \(\MM_{d_i^{2n_{ij}k_{ij}}}\) inside \(\MM_A\).
3. The free crops and swaps, which are restrictions and isomorphisms of
   \(Q\).
4. The terminal projection
   \(Q_{\pi_L}^{\otimes P}\restr Q_{1,t}^{\otimes P}\cong\MM_{t^{2P}}\).

The resulting relative scheme \(r_*\MM_A\restr m_*\MM_B\) has

\[
\begin{aligned}
A&=\prod_i d_i^{2P}, &
B&=t^{2P}\prod_{i,j}M_{ij}^{2k_{ij}},\\
r_*&=s^{6P}\prod_{i,j}(2M_{ij}-1)^{6k_{ij}}E_{ij}, &
m_*&=\prod_{i,j}M_{ij}^{6k_{ij}},
\qquad E_{ij}=1+6k_{ij}(M_{ij}-1).
\end{aligned}
\tag{2.3}
\]

**Special cases.**

- *Common batch* (round 11, eq. (3)): each level has one block
  \((n,k,\tau_i)\) and \(P=nk\).
- *Replication* (round 11, corollary): level \(i\) has \(P/(n_ik_i)\)
  identical blocks \((n_i,k_i,\tau_i)\).
- Exactifying \(J\) replicated \((n,k)\) blocks together is exactly one
  block \((n,kJ)\), so this is also in the class.

The script recomposes (2.3) by multiplying block multiplicities and
compares the result with both special-case formulas.

**How the task's items appear in the definition.**

| Item | Meaning in the class |
| --- | --- |
| Arities | \(d_i\ge2\), arbitrary per level (Remark 8 adds \(d_i=1\)). |
| Crops | Any legal child, plus free crops between levels. |
| Input/output swaps | Pairs are unordered, since \(Q_{r,b}\cong Q_{b,r}\). |
| Types | One type per block, the same in all six orientations and for both signs; any nonempty subset of its class also works. |
| Inventories | \(n_{ij}\) factors of \(Q\), that is, \(n_{ij}\) of each sign. |
| Powers | \(k_{ij}\). |
| Separator | \((2M-1)^6\to M^6\) copies, degree \(6(M-1)\). |
| Exactification | Separate for each block (and so for each level). |
| Auxiliaries | Uncompressed: \(\MM_{d^{2n}}\) per batch. |
| Source | Full evaluation, \(s^{6P}\). |
| Terminal | Crop to \(\{1,t\}\). |
| Exponent | Pooled exponent (the ceiling version is covered a fortiori). |

### 2.4 What the proof actually uses

The proof uses only these properties of (2.3):

1. \(\log A\ge 2P\sum_i\log d_i\).
2. The upper bound on \(B\) in (2.3).
3. \(r_*/m_*\ge s^{6P}\prod E_{ij}\).
4. \(E_{ij}\ge M_{ij}\), together with the type bounds of Lemma 4.
5. The chain geometry.

So the theorem also holds for any scheme whose accounting is no better in
each of these respects: larger \(A\), smaller \(B\), larger
\(r_*/m_*\), or a separator with more copies. Lemma 4 bounds the largest
type count, so subsets of type classes are covered too.

## 3. Statements and proofs (all proved here)

Notation: \(q=d+2\). \(\lambda_d\in(0,1)\) is the positive root of
\(f_d(x)=qx^2+x-d\). Put \(a_d=-\log\lambda_d\),
\(g_d=\log(q/d)\), \(\omega_d=3a_d/g_d\), and \(K=21/20\).

**Lemma 1 (contraction).** Let \(Q(x,y)=x^2+4xy+y^2\) and
\(\Phi(r,b)=\tfrac23\sqrt{Q(r-\tfrac13,b-\tfrac13)}\) for real
\(r,b\ge1\). Then \(\Phi\) is symmetric and nondecreasing in each
argument. For every legal step (2.1) at any arity \(d\ge1\),
\(\Phi(c,r)\le\lambda_d\Phi(r,b)\).

*Proof.* Symmetry is clear. \(\partial_xQ=2x+4y>0\) when \(x,y>0\), and
the centered coordinates are at least \(2/3\).

Put \(R=r-\tfrac13\), \(B=b-\tfrac13\), \(C=c-\tfrac13\),
\(\beta=\lambda+1/q\), and \(T(R,B)=((dB-R)/q,\,R)\). Expanding gives

\[
\lambda^2Q(R,B)-Q(T(R,B))-(1-\beta^2)(R-\lambda B)^2
=\frac{f_d(\lambda)}{q}\Bigl[2R^2+(4-2\beta)RB+\bigl(\lambda\beta+\tfrac dq\bigr)B^2\Bigr],
\]

which vanishes at \(\lambda=\lambda_d\). The script checks this as a
polynomial identity in \(\mathbb Z[q,\lambda,R,B]\) after multiplying by
\(q^3\).

Since \(f_d(1-1/q)=1>0\) and \(f_d\) is increasing on \([0,\infty)\),
\(\lambda<1-1/q\), so \(0<\beta<1\). Because \(q/3=(d+2)/3\), condition
(2.1) is equivalent to \(qC\le dB-R\). As \(C\ge2/3>0\), monotonicity
gives \(Q(C,R)\le Q(T(R,B))\le\lambda^2Q(R,B)\). \(\square\)

**Lemma 2 (endpoint inequality).** For every scheme in the class (any
arities \(d_i\ge1\)),

\[
\log s\ \ge\ \log K+\sum_{i=1}^L a_{d_i}+\tfrac45\log t .
\]

*Proof.* Lemma 1 bounds each step, and monotonicity bounds the free crops
and the terminal crop. Hence
\(\Phi(1,t)\le\Phi(\pi_L)\le\prod_i\lambda_{d_i}\Phi(\pi_0)\).

*Start.* The first step splits an entry \(b\ge2\), so \(s\ge2\). With
\(R_0+B_0=s+\tfrac13\) and \(Q(x,y)\le\tfrac32(x+y)^2\),

\[
\Phi(\pi_0)^2\le\tfrac23(s+\tfrac13)^2\le s^2,
\]

because \(s^2-\tfrac23(s+\tfrac13)^2=\tfrac1{27}\bigl((s-2)(9s+6)+10\bigr)>0\) for \(s\ge2\).

*End.* \(\Phi(1,t)^2=\tfrac49(t^2+2t-\tfrac13)\). Substitute
\(u=t-1\). All eleven coefficients of
\((4/9)^5(u^2+4u+8/3)^5-K^{10}(u+1)^8\) are positive (computed exactly in
the script). Hence \(\Phi(1,t)\ge Kt^{4/5}\) for all \(t\ge1\).

Combining the start and end bounds proves the lemma. \(\square\)

The hypothesis \(s\ge2\) matters. The round-10 review gives a real start
near \((1,1)\) where the inequality with \(K\) fails. Integer chains are
not affected.

**Lemma 3 (ideal gap).** For \(d\ge2\),
\(\omega_d-\tfrac94\ge\frac1{24q^2}\ge\frac1{96d^2}\) and
\(g_d\le2/d\). For \(d=1\), \(\omega_1>2.277\).

*Proof.* Put \(z=(d/q)^{1/4}\), so \(q=2/(1-z^4)\). Then

\[
f_d(z^3)=\frac{z^3(1-z)^2}{1+z^2}>0,
\]

checked as the polynomial identity
\((1-z^4)f_d(z^3)=z^3(1-z)^2(1-z^2)\). Hence \(\lambda<z^3\).

From \(g=-4\log z\) we get \(\omega-\tfrac94=(3/g)\log(z^3/\lambda)\).
By the mean value theorem, with \(f'\le2q+1\) on \([0,1]\), and
\(\log y\ge1-1/y\),

\[
\omega-\tfrac94\ \ge\ \frac{3(1-z)^2}{(1+z^2)(2q+1)g}.
\]

Now use \(1-z\ge(1-z^4)/4=1/(2q)\), \(1+z^2\le2\), \(2q+1\le9d/2\),
and \(g=\log(1+2/d)\le2/d\). This gives \(1/(24q^2)\), and \(q\le2d\)
gives \(1/(96d^2)\). The value for \(d=1\) comes from a rational
interval enclosure. \(\square\)

Numerically, \((\omega_d-\tfrac94)q^2\) decreases toward about \(3/32\)
(0.0942 at \(d=400\)), so the constant \(1/24\) is within a factor of
about 2.3 of the truth (checked numerically).

**Lemma 4 (type counts).** Let \(d\ge2\), \(n\ge1\), and let \(M\) be the
count of any type of size \(n\).

- (a) \(M\le q^n\).
- (b) If \(M>d^n\), then \(n\ge3\) and \(d\le2n\).
- (c) If \(n\ge3\) and \(d\le2n\), then \(M\le q^n/2\).
- (d) If \(n\ge2q\), then \(M\le4e\,q^{n+1}/n<12\,q^{n+1}/n\).

*Proof.* (a) follows from the multinomial theorem.

(b) For \(n=1\), the counts are \(d-1,2,1\), all at most \(d\). For
\(n=2\), they are \((d-1)^2,4(d-1),2(d-1),4,4,1\), all at most \(d^2\),
since \(d^2-4(d-1)=(d-2)^2\). If \(d\ge2n+1\), then using
\(n!/\ell!\le n^{o+m}\),

\[
\frac{M}{(d-1)^n}\le\frac{(2n/(d-1))^o(n/(d-1))^m}{o!\,m!}\le1 .
\]

(c) \(M/q^n\) is a multinomial probability with
\(p=((d-1)/q,2/q,1/q)\). It is at most the probability that a
\(\mathrm{Bin}(n,p_K)\) variable takes the value \(\ell\). Here
\((n+1)p_K\in[1,n]\), because \(n(d-1)\ge3\) and \(d\le3n+1\). So the
binomial has a mode \(a\) with \(1\le a\le n-1\). The two neighbour
ratios have product \(a(n-a)/((a+1)(n-a+1))\ge1/4\), so their sum is at
least \(1\). Hence the mode has mass at most \(1/2\).

(d) Let \(a\) be a maximizing type. Moving one factor from category
\(j\) to category \(i\) cannot increase the probability, so
\(a_jp_i\le(a_i+1)p_j\). Summing over \(j\ne i\) gives
\(a_i\ge(n+1)p_i-1\). Since \(n\ge2q\ge8\), this yields
\(a_K\ge n/8\), \(a_O\ge n/q\), and \(a_M\ge n/(2q)\ge1\).

The factorial bounds \(\sqrt u(u/e)^u\le u!\le e\sqrt u(u/e)^u\) for
\(u\ge1\) follow from concavity of \(\log\): the trapezoid rule on
\([1,u]\) gives the upper bound, and the midpoint rule on
\([j-\tfrac12,j+\tfrac12]\) gives the lower bound. Together with
\(\prod_i(np_i/a_i)^{a_i}\le1\) (Gibbs' inequality), they give

\[
M/q^n\le e\sqrt{n/(a_Ka_Oa_M)}\le4eq/n. \qquad\square
\]

**Definition.** For block \((i,j)\), write \(w_{ij}=n_{ij}k_{ij}/P\), so
that \(\sum_jw_{ij}=1\). Put \(D_{ij}=n_{ij}\log q_i-\log M_{ij}\ge0\).

**Theorem 5 (resource lower bound).** Let
\(0<\varepsilon\le2^{-14}\), \(x=\log(1/\varepsilon)\), and
\(D_0=(96\varepsilon)^{-1/2}\). Suppose a paired shifted-chain scheme
(Section 2.3) has \(B>A\) and pooled exponent \(p<9/4+\varepsilon\).
Then:

1. \(\sum_i\log d_i>\dfrac{3\log K}{2\varepsilon}D_0\log D_0>\dfrac{3\log K}{8\varepsilon}D_0x\).
2. Some level \(i\) has a block \((n,k,\tau)\) with \(d_i>D_0\),
   \(n>\dfrac{9d_ix}{16\varepsilon}>\dfrac{9D_0x}{16\varepsilon}\), and
   \(k>\dfrac{d_i\log d_i}{4\varepsilon}>\dfrac{D_0x}{16\varepsilon}\).
3. \(\log A=2P\sum_i\log d_i
   >\dfrac{27\log(21/20)}{1024\cdot96^{3/2}}\,\varepsilon^{-9/2}x^3
   >10^{-6}\,\varepsilon^{-9/2}\log^3(1/\varepsilon)\).

With the round-11 gap constant \(1/(192d^2)\), the same proof gives
coefficient \(10^{-7}\) for every \(\varepsilon<1/36864\), and in
particular for \(\varepsilon\le2^{-40}\) as claimed in the notes.

*Proof.*

*Step 1 (normalization).* Dividing the logarithms of (2.3) by \(2P\),

\[
\frac{\log(B/A)}{2P}=\log t+\sum_{i,j}w_{ij}\Bigl(g_i-\frac{D_{ij}}{n_{ij}}\Bigr),
\]

\[
\frac{\log(r_*/m_*)}{2P}
=3\log s+\sum_{i,j}w_{ij}\Bigl[\frac3{n_{ij}}\log\frac{2M_{ij}-1}{M_{ij}}
+\frac{\log E_{ij}}{2n_{ij}k_{ij}}\Bigr]
\ \ge\ 3\log s+\sum_{i,j}w_{ij}\frac{\log E_{ij}}{2n_{ij}k_{ij}} .
\]

*Step 2 (profit inequality).* Put \(p_0=\tfrac94+\varepsilon\le\tfrac{12}5\).
Since \(B>A\), the hypothesis \(p<p_0\) means
\(\log(r_*/m_*)<p_0\log(B/A)\). By Lemma 2,
\(3\log s\ge3\log K+\sum_{i,j}w_{ij}\,\omega_{d_i}g_i+\tfrac{12}5\log t\).
Combining the two,

\[
\sum_{i,j}w_{ij}t_{ij}>3\log K+\bigl(\tfrac{12}5-p_0\bigr)\log t\ge3\log K,
\qquad
t_{ij}=(p_0-\omega_{d_i})g_i-\frac{p_0D_{ij}}{n_{ij}}-\frac{\log E_{ij}}{2n_{ij}k_{ij}} .
\]

So the set \(I=\{(i,j):t_{ij}>0\}\) is nonempty, and
\(\sum_Iw_{ij}t_{ij}>3\log K\).

*Step 3 (one profitable block).* Fix \((i,j)\in I\) and drop the indices.

- Since \(D\ge0\) and \(E\ge1\), positivity of \(t\) gives \(\omega<p_0\).
  Lemma 3 then gives \(1/(96d^2)<\varepsilon\), that is, \(d>D_0\).
- Since \(\omega>9/4\),
  \[
  p_0D/n<(p_0-\omega)g<\varepsilon g.
  \tag{\(*\)}
  \]
  Hence \(\tfrac1n\log M=\log q-D/n>\log q-g\varepsilon/p_0>\log d\),
  that is, \(M>d^n\).
- Lemma 4(b,c) now gives \(D\ge\log2\). By \((*)\) and \(g\le2/d\),
  \(n>(9\log2/8)\,d/\varepsilon\).
- With \(q\le2d\) and \(\log2>1/2\), this gives
  \(n/(12q)>3/(128\varepsilon)\).
- Since \(\varepsilon\le9/64\), we have \(n\ge2q\), so Lemma 4(d)
  applies. Since \(\varepsilon\le9/16384\),
  \(D\ge\log(n/(12q))>\log(3/(128\varepsilon))\ge x/2\).
- By \((*)\) again, \(n>p_0D/(\varepsilon g)>9dx/(16\varepsilon)\).
- For the exactification charge, \(E\ge M>d^n\) and
  \(\log E/(2nk)<\varepsilon g\le2\varepsilon/d\). Hence
  \(k>d\log d/(4\varepsilon)\).
- Finally, \(\varepsilon<1/9216\) gives \(\log D_0>x/4\), and \(d>D_0>1\)
  gives \(d\log d>D_0\log D_0>D_0x/4\).

*Step 4 (arity charge).* For \((i,j)\in I\),

\[
t_{ij}<\varepsilon g_i\le2\varepsilon/d_i<\frac{2\varepsilon\log d_i}{D_0\log D_0},
\]

because \(d\log d\) is increasing. Weight by \(w_{ij}\), sum over \(I\),
and use \(\sum_jw_{ij}\le1\):

\[
3\log K<\frac{2\varepsilon}{D_0\log D_0}\sum_i\log d_i .
\]

This proves item 1.

*Step 5 (combination).* \(P\ge nk\) for the block of Step 3. Hence

\[
\log A=2P\sum_i\log d_i
>2\cdot\frac{9D_0x}{16\varepsilon}\cdot\frac{D_0x}{16\varepsilon}\cdot\frac{3\log K\,D_0x}{8\varepsilon}
=\frac{27\log K}{1024}\frac{D_0^3x^3}{\varepsilon^3}.
\]

Use \(D_0^3=96^{-3/2}\varepsilon^{-3/2}\), \(\log(21/20)>1/21\), and
\(96^{3/2}<960\). The coefficient exceeds
\(27/(21\cdot1024\cdot960)=3/2293760>1.3\cdot10^{-6}\). \(\square\)

**Corollary 6 (round-11 statements).**

- (a) With one block \((n,k,\tau_i)\) per level, Theorem 5 is round-11
  eq. (1), with a better constant and range.
- (b) In the replication model (\(n_ik_i\mid P\), with \(P/(n_ik_i)\)
  identical blocks at level \(i\)), Theorem 5 applies directly. It gives
  \(P\ge n_ik_i>\tfrac{9D_0^2x^2}{256\varepsilon^2}\) for a profitable
  level, and the same bound on \(\log A\).

Proved here.

**Corollary 7 (no scheme in the class reaches 9/4).** Every scheme in the
class with \(B>A\) has

\[
p\ \ge\ \min\bigl(\min_i\omega_{d_i},\,\tfrac{12}5\bigr)\ >\ \tfrac94 .
\]

*Proof.* Let \(p_0\) be the middle quantity. If \(p<p_0\), Step 2 gives
\(\sum w_{ij}t_{ij}>3\log K>0\). But every
\(t_{ij}\le(p_0-\omega_{d_i})g_i\le0\), a contradiction. Proved here.

**Remark 8 (extensions; same proof, proved here).**

- (a) *Levels with \(d_i=1\).* These are v5-style resets with no
  auxiliary. Lemmas 1 and 2 hold for \(d=1\), and \(\omega_1>2.277\). So
  for \(\varepsilon<1/40\) these blocks have \(t<0\), and they add nothing
  to \(A\).
- (b) *Different arities for different blocks of one level.* This is
  allowed if every block's step is legal with the same child. The
  contraction factor is \(\min_j\lambda_{d_{ij}}\le\prod_j\lambda_{d_{ij}}^{w_{ij}}\).
  Replace \(\sum_i\log d_i\) by \(\sum_{ij}w_{ij}\log d_{ij}=\log A/(2P)\).
- (c) *Weaker accounting.* Monotonicity (Section 2.4) covers it, as well
  as subsets of type classes.

## 4. Step-by-step audit of the round-11 proof

| Round-11 claim | Status | Comment |
| --- | --- | --- |
| Legal update (2) | taken from the notes | Matches the reset width \(3c+r-1\). The condition \(c<b\) is redundant. |
| Counts (3) | taken from the notes | Recomposed from block relations in the script. Consistent with v5's separator and exactification. |
| Endpoint (4), \(K=21/20\) | proved here | Lemmas 1–2. 96,310 legal steps (\(d\le12\), with swaps and crops) and 9,936 random chain prefixes (with free crops) checked with rational root enclosures. |
| Gap (5), \(g\le2/d\) | proved here | The stronger \(1/(24q^2)\) holds. Checked with intervals for all \(d\le59\) and a sample up to 400. |
| (6)–(8): normalization, profitable set | proved here | Exact. The separator and ceiling terms are dropped in the safe direction. |
| (9) \(d_i>D_0\); (10) \(M_i>d_i^n\) | proved here | |
| Type lemmas (\(n\ge3\), \(d\le2n\), \(D\ge\log2\)) | proved here | Exhaustive for \(n\le30\), \(d\le64\). |
| (11) and its consequences under the cutoff | proved here | Only needs \(\varepsilon\le9/16384\). |
| Modal bound \(12q/n\) | proved here | Checked with the true \(4e\) constant up to \(n=200q+3\), \(d\le60\). Mode inequalities checked. |
| (12), (13), (14) | proved here | |
| Final constant \(27\log K/(1024\cdot192^{3/2})>10^{-7}\) | proved here | Exact value \(3/6422528\approx4.67\cdot10^{-7}\). |
| Replication corollary (15) | proved here | Generalized to arbitrary block partitions. |

The round-11 review's statements also check out, including its remark
that the gap proof gives \(1/(96d^2)\).

The six author tests pass.

## 5. Constants and allowance range

The proof uses the cutoff in only four places:

| Use | Condition |
| --- | --- |
| \(p_0\le12/5\) | \(\varepsilon\le3/20\) |
| \(n\ge2q\) | \(\varepsilon\le9/64\) |
| \(\log(3/(128\varepsilon))\ge x/2\) | \(\varepsilon\le9/16384\) |
| \(\log D_0>x/4\) | \(\varepsilon<1/36864\) with \(D_0=(192\varepsilon)^{-1/2}\); \(\varepsilon<1/9216\) with \(D_0=(96\varepsilon)^{-1/2}\) |

All four conditions are monotone in \(\varepsilon\). So the round-11
statement (\(10^{-7}\), \(\varepsilon\le2^{-40}\)) is correct but
conservative.

The recommended version is \(10^{-6}\) for \(\varepsilon\le2^{-14}\). It
uses only the stronger gap that the lemma's own proof already gives. The
script checks every threshold and coefficient in exact rational
arithmetic. That includes \(\log(21/20)>1/21\) via a certified series, as
well as \(\log2>1/2\) and \(4e<12\).

The matching upper bound in `docs/round11-ramp-bounds.md`
(\(\log A<3\cdot10^9\varepsilon^{-9/2}\log^3(4096/\varepsilon)\)) is in this
class: common \(n=k\), exact mode types, terminal \((1,1)\), separate
exactification. If that bound is correct (not checked here), the order
\(\Theta(\varepsilon^{-9/2}\log^3(1/\varepsilon))\) is tight within the
class.

Each parameter bound in Theorem 5 is matched in order by that
construction:

- \(\max d\gtrsim\varepsilon^{-1/2}\);
- \(n,k\gtrsim\varepsilon^{-3/2}\log(1/\varepsilon)\);
- \(\sum\log d\gtrsim\varepsilon^{-3/2}\log(1/\varepsilon)\).

The constants differ by a factor of about \(10^{15}\).

## 6. The replication corollary

The counts in round-11 (15) are correct. They are the product of
\(P/(n_ik_i)\) copies of each block relation; the script recomposes them
exactly. Normalizing by \(2P\) gives exactly the block profits of
Theorem 5, with weights \(1/\#\text{blocks}\) per copy.

Every profitable level gives \(n_i>9D_0x/(16\varepsilon)\) and
\(k_i>D_0x/(16\varepsilon)\), so \(P\ge n_ik_i\). The arity sum bound is
unchanged. So the corollary holds with the same constant.

Divisibility is not needed; only the partition \(\sum_jn_{ij}k_{ij}=P\)
is. Leftover factors (part of the state skipping a level) and
incomplete blocks fall outside the class (Section 7). Joint
exactification of replicated blocks inside one level is not a loophole:
it is the block \((n,kJ)\).

## 7. What the bound does not cover

The theorem is a statement about the counts (2.3) of one construction
recipe. It is not a lower bound for matrix multiplication, for \(\omega\),
or for tensor rank. It says nothing about practical sizes, bit
complexity, \(B\), \(r_*\), or \(m_*\) individually.

Outside the class:

1. **Compressed auxiliaries.** Any auxiliary of side below
   \(d^{2n}\) per batch (rounds 12–14). Round 14 claims \(p>9/4\) even
   with arbitrary auxiliary compression, but gives no resource bound.
2. **Cheaper source decompositions.** The class charges
   \(s^{6P}\). Only flattening bounds are known: the leg-1 flattening rank
   of \(Q_{r,b}\) is \((rb(r+b-1))^2<(r+b-1)^6\). So the rank of
   \(Q_{r_0,b_0}^{\otimes P}\) may be smaller, and a recursive or joint
   source (for example, using fast matrix multiplication inside
   \(Q\), as in the round-15 drafts) is not covered.
3. **Exactification and separators that break the inequalities used.**
   Collective exactification across levels (one degeneration for several
   levels), or any separator or exactifier with \(E<M\) copies.
   Exactification inside a level is covered.
4. **Other inventories.** Unpaired or sign-asymmetric inventories (the
   round-10 unpaired chain), different types in different orientations,
   and unions of several types with a joint separator. Single types are
   needed so that all sectors are isomorphic to \(Q_{c,r}^{\otimes n}\).
5. **Heterogeneous states.** Blocks of one level with different children,
   factors that skip a level, or trees that split and merge the state.
   For independent sub-chains the bound follows from the tensor-product
   argument, but this is not stated or checked here.
6. **Other local maps or terminal restrictions.** For example v5's
   determinant splits, larger-child maps, or a terminal restriction of
   \(Q_{r,b}\) to \(\MM_N\) with \(N>\max(r,b)^2\). Combinations with
   other schemes (for example, v5's flows) are also outside.
7. **The field.** The bound concerns counts only and is
   field-independent. The schemes themselves use rational separators and
   interpolation (characteristic zero, or large enough fields).

## 8. Problems found and fixes

| Severity | Problem | Fix |
| --- | --- | --- |
| minor | The exponent is defined with a ceiling, unlike v5's pooled exponent. | State the theorem for the pooled exponent; the ceiling version follows. |
| minor | The cutoff \(2^{-40}\) is inherited and is much stronger than needed. | Use \(\varepsilon<1/36864\) (constant \(10^{-7}\)), or \(\varepsilon\le2^{-14}\) with \(10^{-6}\). |
| minor | The gap is weakened from \(1/(96d^2)\) to \(1/(192d^2)\) for no reason. | Use \(1/(24q^2)\ge1/(96d^2)\). |
| minor | Redundant hypotheses: \(c<b\), "complete" types, \(n_ik_i\mid P\), "pooling ceiling" in the class list. | Drop them, and use the block definition (Section 2.3). |
| minor | The scope wording "variable local inventories ... does not cover every possible inventory scheme" is vague. | Use the explicit block partition plus the list in Section 7. |

No fatal or major problem was found.

## 9. Recommendation for the paper

Write a section or appendix titled "A matching lower bound within the
construction", about 3.5–4 pages:

1. **Definition** of the class (Section 2.3), with the count formula
   (2.3) and the list of what is fixed. About 0.75 page. Cite v5 for
   \(Q_{r,b}\), relative schemes, exactification, and pooled recursion.
2. **Lemma 1 and Lemma 2** (quadratic potential and endpoint
   inequality). About 0.6 page. Give the identity with the explicit
   factor \(f_d(\lambda)/q\cdot[\dots]\) and the eleven coefficients in a
   footnote or table.
3. **Lemma 3** (gap \(1/(24q^2)\)). About 0.3 page.
4. **Lemma 4** (type counts (a)–(d)). About 0.75 page. Part (d) is the
   only Stirling-type estimate.
5. **Theorem 5** with the five-step proof. About 1 page.
6. **Corollaries 6–7, Remark 8**, and a scope paragraph condensed from
   Section 7. About 0.5 page.

A shorter alternative: drop Lemma 4(d) and use only \(D\ge\log2\). This
gives \(\log A\gtrsim\varepsilon^{-9/2}\log^2(1/\varepsilon)\) and saves
about half a page, but the bound no longer matches the upper bound. I
recommend the full \(\log^3\) version, since 4(d) is short.

State the theorem as \(10^{-6}\), \(\varepsilon\le2^{-14}\), or simply
"an absolute constant \(c>0\) (one may take \(10^{-6}\))".

## 10. Numerical checks

Run:

```sh
python -I experiments/shifted_chains_check_lower.py
```

It takes about 10 seconds and uses no floating point in any check. It
verifies:

- **Algebra.** The quadratic-potential identity as a polynomial identity
  in \(\mathbb Z[q,\lambda,R,B]\); the gap identity in \(\mathbb Z[z]\);
  the eleven terminal coefficients; the start inequality.
- **Geometry.** 96,310 legal steps (\(d=1..12\), entries \(\le24\), both
  orientations, every crop) and 9,936 prefixes of random mixed-arity
  chains with swaps, child crops, and free crops. Each uses rational
  enclosures of \(\lambda_d\).
- **Type lemmas.** Exhaustive for \(n\le30\), \(2\le d\le64\) (1,890
  pairs). The modal bound and mode inequalities hold for 2,537 larger
  \((n,d)\) with \(n\ge2q\).
- **Analysis.** Factorial bounds for \(u\le400\). The gap
  \(\omega_d-9/4\ge1/(24q^2)\) for all \(d\le59\) and a sample up to 400.
- **Constants.** Every threshold and coefficient in Section 5.
- **Block counts.** Common batch, replication, and joint exactification
  equal to a larger \(k\).
- **End to end.** For the four ramp certificates of
  `docs/round11-arity-ramp.md` (\(D=2,4,8,16\), up to 3,454 levels and
  \(n=32768\)), and for one heterogeneous-block schedule, the script
  computes the pooled exponent \(p\) with rational log intervals. It sets
  \(p_0\) just above \(p\) and checks:
  - the endpoint inequality;
  - \(\sum w\,t>3\log K\);
  - every implication of Step 3 for each certified profitable block.

  The pooled exponents (2.33713, 2.28818, 2.26771, 2.26011) agree with the
  ramp table's ceiling-inclusive bounds.

## 11. What I did not verify

- The existence and exact counts of the stage relation (2.2): the
  shifted-chain maps, the cropped reset, and the paired orientation
  bookkeeping. These are taken from `docs/round8-multiscale-construction.md`.
  I only checked consistency with v5's separator, exactification, and
  tripling geometry.
- The matching upper bound of `docs/round11-ramp-bounds.md`.
- The fixed-arity \(\log^4\) theorem of round 10, specifically its
  integer-boundary argument via \(\kappa_j\). The variable-arity proof
  does not use it.
- Whether the variants listed in Section 7 obey the same order. That
  remains open.

## Adversarial review

Reviewer role: adversarial referee for topic `lower`. Date: 18 October 2026.
New file: [`experiments/shifted_chains_skeptic_lower.py`](../experiments/shifted_chains_skeptic_lower.py)
(run `python -I experiments/shifted_chains_skeptic_lower.py`, about 13
seconds, exact integers, Fractions and outward-rounded rational log
intervals; floats only in printed summaries). It imports nothing from the
checker's script or from earlier rounds. I also reran the checker's script
(all checks pass, about 13 s) and `tests/test_round11_variable_arity_bound.py`
(6 passed). Nothing above this section was changed.

### R.1 Verdict

The mathematics of Lemmas 1–4, Theorem 5, Corollaries 6–7 and Remark 8(b),(c)
is correct **for the class exactly as Section 2.3 defines it**, including the
constants and the allowance ranges. I re-derived each step myself (R.2).

There is one **major** problem, which the checker, the round-11 note and its
review all missed. The class charges every level's auxiliary
\(\MM_{d_i^{2n_{ij}k_{ij}}}\) to the source \(\MM_A\). This is an accounting
convention, not a property of the maps. Because the levels are exactified
separately and run in sequence, the matrix-multiplication factor
\(\MM_{M^{2k}}\) produced by one level is available before the next level
needs its auxiliary, and it can supply that auxiliary by restriction
("forward recycling", R.3). This changes no map, type, separator, source
evaluation, or exactification, and leaves \(r_*\), \(m_*\) and \(B/A\)
unchanged up to a factor \(1-O(L2^{-X})\). It reduces \(\log A\) from
\(2P\sum_i\log d_i\) to about \(2P\log d_1\). On the four round-11 ramp
certificates, recycling cuts \(\log A\) by factors of 226 to 3,655 while
raising the pooled exponent by less than \(10^{-26}\). For the
round11-ramp-bounds schedule, the recycled scheme has \(\log A\) below
\(10^{-7}\varepsilon^{-9/2}\log^3(1/\varepsilon)\) for every \(\varepsilon\le2^{-40}\).
That is the notes' own range. This last statement is conditional on the
exponent theorem of round11-ramp-bounds, which the `upper` checker endorsed
and I did not re-derive.

So Theorem 5 is a true statement about one accounting convention. It is
not a lower bound for "uncompressed paired shifted chains with full source
evaluation and separate exactification" as described in words. The
checker's framing ("matching lower bound within the construction",
"\(\Theta(\varepsilon^{-9/2}\log^3)\) is tight within the class") would mislead
readers unless the convention is stated as a hypothesis. Section R.4 gives
a bound that does not depend on the convention:
\(\log B\ge\log(B/A)>9.8\cdot10^{-5}\varepsilon^{-4}\log^2(1/\varepsilon)\).
It holds with or without recycling, and the recycled ramp matches its order.

Overall: confirmed with corrections (one major, four minor).

### R.2 What I re-derived independently

All items below are **proved here**. The script checks are regression
checks of the proofs, not their basis.

- **Lemma 1.** I re-derived the identity by hand and verified it by a
  different method from the checker's symbolic expansion.
  \(q^3\times\)(defect) is a polynomial with degree at most 3 in \(q\), 4 in
  \(\lambda\), and 2 in each of \(R\) and \(B\). It vanishes on a
  \(6\times6\times6\times6\) product grid, so it is identically zero. The crop
  equivalence \((d+2)c\le db-r+1\iff qC\le dB-R\) holds because
  \((q-d)/3+1/3=1\). It was also checked exhaustively for small entries.
  \(\lambda<1-1/q\) follows from \(f(1-1/q)=1\).
- **Lemma 2.** The start bound \(9s^2-12s-2=(s-2)(9s+6)+10\) and the end
  value \(\Phi(1,t)^2=\frac49(t^2+2t-\frac13)\) are correct. I recomputed the
  eleven coefficients with my own polynomial code; all are positive, and
  the smallest is about 0.0173. As an extra check, I ran an **exhaustive**
  dynamic programme over every chain whose entries are at most 60. It
  covers all arities \(d\ge1\) (using the fact that the worst arity for a
  step is the smallest legal one, since \(\lambda_d\) increases with \(d\)),
  every legal child, input swaps, free crops and every terminal
  \(t\le\max\). It confirms \(s\prod\lambda_i\ge Kt^{4/5}\) at all 1,829
  starting pairs that admit a step. The tightest case is
  \((2,2)\to(1,2)\) at \(d=3\), stopping with \(t=2\), with slack factor
  \(1.118\).
- **Lemma 3.** I verified the identity \((1-z^4)f(z^3)=z^3(1-z)^2(1-z^2)\)
  with \(q=2/(1-z^4)\), and re-derived the chain
  \(\omega-\frac94\ge3(1-z)^2/((1+z^2)(2q+1)g)\ge1/(24q^2)\). It uses
  \(1-z\ge(1-z^4)/4=1/(2q)\), \(2q+1\le9d/2\) for \(d\ge2\), and
  \(g\le2/d\).
- **Lemma 4.** (a) Multinomial sum. (b) The \(n=1,2\) enumeration and the
  \(d\ge2n+1\) bound. (c) The interior binomial mode with neighbour-ratio
  product at least \(1/4\). (d) The one-ball move inequalities
  \(a_i\ge(n+1)p_i-1\), the Stirling bounds and Gibbs' inequality. All four
  are correct. They were checked exhaustively for \(n\le40\), \(d\le90\)
  (3,560 pairs, exact maximum over all types), and for (d) also at 30
  larger \((n,d)\) with \(n\le240\). The script also proves that the
  marginal-greedy mode equals the exhaustive maximum on that range, and
  that \(\max M\ge q^n/(n+1)^2\).
- **Theorem 5, Steps 1–5.** The normalization with weights
  \(w_{ij}=n_{ij}k_{ij}/P\) is exact. Step 2 needs \(p_0\le12/5\) and
  \(t\ge1\). Each implication in Step 3 holds, with the thresholds
  \(\varepsilon\le9/64\) (\(n>4d\ge2q\)), \(\varepsilon\le9/16384\)
  (\(\log(3/(128\varepsilon))\ge x/2\)) and \(\varepsilon<1/9216\)
  (\(\log D_0>x/4\)). Step 4 uses \(\sum_jw_{ij}\le1\). The constant in
  Step 5 is \(2\cdot\frac9{16}\cdot\frac1{16}\cdot\frac38=\frac{27}{1024}\).
  The rational bounds \(27/(21\cdot1024\cdot960)>10^{-6}\) (using
  \(96^3<960^2\)) and \(27/(21\cdot1024\cdot2688)>10^{-7}\) (using
  \(192^3<2688^2\)) were rechecked.
- **Corollaries 6 and 7.** The replication counts are correct, and so is
  the contradiction argument with \(p_0=\min(\min_i\omega_{d_i},12/5)\).
- **v5 consistency.** v5 defines the pooled exponent without a ceiling
  (`def:relative-scheme`). Lemma `lem:exactification` gives \(E=kD+1\) with
  \(D=6(M-1)\). Lü's separator (`rem:polynomial-separator`) uses \(2M-1\)
  copies with degree \(M-1\). The tripling relation
  (`eq:tripling-relation`) consumes no auxiliary, consistent with Remark
  8(a).

### R.3 Major: forward recycling of produced auxiliaries

**Lemma R (forward recycling; proved here).** Take a scheme of
Section 2.3 with levels \(i=1,\dots,L\). Put \(U_i=d_i^{2P}\), the auxiliary
side the level consumes, and \(V_i=\prod_jM_{ij}^{2k_{ij}}\), the auxiliary
side it produces. For a positive integer \(S\), set \(\beta_0=S\) and
\(\beta_i=\lfloor\beta_{i-1}/U_i\rfloor V_i\), and assume
\(\beta_{i-1}\ge U_i\) for all \(i\). Then
\[
 r_*\,\MM_S\ \restr\ m_*\,\MM_{t^{2P}\beta_L},
\]
with the same \(r_*\) and \(m_*\) as in (2.3). Write \(A'=S\) and
\(B'=t^{2P}\beta_L\). Then \(B'/A'\le B/A\). If moreover
\(\beta_{i-1}\ge2^XU_i\) for all \(i\), then
\(\log(B'/A')\ge\log(B/A)-L\,2^{1-X}\).

*Proof.* Induction over the levels. After the source and levels
\(1,\dots,i\), we hold \(\prod_{l>i}X_l\prod_{l\le i}Y_l\) copies of
\(Q_{\pi_i}^{\otimes P}\MM_{\beta_i}\). Here
\(X_l=\prod_jE_{lj}(2M_{lj}-1)^{6k_{lj}}\) and
\(Y_l=\prod_jM_{lj}^{6k_{lj}}\) are the copy counts of level \(l\). For the
next level, restrict \(\MM_{\beta_{i-1}}\) to a principal block of side
\(U_i\lfloor\beta_{i-1}/U_i\rfloor\), which is isomorphic to
\(\MM_{U_i}\otimes\MM_{\lfloor\beta_{i-1}/U_i\rfloor}\) (v5,
`eq:matrix-products`). Then apply the exact (already exactified)
restriction of level \(i\), tensored with the identity on the second
factor. Its output factor is
\(\MM_{V_i}\otimes\MM_{\lfloor\beta_{i-1}/U_i\rfloor}\cong\MM_{\beta_i}\).
Restrictions compose and commute with tensoring by a fixed tensor, and
multiplicities multiply exactly as in the class. Crops and the terminal
projection are unchanged. For the ratio, \(\lfloor y\rfloor\le y\), and
\(\lfloor y\rfloor\ge y(1-1/y)\) with \(-\log(1-u)\le2u\) for \(u\le1/2\).
\(\square\)

No step composes degenerations or shares a parameter. Recycling is
acyclic, so it is not a catalyst. The auxiliary of every level still has
its full side \(d^{2n}\). It is simply supplied by an earlier level
instead of by the source. v5 cannot do this, because its catalytic
degeneration runs all relations in parallel with one parameter. The chain
can, because its levels run in sequence.

**Effect on the finite certificates (checked numerically, exact
intervals).** These are the four ramp certificates of
`round11-arity-ramp.md`. They use the class counts (2.3) and the recycled
counts with \(S=2^{X+1}d_1^{2P}\), where \(X\) is 64 plus the bit length of
the number of levels. The script verifies \(\beta_{i-1}\ge2^XU_i\) at every level.

| D | Levels | Pooled \(p\) below | Digits of \(A\) (class) | Digits of \(A'\) (recycled) | \(\log A/\log A'\) | Increase of \(p\) below |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 130 | 2.3371326 | 17,857,969 | 78,936 | 226 | \(10^{-26}\) |
| 4 | 462 | 2.2881850 | 1,416,018,955 | 2,525,245 | 561 | \(10^{-27}\) |
| 8 | 1,726 | 2.2677061 | 112,670,650,787 | 60,605,366 | 1,859 | \(10^{-29}\) |
| 16 | 3,454 | 2.2601118 | 4,724,998,039,558 | 1,292,914,010 | 3,655 | \(10^{-30}\) |

A fully exact big-integer instance (ramp \(D=2\), \(L=20\), \(n=200\),
\(k=2\), 50 levels, with the floors computed exactly) cuts \(A\) from
35,233 to 253 decimal digits. It verifies
\(B'A\le BA'\) and \(B'A\,2^X\ge BA'(2^X-L)\).

**Effect on the uniform schedule (conditional).** Take the parameter
schedule (6) of `round11-ramp-bounds.md`, with \(D\), \(L\), \(n=k\), exact
mode types, and \(X\) equal to 64 plus the bit lengths of the number of
levels \(J\) and of \(1/\varepsilon\).
The script proves, in exact arithmetic and using only
\(M_i\ge q_i^n/(n+1)^2\), two facts. First, every level multiplies the bank
by more than \(e(1-2^{-X})\): \(2k(ng_{24D}-2\log(n+1))>1\), and all
arities are below \(24D\). Second, the \(L\) bulk levels pay for the jump
from arity \(D\) to the first ramp arity \(24D-3\). After the jump, the
ramp arities decrease, so \(S=2^{X+1}D^{2nk}\) funds every level.
Recycling raises the exponent by less than \(\varepsilon/2^{60}\). If the
exponent theorem of round11-ramp-bounds holds (\(p<9/4+\varepsilon/2\);
endorsed in `shifted-chains-check-upper.md`, not re-derived by me), the
recycled scheme has \(p<9/4+\varepsilon\) and
\[
 \log A'\le(X+1)\log2+2nk\log D\le 1.1\cdot10^{7}\,\varepsilon^{-3}\log^3(4096/\varepsilon)
\]
(the last step uses the round11-ramp-bounds estimates
\(n=k\le2305\varepsilon^{-3/2}\Lambda\) and \(\log D\le\Lambda\)). Here
\(b_7\) denotes the round-11 bound value
\(10^{-7}\varepsilon^{-9/2}\log^3(1/\varepsilon)\), and
\(\rho=(45/458752)\,\varepsilon^{-4}\log^2(1/\varepsilon)\) is the
recycling-invariant lower bound of R.4.

| \(\varepsilon\) | \(\log A'\) recycled | \(\log A'/b_7\) | class \(\log A/b_7\) | \(\log B'/b_7\) | \(\log B'/\rho\) |
|---|---:|---:|---:|---:|---:|
| \(2^{-40}\) | \(4.8\cdot10^{46}\) | \(1.5\cdot10^{-5}\) | \(2.2\cdot10^{15}\) | \(1.4\cdot10^{8}\) | \(4.2\cdot10^{12}\) |
| \(2^{-60}\) | \(1.7\cdot10^{65}\) | \(1.2\cdot10^{-14}\) | \(2.0\cdot10^{15}\) | \(8.5\cdot10^{4}\) | \(3.9\cdot10^{12}\) |
| \(2^{-80}\) | \(4.4\cdot10^{83}\) | \(1.1\cdot10^{-23}\) | \(1.9\cdot10^{15}\) | 60 | \(3.7\cdot10^{12}\) |
| \(2^{-120}\) | \(1.9\cdot10^{120}\) | \(9.0\cdot10^{-42}\) | \(1.8\cdot10^{15}\) | \(3.6\cdot10^{-5}\) | \(3.5\cdot10^{12}\) |
| \(2^{-160}\) | \(5.7\cdot10^{156}\) | \(7.6\cdot10^{-60}\) | \(1.7\cdot10^{15}\) | \(2.5\cdot10^{-11}\) | \(3.4\cdot10^{12}\) |

Thus, for \(\varepsilon\le2^{-40}\), the recycled ramp contradicts the
round-11 bound (1) read for the framework as described in words. The
bound survives only because (2.3) fixes \(A=\prod_id_i^{2P}\). Recycling also
improves the target side asymptotically: \(\log B'=O(\varepsilon^{-4}\log^2)\),
against \(\log B\ge\log A=\Omega(\varepsilon^{-9/2}\log^3)\) in the class.
With the ramp's large constants, however, the crossover lies between
\(2^{-80}\) and \(2^{-120}\). The last column is roughly constant, which is
consistent with \(\log B'=\Theta(\varepsilon^{-4}\log^2(1/\varepsilon))\).

**Lower bound that survives recycling for \(A\) (proved here).** If the first
level has \(d_1\ge2\), then \(A'\ge U_1=d_1^{2P}\). With \(P>3x^2/(8192\varepsilon^3)\)
(Theorem 5(2); it still applies because \(p\le p'\)), this gives
\(\log A'>(3\log2/4096)\,\varepsilon^{-3}x^2\). If a tripling level (\(d=1\),
which consumes no auxiliary; v5 `eq:tripling-relation`) starts the chain,
then \(U_1=1\), and \(A'\) might even be 1. I did not check that such a
bootstrap keeps \(p<9/4+\varepsilon\). Either way, a lower bound on \(A\)
alone mainly measures the accounting choice.

**Fix.** (i) Make the convention an explicit, named hypothesis of the
class, for example "(H\(_{\rm src}\)) every level's auxiliary is a tensor
factor of the source \(\MM_A\)", and put forward recycling first in the
exclusion list of Section 7. (ii) Do not call Theorem 5 a "matching lower
bound within the construction" without that qualifier. (iii) State the
recycling-invariant bound of R.4 next to it. (iv) Consider building
recycling into the construction itself. It costs nothing and improves the
proved resources to \(\log A'=O(\varepsilon^{-3}\log^3)\) and
\(\log B'=O(\varepsilon^{-4}\log^2)\), conditional only on the existing
ramp upper bound. Report both \(A\) and \(B\). In v5's pooled recursion,
one level of recursion cuts the matrices into a \(B\times B\) array of
blocks, so \(B\) sets the size scale.

### R.4 A recycling-invariant resource bound (proved here)

**Proposition T.** Let \(0<\varepsilon\le2^{-14}\) and
\(x=\log(1/\varepsilon)\). Let a scheme of Section 2.3 have \(B>A\) and pooled
exponent \(p<9/4+\varepsilon\). Then

1. \(\sum_ig_{d_i}>3\log K/\varepsilon\);
2. \(\log s>9\log K/(4\varepsilon)\);
3. \(\log B\ge\log(B/A)>\frac{45}{8}\,P\log K/\varepsilon
   >\frac{405\log K}{196608}\,\varepsilon^{-4}x^2>9.8\cdot10^{-5}\,
   \varepsilon^{-4}\log^2(1/\varepsilon)\).

The same bound on \(\log(B'/A')\), and hence on \(\log B'\), holds for every
forward-recycled variant (Lemma R) whose pooled exponent is below
\(9/4+\varepsilon\).

*Proof.* (1) Step 2 gives \(\sum w_{ij}t_{ij}>3\log K\). Every block has
\(t_{ij}\le(p_0-\omega_{d_i})g_i<\varepsilon g_i\), because
\(\omega_{d_i}>9/4\). Also \(\sum_jw_{ij}=1\). (2) Lemma 2 gives
\(\log s\ge\sum_ia_{d_i}\), and \(a_d=\omega_dg_d/3>\frac34g_d\). (3) All
factors of \(r_*/m_*\) other than \(s^{6P}\) are at least 1, so
\(\log(r_*/m_*)\ge6P\log s\). From \(p<p_0\le12/5\),
\(\log(B/A)>\log(r_*/m_*)/p_0\ge\frac52P\log s\). Combine this with (2), and
then with \(P\ge nk>9D_0^2x^2/(256\varepsilon^2)=9x^2/(24576\varepsilon^3)\)
(Theorem 5(2)) and \(\log K>1/21\). For a recycled variant, \(r_*\),
\(m_*\), \(s\) and \(P\) are the same and \(B'/A'\le B/A\), so \(p\le p'\).
Hence (1)–(3) hold for the underlying class scheme, and
\(\log(B'/A')=\log(r_*/m_*)/p'>\log(r_*/m_*)/p_0\). \(\square\)

The rational constants are checked in the script
(\(405/(196608\cdot21)=45/458752>9.8\cdot10^{-5}\)). The table in R.3 shows
that the recycled ramp stays within a factor of about \(4\cdot10^{12}\) of
this bound for \(\varepsilon\) from \(2^{-40}\) to \(2^{-160}\). The order
\(\varepsilon^{-4}\log^2(1/\varepsilon)\) is therefore attained (conditional
on round11-ramp-bounds).

### R.5 Minor issues

1. **Joint exactification within a level.** Section 7 says "Exactification
   inside a level is covered". The checker justifies this only for
   replicated *identical* blocks (the block \((n,kJ)\)). For unequal blocks
   exactified together, \(E_i=1+\sum_j6k_{ij}(M_{ij}-1)\) is not of the form
   (2.3). The claim is still true, with the same constant, by a level-wise
   version of the proof. Put
   \(T_i=\sum_jw_{ij}[(p_0-\omega_i)g_i-p_0D_{ij}/n_{ij}]-\log E_i/(2P)\).
   Then \(\sum_iT_i>3\log K\). If \(T_i>0\), some block has
   \((p_0-\omega_i)g_i>p_0D_{ij}/n_{ij}\), so Step 3 gives
   \(d_i>D_0\) and \(n_{ij}>9d_ix/(16\varepsilon)\). Moreover
   \(\log E_i/(2P)<\varepsilon g_i\) with \(E_i\ge M_{ij}>d_i^{n_{ij}}\), so
   \(P>n_{ij}d_i\log d_i/(4\varepsilon)\), which is all Step 5 uses. Step 4
   applies with \(T_i<\varepsilon g_i\). This argument should replace the
   one-line remark.
2. **Obs 9 overstates.** The end-to-end checks run at
   \(\varepsilon=p_0-9/4\approx0.01\)–\(0.09\), far above \(2^{-14}\). They
   skip the Step-3 implications that need \(\varepsilon\le9/16384\) or
   \(\varepsilon<1/9216\), namely \(D>x/2\), \(n>9dx/(16\varepsilon)\) and
   \(\log D_0>x/4\). They test the bookkeeping of the count formula and
   Lemma 2 on real chains, not "every Step-3 implication". Reword.
3. **"Exact value 3/6422528"** (Section 4, last row) is a rational *lower
   bound* \(27/(21\cdot1024\cdot2688)\). The exact coefficient is
   \(27\log(21/20)/(1024\cdot192^{3/2})\approx4.84\cdot10^{-7}\).
4. **Tightness wording.** "\(\Theta(\varepsilon^{-9/2}\log^3)\) is tight
   within the class" is conditional on round11-ramp-bounds. Per R.3, it is
   specific to (H\(_{\rm src}\)). Say both.

### R.6 Statements I endorse

- **Theorem 5, Corollaries 6–7, Remark 8(b),(c)**, as stated by the checker,
  for the class of Section 2.3 with hypothesis (H\(_{\rm src}\)) made
  explicit. The class also covers joint exactification of unequal blocks
  within a level (R.5.1). Recommended form: \(\log A>10^{-6}\varepsilon^{-9/2}
  \log^3(1/\varepsilon)\) for \(0<\varepsilon\le2^{-14}\), together with the
  parameter bounds \(\max d>D_0\), \(n>9D_0x/(16\varepsilon)\),
  \(k>D_0x/(16\varepsilon)\), \(\sum\log d>(3\log K/8\varepsilon)D_0x\).
  The round-11 form (\(10^{-7}\), \(\varepsilon<1/36864\)) is also correct.
- **Lemma R** (forward recycling) and **Proposition T** (R.4), proved here.
  Proposition T is the resource statement that does not depend on the
  accounting convention.
- **Corollary 7** also holds for recycled variants, since \(p'\ge p\).
- **Conditional (on round11-ramp-bounds):** the recycled ramp has
  \(p<9/4+\varepsilon\), \(\log A'=O(\varepsilon^{-3}\log^3(1/\varepsilon))\) and
  \(\log B'=\Theta(\varepsilon^{-4}\log^2(1/\varepsilon))\) within the class
  plus recycling. In particular, (H\(_{\rm src}\)) is necessary for Theorem 5
  for every \(\varepsilon\le2^{-40}\).

For the paper, I recommend presenting Proposition T as the main resource
lower bound. Theorem 5 can be kept as the statement for the
(H\(_{\rm src}\)) accounting, with Lemma R as a remark that explains why that
hypothesis matters. Alternatively, build recycling into the construction
and present Proposition T as the matching bound for \(B\).

### R.7 Not verified here

- The stage relation (2.2) itself (map topic), as in the checker's note.
- The exponent theorem of round11-ramp-bounds. The conditional statements
  in R.3 and R.6 rely on it; I only checked the self-financing inequalities
  that recycling needs.
- Whether a tripling (\(d=1\)) bootstrap can make \(A'=1\) while keeping
  \(p<9/4+\varepsilon\).
- Lower bounds for the other exclusions of Section 7 (compressed
  auxiliaries, cheaper sources, heterogeneous states, other maps).
