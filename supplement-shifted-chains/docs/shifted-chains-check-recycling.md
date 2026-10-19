# Verification note: forward recycling and accounting-invariant lower bounds

Topic key: `recycling`. Date: 18 October 2026.

This note resolves the accounting issue raised in the adversarial review of
[shifted-chains-check-lower](shifted-chains-check-lower.md) (sections R.3 and
R.4). It re-derives forward recycling as a restriction in v5's sense, re-derives
the recycling-invariant bound on \(\log(B/A)\), proves a new lower bound on the
copy counts that holds for every way of supplying the auxiliaries, bounds the
main construction and its recycled version, and recommends the statements for
Section 7 of the paper.

Sources read: the paper brief
([shifted-chains-paper-brief](shifted-chains-paper-brief.md)); the notes
[shifted-chains-check-lower](shifted-chains-check-lower.md),
[shifted-chains-check-maps](shifted-chains-check-maps.md),
[shifted-chains-check-upper](shifted-chains-check-upper.md),
[shifted-chains-check-seeds](shifted-chains-check-seeds.md) (Lemma 1) and
[shifted-chains-check-gate](shifted-chains-check-gate.md) (statement only), each
with its adversarial review; v5 `manuscript/preliminaries.tex`,
`manuscript/algorithm-bounds.tex` (Lemma 9.1) and `manuscript/build/main.aux`
for the numbering.

New files: this note and
[`experiments/shifted_chains_check_recycling.py`](../experiments/shifted_chains_check_recycling.py).
No other file was changed.

Status labels:

- **proved here**: I re-derived the statement and give a complete proof.
- **checked**: confirmed by the script with exact integers, Fractions or
  outward-rounded rational log intervals.
- **conditional**: proved here from the main theorem of
  [shifted-chains-check-upper](shifted-chains-check-upper.md) (Section 5, endorsed
  by its adversarial review), which I did not re-derive.

v5 numbers used (from `manuscript/build/main.aux`): (2.1)
`eq:matrix-products` \(\MM_d\MM_{d'}\cong\MM_{dd'}\); (2.6)
`eq:cyclic-identities`; (2.7)–(2.8) \(Q_{r,b}\); Definition 2.3 (relative
scheme, pooled exponent); Lemma 9.1 (rational interpolation); (3.6)
`eq:profile-upper`.

## 1. Verdict

1. **Lemma R is correct** (proved here). It is a special case of a *supply
   lemma*: for every way of cutting each stage's auxiliary out of a single
   matrix multiplication factor (the "bank"), which starts as the source factor
   \(\MM_S\) and absorbs every produced factor, the chain gives the restriction
   \(r_*\MM_S\restr m_*\MM_{B'}\) over \(\Q\), with the same \(r_*\) and \(m_*\)
   as Proposition E, and \(B'/S\le\bar B/\bar A\). The proof uses only
   Corollary D′ tensored with identities, principal sub-blocks of \(\MM\) and
   v5 (2.1). The floor losses are exactly as in R.3. I add a simple sufficient
   funding condition: if \(S\ge4J\max_iU_i\prod_{l<i}U_l/V_l\), then every
   stage is funded and \(B'/S\ge\bar B/(2\bar A)\).
2. **Proposition T is correct** (proved here):
   \(\log(B'/S)>\frac{45}{458752}\varepsilon^{-4}\log^2(1/\varepsilon)\) for every
   scheme of the class with any supply and pooled exponent at most
   \(9/4+\varepsilon\). The range is \(0<\varepsilon<1/9216\). The review's
   \(\varepsilon\le2^{-14}\) lies inside this range. A range-free intermediate
   form, \(\log(B'/S)\ge\frac52P\log s>\frac{45\log(21/20)}{8}\,P/\varepsilon\),
   holds for every \(\varepsilon\le3/20\).
3. **The copy counts obey the full \(\varepsilon^{-9/2}\log^3\) bound for every
   supply** (new; proved here). For \(0<\varepsilon<1/9216\), every scheme of
   the class, recycled or not, with pooled exponent at most \(9/4+\varepsilon\)
   satisfies
   \[
   \log r_*>\log m_*\ \ge\ 3\log\bar A\ >\ \frac{81\log(21/20)}{1024\cdot96^{3/2}}\,
   \varepsilon^{-9/2}x^3\ >\ 3.9\cdot10^{-6}\,\varepsilon^{-9/2}x^3,
   \qquad x=\log(1/\varepsilon).
   \]
   Here \(\bar A=\prod_id_i^{2P}\) is the total auxiliary side *consumed* by the
   stages. It is fixed by the chain data, and it equals the source side only
   under the source supply. Theorem 5 of the lower note is, in fact, a bound on
   \(\bar A\). Two proofs are given: the profitable-block sum of Theorem 5's
   Step 4, which \(m_*\) dominates, and the two-line inequality
   \(m_*\ge\bar A^3(s/t)^{6P}\), valid whenever the pooled exponent is at most
   3.
4. **Main construction** (proved here from the verified resource relations).
   Its copy counts satisfy \(\log m_*\le6\log A\) and
   \(\log r_*\le\frac{35}4\log A\), so
   \(\log m_*<1.54\cdot10^{10}\varepsilon^{-9/2}\Lambda^3\) and
   \(\log r_*<2.24\cdot10^{10}\varepsilon^{-9/2}\Lambda^3\), with
   \(\Lambda=\log(4096/\varepsilon)\). With item 3, the copy-count order within
   the construction is \(\Theta(\varepsilon^{-9/2}\log^3(1/\varepsilon))\).
   Its recycled version (bank source \(S=4JD^{2nk}\)) has the same \(r_*\) and
   \(m_*\), \(9/4<p'<9/4+\varepsilon/2\),
   \(\log A'=\log S<5.32\cdot10^6\varepsilon^{-3}\Lambda^3\) and
   \(\log B'<1.5\cdot10^9\varepsilon^{-4}\Lambda^2\) (conditional). So
   \(\log(B/A)\) has order \(\Theta(\varepsilon^{-4}\log^2)\) within the class,
   and the source side under the best supply lies between
   \(5\cdot10^{-4}\varepsilon^{-3}x^2\) and \(O(\varepsilon^{-3}\log^3)\).
5. **Recommendation** (Section 6). State the class with an explicit *supply*;
   state the lower bound on \(r_*\), \(m_*\) and \(\log(B/A)\) for every
   supply, and on the source side only under the source supply; state the
   supply lemma and the recycled main construction as a corollary. Present
   the bound on \(m_*\) as the robust "resource order is optimal" statement.
   The source-supply hypothesis cannot be dropped from the source-side bound:
   for \(\varepsilon\le2^{-26}\), the recycled main construction has a source
   side below that bound (conditional).

No error was found in R.3 or R.4. One correction: R.4 states its range as
\(\varepsilon\le2^{-14}\), but the proof needs only \(\varepsilon<1/9216\).
Several notation clashes with the brief must be fixed in the paper
(Section 8).

## 2. The class, with explicit accounting

### 2.1 Stage relation

I use Corollary D′ of [shifted-chains-check-maps](shifted-chains-check-maps.md)
(proved there and endorsed by its review). For a legal step \((r,b)\to(c,r)\)
at arity \(d\ge2\), that is \(r\ge1\), \(c\ge1\) and \((d+2)c\le db-r+1\)
(which implies \(c<b\)), for every width \(n\ge1\), type \(\tau\) of width
\(n\) with sector count \(M\), and power \(k\ge1\), over \(\Q\):
\[
E\,(2M-1)^{6k}\,Q_{r,b}^{\otimes nk}\,\MM_{d^{2nk}}\ \restr\
M^{6k}\,Q_{c,r}^{\otimes nk}\,\MM_{M^{2k}},\qquad E=1+6k(M-1).
\tag{D′}
\]

### 2.2 Chain data (the class of the lower note, Section 2.3)

- Integers \(J\ge1\) (stages) and \(P\ge1\) (global power).
- Pairs \(\pi_0,\dots,\pi_J\) of positive integers and arities \(d_i\ge2\).
  For each \(i\), after ordering \(\pi_{i-1}=(r,b)\) suitably, there is a
  legal child \(c\), and \(\pi_i\) is \((c,r)\) followed by an optional crop
  of each entry and an optional swap.
- For each stage \(i\), blocks \(j\) with width \(n_{ij}\), power \(k_{ij}\),
  type \(\tau_{ij}\) of width \(n_{ij}\) and sector count \(M_{ij}\ge1\), with
  \(\sum_jn_{ij}k_{ij}=P\). Put \(w_{ij}=n_{ij}k_{ij}/P\) and
  \(E_{ij}=1+6k_{ij}(M_{ij}-1)\).
- A terminal \(t\) with \(1\le t\le\max\pi_J\).

Counts:
\[
s=r_0+b_0-1,\quad U_i=d_i^{2P},\quad V_i=\prod_jM_{ij}^{2k_{ij}},\quad
X_i=\prod_jE_{ij}(2M_{ij}-1)^{6k_{ij}},\quad Y_i=\prod_jM_{ij}^{6k_{ij}},
\]
\[
\bar A=\prod_iU_i,\qquad \bar B=t^{2P}\prod_iV_i,\qquad
r_*=s^{6P}\prod_iX_i,\qquad m_*=\prod_iY_i=\Bigl(\prod_iV_i\Bigr)^3 .
\]
\(U_i\) is the auxiliary side that stage \(i\) consumes, and \(V_i\) the side it
produces. \(\bar A\) and \(\bar B\) are the source and target sides of
Proposition E and of the lower note's (2.3). Note the identity
\(m_*=(\bar B/t^{2P})^3\).

Two geometric facts are used below (proved here). The larger entry never
increases along the chain: a legal step gives \(\max(c,r)\le\max(r,b)\)
because \(c<b\), and crops and swaps do not increase it. Hence
\(t\le\max\pi_J\le\max\pi_0\le s\). Also \(s\ge2\), because the first step
splits an entry \(b>c\ge1\). So \(r_*/m_*\ge s^{6P}\ge2^{6P}>1\).

### 2.3 Supplies

**Definition (supply).** A *supply* is a sequence of positive integers
\(S,f_1,\dots,f_J\) such that \(U_if_i\le\beta_{i-1}\) for every \(i\), where
\[
\beta_0=S,\qquad \beta_i=f_iV_i\quad(1\le i\le J).
\]
\(\beta_i\) is the side of the bank after stage \(i\). The scheme with this
supply has source side \(A'=S\) and target side \(B'=t^{2P}\beta_J\).

- The **source supply** is \(S=\bar A\),
  \(f_i=\prod_{l>i}U_l\prod_{l<i}V_l\). Then \(U_if_i=\beta_{i-1}\) exactly,
  \(\beta_J=\prod_lV_l\), and \((A',B')=(\bar A,\bar B)\). This is the
  accounting of Proposition E and of the lower note ("hypothesis
  (H\(_{\rm src}\))").
- The **recycling supply** with source \(S\) is \(f_i=\lfloor\beta_{i-1}/U_i\rfloor\)
  (Lemma R of the review). It is the largest choice at each stage.

Every other supply cuts less out of the bank. The definition covers all
mixtures: a stage that "takes its auxiliary from the source" and a stage that
"takes it from a produced factor" are both cuts of the bank.

## 3. The supply lemma (task item 1)

**Lemma S (supplies; forward recycling).** *(proved here; checked)* For every
chain scheme and every supply, over \(\Q\),
\[
r_*\,\MM_S\ \restr\ m_*\,\MM_{B'},\qquad B'=t^{2P}\beta_J .
\]
Moreover:

1. \(B'/S\le\bar B/\bar A\), with equality for the source supply.
2. For the recycling supply (assuming \(\beta_{i-1}\ge U_i\) for all \(i\)),
   \[
   \frac{B'}{S}\ \ge\ \frac{\bar B}{\bar A}\prod_{i=1}^J\Bigl(1-\frac{U_i}{\beta_{i-1}}\Bigr).
   \]
   If \(\beta_{i-1}\ge2^XU_i\) for all \(i\), with \(X\ge1\), then
   \(\log(B'/S)\ge\log(\bar B/\bar A)-J\,2^{1-X}\) (this is R.3's form).
3. (Funding.) Put \(\tilde U=\max_{1\le i\le J}U_i\prod_{l<i}(U_l/V_l)\). If
   \(S\ge4J\tilde U\), then the recycling supply has \(\beta_{i-1}\ge2JU_i\)
   for every \(i\), and \(B'/S\ge\bar B/(2\bar A)\).
4. If \(B'>S\), the restriction is a relative scheme (v5 Definition 2.3). Its
   pooled exponent \(p'=\log(r_*/m_*)/\log(B'/S)\) satisfies \(p'\ge p\), where
   \(p\) is the pooled exponent of the source supply (which is then also a
   relative scheme).

*Proof.* Restrictions compose; they survive tensoring with a fixed tensor
(tensor the leg maps with identities) and taking multiples (block-diagonal
maps); and \((mT)T'\cong m(TT')\). These facts are immediate from the
definition of restriction in v5 Section 2.1. Two further facts about
\(\MM\):

- *Principal sub-block.* For \(N'\le N\), \(\MM_N\restr\MM_{N'}\): send every
  variable with an index \(\ge N'\) to \(0\) and keep the others.
- *Splitting.* \(\MM_{Uf}\cong\MM_U\MM_f\), by v5 (2.1), with
  \(\alpha\leftrightarrow(\lfloor\alpha/f\rfloor,\alpha\bmod f)\) on every index.

*Stage relation.* Fix stage \(i\). For each block \(j\), (D′) with
\((n,k,\tau)=(n_{ij},k_{ij},\tau_{ij})\) applies to the pair
\(\pi_{i-1}\) in the order of the legal step. The swap
\(Q_{r,b}\cong Q_{b,r}\) is v5 (2.8). Tensor the block relations over \(j\).
Then use \(\prod_jQ^{\otimes n_{ij}k_{ij}}=Q^{\otimes P}\) and
\(\prod_j\MM_{d_i^{2n_{ij}k_{ij}}}\cong\MM_{U_i}\) (v5 (2.1)), and follow with
the crop \(Q_{c,r}\restr Q_{c',r'}\) for \(c'\le c\), \(r'\le r\). (A crop of
\(C(c,r)\) to \(C(c',r')\) zeroes the variables of indices at least \(c'\), \(r'\)
and \(c'+r'-1\) on the three legs; doing this in every factor crops \(Q\).) This
gives
\[
X_i\,Q_{\pi_{i-1}}^{\otimes P}\,\MM_{U_i}\ \restr\ Y_i\,Q_{\pi_i}^{\otimes P}\,\MM_{V_i}.
\tag{S\(_i\)}
\]

*Induction.* We show, for \(i=0,\dots,J\),
\[
r_*\MM_S\ \restr\ \Bigl(\prod_{l\le i}Y_l\Bigr)\Bigl(\prod_{l>i}X_l\Bigr)\,
Q_{\pi_i}^{\otimes P}\,\MM_{\beta_i}.
\tag{I\(_i\)}
\]
For \(i=0\): v5 (2.8) and Lemma 9.1(a) give \(\R(Q_{\pi_0})\le s^6\) over
\(\Q\), so \(s^{6P}\MM_1\restr Q_{\pi_0}^{\otimes P}\) (a rank decomposition
is a restriction of the unit tensor). Tensor with \(\MM_S\) and take
\(\prod_lX_l\) copies. For \(i-1\to i\): the right side of (I\(_{i-1}\)) is a
direct sum of \((\prod_{l<i}Y_l)(\prod_{l>i}X_l)\) groups, each of
\(X_i\) copies of \(Q_{\pi_{i-1}}^{\otimes P}\MM_{\beta_{i-1}}\). In every copy,
restrict \(\MM_{\beta_{i-1}}\) to its principal block of side
\(U_if_i\le\beta_{i-1}\) and split it as \(\MM_{U_i}\MM_{f_i}\); the group
becomes \((X_iQ_{\pi_{i-1}}^{\otimes P}\MM_{U_i})\MM_{f_i}\). Apply (S\(_i\)) to the
whole group, tensored with the identity on \(\MM_{f_i}\), and merge
\(\MM_{V_i}\MM_{f_i}\cong\MM_{\beta_i}\). Each group becomes
\(Y_i\,Q_{\pi_i}^{\otimes P}\MM_{\beta_i}\). This is (I\(_i\)).
At \(i=J\): \(Q_{\pi_J}\restr Q_{1,t}\) by a crop and possibly a swap, and
\(Q_{1,t}=S^+_{1,t}S^-_{1,t}\cong\MM_t\MM_t\cong\MM_{t^2}\) by v5 (2.6) and
(2.1). Hence \(Q_{\pi_J}^{\otimes P}\MM_{\beta_J}\restr\MM_{t^{2P}\beta_J}\),
and (I\(_J\)) becomes \(r_*\MM_S\restr m_*\MM_{B'}\). Every map is a
restriction with rational coefficients; no degeneration is composed, since
each stage was exactified on its own in (D′).

*Item 1.* \(\beta_i=f_iV_i\le\beta_{i-1}V_i/U_i\). By induction,
\(\beta_J\le S\prod_iV_i/U_i\), so \(B'/S\le t^{2P}\prod_iV_i/U_i=\bar B/\bar A\).
For the source supply, \(U_if_i=\beta_{i-1}\) at every stage, so equality holds.

*Item 2.* \(\lfloor y\rfloor\ge y-1=y(1-1/y)\) with \(y=\beta_{i-1}/U_i\) gives
\(\beta_i\ge(\beta_{i-1}/U_i)(1-U_i/\beta_{i-1})V_i\). Multiply over \(i\). For
the second form use \(-\log(1-u)\le2u\) for \(0\le u\le1/2\).

*Item 3.* Suppose \(\beta_{l-1}\ge2JU_l\) for all \(l<i\) (vacuous for
\(i=1\)). Item 2's per-stage bound gives
\(\beta_{i-1}\ge S\prod_{l<i}(V_l/U_l)\,(1-\frac1{2J})^{i-1}\). Bernoulli's
inequality gives \((1-\frac1{2J})^{i-1}\ge1-\frac{i-1}{2J}\ge\frac12\). Hence
\(\beta_{i-1}\ge2J\tilde U\prod_{l<i}(V_l/U_l)\ge2JU_i\) by the definition of
\(\tilde U\). The same estimate at \(i=J+1\) gives
\(\beta_J\ge\frac S2\prod_l(V_l/U_l)\), so \(B'/S\ge\bar B/(2\bar A)\).

*Item 4.* \(r_*>m_*\) (Section 2.2). If \(B'>S\), then
\(\bar B/\bar A\ge B'/S>1\), so both are relative schemes. The numerators of
\(p\) and \(p'\) are equal and positive, and the denominator of \(p'\) is at
most that of \(p\). \(\square\)

**Remarks.**

- Recycling is acyclic: the bank only carries factors forward. It is not a
  catalyst, and every auxiliary still has its full side \(d_i^{2P}\). v5 cannot
  recycle because its catalytic degeneration runs all relations in parallel
  with one parameter. The chain can, because its stages are exactified
  separately and run in sequence.
- Item 3 is the convenient form for constructions: one computes the "net
  deficit" \(\tilde U\) of the chain once, and \(S=4J\tilde U\) funds every
  stage while losing at most a factor 2 in \(B'/S\). If every stage is
  profitable (\(V_i\ge U_i\)) and the arities do not increase, then
  \(\tilde U=U_1\).
- The literal check (Part 3 of the script) builds a two-stage toy chain whose
  stages are exact restrictions of the same shape as (S\(_i\)): a crop of a
  convolution tensor tensored with copies of Strassen's restriction
  \(7\MM_U\restr\MM_{2U}\), with \(X=7\) and \(14\), \(Y=1\) and \(2\),
  \((U,V)=(2,4),(3,6)\), source \(3\MM_1\restr C(2,2)\) (v5 Lemma 9.1(a)). It
  applies the leg maps of the induction above, including principal blocks,
  splitting, identities on \(\MM_{f_i}\), copy grouping and the terminal crop,
  to the actual tensor \(r_*\MM_S\). It compares the result term by term with
  \(m_*\MM_{B'}\) for \(S=5\) (floors \(5\to4\), \(8\to6\); \(B'=12\)), \(S=2\)
  (\(B'=6\)), \(S=6\) with the source supply (\(B'=24\)), and a non-maximal
  supply. All are exact equalities. This checks the composition mechanism.
  The stage relation (D′) itself was checked in the maps topic.

## 4. Lower bounds (task items 2 and 3)

### 4.1 Ingredients (proved in the lower note; re-derived here)

Notation: \(q=d+2\); \(\lambda_d\in(0,1)\) is the positive root of
\(f_d(y)=qy^2+y-d\); \(a_d=-\log\lambda_d\); \(g_d=\log(q/d)\);
\(\omega_d=3a_d/g_d\); \(K=21/20\); \(x=\log(1/\varepsilon)\);
\(d_\varepsilon=(96\varepsilon)^{-1/2}\). For a block,
\(\delta_{ij}=n_{ij}\log q_i-\log M_{ij}\ge0\) (the lower note's \(D_{ij}\); renamed
because \(D\) is the bulk arity in the brief).

**L1 (contraction).** For
\(\Phi(r,b)=\frac23\sqrt{Q(r-\frac13,b-\frac13)}\), \(Q(y,z)=y^2+4yz+z^2\), every
legal step at arity \(d\) has \(\Phi(c,r)\le\lambda_d\Phi(r,b)\), and \(\Phi\) is
symmetric and nondecreasing. *Re-derived:* with \(R=r-\frac13\),
\(B=b-\frac13\), \(\beta=\lambda+\frac1q\), \(T=((dB-R)/q,R)\),
\[
\lambda^2Q(R,B)-Q(T)-(1-\beta^2)(R-\lambda B)^2=\frac{f_d(\lambda)}q\bigl[2R^2+(4-2\beta)RB+(\lambda\beta+\tfrac dq)B^2\bigr].
\]
The script expands \(q^3\times\)(difference) as a polynomial in
\(\Q[q,\lambda,R,B]\) and finds 0. At \(\lambda=\lambda_d\) the right side
vanishes. \(\lambda_d<1-1/q\) since \(f_d(1-1/q)=1\), so \(0<\beta<1\). Legality
is \(qC\le dB-R\) with \(C=c-\frac13\ge\frac23\), and \(Q\) increases in each
argument on positive arguments.

**L2 (endpoint).** \(\log s\ge\log K+\sum_ia_{d_i}+\frac45\log t\). *Re-derived:*
telescope L1 and use monotonicity for crops. At the start,
\(\Phi(\pi_0)^2\le\frac23(s+\frac13)^2\le s^2\), since
\(Q(y,z)\le\frac32(y+z)^2\) and \(s^2-\frac23(s+\frac13)^2=\frac{(s-2)(9s+6)+10}{27}>0\).
At the end, \(\Phi(1,t)^2=\frac49(t^2+2t-\frac13)\). With \(u=t-1\), all eleven
coefficients of \((\frac49)^5(u^2+4u+\frac83)^5-K^{10}(u+1)^8\) are positive
(script; smallest \(\approx0.0173\)), so \(\Phi(1,t)\ge Kt^{4/5}\).

**L3 (gap).** For \(d\ge2\): \(\omega_d-\frac94\ge\frac1{24q^2}\ge\frac1{96d^2}\),
and \(g_d\le2/d\). *Re-derived:* with \(z=(d/q)^{1/4}\),
\((1-z^4)f_d(z^3)=z^3(1-z)^2(1-z^2)\) (script), so \(\lambda_d<z^3\), and
\(\omega_d-\frac94=\frac3{g_d}\log\frac{z^3}{\lambda_d}\). The mean value theorem
(\(f_d'\le2q+1\) on \([0,1]\)) and \(\log y\ge1-1/y\) give
\(\omega_d-\frac94\ge\frac{3(1-z)^2}{(1+z^2)(2q+1)g_d}\). Then
\(1-z\ge\frac{1-z^4}4=\frac1{2q}\), \(1+z^2\le2\), \(2q+1\le\frac92d\) and
\(g_d\le\frac2d\) give \(\frac1{24q^2}\). In particular \(\omega_d>\frac94\), and
\(a_d=\omega_dg_d/3>\frac34g_d\).

**L4 (type counts).** For \(d\ge2\) and any type of width \(n\):
(a) \(M\le q^n\); (b) if \(M>d^n\) then \(n\ge3\) and \(d\le2n\); (c) if
\(n\ge3\) and \(d\le2n\) then \(M\le q^n/2\); (d) if \(n\ge2q\) then
\(M\le4e\,q^{n+1}/n<12q^{n+1}/n\). *Re-derived:* (a) multinomial theorem.
(b) For \(n\le2\) all counts are at most \(d^n\) (\(4(d-1)\le d^2\)); for
\(d\ge2n+1\), \(M/(d-1)^n\le\frac{(2n/(d-1))^o(n/(d-1))^m}{o!m!}\le1\).
(c) \(M/q^n\) is at most the binomial probability of the kernel count, with
\((n+1)\frac{d-1}q\in[1,n]\), so a mode \(a\) lies in \([1,n-1]\); its two
neighbour ratios have product \(\frac{a(n-a)}{(a+1)(n-a+1)}\ge\frac14\), hence sum
at least 1, so the mode has mass at most \(\frac12\). (d) A maximizer has
\(a_i\ge(n+1)p_i-1\) (one-unit moves), so \(a_K\ge n/8\), \(a_O\ge n/q\),
\(a_M\ge n/(2q)\ge1\). Stirling's bounds
\(\sqrt u(u/e)^u\le u!\le e\sqrt u(u/e)^u\) (trapezoid and midpoint rules for
\(\log\)) and Gibbs' inequality give
\(M/q^n\le e\sqrt{n/(a_Ka_Oa_M)}\le4eq/n\). The script checks (a)–(c)
exhaustively for \(n\le30\), \(2\le d\le40\), and (d) at 399 larger pairs.

### 4.2 The copy-count theorem (task item 3)

**Theorem C (accounting-invariant lower bound).** *(proved here)* Let
\(0<\varepsilon<1/9216\). Take a chain scheme of the class and any supply such
that \(r_*\MM_S\restr m_*\MM_{B'}\) is a relative scheme with pooled exponent
\(p'\le9/4+\varepsilon\). Then:

1. some stage \(i\) has a block \((n,k,\tau)\) with \(d_i>d_\varepsilon\),
   \(n>9d_ix/(16\varepsilon)\) and \(k>d_i\log d_i/(4\varepsilon)\); hence
   \(P>3x^2/(8192\varepsilon^3)\);
2. \(\log r_*>\log m_*\ge3\log\bar A+6P\log(s/t)\ge3\log\bar A\);
3. \(\log\bar A\ \ge\ 2P\sum_{(i,j)\in I}w_{ij}\log d_i\ >\ \dfrac{27\log K}{1024\cdot96^{3/2}}\,\varepsilon^{-9/2}x^3\ >\ 1.3\cdot10^{-6}\,\varepsilon^{-9/2}x^3\), where \(I\) is the set of profitable blocks defined in the proof;
4. hence
   \[
   \log r_*>\log m_*>\frac{81\log(21/20)}{1024\cdot96^{3/2}}\,\varepsilon^{-9/2}x^3>3.9\cdot10^{-6}\,\varepsilon^{-9/2}x^3 ;
   \]
5. \(\log B'\ge\log(B'/S)>\frac{45}{458752}\,\varepsilon^{-4}x^2>9.8\cdot10^{-5}\,\varepsilon^{-4}x^2\) (Proposition T);
6. \(\log S\ge2P\log d_1>\frac{3\log2}{4096}\,\varepsilon^{-3}x^2>5\cdot10^{-4}\,\varepsilon^{-3}x^2\);
7. under the source supply, \(S=\bar A\), so the source side satisfies item 3.

The exact constant in item 4 is \(\approx4.10\cdot10^{-6}\); in item 3 it is
\(\approx1.37\cdot10^{-6}\).

*Proof.* **Step 0 (reduction).** By Lemma S(4), the source supply of the
same chain data is a relative scheme with pooled exponent
\(p\le p'\le p_0:=9/4+\varepsilon\). Steps 1–5 concern this scheme. Its
counts are \((\bar A,\bar B,r_*,m_*)\), and \(r_*\), \(m_*\), \(P\), \(s\), \(t\)
and the \(d_i\) are the same for every supply. Note \(p_0\le12/5\).

**Step 1 (normalization).** Taking logarithms of the counts and dividing by
\(2P\) (using \(\sum_jn_{ij}k_{ij}=P\)):
\[
\frac{\log(\bar B/\bar A)}{2P}=\log t+\sum_{i,j}w_{ij}\Bigl(g_{d_i}-\frac{\delta_{ij}}{n_{ij}}\Bigr),\qquad
\frac{\log(r_*/m_*)}{2P}\ge3\log s+\sum_{i,j}w_{ij}\frac{\log E_{ij}}{2n_{ij}k_{ij}},
\]
where the separator factors \((2M-1)/M\ge1\) were dropped.

**Step 2 (profit inequality).** \(p\le p_0\) means
\(\log(r_*/m_*)\le p_0\log(\bar B/\bar A)\). Insert L2 with
\(3a_{d_i}=\omega_{d_i}g_{d_i}\) and \(\sum_jw_{ij}=1\):
\[
\sum_{i,j}w_{ij}t_{ij}\ \ge\ 3\log K+\bigl(\tfrac{12}5-p_0\bigr)\log t\ \ge\ 3\log K,\qquad
t_{ij}=(p_0-\omega_{d_i})g_{d_i}-\frac{p_0\delta_{ij}}{n_{ij}}-\frac{\log E_{ij}}{2n_{ij}k_{ij}} .
\]
Let \(I=\{(i,j):t_{ij}>0\}\). Since every \(t_{ij}\le0\) off \(I\),
\(\sum_Iw_{ij}t_{ij}\ge3\log K>0\); in particular \(I\ne\emptyset\).

**Step 3 (a profitable block).** Fix \((i,j)\in I\); write \(d,n,k,M,\delta,E,g\).

- \(t>0\), \(\delta\ge0\) and \(E\ge1\) give \(\omega_d<p_0\). By L3,
  \(\frac1{96d^2}<\varepsilon\), so \(d>d_\varepsilon\).
- \(\omega_d>\frac94\) gives \(p_0-\omega_d<\varepsilon\), so
  \(p_0\delta/n<(p_0-\omega_d)g<\varepsilon g\). (\(*\))
- Hence \(\frac1n\log M=\log q-\delta/n>\log q-\varepsilon g/p_0\ge\log d\),
  that is \(M>d^n\).
- L4(b,c) give \(\delta\ge\log2\). By (\(*\)) and \(g\le2/d\),
  \(n>\frac{9\log2}8\cdot\frac d\varepsilon>\frac9{16}\cdot\frac d\varepsilon\).
  So \(n\ge2q\) (as \(\varepsilon\le9/64\)), and \(n/(12q)>3/(128\varepsilon)\)
  (as \(q\le2d\)).
- L4(d) gives \(\delta\ge\log(n/(12q))>\log(3/(128\varepsilon))\ge x/2\)
  (as \(\varepsilon\le9/16384\)). By (\(*\)) again, \(n>p_0\delta/(\varepsilon g)>9dx/(16\varepsilon)\).
- \(E\ge M>d^n\) and \(\log E/(2nk)<(p_0-\omega_d)g<\varepsilon g\le2\varepsilon/d\)
  give \(\log d/(2k)<2\varepsilon/d\), that is \(k>d\log d/(4\varepsilon)\).
- \(\varepsilon<1/9216\) gives \(\log d_\varepsilon>x/4\), and \(d>d_\varepsilon>1\)
  gives \(d\log d>d_\varepsilon\log d_\varepsilon>d_\varepsilon x/4\).

This proves item 1, with \(P\ge nk>\frac{9d_\varepsilon x}{16\varepsilon}\cdot\frac{d_\varepsilon x}{16\varepsilon}=\frac{3x^2}{8192\varepsilon^3}\).

**Step 4 (the profitable sum).** For \((i,j)\in I\),
\(t_{ij}<\varepsilon g_{d_i}\le2\varepsilon/d_i<\frac{2\varepsilon\log d_i}{d_\varepsilon\log d_\varepsilon}\),
because \(d\mapsto d\log d\) increases and \(d_i>d_\varepsilon\). Weight by
\(w_{ij}\) and sum over \(I\):
\[
\Sigma_I:=\sum_{(i,j)\in I}w_{ij}\log d_i\ >\ \frac{3\log K\,d_\varepsilon\log d_\varepsilon}{2\varepsilon}\ >\ \frac{3\log K\,d_\varepsilon x}{8\varepsilon}.
\]

**Step 5 (combination).** Steps 3 and 4 give
\[
2P\,\Sigma_I>2\cdot\frac{9d_\varepsilon^2x^2}{256\varepsilon^2}\cdot\frac{3\log K\,d_\varepsilon x}{8\varepsilon}
=\frac{27\log K}{1024}\cdot\frac{d_\varepsilon^3x^3}{\varepsilon^3}
=\frac{27\log K}{1024\cdot96^{3/2}}\,\varepsilon^{-9/2}x^3 .
\]
*Bound on \(\bar A\) (item 3).* \(\log\bar A=2P\sum_i\log d_i\ge2P\,\Sigma_I\),
since \(\sum_jw_{ij}\le1\).
*Bound on \(m_*\) via the profitable sum.* \(M_{ij}>d_i^{n_{ij}}\) on \(I\)
(Step 3) and \(M_{ij}\ge1\) elsewhere, so
\[
\log m_*=6\sum_{i,j}k_{ij}\log M_{ij}\ \ge\ 6\sum_{I}k_{ij}n_{ij}\log d_i=6P\,\Sigma_I=3\cdot2P\,\Sigma_I .
\]
*Item 2 (a second route).* By Step 0 and \(p\le p_0\le3\),
\(\log(\bar B/\bar A)\ge\frac13\log(r_*/m_*)\ge2P\log s\). With
\(\bar B=t^{2P}m_*^{1/3}\), this is \(m_*^{1/3}\ge\bar A\,(s/t)^{2P}\), and
\(t\le s\) (Section 2.2). Also \(r_*/m_*\ge s^{6P}>1\).
Items 3 and 2 give item 4 with the constant \(3\cdot27/1024=81/1024\).

*Numerics of the constants* (exact rationals, script Part 7):
\(\log K>1/21\) and \(96^3<960^2\) give
\(\frac{27\log K}{1024\cdot96^{3/2}}>\frac{27}{21\cdot1024\cdot960}>1.3\cdot10^{-6}\) and
\(\frac{81\log K}{1024\cdot96^{3/2}}>\frac{81}{21\cdot1024\cdot960}>3.9\cdot10^{-6}\).

**Item 5 (Proposition T).** By Step 2, every block has
\(t_{ij}\le(p_0-\omega_{d_i})g_{d_i}<\varepsilon g_{d_i}\), so
\(3\log K\le\sum w_{ij}t_{ij}<\varepsilon\sum_ig_{d_i}\), that is
\(\sum_ig_{d_i}>3\log K/\varepsilon\). By L2 and \(a_d>\frac34g_d\),
\(\log s>\frac94\log K/\varepsilon\). Now use the *supplied* scheme:
\(p'\le p_0\le\frac{12}5\) gives
\(\log(B'/S)\ge\log(r_*/m_*)/p_0\ge\frac{6P\log s}{12/5}=\frac52P\log s\). So
\[
\log(B'/S)\ \ge\ \tfrac52P\log s\ >\ \tfrac{45}8\log K\cdot\frac P\varepsilon
\ >\ \tfrac{45}8\log K\cdot\frac{3x^2}{8192\,\varepsilon^4}=\frac{135\log K}{65536}\,\varepsilon^{-4}x^2 ,
\]
and \(\frac{135}{65536\cdot21}=\frac{45}{458752}>9.8\cdot10^{-5}\). The first two
inequalities hold for every \(\varepsilon\le3/20\); only the last uses item 1
and hence \(\varepsilon<1/9216\). \(\log B'\ge\log(B'/S)\) as \(S\ge1\).

**Item 6.** \(S=\beta_0\ge U_1f_1\ge U_1=d_1^{2P}\ge2^{2P}\), and item 1 gives
\(2P\log2>\frac{3\log2}{4096}\varepsilon^{-3}x^2\).

**Item 7.** The source supply has \(S=\bar A\). \(\square\)

**The \(\varepsilon\)-range.** The proof uses four thresholds; all are monotone
in \(\varepsilon\):

| Use | Condition |
| --- | --- |
| \(p_0\le12/5\) (Step 2, item 5) | \(\varepsilon\le3/20\) |
| \(n\ge2q\) (L4(d)) | \(\varepsilon\le9/64\) |
| \(\log(3/(128\varepsilon))\ge x/2\) | \(\varepsilon\le9/16384\) |
| \(\log d_\varepsilon>x/4\) | \(\varepsilon<1/9216\) |

So Theorem C (and Proposition T) hold for \(0<\varepsilon<1/9216\), which
contains \(\varepsilon\le2^{-14}\) and \(\varepsilon\le10^{-4}\). The script
verifies the thresholds at the grid points below \(1/9216\).

**Remarks.**

- *Why \(m_*\) is accounting-invariant.* \(m_*=(\prod_iV_i)^3\) is the cube of
  the total auxiliary side *produced*, and \(\bar A=\prod_iU_i\) is the total
  side *consumed*. Both are fixed by the chain. Item 2 says that a scheme with
  \(p\le3\) produces at least what it consumes. A supply decides only which part
  of the consumption is paid by the source; it cannot change \(m_*\) or
  \(r_*\).
- *Extensions with the same proof.* Remark 8(b) of the lower note (different
  arities for different blocks of one stage; put
  \(\bar A=\prod_{i,j}d_{ij}^{2n_{ij}k_{ij}}\)) and joint exactification of the
  blocks of one stage (review R.5.1) keep the theorem. Under joint
  exactification, item 1 holds with \(P>n\,d\log d/(4\varepsilon)\) in place of
  the bound on \(k\), which still gives \(P>3x^2/(8192\varepsilon^3)\); item 3
  follows by the level-wise argument of R.5.1; and item 4 then follows from
  item 2, which uses only \(r_*/m_*\ge s^{6P}\) and
  \(m_*=(\bar B/t^{2P})^3\).
- *Pooled exponent with a ceiling.* The ceiling version is larger, so the
  theorem covers it a fortiori.

## 5. The main construction (task item 4)

### 5.1 Copy counts of the main construction

The main theorem (upper note, Section 5) uses \(D=\lceil\sqrt{4/\varepsilon}\rceil\),
\(R=8D\), \(L=\lceil64D/\varepsilon\rceil\), \(H\) the bit length of
\(\lceil128D/\varepsilon\rceil\), \(n=k=\lceil256DH/\varepsilon\rceil\), \(J=16D-2+L\)
stages (ramp plus bulk), maximal types and terminal \(t=1\). It proves
\(\log A\le2n^2J\Lambda\le2{,}550{,}252{,}000\,\varepsilon^{-9/2}\Lambda^3\)
with \(\Lambda=\log(4096/\varepsilon)\), \(B\le A^2\), and
\(p<9/4+\frac{719}{1988}\varepsilon\). The seeds note (Lemma 1, endorsed) proves
\(m_*=B^3\) and \(r_*=m_*(B/A)^p\le B^3(B/A)^{11/4}\le A^{35/4}\).

**Proposition M.** *(proved here from these)* For rational \(0<\varepsilon\le1\),
the main construction has, with \(A=\bar A\) its source side under the source
supply (the copy counts are the same for every supply),
\[
3\log A<\log m_*\le6\log A<1.54\cdot10^{10}\,\varepsilon^{-9/2}\Lambda^3,\qquad
\log r_*\le\tfrac{35}4\log A<2.24\cdot10^{10}\,\varepsilon^{-9/2}\Lambda^3 .
\]
With the allowance \(\varepsilon\) instead of \(\varepsilon/2\) (apply at
\(2\varepsilon\), \(\varepsilon\le1/2\)):
\(\log m_*<8.4\cdot10^8\varepsilon^{-9/2}\log^3(2048/\varepsilon)\) and
\(\log r_*<1.24\cdot10^9\varepsilon^{-9/2}\log^3(2048/\varepsilon)\).

*Proof.* \(m_*=B^3\le A^6\) and \(B>A\); \(r_*\le A^{35/4}\); and
\(6\times2.551\cdot10^9<1.54\cdot10^{10}\),
\(\frac{35}4\times2.551\cdot10^9<2.24\cdot10^{10}\). For the corollary form,
\(3\cdot10^9\cdot2^{-9/2}\times6<8.4\cdot10^8\) and
\(\times\frac{35}4<1.24\cdot10^9\). \(\square\)

With Theorem C(4) this gives the copy-count order within the construction:

> For \(0<\varepsilon<1/9216\), every scheme of the class with any supply and
> pooled exponent at most \(9/4+\varepsilon\) has
> \(\log r_*>\log m_*>3.9\cdot10^{-6}\varepsilon^{-9/2}\log^3(1/\varepsilon)\), and
> the main construction attains \(\log r_*,\log m_*=O(\varepsilon^{-9/2}\log^3(1/\varepsilon))\).
> So the copy-count order is \(\Theta(\varepsilon^{-9/2}\log^3(1/\varepsilon))\),
> with constants about \(10^{14}\) apart.

The script's ratio of the main construction's \(\log m_*\) bound to the lower
bound (at matched allowance \(\varepsilon/2\)) falls from \(1.4\cdot10^{13}\)
at \(\varepsilon=2^{-16}\) to \(5.9\cdot10^{12}\) at \(2^{-200}\), consistent
with the same order.

### 5.2 The recycled main construction

**Corollary R (recycled main construction).** *(conditional on the main
theorem)* Let \(0<\varepsilon\le1\) be rational. Take the chain, types and
powers of the main theorem, and the recycling supply with source
\(S=4JD^{2nk}\). Then every stage is funded (\(\beta_{i-1}\ge2JU_i\)), the
scheme \(r_*\MM_S\restr m_*\MM_{B'}\) has the same \(r_*\) and \(m_*\) as the
main theorem, \(B'>S\), and
\[
\tfrac94<p'<\tfrac94+\tfrac{719}{1988}\varepsilon+10^{-9}\varepsilon<\tfrac94+\tfrac\varepsilon2,
\]
\[
\log A'=\log S<5.32\cdot10^6\,\varepsilon^{-3}\Lambda^3,\qquad
\log B'<1.5\cdot10^9\,\varepsilon^{-4}\Lambda^2,\qquad \Lambda=\log(4096/\varepsilon).
\]
For allowance \(\varepsilon\) (apply at \(2\varepsilon\), \(\varepsilon\le1/2\)):
\(\log A'<6.7\cdot10^5\varepsilon^{-3}\log^3(2048/\varepsilon)\) and
\(\log B'<9.4\cdot10^7\varepsilon^{-4}\log^2(2048/\varepsilon)\).

*Proof.* Facts from the main theorem's Steps 0, 1 and 5:
\(a:=2\log(n+1)/n\le3/x_0\) with \(x_0=128D/\varepsilon\); \(L g_D\ge64/\varepsilon\);
\(\log(\bar B/\bar A)\ge2nk(1-\theta)G\ge2nk\cdot\frac{497}{512}\cdot\frac{64}\varepsilon\);
\(D\le3\varepsilon^{-1/2}\); \(J\le240\varepsilon^{-3/2}\);
\(n=k\le2305\varepsilon^{-3/2}\Lambda\); and \(n\ge256DH/\varepsilon\ge4608/\varepsilon\)
(\(D\ge2\), \(H\ge9\)). Also \(M_i\ge q_i^n/(n+1)^2\) (upper note, Lemma 6).
Read forwards, the chain has \(L\) bulk stages of arity \(D\), then the ramp with
arities \(3(R-1),3(R-1)-1,\dots,3,2\), all at most \(24D-3\).

*Funding.* Put \(\rho_i=\log(V_i/U_i)\ge2k(ng_{d_i}-2\log(n+1))\).
(F1) Every stage gains: \(d_i\le24D-3\) gives \(g_{d_i}\ge\frac2{d_i+2}>\frac1{12D}\),
and \(2\log(n+1)=an\le\frac{3\varepsilon n}{128D}\), so
\(ng_{d_i}-2\log(n+1)\ge\frac{n}D(\frac1{12}-\frac3{128})>0\).
(F2) The bulk pays for the jump to the ramp:
\(\sum_{i\le L}\rho_i\ge2nk(Lg_D-La)\ge2nk(\frac{64}\varepsilon-2)\ge124nk>2nk\log24\),
using \(La\le(\frac{64D}\varepsilon+1)\frac{3\varepsilon}{128D}<2\). Hence
\(\tilde U=\max_iU_i\prod_{l<i}e^{-\rho_l}=U_1=D^{2nk}\): for bulk stages by
(F1), and for ramp stages because \(U_i\le(24D)^{2nk}\) and
\(\prod_{l<i}e^{-\rho_l}\le e^{-\sum_{l\le L}\rho_l}<24^{-2nk}\). Lemma S(3)
with \(S=4J\tilde U\) gives funding and \(B'/S\ge\bar B/(2\bar A)\).

*Exponent.* \(\log(B'/S)\ge\log(\bar B/\bar A)-\log2>0\), so \(B'>S\), and
\(p'\le p\cdot\frac{\log(\bar B/\bar A)}{\log(\bar B/\bar A)-\log2}\). Hence
\(p'-p\le\frac{p\log2}{\log(\bar B/\bar A)-\log2}\le\frac{(11/4)\log2}{124nk-1}
<\frac{2}{123nk}\le\frac{2\varepsilon^2}{123\cdot4608^2}<10^{-9}\varepsilon\).
The main theorem gives \(p<9/4+\frac{719}{1988}\varepsilon\) and \(p>9/4\)
(Lemma P), and \(p'\ge p\) (Lemma S(4)).

*Source side.* \(\log S=\log(4J)+2nk\log D\). Here
\(2\log D\le\log(9/\varepsilon)\le\Lambda\), \(nk\le2305^2\varepsilon^{-3}\Lambda^2\),
and \(\log(4J)\le\log(960\varepsilon^{-3/2})\le\frac32\Lambda\le0.022\,\Lambda^3\)
(as \(\Lambda\ge\log4096\)). So \(\log S\le(5{,}313{,}025+0.022)\varepsilon^{-3}\Lambda^3\).

*Target side.* \(\log(\bar B/\bar A)\le2nkG\) (as \(M_i\le q_i^n\), \(t=1\)), where
\(G=\sum_ig_{d_i}=\log F(R,R)+Lg_D\) (upper note, Lemma 2). Here
\(Lg_D\le(\frac{64D}\varepsilon+1)\frac2D\le\frac{128}\varepsilon+1\), and
\(\log F(R,R)=\log\frac{3R-1}2+\sum_{h<R}\log(1+\frac1{3h})\le\log(12D)+\frac{1+\log(8D)}3<\frac23\Lambda\)
(or use v5 (3.6), \(F(R,R)\le(2R-1)^{4/3}\)). So
\[
\log B'\le\log S+\log(\bar B/\bar A)\le\tfrac32\Lambda+nk\bigl[\Lambda+\tfrac{256}\varepsilon+2+\tfrac43\Lambda\bigr]
\le\tfrac32\Lambda+2305^2\varepsilon^{-4}\Lambda^2\bigl[256+2\varepsilon+\tfrac73\varepsilon\Lambda\bigr].
\]
Since \(\varepsilon\Lambda\le\log4096<8.32\) for \(\varepsilon\le1\), the bracket is
below \(277.5\), and \(2305^2\cdot277.5+1<1.48\cdot10^9\).
The allowance-\(\varepsilon\) forms follow from
\(5.32\cdot10^6/8<6.7\cdot10^5\) and \(1.5\cdot10^9/16<9.4\cdot10^7\). \(\square\)

*Checked:* Part 6 of the script verifies (F1), (F2), the bounds on \(\log S\)
and \(\log B'\) and \(p'-p<10^{-9}\varepsilon\) on 70 (quick) or 216
(full) rational \(\varepsilon\) from 1 down to \(2^{-200}\), including
\(D\)-breakpoints \(\varepsilon=4/D^2\). Part 5 runs the actual chains at
\(\varepsilon=1,\frac12,\frac14,\frac19\) with exact maximal types, and tracks the
bank with interval logarithms at every stage:

| \(\varepsilon\) | \(D\) | stages | \(p<\) | \(p'<\) | digits \(A\) | digits \(A'\) | digits \(B\) | digits \(B'\) | digits \(m_*\) | digits \(r_*\) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 158 | 2.2799155 | 2.2799155 | \(3.25\cdot10^9\) | \(1.28\cdot10^7\) | \(4.96\cdot10^9\) | \(1.72\cdot10^9\) | \(1.49\cdot10^{10}\) | \(1.88\cdot10^{10}\) |
| 1/2 | 3 | 430 | 2.2643362 | 2.2643362 | \(1.18\cdot10^{11}\) | \(2.25\cdot10^8\) | \(1.59\cdot10^{11}\) | \(4.13\cdot10^{10}\) | \(4.76\cdot10^{11}\) | \(5.69\cdot10^{11}\) |
| 1/4 | 4 | 1,086 | 2.2575793 | 2.2575793 | \(3.45\cdot10^{12}\) | \(2.91\cdot10^9\) | \(4.33\cdot10^{12}\) | \(8.84\cdot10^{11}\) | \(1.30\cdot10^{13}\) | \(1.50\cdot10^{13}\) |
| 1/9 | 6 | 3,550 | 2.2534912 | 2.2534912 | \(1.84\cdot10^{14}\) | \(5.03\cdot10^{10}\) | \(2.12\cdot10^{14}\) | \(2.81\cdot10^{13}\) | \(6.37\cdot10^{14}\) | \(7.00\cdot10^{14}\) |

Digit counts are upper bounds from the interval logarithms. The increase
\(p'-p\) is below \(3\cdot10^{-10}\) in every row, and the first stage has funding
slack exactly \(\log2\) (\(S=4JU_1\)). Recycling cuts the digits of the source
side by factors of 254 (\(\varepsilon=1\)) to 3,665 (\(\varepsilon=1/9\)). At these
moderate \(\varepsilon\), \(B'\) still has 13–35% of the digits of \(B\), because
\(\log(B/A)\) is comparable to \(\log A\) there. The copy counts do not change,
and they are the largest numbers in every row.

### 5.3 Consequences

- *The source-supply hypothesis is necessary for the source-side bound.*
  At allowance \(\varepsilon/2\), Theorem C(7) would demand
  \(\log S>1.3\cdot10^{-6}(\varepsilon/2)^{-9/2}\log^3(2/\varepsilon)\).
  Corollary R gives \(\log S<5.32\cdot10^6\varepsilon^{-3}\Lambda^3\), which is
  smaller for every \(\varepsilon\le2^{-26}\). The ratio of the two is
  \(c\,\varepsilon^{3/2}\bigl(\frac{\log4096+y}{\log2+y}\bigr)^3\) with
  \(y=\log(1/\varepsilon)\), which decreases as \(\varepsilon\) decreases, so one
  check at \(2^{-26}\) suffices (script Part 6). (Conditional.) With the actual
  counts of the schedule, the crossover is already between \(2^{-20}\) and
  \(2^{-24}\) (table in Section 7).
- *Orders within the class* (lower bounds proved; upper bounds conditional):

  | Quantity | lower bound (any supply) | main construction |
  | --- | --- | --- |
  | \(\log m_*\), \(\log r_*\) | \(3.9\cdot10^{-6}\varepsilon^{-9/2}x^3\) | \(O(\varepsilon^{-9/2}\Lambda^3)\), any supply |
  | \(\log\bar A\) (source side under source supply) | \(1.3\cdot10^{-6}\varepsilon^{-9/2}x^3\) | \(O(\varepsilon^{-9/2}\Lambda^3)\) |
  | \(\log(B'/S)\) | \(9.8\cdot10^{-5}\varepsilon^{-4}x^2\) | \(O(\varepsilon^{-4}\Lambda^2)\) |
  | \(\log B'\) | \(9.8\cdot10^{-5}\varepsilon^{-4}x^2\) | \(O(\varepsilon^{-4}\Lambda^2)\), recycled |
  | \(\log S\) (best supply) | \(5\cdot10^{-4}\varepsilon^{-3}x^2\) | \(O(\varepsilon^{-3}\Lambda^3)\), recycled |

  Only the source side under the best supply has a gap (one logarithm).
- *Recycling does not help the seeds.* The seed of the paper's Section 5
  (seeds note, Theorem 7) has \(n_0=(\Xi+1)^{\lceil2/\varepsilon\rceil}\) with
  \(\Xi=r_*(1+r_*m_*)n_*^3\), and \(n_*\le3A\). For the recycled scheme,
  \(\Xi'\ge r_*^2m_*\ge m_*^3=B^9\ge(2A)^9\); without recycling,
  \(\Xi\le54r_*^2m_*A^3\). Hence \(\log\Xi/\log\Xi'<1+\frac13+\frac{\log54}{9\log A}<1.34\).
  So recycling can shrink the seed exponent \(\log n_0\) by a factor of at most
  1.34. The copy counts, not the source side, set the size of the seed. This is a
  further reason to state the robust bound on \(r_*\) and \(m_*\).

## 6. Recommendation for Section 7 (task item 5)

The paper should make the accounting explicit once, in the definition, and
then state three short results. Notation follows the brief: \(N_{ij}\) for
widths, \(k_{ij}\) for powers, stages \(i=1,\dots,J\) acting on pairs
\((r_i,b_i)\), source pair \((r_1,b_1)\), \(s=r_1+b_1-1\). The brief reserves
\(P\) for a v5 profile, so the global power is called \(W\) below. Proofs of
Lemmas L1–L4 and of Theorem 7.3(a)–(b) go to `appendix-lower.tex`.

**Definition 7.1 (`def:class`).**

> A *chain scheme* consists of: integers \(J,W\ge1\); pairs \((r_i,b_i)\) of
> positive integers for \(1\le i\le J+1\); arities \(d_i\ge2\) for \(i\le J\)
> such that, after exchanging \(r_i\) and \(b_i\) if necessary, some
> \(c_i\ge1\) satisfies \((d_i+2)c_i\le d_ib_i-r_i+1\) and, after exchanging
> \(r_{i+1}\) and \(b_{i+1}\) if necessary, \(r_{i+1}\le c_i\) and
> \(b_{i+1}\le r_i\); for each \(i\le J\), blocks \(j\) with widths \(N_{ij}\),
> powers \(k_{ij}\) and types \(\tau_{ij}\) of width \(N_{ij}\)
> (Lemma~\ref{lem:stage-types}), with \(\sum_jN_{ij}k_{ij}=W\); and a terminal
> \(1\le t\le\max(r_{J+1},b_{J+1})\). Let \(M_{ij}\) be the sector count of
> \(\tau_{ij}\) at arity \(d_i\), \(E_{ij}=1+6k_{ij}(M_{ij}-1)\),
> \(U_i=d_i^{2W}\), \(V_i=\prod_jM_{ij}^{2k_{ij}}\), and
> \[
> \bar A=\prod_iU_i,\quad \bar B=t^{2W}\prod_iV_i,\quad
> r_*=s^{6W}\prod_{i,j}E_{ij}(2M_{ij}-1)^{6k_{ij}},\quad m_*=\prod_{i,j}M_{ij}^{6k_{ij}} .
> \]
> A *supply* is a sequence of positive integers \(S,f_1,\dots,f_J\) with
> \(U_if_i\le\beta_{i-1}\) for all \(i\), where \(\beta_0=S\) and
> \(\beta_i=f_iV_i\). The *source supply* is \(S=\bar A\),
> \(f_i=\prod_{l>i}U_l\prod_{l<i}V_l\). The *recycling supply* with source
> \(S\) is \(f_i=\lfloor\beta_{i-1}/U_i\rfloor\).

Follow it with one sentence listing what is fixed: the stage relation of
Corollary~\ref{cor:exact-stage} (uncompressed auxiliaries, Lü's separator,
separate exactification of each block), the full source evaluation
\(s^{6W}\) and the terminal crop; and what varies: arities, children,
crops, swaps, blocks, types, powers, terminal and supply.

**Lemma 7.2 (`lem:recycling`).**

> For every chain scheme and every supply, \(r_*\MM_S\restr m_*\MM_{B'}\)
> over \(\Q\), where \(B'=t^{2W}\beta_J\), and \(B'/S\le\bar B/\bar A\), with
> equality for the source supply. For the recycling supply with source
> \(S\ge4J\max_iU_i\prod_{l<i}U_l/V_l\), every stage has
> \(\beta_{i-1}\ge2JU_i\) and \(B'/S\ge\bar B/(2\bar A)\). If \(B'>S\), the
> pooled exponent of \(r_*\MM_S\restr m_*\MM_{B'}\) is at least that of the
> source supply.

Proof: the induction of Lemma S (half a page). Proposition E becomes the
case "source supply".

**Theorem 7.3 (`thm:lower`).**

> Let \(0<\varepsilon<1/9216\) and \(x=\log(1/\varepsilon)\). Let a chain
> scheme and a supply give a relative scheme \(r_*\MM_S\restr m_*\MM_{B'}\)
> with pooled exponent at most \(9/4+\varepsilon\). Then
>
> (a) \(\log r_*>\log m_*\ge3\log\bar A>3.9\cdot10^{-6}\,\varepsilon^{-9/2}x^3\);
>
> (b) \(\log(B'/S)>9.8\cdot10^{-5}\,\varepsilon^{-4}x^2\).
>
> In particular, under the source supply the source side satisfies
> \(\log\bar A>1.3\cdot10^{-6}\varepsilon^{-9/2}x^3\).

Proof sketch for the section, full proof in the appendix: reduce to the
source supply (Lemma 7.2); the appendix proves
\(\log\bar A>1.3\cdot10^{-6}\varepsilon^{-9/2}x^3\) and
\(\log(\bar B/\bar A)\ge\frac52W\log s>\frac{45}8\log\frac{21}{20}\,\frac W\varepsilon\)
together with \(W>3x^2/(8192\varepsilon^3)\); and
\(m_*\ge\bar A^3\) follows in two lines from
\(\log(\bar B/\bar A)\ge\frac13\log(r_*/m_*)\ge2W\log s\), \(\bar B=t^{2W}m_*^{1/3}\)
and \(t\le s\). (The paper must not call this a "sketch" if it is the only
proof; put the complete proof in the appendix and refer to it.)

**Corollary 7.4 (`cor:recycled-main`).**

> Let \(0<\varepsilon\le1\) be rational. The chain of
> Theorem~\ref{thm:main} with the recycling supply of source
> \(S=4JD^{2Nk}\) gives a relative scheme with the same \(r_*\) and \(m_*\),
> pooled exponent \(9/4<p'<9/4+\varepsilon/2\), \(\log S<5.32\cdot10^6\varepsilon^{-3}\log^3(4096/\varepsilon)\)
> and \(\log B'<1.5\cdot10^9\varepsilon^{-4}\log^2(4096/\varepsilon)\).

**Remark 7.5 (what the bounds say).** Three sentences: copy counts are
\(\Theta(\varepsilon^{-9/2}\log^3)\) for every supply (Theorem 7.3(a) and
Theorem~\ref{thm:main}); \(\log(B/A)\) is \(\Theta(\varepsilon^{-4}\log^2)\)
(7.3(b) and 7.4); the source side is \(\Theta(\varepsilon^{-9/2}\log^3)\) under
the source supply but only between \(\varepsilon^{-3}\log^2\) and
\(\varepsilon^{-3}\log^3\) in general. The last sentence of 7.3 needs the source
supply: for \(\varepsilon\le2^{-26}\), the scheme of Corollary 7.4 has pooled
exponent below \(9/4+\varepsilon/2\) and source side below the bound of that
sentence at allowance \(\varepsilon/2\).
Optionally one more sentence: the seeds of Section 5 depend on \(r_*\) and
\(m_*\), so recycling changes \(\log n_0\) by less than a factor \(1.34\).

**Scope paragraph.** Adapt Section 7 of the lower note, with the supply
removed from the exclusion list (it is now inside the class) and with these
items: compressed auxiliaries (only \(p>9/4\) is known, by
Theorem~\ref{thm:hankel}); cheaper decompositions of the source; joint
exactification across stages; auxiliaries cut from the \(Q\)-state or
coupling orientations; heterogeneous states; other local maps. Say "within
the construction" throughout.

**Consequences for other sections.**

- Introduction, result 4(b): replace "the resource order is optimal" by "the
  copy counts \(r_*,m_*\) have optimal order \(\varepsilon^{-9/2}\log^3\) within
  the construction, for every way of supplying the auxiliaries; the source side
  has this order when the source supplies all auxiliaries".
- Theorem~\ref{thm:main} and Proposition E are statements under the source
  supply; they need no change, but Proposition E should say so, so that
  Section 7 can refer to it.
- The small-source barrier (gate note) is stated for \(A=\prod d_i^{2W}\),
  that is, under the source supply. With recycling, \(A'\le2^{128}\) only
  forces \(d_1^{2W}\le2^{128}\), so multi-stage chains are no longer excluded.
  I did not check whether the barrier survives. The paper should state it
  under the source supply, or drop it (brief, §6).

## 7. Numerical checks

Run from the repository root:

```sh
python -I experiments/shifted_chains_check_recycling.py          # full, about 160 s
python -I experiments/shifted_chains_check_recycling.py --quick  # about 30 s
```

The script imports nothing from the repository. All assertions use exact
integers, Fractions, or rational log intervals (fixed point at scale
\(2^{-320}\), outward rounding; \(\log2\) and \(\log(1+u)\) by the atanh
series with explicit tail bounds). Floats appear only in printed summaries.

| Part | What is checked | Scope |
| --- | --- | --- |
| 1 | L1 identity by polynomial expansion; L3 gap identity; the eleven endpoint coefficients; start inequality; L3 gap and \(g_d\le2/d\) with rational enclosures of \(\lambda_d\) | \(d\le60\) and \(d=100,400,1000\) |
| 2 | L4(a)–(c) exhaustively; greedy maximal type equals the exhaustive maximum; \(M\ge q^n/(n+1)^2\); L4(d) | \(n\le30\), \(d\le40\) (1,170 pairs); 399 pairs with \(n\ge2q\) |
| 3 | Lemma S as a literal restriction on actual tensors (toy stages, Section 3) | \(S=5,2,6\), source and non-maximal supplies |
| 4 | Random chain schemes (swaps, crops, blocks, terminals) and ramp schemes, exact integers: \(m_*=(\bar B/t^{2P})^3\); source supply reproduces \((\bar A,\bar B)\); \(B'S^{-1}\le\bar B\bar A^{-1}\) for random supplies; the exact floor inequality; funding with \(S=\lceil4J\tilde U\rceil\); \(m_*\ge\bar A^3(s/t)^{6P}\) when \(p\le3\); \(t\le s\) | 2,024 schemes (full), 10 with \(p\le3\) |
| 4 | Main-shape chains with small \((n,k)\), exact integers: all supply checks, exact bank (for example \(A\) of 189,625 digits funded by \(S\) of 957 digits); one case has \(p<2.86\) and checks \(m_*\ge\bar A^3(s/t)^{6P}\) exactly | 4 cases |
| 4 | Main-shape chains with 2–3 blocks per stage (interval logs): \(p\le12/5\), \(m_*\ge\bar A^3\), L2, Step 2, \(M>d^n\) on profitable blocks, \(\log m_*\ge6P\Sigma_I\), Proposition T(1)–(2), \(\log(\bar B/\bar A)\ge\frac52P\log s\) | 3 cases, \(p\approx2.27\)–\(2.30\) |
| 5 | The main construction with exact maximal types: \(p\), recycled bank at every stage, \(p'\), bounds of Proposition M and Corollary R, and the same proof ingredients at \(p_0=p\) | \(\varepsilon=1,\frac12,\frac14,\frac19\) |
| 6 | Every inequality in the proof of Corollary R; thresholds of Theorem C; crossover at \(2^{-26}\); ratio table | rational grid \(1\ge\varepsilon\ge2^{-200}\) |
| 7 | All rational constants of Theorem C, Proposition M and Corollary R | exact |

Ratio table (Part 6; main construction at parameter \(\varepsilon\), lower
bounds at allowance \(\varepsilon/2\)):

| \(\varepsilon\) | \(\log m_*\): upper/lower | \(\log(B/A)\): upper/lower | \(\log S\) (recycled): upper/lower | recycled \(\log S\) / source-supply bound on \(\log\bar A\) |
| ---: | ---: | ---: | ---: | ---: |
| \(2^{-16}\) | \(1.42\cdot10^{13}\) | \(3.35\cdot10^{11}\) | \(6.32\cdot10^9\) | \(4.4\cdot10^3\) |
| \(2^{-20}\) | \(1.21\cdot10^{13}\) | \(3.07\cdot10^{11}\) | \(7.07\cdot10^9\) | 62 |
| \(2^{-24}\) | \(1.08\cdot10^{13}\) | \(2.88\cdot10^{11}\) | \(7.84\cdot10^9\) | 0.90 |
| \(2^{-28}\) | \(9.86\cdot10^{12}\) | \(2.75\cdot10^{11}\) | \(8.64\cdot10^9\) | \(1.3\cdot10^{-2}\) |
| \(2^{-40}\) | \(8.34\cdot10^{12}\) | \(2.52\cdot10^{11}\) | \(1.11\cdot10^{10}\) | \(4.6\cdot10^{-8}\) |
| \(2^{-80}\) | \(6.74\cdot10^{12}\) | \(2.26\cdot10^{11}\) | \(1.94\cdot10^{10}\) | \(3.6\cdot10^{-26}\) |
| \(2^{-120}\) | \(6.24\cdot10^{12}\) | \(2.17\cdot10^{11}\) | \(2.77\cdot10^{10}\) | \(3.0\cdot10^{-44}\) |
| \(2^{-160}\) | \(6.00\cdot10^{12}\) | \(2.13\cdot10^{11}\) | \(3.61\cdot10^{10}\) | \(2.5\cdot10^{-62}\) |
| \(2^{-200}\) | \(5.86\cdot10^{12}\) | \(2.10\cdot10^{11}\) | \(4.45\cdot10^{10}\) | \(2.1\cdot10^{-80}\) |

The upper bounds are the proof bounds of Proposition M and Corollary R
evaluated on the actual schedule (not the actual counts). The first two columns
are bounded, as \(\Theta\) predicts. The third grows like \(\log(1/\varepsilon)\):
this is the one-logarithm gap for the source side under the best supply. The
last column drops below 1 between \(2^{-20}\) and \(2^{-24}\).

## 8. Problems found and notes for the paper

| Severity | Problem | Fix |
| --- | --- | --- |
| major (presentation) | Theorem 5 of the lower note bounds \(\bar A=\prod d_i^{2P}\), not the source side of every accounting (R.3). | State Theorem 7.3 with an explicit supply; give the robust bounds on \(r_*,m_*\) and \(\log(B/A)\); keep the source-side bound for the source supply only. |
| minor | R.4 states \(\varepsilon\le2^{-14}\). | The proof works for \(0<\varepsilon<1/9216\). |
| minor | R.4 bounds only \(\log(B/A)\) robustly; R.3 calls \(A\)-bounds "mainly accounting". | Theorem C: the copy counts satisfy the full \(\varepsilon^{-9/2}\log^3\) bound for every supply. |
| minor | R.3's funding condition (\(\beta_{i-1}\ge2^XU_i\), checked per instance) has no closed form. | Lemma S(3): \(S\ge4J\tilde U\) suffices; for the main construction \(\tilde U=D^{2nk}\) (proof in 5.2). |
| notation | The lower note uses \(P\) (reserved by the brief for a v5 profile), \(L\) for the number of stages (the brief: \(J\); \(L\) is the number of bulk stages), \(D_{ij}\) for the type defect and \(D_0\) for the arity threshold (the brief: \(D\) is the bulk arity), and \(\Phi\) for the potential (the brief: \(\Phi\) is the certified fixed-batch quantity). | In the paper use \(W\), \(J\), \(\delta_{ij}\), \(d_\varepsilon\), and a new letter for the potential of L1–L2 (for example \(\Theta\)); note that \(\Psi\) in the brief is a different potential (\(\Psi(r,b)=Q(r-\frac13,b-\frac13)-\frac56\)). |
| open | Whether the small-source barrier survives recycling. | Not checked here; state it under the source supply or drop it. |

Not verified here: the stage relation (D′) itself (maps topic; I used
Corollary D′); the main theorem of the upper note and Lemma 1 of the seeds
note (used for Proposition M and Corollary R, hence "conditional"); the
gate computation.

## Adversarial review

Reviewer role: adversarial referee for topic `recycling`. Date: 18 October
2026. I did not change anything above this section. New file:
[`experiments/shifted_chains_skeptic_recycling.py`](../experiments/shifted_chains_skeptic_recycling.py)
(`python -I experiments/shifted_chains_skeptic_recycling.py`, about 100 s;
`--quick` about 25 s). It imports nothing from the repository and shares no
code with the checker's script. Its logarithms come from Python's `decimal`
module (correctly rounded `ln` and `exp`, widened by one unit in the last
place, all other operations with floor/ceiling rounding), a different method
from the checker's fixed-point atanh series. Every assertion is decided with
integers, Fractions or these intervals. I also reran the checker's script:
it passes in 157 s (full) and prints the values reported in Section 7.

Notation: in this review I keep the note's letters (\(P\), \(S\), \(\beta_i\),
\(U_i\), \(V_i\)). R.4 lists the letters the paper should change.

### R.1 Verdict

**Confirmed, with minor corrections and three additions.**

- Lemma S, Theorem C (items 1–7), Proposition T, Proposition M,
  Corollary R and the consequences of Section 5.3 are correct as stated,
  including every constant and the range \(0<\varepsilon<1/9216\). I
  re-derived each step by hand (R.2) and found no error. The statements
  that depend on the main theorem and on Lemma 1 of the seeds note are
  correctly labelled "conditional".
- The corrections are minor (R.4): two numerical statements are valid but
  loose or depend on an unstated constant; the recommended lemma must say
  when the recycling supply is a supply; the source-side statements must
  say that they concern one chain scheme (finding 4a); and the recommended
  notation still clashes with the brief and with the sections already
  written, in places the note does not list (\(S\) against \(S^\pm_{r,b}\), the
  quadratic form \(Q\) against \(Q_{r,b}\), \(t_{ij}\) against the terminal
  \(t\), \(x\) against \(x=128D/\varepsilon\) in `chains.tex`).
- **Addition 1 (the open item of Section 6 and of brief §6).** Inside one
  chain scheme, the small-source barrier survives every supply, in its
  sharp form: in the gate note's two count models, every chain scheme with
  any supply and source side \(S\le2^{128}\) has pooled exponent at least
  \(p_w=2.97696088251553\ldots\) (R.5). The proof is computer-assisted
  and uses a new two-stage endpoint bound. While I wrote this review, the
  note [shifted-chains-check-small-sources](shifted-chains-check-small-sources.md)
  appeared. Its Theorem 1 is stronger (\(P\le64\) suffices, for any
  source side), and its constants agree with mine. More importantly, its
  Section 4 shows that composing two chain schemes, which uses the same
  mechanism as recycling but lies outside the class, breaks the
  source-side barrier completely. **So the paper should not state the
  source-side barrier as a limit of the construction** (R.5, last part).
- **Addition 2 (proved here).** The two robust bounds of Theorem 7.3,
  on \(r_*,m_*\) and on \(\log(B/A)\), extend from chain schemes with a
  supply to every scheme built from chain schemes and classical algorithms
  by recycling, composition and tensor products (R.5a). The source-side
  bounds do not extend: composition with the classical algorithm gives
  source side 1. So every statement about the source side, including the
  "best supply" bracket and Corollary 7.4's \(\log A'\), is a statement
  about one chain scheme and must say so.
- **Addition 3 (outline, with certified instances).** The one-logarithm gap
  that the note reports for the source side under the best supply is very
  probably an artifact of the main chain, whose first stage has arity
  \(D\). A prefix of \(\lceil\log_2D\rceil\) stages of arity 2 lets
  \(S=4J\,2^{2P}\) fund the whole chain, which divides \(\log S\) by
  \(\log_2D\). I certified this at \(\varepsilon=\frac12,\frac14,\frac19\)
  (R.6). I did not prove it for all \(\varepsilon\).

### R.2 What I re-derived by hand

I re-derived these myself instead of re-reading the note.

- **Citations.** v5 Definition 2.3 asks only for positive integers with
  \(B>A\), so \(S\ge1\) and \(B'>S\) suffice. v5 (2.1) gives
  \(\MM_a\MM_b\cong\MM_{ab}\). v5 (2.6) gives \(S^\sigma_{1,b}\cong\MM_b\),
  hence \(Q_{1,t}\cong\MM_t\MM_t\cong\MM_{t^2}\). v5 (2.8) gives
  \(Q_{r,b}\cong Q_{b,r}\) and \(\R(Q_{r,b})\le(r+b-1)^6\), and Lemma 9.1(a)
  makes the decomposition rational. All are used as the note says.
- **Lemma S.** The stage relation (S\(_i\)): tensor (D′) over the blocks,
  use \(\sum_jn_{ij}k_{ij}=P\), merge the auxiliaries, then crop and swap.
  The crop \(C(c,r)\restr C(c',r')\) zeroes indices at least \(c'\), \(r'\)
  and \(c'+r'-1\); every surviving term has \(\alpha+\beta\le c'+r'-2\).
  The principal block and the splitting are as stated. In the induction,
  the multiplicity \((\prod_{l<i}Y_l)(\prod_{l\ge i}X_l)\) splits into
  \((\prod_{l<i}Y_l)(\prod_{l>i}X_l)\) groups of \(X_i\) copies. The base
  case is a rank decomposition read as a restriction from the unit tensor.
  For items 1–4: \(\beta_i\le\beta_{i-1}V_i/U_i\). Under the source supply
  \(U_if_i=\beta_{i-1}\) telescopes. The floor bound is
  \(\lfloor y\rfloor\ge y-1\). For funding, Bernoulli gives
  \((1-\frac1{2J})^{i-1}\ge\frac12\) for all \(i\le J+1\). Finally
  \(p'\ge p\), because the numerators are equal and positive
  (\(r_*/m_*\ge s^{6P}\ge2^{6P}\)).
- **Geometry.** \(\max(c,r)\le\max(r,b)\) because \(c<b\). Also
  \(t\le\max\pi_0\le s\), because \(\min\pi_0\ge1\).
- **Theorem C, Steps 0–5.** I re-derived each implication and each
  threshold. \(M>d^n\) needs only \(\varepsilon<p_0\). \(\delta\ge\log2\)
  follows from L4(b,c). \(n\ge2q\) holds because
  \(n>\frac9{16}d/\varepsilon\ge4d\ge2d+4\) for \(\varepsilon\le9/64\).
  \(n/(12q)>3/(128\varepsilon)\) uses \(q\le2d\). For L4(d) I checked
  \(a_{\rm K}\ge n/8\), \(a_{\rm O}\ge n/q\), \(a_{\rm M}\ge n/(2q)\) and the
  Stirling/Gibbs step. The \(k\)-bound uses \(E\ge M\). The threshold
  equivalences are exact: \(\log d_\varepsilon>x/4\iff\varepsilon<1/9216\),
  and \(\log(3/(128\varepsilon))\ge x/2\iff\varepsilon\le9/16384\). I also
  re-derived both routes to \(\log m_*\ge3\log\bar A\), Proposition T, and
  all rational constants.
- **L1–L4.** I re-derived the L1 identity, the L3 identity
  \((1-z^4)f_d(z^3)=z^3(1-z)^2(1-z^2)\) and its chain to \(1/(24q^2)\), the
  L2 start polynomial \(9s^2-12s-2=(s-2)(9s+6)+10\), and the binomial-mode
  argument of L4(c).
- **Proposition M and Corollary R.** I checked every inequality.
  - (F1): \(g_d\ge2/(d+2)>1/(12D)\) for \(d\le24D-3\).
  - (F2): \(La<\frac32+\frac{3\varepsilon}{128D}\), and
    \(\tilde U=D^{2nk}\), attained at \(i=1\).
  - Exponent: \(p'-p\le\frac{(11/4)\log2}{124nk-\log2}<\frac{2\varepsilon^2}{123\cdot4608^2}\).
  - Target side: \(\varepsilon\Lambda\le\log4096\) (the maximum is at
    \(\varepsilon=1\)), the bracket is below \(277.5\), and
    \(2305^2\cdot277.5+1<1.48\cdot10^9\).
  - The allowance-\(\varepsilon\) forms and the crossover algebra, including
    its monotonicity in \(\varepsilon\).
  - Seeds: \(\Xi'\ge r_*^2m_*\ge B^9\), \(\Xi\le54r_*^2m_*A^3\), so
    \(\log\Xi/\log\Xi'\le\frac43+\frac{\log54}{9\log A}\).

### R.3 Independent checks (new script)

| Part | Check | Scope | Result |
| --- | --- | --- | --- |
| A | Lemma S as a literal restriction on actual tensors. The stages differ from the checker's toy. Stage 1: Strassen and a crop, \(7(C(2,3)\MM_2)\restr C(2,2)\MM_4\). Stage 2: Strassen and the subrank map \(C(2,2)\restr\langle2\rangle\), so \(Y=2\) comes from the state tensor: \(7(C(2,2)\MM_3)\restr2\,(C(1,1)\MM_6)\). Stage 3: the classical rank-8 decomposition. The source is Lagrange at nodes \(0,1,2,3\). The image of \(r_*\MM_S\) (\(r_*=1568\)) is compared term by term with \(m_*\MM_{B'}\) | 3 stages: recycling \(S=2\) (\(B'=12\)), \(S=5\) (\(B'=24\)), non-maximal \(S=4\) (\(B'=8\)); 2 stages: source supply \(S=6\) (\(B'=24\)), recycling \(S=3\); negative control (inconsistent index merge on one leg) | all exact; the control is detected |
| B | Random chain schemes with exact integers: blocks, random and maximal types, crops, swaps, terminals. A backward generator modelled on the gate witness produces many schemes with \(p\le3\). Checks: every item of Lemma S, \(m_*=(\bar B/t^{2P})^3\), \(m_*t^{6P}\ge\bar A^3s^{6P}\) when \(p\le3\), and \(t\le s\) | 3,500 schemes, 3,274 relative, **246 with \(p\le3\)** (the checker had 10) | pass; on the \(p\le3\) cases \((\log m_*-3\log\bar A)/(6P)\ge0.39\) |
| C | Constants of Theorem C; exact threshold equivalences; L2 polynomial; L3 identity at 30 points; L1 identity on a grid exceeding its degrees; L3 gap with \(\lambda_d\) enclosed by `isqrt`; L4(a)–(c) exhaustively | \(d\le40\) and \(10^2,10^3,10^6\); \(n\le24\), \(d\le30\) | pass |
| D | Corollary R on rational \(\varepsilon\): (F1) at the worst arity \(24D-3\); (F2) in the exact form needed, \(L(ng_D-2\log(n+1))\ge n\log\frac{24D-3}D\); \(p'-p<10^{-9}\varepsilon\); the bounds on \(\log S\) and \(\log B'\); Step 5 of the main theorem; the allowance-\(\varepsilon\) constants; the crossover | 1,032 points: every \(D\)-breakpoint \(4/D^2\) for \(D<300\), \(H\)-breakpoints (\(128D/\varepsilon=2^m\pm\frac12\)), \(2^{-j}\) for \(j\le300\), \(3^{-j}\), random rationals | pass (see note 1 below) |
| E | The main construction, actual counts: my own chain builder; maximal types by exchange optimality; certified \(\log\) of the multinomials from prefix sums of \(\log j\); the recycled bank with its floors at every stage | \(\varepsilon=1,\frac12,\frac14,\frac19\) | every digit count, \(p\) and recycling factor of the note's table reproduced to all printed digits; funding slack \(\log2\), at stage 1 |
| E | Seeds ratio \(\log\Xi/\log\Xi'\) on the actual counts | same | 1.19, 1.22, 1.24, 1.27, all below 1.34 |
| G | Small-source barrier for every supply (R.5): per-stage margins, pair margins, the two-stage endpoint bound, extra-stage gains | all gaining \((n,d,k)\) with \(nk\le64\); two-stage bound exhaustive: 5,764,696 cases (a source pair and orientation, \(d_1\), \(c_1\), \(d_2\); entries \(\le60\), arities 2–8), each against the largest terminal over all crops, orientations and second-stage children (a prefix maximum, cross-checked by direct enumeration); a one-time run with entries \(\le120\) and arities 2–8, 12, 24 covered 85,353,912 cases | pass |
| H | Arity-2 prefix of \(\lceil\log_2D\rceil\) stages with \(S=4J\,2^{2P}\): funding at every stage and \(p'<\frac94+\frac\varepsilon2\) | \(\varepsilon=\frac12,\frac14,\frac19\) | pass (R.6) |

Note 1. My first grid run failed the assertion \(g_{24D-3}>1/(12D)\)
at the smallest grid points (\(\varepsilon\) below about \(10^{-85}\)).
The cause was my script: computing \(g_d\) as a difference of two
logarithms at 90 digits loses the relative precision needed when \(D\)
exceeds about \(10^{43}\). The proof was not at fault. After computing \(g_d\)
by the atanh series with a rational tail bound, every point passes. The
upper-note review met the same effect.

### R.4 Findings

**1. Two numerical statements are valid but loose, or depend on an
unstated constant (minor).**

- (a) "The increase \(p'-p\) is below \(3\cdot10^{-10}\) in every row"
  (Section 5.2) is a valid bound but a loose one. The checker charges
  \(\log(1-\frac1{2J})\) at every stage. In fact the first floor is exact,
  since \(S=4JU_1\), and later floors lose less than
  \(U_i/\beta_{i-1}\), which is astronomically small. Certified:
  \(p'-p<1.9\cdot10^{-12}\), \(2.8\cdot10^{-14}\), \(5.2\cdot10^{-16}\),
  \(5.0\cdot10^{-18}\) at \(\varepsilon=1,\frac12,\frac14,\frac19\).
  *Fix (optional):* quote these numbers, or say "below \(3\cdot10^{-10}\)
  (a crude bound)".
- (b) The last column of the Part 6 table, and the sentence "with the
  actual counts the crossover is already between \(2^{-20}\) and
  \(2^{-24}\)", use the rational constant \(27/(21\cdot1024\cdot960)\approx
  1.308\cdot10^{-6}\). They do not use the exact coefficient
  \(27\log\frac{21}{20}/(1024\cdot96^{3/2})\approx1.368\cdot10^{-6}\).
  With the exact coefficient, the entry at \(2^{-24}\) is \(0.864\)
  instead of \(0.90\). With either constant, the actual crossover lies
  between \(2^{-23}\) (ratio \(2.43\) with the exact coefficient) and
  \(2^{-24}\). The closed-form claim is exact as stated: the proved bounds
  \(5.32\cdot10^6\) and \(1.3\cdot10^{-6}\) cross between \(2^{-25}\)
  (ratio \(e^{0.99}\)) and \(2^{-26}\) (ratio \(0.917\)).
  *Fix:* name the constant, and say "between \(2^{-23}\) and \(2^{-24}\)".

**2. Statement hygiene in the recommended lemma and theorem (minor).**

- (a) \(f_i=\lfloor\beta_{i-1}/U_i\rfloor\) is a supply only if every
  \(f_i\ge1\). The definition should say "provided
  \(\beta_{i-1}\ge U_i\) for all \(i\)". Item 2 of Lemma S assumes this;
  the recommended Definition 7.1 does not.
- (b) The funding sentence of the recommended lemma should say "the
  recycling supply with source \(S\ge4J\max_i\ldots\)". In the JSON form
  this is only implied by the previous sentence.
- (c) In Theorem 7.3(a), \(\bar A\) is the consumed side, not the supplied
  source side. Add one sentence after the theorem: \(S\) may be much
  smaller than \(\bar A\) (recycling), or larger (a wasteful supply), and
  (a) bounds \(m_*\) and \(r_*\) through \(\bar A\) in every case.

**3. Notation clashes that the note does not list (minor, but some are
visible).** Section 8 of the note handles \(P\), \(L\), \(D_{ij}\),
\(D_0\) and \(\Phi\). The following clashes remain. They are against the
brief or against the sections already written in
`manuscript-shifted-chains/`.

| Letter in the note | Clashes with | Suggestion |
| --- | --- | --- |
| \(S\) (source of the supply), as in \(\MM_S\) | \(S^\pm_{r,b}\) (brief, v5, `preliminaries.tex`) | Call the supplied sides \(A\) and \(B\), as in v5 Definition 2.3: the scheme is \(r_*\MM_A\restr m_*\MM_B\) with \(A=\beta_0\) and \(B=t^{2W}\beta_J\). Keep \(\bar A,\bar B\) for the consumed and produced totals. Then Proposition `prop:chain-counts` is the case \(A=\bar A\). In the corollary, write \(A',B'\) for the recycled scheme. |
| \(Q(y,z)=y^2+4yz+z^2\) (L1) | \(Q_{r,b}\) (brief) | No new letter is needed. The brief's \(\Psi\) satisfies \(\Psi(r,b)+\frac56=Q(r-\frac13,b-\frac13)\), so L1 reads \(\Psi(c,r)+\frac56\le\lambda_d^2(\Psi(r,b)+\frac56)\). The lower-bound potential and the compression-limit potential are then visibly the same quadratic form. (The note calls \(\Psi\) "a different potential"; it differs only by the constant and the square root.) |
| \(t_{ij}\) (profit terms) | the terminal \(t\); v5's degeneration parameter \(t\) | \(\vartheta_{ij}\) (unused in the written sections) |
| \(x=\log(1/\varepsilon)\) in the statement of Theorem 7.3 | \(x=128D/\varepsilon\) in the proof of `thm:main` (`chains.tex`) | Write \(\log(1/\varepsilon)\) in the statement; keep \(x\) local to the appendix proof. |
| \(\delta_{ij}\) | \(\delta(n)\), the rate in Theorem 1.2 and `thm:uniform` | mild; acceptable if local to the appendix |
| \(W\), \(U_i\), \(V_i\), \(\beta_i\) | \(W_\ell\) and the stage tensor \(U=C(r,b)B_X(d)\) (`stages.tex`); \(\beta_\varepsilon\) (`seeds.tex`) | mild, since the sections are far apart; the writer may keep them if each is defined in Section 7 |

**4. The small-source barrier: true inside one chain, false for
composites (resolves an open item; matters for `prop:small-sources`).**
See R.5. The note says only "not checked; state it under the source supply
or drop it". Inside one chain scheme, the barrier survives every supply.
Composition, however, breaks it (small-sources note, Section 4). I agree
with that note's recommendation: drop the source-side barrier, and if a
small-size statement is wanted, use the copy-count bound (its Theorem 2).

**4a. Scope of the source-side statements (minor, but needed for
correctness of the wording).** By composition with the classical algorithm,
any exponent above \(9/4\) is reached with source side 1 (small-sources
note, bootstrapping). So Theorem C(6),(7), the "source side under the best
supply" bracket of Remark 7.5, and the \(\log A'\) bound of Corollary 7.4
are statements about a single chain scheme with a supply. Definition 7.1
already restricts to one chain. Remark 7.5 should still say "for chain
schemes (Definition 7.1)", and it should give the composition remark of
the small-sources note as the reason. The two robust bounds survive
composition (R.5a).

**5. The source side under the best supply is probably
\(\Theta(\varepsilon^{-3}\log^2(1/\varepsilon))\) (remark).** See R.6. The
note's "one-logarithm gap" is correct as a statement about what is
proved. The missing logarithm most likely comes from the construction (the
upper bound), not from a weakness of the lower bound.

**6. Everything else checks out.** Specifically:

- the identification of Theorem 5 of the lower note as a bound on
  \(\bar A\);
- both routes to \(m_*\ge\bar A^3\), and the robust copy-count statement;
- the range \(0<\varepsilon<1/9216\);
- the funding lemma and \(\tilde U=D^{2nk}\) for the main chain;
- every constant of Proposition M and Corollary R;
- the necessity of the source-supply hypothesis for the source-side bound;
- the factor \(1.34\) for the seeds;
- the table of Section 5.2, to all printed digits.

I agree with the note's wording for result 4(b) of the introduction. The
robust "optimal order" statement concerns \(r_*\) and \(m_*\). The source
side has that order only under the source supply.

### R.5 The barrier inside one chain, for every supply (proved here; computer-assisted)

*Setting.* Use the two count models of the gate note: one block type per
stage, repeated (common: one \((n,k)\) for all stages, \(P=nk\); blocked:
\((n_i,k_i)\) with \(n_ik_i\mid P\)). Allow any arities \(d_i\ge2\),
children, crops, swaps and terminal, and any supply in the sense of
Lemma S. Call a stage *gaining* if \(M_{\max}(n_i,d_i)>d_i^{n_i}\), and let
\(G\) be the set of gaining stages. Let \(\Phi(p_0)\) be the gate's
normalized margin (gate Lemma 1). Write \(\alpha=40/49\),
\(m(n,d,k;p_0)=3a_d+C(n,d,k,M_{\max};p_0)\), and
\(e(p_0)=\min_{t\ge1}[3\log(\alpha t+1-\alpha)-p_0\log t]\).

**Proposition B.** In both models, every chain scheme with any supply
whose source side satisfies \(S\le2^{128}\) and \(B'>S\) has pooled
exponent \(p'\ge p_w=2.97696088251553\ldots\). The bound is attained by the
one-stage witness \((43,23)\to(1,43)\), \(d=2\), \(n=32\), \(k=2\), with
the source supply \(S=2^{128}\).

*Proof.*

1. **Reduction.** By Lemma S(4), \(p'\ge p\), where \(p\) is the
   source-supply exponent of the same chain. By gate Lemma 1,
   \(\Phi(p_0)>0\) implies \(p>p_0\).
2. **Funding.** \(S\ge U_1f_1\ge2^{2P}\), so \(P\le64\). A non-gaining
   stage has \(V_l\le U_l\), because its type count is at most
   \(M_{\max}\le d^n\). So \(\beta_l=f_lV_l\le\beta_{l-1}\): non-gaining
   stages never enlarge the bank. A gaining stage has
   \(V_l\le q_l^{2P}\). Hence every stage \(i\) satisfies
   \(d_i^{2P}\le\beta_{i-1}\le S\prod_{l\in G,\,l<i}(q_l/d_l)^{2P}\). In
   particular, the first gaining stage has \(d^{2P}\le2^{128}\).
3. **Two facts about the gate bound.** By gate Lemmas 3, 6 and 8,
   \(\Phi(p_0)\ge\sum_{i\in G}C_i+\min_{t\ge1}[3\log(\alpha zt+(\frac43-\alpha)z-\frac13)-p_0\log t]\),
   with \(z=\prod_i\lambda_{d_i}^{-1}\) over all stages and \(C_i\)
   evaluated at \(M_{\max}\).
   - (a) Replacing \(z\) by \(cz\) with \(c\ge1\) raises the minimum by at
     least \(3\log c\), because
     \(c(\alpha zt+(\frac43-\alpha)z)-\frac13\ge c(\alpha zt+(\frac43-\alpha)z-\frac13)\).
   - (b) If \(z\ge1\), the minimum is at least \(3\log z+e(p_0)\), since
     \((\frac43-\alpha)z-\frac13\ge(1-\alpha)z\).
4. **Cases at \(p_0=p_{\rm hi}=2976961/10^6>p_w\).** Part G computes all
   constants with certified intervals.
   - \(G=\emptyset\): then \(p\ge3\) (gate Lemma 7).
   - \(|G|\ge3\): by (b), after dropping the non-gaining factors of \(z\),
     \(\Phi\ge\sum_{i\in G}m_i+e\ge3m_{\min}+e=0.215>0\). Here
     \(m_{\min}=0.2411\) is the minimum over all gaining \((n,d,k)\) with
     \(nk\le64\), attained at \((32,2,2)\), and \(e(p_{\rm hi})=-0.5081\).
   - \(|G|=2\) and \(m_1+m_2+e>0\): the same argument applies.
   - \(|G|=2\), the remaining 4 pairs (from \((30,2,2)\), \((31,2,2)\)
     and \((32,2,2)\), so \(P\ge60\)):
     - with exactly two stages, the two-stage endpoint bound below gives
       \(\Phi\ge0.2198\);
     - with a further stage, that stage is non-gaining and, by step 2, has
       arity at most \(2^{64/P}(q_1/d_1)(q_2/d_2)\le8\). Then (a) gives
       \(\Phi\ge-0.0079+3a_8\ge0.494\), where \(-0.0079\) is the pair bound
       with \(z=1/(\lambda_1\lambda_2)\).
   - \(|G|=1\) with a further stage: the gaining stage \((n,d,k)\) has
     \(d^{2P}\le2^{128}\). The further stage has arity
     \(d'\le2^{64/P}(d+2)/d\), with \(P\ge nk\). The one-stage gate bound
     plus \(3a_{d'}\) is at least \(0.47\) over all such \((n,d,k)\); the
     worst case is \((17,2,1)\) with \(d'\le27\).
   - \(|G|=1\) and exactly one stage: here \(\bar A=d^{2P}\le S\le2^{128}\).
     The gate review's exact one-stage search (finding 1 of the gate
     review, certified by two arithmetic paths) gives \(p\ge p_w\).

So \(p'\ge p\ge p_w\). \(\square\)

**Lemma (two-stage endpoint bound; new, proved here).** Take a chain with
exactly two stages, of arities \(d_1\) and then \(d_2\), with any children,
crops and swaps, source size \(s\) and terminal \(t\). Put
\(\varphi(r,c)=(1+\frac1{d_1})r+(1+\frac2{d_1})c-1-\frac1{d_1}\). Then
\[
s\ \ge\ \min\Bigl\{\varphi\bigl(\tfrac{t+d_2+1}{d_2},t\bigr),\ \varphi\bigl(t,\tfrac{t+d_2+1}{d_2}\bigr),\ \varphi\bigl((1+\tfrac2{d_2})t,1\bigr),\ \varphi\bigl(1,(1+\tfrac2{d_2})t\bigr)\Bigr\}.
\]

*Proof.* Let the first stage act on \((r_1,b_1)\) with child \(c_1\).
Legality gives \(b_1\ge((d_1+2)c_1+r_1-1)/d_1\), so
\(s=r_1+b_1-1\ge\varphi(r_1,c_1)\), and \(\varphi\) increases in both
arguments. The middle pair \(\{r_2,b_2\}\) is a crop of \((c_1,r_1)\) in
some order. The second stage has child \(c_2\ge1\), and
\(t\le\max(c_2,r_2)\).

- If \(t\le r_2\), then
  \(b_2\ge((d_2+2)c_2+r_2-1)/d_2\ge(t+d_2+1)/d_2\). Depending on the
  order, \((c_1,r_1)\ge(t,\frac{t+d_2+1}{d_2})\) or
  \((c_1,r_1)\ge(\frac{t+d_2+1}{d_2},t)\) componentwise.
- If \(t\le c_2\), then \(b_2\ge(d_2+2)t/d_2\) and \(r_2\ge1\). This gives
  the last two terms. \(\square\)

For \(d_1=d_2=2\) and \(t\ge3\) the bound is \(s\ge\frac52t+\frac32\);
smallest parents attain it for odd \(t\) (checked by brute force for
\(t\le21\)). It is far stronger than gate Lemma 3 for two stages. That is
why the pairs that the relaxation leaves open close with margin \(0.22\).

*Shorter versions.*

- \(p\ge29/10\) for every supply: \(|G|\ge2\) closes because
  \(2m_{\min}+e=0.2858\cdot2-0.3196=0.252>0\). \(|G|=1\) closes by the
  gate census, whose relaxed margins are all positive at \(29/10\); by
  step 2, the single gaining stage lies in the census.
- \(p\ge119/40\) for every supply: \(|G|\ge3\) closes by \(0.225\). The
  pairs close by the relaxed bound itself (worst \(+0.0024\)).
  For \(|G|=1\), use the census. Its open cases are forced arity-2 cases
  with \(P\ge33\). They close by gate Lemma 4 if there is one stage. Any
  further stage has arity at most 7 by step 2, and \(3a_7=0.566\) exceeds
  the census deficit \(0.2455\).

*Relation to the small-sources note.* That note's Theorem 1 proves
\(p\ge p_w\) for every chain scheme with \(P\le64\), with no funding
argument and for general blocks. Since \(S\le2^{128}\) forces
\(P\le64\), it implies Proposition B. The two proofs share the case
structure. Their constants were computed by independent code and agree:
\(3a_2+c^*(2)>0.241111\) against my \(m_{\min}=0.2411\); the
\((2,2)\) pair bound \(-0.007919\) against \(-0.0079\); the sharp
\((2,2)\) bound \(0.219802\) against \(0.2198\). Its four affine forms
\((\frac52,\frac32),(\frac{11}4,\frac34),(3,\frac12),(4,0)\) are my two-stage
endpoint bound at \(d_1=d_2=2\). My lemma covers every pair of arities,
but only for chains with exactly two stages. Proposition B is therefore an
independent check of that theorem in the gate's count models, not a new
result for the paper.

*Recommendation (revised after reading the small-sources note).* Do not
state the source-side barrier in the paper, even "for every supply". The
small-sources note composes the witness with a second one-stage chain that
takes its auxiliary from the witness's output (its Lemma C, a two-line
consequence of the same principal-block argument as Lemma S). The result
has source side \(2^{128}\) and \(p<2.87\); with the classical algorithm
as the seed, the source side is 1. I did not rerun its script. I checked
its Lemma C by hand: it is Lemma S's step with one stage. I also checked
its exponent inequality \(p\ge\min(p_1,p_2)\): it follows from
\(\log(B_2f/A_1)\le\log(B_1/A_1)+\log(B_2/A_2)\). If a small-size
statement is wanted, use its Theorem 2 (copy counts), which composition
does not break.

### R.5a The robust bounds survive composition (proved here)

**Proposition.** Let \(0<\varepsilon<1/9216\). Build a relative scheme
from chain schemes (Definition 7.1, any supplies) and classical algorithms
\(N^3\MM_1\restr\MM_N\) by recycling, composition (small-sources note,
Lemma C) and tensor products. If its pooled exponent \(p\) is at most
\(\frac94+\varepsilon\), then
\[
\log r_*>\log m_*>3.9\cdot10^{-6}\varepsilon^{-9/2}\log^3(1/\varepsilon),\qquad
\log(B/A)>9.8\cdot10^{-5}\varepsilon^{-4}\log^2(1/\varepsilon).
\]

*Proof.* Under composition and tensor products, \(r_*\), \(m_*\) and
\(L=\log(r_*/m_*)\) are products and sums over the parts, and
\(\log(B/A)\) is at most the sum of the parts' values. Hence
\(p\ge\min\) of the parts' exponents, over the parts with \(B>A\). A part
with \(B\le A\) only raises \(p\), because \(r_*\ge m_*\) for every part.
Recycling keeps \(r_*,m_*\) and does not lower \(p\) (Lemma S(4)).
Classical parts have \(p=3>\frac94+\varepsilon\). So some part is a chain
scheme \(\mathcal C\) with exponent at most \(\frac94+\varepsilon\), and
Theorem C applies to it. Then
\(m_*\ge m_*(\mathcal C)>3.9\cdot10^{-6}\varepsilon^{-9/2}x^3\), and
\(r_*/m_*\ge r_*(\mathcal C)/m_*(\mathcal C)>1\). Also
\(\log(B/A)=L/p\ge L(\mathcal C)/p_0\ge\frac52P_{\mathcal C}\log s_{\mathcal C}\),
which exceeds the bound by the proof of Proposition T applied to
\(\mathcal C\). \(\square\)

So the robust bounds are statements about every algorithm the
construction can assemble in this way. The source-side bounds hold only for
single chain schemes (finding 4a).

### R.6 An arity-2 prefix removes the extra logarithm (outline; certified instances)

The recycled main chain needs \(S=4JD^{2nk}\), because its first stage has
arity \(D\). Instead, prepend \(\lceil\log_2D\rceil\) stages of arity 2,
built backwards by smallest parents from the main chain's source pair.
Each such stage multiplies the bank by about \(2^{2P}\). So
\(S=4J\,2^{2P}\) funds the whole chain, and \(\log S\) drops by the factor
\(\log_2D\). Each prefix stage raises the normalized numerator by about
\(3\log\mu_2\approx1.567\) and the denominator by \(\log2-a\approx0.693\).
The net cost is about \(0.008\) per stage against \(G\ge64/\varepsilon\),
which is far inside the slack \((\frac12-\frac{719}{1988})\varepsilon\)
when \(\lceil\log_2D\rceil\) is moderate. Part H certifies:

| \(\varepsilon\) | prefix stages | \(p'<\) | digits of \(S\) with prefix | without |
| ---: | ---: | ---: | ---: | ---: |
| 1/2 | 2 | 2.2643733 | \(1.42\cdot10^8\) | \(2.25\cdot10^8\) |
| 1/4 | 2 | 2.2576263 | \(1.45\cdot10^9\) | \(2.91\cdot10^9\) |
| 1/9 | 3 | 2.2535592 | \(1.94\cdot10^{10}\) | \(5.03\cdot10^{10}\) |

A full proof for all \(\varepsilon\) would have to add the prefix to the
charge table of the main theorem. This is routine but not written. The
cost per stage is \(O(\varepsilon)\cdot10^{-4}\), and there are
\(O(\log(1/\varepsilon))\) prefix stages. Until such a proof exists, the
paper should keep the note's bracket for the best supply (for chain
schemes; finding 4a). Given the composition remark, this bracket matters
little. I would mention the prefix at most in one sentence, or not at all.

### R.7 What I could not verify

- The stage relation (D′), the main theorem and Lemma 1 of the seeds note,
  as for the checker. Proposition M and Corollary R stay conditional on
  them.
- The gate count models and the gate review's exact one-stage search. R.5
  uses them; my script does not redo the one-stage search.
- The arity-2 prefix for all \(\varepsilon\) (R.6).
- The small-sources note's script and its Theorem 2. I used only its Lemma
  C and its exponent inequality, which I re-derived, and its certified
  witnesses as reported.

### R.8 Statements I endorse

All are proved here or in the note. The items that depend on the main
theorem are marked conditional.

- **Definition (chain schemes and supplies)**, as recommended in Section 6,
  with finding 2(a), and with the supplied sides named \(A,B\)
  (finding 3).
- **Lemma (supplies; forward recycling)**, as recommended, with finding
  2(b). *Proved; checked as a literal restriction twice, with different
  toy stages.*
- **Theorem (resource lower bound within the construction).** For
  \(0<\varepsilon<1/9216\), and for every chain scheme and every supply
  with pooled exponent at most \(\frac94+\varepsilon\):
  - (a) \(\log r_*>\log m_*\ge3\log\bar A>3.9\cdot10^{-6}\varepsilon^{-9/2}\log^3(1/\varepsilon)\);
  - (b) \(\log(B/A)>9.8\cdot10^{-5}\varepsilon^{-4}\log^2(1/\varepsilon)\);
  - under the source supply, \(\log A=\log\bar A>1.3\cdot10^{-6}\varepsilon^{-9/2}\log^3(1/\varepsilon)\).

  Add the sentence of finding 2(c). *Proved.*
- **Corollary (recycled main construction)**, as recommended. *Conditional
  on the main theorem.*
- **Proposition (robust bounds survive composition)**, R.5a. *Proved.*
  Recommended as one sentence after Theorem 7.3, or as part of the
  composition remark that the small-sources note proposes.
- **Remark (orders).** As recommended, with findings 1(b) and 4a. Copy counts are
  \(\Theta(\varepsilon^{-9/2}\log^3)\), and \(\log(B/A)\) is
  \(\Theta(\varepsilon^{-4}\log^2)\), for every supply. The source side is
  \(\Theta(\varepsilon^{-9/2}\log^3)\) under the source supply, and for the
  best supply it lies between \(5\cdot10^{-4}\varepsilon^{-3}\log^2\) and
  \(O(\varepsilon^{-3}\log^3)\) (probably \(\Theta(\varepsilon^{-3}\log^2)\),
  R.6). The source-supply hypothesis is necessary for
  \(\varepsilon\le2^{-26}\). The seed size changes by less than a factor
  \(1.34\).
- **Proposition B (one chain, every supply, \(S\le2^{128}\Rightarrow p\ge p_w\))**,
  R.5. *Proved; computer-assisted.* It is implied by Theorem 1 of the
  small-sources note and confirms that theorem's constants independently.
  **Not for the paper:** the source-side barrier should be dropped
  (finding 4).
