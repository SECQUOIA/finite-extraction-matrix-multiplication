# Verification note: coefficient sizes, seeds and one algorithm for all sizes (key "seeds")

Date: 18 October 2026. Nothing under `manuscript/`, `upstream/`,
`formalization/`, or any existing file was changed. New files: this note and
[`experiments/shifted_chains_check_seeds.py`](../experiments/shifted_chains_check_seeds.py).

Sources checked: [round9-multiscale-height](round9-multiscale-height.md) and
its [review](round9-review-multiscale-height.md),
[round11-ramp-height](round11-ramp-height.md) and its
[review](round11-review-ramp-height.md), the schedule of
[round11-ramp-bounds](round11-ramp-bounds.md), and v5: Lemma 2.4 (pooled
recursion), Lemma 8.6 (descent), Corollary 8.7 and Remark 8.8 (seeds),
Lemma 9.1 (rational interpolation), Theorem 9.2 (explicit seed), Theorem 9.3
(preprocessing), Lemma 9.4 and Propositions 9.5–9.6 (seed recursion),
Corollary 9.7 and Remark 9.8 (one algorithm for all sizes). Theorem numbers
are those of the compiled v5 (`manuscript/build/main.aux`).

Status labels:

- **proved here**: a complete proof, or a proof outline whose omitted steps
  are routine, is given in this note. Outlines are marked "(outline)".
- **checked numerically**: confirmed by the script with exact integers,
  Fractions, or certified rational enclosures of logarithms.
- **taken from the notes unchecked**: used as an input and not verified here.

## 1. Verdict and summary

**(a) Encoded resources (verified, with scope corrections).** The three
claimed bounds hold for the complete relative scheme of the round-11
family, for the explicit common-denominator generator described in the
notes: common numerator and denominator bit lengths at most $A^{24}$, exact
generation in at most $A^{700}$ bit operations, and $t+A^{28}+1$
significand bits for absolute accuracy $2^{-t}$. I re-derived the
denominator ledger, the composition rule, the guards and the polynomial
envelopes (§3). I found no mathematical error. The corrections concern
scope and looseness:

- the precision bound covers **one** classical execution of the full
  relative batch, not the recursive algorithm (§3.5);
- the bounds are very loose. The true bit lengths are at most
  $2^{O(\varepsilon^{-3/2}\log^2(1/\varepsilon))}$, far below
  $A^{24}=2^{\Theta(\varepsilon^{-9/2}\log^3(1/\varepsilon))}$ (Remark 6);
- the resource guard $r_*<A^{20}$ improves to $r_*\le A^{35/4}$ (Lemma 1).

**(b) An explicit seed (new, proved here).** For rational
$\varepsilon\in(0,1]$, unrolling v5's pooled recursion for the shifted-chain
scheme at side
$$
n_0=(\Xi+1)^{\lceil2/\varepsilon\rceil},\qquad
\Xi=r_*(1+r_*m_*)\,n_*^3,\qquad n_*=\lceil AB/(B-A)\rceil+1,
$$
gives an exact rational bilinear algorithm for $n_0\times n_0$ matrix
multiplication with fewer than $n_0^{9/4+\varepsilon}$ products
(Theorem 7). The seed side is singly exponential:
$$
\frac{24}{\varepsilon}\log A\;\le\;\log n_0\;\le\;
27\Bigl\lceil\frac2\varepsilon\Bigr\rceil\log A
\;<\;2.1\cdot10^{11}\,\varepsilon^{-11/2}\log^3\frac{4096}{\varepsilon}.
$$
The unrolling has fewer than $1+313\,\varepsilon^{-3/2}\log(4096/\varepsilon)$
recursion depths (Proposition 8). The extra factor $1/\varepsilon$ over
$\log A$ is intrinsic to unrolling this scheme (Remark 10). For comparison,
v5's seed has $\log\log d_0=\Theta(1/\varepsilon)$.

**(c) One algorithm for all sizes (new, proved here).** Running the pooled
recursion directly, with explicit constants (Lemma 11) and an allowance
$1/v(n)$ chosen by a computable rule, gives one algorithm with cost
$n^{9/4+\delta(n)}$ (Theorem 12), where
$$
\delta(n)=O\!\left(\frac{(\log\log n)^{6/11}}{(\log n)^{2/11}}\right),
\qquad\text{explicitly}\quad
\frac{0.51}{v(n)}\le 244\,\frac{\ln(4096X)^{6/11}}{X^{2/11}}
\quad(X=\lfloor\log_2n\rfloor\ge2\cdot10^{18}).
$$
The preprocessing (generating the scheme) is counted, in v5's model of
Turing-machine steps plus field operations. It needs no assumption beyond
the generator bound of part (a). It costs $A^{O(1)}=n^{O(1/v(n))}$ steps.
v5's Remark 9.8 gives $\delta(n)=\Theta(1/\log\log n)$ for its own
construction. Going through a square seed instead loses the factor
$1/\varepsilon$ of part (b) and gives only exponent $2/13$ (Remark 13).
Within this algorithm design, $2/11$ cannot be improved, assuming two
claims of the notes that I did not check (Remark 14).

Section 8 lists the problems found. None changes a claimed result.

## 2. Setting, notation and inputs

### 2.1 Notation

I use v5's notation: $\MM_d$, $B_X(d)$, $C(r,b)$, $Q_{r,b}=S^+_{r,b}S^-_{r,b}$,
$\restr$ (restriction), $\degen$ (degeneration), and $mT$ for a direct sum.
Logarithms are natural unless written $\log_2$. The letter $n$ is v5's
matrix side. The notes use $n$ for the number of copies per sign; here that
number is $N$.

### 2.2 The scheme $S_\varepsilon$

For rational $\varepsilon\in(0,1]$ the round-11 schedule is
$$
D=\lceil\sqrt{4/\varepsilon}\,\rceil,\quad R=8D,\quad
L=\lceil64D/\varepsilon\rceil,\quad x=128D/\varepsilon,\quad
H=\mathrm{bitlength}(\lceil x\rceil),\quad
N=k=\lceil256DH/\varepsilon\rceil,\quad J=2(R-1)+L .
$$
The chain is read backwards from $(1,1)$. It uses arities $3j-1,3j$ for
$j=1,\dots,R-1$ and then $L$ times arity $D$. Each reverse step takes the
smallest parent $(r,b)\mapsto(b,\lceil((d+2)r+b-1)/d\rceil)$. Read
forwards, there are $J$ levels with arities $d_1,\dots,d_J<24D$ and source
pair $(r_0,b_0)$; put $s=r_0+b_0-1$ and $q_i=d_i+2$. Level $i$ keeps a
maximal type with weights $(d_i-1,2,1)$, so
$$
M_i=\max_{\ell+o+u=N}\frac{N!}{\ell!\,o!\,u!}(d_i-1)^\ell2^o,\qquad
\frac{q_i^N}{(N+1)^2}\le M_i\le q_i^N,\qquad E_i=1+6k(M_i-1).
$$
The relative scheme $S_\varepsilon\colon r_*\MM_A\restr m_*\MM_B$ has
$$
A=\prod_id_i^{2Nk},\qquad B=\prod_iM_i^{2k},\qquad
r_*=s^{6Nk}\prod_i(2M_i-1)^{6k}E_i,\qquad m_*=\prod_iM_i^{6k},
\tag{2.1}
$$
and pooled exponent $p=\log(r_*/m_*)/\log(B/A)$ (v5 Definition 2.3). Put
$\Lambda=\log(4096/\varepsilon)$, $G=\sum_i\log(q_i/d_i)$,
$a=2\log(N+1)/N$ and $\theta=Ja/G$.

### 2.3 Inputs from the other topics

- **(I1) Stage relation and composition.** *Taken from the notes;
  verified in [shifted-chains-check-maps](shifted-chains-check-maps.md).*
  Each legal level gives a degeneration
  $(2M-1)^6Q_{r,b}^{\otimes N}\MM_{d^{2N}}\degen M^6Q_{c,r}^{\otimes N}\MM_{M^2}$
  of degree at most $6(M-1)$. It is built from integer chain bases, the
  crop and three-block reset, a type restriction, Lu's separator (v5
  Lemma 9.1(b)) in each of the six orientations, and coordinate
  permutations. Each stage is exactified separately at power $k$ (v5
  Lemma 9.1(c)), the stages are composed, and the source is decomposed by v5
  Lemma 9.1(a). This gives $S_\varepsilon$ with rational coefficients and the
  counts (2.1). Here I re-checked only the parts that the height bound uses
  directly: the separator, exactification and convolution identities with
  their denominators, and the unimodularity of the chain bases (§6).
- **(I2) The uniform bound.** *Taken from the notes; verified in
  [shifted-chains-check-upper](shifted-chains-check-upper.md); re-checked
  numerically here.* It gives
  $p\le\Phi:=\log(2r_*/m_*)/\log(B/A)<\tfrac94+\tfrac{719}{1988}\varepsilon$.
  Its proof also gives $G\ge64/\varepsilon$, $J/G\le5D/4$,
  $\theta\le15\varepsilon/512$, and
  $\log A\le2NkJ\log(24D)<2.551\cdot10^9\varepsilon^{-9/2}\Lambda^3$.
  Finally, $M_i\ge q_i^N/(N+1)^2$ gives
  $$\log(B/A)\ge2Nk\,G(1-\theta).\tag{2.2}$$

### 2.4 Resource relations

**Lemma 1 (proved here).** For every rational $\varepsilon\in(0,1]$:

1. $m_*=B^3$;
2. $A\ge2^{2NkJ}$, and $N=k\ge4608$, $J\ge158$;
3. $2A\le B\le A^2$; indeed $\log(B/A)\ge124Nk$;
4. $4\le(B/A)^2\le r_*/m_*=(B/A)^p\le(B/A)^{11/4}$;
5. $r_*\le A^{35/4}$ (the notes have $r_*<A^{20}$);
6. $A<n_*\le3A$, where $n_*=\lceil AB/(B-A)\rceil+1$;
7. $A^{12}\le\Xi$ and $\Xi+1\le A^{27}$, where $\Xi=r_*(1+r_*m_*)n_*^3$.

*Proof.* (1) holds by definition. (2): every $d_i\ge2$, and $N$, $J$ are
nonincreasing in $\varepsilon$ with values $4608$ and $158$ at
$\varepsilon=1$. (3): the multinomial theorem gives $M_i\le q_i^N$, and
$q_i=d_i+2\le d_i^2$ for $d_i\ge2$, so $B\le A^2$. By (2.2),
$\log(B/A)\ge2Nk\cdot(64/\varepsilon)(1-15/512)\ge124Nk$. (4): $p\ge2$ by
Step 1 of v5 Lemma 2.4, and $p<9/4+\varepsilon/2\le11/4$ by (I2).
(5): $r_*=m_*(B/A)^p\le B^3(B/A)^{11/4}\le A^6A^{11/4}$. (6):
$AB/(B-A)>A$, and $B\ge2A$ gives $AB/(B-A)\le2A$, so $n_*\le2A+2\le3A$.
(7): $r_*\ge m_*=B^3\ge A^3$, so $\Xi\ge r_*^2m_*n_*^3\ge A^{12}$. Also
$1+r_*m_*\le2r_*m_*$, so $\Xi\le54r_*^2m_*A^3\le54A^{53/2}$, and
$\Xi+1\le55A^{53/2}\le A^{27}$ because $A\ge2^{540}>55^2$. $\square$

*Checked numerically* on the literal schedules for
$\varepsilon=1,\frac12,\frac14,\frac18$: there
$\log r_*/\log A\le5.78$ and $\log B/\log A\le1.53$ (table in §4.5).

## 3. Part (a): coefficient heights, generation and precision

### 3.1 The maps as a product of layers

Fix one leg; the other two are analogous. The leg-1 substitution matrix of
$S_\varepsilon$ has rows indexed by the $r_*A^2$ source variables and
columns by the $m_*B^2$ target variables. It is a product
$U=L_0L_1\cdots L_T$. Each layer has the form
(block-diagonal over copies) $\otimes$ (one primitive matrix on one tensor
factor) $\otimes$ (identity). The primitive matrices are:

1. **Source decomposition** (v5 Lemma 9.1(a)). For each of the $6Nk$
   oriented factors $C(r_0,b_0)^\pi$, the leg that lands on global leg 1
   gets a stack of $s$ evaluation vectors. These are integers $\ell^\alpha$
   on the first two legs of $C$. On the third leg they are the cardinal
   coefficients $\varpi_{s,\ell,\gamma}$, whose denominators divide $(s-1)!$.
   Each global leg receives $2Nk$ cardinal stacks.
2. **Chain bases.** For the $y$- and $z$-legs of each oriented physical
   tensor $C(r,b)B_X(d)$, the quotient lifts, kernel vectors and their
   inverses have entries in $\{0,\pm1\}$ (checked in §6).
3. **Crop, three-block reset and type projection.** These are coordinate
   selections with 0/1 entries.
4. **Separators** (v5 Lemma 9.1(b)). There is one in each of the $6k$
   oriented copies, and each acts on all three legs. On a fixed global leg,
   $2k$ of them act by $\alpha$-entries $\varpi_{M,g'+1}(\ell)$, with
   denominator dividing $(M_i-1)!$. Another $2k$ act by $\beta$-entries
   $(\ell-g-1)^e\,t^{-e}$, which are Laurent in $t$. The last $2k$ act by
   $\gamma$-entries $[\xi^{e'}]\varpi_{2M_i-1,\ell}(g+1+\xi)\,t^{e'}$, with
   denominator dividing $F_i=(2M_i-2)!$. All are stacked over the
   $2M_i-1$ separator copies.
5. **Exactification** (v5 Lemma 9.1(c)). A stack over the nodes
   $t=1,\dots,E_i$, and on one leg the integer weights
   $(-1)^{t-1}\binom{E_i}t$.
6. **Permutations.** Middle-block reversals, factor reordering, sign
   pairing and the canonical swap $Q_{r,c}\cong Q_{c,r}$.

The notes count at most $24Nk+24k+60$ layers per stage. Any bound of order
$Nk+k$ suffices below. The notes assert this count but never list the maps
one by one; the list above is my reconstruction, and it agrees with the
stage relation of (I1).

### 3.2 The common denominator

**Proposition 2 (proved here).** The integer
$$
\mathcal D=((s-1)!)^{6Nk}\prod_{i=1}^J
\bigl((2M_i-2)!\bigr)^{12k}\,(E_i!)^{6k(M_i-1)}
$$
is a common denominator of every entry of all three maps of
$S_\varepsilon$. It is also a common denominator of every partial product
$L_0\cdots L_j$ formed by the generator.

*Proof.* On one leg, the source contributes $((s-1)!)^{2Nk}$. Stage $i$
contributes at most $((M_i-1)!)^{2k}F_i^{2k}$ from the $\alpha$- and
$\gamma$-factors. At any node $t\le E_i$, the $2k$ $\beta$-factors on that
leg contribute $t^{\sum e_j}$ with $\sum e_j\le2k(M_i-1)$, and this divides
$(E_i!)^{2k(M_i-1)}$. Integer layers contribute nothing. Stacks and direct
sums share one denominator, and products of layers multiply their
denominators ($P/a\cdot Q/b=PQ/(ab)$). Multiplying the three legs'
denominators gives a divisor of $\mathcal D$. $\square$

*Checked numerically:* for $M\le4$, the separator identities of v5
Lemma 9.1(b), the stated denominators, and a full tensor-level check with
random sector tensors and binomial exactification. The exactification
moment identities hold for $E\le40$, and the rational convolution
decompositions for $r,b\le4$. Finally, the stage factor
$F_i^{12k}(E_i!)^{6k(M_i-1)}$ of $\mathcal D$ is divisible by the $6k$-th
power of $(M_i-1)!\,F_i\,\mathrm{lcm}(1,\dots,E_i)^{M_i-1}$ for $M_i\le4$,
$k=1,2$.

### 3.3 The $A^{24}$ bound

**Proposition 3 (proved here; notes' claim confirmed).** Every entry of
every partial product is $c/\mathcal D$ with an integer $c$,
$|c|<2^{A^{24}}$, and $\mathcal D<2^{A^{24}}$.

*Proof.* Put $h=\log_2A$. Lemma 1 gives the guards that the notes use:
$2NkJ\le h\le A/2$, so $N,k,J\le A$ and $6Nk\le3h\le A$;
$M_i\le q_i^N\le d_i^{2N}\le A$; $E_i\le1+A^2\le A^3$; and
$s^{6Nk}\le r_*\le A^{35/4}$, so $s\le A^4$. With
$\log_2(m!)\le m\log_2m$:
$$
\log_2\mathcal D\le D_{\log}:=4A^5h+A\bigl(24A^2(h+1)+18A^5h\bigr).
$$
**Entry values.** A source primitive is at most $(s+1)^s$ in absolute
value, so its $\log_2$ is at most $S_{\log}=A^4(1+4h)$. A separator
primitive is at most $(4M_iE_i)^{4M_i}$, and an exactification weight at
most $2^{E_i}$; both $\log_2$'s are at most $R_{\log}=4A(2+4h)+A^3$.
Integer layers are at most 1.

**Widths.** Every intermediate space has dimension below $A^{200}$; the
notes' product of the convolution, auxiliary, label and raw-word
dimensions is below $A^{58}$.

**Layers.** There are at most $A^4$ layers, counting all stages, the source
and the terminal map.

For a product of matrices, $|(P_1\cdots P_T)_{ij}|\le\prod_l(w_l\max|P_l|)$,
where $w_l$ is the inner dimension. Hence every entry of every partial
product has $\log_2|{\rm value}|\le V_{\log}=A^4(S_{\log}+R_{\log}+200h)$.
The numerator is the value times $\mathcal D$, so its bit length is at most
$D_{\log}+V_{\log}+1$. Substituting $h\le A/2$ (both envelopes increase
with $h$) gives exactly the notes' polynomial
$2A^9+A^8+10A^7+10A^6+108A^5+12A^4+24A^3+2$ for $D_{\log}+V_{\log}+2$.
After the substitution $A=x+16$, the difference $A^{24}$ minus this
polynomial has positive coefficients. $\square$

*Checked:* the script recomputes the polynomial from $D_{\log}$ and
$V_{\log}$ symbolically and confirms that it equals the notes' polynomial.
It then checks positivity after the shift.

The value bounds deserve one remark. The notes' "magnitude at most
$(4ME)^{4M}$" means the absolute value of the rational entry, not of its
numerator over $\mathcal D$. For example, a $\beta$-entry cleared by
$(E!)^{M-1}$ has a numerator of about $6kM^2\log E$ bits. The proof
correctly adds $D_{\log}$ separately, so this is a wording issue only.

### 3.4 Generation

**Proposition 4 (proved here; outline).** The generator outputs the three
maps of $S_\varepsilon$, as integer numerators over the common denominator
$\mathcal D$, using at most $A^{700}$ bit operations.

*Proof outline.* Generating the primitive arrays is cheap. Cardinal
polynomials come from multiplying linear factors; there are no inverse
Vandermonde matrices, no gcds and no lcms. Then multiply at most $A^4$
layers of width below $A^{200}$, which takes at most $A^{604}$ integer
operations. By Proposition 3, every intermediate integer has at most
$A^{24}$ bits, so a schoolbook operation costs at most $A^{50}$ bit
operations. Adding indexing and storage keeps the total below $A^{700}$.
With the width bound $A^{58}$, the same argument gives about $A^{230}$. On
a multitape Turing machine the cost is at most a constant times
$(A^{700})^2$ steps, by the simulation argument of v5 Remark 9.8. $\square$

The notes' further claims are consistent with these bounds: at most
$3r_*A^2m_*B^2\le A^{33}$ entries in the three arrays, at most $A^{34}$
after classical scalarization, and fewer than $A^{40}$ operations for one
execution of the batch.

### 3.5 Precision of one batch

**Proposition 5 (proved here; notes' claim confirmed, scope clarified).**
Consider one execution of the complete relative batch, with every source
product $\MM_A$ computed classically. Then $P=r_*A^3\le A^{12}$ bilinear
products are used, on input vectors of length $D_{\rm tar}=m_*B^2\le A^{10}$.
Use binary round-to-nearest with $b=t+A^{28}+1$ significand bits, and
suppose there is no overflow or underflow. Then
$$
\|\widehat Z-Z\|_{\max}\le2^{-t}\|X\|_{\max}\|Y\|_{\max}.
$$
An exponent range of magnitude $A^{30}+20(e+t+1)$ suffices for inputs
with exponents in $[-e,e]$.

*Proof.* As in the notes. A contribution path has at most
$T=2D_{\rm tar}+P+4\le A^{24}$ rounding factors. The absolute path envelope
is $\Gamma\le PD_{\rm tar}^22^{3A^{24}}$. Then
$\frac{Tu}{1-Tu}\Gamma\le2^{-t}$ follows from
$1+67\log_2A+3A^{24}<A^{28}$. The dyadic-grid argument for the exponent
range is correct: each path has at most three coefficients and two inputs.
Both polynomial inequalities are checked by positivity after the shift.
$\square$

**Scope.** This is the precision for **one application** of the relative
batch. It is not a precision bound for the recursive algorithm. The
recursion multiplies the magnitude envelope by about $2^{3A^{24}}$ per
depth. The analogue of v5 Proposition 9.6 therefore needs about
$t+3\ell_{\max}(A^{24}+O(\log A))$ bits for $\ell_{\max}$ depths. I did not
carry out that analysis in full (§7).

### 3.6 How loose the bounds are

**Remark 6 (proved here; outline).** The real bit lengths are far below
$A^{24}$. From Proposition 2,
$\log_2\mathcal D\le6Nk\,s\log_2s+J\bigl(24kM\log_2(2M)+36k^2M^2\log_2(6kM)\bigr)$
with $M=\max_iM_i\le(24D)^N$. The value envelope is dominated by the
exactification weights and the separator primitives, at most
$O(kM\log(kM))$ bits per layer. The width terms contribute only
$O(\text{layers}\cdot\log A)$. Hence every numerator and $\mathcal D$ have
at most $(24D)^{2N}\cdot\mathrm{poly}(N,k,J,\log A)$ bits, so
$$
\log_2(\text{bit length})\le2N\log_2(24D)+O(\log(NkJ\log A))
=O(\varepsilon^{-3/2}\Lambda^2),
$$
compared with $\log_2(A^{24})=\Theta(\varepsilon^{-9/2}\Lambda^3)$. This
does not change any order in parts (b) and (c). It matters for the
precision of the recursion (§3.5).

## 4. Part (b): an explicit seed

### 4.1 What the unrolling uses

v5 Lemma 2.4 runs the pooled recursion with $\rho=A/B$,
$n_\infty=AB/(B-A)$, leaf threshold $n_*=\lceil n_\infty\rceil+1$, counts
$\nu_{\ell+1}=r_*\lceil\nu_\ell/m_*\rceil$ and sides
$n_{\ell+1}=A\lceil n_\ell/B\rceil$. Step 3 of its proof gives, for every
starting side $n$,
$$
\nu_\ell\le\Bigl(1+\frac{r_*m_*}{r_*-m_*}\Bigr)\Bigl(\frac{r_*}{m_*}\Bigr)^\ell,
\qquad \rho^\ell n\le n_\ell<n_\infty+\rho^\ell n,
\qquad \rho<\rho^{\ell_{\max}}n\le n_*.
\tag{4.1}
$$
Step 5 shows that every leaf product is a product of a linear form in the
left input and a linear form in the right input. The proof of v5
Theorem 9.2 uses only (4.1), Step 5 and the rationality of the maps.
Hence it applies verbatim to any rational relative scheme, in particular to
$S_\varepsilon$.

### 4.2 The seed theorem

**Theorem 7 (explicit shifted-chain seed; proved here).** Let
$\varepsilon\in(0,1]$ be rational, let $S_\varepsilon$ be the scheme of
§2.2, and put
$$
n_*=\Bigl\lceil\frac{AB}{B-A}\Bigr\rceil+1,\qquad
\Xi=r_*(1+r_*m_*)\,n_*^3,\qquad
n_0=(\Xi+1)^{\lceil2/\varepsilon\rceil}.
$$
For every $n\ge n_0$, unroll the pooled recursion of $S_\varepsilon$ at
side $n$, with zero padding and classical leaves. This gives a
decomposition of $\MM_n$ into $R\le\Xi\,n^p<n^{9/4+\varepsilon}$ rank-one
tensors with rational coefficients. In particular this holds for
$n=n_0$, and
$$
\frac{24}{\varepsilon}\log A\le\log n_0\le27\Bigl\lceil\frac2\varepsilon\Bigr\rceil\log A
<2.1\cdot10^{11}\,\varepsilon^{-11/2}\Lambda^3 .
$$
The procedure that computes $n_0$ and the seed from $\varepsilon$ uses only
integer and rational arithmetic.

*Proof.* By (4.1) and $r_*-m_*\ge1$,
$$
\nu_{\ell_{\max}}\le(1+r_*m_*)\Bigl(\frac{r_*}{m_*}\Bigr)^{\ell_{\max}}
<(1+r_*m_*)\frac{r_*}{m_*}n^p\le r_*(1+r_*m_*)\,n^p .
$$
Here $(r_*/m_*)^{\ell_{\max}}=\rho^{-p\ell_{\max}}<(n/\rho)^p$ because
$\rho^{\ell_{\max}}n>\rho$. Each leaf has side at most $n_*$, so the
classical algorithm uses at most $n_*^3$ scalar products per leaf. By Step 5
of v5 Lemma 2.4, these products are rank-one terms of a decomposition of
$\MM_n$. Its coefficients are rational because $S_\varepsilon$ is rational
(I1). So $R\le\nu_{\ell_{\max}}n_*^3<\Xi n^p$. By (I2),
$p<9/4+\varepsilon/2$. Since $n\ge n_0$,
$n^{\varepsilon/2}\ge(\Xi+1)^{\lceil2/\varepsilon\rceil\varepsilon/2}\ge\Xi+1>\Xi$.
Hence $R<n^{9/4+\varepsilon}$.

For the size, Lemma 1(7) gives $\log(\Xi+1)\le27\log A$ and
$\log\Xi\ge12\log A$. Hence
$(2/\varepsilon)\cdot12\log A\le\log n_0\le27\lceil2/\varepsilon\rceil\log A$.
Finally, $\lceil2/\varepsilon\rceil\le3/\varepsilon$ and (I2) give
$\log n_0<81\varepsilon^{-1}\cdot2.551\cdot10^9\varepsilon^{-9/2}\Lambda^3
<2.1\cdot10^{11}\varepsilon^{-11/2}\Lambda^3$. $\square$

*Checked numerically:* for 19 allowances from $1$ to $2^{-80}$ (squared
forms, certified logarithms), and on the literal schedules, where also
$\log\Xi<(9/4+\varepsilon-p)\log n_0$ is verified directly (§4.5).

v5 Lemma 8.6 (descent) is not needed, because the scheme is already
rational. v5 Lemma 9.4 and Propositions 9.5–9.6 apply to this seed as to
any rational seed.

### 4.3 Recursion depth

**Proposition 8 (proved here).** The pooled recursion at side $n_0$ has
$\ell_{\max}$ depths, with
$$
\frac{\log(n_0/(3A))}{\log(B/A)}\le\ell_{\max}<1+\frac{\log n_0}{\log(B/A)}
<1+313\,\varepsilon^{-3/2}\Lambda .
$$

*Proof.* The two bounds in terms of $n_0$ follow from
$\rho^{\ell_{\max}}n_0\le n_{\ell_{\max}}\le n_*\le3A$ and
$\rho^{\ell_{\max}}n_0>\rho$. For the last bound, combine
$\log A\le2NkJ\log(24D)$ with (2.2) and $J/G\le5D/4$,
$\theta\le15/512$. This gives
$\log A/\log(B/A)\le\frac{5D}4\cdot\frac{512}{497}\log(24D)\le1.288\,D\log(24D)$.
Then use $\log n_0\le27\lceil2/\varepsilon\rceil\log A$,
$\lceil2/\varepsilon\rceil\le3/\varepsilon$, $D\le3\varepsilon^{-1/2}$ and
$\log(24D)\le\Lambda$. $\square$

So the seed needs $\Theta(\varepsilon^{-3/2}\log(1/\varepsilon))$ levels of
the pooled recursion. The upper bound is proved. The lower order follows in
outline from $\log n_0\ge(24/\varepsilon)\log A$ and
$\log A/\log(B/A)\ge cD\log D$. Each level applies the whole relative
scheme, whose own chain has $J=\Theta(\varepsilon^{-3/2})$ stages. v5
Remark 9.8 bounds the depth by $\lceil\log_2d_0\rceil$ using only $B/A>2$.
Here $B/A\ge e^{124Nk}$ is enormous, so the depth is tiny compared with
$\log n_0$.

### 4.4 Coefficients and cost of the seed

**Proposition 9 (proved here; outline).** Let $\mathcal D$ be the common
denominator of Proposition 2.

1. All coefficients of the seed of Theorem 7 at side $n_0$ have common
   denominator $\mathcal D^{\ell_{\max}}$, and numerators of bit length at
   most $\ell_{\max}(A^{24}+\log_2(m_*B^2))+1\le\ell_{\max}A^{25}$.
2. The seed can be computed from $\varepsilon$ in at most $n_0^{30}$ bit
   operations. In particular, $\log(\text{preprocessing})=O(\varepsilon^{-11/2}\Lambda^3)$.

*Proof outline.* (1) Propagate the left and right forms downward and the
output forms upward, as in Step 4 of v5 Theorem 9.3. Each depth replaces
a form by a combination of at most $m_*B^2$ forms of the previous depth,
with coefficients $c/\mathcal D$ and $|c|<2^{A^{24}}$ (Proposition 3).
Leaves select existing forms.

(2) Each depth has at most $(\nu_{\ell_{\max}}+m_*)(2n_0)^2\le8\Xi n_0^5$
coordinates, each a vector of length $n_0^2$. One depth costs at most
$16\Xi m_*B^2n_0^7$ operations per side. There are at most $2+\log_2n_0$
depths. Lemma 1 gives $\Xi\le n_0^{\varepsilon/2}$ and
$A\le n_0^{\varepsilon/24}$. So the unrolling needs at most $n_0^{9}$
operations on integers of at most $n_0^{1.2}$ bits, which is at most
$n_0^{12}$ bit operations. Generating $S_\varepsilon$ costs at most
$A^{700}\le n_0^{29.2}$ bit operations (Proposition 4). $\square$

### 4.5 Literal values for the actual schedule

The script builds the actual integer chains, the exact maximal types and
the exact $M_i$ (up to about $10^6$ bits), and encloses every logarithm
rigorously. "Digits" means $\log_{10}$, rounded.

| $\varepsilon$ | $D$ | $J$ | $N=k$ | $p$ (certified) | digits $A$ | digits $B$ | digits $r_*$ | digits $m_*$ | digits $n_0$ | $\frac{\log n_0}{\log A}$ | $\ell_{\max}$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 158 | 4,608 | 2.279915435 | $3.25\cdot10^{9}$ | $4.96\cdot10^{9}$ | $1.88\cdot10^{10}$ | $1.49\cdot10^{10}$ | $1.24\cdot10^{11}$ | 38.3 | 71–73 |
| 1/2 | 3 | 430 | 15,360 | 2.264336138 | $1.18\cdot10^{11}$ | $1.59\cdot10^{11}$ | $5.69\cdot10^{11}$ | $4.76\cdot10^{11}$ | $7.87\cdot10^{12}$ | 66.9 | 189–192 |
| 1/4 | 4 | 1,086 | 49,152 | 2.257579232 | $3.45\cdot10^{12}$ | $4.33\cdot10^{12}$ | $1.50\cdot10^{13}$ | $1.30\cdot10^{13}$ | $4.26\cdot10^{14}$ | 123.7 | 480–484 |
| 1/8 | 6 | 3,166 | 159,744 | 2.253680270 | $1.30\cdot10^{14}$ | $1.50\cdot10^{14}$ | $4.95\cdot10^{14}$ | $4.50\cdot10^{14}$ | $2.93\cdot10^{16}$ | 224.7 | 1,480–1,486 |

These $p$ agree with the independent "upper" check
($\Phi<2.27992,2.26434,2.25758$). The seed targets are
$9/4+\varepsilon$; at $\varepsilon=1$ the target is trivial and is shown
only for scale. For comparison, consider v5's explicit seed (Theorem 9.2)
at $\varepsilon'=1/2$. The argument of v5 Remark 8.8 gives
$d_0>A\ge2^{a\ell_a}$ with $\ell_a=7200$ and $a=2^{7200}$, so the number
of decimal digits of $d_0$ itself has more than 2,000 digits. Here $n_0$
has $7.9\cdot10^{12}$ digits.

### 4.6 The extra factor $1/\varepsilon$

**Remark 10 (proved here, under one assumption from the notes).** The
factor $1/\varepsilon$ between $\log n_0$ and $\log A$ is intrinsic to
unrolling $S_\varepsilon$ with classical leaves. If $\ell_{\max}\ge1$, then
$\nu_1=r_*$ and $\nu_{\ell+1}\ge(r_*/m_*)\nu_\ell$, so
$\nu_{\ell_{\max}}\ge m_*(r_*/m_*)^{\ell_{\max}}\ge B^3(n/(3A))^p$. Also
every leaf has side at least $A$, because $n_{\ell+1}=A\lceil n_\ell/B\rceil\ge A$.
Hence $R\ge B^3A^3(n/3A)^p\ge n^pA^{6-p}/27$. If $p\ge9/4$ (the notes
claim this for the framework; the literal values above satisfy it), then
$R<n^{9/4+\varepsilon}$ forces
$\log n\ge(13/4)\log A/\varepsilon-O(1/\varepsilon)$. Removing the factor
would need a different seed construction, for example cheaper leaves and a
cheaper first level. I did not pursue this.

## 5. Part (c): one algorithm for all sizes

### 5.1 The pooled recursion with explicit constants

**Lemma 11 (proved here).** Let $r\MM_A\restr m\MM_B$ be a relative scheme
with pooled exponent $p\le3$, $B\ge2A$ and $m\le B^3$. Store its three maps
as dense matrices and run the pooled recursion of v5 Lemma 2.4 with
classical leaves. For every $n\ge1$, the number of arithmetic operations
(additions, subtractions, and multiplications, including those by
coefficients) is at most
$$
C_\nu n^p\Bigl[2\frac rmn_*^3+12mB^2\Bigl(\frac43\frac rmn_\infty^2
+\ell_{\max}\Bigl(\frac BA\Bigr)^{p-2}\Bigr)\Bigr]
\le304\,(\log_2n+2)\,B^{11}\,n^p,
$$
where $C_\nu=1+rm/(r-m)$. Data movement (padding, cutting into blocks)
involves no arithmetic and is not counted, as in v5's arithmetic model.

*Proof.* A batch at depth $\ell$ with block side $c_\ell=\lceil n_\ell/B\rceil$
costs at most $6rmA^2B^2c_\ell^2$ operations. Indeed, each of the $rA^2$
left (and right) target blocks is a combination of at most $mB^2$ blocks,
and each of the $mB^2$ output blocks is a combination of at most $rA^2$
blocks. Since $\nu_{\ell+1}=r\lceil\nu_\ell/m\rceil$ and
$n_{\ell+1}=Ac_\ell$, depth $\ell$ costs at most
$\lceil\nu_\ell/m\rceil\cdot6rmA^2B^2c_\ell^2=6mB^2\nu_{\ell+1}n_{\ell+1}^2$
operations. The leaves cost at most
$2\nu_{\ell_{\max}}n_*^3$.

By (4.1), $\nu_\ell\le C_\nu(r/m)^\ell$, and
$n_\ell^2\le2n_\infty^2+2\rho^{2\ell}n^2$ for $\ell\ge1$. Next,
$r/m=(B/A)^p\ge4$ gives
$\sum_{\ell\le\ell_{\max}}(r/m)^\ell\le\frac43(r/m)^{\ell_{\max}}<\frac43\frac rmn^p$.
The terms $\rho^{(2-p)\ell}n^2$ increase with $\ell$, and
$\rho^{\ell_{\max}}n>\rho$, so
$\sum_{\ell=1}^{\ell_{\max}}\rho^{(2-p)\ell}n^2\le\ell_{\max}n^p\rho^{2-p}$.
Summing gives the first bound.

For the second bound, use $C_\nu\le\frac73m\le\frac73B^3$ (from $r\ge4m$),
$r/m\le(B/A)^3$, $n_*\le3A$, $n_\infty\le2A$,
$(B/A)^{p-2}\le B/A$, and $\ell_{\max}+1\le\log_2n+2$ (since $\rho\le1/2$).
The three terms are then at most $126B^6$, $150B^{11}/A$ and
$28\ell_{\max}B^{10}/A$. $\square$

*Checked numerically* on four toy schemes built from Strassen's algorithm:
$7\MM_1\restr\MM_2$, $15\MM_1\restr2\MM_2$, $15\MM_2\restr2\MM_4$ and
$22\MM_1\restr3\MM_2$, the last three with an idle copy so that pooling
matters. For sides $n\le31$, the literal pooled recursion computes $XY$
exactly. The counts and sides satisfy (4.1), the counted operations stay
below both bounds of Lemma 11, and the number of leaf products is at most
$\Xi n^p$. For $n\le6$ the unrolled leaf products form an exact rank
decomposition of $\MM_n$ (full tensor comparison).

For $S_\varepsilon$, Lemma 1 gives the hypotheses, and $B^{11}\le A^{22}$.

### 5.2 The algorithm and the theorem

Let $U(v)=2N_vk_vJ_v\cdot\mathrm{bitlength}(24D_v)$, computed from the
schedule at $\varepsilon=1/v$. Then $U(v)\ge\log_2A$ for $S_{1/v}$, because
$d_i<24D$. $U$ is nondecreasing, and $U(1)=40{,}259{,}026{,}944$.

**Algorithm $\mathcal U$.** On input $n$ and two $n\times n$ matrices over
a field $K$ of characteristic zero:

1. Compute $X=\lfloor\log_2n\rfloor$ and
   $v=v(n)=\max\{v\ge1:3000\,v\,U(v)\le X\}$ by binary search. If no such
   $v$ exists ($X<1.2\cdot10^{14}$), multiply classically.
2. Generate $S_{1/v}$ with the generator of §3 (rational maps over
   $\mathcal D$).
3. Convert its coefficients to elements of $K$ (binary Horner for each
   numerator and for $\mathcal D$, then one inversion).
4. Multiply by the pooled recursion (Lemma 11).

**Theorem 12 (one algorithm for all sizes; proved here).** Count steps as
in v5 Corollary 9.7: steps of a fixed multitape Turing machine during
preprocessing, plus field operations on matrix entries or scheme
coefficients. If $v(n)\ge1$, algorithm $\mathcal U$ uses at most
$$
(c_0+304\log_2n)\;n^{9/4+0.51/v(n)}
$$
steps, where $c_0$ is an absolute constant. It absorbs the Turing-machine
simulation constant and the additive constants below. Otherwise it uses at
most $2n^3$ field operations. Moreover,
$v(n)\ge1$ once $X\ge3000\,U(1)\approx1.21\cdot10^{14}$, and for
$X\ge2\cdot10^{18}$,
$$
\frac{0.51}{v(n)}\le244\,\frac{\ln(4096X)^{6/11}}{X^{2/11}} .
$$
Hence the cost is $n^{9/4+\delta(n)}$ with
$\delta(n)=O((\log\log n)^{6/11}(\log n)^{-2/11})$.

*Proof.* Let $A$ be the source side of $S_{1/v}$. Then
$\log_2A\le U(v)\le X/(3000v)$, so $A\le n^{1/(3000v)}$.

- **Step 1** costs $O(\log^3n)\le O(n)$ machine steps.
- **Step 2** costs at most $A^{700}$ bit operations (Proposition 4), hence
  at most $c_{\rm TM}A^{1400}\le c_{\rm TM}n^{0.467/v}$ machine steps, where $c_{\rm TM}$ is the simulation constant.
- **Step 3**: there are $3r_*A^2m_*B^2\le3A^{20.75}$ coefficients
  (Lemma 1), each with at most $A^{24}$ bits, so at most $A^{46}\le n$
  field operations.
- **Step 4**: Lemma 11 and $p<9/4+1/(2v)$ (I2) give at most
  $304(\log_2n+2)A^{22}n^{9/4+1/(2v)}\le304(\log_2n+2)\,n^{9/4+(1500+22)/(3000v)}$
  operations.

Since $0.467/v<9/4$, $n\le n^{9/4}$ and $1522/3000<0.51$, every term is
at most its coefficient times $n^{9/4+0.51/v}$. The coefficients add up to
$304\log_2n$ plus an absolute constant ($608$ from Step 4, plus the
constants of Steps 1–3).

For the rate, the schedule bounds (I2) give $N\le2305v^{3/2}\Lambda(v)$,
$J\le240v^{3/2}$ and $\mathrm{bitlength}(24D)\le\Lambda(v)$, where
$\Lambda(v)=\ln(4096v)$. Hence $U(v)\le4\cdot10^9v^{9/2}\Lambda(v)^3$, and
every integer
$v\le y:=(X/(1.2\cdot10^{13}\Lambda(X)^3))^{2/11}$ satisfies the selection
condition (note $y\le X$). For $X\ge2\cdot10^{18}$, $y\ge1$, so
$v(n)\ge\lfloor y\rfloor\ge y/2$ and
$1/v(n)\le2(1.2\cdot10^{13})^{2/11}\Lambda(X)^{6/11}X^{-2/11}
\le478\,\Lambda(X)^{6/11}X^{-2/11}$. Multiply by $0.51$. $\square$

*Checked numerically:* $U(v)\le4\cdot10^9v^{9/2}\Lambda(v)^3$ for
$v=1,\dots,64$ and $v=10^2,10^3,10^4,10^6,10^9$. For
$X=10^{18},\dots,10^{100}$, the script runs the selection rule, the bound
$v(n)\ge\lfloor y\rfloor$, and the final inequality in exact arithmetic:

| $X=\lfloor\log_2n\rfloor$ | $v(n)$ | $0.51/v(n)$ | bound $244\,\Lambda^{6/11}X^{-2/11}$ | v5 Remark 9.8: $547200/\log_2X$ |
|---:|---:|---:|---:|---:|
| $10^{18}$ | 4 | 0.128 | (not yet valid) | 9151 |
| $10^{20}$ | 9 | 0.057 | 0.50 | 8236 |
| $10^{24}$ | 48 | 0.011 | 0.10 | 6863 |
| $10^{30}$ | 526 | $9.7\cdot10^{-4}$ | $9.2\cdot10^{-3}$ | 5491 |
| $10^{40}$ | 29,249 | $1.7\cdot10^{-5}$ | $1.6\cdot10^{-4}$ | 4118 |

The guaranteed formula is about ten times weaker than the actual selection.
v5's bound becomes nontrivial ($<3/4$) only when $\log_2\log_2n>729{,}600$.

### 5.3 Discussion of the rate

**Order.** The exponent is
$\frac94+\frac1{2v}+O(\log A_{1/v}/\log n)$, with
$\log A_{1/v}=\Theta(v^{9/2}\log^3v)$. Balancing the two terms gives
$v\approx(\log n)^{2/11}(\log\log n)^{-6/11}$, hence
$\delta(n)=\Theta((\log\log n)^{6/11}(\log n)^{-2/11})$ for this algorithm.
This is polynomial in $1/\log n$. v5's construction gives only
$1/\log\log n$, and that is optimal for v5's argument (v5 Remark 9.8).

**Preprocessing assumption.** None is needed beyond specifying the
generator. v5's Remark 9.8 needed a structural bit-length bound for a
particular implementation, because v5 Theorem 9.3's generic bound
$2^{2\mathfrak S}$ is doubly exponential in the step count. Here the same
role is played by Proposition 3: the common-denominator generator has
coefficient bit lengths at most $A^{24}$, so preprocessing costs
$A^{O(1)}$. Any bound of the form $2^{\mathrm{poly}(\log A)}$ would keep
$\delta(n)=(\log n)^{-\Omega(1)}$. The precise powers 700 and 1400 enter
only through the constant 3000 in the selection rule. A preprocessing bound
as weak as v5 Theorem 9.3's would destroy the rate.

**Remark 13 (a seed-based variant is worse; proved here, outline).** Using
the seed of Theorem 7 with v5's block recursion (Lemma 9.4), as v5
Corollary 9.7 does, costs $c_{\rm seed}n^{p_{\rm seed}}$ with
$\log c_{\rm seed}\le8.5\log n_0+2=O(\varepsilon^{-11/2}\Lambda^3)$. The
padding of $n$ to a power of $n_0$ alone can cost a factor $n_0^{p_{\rm seed}}$.
Balancing $\varepsilon$ against $\varepsilon^{-11/2}/\log n$ gives
$\delta(n)=O((\log\log n)^{6/13}(\log n)^{-2/13})$. Going through a square
seed loses the factor $1/\varepsilon$ of Remark 10. I expect that this
route cannot do better: for $n$ just above a power of $n_0$ the padding
costs a factor $R\ge n_0^2$, and $\log n_0\ge(13/4)\log A/\varepsilon$ by
Remark 10. I have not written this lower bound out.

**Remark 14 (limits of this design; proved here, conditional).** For any
leaf algorithm, the pooled recursion of $S_\varepsilon$ performs at least
$\nu_{\ell_{\max}}\ge B^3(n/3A)^p\ge n^pA^{1/4}/27$ leaf multiplications
(Remark 10, with $p\le11/4$). Hence its exponent is at least
$p+(\frac14\log A-\log27)/\log n$. Assume two claims of the notes that I
did not check: $p\ge9/4$ for the framework (round 14), and
$\log A>10^{-7}\eta^{-9/2}\log^3(1/\eta)$ whenever the paid exponent is
below $9/4+\eta\le9/4+2^{-40}$ (round-11 variable-arity lower bound). Then
pooled recursion over schemes of this framework cannot beat
$\delta(n)=\Omega((\log\log n)^{6/11}(\log n)^{-2/11})$. The exponent $2/11$
is therefore the right order for this design.

## 6. Numerical checks

Script: `python -I experiments/shifted_chains_check_seeds.py` (about 25 s;
`--quick` skips $\varepsilon=1/8$). It also runs as
`python -m experiments.shifted_chains_check_seeds`. It imports nothing from
the repository. Identities use `int` and `Fraction`. Logarithms are
certified enclosures: fixed-point $2\,\mathrm{atanh}$ series with directed
rounding and an explicit tail bound, at 192 bits. Every asserted inequality
is decided by exact arithmetic; floats appear only in the printed summary.

| Section | What is checked | Result |
|---|---|---|
| 3 | Round-11 budget recomputed (every row, $\theta$, excess $<\frac{719}{1988}\varepsilon$); $\log A<2.551\cdot10^9\varepsilon^{-9/2}\Lambda^3$; Theorem 7's $\log n_0<2.1\cdot10^{11}\varepsilon^{-11/2}\Lambda^3$; Proposition 8's constant 313; for 19 allowances from $1$ to $2^{-80}$ | pass; largest certified excess $0.2416\varepsilon$ |
| 3 | $U(v)\le4\cdot10^9v^{9/2}\Lambda(v)^3$ | $v\le64$ and 5 larger $v$: pass |
| 4 | Literal chains for $\varepsilon=1,\frac12,\frac14,\frac18$: all crops and zero ramp slacks, exact maximal types with a transfer-optimality certificate, $q^N/(N+1)^2\le M\le q^N$ exactly, $s<(19R/8)\mu^L$, $F_R^3\ge R^4$, geometric defect, $p$ and $\Phi<9/4+\varepsilon/2$, $2A\le B\le A^2$, $r_*\le A^{35/4}$, $\log(\Xi+1)\le27\log A$, $\log\Xi<(9/4+\varepsilon-p)\log n_0$, depth interval | pass (table in §4.5) |
| 5 | $D_{\log}+V_{\log}+2$ equals the notes' polynomial; $<A^{24}$; precision and exponent-range inequalities; layer count; generation power | pass (positive coefficients after $A=x+16$) |
| 6 | v5 Lemma 9.1(b) separator for $M\le4$ (all coefficient identities, denominators, a full tensor-level degeneration and exactification); 9.1(c) moments for $E\le40$; 9.1(a) for $r,b\le4$; chain bases unimodular with $\{0,\pm1\}$ inverse for $d\le5$, $b\le6$; stage denominator divisibility | pass |
| 7 | Four Strassen-based toy schemes: scheme identity; literal pooled recursion for $n\le31$; (4.1); Lemma 11 bounds; $R\le\Xi n^p$; exact unrolled rank decompositions of $\MM_n$ for $n\le6$ | pass |
| 8 | Selection rule $v(n)$, $v(n)\ge\lfloor y\rfloor$, and $1/v\le478\Lambda^{6/11}X^{-2/11}$ for $X=10^{18},\dots,10^{100}$ | pass |

## 7. What was not verified

- The stage relation (I1) and the uniform bound (I2) are inputs. They are
  verified by the "maps" and "upper" checks. I re-checked (I2) numerically
  and on literal chains, and (I1) only in the parts listed in §6.
- The layer decomposition of §3.1 is reconstructed, not written out map by
  map for a full stage. Propositions 3 and 4 depend on it only through
  "at most $A^4$ layers of width below $A^{200}$, with the listed primitive
  entries". This is robust, but it is an outline.
- The Turing-machine simulation constant $c_{\rm TM}$ (v5 Remark 9.8's
  argument: a constant times the square of the bit operations).
- A precision analysis of the recursive algorithm (the analogue of v5
  Proposition 9.6 for the pooled recursion), and integer bit complexity
  (the analogue of v5 Proposition 9.5) for the uniform algorithm.
- The two inputs of Remark 14 ($p\ge9/4$ for the framework, and the
  variable-arity lower bound).
- Finite fields. All statements are over $\mathbb Q$ and fields of
  characteristic zero; $\mathcal D$ vanishes modulo small primes.

## 8. Problems found in the notes, and fixes

None is a mathematical error in a stated result.

1. **Scope of the precision claim.** The table entry "$t+A^{28}+1$ working
   significand bits" in both height notes concerns one classical execution
   of the full relative batch. A reader can easily take it as the
   precision of the algorithm. *Fix:* say "for one application of the
   relative batch". Add that recursive use needs about
   $t+3\ell_{\max}A^{24}$ bits, or better $t+O(\ell_{\max}(24D)^{2N})$
   bits by Remark 6.
2. **"Magnitude" of primitives.** The bounds $(4ME)^{4M}$ and $(s+1)^s$
   are for the rational values, not for numerators over the common
   denominator. The proof correctly adds $\log_2\mathcal D$. *Fix:*
   wording.
3. **The layer decomposition is asserted, not listed.** *Fix:* the paper
   should list the primitive maps once, as in §3.1.
4. **Loose guards.** $r_*<A^{20}$ (notes) and $r_*<A^{17}$ (upper check)
   become $r_*\le A^{35/4}$, using $m_*=B^3$ and $p\le11/4$. More
   usefully, $\log(\Xi+1)\le27\log A$.
5. **The heights are far from tight** (Remark 6). The paper may state the
   $A^{24}$ form for simplicity, but should not suggest that it is the
   true size.
6. **No seed and no uniform algorithm.** The notes state that they make
   "no standalone seed rank $r/m$ claim". Theorem 7 and Theorem 12 close
   both gaps.
7. **Notation.** The notes' $n$ (copies per sign) clashes with v5's matrix
   side $n$. Here it is $N$.

## 9. Recommendation for the paper

- **Section "Coefficients and seeds" (about 4–5 pages).**
  - Lemma 1, half a page. It is used everywhere.
  - Propositions 2–4 in short form, about 1.5 pages. List the primitive
    maps once (§3.1), give the denominator $\mathcal D$, the composition
    rule, and the $A^{24}$ and $A^{700}$ bounds with the
    positive-polynomial certificate.
  - Proposition 5 as a remark, with the scope sentence of §8.1, and
    Remark 6 in one paragraph.
  - Theorem 7 with its proof, citing v5 Lemma 2.4 Step 3 and Theorem 9.2,
    about one page, plus Proposition 8 and the table of §4.5.
    Proposition 9 can be a short remark.
- **Section "One algorithm for all sizes" (about 2 pages).**
  - Lemma 11 (pooled recursion with explicit constants), Algorithm
    $\mathcal U$, and Theorem 12.
  - One paragraph comparing with v5 Remark 9.8 ($1/\log\log n$ against
    $(\log n)^{-2/11}$), plus Remarks 13 and 14.
  - Present the direct pooled recursion, not a seed, as the uniform
    algorithm. The seed route gives a worse order (Remark 13).
- **Main theorem in the introduction.** Exponent $9/4+\varepsilon$ with
  $\log A=O(\varepsilon^{-9/2}\log^3(1/\varepsilon))$, a rational seed with
  $\log n_0=O(\varepsilon^{-11/2}\log^3(1/\varepsilon))$, and one algorithm
  with exponent $9/4+O((\log\log n)^{6/11}(\log n)^{-2/11})$. State the
  numerical sizes ($n_0$ with $7.9\cdot10^{12}$ digits at
  $\varepsilon=\frac12$; $v(n)\ge1$ only for $\log_2n\ge1.2\cdot10^{14}$)
  so that nobody reads these as practical.

## Adversarial review

Reviewer role: adversarial referee for topic "seeds", 18 October 2026. I
did not edit or delete the checker's text above. New file:
[`experiments/shifted_chains_skeptic_seeds.py`](../experiments/shifted_chains_skeptic_seeds.py)
(`python -I experiments/shifted_chains_skeptic_seeds.py`, about 5 s;
`--full` adds $\varepsilon=\frac18$, about 12 s). It imports nothing from
the repository and shares no code with the checker's script. I also reran
the checker's script: all checks pass in 23 s with the output reported
above.

### Verdict

**Confirmed, with minor corrections.** I found no wrong constant and no
error in Lemma 1, Propositions 2, 3, 5 and 8, Theorem 7, Lemma 11 or
Theorem 12, given the inputs (I1) and (I2). Every number in the note that I
recomputed agrees: $p$ for $\varepsilon=1,\frac12,\frac14,\frac18$ to 10
digits, the digit counts of $A$ and $n_0$, the depth ranges 71–73,
189–192, 480–484 and 1480–1486, $U(1)$, and the selected $v(X)$ for
$X=10^{18},\dots,10^{40}$. The problems are as follows:

- one statement that is false as written: Remark 10 fails for
  $\varepsilon>3/4$;
- the status of the preprocessing bound is overstated: Propositions 3–4,
  and through them Theorem 12, rest on a layer list that is only
  reconstructed;
- the lower bounds of Remarks 10 and 14 count the products executed by
  v5's literal procedure, including zero-filled batch slots, so the claims
  "intrinsic" and "right order for this design" need that scope;
- the $\Theta$ in §5.3 is proved only as an upper bound;
- some notation clashes need fixing.

Two hypotheses that the note leaves unchecked are now discharged by other
checks (finding 3).

### What I re-derived by hand

I re-derived these independently instead of re-reading the note:

- **Lemma 1, all seven items.** I also found that $n_*\le2A+1$, slightly
  better than $3A$. The bound $\Xi+1\le55A^{53/2}\le A^{27}$ needs only
  $A\ge55^2$. The note's "$A\ge2^{540}$" is true but arbitrary: in fact
  $A\ge2^{2NkJ}\ge2^{6.7\cdot10^9}$.
- **Proposition 2.** The $\alpha$-denominators are
  $g'!(M-1-g')!\mid(M-1)!$. The $\gamma$-denominators are
  $(\ell-1)!(2M-1-\ell)!\mid(2M-2)!$, and the Taylor shift by the integer
  $g+1$ keeps them. The $\beta$-denominators over the nodes $t\le E$ divide
  $\mathrm{lcm}(1,\dots,E)^{M-1}\mid(E!)^{M-1}$. The per-leg product of
  the layer denominators is at most $\mathcal D$, so an unreduced partial
  product has numerator at most $|\text{value}|\cdot\mathcal D$, which is
  what Proposition 3 needs.
- **The envelope polynomial.** By hand: $D_{\log}=9A^7+2A^6+12A^4+24A^3$ and
  $V_{\log}=2A^9+A^8+A^7+8A^6+108A^5$ at $h=A/2$. Their sum plus 2 is the
  notes' polynomial. A one-line certificate replaces the shifted-coefficient
  check: the coefficients sum to $169<2^{15}\le A^{15}$, so the polynomial
  is below $169A^9<A^{24}$. Likewise
  $1+67\log_2A+3A^{24}\le71A^{24}<A^{28}$, and
  $5A^{28}+3A^{24}+150\log_2A+5\le163A^{28}<A^{30}$, for $A\ge16$.
- **Theorem 7.** The chain $\nu_{\ell_{\max}}<r_*(1+r_*m_*)n^p$ comes from
  $\rho^{\ell_{\max}}n>\rho$. The ceiling bound
  $\lceil2/\varepsilon\rceil\le3/\varepsilon$ holds because
  $\varepsilon\le1$. Finally $81\cdot2.551\cdot10^9<2.1\cdot10^{11}$, and
  $2\cdot2305^2\cdot240=2{,}550{,}252{,}000$.
- **Proposition 8.** $J/G\le5(D+2)/8\le5D/4$, $\theta\le15/512$, and
  $27\cdot3\cdot\frac54\cdot\frac{512}{497}\cdot3=312.98<313$.
- **Lemma 11.** The per-batch count $6rmA^2B^2c^2$, the identity
  $\lceil\nu_\ell/m\rceil\cdot6rmA^2B^2c_\ell^2=6mB^2\nu_{\ell+1}n_{\ell+1}^2$,
  both sums, and the constants $126$ and $149\tfrac13\le150$. The third
  term is actually at most $28\ell_{\max}B^9/A$; the note's $B^{10}/A$ is
  valid but loose.
- **Theorem 12, Steps 1–4.** This includes $1400/3000<0.467$,
  $1522/3000<0.51$, $3A^{20.75}(2A^{24}+2)\le A^{46}\le n$, and the rate
  argument. For the rate I checked
  $2\cdot(1.2\cdot10^{13})^{2/11}\le478$ (exactly:
  $2^{11}(1.2\cdot10^{13})^2\le478^{11}$), $0.51\cdot478\le244$, and
  $y\ge1$ at $X=2\cdot10^{18}$. For $U(v)\le4\cdot10^9v^{9/2}\Lambda(v)^3$
  for *all* $v$, the bounds $N\le2305v^{3/2}\Lambda$ and $J\le240v^{3/2}$
  come from (I2), and $\mathrm{bitlength}(24D)\le\log_2(144\sqrt v)\le\Lambda(v)$.
  This gives $2.55\cdot10^9$ in place of $4\cdot10^9$. Monotonicity of $U$
  follows from that of $D,L,H,N,J$.
- **Proposition 9.** I checked the coordinate count $8\Xi n_0^5$, the cost
  $16\Xi m_*B^2n_0^7$ per depth and side, and the exponent bookkeeping
  ($7.92+1\to n_0^9$ operations, numerators of at most $n_0^{1.2}$ bits).
  For the upward forms, the bound $m_*B^2$ per depth is right: each
  product entry feeds at most $m_*B^2$ output entries. The row length of
  the output map, $r_*A^2$, would be the wrong count.

### Independent exact checks (new script)

Logarithms come from Python's `decimal.Decimal.ln`, which is documented to
round correctly. Each value is widened by one unit in the last place at 70
digits and converted exactly to a `Fraction`. Huge integers are first
bracketed by their top 200 bits. Every assertion is decided in `int` or
`Fraction`.

| § | Check | Scope | Result |
|---|---|---|---|
| A | All arithmetic constants of Theorems 7 and 12, Proposition 8, Lemma 11, Remark 13 | exact | pass |
| B | Pooled-recursion counts on synthetic parameters with **rational** pooled exponent: $B/A=t^b$ and $r/m=t^a$, so $p=a/b$ and $n^p$ comparisons are exact. 11 schemes: $p\in\{2,\frac73,\frac94,\frac52,\frac{11}4,3\}$; $m$ up to $405^3=B^3$, as in $S_\varepsilon$. Checked: (4.1), Proposition 8 in integer form, $R\le\Xi n^p$ and $\nu_{\ell_{\max}}<r(1+rm)n^p$ (Theorem 7), $\nu_{\ell_{\max}}\ge m(r/m)^{\ell_{\max}}$ and $R\ge mA^3(n/n_*)^p$ (Remark 10), and Lemma 11 against the exact dense count. | 7,756 sides: all $n<400$, $B^j\pm1$, $n_*B^j$, random $n<10^{60}$ | pass |
| B | Theorem 7 end to end at the literal side $n_0=(\Xi+1)^{\lceil2/\varepsilon\rceil}$ (and at $n_0+1$, $2n_0-1$, $Bn_0+3$): $R^{Q}<n^{P}$ exactly for $9/4+\varepsilon=P/Q$ | 36 (scheme, $\varepsilon$) pairs with $p<9/4+\varepsilon/2$; $n_0$ up to 1,839 bits, $\ell_{\max}$ up to 290 | pass |
| C | A rational toy scheme with genuine denominators: Strassen with $U/2$, $V/3$, $6W$, so $\mathcal D=6$, with $m=1,2$ copies. Unrolled symbolically by my own pooled recursion. The leaf products form an exact decomposition of $\MM_n$, and every seed coefficient times $6^{\ell_{\max}}$ is an integer below $2^{\ell_{\max}(6+\log_2(4m))+1}$ (Proposition 9(1)). | $n=3,\dots,9$ | pass |
| D | My own schedule and $U(v)$; $U(1)=40{,}259{,}026{,}944$; $U$ nondecreasing; $U(v)\le4\cdot10^9v^{9/2}\Lambda(v)^3$; selection rule; constants of finding 5 | $v\le3000$ and $10^4,\dots,10^{12}$; $X=10^{18},\dots,10^{40}$ | pass; largest ratio $U/(v^{9/2}\Lambda^3)=1.74\cdot10^8$ (well below $2.55\cdot10^9$); $v(X)=4,9,48,526,29249$ as in the note |
| E | Literal chains with zero ramp slack. Exact sector counts come from a **greedy marginal allocator**, a different method from the checker's transfer repair; I validated it against brute force for $N\le25$, $d\le30$ and certified it by the no-transfer condition. Checked: $q^N/(N+1)^2\le M\le q^N$, $B>2A$, $B\le A^2$, $\Phi<9/4+\varepsilon/2$, **$p>9/4$**, Lemma P's chain inequality $3\log s\ge\frac94G$, $r_*\le A^{35/4}$, $A^{12}\le\Xi$, $\Xi+1\le A^{27}$, $\log\Xi<(9/4+\varepsilon-p)\log n_0$, and the depth range | $\varepsilon=1,\frac12,\frac14,\frac18$ | pass; values identical to §4.5. Lemma P margin $3\log s-\frac94G$ from 2.03 to 2.68 |
| F | Independent expansion of $D_{\log}+V_{\log}+2$, and the one-line certificates above | exact | pass |

Section B covers the counting parts of v5 Lemma 2.4 Step 3, Theorem 7,
Proposition 8, Remark 10 and Lemma 11 at sizes far beyond the checker's
toy recursions ($n\le31$). It does not test the maps. Section C tests the
maps of a tiny rational scheme.

### Findings

**1. Remark 10 is false as stated for $\varepsilon>3/4$ (minor; fix by
restriction).** The remark says that any seed obtained by unrolling
$S_\varepsilon$ with classical leaves and $R<n^{9/4+\varepsilon}$ needs
$\log n\ge\frac{13}4\log A/\varepsilon-O(1/\varepsilon)$. Its proof assumes
$\ell_{\max}\ge1$. For $\varepsilon\in(3/4,1]$ and $n=2$, the unrolling has
$\ell_{\max}=0$ and is classical, with
$R=8<2^{9/4+\varepsilon}$. That is a counterexample. *Fix:* assume
$\varepsilon\le3/4$, as v5 Remark 8.8 does. Then $\ell_{\max}=0$ gives
$R=n^3\ge n^{9/4+\varepsilon}$, so every valid seed has $\ell_{\max}\ge1$,
and the proof applies.

**2. The preprocessing bound is a proof outline, not a proof (minor; the
statuses must change).** The JSON marks Propositions 3 and 4
"proved-here". Section 1(c) and §5.3 say that Theorem 12 "needs no
assumption beyond the generator bound". But both propositions rest on the
reconstructed claim "at most $A^4$ layers of width below $A^{200}$, with
the primitive entries of §3.1", and the note itself says (§7) that this
list is not written out map by map. The analogue in v5 is the "suitable
implementation" hypothesis of Remark 9.8. Here the implementation is
specified, but its cost is not yet proved.

*Fix:* mark Propositions 3 and 4 "outline, conditional on the layer
list", and state Theorem 12 as conditional on Proposition 4. The order
$2/11$ is robust: any generation bound $A^{c}$ with an absolute $c$ gives
the same rate, with $3000$ replaced by a constant depending on $c$. The
paper must write out the layer list, as the checker recommends. I find
the claim plausible, since the final arrays have at most $3A^{20.75}$
entries and every factor of every intermediate leg has dimension
$A^{O(1)}$.

**3. The hypotheses of Remarks 10 and 14 are now discharged (upgrade).**
The note takes "$p\ge9/4$ for the framework" from round 14, unchecked.
Lemma P in the adversarial review of
[shifted-chains-check-upper](shifted-chains-check-upper.md) proves
$p>9/4$ for every scheme of the construction, from v5's least profile.
Corollary 7 of [shifted-chains-check-hankel](shifted-chains-check-hankel.md)
proves it too, under its stated hypotheses. My Section E confirms $p>9/4$ and Lemma P's chain
inequality on the four literal chains. The second input of Remark 14 (the
round-11 lower bound on $\log A$) is endorsed by
[shifted-chains-check-lower](shifted-chains-check-lower.md). That check
also states that the bound applies to the pooled exponent without a
ceiling. This resolves a mismatch in Remark 14, which applies a bound
stated for the "paid" exponent to the pooled exponent $p$. I did not
re-derive either input. Both remarks are now conditional only on (I1),
and on the scheme class of the lower check.

**4. Remarks 10 and 14 count executed products, not rank (minor; scope).**
Both lower bounds use $\nu_1=r_*$: the first batch holds one real product
and $m_*-1$ zero products, and the full count $\nu_{\ell+1}=r\lceil\nu_\ell/m\rceil$
follows. The factor $m_*=B^3$, and hence $A^{1/4}$ in Remark 14, comes
from these zero-filled slots. So the remarks bound the number of leaf
products that v5's procedure *as written* executes. They do not bound the
rank of the emitted decomposition after rank-one terms with a zero form
are deleted. Nor do they bound an implementation that skips products
whose input forms vanish identically. Whether such pruning helps for
$S_\varepsilon$ depends on how the maps mix the $m_*$ target copies; I
expect it does not help much, but this is not proved.

*Fix:* in Remark 10, write "the number $R$ of leaf products of the
procedure". In Remark 14, restrict "2/11 is the right order for this
design" to v5's literal pooled recursion. The paper should not present
$2/11$ as a limit of the construction.

**5. The $\Theta$ in §5.3 is proved only as $O$ (minor).** Theorem 12
proves the upper bound only. The matching lower bound for algorithm
$\mathcal U$ as specified follows from four facts (outline; the three
numerical constants are checked exactly for $v\le3000$ in Section D):

- the literal procedure executes at least $n^pA^{1/4}/27$ leaf products
  (Remark 10), and $p>9/4$ (finding 3);
- $\log_2A\ge2NkL\log_2D\ge0.135\,U(v)$;
- maximality of $v(n)$ gives $X<3000(v+1)U(v+1)\le2\cdot36\cdot3000\,v\,U(v)$;
- $U(v)\ge6.9\cdot10^7v^{9/2}\Lambda(v)^3$.

Together these give $\delta(n)\ge c\,(\Lambda(X)^3/X)^{2/11}$. The
analytic versions of the three numerical constants are routine, but I
did not write them out.

**6. Cost model wording in Lemma 11 (minor).** The note says that data
movement is "not counted, as in v5's arithmetic model". v5 Lemma 2.4,
Step 2, does count padding and cutting, inside $O(\nu_\ell n_\ell^2)$. Only
v5 Corollary 9.7's model counts field operations alone. Counting copies
changes nothing: padding and cutting both inputs and reassembling the
output cost at most
$3\nu_\ell(Bc_\ell)^2\le\frac1{2mA^2}\cdot6mB^2\nu_{\ell+1}n_{\ell+1}^2$
per depth, which is at most half of the batch term.

**7. Notation (minor).** The note uses $D$ for both the schedule parameter
and the common denominator (the JSON writes both as `D`), $R$ for both the
ramp length $8D$ and the number of seed products, and $n_0$ for the seed
side. v5 uses $n_0=n$ as the starting side in Lemma 2.4 and $d_0$ for the
seed side (Theorem 9.2). *Fix:* use $d_0$ for the seed side, $\mathcal D$
for the denominator, and another letter for the ramp length.

**8. Optional sharpenings (not errors).**

- With (I2)'s $p<\frac94+\frac{719}{1988}\varepsilon$, Theorem 7 holds
  with $\lceil1988/(1269\varepsilon)\rceil$ in place of
  $\lceil2/\varepsilon\rceil$. This lowers $\log n_0$ by about 22%.
- $n_*\le2A+1$.
- The literal ratio $\log(\Xi+1)/\log A$ is about 19, against the proved
  27.

### What I could not verify

- The stage relation (I1), and the layer list behind Propositions 3–4. My
  only end-to-end map test is the toy scheme of Section C.
- The Turing-machine simulation constant, taken from v5 Remark 9.8.
- The inputs of Remark 14, beyond what the upper, hankel and lower checks
  state.
- The precision of the recursive algorithm, and integer bit complexity.
  The checker leaves both open, and so do I.

### Final statements I endorse

All are conditional on (I1), and on (I2) as verified by the upper check.

- **Lemma 1**, as stated.
- **Proposition 2 and Proposition 5** (Proposition 5 for one application
  of the batch only).
- **Propositions 3 and 4, Remark 6 and Proposition 9**, as proof outlines.
  Propositions 3–4 are conditional on the layer list of §3.1, which the
  paper must write out.
- **Theorem 7.** For rational $\varepsilon\in(0,1]$ and every
  $n\ge d_0=(\Xi+1)^{\lceil2/\varepsilon\rceil}$, the unrolled pooled
  recursion of $S_\varepsilon$ is a rational decomposition of $\MM_n$ into
  $R\le\Xi n^p<n^{9/4+\varepsilon}$ rank-one tensors, and
  $\frac{24}\varepsilon\log A\le\log d_0\le27\lceil\frac2\varepsilon\rceil\log A
  <2.1\cdot10^{11}\varepsilon^{-11/2}\log^3(4096/\varepsilon)$.
- **Proposition 8**, as stated.
- **Lemma 11**, as stated.
- **Remark 10**, for $\varepsilon\le3/4$, as a lower bound on the number of
  leaf products of the procedure. Its hypothesis $p\ge9/4$ is discharged
  (finding 3).
- **Theorem 12**, as stated, conditional on Proposition 4. The rate is
  $\delta(n)=O((\log\log n)^{6/11}(\log n)^{-2/11})$, with the explicit
  bound $0.51/v(n)\le244\,\ln(4096X)^{6/11}X^{-2/11}$ for
  $X=\lfloor\log_2n\rfloor\ge2\cdot10^{18}$, and $v(n)\ge1$ exactly when
  $X\ge3000\,U(1)\approx1.21\cdot10^{14}$. For the algorithm as specified,
  the order is $\Theta$ (finding 5, outline).
- **Remark 13** (upper bound only), and **Remark 14** restricted to v5's
  literal procedure (finding 4).
