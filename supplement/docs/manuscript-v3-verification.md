# Manuscript version 3: verification reports on the version 2 mathematics

These are the reports of the independent verification done before the version 3 rewrite (17 October 2026). Each heading names one area and the reviewer's verdict. File names and line numbers refer to the version 2 sources in `archive/v2/finite-extraction-source.zip` at the repository root; `docs/` paths refer to this supplement. The reviewers wrote their own exact-arithmetic checks, independent of the supplement code. Those scratch scripts were not preserved. The scripts in `experiments/` reproduce the numbers that the version 3 paper quotes. `manuscript-v3-revision.md` summarizes these reports and lists the fixes made in version 3.

## maps — sound_with_minor_issues
I found no mathematical error in preliminaries.tex or maps.tex. I rebuilt every identity and map in this area independently, using exact integer and cyclotomic arithmetic, under both possible conventions for the superscript leg permutation:
- eq:matrix-products, eq:convolution-rank, eq:cyclic-identities and eq:balanced-properties hold.
- The determinant basis is unimodular and adapted to the filtration, with the stated quotients. Multiplication is block upper triangular with diagonal blocks C(r,b+h-2j). The dual-basis remark is correct.
- Lemma multiway holds on full tensor powers: 24 parameter sets, 138 type classes.
- Lemma tripling holds: r=2,3,4, n=1..3, all m. The maximizer and the bound M_t >= 3^n/(n+1) hold for n<400.
- The separator degeneration holds exactly for 12 parameter sets, including K0<M, K0>M, c=2,3 and M=1. This covers L=K0+c(M-1), the exponent support {c d^2 : d <= d_*}, and the constant term.
- eq:cyclic-tripling-balance and the auxiliary combinations into M_{h+1} and M_M hold as explicit legwise coordinate permutations, for both signs.

The paper does not fix a convention for T^pi or for the order of the factors over a coset. Both choices are harmless: the cosets A_+ and A_- are closed under inversion, and A_+ is normal in S_3, so every identity holds under either convention. I confirmed this by computation.

The remark that one sign for all rows would not give the boundary identification is true as worded. Whether some other isomorphism S^+_{r,b} = S^-_{r,b} exists (r != b) is not addressed by the paper; my test with a stabilizer-algebra chirality invariant was inconclusive.

Findings:
- One citation error: CVZ21 is cited as "Section 3.3", but cyclic symmetrization is defined in Section 3.2, printed p. 16, just before Corollary 3.3. This appears at maps.tex:216 and introduction.tex:208. The earlier v2 literature review carries the same mislabel.
- One exposition issue: symbols are reused with different meanings inside Proposition separator.

All numbered claims were checked by computation on small parameters and by hand in general. The upstream preprint was used only for comparison.

## profile-flows — sound_with_minor_issues
I found no mathematical error in manuscript/profile.tex or manuscript/flows.tex. Every formula, constant and proof step I examined is correct, and the probabilistic proof is rigorous. It proves finite expected absorption rather than assuming it. It also shows that the linear system is nonsingular through the Neumann series, and it handles the reset state n correctly.

Profile: sympy confirms the second-difference formula in all three cases. Exact rationals confirm every profile axiom for m, n, h <= 80, and k_a(F) = s_a. The x_j closed form and the chord identity hold. s_a^3 < (3a-1)/2 holds for 2 <= a < 400, and the identity value 6a+1 is correct. F^3 <= (m+n-1)^4 holds with equality only at (1,1). The constant log F(a,a) - (4/3)log a converges to log(3/2) - logGamma(4/3), about 0.5187. A truncated-grid LP (HiGHS, N = 30 and N = 48, each entry minimized separately) gives LP min = F at every entry whose proof inequalities fit inside the grid. Every gap is explained by truncation.

Flows: I re-implemented the walks independently in exact rationals for r = 2..120 and both injections. Checks:
- the q are positive and sum to 1;
- eq:affine-row holds, the children stay in [r-1, 4r-1], the filtration indices are integers in [0, h] matching the blocks of Lemma multiway, and b >= h+1 holds;
- eq:row-flow holds exactly, including coordinate 0, and mu matches eq:reset-weights;
- the excursion decomposition C_i + p_i C_1/(1-p_1) holds state by state, p_i matches eq:exit-probability, and the uniform walk exits at n with probability i/n;
- the excursion bounds C_i <= 3 sqrt(i)/gamma and E_0 sum sqrt(h) <= g(i)/gamma hold;
- for r = 2..20 the solution matches the repo's own solver exactly.

The claimed row bounds are correct but very loose. The true maxima are 7.0 visits and 6.88 log-charge in the final row (bound 105), and 8.57 visits and 9.97 log-charge in lower rows (bound 180). The drift inequality holds for every n <= 600 and every interior x, with minimum slack 0.047. The square-root sum bound holds, with slack tending to -zeta(-1/2), about 0.208. The constants 54+36sqrt2 (about 104.91) and 90+63sqrt2 (about 179.10) are exact.

The only problems are small wording issues: a non sequitur, a confusable expectation notation, loose "absorption" wording for the uniform walk, and two typo-level phrasings. These are listed as findings, with readability issues in clarity_notes. My independent results agree with the earlier audits (docs/manuscript-v2-profile-audit.md:57-150 and docs/manuscript-v2-opus-review-round1.md:360-410, 600-615), which I read only after finishing my own checks. I did not verify the page numbers cited for GrinsteadSnell97 or LevinPeres17. The repository was not modified (git status is clean).

## rounding — sound_with_minor_issues
I found no mathematical error in manuscript/rounding.tex. I checked it by hand and with my own exact-arithmetic code, independent of the repo's code.

- **Occupation flows (flows.tex).** I solved the occupation linear systems exactly with fractions. Both eq:row-flow and the mu_r formula hold exactly.
- **Rounding method.** I wrote my own BFS augmenting-path rounding. Its results match the Lemma statement on 3000 random multigraphs containing loops, parallel edges and opposing edges.
- **Main runs.** On the real row circulations I covered a=2..12 with K in {1, 2, 7, a^3, a^3*ceil(log2 a)}. I added a=2..20 with randomized augmenting order and random K up to 10^6, for 342 runs in total. In every run:
  - floor <= n <= ceil held on every edge, and the return edge stayed exactly K.
  - eq:rounded-row-flow held exactly, and all three error bounds in eq:rounded-edge-errors held strictly.
  - eq:rounded-ledger held as an identity in the free abelian group, and the catalyst total was exactly U+T-K. M_2 was the only boundary symbol, with zero source multiplicity.
  - G = K log F(a,a) - L agreed to within 1e-73 at 80-digit precision.
  - All bounds in eq:rounded-count-bounds held.
- **Size of the loss.** The ratio L/(4 J_a) was at most 0.0287, reached at a=2, K=1. At a=12, K=6912, L = 3.96 against 4 J_12 = 6716. Ignoring the flow constraint, the worst per-action floor/ceiling choice reaches only 0.169 of 4d.
- **Child probabilities.** q >= 1/(3d) holds exactly for every row up to 80, with equality at r=2, x=3.
- **Closed form for J_a.** It matches direct summation for a=2..300.
- **Sign rule.** The ledger needs only that signs alternate between rows. Giving every row the same sign fails for every a >= 3 I tested (3, 4, 5).
- **Böcherer-Geiger remark.** The logic is correct. I confirmed against the arXiv v4 text that their Section IV.D, Eq. (42) gives D(t^id||t) <= 1/(t_n M), with the approximation as the first argument and natural logs. A brute-force test of that bound found no violation.
- **Repo code.** experiments/multiway_rounded_flow.py gives the same U, T and U+T-K as my code in all 10 of its cases.

The only findings are two places where the exposition is unclear. My conclusions agree with docs/manuscript-v2-profile-audit.md:153-226 and docs/manuscript-v2-literature-review.md:19,32, which I read only after finishing my own checks.

**Not checked:**
- The general proof of the 105/180 row bounds in flows.tex. I checked them numerically only, for a <= 12.
- Citation details for HK56 and KangPayor15.
- How the rounded counts are used by the tensor maps in extraction.tex.

## extraction-quantitative — sound_with_minor_issues
I found no mathematical error in extraction.tex, quantitative.tex, or in how they match Theorems 1.1/1.2 (introduction.tex:36-72) and the abstract (main.tex:37-60). All six requested items check out.

**Checked by hand:**
- The counted catalytic degeneration (Proposition catalytic) gives the stated degeneration. This covers S, H, D, u and v, the residual factors (S^+_{a,a})^{NK} and M_{2^{NK}}, and the single shared parameter t with degrees adding.
- The relative scheme: exactification comes before reuse, the j-fold induction is correct, catalyst supply costs kappa_N^k (not kappa_N^{kj}), and r_* and m_* are as stated.
- Pooled recursion (Lemma batch): the recurrences, p >= 2, the O(n^p) and O(n^2 log n) bounds, pooling across parents, and bilinearity.
- The pooled exponent formula is exact. The Phi bound and its unpooled recurrence are correct.
- Lemma types: both inequalities and the mode argument.
- The type, copy, interpolation and catalyst cost bounds, and p >= tau_a > 9/4.
- Every constant in Theorem quantitative and Corollary explicit-allowance.
- The cyclotomic order L_*: every root of unity used is listed in it.
- Lemma descent, Corollary seed (termination via the exact integer test R^beta < n^alpha), and the wording of Theorem 1.1.

**Checked by computation:**
- An independent exact re-implementation (`construct.py`) builds rational occupations, rounds them by max-flow, and forms the signed ledger and catalyst. It confirmed the J_a formula, sum c = U+T-K, zero catalyst multiplicity for M_2, Delta_N in [NG - T_N, NG], G = K log F - L with 0 <= L <= 4J_a, all three cost bounds, and p >= tau_a. Coverage: a = 2..6 with several K and N; the Theorem's family at a = 2..16; the costs-table parameters at a = 4, 8, 12.
- For the table parameters it reproduces the stated digit counts of A exactly. The exact Phi values (3.5755, 2.8406, 2.6728) lie below the table's certified upper bounds.
- A toy pooled recursion (two Strassen copies times M_3, so r=14, m=2) computes products correctly with padding and cross-parent batching, and satisfies the v_l and n_l bounds.
- High-precision evaluation at a = 2^64 confirms every step of the chain in Theorem quantitative, with modest slack. Numerator/K is at most 887.4 against the stated 3t+850 = 983.1. The contraction lower bound is 57.95 against (4/3)t-7 = 52.15. Interpolation gives 360 <= 361, catalyst 396.5 < 483, and log A/(a^5 l^2) <= 180 <= 181.
- At a = 2^64 the proved bound is p < 22.54, which is far from useful. It drops below 3 only for log_2 a > 1731.

**Not checked:**
- The maps themselves: the determinant filtration, separator and tripling sectors. I relied on their stated lemmas.
- The occupation/drift proof, beyond confirming the reset formulas and row totals numerically for small a.

**Comparison with earlier reviews:** read only after finishing the above. manuscript-v2-finite-audit.md (an older snapshot with K = a^3 l^2) and v2-opus-review-round2 reach the same conclusion.

**Findings:** exposition only. They are an ambiguous formula, an undefined term, and a cross-reference mismatch between Theorem 1.2 and Theorem quantitative.

## appendices — sound_with_minor_issues
All three appendices are mathematically correct as far as I checked; I found no fatal, major or minor mathematical errors. Exact rational and integer computation confirmed the exact-certificate appendix for a=2..60: the probabilities, the telescoping identity (every coefficient of every symmetric y_{r,b}), each intermediate coefficient asserted in the proof of Prop. A.1, positivity, I_c, I_t and I, the integer ledger, sum c = U+T-K, and the entropy identity. The entropy identity was checked exactly as an identity of prime-exponent vectors, since all w, u, d are smooth, and separately with 400-digit logs; a negative control is flagged. For a=2..60 I also confirmed: the closed form for K_a against a brute-force lcm, every gcd and numerator claim in the proof, both divisibilities, the growth bound, and U >= K_a. For the composition appendix I built small explicit instances: determinant bases, the type restriction on tensor powers, the actual Fourier separator substitution over L=2M-1 copies, and the reindexing R_i. They reproduce eq:composed-relation-polynomial, the 0/1 coefficient formula and its index ranges, injectivity of R_i on all monomials (positive degree included), and the constant term as M copies of V_i B_X(M). The tripling reindexing gives V_i independently of the outer labels. S, H and D agree with extraction.tex. For the separator appendix I checked the sparse interpolation identity exactly, eq:one-power-limit and its case analysis on a parameter grid, the separator's exponent support by simulation, the two-power residue argument for all primes q≡3 (mod 4) below 200, and the M=K0=8 example: L=15, d_*=7, smallest admissible q=11, 2475 vs 4096. The repo's own code gives the same K_a for a=2..60, and earlier reviews (docs/manuscript-v2-opus-review-round1.md, section 16) also found these appendices correct. The three findings are exposition only. First, the same symbol n_{i,.} is indexed by child state in Section 7 and by filtration index in Appendix B, which reverses the meaning of n_{i,0}. Second, the closing doubly-exponential remark in Appendix A uses an undefined type scale N and an undefined 'sixfold binary source dimension'. Third, the counts I_c, I_t, I and u, d in Appendix A collide with Section 7 notation.

## finite-costs — sound_with_minor_issues
I found no error affecting any stated result. The inequalities in costs.tex hold, both by hand proof and numerically: eq:elementary-factorial, eq:finite-multinomial, the reset bounds, and eq:log-enclosure. I re-ran the repo pipeline (experiments/multiway_finite_costs.py) from a /tmp copy whose SHA-256 hashes match the JSON. The output is byte-identical to results/multiway-finite-costs.json apart from timing.

My own implementation is independent of the repo code. It covers the exact occupations, my own circulation-rounding max-flow, the signed ledger and catalyst, and an mpmath (80-digit) evaluation of both the exact Phi and the relaxed Phi bound. With BFS (shortest-path) augmentation, it gives types identical to the JSON for a=4, 8 and 12, and the same relaxed bounds. Those bounds are 3.6289260969, 2.8485991647 and 2.6758203588. Each lies below the tabulated values 3.628926097, 2.848599165 and 2.675820359, with margins of about 1e-10. The digit counts of A agree exactly: 84,456,434, 11,877,489,885 and 234,905,651,862, with log10 A well away from an integer boundary. The exact values are Phi = 3.5754691, 2.8406393 and 2.6728401, so the table entries are valid but loose upper bounds.

The comparison subsection is correct. Threefold balancing at power 2k gives the same E, S, H, kappa, u and v as sixfold balancing at power k; I checked this algebraically and numerically to 25 digits. The K_a chain and the remark about tensoring with M_C also hold.

Two issues:
- **Minor:** the table depends on an unstated augmenting-path rule. A valid DFS rounding (the most literal reading of 'first available augmenting path' in extraction.tex) gives different types, larger bounds and different digit counts.
- **Exposition:** the exact upper expression behind the table is not displayed. Using the displayed log E bound instead gives different numbers.

## citations — sound_with_minor_issues
I checked all 29 \cite commands in the included .tex files against references.bib, the 19 entries printed in finite-extraction.pdf (pp. 34-35), and the sources. Most sources came from the local knowledge base (literature/papers/*/original.pdf). I also used Crossref for all 14 DOIs, arXiv for the version and subject-class metadata, and a SHA-256 comparison for the pinned OAI26 PDF. Every DOI resolves to the stated work with matching authors, venue, volume, pages and year.

These pinpoints are verified: Maakestad Lemma 2.5, Theorem 2.8 and Corollary 2.9 (pp. 7 and 10); Hoffman-Kruskal Theorem 2 (printed p. 225, chapter pp. 223-246); Kang-Payor Sections 2.2-3.1 (pp. 2-3); Böcherer-Geiger Section IV.D Eq. (42), which bounds the relative entropy of the KL-optimal M-type approximation by 1/(t_n M); Grinstead-Snell Theorem 11.4 (p. 418); Stothers Theorem 7; AD25 omega < 2.371339; Dup26 omega < 2.371177 (arXiv v1, 17 Aug 2026); and OAI26 Proposition 3.1, Section 4 and the 5M source copies.

Problems found:
1. The CVZ21 pinpoint 'Section 3.3', used twice, is wrong. The cyclic symmetrization cyc(t) is defined in Section 3.2 (ToC p. 16).
2. The diagonal minimality proof in profile.tex reproduces OAI26 Lemma 5.1 step by step, and the profile axioms are OAI26 (4.5), (4.6) and (4.9). Neither is credited. As a result, the intro's 'We prove both the formula and its minimality' overstates novelty for the diagonal.
3. OAI26 is cited only in the introduction and discussion. Sections that reuse its constructions give no local credit: the tripling partition, which is OAI26 Lemma 4.2 with a=h=r, and the separator, which is a variant of OAI26 Proposition 3.1. The abstract does not mention OAI26 at all.
4. Smaller bibliographic errors:
   - The Levin-Peres page range is pp. 256-257, but Section 17.6.1 is on p. 256 only.
   - Maakestad's first name is printed with Ø, while the source and arXiv use Ö. His arXiv primary class is math.AG, not math.RT.
   - Dup26's arXiv primary class is cs.DS, not cs.CC.
   - plainnat lowercases 'Applications' and 'Clebsch-Gordan' and prints '2 edition'.
   - The phrases 'finite interpolation' (for Stothers) and 'asymmetric tensor powers' (for AD25) loosely describe those sources.

None of these affect the mathematical results. The remaining novelty claims are supported against OAI26: multiway restrictions with h>1, the finite extraction, the rounding and occupation analysis, and the 5M to 2M-1 reduction. I did not do an exhaustive search of the wider literature for the multiway determinant restriction.

After my independent check I compared with docs/manuscript-v2-literature-review.md. Its line 16 also gives 'CVZ21 §3.3, printed p. 16', so that earlier review carried the wrong section number. Its line 20 also gives Levin-Peres pp. 256-257.

## global-logic — sound
I reviewed this as a hostile referee and found no fatal, major or minor error in the end-to-end logic. Every link in the chain holds: type restriction, then separator, then threefold balancing, then signed ledger, then catalytic degeneration, then exactification, then catalyst reuse, then relative scheme, then pooled recursion. The chain yields omega <= 9/4 as a limit of finite schemes, each with exponent p >= tau_a > 9/4.

What I verified, and how:
(1) Local maps, exactly and by computation on small cases. The determinant bases are unimodular bases. With the dual output basis on leg 3, the tensor is block upper-triangular with diagonal blocks C(r,b+h-2j). Applying the input basis matrix to leg 3 instead fails, as the paper says. The fixed-type restriction leaves no cross-sector terms and gives multinomial(n; n_j) sectors, each equal to the product of its blocks. The partial-middle tripling has binom(n,m) 2^(n-m) sectors; the middle block is C(r,r)^(23) after the first-index reversal.
(2) The separator with 2M-1 copies. Proved by hand: the congruence is an equality and the weight is c(g-h)^2. Also checked on random sector tensors.
(3) The full single-orientation composition. Type maps, then separator, then the sector reindexing R_i (applied only after separation, as a fixed coordinate permutation on the whole target) give exactly the sum over s of V_i B_X(M) as the t^0 term. Checked for both a split and a tripling.
(4) Orientation bookkeeping, by explicit legwise identifications:
  - S^s_{r,b} is S^-s_{b,r} up to reordering factors within each leg, and S^+_{r,r} = S^-_{r,r}.
  - S^s_{1,b} = M_b, and the product of B_X(d)^pi over a coset is M_d.
  - The tripling sectors balance to (S^s_{r,r})^n.
  - At row boundaries the alternating signs make the factors agree; with a single sign, the factor lists differ.
  - All of this holds under either leg-permutation convention.
(5) Ledger and accounting, recomputed independently in exact arithmetic (occupations, max-flow rounding, signed symbols). The ledger telescopes to K[+;a,a] - K[M_2] for a = 2..12. The catalyst count is U+T-K, and M_2 has zero catalyst multiplicity. G = K log F(a,a) - L holds to 1e-49, with L <= 4J_a. Hence the source and output convolution factors are Cat_N (S^+_{a,a})^{NK} and Cat_N M_{2^{NK}}: the catalyst is literally the same tensor on both sides, up to coordinate isomorphism.
(6) Algorithm and exponent:
  - Exactifying with E = kD+1 before reuse, and reusing the catalyst j times with one catalyst per summand, gives r* = kappa^k E^j S^{kj} (2a-1)^{3NKkj} and m* = H^{kj}.
  - Lemma batch gives cost O(n^p), with p = log(r*/m*)/log(B/A) equal to eq:pooled-exponent, all linear work included.
  - With my own rounding, the exponents for the paper's table parameters are 3.574, 2.8406 and 2.6728. Each is below the table's certified upper bound (3.629, 2.849, 2.676). The digit count of A matches exactly at a=4.

Where the gain comes from (no free resource): in each relation, the M_i^3 separated output copies only pay for the (2M_i-1)^3 source copies (ratio < 8, charged as log(S/H) < 3I log 2). The matrix-dimension gain M_i comes from the three separator dot products, which combine as B_X B_Y B_Z(M_i) = M_{M_i}. The source auxiliary M_{d_i^{Nw_i}} pays for the multiway relation, and the boundary M_2^{NK} supplies NK log 2. Applying log F to the ledger gives log(v/u) ~ NK log F(a,a) - N L.

As an adversarial test, I applied Strassen upper support functionals, which are spectral points on these tight tensors, to the multiway and tripling relations for many theta. There were no violations. The closest case is the leg-3 flattening, where P(r,b) = sqrt(r b (r+b-1)) is concave by a margin of about 2e-5, and that margin is positive analytically. A hand reduction shows the relations imply exactly the profile inequalities, no more.

Dependence on the OpenAI preprint: none on any unproved step. The detecting-character lemma (paper.tex:198) and its appendix are not used. The separator is reproved. Concavity and tripling are realized by exact type restrictions rather than the preprint's weight degenerations (paper.tex:442-605).

Not checked or only partly checked: the occupation drift proof line by line (I only spot-checked the bounds numerically), off-diagonal least-profile minimality, the sixfold-versus-threefold comparison remark, the exact-certificate appendix and the separator-refinement appendix.

Caveats: the computations cover small instances, and the general arguments were checked by hand; this is not a formal verification. My conclusions agree with docs/manuscript-v2-opus-review-round1.md and round2.md, which I read only after finishing. Those reviews were hand-only, so the computations here are independent confirmation. The findings below are wording and notation problems only.

## global-invariants — sound
No test violated a monotone invariant, and none found a fatal or major problem. The individual gadget maps were checked exactly, and these checks give stronger evidence than the invariants: the determinant filtration, Lemma multiway, Lemma tripling, the separator (including general K0 and c), and the separator-appendix arithmetic all hold on every instance tested. Flattening ranks satisfy source >= target at every step, in one orientation and as three-orientation products. The quantum-functional tests turn out to be weak, for a reason I proved: every C(r,b) admits a support distribution with uniform marginals (exact rational points for all r,b <= 12; numerically for r <= 25, b <= 4r+1). Hence F^theta(C(r,b)) = r^th1 b^th2 (r+b-1)^th3. In this construction, every known spectral point is therefore a weighted geometric mean of flattening ranks, and on S^sigma_{r,b} every quantum functional equals r*b*(r+b-1) whatever theta is. Within that limit, all necessary conditions hold: the single-orientation multiway and tripling conditions over a theta grid (3.9M cases, ties only on the edges theta2=0 or theta3=0, plus a proof by hand); the three-orientation profile sqrt(ab(a+b-1)), which satisfies all profile axioms; F^theta(S^+_aa) = a^2(2a-1) > F(a,a)^2 for 2<=a<=3000 (smallest ratio 1.08, at a=2); and per-action slacks along the exact flows for a=2..10, which are nonnegative and telescope exactly to log(a^2(2a-1)) - 2 log F(a,a). The finite catalytic degeneration also passes for a=2,3,4 with independently rounded counts. These tests cannot refute omega <= 9/4 itself. Every known spectral point has zeta(M_n)=n^2, and spectral points with exponent above 2 are not explicitly known. The repository was not modified.
