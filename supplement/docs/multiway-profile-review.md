# Independent review of the multiway profile flow

Date: 2026-10-07. Original reasoning and local checks only; no literature
research. This review treats the stated multiway determinant filtration
and its finite implementation costs as conditional inputs.

The occupation argument in [the flow note](multiway-profile-flows.md)
is valid. No blocking defect was found in the potential bound, change of
measure, reset calculation, rational ledger, or entropy identity. The
result is an $O(a)$ bound on the normalized auxiliary logarithm, subject
to the finite-cost limitations stated there.

For the potential estimate, concavity gives the trapezoidal inequality

\[
\sum_{k=0}^{x}\sqrt{k}
\le \frac23x^{3/2}+\frac12\sqrt{x}.
\]

Dividing by $x+1$ yields the asserted bound on the average of
$\sqrt{2k}$, since $1/2\le2/3$. Jensen's inequality gives the required
bound for the other square-root term. Symmetry handles the other half
of the row. Stopping at a finite horizon and then using monotone
convergence proves finite expected absorption, without assuming it in
advance. The same proof works from every interior state.

The affine function $f$ is positive and harmonic for the uniform walk.
Its path likelihood ratio telescopes to $f(X_t)/f(i)$, which is at most
three for every interior entry. The exit probabilities therefore are
$p_i=i f(n)/(n f(i))$. Each terminal visit resets to state one; thus the
charge for entry two is $C_2+p_2C_1/(1-p_1)$. Using $p_2<2/r$ gives the
stated upper bound. The two numerical constants are approximately
104.912 and 179.095. The corresponding terminal occupations are exactly
$p_i/(1-p_1)$, giving both formulas in the flow note. Since $p_1<1$,
finite excursion expectations imply finite total expectations from
every state, so the full transient occupation matrix is nonsingular.

The binary comparison can use constants independent of the row. For
both injections, every binary occupation weight is at most six, and
each weight with $2r\le b<3r$ is at least one. For the latter claim,
the final-row formula already has numerator at least
$2(5r-1)r$ and denominator $3(r-1)(3r-1)$; the lower-row weight is
larger. For the upper bound, completing the square in the lower-row
numerator bounds an interior weight by

\[
\frac{3(3r-1)^2}{2(r-1)(3r+1)}<6 \qquad(r\ge2).
\]

The exceptional lower-row entry at $b=r$ is also below six. Consequently
the binary sum is $\Theta(r)$ in each row and $\Theta(a^2)$ globally.
The multiway bound improves this particular normalized charge to $O(a)$.

The entropy identity is exact: substitute
$\log q(x,y)=\log f(y)-\log f(x)-\log(h+1)$ into each action, then
pair the resulting logarithms with the occupation ledger. The terminal
identity is $f(n)/f(1)=3$. Alternating row orientations make the two
boundary resources agree by the stated legwise isomorphisms. The final
residual is therefore $S^+_{a,a}-T_2$, and the logarithmic residual is
$\log F(a,a)-\log2$.

The following checks passed:

- Running `python -m experiments.multiway_profile_flows` verifies all
  22 rational row ledgers and 11 alternating global ledgers and reproduces
  the table in the flow note.
- An independent SymPy inverse of the uniform killed transition matrix,
  followed by the Doob change of measure and the reset renewal formula,
  gives exactly the same occupation vectors for both entries in rows
  two through twelve. This calculation excludes the reset state from
  its linear solve, unlike the experiment's joint occupation solve.
- A floating-point diagnostic checks the potential inequality at 15,048
  interior states through row 100. The minimum normalized drift margin
  over the claimed constant is about 0.00928. This is a diagnostic,
  not the proof of the inequality.
- Exact rational checks verify the binary weight bounds above through
  row 100. The algebraic bounds establish them for every row.

These checks do not certify the local determinant maps, choose an
efficient integer scale, or bound the separation, interpolation,
catalyst-reuse, or arithmetic costs of a complete multiplication
algorithm. In particular, the $O(a^3)$ upper bound on the number of type
coordinates remains, and the auxiliary-charge improvement alone does
not imply a useful finite exponent.
