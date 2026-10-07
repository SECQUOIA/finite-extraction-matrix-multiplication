# Independent exposition audit of the revised manuscript

Date: 7 October 2026.

## Scope and conclusion

I read the revised abstract, introduction, preliminaries, scalar-profile proof, tensor maps, occupation flows, circulation rounding, finite extraction, quantitative theorem, finite examples, discussion, and all three active appendices. This was a read-only audit of the TeX manuscript, focused on expert readability, notation, proof structure, interpretation, and the precision of contribution claims. I performed no literature searches or computational experiments and made no TeX edits. Literature attribution was assessed against the source comparisons provided by the designated Luna review, not through an independent literature review.

No substantial exposition blocker remains in the reviewed version. The paper now presents the improved construction coherently rather than as a chronology of repository developments. The main order is appropriate: scalar profile, exact local maps, rational occupations, integer rounding, counted composition and recursion, quantitative parameters, and finite examples. The exact binary certificate belongs in its present appendix, where its denominator obstruction is explicitly limited to its prescribed frequencies.

This conclusion concerns the manuscript's exposition and internal framing. It does not replace the independent mathematical audits or the final typesetting and bibliography checks.

## Corrections identified and incorporated

1. **Relations are not sectors.** The quantitative proof originally called the quantity bounded by (I\le2a^2) the “number of sectors.” It counts active split and reset relations. Their individual sector counts (M_i) can be enormous. The proof now says “number of active relations.”

2. **The auxiliary cost in the abstract needed its scale.** The abstract now identifies the (O(a)) occupation estimate as logarithmic auxiliary cost before integer scaling. It no longer suggests that the actual auxiliary dimension or rounded total cost is linear in (a).

3. **The preprocessing caveat needed precision.** The final extraction paragraph now says that no quantitative bound on preprocessing time or coefficient bit size is asserted. This avoids an apparent conflict with the explicit parameter and relative-source bounds.

4. **Internal workflow language was removed from the finite examples.** The section now presents certified examples and their exact-arithmetic verification, rather than explaining that no new experiment was required during drafting. Its table now has five columns for five entries.

5. **Old schedule obstructions were removed from the framing.** The revised introduction and discussion no longer refer to the excluded small-index obstruction appendix or imply that its lower bound applies to the rounded multiway family. The appendix roadmap now describes the actual active appendices.

6. **The input allowance is explicitly rational.** The integer/rational parameter prescription in the introduction now begins with a positive rational allowance, matching the effective theorem.

The final source read confirms these changes.

## Points that are now explained adequately

- The relative source side (A), the final rational seed side (d), and the time or coefficient size needed to produce the seed are distinguished at the theorem statements and in the discussion. The bound on \(\log A\) is not presented as a final-seed bound.
- The paper proves a finite construction for every fixed positive allowance. It does not claim one fixed exponent-\(9/4\) seed, practical performance, numerical stability, or an exponent below the scalar endpoint.
- The maps explain why sector-specific first-leg transformations are delayed until separation. The composition appendix defines the normalizers on positive-degree terms as well as on the constant term.
- Alternating cyclic orientations, the exact row telescope, and the retained catalyst are described as actual coordinate identifications and multiplicities. The prose does not hide a tensor-factor cancellation.
- Zero occupations and children rounded to zero are treated explicitly. The source auxiliary dimension is kept separate from the used support size in the type penalty.
- The occupation proof distinguishes expected visit count from logarithmic auxiliary charge. The finite interpolation estimate uses the individual-action bound, not merely the larger total bound.
- Exactification occurs before catalyst reuse. The recursion explains pooling across parents, the order of linear transformations, padding, and its arithmetic cost. Rational descent and the terminating seed enumeration are stated separately.
- The introduction credits the established determinant filtration, circulation integrality, interpolation, type counting, symmetrization, and bilinear recursion. Its original contributions are framed as the specified convolution application and its quantitative finite construction, with the numerical endpoint credited to the identified preprint.

## Remaining editorial work

No further structural rewrite is recommended. The final build should check new citation keys, cross-references, displayed equations, and the supplement filenames. Those production checks are outside this source-level audit. A small amount of repetition in the scalar-profile caveat is harmless and does not warrant another editing pass by itself.
