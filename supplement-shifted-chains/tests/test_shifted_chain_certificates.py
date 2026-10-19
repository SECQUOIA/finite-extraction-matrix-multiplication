"""Tests for experiments/shifted_chain_certificates.py.

1. Bookkeeping check.  On a two-stage chain with mixed arities, the closed-form
   counts A, B, r_*, m_* equal the per-stage factors multiplied out stage by
   stage (brute-force sector counts, six orientations, two signs,
   exactification at power k).  Both sides encode the same cost model, so the
   test guards multiplicities and exponents, not the model itself, which rests
   on the stage relation proved in the paper.  The same chain checks the
   certified Phi interval and the digit counts against exact integers.
2. The witness below 3 is checked with exact integers and no logarithms:
   Phi < 3 at the reported k, Phi >= 3 at k-1, and its digit counts.
3. --check mode: the saved report is recomputed and compared byte for byte.
"""

from fractions import Fraction
from math import ceil, comb, floor
import unittest

from experiments import shifted_chain_certificates as sc


def largest_sector_count(N, d):
    return max(comb(N, a) * comb(N - a, b) * (d - 1) ** a * 2 ** b
               for a in range(N + 1) for b in range(N - a + 1))


def composed_counts(stages, N, k):
    """Multiply out the per-stage factors of the cost model, stage by stage.

    Source supply: each of the 6Nk oriented convolution factors of the source
    has a rank decomposition with r_1+b_1-1 terms.  Each stage: in each of the
    six orientations a separator takes 2M-1 copies to M copies with degree
    M-1; for each sign the three orientations turn the dot products B_X(d^N)
    and B_X(M) into MM_(d^N) and MM_M.  Exactification at power k raises the
    stage to the k-th power and multiplies its source copies by k*degree+1.
    The terminal factor Q_(1,t)^(Nk) is MM_(t^(2Nk)).
    """
    r1, b1 = stages[0][:2]
    copies_in, copies_out = (r1 + b1 - 1) ** (6 * N * k), 1
    side_in = side_out = 1
    for _r, _b, d, _c in stages:
        m = largest_sector_count(N, d)
        stage_in = stage_out = 1
        stage_side_in = stage_side_out = 1
        degree = 0
        for _orientation in range(6):
            stage_in *= 2 * m - 1
            stage_out *= m
            degree += m - 1
        for _sign in range(2):
            stage_side_in *= d ** N
            stage_side_out *= m
        copies_in *= stage_in ** k * (k * degree + 1)
        copies_out *= stage_out ** k
        side_in *= stage_side_in ** k
        side_out *= stage_side_out ** k
    t = stages[-1][0]
    return {"A": side_in, "B": side_out * t ** (2 * N * k),
            "r_star": copies_in, "m_star": copies_out}


class ShiftedChainCertificateTests(unittest.TestCase):
    def test_two_stage_bookkeeping_and_exact_interval(self):
        # Terminal (1,3); forward arities 3 then 2: (3,6) -> (3,3) -> (1,3).
        stages = sc.backward_chain((1, 3), [3, 2])
        self.assertEqual(stages, [(3, 6, 3, 3), (3, 3, 2, 1)])
        self.assertEqual(sc.forward_floor_chain((3, 6), [3, 2]), stages)
        N, k = 3, 2
        closed = sc.exact_counts(stages, N, k)
        self.assertEqual(closed, composed_counts(stages, N, k))

        # The certified Phi interval agrees with exact integer comparisons:
        # Phi < u/v  iff  (2 r_*)^v A^u < m_*^v B^u.
        rows = sc.stage_data(stages, N, k)
        phi = sc.exponents(sc.log_counts(8, 3, rows, N, k))["Phi"]
        A, B, r, m = closed["A"], closed["B"], closed["r_star"], closed["m_star"]
        above = Fraction(ceil(phi.hi * 1000) + 1, 1000)
        below = Fraction(floor(phi.lo * 1000) - 1, 1000)
        for q, holds in ((above, True), (below, False)):
            u, v = q.numerator, q.denominator
            self.assertEqual((2 * r) ** v * A ** u < m ** v * B ** u, holds)
        factors = sc.side_factors(3, rows, N, k)
        self.assertEqual(sc.decimal_digits(factors["A"]), len(str(A)))
        self.assertEqual(sc.decimal_digits(factors["B"]), len(str(B)))
        self.assertEqual(sc.decimal_digits([(100, 7)]), 15)  # exactly 10^14

    def test_witness_below_3_with_exact_integers(self):
        spec = sc.WITNESSES[0]
        self.assertEqual(spec["target"], "3")
        stages = sc.backward_chain((1, spec["t"]), sc.arity_list(spec))
        entry = sc.certificate(spec)
        for k, below in ((spec["k"], True), (spec["k"] - 1, False)):
            counts = sc.exact_counts(stages, spec["N"], k)
            A, B, r, m = counts["A"], counts["B"], counts["r_star"], counts["m_star"]
            # Phi < 3  iff  2 r_* A^3 < m_* B^3.
            self.assertEqual(2 * r * A ** 3 < m * B ** 3, below)
            if below:
                self.assertEqual(entry["decimal_digits_A"], len(str(A)))
                self.assertEqual(entry["decimal_digits_B"], len(str(B)))

    def test_saved_report_recomputes(self):
        self.assertEqual(sc.main(["--check"]), 0)


if __name__ == "__main__":
    unittest.main()
