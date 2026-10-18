"""Check the source-side lower bounds of Section 11.2 (subsec:limits).

Run from any directory:
    python experiments/source_side_bounds.py
    python experiments/source_side_bounds.py --check

Part 1 checks the potential conditions d_{r,x} psi(x) >= psi(y) used in
Step 1 of the proof of Proposition prop:source-lower, on every legal edge
x -> y of the rows 2 <= r <= 60, both for the paper's widths
h_{r,x} = min(x, 3r-x) and for all widths 1 <= h <= min(x, 3r-x)
(Remark rem:limits-scope). It also evaluates the bounds of the proof on
the ledger of Example ex:ledger-a2.

Part 2 checks every integer inequality and identity used in the proofs of
Proposition prop:source-lower and Corollary cor:source-tradeoff, in the
remarks after them, and in open question 3 of Section 11.5. Inequalities between logarithms are checked in
exponentiated form; where e enters, it is bounded by partial sums of its
series. Facts that the paper proves for all indices (for example the
induction steps) are also evaluated on a finite range as a sanity check.

Part 3 supports Remark rem:joint-decompositions. It checks that the
flattenings of the convolution tensors C(r,b) and of some symmetrized
tensors S^sigma_{r,b} have full rank, and it runs an exhaustive search
in exact integer arithmetic. The search is complete for the following
reason. A scheme has A >= A_1^j >= exp(jW), and Step 1 of the proof gives
W >= K log(2*3^(a-2)) + zbar log 2, W >= K log 2 + zbar log 6, and, for
a = 2, W >= K log 2 + zbar log 16 (valid for all widths). If A <= 2^24,
the second bound gives jK <= 24 and 6^(j zbar) <= 2^23 < 6^9, so
j zbar <= 8, and the first gives 3^(a-2) <= 2^23 < 3^15, so a <= 16.
The search examines every tuple (a, K, zbar, j) in this box.

Only integers and fractions from Python's standard library are used.
The --check option compares a recomputed report with the saved report.
"""

import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path


MAX_ROW = 60
JOINT_LIMIT_EXPONENT = 24


# ---------------------------------------------------------------- profile

def s(m):
    value = Fraction(1)
    for h in range(1, m):
        value *= Fraction(3 * h + 1, 3 * h)
    return value


def F(m, n):
    low, high = min(m, n), max(m, n)
    return s(low) * (high + Fraction(low - 1, 2))


def eta(a):
    """eta_a = F(a,a)/(2a-1)."""
    return F(a, a) / (2 * a - 1)


def double_factorial_odd(a):
    """(2a-3)!! = 1*3*...*(2a-3), the product of 2r-1 over 2 <= r <= a-1."""
    value = 1
    for r in range(2, a):
        value *= 2 * r - 1
    return value


# ------------------------------------------------------------ part 1: potentials

def children(x, h):
    return range(x - h, x + h + 1, 2)


def edges(r, all_widths):
    for x in range(1, 3 * r):
        largest = min(x, 3 * r - x)
        widths = range(1, largest + 1) if all_widths else [largest]
        for h in widths:
            for y in children(x, h):
                yield x, h, y


def potential_top(r):
    return [Fraction(2)] + [Fraction(x) for x in range(1, 3 * r + 1)]


def potential_low(r):
    return [Fraction(3), Fraction(3, 2)] + [Fraction(x, 2) for x in range(2, 3 * r + 1)]


ROW_TWO_PAPER = [Fraction(v) for v in (2, 1, 2, 6, 6, 9, 18)]
ROW_TWO_ALL = [Fraction(v) for v in (2, 1, 2, 4, 6, 12, 16)]


def first_violation(psi, r, all_widths):
    for x, h, y in edges(r, all_widths):
        if (h + 1) * psi[x] < psi[y]:
            return [x, h, y]
    return None


def potential_gains(psi, r, injection):
    """Coefficients of K and z_r in the bound (eq:potential-bound)."""
    return {"K": str(psi[0] / psi[injection]), "z": str(psi[3 * r] / psi[1])}


def check_potentials():
    counts = {"paper_widths": 0, "all_widths": 0}
    for r in range(2, MAX_ROW + 1):
        for all_widths, key in ((False, "paper_widths"), (True, "all_widths")):
            counts[key] += sum(1 for _ in edges(r, all_widths))
            assert first_violation(potential_top(r), r, all_widths) is None
            assert first_violation(potential_low(r), r, all_widths) is None
        # Gains: top row (injection 1) and lower rows (injection 2).
        assert potential_gains(potential_top(r), r, 1) == {"K": "2", "z": str(3 * r)}
        assert potential_gains(potential_top(r), r, 2) == {"K": "1", "z": str(3 * r)}
        assert potential_gains(potential_low(r), r, 2) == {"K": "3", "z": str(r)}
        # Row r has K splits with child 0 and z_r with child 3r: child 0 needs
        # h = x and child 1 needs h = x - 1 (used in the case analysis).
        for x, h, y in edges(r, True):
            if y == 0:
                assert h == x
            if y == 1:
                assert h == x - 1
            assert y <= x + h <= (h + 1) * x
    # Row two of a = 2 (Example ex:row-two): widths, dimensions, children.
    assert [min(x, 6 - x) + 1 for x in range(1, 6)] == [2, 3, 4, 3, 2]
    assert [list(children(x, min(x, 6 - x))) for x in range(1, 6)] == [
        [0, 2], [0, 2, 4], [0, 2, 4, 6], [2, 4, 6], [4, 6]]
    assert first_violation(ROW_TWO_PAPER, 2, False) is None
    assert first_violation(ROW_TWO_ALL, 2, True) is None
    paper_failure = first_violation(ROW_TWO_PAPER, 2, True)
    assert paper_failure is not None
    assert potential_gains(ROW_TWO_PAPER, 2, 1) == {"K": "2", "z": "18"}
    assert potential_gains(ROW_TWO_ALL, 2, 1) == {"K": "2", "z": "16"}
    return {
        "rows": [2, MAX_ROW],
        "edges_checked": counts,
        "top_row_potential": "psi(0)=2, psi(x)=x; gains K log 2 + z_a log(3a) "
                             "(top row) and z_r log(3r) (lower rows)",
        "lower_row_potential": "psi(0)=3, psi(1)=3/2, psi(x)=x/2; gains K log 3 + z_r log r",
        "row_two_potential_paper_widths": [str(v) for v in ROW_TWO_PAPER],
        "row_two_potential_all_widths": [str(v) for v in ROW_TWO_ALL],
        "paper_row_two_potential_fails_for_other_widths_at_edge_x_h_y": paper_failure,
        "all_conditions_hold": True,
    }


def check_example_ledger():
    """Bounds of the proof on Example ex:ledger-a2 (a = 2, K = 15, N = 1)."""
    K, zbar = 15, 15
    splits = {1: (2, [9, 21]), 2: (3, [6, 14, 22]), 4: (3, [7, 11, 15])}
    total_splits = sum(sum(counts) for _, counts in splits.values())
    A1 = 1
    for dimension, counts in splits.values():
        A1 *= dimension ** sum(counts)
    assert A1 == 2 ** 30 * 3 ** 75
    assert total_splits == 105 >= K + zbar
    # (eq:W-lower-two): A_1 >= 2^K 18^zbar.
    assert A1 >= 2 ** K * 18 ** zbar
    # Catalyst bases r+b-1 of [+;2,b], b = 2, 3, 5, 7, with multiplicities.
    catalyst = {3: 15, 4: 42, 6: 33, 8: 15}
    kappa_root = 1
    for base, multiplicity in catalyst.items():
        kappa_root *= base ** multiplicity
    # (eq:kappa-lower) with N = 1: kappa_1 >= (((2a-3)!!)^K 24^zbar)^3.
    assert kappa_root >= double_factorial_odd(2) ** K * 24 ** zbar
    return {
        "a": 2, "K": K, "zbar": zbar, "splits": total_splits,
        "A1_equals_2^30_3^75": True,
        "W_lower_two_holds": True, "kappa_lower_holds": True,
    }


# ------------------------------------------------- part 2: integer inequalities

def e_bounds(terms=13):
    """Rational bounds e_lo < e < e_hi from the exponential series."""
    partial = sum(Fraction(1, factorial(n)) for n in range(terms))
    tail = Fraction(1, factorial(terms - 1) * (terms - 1))
    return partial, partial + tail


def check_inequalities():
    e_lo, e_hi = e_bounds()
    checks = {}

    def record(name, condition, used_for):
        assert condition, name
        checks[name] = used_for

    record("e_bounds", Fraction(2718, 1000) < e_lo and e_hi < Fraction(11, 4) and e_hi < 3,
           "e between 2.718 and 11/4; e < 3 gives log 3 > 1 and log 12 > 3/4")

    # Profile values.
    record("eta_values", eta(2) == Fraction(10, 9) and eta(3) == Fraction(56, 45)
           and eta(4) == Fraction(110, 81) and F(2, 2) == Fraction(10, 3),
           "eta_2 = 10/9, eta_3 = 56/45, eta_4 = 110/81")

    # Proposition (a), case a = 2.
    record("a2_triplings", 3 ** 3 > 3 * 2 ** 3, "(3/2)^3 > 3, so zbar/K > 1/3")
    record("a2_identity", 2 ** 3 * 18 == 12 ** 2, "log 2 + (1/3) log 18 = (2/3) log 12")
    record("a2_reuse", 24 * 9 ** 27 > 10 ** 27, "24*9^27 > 10^27")
    # Proposition (a), case a = 3.
    record("a3_triplings", 5 ** 6 > 2 ** 6 * 3 ** 5, "5^6 > 2^6*3^5, so zbar/K > 5/6")
    record("a3_reuse", 3 ** 6 * 24 ** 5 * 45 ** 102 > 56 ** 102,
           "3^6*24^5*45^102 > 56^102, so j > 17")
    record("a3_W", 6 * 2 == 12, "W >= log 6 + log 2 = log 12")
    # Proposition (a), case a >= 4.
    record("a4_base", 360 * 81 ** 19 > 110 ** 19, "24*(5!!) = 360 > eta_4^19")
    record("a4_step", 13 ** 19 < 7 * 12 ** 19, "(13/12)^19 < 7")
    for a in range(4, 2001):
        ratio = eta(a + 1) / eta(a)
        assert ratio == Fraction(3 * a + 1, 3 * a) * Fraction(6 * a * a + a - 2, 6 * a * a + a - 1)
        assert ratio < Fraction(13, 12)
    # Quadratic identities behind the ratio formula; agreement at more than
    # two points proves them.
    for a in range(-5, 6):
        assert (3 * a + 2) * (2 * a - 1) == 6 * a * a + a - 2
        assert (3 * a - 1) * (2 * a + 1) == 6 * a * a + a - 1
    record("eta_ratio", True,
           "eta_{a+1}/eta_a = (3a+1)/(3a) * (6a^2+a-2)/(6a^2+a-1) < 13/12 (a in [4, 2000])")
    for a in range(4, 201):
        assert 24 * double_factorial_odd(a) > eta(a) ** 19
    record("a_ge_4_induction_sanity", True, "24 (2a-3)!! > eta_a^19 evaluated for 4 <= a <= 200")
    record("a_ge_4_final", 18 ** 20 > 12 ** 18, "20 log 18 > 18 log 12")
    record("twelve_power", 12 ** 18 > 2 ** 64, "12^18 > 2^64")
    for r in range(2, 200):
        assert (2 * r - 1) * (5 * r - 2) >= 24
    record("catalyst_base", (2 * 2 - 1) * (5 * 2 - 2) == 24,
           "(2r-1)(5r-2) >= 24 for r >= 2, equality at r = 2 (increasing in r)")

    # Proposition (b).
    for a in range(1, 401):
        assert s(a) ** 3 <= Fraction(3 * a - 1, 2)
        assert (3 * a + 2) * (3 * a) ** 3 - (3 * a - 1) * (3 * a + 1) ** 3 == 6 * a + 1
    record("s_cubed", True, "s_a^3 <= (3a-1)/2 (Theorem thm:least-profile, Step 4), a <= 400")
    for a in range(2, 401):
        assert F(a, a) ** 3 < (2 * a - 1) ** 4
        assert (4 * (a + 1) - 2) * (3 * a - 1) - (4 * a - 2) * (3 * (a + 1) - 1) == 2
    record("profile_strict", True, "F(a,a)^3 < (2a-1)^4 for 2 <= a <= 400")
    record("ratio_monotone", Fraction(4 * 2 - 2, 3 * 2 - 1) == Fraction(6, 5),
           "(4a-2)/(3a-1) increases (difference of cross products is 2) from 6/5 at a = 2")
    record("index_at_least_4", 6 ** 9 > 5 ** 10, "(6/5)^9 > 5, so (3a-1)/2 > 5 and a >= 4")
    for a in range(3, 301):
        for r in range(2, a):
            assert (2 * r - 1) * (2 * a + 1 - 2 * r) >= 3 * (2 * a - 3) > 2 * a - 1
        assert double_factorial_odd(a) ** 2 > (2 * a - 1) ** (a - 2)
    record("pairing", True, "((2a-3)!!)^2 > (2a-1)^(a-2), checked for 3 <= a <= 300")
    record("six_a", 6 * (4 - 2) >= 3 * 4 - 1, "6(a-2) >= 3a-1 for a >= 4")
    record("log3_gt_1", e_hi < 3, "log 3 > 1, so log 3/(8 eps) > 1/2 for eps <= 1/4")

    # Corollary (a), range 5/2 < p < 3.
    record("cor_a_upper_range",
           12 ** 4 > 3 ** 3 and 6 ** 18 < 27 * 5 ** 18 and e_hi < 3,
           "36 log 12 > 27 > (6/5)^18, so log(2 log A) > 18 log(6/5)")
    # Corollary (b), lower bound: (18 log(6/5) - log 2)/4 > 0.6,
    # i.e. (6/5)^90 > 2^5 e^12.
    record("cor_b_lower",
           Fraction(6, 5) ** 90 > 2 ** 5 * e_hi ** 12,
           "(6/5)^90 > 2^5 e^12, so 18 log(6/5) - log 2 > 2.4")
    # Corollary (b), upper bound: log 181 + 5l log 2 + 2 log l < 3.48 l for
    # l >= 7200. Here 5 log 2 < 3.47, and 0.01 l - 2 log l - log 181 is
    # increasing for l >= 200 and positive at l = 7200.
    record("cor_b_upper",
           2 ** 500 < e_lo ** 347 and 181 * 7200 ** 2 < e_lo ** 72
           and 348 * 1801 < 630000,
           "2^500 < e^347, 181*7200^2 < e^72, 3.48*1801 < 6300")
    # Corollary (c): log 3/(4 eps) >= log 3/2 > 1/2 for eps <= 1/2.
    record("cor_c", e_hi < 3, "log 3 > 1")
    # Catalyst-free bound: (a-2) log 3 >= ((3a-1)/6) log 3 > (1/3)(3a-1)/2.
    record("catalyst_free", e_hi < 3, "log 3/3 > 1/3")
    # Remark rem:limits-scope: case a = 2 with the potential (2,1,2,4,6,12,16).
    record("scope_a2_identity", 2 ** 3 * 16 == 2 ** 7, "log 2 + (1/3) log 16 = (7/3) log 2")
    record("scope_a2_reuse", 24 * 9 ** 30 > 10 ** 30, "24*9^30 > 10^30, so log 24/log(10/9) > 30")
    record("scope_a2_final", 2 ** 34 > 3 ** 18, "70 log 2 > 18 log 12")
    # Open question 3: p < 2.371339 means p <= 9/4 + eps with
    # eps = 0.121339, and 9/(2 eps) > 37. With log 3 > 1.098, part (b)
    # gives log A > (log 3/(8 eps)) (6/5)^37 > 950, and its proof gives
    # log A > 9 (a-2)^2 log 3/(8 eps) > 3*10^5 for a >= 188.
    q3_eps = Fraction(121339, 10 ** 6)
    log3_lo = Fraction(1098, 1000)
    record("q3_log3", 3 ** 1000 > e_hi ** 1098, "log 3 > 1.098")
    record("q3_part_b",
           Fraction(9, 2) / q3_eps > 37
           and log3_lo / (8 * q3_eps) * Fraction(6, 5) ** 37 > 950,
           "p < 2.371339 gives log A > (log 3/(8 eps)) (6/5)^37 > 950")
    record("q3_a188", 9 * 186 ** 2 * log3_lo / (8 * q3_eps) > 3 * 10 ** 5,
           "a >= 188 gives log A > 9 (a-2)^2 log 3/(8 eps) > 3*10^5")
    # The lowest later bound near 2.371 cited in Section 1.5 is 2.371054887.
    record("q3_later_bounds",
           Fraction(2371339, 10 ** 6) - Fraction(2371054887, 10 ** 9) < Fraction(3, 10 ** 4),
           "the later bounds near 2.371 are lower than 2.371339 by less than 3*10^-4")
    return {
        "e_series_terms": 13,
        "checks": checks,
        "all_checks_passed": True,
    }


def check_case_analysis_box():
    """Sanity check of the case analysis of Proposition prop:source-lower(a).

    On a finite box, every tuple (a, K, zbar, j) that satisfies both
    conditions of (eq:subcubic-necessary) has lower bound >= 12^18 for A.
    This is not a proof (the box is not complete); the proof is analytic.
    """
    examined = feasible = 0
    smallest = None
    for a in range(2, 7):
        for K in range(1, 13):
            for zbar in range(0, 25):
                # zbar log 3 > K log((2a-1)/2).
                if not 3 ** zbar * 2 ** K > (2 * a - 1) ** K:
                    continue
                for j in range(1, 61):
                    examined += 1
                    # j log eta_a > log((2a-3)!!) + (zbar/K) log 24.
                    if not eta(a) ** (j * K) > double_factorial_odd(a) ** K * 24 ** zbar:
                        continue
                    feasible += 1
                    bounds = [(2 * 3 ** (a - 2)) ** K * 2 ** zbar, 2 ** K * 6 ** zbar]
                    if a == 2:
                        bounds.append(2 ** K * 18 ** zbar)
                    bound = max(bounds) ** j
                    assert bound >= 12 ** 18, (a, K, zbar, j)
                    if smallest is None or bound < smallest[0]:
                        smallest = (bound, a, K, zbar, j)
    return {
        "box": "2 <= a <= 6, 1 <= K <= 12, 0 <= zbar <= 24, 1 <= j <= 60",
        "tuples_examined": examined,
        "tuples_satisfying_both_conditions": feasible,
        "smallest_lower_bound_log2": smallest[0].bit_length() - 1,
        "smallest_at_a_K_zbar_j": list(smallest[1:]),
        "all_at_least_12^18": True,
    }


# --------------------------------------- part 3: flattening ranks and search

PRIME = (1 << 61) - 1


def rank_mod_prime(rows):
    """Rank modulo PRIME of an integer matrix given as a list of lists.

    A matrix with full row rank modulo a prime has full row rank over Q.
    """
    rows = [[v % PRIME for v in row] for row in rows]
    rank, columns = 0, len(rows[0]) if rows else 0
    for column in range(columns):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], PRIME - 2, PRIME)
        pivot_row = [v * inverse % PRIME for v in rows[rank]]
        rows[rank] = pivot_row
        for i in range(len(rows)):
            if i != rank and rows[i][column]:
                factor = rows[i][column]
                rows[i] = [(v - factor * w) % PRIME for v, w in zip(rows[i], pivot_row)]
        rank += 1
        if rank == len(rows):
            break
    return rank


def convolution(r, b):
    """C(r,b) as (dimensions, list of index triples with coefficient 1)."""
    entries = [(alpha, beta, alpha + beta) for alpha in range(r) for beta in range(b)]
    return (r, b, r + b - 1), entries


def permute(tensor, pi):
    """T^pi: leg i of T moves to position pi(i) (pi given on 0, 1, 2)."""
    dims, entries = tensor
    new_dims = [0, 0, 0]
    for i in range(3):
        new_dims[pi[i]] = dims[i]
    new_entries = []
    for entry in entries:
        image = [0, 0, 0]
        for i in range(3):
            image[pi[i]] = entry[i]
        new_entries.append(tuple(image))
    return tuple(new_dims), new_entries


def tensor_product(tensors):
    dims = [1, 1, 1]
    entries = [(0, 0, 0)]
    for factor_dims, factor_entries in tensors:
        entries = [
            tuple(e[leg] * factor_dims[leg] + f[leg] for leg in range(3))
            for e in entries for f in factor_entries
        ]
        dims = [dims[leg] * factor_dims[leg] for leg in range(3)]
    return tuple(dims), entries


EVEN = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]   # id, (123), (132)
ODD = [(1, 0, 2), (2, 1, 0), (0, 2, 1)]    # (12), (13), (23)


def symmetrized(r, b, sign):
    base = convolution(r, b)
    return tensor_product([permute(base, pi) for pi in (EVEN if sign > 0 else ODD)])


def flattening_ranks(tensor):
    dims, entries = tensor
    ranks = []
    for leg in range(3):
        others = [o for o in range(3) if o != leg]
        matrix = [[0] * (dims[others[0]] * dims[others[1]]) for _ in range(dims[leg])]
        for entry in entries:
            matrix[entry[leg]][entry[others[0]] * dims[others[1]] + entry[others[1]]] += 1
        ranks.append(rank_mod_prime(matrix))
    return ranks, list(dims)


def check_flattenings():
    convolution_cases = 0
    for r in range(1, 9):
        for b in range(1, 9):
            ranks, dims = flattening_ranks(convolution(r, b))
            assert ranks == dims == [r, b, r + b - 1]
            convolution_cases += 1
    symmetrized_cases = []
    for r, b in ((2, 2), (2, 3), (3, 2), (2, 4), (3, 3)):
        for sign in (1, -1):
            ranks, dims = flattening_ranks(symmetrized(r, b, sign))
            leg = r * b * (r + b - 1)
            assert ranks == dims == [leg, leg, leg]
            symmetrized_cases.append(["+" if sign > 0 else "-", r, b, leg])
    # Leg dimensions of consumed symbols: r b (r+b-1) >= r^2 (2r-1) for b >= r,
    # and the tripling symbol S_{r,4r-1}; their product is increasing in r.
    products = []
    for r in range(2, 101):
        assert all(r * b * (r + b - 1) >= r * r * (2 * r - 1) for b in range(r, 4 * r))
        products.append(r * r * (2 * r - 1) * r * (4 * r - 1) * (5 * r - 2))
    assert products[0] == 12 * 112 == 1344
    assert all(x < y for x, y in zip(products, products[1:]))
    return {
        "convolution_tensors_full_flattening_rank": "C(r,b), 1 <= r, b <= 8",
        "convolution_cases": convolution_cases,
        "symmetrized_tensors_full_flattening_rank": symmetrized_cases,
        "rank_method": "Gaussian elimination modulo 2^61-1; full row rank modulo a "
                       "prime implies full row rank over Q",
        "split_leg_dimension_floor": "r^2 (2r-1) for columns b >= r",
        "split_times_tripling_leg_dimension_at_r_2": 1344,
    }


def joint_search():
    """Exhaustive search for Remark rem:joint-decompositions.

    Conditions for p < 3, with u = a^2 (2a-1) and v = ((a-1)!)^2 (2a-3)!!:
      (i)  2^(3jK) 3^(3j zbar) > u^(jK) v^K 1344^zbar,
      (ii) F(a,a)^(3jK)        > u^(jK) v^K 1344^zbar.
    Lower bound for A: the j-th power of the largest of
      (2*3^(a-2))^K 2^zbar,  2^K 6^zbar,  and 2^K 16^zbar if a = 2.
    """
    limit = 2 ** JOINT_LIMIT_EXPONENT
    # Completeness of the box (see the module docstring).
    assert 6 ** 9 > 2 ** 23 >= 6 ** 8
    assert 3 ** 15 > 2 ** 23 >= 3 ** 14
    a_max, jk_max, jz_max = 16, 24, 8
    examined = 0
    feasible_small = []
    for a in range(2, a_max + 1):
        u = a * a * (2 * a - 1)
        v = factorial(a - 1) ** 2 * double_factorial_odd(a)
        f = F(a, a)
        for j in range(1, jk_max + 1):
            for K in range(1, jk_max // j + 1):
                for zbar in range(0, jz_max // j + 1):
                    examined += 1
                    right = u ** (j * K) * v ** K * 1344 ** zbar
                    local = 2 ** (3 * j * K) * 3 ** (3 * j * zbar) > right
                    profile = f.numerator ** (3 * j * K) > f.denominator ** (3 * j * K) * right
                    bounds = [(2 * 3 ** (a - 2)) ** K * 2 ** zbar, 2 ** K * 6 ** zbar]
                    if a == 2:
                        bounds.append(2 ** K * 16 ** zbar)
                    bound = max(bounds) ** j
                    if local and profile and bound <= limit:
                        feasible_small.append([a, K, zbar, j, bound.bit_length() - 1])
    assert all(entry[4] == JOINT_LIMIT_EXPONENT for entry in feasible_small)
    assert feasible_small == [[2, 2, 1, 4, 24]]
    return {
        "conditions": "(i) 2^(3jK) 3^(3j zbar) > (a^2(2a-1))^(jK) (((a-1)!)^2 (2a-3)!!)^K 1344^zbar; "
                      "(ii) F(a,a)^(3jK) > the same right side",
        "source_lower_bound": "A >= max((2*3^(a-2))^K 2^zbar, 2^K 6^zbar, [a=2] 2^K 16^zbar)^j",
        "box": {"a": [2, a_max], "jK_at_most": jk_max, "j_zbar_at_most": jz_max,
                "K_at_least": 1, "j_at_least": 1, "zbar_at_least": 0},
        "box_completeness": "A <= 2^24 forces jK <= 24, 6^(j zbar) <= 2^23 < 6^9 and "
                            "3^(a-2) <= 2^23 < 3^15",
        "tuples_examined": examined,
        "feasible_tuples_with_bound_at_most_2^24_as_a_K_zbar_j_log2bound": feasible_small,
        "conclusion": "every such scheme with p < 3 has A >= 2^24; the bound of the "
                      "relaxation is attained only at (a, K, zbar, j) = (2, 2, 1, 4)",
    }


def make_report():
    return {
        "description": "Checks for the source-side lower bounds of Section 11.2",
        "potentials": check_potentials(),
        "example_ledger_a2": check_example_ledger(),
        "integer_inequalities": check_inequalities(),
        "case_analysis_box_sanity_check": check_case_analysis_box(),
        "flattening_ranks": check_flattenings(),
        "joint_decomposition_search": joint_search(),
        "all_checks_passed": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true", help="compare with the saved report")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results/source-side-bounds.json")
    arguments = parser.parse_args()
    report = make_report()
    if arguments.check:
        if json.loads(arguments.output.read_text()) != report:
            raise SystemExit("Recomputed report differs from the saved report")
    else:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(json.dumps(report, indent=2) + "\n")
    print("Verified the potentials on rows 2..60, the integer inequalities of "
          "Section 11.2, the flattening ranks, and the exhaustive search (A >= 2^24).")


if __name__ == "__main__":
    main()
