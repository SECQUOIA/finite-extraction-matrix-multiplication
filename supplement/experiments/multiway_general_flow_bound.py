#!/usr/bin/env python3
"""Exact certificates for the all-width conserved-flow dimension bound.

This audits necessary conditions, not the existence of any algorithm.
It uses integer arithmetic and fractions only.
"""

from fractions import Fraction
import json


def audit() -> dict:
    # A multiplicative potential on every legal split in row r=2.
    potential = (2, 1, 2, 4, 6, 12, 16)
    edge_count = 0
    for x in range(1, 6):
        for h in range(1, min(x, 6 - x) + 1):
            for y in range(x - h, x + h + 1, 2):
                assert (h + 1) * potential[x] >= potential[y]
                edge_count += 1

    # If p<3 at a=2, these two strict inequalities are necessary:
    # z/K > log(3/2)/log(3), jK > z log(24)/log(10/9).
    # Exhaust all triples that would have the lower side exponent <96.
    examined = 0
    feasible_below_96 = []
    for K in range(1, 96):
        for z in range(1, 24):
            for j in range(1, 96 // (K + 4 * z) + 1):
                if j * (K + 4 * z) >= 96:
                    continue
                examined += 1
                if 3**z * 2**K <= 3**K:
                    continue
                if 10 ** (j * K) <= 9 ** (j * K) * 24**z:
                    continue
                feasible_below_96.append((K, z, j))
    assert not feasible_below_96
    K, z, j = 2, 1, 16
    assert 3**z * 2**K > 3**K
    assert 10 ** (j * K) > 9 ** (j * K) * 24**z
    assert j * (K + 4 * z) == 96

    # For a=3, z_total/K>5/6 and catalyst overhead imply j>17.
    assert Fraction(5, 2) ** 6 > 3**5
    assert Fraction(3**6 * 24**5) > Fraction(56, 45) ** 102
    assert 6**18 > 2**32

    # For a>=4, write t_a=F(a,a)/(2a-1), P_a=prod_{r=2}^{a-1}(2r-1).
    # P_4>t_4^8. The induction in the note uses t_{a+1}/t_a<(a+1)/a
    # and ((a+1)/a)^8 <= (5/4)^8 < 7 <= 2a-1.
    assert Fraction(15) > Fraction(770, 567) ** 8
    assert Fraction(5, 4) ** 8 < 7
    assert 18**9 > 2**32
    # A sharper uniform statement: handle a=4 separately; for a>=5 use j>=9.
    assert Fraction(360) > Fraction(770, 567) ** 19
    assert 18**20 > 54**9 > 6**18
    # Global potential D(0)=2,D(x)=x: for positive children the slack
    # is at least h(x-1)>=0; for child zero x=h and x(x+1)>=2.
    assert Fraction(105) > Fraction(3185, 2187) ** 12
    assert 2**96 > 12**18
    assert 18**20 > 12**18
    assert 54**13 > 12**18
    assert 162**9 > 12**18 > 2**64

    return {
        "status": "all exact checks passed",
        "scope": "prescribed three-orientation multiway extraction; arbitrary nonnegative integer conserved flows and legal widths",
        "a2_split_edges_checked": edge_count,
        "a2_triples_below_96_examined": examined,
        "a2_relaxed_conditions_minimum_side_lower_bound": "2^96",
        "a2_relaxed_conditions_minimizer": {"K": K, "z": z, "j": j},
        "a3_side_lower_bound": "12^18",
        "a_ge4_side_lower_bound": "18^9",
        "a4_sharper_side_lower_bound": "18^20",
        "a_ge5_side_lower_bound": "54^9",
        "a5_sharper_side_lower_bound": "54^13",
        "a_ge6_side_lower_bound": "162^9",
        "all_a_subcubic_side_lower_bound": ">=12^18 (>2^64)",
        "warning": "These are lower bounds for the prescribed extraction, not for matrix multiplication or other tensor maps.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
