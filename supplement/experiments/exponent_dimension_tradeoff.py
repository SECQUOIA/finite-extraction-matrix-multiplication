#!/usr/bin/env python3
"""Exact certificates for prescribed all-flow exponent/dimension tradeoffs.

This does not search for feasible extraction schemes.  Each reported dimension
is a necessary lower bound, obtained by deliberately discarding overheads.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def profile_defect_ratio(a: int) -> Fraction:
    """exp(4 c_a); F(a,a)^3 <= (2a-1)^4 / this ratio."""
    assert a >= 2
    return Fraction(135, 128) * Fraction(4*a-2, 3*a-1)**4


def index_from_ratio(eps: Fraction, ratio: Fraction) -> int:
    """Smallest integer a satisfying the necessary ratio inequality.

    (2a-1)^(16u) >= ratio^(4u+9v), eps=u/v.
    All comparisons are exact integers, including the search boundary.
    """
    u, v = eps.numerator, eps.denominator
    exponent = 4*u+9*v
    target_num = ratio.numerator**exponent
    target_den = ratio.denominator**exponent
    def passes(a: int) -> bool:
        return (2*a-1)**(16*u)*target_den >= target_num
    hi = 2
    while not passes(hi):
        hi *= 2
    lo = 1
    while lo+1 < hi:
        mid = (lo+hi)//2
        if passes(mid):
            hi = mid
        else:
            lo = mid
    assert passes(hi) and not passes(hi-1)
    return hi


def necessary_bounds(eps: Fraction, rounds: int = 8) -> dict:
    assert 0 < eps <= Fraction(1, 4)
    a = 2
    trace = [a]
    for _ in range(rounds):
        new_a = max(a, index_from_ratio(eps, profile_defect_ratio(a)))
        trace.append(new_a)
        if new_a == a:
            break
        a = new_a
    assert a >= 3
    # The exponent target sharpens reuse: j > 9(a-2)/(8 epsilon).
    # Also log_2(3)>3/2 follows from 9>8.
    reuse_threshold = Fraction(9*(a-2), 8)/eps
    j = reuse_threshold.numerator//reuse_threshold.denominator+1
    log2_A_lower = j*(3*a-4)//2
    return {
        "epsilon": str(eps),
        "target_exponent": str(Fraction(9,4)+eps),
        "necessary_index_at_least": str(a),
        "necessary_reuse_at_least": str(j),
        "source_side_strictly_above_2_power": str(log2_A_lower),
        "factorized_source_side_at_least": {
            "power_of_2": str(j),
            "power_of_3": str(j*(a-2)),
        },
        "bootstrap_indices": [str(x) for x in trace],
        "bootstrap_round_limit": rounds,
        "bootstrap_is_optimality_claim": False,
    }


def check_certificates() -> dict:
    # The induction polynomial for the retained s_a^3 upper bound.
    # (3a+2)(3a)^3-(3a-1)(3a+1)^3 = 6a+1 > 0.
    for a in range(1, 257):
        assert (3*a+2)*(3*a)**3-(3*a-1)*(3*a+1)**3 == 6*a+1
    assert Fraction(4,3)**3 == Fraction(128,135)*Fraction(5,2)
    assert profile_defect_ratio(2) == Fraction(2187,1000)
    assert Fraction(135,128)*Fraction(4,3)**4 == Fraction(10,3)
    # Defect ratio increases: the ratio inside its fourth power does.
    for a in range(2, 257):
        assert Fraction(4*a+2,3*a+2) > Fraction(4*a-2,3*a-1)
    # Pair r with a+1-r in Q_a=prod_{r=2}^{a-1}(2r-1).
    # Every pair exceeds 2a-1, and Q_a^2>(2a-1)^(a-2).
    checks = 0
    for a in range(3, 257):
        product = 1
        for r in range(2,a):
            pair = (2*r-1)*(2*a+1-2*r)
            assert pair >= 3*(2*a-3) > 2*a-1
            product *= 2*r-1
            checks += 1
        assert product**2 > (2*a-1)**(a-2)
    assert 3**2 > 2**3
    return {
        "induction_identity_samples": 256,
        "odd_factor_pair_checks": checks,
        "max_index_checked": 256,
        "proof_for_all_indices": "Symbolic identities and endpoint inequalities in companion Markdown; finite checks are regression checks only.",
        "unconditional_exp_4c": "2187/1000",
        "limiting_exp_4c": "10/3",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT/"results/exponent-dimension-tradeoff.json")
    args = parser.parse_args()
    report = {
        "scope": "All conserved integer flows and legal split widths, with prescribed source and catalyst rank decompositions and the pooled exponent cost model.",
        "paper_modified": False,
        "certificates": check_certificates(),
        "necessary_bounds": [necessary_bounds(eps) for eps in (Fraction(1,4), Fraction(1,10), Fraction(1,20), Fraction(1,100))],
        "not_claimed": ["Feasibility or optimality of displayed indices", "An arbitrary-circuit rank lower bound", "A wall-clock crossover", "A limitation on other source or catalyst decompositions"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
