#!/usr/bin/env python3
"""Exact scalar-profile checks and optional finite linear programs.

These profiles are scalar relaxations from the preserved paper, not matrix
multiplication algorithms. See docs/profile-analysis.md for the proof.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math
from pathlib import Path


def growth_factors(limit: int) -> list[Fraction]:
    """Return H_a = product_{m=1}^{a-1} (1 + 1/(3m)), indexed by a."""
    if limit < 1:
        raise ValueError("limit must be positive")
    factors = [Fraction(0), Fraction(1)]
    for a in range(2, limit + 1):
        factors.append(factors[-1] * Fraction(3 * a - 2, 3 * a - 3))
    return factors


def profile(a: int, b: int, factors: list[Fraction] | None = None) -> Fraction:
    """Evaluate the pointwise least profile satisfying the scalar axioms."""
    if a < 1 or b < 1:
        raise ValueError("indices must be positive")
    m, n = sorted((a, b))
    factors = growth_factors(m) if factors is None else factors
    return factors[m] * Fraction(2 * n + m - 1, 2)


def certificate_grid(a: int, b: int) -> int:
    """Give a sufficient finite grid for the sharp lower-bound proof."""
    if a < 1 or b < 1:
        raise ValueError("indices must be positive")
    m, n = sorted((a, b))
    landmark = m
    while landmark < n:
        landmark = 3 * landmark + m - 1
    return max(4 * m - 1, landmark)


def verify_grid(limit: int) -> dict[str, int | str]:
    """Check every represented axiom exactly using rational arithmetic."""
    factors = growth_factors(limit)
    values = {
        (a, b): profile(a, b, factors)
        for a in range(1, limit + 1)
        for b in range(1, limit + 1)
    }
    counts = {"positive": 0, "symmetric": 0, "boundary": 0,
              "concavity": 0, "tripling": 0, "upper_bound": 0}
    for (a, b), value in values.items():
        assert value > 0
        counts["positive"] += 1
        assert value == values[b, a]
        counts["symmetric"] += 1
        # Cubing compares to (a+b-1)^(4/3) without irrational arithmetic.
        assert value ** 3 <= (a + b - 1) ** 4
        counts["upper_bound"] += 1
        if a == 1:
            assert value == b
            counts["boundary"] += 1
        if 2 <= b < limit:
            slack = 2 * value - values[a, b - 1] - values[a, b + 1]
            assert slack >= 0
            if b <= a:
                assert slack == factors[b] * Fraction(
                    2 * (a - b), 3 * b * (3 * b - 2)
                )
            else:
                assert slack == 0
            counts["concavity"] += 1
        target = 3 * b + a - 1
        if target <= limit:
            assert values[a, target] >= 3 * value
            counts["tripling"] += 1
    return {"status": "exact_checks_passed", "grid_size": limit, **counts}


def solve_finite_lp(a: int, b: int, grid_size: int | None = None) -> dict:
    """Numerically minimize P(a,b) over the finite linear relaxation.

    Symmetry is built into the variable indexing. Strict positivity is relaxed
    to nonnegativity. The nonlinear upper bound is omitted; the exact extremal
    profile satisfies it. A finite LP is numerical corroboration of the proof.
    """
    import numpy as np
    import scipy
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix

    proof_grid = certificate_grid(a, b)
    limit = proof_grid if grid_size is None else grid_size
    if limit < max(a, b):
        raise ValueError("grid must include the target")
    pairs = [(i, j) for i in range(1, limit + 1)
             for j in range(i, limit + 1)]
    index = {pair: k for k, pair in enumerate(pairs)}
    rows, columns, entries = [], [], []
    row_count = 0

    def add_constraint(terms: list[tuple[int, int, float]]) -> None:
        nonlocal row_count
        for i, j, coefficient in terms:
            rows.append(row_count)
            columns.append(index[min(i, j), max(i, j)])
            entries.append(coefficient)
        row_count += 1

    for i in range(1, limit + 1):
        for j in range(2, limit):
            add_constraint([(i, j - 1, 1), (i, j, -2), (i, j + 1, 1)])
        for h in range(1, (limit - i + 1) // 3 + 1):
            add_constraint([(i, h, 3), (i, 3 * h + i - 1, -1)])
    matrix = coo_matrix((entries, (rows, columns)),
                        shape=(row_count, len(pairs))).tocsr()
    objective = np.zeros(len(pairs))
    objective[index[min(a, b), max(a, b)]] = 1
    bounds = [(j, j) if i == 1 else (0, None) for i, j in pairs]
    result = linprog(objective, A_ub=matrix, b_ub=np.zeros(row_count),
                     bounds=bounds, method="highs",
                     options={"time_limit": 60.0})
    exact = profile(a, b)
    report = {
        "target": [a, b], "grid_size": limit,
        "sufficient_proof_grid": proof_grid,
        "variables": len(pairs), "inequalities": row_count,
        "scipy_version": scipy.__version__,
        "solver": "scipy.optimize.linprog(method='highs')",
        "success": bool(result.success), "status": int(result.status),
        "message": result.message,
        "exact_infinite_minimum": str(exact),
        "exact_infinite_minimum_float": float(exact),
    }
    if result.success:
        report.update({
            "lp_minimum": float(result.fun),
            "difference_from_exact_minimum": float(result.fun) - float(exact),
            "maximum_inequality_violation": float(
                np.max(-result.ineqlin.residual, initial=0.0)
            ),
        })
    return report


def parse_target(text: str) -> tuple[int, int]:
    try:
        pieces = text.split(",")
        if len(pieces) != 2:
            raise ValueError
        a, b = map(int, pieces)
        if min(a, b) < 1:
            raise ValueError
    except ValueError as error:
        raise argparse.ArgumentTypeError("target must be two positive integers a,b") from error
    return a, b


def finite_exponent_envelope(log_dimension: float) -> tuple[float, float]:
    """Bounds for 3 log(2a-1)/log F(a,a), evaluated in binary64.

    Gamma log-convexity proves the underlying bounds. These returned floats
    are numerical evaluations, not outward-rounded interval certificates.
    The logarithmic input avoids large gamma values and dimension overflow.
    """
    if log_dimension < math.log(2):
        raise ValueError("dimension must be at least two")
    inverse_a = math.exp(-log_dimension)
    log_c = math.log(1.5) - math.lgamma(4 / 3)
    log_d_upper = (4 * log_dimension / 3 + log_c
                   + math.log1p(-inverse_a / 3))
    log_d_lower = log_d_upper - 2 * math.log1p(inverse_a / 3) / 3
    numerator = 3 * (log_dimension + math.log(2)
                     + math.log1p(-inverse_a / 2))
    return numerator / log_d_upper, numerator / log_d_lower


def exact_threshold(target: Fraction, limit: int) -> int | None:
    """Find the first a <= limit meeting the bound, with exact integer tests.

    This bounded scan is intended for modest dimensions. For target p/q the
    criterion is F(a,a)^p >= (2a-1)^(3q), with no logarithms or rounding.
    """
    if target <= 0 or limit < 2:
        raise ValueError("target must be positive and limit at least two")
    factor = Fraction(1)
    for a in range(2, limit + 1):
        factor *= Fraction(3 * a - 2, 3 * a - 3)
        diagonal = Fraction(3 * a - 1, 2) * factor
        if (diagonal ** target.numerator
                >= (2 * a - 1) ** (3 * target.denominator)):
            return a
    return None


def numerical_exponent(a: int) -> float:
    """Compute a modest-dimension exponent from a stable logarithmic sum."""
    if not 2 <= a <= 1_000_000:
        raise ValueError("use this direct sum only for 2 <= a <= 1000000")
    log_diagonal = math.log((3 * a - 1) / 2) + math.fsum(
        math.log1p(1 / (3 * m)) for m in range(1, a)
    )
    return 3 * math.log(2 * a - 1) / log_diagonal


def finite_cost_estimates() -> dict:
    """Report finite profile indices; none are matrix multiplication seeds."""
    targets = ("2.5", "2.4", "2.3", "2.26", "2.251")
    log_c = math.log(1.5) - math.lgamma(4 / 3)
    records = []
    for target_text in targets:
        # Decimal arithmetic preserves the requested decimal target near 9/4.
        # log_c still comes from binary64; only four significant figures in
        # the dimension estimate are presented as meaningful.
        with localcontext() as context:
            context.prec = 50
            target = Decimal(target_text)
            leading_log_a = (
                3 * Decimal(2).ln() - target * Decimal(str(log_c))
            ) / (4 * target / 3 - 3)
            leading_log10_a = leading_log_a / Decimal(10).ln()
            scientific_a = format(leading_log_a.exp(), ".3E")
        record = {
            "target_exponent": target_text,
            "leading_asymptotic_log_dimension": float(leading_log_a),
            "leading_asymptotic_log10_dimension": float(leading_log10_a),
            "leading_asymptotic_dimension_4_significant_figures": scientific_a,
            "finite_index_estimate": None,
        }
        if target_text in ("2.5", "2.4"):
            record["finite_index_estimate"] = exact_threshold(Fraction(target_text), 100)
            record["status"] = "minimum certified by exact rational scan"
        elif target_text == "2.3":
            # The analytic envelope localizes the crossing near 596000.
            # These adjacent evaluations establish a numerical crossing only.
            candidate = 595975
            record.update({
                "finite_index_estimate": candidate,
                "status": "numerical crossing; not an exact minimality certificate",
                "exponent_at_previous_index": numerical_exponent(candidate - 1),
                "exponent_at_index": numerical_exponent(candidate),
            })
        else:
            record["finite_index_estimate"] = scientific_a
            record["status"] = "asymptotic scale estimate, four significant figures"
            log_a = float(leading_log_a)
            record["localization_log_dimension_half_width"] = 0.001
            record["lower_exponent_bound_below_estimate"] = finite_exponent_envelope(
                log_a - 0.001
            )[0]
            record["upper_exponent_bound_above_estimate"] = finite_exponent_envelope(
                log_a + 0.001
            )[1]
        records.append(record)
    return {
        "scope": "profile index a, not a matrix multiplication seed dimension",
        "formula": "tau_a = 3 log(2a-1) / log F(a,a)",
        "asymptotic_gap_coefficient": (3 * math.log(2) - 2.25 * log_c) / (4 / 3),
        "error_policy": (
            "Only the first two minima use exact rational comparisons. Other "
            "values are numerical estimates. The analytic Gamma envelopes "
            "bound finite-a corrections; their binary64 evaluation is not "
            "certified interval arithmetic. Four significant figures are "
            "retained for very large dimensions."
        ),
        "estimates": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index", type=int, default=64)
    parser.add_argument("--lp-target", action="append", type=parse_target, default=[])
    parser.add_argument("--finite-costs", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "scope": "scalar profile only; not a matrix multiplication algorithm",
        "verification": verify_grid(args.max_index),
        "diagonal_asymptotic_exponent": "4/3",
        "diagonal_asymptotic_constant": 3 / (2 * math.gamma(4 / 3)),
        "linear_programs": [solve_finite_lp(a, b) for a, b in args.lp_target],
    }
    if args.finite_costs:
        report["finite_costs"] = finite_cost_estimates()
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")
    if any(not item["success"] for item in report["linear_programs"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
