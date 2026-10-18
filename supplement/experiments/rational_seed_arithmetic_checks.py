"""Check denominator scaling, intermediate heights, and rounded recursion.

Run from any directory:
    python experiments/rational_seed_arithmetic_checks.py
    python experiments/rational_seed_arithmetic_checks.py --check

This uses a rational rescaling of Strassen's 2-by-2 seed, not the huge
seed in the paper. All reference arithmetic, binary rounding, and error
comparisons use integers or fractions from Python's standard library.
The --check option compares a recomputed report with the saved report.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path
from random import Random


U = [
    [1, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 0],
    [0, 0, 0, 1], [1, 1, 0, 0], [-1, 0, 1, 0], [0, 1, 0, -1],
]
V = [
    [1, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, -1],
    [-1, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [0, 0, 1, 1],
]
W = [
    [1, 0, 0, 1, -1, 0, 1], [0, 0, 1, 0, 1, 0, 0],
    [0, 1, 0, 1, 0, 0, 0], [1, -1, 1, 0, 0, 1, 0],
]


def round_binary(value, precision):
    """Round an exact rational to nearest binary; break ties to even.

    Exponents are unbounded, so overflow and underflow are absent.
    """
    value = Fraction(value)
    if not value:
        return value
    sign = -1 if value < 0 else 1
    numerator, denominator = abs(value.numerator), value.denominator
    exponent = numerator.bit_length() - denominator.bit_length()
    if exponent >= 0:
        if numerator < denominator << exponent:
            exponent -= 1
    elif numerator << -exponent < denominator:
        exponent -= 1
    shift = precision - 1 - exponent
    if shift >= 0:
        numerator <<= shift
    else:
        denominator <<= -shift
    rounded, remainder = divmod(numerator, denominator)
    if 2 * remainder > denominator or (2 * remainder == denominator and rounded % 2):
        rounded += 1
    if shift >= 0:
        return sign * Fraction(rounded, 1 << shift)
    return Fraction(sign * (rounded << -shift))


class Arithmetic:
    def __init__(self, precision=None):
        self.precision = precision
        self.peak_bits = 1
        self.leaves = 0

    def store(self, value):
        if self.precision is not None:
            return round_binary(value, self.precision)
        assert isinstance(value, int)
        self.peak_bits = max(self.peak_bits, abs(value).bit_length() + 1)
        return value

    def add(self, left, right):
        return self.store(left + right)

    def multiply(self, left, right):
        return self.store(left * right)


def combine(coefficients, blocks, arithmetic):
    side = len(blocks[0])
    result = [[0] * side for _ in range(side)]
    for coefficient, block in zip(coefficients, blocks):
        for i in range(side):
            for j in range(side):
                term = arithmetic.multiply(coefficient, block[i][j])
                result[i][j] = arithmetic.add(result[i][j], term)
    return result


def blocks(matrix):
    side = len(matrix) // 2
    return [
        [[matrix[i + x * side][j + y * side] for j in range(side)] for i in range(side)]
        for x, y in [(0, 0), (0, 1), (1, 0), (1, 1)]
    ]


def recursive_product(left, right, maps, arithmetic):
    if len(left) == 1:
        arithmetic.leaves += 1
        return [[arithmetic.multiply(left[0][0], right[0][0])]]
    left_blocks, right_blocks = blocks(left), blocks(right)
    input_u, input_v, output_w = maps
    products = [
        recursive_product(
            combine(u, left_blocks, arithmetic),
            combine(v, right_blocks, arithmetic), maps, arithmetic,
        )
        for u, v in zip(input_u, input_v)
    ]
    output_blocks = [combine(w, products, arithmetic) for w in output_w]
    half = len(left) // 2
    return [
        [output_blocks[(i // half) * 2 + j // half][i % half][j % half]
         for j in range(2 * half)]
        for i in range(2 * half)
    ]


def classical(left, right):
    side = len(left)
    return [[sum(left[i][h] * right[h][j] for h in range(side))
             for j in range(side)] for i in range(side)]


def max_entry(matrix):
    return max(abs(value) for row in matrix for value in row)


def max_row_sum(matrix):
    return max(sum(abs(value) for value in row) for row in matrix)


def max_error(observed, expected):
    return max(abs(x - y) for xr, yr in zip(observed, expected) for x, y in zip(xr, yr))


def verify_binary_rounding():
    # Distinct checks of tie breaking, sign, scaling, and exact powers of two.
    cases = [
        (Fraction(9, 8), 3, Fraction(1)),
        (Fraction(11, 8), 3, Fraction(3, 2)),
        (Fraction(-11, 8), 3, Fraction(-3, 2)),
        (Fraction(9, 64), 3, Fraction(1, 8)),
        (Fraction(72), 3, Fraction(64)),
        (Fraction(1, 1024), 3, Fraction(1, 1024)),
    ]
    for value, precision, expected in cases:
        assert round_binary(value, precision) == expected
    for precision in (3, 12, 20):
        for denominator in range(1, 17):
            for numerator in range(-50, 51):
                value = Fraction(numerator, denominator)
                rounded = round_binary(value, precision)
                assert abs(rounded - value) <= Fraction(1, 1 << precision) * abs(value)
    return {"tie_and_scaling_cases": len(cases), "relative_error_cases": 3 * 16 * 101}


def make_report():
    rounding_checks = verify_binary_rounding()
    rational_maps = (
        [[Fraction(value, 2) for value in row] for row in U],
        [[Fraction(value, 3) for value in row] for row in V],
        [[Fraction(6 * value) for value in row] for row in W],
    )
    denominator = 6
    integer_maps = tuple(
        [[int(denominator * value) for value in row] for row in matrix]
        for matrix in rational_maps
    )
    # Certify the seed identity on every pair of matrix-unit inputs.
    for left_index in range(4):
        for right_index in range(4):
            left = [[int(2 * i + j == left_index) for j in range(2)] for i in range(2)]
            right = [[int(2 * i + j == right_index) for j in range(2)] for i in range(2)]
            exact = recursive_product(left, right, integer_maps, Arithmetic())
            assert exact == [[denominator ** 3 * x for x in row] for row in classical(left, right)]
    d, rank, input_bits = 2, 7, 5
    height = max(max_entry(matrix) for matrix in integer_maps)
    c_in = (d * d * height - 1).bit_length()
    c_out = (rank * height - 1).bit_length()
    gamma = max_row_sum(rational_maps[0]) * max_row_sum(rational_maps[1]) * max_row_sum(rational_maps[2])
    random = Random(217)
    exact_trials, rounded_trials = [], []
    for depth in (1, 2, 3):
        side = d ** depth
        for trial in range(4):
            left = [[random.randrange(-31, 32) for _ in range(side)] for _ in range(side)]
            right = [[random.randrange(-31, 32) for _ in range(side)] for _ in range(side)]
            expected = classical(left, right)
            arithmetic = Arithmetic()
            observed = recursive_product(left, right, integer_maps, arithmetic)
            scale = denominator ** (3 * depth)
            assert observed == [[scale * value for value in row] for row in expected]
            bit_bound = 2 * input_bits + depth * (2 * c_in + c_out) + 2
            assert arithmetic.peak_bits <= bit_bound
            assert arithmetic.leaves == rank ** depth
            exact_trials.append({
                "side": side, "trial": trial, "depth": depth,
                "scale": scale, "peak_signed_bits": arithmetic.peak_bits,
                "proved_bit_bound": bit_bound, "leaf_products": arithmetic.leaves,
                "exact_scaling_verified": True,
            })
            for precision in (12, 20):
                rounded_arithmetic = Arithmetic(precision)
                stored_maps = tuple(
                    [[rounded_arithmetic.store(value) for value in row] for row in matrix]
                    for matrix in rational_maps
                )
                rounded = recursive_product(left, right, stored_maps, rounded_arithmetic)
                error = max_error(rounded, expected)
                # This implementation adds each dot-product term to an initial
                # zero. That first addition is exact, so T counts q-1 or R-1
                # potentially inexact additions, as in the manuscript.
                path_length = depth * (2 * d * d + rank + 3) + 1
                unit_roundoff = Fraction(1, 1 << precision)
                assert path_length * unit_roundoff < 1
                gamma_t = path_length * unit_roundoff / (1 - path_length * unit_roundoff)
                bound = gamma_t * gamma ** depth * max_entry(left) * max_entry(right)
                assert error <= bound
                rounded_trials.append({
                    "side": side, "trial": trial, "significand_bits": precision,
                    "path_length_bound": path_length,
                    "max_absolute_error": str(error), "proved_error_bound": str(bound),
                    "error_bound_verified": True,
                })
    return {
        "description": "Rationally rescaled Strassen seed; not the paper's large seed",
        "random_seed": 217, "seed_side": d, "seed_rank": rank,
        "rational_rescaling": {"U": "1/2", "V": "1/3", "W": "6"},
        "common_denominator": denominator, "integer_coefficient_height": height,
        "gamma": str(gamma), "matrix_unit_identity_cases": 16,
        "binary_rounding_checks": rounding_checks,
        "exact_scaling_trials": exact_trials, "rounded_trials": rounded_trials,
        "all_checks_passed": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare with the saved report")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results/rational-seed-arithmetic-checks.json")
    arguments = parser.parse_args()
    report = make_report()
    if arguments.check:
        if json.loads(arguments.output.read_text()) != report:
            raise SystemExit("Recomputed report differs from the saved report")
    else:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(json.dumps(report, indent=2) + "\n")
    print("Verified 16 seed identities, 12 exact scaling trials, 24 rounded recursion trials, and exact binary-rounding checks.")


if __name__ == "__main__":
    main()
