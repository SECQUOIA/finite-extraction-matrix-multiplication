"""Count an explicit, impractically large small-profile tensor construction.

This program verifies its resource ledger and rigorous logarithmic cost bounds.
It does not materialize the tensor maps or a matrix multiplication rank seed.
All logarithmic intervals use exact rational series and explicit tail bounds.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
from functools import lru_cache
from math import comb, prod
import json


WEIGHTS = (50, 56, 54, 44, 26)
UP_COUNTS = (35, 36, 33, 26, 15)
DOWN_COUNTS = (15, 20, 21, 18, 11)
CATALYST = {2: 35, 3: 56, 4: 54, 5: 44, 6: 26, 7: 15}
PRECISION = 90


def decimal_string(value: Fraction, direction) -> str:
    with localcontext() as context:
        context.prec = PRECISION
        context.rounding = direction
        return str(Decimal(value.numerator) / Decimal(value.denominator))


@lru_cache(maxsize=None)
def unit_log_bounds(value: Fraction, terms: int = 40) -> tuple[Fraction, Fraction]:
    """Bound log(value), for 1<=value<=2, using the atanh series."""
    if not 1 <= value <= 2:
        raise ValueError("unit logarithm requires an argument in [1,2]")
    z = (value - 1) / (value + 1)
    square = z * z
    power = z
    lower = Fraction(0)
    for index in range(terms):
        lower += 2 * power / (2 * index + 1)
        power *= square
    tail = 2 * power / ((2 * terms + 1) * (1 - square))
    return lower, lower + tail


@dataclass(frozen=True)
class Interval:
    lower: Fraction
    upper: Fraction

    @staticmethod
    def exact(value: int) -> "Interval":
        exact = Fraction(value)
        return Interval(exact, exact)

    @staticmethod
    def log_integer(value: int) -> "Interval":
        if value < 1:
            raise ValueError("logarithm requires a positive integer")
        if value == 1:
            return Interval.exact(0)
        exponent = value.bit_length() - 1
        mantissa_bits = 80
        if exponent <= mantissa_bits:
            lower_mantissa = upper_mantissa = Fraction(value, 1 << exponent)
        else:
            top_bits = value >> (exponent - mantissa_bits)
            lower_mantissa = Fraction(top_bits, 1 << mantissa_bits)
            upper_mantissa = Fraction(top_bits + 1, 1 << mantissa_bits)
        log2_lower, log2_upper = unit_log_bounds(Fraction(2))
        lower = exponent * log2_lower + unit_log_bounds(lower_mantissa)[0]
        upper = exponent * log2_upper + unit_log_bounds(upper_mantissa)[1]
        return Interval(lower, upper)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lower + other.lower, self.upper + other.upper)

    def __sub__(self, other: "Interval") -> "Interval":
        return Interval(self.lower - other.upper, self.upper - other.lower)

    def scale(self, numerator: int, denominator: int = 1) -> "Interval":
        if numerator < 0 or denominator < 1:
            raise ValueError("scale requires a nonnegative numerator and positive denominator")
        scale = Fraction(numerator, denominator)
        return Interval(self.lower * scale, self.upper * scale)

    def divide_positive(self, denominator: "Interval") -> "Interval":
        if self.lower < 0 or denominator.lower <= 0:
            raise ValueError("interval division requires nonnegative numerator and positive denominator")
        return Interval(self.lower / denominator.upper, self.upper / denominator.lower)

    def as_strings(self) -> dict[str, str]:
        return {
            "lower": decimal_string(self.lower, ROUND_FLOOR),
            "upper": decimal_string(self.upper, ROUND_CEILING),
        }

    def decimal_digits(self) -> int:
        """For an interval enclosing log10(integer), certify its digit count."""
        lower_floor = self.lower.numerator // self.lower.denominator
        upper_floor = self.upper.numerator // self.upper.denominator
        if lower_floor != upper_floor:
            raise ArithmeticError("interval straddles a decimal digit boundary")
        return int(lower_floor) + 1


def sum_intervals(values) -> Interval:
    result = Interval.exact(0)
    for value in values:
        result = result + value
    return result


def entropy_identity() -> Fraction:
    """Exact limiting dot-product gain per type-frequency scale."""
    result = Fraction(3 ** 15, 2 ** 215)
    for weight, up, down in zip(WEIGHTS, UP_COUNTS, DOWN_COUNTS):
        result *= Fraction(weight ** weight, up ** up * down ** down)
    return result


def resource_ledger(scale: int = 1) -> dict[str, dict[int, int] | int]:
    if scale < 1:
        raise ValueError("scale must be positive")
    inputs = {b: weight * scale for b, weight in zip(range(2, 7), WEIGHTS)}
    inputs[7] = 15 * scale
    outputs = {b: 0 for b in range(1, 8)}
    for b, up, down in zip(range(2, 7), UP_COUNTS, DOWN_COUNTS):
        outputs[b + 1] += up * scale
        outputs[b - 1] += down * scale
    outputs[2] += 15 * scale  # Sixfold balancing of the tripling branches.
    return {
        "inputs": inputs,
        "outputs": outputs,
        "catalyst": {b: count * scale for b, count in CATALYST.items()},
        "consumed_Q2": 15 * scale,
        "produced_Q1": 15 * scale,
        "input_oriented_dot_exponent": sum(WEIGHTS) * scale,
    }


def determinant_terms(b: int) -> dict[tuple[int, int, int, int, int], int]:
    """Exact C(2,b)*B_X(2) coefficients in the determinant-filtration bases.

    Keys: (first input, input sector, input index, output sector, output index).
    Sector 0 is quotient; sector 1 is kernel. Standard output coordinates are
    converted using w_i = q_(i+1)+k_i for i<b and w_b=q_(b+1).
    """
    if b < 2:
        raise ValueError("b must be at least two")
    basis = [(0, i, {("s", i): 1}) for i in range(b)]
    basis.append((0, b, {("w", b - 1): 1}))
    basis.extend((1, i, {("w", i): 1, ("s", i + 1): -1}) for i in range(b - 1))
    terms = {}
    for x in (0, 1):
        for input_sector, input_index, vector in basis:
            for (letter, index), coefficient in vector.items():
                index += x
                if letter == "s":
                    coordinates = ((0, index),)
                elif index == b:
                    coordinates = ((0, b + 1),)
                else:
                    coordinates = ((0, index + 1), (1, index))
                for output_sector, output_index in coordinates:
                    key = (x, input_sector, input_index, output_sector, output_index)
                    terms[key] = terms.get(key, 0) + coefficient
    return {key: coefficient for key, coefficient in terms.items() if coefficient}


def tripling_terms():
    """C(2,7) coefficients with the three sectors used in the construction."""
    for x in (0, 1):
        for y in range(7):
            z = x + y
            y_sector = 0 if y < 2 else (1 if y < 5 else 2)
            z_sector = 0 if z < 3 else (1 if z < 5 else 2)
            yield x, y, z, y_sector, z_sector


def construction_costs(scale: int, interpolation_power: int, reuse: int) -> dict:
    if min(scale, interpolation_power, reuse) < 1:
        raise ValueError("all construction parameters must be positive")
    n, k, j = scale, interpolation_power, reuse
    sectors = [comb(weight * n, up * n) for weight, up in zip(WEIGHTS, UP_COUNTS)]
    sectors.append(comb(15 * n, 5 * n) * comb(10 * n, 5 * n))
    sector_product = prod(sectors)
    degree = 6 * sum((count - 1) ** 2 for count in sectors)
    evaluations = k * degree + 1

    log2 = Interval.log_integer(2)
    log3 = Interval.log_integer(3)
    log10 = Interval.log_integer(10)
    logB = Interval.log_integer(sector_product)
    log_source_size = log2.scale(460 * n)
    log_target_size = log2.scale(30 * n) + logB.scale(2)
    log_ratio = log_target_size - log_source_size
    if log_ratio.lower <= 0:
        raise ValueError("construction does not give a certified dimension increase")
    # Each of the 36 separators has source/target copy ratio below two.
    # Keep this as an upper cost bound, not a tensor cancellation.
    log_copy_ratio_bound = log2.scale(36)
    log_catalyst_rank = sum_intervals(
        Interval.log_integer(b + 1).scale(count)
        for b, count in CATALYST.items()
    ).scale(6 * n)
    log_evaluations = Interval.log_integer(evaluations)
    normalized_calls = (
        log3.scale(90 * n)
        + log_copy_ratio_bound
        + log_evaluations.scale(1, k)
        + log_catalyst_rank.scale(1, j)
    )
    # ceil(r/m) <= 2r/m, since r/m >= 1. This avoids constructing the
    # enormous call and output multiplicities and gives a rigorous upper bound.
    upper_expression = normalized_calls + log2.scale(1, k * j)
    exponent_upper_bound = upper_expression.divide_positive(log_ratio)
    ideal_finite_bound = (log3.scale(90 * n) + log_copy_ratio_bound).divide_positive(log_ratio)
    log10_padded_target = log_target_size.scale(k * j).divide_positive(log10)
    log10_recursive_input = log_source_size.scale(k * j).divide_positive(log10)
    log10_batches = logB.scale(6 * k * j).divide_positive(log10)
    log10_shrink_ratio = log_ratio.scale(k * j).divide_positive(log10)
    return {
        "scale_N": n,
        "interpolation_power_k": k,
        "catalyst_reuse_j": j,
        "status": "explicit tensor recipe; maps and rank seed not materialized; impractical",
        "sector_count_bit_lengths": [count.bit_length() for count in sectors],
        "interpolation_degree_bit_length": degree.bit_length(),
        "interpolation_evaluations_bit_length": evaluations.bit_length(),
        "exponent_upper_expression_interval": exponent_upper_bound.as_strings(),
        "certified_below_2_79": exponent_upper_bound.upper < Fraction(279, 100),
        "finite_type_upper_expression_interval": ideal_finite_bound.as_strings(),
        "padded_target_dimension_decimal_digits": log10_padded_target.decimal_digits(),
        "recursive_input_dimension_decimal_digits": log10_recursive_input.decimal_digits(),
        "simultaneous_output_count_decimal_digits": log10_batches.decimal_digits(),
        "log10_dimension_shrink_ratio": log10_shrink_ratio.as_strings(),
        "resource_ledger": resource_ledger(n),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scale", type=int, default=300)
    parser.add_argument("--interpolation-power", type=int, default=125)
    parser.add_argument("--reuse", type=int, default=3750)
    args = parser.parse_args()
    if min(args.scale, args.interpolation_power, args.reuse) < 1:
        parser.error("all construction parameters must be positive")
    assert entropy_identity() == Fraction(10, 3) ** 15
    print(json.dumps(construction_costs(args.scale, args.interpolation_power, args.reuse), indent=2))


if __name__ == "__main__":
    main()
