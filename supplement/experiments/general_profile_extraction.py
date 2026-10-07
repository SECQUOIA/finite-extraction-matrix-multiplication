"""Exact finite duals and tensor ledgers for general profile indices.

This verifies counts and small tensor maps, not a materialized rank certificate.
Run from the repository root: python -m experiments.general_profile_extraction
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from math import comb, gcd, lcm, prod
import json

from experiments.small_profile_extraction import Interval, sum_intervals


@dataclass(frozen=True)
class Concavity:
    row: int
    column: int
    weight: Fraction
    up: Fraction
    down: Fraction


@dataclass(frozen=True)
class Tripling:
    row: int
    weight: Fraction


def profile_diagonal(index: int) -> Fraction:
    if index < 1:
        raise ValueError("profile index must be positive")
    slope = prod((Fraction(3 * j + 1, 3 * j) for j in range(1, index)), start=Fraction(1))
    return Fraction(3 * index - 1, 2) * slope


def rational_dual(index: int) -> tuple[list[Concavity], list[Tripling]]:
    if index < 2:
        raise ValueError("extraction index must be at least two")
    concavity, tripling = [], []
    for row in range(2, index + 1):
        terminal = 4 * row - 1
        for column in range(row, terminal):
            if row == index:
                weight = Fraction(
                    2 * (2 * column + row - 1) * (terminal - column),
                    3 * (row - 1) * (3 * row - 1),
                )
            elif column == row:
                weight = Fraction(2 * (3 * row - 1), 3 * (row - 1))
            else:
                weight = Fraction(
                    4 * (2 * column + row - 1) * (terminal - column),
                    3 * (row - 1) * (3 * row + 1),
                )
            up_probability = Fraction(2 * column + row + 1, 2 * (2 * column + row - 1))
            concavity.append(Concavity(row, column, weight, weight * up_probability, weight * (1 - up_probability)))
        weight = (
            Fraction(1, row - 1) if row == index
            else Fraction(2 * (3 * row - 1), (row - 1) * (3 * row + 1))
        )
        tripling.append(Tripling(row, weight))
    return concavity, tripling


def integer_scale(index: int) -> int:
    concavity, tripling = rational_dual(index)
    denominators = [number.denominator for item in concavity for number in (item.up, item.down)]
    denominators.extend((item.weight / 3).denominator for item in tripling)
    return lcm(*denominators)


def closed_integer_scale(index: int) -> int:
    if index < 2:
        raise ValueError("extraction index must be at least two")
    final = 3 * (index - 1) * (3 * index - 1) // gcd(3 * index - 1, 4)
    lower_rows = [3 * t * (3 * t + 4) // gcd(t, 2) ** 2 for t in range(1, index - 1)]
    return lcm(final, *lower_rows)


def key(row: int, column: int) -> tuple[int, int]:
    return min(row, column), max(row, column)


def ledger(index: int) -> dict:
    concavity, tripling = rational_dual(index)
    scale = integer_scale(index)
    inputs, outputs = Counter(), Counter()
    for item in concavity:
        inputs[key(item.row, item.column)] += int(scale * item.weight)
        outputs[key(item.row, item.column + 1)] += int(scale * item.up)
        outputs[key(item.row, item.column - 1)] += int(scale * item.down)
    for item in tripling:
        inputs[key(item.row, 4 * item.row - 1)] += int(scale * item.weight)
        outputs[key(item.row, item.row)] += int(scale * item.weight)
    catalyst = {position: min(count, outputs[position]) for position, count in inputs.items()}
    catalyst = {position: count for position, count in catalyst.items() if count}
    return {
        "scale": scale,
        "inputs": dict(inputs),
        "outputs": dict(outputs),
        "catalyst": catalyst,
        "concavity_factors": sum(int(scale * item.weight) for item in concavity),
        "tripling_factors": sum(int(scale * item.weight) for item in tripling),
    }


def prime_factors(value: int) -> Counter:
    if value < 1:
        raise ValueError("factorization requires a positive integer")
    factors = Counter()
    divisor = 2
    while divisor * divisor <= value:
        while value % divisor == 0:
            factors[divisor] += 1
            value //= divisor
        divisor += 1
    if value > 1:
        factors[value] += 1
    return factors


def verify_entropy_identity(index: int) -> bool:
    """Compare prime valuations; avoid expanding enormous rational powers."""
    concavity, tripling = rational_dual(index)
    counts = ledger(index)
    scale = counts["scale"]
    left = Counter({2: scale - counts["concavity_factors"], 3: counts["tripling_factors"]})
    for item in concavity:
        for count, sign in ((int(scale * item.weight), 1), (int(scale * item.up), -1), (int(scale * item.down), -1)):
            for prime, valuation in prime_factors(count).items():
                left[prime] += sign * count * valuation
    diagonal = profile_diagonal(index)
    right = Counter()
    for value, sign in ((diagonal.numerator, 1), (diagonal.denominator, -1)):
        for prime, valuation in prime_factors(value).items():
            right[prime] += sign * scale * valuation
    return all(left[p] == right[p] for p in left.keys() | right.keys())


def determinant_terms(first_length: int, second_length: int) -> dict:
    """Exact general determinant basis change, including its off-diagonal terms."""
    a, b = first_length, second_length
    if a < 2 or b < 2:
        raise ValueError("both input lengths must be at least two")
    basis = [(0, i, {("s", i): 1}) for i in range(b)]
    basis.append((0, b, {("w", b - 1): 1}))
    basis.extend((1, i, {("w", i): 1, ("s", i + 1): -1}) for i in range(b - 1))
    output_degree = a + b - 2
    terms = Counter()
    for first_index in range(a):
        for input_sector, input_index, vector in basis:
            for (letter, index), coefficient in vector.items():
                index += first_index
                if letter == "s":
                    coordinates = ((0, index),)
                elif index == output_degree:
                    coordinates = ((0, output_degree + 1),)
                else:
                    coordinates = ((0, index + 1), (1, index))
                for output_sector, output_index in coordinates:
                    terms[first_index, input_sector, input_index, output_sector, output_index] += coefficient
    return {term: coefficient for term, coefficient in terms.items() if coefficient}


def tripling_terms(index: int):
    if index < 2:
        raise ValueError("index must be at least two")
    for first in range(index):
        for second in range(4 * index - 1):
            output = first + second
            y_sector = 0 if second < index else (1 if second < 3 * index - 1 else 2)
            z_sector = 0 if output < 2 * index - 1 else (1 if output < 3 * index - 1 else 2)
            yield first, second, output, y_sector, z_sector


def small_index_report(index: int) -> dict:
    if index not in (2, 3, 4):
        raise ValueError("explicit binomial costs are intentionally limited to indices 2,3,4")
    concavity, tripling = rational_dual(index)
    counts = ledger(index)
    scale = counts["scale"]
    sectors = [comb(int(scale * item.weight), int(scale * item.up)) for item in concavity]
    for item in tripling:
        factors = int(scale * item.weight)
        assert factors % 3 == 0
        sectors.append(comb(factors, factors // 3) * comb(2 * factors // 3, factors // 3))
    log2 = Interval.log_integer(2)
    logB = Interval.log_integer(prod(sectors))
    log_ratio = (logB + log2.scale(scale)) - log2.scale(counts["concavity_factors"])
    log_ratio = log_ratio.scale(2)
    diagonal = profile_diagonal(index)
    log_diagonal = Interval.log_integer(diagonal.numerator) - Interval.log_integer(diagonal.denominator)
    limit = Interval.log_integer(2 * index - 1).scale(3).divide_positive(log_diagonal)
    # This excludes interpolation and catalyst reuse. It is a diagnostic upper
    # expression after infinite amortization, not an implemented exponent.
    finite_type_expression = (
        Interval.log_integer(2 * index - 1).scale(6 * scale)
        + log2.scale(6 * len(sectors))
    ).divide_positive(log_ratio)
    log_catalyst = sum_intervals(
        Interval.log_integer(row + column - 1).scale(6 * count)
        for (row, column), count in counts["catalyst"].items()
    )
    return {
        "index": index,
        "minimal_scale_K": scale,
        "concavity_relations": len(concavity),
        "tripling_relations": len(tripling),
        "concavity_factors_U": counts["concavity_factors"],
        "tripling_factors_T": counts["tripling_factors"],
        "catalyst_Q_factors": sum(counts["catalyst"].values()),
        "largest_concavity_type_length": max(int(scale * item.weight) for item in concavity),
        "largest_sector_count_bits_at_N1": max(count.bit_length() for count in sectors),
        "source_matrix_dimension_at_N1": f"2^{2 * counts['concavity_factors']}",
        "entropy_identity_verified": verify_entropy_identity(index),
        "limiting_scalar_exponent_interval": limit.as_strings(),
        "N1_type_copy_upper_expression_interval": finite_type_expression.as_strings(),
        "log_catalyst_rank_bound_interval_at_N1": log_catalyst.as_strings(),
        "status": "counted tensor recipe; no composed rank certificate or practical implementation",
    }


def main() -> None:
    reports = [small_index_report(index) for index in (2, 3, 4)]
    index = 63
    scale = closed_integer_scale(index)
    print(json.dumps({
        "small_indices": reports,
        "index_63_scale": {
            "index": index,
            "minimal_scale_K": str(scale),
            "scale_decimal_digits": len(str(scale)),
            "note": "Only the rational scale is computed; tensor types are not expanded.",
        },
    }, indent=2))


if __name__ == "__main__":
    main()
