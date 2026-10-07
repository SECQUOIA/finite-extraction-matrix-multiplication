"""Exact checks and copy costs for a constructive shared-leg separator.

This does not implement a new matrix multiplication algorithm. It checks the
coefficient identities in docs/constructive-analysis.md, without floating point.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, lcm
import json


@dataclass(frozen=True)
class Separator:
    blocks: int
    auxiliary: int
    slope: int = 1

    def __post_init__(self) -> None:
        if min(self.blocks, self.auxiliary, self.slope) < 1:
            raise ValueError("blocks, auxiliary, and slope must be positive")

    @property
    def copies(self) -> int:
        return self.auxiliary + self.slope * (self.blocks - 1)

    @property
    def max_mismatch(self) -> int:
        return min(self.blocks - 1, (self.auxiliary - 1) // self.slope)

    def terms(self):
        """Yield terms after the first Fourier projection, with exact weights."""
        for h, g, u, v in product(
            range(self.blocks), range(self.blocks),
            range(self.auxiliary), range(self.auxiliary),
        ):
            phase = u - v + self.slope * (g - h)
            if phase % self.copies == 0:
                weight = (
                    self.slope * g * g + 2 * h * u
                    - self.slope * h * h - 2 * h * v
                )
                yield h, g, u, v, phase, weight


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    return all(value % d for d in range(2, isqrt(value) + 1))


def projection_order(separator: Separator, power: int) -> int:
    """An exact cyclic projection order; two powers use anisotropic squares."""
    if power < 1:
        raise ValueError("power must be positive")
    bound = separator.max_mismatch
    if bound == 0:
        return 1
    if power <= 2:
        order = bound + 1
        while not (
            is_prime(order)
            and gcd(order, separator.slope) == 1
            and (power == 1 or order % 4 == 3)
        ):
            order += 1
        return order
    order = power * bound * bound + 1
    while gcd(order, separator.slope) != 1:
        order += 1
    return order


def power_exponents(bound: int, power: int) -> set[int]:
    """Effective exponents of a tensor power, after dividing by slope."""
    if bound < 0 or power < 1:
        raise ValueError("bound must be nonnegative and power positive")
    exponents = {0}
    squares = {d * d for d in range(bound + 1)}
    for _ in range(power):
        exponents = {a + b for a in exponents for b in squares}
    return exponents


def sparse_interpolation_weights(exponents: set[int]) -> list[Fraction]:
    """Weights at epsilon=2**j that extract the constant coefficient.

    The polynomial Q(z) = product_{s>0}(z-2**s)/(1-2**s) has
    Q(1)=1 and Q(2**s)=0. Its coefficients are the desired weights.
    Intended for small exact verification, not large stable computation.
    """
    if 0 not in exponents or min(exponents) < 0:
        raise ValueError("exponents must contain zero and be nonnegative")
    coefficients = [Fraction(1)]
    for exponent in sorted(exponents - {0}):
        root = 2 ** exponent
        updated = [Fraction(0)] * (len(coefficients) + 1)
        for index, coefficient in enumerate(coefficients):
            updated[index] -= root * coefficient / (1 - root)
            updated[index + 1] += coefficient / (1 - root)
        coefficients = updated
    return coefficients


def prime_divisors(value: int) -> set[int]:
    factors = set()
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.add(value)
    return factors


def field_with_root(order: int) -> tuple[int, int]:
    """Return a small prime field and an element of exactly the given order."""
    if order == 1:
        return 2, 1
    prime = order + 1
    while not is_prime(prime):
        prime += order
    factors = prime_divisors(order)
    for candidate in range(2, prime):
        root = pow(candidate, (prime - 1) // order, prime)
        if all(pow(root, order // d, prime) != 1 for d in factors):
            return prime, root
    raise AssertionError("finite field has no root of the required order")


def cyclic_average(root: int, order: int, exponent: int, prime: int) -> int:
    return (
        sum(pow(root, (r * exponent) % order, prime) for r in range(order))
        * pow(order, -1, prime)
    ) % prime


def verify(separator: Separator, power: int = 2) -> dict[str, int]:
    """Verify Fourier cancellation and constant extraction over an exact field.

    Internal tensor coefficients factor out. Checking these scalar multipliers
    therefore checks the universal identity for every tensor of the stated form.
    """
    order = projection_order(separator, power)
    combined_order = lcm(separator.copies, order)
    prime, root = field_with_root(combined_order)
    first_root = pow(root, combined_order // separator.copies, prime)
    second_root = pow(root, combined_order // order, prime)
    phase_bound = separator.copies - 1
    for phase in range(-phase_bound, phase_bound + 1):
        assert cyclic_average(first_root, separator.copies, phase, prime) == (
            1 if phase == 0 else 0
        ), (separator, phase)

    supported = list(separator.terms())
    for h, g, u, v, phase, weight in supported:
        assert phase == 0, (separator, h, g, u, v, phase)
        assert weight == separator.slope * (g - h) ** 2
        assert (weight == 0) == (g == h and u == v)
    assert sum(weight == 0 for *_, weight in supported) == (
        separator.blocks * separator.auxiliary
    )
    exponents = power_exponents(separator.max_mismatch, power)
    for exponent in exponents:
        assert cyclic_average(
            second_root, order, separator.slope * exponent, prime
        ) == (1 if exponent == 0 else 0), (separator, power, exponent)

    return {
        "blocks": separator.blocks,
        "auxiliary": separator.auxiliary,
        "slope": separator.slope,
        "power": power,
        "source_copies_before_exactification": separator.copies,
        "maximum_mismatch": separator.max_mismatch,
        "projection_evaluations": order,
        "exact_source_copies": order * separator.copies ** power,
        "direct_source_copies": (separator.blocks * separator.auxiliary) ** power,
        "generic_interpolation_evaluations": power * separator.max_mismatch ** 2 + 1,
        "verification_prime": prime,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-blocks", type=int, default=8)
    args = parser.parse_args()
    if args.max_blocks < 1:
        parser.error("--max-blocks must be positive")
    verified = 0
    for blocks in range(1, args.max_blocks + 1):
        for auxiliary in range(1, args.max_blocks + 1):
            for slope in (1, 2, 3):
                for power in (1, 2, 3):
                    verify(Separator(blocks, auxiliary, slope), power)
                    verified += 1
    for bound in range(5):
        exponents = power_exponents(bound, 2)
        coefficients = sparse_interpolation_weights(exponents)
        for exponent in exponents:
            assert sum(
                coefficient * 2 ** (j * exponent)
                for j, coefficient in enumerate(coefficients)
            ) == (1 if exponent == 0 else 0)
    rows = [verify(Separator(m, m), 2) for m in (2, 4, 8, 16, 32)]
    print(json.dumps({"verified_configurations": verified, "two_power_costs": rows}, indent=2))


if __name__ == "__main__":
    main()
