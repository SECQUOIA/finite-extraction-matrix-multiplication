from decimal import Decimal
from fractions import Fraction
from itertools import product

import pytest

from experiments.small_profile_extraction import (
    CATALYST,
    Interval,
    construction_costs,
    determinant_terms,
    entropy_identity,
    resource_ledger,
    tripling_terms,
)


def test_exact_dual_entropy_identity_and_resource_cancellation():
    assert entropy_identity() == Fraction(10, 3) ** 15
    for scale in (1, 3):
        ledger = resource_ledger(scale)
        for b in range(2, 8):
            expected = CATALYST[b] * scale
            assert ledger["inputs"][b] == expected + (15 * scale if b == 2 else 0)
            assert ledger["outputs"][b] == expected
        assert ledger["outputs"][1] == 15 * scale
        assert ledger["input_oriented_dot_exponent"] == 230 * scale


@pytest.mark.parametrize("b", range(2, 7))
def test_determinant_basis_change_has_the_claimed_blocks(b):
    terms = determinant_terms(b)
    quotient = {(x, 0, y, 0, x + y): 1 for x in (0, 1) for y in range(b + 1)}
    kernel = {(x, 1, y, 1, x + y): 1 for x in (0, 1) for y in range(b - 1)}
    assert terms == quotient | kernel | {(0, 0, b, 1, b - 1): 1}


def test_equal_kernel_frequencies_remove_every_determinant_error_term():
    kept = []
    for word in product(determinant_terms(2), repeat=3):
        if sum(term[1] for term in word) == sum(term[3] for term in word) == 1:
            kept.append(word)
            assert all(term[1] == term[3] for term in word)
    # Three words with one kernel sector; each has C(2,3)^2*C(2,1).
    assert len(kept) == 3 * 6 ** 2 * 2


def test_equal_tripling_frequencies_remove_every_error_term():
    terms = list(tripling_terms())
    for _, _, _, y, z in terms:
        weight = int(y == 1) - int(z == 1)
        assert weight >= 0
        assert (weight == 0) == (y == z)
    kept = []
    for word in product(terms, repeat=3):
        y_counts = tuple(sum(term[3] == h for term in word) for h in range(3))
        z_counts = tuple(sum(term[4] == h for term in word) for h in range(3))
        if y_counts == z_counts == (1, 1, 1):
            kept.append(word)
            assert all(term[3] == term[4] for term in word)
    assert len(kept) == 6 * 4 ** 3


def test_log_interval_encloses_exact_power_relations():
    ratio = Interval.log_integer(2 ** 137).divide_positive(Interval.log_integer(2))
    assert ratio.lower <= 137 <= ratio.upper
    zero = Interval.log_integer(17 ** 19) - Interval.log_integer(17).scale(19)
    assert zero.lower <= 0 <= zero.upper


def test_explicit_bound_is_below_2_79_but_requires_billions_of_digits():
    result = construction_costs(300, 125, 3750)
    interval = result["exponent_upper_expression_interval"]
    assert Decimal("2.78918") < Decimal(interval["lower"])
    assert Decimal(interval["upper"]) < Decimal("2.78919")
    assert result["certified_below_2_79"]
    assert result["padded_target_dimension_decimal_digits"] == 21_665_218_118
    assert result["recursive_input_dimension_decimal_digits"] > 19_000_000_000


def test_invalid_parameters_are_rejected():
    with pytest.raises(ValueError):
        construction_costs(0, 1, 1)
    with pytest.raises(ValueError):
        determinant_terms(1)
    with pytest.raises(ValueError):
        Interval.log_integer(0)
