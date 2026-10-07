from fractions import Fraction

import pytest

from experiments.finite_constructions import (
    Separator,
    cyclic_average,
    field_with_root,
    power_exponents,
    projection_order,
    sparse_interpolation_weights,
    verify,
)


@pytest.mark.parametrize("blocks,auxiliary,slope", [(1, 1, 1), (2, 3, 1), (5, 4, 2), (4, 8, 3)])
def test_exact_separator_coefficient_identity(blocks, auxiliary, slope):
    separator = Separator(blocks, auxiliary, slope)
    for power in (1, 2, 3):
        verify(separator, power)


def test_sparse_interpolation_extracts_arbitrary_constant_coefficient():
    exponents = {0, 1, 4, 9}
    weights = sparse_interpolation_weights(exponents)
    polynomial = {0: Fraction(5, 7), 1: Fraction(-3), 4: Fraction(11, 13), 9: Fraction(17)}
    result = sum(
        weight * sum(coefficient * 2 ** (j * exponent) for exponent, coefficient in polynomial.items())
        for j, weight in enumerate(weights)
    )
    assert result == polynomial[0]


def test_two_power_projection_uses_nonresidue_condition():
    separator = Separator(6, 6)
    assert projection_order(separator, 2) == 7
    assert all(exponent % 7 != 0 for exponent in power_exponents(5, 2) - {0})
    # Merely choosing a prime above the mismatch bound is insufficient for two powers.
    assert 25 in power_exponents(4, 2)
    prime, root = field_with_root(5)
    assert cyclic_average(root, 5, 3 * 3 + 4 * 4, prime) == 1


def test_one_shot_sparse_copy_bound_cannot_beat_direct_copying():
    for blocks in range(1, 10):
        for auxiliary in range(1, 10):
            for slope in range(1, 10):
                separator = Separator(blocks, auxiliary, slope)
                assert separator.copies * (separator.max_mismatch + 1) >= blocks * auxiliary


def test_two_power_construction_saves_copies_for_eight_blocks():
    costs = verify(Separator(8, 8), 2)
    assert costs["exact_source_copies"] == 2475
    assert costs["direct_source_copies"] == 4096
    assert costs["generic_interpolation_evaluations"] == 99
    assert costs["projection_evaluations"] == 11


def test_invalid_parameters_are_rejected():
    with pytest.raises(ValueError):
        Separator(0, 2)
    with pytest.raises(ValueError):
        projection_order(Separator(2, 2), 0)
    with pytest.raises(ValueError):
        sparse_interpolation_weights({1, 4})
