from collections import Counter
from fractions import Fraction
from itertools import product

import pytest

from experiments.general_profile_extraction import (
    closed_integer_scale,
    determinant_terms,
    integer_scale,
    key,
    ledger,
    rational_dual,
    tripling_terms,
    verify_entropy_identity,
)


@pytest.mark.parametrize("index", range(2, 11))
def test_rational_dual_has_only_the_claimed_residual(index):
    concavity, tripling = rational_dual(index)
    coefficients = Counter()
    for item in concavity:
        assert item.weight > 0 and item.up > 0 and item.down > 0
        coefficients[key(item.row, item.column)] += item.weight
        coefficients[key(item.row, item.column + 1)] -= item.up
        coefficients[key(item.row, item.column - 1)] -= item.down
    for item in tripling:
        assert item.weight > 0
        coefficients[key(item.row, 4 * item.row - 1)] += item.weight
        coefficients[key(item.row, item.row)] -= item.weight
    assert {position: value for position, value in coefficients.items() if value} == {
        (index, index): Fraction(1), (1, 2): Fraction(-1)
    }
    assert integer_scale(index) == closed_integer_scale(index)


@pytest.mark.parametrize("index,scale,U,T,catalyst", [(2, 15, 230, 15, 230), (3, 84, 3316, 162, 3394), (4, 3465, 252362, 8877, 257774)])
def test_small_integer_ledgers_and_independent_entropy_identity(index, scale, U, T, catalyst):
    result = ledger(index)
    assert result["scale"] == scale
    assert result["concavity_factors"] == U
    assert result["tripling_factors"] == T
    assert sum(result["catalyst"].values()) == catalyst == U + T - scale
    assert verify_entropy_identity(index)


@pytest.mark.parametrize("a,b", [(3, 3), (3, 7), (4, 4), (4, 10)])
def test_general_determinant_map_and_equal_type_restriction(a, b):
    terms = determinant_terms(a, b)
    quotient = {(x, 0, y, 0, x + y): 1 for x in range(a) for y in range(b + 1)}
    kernel = {(x, 1, y, 1, x + y): 1 for x in range(a) for y in range(b - 1)}
    off_diagonal = {(x, 0, b, 1, b - 1 + x): 1 for x in range(a - 1)}
    assert terms == quotient | kernel | off_diagonal
    retained = 0
    for word in product(terms, repeat=2):
        if sum(term[1] for term in word) == sum(term[3] for term in word) == 1:
            retained += 1
            assert all(term[1] == term[3] for term in word)
    assert retained == 2 * a * (b + 1) * a * (b - 1)


@pytest.mark.parametrize("index", [3, 4, 7])
def test_general_tripling_sectors_are_three_permuted_convolutions(index):
    blocks = [set(), set(), set()]
    for first, second, output, y, z in tripling_terms(index):
        weight = int(y == 1) - int(z == 1)
        assert weight >= 0
        assert (weight == 0) == (y == z)
        if y == z == 0:
            blocks[0].add((first, second, output))
        elif y == z == 1:
            blocks[1].add((index - 1 - first, output - (2 * index - 1), second - index))
        elif y == z == 2:
            blocks[2].add((first, second - (3 * index - 1), output - (3 * index - 1)))
    expected = {(x, y, x + y) for x in range(index) for y in range(index)}
    assert all(block == expected for block in blocks)


def test_invalid_index_is_rejected():
    with pytest.raises(ValueError):
        rational_dual(1)
