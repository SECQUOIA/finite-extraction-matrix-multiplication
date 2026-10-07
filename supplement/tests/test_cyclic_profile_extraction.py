from collections import Counter
from itertools import product
from math import comb

import pytest

from experiments.cyclic_profile_extraction import (
    cyclic_support, finite_counts, partial_tripling_type, signed_ledger, swap_factor_order,
)
from experiments.general_profile_extraction import tripling_terms
from experiments.rounded_profile_flows import rounded_types


@pytest.mark.parametrize("rows,columns", [(1, 2), (2, 3), (3, 4), (3, 3)])
@pytest.mark.parametrize("sign", [1, -1])
def test_transposing_convolution_inputs_flips_cyclic_sign(rows, columns, sign):
    factor_order = swap_factor_order(sign)
    opposite = cyclic_support(columns, rows, -sign)
    reordered = {tuple(tuple(leg[factor] for factor in factor_order) for leg in term)
                 for term in opposite}
    assert reordered == cyclic_support(rows, columns, sign)


@pytest.mark.parametrize("size", [2, 3])
def test_each_boundary_orientation_is_exactly_square_multiplication(size):
    for sign in (1, -1):
        support = cyclic_support(1, size, sign)
        positions = ((2, 1), (1, 0), (2, 0)) if sign == 1 else ((1, 2), (2, 0), (1, 0))
        mapped = {tuple(tuple(leg[position] for position in pair)
                        for leg, pair in zip(term, positions)) for term in support}
        assert mapped == {((i, j), (j, k), (i, k)) for i in range(size)
                          for j in range(size) for k in range(size)}


@pytest.mark.parametrize("index", [2, 3, 4, 8, 16, 63])
def test_alternating_signs_preserve_catalyst_and_exact_residual(index):
    for scale in (1, index ** 3):
        residual, catalyst = signed_ledger(index, scale)
        assert residual == {(1, index, index): scale, (1, 1, 2): -scale}
        splits, triples = rounded_types(index, scale)
        assert sum(catalyst.values()) == sum(x.weight for x in splits) + sum(z for _, z in triples) - scale


def test_constant_row_sign_does_not_telescope():
    residual, _ = signed_ledger(3, 1, alternating=False)
    assert residual == {(1, 3, 3): 1, (1, 1, 2): -1, (1, 2, 3): 1, (-1, 2, 3): -1}


def test_even_cyclic_power_has_exactly_the_old_sixfold_scalar_counts():
    assert finite_counts(2, 1, 3, 2) == finite_counts(2, 1, 6, 1)
    assert finite_counts(3, 1, 3, 2) == finite_counts(3, 1, 6, 1)


@pytest.mark.parametrize("row,count,middle", [(2, 1, 0), (2, 2, 1), (2, 3, 1), (3, 2, 1), (4, 2, 0), (4, 2, 2)])
def test_only_fixing_middle_count_removes_all_off_diagonal_terms(row, count, middle):
    sectors = Counter()
    for word in product(list(tripling_terms(row)), repeat=count):
        if sum(term[3] == 1 for term in word) != middle or sum(term[4] == 1 for term in word) != middle:
            continue
        assert all(term[3] == term[4] for term in word)
        sectors[tuple(term[3] for term in word)] += 1
    assert len(sectors) == comb(count, middle) * 2 ** (count - middle)
    assert set(sectors.values()) == {row ** (2 * count)}


def test_middle_type_mode_and_one_logarithmic_finite_type_penalty():
    for count in range(65):
        middle, sectors = partial_tripling_type(count)
        assert sectors == max(comb(count, m) * 2 ** (count - m) for m in range(count + 1))
        assert sectors * (count + 1) >= 3 ** count
