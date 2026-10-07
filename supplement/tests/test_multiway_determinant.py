from collections import Counter
from itertools import product

import pytest

from experiments.multiway_determinant import (
    basis_vector, coordinates, determinant_terms, divide_delta,
    index_two_chain, verify_local,
)


@pytest.mark.parametrize("d,h", [(2, 2), (3, 2), (3, 3)])
def test_integer_basis_reconstructs_every_original_monomial(d, h):
    for v in range(d + 1):
        for t in range(h + 1):
            monomial = {(v, t): 1}
            reconstructed = Counter()
            for (order, index), value in coordinates(monomial, d, h).items():
                for position, coefficient in basis_vector(d, h, order, index).items():
                    reconstructed[position] += value * coefficient
            assert {position: value for position, value in reconstructed.items() if value} == monomial


def test_h2_small_map_matches_independent_hand_expansion():
    expected = {(first, order, index, order, index + first): 1
                for first in range(2)
                for order, size in enumerate((5, 3, 1))
                for index in range(size)}
    expected.update({(0, 0, 3, 1, 2): 1,
                     (0, 0, 4, 1, 3): 1,
                     (0, 1, 2, 2, 1): 1})
    assert determinant_terms(2, 3, 2) == expected


def test_higher_first_degree_has_a_jump_of_two_with_binomial_coefficient():
    terms = determinant_terms(3, 3, 2)
    assert {key[3:]: value for key, value in terms.items() if key[:3] == (0, 0, 4)} == {
        (0, 4): 1, (1, 3): 2, (2, 2): 1,
    }
    assert verify_local(3, 3, 2)["maximum_order_increase"] == 2


def test_binary_boundary_matches_existing_independent_formula():
    from experiments.general_profile_extraction import determinant_terms as binary_terms
    assert determinant_terms(3, 4, 1) == binary_terms(3, 4)


def test_equal_total_order_projection_removes_all_off_diagonal_products():
    terms = determinant_terms(3, 3, 2)
    retained_words = set()
    # Retain frequency vector (1,0,1), whose total filtration order is two.
    for left, right in product(terms, repeat=2):
        input_orders = (left[1], right[1])
        if sorted(input_orders) != [0, 2]:
            continue
        output_orders = (left[3], right[3])
        if sum(output_orders) == 2:
            assert output_orders == input_orders
            retained_words.add(input_orders)
    assert retained_words == {(0, 2), (2, 0)}


def test_h3_and_trivial_auxiliary_boundaries():
    assert verify_local(2, 4, 3)["sector_input_lengths"] == [7, 5, 3, 1]
    assert verify_local(1, 3, 2)["off_diagonal_terms"] == 0
    assert verify_local(3, 2, 0)["sector_input_lengths"] == [2]


def test_nondivisible_polynomial_and_invalid_dimensions_are_rejected():
    with pytest.raises(ValueError, match="not divisible"):
        divide_delta({(0, 0): 1}, 2, 2)
    with pytest.raises(ValueError, match="b >= h"):
        determinant_terms(2, 2, 2)
    with pytest.raises(ValueError, match="outside"):
        coordinates({(3, 0): 1}, 2, 2)


def test_new_index_two_chain_has_exact_counts_and_entropy_identity():
    result = index_two_chain()
    assert result["residual"] == {2: 15, 1: -15}
    assert result["catalyst"] == {2: 15, 3: 42, 5: 33, 7: 15}
    assert result["N1_middle_only_tripling_sector_count"] > result["N1_equal_three_frequency_tripling_sector_count"]
