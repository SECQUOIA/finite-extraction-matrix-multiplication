"""Exact small checks for the higher determinant filtration and an index-2 chain.

Polynomials have fixed bidegree (d,h). Keys (v,t) record the exponents
of v and t, with u and s exponents recovered from the bidegree.
"""

from collections import Counter
from fractions import Fraction
from math import comb, factorial, prod
import json


def lift_index(d, h, index):
    if not 0 <= index <= d + h:
        raise ValueError("quotient monomial index out of range")
    v = min(index, d)
    return v, index - v


def basis_vector(d, h, order, index):
    """An integer lift of Delta^order times one quotient monomial."""
    if not 0 <= h <= d or not 0 <= order <= h:
        raise ValueError("need 0 <= order <= h <= d")
    v, t = lift_index(d - order, h - order, index)
    return {(v + q, t + order - q): (-1) ** q * comb(order, q)
            for q in range(order + 1)}


def divide_delta(poly, d, h):
    """Exact integer division by u*t-v*s; reject a nondivisible remainder."""
    if d < 1 or h < 1:
        raise ValueError("Delta division needs positive bidegrees")
    remainder = Counter(poly)
    quotient = Counter()
    for t in range(h, 0, -1):
        for v in range(d):
            value = remainder[v, t]
            if value:
                quotient[v, t - 1] += value
                remainder[v, t] -= value
                remainder[v + 1, t - 1] += value
    if any(remainder.values()):
        raise ValueError("polynomial is not divisible by Delta")
    return {position: value for position, value in quotient.items() if value}


def coordinates(poly, d, h):
    """Expand a polynomial in the integer filtration basis by exact division."""
    if not 0 <= h <= d:
        raise ValueError("need 0 <= h <= d")
    if any(not 0 <= v <= d or not 0 <= t <= h for v, t in poly):
        raise ValueError("polynomial coordinate outside its bidegree")
    current = dict(poly)
    result = {}
    for order in range(h + 1):
        diagonal = Counter()
        for (v, t), value in current.items():
            diagonal[v + t] += value
        remainder = Counter(current)
        for index, value in diagonal.items():
            if value:
                result[order, index] = value
                remainder[lift_index(d - order, h - order, index)] -= value
        remainder = {position: value for position, value in remainder.items() if value}
        if order < h:
            current = divide_delta(remainder, d - order, h - order)
        else:
            assert not remainder
    return result


def determinant_terms(first_length, second_length, h):
    """Return (first_index,in_order,in_index,out_order,out_index): coefficient."""
    if first_length < 1 or h < 0 or second_length < h + 1:
        raise ValueError("need r >= 1, h >= 0, b >= h+1")
    d = second_length - 1
    degree = first_length - 1
    result = {}
    for first in range(first_length):
        for order in range(h + 1):
            for index in range(d + h - 2 * order + 1):
                vector = basis_vector(d, h, order, index)
                product = {(v + first, t): value for (v, t), value in vector.items()}
                for (out_order, out_index), value in coordinates(product, d + degree, h).items():
                    result[first, order, index, out_order, out_index] = value
    return result


def verify_local(first_length, second_length, h):
    terms = determinant_terms(first_length, second_length, h)
    expected_diagonal = {
        (first, order, index, order, index + first): 1
        for first in range(first_length)
        for order in range(h + 1)
        for index in range(second_length + h - 2 * order)
    }
    diagonal = {key: value for key, value in terms.items() if key[1] == key[3]}
    assert diagonal == expected_diagonal
    assert all(key[3] >= key[1] for key in terms)
    return {
        "r": first_length, "b": second_length, "h": h,
        "input_dimension": second_length * (h + 1),
        "output_dimension": (first_length + second_length - 1) * (h + 1),
        "sector_input_lengths": [second_length + h - 2 * j for j in range(h + 1)],
        "diagonal_terms": len(diagonal), "off_diagonal_terms": len(terms) - len(diagonal),
        "maximum_order_increase": max(key[3] - key[1] for key in terms),
        "maximum_coefficient_magnitude": max(map(abs, terms.values())),
        "exact_diagonal_and_triangularity_verified": True,
    }


def index_two_chain():
    relations = [(2, 1, (1, 3), (9, 21)),
                 (3, 2, (1, 3, 5), (6, 14, 22)),
                 (5, 2, (3, 5, 7), (7, 11, 15))]
    source, target = Counter(), Counter()
    auxiliary = 1
    entropy_product = Fraction(2 ** 15 * 3 ** 15)
    sectors = []
    for parent, h, children, counts in relations:
        weight = sum(counts)
        assert children == tuple(range(parent - h, parent + h + 1, 2))
        parent_value = Fraction(4 * parent + 2, 3)
        for child, count in zip(children, counts):
            assert Fraction(count, weight) == Fraction(4 * child + 2, 3) / ((h + 1) * parent_value)
            target[child] += count
            entropy_product /= count ** count
        source[parent] += weight
        auxiliary *= (h + 1) ** weight
        entropy_product *= weight ** weight
        sectors.append(factorial(weight) // prod(factorial(count) for count in counts))
    source[7] += 15
    target[2] += 15
    residual = {b: source[b] - target[b] for b in source.keys() | target.keys()
                if source[b] != target[b]}
    assert residual == {2: 15, 1: -15}
    assert auxiliary == 2 ** 30 * 3 ** 75
    assert entropy_product / auxiliary == Fraction(10, 3) ** 15
    catalyst = {b: min(source[b], target[b]) for b in source if min(source[b], target[b])}
    assert catalyst == {2: 15, 3: 42, 5: 33, 7: 15}
    return {
        "K": 15, "concavity_factors": 105, "tripling_factors": 15,
        "residual": residual, "catalyst": catalyst,
        "three_cyclic_source_auxiliary_side_per_N": "2^30 * 3^75",
        "six_permutation_source_auxiliary_side_per_N": "2^60 * 3^150",
        "N1_concavity_sector_counts": sectors,
        "N1_middle_only_tripling_sector_count": comb(15, 5) * 2 ** 10,
        "N1_equal_three_frequency_tripling_sector_count": factorial(15) // factorial(5) ** 3,
        "entropy_identity_verified_exactly": True,
        "scope": "Local maps and integer ledger only; no complete recursive coefficient maps or benchmark.",
    }


if __name__ == "__main__":
    print(json.dumps({
        "local_maps": [verify_local(*case) for case in ((2, 3, 2), (3, 3, 2), (2, 4, 3))],
        "index_two_chain": index_two_chain(),
    }, indent=2))
