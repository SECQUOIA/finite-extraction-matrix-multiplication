"""Small exact checks for alternating threefold profile tensors."""

from collections import Counter
from itertools import product
from math import comb, prod
import json

from experiments.rounded_profile_flows import rounded_types


EVEN = ((0, 1, 2), (1, 2, 0), (2, 0, 1))
ODD = ((0, 2, 1), (1, 0, 2), (2, 1, 0))


def partial_tripling_type(count: int):
    if count < 0:
        raise ValueError("tripling count must be nonnegative")
    middle = (count + 1) // 3
    return middle, comb(count, middle) * 2 ** (count - middle)


def cyclic_support(rows: int, columns: int, sign: int):
    permutations = EVEN if sign == 1 else ODD
    terms = [(i, j, i + j) for i in range(rows) for j in range(columns)]
    return {
        tuple(tuple(word[factor][permutations[factor][leg]] for factor in range(3))
              for leg in range(3))
        for word in product(terms, repeat=3)
    }


def swap_factor_order(sign: int):
    source, target = (EVEN, ODD) if sign == 1 else (ODD, EVEN)
    swap = (1, 0, 2)
    return tuple(target.index(tuple(swap[p] for p in permutation)) for permutation in source)


def signed_key(sign: int, row: int, column: int):
    if row > column:
        row, column, sign = column, row, -sign
    if row == column or row == 1:
        sign = 1
    return sign, row, column


def signed_ledger(index: int, scale: int, alternating: bool = True):
    splits, triples = rounded_types(index, scale)
    inputs, outputs = Counter(), Counter()
    signs = {row: (-1) ** (index - row) if alternating else 1 for row in range(2, index + 1)}
    for item in splits:
        sign = signs[item.row]
        inputs[signed_key(sign, item.row, item.column)] += item.weight
        outputs[signed_key(sign, item.row, item.column + 1)] += item.up
        outputs[signed_key(sign, item.row, item.column - 1)] += item.down
    for row, count in triples:
        sign = signs[row]
        inputs[signed_key(sign, row, 4 * row - 1)] += count
        # Keep the middle sector's odd orientation explicit before canonicalizing.
        outputs[signed_key(sign, row, row)] += 2 * count // 3
        outputs[signed_key(-sign, row, row)] += count // 3
    residual = {position: inputs[position] - outputs[position]
                for position in inputs.keys() | outputs.keys()
                if inputs[position] != outputs[position]}
    catalyst = {position: min(count, outputs[position]) for position, count in inputs.items()
                if min(count, outputs[position])}
    return residual, catalyst


def finite_counts(index: int, scale: int, orientations: int, power: int):
    """Only tiny tests use this materialized scalar-count calculation."""
    assert orientations in (3, 6)
    splits, triples = rounded_types(index, scale)
    _, catalyst = signed_ledger(index, scale)
    sectors = [comb(item.weight, item.up) for item in splits]
    sectors += [comb(z, z // 3) * comb(2 * z // 3, z // 3) for _, z in triples]
    U = sum(item.weight for item in splits)
    multiplier = orientations // 3
    M = prod(sectors)
    S = prod((2 * count - 1) ** orientations for count in sectors)
    H = M ** orientations
    D = orientations * sum((count - 1) ** 2 for count in sectors)
    E = power * D + 1
    kappa = prod((row + column - 1) ** (orientations * count)
                 for (_, row, column), count in catalyst.items())
    return {
        "A": 2 ** (multiplier * U * power),
        "B": (2 ** scale * M) ** (multiplier * power),
        "r": kappa ** power * E * S ** power * (2 * index - 1) ** (orientations * scale * power),
        "m": H ** power,
        "E": E,
    }


def main():
    cases = []
    for index, scale in ((2, 1), (3, 1), (4, 1), (8, 1), (16, 1), (63, 1)):
        residual, catalyst = signed_ledger(index, scale)
        assert residual == {(1, index, index): scale, (1, 1, 2): -scale}
        splits, triples = rounded_types(index, scale)
        U, T = sum(x.weight for x in splits), sum(z for _, z in triples)
        assert sum(catalyst.values()) == U + T - scale
        cases.append({"index": index, "K": scale, "U": U, "T": T,
                      "catalyst_factors": sum(catalyst.values()), "signed_ledger_verified": True})
    counts3, counts6 = finite_counts(2, 1, 3, 2), finite_counts(2, 1, 6, 1)
    assert counts3 == counts6
    print(json.dumps({
        "signed_ledgers": cases,
        "cyclic_power2_equals_sixfold_power1_counts": True,
        "matching_small_count_bit_lengths": {name: value.bit_length() for name, value in counts3.items()},
        "partial_middle_types": [
            {"z": z, "middle_count": partial_tripling_type(z)[0],
             "sector_count": partial_tripling_type(z)[1]} for z in range(9)
        ],
        "scope": "Local exact permutation and ledger checks; no composed multiplication seed.",
    }, indent=2))


if __name__ == "__main__":
    main()
