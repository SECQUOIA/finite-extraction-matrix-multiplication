"""Small rational occupation flows for maximal-width profile relations.

Run: python -m experiments.multiway_profile_flows
This is a count/entropy experiment, not an executable tensor rank certificate.
"""

from collections import Counter
from fractions import Fraction
from math import log, sqrt
import json

from experiments.cyclic_profile_extraction import signed_key
from experiments.general_profile_extraction import rational_dual


def transitions(row: int, position: int, multiway: bool = True):
    """Position is column minus row plus one; zero absorbs, 3*row resets."""
    terminal = 3 * row
    if row < 2 or not 1 <= position < terminal:
        raise ValueError("row >= 2 and an interior position are required")
    width = min(position, terminal - position) if multiway else 1
    offset = Fraction(3 * (row - 1), 2)
    return {
        child: (offset + child) / ((width + 1) * (offset + position))
        for child in range(position - width, position + width + 1, 2)
    }


def occupation(row: int, entry: int, multiway: bool = True):
    """Solve (I-P^T)lambda=e_entry over Q, including the terminal reset."""
    if entry not in (1, 2):
        raise ValueError("entry must be 1 (top row) or 2 (lower row)")
    terminal = 3 * row
    matrix = [
        [Fraction(i == j) for j in range(1, terminal + 1)] + [Fraction(i == entry)]
        for i in range(1, terminal + 1)
    ]
    for position in range(1, terminal):
        probabilities = transitions(row, position, multiway)
        assert sum(probabilities.values()) == 1
        for child, probability in probabilities.items():
            if child:
                matrix[child - 1][position - 1] -= probability
    matrix[0][terminal - 1] -= 1  # terminal resets to position one
    for column in range(terminal):
        pivot = next(i for i in range(column, terminal) if matrix[i][column])
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        denominator = matrix[column][column]
        matrix[column] = [value / denominator for value in matrix[column]]
        for i in range(terminal):
            if i != column and matrix[i][column]:
                factor = matrix[i][column]
                matrix[i] = [a - factor * b for a, b in zip(matrix[i], matrix[column])]
    weights = [line[-1] for line in matrix]
    assert all(weight >= 0 for weight in weights)
    return weights


def row_residual(row: int, weights, multiway: bool = True):
    terminal = 3 * row
    residual = Counter()
    for position, weight in enumerate(weights[:-1], 1):
        residual[position] += weight
        for child, probability in transitions(row, position, multiway).items():
            residual[child] -= weight * probability
    residual[terminal] += weights[-1]
    residual[1] -= weights[-1]
    return {position: value for position, value in residual.items() if value}


def row_report(row: int, entry: int):
    weights = occupation(row, entry)
    binary = occupation(row, entry, multiway=False)
    assert row_residual(row, weights) == {entry: 1, 0: -1}
    assert row_residual(row, binary, multiway=False) == {entry: 1, 0: -1}
    old_splits, old_triples = rational_dual(row + (entry == 2))
    assert binary[:-1] == [item.weight for item in old_splits if item.row == row]
    assert weights[-1] == binary[-1] == next(item.weight for item in old_triples if item.row == row)
    charge, entropy, type_coordinates, active = 0.0, 0.0, 0, 0
    for position, weight in enumerate(weights[:-1], 1):
        if not weight:
            continue
        probabilities = transitions(row, position)
        active += 1
        type_coordinates += len(probabilities)
        charge += float(weight) * log(len(probabilities))
        entropy -= float(weight) * sum(float(q) * log(float(q)) for q in probabilities.values())
    offset = Fraction(3 * (row - 1), 2)
    gap = log(float((offset + entry) / offset))
    assert abs(entropy - charge + float(weights[-1]) * log(3) - gap) < 1e-11
    c = 1 - 2 * sqrt(2) / 3
    bound = 6 / c if entry == 1 else 3 * (sqrt(2) + 2) / c
    assert charge <= bound
    return {
        "row": row,
        "entry_position": entry,
        "occupation_weights_including_terminal": [str(value) for value in weights],
        "terminal_occupation": str(weights[-1]),
        "split_occupation": str(sum(weights[:-1])),
        "active_split_relations": active,
        "active_type_coordinates": type_coordinates,
        "multiway_auxiliary_log_charge": charge,
        "binary_auxiliary_log_charge": float(sum(binary[:-1])) * log(2),
        "exact_row_ledger_verified": True,
        "exact_binary_and_terminal_comparison_verified": True,
        "entropy_identity_numerical_residual": entropy - charge + float(weights[-1]) * log(3) - gap,
    }


def main():
    cases = [row_report(row, entry) for row in range(2, 13) for entry in (1, 2)]
    ledgers = []
    for index in range(2, 13):
        residual = Counter()
        selected = [case for case in cases
                    if case["row"] <= index
                    and case["entry_position"] == (1 if case["row"] == index else 2)]
        for case in selected:
            row = case["row"]
            sign = (-1) ** (index - row)
            weights = list(map(Fraction, case["occupation_weights_including_terminal"]))
            for position, value in row_residual(row, weights).items():
                residual[signed_key(sign, row, row - 1 + position)] += value
        residual = {key: value for key, value in residual.items() if value}
        assert residual == {(1, index, index): 1, (1, 1, 2): -1}
        ledgers.append({
            "index": index,
            "exact_alternating_signed_ledger_verified": True,
            "multiway_auxiliary_log_charge": sum(case["multiway_auxiliary_log_charge"] for case in selected),
            "binary_auxiliary_log_charge": sum(case["binary_auxiliary_log_charge"] for case in selected),
            "active_split_relations": sum(case["active_split_relations"] for case in selected),
            "active_type_coordinates": sum(case["active_type_coordinates"] for case in selected),
        })
    print(json.dumps({
        "scope": "Exact rational ledgers, with diagnostic floating-point logarithms; no integer rounding or finite rank certificate.",
        "cases": cases,
        "global_ledgers": ledgers,
    }, indent=2))


if __name__ == "__main__":
    main()
