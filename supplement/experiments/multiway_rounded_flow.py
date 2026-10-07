"""Conserved integer rounding of maximal-width rational profile flows.

Only counts are constructed. No entropy or finite rank-cost certificate is
computed here. Run: python -m experiments.multiway_rounded_flow
"""

from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import json

from experiments.cyclic_profile_extraction import signed_key
from experiments.multiway_profile_flows import occupation, transitions


@dataclass
class _Arc:
    destination: int
    reverse: int
    capacity: int


def round_circulation(edges: list[tuple[int, int, Fraction]]) -> list[int]:
    """Round nonnegative rational circulation edges within floor/ceiling.

    Parallel edges and opposing directions remain distinct. Self-loops
    are floored, since they have zero incidence at their vertex.
    """
    targets = []
    balance = Counter()
    for source, destination, value in edges:
        if not isinstance(value, (int, Fraction)):
            raise TypeError("circulation values must be integers or Fractions")
        value = Fraction(value)
        if value < 0:
            raise ValueError("circulation values must be nonnegative")
        targets.append(value)
        balance[source] += value
        balance[destination] -= value
    if any(balance.values()):
        raise ValueError("input edges must form an exact circulation")
    if not edges:
        return []
    vertices = {vertex: index for index, vertex in enumerate(sorted(balance))}
    supply, sink = len(vertices), len(vertices) + 1
    graph: list[list[_Arc]] = [[] for _ in range(len(vertices) + 2)]

    def add_arc(source, destination, capacity):
        forward = _Arc(destination, len(graph[destination]), capacity)
        backward = _Arc(source, len(graph[source]), 0)
        graph[source].append(forward)
        graph[destination].append(backward)
        return forward

    result = [value.numerator // value.denominator for value in targets]
    imbalance = Counter()
    fractional_arcs = []
    for index, ((source, destination, _), target, lower) in enumerate(zip(edges, targets, result)):
        source, destination = vertices[source], vertices[destination]
        imbalance[source] -= lower
        imbalance[destination] += lower
        if target != lower and source != destination:
            fractional_arcs.append((index, add_arc(source, destination, 1)))
    required = 0
    for vertex in range(len(vertices)):
        value = imbalance[vertex]
        if value > 0:
            add_arc(supply, vertex, value)
            required += value
        elif value < 0:
            add_arc(vertex, sink, -value)

    delivered = 0
    while delivered < required:
        previous = [None] * len(graph)
        previous[supply] = (-1, -1)
        queue = deque([supply])
        while queue and previous[sink] is None:
            source = queue.popleft()
            for arc_index, arc in enumerate(graph[source]):
                if arc.capacity and previous[arc.destination] is None:
                    previous[arc.destination] = source, arc_index
                    queue.append(arc.destination)
                    if arc.destination == sink:
                        break
        if previous[sink] is None:
            raise RuntimeError("the fractional residual circulation must be feasible")
        amount = required - delivered
        vertex = sink
        while vertex != supply:
            source, arc_index = previous[vertex]
            amount = min(amount, graph[source][arc_index].capacity)
            vertex = source
        vertex = sink
        while vertex != supply:
            source, arc_index = previous[vertex]
            arc = graph[source][arc_index]
            arc.capacity -= amount
            graph[vertex][arc.reverse].capacity += amount
            vertex = source
        delivered += amount
    for index, arc in fractional_arcs:
        result[index] += 1 - arc.capacity
    return result


@dataclass(frozen=True)
class MultiwayType:
    row: int
    column: int
    children: tuple[int, ...]  # Ascending columns: reverse for filtration j.
    counts: tuple[int, ...]
    target_counts: tuple[Fraction, ...]  # K times the harmonic edge flow.

    @property
    def weight(self) -> int:
        return sum(self.counts)

    @property
    def arity(self) -> int:
        return len(self.counts)

    @property
    def target_weight(self) -> Fraction:
        return sum(self.target_counts, Fraction())


@dataclass(frozen=True)
class RoundedRow:
    row: int
    scale: int
    entry_position: int
    actions: tuple[MultiwayType, ...]
    reset_count: int
    reset_target: Fraction


@lru_cache(maxsize=None)
def _occupation(row: int, entry_position: int):
    return tuple(occupation(row, entry_position))


def rounded_row(row: int, scale: int, entry_position: int = 1) -> RoundedRow:
    if not isinstance(row, int) or row < 2:
        raise ValueError("row must be an integer at least two")
    if not isinstance(scale, int) or scale < 1:
        raise ValueError("scale must be a positive integer")
    if entry_position not in (1, 2):
        raise ValueError("entry_position must be one or two")
    weights = _occupation(row, entry_position)
    terminal = 3 * row
    edges, actions = [], []
    for position, weight in enumerate(weights[:-1], 1):
        probabilities = transitions(row, position)
        targets = tuple(scale * weight * probability for probability in probabilities.values())
        start = len(edges)
        edges.extend((position, child, target) for child, target in zip(probabilities, targets))
        actions.append((position, tuple(probabilities), targets, start))
    reset_target = scale * weights[-1]
    edges.extend(((terminal, 1, reset_target), (0, entry_position, Fraction(scale))))
    counts = round_circulation(edges)
    assert counts[-1] == scale
    result = RoundedRow(
        row=row,
        scale=scale,
        entry_position=entry_position,
        actions=tuple(MultiwayType(
            row, row - 1 + position,
            tuple(row - 1 + child for child in children),
            tuple(counts[start:start + len(children)]), targets,
        ) for position, children, targets, start in actions),
        reset_count=counts[-2],
        reset_target=reset_target,
    )
    assert row_ledger(result) == {row - 1 + entry_position: scale, row - 1: -scale}
    return result


def row_ledger(row: RoundedRow):
    residual = Counter()
    for action in row.actions:
        residual[action.column] += action.weight
        for child, count in zip(action.children, action.counts):
            residual[child] -= count
    residual[4 * row.row - 1] += row.reset_count
    residual[row.row] -= row.reset_count
    return {column: count for column, count in residual.items() if count}


def rounded_profile(index: int, scale: int) -> tuple[RoundedRow, ...]:
    if not isinstance(index, int) or index < 2:
        raise ValueError("index must be an integer at least two")
    return tuple(rounded_row(row, scale, 1 if row == index else 2)
                 for row in range(2, index + 1))


def profile_ledger(rows: tuple[RoundedRow, ...]):
    """Return the alternating signed residual and actual catalyst counts."""
    index = rows[-1].row
    inputs, outputs = Counter(), Counter()
    for row in rows:
        sign = (-1) ** (index - row.row)
        for action in row.actions:
            inputs[signed_key(sign, row.row, action.column)] += action.weight
            for child, count in zip(action.children, action.counts):
                outputs[signed_key(sign, row.row, child)] += count
        inputs[signed_key(sign, row.row, 4 * row.row - 1)] += row.reset_count
        outputs[signed_key(sign, row.row, row.row)] += row.reset_count
    residual = {key: inputs[key] - outputs[key] for key in inputs.keys() | outputs.keys()
                if inputs[key] != outputs[key]}
    catalyst = {key: min(count, outputs[key]) for key, count in inputs.items()
                if min(count, outputs[key])}
    return residual, catalyst


def report(index: int, scale: int):
    rows = rounded_profile(index, scale)
    residual, catalyst = profile_ledger(rows)
    assert residual == {(1, index, index): scale, (1, 1, 2): -scale}
    errors = [abs(count - target) for row in rows for action in row.actions
              for count, target in zip(action.counts, action.target_counts)]
    errors.extend(abs(row.reset_count - row.reset_target) for row in rows)
    assert all(error < 1 for error in errors)
    U = sum(action.weight for row in rows for action in row.actions)
    T = sum(row.reset_count for row in rows)
    assert sum(catalyst.values()) == U + T - scale
    return {
        "index": index,
        "K": scale,
        "exact_signed_ledger_verified": True,
        "strict_edge_rounding_bound_verified": True,
        "maximum_absolute_edge_error": str(max(errors)),
        "split_factors": U,
        "tripling_factors": T,
        "catalyst_factors": sum(catalyst.values()),
        "catalyst": [[list(key), count] for key, count in sorted(catalyst.items())],
        "rows": [{
            "row": row.row,
            "entry_position": row.entry_position,
            "reset_count": row.reset_count,
            "reset_target": str(row.reset_target),
            "zero_weight_actions": sum(action.weight == 0 for action in row.actions),
            "active_actions": [{
                "column": action.column,
                "children_ascending": list(action.children),
                "counts_ascending": list(action.counts),
                "weight": action.weight,
                "arity": action.arity,
            } for action in row.actions if action.weight],
        } for row in rows],
    }


def main():
    print(json.dumps({
        "scope": "Exact integer counts and conserved ledgers; no entropy or finite rank-cost certificate.",
        "cases": [report(index, scale) for index in (2, 3, 4, 8, 12)
                  for scale in (1, index ** 3)],
    }, indent=2))


if __name__ == "__main__":
    main()
