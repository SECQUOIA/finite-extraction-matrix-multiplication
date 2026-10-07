from collections import Counter
from fractions import Fraction

import pytest

from experiments.multiway_rounded_flow import (
    profile_ledger, round_circulation, rounded_profile, rounded_row, row_ledger,
)


def assert_conserved_rounding(edges, counts):
    residual = Counter()
    assert len(counts) == len(edges)
    for (source, destination, target), count in zip(edges, counts):
        assert isinstance(count, int) and count >= 0
        assert abs(count - target) < 1
        if not target:
            assert count == 0
        residual[source] += count
        residual[destination] -= count
    assert not any(residual.values())


def test_integer_edges_and_disconnected_self_loops_remain_unchanged():
    edges = [(0, 1, 8), (1, 0, 8), (0, 0, 4), (8, 8, 0), (9, 9, 3)]
    assert round_circulation(edges) == [8, 8, 4, 0, 3]
    assert round_circulation([]) == []


def test_fractional_self_loops_are_floored_without_changing_incidence():
    edges = [(0, 0, Fraction(5, 3)), (0, 1, Fraction(7, 4)),
             (1, 0, Fraction(7, 4)), (1, 1, Fraction(1, 2))]
    counts = round_circulation(edges)
    assert counts[0] == 1 and counts[-1] == 0
    assert_conserved_rounding(edges, counts)


def test_fractional_cycle_with_opposed_fixed_edges_can_reroute():
    # A greedy matching 0->3, 1->5 leaves node 2 unmatched. A valid
    # rounding must be able to change an earlier choice using reverse arcs.
    half = Fraction(1, 2)
    edges = [(0, 3, half), (0, 4, half), (1, 5, half),
             (1, 4, half), (2, 3, half), (2, 5, half),
             (3, 0, 1), (4, 1, 1), (5, 2, 1)]
    counts = round_circulation(edges)
    assert_conserved_rounding(edges, counts)
    assert counts[-3:] == [1, 1, 1]
    assert sum(counts[:2]) == sum(counts[2:4]) == sum(counts[4:6]) == 1


def test_parallel_directed_edges_keep_their_own_rounding_bounds():
    edges = [(0, 1, Fraction(1, 5)), (0, 1, Fraction(4, 5)),
             (1, 0, Fraction(3, 7)), (1, 0, Fraction(4, 7)),
             (1, 1, Fraction(7, 3)), (2, 0, 0)]
    assert_conserved_rounding(edges, round_circulation(edges))


@pytest.mark.parametrize("edges,exception", [
    ([(0, 1, Fraction(1, 2))], ValueError),
    ([(0, 0, Fraction(-1, 2))], ValueError),
    ([(0, 0, 0.5)], TypeError),
])
def test_invalid_circulations_are_rejected(edges, exception):
    with pytest.raises(exception):
        round_circulation(edges)


@pytest.mark.parametrize("index", [2, 3, 4, 8, 12])
def test_rounded_profiles_preserve_all_resource_and_edge_contracts(index):
    for scale in (1, 2, 7, 100):
        rows = rounded_profile(index, scale)
        for row in rows:
            expected_entry = row.row if row.row == index else row.row + 1
            assert row_ledger(row) == {expected_entry: scale, row.row - 1: -scale}
            assert abs(row.reset_count - row.reset_target) < 1
            for action in row.actions:
                assert action.children == tuple(sorted(action.children))
                assert action.arity == min(action.column - row.row + 1,
                                           4 * row.row - 1 - action.column) + 1
                assert all(isinstance(count, int) and count >= 0 for count in action.counts)
                assert action.weight == sum(action.counts)
                for count, target in zip(action.counts, action.target_counts):
                    assert abs(count - target) < 1
                    if target == 0:
                        assert count == 0
        residual, catalyst = profile_ledger(rows)
        assert residual == {(1, index, index): scale, (1, 1, 2): -scale}
        uses = sum(action.weight for row in rows for action in row.actions)
        resets = sum(row.reset_count for row in rows)
        assert sum(catalyst.values()) == uses + resets - scale
        assert all(count > 0 for count in catalyst.values())


def test_small_scale_allows_zero_actions_and_non_tripled_reset_counts():
    rows = rounded_profile(12, 1)
    assert any(action.weight == 0 for row in rows for action in row.actions)
    assert any(row.reset_count % 3 for row in rows)
    assert any(row.reset_count == 0 for row in rows)
    assert any(any(target == 0 for target in action.target_counts)
               for row in rows for action in row.actions)


def test_large_integer_scale_remains_exact():
    scale = 10**50 + 3
    row = rounded_row(2, scale)
    assert row_ledger(row) == {2: scale, 1: -scale}
    assert all(abs(count - target) < 1 for action in row.actions
               for count, target in zip(action.counts, action.target_counts))


@pytest.mark.parametrize("arguments", [(1, 1), (2, 0), (2, 1.5), (2, 1, 3)])
def test_invalid_row_parameters_are_rejected(arguments):
    with pytest.raises(ValueError):
        rounded_row(*arguments)
