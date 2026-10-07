from fractions import Fraction

import pytest

from experiments.general_profile_extraction import rational_dual
from experiments.rounded_profile_flows import (
    entropy_gain, ledger, log_integer, normalized_loss_bound, report, rounded_types,
)
from experiments.small_profile_extraction import Interval


@pytest.mark.parametrize("index", [2, 3, 4, 8, 16, 63])
def test_rounding_preserves_exact_ledger_and_all_type_constraints(index):
    targets, target_triples = rational_dual(index)
    for scale in (1, 2, 3, index ** 2, index ** 3):
        splits, triples = rounded_types(index, scale)
        for item, target in zip(splits, targets):
            assert 0 <= item.up - scale * target.up < 4
            assert 0 <= item.down - scale * target.down < 1
            assert item.up > 0 and item.down > 0
            assert item.weight < 6 * scale + 5
        for (_, count), target in zip(triples, target_triples):
            assert count > 0 and count % 3 == 0
            assert 0 <= count - scale * target.weight < 3
            assert count < 2 * scale + 3
        residual, catalyst = ledger(index, scale)
        assert residual == {(index, index): scale, (1, 2): -scale}
        assert sum(catalyst.values()) == sum(x.weight for x in splits) + sum(z for _, z in triples) - scale


@pytest.mark.parametrize("index", [2, 3, 4, 8])
def test_entropy_gain_matches_independent_KL_formula(index):
    targets, _ = rational_dual(index)
    for scale in (1, index ** 3):
        splits, _ = rounded_types(index, scale)
        direct_loss = Interval.exact(0)
        for item, target in zip(splits, targets):
            q = target.up / target.weight
            for count, probability in ((item.up, q), (item.down, 1-q)):
                ratio = Fraction(count, item.weight) / probability
                log_ratio = Interval.log_integer(ratio.numerator) - Interval.log_integer(ratio.denominator)
                direct_loss = direct_loss + log_ratio.scale(count)
        from experiments.general_profile_extraction import profile_diagonal
        F = profile_diagonal(index)
        potential_loss = (Interval.log_integer(F.numerator) - Interval.log_integer(F.denominator)).scale(scale) - entropy_gain(index, scale)
        assert direct_loss.lower <= potential_loss.upper and potential_loss.lower <= direct_loss.upper
        assert direct_loss.lower >= 0
        assert direct_loss.upper <= scale * normalized_loss_bound(index, scale)


def test_small_exact_tangent_is_unchanged_when_no_rounding_is_needed():
    splits, triples = rounded_types(2, 15)
    assert [x.up for x in splits] == [35, 36, 33, 26, 15]
    assert [x.down for x in splits] == [15, 20, 21, 18, 11]
    assert triples == [(2, 15)]


def test_cost_bound_retains_positive_charges_and_large_dimensions():
    result = report(16)
    assert result["fully_charged_exponent_upper_expression_interval"] is not None
    assert result["recursive_source_dimension_decimal_digits"] > 1_000_000
    assert result["catalyst_Q_factors"] == result["concavity_factors_U"] + result["tripling_factors_T"] - result["K"]


def test_interpolation_amortization_improves_bound_but_increases_base_size():
    first, amortized = report(16), report(16, power=64)
    assert Fraction(amortized["fully_charged_exponent_upper_expression_interval"]["upper"]) < Fraction(first["fully_charged_exponent_upper_expression_interval"]["lower"])
    assert amortized["recursive_source_dimension_decimal_digits"] > first["recursive_source_dimension_decimal_digits"]
    with pytest.raises(ValueError):
        report(16, power=0)


def test_invalid_scale_is_rejected():
    with pytest.raises(ValueError):
        rounded_types(3, 0)


def test_dyadic_rounding_preserves_the_original_log_enclosure():
    for value in (1, 2, 19, 10**100 + 123):
        original, rounded = Interval.log_integer(value), log_integer(value)
        assert rounded.lower <= original.lower <= original.upper <= rounded.upper
        assert rounded.lower.denominator.bit_count() == 1
        assert rounded.upper.denominator.bit_count() == 1
