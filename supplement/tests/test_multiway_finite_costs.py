from fractions import Fraction
from math import comb, factorial, prod

import pytest

from experiments.multiway_finite_costs import (
    count_bounds, multinomial_log_bounds, parameters, power_bounds, report,
    tripling_log_bounds, type_entropy,
)
from experiments.multiway_rounded_flow import rounded_profile
from experiments.rounded_profile_flows import log_integer
from experiments.small_profile_extraction import sum_intervals


def test_integer_family_handles_powers_of_two_and_between_them():
    assert parameters(2) == (8, 2)
    assert parameters(3) == (108, 6)
    assert parameters(4) == (256, 8)
    assert parameters(5) == (1125, 15)
    with pytest.raises(ValueError):
        parameters(1)


def test_entropy_handles_zero_weight_and_one_point_support_exactly():
    for counts in ((0, 0, 0), (0, 7, 0)):
        entropy = type_entropy(counts)
        assert entropy.lower == entropy.upper == 0
        assert multinomial_log_bounds(counts)[0].upper == 0
        assert multinomial_log_bounds(counts)[1].lower == 0
    with pytest.raises(ValueError):
        type_entropy((1, -1))


def test_tiny_materialized_counts_validate_all_log_bound_directions():
    # This tiny test materializes only counts <= 2; the evaluator uses no factorials.
    rows = rounded_profile(2, 1)
    counts = count_bounds(2, 1, 1, rows)
    sectors = [factorial(action.weight) // prod(factorial(n) for n in action.counts)
               for row in rows for action in row.actions if action.weight]
    sectors.extend(comb(row.reset_count, (row.reset_count + 1) // 3)
                   * 2 ** (row.reset_count - (row.reset_count + 1) // 3)
                   for row in rows if row.reset_count)
    assert sectors == [2, 1, 1, 2]
    # Two positive actions have three available children but one used child.
    # Their finite-type penalties must vanish; their auxiliary dimensions do not.
    assert counts["basic_type_loss"] == log_integer(3) + log_integer(2)
    assert counts["type_loss"].upper < counts["basic_type_loss"].lower
    assert counts["source_log"] == log_integer(2).scale(2) + log_integer(3).scale(2)
    exact_delta = log_integer(2) + sum_intervals(log_integer(n) for n in sectors) - counts["source_log"]
    assert counts["contraction_lower_expression"].upper <= exact_delta.lower
    power = power_bounds(2, 1, 1, 1, 2, counts)
    assert power["fully_charged_upper_expression_interval"] is None
    exact_copy = sum_intervals((log_integer(2 * n - 1) - log_integer(n)).scale(3) for n in sectors)
    exact_interpolation = log_integer(3 * sum((n - 1) ** 2 for n in sectors) + 1)
    assert Fraction(power["copy_ratio_upper_interval"]["lower"]) >= exact_copy.upper
    assert Fraction(power["log_interpolation_upper_interval"]["lower"]) >= exact_interpolation.upper


def test_fixed_power_tradeoff_retains_other_charges_and_increases_source_dimension():
    result = report(4)
    low, high, reused = result["powers"]
    assert low["k"] == 1 and high["k"] == 32
    assert low["main_rank_charge_interval"] == high["main_rank_charge_interval"]
    assert low["catalyst_charge_interval"] == high["catalyst_charge_interval"]
    assert low["contraction_lower_expression_interval"] == high["contraction_lower_expression_interval"]
    assert Fraction(high["interpolation_charge_upper_interval"]["upper"]) < Fraction(low["interpolation_charge_upper_interval"]["lower"])
    assert Fraction(high["fully_charged_upper_expression_interval"]["upper"]) < Fraction(low["fully_charged_upper_expression_interval"]["lower"])
    assert high["recursive_source_decimal_digits"] > 31 * low["recursive_source_decimal_digits"]
    assert reused["j"] == 128 * high["j"]
    assert reused["interpolation_charge_upper_interval"] == high["interpolation_charge_upper_interval"]
    assert Fraction(reused["catalyst_charge_interval"]["upper"]) < Fraction(high["catalyst_charge_interval"]["lower"]) / 127
    assert reused["recursive_source_decimal_digits"] > 127 * high["recursive_source_decimal_digits"]
    assert result["catalyst_factors"] == result["interior_factors_U"] + result["tripling_factors_T"] - result["K"]


def test_elementary_multinomial_bounds_enclose_tiny_exact_counts():
    for counts in ((0, 0), (0, 7, 0), (1, 1), (0, 2, 3), (4, 4, 4), (2, 4, 0)):
        exact = factorial(sum(counts)) // prod(factorial(n) for n in counts)
        logarithm = log_integer(exact)
        lower, upper = multinomial_log_bounds(counts)
        assert lower.lower <= logarithm.lower <= logarithm.upper <= upper.upper


def test_partial_tripling_bounds_keep_the_actual_rounded_middle_count():
    for count in range(13):
        middle = (count + 1) // 3
        exact = comb(count, middle) * 2 ** (count - middle)
        logarithm = log_integer(exact)
        lower, upper = tripling_log_bounds(count)
        assert lower.lower <= logarithm.lower <= logarithm.upper <= upper.upper
    lower, upper = tripling_log_bounds(1)
    assert lower == upper == log_integer(2)
