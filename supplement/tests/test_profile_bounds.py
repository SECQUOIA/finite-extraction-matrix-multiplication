"""Independent exact and finite optimization checks of the profile formula."""

from fractions import Fraction

import pytest

from experiments.profile_bounds import (
    certificate_grid,
    exact_threshold,
    finite_exponent_envelope,
    growth_factors,
    numerical_exponent,
    profile,
    solve_finite_lp,
    verify_grid,
)


def test_extremal_profile_satisfies_every_axiom_exactly():
    result = verify_grid(32)
    assert result["status"] == "exact_checks_passed"
    assert result["concavity"] == 32 * 30
    assert result["tripling"] > 0


def test_diagonal_recursion_and_normalization_are_saturated():
    factors = growth_factors(12)
    assert profile(1, 7, factors) == 7
    assert profile(2, 2, factors) == Fraction(10, 3)
    assert profile(3, 3, factors) == Fraction(56, 9)
    for a in range(2, 13):
        assert (profile(a, a, factors) - profile(a - 1, a - 1, factors)
                == factors[a] + factors[a - 1])


@pytest.mark.parametrize("a,b", [(2, 2), (3, 3), (2, 10)])
def test_lp_recovers_proven_minimum(a, b):
    pytest.importorskip("scipy")
    result = solve_finite_lp(a, b)
    assert result["success"], result["message"]
    assert result["lp_minimum"] == pytest.approx(float(profile(a, b)), abs=1e-8)
    assert result["maximum_inequality_violation"] < 1e-8


def test_certificate_grid_includes_tripling_landmark():
    assert certificate_grid(2, 2) == 7
    assert certificate_grid(2, 10) == 22
    assert certificate_grid(10, 2) == 22


@pytest.mark.parametrize("a,b", [(0, 1), (1, 0), (-1, 3)])
def test_invalid_indices_are_rejected(a, b):
    with pytest.raises(ValueError, match="positive"):
        profile(a, b)


def test_small_dimension_thresholds_use_exact_rational_comparisons():
    assert exact_threshold(Fraction(5, 2), 10) == 10
    assert exact_threshold(Fraction(12, 5), 63) == 63


def test_gamma_envelope_contains_direct_product_evaluations():
    import math

    for a in (2, 10, 63, 256):
        lower, upper = finite_exponent_envelope(math.log(a))
        assert lower <= numerical_exponent(a) <= upper
    # No large gamma evaluation is needed even far beyond float dimensions.
    lower, upper = finite_exponent_envelope(1000.0)
    assert 2.25 < lower <= upper < 2.251
