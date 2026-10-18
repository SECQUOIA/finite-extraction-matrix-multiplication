"""Exact finite checks for the rational separator and exactification formulas.

Run from the repository root with:
    python experiments/rational_interpolation_audit.py

The accompanying proofs, rather than these examples, establish all sizes.
"""
from fractions import Fraction
from math import comb


def lagrange_coefficient(nodes, selected, degree):
    """Return one coefficient of the selected Lagrange basis polynomial."""
    coefficients = [1]
    denominator = 1
    for node in nodes:
        if node == selected:
            continue
        expanded = [0] * (len(coefficients) + 1)
        for power, coefficient in enumerate(coefficients):
            expanded[power] -= node * coefficient
            expanded[power + 1] += coefficient
        coefficients = expanded
        denominator *= selected - node
    return Fraction(coefficients[degree], denominator)


def bit_height(value):
    value = Fraction(value)
    return max(1, abs(value.numerator).bit_length(), value.denominator.bit_length())


def separator_weights(sectors):
    central = 2 * sectors - 2
    count = 2 * central + 1
    nodes = range(1, count + 1)
    return [Fraction(node**central) * lagrange_coefficient(nodes, node, central)
            for node in nodes]


def check_separator_moments(sectors):
    central = 2 * sectors - 2
    weights = separator_weights(sectors)
    count = len(weights)
    height_bound = 2 + 2 * count * (count + 1).bit_length()
    assert all(bit_height(weight) <= height_bound for weight in weights)
    moments = {}
    for exponent in range(-central, central + 1):
        moment = sum((weight * Fraction(node)**exponent
                      for node, weight in enumerate(weights, start=1)), Fraction())
        assert moment == int(exponent == 0), (sectors, exponent, moment)
        moments[exponent] = moment
    return moments


def check_separator_labels(sectors, moments):
    for sector in range(sectors):
        for tentative in range(sectors):
            for left in range(sectors):
                for right in range(sectors):
                    mismatch = tentative + left - sector - right
                    survives = moments[mismatch] == 1
                    assert survives == (mismatch == 0)
                    if survives:
                        parameter_exponent = tentative**2 + 2 * sector * (left - right) - sector**2
                        assert parameter_exponent == (tentative - sector)**2
                        assert 0 <= parameter_exponent <= (sectors - 1)**2
                        assert (parameter_exponent == 0) == (tentative == sector and left == right)


def check_exactification(count):
    for exponent in range(count):
        moment = sum((-1)**(node - 1) * comb(count, node) * node**exponent
                     for node in range(1, count + 1))
        assert moment == int(exponent == 0), (count, exponent, moment)


def check_convolution(rows, columns):
    """Check every coefficient of the integer-node convolution identity."""
    count = rows + columns - 1
    nodes = range(1, count + 1)
    interpolation = [[lagrange_coefficient(nodes, node, degree)
                      for degree in range(count)] for node in nodes]
    for left in range(rows):
        for right in range(columns):
            for degree in range(count):
                coefficient = sum((node**(left + right) * interpolation[node - 1][degree]
                                   for node in nodes), Fraction())
                assert coefficient == int(degree == left + right)


def check_pooled_counts(source_count, target_count, source_side, target_side, side):
    """Check exact count/depth inequalities, without logarithmic rounding."""
    r, m, a, b = source_count, target_count, source_side, target_side
    threshold = (a * b + b - a - 1) // (b - a) + 1
    rho, growth = Fraction(a, b), Fraction(r, m)
    count, current, depth = 1, side, 0
    while current > threshold:
        following = a * ((current + b - 1) // b)
        assert following < current
        count = r * ((count + m - 1) // m)
        current = following
        depth += 1
    assert rho**depth * side > rho
    assert count <= (1 + Fraction(r * m, r - m)) * growth**depth
    assert count * current**3 <= r * (1 + r * m) * threshold**3 * growth**depth
    return count * current**3


if __name__ == "__main__":
    for sectors in range(1, 10):
        moments = check_separator_moments(sectors)
        if sectors <= 6:
            check_separator_labels(sectors, moments)
    for count in range(1, 21):
        check_exactification(count)
    for rows in range(1, 5):
        for columns in range(1, 6):
            check_convolution(rows, columns)
    # Each parameter tuple admits the indicated number of Strassen block
    # products, with unused source products allowed. These check pooling,
    # partial batches, and padding; no new low-rank identity is asserted.
    for parameters in [(7, 1, 1, 2), (15, 2, 1, 2), (22, 3, 2, 4)]:
        for side in range(1, 201):
            check_pooled_counts(*parameters, side)
    print("Exact checks passed: separator M=1..9, labels M=1..6, exactification E=1..20, "
          "20 convolution identities, 600 pooled recurrences.")
