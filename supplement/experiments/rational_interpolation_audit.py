"""Exact finite checks for the rational variant of Section 9.1 (Lemma 9.1).

Run from the repository root with:
    python experiments/rational_interpolation_audit.py

Lemma 9.1(b) is the polynomial separator of Lü (arXiv:2610.18914,
Proposition 2.1) with n = M, written in the coordinates of Proposition 4.6.
For random sector tensors the script checks, in exact rational arithmetic,
that its maps on 2M-1 source copies give a polynomial in t of degree at
most M-1 (and exactly M-1), that the coefficients are those computed in
the proof, that the constant term is the direct sum of the T_g B_X(M), and
that dropping any one copy breaks the identity. It also checks the
exactification weights of Lemma 9.1(c), the rank decompositions of
Lemma 9.1(a), and the pooled-recursion counts used in Theorem 9.2.

The accompanying proofs, rather than these examples, establish all sizes.
"""
from fractions import Fraction
from math import comb
import random


def lagrange_basis(nodes, selected):
    """Return the coefficients, lowest degree first, of the Lagrange basis
    polynomial of the given nodes that is one at the selected node."""
    coefficients = [Fraction(1)]
    for node in nodes:
        if node == selected:
            continue
        expanded = [Fraction(0)] * (len(coefficients) + 1)
        for power, coefficient in enumerate(coefficients):
            expanded[power] -= node * coefficient
            expanded[power + 1] += coefficient
        coefficients = [value / (selected - node) for value in expanded]
    return coefficients


def evaluate(coefficients, point):
    value = Fraction(0)
    for coefficient in reversed(coefficients):
        value = value * point + coefficient
    return value


def shifted(coefficients, center):
    """Return the coefficients of p(center + xi) for p given by its coefficients."""
    return [sum((comb(power, degree) * center**(power - degree) * coefficients[power]
                 for power in range(degree, len(coefficients))), Fraction())
            for degree in range(len(coefficients))]


def separator_maps(sectors):
    """Maps of Lemma 9.1(b) in source copy l = 1, ..., 2M-1, for M = sectors.

    first[l][g'] = varpi_{M,g'+1}(l), second[l][g][e] = (l-g-1)^e (with 0^0 = 1),
    third[l][g][e'] = [xi^e'] varpi_{2M-1,l}(g+1+xi); the parameter t enters as
    t^(-e) on the second leg and t^(e') on the third leg."""
    copies = 2 * sectors - 1
    small, large = range(1, sectors + 1), range(1, copies + 1)
    first = {node: [evaluate(lagrange_basis(small, label + 1), node)
                    for label in range(sectors)] for node in large}
    second = {node: [[(node - sector - 1)**index for index in range(sectors)]
                     for sector in range(sectors)] for node in large}
    third = {node: [shifted(lagrange_basis(large, node), sector + 1)[:sectors]
                    for sector in range(sectors)] for node in large}
    return first, second, third


def add_term(polynomial, key, exponent, value):
    if value:
        coefficients = polynomial.setdefault(key, {})
        coefficients[exponent] = coefficients.get(exponent, Fraction(0)) + value
        if not coefficients[exponent]:
            del coefficients[exponent]
            if not coefficients:
                del polynomial[key]


def random_sector_tensor(sectors, rng):
    """Sectors T_g sharing the first leg; the other dimensions depend on g."""
    shared = rng.randint(1, 3)
    tensor = []
    for _ in range(sectors):
        second, third = rng.randint(1, 3), rng.randint(1, 3)
        entries = {(alpha, beta, gamma): Fraction(rng.randint(-3, 3))
                   for alpha in range(shared) for beta in range(second)
                   for gamma in range(third)}
        entries = {index: value for index, value in entries.items() if value}
        if not entries:
            entries[(0, 0, 0)] = Fraction(1)
        tensor.append(entries)
    return tensor


def copy_image(tensor, maps, node):
    """Image of one source copy; keys (alpha, g', g, beta, e, gamma, e'),
    values {exponent of t: coefficient}."""
    first, second, third = maps
    sectors = len(tensor)
    image = {}
    for sector, entries in enumerate(tensor):
        for (alpha, beta, gamma), value in entries.items():
            for label in range(sectors):
                for left in range(sectors):
                    for right in range(sectors):
                        add_term(image, (alpha, label, sector, beta, left, gamma, right),
                                 right - left, value * first[node][label]
                                 * second[node][sector][left] * third[node][sector][right])
    return image


def add_images(images):
    total = {}
    for image in images:
        for key, coefficients in image.items():
            for exponent, value in coefficients.items():
                add_term(total, key, exponent, value)
    return total


def direct_sum(tensor):
    """The direct sum of the T_g B_X(M) on the target variables of Proposition 4.6."""
    sectors = len(tensor)
    target = {}
    for sector, entries in enumerate(tensor):
        for (alpha, beta, gamma), value in entries.items():
            for index in range(sectors):
                add_term(target, (alpha, sector, sector, beta, index, gamma, index), 0, value)
    return target


def closed_form(tensor):
    """The polynomial of the proof: coefficient [xi^(e'-e)] varpi_{M,g'+1}(g+1+xi)."""
    sectors = len(tensor)
    nodes = range(1, sectors + 1)
    shifts = [[shifted(lagrange_basis(nodes, label + 1), sector + 1)
               for sector in range(sectors)] for label in range(sectors)]
    polynomial = {}
    for sector, entries in enumerate(tensor):
        for (alpha, beta, gamma), value in entries.items():
            for label in range(sectors):
                for left in range(sectors):
                    for right in range(left, sectors):
                        add_term(polynomial, (alpha, label, sector, beta, left, gamma, right),
                                 right - left, value * shifts[label][sector][right - left])
    return polynomial


def is_separation(polynomial, tensor):
    """True if the polynomial has no negative exponents and constant term (+)_g T_g B_X(M)."""
    if any(exponent < 0 for coefficients in polynomial.values() for exponent in coefficients):
        return False
    constant = {key: {0: coefficients[0]} for key, coefficients in polynomial.items()
                if 0 in coefficients}
    return constant == direct_sum(tensor)


def exactify(polynomial, count):
    """Lemma 9.1(c) with k = 1: weights (-1)^(l-1) binom(count, l) at the nodes 1..count."""
    total = {}
    for node in range(1, count + 1):
        weight = (-1)**(node - 1) * comb(count, node)
        for key, coefficients in polynomial.items():
            add_term(total, key, 0, weight * sum((value * Fraction(node)**exponent
                                                  for exponent, value in coefficients.items()),
                                                 Fraction()))
    return total


def check_separator(sectors, rng, drop_copies):
    """Check Lemma 9.1(b) for one random sector tensor with M = sectors."""
    tensor = random_sector_tensor(sectors, rng)
    maps = separator_maps(sectors)
    images = {node: copy_image(tensor, maps, node) for node in range(1, 2 * sectors)}
    polynomial = add_images(images.values())
    exponents = [exponent for coefficients in polynomial.values() for exponent in coefficients]
    assert min(exponents) >= 0 and max(exponents) == sectors - 1, (sectors, exponents)
    assert polynomial == closed_form(tensor), sectors
    assert is_separation(polynomial, tensor), sectors
    for count in {sectors, (sectors - 1)**2 + 1}:
        assert exactify(polynomial, count) == direct_sum(tensor), (sectors, count)
    if drop_copies:
        for dropped in images:
            remaining = add_images(image for node, image in images.items() if node != dropped)
            assert not is_separation(remaining, tensor), (sectors, dropped)


def check_exactification(count):
    for exponent in range(count):
        moment = sum((-1)**(node - 1) * comb(count, node) * node**exponent
                     for node in range(1, count + 1))
        assert moment == int(exponent == 0), (count, exponent, moment)


def check_convolution(rows, columns):
    """Check every coefficient of the integer-node convolution identity."""
    count = rows + columns - 1
    nodes = range(1, count + 1)
    interpolation = [lagrange_basis(nodes, node) for node in nodes]
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
    rng = random.Random(20261018)
    separator_cases = 0
    for sectors in range(1, 7):
        for _ in range(3):
            check_separator(sectors, rng, drop_copies=sectors <= 5)
            separator_cases += 1
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
    print(f"Exact checks passed: Lemma 9.1(b) (polynomial separator) on {separator_cases} random "
          "sector tensors with M=1..6 (degree M-1, closed form, constant term, "
          "exactification with E=M and E=(M-1)^2+1; every single dropped copy fails "
          "for M=1..5), exactification E=1..20, 20 convolution identities, "
          "600 pooled recurrences.")
