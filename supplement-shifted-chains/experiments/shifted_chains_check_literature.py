"""Exact checks behind docs/shifted-chains-check-literature.md.

The literature note identifies parts of the shifted-chain construction with
published maps.  This script checks those identifications on small cases
with exact integer and Fraction arithmetic:

1. kernel: for 1 <= h < b and d >= 2 the shifted map
   Q(F_0, ..., F_{d-1}) = sum_j z^(j h) F_j is onto polynomials of length
   B = b + (d-1) h, and its kernel has the basis of adjacent pairs
   (-z^h K, K) with deg K < c = b - h;
2. blocks: in the lift/kernel bases, multiplication by each x_alpha is
   block lower triangular with diagonal blocks C(r, B) and d-1 copies of
   C(r, c); the change of basis is unimodular;
3. forms: the adjacent pairs are Delta_h * (monomial (x) monomial) with
   Delta_h = u^h v' - v^h u'; for h = 1 the kernel is the first step
   F^1 = Delta (V_{b-1} (x) V'_{d-1}) of the determinant (Clebsch-Gordan)
   filtration (OpenAI Lemma 4.1 for d = 2, Maakestad Lemma 2.5, v5 4.1);
4. overlap-add: for h = b the map is bijective on inputs, so
   C(r, d b) is a restriction of C(r, b) (x) B_X(d);
5. reset: the three-block reset of C(r, 3c + r - 1) is OpenAI Lemma 4.2
   ("shifted tripling") with (a, h) = (r, c);
6. concavity: d P(b) >= P(B) + (d - 1) P(c) for every discretely concave
   integer sequence (exhaustive on a small grid);
7. ramp product: prod_{j<R} (3j+1)(3j+2)/((3j-1)(3j)) equals v5's
   F(R, R) = s_R (3R - 1)/2, and F(R, R)^3 >= R^4 (OpenAI Lemma 5.1).

Run from the repository root:  python -I -m experiments.shifted_chains_check_literature
"""

from __future__ import annotations

import itertools
from fractions import Fraction


# ---------------------------------------------------------------- linear algebra


def rank(rows: list[list[Fraction]]) -> int:
    """Rank of a rational matrix by exact Gaussian elimination."""
    m = [list(map(Fraction, r)) for r in rows]
    rk, ncols = 0, (len(m[0]) if m else 0)
    for col in range(ncols):
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
    return rk


def det_int(mat: list[list[int]]) -> int:
    """Exact integer determinant (Bareiss)."""
    a = [row[:] for row in mat]
    n, sign, prev = len(a), 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            swap = next((i for i in range(k + 1, n) if a[i][k] != 0), None)
            if swap is None:
                return 0
            a[k], a[swap] = a[swap], a[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
        prev = a[k][k]
    return sign * a[n - 1][n - 1]


def solve(basis_cols: list[list[int]], v: list[int]) -> list[Fraction]:
    """Coordinates of v in a basis given by columns (square, invertible)."""
    n = len(v)
    aug = [[Fraction(basis_cols[j][i]) for j in range(n)] + [Fraction(v[i])] for i in range(n)]
    for col in range(n):
        piv = next(i for i in range(col, n) if aug[i][col] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        p = aug[col][col]
        aug[col] = [a / p for a in aug[col]]
        for i in range(n):
            if i != col and aug[i][col] != 0:
                f = aug[i][col]
                aug[i] = [a - f * b for a, b in zip(aug[i], aug[col])]
    return [aug[i][n] for i in range(n)]


# ------------------------------------------------------------ shifted chain map


def shifted_bases(length: int, d: int, h: int) -> tuple[list[list[int]], int, int]:
    """Lift + adjacent-pair kernel basis of K^{d*length} for the shifted map.

    Component j, position beta has flat index j*length + beta.  The lift of
    exponent i uses the first component containing it (the round-8 choice).
    Returns (columns, image length, kernel block length).
    """
    big, c = length + (d - 1) * h, length - h
    cols: list[list[int]] = []
    for i in range(big):
        j = next(j for j in range(d) if j * h <= i < j * h + length)
        e = [0] * (d * length)
        e[j * length + i - j * h] = 1
        cols.append(e)
    for j in range(d - 1):
        for k in range(c):
            e = [0] * (d * length)
            e[j * length + h + k] = -1  # -z^h K in component j
            e[(j + 1) * length + k] = 1  # K in component j + 1
            cols.append(e)
    return cols, big, c


def shifted_map(vec: list[int], length: int, d: int, h: int) -> list[int]:
    out = [0] * (length + (d - 1) * h)
    for j in range(d):
        for beta in range(length):
            out[j * h + beta] += vec[j * length + beta]
    return out


def check_shifted_chain(r: int, b: int, d: int, h: int) -> int:
    """Check items 1-3; return the number of nonzero off-diagonal entries."""
    off_diagonal = 0
    ycols, big, c = shifted_bases(b, d, h)
    zlen = b + r - 1
    zcols, big_out, c_out = shifted_bases(zlen, d, h)
    assert big == b + (d - 1) * h and c == b - h and big_out == big + r - 1 and c_out == c + r - 1
    # 1. kernel: lifts map to the standard basis, adjacent pairs to zero, and
    #    the d*b vectors form a unimodular basis.
    for i, col in enumerate(ycols[:big]):
        img = shifted_map(col, b, d, h)
        assert img == [int(t == i) for t in range(big)]
    for col in ycols[big:]:
        assert not any(shifted_map(col, b, d, h))
    ymat = [[ycols[j][i] for j in range(d * b)] for i in range(d * b)]
    assert abs(det_int(ymat)) == 1, "change of basis is not unimodular"
    # 2. blocks of multiplication by x_alpha in the adapted bases.
    for alpha in range(r):
        def mult(col: list[int]) -> list[int]:
            out = [0] * (d * zlen)
            for j in range(d):
                for beta in range(b):
                    out[j * zlen + beta + alpha] += col[j * b + beta]
            return out
        for i, col in enumerate(ycols):
            coords = solve(zcols, mult(col))
            quot, ker = coords[:big_out], coords[big_out:]
            if i < big:  # quotient input: quotient block is C(r, B)
                assert quot == [Fraction(int(t == i + alpha)) for t in range(big_out)]
                off_diagonal += sum(1 for t in ker if t != 0)
            else:  # kernel input: no quotient part; diagonal C(r, c) per pair
                j, k = divmod(i - big, c)
                assert not any(quot)
                assert ker == [Fraction(int(t == j * c_out + k + alpha)) for t in range(len(ker))]
    # 3. forms: adjacent pair (j, k) equals Delta_h * (u^(c-1-k) v^k (x) u'^(d-2-j) v'^j)
    #    after reading component q from the exponent q of v' and the position
    #    from the exponent of v (dehomogenize u = 1, v = z).
    for j in range(d - 1):
        for k in range(c):
            vec = [0] * (d * b)
            # u^h v' * g * m'  ->  v-exponent k, v'-exponent j+1, coefficient +1
            vec[(j + 1) * b + k] += 1
            # -v^h u' * g * m' ->  v-exponent k+h, v'-exponent j, coefficient -1
            vec[j * b + k + h] -= 1
            assert vec == ycols[big + j * c + k]
    return off_diagonal


def check_h1_is_first_filtration_step(b: int, d: int) -> None:
    """For h = 1 the kernel equals Delta*(V_{b-1} (x) V'_{d-1}), v5's F^1."""
    ycols, big, c = shifted_bases(b, d, 1)
    kernel = ycols[big:]
    f1 = []
    for p in range(b - 1):  # basis monomials of V_{b-1} (x) V'_{d-1}
        for q in range(d - 1):
            vec = [0] * (d * b)
            vec[(q + 1) * b + p] += 1  # u v' * v^p v'^q
            vec[q * b + p + 1] -= 1  # -v u' * v^p v'^q
            f1.append(vec)
    assert rank(kernel) == rank(f1) == rank(kernel + f1) == (d - 1) * (b - 1)


def check_overlap_add(r: int, b: int, d: int) -> None:
    """h = b: Q is bijective on inputs, so C(r, d b) <= C(r, b) (x) B_X(d)."""
    zlen = b + r - 1
    for alpha in range(r):
        for beta in range(d * b):
            j, local = divmod(beta, b)
            out = [0] * (d * zlen)
            out[j * zlen + local + alpha] = 1
            img = shifted_map(out, zlen, d, b)
            assert img == [int(t == beta + alpha) for t in range(d * b + r - 1)]


# ------------------------------------------------------------ OpenAI Lemma 4.2


def check_shifted_tripling(a: int, h: int) -> None:
    """OpenAI Lemma 4.2 with (a, h) = (r, c): the shifted-chain reset."""
    big = 3 * h + a - 1
    ylab = lambda y: 0 if y <= h - 1 else (1 if y <= 2 * h + a - 2 else 2)
    zlab = lambda z: 0 if z <= h + a - 2 else (1 if z <= 2 * h + a - 2 else 2)
    sectors: dict[int, set] = {0: set(), 1: set(), 2: set()}
    for x in range(a):
        for y in range(big):
            z = x + y
            weight = int(ylab(y) == 1) - int(zlab(z) == 1)
            assert weight >= 0
            if weight == 0:
                assert ylab(y) == zlab(z)
                sectors[ylab(y)].add((x, y, z))
            else:
                assert ylab(y) == 1 and zlab(z) != 1  # only middle-to-outer terms drop
    conv = {(i, j, i + j) for i in range(a) for j in range(h)}
    assert {(x, y, z) for x, y, z in sectors[0]} == conv
    assert {(x, y - 2 * h - a + 1, z - 2 * h - a + 1) for x, y, z in sectors[2]} == conv
    # middle: x reversed, legs 2 and 3 exchanged
    mid = {(a - 1 - x, z - (h + a - 1), y - h) for x, y, z in sectors[1]}
    assert mid == conv


# ------------------------------------------------------------ scalar statements


def check_concavity_implication(max_len: int = 7, max_inc: int = 3) -> int:
    """d P(b) >= P(B) + (d-1) P(c) for all discretely concave sequences."""
    count = 0
    for incs in itertools.product(range(max_inc, -max_inc - 1, -1), repeat=max_len - 1):
        if any(incs[i] < incs[i + 1] for i in range(len(incs) - 1)):
            continue
        p = [0]
        for t in incs:
            p.append(p[-1] + t)
        for c in range(len(p)):
            for b in range(c + 1, len(p)):
                h = b - c
                for d in range(2, len(p)):
                    big = b + (d - 1) * h
                    if big >= len(p):
                        break
                    assert d * p[b] >= p[big] + (d - 1) * p[c]
                    count += 1
    return count


def check_ramp_product(max_r: int = 300) -> None:
    prod, s = Fraction(1), Fraction(1)
    for big_r in range(1, max_r + 1):
        if big_r > 1:
            j = big_r - 1
            prod *= Fraction((3 * j + 1) * (3 * j + 2), (3 * j - 1) * (3 * j))
            s *= 1 + Fraction(1, 3 * j)
        f_rr = s * Fraction(3 * big_r - 1, 2)
        assert prod == f_rr
        assert f_rr ** 3 >= big_r ** 4  # OpenAI Lemma 5.1 bound F(R,R) >= R^(4/3)


def main() -> None:
    cases = 0
    for r in range(1, 4):
        for b in range(2, 6):
            for d in range(2, 5):
                for h in range(1, b):
                    off = check_shifted_chain(r, b, d, h)
                    # The quotient-to-kernel block is the only off-diagonal
                    # block; it is zero for r = 1 and nonzero for r >= 2.
                    assert (off == 0) == (r == 1), (r, b, d, h, off)
                    cases += 1
    for b in range(2, 7):
        for d in range(2, 6):
            check_h1_is_first_filtration_step(b, d)
    for r in range(1, 4):
        for b in range(1, 5):
            for d in range(2, 5):
                check_overlap_add(r, b, d)
    for a in range(1, 6):
        for h in range(1, 6):
            check_shifted_tripling(a, h)
    concave = check_concavity_implication()
    check_ramp_product()
    print(f"shifted-chain block checks: {cases} cases (r<=3, b<=5, d<=4, all h<b)")
    print("h = 1 kernel equals the first determinant-filtration step: b<=6, d<=5")
    print("overlap-add endpoint h = b: r<=3, b<=4, d<=4")
    print("OpenAI Lemma 4.2 (shifted tripling) as the reset: a, h <= 5")
    print(f"concavity implication: {concave} inequalities on concave sequences")
    print("ramp product equals F(R,R) and F(R,R)^3 >= R^4 for R <= 300")
    print("all checks passed")


if __name__ == "__main__":
    main()
