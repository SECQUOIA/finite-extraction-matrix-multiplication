#!/usr/bin/env python3
"""Independent exact checks for the Hankel flattening barrier of shifted chains.

Companion to docs/shifted-chains-check-hankel.md.  The script is
self-contained (standard library only) and imports no project code.  Every
assertion uses exact integer or Fraction arithmetic; floating point appears
only in the clearly labelled "display" lines at the end.

Run from the repository root:

    python -I experiments/shifted_chains_check_hankel.py            # full run
    python -I experiments/shifted_chains_check_hankel.py --quick    # smaller ranges
    python -m experiments.shifted_chains_check_hankel

Parts:
  A  local Hankel flattening ranks of C(r,b) and of the middle child, computed
     directly over Q, GF(2), GF(3), GF(5), plus the factorization/identity-minor
     certificates that prove them over every field;
  B  sums of sectors sharing the first leg, including sectors with different
     numbers of middle factors (the Cauchy-Schwarz form of the theorem);
  C  the actual shifted-chain stage maps (quotient/kernel bases, crop, reset,
     type restriction), with identity and compressed auxiliaries: exact target
     structure, cross-sector zeros, target flattening ranks, source flattening
     ranks, and the rank inequality;
  D  symbolic identities for the potentials (derivatives, bridge polynomial,
     endpoint polynomials) and exact integer monotonicity over a large grid;
  E  random legal chains (variable arity, crops, swaps, terminals) and the
     arity-ramp chains: exact per-step and telescoped inequalities;
  F  the ordinary-only (u = 1) corollary.
"""

from __future__ import annotations

import argparse
import math
import random
from collections import Counter, defaultdict
from fractions import Fraction as Fr
from itertools import product

FIELDS = (0, 2, 3)  # 0 denotes the rationals


# ---------------------------------------------------------------------------
# Exact linear algebra
# ---------------------------------------------------------------------------

def rank(rows, field):
    """Rank of a sparse matrix (iterable of {int column: int}) over Q (field=0) or GF(p)."""
    pivots = {}
    result = 0
    for row in rows:
        if field:
            cur = {k: v % field for k, v in row.items() if v % field}
        else:
            cur = {k: Fr(v) for k, v in row.items() if v}
        while cur:
            col = min(cur)
            piv = pivots.get(col)
            if piv is None:
                inv = pow(cur[col], -1, field) if field else 1 / cur[col]
                if field:
                    pivots[col] = {k: v * inv % field for k, v in cur.items()}
                else:
                    pivots[col] = {k: v * inv for k, v in cur.items()}
                result += 1
                break
            f = cur[col]
            for k, v in piv.items():
                nv = cur.get(k, 0) - f * v
                if field:
                    nv %= field
                if nv:
                    cur[k] = nv
                else:
                    cur.pop(k, None)
    return result


def inverse(matrix):
    """Exact inverse of a square integer matrix, as a list of Fraction rows."""
    n = len(matrix)
    aug = [[Fr(x) for x in row] + [Fr(int(i == j)) for j in range(n)]
           for i, row in enumerate(matrix)]
    for col in range(n):
        piv = next(i for i in range(col, n) if aug[i][col] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        inv = 1 / aug[col][col]
        aug[col] = [x * inv for x in aug[col]]
        for i in range(n):
            if i != col and aug[i][col] != 0:
                f = aug[i][col]
                aug[i] = [x - f * y for x, y in zip(aug[i], aug[col])]
    return [row[n:] for row in aug]


# ---------------------------------------------------------------------------
# Tensors and the Hankel flattening
# ---------------------------------------------------------------------------
# A tensor is a dict {(x, y, z): coefficient}; x is a tuple (a first-leg word),
# y and z are arbitrary hashable second- and third-leg coordinates.

def conv(r, b):
    """C(r,b) = sum x_i y_j z_{i+j}."""
    return {((i,), j, i + j): 1 for i in range(r) for j in range(b)}


def middle(r, c):
    """Middle child on the unchanged first leg: T[x,y,z] = [y = r-1-x+z], y < r+c-1, z < c."""
    return {((i,), r - 1 - i + k, k): 1 for i in range(r) for k in range(c)}


def tensor_product(factors):
    result = {((), (), ()): 1}
    for f in factors:
        new = {}
        for (x1, y1, z1), c1 in result.items():
            for (x2, y2, z2), c2 in f.items():
                key = (x1 + x2, y1 + (y2,), z1 + (z2,))
                new[key] = new.get(key, 0) + c1 * c2
        result = {k: v for k, v in new.items() if v}
    return result


def psi(tensor, u, v):
    """Hankel flattening: rows (z,a), columns (y,beta), entry sum_x T[x,y,z] prod [a_t + beta_t = x_t]."""
    rows = defaultdict(lambda: defaultdict(int))
    for (x, y, z), coeff in tensor.items():
        options = [[(a, xt - a) for a in range(max(0, xt - v + 1), min(u - 1, xt) + 1)] for xt in x]
        for choice in product(*options):
            a = tuple(p[0] for p in choice)
            beta = tuple(p[1] for p in choice)
            rows[(z, a)][(y, beta)] += coeff
    columns = {}
    return [{columns.setdefault(key, len(columns)): val for key, val in row.items() if val}
            for row in rows.values()]


# ---------------------------------------------------------------------------
# Part A: local ranks
# ---------------------------------------------------------------------------

def certificate_ordinary(r, b, u):
    """Factorization through t=y+beta and the identity minor: rank b+v-1 over every field."""
    v = r + 1 - u
    rank_bound = b + v - 1
    for z in range(r + b - 1):
        for a in range(u):
            for y in range(b):
                for beta in range(v):
                    entry = int(z == a + y + beta)
                    factored = sum(int(z == a + t) * int(t == y + beta) for t in range(rank_bound))
                    assert entry == factored
    for t in range(rank_bound):
        for t2 in range(rank_bound):
            y = min(t2, b - 1)
            beta = t2 - y
            assert 0 <= beta < v and t < r + b - 1
            assert int(t == 0 + y + beta) == int(t == t2)


def certificate_middle(r, c, u):
    """Factorization through t=z+(u-1-a) and the identity minor: rank c+u-1 over every field."""
    v = r + 1 - u
    rank_bound = c + u - 1
    for z in range(c):
        for a in range(u):
            for y in range(r + c - 1):
                for beta in range(v):
                    entry = int(y == r - 1 - (a + beta) + z)
                    factored = sum(int(t == z + u - 1 - a) * int(y == t + v - 1 - beta)
                                   for t in range(rank_bound))
                    assert entry == factored
    for t in range(rank_bound):
        z = min(t, c - 1)
        a = u - 1 - (t - z)
        assert 0 <= a < u
        for t2 in range(rank_bound):
            y, beta = t2, v - 1
            assert y < r + c - 1
            assert int(y == r - 1 - (a + beta) + z) == int(t == t2)


def part_a(rmax, bmax):
    cases = 0
    for r in range(1, rmax + 1):
        for b in range(1, bmax + 1):
            for u in range(1, r + 1):
                v = r + 1 - u
                certificate_ordinary(r, b, u)
                certificate_middle(r, b, u)
                mo, mm = psi(conv(r, b), u, v), psi(middle(r, b), u, v)
                for p in FIELDS + (5,):
                    assert rank(mo, p) == b + v - 1, (r, b, u, p)
                    assert rank(mm, p) == b + u - 1, (r, b, u, p)
                cases += 1
    print(f"A  local ranks: {cases} (r,b,u) cases; ordinary rank b+v-1 and middle rank b+u-1 "
          f"over Q, GF(2), GF(3), GF(5); factorizations and identity minors certified")


# ---------------------------------------------------------------------------
# Part B: sums of sectors sharing the first leg
# ---------------------------------------------------------------------------

def sector_sum(r, c, words, separate=True):
    total = {}
    for g, word in enumerate(words):
        label = g if separate else 0
        for (x, y, z), co in tensor_product([conv(r, c) if w == "O" else middle(r, c) for w in word]).items():
            key = (x, (label, y), (label, z))
            total[key] = total.get(key, 0) + co
    return {k: v for k, v in total.items() if v}


def part_b():
    cases = 0
    for r, c, n in ((2, 1, 2), (2, 2, 2), (3, 1, 2), (3, 2, 2), (4, 1, 2), (4, 2, 2), (2, 1, 3), (3, 1, 3)):
        words = ["".join(w) for w in product("OM", repeat=n)]
        tensor = sector_sum(r, c, words)
        for u in range(1, r + 1):
            v = r + 1 - u
            expected = sum((c + v - 1) ** w.count("O") * (c + u - 1) ** w.count("M") for w in words)
            matrix = psi(tensor, u, v)
            for p in FIELDS:
                assert rank(matrix, p) == expected, (r, c, n, u, p)
            cases += 1
        # Cauchy-Schwarz step used for even r with mixed middle counts.
        if r % 2 == 0:
            alpha, beta = c + r // 2, c + r // 2 - 1
            s1 = sum(alpha ** w.count("O") * beta ** w.count("M") for w in words)
            s2 = sum(beta ** w.count("O") * alpha ** w.count("M") for w in words)
            assert s1 * s2 >= len(words) ** 2 * (alpha * beta) ** n
    # Negative control: without separate sector labels (cross-sector coupling)
    # the rank is not additive.
    # Two copies of one sector word written on the same Y,Z coordinates (an
    # identification of two sectors) have the rank of one copy, not of two.
    coupled = sector_sum(3, 1, ["OM", "OM"], separate=False)
    separate = sector_sum(3, 1, ["OM", "OM"], separate=True)
    assert 2 * rank(psi(coupled, 2, 2), 0) == rank(psi(separate, 2, 2), 0) == 8
    print(f"B  sector sums with mixed middle counts: {cases} (r,c,N,u) cases over Q, GF(2), GF(3); "
          f"rank = sum_g (c+v-1)^(N-J_g) (c+u-1)^J_g; coupled control is not additive")


# ---------------------------------------------------------------------------
# Part C: the actual shifted-chain stage maps
# ---------------------------------------------------------------------------

WEIGHT = {"K": 2, "O": 1, "M": 0}


def shifted_local_maps(d, r, b, c):
    """Input substitution vectors and output coordinate functionals for one position.

    Old input coordinates are (j, beta): component j < d, coefficient beta < b.
    Old output coordinates are (j, gamma), gamma < m = r+b-1.  New coordinates
    are labelled (class, label, index) with classes K (kernel copies), O (left
    and right outer blocks of the cropped quotient) and M (middle block).
    """
    assert 1 <= c < b and (d + 2) * c <= d * b - r + 1, "illegal step"
    h, m = b - c, r + b - 1
    quotient_in = b + (d - 1) * h
    crop = 3 * c + r - 1
    assert quotient_in >= crop
    inputs = []
    for e in range(crop):
        j = next(j for j in range(d) if 0 <= e - j * h < b)
        if e < c:
            key = ("O", "L", e)
        elif e < 2 * c + r - 1:
            key = ("M", 0, e - c)
        else:
            key = ("O", "R", e - (2 * c + r - 1))
        inputs.append((key, {(j, e - j * h): 1}))
    for k in range(d - 1):
        for i in range(c):
            inputs.append((("K", k, i), {(k, i + h): -1, (k + 1, i): 1}))
    basis = []
    for e in range(quotient_in + r - 1):
        j = next(j for j in range(d) if 0 <= e - j * h < m)
        if e < c + r - 1:
            key = ("O", "L", e)
        elif e < 2 * c + r - 1:
            key = ("M", 0, e - (c + r - 1))
        elif e < 3 * c + 2 * r - 2:
            key = ("O", "R", e - (2 * c + r - 1))
        else:
            key = None  # quotient output outside the crop: dropped
        basis.append((key, {(j, e - j * h): 1}))
    for k in range(d - 1):
        for i in range(c + r - 1):
            basis.append((("K", k, i), {(k, i + h): -1, (k + 1, i): 1}))
    old = [(j, g) for j in range(d) for g in range(m)]
    assert len(basis) == len(old)
    index = {o: n for n, o in enumerate(old)}
    matrix = [[0] * len(basis) for _ in old]
    for col, (_, vec) in enumerate(basis):
        for o, val in vec.items():
            matrix[index[o]][col] = val
    inv = inverse(matrix)
    out_by_old = defaultdict(dict)
    for row, (key, _) in zip(inv, basis):
        for o, val in zip(old, row):
            assert val.denominator == 1, "basis change is not unimodular"
            if val and key is not None:
                out_by_old[o][key] = int(val)
    return inputs, out_by_old


def local_piece(r, maps, j_in, j_out):
    """Transformed single-position tensor of C(r,b) tensor (matrix unit E_{j_in, j_out})."""
    inputs, out_by_old = maps
    piece = defaultdict(int)
    for x in range(r):
        for ykey, vec in inputs:
            for (j, beta), cin in vec.items():
                if j == j_in:
                    for zkey, cout in out_by_old.get((j_out, x + beta), {}).items():
                        piece[((x,), ykey, zkey)] += cin * cout
    return {k: v for k, v in piece.items() if v}


def class_type(word):
    counts = Counter(key[0] for key in word)
    return (counts["K"], counts["O"], counts["M"])


def restricted(pieces, n, aux, nu):
    """Apply the fixed maps to C(r,b)^{(x)n} (x) aux and keep the class type nu on legs 2 and 3."""
    total = defaultdict(int)
    for (w_in, w_out), e in aux.items():
        for (x, y, z), co in tensor_product([pieces[(w_in[t], w_out[t])] for t in range(n)]).items():
            if class_type(y) == nu and class_type(z) == nu:
                total[(x, y, z)] += e * co
    return {k: v for k, v in total.items() if v}


def canonical_child(r, c, cls, label):
    if cls == "M":
        return {(x, (cls, label, y), (cls, label, z)) : co for (x, y, z), co in middle(r, c).items()}
    return {(x, (cls, label, y), (cls, label, z)): co for (x, y, z), co in conv(r, c).items()}


def expected_target(d, r, c, n, nu):
    labels = [("K", k) for k in range(d - 1)] + [("O", "L"), ("O", "R"), ("M", 0)]
    target, sectors = {}, []
    for word in product(labels, repeat=n):
        counts = Counter(cls for cls, _ in word)
        if (counts["K"], counts["O"], counts["M"]) != nu:
            continue
        sectors.append(word)
        target.update(tensor_product([canonical_child(r, c, cls, lab) for cls, lab in word]))
    return target, sectors


def source_tensor(r, b, n, aux):
    """C(r,b)^{(x)n} (x) aux, aux = {(w_in, w_out): coefficient} on auxiliary words."""
    total = defaultdict(int)
    local = conv(r, b)
    for (w_in, w_out), e in aux.items():
        factors = [{(x, (w_in[t], y), (w_out[t], z)): co for (x, y, z), co in local.items()} for t in range(n)]
        for key, co in tensor_product(factors).items():
            total[key] += e * co
    return {k: v for k, v in total.items() if v}


def matrix_aux(matrix):
    return {(((i,)), ((j,))): val for i, row in enumerate(matrix) for j, val in enumerate(row) if val}


def check_stage(d, r, b, c, n, aux=None, aux_rank=None, all_u=True):
    """Check one stage; return the number of flattening-rank comparisons made."""
    maps = shifted_local_maps(d, r, b, c)
    pieces = {(i, j): local_piece(r, maps, i, j) for i in range(d) for j in range(d)}
    if n == 1:
        # Local structure: diagonal blocks are the canonical children, and every
        # off-diagonal coefficient strictly increases the class weight.
        local = defaultdict(int)
        for j in range(d):
            for key, co in pieces[(j, j)].items():
                local[key] += co
        cross = 0
        for (x, y, z), co in local.items():
            if co == 0:
                continue
            if y[:2] == z[:2]:
                child = middle(r, c) if y[0] == "M" else conv(r, c)
                assert child.get((x, y[2], z[2]), 0) == co
            else:
                assert WEIGHT[z[0]] > WEIGHT[y[0]], (y, z)
                cross += 1
    identity = {(w, w): 1 for w in product(range(d), repeat=n)}
    if aux is None:
        aux, aux_rank = identity, d ** n
    comparisons = 0
    for nu in [t for t in product(range(n + 1), repeat=3) if sum(t) == n]:
        target, sectors = expected_target(d, r, c, n, nu)
        got = restricted(pieces, n, aux, nu)
        if aux is not identity:
            assert got == restricted(pieces, n, identity, nu), "auxiliary does not preserve the target"
        assert got == target, (d, r, b, c, nu)
        big_m, j_mid = len(sectors), nu[2]
        if big_m == 0:
            continue
        us = range(1, r + 1) if all_u else sorted({1, (r + 1) // 2, r + 1 - (r + 1) // 2, r})
        for u in us:
            v = r + 1 - u
            target_rank = big_m * (c + v - 1) ** (n - j_mid) * (c + u - 1) ** j_mid
            matrix = psi(target, u, v)
            for p in FIELDS:
                assert rank(matrix, p) == target_rank, (d, r, b, c, nu, u, p)
            assert aux_rank * (b + v - 1) ** n >= target_rank
            comparisons += 1
    return comparisons


def part_c(quick):
    total = 0
    single = [(2, 3, 3, 1), (3, 3, 3, 1), (2, 2, 3, 1), (3, 2, 2, 1), (3, 4, 5, 2),
              (4, 4, 4, 2), (3, 5, 5, 2), (2, 7, 12, 4), (5, 3, 7, 2), (2, 1, 2, 1)]
    for d, r, b, c in single:
        total += check_stage(d, r, b, c, 1)
    double = [(2, 3, 3, 1), (3, 3, 3, 1), (2, 2, 3, 1), (3, 2, 2, 1), (2, 1, 2, 1)]
    if not quick:
        double += [(3, 4, 5, 2), (4, 4, 4, 2)]
    for d, r, b, c in double:
        total += check_stage(d, r, b, c, 2, all_u=(r <= 3))
    # Compressed preserving auxiliaries (binary upper-tail projections), width two.
    tails = 0
    for r, b, c in ((3, 3, 1), (5, 5, 1)):
        for k in range(3):
            tail = {(w, w): 1 for w in product(range(2), repeat=2) if sum(w) >= k}
            maps = shifted_local_maps(2, r, b, c)
            pieces = {(i, j): local_piece(r, maps, i, j) for i in range(2) for j in range(2)}
            identity = {(w, w): 1 for w in product(range(2), repeat=2)}
            for nu in [t for t in product(range(3), repeat=3) if sum(t) == 2 and t[0] == k]:
                assert restricted(pieces, 2, tail, nu) == restricted(pieces, 2, identity, nu)
                big_m = len(expected_target(2, r, c, 2, nu)[1])
                q = len(tail)
                for u in range(1, r + 1):
                    v = r + 1 - u
                    assert q * (b + v - 1) ** 2 >= big_m * (c + v - 1) ** (2 - nu[2]) * (c + u - 1) ** nu[2]
                tails += 1
    # Source flattening rank = rank_K(E) * (b+v-1)^N, computed directly.
    sources = 0
    for r, b, matrix, n in (
            (3, 3, [[1, 1], [1, -1]], 1), (3, 2, [[1, 2, 3], [2, 4, 6]], 1), (3, 3, [[0, 0], [0, 0]], 1),
            (4, 3, [[1, 1, 0], [0, 1, 1], [1, 0, 1]], 1), (3, 3, None, 2)):
        if matrix is None:
            aux = {(w, w): 1 for w in product(range(2), repeat=2) if sum(w) >= 1}
            ranks = {p: 3 for p in FIELDS}
        else:
            aux = matrix_aux(matrix)
            ranks = {p: rank([{j: x for j, x in enumerate(row) if x} for row in matrix], p) for p in FIELDS}
        tensor = source_tensor(r, b, n, aux)
        for u in range(1, r + 1):
            v = r + 1 - u
            flat = psi(tensor, u, v)
            for p in FIELDS:
                assert rank(flat, p) == ranks[p] * (b + v - 1) ** n, (r, b, matrix, u, p)
            sources += 1
    print(f"C  shifted-chain stages: {len(single)} width-one and {len(double)} width-two parameter sets; "
          f"targets equal the canonical sector sums exactly (all cross-sector zeros); {total} target "
          f"flattening ranks over Q, GF(2), GF(3); {tails} tail-auxiliary preservations; "
          f"{sources} direct source ranks q(b+v-1)^N (including char-2 rank drop)")


# ---------------------------------------------------------------------------
# Part D: potentials
# ---------------------------------------------------------------------------

class Poly:
    """Sparse multivariate polynomial with Fraction coefficients."""

    def __init__(self, terms=None, nvars=3):
        self.n = nvars
        self.t = {k: Fr(v) for k, v in (terms or {}).items() if v}

    @classmethod
    def const(cls, c, nvars=3):
        return cls({(0,) * nvars: c}, nvars)

    @classmethod
    def var(cls, i, nvars=3):
        return cls({tuple(int(j == i) for j in range(nvars)): 1}, nvars)

    def _lift(self, other):
        return other if isinstance(other, Poly) else Poly.const(other, self.n)

    def __add__(self, other):
        other = self._lift(other)
        terms = dict(self.t)
        for k, v in other.t.items():
            terms[k] = terms.get(k, 0) + v
        return Poly(terms, self.n)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()}, self.n)

    def __sub__(self, other):
        return self + (-self._lift(other))

    def __rsub__(self, other):
        return self._lift(other) - self

    def __mul__(self, other):
        other = self._lift(other)
        terms = defaultdict(Fr)
        for k1, v1 in self.t.items():
            for k2, v2 in other.t.items():
                terms[tuple(a + b for a, b in zip(k1, k2))] += v1 * v2
        return Poly(terms, self.n)

    __rmul__ = __mul__

    def __pow__(self, e):
        result = Poly.const(1, self.n)
        for _ in range(e):
            result = result * self
        return result

    def __eq__(self, other):
        return (self - self._lift(other)).t == {}

    def compose_univariate(self, value):
        """Substitute a polynomial for variable 0 (univariate use)."""
        result = Poly.const(0, value.n)
        for k, v in self.t.items():
            result = result + v * value ** k[0]
        return result

    def coefficients(self):
        degree = max(k[0] for k in self.t)
        return [self.t.get((i,) + (0,) * (self.n - 1), Fr(0)) for i in range(degree + 1)]


def P_int(r, b):
    return r * r + 4 * r * b + b * b - 2 * r - 2 * b


def A_int(r, b):
    return (r + 2 * b - 1) ** 2 - 1


def part_d(grid):
    x, w, kappa = (Poly.var(i) for i in range(3))
    third = Fr(1, 3)
    r_, b_ = x + third, w + third
    P = r_ * r_ + 4 * r_ * b_ + b_ * b_ - 2 * r_ - 2 * b_
    Q = x * x + 4 * x * w + w * w
    assert P == Q - Fr(2, 3)                                    # centring
    t, delta = x + 2 * w, x - w
    assert t * t - 1 == (r_ + 2 * b_ - 1) ** 2 - 1                # A_r(b) = t^2 - 1
    # Numerator of d/dw [ (2/3) log(Q - kappa) - (1/2) log(t^2 - 1) ] times (Q - kappa)(t^2 - 1).
    numerator = Fr(2, 3) * (4 * x + 2 * w) * (t * t - 1) - 2 * t * (Q - kappa)
    assert numerator == Fr(2, 3) * delta ** 3 + 2 * w * delta ** 2 + (6 * kappa - 4) * w + (2 * kappa - Fr(8, 3)) * delta
    assert numerator == Fr(2, 3) * (t * delta * delta - 2 * delta + (3 * kappa - 2) * t)

    def at(k):
        return Fr(2, 3) * (4 * x + 2 * w) * (t * t - 1) - 2 * t * (Q - k)

    # kappa = 2/3 (the notes' potential P): numerator (2/3) delta (t delta - 2) -> note (7).
    assert at(Fr(2, 3)) == Fr(2, 3) * delta * (t * delta - 2)
    # kappa = 5/6 (recommended Phi = P - 1/6): t * 3 * numerator = 2 (t delta - 1)^2 + t^2 - 2.
    assert 3 * t * at(Fr(5, 6)) == 2 * (t * delta - 1) ** 2 + t * t - 2
    # kappa = 3/4 (review's P - 1/12): numerator = 2D with the review's D and its estimates.
    D = Fr(1, 3) * t * delta * delta + Fr(1, 12) * (3 * w - 7 * delta)
    assert at(Fr(3, 4)) == 2 * D
    assert 12 * D - (4 * delta ** 3 + 8 * delta ** 2 - 7 * delta + 2) == (3 * w - 2) * (4 * delta ** 2 + 1)
    assert 32 * (8 * delta ** 2 - 7 * delta + 2) == (16 * delta - 7) ** 2 + 15
    # The kappa = 2/3 derivative really is negative somewhere inside (x-1, x): bridge needed.
    xv, wv = Fr(5, 3) + 10, Fr(5, 3) + 10 - Fr(1, 100)
    tv, dv = xv + 2 * wv, xv - wv
    assert Fr(2, 3) * dv * (tv * dv - 2) < 0

    # Bridge polynomial of the notes (integer potential P, adjacent step b = r-1 -> r).
    s = Poly.var(0, 1)
    Pp = lambda rr, bb: rr * rr + 4 * rr * bb + bb * bb - 2 * rr - 2 * bb
    Ap = lambda rr, bb: (rr + 2 * bb - 1) ** 2 - 1
    bridge = Pp(s, s) ** 4 * Ap(s, s - 1) ** 3 - Pp(s, s - 1) ** 4 * Ap(s, s) ** 3
    V = 2592 * s ** 5 - 14040 * s ** 4 + 28944 * s ** 3 - 28128 * s ** 2 + 12776 * s - 2187
    assert bridge == s ** 3 * (3 * s - 2) ** 3 * V
    shifted = V.compose_univariate(s + 2).coefficients()
    assert shifted == [709, 5672, 15936, 20304, 11880, 2592]

    # Endpoint polynomials.
    sp = Poly.var(0, 1)
    # Source, Phi = P - 1/6:  6*Phi <= 6*((3/2)s^2 + s - 1/2) - 1 and 11 s^2 minus that is 2(s-1)(s-2).
    assert 11 * sp ** 2 - (6 * (Fr(3, 2) * sp ** 2 + sp - Fr(1, 2)) - 1) == 2 * (sp - 1) * (sp - 2)
    # Terminal, Phi: (6 Phi(1,b))^2 - 121 b^3 at b = 1 + tau has nonnegative coefficients.
    tau = Poly.var(0, 1)
    bb = 1 + tau
    term = (6 * (bb * bb + 2 * bb - 1) - 1) ** 2 - 121 * bb ** 3
    assert term.coefficients() == [0, 165, 345, 167, 36]
    # Terminal, P: P(1,b)^2 - 4 b^3 = 4 tau + 8 tau^2 + 4 tau^3 + tau^4.
    assert ((bb * bb + 2 * bb - 1) ** 2 - 4 * bb ** 3).coefficients() == [0, 4, 8, 4, 1]

    # Exact integer grid: monotonicity of P^4/A^3 (notes), (6P-1)^4/A^3 (recommended),
    # (12P-1)^4/A^3 (review), and the endpoint inequalities.
    comparisons = 0
    for r in range(1, grid + 1):
        a_prev = A_int(r, 1)
        p_prev = P_int(r, 1)
        for b in range(1, grid):
            a_next = A_int(r, b + 1)
            p_next = P_int(r, b + 1)
            a3, n3 = a_prev ** 3, a_next ** 3
            assert p_next ** 4 * a3 > p_prev ** 4 * n3
            assert (6 * p_next - 1) ** 4 * a3 > (6 * p_prev - 1) ** 4 * n3
            assert (12 * p_next - 1) ** 4 * a3 > (12 * p_prev - 1) ** 4 * n3
            comparisons += 1
            a_prev, p_prev = a_next, p_next
    endpoint = 0
    for r in range(1, grid + 1):
        for b in range(1, grid + 1):
            span = r + b - 1
            p = P_int(r, b)
            if span >= 2:
                assert 8 * p <= 15 * span * span and 6 * p - 1 <= 11 * span * span
                assert 48 * (12 * p - 1) <= 89 * 12 * span * span
            assert p >= P_int(1, b)
            endpoint += 1
    for b in range(1, 50 * grid):
        assert P_int(1, b) ** 2 >= 4 * b ** 3 and (6 * P_int(1, b) - 1) ** 2 >= 121 * b ** 3
    print(f"D  potentials: derivative identities for all kappa, kappa=2/3, 5/6, 3/4; bridge "
          f"r^3(3r-2)^3 V(r) with V(t+2) = 709+5672t+...; endpoint polynomials; {3 * comparisons} "
          f"exact integer monotonicity steps and {endpoint} endpoint pairs on a {grid}x{grid} grid")


# ---------------------------------------------------------------------------
# Part E/F: chains
# ---------------------------------------------------------------------------

def legal(r, b, c, d):
    return 1 <= c < b and (d + 2) * c <= d * b - r + 1


def random_chain(rng, steps):
    """Build a legal chain backwards from a terminal pair; return source, stages, terminal."""
    terminal = (rng.choice([1, 1, 1, 2, 3]), rng.randint(1, 6))
    pair = terminal
    stages = []
    for _ in range(steps):
        d = rng.choice([2, 3, 4, 5, 8, 16, 64, 1000])
        c, r = pair if rng.random() < 0.5 else pair[::-1]
        b = max(c + 1, -(-((d + 2) * c + r - 1) // d)) + rng.choice([0, 0, 0, 1, 2, 7])
        assert legal(r, b, c, d)
        stages.append((r, b, c, d))
        pair = (r, b) if rng.random() < 0.5 else (b, r)
    stages.reverse()
    return pair, stages, terminal


def ramp_chain(D, L):
    """Round-11 ramp R = 8D followed (towards the source) by L smallest parents of arity D."""
    R = 8 * D
    stages = []
    for j in range(1, R):  # built backwards: (j,j) <- (j,j+1) <- (j+1,j+1)
        stages.append((j, j + 1, j, 3 * j - 1))
        stages.append((j + 1, j + 1, j, 3 * j))
    pair = (R, R)
    for _ in range(L):
        c, r = pair
        b = -(-((D + 2) * c + r - 1) // D)
        assert legal(r, b, c, D) and b > c
        stages.append((r, b, c, D))
        pair = (r, b)
    stages.reverse()
    return pair, stages, (1, 1)


def check_chain(source, stages, terminal, exact_total=True):
    """Exact per-step bounds and (optionally) the telescoped strict 9/4 inequality."""
    current = source
    for r, b, c, d in stages:
        assert sorted(current) == sorted((r, b)), "stage does not read the current pair"
        assert legal(r, b, c, d)
        a_b, a_c = A_int(r, b), A_int(r, c)
        # Rank bound (parity-averaged) below the potential, for P, 6P-1 and 12P-1.
        assert a_b ** 3 * P_int(c, r) ** 4 < a_c ** 3 * P_int(r, b) ** 4
        assert a_b ** 3 * (6 * P_int(c, r) - 1) ** 4 < a_c ** 3 * (6 * P_int(r, b) - 1) ** 4
        assert a_b ** 3 * (12 * P_int(c, r) - 1) ** 4 < a_c ** 3 * (12 * P_int(r, b) - 1) ** 4
        if r % 2:  # odd r: the balanced bound is the stronger one
            assert (r + 2 * b - 1) ** 2 * a_c <= (r + 2 * c - 1) ** 2 * a_b
        current = (c, r)
    assert sorted(current) == sorted(terminal)
    span = sum(source) - 1
    assert span >= 2
    if exact_total:
        num = terminal[1] ** 6
        den = span ** 8
        for r, b, c, _ in stages:
            num *= A_int(r, b) ** 3
            den *= A_int(r, c) ** 3
        assert num < den                               # log b_f + G_bound < (4/3) log s0
        assert 16 ** 4 * num < 15 ** 4 * den           # notes' constant 15/16
        # Ordinary-only (u = 1): the per-step bound telescopes to s0 / s_f exactly.
        prod = Fr(1)
        for r, b, c, _ in stages:
            prod *= Fr(r + b - 1, r + c - 1)
        assert prod == Fr(span, sum(terminal) - 1)
    return span


def gain_bound_log(stages, terminal):
    """Display only (floating point): log b_f + sum (1/2) log(A_r(b)/A_r(c))."""
    return math.log(terminal[1]) + sum(0.5 * (math.log(A_int(r, b)) - math.log(A_int(r, c)))
                                       for r, b, c, _ in stages)


def part_e(quick):
    rng = random.Random(20261018)
    count = 0
    for _ in range(300 if quick else 3000):
        source, stages, terminal = random_chain(rng, rng.randint(1, 12))
        check_chain(source, stages, terminal)
        count += 1
    ramps = [(2, 100), (4, 400)] if quick else [(2, 100), (4, 400), (8, 1600), (16, 3200)]
    lines = []
    for D, L in ramps:
        source, stages, terminal = ramp_chain(D, L)
        span = check_chain(source, stages, terminal, exact_total=(D <= 2))
        floor = 3 * math.log(span) / gain_bound_log(stages, terminal)
        lines.append(f"D={D}, L={L}, levels={len(stages)}: any-auxiliary floor 3 log s0 / bound = {floor:.6f}")
    print(f"E  chains: {count} random legal chains (arities 2..1000, crops, swaps, terminals) with exact "
          f"per-step, telescoped and ordinary-only identities; ramp chains checked per step")
    print("   display only (floating point), lower bounds on the paid exponent for these chain geometries:")
    for line in lines:
        print("     " + line)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--quick", action="store_true", help="smaller ranges")
    args = parser.parse_args()
    part_a(6 if args.quick else 8, 6 if args.quick else 8)
    part_b()
    part_c(args.quick)
    part_d(200 if args.quick else 1200)
    part_e(args.quick)
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
