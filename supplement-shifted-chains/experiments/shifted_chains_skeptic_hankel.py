#!/usr/bin/env python3
"""Adversarial exact checks for the Hankel flattening barrier (referee pass).

Companion to the section "Adversarial review" of
docs/shifted-chains-check-hankel.md.  Standard library only; imports no
project code and none of the checker's code.  Every assertion uses exact
integer or Fraction arithmetic.  Floating point appears only in lines
labelled "display".

Run from the repository root:

    python -I experiments/shifted_chains_skeptic_hankel.py

Parts:
  1  local Hankel ranks with an independent dense elimination, r,b,c <= 9,
     all lifts, over Q, GF(2), GF(3), GF(7); both middle conventions;
  2  negative controls that really test the cross-sector hypothesis
     (correct diagonal blocks plus cross blocks), and block-triangular junk;
  3  the physical stage rebuilt independently; presence of every kind of
     cross term; and the exact MINIMUM rank of a preserving auxiliary,
     found by enumerating the whole affine space of preserving matrices
     over GF(2) and GF(3), compared with the Hankel bound (H);
  4  potentials by polynomial identity testing on grids larger than the
     degree; the real-variable claim for Phi = P - 1/6 at random rational
     points; an explicit real decrease of the notes' P^4/A^3 inside (r-1,r);
  5  every legal chain in a bounded family (exhaustive, not random):
     exact telescoped inequalities;
  6  the compression-saving bound at zero crop slack (new observation);
  7  v5's separator needs exact cross-sector zeros.
"""

from __future__ import annotations

import math
import random
from collections import Counter
from fractions import Fraction as Fr
from itertools import product

# ---------------------------------------------------------------------------
# Dense exact rank
# ---------------------------------------------------------------------------


def rank_mod(rows, p):
    m = [[v % p for v in row] for row in rows]
    if not m:
        return 0
    ncols, rk = len(m[0]), 0
    for col in range(ncols):
        piv = next((i for i in range(rk, len(m)) if m[i][col]), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        inv = pow(m[rk][col], -1, p)
        prow = [v * inv % p for v in m[rk]]
        m[rk] = prow
        for i in range(rk + 1, len(m)):
            f = m[i][col]
            if f:
                m[i] = [(a - f * b) % p for a, b in zip(m[i], prow)]
        rk += 1
    return rk


def rank_q(rows):
    m = [[Fr(v) for v in row] for row in rows]
    if not m:
        return 0
    ncols, rk = len(m[0]), 0
    for col in range(ncols):
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        prow = m[rk]
        for i in range(rk + 1, len(m)):
            f = m[i][col] / prow[col]
            if f:
                m[i] = [a - f * b for a, b in zip(m[i], prow)]
        rk += 1
    return rk


def all_ranks(rows):
    return {"Q": rank_q(rows), 2: rank_mod(rows, 2), 3: rank_mod(rows, 3), 7: rank_mod(rows, 7)}


# ---------------------------------------------------------------------------
# Tensors: list of (xword, y, z, coeff); Hankel lift as a dense matrix
# ---------------------------------------------------------------------------


def ordinary(r, c):
    return [((x,), y, x + y, 1) for x in range(r) for y in range(c)]


def middle(r, c):
    """Middle child in the unreversed shared coordinates: y = r-1-x+z."""
    return [((x,), r - 1 - x + z, z, 1) for x in range(r) for z in range(c)]


def middle_reversed(r, c):
    """Same block after reversing the first index: y = x+z."""
    return [((x,), x + z, z, 1) for x in range(r) for z in range(c)]


def kron(*tensors):
    out = [((), (), (), 1)]
    for t in tensors:
        out = [(x1 + x2, y1 + (y2,), z1 + (z2,), c1 * c2) for (x1, y1, z1, c1) in out for (x2, y2, z2, c2) in t]
    return out


def lifted(tensor, u, v):
    """Dense matrix rows (z,a), columns (y,beta), entry sum_x T[x,y,z] prod_t [a_t+beta_t = x_t]."""
    rows, cols, entries = {}, {}, {}
    for x, y, z, co in tensor:
        for a in product(*[range(max(0, xt - v + 1), min(u - 1, xt) + 1) for xt in x]):
            beta = tuple(xt - at for xt, at in zip(x, a))
            key = (rows.setdefault((z, a), len(rows)), cols.setdefault((y, beta), len(cols)))
            entries[key] = entries.get(key, 0) + co
    mat = [[0] * len(cols) for _ in rows]
    for (i, j), val in entries.items():
        mat[i][j] = val
    return mat


# ---------------------------------------------------------------------------
# Part 1: local ranks
# ---------------------------------------------------------------------------


def part1():
    cases = 0
    for r in range(1, 10):
        for c in range(1, 10):
            for u in range(1, r + 1):
                v = r + 1 - u
                for name, t, want in (("ordinary", ordinary(r, c), c + v - 1),
                                      ("middle", middle(r, c), c + u - 1),
                                      ("middle-reversed", middle_reversed(r, c), c + u - 1)):
                    ranks = all_ranks(lifted(t, u, v))
                    assert set(ranks.values()) == {want}, (name, r, c, u, ranks)
                cases += 1
    print(f"1  local ranks: {cases} (r,c,u) cases, r,c <= 9: ordinary c+v-1, middle c+u-1 (both index "
          f"conventions) over Q, GF(2), GF(3), GF(7)")


# ---------------------------------------------------------------------------
# Part 2: negative controls
# ---------------------------------------------------------------------------


def labelled(tensor, gy, gz):
    return [(x, (gy, y), (gz, z), co) for x, y, z, co in tensor]


def part2():
    rng = random.Random(7)
    r, c = 3, 1
    base = kron(ordinary(r, c), middle(r, c))           # one sector word "OM", N = 2
    rank_base = rank_q(lifted(base, 2, 2))
    assert rank_base == 4
    # (a) Correct diagonal blocks, all cross blocks equal to the block itself
    #     (sector-label pattern = all-ones 2x2): rank does not add.
    full = labelled(base, 0, 0) + labelled(base, 1, 1) + labelled(base, 0, 1) + labelled(base, 1, 0)
    sep = labelled(base, 0, 0) + labelled(base, 1, 1)
    assert rank_q(lifted(sep, 2, 2)) == 2 * rank_base
    assert rank_q(lifted(full, 2, 2)) == rank_base
    # (b) Block-triangular junk (only sector 0 -> sector 1 cross terms):
    #     rank >= sum of block ranks, so (H) survives such junk.
    tri_cases = 0
    for trial in range(40):
        junk = [(x, (0, y), (1, z), rng.randint(-3, 3)) for x in [(i, j) for i in range(r) for j in range(r)]
                for y in [(a, b2) for a in range(c) for b2 in range(r + c - 1)]
                for z in [(a, b2) for a in range(r + c - 1) for b2 in range(c)] if rng.random() < 0.3]
        t = sep + junk
        for p in ("Q", 2, 3):
            mat = lifted(t, 2, 2)
            rk = rank_q(mat) if p == "Q" else rank_mod(mat, p)
            assert rk >= 2 * rank_base, (trial, p, rk)
        tri_cases += 1
    print(f"2  controls: correct diagonal blocks with full cross blocks give rank {rank_base} instead of "
          f"{2 * rank_base} (cross-sector zeros are necessary); {tri_cases} random block-triangular "
          f"junk patterns keep rank >= sum of blocks over Q, GF(2), GF(3)")


# ---------------------------------------------------------------------------
# Part 3: the physical stage, rebuilt independently, and exact minimum ranks
# ---------------------------------------------------------------------------

WEIGHT = {"K": 2, "O": 1, "M": 0}


def invert(mat):
    n = len(mat)
    a = [[Fr(v) for v in row] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(mat)]
    for col in range(n):
        piv = next(i for i in range(col, n) if a[i][col] != 0)
        a[col], a[piv] = a[piv], a[col]
        p = a[col][col]
        a[col] = [v / p for v in a[col]]
        for i in range(n):
            if i != col and a[i][col] != 0:
                f = a[i][col]
                a[i] = [v - f * w for v, w in zip(a[i], a[col])]
    return [row[n:] for row in a]


def stage_pieces(d, r, b, c):
    """pieces[(j_in, j_out)] = list of (x, ykey, zkey, coeff) for C(r,b) (x) E_{j_in j_out} in new coordinates."""
    h, m = b - c, r + b - 1
    big = b + (d - 1) * h
    crop_in, crop_out = 3 * c + r - 1, 3 * c + 2 * r - 2
    assert 1 <= c < b and big >= crop_in

    def cls_in(e):
        return ("O", "L", e) if e < c else (("M", 0, e - c) if e < 2 * c + r - 1 else ("O", "R", e - 2 * c - r + 1))

    def cls_out(e):
        if e < c + r - 1:
            return ("O", "L", e)
        if e < 2 * c + r - 1:
            return ("M", 0, e - c - r + 1)
        if e < crop_out:
            return ("O", "R", e - 2 * c - r + 1)
        return None

    new_in = []
    for e in range(crop_in):
        j = min(j for j in range(d) if 0 <= e - j * h < b)
        new_in.append((cls_in(e), {(j, e - j * h): 1}))
    for k in range(d - 1):
        for i in range(c):
            new_in.append((("K", k, i), {(k, i + h): -1, (k + 1, i): 1}))
    basis = []
    for e in range(big + r - 1):
        j = min(j for j in range(d) if 0 <= e - j * h < m)
        basis.append((cls_out(e), {(j, e - j * h): 1}))
    for k in range(d - 1):
        for i in range(c + r - 1):
            basis.append((("K", k, i), {(k, i + h): -1, (k + 1, i): 1}))
    old = [(j, g) for j in range(d) for g in range(m)]
    assert len(old) == len(basis)
    pos = {o: i for i, o in enumerate(old)}
    umat = [[0] * len(basis) for _ in old]
    for col, (_, vec) in enumerate(basis):
        for o, val in vec.items():
            umat[pos[o]][col] = val
    uinv = invert(umat)
    for i in range(len(old)):                      # U U^{-1} = I and integrality (unimodular)
        for j in range(len(old)):
            assert sum(umat[i][k] * uinv[k][j] for k in range(len(old))) == int(i == j)
            assert uinv[i][j].denominator == 1
    pieces = {}
    for jin, jout in product(range(d), repeat=2):
        acc = {}
        for x in range(r):
            for ykey, vec in new_in:
                for (j, beta), cin in vec.items():
                    if j != jin:
                        continue
                    col = pos[(jout, x + beta)]
                    for row, (zkey, _) in enumerate(basis):
                        val = uinv[row][col]
                        if val and zkey is not None:
                            key = ((x,), ykey, zkey)
                            acc[key] = acc.get(key, 0) + cin * int(val)
        pieces[(jin, jout)] = [(x, y, z, co) for (x, y, z), co in acc.items() if co]
    return pieces


def type_of(word):
    cnt = Counter(k[0] for k in word)
    return (cnt["K"], cnt["O"], cnt["M"])


def restricted_piece(pieces, w_in, w_out, nu):
    out = {}
    for x, y, z, co in kron(*[pieces[(a, b2)] for a, b2 in zip(w_in, w_out)]):
        if type_of(y) == nu and type_of(z) == nu:
            out[(x, y, z)] = out.get((x, y, z), 0) + co
    return {k: v for k, v in out.items() if v}


def canonical(d, r, c, n, nu):
    labels = [("K", k) for k in range(d - 1)] + [("O", "L"), ("O", "R"), ("M", 0)]
    target, count = {}, 0
    for word in product(labels, repeat=n):
        if type_of([(cl,) for cl, _ in word]) != nu:
            continue
        count += 1
        blocks = [middle(r, c) if cl == "M" else ordinary(r, c) for cl, _ in word]
        for x, y, z, co in kron(*blocks):
            key = (x, tuple((cl, lab, yy) for (cl, lab), yy in zip(word, y)),
                   tuple((cl, lab, zz) for (cl, lab), zz in zip(word, z)))
            target[key] = target.get(key, 0) + co
    return target, count


def nullspace_mod(columns, p):
    """columns: list of dict vectors; return a basis of {lam : sum lam_i col_i = 0 mod p}."""
    keys = sorted({k for col in columns for k in col}, key=repr)
    n = len(columns)
    rows = [[columns[j].get(k, 0) % p for j in range(n)] for k in keys]
    piv_cols, rk = [], 0
    for col in range(n):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col]), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], -1, p)
        rows[rk] = [v * inv % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(a - f * b2) % p for a, b2 in zip(rows[i], rows[rk])]
        piv_cols.append(col)
        rk += 1
    free = [j for j in range(n) if j not in piv_cols]
    basis = []
    for fcol in free:
        vec = [0] * n
        vec[fcol] = 1
        for i, pc in enumerate(piv_cols):
            vec[pc] = (-rows[i][fcol]) % p
        basis.append(vec)
    return basis


def min_preserving_rank(pieces, d, n, nu, p, limit):
    words = list(product(range(d), repeat=n))
    pairs = [(wi, wo) for wi in words for wo in words]
    cols = [restricted_piece(pieces, wi, wo, nu) for wi, wo in pairs]
    ker = nullspace_mod(cols, p)
    if len(ker) > limit:
        return None, len(ker)
    ident = [int(wi == wo) for wi, wo in pairs]
    size = len(words)
    best = size
    for lam in product(range(p), repeat=len(ker)):
        vec = ident[:]
        for coef, kv in zip(lam, ker):
            if coef:
                vec = [(a + coef * b2) % p for a, b2 in zip(vec, kv)]
        mat = [vec[i * size:(i + 1) * size] for i in range(size)]
        best = min(best, rank_mod(mat, p))
    return best, len(ker)


def hankel_lower_bound(r, b, c, n, M, J):
    """Smallest integer q satisfying (H) for every lift u."""
    q = 1
    for u in range(1, r + 1):
        v = r + 1 - u
        need = M * (c + v - 1) ** (n - J) * (c + u - 1) ** J
        q = max(q, -(-need // ((b + v - 1) ** n)))
    return q


def part3():
    kinds, diag_lowering = set(), {}
    params1 = [(2, 3, 3, 1), (3, 3, 3, 1), (2, 2, 3, 1), (2, 1, 2, 1), (3, 4, 5, 2), (2, 7, 12, 4),
               (5, 3, 7, 2), (4, 5, 6, 2), (2, 5, 5, 1), (3, 6, 6, 2)]
    for d, r, b, c in params1:
        assert (d + 2) * c <= d * b - r + 1
        pieces = stage_pieces(d, r, b, c)
        diag = {}
        for j in range(d):
            for x, y, z, co in pieces[(j, j)]:
                diag[(x, y, z)] = diag.get((x, y, z), 0) + co
        # The weight rule concerns the identity auxiliary (sum of the diagonal pieces).  Pieces of
        # off-diagonal auxiliary entries E_{j_in j_out} can lower the weight; that is why a
        # non-diagonal auxiliary must be checked for preservation.
        # Even single diagonal pieces E_{jj} can lower the weight (the lowering cancels only in the
        # sum over j), so a diagonal projection auxiliary is not automatically preserving either.
        lowering = 0
        for jin, jout in product(range(d), repeat=2):
            lowering += sum(1 for x, y, z, co in pieces[(jin, jout)] if WEIGHT[z[0]] < WEIGHT[y[0]])
        assert lowering > 0
        diag_lowering[(d, r, b, c)] = sum(1 for x, y, z, co in pieces[(0, 0)] if WEIGHT[z[0]] < WEIGHT[y[0]])
        for (x, y, z), co in diag.items():
            if not co:
                continue
            if y[:2] != z[:2]:
                assert WEIGHT[z[0]] > WEIGHT[y[0]], (d, r, b, c, y, z)
                kinds.add((y[0], z[0]))
            else:
                ref = middle(r, c) if y[0] == "M" else ordinary(r, c)
                assert (x, y[2], z[2], co) in ref, (d, r, b, c, x, y, z, co)
        # every diagonal-block term of the canonical child is present
        for cls, lab in [("K", k) for k in range(d - 1)] + [("O", "L"), ("O", "R"), ("M", 0)]:
            ref = middle(r, c) if cls == "M" else ordinary(r, c)
            for x, yy, zz, co in ref:
                assert diag.get((x, (cls, lab, yy), (cls, lab, zz)), 0) == co
    assert kinds == {("M", "O"), ("M", "K"), ("O", "K")}, kinds
    assert diag_lowering[(2, 3, 3, 1)] > 0
    # Width two: exact targets, (H), and the exact minimum preserving rank over GF(2), GF(3).
    rows, skipped = [], []
    params2 = [(2, 3, 3, 1), (2, 2, 3, 1), (2, 1, 2, 1), (2, 5, 5, 1), (2, 4, 5, 1), (2, 3, 5, 2),
               (3, 3, 3, 1), (3, 2, 2, 1)]
    for d, r, b, c in params2:
        pieces = stage_pieces(d, r, b, c)
        for nu in [t for t in product(range(3), repeat=3) if sum(t) == 2]:
            target, M = canonical(d, r, c, 2, nu)
            words = list(product(range(d), repeat=2))
            got = {}
            for w in words:
                for k, co in restricted_piece(pieces, w, w, nu).items():
                    got[k] = got.get(k, 0) + co
            got = {k: v for k, v in got.items() if v}
            assert got == target, (d, r, b, c, nu)
            if M == 0:
                continue
            bound = hankel_lower_bound(r, b, c, 2, M, nu[2])
            for p in (2, 3):
                best, kdim = min_preserving_rank(pieces, d, 2, nu, p, 17 if p == 2 else 9)
                if best is not None:
                    assert best >= bound, (d, r, b, c, nu, p, best, bound)
                    rows.append((d, r, b, c, nu, M, p, best, bound, kdim))
                else:
                    skipped.append((d, r, b, c, nu, p, kdim))
    # Width one, higher arity: exact minima over GF(2) and GF(3).
    for d, r, b, c in ((3, 3, 3, 1), (4, 4, 4, 2), (5, 3, 7, 2), (4, 3, 4, 1), (5, 5, 5, 1)):
        pieces = stage_pieces(d, r, b, c)
        for nu in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
            target, M = canonical(d, r, c, 1, nu)
            bound = hankel_lower_bound(r, b, c, 1, M, nu[2])
            for p in (2, 3):
                best, kdim = min_preserving_rank(pieces, d, 1, nu, p, 16 if p == 2 else 10)
                if best is not None:
                    assert best >= bound, (d, r, b, c, nu, p, best, bound)
                    rows.append((d, r, b, c, nu, M, p, best, bound, kdim))
                else:
                    skipped.append((d, r, b, c, nu, p, kdim))
    tight = sum(1 for row in rows if row[7] == row[8])
    print(f"3  physical stages rebuilt: {len(params1)} width-one sets (unimodular, U U^-1 = I, all off-"
          f"diagonal terms raise the weight; M->O, M->K, O->K all occur); {len(params2)} width-two sets "
          f"with exact canonical targets; exact minimum preserving rank over the full affine space of "
          f"preserving matrices in {len(rows)} (stage, type, field) cases, all >= the Hankel bound; "
          f"attained in {tight}")
    print(f"   enumeration skipped (kernel too large) in {len(skipped)} cases: "
          + ", ".join(f"d={d} ({r},{b},{c}) {nu} GF({p}) dim {k}" for d, r, b, c, nu, p, k in skipped))
    for row in rows:
        d, r, b, c, nu, M, p, best, bound, kdim = row
        print(f"     d={d} (r,b,c)=({r},{b},{c}) type(K,O,M)={nu} M={M} GF({p}): min rank {best}, "
              f"Hankel bound {bound}, identity rank {d ** 2}, kernel dim {kdim}")


# ---------------------------------------------------------------------------
# Part 4: potentials
# ---------------------------------------------------------------------------


def grid_identity(f, g, nvars, deg):
    """f == g as polynomials of degree <= deg in each variable (checked on a product grid)."""
    for pt in product(range(deg + 1), repeat=nvars):
        pt = [Fr(v) for v in pt]
        assert f(*pt) == g(*pt), pt


def upoly_mul(a, b2):
    out = [0] * (len(a) + len(b2) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b2):
            out[i + j] += x * y
    return out


def upoly_pow(a, e):
    out = [1]
    for _ in range(e):
        out = upoly_mul(out, a)
    return out


def upoly_sub(a, b2):
    n = max(len(a), len(b2))
    a, b2 = a + [0] * (n - len(a)), b2 + [0] * (n - len(b2))
    out = [x - y for x, y in zip(a, b2)]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def taylor_shift(a, s):
    """Coefficients of a(t + s)."""
    out = [0]
    for coef in reversed(a):
        out = upoly_mul(out, [s, 1])
        out[0] += coef
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def P(r, b):
    return r * r + 4 * r * b + b * b - 2 * r - 2 * b


def A(r, t):
    return (r + 2 * t - 1) ** 2 - 1


def part4():
    third = Fr(1, 3)
    # Centring and A = t^2 - 1.
    grid_identity(lambda x, w: P(x + third, w + third), lambda x, w: x * x + 4 * x * w + w * w - Fr(2, 3), 2, 2)
    grid_identity(lambda x, w: A(x + third, w + third), lambda x, w: (x + 2 * w) ** 2 - 1, 2, 2)

    # Derivative numerator (D): (2/3) Q_w (t^2-1) - 2 t (Q - kappa) with Q_w = 4x+2w, t_w = 2.
    def lhs(x, w, k):
        t = x + 2 * w
        return Fr(2, 3) * (4 * x + 2 * w) * (t * t - 1) - 2 * t * (x * x + 4 * x * w + w * w - k)

    def rhs(x, w, k):
        t, dl = x + 2 * w, x - w
        return Fr(2, 3) * (t * dl * dl - 2 * dl + (3 * k - 2) * t)
    grid_identity(lhs, rhs, 3, 3)
    # The derivative itself, by an exact difference quotient limit check at rational points:
    # f(w) = (2/3) log(Q-k) - (1/2) log(t^2-1); f'(w) = lhs / ((Q-k)(t^2-1)).  Equivalent rational
    # form without logarithms: by the quotient rule (Q_w = 4x+2w, t_w = 2),
    # (t^2-1)^4 * d/dw[(Q-k)^4 / (t^2-1)^3] = 4 (Q-k)^3 Q_w (t^2-1) - 3 (Q-k)^4 (2t) t_w,
    # and we check that this equals 6 (Q-k)^3 lhs, so its sign is the sign of lhs.
    def g_prime(x, w, k):
        t, q = x + 2 * w, x * x + 4 * x * w + w * w - k
        return 4 * q ** 3 * (4 * x + 2 * w) * (t * t - 1) - 3 * q ** 4 * 2 * t * 2

    def g_claim(x, w, k):
        q = x * x + 4 * x * w + w * w - k
        return 6 * q ** 3 * lhs(x, w, k)
    grid_identity(g_prime, g_claim, 3, 11)
    # kappa = 5/6 certificate and kappa = 2/3 factorisation.
    grid_identity(lambda t, dl: t * (2 * t * dl * dl - 4 * dl + t), lambda t, dl: 2 * (t * dl - 1) ** 2 + t * t - 2, 2, 3)
    grid_identity(lambda x, w: rhs(x, w, Fr(5, 6)) * 3, lambda x, w: 2 * (x + 2 * w) * (x - w) ** 2 - 4 * (x - w) + (x + 2 * w), 2, 3)
    grid_identity(lambda x, w: rhs(x, w, Fr(2, 3)), lambda x, w: Fr(2, 3) * (x - w) * ((x + 2 * w) * (x - w) - 2), 2, 3)
    # Endpoints for Phi = P - 1/6.
    grid_identity(lambda r, b: P(r, b) - Fr(1, 6), lambda r, b: (r + b - 1) ** 2 - Fr(7, 6) + 2 * r * b, 2, 2)
    grid_identity(lambda s, z: Fr(11, 6) * s * s - (Fr(3, 2) * s * s + s - Fr(2, 3)), lambda s, z: (s - 1) * (s - 2) / 3, 2, 2)
    # 6*Phi(1, 1+tau) = 6(tau^2 + 4 tau + 2) - 1 = 6 tau^2 + 24 tau + 11; P(1, 1+tau) = tau^2 + 4 tau + 2.
    assert all(6 * P(1, 1 + k) - 1 == 6 * k * k + 24 * k + 11 for k in range(5))
    assert upoly_sub(upoly_pow([11, 24, 6], 2), [121 * v for v in upoly_pow([1, 1], 3)]) == [0, 165, 345, 167, 36]
    assert upoly_sub(upoly_pow([2, 4, 1], 2), [4 * v for v in upoly_pow([1, 1], 3)]) == [0, 4, 8, 4, 1]
    # Bridge polynomial of the notes.
    s = [0, 1]
    Pss = [0, -4, 6]                                 # P(r,r) = 6r^2 - 4r
    Psm = [3, -10, 6]                                # P(r,r-1) = 6r^2 - 10r + 3
    assert all(P(k, k) == sum(cf * k ** i for i, cf in enumerate(Pss)) for k in range(1, 9))
    assert all(P(k, k - 1) == sum(cf * k ** i for i, cf in enumerate(Psm)) for k in range(1, 9))
    Arm = [8, -18, 9]                                # A_r(r-1) = (3r-3)^2 - 1
    Arr = [0, -6, 9]                                 # A_r(r) = (3r-1)^2 - 1 = 9r^2 - 6r
    assert all(A(k, k - 1) == sum(cf * k ** i for i, cf in enumerate(Arm)) for k in range(1, 9))
    assert all(A(k, k) == sum(cf * k ** i for i, cf in enumerate(Arr)) for k in range(1, 9))
    bridge = upoly_sub(upoly_mul(upoly_pow(Pss, 4), upoly_pow(Arm, 3)), upoly_mul(upoly_pow(Psm, 4), upoly_pow(Arr, 3)))
    V = [-2187, 12776, -28128, 28944, -14040, 2592]
    assert bridge == upoly_mul(upoly_mul(upoly_pow(s, 3), upoly_pow([-2, 3], 3)), V)
    assert taylor_shift(V, 2) == [709, 5672, 15936, 20304, 11880, 2592]
    # Real-variable claim for Phi at random rational points (r >= 1, 1 <= c < b), exact.
    rng = random.Random(11)
    real_checks = 0
    for _ in range(20000):
        den = rng.choice([1, 2, 3, 5, 7, 11, 97])
        r = Fr(rng.randint(den, 60 * den), den)
        c = Fr(rng.randint(den, 60 * den), den)
        b = c + Fr(rng.randint(1, 60 * den), den)
        lhs6 = (6 * P(r, b) - 1) ** 4 * A(r, c) ** 3
        rhs6 = (6 * P(r, c) - 1) ** 4 * A(r, b) ** 3
        assert lhs6 > rhs6, (r, b, c)
        real_checks += 1
    # Near-degenerate real steps around the diagonal, where the margin is smallest.
    for r in [Fr(k, 4) for k in range(4, 400)]:
        for eps in (Fr(1, 10 ** 6), Fr(1, 1000), Fr(1, 3)):
            for centre in (r - 1, r - Fr(1, 2), r, r + 1):
                c = max(Fr(1), centre)
                b = c + eps
                assert (6 * P(r, b) - 1) ** 4 * A(r, c) ** 3 > (6 * P(r, c) - 1) ** 4 * A(r, b) ** 3
                real_checks += 1
    # The notes' P alone is NOT monotone between integers: an explicit real decrease inside (r-1, r).
    # The kappa = 2/3 derivative is negative exactly for 0 < r-b < 2/t (t = r+2b-1, about 3r).
    r = Fr(12)
    b1, b2 = r - Fr(1, 20), r - Fr(1, 1000)
    assert P(r, b2) ** 4 * A(r, b1) ** 3 < P(r, b1) ** 4 * A(r, b2) ** 3
    # ... while the integer step r-1 -> r is still increasing (the bridge), and Phi is increasing there.
    assert P(r, r) ** 4 * A(r, r - 1) ** 3 > P(r, r - 1) ** 4 * A(r, r) ** 3
    assert (6 * P(r, b2) - 1) ** 4 * A(r, b1) ** 3 > (6 * P(r, b1) - 1) ** 4 * A(r, b2) ** 3
    print(f"4  potentials: centring, derivative numerator (D) for all kappa, the derivative of "
          f"(Q-kappa)^4/(t^2-1)^3, kappa=5/6 and 2/3 certificates, endpoints, bridge and V(t+2) verified "
          f"by grid identity testing / exact polynomial arithmetic; {real_checks} exact real (rational) "
          f"steps for Phi = P - 1/6; explicit real decrease of P^4/A^3 inside (r-1,r) at r=12")


# ---------------------------------------------------------------------------
# Part 5: exhaustive bounded chains
# ---------------------------------------------------------------------------


def part5():
    count, best = 0, (0.0, None)
    arities = (2, 3, 4, 6, 9)
    slacks = (0, 1, 3)

    def parents(pair):
        out = []
        for c, r in {pair, pair[::-1]}:
            for d in arities:
                bmin = max(c + 1, -(-((d + 2) * c + r - 1) // d))
                for sl in slacks:
                    b = bmin + sl
                    assert 1 <= c < b and (d + 2) * c <= d * b - r + 1
                    for nxt in {(r, b), (b, r)}:
                        out.append((nxt, (r, b, c)))
        return out

    def walk(pair, stages, terminal, depth):
        nonlocal count, best
        if stages:
            s0 = sum(pair) - 1
            bf = max(terminal)
            num, den = bf ** 6, s0 ** 8
            for r, b, c in stages:
                num *= A(r, b) ** 3
                den *= A(r, c) ** 3
            assert num < den and 16 ** 4 * num < 15 ** 4 * den
            # Telescoped potential: prod (A(b)/A(c))^3 < (Phi(source)/Phi(terminal))^4, Phi = P - 1/6.
            pa, pc = 1, 1
            for r, b, c in stages:
                pa *= A(r, b) ** 3
                pc *= A(r, c) ** 3
            assert pa * (6 * P(*terminal) - 1) ** 4 < pc * (6 * P(*pair) - 1) ** 4
            count += 1
            ratio = (6 * math.log(bf) + 3 * sum(math.log(A(r, b)) - math.log(A(r, c)) for r, b, c in stages)) \
                / (8 * math.log(s0))                                       # display only
            if ratio > best[0]:
                best = (ratio, (pair, list(reversed(stages)), terminal))
        if depth == 0:
            return
        for nxt, st in parents(pair):
            walk(nxt, stages + [st], terminal, depth - 1)

    for terminal in [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]:
        walk(terminal, [], terminal, 3)
    print(f"5  exhaustive bounded chains: {count} legal chains (depth <= 3, arities {arities}, crop slacks "
          f"{slacks}, both orders, 6 terminals): exact b_f^6 prod A(b)^3 < s0^8 prod A(c)^3, also with 15/16")
    print(f"   display: largest (log b_f + bound)/((4/3) log s0) found = {best[0]:.4f} for {best[1]}")


# ---------------------------------------------------------------------------
# Part 6: how much can compression save at a legal stage?  (new observation)
# ---------------------------------------------------------------------------


def part6():
    checks = 0
    for d in range(2, 30):
        for r in range(1, 40):
            for c in range(1, 30):
                bmin = max(c + 1, -(-((d + 2) * c + r - 1) // d))
                for b in range(bmin, bmin + 4):
                    slack = d * b - (d + 2) * c - r + 1
                    assert slack >= 0
                    # identity behind the bound
                    assert d * (2 * b + r - 1) - (d + 2) * (2 * c + r - 1) == 2 * slack
                    if slack == 0 and r % 2 == 1:
                        assert d * (2 * b + r - 1) == (d + 2) * (2 * c + r - 1)
                    # even-r analogue: d^2 A_r(b) - (d+2)^2 A_r(c) = 4(d+2)(slack(r+2c) - slack + 1) + 4 slack^2 - 4
                    assert d * d * A(r, b) - (d + 2) ** 2 * A(r, c) == \
                        4 * (d + 2) * (slack * (r + 2 * c) - slack + 1) + 4 * slack * slack - 4
                    checks += 1
    # Uncompressed identity auxiliaries satisfy (H) for every type (sanity of the sector count formula).
    sanity = 0
    for d in (2, 3, 5):
        for r, c in ((3, 1), (4, 2), (5, 2), (6, 3), (7, 3)):
            b = max(c + 1, -(-((d + 2) * c + r - 1) // d))
            for n in (1, 2, 5, 9):
                for nk in range(n + 1):
                    for no in range(n + 1 - nk):
                        nm = n - nk - no
                        M = math.factorial(n) // (math.factorial(nk) * math.factorial(no) * math.factorial(nm)) \
                            * (d - 1) ** nk * 2 ** no
                        for u in range(1, r + 1):
                            v = r + 1 - u
                            assert d ** n * (b + v - 1) ** n >= M * (c + v - 1) ** (n - nm) * (c + u - 1) ** nm
                            sanity += 1
    print(f"6  zero-slack identity d(2b+r-1)-(d+2)(2c+r-1) = 2*slack on {checks} legal (d,r,b,c); "
          f"{sanity} uncompressed (type, lift) sanity checks of (H)")


def part7():
    """v5 separator weights on ONE cross-sector term from Y_g to Z_{g2}, g2 != g.

    After Fourier averaging, the surviving index pairs satisfy e' = e + g' - g.  The weights
    X_{g'}: t^{g'^2}, Y_{g,e}: t^{2ge-g^2}, Z_{g2,e'}: t^{-2 g2 e'} give the exponent below.
    For g2 > g some contribution has a negative exponent (the map is no longer a degeneration);
    for g2 < g some contribution has exponent zero (a cross term survives in the constant term,
    which is then not the direct sum).  Either way the separator needs exact cross-sector zeros.
    """
    for M in range(2, 9):
        for g in range(M):
            for g2 in range(M):
                if g2 == g:
                    continue
                exps = [gp * gp + 2 * g * e - g * g - 2 * g2 * (e + gp - g)
                        for gp in range(M) for e in range(M) if 0 <= e + gp - g < M]
                if g2 > g:
                    assert min(exps) < 0, (M, g, g2)
                else:
                    assert min(exps) == 0, (M, g, g2)
    print("7  v5 separator weights on a single cross-sector term (M <= 8): from Y_g to Z_g2 with g2 > g "
          "a negative t-exponent occurs, with g2 < g a cross term survives at t = 0; the recipe needs "
          "exact cross-sector zeros (matches the preserving definition)")


def display_classical_floors():
    # d -> infinity on the efficient ray: lambda = 1 - eps, eps ~ 3/(2d), middle fraction mu ~ 1/d.
    u1 = 4.5 / (math.log(2) + 1.5)
    ur = 4.5 / (3 - math.log(2))
    print(f"   display: d->infinity limits of the classical-flattening floors on the efficient ray: "
          f"u=1 -> {u1:.4f}, u=r -> {ur:.4f}")


def main():
    part1()
    part2()
    part3()
    part4()
    part5()
    part6()
    part7()
    display_classical_floors()
    print("All skeptic checks passed.")


if __name__ == "__main__":
    main()
