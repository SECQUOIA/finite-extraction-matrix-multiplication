#!/usr/bin/env python3
"""Adversarial checks for docs/shifted-chains-check-seeds.md (key "seeds").

Run from the repository root:

    python -I experiments/shifted_chains_skeptic_seeds.py           # eps = 1, 1/2, 1/4
    python -I experiments/shifted_chains_skeptic_seeds.py --full    # also eps = 1/8

Stdlib only; imports nothing from the repository and shares no code with
experiments/shifted_chains_check_seeds.py.  Identities and inequalities
are decided with int and Fraction.  Logarithms come from the decimal
module, whose ln() is documented as correctly rounded; each value is
widened by one unit in the last place (relative 10^(1-PREC)) and then
converted exactly to a Fraction, so every enclosure is rigorous.

Sections
  A. arithmetic constants of the note (Theorems 7, 12, Prop. 8, Lemma 11)
  B. pooled-recursion counting on synthetic parameters with rational p,
     including huge n: (4.1), Theorem 7, Remark 10, Prop. 8, Lemma 11,
     and Theorem 7 end to end at the exact side n0
  C. a rational toy scheme with denominators: unrolled seed is an exact
     decomposition of MM_n, and Prop. 9(1) (denominator D^lmax, height)
  D. schedule, U(v) bound for v <= 3000, the selection rule v(X), and the
     constants of the lower-bound outline (review finding 5)
  E. literal chains (greedy mode allocator, Decimal logs): p, Phi,
     Lemma P (p > 9/4), Lemma 1, n0 digits, depth interval
  F. simpler certificates for the A^24 / precision / exponent-range
     polynomial inequalities, and an independent expansion of the notes'
     polynomial
"""

from __future__ import annotations

import argparse
import decimal
import math
import random
from collections import Counter
from fractions import Fraction as Fr
from itertools import product

PREC = 70


# ---------------------------------------------------------------------------
# certified logarithms via decimal (correctly rounded ln)
# ---------------------------------------------------------------------------

def _ln_dec(m):
    """Rigorous enclosure (lo, hi) of ln(m) for a positive integer m < 2^240."""
    if m == 1:
        return Fr(0), Fr(0)
    with decimal.localcontext() as ctx:
        ctx.prec = PREC
        d = decimal.Decimal(m).ln()
    v = Fr(d)
    err = abs(v) * Fr(1, 10 ** (PREC - 1))
    return v - err, v + err


_LN2 = _ln_dec(2)


def ln_int(n):
    """Rigorous enclosure of ln(n) for any positive integer n."""
    assert n >= 1
    k = max(0, n.bit_length() - 200)
    top = n >> k
    lo, _ = _ln_dec(top)
    _, hi = _ln_dec(top + 1) if k else _ln_dec(top)
    return lo + k * _LN2[0], hi + k * _LN2[1]


def iv_add(*xs):
    return sum(x[0] for x in xs), sum(x[1] for x in xs)


def iv_scale(c, x):
    assert c >= 0
    return c * x[0], c * x[1]


def iv_div(x, y):
    """x/y for intervals with y > 0 and x of any sign."""
    assert y[0] > 0
    cands = [x[0] / y[0], x[0] / y[1], x[1] / y[0], x[1] / y[1]]
    return min(cands), max(cands)


def cdiv(a, b):
    return -((-a) // b)


# ---------------------------------------------------------------------------
# A. constants
# ---------------------------------------------------------------------------

def section_a():
    assert 2 * 2305 ** 2 * 240 == 2_550_252_000 < 2_551 * 10 ** 6
    assert 81 * 2_551 * 10 ** 6 < 21 * 10 ** 10                 # Theorem 7: 2.1e11
    assert Fr(5, 4) * Fr(512, 497) <= Fr(1288, 1000)             # Prop. 8
    assert 27 * 3 * Fr(1288, 1000) * 3 <= 313                    # Prop. 8
    assert Fr(7, 3) * 2 * 27 == 126                              # Lemma 11
    assert Fr(7, 3) * 12 * Fr(4, 3) * 4 <= 150
    assert Fr(7, 3) * 12 == 28
    assert 126 + 150 + 28 == 304
    assert Fr(1400, 3000) <= Fr(467, 1000)                       # Theorem 12, Step 2
    assert Fr(1500 + 22, 3000) < Fr(51, 100)                     # Theorem 12, Step 4
    assert 3000 * 4 * 10 ** 9 == 12 * 10 ** 12
    assert 2 ** 11 * (12 * 10 ** 12) ** 2 <= 478 ** 11           # 2 (1.2e13)^(2/11) <= 478
    assert Fr(51, 100) * 478 <= 244
    # Lemma 1(7): Xi + 1 <= 55 A^(53/2) <= A^27 needs A >= 55^2
    assert 55 ** 2 < 2 ** 12
    # Remark 13: c_seed = (1+6R d0^2) R <= 7 R^2 d0^2 and R < d0^(13/4) give 7 d0^8.5
    assert Fr(13, 4) * 2 + 2 == Fr(17, 2)
    return "constants ok"


# ---------------------------------------------------------------------------
# B. pooled-recursion counting with rational pooled exponent p = a/b
# ---------------------------------------------------------------------------

def pooled(r, m, A, B, n):
    """Exact counts of v5 Lemma 2.4 and the dense operation count of Lemma 11."""
    nstar = cdiv(A * B, B - A) + 1
    nus, sides, ops = [1], [n], 0
    while sides[-1] > nstar:
        c = cdiv(sides[-1], B)
        batches = cdiv(nus[-1], m)
        ops += batches * 6 * r * m * A * A * B * B * c * c
        nus.append(r * batches)
        sides.append(A * c)
    ops += 2 * nus[-1] * sides[-1] ** 3
    return nus, sides, ops, nstar


def le_pow(x, b, y, a):
    """Decide x^b <= y^a for nonnegative Fractions (exact)."""
    return Fr(x) ** b <= Fr(y) ** a


def synthetic_schemes():
    """(name, r, m, A, B, a, b, t): B/A = t^b and r/m = t^a, so p = a/b exactly."""
    out = []
    for (A, m, t, a, b) in [(1, 1, 2, 9, 4), (3, 5, 2, 9, 4), (2, 32 ** 3, 2, 9, 4),
                            (5, 405 ** 3, 3, 9, 4), (1, 1, 2, 5, 2), (2, 3, 2, 5, 2),
                            (1, 1, 2, 2, 1), (1, 1, 2, 3, 1), (1, 1, 2, 11, 4),
                            (4, 7, 3, 7, 3), (1, 2, 5, 9, 4)]:
        B = A * t ** b
        r = m * t ** a
        assert r * A * A >= m * B * B                         # flattening (Step 1)
        out.append((f"p={a}/{b},A={A},B={B},m={m}", r, m, A, B, a, b, t))
    return out


def check_counts(sch, n):
    name, r, m, A, B, a, b, t = sch
    nus, sides, ops, nstar = pooled(r, m, A, B, n)
    lmax = len(nus) - 1
    rho = Fr(A, B)
    ninf = Fr(A * B, B - A)
    Cnu = 1 + Fr(r * m, r - m)
    for l, (nu, sd) in enumerate(zip(nus, sides)):
        assert nu <= Cnu * Fr(r, m) ** l                              # (4.1) counts
        assert rho ** l * n <= sd < ninf + rho ** l * n               # (4.1) sides
    assert rho < rho ** lmax * n <= nstar                             # (4.1) last depth
    # Prop. 8 in integer form
    assert n * A ** lmax <= nstar * B ** lmax
    assert lmax == 0 or B ** (lmax - 1) < n * A ** (lmax - 1)
    assert lmax <= (n.bit_length() - 1) + 1                           # l_max <= log2 n + 1
    # Theorem 7: R = nu_lmax n_lmax^3 <= Xi n^p, and nu_lmax < r(1+rm) n^p
    Xi = r * (1 + r * m) * nstar ** 3
    R = nus[-1] * sides[-1] ** 3
    assert le_pow(Fr(R, Xi), b, n, a)
    assert Fr(nus[-1], r * (1 + r * m)) ** b < Fr(n) ** a
    # Remark 10: nu_lmax >= m (r/m)^lmax, leaves of side >= A, R >= m A^3 (n/n_*)^p
    if lmax >= 1:
        assert nus[-1] >= m * Fr(r, m) ** lmax
        assert sides[-1] >= A
        assert Fr(R, m * A ** 3) ** b >= Fr(n, nstar) ** a
    # Lemma 11 (hypotheses B >= 2A, m <= B^3, p <= 3)
    if B >= 2 * A and m <= B ** 3 and a <= 3 * b:
        rm = Fr(r, m)
        inner = 2 * rm * nstar ** 3 + 12 * m * B * B * (Fr(4, 3) * rm * ninf ** 2
                                                        + lmax * Fr(t) ** (a - 2 * b))
        assert le_pow(Fr(ops) / (Cnu * inner), b, n, a)               # ops <= K
        assert Cnu * inner <= 304 * (1 + lmax) * B ** 11              # K <= 304 (lmax+1) B^11 n^p
    return lmax, R


def theorem7_end_to_end(sch, eps):
    """At n0 = (Xi+1)^ceil(2/eps): R < n0^(9/4+eps) exactly (needs p < 9/4 + eps/2)."""
    name, r, m, A, B, a, b, t = sch
    assert Fr(a, b) < Fr(9, 4) + eps / 2
    nstar = cdiv(A * B, B - A) + 1
    Xi = r * (1 + r * m) * nstar ** 3
    c2 = cdiv(2 * eps.denominator, eps.numerator)
    n0 = (Xi + 1) ** c2
    target = Fr(9, 4) + eps
    out = []
    for n in (n0, n0 + 1, 2 * n0 - 1, n0 * B + 3):
        lmax, R = check_counts(sch, n)
        assert Fr(R) ** target.denominator < Fr(n) ** target.numerator
        out.append(lmax)
    # the bound fails to be guaranteed below n0 only through Xi; check R <= Xi n^p was tight-ish
    return n0.bit_length(), out


def section_b():
    rng = random.Random(20261018)
    schemes = synthetic_schemes()
    checked = 0
    for sch in schemes:
        nstar = cdiv(sch[3] * sch[4], sch[4] - sch[3]) + 1
        ns = set(range(1, 400))
        B = sch[4]
        for j in range(1, 30):
            for off in (-1, 0, 1):
                v = B ** j + off
                if v >= 1:
                    ns.add(v)
                    ns.add(v * nstar)
        for _ in range(150):
            ns.add(rng.randrange(1, 10 ** rng.randrange(2, 61)))
        for n in sorted(ns):
            check_counts(sch, n)
            checked += 1
    e2e = []
    for sch in schemes:
        a, b = sch[5], sch[6]
        for eps in (Fr(1), Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(3, 7)):
            if Fr(a, b) < Fr(9, 4) + eps / 2:
                bits, depths = theorem7_end_to_end(sch, eps)
                e2e.append((sch[0], str(eps), bits, depths[0]))
    return checked, e2e


# ---------------------------------------------------------------------------
# C. a rational toy scheme: unrolled seed and Prop. 9(1)
# ---------------------------------------------------------------------------

# Strassen for 2x2: entry index 2*i+j
S_U = [{0: 1, 3: 1}, {2: 1, 3: 1}, {0: 1}, {3: 1}, {0: 1, 1: 1}, {2: 1, 0: -1}, {1: 1, 3: -1}]
S_V = [{0: 1, 3: 1}, {0: 1}, {1: 1, 3: -1}, {2: 1, 0: -1}, {3: 1}, {0: 1, 1: 1}, {2: 1, 3: 1}]
S_W = {0: {0: 1, 3: 1, 4: -1, 6: 1}, 1: {2: 1, 4: 1}, 2: {1: 1, 3: 1}, 3: {0: 1, 1: -1, 2: 1, 5: 1}}


def rational_toy(m):
    """r MM_1 |> m MM_2 with r = 7m: m Strassen copies, U scaled by 1/2, V by 1/3, W by 6.

    Returns lists: U[s] = {(copy, entry): coef}, V likewise, W[copy][entry] = {s: coef}.
    """
    U, V = [], []
    W = [dict() for _ in range(m)]
    for cp in range(m):
        for t in range(7):
            U.append({(cp, e): Fr(c, 2) for e, c in S_U[t].items()})
            V.append({(cp, e): Fr(c, 3) for e, c in S_V[t].items()})
        for e, terms in S_W.items():
            W[cp][e] = {7 * cp + t: Fr(6 * c) for t, c in terms.items()}
    return U, V, W


def add_form(f, g, c):
    for k, v in g.items():
        nv = f.get(k, 0) + c * v
        if nv:
            f[k] = nv
        else:
            f.pop(k, None)


def unroll_toy(m, n):
    """Pooled recursion of v5 Lemma 2.4 for the toy scheme (A=1, B=2), symbolically.

    Inputs are matrices of linear forms; the leaf products are recorded; the
    outputs are linear forms in the leaf products.  Returns (terms, outputs, lmax).
    """
    U, V, W = rational_toy(m)
    r, A, B = 7 * m, 1, 2
    nstar = cdiv(A * B, B - A) + 1
    X = [[{("x", i, j): Fr(1)} for j in range(n)] for i in range(n)]
    Y = [[{("y", i, j): Fr(1)} for j in range(n)] for i in range(n)]
    level, side, stack = [(X, Y)], n, []
    while side > nstar:
        c = cdiv(side, B)
        nb = cdiv(len(level), m)
        new = []
        for bi in range(nb):
            grp = level[bi * m:(bi + 1) * m]

            def block(M, e, i, j):
                ii, jj = (e // 2) * c + i, (e % 2) * c + j
                return M[ii][jj] if ii < side and jj < side else {}
            for s in range(r):
                xs = [[{} for _ in range(c)] for _ in range(c)]
                ys = [[{} for _ in range(c)] for _ in range(c)]
                for (cp, e), coef in U[s].items():
                    if cp < len(grp):
                        for i, j in product(range(c), repeat=2):
                            add_form(xs[i][j], block(grp[cp][0], e, i, j), coef)
                for (cp, e), coef in V[s].items():
                    if cp < len(grp):
                        for i, j in product(range(c), repeat=2):
                            add_form(ys[i][j], block(grp[cp][1], e, i, j), coef)
                new.append((xs, ys))
        stack.append((side, c, nb, len(level)))
        level, side = new, A * c
    terms = []
    prods = []
    for x, y in level:
        k = len(x)
        P = [[{} for _ in range(k)] for _ in range(k)]
        for i, j, l in product(range(k), repeat=3):
            terms.append((x[i][j], y[j][l]))
            P[i][l][len(terms) - 1] = Fr(1)
        prods.append(P)
    while stack:
        prev, c, nb, nu = stack.pop()
        outs = []
        for bi in range(nb):
            src = prods[bi * r:(bi + 1) * r]
            for cp in range(m):
                Z = [[{} for _ in range(B * c)] for _ in range(B * c)]
                for e, terms_w in W[cp].items():
                    for s, coef in terms_w.items():
                        for i, j in product(range(c), repeat=2):
                            add_form(Z[(e // 2) * c + i][(e % 2) * c + j], src[s][i][j], coef)
                outs.append([row[:prev] for row in Z[:prev]])
        prods = outs[:nu]
    return terms, prods[0]


def section_c():
    rows = []
    for m in (1, 2):
        for n in (3, 4, 5, 6, 7, 8, 9):
            terms, Z = unroll_toy(m, n)
            # depth: recompute counts
            nus, sides, _, nstar = pooled(7 * m, m, 1, 2, n)
            lmax = len(nus) - 1
            # exact tensor comparison with MM_n
            T = Counter()
            for i, l in product(range(n), repeat=2):
                for tix, cw in Z[i][l].items():
                    u, v = terms[tix]
                    for (ku, cu), (kv, cv) in product(u.items(), v.items()):
                        T[ku, kv, (i, l)] += cu * cv * cw
            T = {k: v for k, v in T.items() if v}
            want = {(("x", i, j), ("y", j, l), (i, l)): 1
                    for i in range(n) for j in range(n) for l in range(n)}
            assert T == want, (m, n)
            assert len(terms) == nus[-1] * sides[-1] ** 3
            # Prop. 9(1): every coefficient times D^lmax is an integer, D = 6,
            # with |numerator| < 2^(lmax (h + log2(m B^2)) + 1), h = 6 (36 < 2^6)
            D, h = 6, 6
            bound = 2 ** (lmax * h) * (m * 4) ** lmax * 2
            coeffs = [c for u, v in terms for c in list(u.values()) + list(v.values())]
            coeffs += [c for row in Z for f in row for c in f.values()]
            for c in coeffs:
                num = c * D ** lmax
                assert num.denominator == 1 and abs(num.numerator) < bound
            rows.append((m, n, lmax, len(terms)))
    return rows


# ---------------------------------------------------------------------------
# D. schedule, U(v), the selection rule
# ---------------------------------------------------------------------------

def schedule(eps):
    eps = Fr(eps)
    p, q = eps.numerator, eps.denominator
    D = math.isqrt(cdiv(4 * q, p))
    while D * D * p < 4 * q:
        D += 1
    while D > 1 and (D - 1) ** 2 * p >= 4 * q:
        D -= 1
    R = 8 * D
    L = cdiv(64 * D * q, p)
    H = cdiv(128 * D * q, p).bit_length()
    N = cdiv(256 * D * H * q, p)
    J = 2 * (R - 1) + L
    return D, R, L, H, N, J


def U_of(v):
    D, R, L, H, N, J = schedule(Fr(1, v))
    return 2 * N * N * J * (24 * D).bit_length()


def select(X):
    if 3000 * U_of(1) > X:
        return 0
    lo = 1
    hi = 2
    while 3000 * hi * U_of(hi) <= X:
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if 3000 * mid * U_of(mid) <= X:
            lo = mid
        else:
            hi = mid
    return lo


def section_d():
    assert U_of(1) == 40_259_026_944
    prev = 0
    worst = Fr(0)
    for v in list(range(1, 3001)) + [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 8, 10 ** 12]:
        u = U_of(v)
        assert u >= prev or v > 3000
        prev = u
        lam_lo = ln_int(4096 * v)[0]
        # U(v) <= 4e9 v^(9/2) Lambda^3  <=>  U^2 <= 16e18 v^9 Lambda^6
        assert u * u <= (4 * 10 ** 9) ** 2 * v ** 9 * lam_lo ** 6
        ratio2 = Fr(u * u) / (v ** 9 * lam_lo ** 6)
        worst = max(worst, ratio2)
    # constants of the lower-bound outline (review finding 5), v <= 3000:
    # U(v+1) <= 36 U(v); U(v) >= 6.9e7 v^(9/2) Lambda^3; L log2 D >= 0.135 J bitlength(24D)
    for v in range(1, 3001):
        u, u1 = U_of(v), U_of(v + 1)
        assert u1 <= 36 * u
        lam_hi = ln_int(4096 * v)[1]
        assert u * u >= Fr(69, 10) ** 2 * 10 ** 14 * v ** 9 * lam_hi ** 6
        D, R, L, H, N, J = schedule(Fr(1, v))
        assert L * ln_int(D)[0] / _LN2[1] >= Fr(135, 1000) * J * (24 * D).bit_length()
    table = {}
    for e in (18, 20, 24, 30, 40):
        X = 10 ** e
        v = select(X)
        assert 3000 * v * U_of(v) <= X < 3000 * (v + 1) * U_of(v + 1)
        table[e] = v
    assert table == {18: 4, 20: 9, 24: 48, 30: 526, 40: 29249}, table
    # threshold: y >= 1 for X >= 2e18, i.e. 1.2e13 Lambda(X)^3 <= X at X = 2e18
    X0 = 2 * 10 ** 18
    assert 12 * 10 ** 12 * ln_int(4096 * X0)[1] ** 3 <= X0
    return math.sqrt(float(worst)), table


# ---------------------------------------------------------------------------
# E. literal chains
# ---------------------------------------------------------------------------

def greedy_mode(N, d):
    """Maximize N!/(K!O!U!) (d-1)^K 2^O by greedy marginal allocation (separable concave)."""
    w = (d - 1, 2, 1)
    c = [0, 0, 0]
    # start from a proportional point and correct greedily from below
    tot = d + 2
    c = [N * wi // tot for wi in w]
    c = [max(0, x - 2) for x in c]
    for _ in range(N - sum(c)):
        best = 0
        for i in (1, 2):
            # w_i/(c_i+1) > w_best/(c_best+1)
            if w[i] * (c[best] + 1) > w[best] * (c[i] + 1):
                best = i
        c[best] += 1
    # optimality certificate: no single transfer j -> i increases the objective
    for i in range(3):
        for j in range(3):
            if i != j and c[j] > 0:
                assert w[i] * c[j] <= w[j] * (c[i] + 1)
    return tuple(c)


def mode_value(N, d, c):
    K, O, U = c
    return math.comb(N, K) * math.comb(N - K, O) * (d - 1) ** K * 2 ** O


def brute_mode(N, d):
    best = 0
    for K in range(N + 1):
        for O in range(N - K + 1):
            best = max(best, mode_value(N, d, (K, O, N - K - O)))
    return best


def literal(eps):
    D, R, L, H, N, J = schedule(eps)
    k = N
    rev = [a for j in range(1, R) for a in (3 * j - 1, 3 * j)] + [D] * L
    r = b = 1
    for idx, d in enumerate(rev):
        nb = cdiv((d + 2) * r + b - 1, d)
        slack = d * nb - b + 1 - (d + 2) * r
        assert r < nb and 0 <= slack < d
        if idx < 2 * (R - 1):
            assert slack == 0
        r, b = b, nb
    s = r + b - 1
    cnt = Counter(rev)
    assert sum(cnt.values()) == J and max(cnt) == 3 * R - 3 < 24 * D
    lnA = (0, 0)
    lnB = (0, 0)
    lnR = iv_scale(6 * N * k, ln_int(s))
    G = (0, 0)
    for d, c in cnt.items():
        M = mode_value(N, d, greedy_mode(N, d))
        assert M <= (d + 2) ** N <= M * (N + 1) ** 2
        E = 1 + 6 * k * (M - 1)
        lnA = iv_add(lnA, iv_scale(2 * N * k * c, ln_int(d)))
        lnB = iv_add(lnB, iv_scale(2 * k * c, ln_int(M)))
        lnR = iv_add(lnR, iv_scale(c, iv_add(iv_scale(6 * k, ln_int(2 * M - 1)), ln_int(E))))
        g = (ln_int(d + 2)[0] - ln_int(d)[1], ln_int(d + 2)[1] - ln_int(d)[0])
        G = iv_add(G, iv_scale(c, g))
    lnm = iv_scale(3, lnB)
    gain = (lnB[0] - lnA[1], lnB[1] - lnA[0])
    assert gain[0] > _LN2[1]                                       # B > 2A
    assert lnB[1] <= 2 * lnA[0]                                    # B <= A^2
    num = (lnR[0] - lnm[1], lnR[1] - lnm[0])
    p = iv_div(num, gain)
    Phi = iv_div((num[0] + _LN2[0], num[1] + _LN2[1]), gain)
    assert Phi[1] < Fr(9, 4) + Fr(eps) / 2
    assert p[0] > Fr(9, 4)                                         # Lemma P / Corollary 7
    lns = ln_int(s)
    assert 3 * lns[0] >= Fr(9, 4) * G[1]                           # Lemma P chain inequality
    assert lnR[1] <= Fr(35, 4) * lnA[0]                            # Lemma 1(5)
    # Xi in [r^2 m A^3, 55 r^2 m A^3] (A < n_* <= 3A, 1+rm <= 2rm)
    lnXi_lo = 2 * lnR[0] + lnm[0] + 3 * lnA[0]
    lnXi1_hi = 2 * lnR[1] + lnm[1] + 3 * lnA[1] + ln_int(55)[1]
    assert lnXi_lo >= 12 * lnA[1] and lnXi1_hi <= 27 * lnA[0]      # Lemma 1(7)
    c2 = cdiv(2 * Fr(eps).denominator, Fr(eps).numerator)
    ln_n0 = (c2 * lnXi_lo, c2 * lnXi1_hi)
    # rank R <= Xi n0^p < n0^(9/4+eps)
    assert lnXi1_hi < (Fr(9, 4) + Fr(eps) - p[1]) * ln_n0[0]
    depth = ((ln_n0[0] - lnA[1] - ln_int(3)[1]) / gain[1], 1 + ln_n0[1] / gain[0])
    depth_int = (math.ceil(depth[0]), math.ceil(depth[1]) - 1)   # l_max in this integer range
    ln10 = ln_int(10)
    return dict(eps=str(eps), D=D, J=J, N=N, s_bits=s.bit_length(),
                p=(float(p[0]), float(p[1])), Phi=float(Phi[1]),
                digitsA=float(lnA[0] / ln10[1]), digits_n0=(float(ln_n0[0] / ln10[1]),
                                                            float(ln_n0[1] / ln10[0])),
                ratio_n0_A=float(ln_n0[1] / lnA[0]),
                rA=float(lnR[1] / lnA[0]), BA=float(lnB[1] / lnA[0]),
                depth=depth_int,
                lemmaP_margin=float(3 * lns[0] - Fr(9, 4) * G[1]))


def section_e(full):
    for N in range(1, 26):
        for d in range(2, 31):
            assert mode_value(N, d, greedy_mode(N, d)) == brute_mode(N, d), (N, d)
    rows = [literal(e) for e in ([Fr(1), Fr(1, 2), Fr(1, 4)] + ([Fr(1, 8)] if full else []))]
    return rows


# ---------------------------------------------------------------------------
# F. polynomial inequalities, independently
# ---------------------------------------------------------------------------

def pmul(a, b):
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def padd(*ps):
    out = [Fr(0)] * max(len(p) for p in ps)
    for p in ps:
        for i, x in enumerate(p):
            out[i] += x
    return out


def mono(e, c=1):
    return [Fr(0)] * e + [Fr(c)]


def section_f():
    h = mono(1, Fr(1, 2))                       # h = log2 A <= A/2 (all envelopes increase in h)
    one = mono(0)
    Dlog = padd(pmul(mono(5, 4), h),
                pmul(mono(1), padd(pmul(mono(2, 24), padd(h, one)), pmul(mono(5, 18), h))))
    Slog = pmul(mono(4), padd(one, pmul(mono(0, 4), h)))
    Rlog = padd(pmul(mono(1, 4), padd(mono(0, 2), pmul(mono(0, 4), h))), mono(3))
    Vlog = pmul(mono(4), padd(Slog, Rlog, pmul(mono(0, 200), h)))
    tot = padd(Dlog, Vlog, mono(0, 2))
    want = {9: 2, 8: 1, 7: 10, 6: 10, 5: 108, 4: 12, 3: 24, 0: 2}
    got = {i: c for i, c in enumerate(tot) if c}
    assert got == want, got
    # one-line certificates (A >= 16):
    # sum of coefficients 169 < 2^15 <= A^15, so P(A) <= 169 A^9 < A^24
    assert sum(want.values()) == 169 < 2 ** 15
    # 1 + 67 log2 A + 3 A^24 <= 71 A^24 < A^28 since A^4 >= 16^4 > 71
    assert 1 + 67 + 3 < 16 ** 4
    # 5 A^28 + 3 A^24 + 150 log2 A + 5 <= 163 A^28 < A^30 since A^2 >= 256 > 163
    assert 5 + 3 + 150 + 5 < 16 ** 2
    # P = r_* A^3 <= A^(47/4) and D_tar = m_* B^2 <= A^10 give T <= A^24 and
    # 2 T Gamma <= 2 A^24 A^(47/4 + 20) 2^(3 A^24): 67 log2 A covers 24 + 31.75 + 1
    assert Fr(24) + Fr(47, 4) + 20 + 1 <= 67
    return "polynomial certificates ok"


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true", help="also run the eps=1/8 literal chain")
    args = ap.parse_args()
    print("[A]", section_a())
    checked, e2e = section_b()
    print(f"[B] counting checks on {len(synthetic_schemes())} synthetic schemes, {checked} sides: pass")
    for row in e2e:
        print("    Theorem 7 end to end: scheme {} eps={} n0 has {} bits, l_max(n0)={}".format(*row))
    rows = section_c()
    print("[C] rational toy unrolling (m, n, l_max, leaf products):", rows)
    worst, table = section_d()
    print(f"[D] U(v) <= 4e9 v^4.5 Lambda^3 for v<=3000 and 5 larger v; max ratio {worst:.4e};"
          f" v(X) for X=1e18..1e40: {table}")
    for row in section_e(args.full):
        print("[E]", row)
    print("[F]", section_f())
    print("all skeptic checks passed")


if __name__ == "__main__":
    main()
