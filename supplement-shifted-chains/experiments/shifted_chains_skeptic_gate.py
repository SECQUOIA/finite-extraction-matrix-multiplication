"""Adversarial re-check of the finite gate (topic "gate").

Run from the repository root:

    python -I -B experiments/shifted_chains_skeptic_gate.py

This script imports neither the round-11 producers nor the checker
experiments/shifted_chains_check_gate.py. It uses a different arithmetic
path from both: Python's decimal module at 90 significant digits, whose
ln, exp, sqrt and basic operations are documented to be correctly rounded.
Every sign claim below is accepted only with a padding of 1e-50, which is
about 40 orders of magnitude larger than the accumulated rounding error.
Pure identities (polynomial algebra, chain legality, type counts, integer
sides) use exact integers and Fractions.

Checks:
  1. The quadratic contraction identity, by coefficient comparison in
     Q(d)[lambda]/(q lambda^2 + lambda - d) for d = 2..400.
  2. Lemmas 3, 4 and t <= s on all legal chains of depth <= 3 with
     r0, b0 <= 10, arities 2..7, all crops and all swaps (exact rationals,
     using a bisection enclosure of lambda_d that is independent of isqrt).
  3. The local-cost lemmas on every type of every small (n, d, k), and
     the blocked local relaxation (any n k | P versus the screen's choice).
  4. The census, counted twice (product dynamic programming and recursion),
     with the gaining pairs searched up to d = 4n+10 without assuming
     n >= 3 or d <= 2n.
  5. Every relaxed margin and every one-level closing margin.
  6. The realized one-level witness and a search over all one-level chains
     with A <= 2^128 (every gaining (n, k, d), terminal t <= 400).
  7. Sharpness: at p_hi = 2.976961 every open case is a forced one-level
     chain, every one-level chain has exponent >= the witness's, and the
     tail t > 400 is closed by Lemma 4. Hence the witness exponent
     2.97696088251553944749816701... is the exact minimum of both models
     at A <= 2^128 (given the count model of the notes).
  8. Realized chains of depth 2 and 3 (exact least source for every
     ordered word, checked against brute force), as an upper-side probe.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from functools import lru_cache
from math import factorial
import json
from pathlib import Path
import sys

getcontext().prec = 90
PAD = Decimal("1e-50")
CAP_BITS = 128
CAP = 1 << CAP_BITS
ALPHA = Fraction(40, 49)
D = Decimal


def dec(x: Fraction) -> Decimal:
    return D(x.numerator) / D(x.denominator)


# ---------------------------------------------------------------------------
# 1. The quadratic identity, reduced modulo the minimal polynomial of lambda.
# Elements of Q[lambda]/(q lambda^2 + lambda - d) are pairs (u, v) = u + v*lambda.
# ---------------------------------------------------------------------------

def check_identity(dmax=400):
    for d in range(2, dmax + 1):
        q = d + 2

        def mul(x, y):
            u = x[0] * y[0]
            v = x[0] * y[1] + x[1] * y[0]
            w = x[1] * y[1]                    # w * lambda^2 = w * (d - lambda)/q
            return (u + w * Fraction(d, q), v - w * Fraction(1, q))

        def add(*xs):
            return (sum(x[0] for x in xs), sum(x[1] for x in xs))

        def sc(c, x):
            return (Fraction(c) * x[0], Fraction(c) * x[1])

        lam = (Fraction(0), Fraction(1))
        one = (Fraction(1), Fraction(0))
        lam2 = mul(lam, lam)
        beta = add(lam, sc(Fraction(1, q), one))
        omb2 = add(one, sc(-1, mul(beta, beta)))       # 1 - beta^2
        # Coefficients of R^2, RB, B^2 on both sides.
        # LHS = lam^2 (R^2 + 4RB + B^2) - Q((dB - R)/q, R)
        # Q((dB-R)/q, R) = (d^2B^2 - 2dRB + R^2)/q^2 + 4(dRB - R^2)/q + R^2
        lhs = {
            "RR": add(lam2, sc(-(Fraction(1, q * q) - Fraction(4, q) + 1), one)),
            "RB": add(sc(4, lam2), sc(-(Fraction(-2 * d, q * q) + Fraction(4 * d, q)), one)),
            "BB": add(lam2, sc(-Fraction(d * d, q * q), one)),
        }
        # RHS = (1 - beta^2)(R^2 - 2 lam RB + lam^2 B^2)
        rhs = {"RR": omb2, "RB": sc(-2, mul(omb2, lam)), "BB": mul(omb2, lam2)}
        assert lhs == rhs, d
        # beta < 1 because f(x) = q x^2 + x - d is increasing on x >= 0 and
        # f(1 - 1/q) = 1 > 0 = f(lambda).
        x = 1 - Fraction(1, q)
        assert q * x * x + x - d == 1
    return dmax - 1


# ---------------------------------------------------------------------------
# lambda_d enclosures by bisection on f(x) = (d+2)x^2 + x - d (exact rationals).
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def lam_enclosure(d, bits=96):
    q = d + 2
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if q * mid * mid + mid - d < 0:
            lo = mid
        else:
            hi = mid
    assert q * lo * lo + lo - d < 0 <= q * hi * hi + hi - d
    return lo, hi


def z_low(word):
    z = Fraction(1)
    for d in word:
        z /= lam_enclosure(d)[1]
    return z


# ---------------------------------------------------------------------------
# 2. Geometry on actual chains.
# ---------------------------------------------------------------------------

def check_chains(limit=10, depth=3, arities=range(2, 8)):
    arities = tuple(arities)
    stats = {"chain_endpoints": 0, "one_level_equalities": 0, "min_L3_slack": None}

    def children(r, b):
        for x, y in ((r, b), (b, r)):           # optional input swap
            for d in arities:
                for c in range(1, y):
                    if (d + 2) * c > d * y - x + 1:
                        break
                    yield d, (c, x)

    def walk(state, word, s):
        if word:
            z = z_low(word)
            for t in state:                     # optional output swap
                bound = ALPHA * z * t + (Fraction(4, 3) - ALPHA) * z - Fraction(1, 3)
                assert s >= bound, (state, word, s)
                slack = s - bound
                if stats["min_L3_slack"] is None or slack < stats["min_L3_slack"]:
                    stats["min_L3_slack"] = slack
                assert t <= s
                if len(word) == 1:
                    d = word[0]
                    lhs = d * s
                    rhs = (d + 1) * t + 1
                    assert lhs >= rhs
                    stats["one_level_equalities"] += lhs == rhs
                stats["chain_endpoints"] += 1
        if len(word) < depth:
            for d, nxt in children(*state):
                walk(nxt, word + (d,), s)

    for r0 in range(1, limit + 1):
        for b0 in range(1, limit + 1):
            walk((r0, b0), (), r0 + b0 - 1)
    stats["min_L3_slack"] = float(stats["min_L3_slack"])   # display only
    return stats


def check_one_level_large(limit=120, dmax=12):
    """Lemma 4 on every one-level chain with r0, b0 <= limit and d <= dmax."""
    n_cases = 0
    for d in range(2, dmax + 1):
        for r0 in range(1, limit + 1):
            for b0 in range(1, limit + 1):
                s = r0 + b0 - 1
                for r, b in ((r0, b0), (b0, r0)):
                    cmax = min(b - 1, (d * b - r + 1) // (d + 2))
                    for c in range(1, cmax + 1):
                        for t in (c, r):
                            assert d * s >= (d + 1) * t + 1
                            n_cases += 1
    return n_cases


# ---------------------------------------------------------------------------
# 3. Types and local costs.
# ---------------------------------------------------------------------------

def type_counts(n, d):
    out = []
    for kern in range(n + 1):
        for outer in range(n + 1 - kern):
            mid = n - kern - outer
            out.append(factorial(n) // (factorial(kern) * factorial(outer) * factorial(mid))
                       * (d - 1) ** kern * 2 ** outer)
    return out


@lru_cache(maxsize=None)
def mmax(n, d):
    return max(type_counts(n, d))


def gains(n, d):
    return mmax(n, d) > d ** n


@lru_cache(maxsize=None)
def ln_int(x: int) -> Decimal:
    return D(x).ln()


def local_cost(n, d, k, M, p: Decimal) -> Decimal:
    return (p * ln_int(d) - p / n * ln_int(M) + D(3) / n * (ln_int(2 * M - 1) - ln_int(M))
            + ln_int(1 + 6 * k * (M - 1)) / (2 * n * k))


def check_local_lemmas():
    ps = [D(2), D("2.5"), D("2.9"), D("2.975"), D("2.999")]
    n_checked = 0
    for n in range(1, 13):
        for d in range(2, 2 * n + 4):
            mm = mmax(n, d)
            g = mm > d ** n
            if g:
                assert n >= 3 and d <= 2 * n and mm >= 9
            for k in (1, 2, 3, 5, 8):
                for p in ps:
                    best = local_cost(n, d, k, mm, p)
                    for M in set(type_counts(n, d)):
                        c = local_cost(n, d, k, M, p)
                        if g:
                            assert c >= best - PAD, (n, d, k, M, p)
                        else:
                            assert c >= -PAD, (n, d, k, M, p)
                        n_checked += 1
    return n_checked


def blocked_screen_local(P, d, p):
    """The screen's local value: min over gaining n <= P of C(n, d, floor(P/n), M_max)."""
    vals = [local_cost(n, d, P // n, mmax(n, d), p) for n in range(1, P + 1) if gains(n, d)]
    return min(vals)


def check_blocked_local(Pmax=14):
    """For every physical block n k | P with gaining n and every type,
    the actual local cost is at least the screen's value."""
    ps = [D(2), D("2.9"), D("2.975")]
    count = 0
    for P in range(1, Pmax + 1):
        for d in range(2, 2 * P + 2):
            if not any(gains(n, d) for n in range(1, P + 1)):
                continue
            for p in ps:
                screen = blocked_screen_local(P, d, p)
                for n in range(1, P + 1):
                    if not gains(n, d):
                        continue
                    for k in range(1, P // n + 1):
                        if P % (n * k):
                            continue
                        for M in set(type_counts(n, d)):
                            assert local_cost(n, d, k, M, p) >= screen - PAD
                            count += 1
    return count


# ---------------------------------------------------------------------------
# 4. Census.
# ---------------------------------------------------------------------------

def max_prod(e):
    """Largest x with x^e <= 2^128, by integer bisection."""
    lo, hi = 1, 1 << (CAP_BITS // e + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** e <= CAP:
            lo = mid
        else:
            hi = mid - 1
    return lo


def count_by_dp(arities, bound):
    """Number of nonempty multisets with product <= bound (dynamic programming on products)."""
    table = {1: 1}
    for d in sorted(arities):
        new = dict(table)
        for prod, cnt in table.items():
            p = prod * d
            while p <= bound:
                new[p] = new.get(p, 0) + cnt
                p *= d
        table = new
    return sum(table.values()) - 1


def list_multisets(arities, bound):
    arities = sorted(arities)
    out = []

    def rec(start, prod, acc):
        if acc:
            out.append(tuple(acc))
        for i in range(start, len(arities)):
            d = arities[i]
            if prod * d > bound:
                break
            rec(i, prod * d, acc + [d])
    rec(0, 1, [])
    return out


def common_rows():
    # Gaining pairs are searched without assuming n >= 3 or d <= 2n; the scan
    # goes to d = 4n+10 (Lemma 6 proves there is no gain for d >= 2n+1).
    pairs = []
    for n in range(1, CAP_BITS // 2 + 1):
        d = 2
        while d ** (2 * n) <= CAP and d <= 4 * n + 10:
            if gains(n, d):
                assert n >= 3 and d <= 2 * n
                pairs.append((n, d))
            d += 1
    rows = []
    by_nk = {}
    for n in sorted({n for n, _ in pairs}):
        ar = [d for m, d in pairs if m == n]
        for k in range(1, CAP_BITS // (2 * n) + 1):
            bound = max_prod(2 * n * k)
            ws = list_multisets(ar, bound)
            assert len(ws) == count_by_dp(ar, bound)
            if ws:
                by_nk[f"{n}:{k}"] = len(ws)
            rows += [(n, k, w) for w in ws]
    return pairs, rows, by_nk


def blocked_rows():
    actions = {}
    for P in range(1, CAP_BITS // 2 + 1):
        d = 2
        while d ** (2 * P) <= CAP and d <= 4 * P + 10:
            ns = [n for n in range(1, P + 1) if gains(n, d)]
            if ns:
                assert min(ns) >= 3 and d <= 2 * P
                actions[P, d] = ns
            d += 1
    rows = []
    by_P = {}
    for P in sorted({P for P, _ in actions}):
        ar = [d for (Q, d) in actions if Q == P]
        bound = max_prod(2 * P)
        ws = list_multisets(ar, bound)
        assert len(ws) == count_by_dp(ar, bound)
        by_P[str(P)] = len(ws)
        rows += [(P, w) for w in ws]
    return actions, rows, by_P


# ---------------------------------------------------------------------------
# 5. Margins.
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def ln_lambda(d):
    q = d + 2
    lam = ((D(1 + 4 * d * q)).sqrt() - 1) / (2 * q)
    return lam.ln()


def endpoint_value(a: Decimal, c: Decimal, p: Decimal) -> Decimal:
    t = max(D(1), p * c / ((3 - p) * a))
    return 3 * (a * t + c).ln() - p * t.ln()


def relaxed_endpoint(word, p):
    z = (-sum(ln_lambda(d) for d in word)).exp()
    a = dec(ALPHA) * z
    c = dec(Fraction(4, 3) - ALPHA) * z - D(1) / 3
    return endpoint_value(a, c, p)


def one_level_endpoint(d, p):
    return endpoint_value(D(d + 1) / d, D(1) / d, p)


def classify(margin):
    if margin > PAD:
        return 1
    if margin < -PAD:
        return -1
    raise AssertionError("margin too close to zero for the decimal check")


def screen(rows, local, label, p):
    neg = []
    best = None
    for key, word in rows:
        m = relaxed_endpoint(word, p) + sum(local(key, d, p) for d in word)
        if best is None or m < best[0]:
            best = (m, key, word)
        if classify(m) < 0:
            neg.append((key, word, m))
    return best, neg


# ---------------------------------------------------------------------------
# 6. One-level chains at the cap.
# ---------------------------------------------------------------------------

def exact_exponent(n, k, d, M, s, t):
    """Exact sides and multiplicities of the common-model count formulas, and
    the pooled exponent log(r/m)/log(B/A) as a Decimal (from the huge integers)."""
    A = d ** (2 * n * k)
    B = t ** (2 * n * k) * M ** (2 * k)
    r = s ** (6 * n * k) * (2 * M - 1) ** (6 * k) * (1 + 6 * k * (M - 1))
    m = M ** (6 * k)
    assert B > A
    return A, B, r, m, (D(r).ln() - D(m).ln()) / (D(B).ln() - D(A).ln())


def factored_exponent(n, k, d, M, s, t):
    """The same pooled exponent, computed from logarithms of the small factors."""
    num = (6 * n * k * ln_int(s) + 6 * k * (ln_int(2 * M - 1) - ln_int(M))
           + ln_int(1 + 6 * k * (M - 1)))
    den = 2 * n * k * ln_int(t) + 2 * k * ln_int(M) - 2 * n * k * ln_int(d)
    assert den > 0
    return num / den


def one_level_search(tmax=400):
    """Least exact pooled exponent over one-level chains with A <= 2^128 and t <= tmax.

    For a one-level chain of arity d with terminal t, the least source size is
    s = ceil(((d+1) t + 1)/d) (Lemma 4 and the chain (r, b) = (t, ceil((t+d+1)/d)),
    c = 1); the largest type is optimal (Lemma 8). The window t <= tmax makes this
    an upper bound on the one-level infimum, not a proof that it is the infimum."""
    best = None
    for n in range(1, 65):
        for k in range(1, 64 // n + 1):
            d = 2
            while d ** (2 * n * k) <= CAP and d <= 2 * n:   # Lemma 6: no gain for d > 2n
                if gains(n, d):
                    M = mmax(n, d)
                    for t in range(1, tmax + 1):
                        s = -((-((d + 1) * t + 1)) // d)
                        # realizability of (s, t): r = t, b = s - t + 1, c = 1
                        r, b = t, s - t + 1
                        assert 1 < b and (d + 2) <= d * b - r + 1
                        p = factored_exponent(n, k, d, M, s, t)
                        if best is None or p < best[0]:
                            best = (p, n, k, d, t, s)
                d += 1
    return best


def min_source(word, t):
    """Least s = r0 + b0 - 1 over legal chains with the ordered arities `word`
    (first level first), any swaps and crops, and retained terminal coordinate t.

    Backward from the last level's output (c, r), which is (1, t) or (t, 1): the
    least parent is (r, b) with b = max(c+1, ceil(((d+2)c + r - 1)/d)), and the
    previous output is (r, b) or (b, r). The least source over the remaining levels
    is nondecreasing in both coordinates, so the least b and the least free
    coordinate are optimal; every larger b is also legal."""
    states = {(1, t), (t, 1)}
    for d in reversed(word):
        new = set()
        for c, r in states:
            b = max(c + 1, -((-((d + 2) * c + r - 1)) // d))
            new.add((r, b))
            new.add((b, r))
        states = new
    return min(r + b - 1 for r, b in states)


def check_min_source(limit=9, depth=2, arities=(2, 3, 4)):
    """Compare min_source with brute force over all chains with r0, b0 <= limit."""
    brute = {}

    def walk(state, word, s):
        if word:
            for t in state:
                key = (word, t)
                brute[key] = min(brute.get(key, s), s)
        if len(word) < depth:
            for x, y in (state, state[::-1]):
                for d in arities:
                    for c in range(1, y):
                        if (d + 2) * c > d * y - x + 1:
                            break
                        walk((c, x), word + (d,), s)

    for r0 in range(1, limit + 1):
        for b0 in range(1, limit + 1):
            walk((r0, b0), (), r0 + b0 - 1)
    checked = 0
    for (word, t), s in brute.items():
        m = min_source(word, t)
        assert m <= s
        if m <= limit:          # the least chain has r0, b0 <= m, inside the brute range
            assert m == s, (word, t, m, s)
            checked += 1
    return checked


def multi_level_search(depth, tmax):
    """Least exact pooled exponent over realized common-model chains of the given
    depth (every ordering, largest types, A <= 2^128, t <= tmax)."""
    from itertools import product as iproduct
    best = None
    for n in range(3, 65):
        ar = [d for d in range(2, 2 * n + 1) if gains(n, d)]
        for k in range(1, 64 // n + 1):
            for word in iproduct(ar, repeat=depth):
                prod = 1
                for d in word:
                    prod *= d
                if prod ** (2 * n * k) > CAP:
                    continue
                Ms = [mmax(n, d) for d in word]
                num0 = sum(6 * k * (ln_int(2 * M - 1) - ln_int(M)) + ln_int(1 + 6 * k * (M - 1))
                           for M in Ms)
                den0 = sum(2 * k * ln_int(M) - 2 * n * k * ln_int(d) for M, d in zip(Ms, word))
                for t in range(1, tmax + 1):
                    s = min_source(word, t)
                    den = 2 * n * k * ln_int(t) + den0
                    if den <= 0:
                        continue
                    p = (6 * n * k * ln_int(s) + num0) / den
                    if best is None or p < best[0]:
                        best = (p, n, k, word, t, s)
    return best


def sharp_minimum(crows, brow, c_local, b_local, p_w, T0=400):
    """Evidence that the witness exponent p_w is the exact minimum of both models.

    (a) At the rational p_hi > p_w, every multiset left open by the relaxation is
        a forced one-level case. Relaxed margins decrease in p0, so every other
        chain has p > p_hi > p_w.
    (b) A forced case is a one-level chain. A one-level blocked chain with block
        (n1, k1) is the common one-level scheme with (n, k) = (n1, k1) raised to
        the power P/(n1 k1), so it has the same exponent. Every one-level common
        chain with A <= 2^128, gaining (n, d), largest type (Lemma 8) and least
        source (Lemma 4, exponent increases in s) and t <= T0 has exponent >= p_w.
    (c) For t > T0 the one-level real-t margin at p_hi is increasing (T0 >= t*)
        and positive at T0, so those chains have p > p_hi."""
    p_hi = D("2.976961")
    assert p_w < p_hi
    _, cneg = screen(crows, c_local, "common", p_hi)
    _, bneg = screen(brow, b_local, "blocked", p_hi)
    assert all(len(w) == 1 and 4 * key[0] * key[1] > CAP_BITS for key, w, _ in cneg)
    assert all(len(w) == 1 and 4 * key > CAP_BITS for key, w, _ in bneg)
    ranked = []
    for n in range(1, 65):
        for k in range(1, 64 // n + 1):
            d = 2
            while d ** (2 * n * k) <= CAP and d <= 2 * n:   # Lemma 6: no gain for d > 2n
                if gains(n, d):
                    M = mmax(n, d)
                    for t in range(1, T0 + 1):
                        s = -((-((d + 1) * t + 1)) // d)
                        ranked.append((factored_exponent(n, k, d, M, s, t), n, k, d, t, s))
                    a, c = D(d + 1) / d, D(1) / d
                    assert p_hi * c / ((3 - p_hi) * a) <= T0
                    tail = (3 * (a * T0 + c).ln() - p_hi * D(T0).ln()
                            + local_cost(n, d, k, M, p_hi))
                    assert classify(tail) > 0, (n, k, d)
                d += 1
    ranked.sort()
    assert ranked[0][1:] == (32, 2, 2, 43, 65) and abs(ranked[0][0] - p_w) < PAD
    assert ranked[1][0] > p_w + PAD
    return len(cneg), len(bneg), ranked[:4]


def sharp_minimum_intervals(T0=400):
    """Second, outward-rounded certificate of the sharpness claim.

    Uses the checker's 200-bit outward-rounded logarithm intervals (reviewed in
    the adversarial note), loaded by file path; the producers are not imported."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "checker_gate", "experiments/shifted_chains_check_gate.py")
    ck = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ck)
    p_hi = Fraction(2976961, 1000000)

    def exponent_interval(n, k, d, M, s, t):
        L = ck.log_int
        num = ck.iadd(ck.iscale(L(s), 6 * n * k), ck.iscale(ck.isub(L(2 * M - 1), L(M)), 6 * k),
                      L(1 + 6 * k * (M - 1)))
        den = ck.iadd(ck.iscale(L(t), 2 * n * k), ck.iscale(L(M), 2 * k),
                      ck.iscale(L(d), -2 * n * k))
        assert den[0] > 0 and num[0] > 0
        return Fraction(num[0], den[1]), Fraction(num[1], den[0])

    w_lo, w_hi = exponent_interval(32, 2, 2, ck.m_max(32, 2), 65, 43)
    assert Fraction(2976960882, 10 ** 9) < w_lo <= w_hi < Fraction(2976960883, 10 ** 9) < p_hi
    common = ck.run_common((p_hi,))
    blocked, _ = ck.run_blocked((p_hi,))
    assert ck.forced_one_level(common, blocked, p_hi)
    runner_up = None
    for n in range(1, 65):
        for k in range(1, 64 // n + 1):
            d = 2
            while d ** (2 * n * k) <= CAP and d <= 2 * n:
                if ck.gains(n, d):
                    M = ck.m_max(n, d)
                    for t in range(1, T0 + 1):
                        if (n, k, d, t) == (32, 2, 2, 43):
                            continue
                        s = -((-((d + 1) * t + 1)) // d)
                        lo, _ = exponent_interval(n, k, d, M, s, t)
                        assert lo > w_hi, (n, k, d, t)
                        if runner_up is None or lo < runner_up[0]:
                            runner_up = (lo, n, k, d, t, s)
                    a, c = Fraction(d + 1, d), Fraction(1, d)
                    assert p_hi * c / ((3 - p_hi) * a) <= T0
                    tail = ck.iadd(ck.isub(ck.iscale(ck.log_rat(a * T0 + c), 3),
                                           ck.iscale(ck.log_rat(Fraction(T0)), p_hi)),
                                   ck.local_cost(n, d, k, p_hi))
                    assert tail[0] > 0, (n, k, d)
                d += 1
    return (len(common["gates"][str(p_hi)]["unexcluded"]),
            len(blocked["gates"][str(p_hi)]["unexcluded"]),
            (w_lo, w_hi), runner_up)


def main():
    out = {}
    out["identity_d_checked"] = check_identity()
    out["chains"] = check_chains()
    out["one_level_large_cases"] = check_one_level_large()
    out["local_lemma_cases"] = check_local_lemmas()
    out["blocked_local_cases"] = check_blocked_local()
    print("1. identity (d=2..400):", out["identity_d_checked"], "arities")
    print("2. chain geometry:", out["chains"], "; Lemma 4 large one-level cases:",
          out["one_level_large_cases"])
    print("3. local lemmas (all types):", out["local_lemma_cases"],
          "; blocked physical blocks vs screen:", out["blocked_local_cases"])

    pairs, crow, by_nk = common_rows()
    actions, brow, by_P = blocked_rows()
    saved_c = json.loads(Path("results/round11-variable-finite-gate.json").read_text())["screen"]
    saved_b = json.loads(Path("results/round11-blocked-finite-gate.json").read_text())["screen"]
    assert len(pairs) == 219 and len(crow) == 1752 and by_nk == saved_c["counts_by_n_k"]
    assert max(len(w) for _, _, w in crow) == 21
    assert len(actions) == 219 and len(brow) == 1326 and by_P == saved_b["counts_by_P"]
    assert sum(len(v) for v in actions.values()) == 3744
    assert max(len(w) for _, w in brow) == 21
    print("4. census: common", len(pairs), "pairs,", len(crow), "multisets; blocked",
          len(actions), "actions,", sum(len(v) for v in actions.values()), "choices,",
          len(brow), "multisets; per-(n,k) and per-P counts match the receipts")

    crows = [((n, k), w) for n, k, w in crow]

    def c_local(key, d, p):
        n, k = key
        return local_cost(n, d, k, mmax(n, d), p)

    blocal_cache = {}

    def b_local(P, d, p):
        if (P, d, p) not in blocal_cache:
            blocal_cache[P, d, p] = min(local_cost(n, d, P // n, mmax(n, d), p)
                                        for n in actions[P, d])
        return blocal_cache[P, d, p]

    thresholds = [("29/10", D("2.9")), ("59/20", D("2.95")), ("119/40", D("2.975")),
                  ("5953/2000", D("2.9765")), ("2.9769", D("2.9769"))]
    for name, p in thresholds:
        cbest, cneg = screen(crows, c_local, "common", p)
        bbest, bneg = screen(brow, b_local, "blocked", p)
        line = (f"5. p={name}: common min {cbest[0]:.22f} at {cbest[1:]}, open {len(cneg)}; "
                f"blocked min {bbest[0]:.22f} at {bbest[1:]}, open {len(bneg)}")
        print(line)
        # Forced one level and the one-level closure.
        c_close = []
        for (n, k), w, _ in cneg:
            forced = len(w) == 1 and 4 * n * k > CAP_BITS
            m1 = one_level_endpoint(w[0], p) + c_local((n, k), w[0], p) if len(w) == 1 else None
            c_close.append(((n, k), w, forced, m1))
        b_close = []
        for P, w, _ in bneg:
            forced = len(w) == 1 and 4 * P > CAP_BITS
            m1 = one_level_endpoint(w[0], p) + b_local(P, w[0], p) if len(w) == 1 else None
            b_close.append((P, w, forced, m1))
        all_forced = all(x[2] for x in c_close) and all(x[2] for x in b_close)
        closed = all(x[3] is not None and classify(x[3]) > 0 for x in c_close + b_close)
        mins = [min((x[3] for x in c_close), default=None), min((x[3] for x in b_close), default=None)]
        print(f"   open cases all forced one-level: {all_forced}; all closed by Lemma 4: {closed};"
              f" smallest Lemma-4 margins (common, blocked): "
              f"{[None if v is None else f'{v:.12f}' for v in mins]}")
        if name == "59/20":
            print("   common open:", [(key, w) for key, w, _ in cneg])
            print("   blocked open:", [(key, w) for key, w, _ in bneg])
            print("   most negative relaxed margin (common, blocked):",
                  f"{min(x[2] for x in cneg):.22f}", f"{min(x[2] for x in bneg):.22f}")
        if name in ("29/10",):
            assert not cneg and not bneg
        if name in ("59/20", "119/40", "5953/2000"):
            assert all_forced and closed

    # Witness.
    n, k, d, s, t = 32, 2, 2, 65, 43
    M = factorial(32) // (factorial(8) * factorial(16) * factorial(8)) * 2 ** 16
    assert M == mmax(32, 2) == 506980245130444800
    A, B, r, m, p = exact_exponent(n, k, d, M, s, t)
    assert A == CAP and len(str(B)) == 280
    print(f"6. witness (43,23), d=2, c=1, n=32, k=2: A=2^128, B has {len(str(B))} digits,"
          f" pooled exponent {p:.15f}")
    best = one_level_search()
    print(f"   best one-level chain with A<=2^128 (t<=400): exponent {best[0]:.15f} at"
          f" (n,k,d,t,s)={best[1:]}")
    _, _, _, _, p_best = exact_exponent(best[1], best[2], best[3], mmax(best[1], best[3]),
                                        best[5], best[4])
    assert abs(p_best - best[0]) < PAD
    assert abs(factored_exponent(n, k, d, M, s, t) - p) < PAD
    nc, nb, top = sharp_minimum(crows, brow, c_local, b_local, p)
    print(f"7. at p_hi=2.976961: {nc} common and {nb} blocked open cases, all forced one-level;"
          f" every one-level chain has exponent >= the witness's. Smallest one-level exponents:")
    for row in top:
        print(f"     {row[0]:.15f} at (n,k,d,t,s)={row[1:]}")
    nc2, nb2, (w_lo, w_hi), ru = sharp_minimum_intervals()
    print(f"   outward-rounded repeat: {nc2} common and {nb2} blocked open cases at 2976961/10^6,"
          f" all forced one-level; witness exponent in [{float(w_lo):.12f}, {float(w_hi):.12f}];"
          f" every other one-level datum has exponent > {float(ru[0]):.9f} at {ru[1:]}")
    n_ms = check_min_source(limit=16, depth=2, arities=(2, 3, 4, 5))
    n_ms += check_min_source(limit=10, depth=3, arities=(2, 3, 4))
    print("8. least-source formula agrees with brute force on", n_ms, "(word, t) cases")
    for depth, tmax in ((2, 300), (3, 150)):
        b = multi_level_search(depth, tmax)
        print(f"   best realized common-model chain of depth {depth} (t<={tmax}):"
              f" exponent {b[0]:.12f} at (n,k,word,t,s)={b[1:]}")
    print("all skeptic checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
