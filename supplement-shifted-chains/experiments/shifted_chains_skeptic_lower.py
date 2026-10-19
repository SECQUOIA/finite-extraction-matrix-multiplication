"""Adversarial exact checks for docs/shifted-chains-check-lower.md (key "lower").

Run from the repository root:

    python -I experiments/shifted_chains_skeptic_lower.py

Independent of the checker's script and of all round-7..16 code.  Every
check uses exact integers or Fractions; logarithms are enclosed in rational
intervals with outward rounding.  Floats appear only in printed summaries.

Parts:
  1. Lemma 1 identity, proved by evaluation on a product grid that exceeds
     the degree in every variable (a different method from the checker's
     symbolic expansion), and the gap identity of Lemma 3.
  2. Exhaustive dynamic programme over EVERY chain with entries <= N, every
     arity d >= 1, every legal child, input swaps and free crops: the
     endpoint inequality s * prod(lambda) >= K t^(4/5) (Lemma 2).
  3. Type-count lemma 4 (b), (c), (d), exhaustive on a range.
  4. Constants of Theorem 5 and of the recycling-invariant bound.
  5. Forward recycling of produced auxiliaries (the main finding):
     5a. an exact big-integer instance (bank recursion with floors);
     5b. the four round-11 ramp certificates, with interval logarithms;
     5c. the round11-ramp-bounds schedule at small allowances.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from math import comb, isqrt

sys.set_int_max_str_digits(0)

# ---------------------------------------------------------------------------
# Part 1: algebraic identities.


def Qf(x, y):
    return x * x + 4 * x * y + y * y


def lemma1_defect(q, lam, R, B):
    """q^3 * [lam^2 Q(R,B) - Q((dB-R)/q, R) - (1-beta^2)(R-lam B)^2
               - (f(lam)/q) (2R^2 + (4-2beta) R B + (lam beta + d/q) B^2)],
    with d=q-2, beta=lam+1/q, f(x)=q x^2 + x - d.  Claimed identically 0."""
    q, lam, R, B = F(q), F(lam), F(R), F(B)
    d = q - 2
    beta = lam + 1 / q
    f = q * lam * lam + lam - d
    val = (lam * lam * Qf(R, B) - Qf((d * B - R) / q, R)
           - (1 - beta * beta) * (R - lam * B) ** 2
           - (f / q) * (2 * R * R + (4 - 2 * beta) * R * B
                        + (lam * beta + d / q) * B * B))
    return q ** 3 * val


def check_lemma1_identity():
    """q^3*defect is a polynomial with deg_q<=3, deg_lam<=4, deg_R<=2,
    deg_B<=2.  A polynomial vanishing on a product grid with more points
    than its degree in each variable is zero.  Use 6 points per variable."""
    qs = [1, 2, 3, 5, 7, 11]
    lams = [F(-2), F(-1, 3), 0, F(1, 2), F(3, 4), 2]
    Rs = [F(-1), 0, F(2, 3), 1, F(5, 2), 4]
    Bs = [F(-3), F(1, 5), 0, 1, F(7, 3), 6]
    n = 0
    for q in qs:
        for lam in lams:
            for R in Rs:
                for B in Bs:
                    assert lemma1_defect(q, lam, R, B) == 0
                    n += 1
    # crop condition equivalence: (d+2)c <= d b - r + 1  <=>  q C <= d B - R
    for d in range(1, 30):
        q = d + 2
        for r in range(1, 25):
            for b in range(1, 25):
                for c in range(1, 25):
                    lhs = (d + 2) * c <= d * b - r + 1
                    rhs = q * (c - F(1, 3)) <= d * (b - F(1, 3)) - (r - F(1, 3))
                    assert lhs == rhs
    return n


def check_gap_identity():
    """(1-z^4) f(z^3) = z^3 (1-z)^2 (1-z^2) with q=2/(1-z^4), d=q-2.
    Left side times nothing is a polynomial of degree 7 in z once q is
    substituted; check at 12 rational points of (0,1)."""
    for j in range(1, 13):
        z = F(j, 13)
        q = 2 / (1 - z ** 4)
        d = q - 2
        assert d == q * z ** 4
        f = q * z ** 6 + z ** 3 - d
        assert (1 - z ** 4) * f == z ** 3 * (1 - z) ** 2 * (1 - z * z)
    return True


def check_terminal_polynomial():
    """Lemma 2 end bound, recomputed: with u=t-1,
    (4/9)^5 (u^2+4u+8/3)^5 - (21/20)^10 (u+1)^8 has only positive
    coefficients, so Phi(1,t) >= (21/20) t^(4/5) for t >= 1."""
    def mul(a, b):
        out = [F(0)] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] += x * y
        return out
    base, pw = [F(8, 3), F(4), F(1)], [F(1)]
    for _ in range(5):
        pw = mul(pw, base)
    lin, pw8 = [F(1), F(1)], [F(1)]
    for _ in range(8):
        pw8 = mul(pw8, lin)
    K10 = F(21, 20) ** 10
    coeffs = [F(4, 9) ** 5 * pw[i] - (K10 * pw8[i] if i < len(pw8) else 0)
              for i in range(len(pw))]
    assert len(coeffs) == 11 and all(c > 0 for c in coeffs)
    # and Q(2/3, t-1/3) = t^2 + 2t - 1/3 as polynomials (check 3 points)
    for t in (F(1), F(5, 2), F(7)):
        assert Qf(F(2, 3), t - F(1, 3)) == t * t + 2 * t - F(1, 3)
    return float(min(coeffs))


# ---------------------------------------------------------------------------
# Rational enclosures.

def lam_bounds(d, bits=96):
    """lam_d = (sqrt(1+4d(d+2)) - 1)/(2(d+2)), enclosed in [lo, hi]."""
    q = d + 2
    disc = 1 + 4 * d * q
    s = isqrt(disc << (2 * bits))
    lo = F(s - (1 << bits), 2 * q << bits)
    hi = F(s + 1 - (1 << bits), 2 * q << bits)
    f = lambda x: q * x * x + x - d
    assert f(lo) <= 0 <= f(hi)
    return lo, hi


def round_down(x, bits=110):
    """Largest dyadic <= x with about `bits` significant bits (x >= 0)."""
    if x == 0:
        return F(0)
    num, den = x.numerator, x.denominator
    e = bits - (num.bit_length() - den.bit_length())
    if e >= 0:
        return F((num << e) // den, 1 << e)
    return F((num // (den << (-e))) << (-e))


# ---------------------------------------------------------------------------
# Part 2: exhaustive endpoint check.

def check_endpoint_exhaustive(N=60):
    """For every unordered pair {u,v} (u<=v<=N) admitting a legal step,
    G(u,v) = min over all chains of >=1 legal steps (any arity, swaps,
    crops, free crops, terminal t<=max) of prod(lam_lo^5)/t^4.
    Check s^5 G >= K^5 with s=u+v-1.  Since lambda_d increases with d, the
    smallest legal arity of a step is the worst case; this is asserted on
    the enclosures.  Returns the minimal margin s^5 G / K^5."""
    K5 = F(21, 20) ** 5
    maxd = 3 * N + 3
    lam = {d: lam_bounds(d) for d in range(1, maxd + 2)}
    for d in range(1, maxd + 1):
        assert lam[d][1] < lam[d + 1][0]  # strictly increasing in d
    lam5 = {d: round_down(lam[d][0] ** 5) for d in lam}
    INF = None
    G = {}
    Mn = {}  # min of G over the dominated region {(a,b): a<=b, a<=u, b<=v}

    def H(u, v):  # best continuation after arriving at sorted pair (u,v)
        stop = F(1, v ** 4)
        m = Mn.get((u, v))
        return stop if m is None or stop <= m else m

    worst = None
    order = sorted(((u, v) for v in range(1, N + 1) for u in range(1, v + 1)),
                   key=lambda p: (p[0] + p[1], p[0]))
    for (u, v) in order:
        best = INF
        for r, b in ((u, v), (v, u)):
            for c in range(1, b):
                need = 2 * c + r - 1  # d (b-c) >= 2c + r - 1
                dmin = max(1, -(-need // (b - c)))
                if dmin > maxd:
                    continue
                assert (dmin + 2) * c <= dmin * b - r + 1
                assert dmin == 1 or (dmin + 1) * c > (dmin - 1) * b - r + 1
                cu, cv = min(c, r), max(c, r)
                val = round_down(lam5[dmin] * H(cu, cv))
                if best is None or val < best:
                    best = val
        if best is not None:
            G[(u, v)] = best
            s = u + v - 1
            margin = s ** 5 * best / K5
            assert margin >= 1, (u, v, float(margin))
            if worst is None or margin < worst[0]:
                worst = (margin, (u, v))
        cands = [x for x in (G.get((u, v)),
                             Mn.get((u - 1, v)) if u > 1 else None,
                             (Mn.get((u, v - 1)) if u <= v - 1 else Mn.get((v - 1, v - 1)))
                             if v > 1 else None) if x is not None]
        if cands:
            Mn[(u, v)] = min(cands)
    return len(G), float(worst[0]), worst[1]


# ---------------------------------------------------------------------------
# Part 3: type counts.

def type_count(n, d, l, o):
    return comb(n, l) * comb(n - l, o) * (d - 1) ** l * 2 ** o


def check_type_lemmas(nmax=40, dmax=90):
    cnt = 0
    for n in range(1, nmax + 1):
        for d in range(2, dmax + 1):
            q = d + 2
            Ms = [type_count(n, d, l, o) for l in range(n + 1) for o in range(n - l + 1)]
            assert sum(Ms) == q ** n
            Mx = max(Ms)
            l0, o0, _ = mode_type(n, d)
            assert type_count(n, d, l0, o0) == Mx  # mode_type is exact
            assert Mx * (n + 1) ** 2 >= q ** n  # max >= average (ramp-bounds (8))
            if Mx > d ** n:
                assert n >= 3 and d <= 2 * n          # 4(b)
            if n >= 3 and d <= 2 * n:
                assert 2 * Mx <= q ** n                # 4(c)
            if n >= 2 * q:
                assert 1000 * n * Mx <= 10874 * q ** (n + 1)   # 4(d), 4e < 10.874
            cnt += 1
    # 4(d) for larger n, by exhaustive maximisation over all types.
    big = 0
    for d in (2, 3, 5, 9, 17):
        q = d + 2
        for n in (2 * q, 2 * q + 1, 5 * q, 13 * q + 2, 150, 240):
            if n < 2 * q:
                continue
            Mx = max(type_count(n, d, l, o) for l in range(n + 1) for o in range(n - l + 1))
            assert 1000 * n * Mx <= 10874 * q ** (n + 1)
            big += 1
    return cnt, big


# ---------------------------------------------------------------------------
# Interval logarithms (fixed point, outward rounded).

W = 300


def _atanh_fp(a, b):
    """[lo, hi] integers with lo <= 2^W atanh(a/b) <= hi, 0 <= a/b <= 1/3."""
    assert 0 <= 3 * a <= b
    if a == 0:
        return 0, 0
    tot, j, num, den = 0, 0, a, b
    a2, b2 = a * a, b * b
    while True:
        tot += (num << W) // (den * (2 * j + 1))
        j += 1
        num *= a2
        den *= b2
        if (num << W) * 9 < den * 8:  # tail < (9/8) z^(2j+1) < 1 unit
            break
    return tot, tot + j + 1


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    def __sub__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(self.lo - o.hi, self.hi - o.lo)

    def sc(self, c):
        c = F(c)
        return Iv(self.lo * c, self.hi * c) if c >= 0 else Iv(self.hi * c, self.lo * c)


_t = _atanh_fp(1, 3)
LN2 = Iv(F(2 * _t[0], 1 << W), F(2 * _t[1], 1 << W))
_cache = {}


def ln(N):
    """Interval for log N, N a positive integer."""
    if N in _cache:
        return _cache[N]
    assert N >= 1
    if N == 1:
        res = Iv(0)
    elif N.bit_length() <= 200:
        e = N.bit_length() - 1
        lo, hi = _atanh_fp(N - (1 << e), N + (1 << e))
        res = Iv(F(2 * lo, 1 << W), F(2 * hi, 1 << W)) + LN2.sc(e)
    else:
        e = N.bit_length() - 200
        m = N >> e
        res = Iv(ln(m).lo, ln(m + 1).hi) + LN2.sc(e)
    if N.bit_length() <= 1000:
        _cache[N] = res
    return res


def lnq(x):
    x = F(x)
    return ln(x.numerator) - ln(x.denominator)


# ---------------------------------------------------------------------------
# Part 4: constants.

def check_constants():
    out = {}
    lnK = lnq(F(21, 20))
    assert lnK.lo > F(1, 21)
    # Theorem 5 (checker's recommended form): 27 lnK/(1024*96^(3/2)) > 1e-6.
    assert 96 ** 3 < 960 ** 2
    c96 = F(27, 21 * 1024 * 960)
    assert c96 > F(1, 10 ** 6)
    out["thm5_coef_lower"] = str(c96)
    # Round-11 form: 27 lnK/(1024*192^(3/2)) > 1e-7.
    assert 192 ** 3 < 2688 ** 2
    c192 = F(27, 21 * 1024 * 2688)
    assert c192 > F(1, 10 ** 7)
    # Recycling-invariant bound: log(B/A) > (45/8) P lnK / eps with
    # P > 9 x^2 / (24576 eps^3)  ==>  log(B/A) > (405/196608) lnK eps^-4 x^2.
    assert F(6) * F(9, 4) / F(12, 5) == F(45, 8)
    assert F(9, 256) * F(1, 96) == F(9, 24576)
    cB = F(45, 8) * F(9, 24576)
    assert cB == F(405, 196608)
    cBlow = cB / 21
    assert cBlow > F(98, 10 ** 6)
    out["logB_coef_lower"] = str(cBlow)
    # Cutoffs for eps <= 2^-14: 3/20, 9/64, 9/16384, 1/9216.
    e = F(1, 2 ** 14)
    assert e <= F(3, 20) and e <= F(9, 64) and e <= F(9, 16384) and e < F(1, 9216)
    return out


# ---------------------------------------------------------------------------
# Part 5: forward recycling.

def mode_type(n, d):
    """Exact maximiser of the type count: the n largest marginals
    w_j/t (t=1,2,...) of the weights w=(d-1,2,1).  At most n marginals
    exceed q/n, so all of them belong to the top n; start from those and
    finish greedily (ties do not change the count)."""
    w = (d - 1, 2, 1)
    q = d + 2
    a = [max(0, -(-(n * wj) // q) - 1) if wj > 0 else 0 for wj in w]
    assert sum(a) <= n
    while sum(a) < n:
        j = max(range(3), key=lambda i: F(w[i], a[i] + 1))
        a[j] += 1
    return a


def ramp_chain(D, L):
    """round11-arity-ramp: reverse steps from (1,1), arities 3j-1, 3j for
    j<R=8D, then L steps of arity D; returned in forward order."""
    R = 8 * D
    rev = []
    for j in range(1, R):
        rev += [3 * j - 1, 3 * j]
    rev += [D] * L
    pairs = [(1, 1)]
    for d in rev:
        r, b = pairs[-1]
        pairs.append((b, -(-((d + 2) * r + b - 1) // d)))
    pairs.reverse()
    ar = list(reversed(rev))
    for i, d in enumerate(ar):
        (rp, bp), (c, r2) = pairs[i], pairs[i + 1]
        assert r2 == rp and c >= 1 and (d + 2) * c <= d * bp - rp + 1
    return pairs, ar


def check_recycling_exact(D=2, L=20, n=200, k=2, X=40):
    """Exact integers.  Class scheme: A = prod d_i^(2P), B = prod M_i^(2k).
    Recycled scheme: source S = 2^X d_1^(2P); bank beta_0 = S,
    beta_i = floor(beta_{i-1}/U_i) V_i with U_i = d_i^(2P), V_i = M_i^(2k);
    target B' = beta_J (terminal t=1).  r_*, m_* are unchanged."""
    pairs, ar = ramp_chain(D, L)
    P = n * k
    Ms = {}
    for d in set(ar):
        l, o, m = mode_type(n, d)
        Ms[d] = type_count(n, d, l, o)
    A, B = 1, 1
    for d in ar:
        A *= d ** (2 * P)
        B *= Ms[d] ** (2 * k)
    assert B > A
    S = (1 << X) * ar[0] ** (2 * P)
    bank = S
    for d in ar:
        U = d ** (2 * P)
        assert bank >= (1 << X) * U  # every auxiliary is available
        bank = (bank // U) * Ms[d] ** (2 * k)
    A2, B2 = S, bank
    J = len(ar)
    # B'/A' <= B/A and B'/A' >= (B/A)(1 - J 2^-X):
    assert B2 * A <= B * A2
    assert B2 * A * (1 << X) >= B * A2 * ((1 << X) - J)
    import math
    return dict(levels=J, P=P, digits_A=len(str(A)), digits_A_recycled=len(str(A2)),
                log_ratio_loss_upper=float(F(J, 1 << X)),
                logBA=float(math.log(B) - math.log(A)),
                logBA_recycled=float(math.log(B2) - math.log(A2)))


def ramp_scheme_logs(D, L, n, k):
    """Interval logs for the class scheme on the ramp chain (one block per
    level, P = n k, exact mode types, terminal (1,1))."""
    pairs, ar = ramp_chain(D, L)
    P = n * k
    s = pairs[0][0] + pairs[0][1] - 1
    info = {}
    for d in set(ar):
        l, o, m = mode_type(n, d)
        M = type_count(n, d, l, o)
        E = 1 + 6 * k * (M - 1)
        info[d] = dict(lnd=ln(d), lnM=ln(M), lnE=ln(E), sep=ln(2 * M - 1) - ln(M))
    num = ln(s).sc(6 * P)
    den = Iv(0)
    lnA = Iv(0)
    for d in ar:
        x = info[d]
        num = num + x["sep"].sc(6 * k) + x["lnE"]
        den = den + x["lnM"].sc(2 * k) - x["lnd"].sc(2 * P)
        lnA = lnA + x["lnd"].sc(2 * P)
    return ar, info, P, num, den, lnA


def check_recycling_certificates():
    rows = []
    for D, L, n, k in [(2, 100, 512, 256), (4, 400, 2048, 1024),
                       (8, 1600, 8192, 4096), (16, 3200, 32768, 16384)]:
        ar, info, P, num, den, lnA = ramp_scheme_logs(D, L, n, k)
        assert den.lo > 0
        p_hi = num.hi / den.lo
        J = len(ar)
        X = 64 + J.bit_length()
        # S = 2^(X+1) d_1^(2P); the extra factor 2 absorbs interval rounding.
        lnS = LN2.sc(X + 1) + info[ar[0]]["lnd"].sc(2 * P)
        ell = lnS.lo                      # lower bound for log(bank)
        tiny = F(2, 1 << X)               # -log(1-u) <= 2u for u <= 1/2
        for d in ar:
            lnU = info[d]["lnd"].sc(2 * P)
            assert ell >= lnU.hi + LN2.hi * X   # bank >= 2^X U_i
            ell = ell - lnU.hi + info[d]["lnM"].sc(2 * k).lo - tiny
        den2_lo = ell - lnS.hi            # log(B'/A') >= this (t = 1)
        assert den2_lo > 0
        p2_hi = num.hi / den2_lo
        ln10 = lnq(10)
        rows.append(dict(D=D, levels=J, pooled_p_upper=float(p_hi),
                         recycled_p_upper=float(p2_hi),
                         p_increase_upper=float(p2_hi - num.lo / den.hi),
                         digits_A=float(lnA.hi / ln10.lo),
                         digits_A_recycled=float(lnS.hi / ln10.lo),
                         ratio=float(lnA.lo / lnS.hi)))
        assert p2_hi - p_hi < F(1, 10 ** 12)
    return rows


def check_ramp_bounds_schedule(eps):
    """round11-ramp-bounds schedule (6), recycled.  Checks, with exact
    arithmetic, that the source S = 2^(X+1) D^(2nk) funds every level with
    bank >= 2^X U_i (using only M_i >= q_i^n/(n+1)^2), and compares
    log A' = (X+1) log 2 + 2nk log D, and an upper bound for log B', with
    the class lower bounds 1e-7 eps^-9/2 x^3 and with the
    recycling-invariant lower bound (45/458752) eps^-4 x^2.  The exponent
    claim of round11-ramp-bounds itself is NOT re-checked here."""
    eps = F(eps)
    # D = ceil(sqrt(4/eps)) with an exact integer test
    D = isqrt(int(4 / eps))
    while F(D * D) < 4 / eps:
        D += 1
    L = -((-64 * D * eps.denominator) // eps.numerator)
    assert F(L) >= 64 * D / eps > L - 1
    xx = 128 * D / eps
    H = (-((-xx.numerator) // xx.denominator)).bit_length()
    n = k = -((-256 * D * H * eps.denominator) // eps.numerator)
    R = 8 * D
    J = 2 * (R - 1) + L
    maxd = 3 * R - 3
    assert maxd < 24 * D
    X = 64 + J.bit_length() + (eps.denominator // eps.numerator).bit_length()
    lnn1 = ln(n + 1)
    # (a) every level has V_i >= U_i * exp(2k*margin), margin > 0:
    gmin = ln(24 * D + 2) - ln(24 * D)  # g_d >= g_{24D} for d < 24D
    margin = gmin.sc(n).lo - lnn1.sc(2).hi
    assert 2 * k * margin > 1  # each level multiplies the bank by > e (1 - 2^-X)
    # (b) the jump from bulk arity D to the first ramp arity 3R-3 is funded:
    gD = ln(D + 2) - ln(D)
    bulk_gain = (gD.sc(n).lo - lnn1.sc(2).hi) * 2 * k - F(2, 1 << X)
    need = (ln(maxd) - ln(D)).sc(2 * n * k).hi
    assert bulk_gain * L >= need
    # Ramp arities decrease after the jump, so (a) carries the induction.
    lnA2 = LN2.sc(X + 1) + ln(D).sc(2 * n * k)
    x = lnq(1 / eps)
    # eps^(-9/2) = eps^-4 * eps^(-1/2); eps is an even power of 1/2 below.
    r = isqrt(eps.denominator // eps.numerator)
    assert F(r * r) == 1 / eps
    em92 = (1 / eps) ** 4 * r
    lb7 = x.lo ** 3 * em92 / 10 ** 7
    lb6 = x.lo ** 3 * em92 / 10 ** 6
    # class log A for the same schedule is at least 2nk L log D:
    lnA_class_lo = ln(D).sc(2 * n * k * L).lo
    # Target side.  log(B/A) <= 2nk sum_i g_i = 2nk (L g_D + log F_R), and
    # log F_R = log((3R-1)/2) + sum_{j<R} log(1+1/(3j)) <= log(3R/2) + (1+log R)/3.
    logBA_hi = (gD.sc(L) + lnq(F(3 * R, 2)) + (Iv(1) + ln(R)).sc(F(1, 3))).sc(2 * n * k).hi
    logB2_hi = logBA_hi + lnA2.hi
    robust = F(45, 458752) * x.lo ** 2 * (1 / eps) ** 4  # 9.8e-5 eps^-4 x^2
    return dict(eps_log2=-(eps.denominator.bit_length() - 1), D=D, L=L, n=n, levels=J,
                logA_recycled_upper=float(lnA2.hi),
                logA_recycled_over_1e7_bound=float(lnA2.hi / lb7),
                logA_recycled_over_1e6_bound=float(lnA2.hi / lb6),
                logA_class_over_1e7_bound=float(lnA_class_lo / lb7),
                logB_recycled_upper=float(logB2_hi),
                logB_recycled_over_1e7_bound=float(logB2_hi / lb7),
                logB_recycled_over_robust_lower=float(logB2_hi / robust))


# ---------------------------------------------------------------------------

def main():
    print("Lemma 1 identity: grid points checked =", check_lemma1_identity())
    print("Lemma 3 gap identity:", check_gap_identity())
    print("Lemma 2 terminal polynomial, smallest coefficient:", check_terminal_polynomial())
    print("Lemma 2 exhaustive DP (pairs with a legal step, min margin, at):",
          check_endpoint_exhaustive())
    print("Lemma 4 checks (small, large):", check_type_lemmas())
    print("constants:", check_constants())
    print("recycling, exact instance:", check_recycling_exact())
    for row in check_recycling_certificates():
        print("recycling, ramp certificate:", row)
    for e in (F(1, 2 ** 40), F(1, 2 ** 60), F(1, 2 ** 80), F(1, 2 ** 120), F(1, 2 ** 160)):
        print("recycling, ramp-bounds schedule:", check_ramp_bounds_schedule(e))
    print("all skeptic checks passed")


if __name__ == "__main__":
    main()
