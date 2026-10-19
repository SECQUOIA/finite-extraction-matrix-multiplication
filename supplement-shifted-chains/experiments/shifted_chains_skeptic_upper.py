"""Adversarial re-check of topic "upper" (uniform bound with the arity ramp).

Written independently of experiments/shifted_chains_check_upper.py and of
all round-11 producers; nothing from the repository is imported.

Exact arithmetic only.  Logarithms are enclosed by a method different from
the checker's: ln 2 from sum 1/(k 2^k), and ln y for y in [2/3, 4/3) from the
alternating series of ln(1+u) with an explicit tail bound.  Intervals are
pairs of integers at the fixed scale 2^F, rounded outward.  Floats appear
only in printed summaries, never in an assertion.

Run from the repository root:

    python -I experiments/shifted_chains_skeptic_upper.py          # full
    python -I experiments/shifted_chains_skeptic_upper.py --quick  # smaller
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, isqrt

# ---------------------------------------------------------------------------
# Interval logarithms at scale 2^F.
# ---------------------------------------------------------------------------

F = 288
S = 1 << F


def cdiv(a: int, b: int) -> int:
    return -((-a) // b)


class IV:
    """Interval [lo/2^F, hi/2^F] with integer lo <= hi."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo: int, hi: int):
        assert lo <= hi
        self.lo, self.hi = lo, hi

    @staticmethod
    def exact(x) -> "IV":
        x = Q(x)
        return IV((x.numerator << F) // x.denominator,
                  cdiv(x.numerator << F, x.denominator))

    def __add__(self, o):
        o = o if isinstance(o, IV) else IV.exact(o)
        return IV(self.lo + o.lo, self.hi + o.hi)

    def __sub__(self, o):
        o = o if isinstance(o, IV) else IV.exact(o)
        return IV(self.lo - o.hi, self.hi - o.lo)

    def scale(self, c) -> "IV":
        c = Q(c)
        a, b = c.numerator, c.denominator
        if a >= 0:
            return IV((self.lo * a) // b, cdiv(self.hi * a, b))
        return IV((self.hi * a) // b, cdiv(self.lo * a, b))

    @property
    def qlo(self) -> Q:
        return Q(self.lo, S)

    @property
    def qhi(self) -> Q:
        return Q(self.hi, S)


def _ln2() -> IV:
    K = F + 16
    lo = hi = 0
    for k in range(1, K + 1):
        lo += S // (k << k)
        hi += cdiv(S, k << k)
    hi += cdiv(S, (K + 1) << K)          # tail sum_{k>K} 1/(k 2^k)
    return IV(lo, hi)


LN2 = _ln2()


def _ln1p(a: int, b: int, upper: bool) -> int:
    """Bound on 2^F ln(1 + a/b) for |a/b| <= 0.34 (lower, or upper)."""
    assert b > 0 and 100 * abs(a) <= 34 * b
    neg = a < 0
    A = abs(a)
    plo = phi = S                           # bounds on 2^F |u|^0
    total = 0
    k = 0
    while True:
        k += 1
        plo = (plo * A) // b
        phi = cdiv(phi * A, b)
        positive_term = (not neg) and (k % 2 == 1)
        if neg:
            positive_term = False           # every term of ln(1-|u|) is < 0
        if positive_term:
            total += cdiv(phi, k) if upper else plo // k
        else:
            total -= plo // k if upper else cdiv(phi, k)
        if phi < 4:
            # |tail| <= |u|^(k+1) / ((k+1)(1-|u|)) <= 2 |u|^(k+1)/(k+1)
            tail = 2 * cdiv(phi * A, b) + 2
            return total + tail if upper else total - tail


def ln(x) -> IV:
    """Outward enclosure of ln x for a positive rational (or int) x."""
    x = Q(x)
    num, den = x.numerator, x.denominator
    assert num > 0
    e = num.bit_length() - den.bit_length()
    # want 2/3 <= num/(den 2^e) < 4/3
    def ratio_ge(c_num, c_den, e):         # num/(den 2^e) >= c ?
        if e >= 0:
            return num * c_den >= c_num * (den << e)
        return (num << -e) * c_den >= c_num * den
    while not ratio_ge(2, 3, e):
        e -= 1
    while ratio_ge(4, 3, e):
        e += 1
    G = F + 24
    # y = num/(den 2^e); enclose y in [ylo, yhi] with denominator 2^G.
    if e >= 0:
        yn, yd = num << G, den << e
    else:
        yn, yd = (num << G) << -e, den
    ylo = yn // yd
    yhi = cdiv(yn, yd)
    T = 1 << G
    lo = _ln1p(ylo - T, T, upper=False)
    hi = _ln1p(yhi - T, T, upper=True)
    core = IV(lo, hi)
    if e >= 0:
        return core + IV(e * LN2.lo, e * LN2.hi)
    return core + IV(e * LN2.hi, e * LN2.lo)


def check_logs():
    """Spot checks of the log routine against exact integer facts."""
    # 0.6931471805599453094172321 < ln 2 < 0.6931471805599453094172322
    assert Q(6931471805599453094172321, 10 ** 25) < LN2.qlo
    assert LN2.qhi < Q(6931471805599453094172322, 10 ** 25)
    for (p, q) in [(3, 2), (10, 1), (7, 5), (1, 1000), (10 ** 40 + 7, 3)]:
        a, b = ln(Q(p, q)), ln(Q(q, p))
        z = a + b                            # ln x + ln(1/x) = 0
        assert z.qlo <= 0 <= z.qhi
        assert z.hi - z.lo < 1 << 40         # width below 2^(40-F)
    # 19/7 < e < 30/11 and e^3 > 20.
    assert ln(Q(19, 7)).qhi < 1 < ln(Q(30, 11)).qlo and ln(20).qhi < 3
    w = ln(2) - LN2
    assert w.qlo <= 0 <= w.qhi
    return float(LN2.qlo)


# ---------------------------------------------------------------------------
# Geometry: legal levels, smallest parents, ramp, bulk.
# ---------------------------------------------------------------------------

def legal(parent, child, d) -> bool:
    """Level of arity d from parent (r,b) to child (c,r): quotient-length form."""
    r, b = parent
    c, r2 = child
    if r2 != r or d < 2 or not (1 <= c < b):
        return False
    quotient = d * b - (d - 1) * c          # length of the image of the chain
    return quotient >= 3 * c + r - 1        # room for the tripling crop


def parent_of(child, d):
    """Smallest parent (b, bh) of child (r, b) for arity d, and the slack."""
    r, b = child
    num = (d + 2) * r + b - 1
    bh = cdiv(num, d)
    return (b, bh), d * bh - num


def check_smallest_parent(rmax, dmax):
    n = 0
    worst = Q(0)
    for d in range(2, dmax + 1):
        for r in range(1, rmax + 1):
            for b in range(1, rmax + 1):
                (pb, bh), e = parent_of((r, b), d)
                assert 0 <= e <= d - 1
                assert legal((pb, bh), (r, b), d)
                # minimality by exhaustive search of all smaller second coordinates
                for t in range(1, bh):
                    assert not legal((pb, t), (r, b), d)
                worst = max(worst, Q(max(pb, bh), max(r, b)))
                n += 1
    assert worst <= Q(5, 2)
    return n, worst


def v5_s(m):
    out = Q(1)
    for h in range(1, m):
        out *= 1 + Q(1, 3 * h)
    return out


def v5_F(m, n):
    a, b = min(m, n), max(m, n)
    return v5_s(a) * (b + Q(a - 1, 2))


def build(D, R, L, start=(1, 1), ramp=True):
    """Reverse construction; returns forward list of (parent, child, d)."""
    pair = start
    steps = []
    if ramp:
        assert start == (1, 1)
        for j in range(1, R):
            for d in (3 * j - 1, 3 * j):
                par, e = parent_of(pair, d)
                assert e == 0
                steps.append((par, pair, d))
                pair = par
        assert pair == (R, R)
    slacks = []
    for _ in range(L):
        par, e = parent_of(pair, D)
        slacks.append(e)
        steps.append((par, pair, D))
        pair = par
    steps.reverse()
    for par, ch, d in steps:
        assert legal(par, ch, d)
    if steps:
        assert steps[-1][1] == (1, 1) or not ramp
    return steps, pair, slacks


def check_ramp(Rmax):
    for R in range(1, Rmax + 1):
        steps, top, _ = build(2, R, 0)
        gain = Q(1)
        for _, _, d in steps:
            gain *= Q(d + 2, d)
        assert top == (R, R) and len(steps) == 2 * (R - 1)
        assert gain == v5_F(R, R) == v5_s(R) * Q(3 * R - 1, 2)
        assert gain ** 3 >= R ** 4
    return Rmax


# Polynomial certificate by interpolation (not by expansion).

def _interp(xs, ys):
    """Coefficients (ascending) of the interpolating polynomial, exact."""
    n = len(xs)
    coeffs = [Q(0)] * n
    for i in range(n):
        basis = [Q(1)]
        denom = Q(1)
        for j in range(n):
            if j == i:
                continue
            basis = [Q(0)] + basis
            for t in range(len(basis) - 1):
                basis[t] -= xs[j] * basis[t + 1]
            denom *= xs[i] - xs[j]
        for t in range(n):
            coeffs[t] += ys[i] * basis[t] / denom
    return coeffs


def check_certificate():
    f = lambda u: (u + 1) * ((3 * u + 4) * (3 * u + 5)) ** 3 \
        - 27 * (u + 2) ** 4 * (3 * u + 2) ** 3
    xs = list(range(9))                      # f has degree <= 7
    c = _interp([Q(x) for x in xs], [Q(f(x)) for x in xs])
    while c and c[-1] == 0:
        c.pop()
    assert c == [4544, 17936, 27324, 20007, 7074, 972], c
    # The induction inequality equals j^3 f(j-1): both sides have degree
    # <= 10 in j, so agreement at 11+ points is an identity.
    for j in range(1, 30):
        lhs = j ** 4 * ((3 * j + 1) * (3 * j + 2)) ** 3 \
            - (j + 1) ** 4 * ((3 * j - 1) * 3 * j) ** 3
        assert lhs == j ** 3 * f(j - 1)
    return [int(x) for x in c]


# Potential identity: affine in (r, b, e), checked coefficientwise in Q(mu).

class QM:
    """a + b mu with D mu^2 = mu + D + 2."""

    def __init__(self, D, a, b=0):
        self.D, self.a, self.b = D, Q(a), Q(b)

    def __add__(self, o):
        o = o if isinstance(o, QM) else QM(self.D, o)
        return QM(self.D, self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, QM) else QM(self.D, o)
        return QM(self.D, self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        o = o if isinstance(o, QM) else QM(self.D, o)
        D = self.D
        c2 = self.b * o.b
        return QM(D, self.a * o.a + c2 * Q(D + 2, D),
                  self.a * o.b + self.b * o.a + c2 * Q(1, D))

    __rmul__ = __mul__

    def zero(self):
        return self.a == 0 and self.b == 0


def check_potential_symbolic(Dmax):
    """V(b, bh) - mu V(r, b) - e/D == 0 for all r, b, e, as affine forms.

    With D bh = (D+2) r + b - 1 + e, the difference is an affine form in
    (r, b, e); all four coefficients must vanish in Q(mu).  Each coefficient
    is a rational function of D of degree <= 2 in a fixed basis, so checking
    D = 2..Dmax (Dmax >= 10) proves the identity for every D >= 2.
    """
    for D in range(2, Dmax + 1):
        mu = QM(D, 0, 1)
        eta = mu - Q(1, D)
        third = Q(1, 3)
        # V(x, y) = eta (x - 1/3) + y - 1/3.  Parent (b, bh), child (r, b).
        # coefficient of r: eta*0 + (D+2)/D - mu*eta
        c_r = QM(D, Q(D + 2, D)) - mu * eta
        # coefficient of b: eta + 1/D - mu*1
        c_b = eta + Q(1, D) - mu
        # coefficient of e: 1/D - 1/D
        c_e = QM(D, 0)
        # constant: -eta/3 - 1/D - 1/3 - mu*(-eta/3 - 1/3)
        c_0 = (eta * (-third)) + Q(-1, D) - third - mu * (eta * (-third) - third)
        assert c_r.zero() and c_b.zero() and c_e.zero() and c_0.zero()
        p = lambda t: D * t * t - t - (D + 2)
        assert p(1 + Q(1, D)) == -1 and p(Q(5, 4) + Q(1, D)) == Q(9 * D - 12, 16)
    return Dmax - 1


def mu_bounds(D):
    """Rational lo < mu < hi, mu = (1 + sqrt(4D^2+8D+1)) / (2D)."""
    Delta = 4 * D * D + 8 * D + 1
    s = isqrt(Delta << (2 * F))
    lo = Q((1 << F) + s, (2 * D) << F)
    hi = Q((1 << F) + s + 1, (2 * D) << F)
    p = lambda t: D * t * t - t - (D + 2)
    assert p(lo) < 0 < p(hi)
    return lo, hi


def ln_mu(D) -> IV:
    lo, hi = mu_bounds(D)
    return IV(ln(lo).lo, ln(hi).hi)


def g_of(D) -> IV:
    return ln_gain(D)


def check_gap(D):
    h = ln_mu(D).scale(3) - g_of(D).scale(Q(9, 4))   # g (omega - 9/4)
    g = g_of(D)
    assert h.qlo >= 0
    assert h.qhi <= g.qlo * Q(27, 32 * (D + 1) ** 2)  # notes
    assert h.qhi <= Q(3, 8 * (D + 1) ** 3)            # review (proved below)
    assert h.qhi <= g.qlo * Q(1, 7 * D * D)           # checker
    assert Q(2, D + 2) <= g.qlo and g.qhi <= Q(2, D)
    return h


@lru_cache(maxsize=None)
def ln_gain(d) -> IV:
    return ln(Q(d + 2, d))


def defect_of(steps, top) -> tuple[IV, IV]:
    s = top[0] + top[1] - 1
    G = IV(0, 0)
    for _, _, d in steps:
        G = G + ln_gain(d)
    return ln(s).scale(3) - G.scale(Q(9, 4)), G


def check_bulk(D, L, R):
    steps, top, slacks = build(D, R, L)
    s = top[0] + top[1] - 1
    # Lemma 3: s < mu^L (9R/4 + D)
    rhs = ln_mu(D).scale(L) + ln(Q(9 * R, 4) + D)
    assert ln(s).qhi < rhs.qlo
    defect, G = defect_of(steps, top)
    assert defect.qhi < 3 + Q(27 * L, 16 * D * (D + 1) ** 2)
    # Lemma 1 growth: s <= 2 (5/2)^J - 1 < 2 * 3^J
    J = len(steps)
    assert 2 * s * 2 ** J <= 4 * 5 ** J - 2 * 2 ** J or J == 0
    return defect


def check_no_ramp(D, L):
    """Bulk started at (1,1): s < mu^L (3/2 + D); defect - 3 ln D."""
    steps, top, _ = build(D, 0, L, ramp=False)
    s = top[0] + top[1] - 1
    rhs = ln_mu(D).scale(L) + ln(Q(3, 2) + D)
    assert ln(s).qhi < rhs.qlo
    defect, _ = defect_of(steps, top)
    return defect - ln(D).scale(3)


# ---------------------------------------------------------------------------
# v5's least profile F as a potential for legal levels (new lemma).
# ---------------------------------------------------------------------------

_S_CACHE = [Q(1), Q(1)]                      # _S_CACHE[m] = s_m


def s_fast(m):
    while len(_S_CACHE) <= m:
        h = len(_S_CACHE) - 1
        _S_CACHE.append(_S_CACHE[-1] * (1 + Q(1, 3 * h)))
    return _S_CACHE[m]


def F_fast(m, n):
    a, b = min(m, n), max(m, n)
    return s_fast(a) * (b + Q(a - 1, 2))


def check_profile_potential(rmax, dmax):
    """(i) d F(r,b) >= (d+2) F(c,r) for every legal level (r,b)->(c,r);
    (ii) equality on every ramp level;
    (iii) on whole chains: prod (d_i+2)/d_i <= F(x_0) and F(x_0)^3 <= s^4,
    so 3 ln s - (9/4) G >= 0 for every legal chain ending at (1,1)."""
    for a in range(1, 60):                  # v5 sanity: F(1,b)=b, symmetry
        assert F_fast(1, a) == a == v5_F(a, 1)
    levels = 0
    for d in range(2, dmax + 1):
        for r in range(1, rmax + 1):
            for b in range(2, rmax + 1):
                for c in range(1, b):
                    if legal((r, b), (c, r), d):
                        assert d * F_fast(r, b) >= (d + 2) * F_fast(c, r)
                        levels += 1
    for j in range(1, 200):
        assert (3 * j - 1) * F_fast(j, j + 1) == (3 * j + 1) * F_fast(j, j)
        assert 3 * j * F_fast(j + 1, j + 1) == (3 * j + 2) * F_fast(j, j + 1)
    chains = 0
    for D in (2, 3, 4, 5):
        for R in (1, 2, 3, 5, 8):
            for L in range(0, 13, 3):
                steps, top, _ = build(D, R, L)
                if min(top) > 4000:
                    continue
                gain = Q(1)
                for _, _, d in steps:
                    gain *= Q(d + 2, d)
                Fx = F_fast(*top)
                s = top[0] + top[1] - 1
                assert gain <= Fx and Fx ** 3 <= s ** 4
                chains += 1
    # random legal chains with random arities and random legal children
    st = 987654321
    for _ in range(300):
        pair = (1, 1)
        gain = Q(1)
        for _ in range(12):
            st = (st * 6364136223846793005 + 1442695040888963407) % 2 ** 64
            d = 2 + st % 9
            par, _ = parent_of(pair, d)
            st = (st * 6364136223846793005 + 1442695040888963407) % 2 ** 64
            par = (par[0], par[1] + st % 3)          # any parent above the least
            assert legal(par, pair, d)
            gain *= Q(d + 2, d)
            pair = par
        if min(pair) <= 4000:
            Fx = F_fast(*pair)
            s = pair[0] + pair[1] - 1
            assert gain <= Fx and Fx ** 3 <= s ** 4
            chains += 1
    return levels, chains


# ---------------------------------------------------------------------------
# Types.
# ---------------------------------------------------------------------------

def sector_count(n, d, l, o):
    return comb(n, l) * comb(n - l, o) * (d - 1) ** l * 2 ** o


@lru_cache(maxsize=None)
def mode(n, d):
    """Maximal type by hill climbing on exact transfer ratios.

    The log of the weight is separable concave in (l, o, m) on the simplex,
    so a type that no single transfer improves is a global maximum.
    """
    w = [d - 1, 2, 1]
    q = d + 2
    c = [n * w[0] // q, n * w[1] // q, 0]
    c[2] = n - c[0] - c[1]
    improved = True
    while improved:
        improved = False
        for a in range(3):
            for b in range(3):
                if a != b and c[a] > 0:
                    # ratio after moving one from a to b: (w_b/(c_b+1)) / (w_a/c_a)
                    if w[b] * c[a] > w[a] * (c[b] + 1):
                        c[a] -= 1
                        c[b] += 1
                        improved = True
    return c[0], c[1], sector_count(n, d, c[0], c[1])


def check_types(nmax, dmax):
    cnt = 0
    for d in range(2, dmax + 1):
        q = d + 2
        for n in range(1, nmax + 1):
            vals = [sector_count(n, d, l, o)
                    for l in range(n + 1) for o in range(n + 1 - l)]
            assert sum(vals) == q ** n
            best = max(vals)
            assert best * (n + 1) ** 2 >= q ** n and best <= q ** n
            assert mode(n, d)[2] == best
            cnt += 1
    return cnt


def check_flattening(D, R, L, ns):
    """Necessary condition for the stage relation (S): no flattening rank
    may increase.  Q_{r,b} has flattening rank (r b (r+b-1))^2 on each leg,
    MM_N has N^2.  For every level and every type of size n:
      (2M-1)^6 (r b (r+b-1))^(2n) d^(4n) >= M^6 (c r (c+r-1))^(2n) M^4.
    Returns the smallest ratio log(lhs/rhs)/n observed (as a float)."""
    steps, _, _ = build(D, R, L)
    seen = set()
    worst = None
    for (r, b), (c, _), d in steps:
        key = (r, b, c, d)
        if key in seen:
            continue
        seen.add(key)
        for n in ns:
            for l in range(n + 1):
                for o in range(n + 1 - l):
                    M = sector_count(n, d, l, o)
                    lhs = (2 * M - 1) ** 6 * (r * b * (r + b - 1)) ** (2 * n) * d ** (4 * n)
                    rhs = M ** 10 * (c * r * (c + r - 1)) ** (2 * n)
                    assert lhs >= rhs, (key, n, l, o)
                    if (l, o) == mode(n, d)[:2]:
                        val = Q(lhs, rhs)
                        worst = val if worst is None or val < worst else worst
    return len(seen)


# ---------------------------------------------------------------------------
# The parameter theorem.
# ---------------------------------------------------------------------------

def schedule(eps):
    eps = Q(eps)
    assert 0 < eps <= 1
    a, b = eps.numerator, eps.denominator
    D = isqrt(cdiv(4 * b, a))
    while D * D * a < 4 * b:
        D += 1
    while (D - 1) ** 2 * a >= 4 * b:
        D -= 1
    L = cdiv(64 * D * b, a)
    x = Q(128 * D * b, a)
    H = cdiv(x.numerator, x.denominator).bit_length()
    n = cdiv(256 * D * H * b, a)
    return dict(eps=eps, D=D, R=8 * D, L=L, x=x, H=H, n=n, k=n,
                J=16 * D - 2 + L)


def check_theorem_bounds(eps, fourier=False):
    p = schedule(eps)
    eps, D, L, x, H, n, k, J = (p[t] for t in "eps D L x H n k J".split())
    # Step 0
    assert D >= 2 and D * D * eps >= 4 and x >= 256
    assert 2 ** (H - 1) <= cdiv(x.numerator, x.denominator) < 2 ** H
    assert H <= x and n >= 2 * x * H and n + 1 <= x ** 3
    assert ln(x).qhi < H and ln(24 * D).qhi < H
    assert ln(6 * k).qhi < k and J * 4 <= 5 * L
    # Step 1
    # exact Fraction division keeps relative precision for tiny eps
    a_hi = 2 * ln(n + 1).qhi / n
    assert a_hi <= 3 / x
    if D < 2 ** 32:
        glo = g_of(D).qlo
    else:
        # relative precision for huge D: ln(1+u) >= u - u^2/2 (alternating)
        u = Q(2, D)
        glo = u - u * u / 2
    Glo = glo * L
    assert Glo >= Q(2 * L, D + 2) >= 64 / eps
    assert J / Glo <= Q(5 * D, 4)
    theta = a_hi * J / Glo
    assert theta <= Q(15, 512) * eps
    # Step 4 rows (values are upper bounds of the actual charges / G)
    rows = {
        "geometric": ((3 + Q(27 * L, 16 * D * (D + 1) ** 2)) / Glo, Q(33, 128)),
        "type": (Q(9, 4) * theta, Q(135, 2048)),
        "separator": (3 * J * LN2.qhi / (n * Glo), Q(15, 1024)),
        "exact_6k": (J * ln(6 * k).qhi / (2 * n * k * Glo), Q(5, 2048)),
        "exact_q": ((2 if fourier else 1) * J * ln(24 * D).qhi / (2 * k * Glo),
                    Q(10 if fourier else 5, 2048)),
        "pool": (LN2.qhi / (2 * n * k * Glo), Q(1, 128)),
    }
    for name, (val, cap) in rows.items():
        assert val <= cap * eps, (name, eps)
    total_cap = sum(c for _, c in rows.values())
    assert total_cap == (Q(724, 2048) if fourier else Q(719, 2048))
    excess = sum(v for v, _ in rows.values()) / (1 - theta)
    bound = (Q(724, 1988) if fourier else Q(719, 1988)) * eps
    assert excess < bound < eps / 2
    # Step 5
    Lam = ln(4096 / eps)
    assert D * D * eps <= 9 and J * J * eps ** 3 <= 240 ** 2
    assert H <= 3 * Lam.qlo
    assert n * n * eps ** 3 <= 2305 ** 2 * Lam.qlo ** 2
    assert ln(24 * D).qhi <= Lam.qlo
    logA_hi = 2 * n * k * J * ln(24 * D).qhi
    assert logA_hi ** 2 * eps ** 9 < (3 * 10 ** 9) ** 2 * Lam.qlo ** 6
    return excess / eps


def grid(quick):
    out = set()
    out.update(Q(1, m) for m in range(1, 120 if quick else 400))
    out.update(Q(4, D * D) for D in range(2, 60 if quick else 400))  # D^2 eps = 4
    out.update(Q(m, 1000) for m in range(1, 1001, 37 if quick else 3))
    # H breakpoints: x = 128 D / eps near powers of two, for each D.
    for D in range(2, 30 if quick else 120):
        lo_x, hi_x = 32 * D * (D - 1) ** 2, 32 * D ** 3   # x-range giving this D
        for m in range(8, 400):
            P = 2 ** m
            if P > hi_x + 1:
                break
            for xx in (Q(P) - Q(1, 2), Q(P), Q(P) + Q(1, 2), Q(P - 1)):
                if lo_x < xx <= hi_x and xx >= 256:
                    e = Q(128 * D) / xx
                    if e <= 1 and schedule(e)["D"] == D:
                        out.add(e)
    out.update(Q(1, 10 ** t) for t in range(1, 40 if quick else 120, 3))
    out.update([Q(1, 2 ** 200), Q(1, 3 ** 150), Q(7, 10 ** 9), Q(999, 1000),
                Q(4, 9), Q(4, 9) + Q(1, 10 ** 12), Q(4, 9) - Q(1, 10 ** 12)])
    # deterministic pseudo-random rationals
    st = 12345
    for _ in range(60 if quick else 400):
        st = (st * 6364136223846793005 + 1442695040888963407) % 2 ** 64
        num = st % 10 ** 6 + 1
        st = (st * 6364136223846793005 + 1442695040888963407) % 2 ** 64
        den = num + st % 10 ** 9
        out.add(Q(num, den))
    return sorted(out)


# ---------------------------------------------------------------------------
# Complete instances: actual chain, types, counts.
# ---------------------------------------------------------------------------

def instance(eps):
    p = schedule(eps)
    eps, D, R, L, n, k, J = (p[t] for t in "eps D R L n k J".split())
    steps, top, _ = build(D, R, L)
    assert len(steps) == J
    s = top[0] + top[1] - 1
    mult = {}
    for _, _, d in steps:
        mult[d] = mult.get(d, 0) + 1
    # normalized by 2nk
    num = ln(s).scale(3)
    den = IV(0, 0)
    G = IV(0, 0)
    logA = IV(0, 0)
    logB = IV(0, 0)
    logm = IV(0, 0)
    logr = ln(s).scale(6 * n * k)
    for d, c in sorted(mult.items()):
        l, o, M = mode(n, d)
        q = d + 2
        assert M * (n + 1) ** 2 >= q ** n >= M and M <= d ** (2 * n)
        E = 1 + 6 * k * (M - 1)
        lM, ld, lE, l2 = ln(M), ln(d), ln(E), ln(Q(2 * M - 1, M))
        num = num + l2.scale(Q(3 * c, n)) + lE.scale(Q(c, 2 * n * k))
        den = den + (lM.scale(Q(1, n)) - ld).scale(c)
        G = G + ln(Q(q, d)).scale(c)
        logA = logA + ld.scale(2 * n * k * c)
        logB = logB + lM.scale(2 * k * c)
        logm = logm + lM.scale(6 * k * c)
        logr = logr + (ln(2 * M - 1).scale(6 * k) + lE).scale(c)
    assert den.qlo > 0
    p_hi = num.qhi / den.qlo                     # pooled exponent p
    pool = LN2.scale(Q(1, 2 * n * k))
    Phi = num + pool
    Phi_hi = Phi.qhi / den.qlo
    Phi_lo = Phi.qlo / den.qhi
    assert Phi_hi < Q(9, 4) + Q(719, 1988) * eps
    # X = numerator - (9/4) * denominator (sign matters in Step 3)
    X = Phi - den.scale(Q(9, 4))
    defect = ln(s).scale(3) - G.scale(Q(9, 4))
    # resources
    assert logB.qhi <= 2 * logA.qlo and logm.qhi <= 6 * logA.qlo
    assert logr.qhi < 17 * logA.qlo
    # pooled exponent p >= 2 (v5 Lemma batch): r* A^2 >= m* B^2
    assert (logr + logA.scale(2)).qlo >= (logm + logB.scale(2)).qhi
    return dict(eps=str(eps), D=D, L=L, J=J, n=n,
                Phi=(float(Phi_lo), float(Phi_hi)),
                excess_over_eps=float((Phi_hi - Q(9, 4)) / eps),
                Phi_minus_p=float(Phi_hi - num.qlo / den.qhi),
                X_lo=float(X.qlo), defect=(float(defect.qlo), float(defect.qhi)),
                logr_over_logA=float(logr.qhi / logA.qlo))


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    a = ap.parse_args(argv)
    qk = a.quick
    out = {}
    out["ln2_lo"] = check_logs()
    out["smallest_parent_cases, max growth"] = check_smallest_parent(
        25 if qk else 45, 15 if qk else 30)
    out["ramp_R_checked"] = check_ramp(100 if qk else 400)
    out["certificate"] = check_certificate()
    out["potential_D_checked"] = check_potential_symbolic(60 if qk else 200)
    Ds = list(range(2, 200 if qk else 1500)) + [10 ** 5, 10 ** 8, 10 ** 12]
    worst = Q(0)
    for D in Ds:
        h = check_gap(D)
        worst = max(worst, h.qhi * (D + 1) ** 3)
    out["gap_D_checked"] = len(Ds)
    out["max (D+1)^3 h_D"] = float(worst)
    bulk = []
    for D in (2, 3, 4, 6, 9, 16, 33, 64) + (() if qk else (128, 300)):
        for L in (0, 1, 2, 4 * D, 64 * D):
            bulk.append(check_bulk(D, L, 8 * D))
    for D, R, L in ((2, 1, 30), (3, 2, 30), (5, 3, 40), (7, 11, 50)):
        bulk.append(check_bulk(D, L, R))
    out["bulk_chains"] = len(bulk)
    out["min_defect_lo"] = min(float(b.qlo) for b in bulk)
    out["max_defect_hi"] = max(float(b.qhi) for b in bulk)
    nr = [check_no_ramp(D, 4 * D) for D in (4, 8, 16, 32, 64, 128) + (() if qk else (256, 512))]
    out["no_ramp: defect - 3 ln D (range)"] = (min(float(v.qlo) for v in nr),
                                              max(float(v.qhi) for v in nr))
    out["profile_potential (levels, chains)"] = check_profile_potential(
        20 if qk else 40, 12 if qk else 30)
    out["types_checked"] = check_types(14 if qk else 30, 10 if qk else 25)
    out["flattening_levels"] = sum(check_flattening(D, 8 * D, 6, (1, 2, 3) if qk else (1, 2, 3, 5, 8))
                                   for D in (2, 3))
    g = grid(qk)
    ex = [check_theorem_bounds(e) for e in g]
    exf = [check_theorem_bounds(e, fourier=True) for e in g[::7]]
    out["grid_size"] = len(g)
    out["max proved-row excess / eps"] = float(max(ex))
    out["fourier rows max excess / eps"] = float(max(exf))
    assert (3 * 10 ** 9) ** 2 < (14 * 10 ** 7) ** 2 * 2 ** 9   # Corollary
    insts = [Q(1), Q(1, 2)] + ([] if qk else [Q(1, 4)])
    out["instances"] = [instance(e) for e in insts]
    for k_, v in out.items():
        print(f"{k_}: {v}")
    print("ALL SKEPTIC CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
