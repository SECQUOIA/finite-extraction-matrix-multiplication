"""Independent check of the round-11 finite gates for shifted polynomial chains.

Run from the repository root:

    python -I -B experiments/shifted_chains_check_gate.py

The script does not import the round-11 producers. It re-derives

* the quadratic contraction identity, as an exact polynomial identity,
* the type-count lemmas and the exact maximum sector counts,
* the complete multiset census for the common-(n,k) gate and the blocked
  (global power P) gate,
* every relaxed margin, using its own outward-rounded logarithms,
* for the common gate, a second certificate of every sign that uses no
  logarithms at all: an exact comparison of two integers,
* an exact one-level endpoint bound. Every case that the relaxation leaves
  open at thresholds 59/20, 119/40 and 5953/2000 is a forced one-level chain
  of arity 2, and the one-level bound closes it.

It reads the saved round-11 receipts only to compare counts and digests.
All certificates use integers and Fractions; no floating point is used.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import comb, isqrt
import json
from pathlib import Path
import sys

CAP_BITS = 128
CAP = 1 << CAP_BITS
ALPHA = Fraction(40, 49)
PREC = 200          # fixed-point bits of every logarithm interval
GUARD = 40          # extra working bits inside the series
Z_BITS = 64         # dyadic rounding of the inverse contraction z
ROOT_BITS = 128     # bits in the square-root enclosure of lambda_d

ONE = 1 << PREC


# ---------------------------------------------------------------------------
# Outward-rounded logarithms.  An interval is a pair (lo, hi) of integers and
# encloses the real interval [lo / 2^PREC, hi / 2^PREC].
# ---------------------------------------------------------------------------

def _ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def _two_atanh(w_lo: Fraction, w_hi: Fraction):
    """Enclose 2*atanh(w) for every w in [w_lo, w_hi], 0 <= w_lo <= w_hi <= 1/3."""
    assert 0 <= w_lo <= w_hi <= Fraction(1, 3)
    bits = PREC + GUARD
    unit = 1 << bits
    a_lo = w_lo.numerator * unit // w_lo.denominator
    a_hi = _ceil_div(w_hi.numerator * unit, w_hi.denominator)
    sq_lo = a_lo * a_lo >> bits
    sq_hi = _ceil_div(a_hi * a_hi, unit)
    assert sq_hi < unit
    term_lo, term_hi = a_lo, a_hi            # enclose w^(2j+1) * 2^bits
    sum_lo = sum_hi = 0
    j = 0
    while True:
        sum_lo += term_lo // (2 * j + 1)
        sum_hi += _ceil_div(term_hi, 2 * j + 1)
        term_lo = term_lo * sq_lo >> bits
        term_hi = _ceil_div(term_hi * sq_hi, unit)
        j += 1
        if term_hi < (1 << (GUARD - 8)):
            # sum_{i>=j} w^(2i+1)/(2i+1) <= w^(2j+1) / ((2j+1)(1-w^2))
            sum_hi += _ceil_div(term_hi * unit, (2 * j + 1) * (unit - sq_hi))
            break
    lo = 2 * sum_lo >> GUARD
    hi = _ceil_div(2 * sum_hi, 1 << GUARD)
    return lo, hi


LOG2 = _two_atanh(Fraction(1, 3), Fraction(1, 3))


@lru_cache(maxsize=None)
def log_int(n: int):
    """Enclose log(n) for a positive integer n."""
    if n < 1:
        raise ValueError("log of a nonpositive integer")
    if n == 1:
        return (0, 0)
    e = n.bit_length() - 1
    m = PREC + GUARD
    if e <= m:
        y_lo = y_hi = Fraction(n, 1 << e)
    else:
        top = n >> (e - m)
        y_lo, y_hi = Fraction(top, 1 << m), Fraction(top + 1, 1 << m)
    w_lo, w_hi = (y_lo - 1) / (y_lo + 1), (y_hi - 1) / (y_hi + 1)
    a_lo, a_hi = _two_atanh(w_lo, w_hi)
    return (e * LOG2[0] + a_lo, e * LOG2[1] + a_hi)


def log_rat(x: Fraction):
    x = Fraction(x)
    if x <= 0:
        raise ValueError("log of a nonpositive rational")
    a, b = log_int(x.numerator), log_int(x.denominator)
    return (a[0] - b[1], a[1] - b[0])


def iadd(*items):
    return (sum(i[0] for i in items), sum(i[1] for i in items))


def isub(x, y):
    return (x[0] - y[1], x[1] - y[0])


def iscale(x, c):
    c = Fraction(c)
    p, q = c.numerator, c.denominator
    if c >= 0:
        return ((x[0] * p) // q, _ceil_div(x[1] * p, q))
    return ((x[1] * p) // q, _ceil_div(x[0] * p, q))


def idec(x, digits=22):
    """Decimal strings that are outward-rounded from the integer interval."""
    scale = 10 ** digits
    lo = (x[0] * scale) >> PREC
    hi = _ceil_div(x[1] * scale, ONE)

    def fmt(v):
        sign = "-" if v < 0 else ""
        v = abs(v)
        return f"{sign}{v // scale}.{v % scale:0{digits}d}"
    return fmt(lo), fmt(hi)


# ---------------------------------------------------------------------------
# Geometry.
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def lam_bounds(d: int):
    """Rational lo < lambda_d < hi, certified by the sign of q x^2 + x - d."""
    q = d + 2
    disc = 1 + 4 * d * q
    scale = 1 << ROOT_BITS
    root = isqrt(disc * scale * scale)
    lo = Fraction(root - scale, 2 * q * scale)
    hi = Fraction(root + 1 - scale, 2 * q * scale)
    assert 0 < lo < hi < 1 - Fraction(1, q)
    assert q * lo * lo + lo - d < 0 < q * hi * hi + hi - d
    return lo, hi


def z_bounds(arities):
    """Dyadic z_lo <= prod 1/lambda_d <= z_hi."""
    lo, hi = Fraction(1), Fraction(1)
    for d in arities:
        lam_lo, lam_hi = lam_bounds(d)
        lo /= lam_hi
        hi /= lam_lo
    s = 1 << Z_BITS
    return (Fraction(lo.numerator * s // lo.denominator, s),
            Fraction(_ceil_div(hi.numerator * s, hi.denominator), s))


def relaxed_line(z):
    """s >= a t + c for the quadratic relaxation with inverse contraction z."""
    return ALPHA * z, (Fraction(4, 3) - ALPHA) * z - Fraction(1, 3)


def endpoint(a, c, p):
    """Exact minimizer over real t>=1 of 3 log(a t + c) - p log t."""
    assert a > 0 and c > 0 and 2 <= p < 3
    t = max(Fraction(1), p * c / ((3 - p) * a))
    return t, a * t + c


def one_level_line(d):
    """Exact bound s >= (1+1/d) t + 1/d for a chain with exactly one level."""
    return Fraction(d + 1, d), Fraction(1, d)


# ---------------------------------------------------------------------------
# Sector counts.
# ---------------------------------------------------------------------------

def type_count(n, d, kern, outer):
    return comb(n, kern) * comb(n - kern, outer) * (d - 1) ** kern * 2 ** outer


@lru_cache(maxsize=None)
def m_max(n: int, d: int) -> int:
    return max(type_count(n, d, a, b) for a in range(n + 1) for b in range(n + 1 - a))


def gains(n, d):
    return m_max(n, d) > d ** n


# ---------------------------------------------------------------------------
# Local cost C(n,d,k;p) with M = M_max(n,d), as an interval.
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def local_cost(n, d, k, p):
    m = m_max(n, d)
    e = 1 + 6 * k * (m - 1)
    return iadd(iscale(log_int(d), p),
                iscale(log_int(m), -p / n),
                iscale(isub(log_int(2 * m - 1), log_int(m)), Fraction(3, n)),
                iscale(log_int(e), Fraction(1, 2 * n * k)))


def endpoint_interval(a, c, p):
    t, s = endpoint(a, c, p)
    return isub(iscale(log_rat(s), 3), iscale(log_rat(t), p)), t


# ---------------------------------------------------------------------------
# Census.
# ---------------------------------------------------------------------------

def max_product(exponent):
    """Largest integer x with x^exponent <= 2^128."""
    x = 1 << (CAP_BITS // exponent)          # x^exponent <= 2^128 at least for this
    while (x + 1) ** exponent <= CAP:
        x += 1
    while x ** exponent > CAP:
        x -= 1
    return x


def multisets(arities, bound):
    """All nonempty multisets (sorted tuples) of arities with product <= bound,
    built from multiplicity vectors one arity at a time."""
    arities = sorted(arities)
    out = []

    def rec(i, prod, acc):
        if i == len(arities):
            if acc:
                out.append(tuple(acc))
            return
        d = arities[i]
        mult = 0
        p = prod
        while p <= bound:
            rec(i + 1, p, acc + [d] * mult)
            mult += 1
            p *= d
    rec(0, 1, [])
    out.sort()          # lexicographic order = sorted depth-first prefix order
    return out


def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r


def common_census():
    rows = []
    for n in range(3, CAP_BITS // 2 + 1):
        retained = [d for d in range(2, 2 * n + 1) if d ** (2 * n) <= CAP and gains(n, d)]
        for k in range(1, CAP_BITS // (2 * n) + 1):
            for word in multisets(retained, max_product(2 * n * k)):
                rows.append((n, k, word))
    return rows


def blocked_actions():
    """For each global power P, the arities with at least one gaining n<=P."""
    table = {}
    for P in range(3, CAP_BITS // 2 + 1):
        for d in range(2, 2 * P + 1):
            if d ** (2 * P) > CAP:
                continue
            ns = [n for n in range(3, P + 1) if gains(n, d)]
            if ns:
                table[P, d] = ns
    return table


# ---------------------------------------------------------------------------
# Exact log-free sign test for the common gate.
#
# For p=u/v, 2nkv * margin equals
#   6nkv log S - 2nku log t + sum_i [2nku log d_i - 2ku log M_i
#        + 6kv log((2M_i-1)/M_i) + v log E_i],
# so its sign is the sign of LHS - RHS below.
# ---------------------------------------------------------------------------

def exact_sign(n, k, word, p, S, t):
    u, v = p.numerator, p.denominator
    e_s, e_t = 6 * n * k * v, 2 * n * k * u
    lhs = S.numerator ** e_s * t.denominator ** e_t * prod(word) ** (2 * n * k * u)
    rhs = S.denominator ** e_s * t.numerator ** e_t
    for d in word:
        m = m_max(n, d)
        e = 1 + 6 * k * (m - 1)
        lhs *= (2 * m - 1) ** (6 * k * v) * e ** v
        rhs *= m ** (2 * k * u + 6 * k * v)
    return (lhs > rhs) - (lhs < rhs)


# ---------------------------------------------------------------------------
# Checks.
# ---------------------------------------------------------------------------

class Poly:
    """Minimal exact polynomial in named variables (dict: exponent tuple -> Fraction)."""
    VARS = ("R", "B", "lam", "d", "u", "M", "r", "b")

    def __init__(self, terms=None):
        self.t = {k: Fraction(v) for k, v in (terms or {}).items() if v != 0}

    @classmethod
    def var(cls, name):
        e = [0] * len(cls.VARS)
        e[cls.VARS.index(name)] = 1
        return cls({tuple(e): 1})

    @classmethod
    def const(cls, c):
        return cls({(0,) * len(cls.VARS): Fraction(c)})

    def _lift(self, o):
        return o if isinstance(o, Poly) else Poly.const(o)

    def __add__(self, o):
        o = self._lift(o)
        out = dict(self.t)
        for k, v in o.t.items():
            out[k] = out.get(k, 0) + v
        return Poly(out)
    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()})

    def __sub__(self, o):
        return self + (-self._lift(o))

    def __rsub__(self, o):
        return self._lift(o) - self

    def __mul__(self, o):
        o = self._lift(o)
        out = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                out[k] = out.get(k, 0) + v1 * v2
        return Poly(out)
    __rmul__ = __mul__

    def __pow__(self, n):
        out = Poly.const(1)
        for _ in range(n):
            out = out * self
        return out

    def is_zero(self):
        return not self.t


def check_algebra():
    R, B, lam, d, u, M, r, b = (Poly.var(x) for x in Poly.VARS)
    q = d + 2
    G = q * lam ** 2 + lam - d
    Q = lambda x, y: x * x + 4 * x * y + y * y
    # q^2 [lam^2 Q(R,B) - Q(T_d(R,B)) - (1-beta^2)(R-lam B)^2], with Q homogeneous
    # of degree 2 so that q^2 Q((dB-R)/q, R) = Q(dB-R, qR), and
    # q^2 (1-beta^2) = q^2 - (q lam + 1)^2.
    diff = q * q * lam * lam * Q(R, B) - Q(d * B - R, q * R) - (q * q - (q * lam + 1) ** 2) * (R - lam * B) ** 2
    quotient = (2 * q * R * R + (4 * q - 2 - 2 * q * lam) * R * B + (q * lam * lam + lam + d) * B * B)
    assert (diff - G * quotient).is_zero()
    # beta < 1: q x^2 + x - d is increasing for x >= 0 and q(1-1/q)^2 + (1-1/q) - d = 1;
    # multiplied by q: (q-1)^2 + (q-1) - d q = q, i.e. the value is exactly 1.
    assert ((q - 1) ** 2 + (q - 1) - d * q - q).is_zero()
    # Centering: (d b - r + 1) - (d+2)/3 = d (b - 1/3) - (r - 1/3).
    third = Fraction(1, 3)
    assert ((d * b - r + 1) - q * third - (d * (b - third) - (r - third))).is_zero()
    # Endpoint value Q(2/3, t-1/3) = t^2 + 2t - 1/3 with t = u + 1.
    t = u + 1
    assert (Q(Poly.const(Fraction(2, 3)), t - third) - (t * t + 2 * t - third)).is_zero()
    # Affine relaxation residual with alpha = 40/49.
    res = Fraction(2, 3) * (t * t + 2 * t - third) - (Fraction(4, 3) + ALPHA * u) ** 2
    assert (res - (Fraction(2, 7203) * u * u + Fraction(24, 49) * u)).is_zero()
    assert Fraction(2, 3) - ALPHA ** 2 == Fraction(2, 7203)
    # Mode-replacement derivative bound, cleared of denominators M(2M-1)(6M-5).
    lhs = 6 * M * (6 * M - 5) + 3 * M * (2 * M - 1) - 5 * (2 * M - 1) * (6 * M - 5)
    assert (lhs + ((M - 2) * (18 * M - 11) + 3)).is_zero()
    assert 17 ** 6 * 49 < 9 ** 10
    return {"R^2": "2q G", "RB": "(4q-2-2q lam) G", "B^2": "(q lam^2+lam+d) G"}


def check_type_lemmas():
    small = 0
    for d in range(2, 301):
        for n in (1, 2):
            assert m_max(n, d) <= d ** n
            small += 1
    large = 0
    for n in range(1, 65):
        for d in range(2 * n + 1, 2 * n + 6):
            assert m_max(n, d) == (d - 1) ** n < d ** n
            large += 1
    return small, large


def check_local_geometry(limit=60, max_d=8):
    """Every legal step on (r,b) <= limit, both orientations, every crop:
    Q(next centered) <= lambda_hi^2 Q(current centered)."""
    third = Fraction(1, 3)

    def Qc(x, y):
        x, y = x - third, y - third
        return x * x + 4 * x * y + y * y
    cases = 0
    for d in range(2, max_d + 1):
        lam2 = lam_bounds(d)[1] ** 2
        for r in range(1, limit + 1):
            for b in range(1, limit + 1):
                qv = Qc(r, b)
                for c in range(1, b):
                    if (d + 2) * c > d * b - r + 1:
                        break
                    assert Qc(c, r) <= lam2 * qv
                    cases += 1
    return cases


def check_chains(limit=10, depth=3, arities=(2, 3, 4)):
    """End-to-end check on all short legal chains with swaps and crops:
    s >= a(z_lo) t + c(z_lo), and for one-level chains s >= (1+1/d)t + 1/d."""
    count = 0

    def steps(r, b):
        for x, y in ((r, b), (b, r)):          # optional input swap
            for d in arities:
                for c in range(1, y):
                    if (d + 2) * c > d * y - x + 1:
                        break
                    yield d, (c, x)

    def walk(state, word, s):
        nonlocal count
        if word:
            z_lo, _ = z_bounds(word)
            a, c = relaxed_line(z_lo)
            for t in state:                    # optional final output swap
                assert s >= a * t + c
                if len(word) == 1:
                    a1, c1 = one_level_line(word[0])
                    assert s >= a1 * t + c1
                count += 1
        if len(word) < depth:
            for d, nxt in steps(*state):
                walk(nxt, word + (d,), s)

    for r0 in range(1, limit + 1):
        for b0 in range(1, limit + 1):
            walk((r0, b0), (), r0 + b0 - 1)
    return count


def run_common(thresholds, exact=()):
    rows = common_census()
    digest = sha256()
    by_nk = {}
    for n, k, word in rows:
        digest.update(f"{n}:{k}:{','.join(map(str, word))}:{prod(word)}\n".encode())
        by_nk[f"{n}:{k}"] = by_nk.get(f"{n}:{k}", 0) + 1
    report = {"multisets": len(rows), "max_depth": max(len(w) for _, _, w in rows),
              "positive_mode_pairs": sum(1 for n in range(3, 65) for d in range(2, 2 * n + 1)
                                         if d ** (2 * n) <= CAP and gains(n, d)),
              "digest": digest.hexdigest(), "counts_by_n_k": by_nk, "gates": {}}
    for p in thresholds:
        neg, minimum, exact_pos, exact_neg = [], None, 0, 0
        for n, k, word in rows:
            z_lo, z_hi = z_bounds(word)
            a, c = relaxed_line(z_lo)
            end, t = endpoint_interval(a, c, p)
            local = iadd(*(local_cost(n, d, k, p) for d in word))
            margin = iadd(end, local)
            if minimum is None or margin[0] < minimum[0][0]:
                minimum = (margin, (n, k, word))
            if margin[0] <= 0:
                # Upper bound for the exact relaxed value: z_hi and any t.
                a2, c2 = relaxed_line(z_hi)
                end2, t2 = endpoint_interval(a2, c2, p)
                upper = iadd(end2, local)
                assert upper[1] < 0, ("undecided interval", n, k, word)
                neg.append((n, k, word, upper))
            if p in exact:
                _, S = endpoint(a, c, p)
                sign = exact_sign(n, k, word, p, S, t)
                if margin[0] > 0:
                    assert sign > 0
                    exact_pos += 1
                else:
                    a2, c2 = relaxed_line(z_hi)
                    t2, S2 = endpoint(a2, c2, p)
                    assert exact_sign(n, k, word, p, S2, t2) < 0
                    exact_neg += 1
        report["gates"][str(p)] = {
            "unexcluded": [(n, k, w) for n, k, w, _ in neg],
            "min_margin": idec(minimum[0]), "argmin": minimum[1],
            "most_negative_upper": idec(min((x[3] for x in neg), default=(0, 0))) if neg else None,
            "exact_positive": exact_pos, "exact_negative": exact_neg}
    return report


def blocked_local_min(P, d, p, table):
    vals = [(local_cost(n, d, P // n, p), n) for n in table[P, d]]
    lo = min(v[0][0] for v in vals)
    hi = min(v[0][1] for v in vals)
    active = [n for v, n in vals if v[0] <= hi]
    return (lo, hi), active


def run_blocked(thresholds):
    table = blocked_actions()
    report = {"actions": len(table), "eligible_choices": sum(len(v) for v in table.values()),
              "gates": {}}
    rows = []
    for P in range(3, 65):
        ar = [d for (Q, d) in table if Q == P]
        for word in multisets(ar, max_product(2 * P)):
            rows.append((P, word))
    digest = sha256()
    by_P = {}
    for P, word in rows:
        digest.update(f"{P}:{','.join(map(str, word))}:{prod(word)}\n".encode())
        by_P[str(P)] = by_P.get(str(P), 0) + 1
    report.update({"multisets": len(rows), "max_depth": max(len(w) for _, w in rows),
                   "digest": digest.hexdigest(), "counts_by_P": by_P})
    for p in thresholds:
        nondividing = 0
        for (P, d) in table:
            _, active = blocked_local_min(P, d, p, table)
            if any(P % (n * (P // n)) for n in active):
                nondividing += 1
        neg, minimum = [], None
        for P, word in rows:
            z_lo, z_hi = z_bounds(word)
            end, _ = endpoint_interval(*relaxed_line(z_lo), p)
            local = iadd(*(blocked_local_min(P, d, p, table)[0] for d in word))
            margin = iadd(end, local)
            if minimum is None or margin[0] < minimum[0][0]:
                minimum = (margin, (P, word))
            if margin[0] <= 0:
                end2, _ = endpoint_interval(*relaxed_line(z_hi), p)
                upper = iadd(end2, local)
                assert upper[1] < 0, ("undecided interval", P, word)
                neg.append((P, word))
        report["gates"][str(p)] = {"unexcluded": neg, "min_margin": idec(minimum[0]),
                                   "argmin": minimum[1],
                                   "actions_with_nondividing_minimizer": nondividing}
    return report, table


def one_level_supplement(common, blocked, table, p, exact=True):
    """Close the open cases with the exact one-level line s >= (1+1/d)t + 1/d.

    Each open case must be forced to be a one-level physical chain: a second
    level of any arity >= 2 would give A >= 2^(4nk) > 2^128 (common gate) or
    A >= 2^(4P) > 2^128 (blocked gate)."""
    out = {"common": [], "blocked": []}
    for n, k, word in common["gates"][str(p)]["unexcluded"]:
        assert len(word) == 1 and 4 * n * k > CAP_BITS
        d = word[0]
        a, c = one_level_line(d)
        end, t = endpoint_interval(a, c, p)
        margin = iadd(end, local_cost(n, d, k, p))
        assert margin[0] > 0
        if exact:
            t_exact, S = endpoint(a, c, p)
            assert exact_sign(n, k, word, p, S, t_exact) > 0
        out["common"].append(((n, k, word), idec(margin, 6)[0]))
    for P, word in blocked["gates"][str(p)]["unexcluded"]:
        assert len(word) == 1 and 4 * P > CAP_BITS
        d = word[0]
        a, c = one_level_line(d)
        end, _ = endpoint_interval(a, c, p)
        local, _ = blocked_local_min(P, d, p, table)
        margin = iadd(end, local)
        assert margin[0] > 0
        out["blocked"].append(((P, word), idec(margin, 6)[0]))
    return out


def realized_one_level_chain():
    """The round-9 witness: (r0,b0)=(43,23), d=2, c=1, n=32, k=2, type (8,16,8).
    Returns the exact pooled exponent enclosure log(r/m)/log(B/A)."""
    n, k, d, r0, b0, c = 32, 2, 2, 43, 23, 1
    assert (d + 2) * c <= d * b0 - r0 + 1 and 1 <= c < b0
    s, t = r0 + b0 - 1, r0                      # child state (c, r0); terminal t = r0
    m = type_count(n, d, 8, 16)
    assert m == m_max(n, d)
    A = d ** (2 * n * k)
    B = t ** (2 * n * k) * m ** (2 * k)
    r_star = s ** (6 * n * k) * (2 * m - 1) ** (6 * k) * (1 + 6 * k * (m - 1))
    m_star = m ** (6 * k)
    assert B > A
    num = log_rat(Fraction(r_star, m_star))
    den = log_rat(Fraction(B, A))
    lo = Fraction(num[0], den[1])
    hi = Fraction(num[1], den[0])
    return A == CAP, (str(lo.numerator * 10 ** 9 // lo.denominator),
                      str(_ceil_div(hi.numerator * 10 ** 9, hi.denominator)))


def forced_one_level(common, blocked, p):
    """Every open case is a single arity whose source power forbids a second level."""
    return (all(len(w) == 1 and 4 * n * k > CAP_BITS for n, k, w in common["gates"][str(p)]["unexcluded"])
            and all(len(w) == 1 and 4 * P > CAP_BITS for P, w in blocked["gates"][str(p)]["unexcluded"]))


def show(label, report, key):
    for p, g in report["gates"].items():
        extra = ""
        if "exact_positive" in g:
            extra = f"; exact integer signs +{g['exact_positive']} -{g['exact_negative']}"
        if key in g:
            extra += f"; actions with a non-dividing possible minimizer {g[key]}"
        print(f"  {label} p={p}: min relaxed margin in {g['min_margin']} at {g['argmin']};"
              f" unexcluded {len(g['unexcluded'])}{extra}")


def main():
    t29, t295, t2975, t29765 = (Fraction(29, 10), Fraction(59, 20),
                                Fraction(119, 40), Fraction(5953, 2000))
    print("quadratic identity: q^2*difference = G*quotient, quotient coefficients", check_algebra())
    print("type lemmas (n=1,2 checks; d>=2n+1 checks):", check_type_lemmas())
    print("local Q-contraction step checks:", check_local_geometry())
    print("end-to-end short chains checked:", check_chains())

    thresholds = (t29, t295, t2975, t29765)
    common = run_common(thresholds, exact=(t29, t295, t2975))
    saved = json.loads(Path("results/round11-variable-finite-gate.json").read_text())["screen"]
    assert common["multisets"] == saved["nonempty_retained_multisets"] == 1752
    assert common["max_depth"] == saved["maximum_retained_depth"] == 21
    assert common["positive_mode_pairs"] == saved["positive_mode_n_d_pairs"] == 219
    assert common["digest"] == saved["multiset_census_sha256"]
    assert common["counts_by_n_k"] == saved["counts_by_n_k"]
    print("common gate census:", common["multisets"], "multisets, depth", common["max_depth"],
          "; 219 (n,d) pairs; digest and per-(n,k) counts match the receipt")
    show("common", common, None)
    g = common["gates"]["59/20"]
    print("  common p=59/20 open cases (n,k,arities):", g["unexcluded"])
    print("  common p=59/20 most negative certified upper bound:", g["most_negative_upper"])
    assert not common["gates"]["29/10"]["unexcluded"]
    assert len(common["gates"]["59/20"]["unexcluded"]) == 17

    blocked, table = run_blocked(thresholds)
    saved = json.loads(Path("results/round11-blocked-finite-gate.json").read_text())["screen"]
    assert blocked["actions"] == saved["P_d_actions"] == 219
    assert blocked["multisets"] == saved["nonempty_retained_multisets"] == 1326
    assert blocked["max_depth"] == saved["maximum_retained_depth"] == 21
    assert blocked["digest"] == saved["multiset_census_sha256"]
    assert blocked["counts_by_P"] == saved["counts_by_P"]
    assert blocked["eligible_choices"] == 3744
    print("blocked gate census:", blocked["multisets"], "multisets;", blocked["actions"],
          "(P,d) actions;", blocked["eligible_choices"], "eligible (P,d,n) choices; digest matches")
    show("blocked", blocked, "actions_with_nondividing_minimizer")
    print("  blocked p=59/20 open cases (P,arities):", blocked["gates"]["59/20"]["unexcluded"])
    assert not blocked["gates"]["29/10"]["unexcluded"]
    assert len(blocked["gates"]["59/20"]["unexcluded"]) == 21
    assert blocked["gates"]["29/10"]["actions_with_nondividing_minimizer"] == 48

    for p in (t295, t2975, t29765):
        assert forced_one_level(common, blocked, p)
        sup = one_level_supplement(common, blocked, table, p, exact=(p != t29765))
        print(f"one-level supplement at p={p}: closes all {len(sup['common'])} common and"
              f" {len(sup['blocked'])} blocked open cases; smallest margins",
              min(sup["common"], key=lambda x: Fraction(x[1])),
              min(sup["blocked"], key=lambda x: Fraction(x[1])))
    print("round-9 one-level witness at A=2^128, pooled exponent x 1e9 in", realized_one_level_chain())
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
