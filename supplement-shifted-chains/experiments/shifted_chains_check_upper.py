"""Independent check of the uniform upper bound for the arity-ramp chain.

Topic "upper" of the shifted-chain verification.  The script imports no
producer code.  Identities are checked with exact integers and Fractions.
Every logarithm is enclosed in an interval with rational endpoints whose
denominators are powers of two; all rounding is outward.  No floating point
enters any certificate.

Run from the repository root (the script imports nothing from the repo):

    python -I experiments/shifted_chains_check_upper.py          # full run
    python -I experiments/shifted_chains_check_upper.py --quick  # smaller

The script exits with an AssertionError if any check fails and otherwise
prints a short summary.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Fr
from math import comb, isqrt
import sys

# ---------------------------------------------------------------------------
# Outward-rounded interval arithmetic with rational endpoints.
# ---------------------------------------------------------------------------

P = 256                      # working precision in bits
ONE = 1 << P


def _floor_div(a, b):
    return a // b


def _ceil_div(a, b):
    return -((-a) // b)


def _down(x: Fr) -> Fr:
    return Fr((x.numerator << P) // x.denominator, ONE)


def _up(x: Fr) -> Fr:
    return Fr(_ceil_div(x.numerator << P, x.denominator), ONE)


class I:
    """A closed interval [lo, hi] with Fraction endpoints."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = Fr(lo)
        hi = lo if hi is None else Fr(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = lo, hi

    def rounded(self):
        return I(_down(self.lo), _up(self.hi))

    def __add__(self, o):
        o = o if isinstance(o, I) else I(o)
        return I(self.lo + o.lo, self.hi + o.hi).rounded()

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = o if isinstance(o, I) else I(o)
        return I(self.lo - o.hi, self.hi - o.lo).rounded()

    def __rsub__(self, o):
        return I(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, I) else I(o)
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return I(min(p), max(p)).rounded()

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0, "division needs a positive divisor"
        p = (self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi)
        return I(min(p), max(p)).rounded()

    def __repr__(self):
        return f"[{float(self.lo):.12g}, {float(self.hi):.12g}]"


def _atanh_fixed(zn: int, zd: int):
    """Integers lo, hi with lo <= 2^P * atanh(zn/zd) <= hi, for 0<=z<=1/3."""
    assert 0 <= 3 * zn <= zd
    zlo = (zn << P) // zd
    zhi = _ceil_div(zn << P, zd)
    z2lo = (zlo * zlo) >> P
    z2hi = _ceil_div(zhi * zhi, ONE)
    plo, phi = zlo, zhi
    slo = shi = 0
    k = 0
    while True:
        slo += plo // (2 * k + 1)
        shi += _ceil_div(phi, 2 * k + 1)
        plo = (plo * z2lo) >> P
        phi = _ceil_div(phi * z2hi, ONE)
        k += 1
        if phi <= 4:
            # Tail sum_{j>=k} z^(2j+1)/(2j+1) <= z^(2k+1)/((2k+1)(1-z^2)),
            # and 1/(1-z^2) <= 9/8 because z <= 1/3.
            shi += _ceil_div(9 * phi, 8 * (2 * k + 1)) + 1
            return slo, shi


_lo2, _hi2 = _atanh_fixed(1, 3)
LOG2 = I(Fr(2 * _lo2, ONE), Fr(2 * _hi2, ONE))


def log(x) -> I:
    """Outward enclosure of the natural logarithm of a positive rational."""
    x = Fr(x)
    assert x > 0
    num, den = x.numerator, x.denominator
    m = num.bit_length() - den.bit_length()      # 2^(m-1) < x < 2^(m+1)
    if m >= 0:
        if num < (den << m):
            m -= 1
    elif (num << -m) < den:
        m -= 1
    # Now 2^m <= x < 2^(m+1).
    if m >= 0:
        assert den << m <= num < den << (m + 1)
    else:
        assert den <= num << -m < den << 1
    shift = P - m
    y = (num << shift) // den if shift >= 0 else num // (den << -shift)
    assert ONE <= y < 2 * ONE
    lo_n, _ = _atanh_fixed(y - ONE, y + ONE)
    _, hi_n = _atanh_fixed(y + 1 - ONE, y + 1 + ONE)
    core = I(Fr(2 * lo_n, ONE), Fr(2 * hi_n, ONE))
    return core + LOG2 * m


def sqrt_interval(x: Fr) -> I:
    x = Fr(x)
    s = isqrt((x.numerator << (2 * P)) // x.denominator)
    return I(Fr(s, ONE), Fr(s + 1, ONE))


# ---------------------------------------------------------------------------
# (a) Legal reverse steps.
# ---------------------------------------------------------------------------

def legal(parent, child, d):
    """Forward step C(r,b) -> child pair (c,r) of arity d."""
    r, b = parent
    c, r2 = child
    return r2 == r and 1 <= c < b and (d + 2) * c <= d * b - r + 1


def smallest_parent(r, b, d):
    """Reverse step: child pair (r,b) -> parent (b, b_hat), and the slack."""
    assert d >= 2 and r >= 1 and b >= 1
    bh = _ceil_div((d + 2) * r + b - 1, d)
    e = d * bh - b + 1 - (d + 2) * r
    return (b, bh), e


def check_reverse_steps(limit_rb=70, limit_d=45):
    count = 0
    for d in range(2, limit_d + 1):
        for r in range(1, limit_rb + 1):
            for b in range(1, limit_rb + 1):
                parent, e = smallest_parent(r, b, d)
                assert 0 <= e < d
                assert legal(parent, (r, b), d)
                # Minimality: no smaller second coordinate is legal.
                assert not legal((b, parent[1] - 1), (r, b), d)
                # The largest legal child of the parent is r itself.
                assert (d * parent[1] - b + 1) // (d + 2) == r
                # The maximum dimension grows by at most a factor 5/2 < 3.
                assert 2 * max(parent) <= 5 * max(r, b)
                count += 1
    return count


# ---------------------------------------------------------------------------
# (b) The zero-slack ramp and v5's profile F.
# ---------------------------------------------------------------------------

def s_v5(m):
    out = Fr(1)
    for h in range(1, m):
        out *= Fr(3 * h + 1, 3 * h)
    return out


def F_v5(m, n):
    lo, hi = min(m, n), max(m, n)
    return s_v5(lo) * (hi + Fr(lo - 1, 2))


def ramp_arities(R):
    """Reverse order: arities used from (1,1) up to (R,R)."""
    return [d for j in range(1, R) for d in (3 * j - 1, 3 * j)]


def check_ramp(maxR=300):
    for R in range(1, maxR + 1):
        pair = (1, 1)
        gain = Fr(1)
        for j in range(1, R):
            assert pair == (j, j)
            for d, expect in ((3 * j - 1, (j, j + 1)), (3 * j, (j + 1, j + 1))):
                pair, e = smallest_parent(*pair, d)
                assert pair == expect and e == 0
                gain *= Fr(d + 2, d)
        assert pair == (R, R)
        assert gain == F_v5(R, R) == s_v5(R) * Fr(3 * R - 1, 2)
        assert gain ** 3 >= R ** 4                       # F_R >= R^(4/3)
        assert (2 * R - 1) ** 12 < 2 ** 12 * gain ** 9   # ramp defect < 3 log 2
        # The ramp alone has ideal exponent 3 log(2R-1)/log F(R,R) = tau_R,
        # v5's profile exponent: source 2R-1 and gain F(R,R) are exact.
    return maxR


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def poly_pow(a, k):
    out = [1]
    for _ in range(k):
        out = poly_mul(out, a)
    return out


def check_polynomial_certificate():
    """j[(3j+1)(3j+2)]^3 - 27(j+1)^4(3j-1)^3 at j=u+1, ascending in u."""
    j = [1, 1]                       # u+1
    first = poly_mul(j, poly_pow(poly_mul([4, 3], [5, 3]), 3))
    second = poly_mul(poly_pow([2, 1], 4), poly_pow([2, 3], 3))
    diff = [a - 27 * b for a, b in zip(first, second)]
    while diff and diff[-1] == 0:
        diff.pop()
    assert diff == [4544, 17936, 27324, 20007, 7074, 972], diff
    # Cross-check against the unsubstituted inequality for small j:
    for jj in range(1, 200):
        lhs = jj ** 4 * ((3 * jj + 1) * (3 * jj + 2)) ** 3
        rhs = (jj + 1) ** 4 * ((3 * jj - 1) * 3 * jj) ** 3
        val = sum(c * (jj - 1) ** i for i, c in enumerate(diff))
        assert lhs - rhs == jj ** 3 * val and val > 0
    return diff


# ---------------------------------------------------------------------------
# (c) Bulk potential, root bounds, and the geometric defect.
# ---------------------------------------------------------------------------

class QMu:
    """Elements a + b*mu of Q(mu), with D mu^2 = mu + D + 2."""

    def __init__(self, D, a, b=0):
        self.D, self.a, self.b = D, Fr(a), Fr(b)

    def __add__(self, o):
        return QMu(self.D, self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return QMu(self.D, self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        D = self.D
        a = self.a * o.a
        b = self.a * o.b + self.b * o.a
        c = self.b * o.b                       # coefficient of mu^2
        return QMu(D, a + c * Fr(D + 2, D), b + c * Fr(1, D))

    def is_zero(self):
        return self.a == 0 and self.b == 0


def check_potential_identity(maxD=30, maxrb=25):
    count = 0
    for D in range(2, maxD + 1):
        mu = QMu(D, 0, 1)
        eta = QMu(D, Fr(-1, D), 1)
        third = Fr(1, 3)

        def V(r, b):
            return eta * QMu(D, r - third) + QMu(D, b - third)

        for r in range(1, maxrb + 1):
            for b in range(1, maxrb + 1):
                parent, e = smallest_parent(r, b, D)
                lhs = V(*parent)
                rhs = mu * V(r, b) + QMu(D, Fr(e, D))
                assert (lhs - rhs).is_zero()
                count += 1
        # Root location: p(1+1/D) = -1 and p(5/4+1/D) = (9D-12)/16.
        p = lambda t: D * t * t - t - (D + 2)
        assert p(1 + Fr(1, D)) == -1
        assert p(Fr(5, 4) + Fr(1, D)) == Fr(9 * D - 12, 16)
    return count


def mu_interval(D):
    """Positive root of D mu^2 - mu - (D+2), enclosed."""
    sq = sqrt_interval(Fr(4 * D * D + 8 * D + 1))
    lo = (1 + sq.lo) / (2 * D)
    hi = (1 + sq.hi) / (2 * D)
    pl = D * lo * lo - lo - (D + 2)
    ph = D * hi * hi - hi - (D + 2)
    assert pl <= 0 <= ph
    return I(lo, hi)


def log_mu(D):
    m = mu_interval(D)
    return I(log(m.lo).lo, log(m.hi).hi)


def g_of(D):
    return log(Fr(D + 2, D))


def build_chain(D, R, L):
    """Reverse construction from (1,1): ramp to (R,R), then L arity-D steps.

    Returns the forward list of arities, the source pair, the bulk slacks,
    and the largest per-step growth ratio of the maximum dimension.
    """
    pair = (1, 1)
    arities = []
    slacks = []
    growth_ok = True
    pairs = [pair]
    for d in ramp_arities(R):
        new, e = smallest_parent(*pair, d)
        assert e == 0
        growth_ok &= max(new) <= 3 * max(pair)
        pair = new
        arities.append(d)
        pairs.append(pair)
    assert pair == (R, R)
    for _ in range(L):
        new, e = smallest_parent(*pair, D)
        assert 0 <= e < D
        growth_ok &= max(new) <= 3 * max(pair)
        slacks.append(e)
        pair = new
        arities.append(D)
        pairs.append(pair)
    assert growth_ok
    # Forward legality of every step.
    for idx in range(len(arities)):
        parent, child = pairs[idx + 1], pairs[idx]
        assert legal(parent, child, arities[idx])
    return list(reversed(arities)), pair, slacks


def check_geometry(D, L, R=None):
    R = 8 * D if R is None else R
    arities, (r0, b0), slacks = build_chain(D, R, L)
    J = len(arities)
    assert J == 2 * (R - 1) + L and max(arities) == max(3 * R - 3, D)
    s = r0 + b0 - 1
    assert s <= 2 * 3 ** J - 1
    lm = log_mu(D)
    g = g_of(D)
    FR = F_v5(R, R)
    G = log(FR) + g * L
    ls = log(s)
    # (5): s < mu^L (9R/4 + D); with R = 8D this is s < (19R/8) mu^L.
    bound5 = log(Fr(9 * R, 4) + D) + lm * L
    assert ls.hi < bound5.lo
    defect = ls * 3 - G * Fr(9, 4)
    h = lm * 3 - g * Fr(9, 4)
    # (6) in the notes' form and in the sharper form.
    notes6 = Fr(3) + Fr(27 * L, 16 * D * (D + 1) ** 2)
    assert defect.hi < notes6
    if R == 8 * D:
        sharp6 = log(Fr(19, 8)) * 3 + h * L
        assert defect.hi < sharp6.lo
    ramp_defect = log(2 * R - 1) * 3 - log(FR) * Fr(9, 4)
    assert ramp_defect.hi < (LOG2 * 3).lo
    return {"D": D, "L": L, "R": R, "J": J, "source": (r0, b0),
            "defect_hi": float(defect.hi), "ramp_defect_hi": float(ramp_defect.hi)}


# ---------------------------------------------------------------------------
# (d) Ideal exponent and gap.
# ---------------------------------------------------------------------------

def check_gap(D):
    lm = log_mu(D)
    g = g_of(D)
    h = lm * 3 - g * Fr(9, 4)           # = g (omega_D - 9/4)
    assert h.lo >= 0                     # omega_D >= 9/4 (strictly > in fact)
    # Notes (round 8): omega_D - 9/4 <= 27/(32 (D+1)^2).
    assert h.hi <= g.lo * Fr(27, 32 * (D + 1) ** 2)
    # Review's sharper form: g (omega_D - 9/4) <= 3/(8 (D+1)^3).
    assert h.hi <= Fr(3, 8 * (D + 1) ** 3)
    # This note's form: omega_D - 9/4 <= cosh(1/2)/(8 D^2) < 1/(7 D^2).
    assert h.hi <= g.lo * Fr(1, 7 * D * D)
    # Bounds on g used in the proofs.
    assert g.lo >= Fr(2, D + 2) and g.hi <= Fr(2, D)
    return h


# ---------------------------------------------------------------------------
# (e) The parameter theorem.
# ---------------------------------------------------------------------------

def schedule(eps):
    eps = Fr(eps)
    assert 0 < eps <= 1
    a, b = eps.numerator, eps.denominator
    # D = ceil(sqrt(4/eps)) = least D with D^2 * a >= 4 b.
    D = isqrt((4 * b) // a)
    if D * D * a < 4 * b:
        D += 1
    assert D * D * a >= 4 * b and (D - 1) ** 2 * a < 4 * b
    R = 8 * D
    L = _ceil_div((64 * D * b), a)
    x = Fr(128 * D) / eps
    H = _ceil_div(x.numerator, x.denominator).bit_length()
    n = _ceil_div(256 * D * H * b, a)
    J = 16 * D - 2 + L
    return {"eps": eps, "D": D, "R": R, "L": L, "x": x, "H": H, "n": n, "k": n, "J": J}


def check_uniform(eps):
    """All inequalities of the uniform proof, from the schedule alone."""
    p = schedule(eps)
    eps, D, R, L, x, H, n, k, J = (p[t] for t in ("eps", "D", "R", "L", "x", "H", "n", "k", "J"))
    assert D >= 2 and x >= 256 and n >= 3 and k >= 3
    assert 2 ** H > x                        # hence H > log2 x >= log x
    assert H <= x and n >= 2 * x * H and n + 1 <= x ** 3
    lx = log(x)
    assert lx.hi < H
    a = log(n + 1) * Fr(2, n)               # type loss per level
    assert a.hi <= 3 / x
    assert J <= Fr(5, 4) * L
    g = g_of(D)
    assert g.lo >= Fr(2, D + 2)
    Glo = g.lo * L                           # G >= L g_D (ramp gain omitted)
    assert Fr(2 * L, D + 2) >= 64 / eps
    assert Fr(J) / Glo <= Fr(5, 4) * D
    theta = a.hi * J / Glo
    assert theta <= Fr(15, 512) * eps
    # Charges relative to G (upper bounds).
    geometry = (3 + Fr(27 * L, 16 * D * (D + 1) ** 2)) / Glo
    copies = 3 * J * LOG2.hi / (n * Glo)
    lq = log(24 * D)
    assert lq.hi < H
    l6k = log(6 * k)
    assert l6k.hi < k
    exact_k = J * l6k.hi / (2 * n * k * Glo)
    exact_q = J * lq.hi / (2 * k * Glo)
    pooling = LOG2.hi / (2 * n * k * Glo)
    rows = {"geometry": (geometry, Fr(33, 128)),
            "type_loss_times_9/4": (Fr(9, 4) * theta, Fr(135, 2048)),
            "separator_copies": (copies, Fr(15, 1024)),
            "exactification_log6k": (exact_k, Fr(5, 2048)),
            "exactification_logq": (exact_q, Fr(5, 2048)),
            "pooling_ceiling": (pooling, Fr(1, 128))}
    for name, (val, claim) in rows.items():
        assert val <= claim * eps, (name, float(val / eps), float(claim))
    assert sum(c for _, c in rows.values()) == Fr(719, 2048)
    total = sum(v for v, _ in rows.values())
    excess = total / (1 - theta)
    assert excess < Fr(719, 1988) * eps < eps / 2
    # Size bounds: D <= 3 eps^-1/2, L <= 193 eps^-3/2, J <= 240 eps^-3/2,
    # H <= 3 Lambda, n <= 2305 eps^-3/2 Lambda, log(24D) <= Lambda.
    Lam = log(4096 / eps)
    assert D * D * eps <= 9
    assert L * L * eps ** 3 <= 193 ** 2
    assert J * J * eps ** 3 <= 240 ** 2
    assert H <= 3 * Lam.lo
    assert n * n * eps ** 3 <= 2305 ** 2 * Lam.lo ** 2
    assert lq.hi <= Lam.lo
    logA_upper = 2 * n * k * J * lq.hi       # >= 2nk sum log d_i
    # log A < 3e9 eps^-9/2 Lambda^3, squared to remove the half power.
    assert logA_upper ** 2 * eps ** 9 < (3 * 10 ** 9) ** 2 * Lam.lo ** 6
    assert 2 * 2305 ** 2 * 240 == 2_550_252_000 < 3 * 10 ** 9
    # Corollary with allowance eps (not eps/2), for eps <= 1/2: apply the
    # theorem to 2 eps; 3e9 (2 eps)^(-9/2) < 1.4e8 eps^(-9/2).
    assert (3 * 10 ** 9) ** 2 < (14 * 10 ** 7) ** 2 * 2 ** 9
    return {"eps": eps, "D": D, "L": L, "J": J, "H": H, "n": n,
            "excess_over_eps_upper": float(excess / eps),
            "logA_upper_over_bound": float(logA_upper / (3e9 * float(Lam.lo) ** 3) * float(eps) ** 4.5)}


# ---------------------------------------------------------------------------
# End-to-end instances: actual chain, actual types, actual counts.
# ---------------------------------------------------------------------------

def weighted_mode(n, d):
    """A maximizer of n!/(l! o! m!) (d-1)^l 2^o, with an optimality proof.

    Start from proportional counts and complete greedily; then certify global
    optimality by the exchange condition: every selected last marginal
    w_c/n_c is at least every unselected next marginal w_c'/(n_c'+1).
    Since each category's marginals decrease, this selects n largest
    marginals, which maximizes the product of the chosen marginals.
    """
    w = (d - 1, 2, 1)
    q = d + 2
    cnt = [n * wi // q for wi in w]
    while sum(cnt) < n:
        best = max(range(3), key=lambda c: Fr(w[c], cnt[c] + 1))
        cnt[best] += 1
    for c in range(3):
        if cnt[c] == 0:
            continue
        for c2 in range(3):
            if c2 != c:
                assert Fr(w[c], cnt[c]) >= Fr(w[c2], cnt[c2] + 1)
    l, o, m = cnt
    M = comb(n, l) * comb(n - l, o) * (d - 1) ** l * 2 ** o
    return tuple(cnt), M


def check_instance(eps, verify_mode_bound=True):
    p = schedule(eps)
    eps, D, R, L, n, k, J = (p[t] for t in ("eps", "D", "R", "L", "n", "k", "J"))
    arities, (r0, b0), _ = build_chain(D, R, L)
    assert len(arities) == J
    s = r0 + b0 - 1
    mult = {}
    for d in arities:
        mult[d] = mult.get(d, 0) + 1
    num = log(s) * 3
    den = I(0)
    G = I(0)
    sum_logd = I(0)
    for d, c in sorted(mult.items()):
        q = d + 2
        _, M = weighted_mode(n, d)
        assert M <= q ** n
        if verify_mode_bound:
            assert M * (n + 1) ** 2 >= q ** n
        assert M <= d ** (2 * n)                 # per level: gives B <= A^2
        E = 1 + 6 * k * (M - 1)
        assert E <= 6 * k * M
        lM = log(M)
        ld = log(d)
        num = num + log(Fr(2 * M - 1, M)) * Fr(3 * c, n) + log(E) * Fr(c, 2 * n * k)
        den = den + (lM * Fr(1, n) - ld) * c
        G = G + log(Fr(q, d)) * c
        sum_logd = sum_logd + ld * c
    num = num + LOG2 * Fr(1, 2 * n * k)
    assert den.lo > 0                            # B > A
    Phi = num / den                              # = log(2 r*/m*) / log(B/A)
    bound = Fr(9, 4) + Fr(719, 1988) * eps
    assert Phi.hi < bound
    defect = log(s) * 3 - G * Fr(9, 4)
    assert defect.hi < 3 + Fr(27 * L, 16 * D * (D + 1) ** 2)
    logA = sum_logd * (2 * n * k)
    Lam = log(4096 / eps)
    assert logA.hi ** 2 * eps ** 9 < (3 * 10 ** 9) ** 2 * Lam.lo ** 6
    # r_* < A^20, using exact logs of the actual factors.
    # log r* = 6nk log s + sum c(6k log(2M-1) + log E).
    return {"eps": str(eps), "D": D, "R": R, "L": L, "J": J, "n": n,
            "source_pair_bits": (r0.bit_length(), b0.bit_length()),
            "Phi_upper": float(Phi.hi),
            "excess_over_eps_upper": float((Phi.hi - Fr(9, 4)) / eps),
            "geometric_defect_upper": float(defect.hi),
            "logA_upper": float(logA.hi)}


def check_resource_bounds(eps):
    """B <= A^2, m* <= A^6, r* < A^20 on an actual instance, by logs."""
    p = schedule(eps)
    D, R, L, n, k = (p[t] for t in ("D", "R", "L", "n", "k"))
    arities, (r0, b0), _ = build_chain(D, R, L)
    s = r0 + b0 - 1
    logA = I(0)
    logB = I(0)
    logm = I(0)
    logr = log(s) * (6 * n * k)
    seen = {}
    for d in arities:
        if d not in seen:
            _, M = weighted_mode(n, d)
            E = 1 + 6 * k * (M - 1)
            seen[d] = (log(d), log(M), log(2 * M - 1), log(E))
        ld, lM, l2M, lE = seen[d]
        logA = logA + ld * (2 * n * k)
        logB = logB + lM * (2 * k)
        logm = logm + lM * (6 * k)
        logr = logr + l2M * (6 * k) + lE
    assert logB.hi <= 2 * logA.lo
    assert logm.hi <= 6 * logA.lo
    assert logr.hi < 17 * logA.lo                # proved: r* < A^17
    assert s <= 2 * 3 ** len(arities)
    return {"eps": str(p["eps"]), "logB/logA": float(logB.hi / logA.lo),
            "logm/logA": float(logm.hi / logA.lo), "logr/logA": float(logr.hi / logA.lo)}


def reproduce_ramp_table_row(D=2, L=100, n=512, k=256):
    """Recompute the first finite row of docs/round11-arity-ramp.md."""
    arities, (r0, b0), _ = build_chain(D, 8 * D, L)
    assert len(arities) == 130
    s = r0 + b0 - 1
    num = log(s) * 3
    den = I(0)
    for d in arities:
        _, M = weighted_mode(n, d)
        E = 1 + 6 * k * (M - 1)
        num = num + log(Fr(2 * M - 1, M)) * Fr(3, n) + log(E) * Fr(1, 2 * n * k)
        den = den + log(M) * Fr(1, n) - log(d)
    fixed = (num + LOG2 * Fr(1, 2 * n * k)) / den
    # Same quantity as log(2 r*/m*)/log(B/A); the producer normalizes by
    # 2k instead of 2nk, which does not change the ratio.  The published
    # value is "below 2.337133".
    assert fixed.hi < Fr(2337133, 10 ** 6)
    return float(fixed.hi)


# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args(argv)

    out = {}
    out["log2_interval_width"] = float(LOG2.hi - LOG2.lo)
    assert Fr(69314718055994530941, 10 ** 20) < LOG2.lo <= LOG2.hi < Fr(69314718055994530942, 10 ** 20)
    out["reverse_steps_checked"] = check_reverse_steps(40 if args.quick else 70,
                                                       25 if args.quick else 45)
    out["ramp_radii_checked"] = check_ramp(120 if args.quick else 300)
    out["polynomial_certificate"] = check_polynomial_certificate()
    out["potential_identities_checked"] = check_potential_identity(12 if args.quick else 30)

    gapD = list(range(2, 401 if args.quick else 2001)) + [10 ** 4, 10 ** 6, 10 ** 9]
    worst = Fr(0)
    for D in gapD:
        h = check_gap(D)
        worst = max(worst, h.hi * (D + 1) ** 3)
    out["gap_D_checked"] = len(gapD)
    out["max_(D+1)^3*g*(omega-9/4)"] = float(worst)

    geo = [check_geometry(D, 4 * D) for D in (2, 4, 8, 16, 32, 64, 128, 256)
           + (() if args.quick else (512, 1024))]
    geo += [check_geometry(D, L) for D in (2, 3, 5, 7) for L in (0, 1, 7, 100, 1000)]
    geo += [check_geometry(D, 50, R) for D in (2, 5) for R in (1, 2, 3, 9, 40)]
    out["geometry_chains"] = len(geo)
    out["max_defect_L=4D"] = max(gq["defect_hi"] for gq in geo[:10])
    out["max_ramp_defect"] = max(gq["ramp_defect_hi"] for gq in geo)

    grid = [Fr(1), Fr(99, 100), Fr(3, 4), Fr(2, 3), Fr(1, 2), Fr(2, 5), Fr(1, 3),
            Fr(1, 4), Fr(1, 5), Fr(3, 16), Fr(1, 7), Fr(1, 10), Fr(1, 16), Fr(1, 50),
            Fr(1, 100), Fr(1, 1000), Fr(1, 10 ** 6), Fr(1, 2 ** 20), Fr(1, 2 ** 40),
            Fr(1, 2 ** 80), Fr(1, 3 ** 50), Fr(7, 10 ** 9), Fr(1, 10 ** 30)]
    grid += [Fr(1, m) for m in range(1, 101 if args.quick else 401)]
    grid += [Fr(m, 400) for m in range(1, 401, 1 if not args.quick else 7)]
    uni = [check_uniform(e) for e in grid]
    out["uniform_eps_checked"] = len(grid)
    out["max_excess_over_eps_upper"] = max(u["excess_over_eps_upper"] for u in uni)
    out["max_logA_upper_over_stated_bound"] = max(u["logA_upper_over_bound"] for u in uni)

    inst_eps = [Fr(1), Fr(1, 2)] + ([] if args.quick else [Fr(1, 4), Fr(1, 9)])
    out["instances"] = [check_instance(e) for e in inst_eps]
    out["resources"] = [check_resource_bounds(e) for e in inst_eps[:2]]
    out["ramp_table_row_D2"] = reproduce_ramp_table_row()

    for key, val in out.items():
        print(f"{key}: {val}")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
