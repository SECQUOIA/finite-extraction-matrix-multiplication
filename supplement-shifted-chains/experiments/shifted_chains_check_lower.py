"""Independent exact checks for the shifted-chain resource lower bound.

Companion to docs/shifted-chains-check-lower.md. The universal argument is
in that note; this script checks its algebraic identities, its finite
lemmas on small cases, its constants and cutoffs, and the whole inequality
chain on explicit ramp schemes. It imports nothing from earlier rounds.

Run from the repository root:

    python -I experiments/shifted_chains_check_lower.py

All identities use exact integers or Fractions. Logarithms and quadratic
roots are enclosed in rational intervals with outward rounding; no
floating-point number enters a check.
"""

from __future__ import annotations

import random
from fractions import Fraction as F
from math import comb, isqrt

# --------------------------------------------------------------------------
# Small exact multivariate polynomials: dict {exponent tuple: int}.


def p_add(*polys):
    out = {}
    for poly in polys:
        for mono, coef in poly.items():
            out[mono] = out.get(mono, 0) + coef
    return {m: c for m, c in out.items() if c}


def p_scale(poly, c):
    return {m: c * v for m, v in poly.items() if c * v}


def p_mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            mono = tuple(x + y for x, y in zip(ma, mb))
            out[mono] = out.get(mono, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def p_var(i, nvars):
    return {tuple(1 if j == i else 0 for j in range(nvars)): 1}


def p_const(c, nvars):
    return {tuple([0] * nvars): c} if c else {}


def check_quadratic_identity():
    """q^3 times  lam^2 Q(R,B) - Q((dB-R)/q,R) - (1-beta^2)(R-lam B)^2
    equals f(lam) * [2q^2R^2 + (4q^2-2q^2lam-2q)RB + (q^2lam^2+q lam+q d)B^2],
    with d=q-2, beta=lam+1/q, f(x)=q x^2+x-d, Q(x,y)=x^2+4xy+y^2.
    Hence the reduced identity holds at the root of f."""
    nv = 4
    q, lam, R, B = (p_var(i, nv) for i in range(nv))
    d = p_add(q, p_const(-2, nv))

    def Q(x, y):
        return p_add(p_mul(x, x), p_scale(p_mul(x, y), 4), p_mul(y, y))

    q2 = p_mul(q, q)
    q3 = p_mul(q2, q)
    lam2 = p_mul(lam, lam)
    lhs = p_add(
        p_mul(p_mul(q3, lam2), Q(R, B)),
        p_scale(p_mul(q, Q(p_add(p_mul(d, B), p_scale(R, -1)), p_mul(q, R))), -1),
    )
    qlam1 = p_add(p_mul(q, lam), p_const(1, nv))
    one_minus_beta2_q2 = p_add(q2, p_scale(p_mul(qlam1, qlam1), -1))
    sq = p_add(R, p_scale(p_mul(lam, B), -1))
    rhs_square = p_mul(p_mul(q, one_minus_beta2_q2), p_mul(sq, sq))
    f = p_add(p_mul(q, lam2), lam, p_scale(d, -1))
    bracket = p_add(
        p_scale(p_mul(q2, p_mul(R, R)), 2),
        p_mul(p_add(p_scale(q2, 4), p_scale(p_mul(q2, lam), -2), p_scale(q, -2)), p_mul(R, B)),
        p_mul(p_add(p_mul(q2, lam2), p_mul(q, lam), p_mul(q, d)), p_mul(B, B)),
    )
    assert p_add(lhs, p_scale(rhs_square, -1), p_scale(p_mul(f, bracket), -1)) == {}
    # f(1-1/q) = 1 > 0, so the positive root lies below 1-1/q and beta<1.
    for qq in range(3, 200):
        x = 1 - F(1, qq)
        assert qq * x * x + x - (qq - 2) == 1
    return True


def check_gap_identity():
    """With q=2/(1-z^4): (1-z^4) f(z^3) = z^3 (1-z)^2 (1-z^2),
    i.e. f(z^3) = z^3 (1-z)^2/(1+z^2)."""
    # (1-z^4) f(z^3) = 2 z^6 + (1-z^4) z^3 - 2 z^4, using q(1-z^4)=2 and
    # (q-2)(1-z^4)=2 z^4.
    left = {6: 2, 3: 1, 7: -1, 4: -2}
    right = {}
    # z^3 (1 - 2z + z^2)(1 - z^2)
    a = {0: 1, 1: -2, 2: 1}
    b = {0: 1, 2: -1}
    for i, ci in a.items():
        for j, cj in b.items():
            right[i + j + 3] = right.get(i + j + 3, 0) + ci * cj
    right = {k: v for k, v in right.items() if v}
    assert left == right
    return True


def terminal_coefficients(K=F(21, 20)):
    """Coefficients of (4/9)^5 (u^2+4u+8/3)^5 - K^10 (u+1)^8 in powers of u."""
    base = [F(8, 3), F(4), F(1)]
    power = [F(1)]
    for _ in range(5):
        new = [F(0)] * (len(power) + 2)
        for i, x in enumerate(power):
            for j, y in enumerate(base):
                new[i + j] += x * y
        power = new
    power = [F(4, 9) ** 5 * x for x in power]
    for j in range(9):
        power[j] -= K ** 10 * comb(8, j)
    return power


def check_endpoint_algebra():
    coeffs = terminal_coefficients()
    assert len(coeffs) == 11 and all(c > 0 for c in coeffs)
    # Initial comparison: (2/3)(s+1/3)^2 <= s^2 for s>=2, since
    # 3 s^2 - 2 (s+1/3)^2 = (1/9)(9 s^2 - 12 s - 2) and
    # 9 s^2 - 12 s - 2 = (s-2)(9 s + 6) + 10.
    for s in range(2, 500):
        assert 9 * s * s - 12 * s - 2 == (s - 2) * (9 * s + 6) + 10 > 0
        assert F(2, 3) * (s + F(1, 3)) ** 2 < s * s
    # Terminal: Q(2/3, t-1/3) = t^2 + 2 t - 1/3.
    for t in range(1, 200):
        T = t - F(1, 3)
        assert F(4, 9) + 4 * F(2, 3) * T + T * T == t * t + 2 * t - F(1, 3)
    return [str(c) for c in coeffs]


# --------------------------------------------------------------------------
# Rational interval logarithms.

W = 256  # fixed-point bits


def _atanh_fixed(a, b):
    """Integer enclosure [lo, hi] of 2^W * atanh(a/b), 0 <= a/b <= 1/3."""
    assert a >= 0 and 3 * a <= b
    if a == 0:
        return 0, 0
    lo, j, pa, pb = 0, 0, a, b
    a2, b2 = a * a, b * b
    while True:
        lo += (pa << W) // (pb * (2 * j + 1))
        j += 1
        pa *= a2
        pb *= b2
        # Remaining tail <= (9/8) t^(2j+1)/(2j+1); stop when below one unit.
        if (pa << W) * 9 < pb * (2 * j + 1) * 8:
            break
    return lo, lo + j + 2


class I:
    """Closed rational interval."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, o):
        o = o if isinstance(o, I) else I(o)
        return I(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = o if isinstance(o, I) else I(o)
        return I(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return I(o) - self

    def scale(self, c):
        c = F(c)
        return I(self.lo * c, self.hi * c) if c >= 0 else I(self.hi * c, self.lo * c)

    def __mul__(self, o):
        if not isinstance(o, I):
            return self.scale(o)
        ps = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return I(min(ps), max(ps))

    __rmul__ = __mul__

    def __truediv__(self, o):
        if not isinstance(o, I):
            return self.scale(1 / F(o))
        assert o.lo > 0
        return self * I(1 / o.hi, 1 / o.lo)


_l2 = _atanh_fixed(1, 3)
LOG2 = I(F(2 * _l2[0], 1 << W), F(2 * _l2[1], 1 << W))
_LOG_CACHE = {}


def log_int(N):
    if N in _LOG_CACHE:
        return _LOG_CACHE[N]
    assert N >= 1
    if N == 1:
        out = I(0)
    else:
        bl = N.bit_length()
        if bl <= 140:
            e = bl - 1
            lo, hi = _atanh_fixed(N - (1 << e), N + (1 << e))
            out = I(F(2 * lo, 1 << W), F(2 * hi, 1 << W)) + LOG2.scale(e)
        else:
            e = bl - 130
            m = N >> e
            out = I(log_int(m).lo, log_int(m + 1).hi) + LOG2.scale(e)
    if N.bit_length() <= 4096:
        _LOG_CACHE[N] = out
    return out


def log_frac(x):
    x = F(x)
    return log_int(x.numerator) - log_int(x.denominator)


def lam_interval(d):
    """Rational enclosure of the positive root of (d+2)x^2 + x - d."""
    q, P = d + 2, 200
    S = isqrt((1 + 4 * d * q) << (2 * P))
    lo = F(S - (1 << P), (2 * q) << P)
    hi = F(S + 1 - (1 << P), (2 * q) << P)

    def f(x):
        return q * x * x + x - d

    assert f(lo) < 0 < f(hi)
    return lo, hi


def a_interval(d):
    lo, hi = lam_interval(d)
    return I(-log_frac(hi).hi, -log_frac(lo).lo)


def g_interval(d):
    return log_int(d + 2) - log_int(d)


def omega_interval(d):
    a, g = a_interval(d), g_interval(d)
    return I(3 * a.lo / g.hi, 3 * a.hi / g.lo)


# --------------------------------------------------------------------------
# Geometry: one-step contraction and whole-chain endpoint inequality.


def Qc(r, b):
    R, B = r - F(1, 3), b - F(1, 3)
    return R * R + 4 * R * B + B * B


def check_steps(max_dim=24, arities=range(1, 13)):
    """Every legal step, with optional input swap and every legal crop,
    satisfies Q(child) < lambda^2 Q(parent) (strict, using a lower root
    enclosure). Includes d=1 (pure tripling levels)."""
    count = 0
    for d in arities:
        lam_lo, _ = lam_interval(d)
        for r0 in range(1, max_dim + 1):
            for b0 in range(1, max_dim + 1):
                for r, b in ((r0, b0), (b0, r0)):
                    for c in range(1, b):
                        if (d + 2) * c > d * b - r + 1:
                            break
                        child = Qc(c, r)
                        assert child < lam_lo ** 2 * Qc(r, b)
                        # exact affine form of the crop condition
                        assert c - F(1, 3) <= (d * (b - F(1, 3)) - (r - F(1, 3))) / (d + 2)
                        count += 1
    return count


def check_random_chains(trials=3000, seed=20261018):
    """Random forward chains with mixed arities (including d=1), input
    swaps, extra crops of the child, and free coordinatewise crops.
    Check s >= K t^(4/5) / prod(lambda_i) at every nonempty prefix, for
    t either coordinate of the current pair."""
    rng = random.Random(seed)
    K = F(21, 20)
    lam_lo = {d: lam_interval(d)[0] for d in range(1, 41)}
    checked = 0
    for _ in range(trials):
        r, b = rng.randint(1, 10 ** rng.randint(1, 8)), rng.randint(2, 10 ** rng.randint(1, 8))
        s = r + b - 1
        prod_lo = F(1)
        steps = 0
        while True:
            if rng.random() < 0.5:
                r, b = b, r  # optional input swap
            d = rng.choice([1, 2, 2, 3, 4, 5, 8, 13, 21, 40])
            cmax = (d * b - r + 1) // (d + 2)
            cmax = min(cmax, b - 1)
            if cmax < 1:
                break
            c = cmax if rng.random() < 0.6 else rng.randint(1, cmax)
            r, b = c, r
            prod_lo *= lam_lo[d]
            steps += 1
            if rng.random() < 0.1:  # free crop of one coordinate
                if rng.random() < 0.5 and r > 1:
                    r = rng.randint(1, r)
                elif b > 1:
                    b = rng.randint(1, b)
            for t in (r, b):
                # s >= K t^(4/5)/prod(lambda) <= s * prod(lam_lo) >= K t^(4/5)
                assert (s * prod_lo) ** 5 >= K ** 5 * t ** 4
                checked += 1
            if steps > 60:
                break
    return checked


# --------------------------------------------------------------------------
# Type counts.


def type_count(n, d, t):
    ell, o, m = t
    assert ell + o + m == n and min(t) >= 0
    return comb(n, ell) * comb(n - ell, o) * (d - 1) ** ell * 2 ** o


def mode_type(n, d):
    """Greedy largest-marginal allocation; maximizes the type count."""
    w = (d - 1, 2, 1)
    a = [0, 0, 0]
    for _ in range(n):
        best = 0
        for j in (1, 2):
            if w[j] * (a[best] + 1) > w[best] * (a[j] + 1):
                best = j
        a[best] += 1
    return tuple(a)


def check_type_lemmas(max_n=30, max_d=64):
    checks = 0
    for n in range(1, max_n + 1):
        for d in range(2, max_d + 1):
            q = d + 2
            counts = {}
            for ell in range(n + 1):
                for o in range(n - ell + 1):
                    t = (ell, o, n - ell - o)
                    counts[t] = type_count(n, d, t)
            assert sum(counts.values()) == q ** n
            Mmax = max(counts.values())
            gm = mode_type(n, d)
            assert counts[gm] == Mmax
            if n <= 2:
                assert Mmax <= d ** n
            if d >= 2 * n + 1:
                assert Mmax <= (d - 1) ** n
            if Mmax > d ** n:
                assert n >= 3 and d <= 2 * n
            if n >= 3 and d <= 2 * n:
                assert 2 * Mmax <= q ** n
            # mode counts: a_i >= (n+1) p_i - 1, i.e. q (a_i+1) >= (n+1) w_i
            w = (d - 1, 2, 1)
            for t, v in counts.items():
                if v == Mmax:
                    assert all(q * (t[i] + 1) >= (n + 1) * w[i] for i in range(3))
            if n >= 2 * q:
                assert n * Mmax <= 12 * q ** (n + 1)
            checks += 1
    # Larger n for the modal bound, using the verified greedy mode.
    big = 0
    for d in range(2, 61):
        q = d + 2
        for n in list(range(2 * q, 2 * q + 40)) + [10 * q, 50 * q + 7, 200 * q + 3]:
            t = mode_type(n, d)
            M = type_count(n, d, t)
            w = (d - 1, 2, 1)
            assert all(q * (t[i] + 1) >= (n + 1) * w[i] for i in range(3))
            assert t[0] * 8 >= n and t[1] * q >= n and t[2] * 2 * q >= n
            # 4e < 10.874
            assert 1000 * n * M <= 10874 * q ** (n + 1)
            big += 1
    return checks, big


def check_factorial_bounds(max_u=400):
    """sqrt(u)(u/e)^u <= u! <= e sqrt(u)(u/e)^u, i.e.
    (u+1/2)log u - u <= log u! <= (u+1/2)log u - u + 1, by log enclosures.
    (Equality holds on the right at u=1.)"""
    for u in range(1, max_u + 1):
        lf = log_int(_fact(u))
        base = log_int(u).scale(F(2 * u + 1, 2)) - I(u)
        assert lf.lo >= base.hi
        assert lf.hi <= (base + I(1)).lo
    return max_u


_FACT = [1]


def _fact(u):
    while len(_FACT) <= u:
        _FACT.append(_FACT[-1] * len(_FACT))
    return _FACT[u]


# --------------------------------------------------------------------------
# Ideal gap omega_d - 9/4 >= 1/(24 q^2) >= 1/(96 d^2) >= 1/(192 d^2).


def check_gap(dmax=400):
    rows = []
    for d in list(range(1, 60)) + list(range(60, dmax + 1, 17)):
        q = d + 2
        om = omega_interval(d)
        gap_lo = om.lo - F(9, 4)
        if d >= 2:
            assert gap_lo >= F(1, 24 * q * q)
            assert gap_lo >= F(1, 96 * d * d)
        else:
            assert gap_lo > F(1, 100)  # d=1: omega_1 = 2.2775...
        assert g_interval(d).hi <= F(2, d)
        if d in (1, 2, 3, 8, 16, 64, 128, 247, 400):
            rows.append((d, float(om.lo), float(gap_lo * q * q)))
    return rows


# --------------------------------------------------------------------------
# Constants and the allowance cutoff.


def check_constants():
    out = {}
    # log(21/20) > 1/21
    assert log_frac(F(21, 20)).lo > F(1, 21)
    assert 192 < 14 ** 2
    coef = F(27, 1024 * 21 * 192 * 14)
    assert coef > F(1, 10 ** 7)
    out["coefficient_lower_bound"] = str(coef)
    # Cutoff conditions, each monotone in epsilon:
    #  (i)   9/4+eps <= 12/5                  eps <= 3/20
    #  (ii)  9q/(32 eps) >= 2q   (n >= 2q)     eps <= 9/64
    #  (iii) 3/(128 eps) >= eps^(-1/2)         eps <= 9/16384
    #  (iv)  (192 eps)^(-1/2) > eps^(-1/4)     eps < 1/36864
    for eps in (F(1, 2 ** 16), F(1, 2 ** 40), F(1, 36865)):
        assert eps <= F(3, 20) and eps <= F(9, 64) and eps <= F(9, 16384)
        assert eps < F(1, 36864)
    out["round11_cutoff_needed"] = "eps < 1/36864 (2^-40 and 2^-16 both suffice)"
    # Recommended version: gap 1/(96 d^2), D0=(96 eps)^(-1/2).
    #  (iv') (96 eps)^(-1/2) > eps^(-1/4)      eps < 1/9216
    eps = F(1, 2 ** 14)
    assert eps <= F(3, 20) and eps <= F(9, 64) and eps <= F(9, 16384)
    assert eps < F(1, 9216)
    assert 96 < 10 ** 2  # 96^(3/2) < 960
    coef96 = F(27, 1024 * 21 * 960)
    assert coef96 > F(1, 10 ** 6)
    out["recommended_coefficient_lower_bound"] = str(coef96)
    out["recommended_cutoff"] = "eps <= 2^-14 (needs eps < 1/9216)"
    # log 2 > 1/2 and 4e < 12 (used in the modal bound)
    assert LOG2.lo > F(1, 2)
    e_hi = F(2721, 1000)  # e < 2.721, so 4e < 10.884 < 12
    assert 4 * e_hi < 12 and log_frac(e_hi).lo > 1
    # 2q+1 <= 9d/2 for d>=2 (gap lemma)
    assert all(2 * (d + 2) + 1 <= F(9 * d, 2) for d in range(2, 1000))
    return out


# --------------------------------------------------------------------------
# Block schedules (common batch, replication, heterogeneous blocks).


def block_counts(s, t, P, levels):
    """Compose the source, every exactified block relation, and the
    terminal projection by multiplying multiplicities.  levels is a list of
    (d, [(n, k, type), ...]) with sum n*k = P at each level."""
    r_star, m_star = s ** (6 * P), 1
    A, B = 1, t ** (2 * P)
    for d, blocks in levels:
        assert sum(n * k for n, k, _ in blocks) == P
        for n, k, ty in blocks:
            M = type_count(n, d, ty)
            E = 1 + 6 * k * (M - 1)
            r_star *= (2 * M - 1) ** (6 * k) * E
            m_star *= M ** (6 * k)
            A *= d ** (2 * n * k)
            B *= M ** (2 * k)
    return A, B, r_star, m_star


def check_blocks():
    # Replication model of the round-11 corollary: closed form (15).
    P = 60
    stages = [(2, 3, 2, (1, 1, 1)), (3, 4, 3, (2, 1, 1)), (16, 5, 2, (3, 1, 1))]
    levels = [(d, [(n, k, ty)] * (P // (n * k))) for d, n, k, ty in stages]
    A, B, r, m = block_counts(5, 2, P, levels)
    A2, B2, num, den = 1, 2 ** (2 * P), 5 ** (6 * P), 1
    for d, n, k, ty in stages:
        M = type_count(n, d, ty)
        E = 1 + 6 * k * (M - 1)
        A2 *= d ** (2 * P)
        B2 *= M ** (2 * P // n)
        num *= (2 * M - 1) ** (6 * P // n) * E ** (P // (n * k))
        den *= M ** (6 * P // n)
    assert (A, B) == (A2, B2) and F(r, m) == F(num, den)
    # Common batch: P = n k, single block per level, formula (3).
    n, k = 4, 3
    ds = [2, 5, 3]
    tys = [(2, 1, 1), (3, 1, 0), (1, 2, 1)]
    A, B, r, m = block_counts(7, 3, n * k, [(d, [(n, k, ty)]) for d, ty in zip(ds, tys)])
    Ms = [type_count(n, d, ty) for d, ty in zip(ds, tys)]
    A3 = 1
    B3 = 3 ** (2 * n * k)
    r3, m3 = 7 ** (6 * n * k), 1
    for d, M in zip(ds, Ms):
        A3 *= d ** (2 * n * k)
        B3 *= M ** (2 * k)
        r3 *= (2 * M - 1) ** (6 * k) * (1 + 6 * k * (M - 1))
        m3 *= M ** (6 * k)
    assert (A, B, r, m) == (A3, B3, r3, m3)
    # Joint exactification of J replicated (n,k) blocks is the block (n,kJ).
    J = 3
    lhs = block_counts(5, 1, n * k * J, [(3, [(n, k * J, (2, 1, 1))])])
    M = type_count(n, 3, (2, 1, 1))
    assert lhs[2] == 5 ** (6 * n * k * J) * (2 * M - 1) ** (6 * k * J) * (1 + 6 * k * J * (M - 1))
    return True


# --------------------------------------------------------------------------
# End-to-end: the whole inequality chain on explicit ramp schemes.


def ramp_chain(D, L):
    """Forward chain of round11-arity-ramp: L levels of arity D, then the
    zero-slack ramp down to (1,1)."""
    R = 8 * D
    rev = []
    for j in range(1, R):
        rev += [3 * j - 1, 3 * j]
    rev += [D] * L
    pairs = [(1, 1)]
    for d in rev:
        r, b = pairs[-1]
        bhat = -(-((d + 2) * r + b - 1) // d)
        pairs.append((b, bhat))
    pairs.reverse()
    arities = list(reversed(rev))
    for i, d in enumerate(arities):
        (rp, bp), (c, r2) = pairs[i], pairs[i + 1]
        assert r2 == rp and 1 <= c < bp and (d + 2) * c <= d * bp - rp + 1
    return pairs, arities


def end_to_end(D, L, n, k, blocks=None):
    """Whole inequality chain on the ramp scheme (D, L).  By default every
    level is one block (n, k) with P = n k.  blocks(d) may instead return a
    list of (n_j, k_j) with sum n_j k_j = P (heterogeneous blocks); every
    block uses an exact mode type."""
    P = n * k
    blocks = blocks or (lambda d: [(n, k)])
    pairs, arities = ramp_chain(D, L)
    s = pairs[0][0] + pairs[0][1] - 1
    bf = pairs[-1][1]
    K = F(21, 20)
    info = {}
    for d in set(arities):
        bl = []
        for nj, kj in blocks(d):
            M = type_count(nj, d, mode_type(nj, d))
            E = 1 + 6 * kj * (M - 1)
            bl.append(dict(n=nj, k=kj, w=F(nj * kj, P), M=M, logM=log_int(M),
                           logE=log_int(E), sep=log_int(2 * M - 1) - log_int(M)))
        assert sum(b["w"] for b in bl) == 1
        info[d] = dict(blocks=bl, logd=log_int(d), logq=log_int(d + 2),
                       a=a_interval(d), g=g_interval(d))
    mult = {}
    for d in arities:
        mult[d] = mult.get(d, 0) + 1
    # Normalized logs: num = log(r*/m*)/(2P), den = log(B/A)/(2P).
    num = log_int(s).scale(3)
    den = log_int(bf)
    for d, c in mult.items():
        x = info[d]
        for b in x["blocks"]:
            num = num + (b["sep"].scale(F(3, b["n"]))
                         + b["logE"].scale(F(1, 2 * b["n"] * b["k"]))).scale(c * b["w"])
            den = den + (b["logM"].scale(F(1, b["n"])) - x["logd"]).scale(c * b["w"])
    assert den.lo > 0  # B > A
    p = num / den
    p0 = F(int(p.hi * 10 ** 9) + 2, 10 ** 9)  # p0 > p
    eps = p0 - F(9, 4)
    assert 0 < eps <= F(3, 20)
    # Potential inequality (4) for this chain.
    asum = I(0)
    for d, c in mult.items():
        asum = asum + info[d]["a"].scale(c)
    margin = log_int(s) - log_frac(K) - asum - log_int(bf).scale(F(4, 5))
    assert margin.lo > 0
    # Block profits t and their weighted sum.
    tot = I(0)
    profitable = set()
    for d, c in mult.items():
        x = info[d]
        q = d + 2
        for b in x["blocks"]:
            nj, kj, M = b["n"], b["k"], b["M"]
            Dd = x["logq"].scale(nj) - b["logM"]
            t = (x["g"].scale(p0) - x["a"].scale(3) - Dd.scale(p0 / nj)
                 - b["logE"].scale(F(1, 2 * nj * kj)))
            tot = tot + t.scale(c * b["w"])
            if t.lo > 0:
                assert 192 * eps * d * d > 1 and 96 * eps * d * d > 1  # d > D0
                assert M > d ** nj and nj >= 3 and d <= 2 * nj and 2 * M <= q ** nj
                assert nj * eps * x["g"].lo > p0 * LOG2.hi
                assert 2 * kj * eps * x["g"].lo > x["logd"].hi
                assert eps * x["g"].hi > t.lo  # t < eps g
                if nj > 12 * q:
                    assert nj * M <= 12 * q ** (nj + 1)
                    assert nj * eps * x["g"].lo > p0 * log_frac(F(nj, 12 * q)).hi
                profitable.add((d, nj, kj))
    assert tot.lo > 3 * log_frac(K).hi
    assert profitable
    return dict(D=D, L=L, P=P, blocks=sorted({tuple(blocks(d)) for d in mult}),
                levels=len(arities), s_digits=len(str(s)),
                pooled_exponent_upper=float(p.hi), eps=float(eps),
                profitable_blocks=len(profitable),
                profitable_arities=sorted({d for d, _, _ in profitable}),
                sum_profit_lower=float(tot.lo), margin_lower=float(margin.lo))


# --------------------------------------------------------------------------


def main():
    print("quadratic potential identity:", check_quadratic_identity())
    print("ideal-gap identity:", check_gap_identity())
    print("terminal coefficients positive:", check_endpoint_algebra()[:2], "...")
    print("legal steps checked:", check_steps())
    print("random chain prefixes checked:", check_random_chains())
    print("type lemma checks (small, large):", check_type_lemmas())
    print("factorial bounds checked up to u =", check_factorial_bounds())
    print("gap rows (d, omega_lo, (omega-9/4)q^2 lower):")
    for row in check_gap():
        print("   ", row)
    print("constants:", check_constants())
    print("block schedules:", check_blocks())
    # The four ramp certificates of docs/round11-arity-ramp.md (D, L, n, k).
    cases = [(2, 100, 512, 256), (4, 400, 2048, 1024),
             (8, 1600, 8192, 4096), (16, 3200, 32768, 16384)]
    for case in cases:
        print("end-to-end:", end_to_end(*case))
    # Heterogeneous blocks (no divisibility pattern): P = 2048*1024 split as
    # (2048,512)+(1024,1024) at even arities and (4096,256)+(1024,1024) at odd.
    hetero = end_to_end(4, 400, 2048, 1024, lambda d: [(2048, 512), (1024, 1024)]
                        if d % 2 == 0 else [(4096, 256), (1024, 1024)])
    print("end-to-end, heterogeneous blocks:", hetero)
    print("all checks passed")


if __name__ == "__main__":
    main()
