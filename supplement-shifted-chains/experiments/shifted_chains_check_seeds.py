#!/usr/bin/env python3
"""Independent checks for docs/shifted-chains-check-seeds.md.

Run from the repository root with either of

    python -I experiments/shifted_chains_check_seeds.py
    python -m experiments.shifted_chains_check_seeds

Add ``--quick`` to skip the largest literal chain (allowance 1/8).

The script uses only the standard library and imports nothing from the
repository.  Identities are checked with exact integers and Fractions.
Logarithms are certified rational enclosures computed in fixed-point
integer arithmetic with directed rounding; every asserted inequality is
decided by these enclosures.  Floats are used only in printed summaries.

Sections
  1. certified logarithms and intervals
  2. the round-11 schedule, the literal integer chain and weighted modes
  3. uniform parameter inequalities over many allowances
  4. literal chains: complete counts, pooled exponent, seed side, depth
  5. coefficient-height and precision envelopes (positive shifted polynomials)
  6. separator / exactification identities and the denominator ledger;
     unimodularity of the integer chain bases
  7. pooled recursion on toy relative schemes: unrolled seeds and the
     explicit cost lemma
  8. the uniform algorithm: the selection rule and the rate
"""

from __future__ import annotations

import argparse
import math
import random
from collections import Counter
from fractions import Fraction as Fr
from itertools import product

# ---------------------------------------------------------------------------
# 1. Certified logarithms and intervals
# ---------------------------------------------------------------------------

W = 192                      # fixed-point fraction bits
ONE = 1 << W
_TERMS = 70                  # atanh terms; z <= 1/3 gives tail < 2^-(W+8)


def _cdiv(a, b):
    return -((-a) // b)


def _atanh2_fixed(num, den, lower):
    """2*atanh(num/den)*2^W rounded down (lower) or up, for 0<=num/den<=1/3."""
    assert 0 <= 3 * num <= den
    z = (num << W) // den if lower else _cdiv(num << W, den)
    z2 = (z * z) >> W if lower else _cdiv(z * z, ONE)
    power, total = z, 0
    for j in range(_TERMS):
        total += power // (2 * j + 1) if lower else _cdiv(power, 2 * j + 1)
        power = (power * z2) >> W if lower else _cdiv(power * z2, ONE)
    if not lower:
        # tail <= z^(2T+1)/((2T+1)(1-z^2)) <= (9/8) z^(2T+1)/(2T+1)
        total += _cdiv(9 * power, 8 * (2 * _TERMS + 1)) + 1
    return 2 * total


_LN2 = (_atanh2_fixed(1, 3, True), _atanh2_fixed(1, 3, False))


def _ln_mantissa(num, den, lower):
    """ln(num/den)*2^W for 1 <= num/den <= 2."""
    assert den <= num <= 2 * den
    return _atanh2_fixed(num - den, num + den, lower)


class Iv:
    """A closed interval [lo, hi] of rationals (dyadic after rounding)."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = Fr(lo)
        self.hi = Fr(lo if hi is None else hi)
        assert self.lo <= self.hi

    def rnd(self):
        return Iv(Fr(math.floor(self.lo * ONE), ONE), Fr(math.ceil(self.hi * ONE), ONE))

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Iv) else Iv(o)))

    def __rsub__(self, o):
        return Iv(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        c = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return Iv(min(c), max(c)).rnd()

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        assert o.lo > 0, "division by an interval that is not positive"
        return (self * Iv(1 / o.hi, 1 / o.lo)).rnd()

    def __rtruediv__(self, o):
        return Iv(o) / self

    def f(self):
        return float((self.lo + self.hi) / 2)


LN2 = Iv(Fr(_LN2[0], ONE), Fr(_LN2[1], ONE))


def ln_int(n):
    """Certified enclosure of ln(n) for an integer n >= 1."""
    assert n >= 1
    e = n.bit_length() - 1
    if e <= W:
        lo = _ln_mantissa(n, 1 << e, True)
        hi = _ln_mantissa(n, 1 << e, False)
    else:
        top = n >> (e - W)
        lo = _ln_mantissa(top, ONE, True)
        hi = _ln_mantissa(top + 1, ONE, False)
    return Iv(Fr(e * _LN2[0] + lo, ONE), Fr(e * _LN2[1] + hi, ONE))


def ln_q(x):
    x = Fr(x)
    assert x > 0
    return ln_int(x.numerator) - ln_int(x.denominator)


def ln_sqrt_quadratic(D):
    """Enclosure of ln(mu), mu=(1+sqrt(1+4D(D+2)))/(2D), the root of D mu^2-mu-(D+2)."""
    S = 1 + 4 * D * (D + 2)
    root = math.isqrt(S << (2 * W))
    lo = Fr(ONE + root, 2 * D * ONE)
    hi = Fr(ONE + root + 1, 2 * D * ONE)
    # exact sign checks of the defining quadratic at the two endpoints
    assert D * lo * lo - lo - (D + 2) <= 0 <= D * hi * hi - hi - (D + 2)
    a, b = ln_q(lo), ln_q(hi)
    return Iv(a.lo, b.hi)


def ceil_fr(x):
    x = Fr(x)
    return -((-x.numerator) // x.denominator)


# ---------------------------------------------------------------------------
# 2. The round-11 schedule, the literal chain and weighted modes
# ---------------------------------------------------------------------------

def schedule(eps):
    """Round-11 ramp schedule, recomputed independently from its definition."""
    eps = Fr(eps)
    assert 0 < eps <= 1
    D = math.isqrt(4 * eps.denominator // eps.numerator)
    while D * D * eps < 4:
        D += 1
    while D > 1 and (D - 1) * (D - 1) * eps >= 4:
        D -= 1
    R = 8 * D
    L = ceil_fr(64 * D / eps)
    x = 128 * D / eps
    H = ceil_fr(x).bit_length()
    n = ceil_fr(256 * D * H / eps)
    J = 2 * (R - 1) + L
    return dict(eps=eps, D=D, R=R, L=L, x=x, H=H, n=n, k=n, J=J)


def literal_chain(D, R, L):
    """Reverse construction from (1,1); returns source pair and forward arity counts."""
    reverse = [a for j in range(1, R) for a in (3 * j - 1, 3 * j)] + [D] * L
    r = b = 1
    for idx, d in enumerate(reverse):
        pr, pb = b, ceil_fr(Fr((d + 2) * r + b - 1, d))
        slack = d * pb - pr + 1 - (d + 2) * r
        assert 1 <= r < pb and 0 <= slack < d, (idx, d, r, b)
        # forward map (pr,pb) -> (c,pr) with the largest legal child c == r
        assert (d * pb - pr + 1) // (d + 2) == r
        if idx < 2 * (R - 1):
            assert slack == 0
        r, b = pr, pb
    return (r, b), Counter(reverse)


def weighted_mode(n, d):
    """Global maximizer of n!/(K!O!U!) (d-1)^K 2^O over K+O+U=n.

    The objective is separable and concave in the counts, so a point at
    which no single unit transfer increases it is a global maximizer;
    the final loop certifies that criterion exactly.
    """
    w = (d - 1, 2, 1)
    tot = d + 2
    c = [n * wi // tot for wi in w]
    while sum(c) < n:
        i = max(range(3), key=lambda t: Fr(w[t], c[t] + 1))
        c[i] += 1
    changed = True
    while changed:
        changed = False
        for i in range(3):
            for j in range(3):
                if i != j and c[j] > 0 and Fr(w[i], c[i] + 1) > Fr(w[j], c[j]):
                    c[i] += 1
                    c[j] -= 1
                    changed = True
    for i in range(3):
        for j in range(3):
            if i != j and c[j] > 0:
                assert Fr(w[i], c[i] + 1) <= Fr(w[j], c[j])
    K, O, U = c
    M = math.comb(n, K) * math.comb(n - K, O) * (d - 1) ** K * 2 ** O
    return (K, O, U), M


# ---------------------------------------------------------------------------
# 3. Uniform parameter inequalities over many allowances
# ---------------------------------------------------------------------------

LOGA_CONST = 2 * 2305 ** 2 * 240          # = 2,550,252,000 (round-11 note)
SEED_CONST = Fr(21, 100) * 10 ** 12       # log n0 < 2.1e11 eps^(-11/2) Lambda^3
DEPTH_CONST = 313                         # depth < 1 + 313 eps^(-3/2) Lambda
U_CONST = 4 * 10 ** 9                     # U(v) <= 4e9 v^(9/2) Lambda(v)^3


def uniform_certificate(eps):
    """Re-derive the round-11 budget and the new seed/depth constants."""
    p = schedule(eps)
    eps, D, L, J, n, k, H, x = (p[t] for t in ("eps", "D", "L", "J", "n", "k", "H", "x"))
    lam = ln_q(4096 / eps)
    assert 4 <= D * D * eps <= 9                       # D <= 3 eps^(-1/2)
    assert J <= Fr(5, 4) * L and L >= 64 * D
    assert H >= ln_q(x).hi and H <= x
    assert n >= 2 * x * H and n + 1 <= x ** 3
    assert ln_int(6 * k).hi < k
    assert ln_int(24 * D).hi < H
    g = ln_q(Fr(D + 2, D))
    G_lo = L * g.lo                                    # ramp gain log F_R >= 0 dropped
    assert G_lo >= 64 / eps
    a = 2 * ln_int(n + 1) / n
    theta = J * a / G_lo
    geometry = Iv(3 + Fr(27 * L, 16 * D * (D + 1) ** 2)) / G_lo
    copies = 3 * J * LN2 / (n * G_lo)
    exact = J * ln_int(6 * k) / (2 * n * k * G_lo) + J * ln_int(24 * D) / (2 * k * G_lo)
    pooling = LN2 / (2 * n * k * G_lo)
    excess = (geometry + copies + exact + pooling + Fr(9, 4) * theta) / (1 - theta)
    assert theta.hi <= 15 * eps / 512
    assert geometry.hi < 33 * eps / 128
    assert excess.hi < Fr(719, 1988) * eps < eps / 2
    # source side: log A <= 2 n k J ln(24D) < 2.551e9 eps^(-9/2) Lambda^3 (squared)
    logA_up = 2 * n * k * J * ln_int(24 * D)
    assert logA_up.hi ** 2 < LOGA_CONST ** 2 * eps ** -9 * lam.lo ** 6
    # seed side (Theorem 7): log n0 <= 27 ceil(2/eps) log A
    c2 = ceil_fr(2 / eps)
    logn0_up = 27 * c2 * logA_up
    assert logn0_up.hi ** 2 < SEED_CONST ** 2 * eps ** -11 * lam.lo ** 6
    # depth: l_max < 1 + log n0 / log(B/A), log(B/A) >= 2nk G (1-theta)
    ratio = J * ln_int(24 * D) / (G_lo * (1 - theta))   # >= log A / log(B/A)
    assert ratio.hi <= Fr(1288, 1000) * D * ln_int(24 * D).lo
    depth_extra = 27 * c2 * ratio
    assert depth_extra.hi ** 2 <= DEPTH_CONST ** 2 * eps ** -3 * lam.lo ** 2
    return dict(eps=eps, D=D, J=J, n=n, excess_over_eps=float(excess.hi / eps),
                log10A_upper=float(logA_up.hi) / math.log(10),
                log10n0_upper=float(logn0_up.hi) / math.log(10),
                depth_upper=float(1 + depth_extra.hi))


def U_of_v(v):
    """Integer upper bound for log2 A of the scheme at allowance 1/v."""
    p = schedule(Fr(1, v))
    return 2 * p["n"] * p["k"] * p["J"] * (24 * p["D"]).bit_length()


def check_U_bound(v):
    u = U_of_v(v)
    lam = ln_int(4096 * v)
    assert (24 * schedule(Fr(1, v))["D"]).bit_length() <= lam.lo     # bitlength(24D) <= Lambda(v)
    assert u * u <= U_CONST ** 2 * v ** 9 * lam.lo ** 6
    return u


# ---------------------------------------------------------------------------
# 4. Literal chains: complete counts, pooled exponent, seed side, depth
# ---------------------------------------------------------------------------

def literal_report(eps):
    p = schedule(eps)
    eps, D, R, L, J, n, k = (p[t] for t in ("eps", "D", "R", "L", "J", "n", "k"))
    (r0, b0), cnt = literal_chain(D, R, L)
    s = r0 + b0 - 1
    assert sum(cnt.values()) == J and max(cnt) < 24 * D
    lnM, lnM2, lnE = {}, {}, {}
    for d in cnt:
        _, M = weighted_mode(n, d)
        q = d + 2
        Q = q ** n
        assert M <= Q and M * (n + 1) ** 2 >= Q            # q^n/(n+1)^2 <= M <= q^n
        assert Q <= d ** (2 * n)                            # q <= d^2
        E = 1 + 6 * k * (M - 1)
        lnM[d], lnM2[d], lnE[d] = ln_int(M), ln_int(2 * M - 1), ln_int(E)
    lns = ln_int(s)
    G = sum((c * (ln_int(d + 2) - ln_int(d)) for d, c in cnt.items()), Iv(0))
    defect = 3 * lns - Fr(9, 4) * G
    assert defect.hi < 3 + Fr(27 * L, 16 * D * (D + 1) ** 2)
    lnmu = ln_sqrt_quadratic(D)
    assert lns.hi < (ln_q(Fr(19 * R, 8)) + L * lnmu).lo     # s < (19R/8) mu^L
    FR = Fr(1)
    for j in range(1, R):
        FR *= Fr((3 * j + 1) * (3 * j + 2), (3 * j - 1) * (3 * j))
    assert FR ** 3 >= R ** 4                                # F_R >= R^(4/3)
    logA = 2 * n * k * sum((c * ln_int(d) for d, c in cnt.items()), Iv(0))
    logB = 2 * k * sum((c * lnM[d] for d, c in cnt.items()), Iv(0))
    logm = 3 * logB
    logr = 6 * n * k * lns + sum((c * (6 * k * lnM2[d] + lnE[d]) for d, c in cnt.items()), Iv(0))
    gain = logB - logA
    assert gain.lo > LN2.hi                                 # B > 2A
    pexp = (logr - logm) / gain
    Phi = (logr - logm + LN2) / gain
    assert Phi.hi < Fr(9, 4) + eps / 2
    assert logB.hi <= 2 * logA.lo                           # B <= A^2
    assert logr.hi <= Fr(35, 4) * logA.lo                   # r <= A^(35/4) (new)
    assert logr.hi < 20 * logA.lo                           # r < A^20 (round-11 note)
    # seed side of Theorem 7: Xi = r(1+rm)n_*^3, A <= n_* <= 3A
    lnXi_lo = 2 * logr + logm + 3 * logA
    lnXi1_hi = 2 * logr + logm + 3 * logA + ln_int(55)
    assert lnXi1_hi.hi <= 27 * logA.lo
    c2 = ceil_fr(2 / eps)
    logn0 = Iv(c2 * lnXi_lo.lo, c2 * lnXi1_hi.hi)
    # rank: R <= Xi n0^p < n0^(9/4+eps)  <=>  log Xi < (9/4+eps-p) log n0
    assert lnXi1_hi.hi < (Fr(9, 4) + eps - pexp.hi) * logn0.lo
    depth_hi = 1 + logn0.hi / gain.lo
    # l_max >= log(n0/n_*)/log(B/A) with n_* <= 3A
    depth_lo = (logn0.lo - logA.hi - ln_int(3).hi) / gain.hi
    ln10 = math.log(10)
    return dict(eps=str(eps), D=D, J=J, n=n, s_digits=len(str(s)),
                p=(float(pexp.lo), float(pexp.hi)), Phi_upper=float(Phi.hi),
                log10A=logA.f() / ln10, log10B=logB.f() / ln10,
                log10r=logr.f() / ln10, log10m=logm.f() / ln10,
                log_r_over_log_A=float(logr.hi / logA.lo),
                log_B_over_log_A=float(logB.hi / logA.lo),
                log10n0=(float(logn0.lo) / ln10, float(logn0.hi) / ln10),
                log_n0_over_log_A=float(logn0.hi / logA.lo),
                depth=(float(depth_lo), float(depth_hi)), geometric_defect=float(defect.hi))


# ---------------------------------------------------------------------------
# 5. Coefficient-height and precision envelopes
# ---------------------------------------------------------------------------

def poly_mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] = out.get(i + j, 0) + x * y
    return {e: c for e, c in out.items() if c}


def poly_add(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}


def poly_scale(c, p):
    return {e: c * x for e, x in p.items()}


def positive_after_shift(p, shift=16):
    """True iff every coefficient of p(x+shift) is positive; then p(A)>0 for A>=shift."""
    deg = max(p)
    coeffs = [sum(Fr(c) * math.comb(e, j) * shift ** (e - j) for e, c in p.items() if e >= j)
              for j in range(deg + 1)]
    return all(c > 0 for c in coeffs)


def height_envelopes():
    """Re-derive the A^24 / precision / exponent-range polynomial inequalities.

    Variables: A (source side, A>=16) and h=log2 A <= A/2.  Each envelope is
    increasing in h, so h may be replaced by A/2.
    """
    A = {1: 1}
    h = {1: Fr(1, 2)}                       # h <= A/2
    one = {0: 1}

    def pw(e):
        return {e: 1}
    # denominator: 6nk log2((s-1)!) + sum_i [12k log2((2M-2)!) + 6k(M-1) log2(E!)]
    # with 6nk<=A, s<=A^4, k,M,J<=A, E<=A^3, log2 N! <= N log2 N
    Dlog = poly_add(poly_mul(poly_scale(4, pw(5)), h),
                    poly_mul(A, poly_add(poly_mul(poly_scale(24, pw(2)), poly_add(h, one)),
                                         poly_mul(poly_scale(18, pw(5)), h))))
    Slog = poly_mul(pw(4), poly_add(one, poly_scale(4, h)))
    Rlog = poly_add(poly_mul(poly_scale(4, A), poly_add(poly_scale(2, one), poly_scale(4, h))), pw(3))
    Vlog = poly_mul(pw(4), poly_add(Slog, Rlog, poly_scale(200, h)))
    total = poly_add(Dlog, Vlog, poly_scale(2, one))
    stated = {9: 2, 8: 1, 7: 10, 6: 10, 5: 108, 4: 12, 3: 24, 0: 2}
    assert total == stated, total
    checks = {
        "bits <= A^24": positive_after_shift(poly_add(pw(24), poly_scale(-1, total))),
        # 1 + 67 log2 A + 3 A^24 < A^28
        "precision t+A^28+1": positive_after_shift(
            poly_add(pw(28), poly_scale(-1, poly_add(one, poly_scale(67, h), poly_scale(3, pw(24)))))),
        # 5 A^28 + 3 A^24 + 150 log2 A + 5 < A^30
        "exponent range": positive_after_shift(
            poly_add(pw(30), poly_scale(-1, poly_add(poly_scale(5, pw(28)), poly_scale(3, pw(24)),
                                                    poly_scale(150, h), poly_scale(5, one))))),
        # stage layers 24nk+24k+60 <= 12A+60 <= A^2 (strict at A>=16: 256-252=4)
        "layers per stage": positive_after_shift({2: 1, 1: -12, 0: -60}),
        # width: A^20 (convolution) * A^6 (aux) * A^26 (labels) * A^6 (raw words) <= A^58 < A^200
        "generation": positive_after_shift({700: 1, 654: -1, 610: -1}),
    }
    assert all(checks.values()), checks
    return checks


# ---------------------------------------------------------------------------
# 6. Separator/exactification identities, denominators, chain bases
# ---------------------------------------------------------------------------

def lagrange_coeffs(nodes, idx):
    """Coefficients (low to high) of the Lagrange basis polynomial for nodes[idx]."""
    poly = [Fr(1)]
    den = 1
    for j, t in enumerate(nodes):
        if j != idx:
            new = [Fr(0)] * (len(poly) + 1)
            for i, c in enumerate(poly):
                new[i] -= c * t
                new[i + 1] += c
            poly = new
            den *= nodes[idx] - t
    return [c / den for c in poly]


def eval_poly(p, x):
    return sum((c * Fr(x) ** i for i, c in enumerate(p)), Fr(0))


def taylor_coeff(p, center, order):
    return sum((p[i] * math.comb(i, order) * Fr(center) ** (i - order)
                for i in range(order, len(p))), Fr(0))


def separator_check(M):
    """Lemma 9.1(b) of v5 for M blocks: identities, degree and denominators."""
    nodes_M = list(range(1, M + 1))
    nodes_2M = list(range(1, 2 * M))
    first = [lagrange_coeffs(nodes_M, g) for g in range(M)]
    last = [lagrange_coeffs(nodes_2M, l) for l in range(2 * M - 1)]
    F = math.factorial(2 * M - 2)
    alpha = {(l, gp): eval_poly(first[gp], l) for l in nodes_2M for gp in range(M)}
    beta = {(l, g, e): Fr(l - g - 1) ** e for l in nodes_2M for g in range(M) for e in range(M)}
    gamma = {(l, g, ep): taylor_coeff(last[l - 1], g + 1, ep)
             for l in nodes_2M for g in range(M) for ep in range(M)}
    assert all((c * math.factorial(M - 1)).denominator == 1 for c in alpha.values())
    assert all((c * F).denominator == 1 for c in gamma.values())
    assert all(c.denominator == 1 for c in beta.values())
    for g, gp, e, ep in product(range(M), repeat=4):
        K = sum(alpha[l, gp] * beta[l, g, e] * gamma[l, g, ep] for l in nodes_2M)
        # coefficient of t^(ep-e); must be [xi^(ep-e)] L_{g'}(g+1+xi)
        want = taylor_coeff(first[gp], g + 1, ep - e) if ep >= e else Fr(0)
        assert K == want
        if ep == e:
            assert K == (1 if g == gp else 0)
    # tensor-level check with random sector tensors and exactification (k=1)
    rng = random.Random(M)
    dims = 2
    sectors = [{(a, b, c): rng.randint(-3, 3) for a in range(dims) for b in range(dims) for c in range(dims)}
               for _ in range(M)]
    E = (M - 1) + 1
    weights = {t: (-1) ** (t - 1) * math.comb(E, t) for t in range(1, E + 1)}
    total = Counter()
    for t in range(1, E + 1):          # parameter node
        for l in nodes_2M:             # separator copy
            for g, sec in enumerate(sectors):
                for (a, b, c), coef in sec.items():
                    if not coef:
                        continue
                    for gp in range(M):
                        for e in range(M):
                            for ep in range(M):
                                val = (alpha[l, gp] * beta[l, g, e] * Fr(t) ** (-e)
                                       * gamma[l, g, ep] * Fr(t) ** ep)
                                if val:
                                    total[(a, gp), (g, b, e), (g, c, ep)] += weights[t] * coef * val
    target = Counter()
    for g, sec in enumerate(sectors):
        for (a, b, c), coef in sec.items():
            for e in range(M):
                if coef:
                    target[(a, g), (g, b, e), (g, c, e)] += coef
    assert {k: v for k, v in total.items() if v} == {k: v for k, v in target.items() if v}
    # stage denominator for 6 orientations and power k clears the 6k+6k+6k factors
    for k in (1, 2):
        Ek = 1 + 6 * k * (M - 1)
        Dlev = F ** (12 * k) * math.factorial(Ek) ** (6 * k * (M - 1))
        per_factor = math.factorial(M - 1) * F * math.lcm(*range(1, Ek + 1)) ** (M - 1)
        assert Dlev % per_factor ** (6 * k) == 0
    return True


def finite_difference_check(Emax=40):
    for E in range(1, Emax + 1):
        for j in range(E):
            s = sum((-1) ** (t - 1) * math.comb(E, t) * t ** j for t in range(1, E + 1))
            assert s == (1 if j == 0 else 0)
    return True


def rational_convolution_check(r, b):
    """Lemma 9.1(a): C(r,b) from integer evaluations and Lagrange output weights."""
    n = r + b - 1
    nodes = list(range(1, n + 1))
    cards = [lagrange_coeffs(nodes, l) for l in range(n)]
    den = math.factorial(n - 1)
    for l in range(n):
        assert all((c * den).denominator == 1 for c in cards[l])
    for a, bb in product(range(r), range(b)):
        for g in range(n):
            val = sum(Fr(nodes[l]) ** a * Fr(nodes[l]) ** bb * cards[l][g] for l in range(n))
            assert val == (1 if g == a + bb else 0)
    return True


def chain_basis_check(d, b, c):
    """Quotient lifts and kernel vectors of Q(F)=sum z^(jh)F_j are a unimodular basis
    with entries and inverse entries in {0,+1,-1}."""
    h = b - c
    Bq = d * b - (d - 1) * c
    idx = {(j, u): j * b + u for j in range(d) for u in range(b)}
    vecs = []
    for u in range(Bq):
        j = max(0, -(-(u - b + 1) // h)) if u >= b else 0
        assert 0 <= u - j * h < b and (j == 0 or u - (j - 1) * h >= b)
        v = [0] * (d * b)
        v[idx[j, u - j * h]] = 1
        vecs.append(v)
    for j in range(d - 1):
        for i in range(c):
            v = [0] * (d * b)
            v[idx[j, i + h]] = -1
            v[idx[j + 1, i]] = 1
            vecs.append(v)
    N = d * b
    assert len(vecs) == N
    # Q image of the kernel vectors is zero; lifts map to monomials
    for v in vecs[Bq:]:
        img = Counter()
        for (j, u), pos in idx.items():
            if v[pos]:
                img[j * h + u] += v[pos]
        assert not any(img.values())
    # invert the column matrix exactly
    P = [[Fr(vecs[col][row]) for col in range(N)] for row in range(N)]
    aug = [P[i] + [Fr(int(i == j)) for j in range(N)] for i in range(N)]
    det_sign = 1
    for col in range(N):
        piv = next(r for r in range(col, N) if aug[r][col] != 0)
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
            det_sign = -det_sign
        pv = aug[col][col]
        assert abs(pv) == 1, "pivot not a unit"
        aug[col] = [x / pv for x in aug[col]]
        for r in range(N):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [x - f * y for x, y in zip(aug[r], aug[col])]
    inv = [row[N:] for row in aug]
    assert all(x in (0, 1, -1) for row in inv for x in row)
    return True


# ---------------------------------------------------------------------------
# 7. Pooled recursion on toy relative schemes
# ---------------------------------------------------------------------------

STRASSEN_U = [{0: 1, 3: 1}, {2: 1, 3: 1}, {0: 1}, {3: 1}, {0: 1, 1: 1}, {2: 1, 0: -1}, {1: 1, 3: -1}]
STRASSEN_V = [{0: 1, 3: 1}, {0: 1}, {1: 1, 3: -1}, {2: 1, 0: -1}, {3: 1}, {0: 1, 1: 1}, {2: 1, 3: 1}]
# output entry (alpha,gamma) index 2*alpha+gamma -> {product: coef}
STRASSEN_W = {0: {0: 1, 3: 1, 4: -1, 6: 1}, 1: {2: 1, 4: 1}, 2: {1: 1, 3: 1}, 3: {0: 1, 1: -1, 2: 1, 5: 1}}


def toy_scheme(m, a, idle=0):
    """(7m+idle) MM_a |> m MM_{2a}: m Strassen copies tensored with MM_a, plus idle copies.

    U[s][(a1,b1)] = {(c', alpha', beta'): coef} gives source left entries;
    V likewise; Wout[c'][(alpha',gamma')] = {(s, a1, g1): coef} gives outputs.
    """
    r, B = 7 * m + idle, 2 * a
    U = [dict() for _ in range(r)]
    V = [dict() for _ in range(r)]
    Wout = [dict() for _ in range(m)]
    for cp in range(m):
        for t in range(7):
            s = 7 * cp + t
            for a1, b1 in product(range(a), repeat=2):
                U[s][a1, b1] = {(cp, (e // 2) * a + a1, (e % 2) * a + b1): c for e, c in STRASSEN_U[t].items()}
                V[s][a1, b1] = {(cp, (e // 2) * a + a1, (e % 2) * a + b1): c for e, c in STRASSEN_V[t].items()}
        for o, terms in STRASSEN_W.items():
            al, ga = divmod(o, 2)
            for a1, g1 in product(range(a), repeat=2):
                Wout[cp][al * a + a1, ga * a + g1] = {(7 * cp + t, a1, g1): c for t, c in terms.items()}
    return dict(r=r, m=m, A=a, B=B, U=U, V=V, W=Wout)


class Form(dict):
    """Sparse linear form; supports +, scalar *, and 0 + form."""

    def __add__(self, other):
        if isinstance(other, int) and other == 0:
            return self
        out = Form(self)
        for k, v in other.items():
            nv = out.get(k, 0) + v
            if nv:
                out[k] = nv
            else:
                out.pop(k, None)
        return out

    __radd__ = __add__

    def __rmul__(self, c):
        return Form({k: c * v for k, v in self.items()}) if c else Form()


def pooled_recursion(sch, X, Y, leaf_mul, zero):
    """The pooled recursion of v5 Lemma 2.4, literally, over an arbitrary 'ring'.

    Returns (product, stats).  Arithmetic is counted with the dense formulas
    used in the explicit cost lemma: 6 r m A^2 B^2 c^2 per batch and 2 n^3 per
    classical leaf product.
    """
    r, m, A, B = sch["r"], sch["m"], sch["A"], sch["B"]
    n = len(X)
    n_inf = Fr(A * B, B - A)
    n_star = ceil_fr(n_inf) + 1
    level = [(X, Y)]
    side = n
    stack, nus, sides, ops = [], [1], [n], 0
    while side > n_star:
        nu = len(level)
        c = ceil_fr(Fr(side, B))
        batches = ceil_fr(Fr(nu, m))
        new = []
        for bi in range(batches):
            group = level[bi * m:(bi + 1) * m]
            def pad(Mx):
                return [[Mx[i][j] if i < side and j < side else zero for j in range(B * c)] for i in range(B * c)]
            Xs = [pad(g[0]) for g in group] + [None] * (m - len(group))
            Ys = [pad(g[1]) for g in group] + [None] * (m - len(group))
            for s in range(r):
                xs = [[zero] * (A * c) for _ in range(A * c)]
                ys = [[zero] * (A * c) for _ in range(A * c)]
                for (a1, b1), terms in sch["U"][s].items():
                    for (cp, al, be), coef in terms.items():
                        if Xs[cp] is None:
                            continue
                        for i in range(c):
                            for j in range(c):
                                xs[a1 * c + i][b1 * c + j] += coef * Xs[cp][al * c + i][be * c + j]
                for (a1, b1), terms in sch["V"][s].items():
                    for (cp, al, be), coef in terms.items():
                        if Ys[cp] is None:
                            continue
                        for i in range(c):
                            for j in range(c):
                                ys[a1 * c + i][b1 * c + j] += coef * Ys[cp][al * c + i][be * c + j]
                new.append((xs, ys))
        ops += batches * 6 * r * m * A * A * B * B * c * c
        stack.append((side, c, batches, nu))
        level = new
        side = A * c
        nus.append(len(level))
        sides.append(side)
    prods = []
    for x, y in level:
        k = len(x)
        P = [[zero] * k for _ in range(k)]
        for i in range(k):
            for j in range(k):
                for l in range(k):
                    P[i][l] = P[i][l] + leaf_mul(x[i][j], y[j][l])
        prods.append(P)
        ops += 2 * k ** 3
    while stack:
        prev, c, batches, nu = stack.pop()
        outs = []
        for bi in range(batches):
            src = prods[bi * r:(bi + 1) * r]
            for cp in range(m):
                Z = [[zero] * (B * c) for _ in range(B * c)]
                for (al, ga), terms in sch["W"][cp].items():
                    for (s, a1, g1), coef in terms.items():
                        for i in range(c):
                            for j in range(c):
                                Z[al * c + i][ga * c + j] += coef * src[s][a1 * c + i][g1 * c + j]
                outs.append([row[:prev] for row in Z[:prev]])
        prods = outs[:nu]
    return prods[0], dict(nu=nus, sides=sides, ops=ops, lmax=len(nus) - 1, n_star=n_star)


def check_scheme(sch, trials=3):
    """The toy scheme itself is a restriction r MM_A |> m MM_B (random evaluation)."""
    rng = random.Random(1)
    r, m, A, B = sch["r"], sch["m"], sch["A"], sch["B"]
    for _ in range(trials):
        Xs = [[[rng.randint(-5, 5) for _ in range(B)] for _ in range(B)] for _ in range(m)]
        Ys = [[[rng.randint(-5, 5) for _ in range(B)] for _ in range(B)] for _ in range(m)]
        P = []
        for s in range(r):
            x = [[sum(c * Xs[cp][al][be] for (cp, al, be), c in sch["U"][s].get((i, j), {}).items())
                  for j in range(A)] for i in range(A)]
            y = [[sum(c * Ys[cp][al][be] for (cp, al, be), c in sch["V"][s].get((i, j), {}).items())
                  for j in range(A)] for i in range(A)]
            P.append([[sum(x[i][j] * y[j][l] for j in range(A)) for l in range(A)] for i in range(A)])
        for cp in range(m):
            for al, ga in product(range(B), repeat=2):
                got = sum(c * P[s][a1][g1] for (s, a1, g1), c in sch["W"][cp].get((al, ga), {}).items())
                want = sum(Xs[cp][al][j] * Ys[cp][j][ga] for j in range(B))
                assert got == want
    return True


def lemma_P_bound(sch, n, lmax):
    """ln of the two bounds of Lemma 11 (with the actual depth l_max):

    K = C_nu n^p [2 (r/m) n_*^3 + 12 m B^2 ((4/3)(r/m) n_inf^2 + l_max (B/A)^(p-2))]
    S = 304 (log2 n + 2) B^11 n^p.
    Returns (enclosure of ln K, enclosure of ln S, enclosure of p).
    """
    r, m, A, B = sch["r"], sch["m"], sch["A"], sch["B"]
    lnBA = ln_q(Fr(B, A))
    p = ln_q(Fr(r, m)) / lnBA
    rho_m = Fr(r, m)
    n_inf = Fr(A * B, B - A)
    n_star = ceil_fr(n_inf) + 1
    C_nu = 1 + Fr(r * m, r - m)
    lnn = ln_int(n)
    # (B/A)^(p-2) <= exp(upper(ln)) bounded via a rational upper bound of exp on [0, 1.1]
    t = ((p - 2) * lnBA).hi
    assert 0 <= t <= Fr(11, 10)
    exp_up = sum(t ** j / math.factorial(j) for j in range(40)) + Fr(1, 10 ** 12)
    inner = 2 * rho_m * n_star ** 3 + 12 * m * B * B * (Fr(4, 3) * rho_m * n_inf ** 2 + lmax * exp_up)
    lnK = ln_q(C_nu * inner) + p * lnn
    log2n = lnn / LN2
    lnS = ln_int(304) + ln_q((log2n + 2).lo) + 11 * ln_int(B) + p * lnn
    lnS = Iv(lnS.lo, lnS.hi + 1)        # only the lower end is used
    return lnK, lnS, p


def toy_pooled_checks():
    results = []
    schemes = {"7MM_1>MM_2": toy_scheme(1, 1), "15MM_1>2MM_2": toy_scheme(2, 1, idle=1),
               "15MM_2>2MM_4": toy_scheme(2, 2, idle=1), "22MM_1>3MM_2": toy_scheme(3, 1, idle=1)}
    rng = random.Random(7)
    for name, sch in schemes.items():
        check_scheme(sch)
        r, m, A, B = sch["r"], sch["m"], sch["A"], sch["B"]
        assert B >= 2 * A and r >= 4 * m and m <= B ** 3
        for n in [1, 2, 3, 4, 5, 6, 7, 9, 12, 17, 23, 31]:
            X = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
            Y = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
            Z, st = pooled_recursion(sch, X, Y, lambda a, b: a * b, 0)
            assert Z == [[sum(X[i][j] * Y[j][l] for j in range(n)) for l in range(n)] for i in range(n)]
            # recurrences and depth facts of v5 Lemma 2.4, Step 3
            n_inf = Fr(A * B, B - A)
            rho = Fr(A, B)
            for l, (nu, sd) in enumerate(zip(st["nu"], st["sides"])):
                assert nu <= (1 + Fr(r * m, r - m)) * Fr(r, m) ** l
                assert rho ** l * n <= sd < n_inf + rho ** l * n or l == 0
            lm = st["lmax"]
            assert rho ** lm * n > rho and rho ** lm * n <= st["sides"][-1] <= st["n_star"]
            boundK, boundS, p = lemma_P_bound(sch, n, lm)
            lnops = ln_int(st["ops"])
            assert lnops.hi <= boundK.lo and boundK.hi <= boundS.lo
            # leaf scalar products R <= Xi n^p
            R = st["nu"][-1] * st["sides"][-1] ** 3
            Xi = r * (1 + r * m) * st["n_star"] ** 3
            assert ln_int(R).hi <= (ln_int(Xi) + p * ln_int(n)).lo
        results.append((name, r, m, A, B))
    # unrolled seeds: the leaf products are a rank decomposition of MM_n
    for name, sch in schemes.items():
        for n in [2, 3, 4, 5, 6]:
            terms = []

            def leaf(u, v):
                if not u or not v:
                    return Form()
                terms.append((u, v))
                return Form({len(terms) - 1: 1})
            X = [[Form({("x", i, j): 1}) for j in range(n)] for i in range(n)]
            Y = [[Form({("y", i, j): 1}) for j in range(n)] for i in range(n)]
            Z, st = pooled_recursion(sch, X, Y, leaf, Form())
            tensor = Counter()
            wforms = [dict() for _ in terms]
            for i in range(n):
                for l in range(n):
                    for t, c in Z[i][l].items():
                        wforms[t][i, l] = c
            for (u, v), w in zip(terms, wforms):
                for (ku, cu), (kv, cv), (kw, cw) in product(u.items(), v.items(), w.items()):
                    tensor[ku, kv, kw] += cu * cv * cw
            want = {(("x", i, j), ("y", j, l), (i, l)): 1 for i in range(n) for j in range(n) for l in range(n)}
            assert {k: v for k, v in tensor.items() if v} == want
            Xi = sch["r"] * (1 + sch["r"] * sch["m"]) * st["n_star"] ** 3
            assert len(terms) <= st["nu"][-1] * st["sides"][-1] ** 3
    return results


# ---------------------------------------------------------------------------
# 8. The uniform algorithm: selection rule and rate
# ---------------------------------------------------------------------------

C_SEL = 3000


def select_v(X):
    """Largest v>=1 with C_SEL * v * U(v) <= X (U is nondecreasing), or 0."""
    if C_SEL * U_of_v(1) > X:
        return 0
    lo, hi = 1, 2
    while C_SEL * hi * U_of_v(hi) <= X:
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if C_SEL * mid * U_of_v(mid) <= X:
            lo = mid
        else:
            hi = mid
    return lo


def uniform_rate_table(Xs):
    """For X = floor(log2 n): the selected v, a guaranteed lower bound f, and the rate.

    Checked: v(X) >= f, where f is the floor of a certified lower bound for
    y = (X/(1.2e13 Lambda(X)^3))^(2/11), Lambda(X) = ln(4096 X); and, when
    f >= 1, (1/v)^11 <= 478^11 Lambda^6 / X^2, i.e.
    1/v <= 478 Lambda^(6/11) X^(-2/11).
    """
    assert 2 ** 11 * (12 * 10 ** 12) ** 2 <= 478 ** 11
    X0 = 2 * 10 ** 18                        # threshold of Theorem 12: y >= 1 there
    assert X0 >= 12 * 10 ** 12 * ln_int(4096 * X0).hi ** 3
    rows = []
    for X in Xs:
        v = select_v(X)
        lam = ln_int(4096 * X)
        y11_lo = (Fr(X) / (Fr(12 * 10 ** 12) * lam.hi ** 3)) ** 2    # lower bound for y^11
        lo, hi = 0, 1
        while Fr(hi) ** 11 <= y11_lo:
            hi *= 2
        while hi - lo > 1:                     # largest f with f^11 <= y11_lo
            mid = (lo + hi) // 2
            if Fr(mid) ** 11 <= y11_lo:
                lo = mid
            else:
                hi = mid
        f = lo
        assert v >= f
        if f >= 1:
            assert Fr(X) ** 2 <= Fr(478 * v) ** 11 * lam.lo ** 6
        rows.append(dict(log2n=X, v=v, f=f, delta_new=(0.51 / v if v else None),
                         formula=243.8 * math.log(4096 * X) ** (6 / 11) * X ** (-2 / 11),
                         delta_v5=547200 / math.log2(X)))
    return rows


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--quick", action="store_true", help="skip the eps=1/8 literal chain")
    args = ap.parse_args()

    print("[3] uniform schedule inequalities (round-11 budget, Theorem 7 and Proposition 8 constants)")
    eps_list = [Fr(1), Fr(9, 10), Fr(2, 3), Fr(1, 2), Fr(3, 7), Fr(1, 3), Fr(1, 4), Fr(1, 5),
                Fr(1, 7), Fr(1, 8), Fr(1, 10), Fr(1, 16), Fr(1, 100), Fr(1, 1000), Fr(3, 1024),
                Fr(1, 2 ** 20), Fr(7, 2 ** 30), Fr(1, 2 ** 40), Fr(1, 2 ** 80)]
    worst = 0.0
    for e in eps_list:
        row = uniform_certificate(e)
        worst = max(worst, row["excess_over_eps"])
    print(f"    {len(eps_list)} allowances pass; max certified (Phi-9/4)/eps = {worst:.4f} < 719/1988")
    for v in list(range(1, 65)) + [100, 1000, 10 ** 4, 10 ** 6, 10 ** 9]:
        check_U_bound(v)
    print("    U(v) <= 4e9 v^(9/2) ln(4096 v)^3 for v=1..64 and five larger v")

    print("[4] literal chains (complete counts, certified logs)")
    lits = [Fr(1), Fr(1, 2), Fr(1, 4)] + ([] if args.quick else [Fr(1, 8)])
    for e in lits:
        row = literal_report(e)
        print("    eps={eps}: D={D} J={J} N=k={n} p in [{p0:.9f},{p1:.9f}] Phi<{Phi:.9f}".format(
            p0=row["p"][0], p1=row["p"][1], Phi=row["Phi_upper"], **row))
        print("      digits: A~{:.4e} B~{:.4e} r~{:.4e} m~{:.4e} n0 in [{:.4e},{:.4e}]".format(
            row["log10A"], row["log10B"], row["log10r"], row["log10m"], *row["log10n0"]))
        print("      log r/log A<={:.3f} log B/log A<={:.3f} log n0/log A<={:.2f} depth in [{:.1f},{:.1f}]"
              " defect<{:.3f}".format(row["log_r_over_log_A"], row["log_B_over_log_A"],
                                      row["log_n0_over_log_A"], row["depth"][0], row["depth"][1],
                                      row["geometric_defect"]))

    print("[5] height/precision envelopes:", height_envelopes())

    print("[6] separator (M=1..4), finite differences (E<=40), rational convolution (r,b<=4),"
          " chain bases (d<=5,b<=6)")
    assert all(separator_check(M) for M in range(1, 5))
    assert finite_difference_check(40)
    assert all(rational_convolution_check(r, b) for r in range(1, 5) for b in range(1, 5))
    assert all(chain_basis_check(d, b, c) for d in range(2, 6) for b in range(2, 7) for c in range(1, b))
    print("    all pass")

    print("[7] pooled recursion on toy schemes:", [t[0] for t in toy_pooled_checks()])

    print("[8] uniform algorithm: X=floor(log2 n), selected v, guaranteed floor, rate")
    for row in uniform_rate_table([10 ** 18, 10 ** 20, 10 ** 24, 10 ** 30, 10 ** 40, 10 ** 60, 10 ** 100]):
        print("    X=1e{:d}: v={} (>= {}), 0.51/v={:.3e}, 243.8*Lam^(6/11)X^(-2/11)={:.3e}, v5 bound={:.1f}".format(
            len(str(row["log2n"])) - 1, row["v"], row["f"], row["delta_new"], row["formula"], row["delta_v5"]))
    print("all checks passed")


if __name__ == "__main__":
    main()
