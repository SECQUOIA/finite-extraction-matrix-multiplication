"""Exact checks for docs/shifted-chains-check-recycling.md (key "recycling").

Run from the repository root:

    python -I experiments/shifted_chains_check_recycling.py [--quick]

The script imports nothing from the repository.  Every assertion uses exact
integers or Fractions; logarithms are enclosed in rational intervals with
outward rounding (fixed point, scale 2^-320).  Floats appear only in the
printed summaries, except the recycling factors of Part 5, which are printed
as certified bounds.

Parts
  1. Identities behind Lemmas 1-3 of the lower-bound proof (polynomial
     expansion), the endpoint coefficients, the start inequality.
  2. Type-count lemma (Lemma 4 (a)-(d)) on finite ranges.
  3. Lemma R (supply / forward recycling) as a literal restriction: a toy
     chain whose stages are exact restrictions of the stage shape
     X (T (x) MM_U) >= Y (T' (x) MM_V); the bank composition is applied to
     actual tensors and compared with m_* MM_{B'} term by term.
  4. Random chain schemes of the class (blocks, swaps, crops, terminal t):
     exact counts, every supply inequality, the recycling floors, the
     funding lemma, m_* = (B/t^{2P})^3 and m_* >= Abar^3 (s/t)^{6P} when
     p <= 3, the endpoint inequality, and Step 2 / Proposition T
     ingredients when p <= 12/5.
  5. The main construction at eps = 1, 1/2 (and 1/4, 1/9 without --quick):
     exact maximal types, interval logarithms of all counts, the recycled
     scheme with S = 4 J D^{2nk}, funding at every level, p and p', the
     bounds on log A', log B', log m_*, log r_*, and the proof ingredients.
     Certified recycling factors: the exact decimal digit counts of A and A'
     and their ratio, and an enclosure of log A / log A', rounded outward to
     4 decimals (the paper quotes the eps = 1 digit counts after
     Corollary 7.13; the README lists the ratios).
  6. A grid of rational eps down to 2^-200: every inequality of the proofs
     of the recycled-construction bounds, the thresholds of the lower
     bounds, and the table of upper/lower ratios.
  7. Rational constants.
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from fractions import Fraction as Fr
from math import comb, isqrt

sys.set_int_max_str_digits(0)

# ---------------------------------------------------------------------------
# Interval logarithms (fixed point, scale 2^-W, outward rounding).

W = 320
ONE = 1 << W


def _atanh_fixed(a, b):
    """Integers lo <= 2^W atanh(a/b) <= hi, for integers 0 <= 3a <= b."""
    assert b > 0 and 0 <= 3 * a <= b
    if a == 0:
        return 0, 0
    total, j, num, den = 0, 0, a, b
    a2, b2 = a * a, b * b
    while True:
        total += (num << W) // (den * (2 * j + 1))
        j += 1
        num *= a2
        den *= b2
        if (num << W) < den:
            break
    # j floors lose < j units; the tail is < z^(2j+1)/(1-z^2) <= 9/8 unit.
    return total, total + j + 2


def _ceil_div(a, b):
    return -((-a) // b)


class Iv:
    """Closed interval [lo, hi] * 2^-W with integer endpoints."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        assert lo <= hi
        self.lo, self.hi = lo, hi

    @staticmethod
    def of(x):
        x = Fr(x)
        return Iv((x.numerator << W) // x.denominator,
                  _ceil_div(x.numerator << W, x.denominator))

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv.of(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, Iv) else Iv.of(o)
        return Iv(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return Iv.of(o) - self

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __mul__(self, c):
        if isinstance(c, Iv):
            assert self.lo >= 0 and c.lo >= 0
            return Iv((self.lo * c.lo) >> W, _ceil_div(self.hi * c.hi, ONE))
        c = Fr(c)
        u, v = c.numerator, c.denominator
        if c >= 0:
            return Iv((self.lo * u) // v, _ceil_div(self.hi * u, v))
        return Iv((self.hi * u) // v, _ceil_div(self.lo * u, v))

    __rmul__ = __mul__

    @property
    def flo(self):
        return Fr(self.lo, ONE)

    @property
    def fhi(self):
        return Fr(self.hi, ONE)

    def __float__(self):
        return (self.lo + self.hi) / 2 / ONE


_t = _atanh_fixed(1, 3)
LN2 = Iv(2 * _t[0], 2 * _t[1])
_LNCACHE = {}


def ln_int(N):
    """Interval for log N, N a positive integer."""
    assert N >= 1
    if N in _LNCACHE:
        return _LNCACHE[N]
    if N == 1:
        res = Iv(0, 0)
    else:
        e = N.bit_length() - 1
        if e <= 400:
            lo, hi = _atanh_fixed(N - (1 << e), N + (1 << e))
            res = Iv(2 * lo, 2 * hi) + LN2 * e
        else:
            sh = e - 400
            m = N >> sh
            res = Iv(ln_int(m).lo, ln_int(m + 1).hi) + LN2 * sh
    if N.bit_length() <= 2000:
        _LNCACHE[N] = res
    return res


def ln_frac(x):
    x = Fr(x)
    assert x > 0
    return ln_int(x.numerator) - ln_int(x.denominator)


def g_of(d):
    """g_d = log((d+2)/d) = 2 atanh(1/(d+1))."""
    lo, hi = _atanh_fixed(1, d + 1)
    return Iv(2 * lo, 2 * hi)


LNK = ln_frac(Fr(21, 20))


def lam_bounds(d, bits=400):
    """Rational lo <= lambda_d <= hi; lambda_d > 0 is the root of q x^2 + x - d."""
    q = d + 2
    N = 1 + 4 * q * d
    s = isqrt(N << (2 * bits))
    lo = Fr(s, 1 << bits)
    hi = Fr(s + 1, 1 << bits)
    if lo * lo == N:
        hi = lo
    lam_lo, lam_hi = (lo - 1) / (2 * q), (hi - 1) / (2 * q)
    assert q * lam_lo ** 2 + lam_lo - d <= 0 <= q * lam_hi ** 2 + lam_hi - d
    return lam_lo, lam_hi


_ACACHE = {}


def a_of(d):
    """a_d = -log lambda_d (interval)."""
    if d not in _ACACHE:
        lo, hi = lam_bounds(d)
        _ACACHE[d] = Iv((-ln_frac(hi)).lo, (-ln_frac(lo)).hi)
    return _ACACHE[d]


# ---------------------------------------------------------------------------
# Part 1: identities (sparse polynomial expansion over Q).

def padd(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            v = out.get(e, 0) + c
            if v:
                out[e] = v
            else:
                out.pop(e, None)
    return out


def pmul(*ps):
    out = {(0,) * len(next(iter(ps[0]))): Fr(1)} if ps[0] else {}
    for p in ps:
        new = {}
        for e1, c1 in out.items():
            for e2, c2 in p.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                v = new.get(e, 0) + c1 * c2
                if v:
                    new[e] = v
                else:
                    new.pop(e, None)
        out = new
    return out


def pconst(c, nv):
    return {(0,) * nv: Fr(c)} if c else {}


def pvar(i, nv):
    return {tuple(1 if j == i else 0 for j in range(nv)): Fr(1)}


def pscale(p, c):
    return {e: v * c for e, v in p.items() if v * c}


def check_identities():
    nv = 4  # variables q, lam, R, B
    q, lam, R, B = (pvar(i, nv) for i in range(nv))
    one = pconst(1, nv)
    d = padd(q, pconst(-2, nv))

    def Qf(x, y):
        return padd(pmul(x, x), pscale(pmul(x, y), 4), pmul(y, y))

    dBR = padd(pmul(d, B), pscale(R, -1))                     # dB - R = q*T1
    lhs1 = pmul(q, q, q, lam, lam, Qf(R, B))                  # q^3 lam^2 Q(R,B)
    # q^3 Q(T1, R) with T1 = (dB-R)/q:
    qT = padd(pmul(q, dBR, dBR), pscale(pmul(q, q, dBR, R), 4), pmul(q, q, q, R, R))
    ql1 = padd(pmul(q, lam), one)                             # q*beta = q lam + 1
    one_minus_b2 = padd(pmul(q, q, q), pscale(pmul(q, ql1, ql1), -1))  # q^3(1-beta^2)
    RlB = padd(R, pscale(pmul(lam, B), -1))
    f = padd(pmul(q, lam, lam), lam, pscale(d, -1))
    bracket = padd(pscale(pmul(q, R, R), 2),
                   pmul(padd(pscale(q, 4), pscale(pmul(q, lam), -2), pconst(-2, nv)), R, B),
                   pmul(padd(pmul(q, lam, lam), lam, d), B, B))
    total = padd(lhs1, pscale(qT, -1), pscale(pmul(one_minus_b2, RlB, RlB), -1),
                 pscale(pmul(q, f, bracket), -1))
    assert total == {}, "Lemma 1 identity fails"

    # Gap identity (1 - z^4) f(z^3) = z^3 (1-z)^2 (1-z^2) with q = 2/(1-z^4):
    # (1-z^4) f(z^3) = 2 z^6 + (1-z^4) z^3 - 2 + 2(1-z^4).
    nz = 1
    z = pvar(0, nz)
    c1 = pconst(1, nz)

    def zp(k):
        return {(k,): Fr(1)}

    one_m_z4 = padd(c1, pscale(zp(4), -1))
    lhs = padd(pscale(zp(6), 2), pmul(one_m_z4, zp(3)), pconst(-2, nz), pscale(one_m_z4, 2))
    one_m_z = padd(c1, pscale(z, -1))
    rhs = pmul(zp(3), one_m_z, one_m_z, padd(c1, pscale(zp(2), -1)))
    assert padd(lhs, pscale(rhs, -1)) == {}, "gap identity fails"

    # Endpoint: (4/9)^5 (u^2+4u+8/3)^5 - K^10 (u+1)^8 has positive coefficients.
    u = pvar(0, 1)
    base = padd(pmul(u, u), pscale(u, 4), pconst(Fr(8, 3), 1))
    p5 = pmul(base, base, base, base, base)
    u1 = padd(u, pconst(1, 1))
    p8 = pmul(*([u1] * 8))
    K10 = Fr(21, 20) ** 10
    diff = padd(pscale(p5, Fr(4, 9) ** 5), pscale(p8, -K10))
    coeffs = [diff.get((i,), Fr(0)) for i in range(11)]
    assert all(c > 0 for c in coeffs), "endpoint coefficients"
    # Start: s^2 - (2/3)(s+1/3)^2 = ((s-2)(9s+6)+10)/27 > 0 for s >= 2.
    for s in range(2, 200):
        v = s * s - Fr(2, 3) * (s + Fr(1, 3)) ** 2
        assert v == Fr((s - 2) * (9 * s + 6) + 10, 27) and v > 0
    # Gap lemma numerically: omega_d - 9/4 >= 1/(24 q^2), lambda_d < (d/q)^(3/4).
    for d in list(range(2, 61)) + [100, 400, 1000]:
        q = d + 2
        lam_lo, lam_hi = lam_bounds(d)
        assert lam_hi ** 4 * q ** 3 < d ** 3
        om = a_of(d) * 3
        g = g_of(d)
        assert om.flo - Fr(9, 4) * g.fhi >= g.fhi / (24 * q * q)   # (omega-9/4) g >= g/(24q^2)
        assert g.fhi <= Fr(2, d)
    return float(min(coeffs))


# ---------------------------------------------------------------------------
# Part 2: type counts.

def type_count(n, d, l, o):
    return comb(n, l) * comb(n - l, o) * (d - 1) ** l * 2 ** o


def max_type(n, d):
    """Exact maximiser of the type count (separable concave; greedy from a
    point below every maximiser, using a_i >= (n+1)p_i - 1)."""
    w = (d - 1, 2, 1)
    q = d + 2
    a = [max(0, _ceil_div((n + 1) * wi, q) - 1) for wi in w]
    assert sum(a) <= n
    while sum(a) < n:
        # largest marginal w_i/(a_i+1)
        best = 0
        for i in (1, 2):
            if w[i] * (a[best] + 1) > w[best] * (a[i] + 1):
                best = i
        a[best] += 1
    return a


def max_count(n, d):
    l, o, m = max_type(n, d)
    return type_count(n, d, l, o)


def check_type_lemmas(nmax=30, dmax=40):
    pairs = 0
    for n in range(1, nmax + 1):
        for d in range(2, dmax + 1):
            q = d + 2
            best = 0
            for l in range(n + 1):
                for o in range(n - l + 1):
                    M = type_count(n, d, l, o)
                    best = max(best, M)
                    assert M <= q ** n                                  # (a)
                    if M > d ** n:
                        assert n >= 3 and d <= 2 * n                    # (b)
                    if n >= 3 and d <= 2 * n:
                        assert 2 * M <= q ** n                          # (c)
            assert best == max_count(n, d)
            assert best * (n + 1) ** 2 >= q ** n                        # upper note Lemma 6
            pairs += 1
    # (d): n >= 2q  ==>  M <= 4e q^(n+1)/n, checked with 4e < 10874/1000.
    big = 0
    for d in range(2, 21):
        q = d + 2
        for n in range(2 * q, 2 * q + 61, 3):
            M = max_count(n, d)
            assert M * n * 1000 <= 10874 * q ** (n + 1)
            big += 1
    return pairs, big


# ---------------------------------------------------------------------------
# Part 3: Lemma R as a literal restriction on a toy chain.

def strassen():
    """Seven triples (u_c, v_c, w_c) of forms on MM_2 variables with
    sum_c u_c v_c w_c = MM_2 = sum x_ij y_jk z_ki (0-indexed)."""
    U = [{(0, 0): 1, (1, 1): 1}, {(1, 0): 1, (1, 1): 1}, {(0, 0): 1}, {(1, 1): 1},
         {(0, 0): 1, (0, 1): 1}, {(1, 0): 1, (0, 0): -1}, {(0, 1): 1, (1, 1): -1}]
    V = [{(0, 0): 1, (1, 1): 1}, {(0, 0): 1}, {(0, 1): 1, (1, 1): -1}, {(1, 0): 1, (0, 0): -1},
         {(1, 1): 1}, {(0, 0): 1, (0, 1): 1}, {(1, 0): 1, (1, 1): 1}]
    Cmap = {(0, 0): {0: 1, 3: 1, 4: -1, 6: 1}, (0, 1): {2: 1, 4: 1},
            (1, 0): {1: 1, 3: 1}, (1, 1): {0: 1, 1: -1, 2: 1, 5: 1}}
    Wz = [dict() for _ in range(7)]
    for (i, k), cs in Cmap.items():
        for c, sg in cs.items():
            Wz[c][(k, i)] = sg
    return [U, V, Wz]


STRASSEN = strassen()


def apply_restriction(T, legmap):
    """legmap(leg, var) -> dict target var -> coeff (empty dict = 0)."""
    out = {}
    cache = [{}, {}, {}]
    for (u, v, w), c0 in T.items():
        forms = []
        for leg, var in enumerate((u, v, w)):
            f = cache[leg].get(var)
            if f is None:
                f = legmap(leg, var)
                cache[leg][var] = f
            if not f:
                break
            forms.append(f)
        else:
            A, B, C = forms
            for a, ca in A.items():
                for b, cb in B.items():
                    cab = c0 * ca * cb
                    for c, cc in C.items():
                        key = (a, b, c)
                        val = out.get(key, 0) + cab * cc
                        if val:
                            out[key] = val
                        else:
                            del out[key]
    return out


def lagrange_rows(n):
    """varpi[l][g]: coefficient of xi^g in prod_{j != l} (xi-j)/(l-j), nodes 1..n."""
    rows = []
    for l in range(1, n + 1):
        poly = [Fr(1)]
        den = Fr(1)
        for j in range(1, n + 1):
            if j == l:
                continue
            poly = [Fr(0)] + poly
            for t in range(len(poly) - 1):
                poly[t] -= j * poly[t + 1]
            den *= (l - j)
        rows.append([c / den for c in poly])
    return rows


def conv_tensor(r, b):
    return {(((), (al,)), ((), (be,)), ((), (al + be,))): Fr(1) for al in range(r) for be in range(b)}


def run_toy_chain(S, f_choice):
    """Two toy stages of the stage shape X (T (x) MM_U) >= Y (T' (x) MM_V):
    crop C(2,2) >= C(2,1) (resp. C(2,1) >= C(1,1)) tensored with Y copies of
    Strassen (x) id: 7Y MM_U >= Y MM_{2U}.  Stage 1: U=2, Y=1; stage 2: U=3, Y=2.
    Source: 3 MM_1 >= C(2,2) (v5 Lemma 9.1(a), nodes 1,2,3).
    f_choice(i, beta_prev, U) gives f_i.  Returns (r_*, m_*, S, B', ok)."""
    s, (U1, Y1), (U2, Y2) = 3, (2, 1), (3, 2)
    X1, X2 = 7 * Y1, 7 * Y2
    V1, V2 = 2 * U1, 2 * U2
    f1 = f_choice(1, S, U1)
    assert 1 <= f1 and U1 * f1 <= S
    b1 = f1 * V1
    f2 = f_choice(2, b1, U2)
    assert 1 <= f2 and U2 * f2 <= b1
    b2 = f2 * V2
    r_star, m_star = s * X1 * X2, Y1 * Y2
    # source tensor r_* MM_S, copies indexed (c0, c1, c2)
    T = {}
    for c0 in range(s):
        for c1 in range(X1):
            for c2 in range(X2):
                tag = (c0, c1, c2)
                for a in range(S):
                    for b in range(S):
                        for c in range(S):
                            T[((tag, (a, b)), (tag, (b, c)), (tag, (c, a)))] = Fr(1)
    vp = lagrange_rows(s)

    # step 0: s MM_1 >= C(2,2) in every group (c1, c2), identity on MM_S
    def step0(leg, var):
        (c0, c1, c2), mm = var
        node = c0 + 1
        if leg == 0:
            form = {(al,): Fr(node) ** al for al in range(2)}
        elif leg == 1:
            form = {(be,): Fr(node) ** be for be in range(2)}
        else:
            form = {(ga,): vp[c0][ga] for ga in range(3) if vp[c0][ga]}
        return {((c1, c2), tv, mm): cf for tv, cf in form.items()}

    T = apply_restriction(T, step0)
    expect = {}
    for c1 in range(X1):
        for c2 in range(X2):
            for (xa, yb, zc), cf in conv_tensor(2, 2).items():
                for a in range(S):
                    for b in range(S):
                        for c in range(S):
                            expect[(((c1, c2), xa[1], (a, b)), ((c1, c2), yb[1], (b, c)),
                                    ((c1, c2), zc[1], (c, a)))] = cf
    assert T == expect, "source evaluation"

    def stage(keep, U, f, Y, beta_prev, which):
        def m(leg, var):
            copies, tv, (a, b) = var
            if not keep(leg, tv):
                return {}
            if a >= U * f or b >= U * f:        # principal block MM_beta >= MM_{U f}
                return {}
            aU, af = divmod(a, f)               # MM_{U f} = MM_U (x) MM_f
            bU, bf = divmod(b, f)
            cidx = copies[which]
            y, c = divmod(cidx, 7)
            assert y < Y
            out = {}
            for (i, j), sg in STRASSEN[leg][c].items():
                # MM_2 (x) MM_U = MM_{2U}, then (x) MM_f = MM_{2U f}
                na = (i * U + aU) * f + af
                nb = (j * U + bU) * f + bf
                newc = list(copies)
                newc[which] = y
                out[(tuple(newc), tv, (na, nb))] = Fr(sg)
            return out
        return m

    def keep1(leg, tv):   # C(2,2) >= C(2,1): y_beta with beta < 1, z_gamma with gamma < 2
        return tv[0] < (2, 1, 2)[leg]

    def keep2(leg, tv):   # C(2,1) >= C(1,1)
        return tv[0] < 1

    T = apply_restriction(T, stage(keep1, U1, f1, Y1, S, 0))
    T = apply_restriction(T, stage(keep2, U2, f2, Y2, b1, 1))
    target = {}
    for y1 in range(Y1):
        for y2 in range(Y2):
            tag = (y1, y2)
            for a in range(b2):
                for b in range(b2):
                    for c in range(b2):
                        target[((tag, (0,), (a, b)), (tag, (0,), (b, c)), (tag, (0,), (c, a)))] = Fr(1)
    ok = T == target
    return r_star, m_star, S, b2, ok


def check_toy_chain():
    # Strassen itself
    T = {(((c,), ()), ((c,), ()), ((c,), ())): Fr(1) for c in range(7)}

    def sm(leg, var):
        return dict(STRASSEN[leg][var[0][0]])
    res = apply_restriction(T, sm)
    mm2 = {((a, b), (b, c), (c, a)): Fr(1) for a in range(2) for b in range(2) for c in range(2)}
    assert res == mm2, "Strassen"
    out = []
    # (i) recycling supply with S = 5 (floors 5 -> 4, 8 -> 6),
    # (ii) minimal supply S = 2, (iii) S = 6 = U1 U2 reproduces the source supply.
    for S in (5, 2, 6):
        r, m, S_, b2, ok = run_toy_chain(S, lambda i, beta, U: beta // U)
        assert ok, "toy chain restriction fails for S=%d" % S
        out.append((S_, r, m, b2))
    # source-supply pattern f_1 = U2, f_2 = V1 at S = A = 6 gives B = V1 V2 = 24
    r, m, S_, b2, ok = run_toy_chain(6, lambda i, beta, U: 3 if i == 1 else 4)
    assert ok and b2 == 24
    # non-maximal supply: S = 6, f1 = 1, f2 = 1 gives B' = 6 (still a restriction)
    r, m, S_, b2, ok = run_toy_chain(6, lambda i, beta, U: 1)
    assert ok and b2 == 6
    return out


# ---------------------------------------------------------------------------
# Part 4: chain schemes with blocks; exact bookkeeping.

class Scheme:
    """A chain scheme of the class: pairs, arities, blocks (n,k,M), terminal t."""

    def __init__(self, pairs, arities, blocks, P, t):
        self.pairs, self.arities, self.blocks, self.P, self.t = pairs, arities, blocks, P, t
        self.J = len(arities)
        r0, b0 = pairs[0]
        self.s = r0 + b0 - 1
        self._exact = False

    def exact(self):
        """Exact integers U_i, V_i, X_i, Y_i (computed on demand)."""
        if self._exact:
            return
        self._exact = True
        P = self.P
        self.U = [d ** (2 * P) for d in self.arities]
        self.V, self.X, self.Y = [], [], []
        for i, bl in enumerate(self.blocks):
            V = X = Y = 1
            for (n, k, M) in bl:
                E = 1 + 6 * k * (M - 1)
                V *= M ** (2 * k)
                X *= E * (2 * M - 1) ** (6 * k)
                Y *= M ** (6 * k)
            self.V.append(V)
            self.X.append(X)
            self.Y.append(Y)

    def counts(self):
        self.exact()
        A = B = r = m = 1
        for i in range(self.J):
            A *= self.U[i]
            B *= self.V[i]
            r *= self.X[i]
            m *= self.Y[i]
        B *= self.t ** (2 * self.P)
        r *= self.s ** (6 * self.P)
        return A, B, r, m

    def bank(self, S, fsel):
        self.exact()
        beta = S
        betas = [S]
        for i in range(self.J):
            f = fsel(i, beta)
            assert 1 <= f and self.U[i] * f <= beta
            beta = f * self.V[i]
            betas.append(beta)
        return betas, self.t ** (2 * self.P) * beta


def legal_step(r, b, d, c):
    return r >= 1 and d >= 2 and c >= 1 and (d + 2) * c <= d * b - r + 1


def random_scheme(rng, maxent=24, dmax=8):
    large = rng.random() < 0.5
    while True:
        r0, b0 = rng.randint(1, maxent), rng.randint(2, maxent)
        if rng.random() < 0.5:
            r0, b0 = b0, r0
        P = rng.choice([1, 2, 3, 4, 6, 8, 12, 16])
        if large:
            P = rng.choice([256, 512, 1024])
        pairs, ars, blocks = [(r0, b0)], [], []
        for _ in range(rng.randint(1, 5)):
            u, v = pairs[-1]
            opts = []
            for (r, b) in {(u, v), (v, u)}:
                for d in range(2, dmax + 1):
                    cm = (d * b - r + 1) // (d + 2)
                    if cm >= 1:
                        opts.append((r, b, d, cm))
            if not opts:
                break
            r, b, d, cm = rng.choice(opts)
            c = rng.randint(max(1, cm - 2), cm) if not large else cm
            assert legal_step(r, b, d, c) and c < b
            new = (c, r)
            if rng.random() < 0.25 and not large:
                new = (rng.randint(1, new[0]), rng.randint(1, new[1]))
            bl, rem = [], P
            while rem > 0:
                if large:
                    n = rng.choice([32, 64, 128])
                    k = min(rem // n, rng.choice([4, 8, 16]))
                    if k == 0:
                        n, k = rem, 1
                else:
                    k = rng.randint(1, rem)
                    n = rng.randint(1, rem // k)
                if large or rng.random() < 0.5:
                    l, o, _ = max_type(n, d)
                else:
                    l = rng.randint(0, n)
                    o = rng.randint(0, n - l)
                bl.append((n, k, type_count(n, d, l, o)))
                rem -= n * k
            ars.append(d)
            blocks.append(bl)
            pairs.append(new)
        if ars:
            t = max(pairs[-1]) if large else rng.randint(1, max(pairs[-1]))
            return Scheme(pairs, ars, blocks, P, t)


def ramp_scheme(R, stop, blocks_nk, t_max=True):
    """Forward ramp from (R,R) down to (stop,stop) (arities 3j, 3j-1), each
    stage with the blocks blocks_nk = [(n,k), ...] and maximal types."""
    pairs, ars = [(R, R)], []
    for j in range(R - 1, stop - 1, -1):
        for d, new in ((3 * j, (j, j + 1)), (3 * j - 1, (j, j))):
            r, b = pairs[-1]
            # (j+1,j+1) -> (j, j+1) and (j, j+1) -> (j, j): split b, keep r
            if not legal_step(r, b, d, new[0]) or new[1] != r:
                r, b = b, r
            assert legal_step(r, b, d, new[0]) and new[1] == r
            ars.append(d)
            pairs.append(new)
    P = sum(n * k for n, k in blocks_nk)
    blocks = [[(n, k, max_count(n, d)) for n, k in blocks_nk] for d in ars]
    t = max(pairs[-1]) if t_max else 1
    return Scheme(pairs, ars, blocks, P, t)


def chain_main_shape(D, L):
    """Ramp from (1,1) to (8D,8D) (arities 3j-1, 3j), then L smallest-parent
    steps of arity D; forward order.  Returns (pairs, arities)."""
    R = 8 * D
    rev = []
    for j in range(1, R):
        rev += [3 * j - 1, 3 * j]
    rev += [D] * L
    pairs = [(1, 1)]
    for d in rev:
        r, b = pairs[-1]
        pairs.append((b, _ceil_div((d + 2) * r + b - 1, d)))
    pairs.reverse()
    ars = list(reversed(rev))
    for i, d in enumerate(ars):
        (rp, bp), (c, r2) = pairs[i], pairs[i + 1]
        assert r2 == rp and legal_step(rp, bp, d, c)
    return pairs, ars


def main_shape_scheme(D, L, n, k):
    pairs, ars = chain_main_shape(D, L)
    Ms = {d: max_count(n, d) for d in set(ars)}
    blocks = [[(n, k, Ms[d])] for d in ars]
    return Scheme(pairs, ars, blocks, n * k, 1)


def scheme_logs(sc):
    """Interval logs of A, B, r_*, m_*."""
    lnA = Iv(0, 0)
    lnV = Iv(0, 0)
    lnr = ln_int(sc.s) * (6 * sc.P)
    for i in range(sc.J):
        lnA = lnA + ln_int(sc.arities[i]) * (2 * sc.P)
        for (n, k, M) in sc.blocks[i]:
            lnV = lnV + ln_int(M) * (2 * k)
            lnr = lnr + ln_int(2 * M - 1) * (6 * k) + ln_int(1 + 6 * k * (M - 1))
    lnB = lnV + ln_int(sc.t) * (2 * sc.P)
    lnm = lnV * 3
    return lnA, lnB, lnr, lnm


def proof_ingredients(sc, lnA, lnB, lnr, lnm, p_hi, lnBA_supplied=None):
    """For p <= p0 := p_hi <= 12/5: endpoint (Lemma 2), Step 2 sum, the
    profitable-block facts used for m_*, Proposition T (1)-(2) and the
    (5/2) P log s bound.  Returns a small dict."""
    p0 = p_hi
    assert p0 <= Fr(12, 5)
    eps = p0 - Fr(9, 4)
    P = sc.P
    lns = ln_int(sc.s)
    # Lemma 2: log s >= log K + sum a_d + (4/5) log t
    sa = Iv(0, 0)
    sg = Iv(0, 0)
    for d in sc.arities:
        sa = sa + a_of(d)
        sg = sg + g_of(d)
    assert lns.flo >= (LNK + sa + ln_int(sc.t) * Fr(4, 5)).fhi
    # Step 2: sum_ij w_ij t_ij >= 3 log K (lower end of the interval sum)
    tot = Iv(0, 0)
    prof_lnd = Iv(0, 0)     # sum over profitable blocks of w log d (lower bound)
    nprof = 0
    for i, d in enumerate(sc.arities):
        q = d + 2
        om_g = a_of(d) * 3                       # omega_d g_d
        g = g_of(d)
        for (n, k, M) in sc.blocks[i]:
            w = Fr(n * k, P)
            E = 1 + 6 * k * (M - 1)
            Dij = ln_int(q) * n - ln_int(M)
            t = g * p0 - om_g - Dij * (p0 / n) - ln_int(E) * Fr(1, 2 * n * k)
            tot = tot + t * w
            if t.lo > 0:                         # certified profitable block
                nprof += 1
                assert M > d ** n                # Step 3: M > d^n on profitable blocks
                assert (om_g.fhi < p0 * g.flo)   # omega_d < p0
                prof_lnd = prof_lnd + ln_int(d) * w
    assert tot.flo >= 3 * LNK.fhi, "Step 2"
    # log m_* >= 6 P sum_I w log d  (certified direction)
    assert lnm.flo >= (prof_lnd * (6 * P)).fhi
    # Proposition T (1), (2):
    assert sg.flo * eps > 3 * LNK.fhi
    assert lns.flo * 4 * eps > 9 * LNK.fhi
    # log(B/A) >= log(r/m)/p0 >= (5/2) P log s
    lnBA = lnB - lnA
    assert lnBA.flo >= (lns * Fr(5 * P, 2)).fhi
    if lnBA_supplied is not None:
        assert lnBA_supplied.flo >= (lns * Fr(5 * P, 2)).fhi
    return dict(eps_eff=float(eps), profitable_blocks=nprof, step2_sum=float(tot),
                three_lnK=float(LNK * 3))


def supply_checks(sc, rng):
    A, B, r, m = sc.counts()
    P, t, J = sc.P, sc.t, sc.J
    tP = t ** (2 * P)
    assert B % tP == 0 and m == (B // tP) ** 3            # m_* = (B/t^{2P})^3
    # source supply reproduces (A, B)
    def fsrc(i, beta):
        f = 1
        for l in range(i + 1, J):
            f *= sc.U[l]
        for l in range(i):
            f *= sc.V[l]
        return f
    _, Bsrc = sc.bank(A, fsrc)
    assert Bsrc == B
    # random supplies: B' S... B'/S <= B/A
    for _ in range(3):
        S = rng.randint(sc.U[0], 3 * A + sc.U[0])
        beta = S
        ok = True
        for i in range(J):
            if beta < sc.U[i]:
                ok = False
                break
            beta = rng.randint(1, beta // sc.U[i]) * sc.V[i]
        if not ok:
            continue
        Bp = tP * beta
        assert Bp * A <= B * S
    # recycling supply with floors: exact floor inequality
    S = sc.U[0] * rng.randint(1, 50)
    betas = [S]
    ok = True
    for i in range(J):
        if betas[-1] < sc.U[i]:
            ok = False
            break
        betas.append((betas[-1] // sc.U[i]) * sc.V[i])
    if ok:
        Bp = tP * betas[-1]
        num, den = 1, 1
        for i in range(J):
            num *= betas[i] - sc.U[i]
            den *= betas[i]
        assert Bp * A <= B * S
        assert Bp * A * den >= B * S * num                 # floor losses
    # funding lemma: S >= 4 J max_i U_i prod_{l<i} U_l/V_l
    Ut = Fr(0)
    acc = Fr(1)
    for i in range(J):
        Ut = max(Ut, sc.U[i] * acc)
        acc *= Fr(sc.U[i], sc.V[i])
    S = _ceil_div((4 * J * Ut).numerator, (4 * J * Ut).denominator)
    betas, Bp = sc.bank(S, lambda i, beta: beta // sc.U[i])
    for i in range(J):
        assert betas[i] >= 2 * J * sc.U[i]
    assert Bp * A <= B * S and 2 * Bp * A >= B * S
    # m_* >= Abar^3 (s/t)^{6P} whenever B > A and p <= 3
    if B > A:
        lnA_, lnB_, lnr_, lnm_ = scheme_logs(sc)
        # decide p <= 3 exactly only when the interval does not decide it
        d3 = (lnr_ - lnm_) - (lnB_ - lnA_) * 3
        p_le_3 = d3.fhi <= 0 or (d3.flo <= 0 and r * A ** 3 <= m * B ** 3)
    else:
        p_le_3 = False
    if p_le_3:
        assert B >= A * sc.s ** (2 * P)
        assert m * t ** (6 * P) >= A ** 3 * sc.s ** (6 * P)
    # geometry: max entries nonincreasing; t <= s
    mx = [max(p) for p in sc.pairs]
    assert all(mx[i + 1] <= mx[i] for i in range(len(mx) - 1)) and sc.t <= sc.s
    return p_le_3, (S, Bp)


def check_random_schemes(count, seed=20261018):
    rng = random.Random(seed)
    n_rel = n_p3 = n_p125 = 0
    fixed = [ramp_scheme(R, stop, bnk, tm)
             for R, stop in ((3, 1), (4, 1), (5, 2), (6, 3))
             for bnk in ([(128, 16)], [(256, 8), (64, 32)], [(256, 32)])
             for tm in (True, False)]
    for idx in range(count + len(fixed)):
        sc = fixed[idx] if idx < len(fixed) else random_scheme(rng)
        sc.exact()
        p_le_3, (S, Bp) = supply_checks(sc, rng)
        A, B, r, m = sc.counts()
        if B > A:
            n_rel += 1
        n_p3 += p_le_3
        if B > A:
            lnA, lnB, lnr, lnm = scheme_logs(sc)
            p_hi = (lnr - lnm).fhi / (lnB - lnA).flo
            if p_hi <= Fr(12, 5):                           # certified p <= 12/5
                proof_ingredients(sc, lnA, lnB, lnr, lnm, p_hi)
                n_p125 += 1
    return dict(schemes=count + len(fixed), relative=n_rel, p_le_3=n_p3, p_le_12_5=n_p125)


def check_block_schemes():
    """Main-construction chain shapes with several blocks per stage (interval
    logs only): p, m_* >= Abar^3, and the proof ingredients at p0 = p."""
    rows = []
    for D, L, bnk in ((2, 128, [(2048, 1024), (1024, 2048)]),
                      (2, 128, [(4096, 1024), (512, 512), (1024, 256)]),
                      (3, 384, [(4096, 2048), (8192, 1024)])):
        pairs, ars = chain_main_shape(D, L)
        Ms = {}
        for d in set(ars):
            for n, _ in bnk:
                Ms[(n, d)] = max_count(n, d)
        blocks = [[(n, k, Ms[(n, d)]) for n, k in bnk] for d in ars]
        P = sum(n * k for n, k in bnk)
        sc = Scheme(pairs, ars, blocks, P, 1)
        lnA, lnB, lnr, lnm = scheme_logs(sc)
        p_hi = (lnr - lnm).fhi / (lnB - lnA).flo
        assert p_hi <= Fr(12, 5)
        assert lnm.flo >= 3 * lnA.fhi                       # m_* >= Abar^3
        ing = proof_ingredients(sc, lnA, lnB, lnr, lnm, p_hi)
        rows.append(dict(D=D, L=L, blocks=bnk, p_upper=float(p_hi), **ing))
    return rows


def check_main_shape_exact(cases):
    """Main-construction chain shapes with small (n,k): exact big-integer
    counts, all supply checks, and the proof ingredients."""
    rng = random.Random(7)
    rows = []
    for D, L, n, k in cases:
        sc = main_shape_scheme(D, L, n, k)
        p_le_3, (S, Bp) = supply_checks(sc, rng)
        A, B, r, m = sc.counts()
        lnA, lnB, lnr, lnm = scheme_logs(sc)
        p_hi = (lnr - lnm).fhi / (lnB - lnA).flo
        row = dict(D=D, L=L, n=n, k=k, levels=sc.J, p_upper=float(p_hi), p_le_3=p_le_3,
                   digits_A=len(str(A)), digits_A_funded=len(str(S)))
        if p_hi <= Fr(12, 5):
            lnBp = ln_int(Bp) - ln_int(S)
            row.update(proof_ingredients(sc, lnA, lnB, lnr, lnm, p_hi, lnBp))
        rows.append(row)
    return rows


# ---------------------------------------------------------------------------
# Part 5: the main construction (exact types, interval logs).

def schedule(eps):
    eps = Fr(eps)
    assert 0 < eps <= 1
    a, b = eps.numerator, eps.denominator
    D = isqrt((4 * b) // a)
    if D * D * a < 4 * b:
        D += 1
    assert D * D * a >= 4 * b and (D - 1) ** 2 * a < 4 * b
    R = 8 * D
    L = _ceil_div(64 * D * b, a)
    x = Fr(128 * D) / eps
    H = _ceil_div(x.numerator, x.denominator).bit_length()
    n = _ceil_div(256 * D * H * b, a)
    J = 16 * D - 2 + L
    return dict(eps=eps, D=D, R=R, L=L, x=x, H=H, n=n, k=n, J=J)


def Lam(eps):
    return ln_frac(4096 / Fr(eps))


C_AREC = Fr(532, 100) * 10 ** 6         # 5.32e6
C_BREC = Fr(15, 10) * 10 ** 9            # 1.5e9
C_LOGA = Fr(3, 1) * 10 ** 9              # main theorem: log A < 3e9 eps^-9/2 Lambda^3
C_LOGA_PROOF = Fr(2550252000)            # proof value of the main theorem


def check_main_instance(eps):
    sp = schedule(eps)
    eps = sp["eps"]
    D, L, n, k, J = sp["D"], sp["L"], sp["n"], sp["k"], sp["J"]
    pairs, ars = chain_main_shape(D, L)
    assert len(ars) == J and max(ars) == 24 * D - 3 and ars[0] == D
    P = n * k
    s = pairs[0][0] + pairs[0][1] - 1
    Ms = {d: max_count(n, d) for d in set(ars)}
    lnd = {d: ln_int(d) for d in Ms}
    lnM = {d: ln_int(M) for d, M in Ms.items()}
    lnA = Iv(0, 0)
    lnV = Iv(0, 0)
    lnr = ln_int(s) * (6 * P)
    for d in ars:
        M = Ms[d]
        lnA = lnA + lnd[d] * (2 * P)
        lnV = lnV + lnM[d] * (2 * k)
        lnr = lnr + ln_int(2 * M - 1) * (6 * k) + ln_int(1 + 6 * k * (M - 1))
    lnB = lnV
    lnm = lnV * 3
    lnBA = lnB - lnA
    lnrm = lnr - lnm
    p_lo, p_hi = lnrm.flo / lnBA.fhi, lnrm.fhi / lnBA.flo
    assert Fr(9, 4) < p_lo and p_hi < Fr(9, 4) + Fr(719, 1988) * eps
    # recycled: S = 4 J D^{2nk}; bank with maximal f_i; funding beta_{i-1} >= 2J U_i
    lnS = ln_int(4 * J) + lnd[D] * (2 * P)
    ell = lnS
    ln2J = ln_int(2 * J)
    loss = ln_int(2 * J - 1) - ln_int(2 * J)                      # log(1 - 1/(2J))
    min_slack = None
    for d in ars:
        lnU = lnd[d] * (2 * P)
        slack = ell.flo - (ln2J + lnU).fhi
        assert slack >= 0, "funding fails"
        min_slack = slack if min_slack is None else min(min_slack, slack)
        ell = Iv((ell - lnU + lnM[d] * (2 * k) + loss).lo, (ell - lnU + lnM[d] * (2 * k)).hi)
    lnBpAp = ell - lnS
    assert lnBpAp.flo >= (lnBA - LN2).flo          # B'/A' >= B/(2A)
    assert lnBpAp.flo <= lnBA.fhi                  # consistent with B'/A' <= B/A (exact in Part 4)
    pp_hi = lnrm.fhi / lnBpAp.flo
    assert pp_hi < Fr(9, 4) + eps / 2
    assert pp_hi - p_hi < eps / 10 ** 9
    Lm = Lam(eps)
    # bounds on the main construction (source supply)
    L3 = Lm * Lm * Lm
    assert lnA.fhi < C_LOGA_PROOF * L3.flo / (eps ** 4 * sqrt_hi(eps))
    assert lnm.fhi <= 6 * lnA.flo and lnr.fhi <= Fr(35, 4) * lnA.flo
    assert lnm.flo >= 3 * lnA.fhi                  # m_* >= Abar^3
    # recycled bounds
    assert lnS.fhi < C_AREC * L3.flo / eps ** 3
    assert ell.fhi < C_BREC * (Lm * Lm).flo / eps ** 4
    # proof ingredients at p0 = p_hi
    sc = Scheme(pairs, ars, [[(n, k, Ms[d])] for d in ars], P, 1)
    ing = proof_ingredients(sc, lnA, lnB, lnr, lnm, p_hi, lnBpAp)
    ln10 = ln_int(10)
    return dict(eps=str(eps), D=D, levels=J, n=n, recycling_factor=recycling_factor(lnA, lnS),
                p_upper=float(p_hi), p_recycled_upper=float(pp_hi),
                p_increase_upper=float(pp_hi - p_lo),
                digits_A=float(lnA.fhi / ln10.flo),
                digits_A_recycled=float(lnS.fhi / ln10.flo),
                digits_B=float(lnB.fhi / ln10.flo),
                digits_B_recycled=float(ell.fhi / ln10.flo),
                digits_m=float(lnm.fhi / ln10.flo), digits_r=float(lnr.fhi / ln10.flo),
                logm_over_logA=float(lnm.fhi / lnA.flo), logr_over_logA=float(lnr.fhi / lnA.flo),
                min_funding_slack_nats=float(min_slack), **ing)


def decimal_digits(ln_x):
    """floor(log10 x) + 1 from an enclosure of log x, x >= 1."""
    ln10 = ln_int(10)
    lo, hi = (ln_x.flo / ln10.fhi).__floor__(), (ln_x.fhi / ln10.flo).__floor__()
    assert lo == hi, "digit count not decided"
    return lo + 1


def outward(lo, hi, places=4):
    """'[a, b]' with a <= lo and b >= hi, for 0 <= lo <= hi, to `places` decimals."""
    scale = 10 ** places
    a, b = (lo * scale).__floor__(), _ceil_div((hi * scale).numerator, (hi * scale).denominator)
    return "[%d.%0*d, %d.%0*d]" % (a // scale, places, a % scale, b // scale, places, b % scale)


def recycling_factor(lnA, lnS):
    """Certified factors by which recycling divides the size of the source side."""
    digits_A, digits_S = decimal_digits(lnA), decimal_digits(lnS)
    ratio = Fr(digits_A, digits_S)
    return dict(decimal_digits_A=digits_A, decimal_digits_A_recycled=digits_S,
                digits_ratio=outward(ratio, ratio),
                log_ratio=outward(lnA.flo / lnS.fhi, lnA.fhi / lnS.flo))


def sqrt_hi(eps, bits=400):
    """A rational upper bound for eps^(1/2)."""
    eps = Fr(eps)
    return Fr(isqrt((eps.numerator << (2 * bits)) // eps.denominator) + 1, 1 << bits)


# ---------------------------------------------------------------------------
# Part 6: grid of eps.

def recycled_bounds_on_grid(eps):
    """Every inequality used in the proof of Corollary 5.2 (recycled main
    construction), from the schedule alone; returns the bound values."""
    sp = schedule(eps)
    eps = sp["eps"]
    D, R, L, x, H, n, k, J = (sp[t] for t in ("D", "R", "L", "x", "H", "n", "k", "J"))
    # parameter facts of the main theorem used here
    assert D >= 2 and x >= 256 and 2 ** H > x and H <= x and n >= 2 * x * H and n + 1 <= x ** 3
    a = ln_int(n + 1) * Fr(2, n)
    assert a.fhi <= 3 / x
    assert Fr(J) ** 2 * eps ** 3 <= 240 ** 2                     # J <= 240 eps^-3/2
    assert Fr(D) ** 2 * eps <= 9                                 # D <= 3 eps^-1/2
    Lm = Lam(eps)
    assert Fr(n) ** 2 * eps ** 3 <= 2305 ** 2 * Lm.flo ** 2      # n <= 2305 eps^-3/2 Lambda
    # (F1) every level gains: n g_d - 2 log(n+1) > 0 for all d <= 24D-3
    gmin = g_of(24 * D - 3)
    assert (gmin * n - ln_int(n + 1) * 2).flo > 0
    assert Fr(1, 12) - Fr(3, 128) > 0
    # (F2) the bulk pays for the ramp jump:
    #      L (n g_D - 2 log(n+1)) >= n log((24D-3)/D)  (divided by 2k)
    gD = g_of(D)
    lhs = (gD * n - ln_int(n + 1) * 2) * L
    rhs = ln_frac(Fr(24 * D - 3, D)) * n
    assert lhs.flo >= rhs.fhi
    assert (gD * L).flo >= 64 / eps and (a * L).fhi < 2
    # log A' = log(4J) + 2nk log D
    lnAp = ln_int(4 * J) + ln_int(D) * (2 * n * k)
    assert ln_int(4 * J).fhi <= (Lm * Fr(3, 2)).flo
    assert (ln_int(D) * 2).fhi <= Lm.flo
    L3 = (Lm * Lm * Lm)
    assert lnAp.fhi < C_AREC * L3.flo / eps ** 3
    # log(B/A) <= 2nk G with G <= L g_D + log(3R/2) + (1+log R)/3 < 128/eps + 1 + (2/3) Lambda
    lnF_hi = ln_frac(Fr(3 * R, 2)) + (Iv.of(1) + ln_int(R)) * Fr(1, 3)
    G_hi = gD * L + lnF_hi
    assert G_hi.fhi < 128 / eps + 1 + Fr(2, 3) * Lm.flo
    lnBA_hi = G_hi * (2 * n * k)
    lnBp_hi = lnAp.fhi + lnBA_hi.fhi
    assert lnBp_hi < C_BREC * (Lm * Lm).flo / eps ** 4
    # p' - p <= (11/4) log 2 / (log(B/A) - log 2), log(B/A) >= 2nk (497/512)(64/eps)
    lnBA_lo = Fr(2 * n * k) * Fr(497, 512) * 64 / eps
    inc = Fr(11, 4) * LN2.fhi / (lnBA_lo - LN2.fhi)
    assert inc < eps / 10 ** 9
    assert Fr(719, 1988) + Fr(1, 10 ** 9) < Fr(1, 2)
    # upper bounds on copy counts (source or recycled supply; same r_*, m_*)
    lnm_hi = (ln_int(24 * D - 1) * (6 * n * k * J)).fhi           # 3 log B <= 6nk sum log q
    return dict(eps=eps, D=D, n=n, J=J, Lambda=Lm, lnAp=lnAp.fhi, lnBp=lnBp_hi,
                lnBA_hi=lnBA_hi.fhi, lnm_hi=lnm_hi)


C_M = Fr(81, 21 * 1024 * 960)        # 81/(1024*96^{3/2}) * log(21/20) > this
C_ABAR = Fr(27, 21 * 1024 * 960)
C_BA = Fr(45, 458752)
C_AP = Fr(3, 4096)                    # times log 2


def lower_bounds(eps):
    """Lower bounds of Theorem 4.1 at allowance eps (requires eps < 1/9216)."""
    eps = Fr(eps)
    assert eps < Fr(1, 9216)
    x = ln_frac(1 / eps)
    # thresholds of Steps 3-5
    assert eps <= Fr(3, 20) and eps <= Fr(9, 64) and eps <= Fr(9, 16384)
    assert ln_frac(3 / (128 * eps)).flo >= x.fhi / 2
    # log D0 > x/4 with D0 = (96 eps)^-1/2  <=>  log(1/(96 eps)) > x/2
    assert ln_frac(1 / (96 * eps)).flo > x.fhi / 2
    x3 = (x * x * x).flo
    x2 = (x * x).flo
    sq_hi = sqrt_hi(eps)                 # eps^-9/2 >= 1/(eps^4 sq_hi)
    return dict(m=C_M * x3 / (eps ** 4 * sq_hi), Abar=C_ABAR * x3 / (eps ** 4 * sq_hi),
                BA=C_BA * x2 / eps ** 4, Ap=C_AP * LN2.flo * x2 / eps ** 3)


def check_grid(quick):
    grid = [Fr(1), Fr(1, 2), Fr(1, 3), Fr(4, 9), Fr(999, 1000), Fr(2, 3)]
    grid += [Fr(1, m) for m in range(4, 60 if quick else 400, 7)]
    grid += [Fr(4, D * D) for D in range(3, 40 if quick else 200, 3)]
    grid += [Fr(1, 2 ** j) for j in range(2, 201, 9 if quick else 3)]
    grid += [Fr(1, 10 ** j) for j in range(2, 61, 6)]
    grid += [Fr(1, 3 ** j) for j in range(2, 121, 13)]
    for e in grid:
        recycled_bounds_on_grid(e)
    # Closed-form crossover: for eps = 2^-26, the recycled bound
    # 5.32e6 eps^-3 Lambda^3 lies below the source-supply bound on log Abar at
    # allowance eps/2, C_ABAR (eps/2)^-9/2 log^3(2/eps).  The ratio of the two
    # is c eps^{3/2} ((log 4096 + y)/(log 2 + y))^3, y = log(1/eps), which
    # decreases with eps, so the inequality holds for every eps <= 2^-26.
    e = Fr(1, 2 ** 26)
    Lm = Lam(e)
    ub = C_AREC * (Lm * Lm * Lm).fhi / e ** 3
    l2 = ln_frac(2 / e)
    lb = C_ABAR * (l2 * l2 * l2).flo / ((e / 2) ** 4 * sqrt_hi(e / 2))
    assert ub < lb
    # table: main construction run at parameter eps (p < 9/4 + eps/2) against
    # the lower bounds at allowance eps/2.
    table = []
    for j in (16, 20, 24, 28, 32, 36, 40, 80, 120, 160, 200):
        e = Fr(1, 2 ** j)
        ub = recycled_bounds_on_grid(e)
        lb = lower_bounds(e / 2)
        table.append(dict(eps="2^-%d" % j,
                          logm_upper_over_lower=float(ub["lnm_hi"] / lb["m"]),
                          logBA_upper_over_lower=float(ub["lnBA_hi"] / lb["BA"]),
                          logAp_upper_over_lower=float(ub["lnAp"] / lb["Ap"]),
                          logAp_recycled_over_class_Abar_lower=float(ub["lnAp"] / lb["Abar"]),
                          logBp_upper_over_logBA_lower=float(ub["lnBp"] / lb["BA"])))
    return len(grid), table


# ---------------------------------------------------------------------------
# Part 7: constants.

def check_constants():
    assert LNK.flo > Fr(1, 21)
    assert 96 ** 3 < 960 ** 2
    assert C_ABAR > Fr(13, 10 ** 7)                   # 1.3e-6
    assert C_M > Fr(39, 10 ** 7)                      # 3.9e-6
    assert C_M == 3 * C_ABAR
    assert Fr(45, 8) * Fr(3, 8192) == Fr(135, 65536)
    assert Fr(135, 65536) / 21 == C_BA and C_BA > Fr(98, 10 ** 6)
    assert C_AP * LN2.flo > Fr(5, 10 ** 4)
    # chain of Step 5 for m_*: 6 * (9/16)(1/16) * (3/8) = 81/1024
    assert 6 * Fr(9, 16) * Fr(1, 16) * Fr(3, 8) == Fr(81, 1024)
    # P > 9 D0^2 x^2/(256 eps^2) = 3 x^2 /(8192 eps^3)
    assert Fr(9, 256) * Fr(1, 96) == Fr(3, 8192)
    # thresholds
    assert Fr(1, 9216) < Fr(9, 16384) < Fr(9, 64) < Fr(3, 20)
    assert Fr(1, 2 ** 14) < Fr(1, 9216)
    # recycled constants: 2305^2 = 5,313,025; 5313025 + 0.022 < 5.32e6
    assert 2305 ** 2 == 5313025 and 5313025 + Fr(22, 1000) < C_AREC
    # (3/2) Lambda <= 0.022 Lambda^3 needs Lambda^2 >= 1.5/0.022: Lambda >= log 4096
    assert (ln_int(4096) * ln_int(4096)).flo * Fr(22, 1000) >= Fr(3, 2)
    # log B' constant: 2305^2 (256 + 2 + (7/3) log 4096) + slack < 1.5e9
    c = 2305 ** 2 * (256 + 2 + Fr(7, 3) * ln_int(4096).fhi)
    assert c + 1 < C_BREC
    # (4/3) log 48 < (2/3) log 4096 ; log 36 + (1 + log 24)/3 < (2/3) log 4096
    assert (ln_int(48) * Fr(4, 3)).fhi < (ln_int(4096) * Fr(2, 3)).flo
    assert (ln_int(36) + (Iv.of(1) + ln_int(24)) * Fr(1, 3)).fhi < (ln_int(4096) * Fr(2, 3)).flo
    # main theorem bound vs proof value; copy counts 6x and 35/4 x
    assert C_LOGA_PROOF < C_LOGA
    assert 6 * C_LOGA_PROOF < Fr(154, 10) * 10 ** 9 and Fr(35, 4) * C_LOGA_PROOF < Fr(224, 10) * 10 ** 9
    # corollary (allowance eps, eps <= 1/2): 3e9 * 2^-9/2 < 1.4e8; times 6 and 35/4
    assert (3 * 10 ** 9) ** 2 < (Fr(14, 100) * 10 ** 9) ** 2 * 2 ** 9
    assert (6 * 3 * 10 ** 9) ** 2 < (Fr(84, 100) * 10 ** 9) ** 2 * 2 ** 9
    assert (Fr(35, 4) * 3 * 10 ** 9) ** 2 < (Fr(124, 100) * 10 ** 9) ** 2 * 2 ** 9
    return dict(C_m=float(C_M), C_Abar=float(C_ABAR), C_BA=float(C_BA),
                C_Ap=float(C_AP * LN2.flo))



# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    print("Part 1: identities; smallest endpoint coefficient:", check_identities())
    print("Part 2: type lemmas (exhaustive pairs, large pairs):", check_type_lemmas())
    print("Part 3: toy chains (S, r_*, m_*, B') verified as restrictions:", check_toy_chain())
    print("Part 4: random schemes:", check_random_schemes(300 if args.quick else 2000))
    cases = [(2, 20, 200, 2), (2, 40, 400, 1)] if args.quick else \
        [(2, 20, 200, 2), (2, 40, 400, 1), (2, 128, 300, 3), (3, 60, 500, 2)]
    for row in check_main_shape_exact(cases):
        print("Part 4: main-shape exact:", row)
    for row in check_block_schemes():
        print("Part 4: block schemes:", row)
    factors = []
    for e in ([Fr(1), Fr(1, 2)] if args.quick else [Fr(1), Fr(1, 2), Fr(1, 4), Fr(1, 9)]):
        row = check_main_instance(e)
        factors.append((row["eps"], row.pop("recycling_factor")))
        print("Part 5: main construction:", row)
    for eps, f in factors:
        print("Part 5: recycling factor at eps = %s: digits(A) = %d, digits(A') = %d, "
              "digits(A)/digits(A') in %s, log A/log A' in %s"
              % (eps, f["decimal_digits_A"], f["decimal_digits_A_recycled"],
                 f["digits_ratio"], f["log_ratio"]))
    ng, table = check_grid(args.quick)
    print("Part 6: grid points:", ng)
    for row in table:
        print("Part 6:", row)
    print("Part 7: constants:", check_constants())
    print("all checks passed in %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
