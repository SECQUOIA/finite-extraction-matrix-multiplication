"""Independent exact checks for the adversarial review of
docs/shifted-chains-check-recycling.md (key "recycling").

Run from the repository root:

    python -I experiments/shifted_chains_skeptic_recycling.py [--quick]

The script imports nothing from the repository and shares no code with
experiments/shifted_chains_check_recycling.py.  Every assertion is decided
with exact integers, Fractions, or outward-rounded Decimal intervals:
Decimal.ln and Decimal.exp are correctly rounded (half-even), so each value is
widened by one unit in the last place, and every other interval operation uses
the ROUND_FLOOR / ROUND_CEILING contexts.  Floats appear only in printed
summaries.

Parts
  A. Lemma S (supplies) as a literal restriction on actual tensors: a
     three-stage toy chain whose stages are exact restrictions built from
     Strassen's rank-7 decomposition, the classical rank-8 decomposition, a
     crop, and the subrank restriction C(2,2) >= <2> (so Y = 2 comes from the
     state tensor, not from the auxiliary).  Source evaluation by Lagrange
     interpolation at the nodes 0..s-1.  Recycling, source and non-maximal
     supplies; the image is compared term by term with m_* MM_{B'}.
  B. Random chain schemes of the class (blocks, random types, crops, swaps,
     terminal), exact integers, biased towards pooled exponent <= 3: every
     item of Lemma S, the identity m_* = (Bbar/t^{2W})^3, the copy-count
     inequality m_* t^{6W} >= Abar^3 s^{6W} when p <= 3, and t <= s.
  C. Constants and thresholds of Theorem C / Proposition T; the endpoint
     polynomial, the gap identity, and the type lemmas on small ranges.
  D. Corollary R on a grid of rational eps (D- and H-breakpoints, 1 down to
     2^-300): (F1), (F2) in the exact form needed, p' - p, log S, log B',
     Proposition M; the crossover at 2^-26 and the actual-schedule crossover.
  E. The main construction at eps = 1, 1/2, 1/4 (and 1/9 without --quick):
     maximal types by exchange-optimal search, interval logs, the recycled bank
     with exact floor accounting at every stage, p and p', digit counts.
     The same part checks the seeds ratio log Xi / log Xi' < 1.34.
  G. The small-source barrier (gate note) for every supply: per-level margins
     3 a_d + C(n,d,k,M_max; p0) over all gaining (n,d,k) with nk <= 64, the
     endpoint minimum, pair margins (relaxed and with the new two-level
     endpoint bound, checked exhaustively on small chains), and the
     extra-level gains allowed by funding; at p0 = 29/10, 119/40 and
     p_hi = 2976961/10^6.
  H. An arity-2 prefix of ceil(log2 D) stages: the recycled source
     S = 4 J 2^{2W} funds the main chain at eps = 1/2, 1/4 (and 1/9 without
     --quick), with p' < 9/4 + eps/2.

Runtime: about 25 s with --quick, about 100 s without.
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as Fr
from math import comb, factorial, isqrt

sys.set_int_max_str_digits(0)

PREC = 90
CF = Context(prec=PREC, rounding=ROUND_FLOOR)
CC = Context(prec=PREC, rounding=ROUND_CEILING)
CN = Context(prec=PREC, rounding=ROUND_HALF_EVEN)


# ---------------------------------------------------------------------------
# Outward-rounded Decimal intervals.

class DI:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = lo, hi

    @staticmethod
    def exact(x):
        """Interval enclosing a Fraction or int."""
        x = Fr(x)
        lo = CF.divide(Decimal(x.numerator), Decimal(x.denominator))
        hi = CC.divide(Decimal(x.numerator), Decimal(x.denominator))
        return DI(lo, hi)

    def __add__(self, o):
        if not isinstance(o, DI):
            o = DI.exact(o)
        return DI(CF.add(self.lo, o.lo), CC.add(self.hi, o.hi))

    __radd__ = __add__

    def __neg__(self):
        return DI(-self.hi, -self.lo)

    def __sub__(self, o):
        if not isinstance(o, DI):
            o = DI.exact(o)
        return DI(CF.subtract(self.lo, o.hi), CC.subtract(self.hi, o.lo))

    def __rsub__(self, o):
        return DI.exact(o) - self

    def __mul__(self, o):
        if not isinstance(o, DI):
            o = DI.exact(o)
        c = [CF.multiply(a, b) for a in (self.lo, self.hi) for b in (o.lo, o.hi)]
        d = [CC.multiply(a, b) for a in (self.lo, self.hi) for b in (o.lo, o.hi)]
        return DI(min(c), max(d))

    __rmul__ = __mul__

    def __truediv__(self, o):
        if not isinstance(o, DI):
            o = DI.exact(o)
        assert o.lo > 0 or o.hi < 0
        c = [CF.divide(a, b) for a in (self.lo, self.hi) for b in (o.lo, o.hi)]
        d = [CC.divide(a, b) for a in (self.lo, self.hi) for b in (o.lo, o.hi)]
        return DI(min(c), max(d))

    def flo(self):
        return Fr(self.lo)

    def fhi(self):
        return Fr(self.hi)

    def __float__(self):
        return float((self.lo + self.hi) / 2)


def _widen(v):
    return DI(CN.next_minus(v), CN.next_plus(v))


LN2 = _widen(CN.ln(Decimal(2)))
LN10 = _widen(CN.ln(Decimal(10)))
_LNC = {}


def ln_int(N):
    """Interval for log N, N >= 1 an integer (top 240 bits for huge N)."""
    assert N >= 1
    if N in _LNC:
        return _LNC[N]
    if N == 1:
        res = DI(Decimal(0), Decimal(0))
    elif N.bit_length() <= 240:
        res = _widen(CN.ln(Decimal(N)))
    else:
        e = N.bit_length() - 240
        m = N >> e
        lo = _widen(CN.ln(Decimal(m))).lo
        hi = _widen(CN.ln(Decimal(m + 1))).hi
        res = DI(lo, hi) + LN2 * e
    if N.bit_length() <= 4000:
        _LNC[N] = res
    return res


def ln_q(x):
    x = Fr(x)
    assert x > 0
    return ln_int(x.numerator) - ln_int(x.denominator)


def exp_hi(v):
    """Upper bound for exp(v), v a Decimal."""
    return CN.next_plus(CN.exp(v))


def lam_interval(d):
    """lambda_d = (sqrt(1+4dq) - 1)/(2q), q = d+2, enclosed by isqrt."""
    q = d + 2
    N = 1 + 4 * d * q
    sc = 1 << 300
    r = isqrt(N * sc * sc)
    lo, hi = Fr(r, sc), Fr(r + 1, sc)
    lam_lo, lam_hi = (lo - 1) / (2 * q), (hi - 1) / (2 * q)
    assert q * lam_lo ** 2 + lam_lo <= d <= q * lam_hi ** 2 + lam_hi
    return lam_lo, lam_hi


_AC = {}


def a_of(d):
    """a_d = -log lambda_d."""
    if d not in _AC:
        lo, hi = lam_interval(d)
        _AC[d] = DI((-ln_q(hi)).lo, (-ln_q(lo)).hi)
    return _AC[d]


_GC = {}


def g_of(d):
    """g_d = log((d+2)/d) = 2 atanh(z), z = 1/(d+1), with relative precision:
    2(z + z^3/3 + z^5/5) <= g_d <= that + 2 z^7/(7(1-z^2))."""
    if d in _GC:
        return _GC[d]
    if d <= 10 ** 6:
        res = ln_q(Fr(d + 2, d))
    else:
        z = Fr(1, d + 1)
        lo = 2 * (z + z ** 3 / 3 + z ** 5 / 5)
        hi = lo + 2 * z ** 7 / (7 * (1 - z * z))
        res = DI(CF.divide(Decimal(lo.numerator), Decimal(lo.denominator)),
                 CC.divide(Decimal(hi.numerator), Decimal(hi.denominator)))
    if len(_GC) < 10 ** 5:
        _GC[d] = res
    return res


# ---------------------------------------------------------------------------
# Part A: Lemma S as a literal restriction (three stages).

def image(T, legmap):
    """Apply leg maps to a tensor {(u,v,w): coeff}.  legmap(leg, var) returns
    a dict {var': coeff}; an empty dict means the variable is sent to 0."""
    out = {}
    memo = ({}, {}, {})
    for key, c0 in T.items():
        forms = []
        for leg in range(3):
            var = key[leg]
            f = memo[leg].get(var)
            if f is None:
                f = legmap(leg, var)
                memo[leg][var] = f
            if not f:
                break
            forms.append(f)
        else:
            fa, fb, fc = forms
            for a, ca in fa.items():
                for b, cb in fb.items():
                    cab = c0 * ca * cb
                    for c, cc in fc.items():
                        k = (a, b, c)
                        v = out.get(k, 0) + cab * cc
                        if v:
                            out[k] = v
                        else:
                            out.pop(k, None)
    return out


def mm_terms(N):
    """MM_N = sum x_{ab} y_{bc} z_{ca}, variables as index pairs."""
    return [((a, b), (b, c), (c, a)) for a in range(N) for b in range(N) for c in range(N)]


def strassen_forms():
    """Rank-7 decomposition of MM_2: products m_l = u_l(x) v_l(y); the entry
    (i,k) of XY is a signed sum of products, and it is the coefficient of
    z_{ki} in MM_2.  Returns three lists of dicts (leg forms)."""
    X = lambda i, j: (i, j)
    u = [{X(0, 0): 1, X(1, 1): 1}, {X(1, 0): 1, X(1, 1): 1}, {X(0, 0): 1},
         {X(1, 1): 1}, {X(0, 0): 1, X(0, 1): 1}, {X(1, 0): 1, X(0, 0): -1},
         {X(0, 1): 1, X(1, 1): -1}]
    v = [{X(0, 0): 1, X(1, 1): 1}, {X(0, 0): 1}, {X(0, 1): 1, X(1, 1): -1},
         {X(1, 0): 1, X(0, 0): -1}, {X(1, 1): 1}, {X(0, 0): 1, X(0, 1): 1},
         {X(1, 0): 1, X(1, 1): 1}]
    entries = {(0, 0): {0: 1, 3: 1, 4: -1, 6: 1}, (0, 1): {2: 1, 4: 1},
               (1, 0): {1: 1, 3: 1}, (1, 1): {0: 1, 1: -1, 2: 1, 5: 1}}
    w = [dict() for _ in range(7)]
    for (i, k), lst in entries.items():
        for l, sg in lst.items():
            w[l][(k, i)] = sg
    return [u, v, w]


def classical_forms():
    """Rank-8 decomposition of MM_2: one product per term x_ab y_bc z_ca."""
    terms = mm_terms(2)
    return [[{t[leg]: 1} for t in terms] for leg in range(3)]


def check_decomposition(forms, N=2):
    r = len(forms[0])
    T = {((l,), (l,), (l,)): Fr(1) for l in range(r)}
    res = image(T, lambda leg, var: dict(forms[leg][var[0]]))
    return res == {t: Fr(1) for t in mm_terms(N)}


def lagrange_coeffs(nodes):
    """L[l][g] = coefficient of xi^g in prod_{j != l}(xi - x_j)/(x_l - x_j)."""
    out = []
    for l, xl in enumerate(nodes):
        poly = [Fr(1)]
        den = Fr(1)
        for j, xj in enumerate(nodes):
            if j == l:
                continue
            new = [Fr(0)] * (len(poly) + 1)
            for i, c in enumerate(poly):
                new[i + 1] += c
                new[i] -= xj * c
            poly = new
            den *= (xl - xj)
        out.append([c / den for c in poly])
    return out


def conv(r, b):
    return [((al,), (be,), (al + be,)) for al in range(r) for be in range(b)]


class ToyStage:
    """X (T (x) MM_U) >= Y (T' (x) MM_V) with V = 2U, built from a rank-X/Y
    decomposition of MM_2 (forms) and a state map (sv -> {(y, sv'): coeff})."""

    def __init__(self, U, forms, Y, statemap):
        self.U, self.forms, self.Y, self.statemap = U, forms, Y, statemap
        self.X = len(forms[0])          # decomposition index; Y comes from the state map
        self.V = 2 * U


def run_toy(stages, s_nodes, T0, S, fs, bad_merge=False):
    """Apply the induction of Lemma S literally to r_* MM_S and compare the
    image with m_* MM_{B'}.  stages: list of ToyStage; fs: list of f_i."""
    J = len(stages)
    s = len(s_nodes)
    Xs = [st.X for st in stages]
    Ys = [st.Y for st in stages]
    r_star = s
    for x in Xs:
        r_star *= x
    m_star = 1
    for y in Ys:
        m_star *= y
    # bank sizes
    betas = [S]
    for st, f in zip(stages, fs):
        assert f >= 1 and st.U * f <= betas[-1], "not a supply"
        betas.append(f * st.V)
    # r_* MM_S: copies indexed by (node, x_1, ..., x_J)
    T = {}
    import itertools
    for node in range(s):
        for xs in itertools.product(*[range(x) for x in Xs]):
            tag = (node,) + xs
            for (a, b, c) in mm_terms(S):
                T[((tag, (), a), (tag, (), b), (tag, (), c))] = Fr(1)
    # source evaluation: s MM_1 >= T0 (Lagrange), identity on MM_S
    L = lagrange_coeffs(s_nodes)
    T0_dims = (max(t[0][0] for t in T0) + 1, max(t[1][0] for t in T0) + 1,
               max(t[2][0] for t in T0) + 1)
    assert T0_dims[2] == s                     # rank r+b-1 = number of nodes

    def src(leg, var):
        tag, _, mm = var
        l, rest = tag[0], tag[1:]
        xi = s_nodes[l]
        out = {}
        if leg == 0:
            for al in range(T0_dims[0]):
                out[(rest, (al,), mm)] = Fr(xi) ** al
        elif leg == 1:
            for be in range(T0_dims[1]):
                out[(rest, (be,), mm)] = Fr(xi) ** be
        else:
            for ga in range(T0_dims[2]):
                if L[l][ga]:
                    out[(rest, (ga,), mm)] = L[l][ga]
        return out

    T = image(T, src)
    expect = {}
    for xs in itertools.product(*[range(x) for x in Xs]):
        for (sx, sy, sz) in T0:
            for (a, b, c) in mm_terms(S):
                expect[((xs, sx, a), (xs, sy, b), (xs, sz, c))] = Fr(1)
    assert T == expect, "source evaluation"
    # stages
    for i, (st, f) in enumerate(zip(stages, fs)):
        U, Y = st.U, st.Y

        def stage_map(leg, var, st=st, f=f, i=i, U=U):
            copies, sv, (a, b) = var
            Uf = U * f
            if a >= Uf or b >= Uf:                 # principal block
                return {}
            aU, af = divmod(a, f)                  # MM_{Uf} = MM_U (x) MM_f
            bU, bf = divmod(b, f)
            x = copies[i]
            sm = st.statemap(leg, sv)
            if not sm:
                return {}
            out = {}
            for (al, be), cf in st.forms[leg][x].items():
                na = (al * U + aU) * f + af        # MM_2 (x) MM_U = MM_{2U}; (x) MM_f
                nb = (be * U + bU) * f + bf
                if bad_merge and leg == 1:         # negative control: inconsistent merge
                    nb = (bU * 2 + be) * f + bf
                for (y, sv2), cs in sm.items():
                    nc = copies[:i] + (y,) + copies[i + 1:]
                    k = (nc, sv2, (na, nb))
                    out[k] = out.get(k, 0) + Fr(cf) * cs
            return {k: v for k, v in out.items() if v}

        T = image(T, stage_map)
    Bp = betas[-1]                               # terminal t = 1, state C(1,1) = MM_1
    target = {}
    for ys in itertools.product(*[range(y) for y in Ys]):
        for (a, b, c) in mm_terms(Bp):
            target[((ys, (0,), a), (ys, (0,), b), (ys, (0,), c))] = Fr(1)
    return r_star, m_star, Bp, T == target


def crop_map(keep):
    """C(r,b) >= C(r',b'): keep[leg] = number of kept indices; one output copy."""
    def m(leg, sv):
        return {(0, sv): Fr(1)} if sv[0] < keep[leg] else {}
    return m


def subrank_c22(leg, sv):
    """C(2,2) >= <2> = 2 C(1,1): x_a -> copy a, y_b -> copy b, z_0 -> copy 0,
    z_2 -> copy 1, z_1 -> 0."""
    i = sv[0]
    if leg < 2:
        return {(i, (0,)): Fr(1)}
    if i == 1:
        return {}
    return {(i // 2, (0,)): Fr(1)}


def identity_state(leg, sv):
    return {(0, sv): Fr(1)}


def part_A(quick):
    ST, CL = strassen_forms(), classical_forms()
    assert check_decomposition(ST), "Strassen"
    assert check_decomposition(CL), "classical"
    # subrank map: C(2,2) >= 2 C(1,1)
    img = image({t: Fr(1) for t in conv(2, 2)}, subrank_c22)
    assert img == {((0, (0,)), (0, (0,)), (0, (0,))): 1, ((1, (0,)), (1, (0,)), (1, (0,))): 1}
    st1 = ToyStage(2, ST, 1, crop_map((2, 2, 3)))     # 7 (C(2,3) MM_2) >= C(2,2) MM_4
    st2 = ToyStage(3, ST, 2, subrank_c22)              # 7 (C(2,2) MM_3) >= 2 C(1,1) MM_6
    st3 = ToyStage(2, CL, 1, identity_state)           # 8 (C(1,1) MM_2) >= C(1,1) MM_4
    nodes = [0, 1, 2, 3]
    T0 = conv(2, 3)
    results = []
    # Three-stage chain: Abar = 12, Bbar = 96, r_* = 4*7*7*8, m_* = 2.
    runs = [(2, [1, 1, 3], "recycling S=2 (floors 4/3 -> 1)"),
            (4, [1, 1, 2], "non-maximal S=4")]
    if not quick:
        runs.append((5, [2, 2, 6], "recycling S=5 (floors 5/2, 8/3)"))
    for S, fs, label in runs:
        r, m, Bp, ok = run_toy([st1, st2, st3], nodes, T0, S, fs)
        assert ok, label
        assert (r, m) == (1568, 2)
        assert Bp * 12 <= 96 * S                        # B'/S <= Bbar/Abar
        results.append((label, S, Bp))
    # Two-stage chain with the source supply: S = Abar = 6, f1 = U2, f2 = V1.
    r, m, Bp, ok = run_toy([st1, st2], nodes, T0, 6, [3, 4])
    assert ok and Bp == 24 and (r, m) == (196, 2), "source supply"
    results.append(("source supply S=6", 6, Bp))
    # Negative control: an inconsistent index merge on one leg must be detected.
    r, m, Bp, ok = run_toy([st1, st2], nodes, T0, 3, [1, 1], bad_merge=True)
    assert not ok, "negative control not detected"
    # Recycling for the same two stages, S = 3: f1 = 1, beta1 = 4, f2 = 1.
    r, m, Bp, ok = run_toy([st1, st2], nodes, T0, 3, [1, 1])
    assert ok and Bp == 6
    results.append(("recycling S=3", 3, Bp))
    return results


# ---------------------------------------------------------------------------
# Part B: random chain schemes, exact integers.

def type_count(n, d, t):
    l, o, m = t
    assert l + o + m == n
    return factorial(n) // (factorial(l) * factorial(o) * factorial(m)) * (d - 1) ** l * 2 ** o


def max_type(n, d):
    """A type maximizing the sector count, by single-transfer optimality
    (log of the count is separably concave in (l,o,m) on l+o+m = n)."""
    w = (d - 1, 2, 1)
    q = d + 2
    a = [((n + 1) * wi) // q for wi in w]
    while sum(a) < n:
        a[0] += 1
    while sum(a) > n:
        i = max(range(3), key=lambda j: a[j])
        a[i] -= 1
    changed = True
    while changed:
        changed = False
        for i in range(3):
            for j in range(3):
                # move one unit j -> i: factor w_i a_j / (w_j (a_i + 1))
                if i != j and a[j] > 0 and w[i] * a[j] > w[j] * (a[i] + 1):
                    a[i] += 1
                    a[j] -= 1
                    changed = True
    for i in range(3):
        for j in range(3):
            if i != j and a[j] > 0:
                assert w[i] * a[j] <= w[j] * (a[i] + 1)
    return tuple(a)


_MMAX = {}


def M_max(n, d):
    if (n, d) not in _MMAX:
        _MMAX[(n, d)] = type_count(n, d, max_type(n, d))
    return _MMAX[(n, d)]


def legal(r, b, d, c):
    return r >= 1 and c >= 1 and (d + 2) * c <= d * b - r + 1


class Chain:
    """Chain scheme of the class with exact counts."""

    def __init__(self, pairs, ars, blocks, W, t):
        self.pairs, self.ars, self.blocks, self.W, self.t = pairs, ars, blocks, W, t
        self.J = len(ars)
        r0, b0 = pairs[0]
        self.s = r0 + b0 - 1
        self.U, self.V, self.X, self.Y = [], [], [], []
        for d, bl in zip(ars, blocks):
            assert sum(n * k for n, k, _ in bl) == W
            V = X = Y = 1
            for n, k, tp in bl:
                M = type_count(n, d, tp)
                E = 1 + 6 * k * (M - 1)
                V *= M ** (2 * k)
                X *= E * (2 * M - 1) ** (6 * k)
                Y *= M ** (6 * k)
            self.U.append(d ** (2 * W))
            self.V.append(V)
            self.X.append(X)
            self.Y.append(Y)
        self.Abar = 1
        for u in self.U:
            self.Abar *= u
        prodV = 1
        for v in self.V:
            prodV *= v
        self.prodV = prodV
        self.Bbar = t ** (2 * W) * prodV
        self.rstar = self.s ** (6 * W)
        for x in self.X:
            self.rstar *= x
        self.mstar = 1
        for y in self.Y:
            self.mstar *= y

    def bank(self, S, fs):
        betas = [S]
        for U, V, f in zip(self.U, self.V, fs):
            assert f >= 1 and U * f <= betas[-1]
            betas.append(f * V)
        return betas

    def source_supply(self):
        fs = []
        for i in range(self.J):
            f = 1
            for l in range(i + 1, self.J):
                f *= self.U[l]
            for l in range(i):
                f *= self.V[l]
            fs.append(f)
        return self.Abar, fs

    def recycling(self, S):
        betas, fs = [S], []
        for U, V in zip(self.U, self.V):
            f = betas[-1] // U
            if f < 1:
                return None, None
            fs.append(f)
            betas.append(f * V)
        return fs, betas


def random_chain(rng, profile):
    """Random scheme; profile 'gain' biases towards pooled exponent <= 3."""
    for _ in range(200):
        if profile == "gain":
            W = rng.choice([24, 36, 48, 60, 72, 96])
            r, b = rng.randint(2, 12), rng.randint(2, 40)
            dmax = 5
        else:
            W = rng.choice([1, 2, 3, 4, 6, 8, 12])
            r, b = rng.randint(1, 30), rng.randint(1, 30)
            dmax = 9
        pairs = [(r, b)]
        ars, blocks = [], []
        depth = rng.randint(1, 4)
        for _ in range(depth):
            r, b = pairs[-1]
            opts = []
            for (rr, bb) in ((r, b), (b, r)):
                for d in range(2, dmax + 1):
                    cmax = (d * bb - rr + 1) // (d + 2)
                    if cmax >= 1:
                        opts.append((rr, bb, d, cmax))
            if not opts:
                break
            rr, bb, d, cmax = rng.choice(opts)
            c = cmax if rng.random() < 0.6 else rng.randint(1, cmax)
            assert legal(rr, bb, d, c) and c < bb
            nr, nb = c, rr
            if rng.random() < 0.25:
                nr = rng.randint(1, nr)
            if rng.random() < 0.25:
                nb = rng.randint(1, nb)
            if rng.random() < 0.5:
                nr, nb = nb, nr
            # blocks
            bl, rem = [], W
            while rem > 0:
                divs = [m for m in range(1, rem + 1) if rem % m == 0]
                if profile == "gain":
                    n = rng.choice([m for m in divs if m >= min(8, rem)] or divs)
                else:
                    n = rng.choice(divs)
                kmax = rem // n
                k = kmax if rng.random() < 0.7 else rng.randint(1, kmax)
                if rng.random() < 0.75:
                    tp = max_type(n, d)
                else:
                    l = rng.randint(0, n)
                    o = rng.randint(0, n - l)
                    tp = (l, o, n - l - o)
                bl.append((n, k, tp))
                rem -= n * k
            ars.append(d)
            blocks.append(bl)
            pairs.append((nr, nb))
        if not ars:
            continue
        mx = max(pairs[-1])
        t = mx if rng.random() < 0.6 else rng.randint(1, mx)
        return Chain(pairs, ars, blocks, W, t)
    return None


def random_chain_backward(rng):
    """Short chains built backwards from the terminal pair (1, t) by smallest
    parents (child of length c), small arities, one or two blocks per stage
    with large widths: the regime of the gate witness, where p is near 3."""
    depth = rng.randint(1, 3)
    t = rng.randint(5, 60)
    child = (1, t)                       # pair after the last stage
    pairs_rev, ars_rev = [child], []
    for _ in range(depth):
        d = rng.choice([2, 2, 2, 2, 3, 4])
        c, r = child if rng.random() < 0.8 else (child[1], child[0])
        b = -((-((d + 2) * c + r - 1)) // d)
        if b <= c:
            b = c + 1
        assert legal(r, b, d, c)
        parent = (r, b) if rng.random() < 0.5 else (b, r)
        pairs_rev.append(parent)
        ars_rev.append(d)
        child = parent
    pairs = pairs_rev[::-1]
    ars = ars_rev[::-1]
    # re-derive the forward steps and check legality with the recorded orientation
    for i, d in enumerate(ars):
        r, b = pairs[i]
        nxt = pairs[i + 1]
        ok = False
        for (rr, bb) in ((r, b), (b, r)):
            for (c1, r1) in (nxt, nxt[::-1]):
                if r1 <= rr and legal(rr, bb, d, c1):
                    ok = True
        assert ok
    W = rng.choice([64, 72, 96, 120, 144])
    blocks = []
    for d in ars:
        bl, rem = [], W
        while rem > 0:
            divs = ([m for m in range(16, min(rem, 60) + 1) if rem % m == 0]
                    if rng.random() < 0.85 else [m for m in range(8, rem + 1) if rem % m == 0])
            divs = divs or [rem]
            n = rng.choice(divs)
            k = rem // n if rng.random() < 0.8 else rng.randint(1, rem // n)
            bl.append((n, k, max_type(n, d)))
            rem -= n * k
        blocks.append(bl)
    tt = max(pairs[-1]) if rng.random() < 0.8 else rng.randint(1, max(pairs[-1]))
    return Chain(pairs, ars, blocks, W, tt)


def supply_checks(ch, rng):
    A, B, W, t, s = ch.Abar, ch.Bbar, ch.W, ch.t, ch.s
    # geometry: the larger entry never increases; t <= s
    mxs = [max(p) for p in ch.pairs]
    assert all(mxs[i + 1] <= mxs[i] for i in range(len(mxs) - 1))
    assert t <= mxs[-1] <= s and s >= 2
    # m_* = (Bbar / t^{2W})^3 and r_* > m_* (indeed r_*/m_* >= s^{6W})
    assert ch.mstar == ch.prodV ** 3 and B == t ** (2 * W) * ch.prodV
    assert ch.rstar >= ch.mstar * s ** (6 * W) > ch.mstar
    # source supply: U_i f_i = beta_{i-1}, (S, B') = (Abar, Bbar)
    S, fs = ch.source_supply()
    betas = ch.bank(S, fs)
    assert all(ch.U[i] * fs[i] == betas[i] for i in range(ch.J))
    assert S == A and t ** (2 * W) * betas[-1] == B
    # random (non-maximal) supplies: B'/S <= Bbar/Abar
    for _ in range(3):
        S = rng.randint(ch.U[0], 4 * ch.U[0] + 7)
        fs, beta = [], S
        ok = True
        for U, V in zip(ch.U, ch.V):
            if beta < U:
                ok = False
                break
            f = rng.randint(1, beta // U)
            fs.append(f)
            beta = f * V
        if ok:
            Bp = t ** (2 * W) * ch.bank(S, fs)[-1]
            assert Bp * A <= B * S
    # recycling supply: exact floor inequality
    for S in (ch.U[0], ch.U[0] + 1, 3 * ch.U[0] - 1):
        fs, betas = ch.recycling(S)
        if fs is None:
            continue
        Bp = t ** (2 * W) * betas[-1]
        assert Bp * A <= B * S
        num, den = 1, 1
        for i in range(ch.J):
            num *= betas[i] - ch.U[i]
            den *= betas[i]
        assert Bp * A * den >= B * S * num
    # funding lemma: S >= 4 J Utilde with Utilde = max_i U_i prod_{l<i} U_l/V_l
    Ut, run = Fr(0), Fr(1)
    for i in range(ch.J):
        Ut = max(Ut, ch.U[i] * run)
        run *= Fr(ch.U[i], ch.V[i])
    S = -((-4 * ch.J * Ut.numerator) // Ut.denominator)
    fs, betas = ch.recycling(S)
    assert fs is not None
    assert all(betas[i] >= 2 * ch.J * ch.U[i] for i in range(ch.J))
    Bp = t ** (2 * W) * betas[-1]
    assert 2 * Bp * A >= B * S and Bp * A <= B * S
    # copy-count inequality (Theorem C(2)) when Bbar > Abar and p <= 3:
    # p <= 3  <=>  r_* Abar^3 <= m_* Bbar^3
    p_le_3 = B > A and ch.rstar * A ** 3 <= ch.mstar * B ** 3
    if p_le_3:
        assert ch.mstar * t ** (6 * W) >= A ** 3 * s ** (6 * W)
        assert ch.mstar >= A ** 3
    return p_le_3, B > A


def part_B(quick):
    rng = random.Random(77031)
    stats = {"schemes": 0, "relative": 0, "p_le_3": 0, "min_ratio": None}
    n_each = 150 if quick else 700
    for profile in ("backward", "gain", "plain"):
        for _ in range(3 * n_each if profile == "backward" else n_each):
            ch = random_chain_backward(rng) if profile == "backward" else random_chain(rng, profile)
            if ch is None:
                continue
            p3, rel = supply_checks(ch, rng)
            stats["schemes"] += 1
            stats["relative"] += rel
            if p3:
                stats["p_le_3"] += 1
                # normalized slack of m_* >= Abar^3: (log m_* - 3 log Abar)/(6W)
                v = float((ln_int(ch.mstar) - ln_int(ch.Abar) * 3).lo) / (6 * ch.W)
                stats["min_ratio"] = v if stats["min_ratio"] is None else min(stats["min_ratio"], v)
    assert stats["p_le_3"] >= (30 if quick else 150), stats
    return stats


# ---------------------------------------------------------------------------
# Part C: constants, thresholds and lemma re-checks.

def poly_mul(p, q):
    out = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def poly_pow(p, e):
    out = [Fr(1)]
    for _ in range(e):
        out = poly_mul(out, p)
    return out


def part_C():
    K = Fr(21, 20)
    # log K > 1/21 (from log(1+u) > u/(1+u)), certified as well
    assert ln_q(K).flo() > Fr(1, 21)
    # constants
    assert 96 ** 3 < 960 ** 2
    c_abar = Fr(27, 21 * 1024 * 960)
    c_m = 3 * c_abar
    c_ba = Fr(135, 65536 * 21)
    assert c_abar > Fr(13, 10 ** 7) and c_m > Fr(39, 10 ** 7)
    assert c_m == Fr(81, 21 * 1024 * 960)
    assert c_ba == Fr(45, 458752) and c_ba > Fr(98, 10 ** 6)
    assert (LN2 * Fr(3, 4096)).flo() > Fr(5, 10 ** 4)
    # Step 3 / Step 5 algebra: P > (9 d x/(16 eps)) (d x/(16 eps)) with d^2 = 1/(96 eps)
    assert Fr(9, 16) * Fr(1, 16) * Fr(1, 96) == Fr(3, 8192)
    assert 2 * Fr(9, 16) * Fr(1, 16) * Fr(3, 8) == Fr(27, 1024)
    assert Fr(45, 8) * Fr(3, 8192) == Fr(135, 65536)
    assert (LN2 * Fr(9, 8)).flo() > Fr(9, 16)            # 9 log 2/8 > 9/16
    # thresholds, exactly: log d_eps > x/4 <=> eps < 1/9216;
    # log(3/(128 eps)) >= x/2 <=> eps <= 9/16384; n > (9/16) d/eps >= 4d >= 2q <=> eps <= 9/64
    for eps in (Fr(1, 9216), Fr(1, 9217), Fr(9, 16384), Fr(9, 16385), Fr(1, 2 ** 14)):
        # d_eps^4 > 1/eps  <=>  1/(9216 eps^2) > 1/eps
        assert (Fr(1, 9216) / eps ** 2 > 1 / eps) == (eps < Fr(1, 9216))
        assert ((Fr(3, 128) / eps) ** 2 >= 1 / eps) == (eps <= Fr(9, 16384))
    assert Fr(1, 2 ** 14) < Fr(1, 9216) < Fr(9, 16384) < Fr(9, 64) < Fr(3, 20)
    assert Fr(9, 4) + Fr(3, 20) == Fr(12, 5)
    # endpoint polynomial (L2): (4/9)^5 (u^2+4u+8/3)^5 - K^10 (u+1)^8 > 0 coefficientwise
    lhs = [c * Fr(4, 9) ** 5 for c in poly_pow([Fr(8, 3), Fr(4), Fr(1)], 5)]
    rhs = [c * K ** 10 for c in poly_pow([Fr(1), Fr(1)], 8)]
    diff = [lhs[i] - (rhs[i] if i < len(rhs) else 0) for i in range(len(lhs))]
    assert len(diff) == 11 and all(c > 0 for c in diff)
    # gap identity (1 - z^4) f(z^3) = z^3 (1-z)^2 (1-z^2), f(y) = q y^2 + y - d,
    # q = 2/(1-z^4), d = q - 2; checked at 30 rational points (degree <= 9)
    for i in range(1, 31):
        z = Fr(i, 31)
        q = 2 / (1 - z ** 4)
        d = q - 2
        f = q * z ** 6 + z ** 3 - d
        assert (1 - z ** 4) * f == z ** 3 * (1 - z) ** 2 * (1 - z ** 2)
    # L1 identity on a grid exceeding the degrees in (q, lam, R, B)
    for q in range(3, 10):
        d = q - 2
        for lam in (Fr(j, 7) for j in range(1, 7)):
            beta = lam + Fr(1, q)
            f = q * lam ** 2 + lam - d
            for R in range(1, 5):
                for B in range(1, 5):
                    Qf = lambda y, z: y * y + 4 * y * z + z * z
                    T1 = Fr(d * B - R, q)
                    left = lam ** 2 * Qf(R, B) - Qf(T1, R) - (1 - beta ** 2) * (R - lam * B) ** 2
                    right = f / q * (2 * R * R + (4 - 2 * beta) * R * B + (lam * beta + Fr(d, q)) * B * B)
                    assert left == right
    # gap lemma: (omega_d - 9/4) g_d >= g_d/(24 q^2), i.e. a_d - (3/4) g_d >= g_d/(72 q^2)
    for d in list(range(2, 41)) + [100, 1000, 10 ** 6]:
        q = d + 2
        a, g = a_of(d), g_of(d)
        assert (a - g * Fr(3, 4)).flo() >= (g * Fr(1, 72 * q * q)).fhi()
        assert g.fhi() <= Fr(2, d)
    # type lemmas (a)-(c), exhaustive
    for n in range(1, 25):
        for d in range(2, 31):
            q = d + 2
            best = 0
            for l in range(n + 1):
                for o in range(n - l + 1):
                    M = type_count(n, d, (l, o, n - l - o))
                    best = max(best, M)
                    assert M <= q ** n
                    if M > d ** n:
                        assert n >= 3 and d <= 2 * n
                    if n >= 3 and d <= 2 * n:
                        assert 2 * M <= q ** n
            assert best == M_max(n, d)
    return {"min_endpoint_coeff": float(min(diff)), "C_m": float(c_m), "C_Abar": float(c_abar),
            "C_BA": float(c_ba)}


# ---------------------------------------------------------------------------
# Part D: Corollary R on a grid of eps.

def sched(eps):
    """The main theorem's schedule, by integer arithmetic."""
    eps = Fr(eps)
    assert 0 < eps <= 1
    D = 2
    while D * D * eps < 4:          # least D with D^2 eps >= 4 (galloping)
        D *= 2
    lo, hi = D // 2, D
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid * mid * eps >= 4:
            hi = mid
        else:
            lo = mid
    D = max(hi, 2)
    assert D * D * eps >= 4 and (D == 2 or (D - 1) ** 2 * eps < 4)
    R = 8 * D
    L = -((-64 * D * eps.denominator) // eps.numerator)
    x0 = Fr(128 * D) / eps
    H = (-((-x0.numerator) // x0.denominator)).bit_length()
    n = -((-256 * D * H * eps.denominator) // eps.numerator)
    J = 16 * D - 2 + L
    return dict(eps=eps, D=D, R=R, L=L, x0=x0, H=H, n=n, k=n, J=J)


def Lam(eps):
    return ln_q(Fr(4096) / Fr(eps))


C_SREC = Fr(532, 100) * 10 ** 6      # log S  < 5.32e6 eps^-3 Lambda^3
C_BREC = Fr(15, 10) * 10 ** 9        # log B' < 1.5e9 eps^-4 Lambda^2
C_LOGA = Fr(2550252000)              # main theorem, Step 5


def check_corR(eps):
    sp = sched(eps)
    eps, D, R, L, n, k, J = sp["eps"], sp["D"], sp["R"], sp["L"], sp["n"], sp["k"], sp["J"]
    W = n * k
    Lm = Lam(eps)
    # parameter facts
    assert n * eps >= 4608                               # n >= 4608/eps
    assert Fr(J) ** 2 * eps ** 3 <= 240 ** 2             # J <= 240 eps^-3/2
    assert Fr(D) ** 2 * eps <= 9                         # D <= 3 eps^-1/2
    assert Fr(n) ** 2 * eps ** 3 <= (2305 * Lm).flo() ** 2
    a = ln_int(n + 1) * Fr(2, n)                         # a = 2 log(n+1)/n
    assert a.fhi() <= 3 * eps / (128 * D)
    # (F1): the worst arity 24D-3 still gains
    dmax = 24 * D - 3
    gmax = g_of(dmax)
    assert (gmax * n - ln_int(n + 1) * 2).flo() > 0
    assert gmax.flo() > Fr(1, 12 * D)
    # (F2) in the form needed: L (n g_D - 2 log(n+1)) >= n log((24D-3)/D)
    gD = g_of(D)
    assert (L * (gD * n - ln_int(n + 1) * 2)).flo() >= (ln_q(Fr(dmax, D)) * n).fhi()
    assert (gD * L).flo() >= 64 / eps and (a * L).fhi() < 2
    # p' - p <= (11/4) log 2 / (log(B/A) - log 2), log(B/A) >= 2 n k (L g_D - J a)
    lnBA_lo = (gD * L - a * J) * (2 * W)
    assert lnBA_lo.flo() >= 124 * W
    inc = (LN2 * Fr(11, 4)) / (lnBA_lo - LN2)
    assert inc.fhi() < eps / 10 ** 9
    # log S = log(4J) + 2nk log D
    lnS = ln_int(4 * J) + ln_int(D) * (2 * W)
    L3 = Lm * Lm * Lm
    assert lnS.fhi() < C_SREC * L3.flo() / eps ** 3
    # log B' <= log S + 2nk G_up, G_up = L g_D + log(3R/2) + (1 + log(R-1))/3
    G_up = gD * L + ln_q(Fr(3 * R, 2)) + (1 + ln_int(R - 1)) * Fr(1, 3)
    lnBp_up = lnS + G_up * (2 * W)
    assert lnBp_up.fhi() < C_BREC * (Lm * Lm).flo() / eps ** 4
    # main theorem Step 5 (source supply): log A <= 2 n k J log(24 D)
    lnA_up = ln_int(24 * D) * (2 * W * J)
    s15 = Fr(isqrt((10 ** 60 * eps.denominator) // eps.numerator) + 1, 10 ** 30)   # >= eps^-1/2
    assert lnA_up.fhi() < C_LOGA * L3.flo() * s15 / eps ** 4
    return dict(lnS=lnS, lnBp_up=lnBp_up, lnA_up=lnA_up, W=W, D=D, J=J)


def eps_grid(quick):
    g = [Fr(1), Fr(1, 2), Fr(1, 3), Fr(1, 4), Fr(4, 9), Fr(4, 9) + Fr(1, 10 ** 12),
         Fr(4, 9) - Fr(1, 10 ** 12), Fr(999, 1000), Fr(1, 9), Fr(1, 9216), Fr(1, 10 ** 4)]
    for D in range(2, 60 if quick else 300):
        e = Fr(4, D * D)                                   # D-breakpoints
        g += [e, e * (1 + Fr(1, 10 ** 9))] if e * (1 + Fr(1, 10 ** 9)) <= 1 else [e]
    for D in (2, 3, 5, 17, 64):
        for m in range(9, 30 if quick else 60):
            # H-breakpoints: 128 D / eps = 2^m +- 1/2
            for off in (Fr(-1, 2), Fr(1, 2)):
                e = Fr(128 * D) / (2 ** m + off)
                if 0 < e <= 1 and sched(e)["D"] == D:
                    g.append(e)
    g += [Fr(1, 2 ** j) for j in range(1, 301, 1 if not quick else 7)]
    g += [Fr(1, 3 ** j) for j in range(1, 190, 11)]
    rng = random.Random(4)
    for _ in range(20 if quick else 120):
        g.append(Fr(rng.randint(1, 10 ** 6), rng.randint(10 ** 6, 10 ** 30)))
    return sorted(set(e for e in g if 0 < e <= 1), reverse=True)


def part_D(quick):
    grid = eps_grid(quick)
    for e in grid:
        check_corR(e)
    # constants of the allowance-eps forms
    assert C_SREC / 8 < Fr(67, 100) * 10 ** 6 and C_BREC / 16 < Fr(94, 10) * 10 ** 7
    assert 6 * C_LOGA < Fr(154, 100) * 10 ** 10 and Fr(35, 4) * C_LOGA < Fr(224, 100) * 10 ** 10
    # (3e9 * 2^-9/2) * 6 < 8.4e8 and * 35/4 < 1.24e9: square both sides
    assert (Fr(3 * 10 ** 9 * 6) / 16) ** 2 < 2 * Fr(84 * 10 ** 7) ** 2
    assert (Fr(3 * 10 ** 9) * Fr(35, 4) / 16) ** 2 < 2 * Fr(124 * 10 ** 7) ** 2
    # crossover: at eps = 2^-26 the proved recycled bound lies below the
    # source-supply bound 1.3e-6 (eps/2)^-9/2 log^3(2/eps) (allowance eps/2)
    out = {}
    for j in (24, 25, 26, 27, 40):
        e = Fr(1, 2 ** j)
        Lmv = Lam(e)
        up_log = ln_q(C_SREC) + LN2 * (3 * j) + DI(CF.ln(Lmv.lo), CC.ln(Lmv.hi)) * 3
        xx = ln_q(Fr(2) / e)
        lo_log = ln_q(Fr(13, 10 ** 7)) + LN2 * Fr(9 * (j + 1), 2) + DI(CF.ln(xx.lo), CC.ln(xx.hi)) * 3
        out[j] = float(up_log - lo_log)
        if j >= 26:
            assert up_log.fhi() < lo_log.flo(), j
        if j == 25:
            assert up_log.flo() > lo_log.fhi()          # 2^-26 is the first power of 2
    # crossover with the actual schedule: log S (exact for the schedule) against
    # the exact source-supply coefficient c = 27 log K/(1024 96^{3/2}) at eps/2
    sq96_hi = Fr(isqrt(96 * 10 ** 40) + 1, 10 ** 20)
    sq96_lo = Fr(isqrt(96 * 10 ** 40), 10 ** 20)
    cK = ln_q(Fr(21, 20)) * Fr(27, 1024)
    act = {}
    for j in (16, 20, 22, 23, 24, 28):
        e = Fr(1, 2 ** j)
        lnS = check_corR(e)["lnS"]
        xx = ln_q(Fr(2) / e)
        # lower bound value: c (eps/2)^-9/2 x^3, with (eps/2)^-9/2 = 2^{9(j+1)/2}
        lb_lo = DI(CF.ln(cK.lo), CC.ln(cK.hi)) - DI(CF.ln(Decimal(sq96_hi.numerator) / Decimal(sq96_hi.denominator)),
                                                     CC.ln(Decimal(sq96_hi.numerator) / Decimal(sq96_hi.denominator))) * 3
        lb_log = lb_lo + LN2 * Fr(9 * (j + 1), 2) + DI(CF.ln(xx.lo), CC.ln(xx.hi)) * 3
        lnS_log = DI(CF.ln(lnS.lo), CC.ln(lnS.hi))
        act[j] = float(lnS_log - lb_log)
    # ratio > 1 at 2^-20, < 1 at 2^-24 (log of ratio)
    assert act[20] > 0 and act[24] < 0
    return {"grid_points": len(grid), "log_ratio_proved_bounds": out, "log_ratio_actual_schedule": act}


# ---------------------------------------------------------------------------
# Part E: the main construction, actual counts.

class LogFact:
    """Certified prefix sums ln(j!) for j <= N."""

    def __init__(self, N):
        self.lo = [Decimal(0), Decimal(0)]
        self.hi = [Decimal(0), Decimal(0)]
        clo, chi = Decimal(0), Decimal(0)
        for j in range(2, N + 1):
            v = CN.ln(Decimal(j))
            clo = CF.add(clo, CN.next_minus(v))
            chi = CC.add(chi, CN.next_plus(v))
            self.lo.append(clo)
            self.hi.append(chi)

    def __call__(self, j):
        return DI(self.lo[j], self.hi[j])


def main_chain(D, R, L):
    """Backwards from (1,1): ramp (arities 3j-1, 3j, j < R), then L bulk
    stages of arity D, each by the smallest parent.  Returns forward pairs and
    arities."""
    pair = (1, 1)
    pairs, ars = [pair], []

    def parent(pair, d):
        r, b = pair
        bh = -((-((d + 2) * r + b - 1)) // d)
        assert legal(b, bh, d, r)
        return (b, bh)

    for j in range(1, R):
        for d in (3 * j - 1, 3 * j):
            pair = parent(pair, d)
            pairs.append(pair)
            ars.append(d)
    for _ in range(L):
        pair = parent(pair, D)
        pairs.append(pair)
        ars.append(D)
    pairs.reverse()
    ars.reverse()
    return pairs, ars


def part_E(eps_list):
    rows = []
    for eps in eps_list:
        sp = sched(eps)
        eps, D, R, L, n, k, J = sp["eps"], sp["D"], sp["R"], sp["L"], sp["n"], sp["k"], sp["J"]
        W = n * k
        pairs, ars = main_chain(D, R, L)
        assert len(ars) == J and ars[0] == D and max(ars) == 24 * D - 3
        s = pairs[0][0] + pairs[0][1] - 1
        lf = LogFact(n)
        lnM, lnd = {}, {}
        for d in set(ars):
            l, o, m = max_type(n, d)
            lnM[d] = lf(n) - lf(l) - lf(o) - lf(m) + ln_int(d - 1) * l + LN2 * o
            lnd[d] = ln_int(d)
            q = d + 2
            # M >= q^n/(n+1)^2 and M <= q^n (upper note, Lemma 6)
            assert lnM[d].flo() >= (ln_int(q) * n - ln_int(n + 1) * 2).fhi()
            assert lnM[d].fhi() <= (ln_int(q) * n).flo() or d == 1
        lnA = sum((lnd[d] for d in ars), DI(Decimal(0), Decimal(0))) * (2 * W)
        lnV = sum((lnM[d] for d in ars), DI(Decimal(0), Decimal(0))) * (2 * k)
        lnm = lnV * 3
        # r_* = s^{6W} prod (2M-1)^{6k} E,  E = 1 + 6k(M-1)
        lnr = ln_int(s) * (6 * W)
        for d in ars:
            M_lo = lnM[d].lo
            tiny = exp_hi(-M_lo) * 2                       # >= 2/M
            two_m1 = DI(CF.subtract((LN2 + lnM[d]).lo, tiny), (LN2 + lnM[d]).hi)
            ee = DI(CF.subtract((ln_int(6 * k) + lnM[d]).lo, tiny), (ln_int(6 * k) + lnM[d]).hi)
            lnr = lnr + two_m1 * (6 * k) + ee
        lnBA = lnV - lnA
        lnrm = lnr - lnm
        p_lo, p_hi = (lnrm / lnBA).flo(), (lnrm / lnBA).fhi()
        assert Fr(9, 4) < p_lo and p_hi < Fr(9, 4) + Fr(719, 1988) * eps
        # recycled bank, S = 4 J D^{2W}, f_i = floor(beta_{i-1}/U_i)
        lnS = ln_int(4 * J) + lnd[D] * (2 * W)
        lb = lnS
        ln2J = ln_int(2 * J)
        min_slack = None
        for d in ars:
            y = lb - lnd[d] * (2 * W)                      # log(beta/U)
            slack = (y - ln2J).flo()
            assert slack >= 0, "funding"
            min_slack = slack if min_slack is None else min(min_slack, slack)
            u = exp_hi(-y.lo)                              # >= 1/(beta/U), <= 1/(2J)
            fl = DI(CF.subtract(y.lo, CC.multiply(u, Decimal(2))), y.hi)   # log floor
            lb = fl + lnM[d] * (2 * k)
        lnBpS = lb - lnS
        assert lnBpS.flo() >= (lnBA - LN2).flo() and lnBpS.flo() > 0
        pp_hi = (lnrm / lnBpS).fhi()
        assert pp_hi < Fr(9, 4) + eps / 2 and pp_hi - p_lo < eps / 10 ** 9
        # Proposition M on actual counts; m_* >= Abar^3
        assert lnm.fhi() <= 6 * lnA.flo() and lnr.fhi() <= Fr(35, 4) * lnA.flo()
        assert lnm.flo() >= 3 * lnA.fhi()
        # seeds: Xi = r(1+rm) n_*^3 with A < n_* <= 3A (B >= 2A);  recycled likewise
        assert lnBA.flo() > LN2.fhi() and lnBpS.flo() > LN2.fhi()
        lnXi_hi = lnr + LN2 + lnr + lnm + (ln_int(3) + lnA) * 3
        lnXip_lo = lnr + lnr + lnm + lnS * 3
        ratio = (lnXi_hi / lnXip_lo).fhi()
        assert ratio < Fr(134, 100)
        assert ratio <= Fr(4, 3) + (ln_int(54) / (lnA * 9)).fhi() + Fr(1, 10 ** 30)
        d10 = lambda v: float(v.hi / LN10.lo)
        rows.append(dict(eps=str(eps), D=D, stages=J, n=n, p_hi=float(p_hi), pp_hi=float(pp_hi),
                         dp=float(pp_hi - p_lo), digA=d10(lnA), digAp=d10(lnS), digB=d10(lnV),
                         digBp=d10(lb), digm=d10(lnm), digr=d10(lnr),
                         cut=float(lnA.lo / lnS.hi), slack=float(min_slack),
                         seed_ratio=float(ratio)))
    return rows


# ---------------------------------------------------------------------------
# Part G: the small-source barrier (gate note) under recycling.
#
# Normalized margin (gate Lemma 1): p >= p0 iff
#   3 log s - p0 log t + sum_i C(n_i, d_i, k_i, M_i; p0) >= 0,
#   C = p0 log d - (p0/n) log M + (3/n) log((2M-1)/M) + log(1+6k(M-1))/(2nk).
# Gate Lemma 3: s >= alpha z t + (4/3 - alpha) z - 1/3, z = prod lambda_d^-1,
# alpha = 40/49.  For a set G of gaining levels (M_max(n,d) > d^n) and z_G >= 1,
# s >= z_G (alpha t + 1 - alpha), so the margin is at least
#   sum_{i in G} [3 a_{d_i} + C(n_i,d_i,k_i,M_max)] + e(p0),
#   e(p0) = min_{t >= 1} [3 log(alpha t + 1 - alpha) - p0 log t].

ALPHA = Fr(40, 49)


def C_level(n, d, k, M, p0):
    lnM = ln_int(M)
    return (ln_int(d) * p0 - lnM * (p0 / n) + ln_q(Fr(2 * M - 1, M)) * Fr(3, n)
            + ln_int(1 + 6 * k * (M - 1)) * Fr(1, 2 * n * k))


def endpoint_min(a, c, p0):
    """Certified lower bound for min_{t>=1} 3 log(a t + c) - p0 log t,
    a, c > 0 rationals, 2 <= p0 < 3 (gate Lemma 5: t* = max(1, p0 c/((3-p0) a)))."""
    ts = max(Fr(1), p0 * c / ((3 - p0) * a))
    return ln_q(a * ts + c) * 3 - ln_q(ts) * p0


def gaining_triples(Wmax=64):
    out = []
    for n in range(3, Wmax + 1):
        for d in range(2, 2 * n + 1):
            M = M_max(n, d)
            if M > d ** n:
                for k in range(1, Wmax // n + 1):
                    out.append((n, d, k, M))
    return out


def part_G(quick):
    res = {}
    triples = gaining_triples(64)
    lam_lo = {}
    for p0 in (Fr(29, 10), Fr(119, 40)):
        e = endpoint_min(ALPHA, 1 - ALPHA, p0)
        margins = []
        for (n, d, k, M) in triples:
            m = a_of(d) * 3 + C_level(n, d, k, M, p0)
            margins.append((m.flo(), (n, d, k), m))
        margins.sort(key=lambda x: x[0])
        mmin = margins[0][0]
        assert mmin > 0
        info = dict(e=float(e), m_min=float(mmin), argmin=margins[0][1],
                    two_levels=float(2 * mmin + e.flo()), three_levels=float(3 * mmin + e.flo()))
        assert 3 * mmin + e.flo() > 0
        if 2 * mmin + e.flo() > 0:
            info["closed_two_or_more"] = True
        else:
            # pairs of gaining levels with m1 + m2 + e < 0 need the sharper bound
            # with z = 1/(lambda_1 lambda_2) in gate Lemma 3.
            thr = -e.flo()
            small = [x for x in margins if x[0] < thr - mmin]
            worst, bad = None, []
            for i in range(len(small)):
                for j in range(i, len(small)):
                    m1, t1, _ = small[i]
                    m2, t2, _ = small[j]
                    if m1 + m2 + e.flo() >= 0:
                        continue
                    d1, d2 = t1[1], t2[1]
                    l1 = lam_interval(d1)[1]
                    l2 = lam_interval(d2)[1]
                    z = 1 / (l1 * l2)                     # lower bound for z
                    # truncate z downward to keep the rationals small
                    z = Fr((z.numerator * 2 ** 64) // z.denominator, 2 ** 64)
                    a = ALPHA * z
                    c = (Fr(4, 3) - ALPHA) * z - Fr(1, 3)
                    n1, _, k1 = t1
                    n2, _, k2 = t2
                    M1, M2 = M_max(n1, d1), M_max(n2, d2)
                    val = (C_level(n1, d1, k1, M1, p0) + C_level(n2, d2, k2, M2, p0)
                           + endpoint_min(a, c, p0))
                    v = val.flo()
                    if worst is None or v < worst[0]:
                        worst = (v, t1, t2)
                    if v <= 0:
                        bad.append((float(v), t1, t2))
            info["pairs_checked"] = len(small)
            info["worst_pair"] = (float(worst[0]), worst[1], worst[2]) if worst else None
            info["negative_pairs"] = bad[:10]
            info["n_negative_pairs"] = len(bad)
        if not info.get("closed_two_or_more"):
            assert info["n_negative_pairs"] == 0
            info["small_triples"] = [x[1] for x in margins if x[0] < -e.flo() - mmin]
        res[str(p0)] = info
    # One gaining level, forced arity-2 cases open in the gate census at 119/40
    # (W = nk >= 33, relaxed margin >= -0.24545587207587150...).  An extra level
    # before the gaining one is funded from a bank <= S <= 2^128, so d^{2W} <= 2^128
    # and d <= 3; after it, from a bank <= 2^128 4^{2W}/2^{2W}, so d <= 7.
    for W in range(33, 65):
        assert 4 ** (2 * W) > 2 ** 128                          # d <= 3 before
        assert 8 ** (2 * W) > 2 ** 128 * 4 ** (2 * W) // 2 ** (2 * W)   # d <= 7 after
    gate_min_119_40 = Fr(-24545587207587151, 10 ** 17)            # gate table, rounded down
    assert (a_of(7) * 3).flo() + gate_min_119_40 > 0
    assert all(a_of(d).flo() >= a_of(7).flo() for d in range(2, 8))
    res["extra_level_gain_3a7"] = float(a_of(7) * 3)
    return res


# Two-level endpoint bound (new; proved in the review): for a chain with
# exactly two levels of arities d1 then d2 (any children, crops, swaps) and
# terminal t,  s >= s2(t) := min_i (a_i t + c_i) with, writing
# phi(r, c) = r (1 + 1/d1) + c (1 + 2/d1) - 1 - 1/d1,
#   phi((t + d2 + 1)/d2, t),  phi(t, (t + d2 + 1)/d2),
#   phi((d2 + 2) t/d2, 1),    phi(1, (d2 + 2) t/d2).

def two_level_pieces(d1, d2):
    def phi_coeffs(r_a, r_c, c_a, c_c):
        # phi(r_a t + r_c, c_a t + c_c) = a t + c
        A1, A2 = 1 + Fr(1, d1), 1 + Fr(2, d1)
        return (A1 * r_a + A2 * c_a, A1 * r_c + A2 * c_c - 1 - Fr(1, d1))
    q2 = Fr(d2 + 2, d2)
    return [phi_coeffs(Fr(1, d2), Fr(d2 + 1, d2), Fr(1), Fr(0)),
            phi_coeffs(Fr(1), Fr(0), Fr(1, d2), Fr(d2 + 1, d2)),
            phi_coeffs(q2, Fr(0), Fr(0), Fr(1)),
            phi_coeffs(Fr(0), Fr(1), q2, Fr(0))]


def check_two_level_bound(maxent=24, arities=(2, 3, 4, 5)):
    """Exhaustive check of s >= s2(t) over all two-level chains with entries
    <= maxent: every source pair and orientation, every legal child c1, every
    crop (x, y) <= (c1, r1) and orientation of the middle pair, every legal
    child c2 and every terminal t <= max(c2, r2).  Since s2 increases in t,
    it suffices to compare with the largest reachable terminal, computed by a
    prefix maximum over the crops (cross-checked by direct enumeration)."""
    pieces = {(d1, d2): two_level_pieces(d1, d2) for d1 in arities for d2 in arities}
    T = {}
    for d2 in arities:
        tab = [[0] * (maxent + 1) for _ in range(maxent + 1)]
        for x in range(1, maxent + 1):
            for y in range(1, maxent + 1):
                cmax = (d2 * y - x + 1) // (d2 + 2)
                tab[x][y] = max(cmax, x) if cmax >= 1 else 0
        P = [[0] * (maxent + 1) for _ in range(maxent + 1)]
        for x in range(1, maxent + 1):
            for y in range(1, maxent + 1):
                P[x][y] = max(tab[x][y], tab[y][x], P[x - 1][y], P[x][y - 1])
        T[d2] = P
    count = 0
    for r0 in range(1, maxent + 1):
        for b0 in range(1, maxent + 1):
            s = r0 + b0 - 1
            for (r1, b1) in ((r0, b0), (b0, r0)):
                for d1 in arities:
                    for c1 in range(1, b1):
                        if not legal(r1, b1, d1, c1):
                            continue
                        for d2 in arities:
                            t = T[d2][c1][r1]
                            if t == 0:
                                continue
                            bound = min(a * t + c for a, c in pieces[(d1, d2)])
                            assert s >= bound, (r0, b0, d1, c1, d2, t)
                            count += 1
    for r0 in range(1, 9):
        for b0 in range(1, 9):
            for (r1, b1) in ((r0, b0), (b0, r0)):
                for d1 in arities[:3]:
                    for c1 in range(1, b1):
                        if not legal(r1, b1, d1, c1):
                            continue
                        for d2 in arities[:3]:
                            best = 0
                            for x in range(1, c1 + 1):
                                for y in range(1, r1 + 1):
                                    for (r2, b2) in ((x, y), (y, x)):
                                        for c2 in range(1, b2):
                                            if legal(r2, b2, d2, c2):
                                                best = max(best, c2, r2)
                            assert best == T[d2][c1][r1]
    return count


def part_G_sharp(quick):
    """Pooled exponent >= p_w for every supply with S <= 2^128 (gate models),
    given the gate review's one-level search: all cases except one-level chains
    are shown to have p > p_hi = 2976961/10^6 > p_w."""
    p0 = Fr(2976961, 10 ** 6)
    out = {}
    # (a one-time run with maxent = 120 and arities 2-8, 12, 24 checked
    #  85,353,912 cases in about 10 minutes)
    out["two_level_bound_cases"] = (check_two_level_bound(40) if quick
                                    else check_two_level_bound(60, (2, 3, 4, 5, 6, 7, 8)))
    triples = gaining_triples(64)
    e = endpoint_min(ALPHA, 1 - ALPHA, p0)
    mvals = {}
    for (n, d, k, M) in triples:
        mvals[(n, d, k)] = (a_of(d) * 3 + C_level(n, d, k, M, p0)).flo()
    mmin = min(mvals.values())
    # |G| >= 3
    assert mmin > 0 and 3 * mmin + e.flo() > 0
    out["three_or_more"] = float(3 * mmin + e.flo())
    # |G| = 1 with at least one non-gaining level: the gaining level is funded,
    # so d^{2W} <= 2^128 (W >= nk); an extra level has arity
    # d' <= 2^{64/W} (d+2)/d, and it raises the relaxed bound by 3 a_{d'}.
    worst1 = None
    for (n, d, k, M) in triples:
        W = n * k
        if d ** (2 * W) > 2 ** 128:
            continue
        lam_hi = lam_interval(d)[1]
        z = 1 / lam_hi
        z = Fr((z.numerator * 2 ** 64) // z.denominator, 2 ** 64)
        rel = C_level(n, d, k, M, p0) + endpoint_min(ALPHA * z, (Fr(4, 3) - ALPHA) * z - Fr(1, 3), p0)
        dp = 2
        while (dp + 1) ** (2 * W) * d ** (2 * W) <= 2 ** 128 * (d + 2) ** (2 * W):
            dp += 1
        v = rel.flo() + (a_of(dp) * 3).flo()
        if v <= 0 or worst1 is None or v < worst1[0]:
            worst1 = (v, (n, d, k), dp, float(rel))
        assert v > 0, (n, d, k, dp, float(rel))
    out["one_gaining_extra_level_worst"] = (float(worst1[0]), worst1[1], worst1[2], worst1[3])
    # |G| = 2: pairs with m1 + m2 + e <= 0
    small = sorted([(v, key) for key, v in mvals.items() if v < -e.flo() - mmin])
    worst2, npairs = None, 0
    Ms = {(n, d, k): M for (n, d, k, M) in triples}
    for i in range(len(small)):
        for j in range(i, len(small)):
            (m1, t1), (m2, t2) = small[i], small[j]
            if m1 + m2 + e.flo() > 0:
                continue
            npairs += 1
            (n1, d1, k1), (n2, d2, k2) = t1, t2
            C12 = C_level(n1, d1, k1, Ms[t1], p0) + C_level(n2, d2, k2, Ms[t2], p0)
            # exactly two levels: exact two-level endpoint bound, both orders
            ex = None
            for (da, db) in ((d1, d2), (d2, d1)):
                for a, c in two_level_pieces(da, db):
                    if c > 0:
                        v = endpoint_min(a, c, p0)
                    else:
                        v = ln_q(a) * 3            # c = 0: minimum at t = 1
                    ex = v.flo() if ex is None else min(ex, v.flo())
            exact2 = C12.flo() + ex
            assert exact2 > 0, (t1, t2, float(exact2))
            # three or more levels: relaxed pair bound plus 3 a_{d'} for one extra level
            l1, l2 = lam_interval(d1)[1], lam_interval(d2)[1]
            z = 1 / (l1 * l2)
            z = Fr((z.numerator * 2 ** 64) // z.denominator, 2 ** 64)
            rel = C12.flo() + endpoint_min(ALPHA * z, (Fr(4, 3) - ALPHA) * z - Fr(1, 3), p0).flo()
            W = max(n1 * k1, n2 * k2)
            dp = 2
            while ((dp + 1) * d1 * d2) ** (2 * W) <= 2 ** 128 * ((d1 + 2) * (d2 + 2)) ** (2 * W):
                dp += 1
            more = rel + (a_of(dp) * 3).flo()
            assert more > 0, (t1, t2, float(rel), dp)
            cand = (float(exact2), float(rel), float(more), t1, t2, dp)
            if worst2 is None or cand[0] < worst2[0]:
                worst2 = cand
    out["pairs"] = npairs
    out["pair_worst"] = worst2
    out["m_min"] = float(mmin)
    out["e"] = float(e)
    return out


# ---------------------------------------------------------------------------
# Part H: an arity-2 prefix removes the extra logarithm of the recycled source
# (certified on actual instances; the general statement is an outline).

def part_H(eps_list):
    rows = []
    for eps in eps_list:
        sp = sched(eps)
        eps, D, R, L, n, k = sp["eps"], sp["D"], sp["R"], sp["L"], sp["n"], sp["k"]
        W = n * k
        mpre = (D - 1).bit_length()                # ceil(log2 D)
        pairs, ars = main_chain(D, R, L)
        pair = pairs[0]
        for _ in range(mpre):                      # prepend arity-2 stages (backwards)
            r, b = pair
            bh = -((-(4 * r + b - 1)) // 2)
            assert legal(b, bh, 2, r)
            pair = (b, bh)
            pairs.insert(0, pair)
            ars.insert(0, 2)
        J = len(ars)
        s = pairs[0][0] + pairs[0][1] - 1
        lf = LogFact(n)
        lnM = {}
        for d in set(ars):
            l, o, m = max_type(n, d)
            lnM[d] = lf(n) - lf(l) - lf(o) - lf(m) + ln_int(d - 1) * l + LN2 * o
        Z = DI(Decimal(0), Decimal(0))
        lnA = sum((ln_int(d) for d in ars), Z) * (2 * W)
        lnV = sum((lnM[d] for d in ars), Z) * (2 * k)
        lnm = lnV * 3
        lnr = ln_int(s) * (6 * W)                  # upper bound: 2M-1 < 2M, E < 6kM
        for d in ars:
            lnr = lnr + (LN2 + lnM[d]) * (6 * k) + ln_int(6 * k) + lnM[d]
        p_hi = ((lnr - lnm) / (lnV - lnA)).fhi()
        lnS = ln_int(4 * J) + LN2 * (2 * W)        # S = 4 J 2^{2W}
        lb = lnS
        for d in ars:
            y = lb - ln_int(d) * (2 * W)
            assert (y - ln_int(2 * J)).flo() >= 0, "funding"
            u = exp_hi(-y.lo)
            lb = DI(CF.subtract(y.lo, CC.multiply(u, Decimal(2))), y.hi) + lnM[d] * (2 * k)
        pp_hi = ((lnr - lnm) / (lb - lnS)).fhi()
        assert pp_hi < Fr(9, 4) + eps / 2
        rows.append(dict(eps=str(eps), prefix=mpre, p_hi=float(p_hi), pp_hi=float(pp_hi),
                         digS=float(lnS.hi / LN10.lo),
                         digS_without_prefix=float((ln_int(4 * (J - mpre)) + ln_int(D) * (2 * W)).hi / LN10.lo)))
    return rows


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    quick = args.quick
    t0 = time.time()

    def stamp(label, val):
        print("%-28s %s   [%.1f s]" % (label, val, time.time() - t0), flush=True)

    stamp("A literal restrictions:", part_A(quick))
    stamp("B random chain schemes:", part_B(quick))
    stamp("C constants and lemmas:", part_C())
    stamp("D Corollary R grid:", part_D(quick))
    eps_list = [Fr(1), Fr(1, 2), Fr(1, 4)] + ([] if quick else [Fr(1, 9)])
    for row in part_E(eps_list):
        stamp("E main construction:", row)
    stamp("G barrier, 29/10, 119/40:", part_G(quick))
    stamp("G barrier, sharp p_w:", part_G_sharp(quick))
    for row in part_H([Fr(1, 2), Fr(1, 4)] + ([] if quick else [Fr(1, 9)])):
        stamp("H arity-2 prefix:", row)
    print("all checks passed in %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    main()
