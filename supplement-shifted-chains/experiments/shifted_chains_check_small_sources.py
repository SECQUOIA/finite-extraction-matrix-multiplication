"""Does the small-source barrier survive forward recycling?  (Topic "small sources".)

Run from the repository root (Python 3.11+, standard library only):

    python -I -B experiments/shifted_chains_check_small_sources.py

    python -I -B experiments/shifted_chains_check_small_sources.py --screen

It prints a report and writes no file (about 15 s; --screen adds about a minute).
Note: docs/shifted-chains-check-small-sources.md.

Cost model (docs/shifted-chains-check-certificates.md Section 2, block form of
docs/shifted-chains-check-lower.md Section 2.3).  A stage of arity d >= 2 maps
the pair (r, b) to (c, r) with 1 <= c < b and (d+2)c <= d b - r + 1.  A chain
scheme has a global power P; every stage i splits the P paired factors into
blocks j with N_ij k_ij summing to P, each with a type of sector count M_ij,
and the source pair has s = r_1 + b_1 - 1.  With E = 1 + 6k(M-1):

    A   = prod_i d_i^(2P),               B   = t^(2P) prod_ij M_ij^(2k_ij),
    r_* = s^(6P) prod_ij (2M_ij-1)^(6k_ij) E_ij,
    m_* = prod_ij M_ij^(6k_ij),          p   = log(r_*/m_*) / log(B/A).

Divided by 2P, log(r_*/m_*) - p0 log(B/A) is the normalized margin

    3 log s - p0 log t + sum_i sum_j w_ij c(N_ij, d_i, k_ij, M_ij; p0),
    c(N,d,k,M;p0) = p0 log d - (p0/N) log M + (3/N) log((2M-1)/M) + log(E)/(2Nk),

with weights w_ij = N_ij k_ij / P; p < p0 iff the margin is negative.

Parts:
  A. Composition (recycling across chains) breaks the barrier: exact
     certificates of a scheme with source side 2^128 and p < 2.9, and of one
     with source side 1 and p < 2.9.
  B. Recycling inside one chain cannot break it: every chain scheme with
     P <= 64 (in particular every recycled chain with source side <= 2^128)
     has p >= p_w = 2.97696088...; the certificate of every step.
  C. A recycling-invariant replacement: every chain scheme with p < 3 has
     m_* >= M0^12, M0 = 2,558,607,507,456 (so m_* > 2^494), with equality
     attained; exact integer certificates.
  D. Regression checks of the geometric lemmas on all small chains.
  --screen: the floating-point screen that selected the composite witness of
     part A (selection only; the witness itself is certified exactly).

Arithmetic: every certified claim is an exact integer comparison or uses
rational intervals with outward rounding (2 artanh series with an explicit
tail bound, 256-bit dyadic endpoints).  No floating-point number enters a
certificate; floats appear only in printed summaries.  Every check raises
CheckError on failure (no assert statements, so python -O checks the same).
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import comb, isqrt, log, log2
import argparse
import sys
import time


class CheckError(Exception):
    """A certificate or consistency check failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


# ---------------------------------------------------------------------------
# Certified logarithms

WBITS = 256            # dyadic precision of every logarithm endpoint
SCALE = 1 << WBITS
MANTISSA = 256         # bits kept of a large integer before its logarithm
TERMS = 100            # artanh terms; rho <= 1/3, the tail is bounded explicitly


def _ln_ratio(num: int, den: int) -> tuple[int, int]:
    """Integers L <= U with L/2^W <= ln(num/den) <= U/2^W, for 1 <= num/den <= 2.

    ln x = 2 artanh(rho), rho = (x-1)/(x+1) <= 1/3; every power and term is
    rounded in the safe direction, and the tail after TERMS terms is at most
    rho^(2T+1) / ((2T+1)(1 - rho^2))."""
    require(den <= num <= 2 * den, "ratio outside [1, 2]")
    p, q = num - den, num + den
    if p == 0:
        return 0, 0
    p2, q2 = p * p, q * q
    low = (p * SCALE) // q
    high = -((-p * SCALE) // q)
    lo_sum = hi_sum = 0
    for j in range(TERMS):
        lo_sum += low // (2 * j + 1)
        hi_sum += -((-high) // (2 * j + 1))
        low = (low * p2) // q2
        high = -((-high * p2) // q2)
    tail = -((-high * q2) // ((2 * TERMS + 1) * (q2 - p2)))
    return 2 * lo_sum, 2 * (hi_sum + tail)


class Iv:
    """Closed rational interval [lo, hi]."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = Fraction(lo)
        self.hi = Fraction(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ArithmeticError("empty interval")

    def __add__(self, other):
        other = other if isinstance(other, Iv) else Iv(other)
        return Iv(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __sub__(self, other):
        other = other if isinstance(other, Iv) else Iv(other)
        return Iv(self.lo - other.hi, self.hi - other.lo)

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def scale(self, factor) -> "Iv":
        factor = Fraction(factor)
        if factor >= 0:
            return Iv(self.lo * factor, self.hi * factor)
        return Iv(self.hi * factor, self.lo * factor)

    def over(self, other: "Iv") -> "Iv":
        require(self.lo >= 0 and other.lo > 0, "division needs num >= 0 and den > 0")
        return Iv(self.lo / other.hi, self.hi / other.lo)

    def __repr__(self):
        return f"[{float(self.lo):.15g}, {float(self.hi):.15g}]"


LN2_INT = _ln_ratio(2, 1)


@lru_cache(maxsize=None)
def ln_int(x: int) -> Iv:
    """Enclosure of ln x for a positive integer x."""
    require(isinstance(x, int) and x >= 1, "positive integer required")
    if x == 1:
        return Iv(0)
    e = x.bit_length() - 1
    if e <= MANTISSA:
        lo_r = hi_r = (x, 1 << e)
    else:
        top = x >> (e - MANTISSA)
        lo_r, hi_r = (top, 1 << MANTISSA), (top + 1, 1 << MANTISSA)
    lo = e * LN2_INT[0] + _ln_ratio(*lo_r)[0]
    hi = e * LN2_INT[1] + _ln_ratio(*hi_r)[1]
    return Iv(Fraction(lo, SCALE), Fraction(hi, SCALE))


def ln_frac(x: Fraction) -> Iv:
    x = Fraction(x)
    require(x > 0, "positive rational required")
    return ln_int(x.numerator) - ln_int(x.denominator)


def ln_big(x: int) -> Iv:
    """Enclosure of ln x for an arbitrary positive integer (not cached)."""
    return ln_int.__wrapped__(x)


# ---------------------------------------------------------------------------
# lambda_d, the positive root of (d+2)x^2 + x - d


@lru_cache(maxsize=None)
def lam_bounds(d: int, bits: int = 160) -> tuple[Fraction, Fraction]:
    """Rationals lo < lambda_d <= hi, certified by the sign of f(x) = (d+2)x^2 + x - d."""
    q = d + 2
    root = isqrt((1 + 4 * d * q) << (2 * bits))          # sqrt(1+4dq) in [root, root+1]/2^bits
    lo = Fraction(root - (1 << bits), 2 * q << bits)
    hi = Fraction(root + 1 - (1 << bits), 2 * q << bits)

    def f(x):
        return q * x * x + x - d
    require(lo > 0 and f(lo) < 0 <= f(hi), f"lambda enclosure for d={d}")
    return lo, hi


def a_lower(d: int) -> Fraction:
    """Lower bound of a_d = -ln(lambda_d)."""
    return (-ln_frac(lam_bounds(d)[1])).lo


# ---------------------------------------------------------------------------
# Types and sector counts


def sector_count(N: int, d: int, nK: int, nO: int) -> int:
    return comb(N, nK) * comb(N - nK, nO) * (d - 1) ** nK * 2 ** nO


@lru_cache(maxsize=None)
def all_counts(N: int, d: int) -> tuple[int, ...]:
    """Sorted distinct sector counts of all types (nK, nO, nmid) of width N."""
    return tuple(sorted({sector_count(N, d, a, b) for a in range(N + 1) for b in range(N + 1 - a)}))


@lru_cache(maxsize=None)
def mode(N: int, d: int) -> tuple[int, int, int]:
    """A type of largest sector count, certified by the exchange conditions
    w_i a_j <= w_j (a_i + 1) (i != j, a_j > 0) for the weights w = (d-1, 2, 1);
    these characterize the maxima (docs/shifted-chains-check-certificates.md, Lemma 2)."""
    w = (d - 1, 2, 1)
    a = [max(0, N * wi // (d + 2) - 1) for wi in w]
    for _ in range(N - sum(a)):
        best = 0
        for i in (1, 2):
            if w[i] * (a[best] + 1) > w[best] * (a[i] + 1):
                best = i
        a[best] += 1
    for i in range(3):
        for j in range(3):
            if i != j and a[j] > 0:
                require(w[i] * a[j] <= w[j] * (a[i] + 1), f"mode certificate N={N} d={d}")
    return tuple(a)


@lru_cache(maxsize=None)
def m_max(N: int, d: int) -> int:
    a = mode(N, d)
    return sector_count(N, d, a[0], a[1])


def gains(N: int, d: int) -> bool:
    return m_max(N, d) > d ** N


@lru_cache(maxsize=None)
def cost(N: int, d: int, k: int, M: int, p0: Fraction) -> Iv:
    """Enclosure of c(N, d, k, M; p0)."""
    E = 1 + 6 * k * (M - 1)
    return (ln_int(d).scale(p0) - ln_int(M).scale(Fraction(p0) / N)
            + (ln_int(2 * M - 1) - ln_int(M)).scale(Fraction(3, N))
            + ln_int(E).scale(Fraction(1, 2 * N * k)))


def endpoint_min(a: Fraction, C: Fraction, p0: Fraction) -> Iv:
    """Enclosure of min over real t >= 1 of 3 ln(a t + C) - p0 ln t (a > 0, C >= 0, p0 < 3).

    The derivative has the sign of (3 - p0) a t - p0 C, so the minimum is at
    t* = max(1, p0 C / ((3 - p0) a)) (Lemma 5 of the gate note)."""
    require(a > 0 and C >= 0 and p0 < 3, "endpoint_min arguments")
    t = max(Fraction(1), p0 * C / ((3 - p0) * a))
    return ln_frac(a * t + C).scale(3) - ln_frac(t).scale(p0)


def ceil_div(x: int, y: int) -> int:
    return -((-x) // y)


def s_min_one(d: int, t: int) -> int:
    """Least source span of a chain with a stage of arity d and terminal t:
    ceil(((d+1) t + 1) / d) (Lemma 4 of the gate note, extended in the note)."""
    return ceil_div((d + 1) * t + 1, d)


def one_stage(N: int, k: int, d: int, t: int, M: int | None = None):
    """Exact integers (A, B, r, m, s) of the one-stage chain (t, s-t+1) -> (1, t), c = 1."""
    M = m_max(N, d) if M is None else M
    s = s_min_one(d, t)
    r0, b0, c = t, s - t + 1, 1
    require(1 <= c < b0 and (d + 2) * c <= d * b0 - r0 + 1, "illegal one-stage chain")
    P = N * k
    A = d ** (2 * P)
    B = t ** (2 * P) * M ** (2 * k)
    r = s ** (6 * P) * (2 * M - 1) ** (6 * k) * (1 + 6 * k * (M - 1))
    m = M ** (6 * k)
    return A, B, r, m, s


def exponent_iv(A: int, B: int, r: int, m: int) -> Iv:
    return (ln_big(r) - ln_big(m)).over(ln_big(B) - ln_big(A))


def below(r: int, m: int, A: int, B: int, q: Fraction) -> bool:
    """Exact test of p < q, i.e. r^v A^u < m^v B^u for q = u/v (B > A)."""
    require(B > A, "not a relative scheme")
    u, v = q.numerator, q.denominator
    return r ** v * A ** u < m ** v * B ** u


def bits(x: int) -> float:
    """log2 x, for printing only."""
    e = max(0, x.bit_length() - 60)
    return log2(x >> e) + e


# ---------------------------------------------------------------------------
# Part A. Composition across chains


W_DATA = {"N": 32, "k": 2, "d": 2, "t": 43}           # the gate witness (43,23) -> (1,43)
T_DATA = {"N": 92, "k": 5, "d": 2, "t": 7}            # (7,5) -> (1,7)


def part_a() -> dict:
    out = {}
    Aw, Bw, rw, mw, sw = one_stage(**W_DATA)
    require(Aw == 1 << 128 and sw == 65 and mode(32, 2) == (8, 16, 8), "W data")
    require(m_max(32, 2) == 506980245130444800, "W sector count")
    pw = exponent_iv(Aw, Bw, rw, mw)
    require(Fraction(2976960882, 10 ** 9) < pw.lo and pw.hi < Fraction(2976960883, 10 ** 9),
            "p_w enclosure")
    out["W"] = {"A_bits": 128, "B_log2": bits(Bw), "m_log2": bits(mw), "p": pw}

    At, Bt, rt, mt, st = one_stage(**T_DATA)
    require(At == 1 << 920 and st == 11, "T data")
    pt = exponent_iv(At, Bt, rt, mt)
    out["T"] = {"A_log2": 920, "B_log2": bits(Bt), "m_log2": bits(mt), "p": pt,
                "type": mode(92, 2), "s": st}

    # Composition: W's produced MM_{B_w} supplies T's auxiliary MM_{A_T}.
    require(Bw >= At, "W's target side must cover T's source side")
    f = Bw // At
    A1, B1, r1, m1 = Aw, Bt * f, rw * rt, mw * mt
    p1 = exponent_iv(A1, B1, r1, m1)
    require(below(r1, m1, A1, B1, Fraction(29, 10)), "W then T: p < 29/10")
    require(below(r1, m1, A1, B1, Fraction(287, 100)), "W then T: p < 287/100")
    require(not below(r1, m1, A1, B1, Fraction(2866, 1000)), "W then T: p >= 2866/1000")
    require(p1.hi < pw.lo, "W then T beats p_w")
    out["WT"] = {"A_bits": 128, "floor_factor": f, "B_log2": bits(B1), "m_log2": bits(m1),
                 "r_log2": bits(r1), "p": p1, "B_digits": len(str(B1))}

    # Classical precomposition: (A_T)^3 MM_1 |> MM_{A_T} (the classical algorithm), then T.
    A2, B2, r2, m2 = 1, Bt, At ** 3 * rt, mt
    p2 = exponent_iv(A2, B2, r2, m2)
    require(below(r2, m2, A2, B2, Fraction(29, 10)), "classical then T: p < 29/10")
    require(below(r2, m2, A2, B2, Fraction(2875, 1000)), "classical then T: p < 2875/1000")
    out["CT"] = {"A": 1, "B_log2": bits(B2), "m_log2": bits(m2), "p": p2}

    # Iterating T after W: the exponent decreases toward p_T (bank floors included exactly).
    bank, r, m = Bw, rw, mw
    trail = []
    for j in range(1, 7):
        require(bank >= At, "bank too small")
        bank = (bank // At) * Bt
        r, m = r * rt, m * mt
        trail.append((j, exponent_iv(Aw, bank, r, m)))
    for (_, a), (_, b) in zip(trail, trail[1:]):
        require(b.hi < a.lo, "iterating T must lower the exponent here")
    out["iterates"] = trail
    return out


# ---------------------------------------------------------------------------
# Part B. Recycling inside one chain: P <= 64 forces p >= p_w (Theorem 1)

P_CAP = 64
P_HI = Fraction(2976961, 10 ** 6)
ALPHA = Fraction(40, 49)
T0 = 600


def gaining_blocks(d: int, pcap: int = P_CAP):
    """All (N, k) with N k <= pcap and a gaining type at arity d (Lemma 4(b) of the lower note:
    gain forces N >= 3 and d <= 2N)."""
    for N in range(3, pcap + 1):
        if d > 2 * N or not gains(N, d):
            continue
        for k in range(1, pcap // N + 1):
            yield N, k


def part_b() -> dict:
    out = {}
    # B1. Best local cost per arity at p_hi over all gaining blocks with N k <= 64, largest type
    # (Lemma 8 of the gate note: for a gaining block the largest type has the least cost).
    cstar = {}
    arg = {}
    for d in range(2, 2 * P_CAP + 1):
        best = None
        for N, k in gaining_blocks(d):
            c = cost(N, d, k, m_max(N, d), P_HI)
            if best is None or c.lo < best.lo:
                best, arg[d] = c, (N, k)
        if best is not None:
            cstar[d] = best
    for d in range(2 * P_CAP + 1, 2 * P_CAP + 40):
        require(not any(gains(N, d) for N in range(1, P_CAP + 1)), f"unexpected gain at d={d}")
    kept = sorted(d for d, c in cstar.items() if c.lo < 0)
    require(kept == [2, 3, 4, 5], f"kept arities {kept}")
    for d, c in cstar.items():
        if d not in kept:
            require(c.lo >= 0, f"local cost at d={d} must be nonnegative")
        else:
            require(c.hi < 0, f"local cost at d={d} must be negative")
    out["cstar"] = {d: (cstar[d], arg[d]) for d in kept}
    out["min_nonneg"] = min((cstar[d].lo, d) for d in cstar if d not in kept)

    # B2. eta(d) = 3 a_d + c*(d) > 0.
    eta = {d: 3 * a_lower(d) + cstar[d].lo for d in kept}
    require(all(v > 0 for v in eta.values()), "eta must be positive")
    out["eta"] = eta

    # B3. Relaxed two-stage margins (gate Lemma 3 with Lemma 5).
    def relaxed(word):
        z = Fraction(1)
        for d in word:
            z /= lam_bounds(d)[1]
        a, C = ALPHA * z, (Fraction(4, 3) - ALPHA) * z - Fraction(1, 3)
        return endpoint_min(a, C, P_HI).lo + sum(cstar[d].lo for d in word)

    pairs = {(d1, d2): relaxed((d1, d2)) for d1 in kept for d2 in kept if d1 <= d2}
    open_pairs = sorted(w for w, v in pairs.items() if v <= 0)
    require(open_pairs == [(2, 2)], f"open pairs {open_pairs}")
    out["pairs"] = pairs

    # B4. The word (2, 2) by exact least-source affine bounds.
    forms = least_source_forms((2, 2))
    exact22 = min(endpoint_min(kap, kap0, P_HI).lo for kap, kap0 in forms) + 2 * cstar[2].lo
    require(exact22 > 0, "(2,2) not closed")
    out["forms22"] = forms
    out["exact22"] = exact22

    # B5. Three or more kept stages: R(w) >= R(pair) + sum of eta over the others.
    three = min(pairs.values()) + min(eta.values())
    require(three > 0, "three-stage words not closed")
    out["three"] = three

    # B6. One kept stage: every one-stage datum with N k <= 64 and d in kept has margin > 0
    # at p_hi, except the witness W, whose exponent is p_w < p_hi.
    closed_relaxed = scanned = 0
    near = []
    for d in kept:
        a, C = Fraction(d + 1, d), Fraction(1, d)
        tstar = P_HI * C / ((3 - P_HI) * a)
        require(tstar <= T0, "tail start")
        for N, k in gaining_blocks(d):
            M = m_max(N, d)
            c = cost(N, d, k, M, P_HI)
            if endpoint_min(a, C, P_HI).lo + c.lo > 0:
                closed_relaxed += 1
                continue
            scanned += 1
            tail = ln_frac(a * T0 + C).scale(3) - ln_int(T0).scale(P_HI) + c
            require(tail.lo > 0, f"tail N={N} k={k} d={d}")
            for t in range(1, T0 + 1):
                s = s_min_one(d, t)
                margin = ln_int(s).scale(3) - ln_int(t).scale(P_HI) + c
                if (N, k, d, t) == (32, 2, 2, 43):
                    require(margin.hi < 0, "W must have p < p_hi")
                    continue
                require(margin.lo > 0, f"one-stage datum N={N} k={k} d={d} t={t}")
                near.append((margin.lo, N, k, d, t))
    near.sort()
    out["one_stage"] = {"closed_by_relaxation": closed_relaxed, "scanned": scanned,
                        "closest": near[:3]}
    return out


def least_source_forms(word):
    """Affine lower bounds s >= kappa t + kappa0, one per orientation choice, for every
    chain containing stages of the given arities (in this order) and terminal t.

    Backward from the terminal: the last kept stage's output (c, r) dominates (1, t)
    or (t, 1); its input is (r, b) with b >= ((d+2) c + r - 1)/d; the previous kept
    stage's output dominates that input in one of two orders; and so on.  Every
    lower bound is increasing in c and r, so equality in each step is least.
    Other stages, crops and swaps only replace a pair by a dominated pair."""
    states = [((Fraction(0), Fraction(1)), (Fraction(1), Fraction(0))),     # (c, r) = (1, t)
              ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))]     # (c, r) = (t, 1)
    # an affine form is (coefficient of t, constant)
    for i, d in enumerate(reversed(word)):
        new = []
        for c, r in states:
            b = ((d + 2) * c[0] + r[0]) / d, ((d + 2) * c[1] + r[1] - 1) / d
            if i == len(word) - 1:
                new.append((r[0] + b[0], r[1] + b[1] - 1))
            else:
                new.append((r, b))
                new.append((b, r))
        states = new
    return sorted(set(states))


# ---------------------------------------------------------------------------
# Part C. Batch size of subcubic schemes (Theorem 2)


def part_c() -> dict:
    out = {}
    M0 = m_max(23, 2)
    require(M0 == all_counts(23, 2)[-1] == 2558607507456, "M0")
    modes = [(a, b, 23 - a - b) for a in range(24) for b in range(24 - a)
             if sector_count(23, 2, a, b) == M0]
    cap = M0 ** 12                                   # the budget: m_* < cap
    out["M0"], out["modes"], out["cap_log2"] = M0, modes, bits(cap)

    # C1. One kept stage.  A block (N, d, k, M) with M^(6k) < cap must satisfy
    # (d+1)^(6Nk) (2M-1)^(6k) E >= M^(12k), i.e. 3 ln((d+1)/d) + c(N,d,k,M;3) >= 0.
    # Only M > (d+1)^N can fail; that needs N >= 3 and d <= 2N.
    n1 = 0
    d = 2
    while (d + 1) ** (6 * max(3, ceil_div(d, 2))) < cap:
        N = max(3, ceil_div(d, 2))
        while (d + 1) ** (6 * N) < cap:
            if d <= 2 * N:
                counts = [M for M in all_counts(N, d) if M > (d + 1) ** N]
                k = 1
                while (d + 1) ** (6 * N * k) < cap:
                    for M in counts:
                        if M ** (6 * k) >= cap:
                            break
                        E = 1 + 6 * k * (M - 1)
                        require((d + 1) ** (6 * N * k) * (2 * M - 1) ** (6 * k) * E >= M ** (12 * k),
                                f"one-stage subcubic block below the cap: N={N} d={d} k={k} M={M}")
                        n1 += 1
                    k += 1
            N += 1
        d += 1
    out["one_stage_checks"] = n1

    # C2. Two or more kept stages.  Every gaining block (M > d^N) with M^(6k) < cap has
    # eta = 3 a_d + c(N,d,k,M;3) >= ln(34/25); and 2 ln(34/25) + 3 ln(40/49) > 0.
    require(34 ** 2 * 40 ** 3 > 25 ** 2 * 49 ** 3, "2 ln(34/25) + 3 ln(40/49) > 0")
    n2 = 0
    worst = None
    d = 2
    while d ** (6 * max(3, ceil_div(d, 2))) < cap:
        lam_hi = lam_bounds(d, bits=48)[1]
        u, v = lam_hi.numerator, lam_hi.denominator
        N = max(3, ceil_div(d, 2))
        while d ** (6 * N) < cap:
            if d <= 2 * N:
                counts = [M for M in all_counts(N, d) if M > d ** N]
                k = 1
                while d ** (6 * N * k) < cap:
                    left_fixed = d ** (6 * N * k) * 25 ** (2 * N * k) * v ** (6 * N * k)
                    right_fixed = 34 ** (2 * N * k) * u ** (6 * N * k)
                    for M in counts:
                        if M ** (6 * k) >= cap:
                            break
                        E = 1 + 6 * k * (M - 1)
                        require(left_fixed * (2 * M - 1) ** (6 * k) * E >= right_fixed * M ** (12 * k),
                                f"eta below ln(34/25): N={N} d={d} k={k} M={M}")
                        n2 += 1
                    if counts and counts[0] ** (6 * k) < cap:
                        top = max(M for M in counts if M ** (6 * k) < cap)
                        val = 3 * a_lower(d) + cost(N, d, k, top, Fraction(3)).lo
                        if worst is None or val < worst[0]:
                            worst = (val, N, d, k, top)
                    k += 1
            N += 1
        d += 1
    out["multi_stage_checks"] = n2
    out["eta_min"] = worst

    # C3. Sharpness: the one-stage chain N=23, k=2, d=2, largest type, least terminal t.
    t = 1
    while True:
        A, B, r, m, s = one_stage(23, 2, 2, t, M0)
        if B > A and below(r, m, A, B, Fraction(3)):
            break
        t += 1
        require(t < 5000, "no subcubic terminal found")
    require(m == cap, "m_* of the sharp chain")
    A2, B2, r2, m2, _ = one_stage(23, 2, 2, t - 1, M0)
    out["sharp"] = {"t": t, "s": s, "source_pair": (t, s - t + 1), "A_log2": 92,
                    "B_log2": bits(B), "B_digits": len(str(B)), "m_log2": bits(m),
                    "r_log2": bits(r), "p": exponent_iv(A, B, r, m),
                    "previous_t_not_subcubic": not (B2 > A2 and below(r2, m2, A2, B2, Fraction(3)))}
    return out


# ---------------------------------------------------------------------------
# Part D. Regression checks of the geometry on small chains (exact rationals)


def part_d(limit: int = 12, depth: int = 3, arities=(2, 3, 4, 5)) -> dict:
    stats = {"endpoints": 0, "two_arity2": 0}
    forms22 = least_source_forms((2, 2))

    def walk(state, word, s):
        if word:
            z = Fraction(1)
            for d in word:
                z /= lam_bounds(d)[1]
            for t in state:
                stats["endpoints"] += 1
                require(t <= s, "t <= s")
                require(s >= ALPHA * z * t + (Fraction(4, 3) - ALPHA) * z - Fraction(1, 3),
                        f"gate Lemma 3 fails at {word}, s={s}, t={t}")
                for d in set(word):
                    require(d * s >= (d + 1) * t + 1, f"extended Lemma 4 fails at {word}, s={s}, t={t}")
                if word.count(2) >= 2:
                    stats["two_arity2"] += 1
                    require(any(s >= kap * t + kap0 for kap, kap0 in forms22),
                            f"(2,2) forms fail at {word}, s={s}, t={t}")
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
    # Modes against exhaustive enumeration.
    n_modes = 0
    for N in range(1, 41):
        for d in range(2, 2 * N + 4):
            require(m_max(N, d) == all_counts(N, d)[-1], f"mode N={N} d={d}")
            n_modes += 1
    stats["modes_checked"] = n_modes
    return stats


# ---------------------------------------------------------------------------
# Optional: the floating-point screen that selected T (selection only)


def screen_composites(tmax: int = 200) -> list[tuple]:
    """Exponent of W followed by every one-stage arity-2 chain T with A_T <= B_w and t <= tmax.

    Floats are used only to rank candidates; part A certifies the chosen one exactly."""
    Aw, Bw, rw, mw, _ = one_stage(**W_DATA)

    def flog(x):
        e = max(0, x.bit_length() - 900)
        return log(x >> e) + e * log(2)
    lw = flog(rw) - flog(mw)
    budget = Bw.bit_length() - 1                    # 2^budget <= B_w
    ranked = []
    for N in range(3, budget // 2 + 1):
        if not gains(N, 2):
            continue
        M = m_max(N, 2)
        for k in range(1, budget // (2 * N) + 1):
            P = N * k
            At = 1 << (2 * P)
            if At > Bw:
                continue
            f = Bw // At
            for t in range(2, tmax + 1):
                s = s_min_one(2, t)
                lr = 6 * P * log(s) + 6 * k * log((2 * M - 1) / M) + log(1 + 6 * k * (M - 1))
                lg = 2 * P * log(t) + 2 * k * log(M) + log(f) - 128 * log(2)
                if lg > 0:
                    ranked.append(((lw + lr) / lg, N, k, t))
    ranked.sort()
    return ranked[:5]


# ---------------------------------------------------------------------------


def fmt(iv: Iv, digits: int = 12) -> str:
    scale = 10 ** digits
    lo = (iv.lo * scale).__floor__()
    hi = (iv.hi * scale).__ceil__()
    return f"[{lo / scale:.{digits}f}, {hi / scale:.{digits}f}]"


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--screen", action="store_true",
                        help="also rerun the floating-point screen that selected the composite witness")
    args = parser.parse_args(argv)
    t0 = time.time()
    a = part_a()
    print("A. Composition across chains (exact integers)")
    print(f"   W: (43,23) -> (1,43), d=2, N=32, k=2, type (8,16,8): A = 2^128,"
          f" log2 B = {a['W']['B_log2']:.3f}, log2 m_* = {a['W']['m_log2']:.3f}, p in {fmt(a['W']['p'])}")
    print(f"   T: (7,5) -> (1,7), d=2, N=92, k=5, type {a['T']['type']}: A = 2^920,"
          f" log2 B = {a['T']['B_log2']:.3f}, log2 m_* = {a['T']['m_log2']:.3f}, p in {fmt(a['T']['p'])}")
    print(f"   W then T (T's auxiliary from W's output, floor factor {a['WT']['floor_factor']}): A' = 2^128,"
          f" log2 B' = {a['WT']['B_log2']:.3f} ({a['WT']['B_digits']} digits), log2 m_* = {a['WT']['m_log2']:.3f},")
    print(f"      p in {fmt(a['WT']['p'])}; certified exactly: 2866/1000 <= p < 287/100 < 29/10")
    print(f"   classical MM_(2^920) then T: A' = 1, log2 B' = {a['CT']['B_log2']:.3f},"
          f" p in {fmt(a['CT']['p'])}; certified exactly: p < 2875/1000 < 29/10")
    print("   W then T repeated j times (exact floors): " +
          ", ".join(f"j={j}: p<{float(iv.hi):.6f}" for j, iv in a["iterates"]))

    b = part_b()
    print("B. One chain, P <= 64 (covers every recycled chain with A' <= 2^128)")
    for d, (c, (N, k)) in b["cstar"].items():
        print(f"   d={d}: least local cost at p_hi = 2.976961 is {fmt(c, 9)} at (N,k)=({N},{k});"
              f" eta > {float(b['eta'][d]):.6f}")
    print(f"   all other arities have local cost >= 0 (least {float(b['min_nonneg'][0]):.6f} at d={b['min_nonneg'][1]})")
    print("   relaxed two-stage margins: " + ", ".join(f"{w}: {float(v):+.6f}" for w, v in sorted(b["pairs"].items())))
    print(f"   (2,2) least-source forms {[(str(x), str(y)) for x, y in b['forms22']]}; exact margin > {float(b['exact22']):.6f}")
    print(f"   three or more kept stages: margin > {float(b['three']):.6f}")
    o = b["one_stage"]
    print(f"   one kept stage: {o['closed_by_relaxation']} blocks closed by the relaxation, {o['scanned']} scanned"
          f" for t <= {T0} with tails; closest normalized margins (other than W): "
          + ", ".join(f"{float(m):.3e} at (N,k,d,t)={x}" for m, *x in o["closest"]))
    print("   => every chain scheme with P <= 64 has p >= p_w, with equality only for W's data")

    c = part_c()
    print("C. Batch size of subcubic chain schemes (exact integers)")
    print(f"   M0 = M_max(23,2) = {c['M0']}, modes {c['modes']}; M0^12 = 2^{c['cap_log2']:.4f}")
    print(f"   one kept stage: {c['one_stage_checks']} blocks with M > (d+1)^N and M^(6k) < M0^12,"
          f" none with (d+1)^(6Nk) (2M-1)^(6k) E < M^(12k)")
    print(f"   two or more kept stages: {c['multi_stage_checks']} gaining blocks with M^(6k) < M0^12, all eta >= ln(34/25);"
          f" least eta > {float(c['eta_min'][0]):.6f} at (N,d,k)={c['eta_min'][1:4]}")
    sh = c["sharp"]
    print(f"   sharp: one stage {sh['source_pair']} -> (1,{sh['t']}), d=2, N=23, k=2: p in {fmt(sh['p'])} < 3,"
          f" m_* = M0^12, log2 B = {sh['B_log2']:.2f} ({sh['B_digits']} digits), log2 r_* = {sh['r_log2']:.2f};"
          f" t-1 not subcubic: {sh['previous_t_not_subcubic']}")

    dd = part_d()
    print(f"D. Geometry regression: {dd['endpoints']} chain endpoints (depth <= 3, r0,b0 <= 12, arities 2..5),"
          f" {dd['two_arity2']} with two arity-2 stages; {dd['modes_checked']} modes checked exhaustively")
    if args.screen:
        print("Screen (floating point, selection only): best compositions W then T, T one stage of arity 2:")
        for p, N, k, t in screen_composites():
            print(f"   p ~ {p:.9f} at (N,k,t) = ({N},{k},{t})")
    print(f"all checks passed in {time.time() - t0:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
