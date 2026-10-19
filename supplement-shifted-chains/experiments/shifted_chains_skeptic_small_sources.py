"""Independent checks for the adversarial review of
docs/shifted-chains-check-small-sources.md (topic "small sources").

Run from the repository root (Python 3.11+, standard library only):

    python -I -B experiments/shifted_chains_skeptic_small_sources.py

It prints a report and writes no file (about 30 s).  It imports nothing
from the repository and shares no code with
experiments/shifted_chains_check_small_sources.py.

Arithmetic.  Every claim marked "exact" is an exact integer comparison.
Claims about real numbers (pooled exponents, local costs, margins) use
Python's decimal module at 100 significant digits; Decimal.ln and Decimal.sqrt
are correctly rounded, so every computed value is within 1e-80 of the true
value, and every sign decision must clear a padding of 1e-50.  Logarithms of
large integers use the top 400 bits (relative error below 2^-399).  Floats
appear only in printed summaries.  Every check raises CheckError on failure.

Parts
  A. The composite witnesses of the note (W, then T; classical, then T; the
     iterates), recomputed from independent counts (sector counts by
     exhaustive type enumeration).
  B. NEW: block-level recycling inside ONE chain.  A one-stage chain of
     arity 2 whose blocks are funded one after another from the bank has
     source side 2^128 (resp. 64) and pooled exponent below 2.9 (resp. 2.85),
     certified exactly.  So the note's claim that recycling inside one chain
     cannot beat p_w at source side <= 2^128 holds only for stage-level
     supplies.
  C. Theorem 2 (m_* >= M0^12 for p < 3): both finite enumerations redone with
     different loops and a different rational upper bound for lambda_d; the
     sharp chain; and the effect of discarding copies.
  D. Theorem 1 (P <= 64 implies p >= p_w): the local costs, pair margins,
     (2,2) forms and one-stage scan redone in decimal arithmetic, with the
     local costs minimized over ALL types for d <= 6 (no use of the
     largest-type lemma there).
  E. Geometry on small chains with free crops (depth <= 4): the extended
     one-stage bound, the potential bound with alpha = 40/49, and the four
     (2,2) forms, by exhaustive enumeration.
"""

from __future__ import annotations

import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from functools import lru_cache
from math import comb, isqrt

getcontext().prec = 100
PAD = Decimal("1e-50")


class CheckError(Exception):
    pass


def need(cond: bool, msg: str) -> None:
    if not cond:
        raise CheckError(msg)


# ---------------------------------------------------------------------------
# Logarithms (decimal) and counts

LN2 = Decimal(2).ln()


def ln(x) -> Decimal:
    """ln of a positive integer or Fraction, to about 1e-90 absolute error."""
    if isinstance(x, Fraction):
        return ln(x.numerator) - ln(x.denominator)
    need(isinstance(x, int) and x >= 1, "ln of a positive integer")
    if x.bit_length() <= 4096:
        return _ln_small(x)
    e = x.bit_length() - 400
    return Decimal(x >> e).ln() + e * LN2


@lru_cache(maxsize=None)
def _ln_small(x: int) -> Decimal:
    e = max(0, x.bit_length() - 400)
    return Decimal(x >> e).ln() + e * LN2


def pos(x: Decimal, msg: str) -> None:
    need(x > PAD, msg)


def neg(x: Decimal, msg: str) -> None:
    need(x < -PAD, msg)


def sector(N: int, d: int, a: int, b: int) -> int:
    """Sector count of the type (kernel a, outer b, middle N-a-b) at arity d."""
    return comb(N, a) * comb(N - a, b) * (d - 1) ** a * 2 ** b


@lru_cache(maxsize=None)
def counts(N: int, d: int) -> tuple[int, ...]:
    """All distinct sector counts of width N at arity d, ascending (exhaustive)."""
    return tuple(sorted({sector(N, d, a, b) for a in range(N + 1) for b in range(N + 1 - a)}))


def mmax(N: int, d: int) -> int:
    return counts(N, d)[-1]


def s_least(d: int, t: int) -> int:
    """ceil(((d+1)t+1)/d)."""
    return ((d + 1) * t + 1 + d - 1) // d


def lam_upper(d: int) -> Fraction:
    """A rational u/v >= lambda_d (positive root of (d+2)x^2+x-d), certified by f(u/v) >= 0.

    Different from the checker: Newton's method from x = 1 (f is convex and
    increasing on x > 0, so the iterates stay above the root), each iterate
    rounded up to a multiple of 2^-80."""
    q = d + 2

    def f(x):
        return q * x * x + x - d
    x = Fraction(1)
    for _ in range(200):
        y = x - f(x) / (2 * q * x + 1)
        y = Fraction(-((-y.numerator * 2 ** 80) // y.denominator), 2 ** 80)
        if y >= x:
            break
        x = y
    need(f(x) >= 0 and x > 0, f"lambda upper bound d={d}")
    need(f(x - Fraction(1, 2 ** 70)) < 0, f"lambda upper bound not tight d={d}")
    return x


def lam_dec(d: int) -> Decimal:
    q = d + 2
    return ((Decimal(1 + 4 * d * q)).sqrt() - 1) / (2 * q)


def chain_counts(S_supply, t: int, s: int, stages):
    """Counts of a chain scheme.  stages = [(d, [(N, k, M), ...]), ...].

    Returns (A, B, r, m, P) for the source supply."""
    P = sum(N * k for N, k, _ in stages[0][1])
    A, B, r, m = 1, t ** (2 * P), s ** (6 * P), 1
    for d, blocks in stages:
        need(sum(N * k for N, k, _ in blocks) == P, "blocks must cover the P factors")
        A *= d ** (2 * P)
        for N, k, M in blocks:
            E = 1 + 6 * k * (M - 1)
            B *= M ** (2 * k)
            r *= (2 * M - 1) ** (6 * k) * E
            m *= M ** (6 * k)
    return A, B, r, m, P


def below(r: int, m: int, A: int, B: int, q: Fraction) -> bool:
    """Exact: p < q  iff  r^v A^u < m^v B^u  (B > A)."""
    need(B > A, "B > A")
    u, v = q.numerator, q.denominator
    return r ** v * A ** u < m ** v * B ** u


def pdec(A, B, r, m) -> Decimal:
    return (ln(r) - ln(m)) / (ln(B) - ln(A))


# ---------------------------------------------------------------------------
# Part A


def one_stage(N, k, d, t):
    s = s_least(d, t)
    r0, b0 = t, s - t + 1
    need((d + 2) * 1 <= d * b0 - r0 + 1 and 1 < b0, "legal one-stage chain")
    M = mmax(N, d)
    return chain_counts(None, t, s, [(d, [(N, k, M)])])[:4], s


def part_a():
    out = {}
    (Aw, Bw, rw, mw), sw = one_stage(32, 2, 2, 43)
    Mw = mmax(32, 2)
    need(Mw == 506980245130444800 and sw == 65 and Aw == 2 ** 128, "W data")
    need(Mw == sector(32, 2, 8, 16), "W type (8,16,8)")
    pw = pdec(Aw, Bw, rw, mw)
    need(Decimal("2.976960882515") < pw < Decimal("2.976960882516"), "p_w")
    (At, Bt, rt, mt), st = one_stage(92, 5, 2, 7)
    need(At == 2 ** 920 and st == 11, "T data")
    need(mmax(92, 2) == sector(92, 2, 23, 46), "T type (23,46,23)")
    pt = pdec(At, Bt, rt, mt)
    out["pw"], out["pt"] = pw, pt
    # W then T (composition; T's auxiliary from W's output)
    f = Bw // At
    need(f == 904, "floor factor")
    A1, B1, r1, m1 = Aw, Bt * f, rw * rt, mw * mt
    need(below(r1, m1, A1, B1, Fraction(287, 100)), "W;T: p < 2.87")
    need(not below(r1, m1, A1, B1, Fraction(2866, 1000)), "W;T: p >= 2.866")
    out["WT"] = pdec(A1, B1, r1, m1)
    out["WT_digits"] = len(str(B1))
    # composite exponent >= weighted mean of the parts (Lemma C bound)
    G1, G2 = ln(Bw) - ln(Aw), ln(Bt) - ln(At)
    need(ln(B1) - ln(A1) <= G1 + G2 + PAD, "log(B2 f/A1) <= G1 + G2")
    # classical then T
    A2, B2, r2, m2 = 1, Bt, At ** 3 * rt, mt
    need(below(r2, m2, A2, B2, Fraction(23, 8)), "classical;T: p < 2.875")
    out["CT"] = pdec(A2, B2, r2, m2)
    # iterates
    bank, r, m, trail = Bw, rw, mw, []
    for _ in range(6):
        need(bank >= At, "funded")
        bank = (bank // At) * Bt
        r, m = r * rt, m * mt
        trail.append(pdec(Aw, bank, r, m))
    need(all(b < a for a, b in zip(trail, trail[1:])), "iterates decrease")
    out["iter"] = trail
    # bootstrapping hypothesis for the iterates: beta_0 = B_w >= 2X, X = B_T/(rho-1)
    need(Bw * (Bt - At) >= 2 * Bt * At, "B_w >= 2 B_T/(rho-1)")
    return out


# ---------------------------------------------------------------------------
# Part B: block-level recycling inside one chain

WITNESSES = {
    "S=2^128": (2 ** 128, 9, [(32, 2), (39, 3), (54, 4), (82, 5)], Fraction(29, 10)),
    "S=64": (64, 7, [(3, 1), (3, 1), (4, 1), (5, 1), (7, 1), (11, 1), (18, 1), (16, 2), (27, 2),
                     (33, 3), (60, 3), (86, 4), (110, 6), (160, 8)], Fraction(57, 20)),
}


def block_recycled(S: int, t: int, blocks, d: int = 2):
    """One-stage chain (t, b) -> (1, t) of arity d whose blocks are funded one after
    another from a bank that starts at S (each block's auxiliary is a principal
    sub-block of the bank; its produced factor joins the bank)."""
    s = s_least(d, t)
    r0, b0 = t, s - t + 1
    need(1 < b0 and (d + 2) * 1 <= d * b0 - r0 + 1, "legal step (t, b) -> (1, t)")
    full = [(N, k, mmax(N, d)) for N, k in blocks]
    A, B, r, m, P = chain_counts(None, t, s, [(d, full)])
    bank, slack = S, []
    for N, k, M in full:
        U, V = d ** (2 * N * k), M ** (2 * k)
        need(bank >= U, f"block ({N},{k}) not funded")
        slack.append(bank.bit_length() - U.bit_length())
        bank = (bank // U) * V
    Bp = t ** (2 * P) * bank
    need(Bp * A <= B * S, "B'/S <= B/A (so p' >= p)")
    return {"A": A, "B": B, "r": r, "m": m, "P": P, "s": s, "pair": (r0, b0),
            "Bp": Bp, "S": S, "slack_bits": slack}


def part_b():
    out = {}
    for name, (S, t, blocks, q) in WITNESSES.items():
        w = block_recycled(S, t, blocks)
        need(below(w["r"], w["m"], S, w["Bp"], q), f"{name}: p' < {q}")
        w["p_rec"] = pdec(S, w["Bp"], w["r"], w["m"])
        w["p_src"] = pdec(w["A"], w["B"], w["r"], w["m"])
        w["q"] = q
        need(w["p_rec"] < Decimal("2.97696088"), "beats p_w")
        out[name] = w
    return out


# ---------------------------------------------------------------------------
# Part C: Theorem 2


def part_c():
    out = {}
    M0 = mmax(23, 2)
    need(M0 == 2558607507456, "M0")
    modes = sorted((a, b, 23 - a - b) for a in range(24) for b in range(24 - a)
                   if sector(23, 2, a, b) == M0)
    need(modes == [(5, 12, 6), (6, 11, 6), (6, 12, 5)], "modes of M0")
    cap = M0 ** 12
    need(2 ** 494 < cap < 2 ** 495, "2^494 < M0^12 < 2^495")
    out["modes"] = modes

    # C1 (one kept stage): every (N,d,k,M) with M > (d+1)^N, M^(6k) < cap satisfies
    # (d+1)^(6Nk) (2M-1)^(6k) E >= M^(12k).  Loops over d <= 200, N <= 200 with
    # explicit breaks; the breaks are justified because (d+1)^N < M forces
    # (d+1)^(6Nk) < M^(6k) < cap.
    n1, d_used1, N_used1 = 0, 0, 0
    for d in range(2, 201):
        for N in range(1, 201):
            if (d + 1) ** (6 * N) >= cap:
                break
            big = [M for M in counts(N, d) if M > (d + 1) ** N]
            if big:
                need(N >= 3 and d <= 2 * N, "gain lemma")
            for k in range(1, 400):
                if (d + 1) ** (6 * N * k) >= cap:
                    break
                for M in big:
                    if M ** (6 * k) >= cap:
                        continue
                    E = 1 + 6 * k * (M - 1)
                    need((d + 1) ** (6 * N * k) * (2 * M - 1) ** (6 * k) * E >= M ** (12 * k),
                         f"C1 counterexample N={N} d={d} k={k} M={M}")
                    n1 += 1
                    d_used1, N_used1 = max(d_used1, d), max(N_used1, N)
    # beyond d = 200 even N = 1 is too big?  (d+1)^6 < cap for d <= 2^82; so check the
    # gain lemma instead: M > (d+1)^N > d^N needs d <= 2N and (d+1)^(6N) < cap needs N <= 52.
    # d >= 201: a block with M > d^N needs N >= d/2 > 100 (gain lemma), and then
    # d^(6N) >= 201^606 > cap, so no block of C1 or C2 is missed by the range d <= 200.
    need(201 ** (6 * 101) > cap, "range of d")
    out["C1"] = (n1, d_used1, N_used1)

    # C2 (two or more kept stages): every (N,d,k,M) with M > d^N, M^(6k) < cap has
    # 3 a_d + c(N,d,k,M;3) >= ln(34/25), in exact form with u/v >= lambda_d.
    n2, worst = 0, None
    for d in range(2, 201):
        lam = lam_upper(d)
        u, v = lam.numerator, lam.denominator
        for N in range(1, 201):
            if d ** (6 * N) >= cap:
                break
            big = [M for M in counts(N, d) if M > d ** N]
            if big:
                need(N >= 3 and d <= 2 * N, "gain lemma")
            for k in range(1, 400):
                if d ** (6 * N * k) >= cap:
                    break
                L = (d * v) ** (6 * N * k) * 25 ** (2 * N * k)
                R = 34 ** (2 * N * k) * u ** (6 * N * k)
                for M in big:
                    if M ** (6 * k) >= cap:
                        continue
                    E = 1 + 6 * k * (M - 1)
                    need(L * (2 * M - 1) ** (6 * k) * E >= R * M ** (12 * k),
                         f"C2 counterexample N={N} d={d} k={k} M={M}")
                    n2 += 1
                    val = -3 * lam_dec(d).ln() + (ln(d ** (6 * N * k) * (2 * M - 1) ** (6 * k) * E)
                                                  - ln(M ** (12 * k))) / (2 * N * k)
                    if worst is None or val < worst[0]:
                        worst = (val, N, d, k)
    need(34 ** 2 * 40 ** 3 > 25 ** 2 * 49 ** 3, "2 ln(34/25) + 3 ln(40/49) > 0")
    out["C2"] = (n2, worst)

    # C3: sharpness.  Least t with the one-stage chain (N,k,d) = (23,2,2), M = M0, s = s_least.
    t = 1
    while True:
        s = s_least(2, t)
        A, B, r, m, _ = chain_counts(None, t, s, [(2, [(23, 2, M0)])])
        if B > A and r * A ** 3 < m * B ** 3:
            break
        t += 1
        need(t < 2000, "no sharp terminal")
    need(m == cap and t == 361 and (t, s - t + 1) == (361, 182), "sharp chain")
    out["sharp"] = (t, s, pdec(A, B, r, m))

    # C4: discarding copies.  r MM_A |> m' MM_B with m' < m is again a restriction.
    # For the same block at a large terminal, the least m' with p < 3 is below M0^12.
    res = []
    for t in (1000, 10 ** 4, 10 ** 6):
        s = s_least(2, t)
        A, B, r, m, _ = chain_counts(None, t, s, [(2, [(23, 2, M0)])])
        mp = (r * A ** 3) // (B ** 3) + 1           # least m' with r A^3 < m' B^3
        need(r * A ** 3 < mp * B ** 3 and mp < m, "discarding copies keeps p < 3")
        res.append((t, ln(mp) / LN2))
    out["drop"] = res
    return out


# ---------------------------------------------------------------------------
# Part D: Theorem 1 in decimal arithmetic

P_HI = Decimal("2.976961")
ALPHA = Decimal(40) / 49


def cdec(N, d, k, M, p0):
    E = 1 + 6 * k * (M - 1)
    return p0 * ln(d) - p0 * ln(M) / N + 3 * (ln(2 * M - 1) - ln(M)) / N + ln(E) / (2 * N * k)


def endmin(a: Decimal, C: Decimal, p0: Decimal) -> Decimal:
    t = max(Decimal(1), p0 * C / ((3 - p0) * a))
    return 3 * (a * t + C).ln() - p0 * t.ln()


def part_d():
    out = {}
    cstar = {}
    for d in range(2, 130):
        best = None
        for N in range(1, 65):
            Ms = counts(N, d)
            if Ms[-1] <= d ** N:
                continue
            need(N >= 3 and d <= 2 * N, "gain lemma (D)")
            # d <= 6: minimize over ALL types; d >= 7: largest type (gate Lemma 8)
            cand = [M for M in Ms if M > d ** N] if d <= 6 else [Ms[-1]]
            for k in range(1, 64 // N + 1):
                for M in cand:
                    c = cdec(N, d, k, M, P_HI)
                    if best is None or c < best[0]:
                        best = (c, N, k, M)
        if best is not None:
            cstar[d] = best
    kept = sorted(d for d, b in cstar.items() if b[0] < 0)
    need(kept == [2, 3, 4, 5], f"kept {kept}")
    for d, b in cstar.items():
        if d not in kept:
            pos(b[0], f"c*({d}) >= 0")
    for d in kept:
        need(cstar[d][3] == mmax(cstar[d][1], d), f"minimizer at d={d} is the largest type")
    a = {d: -lam_dec(d).ln() for d in kept}
    eta = {d: 3 * a[d] + cstar[d][0] for d in kept}
    out["cstar"] = {d: cstar[d][:3] for d in kept}
    out["eta"] = eta
    out["min_other"] = min((b[0], d) for d, b in cstar.items() if d not in kept)

    def relaxed(word):
        z = Decimal(1)
        for d in word:
            z /= lam_dec(d)
        return endmin(ALPHA * z, (Decimal(4) / 3 - ALPHA) * z - Decimal(1) / 3, P_HI) \
            + sum(cstar[d][0] for d in word)
    pairs = {(x, y): relaxed((x, y)) for x in kept for y in kept if x <= y}
    for w, v in pairs.items():
        if w != (2, 2):
            pos(v, f"pair {w}")
    neg(pairs[(2, 2)], "(2,2) relaxed is open")
    forms = [(Fraction(5, 2), Fraction(3, 2)), (Fraction(11, 4), Fraction(3, 4)),
             (Fraction(3), Fraction(1, 2)), (Fraction(4), Fraction(0))]
    ex22 = min(endmin(Decimal(k.numerator) / k.denominator, Decimal(c.numerator) / c.denominator, P_HI)
               for k, c in forms) + 2 * cstar[2][0]
    pos(ex22, "(2,2) exact forms")
    three = min(pairs.values()) + min(eta.values())
    pos(three, "three or more")
    out["pairs"], out["ex22"], out["three"] = pairs, ex22, three

    # one kept stage: one-stage data (N,k,d,t), Nk <= 64, d in kept, t <= 700; tail past 700
    near = []
    for d in kept:
        aa, CC = Decimal(d + 1) / d, Decimal(1) / d
        tstar = P_HI * CC / ((3 - P_HI) * aa)
        need(tstar < 700, "tail start")
        for N in range(3, 65):
            M = mmax(N, d)
            if M <= d ** N:
                continue
            for k in range(1, 64 // N + 1):
                c = cdec(N, d, k, M, P_HI)
                pos(3 * (aa * 700 + CC).ln() - P_HI * Decimal(700).ln() + c, f"tail {N},{k},{d}")
                if endmin(aa, CC, P_HI) + c > PAD:
                    continue
                for t in range(1, 701):
                    g = 3 * ln(s_least(d, t)) - P_HI * ln(t) + c
                    if (N, k, d, t) == (32, 2, 2, 43):
                        neg(g, "W below p_hi")
                        continue
                    pos(g, f"one-stage datum {(N, k, d, t)}")
                    near.append((g, (N, k, d, t)))
    near.sort()
    out["near"] = near[:3]
    return out


# ---------------------------------------------------------------------------
# Part E: geometry with free crops


def part_e(limit=10, depth=4, arities=(2, 3, 4, 5, 6, 7)):
    """Dynamic programme over (unordered pair, word of arities): the least source span
    s reaching the pair through legal steps with free crops of both new entries.  All
    three bounds are of the form s >= g(t), so the least s is the binding case."""
    forms = [(Fraction(5, 2), Fraction(3, 2)), (Fraction(11, 4), Fraction(3, 4)),
             (Fraction(3), Fraction(1, 2)), (Fraction(4), Fraction(0))]
    zlo = {}

    def z_of(word):
        if word not in zlo:
            z = Fraction(1)
            for d in word:
                z /= lam_upper(d)          # lambda upper bound gives a lower bound on z
            zlo[word] = z
        return zlo[word]
    layer = {}
    for r0 in range(1, limit + 1):
        for b0 in range(r0, limit + 1):
            key = ((r0, b0), ())
            layer[key] = min(layer.get(key, 10 ** 9), r0 + b0 - 1)
    stats = {"states": 0, "endpoints": 0, "two2": 0}
    for _ in range(depth):
        nxt = {}
        for (pair, word), s in layer.items():
            x, y = pair
            for r, b in ((x, y), (y, x)):
                for d in arities:
                    for c in range(1, b):
                        if (d + 2) * c > d * b - r + 1:
                            break
                        for c2 in range(1, c + 1):
                            for r2 in range(1, r + 1):
                                key = (tuple(sorted((c2, r2))), word + (d,))
                                if s < nxt.get(key, 10 ** 9):
                                    nxt[key] = s
        for (pair, word), s in nxt.items():
            stats["states"] += 1
            z = z_of(word)
            for t in range(1, max(pair) + 1):
                stats["endpoints"] += 1
                need(t <= s, "t <= s")
                need(s + Fraction(1, 3) >= z * (Fraction(40, 49) * t + Fraction(4, 3) - Fraction(40, 49)),
                     f"potential bound {word} s={s} t={t}")
                for d in set(word):
                    need(d * s >= (d + 1) * t + 1, f"extended one-stage bound {word} s={s} t={t}")
                if word.count(2) >= 2:
                    stats["two2"] += 1
                    need(any(s >= k * t + c for k, c in forms), f"(2,2) forms {word} s={s} t={t}")
        layer = nxt
    return stats


# ---------------------------------------------------------------------------


def main() -> int:
    sys.set_int_max_str_digits(0)
    t0 = time.time()
    a = part_a()
    print("A. Composite witnesses (exact thresholds; decimal values)")
    print(f"   p_w = {a['pw']:.15f}   p_T = {a['pt']:.12f}")
    print(f"   W then T: p = {a['WT']:.12f} (exact: 2.866 <= p < 2.87), B has {a['WT_digits']} digits")
    print(f"   classical then T: p = {a['CT']:.12f} (exact: p < 2.875)")
    print("   iterates: " + ", ".join(f"{float(x):.6f}" for x in a["iter"]))

    b = part_b()
    print("B. Block-level recycling inside ONE one-stage chain (d = 2), exact bank and thresholds")
    for name, w in b.items():
        print(f"   {name}: source pair {w['pair']} -> (1,{w['pair'][0]}), s = {w['s']}, P = {w['P']},"
              f" {len(WITNESSES[name][2])} blocks; funding slack (bits) {w['slack_bits']}")
        print(f"      recycled: A' = {name[2:]}, p' = {w['p_rec']:.9f} (exact: p' < {w['q']});"
              f" source supply: A = 2^{2 * w['P']}, p = {w['p_src']:.9f}")

    c = part_c()
    print("C. Theorem 2")
    print(f"   modes of M0: {c['modes']}")
    print(f"   one kept stage: {c['C1'][0]} blocks checked (max d = {c['C1'][1]}, max N = {c['C1'][2]})")
    n2, worst = c["C2"]
    print(f"   two or more kept stages: {n2} blocks checked; least 3a_d + c = {worst[0]:.6f} at (N,d,k) = {worst[1:]};"
          f" ln(34/25) = {Decimal(34 / 25).ln():.6f}")
    t, s, p = c["sharp"]
    print(f"   sharp: t = {t}, s = {s}, p = {p:.12f}")
    print("   discarding copies of the (23,2) block at terminal t: least subcubic m' = 2^" +
          ", 2^".join(f"{float(x):.4f} (t={t})" for t, x in c["drop"])
          + f"  vs M0^12 = 2^{float(12 * ln(2558607507456) / LN2):.4f}")

    d = part_d()
    print("D. Theorem 1 (decimal)")
    for dd, (cc, N, k) in d["cstar"].items():
        print(f"   d={dd}: c* = {cc:.9f} at (N,k)=({N},{k}); eta = {d['eta'][dd]:.6f}")
    print(f"   least c* over d = 6..129: {d['min_other'][0]:.6f} at d={d['min_other'][1]}")
    print("   pairs: " + ", ".join(f"{w}: {float(v):+.6f}" for w, v in sorted(d["pairs"].items())))
    print(f"   (2,2) forms: {d['ex22']:.6f}; three or more: {d['three']:.6f}")
    print("   closest one-stage data: " + ", ".join(f"{float(g):.3e} at {x}" for g, x in d["near"]))

    e = part_e()
    print(f"E. Geometry with free crops: {e['states']} least-span states, {e['endpoints']} endpoints"
          f" (depth <= 4, source entries <= 10, arities 2..7), {e['two2']} with two arity-2 stages")
    print(f"all checks passed in {time.time() - t0:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
