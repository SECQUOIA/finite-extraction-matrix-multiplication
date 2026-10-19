"""Adversarial re-check of docs/shifted-chains-check-certificates.md.

Independent of experiments/shifted_chain_certificates.py except in part 6,
which feeds newly selected points to the canonical `certificate` function
as a cross-check.  Standard library only.

1. Chains: legality is tested in the round-8 form (h = b-c >= 1, quotient
   width b+(d-1)h >= 3c+r-1), not in the derived form (L).  Source pairs
   are built backward, and every step checks that b'-1 is illegal.
2. Modes: a complete search over the box n*w_i/W - 1 <= a_i <= n*w_i/W + 2,
   which contains every maximizer (proof in the adversarial review).
3. Logarithms: Python's decimal ln, which is correctly rounded, widened by
   two ulps and then combined with directed-rounding interval arithmetic
   (ROUND_FLOOR / ROUND_CEILING contexts).  This is a second rigorous
   method, different from the canonical artanh enclosure.
4. Exact integer certificates without logarithms for the smaller points:
   Phi < q  <=>  (2 r_*)^v A^u < m_*^v B^u  for q = u/v, with q a
   simple rational between the certified bound and the target.  The
   least-power claim is checked the same way at k-1.
5. Arithmetic in the note: 3 log 40/log 54, and the digit thresholds
   from v5 Corollary 11.2(a).
6. A fair comparison with v5 Table 2: points below v5's computed Phi
   (2.8406393 and 2.6728401, floating point in v5), not only below v5's
   relaxed bound Phi-bar.  The screen's selections are compared with the
   report's comparisons_with_v5.

Parts 1-3 compare every point that the report (schema
shifted-chain-certificates-v2) contains with the report: source pair,
sector counts (SHA-256), Phi, p and digit counts.

Run from the repository root:
    python -I experiments/shifted_chains_skeptic_certificates.py            # parts 1-5, ~2 min
    python -I experiments/shifted_chains_skeptic_certificates.py --screen   # adds part 6, a few s more
Prints a report; writes no file.
"""

from __future__ import annotations

from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "results" / "shifted-chain-certificates.json"
sys.set_int_max_str_digits(0)

PREC = 90
NEAR = Context(prec=PREC, rounding=ROUND_HALF_EVEN)
DOWN = Context(prec=PREC, rounding=ROUND_FLOOR)
UP = Context(prec=PREC, rounding=ROUND_CEILING)


# ---------------------------------------------------------------------------
# 1. Chains in the round-8 parametrization


def legal(r: int, b: int, d: int, c: int) -> bool:
    if d < 2 or r < 1 or c < 1:
        return False
    h = b - c
    if h < 1:
        return False
    quotient = b + (d - 1) * h          # length of the image of (1)
    return quotient >= 3 * c + r - 1    # crop to C(r, 3c+r-1), condition (3)


def parent(child: tuple[int, int], d: int) -> tuple[int, int]:
    """Least b' such that the level (b, b', d, r) is legal; child = (r, b)."""
    r, b = child
    bp = ((d + 2) * r + b - 1 + d - 1) // d
    assert legal(b, bp, d, r) and not legal(b, bp - 1, d, r)
    return b, bp


def build(terminal, arities):
    pair = tuple(terminal)
    levels = []
    for d in reversed(arities):
        p = parent(pair, d)
        levels.append((p[0], p[1], d, pair[0]))
        pair = p
    levels.reverse()
    # forward replay: the next parent is (c, r), largest legal child each time
    r, b = levels[0][:2]
    for (rr, bb, d, c) in levels:
        assert (rr, bb) == (r, b)
        assert legal(r, b, d, c) and not legal(r, b, d, c + 1)
        r, b = c, r
    assert (r, b) == tuple(terminal)
    return levels


def ramp(side: int) -> list[int]:
    out = []
    for j in range(side - 1, 0, -1):
        out += [3 * j, 3 * j - 1]
    return out


# ---------------------------------------------------------------------------
# 2. Modes by complete box search


def H_of(n, d, K, O):
    return comb(n, K) * comb(n - K, O) * (d - 1) ** K * 2 ** O


def mode_H(n: int, d: int) -> tuple[int, tuple[int, int, int]]:
    w = (d - 1, 2, 1)
    W = d + 2
    lo = [max(0, -((W - n * wi) // W)) for wi in w]       # ceil((n wi - W)/W)
    hi = [(n * wi + 2 * W) // W for wi in w]
    best = (-1, None)
    for K in range(lo[0], hi[0] + 1):
        for O in range(lo[1], hi[1] + 1):
            M = n - K - O
            if M < lo[2] or M > hi[2]:
                continue
            h = H_of(n, d, K, O)
            if h > best[0]:
                best = (h, (K, O, M))
    return best


# ---------------------------------------------------------------------------
# 3. Rigorous decimal intervals


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        assert lo <= hi
        self.lo, self.hi = lo, hi

    def __add__(self, o):
        return I(DOWN.add(self.lo, o.lo), UP.add(self.hi, o.hi))

    def __sub__(self, o):
        return I(DOWN.subtract(self.lo, o.hi), UP.subtract(self.hi, o.lo))

    def scale(self, n: int):
        assert n >= 0
        return I(DOWN.multiply(self.lo, Decimal(n)), UP.multiply(self.hi, Decimal(n)))

    def div(self, o):
        assert self.lo >= 0 and o.lo > 0
        return I(DOWN.divide(self.lo, o.hi), UP.divide(self.hi, o.lo))


ZERO = I(Decimal(0), Decimal(0))


def _ln_small(x: int) -> I:
    y = NEAR.ln(Decimal(x))
    lo, hi = y, y
    for _ in range(2):
        lo, hi = NEAR.next_minus(lo), NEAR.next_plus(hi)
    return I(lo, hi)


LN2 = _ln_small(2)
LN10 = _ln_small(10)
_cache: dict[int, I] = {}


def ln(x: int) -> I:
    if x == 1:
        return ZERO
    if x in _cache:
        return _cache[x]
    shift = max(0, x.bit_length() - 280)
    if shift == 0:
        out = _ln_small(x)
    else:
        m = x >> shift
        out = LN2.scale(shift) + I(_ln_small(m).lo, _ln_small(m + 1).hi)
    _cache[x] = out
    return out


def certificate(terminal, arities, n, k, target: Fraction):
    levels = build(terminal, arities)
    s = levels[0][0] + levels[0][1] - 1
    t = terminal[1]
    mult: dict[int, int] = {}
    for _, _, d, _ in levels:
        mult[d] = mult.get(d, 0) + 1
    modes = {d: mode_H(n, d) for d in mult}

    def phi(kk):
        num = ln(s).scale(6 * n * kk)
        gain = ln(t).scale(2 * n * kk)
        logA = ZERO
        logB = ln(t).scale(2 * n * kk)
        for d, c in mult.items():
            h = modes[d][0]
            e = 1 + 6 * kk * (h - 1)
            num = num + (ln(2 * h - 1) - ln(h)).scale(6 * kk * c) + ln(e).scale(c)
            gain = gain + ln(h).scale(2 * kk * c) - ln(d).scale(2 * n * kk * c)
            logA = logA + ln(d).scale(2 * n * kk * c)
            logB = logB + ln(h).scale(2 * kk * c)
        return (num + LN2).div(gain), num.div(gain), logA, logB

    Phi, p, logA, logB = phi(k)
    prev = phi(k - 1)[0] if k > 1 else None

    def digits(L):
        x = L.div(LN10)
        a, b = int(x.lo), int(x.hi)
        assert a == b, "digit count not decided"
        return a + 1

    return {
        "levels": levels, "s": s, "t": t, "mult": mult, "modes": modes,
        "Phi": Phi, "p": p, "Phi_prev": prev,
        "digits_A": digits(logA), "digits_B": digits(logB),
        "passes": Phi.hi < target,
        "least_k": prev is None or prev.lo >= target,
    }


# ---------------------------------------------------------------------------
# 4. Exact integer certificates


def simplest_between(a: Fraction, b: Fraction) -> Fraction:
    """A fraction with small denominator in the open interval (a, b), 0 <= a < b."""
    assert 0 <= a < b
    fl = a.numerator // a.denominator
    if fl + 1 < b:
        return Fraction(fl + 1)
    if a == fl:
        return fl + Fraction(1, int(1 / (b - fl)) + 1)
    return fl + 1 / simplest_between(1 / (b - fl), 1 / (a - fl))


def exact_counts(cert, kk):
    n = cert["n"]
    s, t = cert["s"], cert["t"]
    A, B = 1, t ** (2 * n * kk)
    r, m = s ** (6 * n * kk), 1
    for d, c in cert["mult"].items():
        h = cert["modes"][d][0]
        e = 1 + 6 * kk * (h - 1)
        A *= d ** (2 * n * kk * c)
        B *= h ** (2 * kk * c)
        r *= ((2 * h - 1) ** (6 * kk) * e) ** c
        m *= h ** (6 * kk * c)
    return A, B, r, m


def exact_phi_below(cert, kk, q: Fraction) -> bool:
    A, B, r, m = exact_counts(cert, kk)
    u, v = q.numerator, q.denominator
    return (2 * r) ** v * A ** u < m ** v * B ** u


def to_frac(x: Decimal) -> Fraction:
    return Fraction(x)


def sha256_int(m: int) -> str:
    return hashlib.sha256(m.to_bytes((m.bit_length() + 7) // 8, "big")).hexdigest()


# ---------------------------------------------------------------------------
# 6. Fair comparison screen (float, selection only)


def screen(target: float, t_max=64, levels_max=60, n_max=1500):
    from math import lgamma, log, log1p, exp
    logH = {}
    for n in range(1, n_max + 1):
        h, (K, O, M) = mode_H(n, 2)
        logH[n] = lgamma(n + 1) - lgamma(K + 1) - lgamma(O + 1) - lgamma(M + 1) + O * log(2)
    best = None
    for t in range(1, t_max + 1):
        pair = (1, t)
        for L in range(1, levels_max + 1):
            pair = parent(pair, 2)
            s = pair[0] + pair[1] - 1
            for n in range(1, n_max + 1):
                if best is not None and 2 * n * L * log(2) / log(10) >= best[0]:
                    break
                h = logH[n]
                gain = n * log(t) + L * (h - n * log(2))
                if gain <= 0:
                    continue
                inv = exp(-h)
                base = 3 * n * log(s) + 3 * L * log(2 - inv)
                slack = target * gain - base
                if slack <= 0:
                    continue

                def ok(k):
                    interp = h + log(6 * k) + log1p(-(1 - 1 / (6 * k)) * inv)
                    return (L * interp + log(2)) / (2 * k) < slack

                hi = 1
                while not ok(hi):
                    hi *= 2
                    if hi > 1 << 22:
                        break
                if not ok(hi):
                    continue
                lo = hi // 2 + 1 if hi > 1 else 1
                while lo < hi:
                    mid = (lo + hi) // 2
                    if ok(mid):
                        hi = mid
                    else:
                        lo = mid + 1
                digits = 2 * n * hi * L * log(2) / log(10)
                if best is None or digits < best[0] - 1e-9:
                    best = (digits, t, L, n, hi)
    return best


# ---------------------------------------------------------------------------


def main():
    report = json.loads(REPORT.read_text())
    saved = {w["name"]: w for w in report["witnesses"] + report["comparisons_with_v5"]}
    specs = [
        ("below-3", (1, 128), [2], 24, 2, Fraction(3)),
        ("below-2.77429", (1, 5), [2], 215, 10, Fraction(277429, 100000)),
        ("below-2.7", (1, 3), [2] * 5, 147, 8, Fraction(27, 10)),
        ("below-2.5", (1, 3), [2] * 15, 264, 14, Fraction(5, 2)),
        ("below-2.3", (1, 1), [2] * 121 + ramp(3), 1999, 80, Fraction(23, 10)),
        ("below-2.26", (1, 1), [4] * 1244 + ramp(11), 28336, 1118, Fraction(113, 50)),
        ("below-2.84063", (1, 5), [2], 93, 5, Fraction(284063, 10 ** 5)),
        ("below-2.67283", (1, 3), [2] * 7, 138, 8, Fraction(267283, 10 ** 5)),
        ("below-v5-a8-bound", (1, 7), [2], 81, 5, Fraction(2848599165, 10 ** 9)),
        ("below-v5-a12-bound", (1, 3), [2] * 7, 153, 7, Fraction(2675820359, 10 ** 9)),
        ("round-10 point below 2.5", (1, 3), [2] * 16, 248, 14, Fraction(5, 2)),
    ]
    all_ok = True
    print("1-3. independent model + decimal directed-rounding certificates")
    certs = {}
    for name, term, ar, n, k, target in specs:
        t0 = time.time()
        c = certificate(term, ar, n, k, target)
        c["n"], c["k"], c["target"] = n, k, target
        certs[name] = c
        line = (f"  {name:<30} Phi in [{str(c['Phi'].lo)[:16]}, {str(c['Phi'].hi)[:16]}]  "
                f"A {c['digits_A']:,}  B {c['digits_B']:,}  pass={c['passes']} least_k={c['least_k']}")
        if name in saved:
            w = saved[name]
            agree = (c["digits_A"] == w["decimal_digits_A"] and c["digits_B"] == w["decimal_digits_B"]
                     and all(Fraction(w[key]["lower"]) <= to_frac(c[key].lo)
                             and to_frac(c[key].hi) <= Fraction(w[key]["upper"]) for key in ("Phi", "p"))
                     and list(c["levels"][0][:2]) == w["source_pair"]
                     and w["stages_J"] == len(c["levels"]) and w["N_per_sign"] == n and w["k"] == k
                     and Fraction(w["target"]) == target
                     and sorted(c["mult"]) == [x["arity"] for x in w["types"]]
                     and all(x["stages"] == c["mult"][x["arity"]]
                             and sha256_int(c["modes"][x["arity"]][0]) == x["M_sha256_big_endian"]
                             for x in w["types"]))
            line += "  matches report" if agree else "  MISMATCH with report"
            all_ok &= agree
        all_ok &= c["passes"] and c["least_k"]
        print(line + f"  ({time.time() - t0:.1f}s)")
    missing = sorted(set(saved) - set(certs))
    if missing:
        print("  report points not rechecked:", missing)
        all_ok = False
    big = max(certs["below-2.26"]["modes"].values())[0]
    print(f"  largest sector count in the 2.26 witness: {big.bit_length()} bits; "
          f"E has {(1 + 6 * 1118 * (big - 1)).bit_length()} bits")

    print("4. exact integer certificates (no logarithms)")
    for name in ("below-3", "below-v5-a8-bound", "below-2.84063", "below-2.77429", "below-2.7",
                 "below-v5-a12-bound", "below-2.67283"):
        c = certs[name]
        t0 = time.time()
        q = simplest_between(to_frac(c["Phi"].hi), c["target"])
        ok_pass = exact_phi_below(c, c["k"], q)
        # least k: Phi(k-1) >= q2 >= target
        prev_lo = to_frac(c["Phi_prev"].lo)
        q2 = simplest_between(c["target"], prev_lo) if prev_lo > c["target"] else c["target"]
        ok_least = not exact_phi_below(c, c["k"] - 1, q2)
        all_ok &= ok_pass and ok_least
        print(f"  {name:<20} Phi(k) < {q} (exact): {ok_pass};  Phi(k-1) >= {q2} (exact): {ok_least}"
              f"  ({time.time() - t0:.1f}s)")

    print("5. arithmetic quoted in the note")
    r40 = NEAR.divide(NEAR.multiply(Decimal(3), NEAR.ln(Decimal(40))), NEAR.ln(Decimal(54)))
    print(f"  3 log 40 / log 54 = {str(r40)[:16]}  (> 2.77429: {r40 > Decimal('2.77429')})")
    c65 = NEAR.ln(Decimal("1.2"))
    for p in ("2.26", "2.3"):
        eps = Decimal(p) - Decimal("2.25")
        # p > 9/4 + 9 log(6/5) / (2 log(2 log A))  =>  log(2 log A) > 9 log(6/5)/(2 eps)
        x = NEAR.divide(NEAR.multiply(Decimal(9), c65), NEAR.multiply(Decimal(2), eps))
        logA = NEAR.divide(NEAR.exp(x), Decimal(2))
        print(f"  v5 Cor 11.2(a), p<{p}: log A > {logA:.4E}, digits of A > {NEAR.divide(logA, NEAR.ln(Decimal(10))):.4E}")

    if "--screen" in sys.argv:
        print("6. fair comparison: shifted-chain points below v5's computed Phi (float screen, exact certificate)")
        sys.path.insert(0, str(ROOT / "experiments"))
        import shifted_chain_certificates as sc  # noqa: E402
        for label, target_text in (("a=8, v5 Phi 2.8406393", "2.84063"), ("a=12, v5 Phi 2.6728401", "2.67283")):
            t0 = time.time()
            best = screen(float(target_text))
            digits, t, L, n, k = best
            target = Fraction(target_text)
            mine = certificate((1, t), [2] * L, n, k, target)
            canon = sc.certificate({"name": label, "target": target_text, "t": t,
                                    "runs": [[2, L]], "ramp_R": None, "N": n, "k": k})
            w = saved[f"below-{target_text}"]
            in_report = (w["terminal_pair"] == [1, t] and w["arity_runs_source_first"] == [[2, L]]
                         and w["N_per_sign"] == n and w["k"] == k and w["Phi"] == canon["Phi"])
            print(f"  {label}: target {target_text}: terminal (1,{t}), {L} levels of arity 2, n={n}, k={k}: "
                  f"Phi<{canon['Phi']['upper']} (mine {str(mine['Phi'].hi)[:14]}), "
                  f"A 2^{2 * n * k * L}: {canon['decimal_digits_A']:,} digits (mine {mine['digits_A']:,}), "
                  f"B {canon['decimal_digits_B']:,} digits; least k {mine['least_k']}; "
                  f"{'same as report' if in_report else 'DIFFERS from report'}  ({time.time() - t0:.0f}s)")
            all_ok &= mine["passes"] and mine["least_k"] and canon["Phi_below_target"] and in_report

    print("ALL CHECKS PASSED" if all_ok else "SOME CHECK FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
