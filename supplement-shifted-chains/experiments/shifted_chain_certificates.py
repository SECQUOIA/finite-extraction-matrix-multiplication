"""Finite certificates for chains of shifted-chain stages.

Supplement to the paper "A singly exponential construction of matrix
multiplication algorithms with exponent approaching 9/4".  The cost model is
derived in docs/shifted-chains-check-certificates.md (with its adversarial
review); "v5" is the preceding paper, cited with its own numbering.

Cost model, in the paper's notation.  A stage of arity d >= 2 takes the pair
(r, b) to the pair (c, r), where

    1 <= c < b,   (d + 2) c <= d b - r + 1.

A chain has stages i = 1, ..., J from the source pair (r_1, b_1) to the
terminal pair (1, t).  Every stage uses N factors of each cyclic sign, one type
(nK_i, nO_i, nmid_i) with nK_i + nO_i + nmid_i = N in all six orientations,
and the common exactification power k.  Put

    M_i = N! / (nK_i! nO_i! nmid_i!) * (d_i - 1)^nK_i * 2^nO_i,
    E_i = 1 + 6 k (M_i - 1),        s = r_1 + b_1 - 1.

The relative scheme r_* MM_A |> m_* MM_B over Q has

    A   = prod_i d_i^(2Nk),          B   = t^(2Nk) prod_i M_i^(2k),
    r_* = s^(6Nk) prod_i (2M_i - 1)^(6k) E_i,
    m_* = prod_i M_i^(6k).

The pooled exponent is p = log(r_*/m_*) / log(B/A) (v5 Lemma 2.4).  The
certified quantity is v5's fixed-batch bound (10.1),

    Phi = log(2 r_*/m_*) / log(B/A) = p + log 2 / log(B/A).

The term log 2 pays for the ceiling ceil(r_*/m_*) of the recursion that
batches the products of each batch only among themselves (v5 Section 10.1).
The pooled recursion of v5 Lemma 2.4 also rounds up, to ceil(nu_l/m_*)
batches (v5 (2.9)), but these ceilings do not enter its exponent p.  So a
certificate Phi < q gives exponent below q with or without pooling.

For a fixed chain, N and types, Phi strictly decreases in k and A increases
in k.  Each certificate also proves Phi >= target at k - 1, so k is the least
power, and A the least source side, for that chain, N and types.  The
witnesses are selected points, not minimal ones.

All logarithms are enclosed by rational intervals with outward rounding; no
floating-point number enters a certificate.  The large integers A, B, r_*,
m_* are never formed.  Their logarithms are sums of logarithms of moderate
integers (d_i, M_i, 2M_i - 1, E_i, s, t) with exact integer multipliers.
Every check raises an exception when it fails (CertificateError for a failed
certificate check, ValueError for malformed input); there are no assert
statements, so `python -O` checks the same.

Usage, from the repository root (Python 3.11+, standard library only, about
0.4 s, deterministic output):

    python -I experiments/shifted_chain_certificates.py          # write report
    python -I experiments/shifted_chain_certificates.py --check  # recompute, compare

The first form rewrites results/shifted-chain-certificates.json.  The second
recomputes every certificate and compares the result with the saved report
byte for byte; it exits with status 1 on a mismatch.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import comb
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "shifted-chain-certificates.json"

# Logarithm enclosure parameters.
MANTISSA_BITS = 192   # bits of an integer kept before its logarithm is taken
SERIES_TERMS = 110    # terms of the artanh series; the tail is bounded explicitly
DYADIC_BITS = 320     # every logarithm is rounded outward to a multiple of 2^-320
DECIMALS = 12         # printed exponent bounds, rounded outward
SIGNIFICANT = 6       # significant digits of printed small bounds, rounded outward


class CertificateError(Exception):
    """A certificate or one of its consistency checks failed."""


# ---------------------------------------------------------------------------
# Rational intervals and certified logarithms


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self):
        if self.lo > self.hi:
            raise ArithmeticError("empty interval")

    @staticmethod
    def exact(value) -> "Interval":
        value = Fraction(value)
        return Interval(value, value)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other: "Interval") -> "Interval":
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def times(self, factor) -> "Interval":
        """Multiply by an exact rational."""
        factor = Fraction(factor)
        if factor < 0:
            return Interval(self.hi * factor, self.lo * factor)
        return Interval(self.lo * factor, self.hi * factor)

    def over(self, other: "Interval") -> "Interval":
        """Quotient of a nonnegative interval by a positive interval."""
        if self.lo < 0 or other.lo <= 0:
            raise ArithmeticError("need a nonnegative numerator and a positive denominator")
        return Interval(self.lo / other.hi, self.hi / other.lo)

    def decimal_strings(self, decimals: int = DECIMALS) -> dict[str, str]:
        """Fixed-point decimals, the lower end rounded down and the upper end up."""
        scale = 10 ** decimals
        return {"lower": _fixed((self.lo * scale).__floor__(), decimals),
                "upper": _fixed((self.hi * scale).__ceil__(), decimals)}

    def scientific_strings(self, digits: int = SIGNIFICANT) -> dict[str, str]:
        """Scientific notation for a positive interval, rounded outward."""
        if self.lo <= 0:
            raise ArithmeticError("need a positive interval")
        return {"lower": _scientific(self.lo, digits, up=False),
                "upper": _scientific(self.hi, digits, up=True)}


def _fixed(value: int, decimals: int) -> str:
    sign = "-" if value < 0 else ""
    digits = str(abs(value)).rjust(decimals + 1, "0")
    return f"{sign}{digits[:-decimals]}.{digits[-decimals:]}"


def _scientific(value: Fraction, digits: int, up: bool) -> str:
    exponent = len(str(value.numerator)) - len(str(value.denominator))
    while Fraction(10) ** exponent > value:
        exponent -= 1
    while Fraction(10) ** (exponent + 1) <= value:
        exponent += 1
    scaled = value * Fraction(10) ** (digits - 1 - exponent)
    mantissa = scaled.__ceil__() if up else scaled.__floor__()
    if mantissa == 10 ** digits:  # rounding up reached the next power of 10
        mantissa, exponent = 10 ** (digits - 1), exponent + 1
    text = str(mantissa)
    return f"{text[0]}.{text[1:]}e{exponent}"


def _log_ratio_bounds(numerator: int, denominator: int) -> tuple[int, int]:
    """Integers L <= U with L/2^W <= log(x) <= U/2^W for x = num/den in [1, 2].

    Uses log x = 2 artanh(rho), rho = (x-1)/(x+1) in [0, 1/3], with directed
    integer rounding of every power and term, and the tail bound
    sum_{j>=J} rho^(2j+1)/(2j+1) <= rho^(2J+1) / ((2J+1)(1-rho^2)).
    """
    if not denominator <= numerator <= 2 * denominator:
        raise ValueError("ratio must lie in [1, 2]")
    p, q = numerator - denominator, numerator + denominator
    if p == 0:
        return 0, 0
    scale = 1 << DYADIC_BITS
    p2, q2 = p * p, q * q
    low_power = (p * scale) // q          # <= rho * 2^W
    high_power = -((-p * scale) // q)     # >= rho * 2^W
    low_sum = high_sum = 0
    for j in range(SERIES_TERMS):
        low_sum += low_power // (2 * j + 1)
        high_sum += -((-high_power) // (2 * j + 1))
        low_power = (low_power * p2) // q2
        high_power = -((-high_power * p2) // q2)
    tail_denominator = (2 * SERIES_TERMS + 1) * (q2 - p2)
    tail = -((-high_power * q2) // tail_denominator)
    return 2 * low_sum, 2 * (high_sum + tail)


@lru_cache(maxsize=None)
def log_integer(value: int) -> Interval:
    """Certified enclosure of the natural logarithm of a positive integer."""
    if not isinstance(value, int) or value < 1:
        raise ValueError("positive integer required")
    if value == 1:
        return Interval.exact(0)
    exponent = value.bit_length() - 1
    log2_low, log2_high = _log_ratio_bounds(2, 1)
    if exponent <= MANTISSA_BITS:
        low = high = (value, 1 << exponent)
    else:
        top = value >> (exponent - MANTISSA_BITS)
        low, high = (top, 1 << MANTISSA_BITS), (top + 1, 1 << MANTISSA_BITS)
    lower = exponent * log2_low + _log_ratio_bounds(*low)[0]
    upper = exponent * log2_high + _log_ratio_bounds(*high)[1]
    scale = 1 << DYADIC_BITS
    return Interval(Fraction(lower, scale), Fraction(upper, scale))


def decimal_digits(factors) -> int:
    """Number of decimal digits of X = prod base^exponent (positive integers).

    If the enclosure of log10 X straddles an integer m, decide X >= 10^m by
    writing X/10^m = 2^(alpha-m) 5^(beta-m) Q with Q coprime to 10.
    """
    log_x = Interval.exact(0)
    for base, exponent in factors:
        log_x += log_integer(base).times(exponent)
    log10 = log_x.over(log_integer(10))
    low, high = log10.lo.__floor__(), log10.hi.__floor__()
    if low == high:
        return int(low) + 1
    if high != low + 1:
        raise CertificateError("logarithm enclosure too wide")
    m = int(high)
    alpha = beta = 0
    rest = Interval.exact(0)
    for base, exponent in factors:
        while base % 2 == 0:
            base //= 2
            alpha += exponent
        while base % 5 == 0:
            base //= 5
            beta += exponent
        rest += log_integer(base).times(exponent)
    if alpha == beta == m and rest.hi == 0:
        return m + 1  # X = 10^m exactly
    difference = log_integer(2).times(alpha - m) + log_integer(5).times(beta - m) + rest
    if difference.lo >= 0:
        return m + 1
    if difference.hi < 0:
        return m
    raise CertificateError("cannot decide the digit count")


# ---------------------------------------------------------------------------
# Chains of stages


def check_stage(r: int, b: int, d: int, c: int) -> int:
    """Check that (r, b) -> (c, r) is a stage of arity d; return its slack."""
    if d < 2 or min(r, b, c) < 1:
        raise CertificateError("a stage needs d >= 2 and positive dimensions")
    if not c < b:
        raise CertificateError("a stage needs c < b")
    slack = d * b - r + 1 - (d + 2) * c
    if slack < 0:
        raise CertificateError("quotient length d*b-(d-1)*c is shorter than 3c+r-1")
    return slack


def smallest_parent(child: tuple[int, int], d: int) -> tuple[int, int]:
    """Smallest parent (b, b') of an arity-d stage with child pair (r, b)."""
    r, b = child
    return b, -(-((d + 2) * r + b - 1) // d)


def ramp_arities(side: int) -> list[int]:
    """Forward arities 3j, 3j-1 (j = side-1, ..., 1) of the ramp from (side, side) to (1, 1)."""
    return [d for j in range(side - 1, 0, -1) for d in (3 * j, 3 * j - 1)]


def backward_chain(terminal: tuple[int, int], arities: list[int]) -> list[tuple[int, int, int, int]]:
    """Stages (r, b, d, c), source first, built from the terminal by smallest parents."""
    pair = tuple(terminal)
    stages = []
    for d in reversed(arities):
        parent = smallest_parent(pair, d)
        slack = check_stage(*parent, d, pair[0])
        if slack >= d:
            raise CertificateError("smallest parent with slack >= d")
        stages.append((parent[0], parent[1], d, pair[0]))
        pair = parent
    stages.reverse()
    return stages


def forward_floor_chain(source: tuple[int, int], arities: list[int]) -> list[tuple[int, int, int, int]]:
    """Stages (r, b, d, c) with the largest legal child c at every stage."""
    r, b = source
    stages = []
    for d in arities:
        c = (d * b - r + 1) // (d + 2)
        check_stage(r, b, d, c)
        stages.append((r, b, d, c))
        r, b = c, r
    return stages


def chain_ends(stages) -> tuple[tuple[int, int], tuple[int, int]]:
    """Check consecutive stages and return (source pair, terminal pair)."""
    for (r, b, d, c), following in zip(stages, stages[1:] + [None]):
        check_stage(r, b, d, c)
        if following is not None and (following[0], following[1]) != (c, r):
            raise CertificateError("consecutive stages do not match")
    last = stages[-1]
    return (stages[0][0], stages[0][1]), (last[3], last[0])


# ---------------------------------------------------------------------------
# Types


def sector_count(d: int, kernel: int, outer: int, middle: int) -> int:
    N = kernel + outer + middle
    return comb(N, kernel) * comb(N - kernel, outer) * (d - 1) ** kernel * 2 ** outer


def mode(N: int, d: int) -> tuple[int, int, int]:
    """A type (nK, nO, nmid) maximizing the sector count, with a proof check.

    Start below every mode, at max(0, floor(N w_i/(d+2)) - 1) for the weights
    w = (d-1, 2, 1), and assign the remaining positions greedily by the
    largest marginal w_i/(a_i+1), ties to the lower index.  The result is then
    checked against the exchange conditions w_i a_j <= w_j (a_i + 1) for all
    i != j with a_j > 0, which characterize the maxima of this separable
    concave objective; the check, not the construction, certifies the mode.
    """
    if N < 1 or d < 2:
        raise ValueError("need N >= 1 and d >= 2")
    weights = (d - 1, 2, 1)
    counts = [max(0, N * w // (d + 2) - 1) for w in weights]
    for _ in range(N - sum(counts)):
        best = 0
        for i in (1, 2):
            if weights[i] * (counts[best] + 1) > weights[best] * (counts[i] + 1):
                best = i
        counts[best] += 1
    for i in range(3):
        for j in range(3):
            if i != j and counts[j] > 0 and weights[i] * counts[j] > weights[j] * (counts[i] + 1):
                raise CertificateError(f"type {counts} is not a mode for N={N}, d={d}")
    return tuple(counts)


# ---------------------------------------------------------------------------
# The cost model


def stage_data(stages, N: int, k: int) -> list[dict]:
    """Per-arity data (arity, stages, type, M, 2M-1, E) in increasing arity."""
    multiplicity = Counter(d for _, _, d, _ in stages)
    rows = []
    for d in sorted(multiplicity):
        retained = mode(N, d)
        m = sector_count(d, *retained)
        rows.append({"arity": d, "stages": multiplicity[d], "type": retained,
                     "M": m, "copies": 2 * m - 1, "E": 1 + 6 * k * (m - 1)})
    return rows


def exact_counts(stages, N: int, k: int) -> dict[str, int]:
    """The integers A, B, r_*, m_* of the closed formula (small chains only)."""
    (r1, b1), (one, t) = chain_ends(stages)
    if one != 1:
        raise CertificateError("the terminal pair must be (1, t)")
    s = r1 + b1 - 1
    A, B, r_star, m_star = 1, t ** (2 * N * k), s ** (6 * N * k), 1
    for row in stage_data(stages, N, k):
        c = row["stages"]
        A *= row["arity"] ** (2 * N * k * c)
        B *= row["M"] ** (2 * k * c)
        r_star *= (row["copies"] ** (6 * k) * row["E"]) ** c
        m_star *= row["M"] ** (6 * k * c)
    return {"A": A, "B": B, "r_star": r_star, "m_star": m_star}


def log_counts(s: int, t: int, rows, N: int, k: int) -> dict[str, Interval]:
    """Enclosures of log(r_*/m_*) and log(B/A)."""
    log_ratio = log_integer(s).times(6 * N * k)
    log_gain = log_integer(t).times(2 * N * k)
    for row in rows:
        c, log_m = row["stages"], log_integer(row["M"])
        log_gain += (log_m - log_integer(row["arity"]).times(N)).times(2 * k * c)
        log_ratio += (log_integer(row["copies"]) - log_m).times(6 * k * c)
        log_ratio += log_integer(row["E"]).times(c)
    return {"log_ratio": log_ratio, "log_gain": log_gain}


def side_factors(t: int, rows, N: int, k: int) -> dict[str, list[tuple[int, int]]]:
    """A and B as products base^exponent with exact integer exponents."""
    return {"A": [(row["arity"], 2 * N * k * row["stages"]) for row in rows],
            "B": [(t, 2 * N * k)] + [(row["M"], 2 * k * row["stages"]) for row in rows]}


def exponents(logs: dict[str, Interval]) -> dict[str, Interval]:
    """Enclosures of p, Phi and Phi - p = log 2 / log(B/A)."""
    gain = logs["log_gain"]
    if gain.lo <= 0:
        raise CertificateError("B > A is not certified")
    return {"p": logs["log_ratio"].over(gain),
            "Phi": (logs["log_ratio"] + log_integer(2)).over(gain),
            "Phi_minus_p": log_integer(2).over(gain)}


# ---------------------------------------------------------------------------
# Witnesses

# Each point: strict target for Phi, terminal pair (1, t), forward arities
# (constant-arity runs, source first, then optionally the ramp from (R, R) to
# (1, 1)), N factors per sign and power k.  Chains are built backward from
# (1, t) by smallest parents; every type is a certified mode.
WITNESSES = (
    {"name": "below-3", "target": "3", "t": 128, "runs": [[2, 1]], "ramp_R": None,
     "N": 24, "k": 2},
    {"name": "below-2.77429", "target": "2.77429", "t": 5, "runs": [[2, 1]], "ramp_R": None,
     "N": 215, "k": 10},
    {"name": "below-2.7", "target": "2.7", "t": 3, "runs": [[2, 5]], "ramp_R": None,
     "N": 147, "k": 8},
    {"name": "below-2.5", "target": "2.5", "t": 3, "runs": [[2, 15]], "ramp_R": None,
     "N": 264, "k": 14},
    {"name": "below-2.3", "target": "2.3", "t": 1, "runs": [[2, 121]], "ramp_R": 3,
     "N": 1999, "k": 80},
    {"name": "below-2.26", "target": "2.26", "t": 1, "runs": [[4, 1244]], "ramp_R": 11,
     "N": 28336, "k": 1118},
)

# Points below the computed exponents Phi of v5's Table 2 rows a=8 and a=12
# (floating-point values 2.8406393 and 2.6728401; v5 says that pooling lowers
# them by less than 1e-7).  Selected by a bounded floating-point screen over
# terminals (1, t), t <= 64, up to 60 stages of arity 2 and N <= 1500
# (experiments/shifted_chains_skeptic_certificates.py --screen); the
# certificates below are exact.
V5_COMPARISONS = (
    {"name": "below-2.84063", "target": "2.84063", "t": 5, "runs": [[2, 1]], "ramp_R": None,
     "N": 93, "k": 5,
     "v5_table_2": {"a": 8, "Phi_computed": "2.8406393", "Phi_bar_certified": "2.848599165",
                    "decimal_digits_A": 11877489885}},
    {"name": "below-2.67283", "target": "2.67283", "t": 3, "runs": [[2, 7]], "ramp_R": None,
     "N": 138, "k": 8,
     "v5_table_2": {"a": 12, "Phi_computed": "2.6728401", "Phi_bar_certified": "2.675820359",
                    "decimal_digits_A": 234905651862}},
)


def arity_list(spec) -> list[int]:
    arities = [d for d, repeat in spec["runs"] for _ in range(repeat)]
    if spec["ramp_R"] is not None:
        arities += ramp_arities(spec["ramp_R"])
    return arities


def arity_text(spec) -> str:
    """Compact forward arities, e.g. '4^1244, then 3j, 3j-1 for j = 10, ..., 1'."""
    parts = [f"{d}^{repeat}" if repeat > 1 else str(d) for d, repeat in spec["runs"]]
    side = spec["ramp_R"]
    if side is not None:
        indices = ", ".join(str(j) for j in range(side - 1, 0, -1)) if side <= 4 else f"{side - 1}, ..., 1"
        parts.append(f"then 3j, 3j-1 for j = {indices} (ramp from ({side},{side}))")
    return ", ".join(parts)


def compress(arities: list[int]) -> list[list[int]]:
    runs = []
    for d in arities:
        if runs and runs[-1][0] == d:
            runs[-1][1] += 1
        else:
            runs.append([d, 1])
    return runs


def certificate(spec) -> dict:
    target = Fraction(spec["target"])
    N, k, t = spec["N"], spec["k"], spec["t"]
    if min(N, k, t) < 1:
        raise ValueError("need N, k, t >= 1")
    arities = arity_list(spec)
    stages = backward_chain((1, t), arities)
    source, terminal = chain_ends(stages)
    if terminal != (1, t):
        raise CertificateError("the chain does not end at (1, t)")
    if forward_floor_chain(source, arities) != stages:
        raise CertificateError("the forward largest-child chain differs")
    side = spec["ramp_R"]
    if side is not None and stages[len(arities) - 2 * (side - 1)][:2] != (side, side):
        raise CertificateError("the ramp does not start at (R, R)")
    s = source[0] + source[1] - 1
    rows = stage_data(stages, N, k)
    bounds = exponents(log_counts(s, t, rows, N, k))
    if bounds["p"].lo <= 2:
        raise CertificateError("p > 2 is not certified")
    if not bounds["Phi"].hi < target:
        raise CertificateError(f"{spec['name']}: Phi is not certified below {spec['target']}")
    previous = None
    if k > 1:
        previous = exponents(log_counts(s, t, stage_data(stages, N, k - 1), N, k - 1))["Phi"]
        if previous.lo < target:
            raise CertificateError(f"{spec['name']}: Phi >= target at k-1 is not certified")
    factors = side_factors(t, rows, N, k)
    types = []
    for row in rows:
        m = row["M"]
        types.append({
            "arity": row["arity"], "stages": row["stages"],
            "type_nK_nO_nmid": list(row["type"]),
            "M_bit_length": m.bit_length(),
            "M": str(m) if m < 10 ** 60 else None,
            "M_sha256_big_endian": hashlib.sha256(m.to_bytes((m.bit_length() + 7) // 8, "big")).hexdigest(),
        })
    steps = [list(stage) for stage in stages]
    entry = {
        "name": spec["name"],
        "target": spec["target"],
        "source_pair": list(source),
        "s": s,
        "terminal_pair": list(terminal),
        "arities_source_first": arity_text(spec),
        "arity_runs_source_first": compress(arities),
        "stages_J": len(stages),
        "N_per_sign": N,
        "k": k,
        "types": types,
        "stages_r_b_d_c": steps if len(steps) <= 20 else None,
        "stages_sha256": hashlib.sha256(json.dumps(steps).encode()).hexdigest(),
        "A": " * ".join(f"{base}^{exponent}" for base, exponent in factors["A"]),
        "decimal_digits_A": decimal_digits(factors["A"]),
        "decimal_digits_B": decimal_digits(factors["B"]),
        "Phi": bounds["Phi"].decimal_strings(),
        "p": bounds["p"].decimal_strings(),
        "Phi_minus_p": bounds["Phi_minus_p"].scientific_strings(),
        "Phi_below_target": True,
        "k_is_least": True,
        "Phi_at_k_minus_1_lower": None if previous is None else previous.decimal_strings()["lower"],
    }
    if "v5_table_2" in spec:
        entry["v5_table_2"] = spec["v5_table_2"]
    return entry


def report() -> dict:
    return {
        "schema": "shifted-chain-certificates-v2",
        "producer": "experiments/shifted_chain_certificates.py",
        "model": {
            "stage": "(r,b) -> (c,r) of arity d: d>=2, 1<=c<b, (d+2)c <= d*b-r+1",
            "chain": ("stages i=1..J from the source pair (r_1,b_1) to the terminal pair (1,t), "
                      "built backward from (1,t) by the smallest parent b'=ceil(((d+2)r+b-1)/d); "
                      "checked equal to the forward chain with the largest child c=floor((d*b-r+1)/(d+2))"),
            "ramp": "ramp from (R,R) to (1,1): forward arities 3j, 3j-1 for j=R-1,...,1",
            "types": ("(nK,nO,nmid) with nK+nO+nmid=N per sign, the same in all six orientations; "
                      "a mode of M, certified by the exchange conditions"),
            "sector_count": "M = N!/(nK! nO! nmid!) * (d-1)^nK * 2^nO",
            "exactification": "E = 1+6k(M-1) at every stage (Lu's separator, degree 6(M-1), over Q)",
            "counts": ("A = prod_i d_i^(2Nk); B = t^(2Nk) prod_i M_i^(2k); "
                       "r_* = s^(6Nk) prod_i (2M_i-1)^(6k) E_i; m_* = prod_i M_i^(6k); s = r_1+b_1-1"),
            "p": "log(r_*/m_*)/log(B/A), the pooled exponent (v5 Lemma 2.4)",
            "Phi": "log(2 r_*/m_*)/log(B/A) = p + log 2/log(B/A), the fixed-batch bound (v5 (10.1))",
            "ceiling": ("the log 2 term pays for the ceiling ceil(r_*/m_*) of the recursion without pooling "
                        "(v5 Section 10.1); the pooled recursion also has ceilings ceil(nu_l/m_*) (v5 (2.9)), "
                        "but they do not enter its exponent p"),
            "least_k": ("Phi strictly decreases in k and A increases in k for fixed chain, N and types; "
                        "Phi at k-1 is certified >= target, so k and A are least for that chain, N and types"),
            "field": "Q (rational interpolation, Lu's separator, rational exactification)",
            "selection": "the points are selected, not minimal",
        },
        "log_enclosure": {"mantissa_bits": MANTISSA_BITS, "series_terms": SERIES_TERMS,
                          "dyadic_bits": DYADIC_BITS, "printed_decimals": DECIMALS,
                          "printed_significant_digits_of_Phi_minus_p": SIGNIFICANT,
                          "rounding": "every printed bound is rounded outward"},
        "witnesses": [certificate(spec) for spec in WITNESSES],
        "comparisons_with_v5_note": (
            "Targets 2.84063 and 2.67283 lie about 1e-5 below the computed Phi of v5 Table 2 rows a=8 and "
            "a=12 (floating-point values 2.8406393 and 2.6728401), not only below v5's certified bounds "
            "Phi-bar. v5 states that pooling lowers its Phi by less than 1e-7, so the targets are also below "
            "v5's pooled exponents p if v5's floating-point values are accurate to 1e-6. v5 does not "
            "tabulate its B."),
        "comparisons_with_v5": [certificate(spec) for spec in V5_COMPARISONS],
    }


def serialize(data: dict) -> str:
    return json.dumps(data, indent=2) + "\n"


def summary_lines(data: dict) -> list[str]:
    lines = []
    for entry in data["witnesses"] + data["comparisons_with_v5"]:
        types = [f"d={row['arity']}: {tuple(row['type_nK_nO_nmid'])}" for row in entry["types"]]
        if len(types) > 4:
            types = types[:4] + ["..."]
        source = ", ".join(str(x) if x < 10 ** 12 else f"<{len(str(x))} digits>" for x in entry["source_pair"])
        lines.append(
            f"{entry['name']:>14}: source ({source}), arities {entry['arities_source_first']}, "
            f"terminal {tuple(entry['terminal_pair'])}, N={entry['N_per_sign']}, k={entry['k']} (least), "
            f"types {', '.join(types)}\n"
            f"{'':>16}Phi < {entry['Phi']['upper']}, p in [{entry['p']['lower']}, {entry['p']['upper']}], "
            f"Phi-p in [{entry['Phi_minus_p']['lower']}, {entry['Phi_minus_p']['upper']}], "
            f"digits A {entry['decimal_digits_A']:,}, digits B {entry['decimal_digits_B']:,}")
    return lines


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="recompute and compare with the saved report")
    args = parser.parse_args(argv)
    data = report()
    text = serialize(data)
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != text:
            print("MISMATCH: recomputed certificates differ from", OUTPUT)
            return 1
        print("OK: recomputed certificates match", OUTPUT)
    else:
        OUTPUT.write_text(text)
        print("wrote", OUTPUT)
    print("\n".join(summary_lines(data)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
