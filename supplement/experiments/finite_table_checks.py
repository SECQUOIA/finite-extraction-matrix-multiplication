"""Reproduce every number printed in Section 9 (finite examples) of the paper.

Usage:
    python finite_table_checks.py [path/to/multiway-finite-costs.json]

The default path is ../results/multiway-finite-costs.json relative to this
script (the layout of the repository, with this script in experiments/).

The script uses only the Python standard library. It reads the saved report
of experiments/multiway_finite_costs.py and prints two kinds of numbers.

* Certified numbers, copied from the report: the upper bounds Phi-bar of the
  sufficient upper expression, the lower bound for Delta_N, the decimal digit
  counts of the source side A, and the other enclosures. The report computes
  them with exact rational interval arithmetic; this script only rounds the
  upper end of each enclosure upwards.

* Floating-point evaluations, recomputed here from the integer counts in the
  report: the fixed-batch bound Phi itself (with log M_i from the log-gamma
  function and E and L/M^3 from the actual sector counts), the pooled exponent
  p, the profile exponent tau_a, the terms of Phi-bar divided by its
  denominator, and the percentages quoted in the text. These are not
  certified.

Notation follows the paper: N = 1 type scale, K rounding scale, k
interpolation power, j reuse count, ell_a = ceil(log2 a).
"""

from decimal import ROUND_CEILING, Decimal, getcontext
from fractions import Fraction
import json
import math
from pathlib import Path
import sys

getcontext().prec = 100


def up(interval, places):
    """Upper end of a saved enclosure, rounded upwards to `places` decimals."""
    quantum = Decimal(1).scaleb(-places)
    return Decimal(interval["upper"]).quantize(quantum, rounding=ROUND_CEILING)


def mid(interval):
    """Floating-point value of a saved enclosure (its width is below 1e-30)."""
    return float((Decimal(interval["lower"]) + Decimal(interval["upper"])) / 2)


def profile_diagonal(a):
    """F(a,a) = s_a (3a-1)/2 with s_a = prod_{h=1}^{a-1} (1 + 1/(3h))."""
    s = Fraction(1)
    for h in range(1, a):
        s *= 1 + Fraction(1, 3 * h)
    return s * Fraction(3 * a - 1, 2)


def log_fraction(x):
    return math.log(x.numerator) - math.log(x.denominator)


def log_factorial(n):
    return math.lgamma(n + 1)


def relations(report, N):
    """Return (log M_i for all relations, sum_i N w_i log d_i)."""
    log_sectors, source_log = [], 0.0
    for row in report["rows"]:
        for split in row["active_actions"]:
            counts = [N * n for n in split["counts_ascending"] if n > 0]
            weight = sum(counts)
            log_sectors.append(log_factorial(weight) - sum(map(log_factorial, counts)))
            source_log += weight * math.log(split["arity"])
        z = N * row["reset_count"]
        if z:
            m = (z + 1) // 3
            log_sectors.append(log_factorial(z) - log_factorial(m) - log_factorial(z - m)
                               + (z - m) * math.log(2))
    return log_sectors, source_log


def log_sum_exp(values):
    top = max(values)
    return top + math.log(sum(math.exp(v - top) for v in values))


def exact_phi(a, K, N, k, j, log_sectors, source_log, log_kappa):
    """Floating-point value of Phi (eq:finite-exponent) and of Delta_N."""
    delta = N * K * math.log(2) + sum(log_sectors) - source_log
    # log(L/M^3) = 3 sum_i log((2M_i-1)/M_i) = 3 sum_i log(2 - 1/M_i)
    copy = 3 * sum(math.log(2 - math.exp(-x)) for x in log_sectors)
    # E = 1 + 3k sum_i (M_i-1)^2; log(M_i - 1) = x + log(1 - e^{-x})
    logs = [2 * (x + math.log1p(-math.exp(-x))) for x in log_sectors if x > 0]
    log_s = log_sum_exp(logs)
    log_e = math.log(3 * k) + log_s + math.log1p(math.exp(-log_s) / (3 * k))
    numerator = (3 * N * K * math.log(2 * a - 1) + copy + log_e / k
                 + log_kappa / j + math.log(2) / (k * j))
    return numerator / delta, delta


def main():
    default = Path(__file__).resolve().parent.parent / "results" / "multiway-finite-costs.json"
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else default
    data = json.loads(path.read_text())
    N = 1
    print(f"Report: {path}")
    print(f"Family: {data['family']}\n")

    summary = []
    for report in data["reports"]:
        a, K = report["index"], report["K"]
        ell = (a - 1).bit_length()
        assert K == a ** 3 * ell ** 2
        F = profile_diagonal(a)
        log_F = log_fraction(F)
        tau = 3 * math.log(2 * a - 1) / log_F

        log_sectors, source_log = relations(report, N)
        assert len(log_sectors) == report["active_actions"] + report["active_tripling_relations"]
        log_kappa = sum(3 * N * c * math.log(r + b - 1) for (_, r, b), c in report["signed_catalyst"])
        # Cross-checks of the recomputed quantities against the certified report.
        assert math.isclose(source_log, mid(report["log_source_auxiliary_interval"]), rel_tol=1e-12)
        assert math.isclose(log_kappa, mid(report["log_catalyst_rank_interval"]), rel_tol=1e-12)

        rounding_loss = mid(report["rounding_entropy_loss_interval"])   # N * mathcal L, N = 1
        type_loss = mid(report["finite_type_loss_upper_interval"])      # sum_i (N H_i - lower m_i)
        gain = mid(report["entropy_gain_interval"])                     # G = K log F(a,a) - L
        assert math.isclose(gain, K * log_F - rounding_loss, rel_tol=1e-12)

        print(f"=== a = {a}: ell_a = {ell}, K = a^3 ell_a^2 = {K}, N = {N}, "
              f"active relations I = {len(log_sectors)}")
        print(f"F(a,a) = {F}  (log F(a,a) = {log_F:.6f})")
        print(f"tau_a = {tau:.7f}   tau_a - 9/4 = {tau - 2.25:.4f}")
        print(f"rounding loss N*L = {rounding_loss:.4f}")
        print(f"type loss bound sum_i (N H_i - lower m_i) = {type_loss:.4f}"
              f" = {100 * type_loss / (N * K * log_F):.2f}% of N K log F(a,a)")

        for power in report["powers"]:
            k, j = power["k"], power["j"]
            low_delta = Decimal(power["contraction_lower_expression_interval"]["lower"])
            assert low_delta > 0
            phi_bar = up(power["fully_charged_upper_expression_interval"], 9)
            phi, delta = exact_phi(a, K, N, k, j, log_sectors, source_log, log_kappa)
            assert float(low_delta) <= delta and phi <= float(phi_bar)
            assert math.isclose(float(low_delta), N * gain - type_loss, rel_tol=1e-12)
            pooled_gap = math.log(2) / (k * j * delta)
            print(f"\n  (k, j) = ({k}, {j})" + ("   [= (32, 128 a ell_a): Table]" if j == 128 * a * ell
                                                  else f"   [= ({k}, a ell_a)]" if j == a * ell else ""))
            print(f"    certified: lower Delta_N > {float(low_delta):.6f}; "
                  f"Phi-bar <= {phi_bar} (3 decimals: {up(power['fully_charged_upper_expression_interval'], 3)}); "
                  f"decimal digits of A = {power['recursive_source_decimal_digits']}")
            print(f"    floating point: Delta_N = {delta:.6f}, Phi = {phi:.7f}, "
                  f"p = Phi - log2/(k j Delta_N) = {phi - pooled_gap:.7f}, "
                  f"Phi - p = {pooled_gap:.2e}")
            print(f"    (Phi-bar - Phi)/Phi = {100 * (float(phi_bar) - phi) / phi:.3f}%")
            if j == 128 * a * ell:
                d = float(low_delta)
                terms = {
                    "main term 3NK log(2a-1)": mid(power["main_rank_charge_interval"]),
                    "copy bound 3I log 2": mid(power["copy_ratio_upper_interval"]),
                    "interpolation bound": mid(power["interpolation_charge_upper_interval"]),
                    "catalyst overhead": mid(power["catalyst_charge_interval"]),
                    "last term log2/(kj)": mid(power["ceiling_charge_upper_interval"]),
                }
                print("    terms of Phi-bar divided by lower Delta_N:")
                for name, value in terms.items():
                    print(f"      {name:28s} {value / d:.4f}" if value / d > 1e-4
                          else f"      {name:28s} {value / d:.2e}")
                print(f"    Phi-bar - tau_a = {float(phi_bar) - tau:.4f}")
                summary.append((a, K, j, tau, terms, d, phi_bar, phi, power["recursive_source_decimal_digits"]))
        print()

    print("=== Table (a | tau_a | main | copy | interpolation | catalyst | Phi-bar | Phi | digits of A)")
    for a, K, j, tau, terms, d, phi_bar, phi, digits in summary:
        values = [v / d for v in terms.values()][:4]
        print(f"{a:3d} | K={K} j={j} | {tau:.4f} | " + " | ".join(f"{v:.4f}" for v in values)
              + f" | {phi_bar} | {phi:.7f} | {digits:,}")

    # Section 10, open question 3: tau_a > 2.371339 for a <= 187 (floating point).
    taus = {a: 3 * math.log(2 * a - 1) / log_fraction(profile_diagonal(a)) for a in range(2, 189)}
    decreasing = all(taus[a] > taus[a + 1] for a in range(2, 188))
    print("\n=== Profile exponents tau_a = 3 log(2a-1) / log F(a,a), floating point")
    print(f"tau_a decreasing for 2 <= a <= 188: {decreasing}")
    print(f"min_(a <= 187) tau_a = tau_187 = {min(taus[a] for a in range(2, 188)):.7f};"
          f" tau_188 = {taus[188]:.7f}; threshold 2.371339 (Alman et al. 2025)")


if __name__ == "__main__":
    main()
