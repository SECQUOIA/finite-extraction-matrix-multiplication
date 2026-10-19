"""Verification run for docs/shifted-chains-check-certificates.md.

1. Recompute the canonical witnesses and v5 comparison points of the report
   (schema shifted-chain-certificates-v2) with an independent logarithm
   (decimal module, 80 digits) and independent brute-force modes for small n,
   and compare chains, sector counts, Phi, p and digit counts with the report.
2. Recompute, in the canonical cost model, every finite certificate tabulated
   in the round-8, round-10 and round-11 notes, from the parameters stored in
   their receipts, and compare exponent bounds and digit counts.
3. Print the v5 Table (section 10) values from results/multiway-finite-costs.json.
4. With --screen, rerun a bounded float screen below v5's certified bounds
   Phi-bar (about 30 seconds).  The report's points below v5's computed Phi
   were selected by experiments/shifted_chains_skeptic_certificates.py --screen.

Run from the repository root:  python -I experiments/shifted_chains_check_certificates.py
Prints a report; writes no file.
"""

from __future__ import annotations

from collections import Counter
from decimal import Decimal, getcontext
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
import shifted_chain_certificates as sc  # noqa: E402

sys.set_int_max_str_digits(0)
getcontext().prec = 80
LN2 = Decimal(2).ln()
LN10 = Decimal(10).ln()


def load(name):
    return json.loads((ROOT / "results" / name).read_text())


# ---------------------------------------------------------------------------
# 1. Independent recomputation of the canonical witnesses


def dln(value: int) -> Decimal:
    shift = max(0, value.bit_length() - 240)
    return Decimal(value >> shift).ln() + shift * LN2


def brute_mode_count(n: int, d: int) -> int:
    best = 0
    for kernel in range(n + 1):
        for outer in range(n - kernel + 1):
            best = max(best, comb(n, kernel) * comb(n - kernel, outer)
                       * (d - 1) ** kernel * 2 ** outer)
    return best


def independent_witness(spec, saved):
    n, k = spec["N"], spec["k"]
    arities = sc.arity_list(spec)
    # Rebuild the chain forward from the saved source with the largest-child rule.
    r, b = saved["source_pair"]
    steps = []
    for d in arities:
        c = (d * b - r + 1) // (d + 2)
        assert 1 <= c < b and (d + 2) * c <= d * b - r + 1
        steps.append([r, b, d, c])
        r, b = c, r
    t = spec["t"]
    assert [r, b] == [1, t] == saved["terminal_pair"]
    chain_ok = (hashlib.sha256(json.dumps(steps).encode()).hexdigest() == saved["stages_sha256"]
                and saved["stages_J"] == len(steps))
    s = sum(saved["source_pair"]) - 1
    assert s == saved["s"]
    counts = {}
    for d in arities:
        counts[d] = counts.get(d, 0) + 1
    log_ratio = 6 * n * k * dln(s)
    log_gain = 2 * n * k * dln(t)
    log_A = Decimal(0)
    log_B = 2 * n * k * dln(t)
    for row in saved["types"]:
        d, c = row["arity"], row["stages"]
        kernel, outer, middle = row["type_nK_nO_nmid"]
        assert kernel + outer + middle == n and c == counts[d]
        h = comb(n, kernel) * comb(n - kernel, outer) * (d - 1) ** kernel * 2 ** outer
        if n <= 300:
            assert h == brute_mode_count(n, d), (n, d)
        h_bytes = h.to_bytes((h.bit_length() + 7) // 8, "big")
        chain_ok &= (hashlib.sha256(h_bytes).hexdigest() == row["M_sha256_big_endian"]
                     and row["M"] in (None, str(h)))
        e = 1 + 6 * k * (h - 1)
        log_ratio += c * (6 * k * (dln(2 * h - 1) - dln(h)) + dln(e))
        log_gain += 2 * k * c * (dln(h) - n * dln(d))
        log_A += 2 * n * k * c * dln(d)
        log_B += 2 * k * c * dln(h)
    phi = (log_ratio + LN2) / log_gain
    p = log_ratio / log_gain
    digits_A = int(log_A / LN10) + 1
    digits_B = int(log_B / LN10) + 1
    ok = (chain_ok and sorted(counts) == [row["arity"] for row in saved["types"]]
          and Decimal(saved["Phi"]["lower"]) <= phi <= Decimal(saved["Phi"]["upper"])
          and Decimal(saved["p"]["lower"]) <= p <= Decimal(saved["p"]["upper"])
          and phi < Decimal(spec["target"])
          and digits_A == saved["decimal_digits_A"] and digits_B == saved["decimal_digits_B"])
    return ok, phi


# ---------------------------------------------------------------------------
# 2. Documented certificates recomputed in the canonical model


def stage_rows(levels, n, k, types=None):
    """sc.stage_data, but with the explicit types of a receipt when given."""
    if types is None:
        return sc.stage_data(levels, n, k)
    rows = []
    for d, count in sorted(Counter(d for _, _, d, _ in levels).items()):
        m = sc.sector_count(d, *types[d])
        rows.append({"arity": d, "stages": count, "type": types[d],
                     "M": m, "copies": 2 * m - 1, "E": 1 + 6 * k * (m - 1)})
    return rows


def model_bounds(levels, n, k, types=None):
    (r0, b0), (_, t) = sc.chain_ends(levels)
    rows = stage_rows(levels, n, k, types)
    logs = sc.log_counts(r0 + b0 - 1, t, rows, n, k)
    bounds = sc.exponents(logs)
    factors = sc.side_factors(t, rows, n, k)
    return {"phi": bounds["Phi"], "p": bounds["p"],
            "digits_A": sc.decimal_digits(factors["A"]),
            "digits_B": sc.decimal_digits(factors["B"])}


def compare(label, ours, doc_phi_upper, doc_A, doc_B, doc_phi_lower=None):
    upper = Fraction(doc_phi_upper)
    lower = Fraction(doc_phi_lower) if doc_phi_lower is not None else upper - Fraction(1, 10 ** 9)
    overlap = ours["phi"].lo <= upper and lower <= ours["phi"].hi
    same = overlap and ours["digits_A"] == doc_A and (doc_B is None or ours["digits_B"] == doc_B)
    print(f"  {'OK ' if same else 'DIFF'} {label:<44} Phi<{ours['phi'].decimal_strings()['upper']} "
          f"(doc {str(doc_phi_upper)[:14]})  A {ours['digits_A']:,} (doc {doc_A:,})  "
          f"B {ours['digits_B']:,} (doc {doc_B if doc_B is None else f'{doc_B:,}'})")
    return same


def round8_multiscale():
    print("round-8 multiscale construction table (explicit types ((d-1)t,2t,t), crops c, c)")
    results = []
    for item in load("round8-multiscale-construction.json")["finite_certificates"]:
        d, cycles, scale, k = (int(item[key]) for key in
                               ("arity", "cycles", "type_scale", "interpolation_power_k"))
        sides = [1]
        for _ in range(cycles):
            sides.append(-(-((d + 2) * sides[-1] - 1) // (d - 1)))
        assert str(sides[-1]) == item["initial_diagonal_side"]
        levels = []
        for j in range(cycles, 0, -1):
            a, c = sides[j], sides[j - 1]
            assert ((d - 1) * a + 1) // (d + 2) == c
            levels += [(a, a, d, c), (c, a, d, c)]
        n = (d + 2) * scale
        ours = model_bounds(levels, n, k, {d: ((d - 1) * scale, 2 * scale, scale)})
        interval = item["fully_charged_fixed_batch_exponent_upper_interval"]
        results.append(compare(f"d={d} cycles={cycles} t={scale} k={k}", ours,
                               interval["upper"], int(item["source_decimal_digits"]), None,
                               interval["lower"]))
    return results


def round8_terminal():
    print("round-8 terminal inventory (forward largest-child chains, explicit types, t=b_final)")
    results = []
    for item in load("round8-terminal-inventory.json")["certified_candidates"]:
        d, n, k, depth = (int(item[key]) for key in ("d", "n_per_sign", "k", "levels"))
        source = tuple(int(x) for x in item["chain"]["initial"])
        levels = sc.forward_floor_chain(source, [d] * depth)
        assert [levels[-1][3], levels[-1][0]] == list(item["chain"]["final"])
        kind = item["type"]
        ours = model_bounds(levels, n, k, {d: (kind["kernel"], kind["outer"], kind["middle"])})
        interval = item["certified_fixed_batch_upper_interval"]
        results.append(compare(f"target {item['target']} d={d} n={n} k={k} L={depth}", ours,
                               interval[1], int(item["certified_source_decimal_digits"]),
                               int(item["certified_target_decimal_digits"]), interval[0]))
    return results


def round10_adaptive():
    print("round-10 adaptive chain (explicit steps and types)")
    data = load("round10-adaptive-chain.json")
    results = []
    for group in ("certified_adaptive_candidates", "certified_nonconstant_arity_candidates",
                  "one_level_C33_controls"):
        for item in data[group]:
            levels = [(s["r"], s["b"], s["d"], s["c"]) for s in item["steps"]]
            types = {}
            for s in item["steps"]:
                assert types.setdefault(s["d"], tuple(s["type_kernel_outer_middle"])) == \
                    tuple(s["type_kernel_outer_middle"])
            assert sc.chain_ends(levels)[1][1] == item["terminal"]
            ours = model_bounds(levels, item["n"], item["k"], types)
            interval = item["certified_fixed_batch_upper_interval"]
            results.append(compare(f"{group.split('_')[1]} target {item['target']} arities {item['arities'][:4]}",
                                   ours, interval[1], item["source_decimal_digits"],
                                   item["target_decimal_digits"], interval[0]))
    return results


def round11_ramp():
    print("round-11 arity ramp table (R=8D, modes)")
    results = []
    for item in load("round11-arity-ramp.json")["finite_certificates"]:
        D, L, R = item["bulk_arity"], item["bulk_levels"], item["ramp_side"]
        arities = [D] * L + sc.ramp_arities(R)
        levels = sc.backward_chain((1, 1), arities)
        assert list(sc.chain_ends(levels)[0]) == item["source_pair"]
        ours = model_bounds(levels, item["inventory_per_sign"], item["power"])
        interval = item["certified_fixed_batch_upper_interval"]
        results.append(compare(f"D={D} L={L} n={item['inventory_per_sign']} k={item['power']}",
                               ours, interval["upper"], item["source_decimal_digits"],
                               item["target_decimal_digits"], interval["lower"]))
    return results


def round11_search():
    print("round-11 finite ramp search (modes)")
    results = []
    for item in load("round11-finite-ramp-search.json")["certified_candidates"]:
        D, L, R = item["bulk_arity"], item["bulk_levels"], item["ramp_side"]
        levels = sc.backward_chain((1, 1), [D] * L + sc.ramp_arities(R))
        assert list(sc.chain_ends(levels)[0]) == item["source_pair"]
        ours = model_bounds(levels, item["n"], item["k"])
        interval = item["certified_fixed_batch_upper_interval"]
        results.append(compare(f"target {item['target']} D={D} R={R} L={L} n={item['n']} k={item['k']}",
                               ours, interval["upper"], item["source_decimal_digits"],
                               item["target_decimal_digits"], interval["lower"]))
    return results


def v5_table():
    print("v5 Table (section 10): sufficient upper expression and digits of A")
    for report in load("multiway-finite-costs.json")["reports"]:
        row = report["powers"][-1]
        upper = sc.Interval.exact(Fraction(row["fully_charged_upper_expression_interval"]["upper"]))
        print(f"  a={report['index']:>2} k={row['k']} j={row['j']}: bound<{upper.decimal_strings(9)['upper']}  "
              f"digits(A)={row['recursive_source_decimal_digits']:,}")


def v5_quality_screen(target: float, d=2, t_max=40, levels_max=40, n_max=700):
    """Bounded float screen: least log10 A with Phi < target.

    Chains: terminal (1,t), constant arity d, smallest parents; modes;
    least power k by bisection (Phi decreases in k).  Selection only; the
    selected points are certified exactly by the canonical script.
    """
    from math import exp, lgamma, log, log1p
    log_h = {}
    for n in range(1, n_max + 1):
        kernel, outer, middle = sc.mode(n, d)
        log_h[n] = (lgamma(n + 1) - lgamma(kernel + 1) - lgamma(outer + 1) - lgamma(middle + 1)
                    + kernel * log(d - 1) + outer * log(2))
    best = None
    for t in range(1, t_max + 1):
        pair = (1, t)
        for levels in range(1, levels_max + 1):
            pair = sc.smallest_parent(pair, d)
            s = pair[0] + pair[1] - 1
            for n in range(1, n_max + 1):
                h = log_h[n]
                gain = n * log(t) + levels * (h - n * log(d))
                if gain <= 0:
                    continue
                inverse = exp(-h)
                base = 3 * n * log(s) + 3 * levels * log(2 - inverse)

                def phi(k):
                    interpolation = h + log(6 * k) + log1p(-(1 - 1 / (6 * k)) * inverse)
                    return (base + (levels * interpolation + log(2)) / (2 * k)) / gain

                high = 1 << 20
                if phi(high) >= target:
                    continue
                low = 1
                while low < high:
                    middle = (low + high) // 2
                    if phi(middle) < target:
                        high = middle
                    else:
                        low = middle + 1
                digits = 2 * n * low * levels * log(d) / log(10)
                if best is None or digits < best[0] - 1e-9:
                    best = (digits, t, levels, n, low)
    return best


def main():
    report = json.loads(sc.OUTPUT.read_text())
    saved = {w["name"]: w for w in report["witnesses"] + report["comparisons_with_v5"]}
    if "--screen" in sys.argv:
        for target in (2.848599165, 2.675820359):
            digits, t, levels, n, k = v5_quality_screen(target)
            print(f"screen below {target}: terminal (1,{t}), {levels} levels of arity 2, "
                  f"n={n}, k={k}, about {digits:.1f} digits of A")
    print("independent decimal recomputation of the canonical witnesses")
    all_ok = True
    for spec in sc.WITNESSES + sc.V5_COMPARISONS:
        ok, phi = independent_witness(spec, saved[spec["name"]])
        all_ok &= ok
        print(f"  {'OK ' if ok else 'DIFF'} {spec['name']:<14} Phi={str(phi)[:20]}")
    for part in (round8_multiscale, round8_terminal, round10_adaptive, round11_ramp, round11_search):
        all_ok &= all(part())
    v5_table()
    # The same float screen with n up to 700 (the round-10 grid stopped at
    # n=256) finds a slightly smaller source below 2.5 than documented; the
    # v2 report uses it as its below-2.5 witness.
    smaller = sc.certificate({"name": "screen-below-2.5", "target": "5/2", "t": 3,
                              "runs": [[2, 15]], "ramp_R": None, "N": 264, "k": 14})
    print(f"smaller in-model point below 2.5 (the report's below-2.5 witness): terminal (1,3), "
          f"15 levels of arity 2, n=264, k=14: "
          f"Phi<{smaller['Phi']['upper']}, digits(A)={smaller['decimal_digits_A']:,}, "
          f"digits(B)={smaller['decimal_digits_B']:,} (round-10 point: 33,446 and 69,111)")
    ratios = (Fraction(28841545, 12371380), Fraction(146801351550, 48859824830))
    print("digit ratios quoted in round-11 search:", [f"{float(x):.4f}" for x in ratios])
    print("ALL CONSISTENT" if all_ok else "DISCREPANCIES FOUND")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
