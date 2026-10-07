"""Rigorous log bounds for fixed rounded multiway profiles, without factorials."""

import hashlib
import json
from pathlib import Path
import time

from experiments.general_profile_extraction import profile_diagonal
from experiments.multiway_rounded_flow import profile_ledger, rounded_profile
from experiments.rounded_profile_flows import log_integer
from experiments.small_profile_extraction import Interval, sum_intervals


def parameters(index):
    if not isinstance(index, int) or index < 2:
        raise ValueError("index must be an integer at least two")
    logarithm = (index - 1).bit_length()
    return index ** 3 * logarithm ** 2, index * logarithm


def type_entropy(counts):
    """Enclose w H(n/w), omitting zero frequencies and zero-weight actions."""
    if any(not isinstance(count, int) or count < 0 for count in counts):
        raise ValueError("type counts must be nonnegative integers")
    weight = sum(counts)
    if weight == 0:
        return Interval.exact(0)
    raw = log_integer(weight).scale(weight) - sum_intervals(
        log_integer(count).scale(count) for count in counts if count
    )
    # Entropy is nonnegative; this also makes one-point support exact zero.
    if sum(count > 0 for count in counts) <= 1:
        return Interval.exact(0)
    return Interval(max(raw.lower, 0), max(raw.upper, 0))


def interval_min(*values):
    return Interval(min(value.lower for value in values), min(value.upper for value in values))


def interval_max(*values):
    return Interval(max(value.lower for value in values), max(value.upper for value in values))


def multinomial_log_bounds(counts):
    """Enclose explicit lower/upper expressions for log of a multinomial.

    The elementary factorial bounds are intersected with the exact-type
    lower bound, nonnegativity, and the entropy upper bound.
    """
    entropy = type_entropy(counts)
    positive = [count for count in counts if count]
    if len(positive) <= 1:
        return Interval.exact(0), Interval.exact(0)
    weight, support = sum(positive), len(positive)
    c0 = (Interval.exact(1) + log_integer(2)).scale(1, 2)
    half_logs = (log_integer(weight) - sum_intervals(log_integer(n) for n in positive)).scale(1, 2)
    lower = interval_max(
        Interval.exact(0),
        entropy - log_integer(weight + 1).scale(support - 1),
        entropy + half_logs + c0 - Interval.exact(support),
    )
    upper = interval_min(entropy, entropy + half_logs + Interval.exact(1) - c0.scale(support))
    return lower, upper


def tripling_log_bounds(count):
    if not isinstance(count, int) or count < 0:
        raise ValueError("tripling count must be a nonnegative integer")
    middle = (count + 1) // 3
    lower, upper = multinomial_log_bounds((middle, count - middle))
    outer = log_integer(2).scale(count - middle)
    entropy = log_integer(3).scale(count)
    return (interval_max(entropy - log_integer(count + 1), lower + outer),
            interval_min(entropy, upper + outer))


def count_bounds(index, scale, type_scale, rows):
    """Return internal interval quantities once, for reuse across fixed powers."""
    if scale < 1 or type_scale < 1:
        raise ValueError("scale and type scale must be positive")
    residual, catalyst = profile_ledger(rows)
    assert residual == {(1, index, index): scale, (1, 1, 2): -scale}
    assert all(row.scale == scale for row in rows)
    actions = [action for row in rows for action in row.actions if action.weight]
    triples = [row.reset_count for row in rows if row.reset_count]
    U = sum(action.weight for action in actions)
    T = sum(triples)
    assert sum(catalyst.values()) == U + T - scale
    source_log = sum_intervals(log_integer(action.arity).scale(action.weight) for action in actions)
    entropies = [type_entropy(action.counts) for action in actions]
    gain = (log_integer(2).scale(scale) - source_log + sum_intervals(entropies)
            + log_integer(3).scale(T))
    basic_type_loss = sum_intervals(
        log_integer(type_scale * action.weight + 1).scale(sum(n > 0 for n in action.counts) - 1)
        for action in actions
    ) + sum_intervals(log_integer(type_scale * z + 1) for z in triples)
    action_bounds = [multinomial_log_bounds(tuple(type_scale * n for n in action.counts)) for action in actions]
    tripling_bounds = [tripling_log_bounds(type_scale * z) for z in triples]
    type_loss = sum_intervals(entropy.scale(type_scale) - lower
                             for entropy, (lower, _) in zip(entropies, action_bounds))
    type_loss = type_loss + sum_intervals(log_integer(3).scale(type_scale * z) - lower
                                        for z, (lower, _) in zip(triples, tripling_bounds))
    sector_upper = [upper for _, upper in action_bounds + tripling_bounds]
    max_sector = Interval(max(value.lower for value in sector_upper), max(value.upper for value in sector_upper))
    catalyst_log = sum_intervals(
        log_integer(row + column - 1).scale(3 * type_scale * count)
        for (_, row, column), count in catalyst.items()
    )
    diagonal = profile_diagonal(index)
    rounding_loss = (log_integer(diagonal.numerator) - log_integer(diagonal.denominator)).scale(scale) - gain
    total_arity = sum(action.arity for row in rows for action in row.actions)
    assert rounding_loss.upper <= 4 * total_arity
    return {
        "actions": actions, "triples": triples, "U": U, "T": T,
        "catalyst": catalyst, "I": len(actions) + len(triples), "total_arity": total_arity,
        "source_log": source_log.scale(type_scale), "gain": gain,
        "rounding_loss": rounding_loss, "type_loss": type_loss, "basic_type_loss": basic_type_loss,
        "contraction_lower_expression": gain.scale(type_scale) - type_loss,
        "max_sector_log_upper": max_sector, "catalyst_log": catalyst_log,
    }


def power_bounds(index, scale, type_scale, power, reuse, counts):
    if power < 1 or reuse < 1:
        raise ValueError("power and reuse must be positive")
    copy_upper = log_integer(2).scale(3 * counts["I"])
    interpolation_upper = (log_integer(3 * power * counts["I"] + 1)
                           + counts["max_sector_log_upper"].scale(2))
    main_rank = log_integer(2 * index - 1).scale(3 * type_scale * scale)
    catalyst_charge = counts["catalyst_log"].scale(1, reuse)
    ceiling_charge = log_integer(2).scale(1, power * reuse)
    numerator = main_rank + copy_upper + interpolation_upper.scale(1, power) + catalyst_charge + ceiling_charge
    contraction = counts["contraction_lower_expression"]
    exponent = numerator.divide_positive(contraction) if contraction.lower > 0 else None
    source_log = counts["source_log"].scale(power * reuse)
    source_log10 = source_log.divide_positive(log_integer(10))
    return {
        "N": type_scale, "k": power, "j": reuse,
        "main_rank_charge_interval": main_rank.as_strings(),
        "copy_ratio_upper_interval": copy_upper.as_strings(),
        "log_interpolation_upper_interval": interpolation_upper.as_strings(),
        "interpolation_charge_upper_interval": interpolation_upper.scale(1, power).as_strings(),
        "catalyst_charge_interval": catalyst_charge.as_strings(),
        "ceiling_charge_upper_interval": ceiling_charge.as_strings(),
        "contraction_lower_expression_interval": contraction.as_strings(),
        "fully_charged_upper_expression_interval": exponent.as_strings() if exponent else None,
        "recursive_source_log_interval": source_log.as_strings(),
        "recursive_source_decimal_digits": source_log10.decimal_digits(),
        "certifies_below_rank40_exponent": bool(exponent and exponent.upper <
            log_integer(40).scale(3).divide_positive(log_integer(54)).lower),
        "scope": "Intervals enclose a sufficient upper expression, not the exact recipe exponent.",
    }


def report(index, comparisons=((1, 1), (32, 1), (32, 128))):
    scale, reuse = parameters(index)
    started = time.perf_counter()
    rows = rounded_profile(index, scale)
    counts = count_bounds(index, scale, 1, rows)
    return {
        "index": index, "ceil_log2_index": (index - 1).bit_length(), "K": scale,
        "flow_and_log_bound_seconds": time.perf_counter() - started,
        "active_actions": len(counts["actions"]), "active_tripling_relations": len(counts["triples"]),
        "total_available_type_coordinates": counts["total_arity"],
        "active_type_support_coordinates": sum(sum(n > 0 for n in action.counts) for action in counts["actions"]),
        "interior_factors_U": counts["U"], "tripling_factors_T": counts["T"],
        "catalyst_factors": sum(counts["catalyst"].values()),
        "signed_catalyst": [[list(key), count] for key, count in sorted(counts["catalyst"].items())],
        "exact_signed_ledger_verified": True,
        "entropy_gain_interval": counts["gain"].as_strings(),
        "rounding_entropy_loss_interval": counts["rounding_loss"].as_strings(),
        "rounding_loss_integer_upper_bound": 4 * counts["total_arity"],
        "finite_type_loss_upper_interval": counts["type_loss"].as_strings(),
        "basic_finite_type_loss_upper_interval": counts["basic_type_loss"].as_strings(),
        "log_source_auxiliary_interval": counts["source_log"].as_strings(),
        "log_catalyst_rank_interval": counts["catalyst_log"].as_strings(),
        "rows": [{
            "row": row.row, "reset_count": row.reset_count,
            "middle_count_at_N1": (row.reset_count + 1) // 3,
            "active_actions": [{"column": action.column, "arity": action.arity,
                                "children_ascending": list(action.children), "counts_ascending": list(action.counts)}
                               for action in row.actions if action.weight],
        } for row in rows],
        "powers": [power_bounds(index, scale, 1, power, reuse * multiplier, counts)
                   for power, multiplier in comparisons],
    }


if __name__ == "__main__":
    files = [Path("experiments") / name for name in (
        "multiway_finite_costs.py", "multiway_rounded_flow.py", "multiway_profile_flows.py",
        "cyclic_profile_extraction.py", "general_profile_extraction.py",
        "rounded_profile_flows.py", "small_profile_extraction.py",
    )]
    print(json.dumps({
        "family": "L=ceil(log2 a), K=a^3 L^2, N=1; fixed (k,j) comparisons (1,aL), (32,aL), (32,128aL)",
        "sector_log_bounds": "Elementary factorial bounds intersected with support-type bounds, entropy bounds, and nonnegativity.",
        "fixed_indices": [4, 8, 12],
        "no_factorials_or_sector_maps_materialized": True,
        "source_hash_scope": "Evaluator and local calculation dependencies; Python standard library excluded.",
        "source_sha256": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in files},
        "reports": [report(index) for index in (4, 8, 12)],
    }, indent=2))
