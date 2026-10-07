"""Round profile flows with exact conservation and certify their count costs.

No tensor sectors, group subsets, or composed rank decompositions are expanded.
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import json

from experiments.general_profile_extraction import key, profile_diagonal, rational_dual
from experiments.small_profile_extraction import Interval, sum_intervals


LOG_DYADIC_BITS = 160


@lru_cache(maxsize=None)
def log_integer(value: int) -> Interval:
    """Outward-round proved log bounds before accumulating many of them."""
    enclosure = Interval.log_integer(value)
    denominator = 1 << LOG_DYADIC_BITS
    lower = enclosure.lower.numerator * denominator // enclosure.lower.denominator
    upper = -(-enclosure.upper.numerator * denominator // enclosure.upper.denominator)
    return Interval(Fraction(lower, denominator), Fraction(upper, denominator))


@dataclass(frozen=True)
class Split:
    row: int
    column: int
    up: int
    down: int

    @property
    def weight(self):
        return self.up + self.down


def ceiling(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def rounded_types(index: int, scale: int):
    if scale < 1 or not isinstance(scale, int):
        raise ValueError("scale must be a positive integer")
    concavity, tripling = rational_dual(index)
    target = {(item.row, item.column): item for item in concavity}
    triples = [(item.row, 3 * ceiling(scale * item.weight / 3)) for item in tripling]
    result = []
    for row, count in triples:
        terminal = 4 * row - 1
        down = {b: ceiling(scale * target[row, b].down) for b in range(row, terminal)}
        assert down[row] == scale
        for column in range(row, terminal):
            up = count if column == terminal - 1 else down[column + 1] + count
            if row < index and column == row:
                up -= scale
            result.append(Split(row, column, up, down[column]))
    return result, triples


def ledger(index: int, scale: int):
    splits, triples = rounded_types(index, scale)
    inputs, outputs = Counter(), Counter()
    for item in splits:
        inputs[key(item.row, item.column)] += item.weight
        outputs[key(item.row, item.column + 1)] += item.up
        outputs[key(item.row, item.column - 1)] += item.down
    for row, count in triples:
        inputs[key(row, 4 * row - 1)] += count
        outputs[key(row, row)] += count
    residual = {position: inputs[position] - outputs[position]
                for position in inputs.keys() | outputs.keys()
                if inputs[position] != outputs[position]}
    catalyst = {position: min(count, outputs[position]) for position, count in inputs.items()
                if min(count, outputs[position])}
    return residual, catalyst


def normalized_loss_bound(index: int, scale: int) -> Fraction:
    harmonic = sum((Fraction(1, h) for h in range(1, 3 * index)), Fraction())
    return Fraction(100 * index * (index - 1), 7 * scale * scale) * harmonic


def entropy_gain(index: int, scale: int) -> Interval:
    splits, triples = rounded_types(index, scale)
    entropy = sum_intervals(
        log_integer(item.weight).scale(item.weight)
        - log_integer(item.up).scale(item.up)
        - log_integer(item.down).scale(item.down)
        for item in splits
    )
    return (entropy + log_integer(2).scale(scale)
            + log_integer(3).scale(sum(count for _, count in triples))
            - log_integer(2).scale(sum(item.weight for item in splits)))


def report(index: int, scale: int | None = None, power: int = 1) -> dict:
    if power < 1 or not isinstance(power, int):
        raise ValueError("interpolation power must be a positive integer")
    scale = index ** 3 if scale is None else scale
    splits, triples = rounded_types(index, scale)
    residual, catalyst = ledger(index, scale)
    assert residual == {(index, index): scale, (1, 2): -scale}
    assert all(item.up > 0 and item.down > 0 for item in splits)
    assert all(count > 0 and count % 3 == 0 for _, count in triples)
    U, T = sum(item.weight for item in splits), sum(count for _, count in triples)
    I = len(splits) + len(triples)
    gain = entropy_gain(index, scale)
    diagonal = profile_diagonal(index)
    logF = log_integer(diagonal.numerator) - log_integer(diagonal.denominator)
    loss = logF.scale(scale) - gain
    loss_bound = normalized_loss_bound(index, scale)
    assert loss.upper <= scale * loss_bound
    type_loss = (sum_intervals(log_integer(item.weight + 1) for item in splits)
                 + sum_intervals(log_integer(count + 1).scale(2) for _, count in triples))
    contraction_lower = (gain - type_loss).scale(2)
    log2 = log_integer(2)
    sector_bounds = [log2.scale(max(item.weight for item in splits)),
                     log_integer(3).scale(max(count for _, count in triples))]
    max_sector = Interval(max(v.lower for v in sector_bounds), max(v.upper for v in sector_bounds))
    log_exactification_upper = log_integer(6 * power * I + 1) + max_sector.scale(2)
    log_catalyst = sum_intervals(
        log_integer(row + column - 1).scale(6 * count)
        for (row, column), count in catalyst.items()
    )
    reuse = index ** 3
    numerator_upper = (log_integer(2 * index - 1).scale(6 * scale)
                       + log2.scale(6 * I) + log_exactification_upper.scale(1, power)
                       + log_catalyst.scale(1, reuse) + log2.scale(1, power * reuse))
    exponent_bound = (numerator_upper.divide_positive(contraction_lower).as_strings()
                      if contraction_lower.lower > 0 else None)
    log10 = log_integer(10)
    source_log10 = log2.scale(2 * U * power * reuse).divide_positive(log10)
    return {
        "index": index,
        "log_interval_accumulation_dyadic_bits": LOG_DYADIC_BITS,
        "K": scale,
        "N": 1,
        "k": power,
        "j": reuse,
        "concavity_factors_U": U,
        "tripling_factors_T": T,
        "catalyst_Q_factors": sum(catalyst.values()),
        "max_split_weight": max(item.weight for item in splits),
        "max_tripling_weight": max(count for _, count in triples),
        "exact_ledger_verified": True,
        "normalized_KL_loss_interval": loss.scale(1, scale).as_strings(),
        "normalized_KL_loss_rational_upper_bound": str(loss_bound),
        "rounded_entropy_limit_exponent_interval":
            log_integer(2 * index - 1).scale(3 * scale).divide_positive(gain).as_strings()
            if gain.lower > 0 else None,
        "N1_log_contraction_lower_expression_interval": contraction_lower.as_strings(),
        "fully_charged_exponent_upper_expression_interval": exponent_bound,
        "recursive_source_dimension": f"2^{2 * U * power * reuse}",
        "recursive_source_dimension_decimal_digits": source_log10.decimal_digits(),
        "status": "symbolic count bounds; no sectors or coefficient maps materialized",
    }


def main():
    print(json.dumps({
        "rounding": "ceil down edges; ceil tripling to multiples of three; recover up edges from currents",
        "reports": [report(index) for index in (2, 3, 4, 8, 16, 63)],
        "finite_interpolation_amortization_examples": [report(index, power=64) for index in (16, 63)],
        "scope": "Polynomial normalization; astronomical recursion constants; no practical algorithm claimed.",
    }, indent=2))


if __name__ == "__main__":
    main()
