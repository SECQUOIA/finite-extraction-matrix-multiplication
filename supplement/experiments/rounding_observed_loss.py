"""Numbers quoted in Remark rem:observed-loss (Section 6, rounding.tex).

For each target index a and rounding scale K, the script
  1. computes the exact rational occupations of every row walk
     (fractions.Fraction, exact Gaussian elimination),
  2. rounds each row graph with the rule of Theorem effective:
     breadth-first augmenting paths, arcs listed as the transition edges by
     increasing state x and then increasing child y, then the tripling edge
     3r -> 1, then the source arcs and the sink arcs by increasing state
     (the return edge 0 -> xin_r has the integer value K and gets no arc),
  3. checks the rounded row identities, the edge error bounds and the
     closed form of J_a exactly, and
  4. evaluates the rounding loss
         L = sum_{active (r,x)} sum_{y: n>0} n_{r,x,y} log(n_{r,x,y} / (w_{r,x} q_{r,x,y}))
     in floating point (math.log, float64), together with 4 J_a.

The rounding routine mirrors experiments/multiway_rounded_flow.py of the
repository (same arc order and the same residual scan order).  The script also
compares its counts with that module of the enclosing repository (read only; bytecode writing is disabled).

Run: python3 -I rounding_observed_loss.py
"""
from collections import Counter, deque
from fractions import Fraction
import math
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def transitions(r, x):
    n = 3 * r
    h = min(x, n - x)
    c = Fraction(3 * (r - 1), 2)
    return {y: (c + y) / ((h + 1) * (c + x)) for y in range(x - h, x + h + 1, 2)}


def occupations(r, xin):
    """Return [lambda_1, ..., lambda_{3r-1}, mu] for injection state xin."""
    n = 3 * r
    A = [[Fraction(int(i == j)) for j in range(1, n + 1)] + [Fraction(int(i == xin))]
         for i in range(1, n + 1)]
    for x in range(1, n):
        for y, p in transitions(r, x).items():
            if y:
                A[y - 1][x - 1] -= p
    A[0][n - 1] -= 1  # tripling: state 3r -> state 1
    for col in range(n):
        piv = next(i for i in range(col, n) if A[i][col])
        A[col], A[piv] = A[piv], A[col]
        d = A[col][col]
        A[col] = [v / d for v in A[col]]
        for i in range(n):
            if i != col and A[i][col]:
                f = A[i][col]
                A[i] = [u - f * v for u, v in zip(A[i], A[col])]
    return [row[-1] for row in A]


def round_circulation(edges):
    """Floor/ceiling rounding of a rational circulation by BFS augmenting paths."""
    vertices = sorted({u for u, _, _ in edges} | {v for _, v, _ in edges})
    index = {v: i for i, v in enumerate(vertices)}
    src, snk = len(vertices), len(vertices) + 1
    graph = [[] for _ in range(len(vertices) + 2)]  # arcs: [head, reverse position, capacity]

    def add_arc(u, v, cap):
        fwd = [v, len(graph[v]), cap]
        bwd = [u, len(graph[u]), 0]
        graph[u].append(fwd)
        graph[v].append(bwd)
        return fwd

    floors = [value.numerator // value.denominator for _, _, value in edges]
    imbalance = Counter()  # in-minus-out balance of the integer parts
    frac_arcs = []
    for i, ((u, v, value), lo) in enumerate(zip(edges, floors)):
        imbalance[index[u]] -= lo
        imbalance[index[v]] += lo
        if value != lo and u != v:
            frac_arcs.append((i, add_arc(index[u], index[v], 1)))
    need = 0
    for v in range(len(vertices)):
        if imbalance[v] > 0:
            add_arc(src, v, imbalance[v])
            need += imbalance[v]
    for v in range(len(vertices)):
        if imbalance[v] < 0:
            add_arc(v, snk, -imbalance[v])
    done = 0
    while done < need:
        prev = [None] * len(graph)
        prev[src] = (-1, -1)
        queue = deque([src])
        while queue and prev[snk] is None:
            u = queue.popleft()
            for k, arc in enumerate(graph[u]):
                if arc[2] and prev[arc[0]] is None:
                    prev[arc[0]] = (u, k)
                    queue.append(arc[0])
                    if arc[0] == snk:
                        break
        assert prev[snk] is not None, "fractional flow must be feasible"
        amount, v = need - done, snk
        while v != src:
            u, k = prev[v]
            amount = min(amount, graph[u][k][2])
            v = u
        v = snk
        while v != src:
            u, k = prev[v]
            arc = graph[u][k]
            arc[2] -= amount
            graph[v][arc[1]][2] += amount
            v = u
        done += amount
    counts = floors[:]
    for i, arc in frac_arcs:
        counts[i] += 1 - arc[2]
    return counts


def round_row(r, K, xin):
    occ = occupations(r, xin)
    lam, mu = occ[:-1], occ[-1]
    edges, slots = [], []
    for x in range(1, 3 * r):
        for y, p in transitions(r, x).items():
            slots.append((x, y))
            edges.append((x, y, K * lam[x - 1] * p))
    edges.append((3 * r, 1, K * mu))
    edges.append((0, xin, Fraction(K)))
    counts = round_circulation(edges)
    assert counts[-1] == K
    n = {slot: c for slot, c in zip(slots, counts)}
    z = counts[-2]
    # exact checks: edge errors and rounded row identity
    for (u, v, value), c in zip(edges, counts):
        assert abs(c - value) < 1
    bal = Counter()
    for (x, y), c in n.items():
        bal[x] += c
        bal[y] -= c
    bal[3 * r] += z
    bal[1] -= z
    assert {k: v for k, v in bal.items() if v} == {xin: K, 0: -K}
    return n, z


def J(a):
    return sum(len(transitions(r, x)) for r in range(2, a + 1) for x in range(1, 3 * r))


def loss(a, K):
    terms = []
    rows = {}
    for r in range(2, a + 1):
        n, z = round_row(r, K, 1 if r == a else 2)
        rows[r] = (n, z)
        for x in range(1, 3 * r):
            q = transitions(r, x)
            w = sum(n[(x, y)] for y in q)
            for y, p in q.items():
                c = n[(x, y)]
                if c:
                    terms.append(c * math.log(c / (w * float(p))))
    return math.fsum(terms), rows


def repo_counts(a, K):
    if not os.path.isdir(REPO):
        return None
    sys.dont_write_bytecode = True
    if REPO not in sys.path:
        sys.path.insert(0, REPO)
    from experiments.multiway_rounded_flow import rounded_profile
    out = {}
    for row in rounded_profile(a, K):
        r = row.row
        n = {}
        for act in row.actions:
            x = act.column - r + 1
            for col, c in zip(act.children, act.counts):
                n[(x, col - r + 1)] = c
        out[r] = (n, row.reset_count)
    return out


def main():
    for a in range(2, 301):
        closed = Fraction(12 * a**3 + 42 * a**2 + 12 * a - 65 + (-1) ** a, 16)
        assert sum((9 * r * r) // 4 + 3 * r - 1 for r in range(2, a + 1)) == closed
    print("closed form of J_a verified for 2 <= a <= 300")
    worst = []
    for a in range(2, 13):
        Ka = a**3 * math.ceil(math.log2(a))
        for K in sorted({1, 2, 7, a**3, Ka}):
            L, rows = loss(a, K)
            ref = repo_counts(a, K)
            if ref is not None:
                assert ref == rows, (a, K)
            fourJ = 4 * J(a)
            worst.append((L / fourJ, a, K, L, fourJ))
            print(f"a={a:2d} K={K:5d}  L={L:.6f}  4J_a={fourJ:5d}  L/(4J_a)={L / fourJ:.5f}")
    worst.sort(reverse=True)
    print("largest ratios:", [(round(t[0], 5), t[1], t[2]) for t in worst[:3]])
    n, z = loss(2, 1)[1][2]
    print("a=2, K=1 nonzero counts:", {k: v for k, v in n.items() if v}, "z_2 =", z)
    print("log 5 =", math.log(5), " log(5)/56 =", math.log(5) / 56)
    print("compared with repository module:", os.path.isdir(REPO))


if __name__ == "__main__":
    main()
