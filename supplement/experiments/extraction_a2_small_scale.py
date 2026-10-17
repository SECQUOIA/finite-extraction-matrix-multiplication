#!/usr/bin/env python3
"""Sign of Delta_1 for the target index a = 2 and type scale N = 1.

Supports two statements of Section 7 ("The finite construction"):

  (1) For a = 2 and N = 1, every rounding allowed by Lemma
      circulation-rounding gives Delta_1 < 0 when K <= 7.
  (2) The numbers of Example ex:ledger-a2 at K = 15: Delta_1 ~ 7.28,
      G = 15 log(10/3) ~ 18.06, T_1 ~ 20.78 and G - T_1 ~ -2.72.

Everything is recomputed from scratch with the Python standard library:
the row walk of row r = 2 (Section 5), its occupations, every integer
circulation with floor <= psi_e <= ceil on each edge (the conclusion of
Lemma circulation-rounding; this includes the roundings produced by every
augmenting-path rule), and Delta_1 = log(B_1/A_1) with
A_1 = prod d_i^{w_i} and B_1 = 2^K prod M_i (equations eq:sector-counts,
eq:dimensions, eq:delta-N with N = 1).  The sign of Delta_1 is decided by
the exact integer comparison of B_1 with A_1; floating point is used only
to print the values.

Run:  python3 -I extraction_a2_small_scale.py
"""
from fractions import Fraction
from itertools import product
from math import comb, factorial, floor, ceil, log

R = 2              # the only row for a = 2
TOP = 3 * R        # states 0, ..., 3r
INJECTION = 1      # injection state of the final row
K_MAX = 20


def f(x):
    """f_r(x) = 3(r-1)/2 + x, so that F(r, r-1+x) = s_r f_r(x)."""
    return Fraction(3 * (R - 1), 2) + x


def transitions():
    """q[x][y] for the interior states x = 1, ..., 3r-1."""
    q = {}
    for x in range(1, TOP):
        h = min(x, TOP - x)
        d = h + 1
        q[x] = {y: f(y) / (d * f(x)) for y in range(x - h, x + h + 1, 2)}
    return q


def solve(matrix, rhs):
    """Gauss-Jordan elimination over the rationals."""
    n = len(rhs)
    a = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        piv = next(i for i in range(col, n) if a[i][col] != 0)
        a[col], a[piv] = a[piv], a[col]
        pv = a[col][col]
        a[col] = [v / pv for v in a[col]]
        for i in range(n):
            if i != col and a[i][col] != 0:
                fac = a[i][col]
                a[i] = [vi - fac * vc for vi, vc in zip(a[i], a[col])]
    return [a[i][n] for i in range(n)]


def occupations(q):
    """Expected visits to states 1..3r of the walk started at INJECTION.

    State 0 absorbs; state 3r returns to state 1 (a tripling).  The visit
    vector v satisfies v = e_in + v P on the transient states 1..3r.
    """
    states = list(range(1, TOP + 1))
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    P = [[Fraction(0)] * n for _ in range(n)]
    for x, children in q.items():
        for y, p in children.items():
            if y >= 1:
                P[idx[x]][idx[y]] += p
    P[idx[TOP]][idx[1]] = Fraction(1)
    # (I - P^T) v = e_in
    mat = [[(Fraction(1) if i == j else Fraction(0)) - P[j][i]
            for j in range(n)] for i in range(n)]
    rhs = [Fraction(1) if s == INJECTION else Fraction(0) for s in states]
    v = solve(mat, rhs)
    lam = {x: v[idx[x]] for x in range(1, TOP)}
    mu = v[idx[TOP]]
    return lam, mu


def multinomial(parts):
    out = factorial(sum(parts))
    for p in parts:
        out //= factorial(p)
    return out


def roundings(K, q, lam, mu):
    """All integer circulations with floor <= psi_e <= ceil on every edge.

    Edges: transition edges x -> y, the tripling edge 3r -> 1 and the
    return edge 0 -> injection state (target K, an integer, so fixed).
    """
    edges = [(x, y) for x in q for y in q[x]] + [(TOP, 1)]
    target = {(x, y): K * lam[x] * q[x][y] for x in q for y in q[x]}
    target[(TOP, 1)] = K * mu
    choices = [sorted({floor(target[e]), ceil(target[e])}) for e in edges]
    for combo in product(*choices):
        psi = dict(zip(edges, combo))
        balance = [0] * (TOP + 1)
        for (x, y), c in psi.items():
            balance[x] += c
            balance[y] -= c
        balance[0] += K           # return edge 0 -> injection state
        balance[INJECTION] -= K
        if all(b == 0 for b in balance):
            yield psi


def sides(K, q, psi, N=1):
    """Exact integers A_1 and B_1 of eq:dimensions."""
    A1 = 1
    M = 1
    for x in q:
        counts = [psi[(x, y)] for y in q[x]]
        w = sum(counts)
        if w == 0:
            continue            # inactive split
        d = min(x, TOP - x) + 1
        A1 *= d ** (N * w)
        M *= multinomial([N * c for c in counts])
    z = N * psi[(TOP, 1)]
    m = (z + 1) // 3
    M *= comb(z, m) * 2 ** (z - m)
    B1 = 2 ** (N * K) * M
    return A1, B1


def main():
    q = transitions()
    lam, mu = occupations(q)
    print("occupations (row 2, injection at state 1):",
          {x: str(v) for x, v in lam.items()}, "mu =", mu)
    print()
    print(" K  #roundings  all B1<A1  all B1>A1  min Delta_1  max Delta_1")
    for K in range(1, K_MAX + 1):
        rows = []
        for psi in roundings(K, q, lam, mu):
            A1, B1 = sides(K, q, psi)
            rows.append((A1, B1, log(B1) - log(A1)))
        neg = all(B1 < A1 for A1, B1, _ in rows)
        pos = all(B1 > A1 for A1, B1, _ in rows)
        lo = min(r[2] for r in rows)
        hi = max(r[2] for r in rows)
        print(f"{K:2d}  {len(rows):10d}  {str(neg):>9}  {str(pos):>9}"
              f"  {lo:11.4f}  {hi:11.4f}")
    print()
    claim = all(
        all(B1 < A1 for A1, B1 in
            (sides(K, q, psi) for psi in roundings(K, q, lam, mu)))
        for K in range(1, 8))
    print("Claim: for a=2, N=1 and every K<=7, every allowed rounding has "
          "B_1 < A_1 (Delta_1 < 0):", claim)

    # Example ex:ledger-a2 at K = 15
    K = 15
    rs = list(roundings(K, q, lam, mu))
    assert len(rs) == 1, "K=15 should leave every target unchanged"
    psi = rs[0]
    A1, B1 = sides(K, q, psi)
    print()
    print("K = 15 counts:", {f"{x}->{y}": c for (x, y), c in psi.items()
                             if c > 0})
    print("A_1 == 2^30 3^75:", A1 == 2 ** 30 * 3 ** 75)
    print(f"Delta_1 = {log(B1) - log(A1):.4f}")
    s2 = Fraction(4, 3)      # s_2 = 1 + 1/3, and F(2,2) = s_2 f_2(1)
    G = K * log(s2 * f(1))
    print("F(2,2) =", s2 * f(1), f"; G = 15 log F(2,2) = {G:.4f}")
    T1 = 0.0
    for x in q:
        counts = [psi[(x, y)] for y in q[x]]
        w = sum(counts)
        if w:
            T1 += (sum(1 for c in counts if c > 0) - 1) * log(w + 1)
    z = psi[(TOP, 1)]
    if z:
        T1 += log(z + 1)
    print(f"T_1 = {T1:.4f}; G - T_1 = {G - T1:.4f}")
    # every empirical distribution equals q, so the rounding loss is zero
    exact = all(psi[(x, y)] == K * lam[x] * q[x][y] for x in q for y in q[x])
    print("counts equal K lambda q exactly (rounding loss 0):", exact)


if __name__ == "__main__":
    main()
