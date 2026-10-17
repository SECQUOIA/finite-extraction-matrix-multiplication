"""Numbers quoted in Section 5 (flows.tex) of the rewritten paper.

1. Example row-two: exact rational occupations of the row walk of row r=2
   (fractions.Fraction, exact Gaussian elimination).
2. Remark occupation-constants: floating-point evaluation (numpy, float64)
   of the row sums sum_x lambda_{r,x} and sum_x lambda_{r,x} log d_{r,x}
   for 2 <= r <= 120, for the final row (injection state 1) and a lower row
   (injection state 2).

The row walk: states 0..3r; interior x has width h=min(x,3r-x), d=h+1,
children y = x-h, x-h+2, ..., x+h with probability f(y)/(d f(x)),
f(x) = 3(r-1)/2 + x; state 3r moves to 1 (tripling); state 0 absorbs.
Occupations: v=(lambda_1..lambda_{3r-1}, mu) solves (Id - Pi^T) v = e_xin.
Self-contained; reads no files. Run: python3 -I flows_row_maxima.py
"""
import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

from fractions import Fraction
import math
import numpy as np


def transitions(r):
    n = 3 * r
    c = Fraction(3 * (r - 1), 2)
    rows = {}
    for x in range(1, n):
        h = min(x, n - x)
        d = h + 1
        rows[x] = {y: (c + y) / (d * (c + x)) for y in range(x - h, x + h + 1, 2)}
    return rows


def exact_occupations(r, xin):
    n = 3 * r
    q = transitions(r)
    # unknowns v[1..n], v[n] = mu; equation for coordinate y in 1..n:
    # v_y - sum_x v_x Pi[x][y] = [y == xin]
    A = [[Fraction(0)] * (n + 1) for _ in range(n)]
    for y in range(1, n + 1):
        A[y - 1][y - 1] += 1
        A[y - 1][n] = Fraction(int(y == xin))
    for x in range(1, n):
        for y, p in q[x].items():
            if y >= 1:
                A[y - 1][x - 1] -= p
    A[0][n - 1] -= 1  # tripling 3r -> 1
    for i in range(n):  # Gauss-Jordan
        piv = next(k for k in range(i, n) if A[k][i] != 0)
        A[i], A[piv] = A[piv], A[i]
        inv = 1 / A[i][i]
        A[i] = [a * inv for a in A[i]]
        for k in range(n):
            if k != i and A[k][i] != 0:
                fac = A[k][i]
                A[k] = [a - fac * b for a, b in zip(A[k], A[i])]
    v = [A[i][n] for i in range(n)]
    return v[: n - 1], v[n - 1]


def float_sums(r, xin):
    n = 3 * r
    c = 1.5 * (r - 1)
    Pi = np.zeros((n, n))
    for x in range(1, n):
        h = min(x, n - x)
        d = h + 1
        for y in range(x - h, x + h + 1, 2):
            if y >= 1:
                Pi[x - 1, y - 1] += (c + y) / (d * (c + x))
    Pi[n - 1, 0] = 1.0
    e = np.zeros(n)
    e[xin - 1] = 1.0
    v = np.linalg.solve(np.eye(n) - Pi.T, e)
    lam = v[: n - 1]
    logd = np.array([math.log(min(x, n - x) + 1) for x in range(1, n)])
    return float(lam.sum()), float((lam * logd).sum()), float(v[n - 1])


def main():
    print("Example row-two (exact):")
    for xin in (1, 2):
        lam, mu = exact_occupations(2, xin)
        logsum = " + ".join(
            f"({l})*log({min(x, 6 - x) + 1})" for x, l in enumerate(lam, 1) if l
        )
        print(f"  xin={xin}: lambda_1..5 = {[str(l) for l in lam]}, mu = {mu},"
              f" total = {sum(lam)}")
        val = sum(float(l) * math.log(min(x, 6 - x) + 1) for x, l in enumerate(lam, 1))
        print(f"    sum lambda log d = {logsum} = {val:.6f}")
    print("Remark occupation-constants (float64 evaluation, 2 <= r <= 120):")
    for xin, name in ((1, "final row"), (2, "lower row")):
        res = [(r,) + float_sums(r, xin) for r in range(2, 121)]
        s = max(res, key=lambda t: t[1])
        ls = max(res, key=lambda t: t[2])
        print(f"  {name}: max sum lambda = {s[1]:.6f} at r={s[0]};"
              f" max sum lambda log d = {ls[2]:.6f} at r={ls[0]};"
              f" max mu = {max(t[3] for t in res):.6f}")
        second = sorted(res, key=lambda t: -t[1])[1]
        print(f"    second largest sum lambda = {second[1]:.6f} at r={second[0]}")


if __name__ == "__main__":
    main()
