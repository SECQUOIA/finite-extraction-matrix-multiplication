"""Adversarial exact checks for docs/shifted-chains-check-literature.md.

These checks are written independently of
experiments/shifted_chains_check_literature.py.  They use only integers and
Fraction.  They test the fragile steps of the literature note:

1. fibers: every kernel vector of the shifted map lives in one exponent
   fiber, where the basis is "first component" plus adjacent differences;
   this proves unimodularity for all parameters (the checker only computed
   determinants on 90 cases);
2. blocks: the block structure of multiplication by z^alpha, computed with
   the explicit inverse (lift plus a path of differences) instead of
   Gaussian elimination, on a larger grid;
3. forms: ker Q = Delta_h (V_{b-h} (x) V'_{d-1}) by multiplying forms in
   four variables, for every h < b;
4. class restriction: the combined stage (split, crop, OpenAI's
   three-interval reset with (a, h) = (r, c)) with class weights K=2,
   L=R=1, M=0 is block triangular with no coefficient between different
   labels of one class; brute force on tensor squares and cubes confirms
   that a class-type restriction leaves only matched words and that the
   number of words is formula (4) of the round-8 note;
5. Uznanski v2 Appendix A: his coordinates p = a + t b, h = b - p_{e+1} t^e
   and his formula for multiplication by f are the shifted map with
   d = 2 and h = 1;
6. concavity: d P(b) - P(B) - (d-1) P(c) is a nonnegative combination of
   second differences (tent coefficients), so it holds for every concave
   row; v5's least profile F satisfies every legal round-11 stage
   inequality d F(r,b) >= (d+2) F(r,c), with equality on the ramp;
7. ramp: the round-11 product equals F(R,R), each ramp pair has the factor
   of OpenAI's (5.1) with equality, and the round-11 positivity
   coefficients are as stated; F(m,n)^3 <= (m+n-1)^4.

Run from the repository root:
    python -I experiments/shifted_chains_skeptic_literature.py
"""

from __future__ import annotations

import itertools
from collections import defaultdict
from fractions import Fraction
from math import factorial


# --------------------------------------------------------------- shifted map


def fiber(i: int, length: int, d: int, h: int) -> list[int]:
    """Components j whose block [j h, j h + length) contains exponent i."""
    return [j for j in range(d) if 0 <= i - j * h < length]


def coords(vec: dict[tuple[int, int], int], length: int, d: int, h: int) -> dict:
    """Coordinates in the lift/kernel basis via the explicit inverse.

    e_(j, beta) = lift(i) + sum_{j' = jmin(i)}^{j-1} kappa_(j', i - (j'+1) h),
    with i = j h + beta.  Keys: ('q', i) and ('k', j', k).
    """
    out: dict = defaultdict(int)
    for (j, beta), coef in vec.items():
        if coef == 0:
            continue
        i = j * h + beta
        out[("q", i)] += coef
        jmin = fiber(i, length, d, h)[0]
        for jp in range(jmin, j):
            out[("k", jp, i - (jp + 1) * h)] += coef
    return {key: v for key, v in out.items() if v}


def check_fibers(length: int, d: int, h: int) -> None:
    """Unimodularity for all parameters: each fiber is a path of components."""
    c = length - h
    big = length + (d - 1) * h
    seen = set()
    for i in range(big):
        comps = fiber(i, length, d, h)
        assert comps and comps == list(range(comps[0], comps[-1] + 1))  # contiguous
        # kernel vectors kappa_(j,k) at exponent (j+1) h + k = i
        kap = [(j, i - (j + 1) * h) for j in range(d - 1) if 0 <= i - (j + 1) * h < c]
        assert [j for j, _ in kap] == comps[:-1], (i, comps, kap)
        seen.update(kap)
    assert len(seen) == (d - 1) * c
    # within a fiber with components j0 < ... < jm the basis is
    # e_j0, e_j1 - e_j0, ..., e_jm - e_j(m-1): unitriangular, determinant 1.


def check_blocks(r: int, b: int, d: int, h: int) -> bool:
    """Block structure of multiplication by z^alpha; returns 'off-diagonal seen'."""
    c, zl = b - h, b + r - 1
    big = b + (d - 1) * h
    off = False
    for alpha in range(r):
        # quotient input: lift(i) = e_(jmin(i), i - jmin h)
        for i in range(big):
            j = fiber(i, b, d, h)[0]
            prod = {(j, i - j * h + alpha): 1}
            co = coords(prod, zl, d, h)
            assert co.pop(("q", i + alpha)) == 1
            assert all(key[0] == "k" for key in co)  # only kernel off-diagonal part
            off = off or bool(co)
        # kernel input kappa_(j,k) = -e_(j, h+k) + e_(j+1, k)
        for j in range(d - 1):
            for k in range(c):
                prod = {(j, h + k + alpha): -1, (j + 1, k + alpha): 1}
                assert coords(prod, zl, d, h) == {("k", j, k + alpha): 1}
    return off


def poly_mul(p: dict, q: dict) -> dict:
    out: dict = defaultdict(int)
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            out[tuple(a + b2 for a, b2 in zip(e1, e2))] += c1 * c2
    return {e: v for e, v in out.items() if v}


def check_forms(b: int, d: int, h: int) -> None:
    """kappa_(j,k) = Delta_h * (u^(c-1-k) v^k (x) u'^(d-2-j) v'^j), exponents (u,v,u',v')."""
    c = b - h
    delta_h = {(h, 0, 0, 1): 1, (0, h, 1, 0): -1}  # u^h v' - v^h u'
    for j in range(d - 1):
        for k in range(c):
            form = poly_mul(delta_h, {(c - 1 - k, k, d - 2 - j, j): 1})
            vec = {}
            for (eu, ev, eu2, ev2), coef in form.items():
                assert eu + ev == b - 1 and eu2 + ev2 == d - 1  # lies in V_b (x) V'_d
                vec[(ev2, ev)] = coef  # component = exponent of v', position = exponent of v
            assert vec == {(j, h + k): -1, (j + 1, k): 1}


# ------------------------------------------------- combined class restriction


def stage_tensor(r: int, b: int, d: int, h: int):
    """Adapted-basis coefficients of the cropped stage, with class labels."""
    c, zl = b - h, b + r - 1
    big = b + (d - 1) * h
    crop_y, crop_z = 3 * c + r - 1, 3 * c + 2 * r - 2
    assert big >= crop_y

    def ylab(key):
        if key[0] == "k":
            return ("K", key[1])
        i = key[1]
        return "L" if i <= c - 1 else ("M" if i <= 2 * c + r - 2 else "R")

    def zlab(key):
        if key[0] == "k":
            return ("K", key[1])
        i = key[1]
        return "L" if i <= c + r - 2 else ("M" if i <= 2 * c + r - 2 else "R")

    ys = [("q", i) for i in range(crop_y)] + [("k", j, k) for j in range(d - 1) for k in range(c)]
    terms = []  # (alpha, y, z, coef)
    for alpha in range(r):
        for y in ys:
            if y[0] == "q":
                j = fiber(y[1], b, d, h)[0]
                prod = {(j, y[1] - j * h + alpha): 1}
            else:
                _, j, k = y
                prod = {(j, h + k + alpha): -1, (j + 1, k + alpha): 1}
            for z, coef in coords(prod, zl, d, h).items():
                if z[0] == "q" and z[1] >= crop_z:
                    continue  # cropped output coordinate
                terms.append((alpha, y, z, coef))
    return terms, ylab, zlab


WEIGHT = {"K": 2, "L": 1, "R": 1, "M": 0}


def cls(label) -> str:
    return label[0] if isinstance(label, tuple) else label


def klass(label) -> str:
    """Class of a label: kernel K, outer O (L or R), middle M."""
    lab = cls(label)
    return "O" if lab in ("L", "R") else lab


def check_class_restriction(r: int, b: int, d: int, h: int, powers: tuple[int, ...]) -> int:
    terms, ylab, zlab = stage_tensor(r, b, d, h)
    c = b - h
    diag = defaultdict(int)
    for alpha, y, z, coef in terms:
        ly, lz = ylab(y), zlab(z)
        wy, wz = WEIGHT[cls(ly)], WEIGHT[cls(lz)]
        if ly == lz:
            assert coef == 1
            diag[ly] += 1
        else:
            assert wz > wy, (r, b, d, h, alpha, y, z, ly, lz)  # strictly increases weight
    # each diagonal block has r*c terms (C(r,c) or its (23)-transpose)
    labels = ["L", "M", "R"] + [("K", j) for j in range(d - 1)]
    assert all(diag[lab] == r * c for lab in labels), diag
    # brute-force tensor powers with a fixed class type
    checked = 0
    for n in powers:
        for nk in range(n + 1):
            for no in range(n + 1 - nk):
                nm = n - nk - no
                want = (nk, no, nm)
                words = set()
                for combo in itertools.product(terms, repeat=n):
                    yw = tuple(ylab(t[1]) for t in combo)
                    zw = tuple(zlab(t[2]) for t in combo)
                    tyy = tuple(sum(klass(x) == s for x in yw) for s in ("K", "O", "M"))
                    tzz = tuple(sum(klass(x) == s for x in zw) for s in ("K", "O", "M"))
                    if tyy != want or tzz != want:
                        continue
                    assert yw == zw, (yw, zw)  # only matched words survive
                    words.add(yw)
                expected = factorial(n) // (factorial(nk) * factorial(no) * factorial(nm))
                expected *= (d - 1) ** nk * 2 ** no
                assert len(words) == expected, (n, want, len(words), expected)
                checked += 1
    return checked


# ------------------------------------------------------------- Uznanski App. A


def check_uznanski_appendix_a(r: int, s: int) -> None:
    """p = a + t b, h = b - p_(e+1) t^e  with e = s-1; multiplication rule."""
    e = s - 1
    for a_idx in range(s):
        for comp in (0, 1):
            # basis input: a = t^a_idx (comp 0) or b = t^a_idx (comp 1)
            a = [0] * s
            bb = [0] * s
            (a if comp == 0 else bb)[a_idx] = 1
            p = [a[i] + (bb[i - 1] if i >= 1 else 0) for i in range(s)] + [bb[s - 1]]
            hh = bb[:]
            hh[e] -= p[e + 1]
            hh = hh[:e]  # deg h <= e-1
            assert len(p) == s + 1 and all(v == 0 for v in [bb[e] - p[e + 1]])
            # same as round-8 coordinates: quotient = Q(a,b) = a + z b,
            # kernel coordinate K with (a,b) = lift(p) + (-z K, K)
            co = coords({(0, i): a[i] for i in range(s)} | {(1, i): bb[i] for i in range(s)}, s, 2, 1)
            q = [co.get(("q", i), 0) for i in range(s + 1)]
            kk = [co.get(("k", 0, k), 0) for k in range(s - 1)]
            assert q == p and kk == hh, (q, p, kk, hh)
    # multiplication rule (p,h) -> (f p, f h + p_s t^(s-1) (f - f_(r-1) t^(r-1)))
    for f_idx in range(r):
        f = [0] * r
        f[f_idx] = 1
        for comp in (0, 1):
            for a_idx in range(s):
                a = [0] * s
                bb = [0] * s
                (a if comp == 0 else bb)[a_idx] = 1
                fa = [sum(f[i] * a[k - i] for i in range(r) if 0 <= k - i < s) for k in range(r + s - 1)]
                fb = [sum(f[i] * bb[k - i] for i in range(r) if 0 <= k - i < s) for k in range(r + s - 1)]
                co_in = coords({(0, i): a[i] for i in range(s)} | {(1, i): bb[i] for i in range(s)}, s, 2, 1)
                co_out = coords({(0, i): fa[i] for i in range(r + s - 1)} | {(1, i): fb[i] for i in range(r + s - 1)}, r + s - 1, 2, 1)
                p = [co_in.get(("q", i), 0) for i in range(s + 1)]
                hh = [co_in.get(("k", 0, k), 0) for k in range(s - 1)]
                fp = [sum(f[i] * p[k - i] for i in range(r) if 0 <= k - i <= s) for k in range(r + s)]
                fh = [sum(f[i] * hh[k - i] for i in range(r) if 0 <= k - i < s - 1) for k in range(r + s - 2)]
                corr = [0] * (r + s - 2)
                g = f[:]
                g[r - 1] = 0  # f - f_(r-1) t^(r-1)
                for i in range(r - 1):
                    corr[s - 1 + i] += p[s] * g[i]
                want_k = [fh[k] + corr[k] for k in range(r + s - 2)]
                assert [co_out.get(("q", i), 0) for i in range(r + s)] == fp
                assert [co_out.get(("k", 0, k), 0) for k in range(r + s - 2)] == want_k


# ------------------------------------------------------------------ scalars


def s_val(m: int) -> Fraction:
    out = Fraction(1)
    for t in range(1, m):
        out *= Fraction(3 * t + 1, 3 * t)
    return out


def F(m: int, n: int) -> Fraction:
    lo, hi = min(m, n), max(m, n)
    return s_val(lo) * (hi + Fraction(lo - 1, 2))


def check_tent(bmax: int = 30, dmax: int = 10) -> int:
    """d P(b) - P(B) - (d-1) P(c) = sum_t lam_t (2P(t) - P(t-1) - P(t+1)), lam >= 0."""
    count = 0
    for b in range(2, bmax + 1):
        for h in range(1, b):
            c = b - h
            for d in range(2, dmax + 1):
                big = b + (d - 1) * h
                lam = {t: ((d - 1) * (t - c) if t <= b else big - t) for t in range(c + 1, big)}
                assert all(v >= 0 for v in lam.values())
                coef = defaultdict(int)
                for t, v in lam.items():
                    coef[t] += 2 * v
                    coef[t - 1] -= v
                    coef[t + 1] -= v
                target = defaultdict(int)
                target[b] += d
                target[big] -= 1
                target[c] -= d - 1
                assert {k: v for k, v in coef.items() if v} == {k: v for k, v in target.items() if v}
                count += 1
    return count


def check_profile_stage(rmax: int = 10, bmax: int = 36, dmax: int = 10) -> int:
    """F satisfies d F(r,b) >= (d+2) F(r,c) whenever (d+2) c <= d b - r + 1."""
    count = 0
    for r in range(1, rmax + 1):
        for b in range(2, bmax + 1):
            for d in range(2, dmax + 1):
                for c in range(1, b):
                    if (d + 2) * c <= d * b - r + 1:
                        assert d * F(r, b) >= (d + 2) * F(r, c), (r, b, c, d)
                        count += 1
    return count


def check_ramp(rmax: int = 120) -> None:
    prod = Fraction(1)
    for j in range(1, rmax):
        # two reverse steps (j,j) <-[d=3j-1]- (j,j+1) <-[d=3j]- (j+1,j+1), zero slack
        for d, (r, b), child in ((3 * j - 1, (j, j + 1), (j, j)), (3 * j, (j + 1, j + 1), (j, j + 1))):
            cc = child[0]
            assert (d + 2) * cc == d * b - r + 1  # legal with zero slack
            assert d * F(r, b) == (d + 2) * F(cc, r)  # tight for v5's F
        prod *= Fraction((3 * j + 1) * (3 * j + 2), (3 * j - 1) * (3 * j))
        assert prod == F(j + 1, j + 1)
        # OpenAI (5.1) with equality: D_a - D_(a-1) = H_(a-1) + H_a, H_a = 2 D_a/(3a-1)
        a = j + 1
        Da, Db = F(a, a), F(a - 1, a - 1)
        assert Da - Db == 2 * Db / (3 * a - 4) + 2 * Da / (3 * a - 1)


def round11_coefficients() -> list[int]:
    """Coefficients of (j^4[(3j+1)(3j+2)]^3 - (j+1)^4[(3j-1)3j]^3)/j^3 in u = j-1."""
    # Work with exact integer polynomials in j, then shift.
    def pmul(p, q):
        out = [0] * (len(p) + len(q) - 1)
        for i, x in enumerate(p):
            for k, y in enumerate(q):
                out[i + k] += x * y
        return out

    def ppow(p, k):
        out = [1]
        for _ in range(k):
            out = pmul(out, p)
        return out

    j = [0, 1]
    a = pmul(ppow(j, 4), ppow(pmul([1, 3], [2, 3]), 3))
    bpoly = pmul(ppow([1, 1], 4), ppow(pmul([-1, 3], [0, 3]), 3))
    n = max(len(a), len(bpoly))
    diff = [(a[i] if i < len(a) else 0) - (bpoly[i] if i < len(bpoly) else 0) for i in range(n)]
    while diff and diff[-1] == 0:
        diff.pop()
    assert diff[:3] == [0, 0, 0]  # divisible by j^3
    q = diff[3:]
    # substitute j = u + 1: sum q_k (u+1)^k
    out = [0] * len(q)
    for k, coef in enumerate(q):
        for i, binom in enumerate(ppow([1, 1], k)):
            out[i] += coef * binom
    return out


def check_profile_upper(nmax: int = 60) -> None:
    for m in range(1, nmax + 1):
        for n in range(1, nmax + 1):
            assert F(m, n) ** 3 <= (m + n - 1) ** 4


def main() -> None:
    fib = blk = 0
    for b in range(2, 9):
        for d in range(2, 7):
            for h in range(1, b):
                check_fibers(b, d, h)
                check_forms(b, d, h)
                fib += 1
                for r in range(1, 5):
                    off = check_blocks(r, b, d, h)
                    assert off == (r >= 2)
                    blk += 1
    print(f"fibers and forms (unimodularity for all parameters; Delta_h kernel): {fib} cases, b<=8, d<=6")
    print(f"block structure via explicit inverse: {blk} cases, r<=4; off-diagonal iff r>=2")

    single = 0
    for r in range(1, 4):
        for b in range(2, 9):
            for d in range(2, 6):
                for h in range(1, b):
                    c = b - h
                    if b + (d - 1) * h >= 3 * c + r - 1:
                        check_class_restriction(r, b, d, h, powers=())
                        single += 1
    print(f"class weights (K=2, L=R=1, M=0) on split+crop+reset: {single} stages, single-copy property")
    power_cases = 0
    for (r, b, d, h) in [(1, 2, 3, 1), (2, 2, 3, 1), (2, 3, 3, 2), (2, 4, 4, 2), (3, 3, 3, 2)]:
        power_cases += check_class_restriction(r, b, d, h, powers=(2,))
    for (r, b, d, h) in [(1, 2, 3, 1), (2, 2, 3, 1)]:
        power_cases += check_class_restriction(r, b, d, h, powers=(3,))
    print(f"brute-force class-type restriction on tensor squares/cubes: {power_cases} types; formula (4) confirmed")

    for r in range(1, 5):
        for s in range(2, 6):
            check_uznanski_appendix_a(r, s)
    print("Uznanski v2 Appendix A coordinates and multiplication rule = shifted map (d=2, h=1): r<=4, s<=5")

    print(f"tent coefficients (proof of the concavity step for every concave row): {check_tent()} cases")
    print(f"least profile F satisfies all legal stage inequalities: {check_profile_stage()} cases")
    check_ramp()
    coeffs = round11_coefficients()
    assert coeffs == [4544, 17936, 27324, 20007, 7074, 972], coeffs
    print("ramp: product = F(R,R), every ramp step tight for F, OpenAI (5.1) with equality; "
          f"round-11 coefficients {coeffs}")
    check_profile_upper()
    print("F(m,n)^3 <= (m+n-1)^4 for m,n <= 60")
    print("all skeptic checks passed")


if __name__ == "__main__":
    main()
