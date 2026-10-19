"""Exact checks for the shifted-chain local maps, the one-stage restriction,
and the chain counts.

This script imports nothing from earlier rounds. Every identity is checked
with Python integers or fractions.Fraction. Floating point is not used for
any identity; the optional exponent comparisons in section 9 use the
decimal module at 60 significant digits only to compare with earlier
reported numbers and are not certificates.

Sections
  1. physical tensors C(r,b) and C(r,b)B_X(d)
  2. shifted-chain bases, their integer inverses, and the quotient map Q
  3. the transformed tensor: block-triangular structure (Lemma shifted chain)
  4. crop and reset labels, weights, and diagonal blocks (Lemma reset)
  5. tensor powers: cross-term deletion, sectors, reindexing to the
     canonical sector tensor, and an independent route through the
     physical tensor power (Lemma stage restriction)
  6. the rational polynomial separator, interpolation and exactification
     identities of v5 Lemma 9.1, checked on small sizes
  7. orientation bookkeeping for the paired inventory Q_{r,b}
  8. legal steps, smallest parents, the zero-slack ramp, the two-stage cycle
  9. chain counts: composition bookkeeping and comparison with the
     round-8 and round-11 reported numbers

Run from the repository root:
    python -I experiments/shifted_chains_check_maps.py
"""

from collections import Counter, defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial, prod
import json
import sys
import time

# ---------------------------------------------------------------------------
# 1. Physical tensors
# ---------------------------------------------------------------------------


def conv(r, b):
    """C(r,b) = sum x_a y_beta z_{a+beta} as a sparse dict."""
    return {(a, beta, a + beta): 1 for a in range(r) for beta in range(b)}


def swap23(tensor):
    return {(k[0], k[2], k[1]): v for k, v in tensor.items()}


def physical(r, b, d):
    """C(r,b) B_X(d): multiplication of P (r coefficients) by d polynomials
    F_0..F_{d-1} of b coefficients each.  Second-leg index p*b+beta,
    third-leg index p*(b+r-1)+gamma.  The B_X(d) first leg is one-dimensional,
    so the first-leg index is just a."""
    out = b + r - 1
    return {(a, p * b + beta, p * out + a + beta): 1
            for a in range(r) for beta in range(b) for p in range(d)}


# ---------------------------------------------------------------------------
# 2. Shifted-chain bases
# ---------------------------------------------------------------------------


def earliest_component(e, length, h, d):
    for p in range(d):
        if p * h <= e <= p * h + length - 1:
            return p
    raise ValueError("exponent not covered")


def chain_basis(length, h, d):
    """Basis of F^{d*length} = d components of `length` coefficients.

    New coordinates: quotient lifts 0..Bq-1, then kernel (j,i) at
    Bq + j*child + i, with child = length - h.
    Returns (forward, inverse, Bq, child):
      forward[u] = {physical index: coefficient} (column u of the basis matrix)
      inverse[phys] = {new index: coefficient} (coordinates of a physical
                       monomial in the new basis)."""
    child = length - h
    bq = length + (d - 1) * h
    forward = []
    for e in range(bq):
        p0 = earliest_component(e, length, h, d)
        forward.append({p0 * length + (e - p0 * h): 1})
    for j in range(d - 1):
        for i in range(child):
            forward.append({j * length + i + h: -1, (j + 1) * length + i: 1})
    inverse = []
    for p in range(d):
        for m in range(length):
            e = p * h + m
            p0 = earliest_component(e, length, h, d)
            coords = {e: 1}
            for j in range(p0, p):
                i = m + (p - 1 - j) * h
                assert 0 <= i < child
                coords[bq + j * child + i] = 1
            inverse.append(coords)
    return forward, inverse, bq, child


def dense_from_columns(columns, nrows):
    mat = [[0] * len(columns) for _ in range(nrows)]
    for col, vec in enumerate(columns):
        for row, val in vec.items():
            mat[row][col] = val
    return mat


def matmul(a, b):
    n, m, p = len(a), len(b), len(b[0])
    return [[sum(a[i][k] * b[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def check_chain_basis(length, h, d):
    """Unimodularity, coefficient sets, and the exact sequence."""
    forward, inverse, bq, child = chain_basis(length, h, d)
    n = d * length
    assert len(forward) == n and bq + (d - 1) * child == n
    pi = dense_from_columns(forward, n)          # physical x new
    pinv = dense_from_columns(inverse, n)        # new x physical
    assert matmul(pi, pinv) == identity(n)
    assert matmul(pinv, pi) == identity(n)
    assert {v for col in forward for v in col.values()} <= {-1, 1}
    assert {v for col in inverse for v in col.values()} == {1}
    assert sum(len(c) for c in forward) == d * length + (d - 1) * child
    # Q(F_0..F_{d-1}) = sum_j z^{jh} F_j, as a bq x n matrix
    qmat = [[0] * n for _ in range(bq)]
    for p in range(d):
        for m in range(length):
            qmat[p * h + m][p * length + m] = 1
    qpi = matmul(qmat, pi)
    expected = [[int(i == j) if j < bq else 0 for j in range(n)]
                for i in range(bq)]
    assert qpi == expected   # lifts map to monomials, kernel vectors to 0
    return forward, inverse, bq, child


# ---------------------------------------------------------------------------
# 3. Transformed tensor
# ---------------------------------------------------------------------------


def stage_tensor(r, b, c, d):
    """Coefficients of C(r,b)B_X(d) in the shifted-chain bases:
    second leg y = Pi_in y', third leg z = Pi_out^{-T} z'."""
    h = b - c
    fin, _, bq, child = check_chain_basis(b, h, d)
    _, gout, bq_out, child_out = check_chain_basis(b + r - 1, h, d)
    assert bq == d * b - (d - 1) * c and child == c
    assert bq_out == bq + r - 1 and child_out == c + r - 1
    rows_in = [[] for _ in range(d * b)]
    for u, col in enumerate(fin):
        for phys, val in col.items():
            rows_in[phys].append((u, val))
    tensor = Counter()
    for (a, beta, gamma), coef in physical(r, b, d).items():
        for u, fu in rows_in[beta]:
            for v, gv in gout[gamma].items():
                tensor[a, u, v] += coef * fu * gv
    return {k: v for k, v in tensor.items() if v}, rows_in, gout, bq


def check_shifted_chain(r, b, c, d):
    """Lemma shifted chain: diagonal blocks C(r,B) and (d-1) C(r,c);
    kernel->quotient zero; quotient->kernel coefficients in {1}."""
    tensor, _, _, bq = stage_tensor(r, b, c, d)
    bq_out = bq + r - 1
    co = c + r - 1

    def kind_in(u):
        return ("q", u) if u < bq else ("k",) + divmod(u - bq, c)

    def kind_out(v):
        return ("q", v) if v < bq_out else ("k",) + divmod(v - bq_out, co)

    offdiag = 0
    diag = Counter()
    for (a, u, v), val in tensor.items():
        ku, kv = kind_in(u), kind_out(v)
        if ku[0] == "q" and kv[0] == "q":
            assert kv[1] == ku[1] + a and val == 1
            diag["q"] += 1
        elif ku[0] == "k" and kv[0] == "k":
            assert ku[1] == kv[1] and kv[2] == ku[2] + a and val == 1
            diag["k"] += 1
        elif ku[0] == "k" and kv[0] == "q":
            raise AssertionError("kernel input reached quotient output")
        else:
            assert val == 1
            offdiag += 1
    assert diag["q"] == r * bq and diag["k"] == (d - 1) * r * c
    return offdiag


# ---------------------------------------------------------------------------
# 4. Crop and reset labels
# ---------------------------------------------------------------------------

WEIGHT = {"L": 1, "R": 1, "M": 0}


def weight(label):
    return 2 if label[0] == "K" else WEIGHT[label]


def klass(label):
    return "K" if label[0] == "K" else ("M" if label == "M" else "O")


def legal(r, b, c, d):
    return 1 <= c < b and (d + 2) * c <= d * b - r + 1


def make_labels(r, b, c, d):
    bq = d * b - (d - 1) * c
    assert bq >= 3 * c + r - 1
    bq_out = bq + r - 1

    def lab_in(u):
        if u < bq:
            if u < c:
                return ("L", u)
            if u <= 2 * c + r - 2:
                return ("M", u - c)
            if u <= 3 * c + r - 2:
                return ("R", u - (2 * c + r - 1))
            return None                                  # cropped away
        j, i = divmod(u - bq, c)
        return ("K%d" % j, i)

    def lab_out(v):
        if v < bq_out:
            if v <= c + r - 2:
                return ("L", v)
            if v <= 2 * c + r - 2:
                return ("M", v - (c + r - 1))
            if v <= 3 * c + 2 * r - 3:
                return ("R", v - (2 * c + r - 1))
            return None                                  # cropped away
        j, i = divmod(v - bq_out, c + r - 1)
        return ("K%d" % j, i)

    return lab_in, lab_out


def block(label, r, c):
    """Claimed diagonal block in local coordinates (a, (label,i), (label,i'))."""
    if label == "M":
        return {(a, (label, (r - 1 - a) + g), (label, g)): 1
                for a in range(r) for g in range(c)}
    return {(a, (label, i), (label, i + a)): 1
            for a in range(r) for i in range(c)}


def alphabet(d):
    return ["K%d" % j for j in range(d - 1)] + ["L", "R", "M"]


def kept_entries(r, b, c, d):
    """Single-position check of crop + reset + weights; returns kept entries."""
    tensor, _, _, _ = stage_tensor(r, b, c, d)
    lab_in, lab_out = make_labels(r, b, c, d)
    entries = []
    blocks = defaultdict(dict)
    cross = Counter()
    for (a, u, v), val in tensor.items():
        li, lo = lab_in(u), lab_out(v)
        if li is None or lo is None:
            continue
        entries.append((a, li, lo, val))
        if li[0] == lo[0]:
            blocks[li[0]][a, li, lo] = val
        else:
            assert weight(lo[0]) > weight(li[0]), (li, lo)
            cross[klass(li[0]), klass(lo[0])] += 1
    for label in alphabet(d):
        assert blocks[label] == block(label, r, c), label
    # local identification of the blocks with C(r,c) and C(r,c)^(23)
    target = conv(r, c)
    target23 = swap23(target)
    for label in alphabet(d):
        image = {(r - 1 - a if label == "M" else a, li[1], lo[1]): v
                 for (a, li, lo), v in blocks[label].items()}
        assert image == (target23 if label == "M" else target)
    # with the crop, the quotient-to-quotient part is exactly C(r, 3c+r-1);
    # quotient coordinates are u < B and v < B+r-1, and B >= 3c+r-1
    q_diag = {(a, u, v): val for (a, u, v), val in tensor.items()
              if u < 3 * c + r - 1 and v < 3 * c + 2 * r - 2}
    assert q_diag == conv(r, 3 * c + r - 1)
    return entries, cross


# ---------------------------------------------------------------------------
# 5. Tensor powers
# ---------------------------------------------------------------------------


def type_of(word):
    cnt = Counter(klass(lab) for lab in word)
    return (cnt["K"], cnt["O"], cnt["M"])


def words_of_type(d, n, tau):
    return [w for w in product(alphabet(d), repeat=n) if type_of(w) == tau]


def sector_count(d, tau):
    nk, no, nm = tau
    n = nk + no + nm
    return factorial(n) // (factorial(nk) * factorial(no) * factorial(nm)) \
        * (d - 1) ** nk * 2 ** no


def tensor_product(factors):
    """Product of sparse 3-leg tensors with keys (a, y, z); result keys are
    tuples of per-position indices."""
    result = {((), (), ()): 1}
    for f in factors:
        nxt = {}
        for (xa, ya, za), va in result.items():
            for (xb, yb, zb), vb in f.items():
                nxt[xa + (xb,), ya + (yb,), za + (zb,)] = va * vb
        result = nxt
    return result


def retained_from_entries(entries, n, tau):
    """Restriction of the n-th power to words of type tau on legs 2 and 3,
    using product bases: the coefficient is the product of the coefficients."""
    groups = defaultdict(list)
    for a, li, lo, val in entries:
        groups[li[0], lo[0]].append((a, li, lo, val))
    result = Counter()
    for combo in product(list(groups), repeat=n):
        if type_of([p[0] for p in combo]) != tau:
            continue
        if type_of([p[1] for p in combo]) != tau:
            continue
        for terms in product(*(groups[p] for p in combo)):
            key = (tuple(t[0] for t in terms), tuple(t[1] for t in terms),
                   tuple(t[2] for t in terms))
            result[key] += prod(t[3] for t in terms)
    return {k: v for k, v in result.items() if v}


def claimed_retained(r, c, d, n, tau):
    total = {}
    words = words_of_type(d, n, tau)
    for w in words:
        part = tensor_product([block(lab, r, c) for lab in w])
        for key, val in part.items():
            assert key not in total
            total[key] = val
    return total, words


def canonical_sector(r, c, n, nm):
    target = conv(r, c)
    return tensor_product([target] * (n - nm) + [swap23(target)] * nm)


def reindex_sector(sector, word, r):
    """Word-dependent reordering (ordinary positions first, middle last, each
    in original order) and first-index reversal at middle positions."""
    ordinary = [t for t, lab in enumerate(word) if lab != "M"]
    middle = [t for t, lab in enumerate(word) if lab == "M"]
    perm = ordinary + middle
    image = {}
    for (xs, ys, zs), val in sector.items():
        key = (tuple(r - 1 - xs[t] if word[t] == "M" else xs[t] for t in perm),
               tuple(ys[t][1] for t in perm), tuple(zs[t][1] for t in perm))
        assert key not in image
        image[key] = val
    return image


def check_power(r, b, c, d, n, tau, entries):
    retained = retained_from_entries(entries, n, tau)
    claimed, words = claimed_retained(r, c, d, n, tau)
    assert retained == claimed
    assert len(words) == sector_count(d, tau)
    sectors = defaultdict(dict)
    for (xs, ys, zs), val in retained.items():
        win = tuple(y[0] for y in ys)
        wout = tuple(z[0] for z in zs)
        assert win == wout                      # no cross term survives
        sectors[win][xs, ys, zs] = val
    assert set(sectors) == set(words)
    canon = canonical_sector(r, c, n, tau[2])
    for w, sec in sectors.items():
        assert reindex_sector(sec, w, r) == canon
    # sector coordinates are disjoint on legs 2 and 3
    ys_seen, zs_seen = {}, {}
    for w, sec in sectors.items():
        for (_, ys, zs) in sec:
            assert ys_seen.setdefault(ys, w) == w
            assert zs_seen.setdefault(zs, w) == w
    return len(words), len(retained)


def physical_power_route(r, b, c, d, n, tau):
    """Independent route: expand the physical n-th power, transform with the
    Kronecker powers of the basis matrices, restrict by labels."""
    _, rows_in, gout, _ = stage_tensor(r, b, c, d)
    lab_in, lab_out = make_labels(r, b, c, d)
    phys = list(physical(r, b, d).items())
    result = Counter()
    for terms in product(phys, repeat=n):
        xs = tuple(t[0][0] for t in terms)
        coef0 = prod(t[1] for t in terms)
        ins = [rows_in[t[0][1]] for t in terms]
        outs = [list(gout[t[0][2]].items()) for t in terms]
        for us in product(*ins):
            li = [lab_in(u) for u, _ in us]
            if any(x is None for x in li) or type_of([x[0] for x in li]) != tau:
                continue
            cu = prod(fu for _, fu in us)
            for vs in product(*outs):
                lo = [lab_out(v) for v, _ in vs]
                if any(x is None for x in lo) or \
                        type_of([x[0] for x in lo]) != tau:
                    continue
                result[xs, tuple(li), tuple(lo)] += \
                    coef0 * cu * prod(gv for _, gv in vs)
    result = {k: v for k, v in result.items() if v}
    claimed, _ = claimed_retained(r, c, d, n, tau)
    assert result == claimed
    return len(result)


# ---------------------------------------------------------------------------
# 6. v5 Lemma 9.1: rational interpolation, separator, exactification
# ---------------------------------------------------------------------------


def poly_mul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, bb in enumerate(q):
            out[i + j] += a * bb
    return out


def lagrange(n, ell):
    """Coefficients of the Lagrange basis polynomial varpi_{n,ell}, nodes 1..n."""
    poly, den = [Fraction(1)], 1
    for lp in range(1, n + 1):
        if lp != ell:
            poly = poly_mul(poly, [Fraction(-lp), Fraction(1)])
            den *= ell - lp
    return [x / den for x in poly]


def peval(poly, x):
    return sum(cf * Fraction(x) ** i for i, cf in enumerate(poly))


def shifted_coefficient(poly, shift, k):
    """[xi^k] poly(shift + xi)."""
    return sum(comb(s, k) * Fraction(shift) ** (s - k) * poly[s]
               for s in range(k, len(poly)))


def check_rational_convolution(r, b):
    n = r + b - 1
    total = Counter()
    for ell in range(1, n + 1):
        lag = lagrange(n, ell)
        for a in range(r):
            for be in range(b):
                for g in range(n):
                    total[a, be, g] += Fraction(ell) ** a * Fraction(ell) ** be \
                        * lag[g]
    assert {k: v for k, v in total.items() if v} == conv(r, b)


def check_separator_kernel(m):
    """Lemma 9.1(b): for every sector g, the summed coefficient of
    X_{g'} Y_{g,e} Z_{g,e'} t^{e'-e} over the 2M-1 copies vanishes unless
    0 <= e'-e <= M-1, and equals [g'=g] when e'=e."""
    copies = 2 * m - 1
    xw = [[peval(lagrange(m, gp + 1), ell) for gp in range(m)]
          for ell in range(1, copies + 1)]
    big = [lagrange(copies, ell) for ell in range(1, copies + 1)]
    max_power = 0
    for g in range(m):
        yw = [[Fraction(ell - g - 1) ** e for e in range(m)]
              for ell in range(1, copies + 1)]
        zw = [[shifted_coefficient(big[ell - 1], g + 1, ep) for ep in range(m)]
              for ell in range(1, copies + 1)]
        for gp in range(m):
            for e in range(m):
                for ep in range(m):
                    val = sum(xw[l][gp] * yw[l][e] * zw[l][ep]
                              for l in range(copies))
                    if ep < e:
                        assert val == 0
                    elif ep == e:
                        assert val == (1 if gp == g else 0)
                    if val:
                        max_power = max(max_power, ep - e)
    assert max_power <= m - 1
    return max_power


def check_finite_difference(e_max):
    for e in range(1, e_max + 1):
        for j in range(e):
            s = sum((-1) ** (ell - 1) * comb(e, ell) * ell ** j
                    for ell in range(1, e + 1))
            assert s == (1 if j == 0 else 0)


def separator_on_retained(r, b, c, d, n, tau):
    """Apply the Lemma 9.1(b) maps to the retained tensor itself (shared leg 1)
    and compare the constant term with the direct sum of T_g B_X(M)."""
    entries, _ = kept_entries(r, b, c, d)
    retained = retained_from_entries(entries, n, tau)
    words = sorted({tuple(y[0] for y in ys) for (_, ys, _) in retained})
    m = len(words)
    index = {w: g for g, w in enumerate(words)}
    copies = 2 * m - 1
    big = [lagrange(copies, ell) for ell in range(1, copies + 1)]
    xw = [[peval(lagrange(m, gp + 1), ell) for gp in range(m)]
          for ell in range(1, copies + 1)]
    kernel = {}
    for g in range(m):
        for gp in range(m):
            for e in range(m):
                for ep in range(m):
                    val = sum(xw[l][gp] * Fraction(l + 1 - g - 1) ** e *
                              shifted_coefficient(big[l], g + 1, ep)
                              for l in range(copies))
                    if val:
                        kernel[g, gp, e, ep] = val
    poly = Counter()
    for (xs, ys, zs), val in retained.items():
        g = index[tuple(y[0] for y in ys)]
        for (gg, gp, e, ep), kv in kernel.items():
            if gg == g:
                poly[(xs, gp), (ys, e), (zs, ep), ep - e] += val * kv
    poly = {k: v for k, v in poly.items() if v}
    assert all(0 <= k[3] <= m - 1 for k in poly)
    constant = {k[:3]: v for k, v in poly.items() if k[3] == 0}
    expected = {}
    for (xs, ys, zs), val in retained.items():
        g = index[tuple(y[0] for y in ys)]
        for e in range(m):
            expected[(xs, g), (ys, e), (zs, e)] = val
    assert constant == expected
    return m, max(k[3] for k in poly)


# ---------------------------------------------------------------------------
# 7. Orientations
# ---------------------------------------------------------------------------

S3 = list(permutations(range(3)))


def compose(p, q):            # (p q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(3))


def parity(p):
    return sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j]) % 2


def orient(tensor, p):
    """T^p places leg i of T at position p(i)."""
    out = {}
    for key, v in tensor.items():
        new = [None] * 3
        for i in range(3):
            new[p[i]] = key[i]
        out[tuple(new)] = v
    return out


def check_orientations():
    t23 = (0, 2, 1)
    even = [p for p in S3 if parity(p) == 0]
    odd = [p for p in S3 if parity(p) == 1]
    assert sorted(compose(p, t23) for p in even) == sorted(odd)
    assert sorted(compose(p, t23) for p in odd) == sorted(even)
    for r, c in [(2, 3), (3, 2), (1, 4), (3, 3)]:
        t = conv(r, c)
        for p in S3:
            for q in S3:
                assert orient(orient(t, q), p) == orient(t, compose(p, q))
            assert orient(swap23(t), p) == orient(t, compose(p, t23))
        # C(c,r) = C(r,c)^(12): first identity of v5 (2.6)
        assert orient(t, (1, 0, 2)) == conv(c, r)
    # multiset of orientations in prod_{pi in S3} V^pi for V = C^(N-nm) (C^(23))^nm
    for n in range(1, 5):
        for nm in range(n + 1):
            multiset = Counter()
            for p in S3:
                multiset[p] += n - nm
                multiset[compose(p, t23)] += nm
            assert all(multiset[p] == n for p in S3)   # = Q_{r,c}^{(x) n}
            for sign_set, other in ((even, odd), (odd, even)):
                ms = Counter()
                for p in sign_set:
                    ms[p] += n - nm
                    ms[compose(p, t23)] += nm
                assert all(ms[p] == n - nm for p in sign_set)
                assert all(ms[p] == nm for p in other)
    return True


# ---------------------------------------------------------------------------
# 8. Legal steps and chains
# ---------------------------------------------------------------------------


def smallest_parent(child, d):
    r, b = child
    bhat = -(-((d + 2) * r + b - 1) // d)
    return (b, bhat)


def check_steps():
    count = 0
    for d in range(2, 13):
        for r in range(1, 31):
            for b in range(2, 31):
                for c in range(1, b):
                    bq = d * b - (d - 1) * c
                    assert (bq >= 3 * c + r - 1) == legal(r, b, c, d)
                    count += 1
    parents = 0
    for d in range(2, 21):
        for r in range(1, 41):
            for b in range(1, 41):
                pr, pb = smallest_parent((r, b), d)
                slack = d * pb - b + 1 - (d + 2) * r
                assert 0 <= slack < d
                assert legal(pr, pb, r, d)               # parent (b, bhat), child r
                # minimality: bhat - 1 is not a legal parent column
                assert not legal(pr, pb - 1, r, d)
                parents += 1
    for j in range(1, 501):
        p1 = smallest_parent((j, j), 3 * j - 1)
        assert p1 == (j, j + 1)
        assert (3 * j - 1) * (j + 1) - j + 1 - (3 * j + 1) * j == 0
        p2 = smallest_parent(p1, 3 * j)
        assert p2 == (j + 1, j + 1)
        assert 3 * j * (j + 1) - (j + 1) + 1 - (3 * j + 2) * j == 0
    # ramp gain identity (4) of round 11
    for big_r in range(1, 61):
        lhs = prod((Fraction((3 * j + 1) * (3 * j + 2), (3 * j - 1) * (3 * j))
                    for j in range(1, big_r)), start=Fraction(1))
        rhs = Fraction(3 * big_r - 1, 2) * prod(
            (Fraction(3 * j + 1, 3 * j) for j in range(1, big_r)),
            start=Fraction(1))
        assert lhs == rhs
    # round 8 two-stage cycle (7) and reverse recurrence (8)
    cycles = 0
    for d in range(3, 61):
        for a in range(2, 2001):
            c = ((d - 1) * a + 1) // (d + 2)
            assert 1 <= c < a
            assert legal(a, a, c, d) and legal(c, a, c, d)
            cycles += 1
        aj = 1
        for _ in range(60):
            nxt = -(-((d + 2) * aj - 1) // (d - 1))
            assert ((d - 1) * nxt + 1) // (d + 2) == aj
            aj = nxt
    return count, parents, cycles


# ---------------------------------------------------------------------------
# 9. Chain counts
# ---------------------------------------------------------------------------


def compose_chain(stages, n, k):
    """Bookkeeping of the composition proof.  stages: list of
    (r, b, c, d, M).  Returns (A, B, r_star, m_star) by simulating the
    sequence of exact stage restrictions."""
    s = stages[0][0] + stages[0][1] - 1
    charges = [(1 + 6 * k * (m - 1)) * (2 * m - 1) ** (6 * k)
               for (_, _, _, _, m) in stages]
    a_side = prod(d ** (2 * n * k) for (_, _, _, d, _) in stages)
    copies = s ** (6 * n * k) * prod(charges)       # copies of MM_A
    # rank decomposition: s^{6nk} MM_1 |> Q_0^{(x) nk}
    assert copies % s ** (6 * n * k) == 0
    copies //= s ** (6 * n * k)                     # copies of Q_0^{nk} MM_A
    pair = (stages[0][0], stages[0][1])
    pending_source = a_side                          # unused source auxiliaries
    target_side = 1
    for i, (r, b, c, d, m) in enumerate(stages):
        assert pair == (r, b) and legal(r, b, c, d)
        aux = d ** (2 * n * k)
        assert pending_source % aux == 0
        pending_source //= aux
        assert copies % charges[i] == 0
        copies = copies // charges[i] * m ** (6 * k)
        target_side *= m ** (2 * k)
        pair = (c, r)                                # Q_{r,c} = Q_{c,r}
    assert pair == (1, 1) and pending_source == 1
    return a_side, target_side, s ** (6 * n * k) * prod(charges), copies


def formula_round11(stages, n, k):
    by_d = defaultdict(list)
    for st in stages:
        by_d[st[3]].append(st[4])
    s = stages[0][0] + stages[0][1] - 1
    a = prod(d ** (2 * n * k * len(ms)) for d, ms in by_d.items())
    bb = prod(m ** (2 * k) for ms in by_d.values() for m in ms)
    rr = s ** (6 * n * k) * prod(((2 * m - 1) ** (6 * k) * (1 + 6 * k * (m - 1)))
                                 for ms in by_d.values() for m in ms)
    mm = prod(m ** (6 * k) for ms in by_d.values() for m in ms)
    return a, bb, rr, mm


def mode_type(n, d):
    """A maximizer of n!/(K!O!M!) (d-1)^K 2^O by exact exchange moves."""
    w = (d - 1, 2, 1)
    t = [n * w[i] // (d + 2) for i in range(3)]
    t[0] += n - sum(t)
    improved = True
    while improved:
        improved = False
        for x in range(3):
            for y in range(3):
                if x != y and t[x] > 0 and t[x] * w[y] > (t[y] + 1) * w[x]:
                    t[x] -= 1
                    t[y] += 1
                    improved = True
    return tuple(t)


def is_local_mode(n, d, t):
    w = (d - 1, 2, 1)
    return all(not (x != y and t[x] > 0 and t[x] * w[y] > (t[y] + 1) * w[x])
               for x in range(3) for y in range(3))


def big_ln(x):
    """ln of a positive integer to the current decimal precision."""
    bits = x.bit_length()
    shift = max(0, bits - 320)
    top = x >> shift
    return Decimal(top).ln() + shift * Decimal(2).ln()


def ramp_chain(big_d, bulk):
    """Round 11: zero-slack ramp to (R,R), R=8D, then `bulk` steps of arity D.
    Returns forward stages (r,b,c,d) from the source to the terminal."""
    big_r = 8 * big_d
    pairs, arities = [(1, 1)], []
    for j in range(1, big_r):
        for d in (3 * j - 1, 3 * j):
            pairs.append(smallest_parent(pairs[-1], d))
            arities.append(d)
    for _ in range(bulk):
        pairs.append(smallest_parent(pairs[-1], big_d))
        arities.append(big_d)
    stages = []
    for i in range(len(arities) - 1, -1, -1):
        r, b = pairs[i + 1]
        child = pairs[i]
        c = child[0]
        assert child == (c, r)
        stages.append((r, b, c, arities[i]))
    return stages


def check_counts_small():
    """Composition bookkeeping equals both closed forms on small chains."""
    checked = 0
    for (n, k) in ((1, 1), (2, 1), (3, 2)):
        for chain in ([(1, 2, 1, 2)], [(2, 2, 1, 3), (1, 2, 1, 3)],
                      ramp_chain(2, 0), ramp_chain(2, 3)):
            stages = []
            for (r, b, c, d) in chain:
                t = mode_type(n, d)
                stages.append((r, b, c, d, sector_count(d, t)))
            got = compose_chain(stages, n, k)
            assert got == formula_round11(stages, n, k)
            checked += 1
    return checked


def round8_row(d, cycles, t, k):
    n = (d + 2) * t
    tau = ((d - 1) * t, 2 * t, t)
    m = sector_count(d, tau)
    a = 1
    for _ in range(cycles):
        a = -(-((d + 2) * a - 1) // (d - 1))
    ell = 2 * cycles
    e = 1 + 6 * k * (m - 1)
    getcontext().prec = 60
    num = (3 * n * big_ln(2 * a - 1) / ell + 3 * (big_ln(2 * m - 1) - big_ln(m))
           + big_ln(e) / (2 * k) + Decimal(2).ln() / (2 * ell * k))
    den = big_ln(m) - n * Decimal(d).ln()
    digits_a = int(2 * n * ell * k * Decimal(d).log10()) + 1
    return num / den, digits_a, m > d ** n


def round11_row(big_d, bulk, n, k, json_types=None):
    chain = ramp_chain(big_d, bulk)
    getcontext().prec = 60
    s = chain[0][0] + chain[0][1] - 1
    arity_count = Counter(st[3] for st in chain)
    types = {d: mode_type(n, d) for d in arity_count}
    for d, t in types.items():
        assert is_local_mode(n, d, t)
    if json_types is not None:
        for d, t in json_types.items():
            assert is_local_mode(n, d, t)
            assert sector_count(d, t) == sector_count(d, types[d])
    ln_a = sum(2 * n * k * cnt * Decimal(d).ln() for d, cnt in arity_count.items())
    ln_b = ln_r = ln_m = Decimal(0)
    ln_r = 6 * n * k * big_ln(s)
    for d, cnt in arity_count.items():
        m = sector_count(d, types[d])
        ln_b += 2 * k * cnt * big_ln(m)
        ln_m += 6 * k * cnt * big_ln(m)
        ln_r += cnt * (6 * k * big_ln(2 * m - 1) + big_ln(1 + 6 * k * (m - 1)))
    rel = (ln_r - ln_m) / (ln_b - ln_a)
    fixed = (ln_r - ln_m + Decimal(2).ln()) / (ln_b - ln_a)
    digits_a = int(ln_a / Decimal(10).ln()) + 1
    return {"source_pair": (chain[0][0], chain[0][1]), "levels": len(chain),
            "max_arity": max(arity_count), "digits_A": digits_a,
            "relative": rel, "fixed": fixed, "B_gt_A": ln_b > ln_a}


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    start = time.time()
    report = {}

    # Sections 2-3: shifted-chain lemma, all d in 2..5, r in 1..6, b in 2..6
    cases = offdiag_cases = 0
    for d in range(2, 6):
        for r in range(1, 7):
            for b in range(2, 7):
                for c in range(1, b):
                    off = check_shifted_chain(r, b, c, d)
                    assert (off > 0) == (r >= 2)
                    cases += 1
                    offdiag_cases += off > 0
    # the binary jump with h larger than r (example from the notes)
    check_shifted_chain(3, 5, 1, 2)
    report["shifted_chain_cases"] = cases
    report["cases_with_offdiagonal_quotient_to_kernel"] = offdiag_cases

    # Section 4: crop + reset single-position checks on every legal case
    legal_cases = []
    cross_kinds = Counter()
    for d in range(2, 6):
        for r in range(1, 7):
            for b in range(2, 7):
                for c in range(1, b):
                    if legal(r, b, c, d):
                        _, cross = kept_entries(r, b, c, d)
                        cross_kinds.update(cross)
                        legal_cases.append((r, b, c, d))
    report["legal_crop_reset_cases"] = len(legal_cases)
    report["cross_coefficient_kinds"] = {"%s->%s" % k: v
                                         for k, v in sorted(cross_kinds.items())}

    # Section 5: tensor powers N = 1,2,3, all types, legal cases with d <= 4
    power_checks = 0
    max_sectors = 0
    max_terms = 0
    for (r, b, c, d) in legal_cases:
        if d > 4:
            continue
        entries, _ = kept_entries(r, b, c, d)
        for n in (1, 2, 3):
            if n == 3 and r * c > 6:
                continue
            for nk in range(n + 1):
                for no in range(n + 1 - nk):
                    tau = (nk, no, n - nk - no)
                    m, terms = check_power(r, b, c, d, n, tau, entries)
                    power_checks += 1
                    max_sectors = max(max_sectors, m)
                    max_terms = max(max_terms, terms)
    report["tensor_power_checks"] = power_checks
    report["largest_sector_count_checked"] = max_sectors
    report["largest_retained_tensor_terms"] = max_terms

    # independent physical-power route
    phys_checks = []
    for (r, b, c, d, n, tau) in [
            (2, 3, 1, 2, 2, (1, 1, 0)), (2, 3, 1, 2, 2, (0, 1, 1)),
            (2, 3, 1, 2, 2, (1, 0, 1)), (1, 2, 1, 2, 2, (1, 1, 0)),
            (2, 4, 1, 3, 2, (1, 0, 1)), (3, 4, 1, 3, 2, (0, 1, 1)),
            (2, 4, 2, 4, 2, (1, 1, 0)), (1, 3, 1, 2, 3, (1, 1, 1)),
            (2, 3, 1, 2, 3, (1, 1, 1)), (1, 2, 1, 3, 3, (1, 1, 1))]:
        assert legal(r, b, c, d)
        phys_checks.append(((r, b, c, d, n, tau),
                            physical_power_route(r, b, c, d, n, tau)))
    report["physical_power_route_checks"] = len(phys_checks)

    # Section 6: Lemma 9.1 checks
    for r in range(1, 7):
        for b in range(1, 7):
            check_rational_convolution(r, b)
    sep = {m: check_separator_kernel(m) for m in range(1, 17)}
    check_finite_difference(40)
    sep_on_tensor = [separator_on_retained(2, 3, 1, 2, 2, (1, 1, 0)),
                     separator_on_retained(2, 3, 1, 2, 1, (0, 1, 0)),
                     separator_on_retained(1, 3, 1, 2, 3, (1, 1, 1))]
    report["separator_kernel_max_degree_by_M"] = sep
    report["separator_on_retained_(M,max_degree)"] = sep_on_tensor

    # Section 7
    check_orientations()
    report["orientation_checks"] = "passed"

    # Section 8
    report["step_checks"] = dict(zip(
        ("crop_equivalences", "smallest_parents", "two_stage_cycles"),
        check_steps()))

    # Section 9
    report["count_bookkeeping_checks"] = check_counts_small()
    r8 = round8_row(5, 200, 30, 500)
    assert Decimal("2.75866818419636154435") < r8[0] < Decimal("2.75866818419636154451")
    report["round8_row1"] = {"fixed_batch_exponent": str(r8[0])[:24],
                             "digits_A": r8[1], "M_gt_d^N": r8[2]}
    # round 8 row 4: A = 100^(2 N ell k) with N = 102*5000, ell = 200000
    exponent_a = 2 * (102 * 5000) * 200000 * 100000
    assert exponent_a == 20400000000000000
    report["round8_row4_digits_A"] = 2 * exponent_a + 1
    rows = {}
    data = None
    try:
        with open("results/round11-arity-ramp.json") as fh:
            data = json.load(fh)
    except OSError:
        pass
    thresholds = {2: "2.337133", 4: "2.288185", 8: "2.267707", 16: "2.260112"}
    for idx, (big_d, bulk, n, k) in enumerate(((2, 100, 512, 256),
                                               (4, 400, 2048, 1024),
                                               (8, 1600, 8192, 4096),
                                               (16, 3200, 32768, 16384))):
        json_types = None
        if data is not None:
            cert = data["finite_certificates"][idx]
            assert cert["bulk_arity"] == big_d and cert["bulk_levels"] == bulk
            json_types = {t["arity"]: tuple(t["type_kernel_outer_middle"])
                          for t in cert["types_and_arity_counts"]}
        row = round11_row(big_d, bulk, n, k, json_types)
        if data is not None:
            assert list(row["source_pair"]) == cert["source_pair"]
            assert row["digits_A"] == cert["source_decimal_digits"]
            assert row["levels"] == cert["total_levels"]
            lo = Decimal(cert["certified_relative_exponent_interval"]["lower"])
            hi = Decimal(cert["certified_relative_exponent_interval"]["upper"])
            assert lo - Decimal("1e-40") <= row["relative"] <= hi + Decimal("1e-40")
        assert row["fixed"] < Decimal(thresholds[big_d]) and row["B_gt_A"]
        rows[big_d] = {"levels": row["levels"], "max_arity": row["max_arity"],
                       "digits_A": row["digits_A"],
                       "pooled_exponent": str(row["relative"])[:22],
                       "fixed_batch_exponent": str(row["fixed"])[:22],
                       "B_gt_A": row["B_gt_A"]}
    report["round11_rows"] = rows
    report["seconds"] = round(time.time() - start, 1)
    json.dump(report, sys.stdout, indent=1, default=str)
    print()


if __name__ == "__main__":
    main()
