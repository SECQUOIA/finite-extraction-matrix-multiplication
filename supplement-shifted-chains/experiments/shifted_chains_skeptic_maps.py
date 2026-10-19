"""Adversarial exact checks for the shifted-chain stage (topic "maps").

Written independently of experiments/shifted_chains_check_maps.py (nothing is
imported from it or from earlier rounds). Every identity uses Python integers
or fractions.Fraction; no floating point is used in any check.

What this adds to the checker's script:
  1. Lemma A(iii) including the explicit quotient->kernel formula, over a
     wider range, computed by the bilinear-map route (multiply a basis vector,
     read its coordinates), plus a proof-backed check that the off-diagonal
     block is nonzero for r >= 2 and a count of legal cases where the crop
     already removes every quotient->kernel coefficient.
  2. One orientation of the stage, end to end, starting from the physical
     tensor power U^{(x)N}: shifted-chain basis change, crop and type
     restriction (summed over physical terms), then for each of the 2M-1
     copies the v5 Lemma 9.1(b) separator and the word-dependent reindexing
     on ALL target variables. Checks: no cross-word term survives, no
     negative t-powers, degree <= M-1, constant term = M (V B_X(M)) in
     canonical coordinates (V built independently from C(r,c)).
  3. Exactification (v5 Lemma 9.1(c)) by literal evaluation of the full
     composite leg maps (basis change, restriction, separator, reindexing)
     on every physical variable at the nodes 1..E: an exact finite
     restriction
        E (2M-1)^k U^{(x)Nk}  restricts to  M^k (V B_X(M))^{(x)k},
     E = 1+k(M-1), checked for k = 1 and k = 2.
  4. Six orientations on actual tensors: (x)_pi V^pi equals Q_{r,c}^{(x)N}
     after an explicit slot permutation; (x)_pi B_X(m)^pi equals MM_{m^2}
     after explicit index grouping.
  5. Denominators of Lemma 9.1(a),(b): every prime is at most n-1 resp. 2M-2
     (supports the positive-characteristic outline).
  6. Digit counts of A for the round-11 rows with an explicit margin from the
     integer boundary (the checker computed int(log10 A)+1 without a margin).
  7. After the crop, quotient->kernel coefficients survive iff b <= 3c+r-2
     (r >= 2); this never fails for smallest-parent stages (round 11 (2)) or
     for the round-8 two-stage cycle, so the full type restriction is needed
     there. Negative control: fixing only the middle count leaves cross-word
     terms in such cases, and none when b >= 3c+r-1.

Run from the repository root:
    python -I experiments/shifted_chains_skeptic_maps.py
"""

from collections import Counter, defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial, prod
import sys
import time


# ---------------------------------------------------------------------------
# 0. Basic tensors
# ---------------------------------------------------------------------------


def conv(r, b):
    return {(a, be, a + be): 1 for a in range(r) for be in range(b)}


def transpose23(t):
    return {(k[0], k[2], k[1]): v for k, v in t.items()}


def kron(factors):
    """Tensor product of sparse 3-leg tensors; coordinates become tuples."""
    out = {((), (), ()): 1}
    for f in factors:
        nxt = {}
        for (x, y, z), v in out.items():
            for (a, b, c), w in f.items():
                nxt[x + (a,), y + (b,), z + (c,)] = v * w
        out = nxt
    return out


# ---------------------------------------------------------------------------
# 1. Lemma A by the bilinear-map route, with the explicit off-diagonal formula
# ---------------------------------------------------------------------------


def first_comp(e, ell, h, d):
    for p in range(d):
        if p * h <= e <= p * h + ell - 1:
            return p
    raise AssertionError("uncovered exponent")


def lift(e, ell, h, d):
    p = first_comp(e, ell, h, d)
    return {(p, e - p * h): 1}


def kappa(j, i, h):
    return {(j, i + h): -1, (j + 1, i): 1}


def coords(vec, ell, h, d):
    """Coordinates of a vector of W_ell in the lift/kernel basis, via the
    inverse formula (star); returns {('q',e) or ('k',j,i): coef}."""
    out = Counter()
    for (p, m), v in vec.items():
        e = p * h + m
        p0 = first_comp(e, ell, h, d)
        out[("q", e)] += v
        for j in range(p0, p):
            i = m + (p - 1 - j) * h
            assert 0 <= i < ell - h
            out[("k", j, i)] += v
    return {k: v for k, v in out.items() if v}


def basis_vectors(ell, h, d):
    big_l = ell + (d - 1) * h
    vecs = {("q", e): lift(e, ell, h, d) for e in range(big_l)}
    for j in range(d - 1):
        for i in range(ell - h):
            vecs[("k", j, i)] = kappa(j, i, h)
    return vecs


def check_lemma_a(r, b, c, d):
    h = b - c
    vin = basis_vectors(b, h, d)
    assert len(vin) == d * b
    # (star) is a left inverse of the basis matrix => it is the inverse
    for lab, vec in vin.items():
        assert coords(vec, b, h, d) == {lab: 1}, (lab, vec)
    # Q maps lifts to monomials and kernel vectors to zero
    for lab, vec in vin.items():
        img = Counter()
        for (p, m), v in vec.items():
            img[p * h + m] += v
        img = {k: v for k, v in img.items() if v}
        assert img == ({lab[1]: 1} if lab[0] == "q" else {})
    # multiply each input basis vector by z^alpha and read output coordinates
    pb = lambda e: first_comp(e, b, h, d)
    pout = lambda e: first_comp(e, b + r - 1, h, d)
    off = off_kept = 0
    for a in range(r):
        for lab, vec in vin.items():
            shifted = {(p, m + a): v for (p, m), v in vec.items()}
            got = coords(shifted, b + r - 1, h, d)
            if lab[0] == "q":
                e = lab[1]
                want = {("q", e + a): 1}
                for j in range(pout(e + a), pb(e)):
                    want[("k", j, e + a - (j + 1) * h)] = 1
                off += len(want) - 1
                if e < 3 * c + r - 1:
                    off_kept += len(want) - 1
            else:
                want = {("k", lab[1], lab[2] + a): 1}
            assert got == want, (r, b, c, d, a, lab, got, want)
    if r >= 2:
        # proof of nonvanishing: e=b, alpha=0 reaches kernel copy 0 at index c
        assert pb(b) == 1 and pout(b) == 0
        if (d + 2) * c <= d * b - r + 1:
            # after the crop, quotient->kernel terms survive iff b < 3c+r-1
            assert (off_kept == 0) == (b >= 3 * c + r - 1)
    return off


def lemma_a_sweep():
    cases = offdiag_cases = crop_kills_kernel_cross = 0
    for d in range(2, 8):
        for r in range(1, 7):
            for b in range(2, 9):
                for c in range(1, b):
                    off = check_lemma_a(r, b, c, d)
                    cases += 1
                    offdiag_cases += off > 0
                    assert (off > 0) == (r >= 2)
                    legal = (d + 2) * c <= d * b - r + 1
                    if legal and r >= 2 and b >= 3 * c + r - 1:
                        # every kept quotient input e < 3c+r-1 <= b has p_b(e)=0
                        crop_kills_kernel_cross += 1
    return cases, offdiag_cases, crop_kills_kernel_cross


def smallest_parent_keeps_kernel_cross(max_d=30, max_side=60):
    """For the smallest legal parent (b, bhat) of a child (r, b) (round 11
    (2)), with parent first length b >= 2, the crop never removes all
    quotient->kernel coefficients, i.e. bhat < 3r + b - 1. So in every such
    chain stage the full type (not just the middle count) must be fixed."""
    n = 0
    for d in range(2, max_d + 1):
        for r in range(1, max_side + 1):
            for b in range(2, max_side + 1):
                bhat = -(-((d + 2) * r + b - 1) // d)
                assert bhat < 3 * r + b - 1, (d, r, b, bhat)
                n += 1
    return n


def round8_cycle_keeps_kernel_cross(max_d=60, max_a=2000):
    """Round-8 two-stage cycle: stages (a,a,c) and (c,a,c) with
    c = floor(((d-1)a+1)/(d+2)). Whenever the multiplier length r >= 2, the
    crop keeps some quotient->kernel coefficient (b < 3c+r-1)."""
    n = 0
    for d in range(3, max_d + 1):
        for a in range(2, max_a + 1):
            c = ((d - 1) * a + 1) // (d + 2)
            for (r, b) in ((a, a), (c, a)):
                assert (d + 2) * c <= d * b - r + 1 and 1 <= c < b
                if r >= 2:
                    assert b < 3 * c + r - 1, (d, a, r, b, c)
                n += 1
    return n


# ---------------------------------------------------------------------------
# 2. One orientation of the stage as composite maps on U^{(x)N}
# ---------------------------------------------------------------------------


def lagrange(n, node):
    """Coefficients (low to high) of the Lagrange basis polynomial of the
    nodes 1..n at `node`."""
    poly, den = [Fraction(1)], 1
    for other in range(1, n + 1):
        if other != node:
            nxt = [Fraction(0)] * (len(poly) + 1)
            for i, cf in enumerate(poly):
                nxt[i + 1] += cf
                nxt[i] -= other * cf
            poly = nxt
            den *= node - other
    return [cf / den for cf in poly]


def evalp(poly, x):
    return sum(cf * Fraction(x) ** i for i, cf in enumerate(poly))


def taylor_coeff(poly, shift, k):
    """[xi^k] poly(shift + xi)."""
    return sum(comb(s, k) * Fraction(shift) ** (s - k) * poly[s]
               for s in range(k, len(poly)))


class Stage:
    """Single-orientation stage data for (r,b,c,d), inventory N, type tau."""

    def __init__(self, r, b, c, d, n, tau):
        assert 1 <= c < b and d >= 2 and (d + 2) * c <= d * b - r + 1
        assert sum(tau) == n
        self.r, self.b, self.c, self.d, self.n, self.tau = r, b, c, d, n, tau
        self.h = b - c
        self.lp = 3 * c + r - 1                     # L'
        # leg-2 basis columns: physical (p,m) -> list of (label, coef)
        rows = defaultdict(list)
        for lab, vec in basis_vectors(b, self.h, d).items():
            for phys, v in vec.items():
                rows[phys].append((lab, v))
        self.rows_in = rows
        # leg-3 contragredient: physical (p,m) -> coordinates in output basis
        self.inv_out = {(p, m): coords({(p, m): 1}, b + r - 1, self.h, d)
                        for p in range(d) for m in range(b + r - 1)}
        words = [w for w in product(self.alphabet(), repeat=n)
                 if self.wtype(w) == tau]
        self.words = words
        self.index = {w: g for g, w in enumerate(words)}
        self.m = len(words)
        nk, no, nm = tau
        assert self.m == factorial(n) // (factorial(nk) * factorial(no)
                                          * factorial(nm)) \
            * (d - 1) ** nk * 2 ** no

    def alphabet(self):
        return ["K%d" % j for j in range(self.d - 1)] + ["L", "R", "Mid"]

    @staticmethod
    def wtype(word):
        cnt = Counter("K" if w[0] == "K" else ("Mid" if w == "Mid" else "O")
                      for w in word)
        return (cnt["K"], cnt["O"], cnt["Mid"])

    # letters and local indices --------------------------------------------
    def letter_in(self, lab):
        c, r = self.c, self.r
        if lab[0] == "k":
            return "K%d" % lab[1], lab[2]
        e = lab[1]
        if e < c:
            return "L", e
        if e <= 2 * c + r - 2:
            return "Mid", e - c
        if e <= 3 * c + r - 2:
            return "R", e - (2 * c + r - 1)
        return None

    def letter_out(self, lab):
        c, r = self.c, self.r
        if lab[0] == "k":
            return "K%d" % lab[1], lab[2]
        v = lab[1]
        if v <= c + r - 2:
            return "L", v
        if v <= 2 * c + r - 2:
            return "Mid", v - (c + r - 1)
        if v <= 3 * c + 2 * r - 3:
            return "R", v - (2 * c + r - 1)
        return None

    def order(self, word):
        return ([t for t, w in enumerate(word) if w != "Mid"]
                + [t for t, w in enumerate(word) if w == "Mid"])

    # composite leg maps for separator copy `node` (1..2M-1) -----------------
    # each returns a list of (target variable, t-exponent, coefficient)
    def map_x(self, xs, node):
        m, out = self.m, []
        for gp in range(m):
            cf = evalp(lagrange(m, gp + 1), node)
            if cf:
                word = self.words[gp]
                xr = tuple(self.r - 1 - xs[t] if word[t] == "Mid" else xs[t]
                           for t in self.order(word))
                out.append((("X", gp, xr), 0, cf))
        return out

    def map_y(self, ys, node):
        out = []
        for combo in product(*(self.rows_in[y] for y in ys)):
            lets = [self.letter_in(lab) for lab, _ in combo]
            if any(x is None for x in lets):
                continue
            word = tuple(x[0] for x in lets)
            if self.wtype(word) != self.tau:
                continue
            cf0 = prod(v for _, v in combo)
            g = self.index[word]
            loc = tuple(lets[t][1] for t in self.order(word))
            for e in range(self.m):
                cf = cf0 * Fraction(node - g - 1) ** e
                if cf:
                    out.append((("Y", g, loc, e), -e, cf))
        return out

    def map_z(self, zs, node):
        out = []
        big = lagrange(2 * self.m - 1, node)
        for combo in product(*(list(self.inv_out[z].items()) for z in zs)):
            lets = [self.letter_out(lab) for lab, _ in combo]
            if any(x is None for x in lets):
                continue
            word = tuple(x[0] for x in lets)
            if self.wtype(word) != self.tau:
                continue
            cf0 = prod(v for _, v in combo)
            g = self.index[word]
            loc = tuple(lets[t][1] for t in self.order(word))
            for ep in range(self.m):
                cf = cf0 * taylor_coeff(big, g + 1, ep)
                if cf:
                    out.append((("Z", g, loc, ep), ep, cf))
        return out

    # tensors ----------------------------------------------------------------
    def physical_power(self):
        r, b, d = self.r, self.b, self.d
        one = [(a, (p, be), (p, a + be)) for a in range(r) for be in range(b)
               for p in range(d)]
        return [tuple(zip(*terms)) for terms in product(one, repeat=self.n)]

    def canonical_target(self):
        """M (V B_X(M)) in the canonical coordinates used by the maps."""
        r, c, n, nm = self.r, self.c, self.n, self.tau[2]
        v = kron([conv(r, c)] * (n - nm) + [transpose23(conv(r, c))] * nm)
        out = {}
        for g in range(self.m):
            for (xs, ys, zs), val in v.items():
                for e in range(self.m):
                    out[("X", g, xs), ("Y", g, ys, e), ("Z", g, zs, e)] = val
        return out


def restricted_tensor(st):
    """Basis change + crop + type restriction applied to U^{(x)N}, summed
    over the physical terms (so cancellations happen here). Keys are
    (xs, ys', zs') with ys', zs' tuples of new-basis labels."""
    res = Counter()
    for xs, ys, zs in st.physical_power():
        ins = [c for c in product(*(st.rows_in[y] for y in ys))]
        outs = [c for c in product(*(list(st.inv_out[z].items()) for z in zs))]
        for ci in ins:
            li = [st.letter_in(lab) for lab, _ in ci]
            if any(x is None for x in li) or \
                    st.wtype([x[0] for x in li]) != st.tau:
                continue
            vi = prod(v for _, v in ci)
            for co in outs:
                lo = [st.letter_out(lab) for lab, _ in co]
                if any(x is None for x in lo) or \
                        st.wtype([x[0] for x in lo]) != st.tau:
                    continue
                res[xs, tuple(l for l, _ in ci), tuple(l for l, _ in co)] += \
                    vi * prod(v for _, v in co)
    return {k: v for k, v in res.items() if v}


def stage_polynomial(st):
    """Restriction (above), then the Lemma 9.1(b) separator on the 2M-1
    copies followed by the word-dependent reindexing on all target
    variables; returns {(X,Y,Z): {t-exponent: coef}}. By linearity this is
    the image of (2M-1) U^{(x)N} under the composite maps. The separator
    coefficients are first summed over the copies, per sector g."""
    t = restricted_tensor(st)
    m = st.m
    kern = {}
    for g in range(m):
        acc = Counter()
        for node in range(1, 2 * m):
            big = lagrange(2 * m - 1, node)
            zc = [taylor_coeff(big, g + 1, ep) for ep in range(m)]
            yc = [Fraction(node - g - 1) ** e for e in range(m)]
            for gp in range(m):
                xc = evalp(lagrange(m, gp + 1), node)
                if not xc:
                    continue
                for e in range(m):
                    if not yc[e]:
                        continue
                    for ep in range(m):
                        if zc[ep]:
                            acc[gp, e, ep] += xc * yc[e] * zc[ep]
        kern[g] = [(k, v) for k, v in acc.items() if v]
    res = defaultdict(Counter)
    for (xs, ys, zs), val in t.items():
        li = [st.letter_in(l) for l in ys]
        lo = [st.letter_out(l) for l in zs]
        word = tuple(x[0] for x in li)
        assert word == tuple(x[0] for x in lo), \
            "cross-word term survived the restriction"
        g = st.index[word]
        yloc = tuple(li[q][1] for q in st.order(word))
        zloc = tuple(lo[q][1] for q in st.order(word))
        for (gp, e, ep), kv in kern[g]:
            w2 = st.words[gp]
            xr = tuple(st.r - 1 - xs[q] if w2[q] == "Mid" else xs[q]
                       for q in st.order(w2))
            key = (("X", gp, xr), ("Y", g, yloc, e), ("Z", g, zloc, ep))
            res[key][ep - e] += val * kv
    out = {}
    for key, poly in res.items():
        poly = {k: v for k, v in poly.items() if v}
        if poly:
            out[key] = poly
    return out


def negative_control_mid_only(r, b, c, d, n, nm):
    """Fix only the middle count (as v5 Lemma 4.5 does for a tripling).
    Returns the number of surviving terms whose leg-2 and leg-3 words differ;
    a positive value shows that the kernel/outer counts must also be fixed
    and that the word-equality check above is not vacuous."""
    st = Stage(r, b, c, d, n, (0, n - nm, nm))
    bad = 0
    acc = Counter()
    for xs, ys, zs in st.physical_power():
        for ci in product(*(st.rows_in[y] for y in ys)):
            li = [st.letter_in(lab) for lab, _ in ci]
            if any(x is None for x in li) or \
                    sum(x[0] == "Mid" for x in li) != nm:
                continue
            for co in product(*(list(st.inv_out[z].items()) for z in zs)):
                lo = [st.letter_out(lab) for lab, _ in co]
                if any(x is None for x in lo) or \
                        sum(x[0] == "Mid" for x in lo) != nm:
                    continue
                acc[xs, tuple(l for l, _ in ci), tuple(l for l, _ in co)] += \
                    prod(v for _, v in ci) * prod(v for _, v in co)
    for (xs, ys, zs), v in acc.items():
        if v and tuple(st.letter_in(l)[0] for l in ys) != \
                tuple(st.letter_out(l)[0] for l in zs):
            bad += 1
    return bad


def check_stage(r, b, c, d, n, tau):
    st = Stage(r, b, c, d, n, tau)
    poly = stage_polynomial(st)
    exps = [k for p in poly.values() for k in p]
    assert min(exps) >= 0, "negative power of t survived"
    assert max(exps) <= st.m - 1
    const = {key: p[0] for key, p in poly.items() if 0 in p}
    assert const == st.canonical_target()
    return st.m, max(exps), len(const)


def check_exact_k(r, b, c, d, n, tau, k):
    """Literal Lemma 9.1(c): evaluate every composite leg map at t = 1..E,
    take k-th tensor powers of the maps on k-th powers of the source, weight
    by (-1)^(l-1) binom(E,l), and compare with the k-th power of the target.
    Source: E copies of ((2M-1) U^{(x)N})^{(x)k}."""
    st = Stage(r, b, c, d, n, tau)
    m = st.m
    big_e = k * (m - 1) + 1
    terms = st.physical_power()
    # one copy of the separator source T = (2M-1) U^{(x)N}; its terms carry
    # the copy label `node`
    base = [(node, xs, ys, zs) for node in range(1, 2 * m)
            for xs, ys, zs in terms]
    target1 = st.canonical_target()
    target = {}
    for combo in product(target1.items(), repeat=k):
        key = tuple(tuple(kk[i] for kk, _ in combo) for i in range(3))
        target[key] = prod(v for _, v in combo)
    total = Counter()
    for tval in range(1, big_e + 1):
        weight = (-1) ** (tval - 1) * comb(big_e, tval)
        tv = Fraction(tval)
        mx, my, mz = {}, {}, {}

        def leg(cache, fn, node, var):
            key = (node, var)
            if key not in cache:
                cache[key] = [(tgt, cf * tv ** ex) for tgt, ex, cf in
                              fn(var, node)]
            return cache[key]

        for combo in product(base, repeat=k):
            lx = [leg(mx, st.map_x, nd, xs) for nd, xs, _, _ in combo]
            ly = [leg(my, st.map_y, nd, ys) for nd, _, ys, _ in combo]
            if any(not l for l in ly):
                continue
            lz = [leg(mz, st.map_z, nd, zs) for nd, _, _, zs in combo]
            for xx in product(*lx):
                X = tuple(t for t, _ in xx)
                cxx = prod(cf for _, cf in xx)
                for yy in product(*ly):
                    Y = tuple(t for t, _ in yy)
                    cyy = prod(cf for _, cf in yy)
                    for zz in product(*lz):
                        Z = tuple(t for t, _ in zz)
                        total[X, Y, Z] += weight * cxx * cyy * \
                            prod(cf for _, cf in zz)
    total = {kk: v for kk, v in total.items() if v}
    assert total == target, "exactified restriction differs from target"
    return m, big_e, big_e * (2 * m - 1) ** k, len(target)


# ---------------------------------------------------------------------------
# 3. Six orientations on actual tensors
# ---------------------------------------------------------------------------

S3 = list(permutations(range(3)))
T23 = (0, 2, 1)


def compose(p, q):
    return tuple(p[q[i]] for i in range(3))


def orient(t, p):
    out = {}
    for key, v in t.items():
        new = [None] * 3
        for i in range(3):
            new[p[i]] = key[i]
        out[tuple(new)] = v
    return out


def six_fold(t_of_slot):
    """(x)_{pi in S3} t_of_slot(pi)^pi, slots in the order of S3."""
    return kron([orient(t_of_slot(p), p) for p in S3])


def check_orientation_identity(r, c, n, nm):
    base = conv(r, c)
    v = kron([base] * (n - nm) + [transpose23(base)] * nm)
    # flatten V's per-leg tuples so that V is a 3-leg tensor
    lhs = six_fold(lambda p: v)
    # Q_{r,c}^{(x)n} with n sub-slots per orientation slot
    rhs = kron([orient(base, p) for p in S3 for _ in range(n)])
    # explicit slot permutation: sub-slot (pi, s) of the left side holds
    # C^{pi} for s < n-nm and C^{pi (23)} for s >= n-nm
    pos = {}
    used = Counter()
    for p in S3:
        for s in range(n):
            target_p = p if s < n - nm else compose(p, T23)
            q = S3.index(target_p)
            pos[S3.index(p), s] = q * n + used[q]
            used[q] += 1
    assert all(used[q] == n for q in range(6))

    def remap(leg_tuple):
        out = [None] * (6 * n)
        for slot, sub in enumerate(leg_tuple):
            for s, val in enumerate(sub):
                out[pos[slot, s]] = val
        return tuple(out)

    mapped = {tuple(remap(k[i]) for i in range(3)): val
              for k, val in lhs.items()}
    assert len(mapped) == len(lhs)
    assert mapped == rhs
    return len(rhs)


def check_dot_products(m):
    bx = {(0, g, g): 1 for g in range(m)}
    prodt = six_fold(lambda p: bx)
    # slot types: pi(1)=1 -> index shared by legs 2,3 (gamma);
    # pi(1)=2 -> legs 1,3 (alpha); pi(1)=3 -> legs 1,2 (beta)
    kinds = {0: [], 1: [], 2: []}
    for s, p in enumerate(S3):
        kinds[p[0]].append(s)
    assert all(len(v) == 2 for v in kinds.values())

    def idx(leg_tuple, leg, kind):
        # index of the summation variable of the slots of `kind` on `leg`
        return tuple(leg_tuple[s] for s in kinds[kind])

    mm = {}
    for (x, y, z), v in prodt.items():
        alpha = idx(x, 0, 1)
        assert alpha == idx(z, 2, 1)
        beta = idx(x, 0, 2)
        assert beta == idx(y, 1, 2)
        gamma = idx(y, 1, 0)
        assert gamma == idx(z, 2, 0)
        mm[(alpha, beta), (beta, gamma), (gamma, alpha)] = v
    side = list(product(range(m), repeat=2))
    want = {((a, bb), (bb, g), (g, a)): 1 for a in side for bb in side
            for g in side}
    assert mm == want and len(prodt) == len(want)
    return len(want)


# ---------------------------------------------------------------------------
# 4. Denominators of Lemma 9.1(a),(b)
# ---------------------------------------------------------------------------


def prime_factors(n):
    out, p = set(), 2
    while p * p <= n:
        while n % p == 0:
            out.add(p)
            n //= p
        p += 1
    if n > 1:
        out.add(n)
    return out


def check_denominators(max_m=12, max_n=14):
    for m in range(1, max_m + 1):
        primes = set()
        big = [lagrange(2 * m - 1, l) for l in range(1, 2 * m)]
        for l in range(1, 2 * m):
            for gp in range(m):
                primes |= prime_factors(evalp(lagrange(m, gp + 1), l).denominator)
            for g in range(m):
                for ep in range(m):
                    primes |= prime_factors(
                        taylor_coeff(big[l - 1], g + 1, ep).denominator)
        assert all(p <= max(2 * m - 2, 1) for p in primes), (m, primes)
    for n in range(1, max_n + 1):
        primes = set()
        for l in range(1, n + 1):
            for cf in lagrange(n, l):
                primes |= prime_factors(cf.denominator)
        assert all(p <= max(n - 1, 1) for p in primes)
    return True


# ---------------------------------------------------------------------------
# 5. Round-11 digit counts with a boundary margin
# ---------------------------------------------------------------------------


def ramp_arities(big_d, bulk):
    big_r = 8 * big_d
    ar = Counter()
    pairs = [(1, 1)]
    for j in range(1, big_r):
        for d in (3 * j - 1, 3 * j):
            r, b = pairs[-1]
            bhat = -(-((d + 2) * r + b - 1) // d)
            slack = d * bhat - b + 1 - (d + 2) * r
            assert slack == 0                       # zero-slack ramp (3)
            pairs.append((b, bhat))
            ar[d] += 1
    for _ in range(bulk):
        r, b = pairs[-1]
        d = big_d
        bhat = -(-((d + 2) * r + b - 1) // d)
        slack = d * bhat - b + 1 - (d + 2) * r
        assert 0 <= slack < d
        # the stage (b, bhat) -> child (r, b) is legal: c=r, 1<=c<bhat
        assert 1 <= r < bhat and (d + 2) * r <= d * bhat - b + 1
        pairs.append((b, bhat))
        ar[d] += 1
    assert pairs[2 * (big_r - 1)] == (big_r, big_r)
    return ar, pairs[-1]


def check_digits():
    getcontext().prec = 80
    reported = {(2, 100, 512, 256): (17857969, 130),
                (4, 400, 2048, 1024): (1416018955, 462),
                (8, 1600, 8192, 4096): (112670650787, 1726),
                (16, 3200, 32768, 16384): (4724998039558, 3454)}
    margins = {}
    for (big_d, bulk, n, k), (digits, levels) in reported.items():
        ar, _ = ramp_arities(big_d, bulk)
        assert sum(ar.values()) == levels
        log10a = sum(2 * n * k * cnt * Decimal(d).log10()
                     for d, cnt in ar.items())
        frac = log10a - int(log10a)
        margin = min(frac, 1 - frac)
        assert margin > Decimal("1e-30")          # far above rounding error
        assert int(log10a) + 1 == digits
        margins[big_d] = str(margin)[:8]
    return margins


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    t0 = time.time()
    rep = {}
    cases, offd, crop_kills = lemma_a_sweep()
    rep["lemma_A_cases_with_offdiag_formula"] = cases
    rep["lemma_A_cases_offdiag_nonzero"] = offd
    rep["legal_r>=2_cases_where_crop_removes_all_quotient_to_kernel"] = crop_kills
    rep["smallest_parent_stages_keeping_kernel_cross"] = \
        smallest_parent_keeps_kernel_cross()
    rep["round8_cycle_stages_checked_keeping_kernel_cross"] = \
        round8_cycle_keeps_kernel_cross()

    stage_cases = [
        (2, 3, 1, 2, 1, (0, 1, 0)), (2, 3, 1, 2, 1, (1, 0, 0)),
        (2, 3, 1, 2, 2, (1, 1, 0)), (2, 3, 1, 2, 2, (0, 1, 1)),
        (2, 3, 1, 2, 2, (1, 0, 1)), (1, 2, 1, 2, 2, (1, 1, 0)),
        (2, 4, 1, 3, 2, (1, 0, 1)), (3, 4, 1, 3, 1, (0, 0, 1)),
        (2, 4, 2, 4, 1, (1, 0, 0)), (3, 5, 1, 2, 1, (0, 1, 0)),
        (2, 3, 1, 2, 3, (1, 1, 1)), (1, 3, 1, 2, 3, (1, 1, 1)),
    ]
    out = []
    for case in stage_cases:
        out.append((case, check_stage(*case)))
    rep["stage_end_to_end_(case,(M,maxdeg,const_terms))"] = [
        (str(c), v) for c, v in out]

    # fixing only the middle count leaves cross-word terms when some
    # quotient->kernel coefficient survives the crop ...
    rep["negative_control_mid_count_only_cross_terms"] = {
        str(cs): negative_control_mid_only(*cs)
        for cs in [(2, 3, 1, 2, 1, 0), (2, 3, 1, 2, 2, 0), (2, 3, 1, 2, 2, 1)]}
    assert all(v > 0 for v in
               rep["negative_control_mid_count_only_cross_terms"].values())
    # ... but not when b >= 3c+r-1, where the crop already removes them
    rep["mid_count_only_when_crop_removes_kernel_cross"] = {
        str(cs): negative_control_mid_only(*cs)
        for cs in [(2, 4, 1, 3, 2, 1), (3, 5, 1, 2, 1, 0)]}
    assert all(v == 0 for v in
               rep["mid_count_only_when_crop_removes_kernel_cross"].values())

    exact = []
    for case, k in [((2, 3, 1, 2, 1, (0, 1, 0)), 1),
                    ((2, 3, 1, 2, 2, (0, 1, 1)), 1),
                    ((2, 3, 1, 2, 2, (1, 1, 0)), 1),
                    ((2, 3, 1, 2, 1, (0, 1, 0)), 2),
                    ((1, 2, 1, 2, 1, (0, 1, 0)), 2)]:
        exact.append((str(case), k, check_exact_k(*case, k)))
    rep["exactified_restrictions_(case,k,(M,E,source_copies,target_terms))"] = exact

    orient_checks = []
    for (r, c, n) in [(2, 3, 1), (3, 2, 1), (2, 2, 1), (1, 3, 1),
                      (1, 2, 2), (2, 1, 2)]:
        for nm in range(n + 1):
            orient_checks.append(((r, c, n, nm),
                                  check_orientation_identity(r, c, n, nm)))
    rep["six_orientation_identity_checks"] = len(orient_checks)
    rep["sixfold_dot_product_is_MM_m^2"] = {m: check_dot_products(m)
                                             for m in (2, 3)}
    rep["denominator_primes_bounded"] = check_denominators()
    rep["round11_digits_margin"] = check_digits()
    rep["seconds"] = round(time.time() - t0, 1)
    for k, v in rep.items():
        print(k, ":", v)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
