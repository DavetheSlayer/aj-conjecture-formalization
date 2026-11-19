"""Faithful transcription into Python of the definitions of the statement: braid knots, the
Kauffman bracket, the coloured Jones function, recurrence operators and the knot group
(lean/Proofs/AJConjecture/BraidKnot.lean, KauffmanBracket.lean, ColoredJones.lean,
RecurrenceIdeal.lean, KnotGroup.lean). Transcribed from their verbatim copies in the earlier
single-file challenge AJChallenge.lean (lines 30-141 at commit a5005af).
Laurent polynomials in T over Z are dicts {exponent: coeff} wrapped in class LP.
Two code paths for `bracket`:
  bracket_literal : dense matrices indexed by functions Fin m -> Bool, exactly as in Lean.
  bracket_fast    : same operator applied sector by sector with Kronecker-substituted big ints.
"""
from math import comb
from itertools import product
import numpy as np

class LP:
    __slots__ = ("c",)
    def __init__(self, c=None):
        self.c = {e: v for e, v in (c or {}).items() if v != 0}
    def __add__(self, o):
        o = _lp(o); r = dict(self.c)
        for e, v in o.c.items(): r[e] = r.get(e, 0) + v
        return LP(r)
    __radd__ = __add__
    def __neg__(self): return LP({e: -v for e, v in self.c.items()})
    def __sub__(self, o): return self + (-_lp(o))
    def __rsub__(self, o): return _lp(o) - self
    def __mul__(self, o):
        o = _lp(o); r = {}
        for e1, v1 in self.c.items():
            for e2, v2 in o.c.items():
                r[e1 + e2] = r.get(e1 + e2, 0) + v1 * v2
        return LP(r)
    __rmul__ = __mul__
    def __eq__(self, o): return self.c == _lp(o).c
    def __hash__(self): return hash(tuple(sorted(self.c.items())))
    def is_zero(self): return not self.c
    def sub_T(self, k):
        """T -> T^k"""
        return LP({e * k: v for e, v in self.c.items()})
    def __repr__(self):
        if not self.c: return "0"
        return " ".join(("%+d*T^%d" % (v, e)) for e, v in sorted(self.c.items()))
def _lp(x): return x if isinstance(x, LP) else LP({0: int(x)})
def T(e): return LP({e: 1})
ZERO, ONE = LP(), LP({0: 1})

# ---------------- KauffmanBracket.lean ----------------
def cupCapEntry(a0, a1, b0, b1):
    key = (a0, a1, b0, b1)
    if key == (False, True, False, True): return -T(2)
    if key == (False, True, True, False): return ONE
    if key == (True, False, False, True): return ONE
    if key == (True, False, True, False): return -T(-2)
    return ZERO

def states(m): return list(product([False, True], repeat=m))

def tlGen(m, i):
    st = states(m); M = {}
    for a in st:
        for b in st:
            if i + 1 < m:
                if all(a[k] == b[k] for k in range(m) if k != i and k != i + 1):
                    v = cupCapEntry(a[i], a[i + 1], b[i], b[i + 1])
                else: v = ZERO
            else: v = ZERO
            if not v.is_zero(): M[(a, b)] = v
    return M

def mat_add(A, B):
    R = dict(A)
    for k, v in B.items():
        s = R.get(k, ZERO) + v
        if s.is_zero(): R.pop(k, None)
        else: R[k] = s
    return R
def mat_smul(c, A): return {k: c * v for k, v in A.items()}
def mat_one(m): return {(a, a): ONE for a in states(m)}
def mat_mul(A, B):
    rowsB = {}
    for (b, c), v in B.items(): rowsB.setdefault(b, []).append((c, v))
    R = {}
    for (a, b), v in A.items():
        for c, w in rowsB.get(b, ()):
            R[(a, c)] = R.get((a, c), ZERO) + v * w
    return {k: v for k, v in R.items() if not v.is_zero()}

def crossingMatrix(m, g):
    i, b = g
    if b: return mat_add(mat_smul(T(1), mat_one(m)), mat_smul(T(-1), tlGen(m, i)))
    else: return mat_add(mat_smul(T(-1), mat_one(m)), mat_smul(T(1), tlGen(m, i)))

def bracket_literal(m, w):
    P = mat_one(m)
    for g in reversed(w):          # List.prod = M1 * (M2 * (... * 1))
        P = mat_mul(crossingMatrix(m, g), P)
    D = {}
    for a in states(m):
        d = ONE
        for k in range(m): d = d * (-T(-2) if a[k] else -T(2))
        D[(a, a)] = d
    Q = mat_mul(D, P)
    tr = ZERO
    for a in states(m): tr = tr + Q.get((a, a), ZERO)
    return tr

# fast path -------------------------------------------------------------
def bracket_fast(m, w, chunk=128):
    """Same trace.  Uses crossing(true) = T^-3 (s^2 + E), crossing(false) = T^-1 (1 + E),
    E = T^2 * tlGen with entries (-s^2, s, s, -1), s = T^2; diag = (-1)^m T^(-2m) prod(1 if a_k else s^2).
    Polynomials in s are stored as integers via s = 2^B (balanced digits), B chosen from a proven bound:
    every factor has row-sum of |coeff| <= 3, so |coeff of trace| <= 2^m * 3^len(w)."""
    n = len(w)
    if m == 0: return ONE
    B = 64 * ((int(1.585 * n) + m + 8) // 64 + 1)
    s = 1 << B; s2 = s * s
    p = sum(1 for g in w if g[1]); q = n - p
    total = 0
    for wt in range(m + 1):
        sts = [x for x in range(1 << m) if bin(x).count("1") == wt]
        idx = {x: j for j, x in enumerate(sts)}; S = len(sts)
        pairs = {}
        for i in set(g[0] for g in w):
            ft = [j for j, x in enumerate(sts) if not (x >> i) & 1 and (x >> (i + 1)) & 1]
            tf = [idx[sts[j] ^ (1 << i) ^ (1 << (i + 1))] for j in ft]
            pairs[i] = (np.array(ft, dtype=int), np.array(tf, dtype=int))
        dprime = [1] * S
        for j, x in enumerate(sts):
            d = 1
            for k in range(m):
                if not (x >> k) & 1: d *= s2
            dprime[j] = d
        for r0 in range(0, S, chunk):
            r1 = min(S, r0 + chunk)
            P = np.zeros((r1 - r0, S), dtype=object)
            for r in range(r0, r1): P[r - r0, r] = 1
            for (i, b) in w:
                ft, tf = pairs[i]
                PFT = P[:, ft].copy(); PTF = P[:, tf].copy()
                if b: P = P * s2
                else: P = P.copy()
                if len(ft):
                    P[:, ft] = P[:, ft] + (PTF * s - PFT * s2)
                    P[:, tf] = P[:, tf] + (PFT * s - PTF)
            for r in range(r0, r1):
                total += dprime[r] * P[r - r0, r]
    # decode balanced base-2^B digits
    coeffs = {}; V = total; j = 0; half = 1 << (B - 1); mask = s - 1
    while V != 0:
        r = V & mask
        if r >= half: r -= s
        if r: coeffs[j] = r
        V = (V - r) >> B; j += 1
    sign = -1 if m % 2 else 1
    shift = -3 * p - q - 2 * m
    return LP({2 * e + shift: sign * v for e, v in coeffs.items()})

bracket = bracket_fast

# ---------------- ColoredJones.lean ----------------
def cableGen(c, g):
    i, b = g
    if b: return [(c * i + a + bb, True) for a in reversed(range(c)) for bb in range(c)]
    else: return [(c * i + a + bb, False) for a in range(c) for bb in reversed(range(c))]
def cable(c, w):
    out = []
    for g in w: out += cableGen(c, g)
    return out
def writhe(w): return sum(1 if g[1] else -1 for g in w)
def chebyshevBracket(m, w, k, br=None):
    br = br or bracket
    tot = ZERO
    for j in range(k // 2 + 1):
        tot = tot + ((-1) ** j * comb(k - j, j)) * br((k - 2 * j) * m, cable(k - 2 * j, w))
    return tot
def coloredJonesPos(m, w, k, br=None):
    wr = writhe(w)
    return ((-1) ** (k * (1 + abs(wr)))) * (T(-wr * ((k + 1) ** 2 - 1)) * chebyshevBracket(m, w, k, br))
def coloredJones(m, w, n, br=None):
    if n > 0: return coloredJonesPos(m, w, n - 1, br)
    if n < 0: return -coloredJonesPos(m, w, (-n) - 1, br)
    return ZERO

# ---------------- KnotGroup.lean ----------------
# free group elements: tuples of nonzero ints, generator k <-> k+1, inverse <-> -(k+1)
def fg_reduce(wd):
    out = []
    for x in wd:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    return tuple(out)
def fg_mul(*ws):
    r = []
    for wd in ws: r += list(wd)
    return fg_reduce(r)
def fg_inv(wd): return tuple(-x for x in reversed(wd))
def fg_of(k): return (k + 1,)
def fg_pow(wd, e):
    if e >= 0: return fg_mul(*([wd] * e))
    return fg_mul(*([fg_inv(wd)] * (-e)))

def artinGen(m, g, k):
    i, b = g
    if i + 1 < m:
        if k == i: return (i + 1, fg_of(k) if b else ())
        elif k == i + 1: return (i, () if b else fg_inv(fg_of(k)))
        else: return (k, ())
    else: return (k, ())
def artinHom(m, g, wd):
    out = ()
    for x in wd:
        k = abs(x) - 1
        k2, c = artinGen(m, g, k)
        img = fg_mul(c, fg_of(k2), fg_inv(c))
        out = fg_mul(out, img if x > 0 else fg_inv(img))
    return out
def artinWord(m, w, k):
    if not w: return (k, ())
    g, rest = w[0], w[1:]
    k1, c1 = artinWord(m, rest, k)
    k2, c2 = artinGen(m, g, k1)
    return (k2, fg_mul(artinHom(m, g, c1), c2))
def artinRels(m, w):
    rels = []
    for k in range(m):
        k2, c = artinWord(m, w, k)
        rels.append(fg_mul(fg_inv(fg_of(k)), c, fg_of(k2), fg_inv(c)))
    return rels
def meridian(m, w): return fg_of(0)
def longitude(m, w):
    k = 0; parts = []
    for j in range(m):
        parts.append(artinWord(m, w, k)[1])
        k = artinWord(m, w, k)[0]
    return fg_mul(*parts, fg_pow(fg_of(0), -writhe(w)))
