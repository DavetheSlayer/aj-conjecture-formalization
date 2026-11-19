"""Line-by-line transcription of the Lean definitions of the two AJ invariants
(AJConjecture/KauffmanBracket.lean, ColoredJones.lean, KnotGroup.lean), for calibration.

Laurent polynomials in T are dicts {exponent: integer coefficient}.
Free-group words are tuples of (generator index, +1 / -1), reduced on the fly.
"""
from itertools import product
from math import comb

# ---------------- Laurent polynomials ----------------
def lp(e, c=1): return {e: c} if c else {}
def add(p, q):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, 0) + c
        if r[e] == 0: del r[e]
    return r
def mul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            r[e1 + e2] = r.get(e1 + e2, 0) + c1 * c2
    return {e: c for e, c in r.items() if c}
def scal(c, p): return {e: c * v for e, v in p.items()} if c else {}

# ---------------- KauffmanBracket.lean ----------------
def cupCapEntry(a0, a1, b0, b1):
    key = (a0, a1, b0, b1)
    if key == (False, True, False, True): return lp(2, -1)
    if key == (False, True, True, False): return lp(0, 1)
    if key == (True, False, False, True): return lp(0, 1)
    if key == (True, False, True, False): return lp(-2, -1)
    return {}

def apply_tlGen(m, i, vec):
    """vec: dict state(tuple of bool) -> Laurent poly; returns vec * tlGen (row vector action):
    (v M)[b] = sum_a v[a] M[a, b]."""
    out = {}
    for a, coeff in vec.items():
        for b0, b1 in product((False, True), repeat=2):
            e = cupCapEntry(a[i], a[i + 1], b0, b1)
            if e:
                b = a[:i] + (b0, b1) + a[i + 2:]
                out[b] = add(out.get(b, {}), mul(coeff, e))
    return {s: p for s, p in out.items() if p}

def apply_crossing(m, g, vec):
    i, pos = g
    e = apply_tlGen(m, i, vec)
    c_id, c_e = (lp(1), lp(-1)) if pos else (lp(-1), lp(1))
    out = {s: mul(c_id, p) for s, p in vec.items()}
    for s, p in e.items():
        out[s] = add(out.get(s, {}), mul(c_e, p))
    return {s: p for s, p in out.items() if p}

def bracket(m, w):
    """trace(diagonal(prod_k (if a k then -T^-2 else -T^2)) * prod crossingMatrix)."""
    total = {}
    for a in product((False, True), repeat=m):
        vec = {a: lp(0)}
        for g in w:
            vec = apply_crossing(m, g, vec)
        d = lp(0)
        for bit in a:
            d = mul(d, lp(-2, -1) if bit else lp(2, -1))
        total = add(total, mul(d, vec.get(a, {})))
    return total

# ---------------- ColoredJones.lean ----------------
def cableGen(c, g):
    i, pos = g
    if pos:
        return [(c * i + a + b, True) for a in reversed(range(c)) for b in range(c)]
    return [(c * i + a + b, False) for a in range(c) for b in reversed(range(c))]
def cable(c, w): return [h for g in w for h in cableGen(c, g)]
def writhe(w): return sum(1 if g[1] else -1 for g in w)
def chebyshevBracket(m, w, k):
    tot = {}
    for j in range(k // 2 + 1):
        tot = add(tot, scal((-1) ** j * comb(k - j, j), bracket((k - 2 * j) * m, cable(k - 2 * j, w))))
    return tot
def coloredJonesPos(m, w, k):
    wr = writhe(w)
    return scal((-1) ** (k * (1 + abs(wr))), mul(lp(-wr * ((k + 1) ** 2 - 1)), chebyshevBracket(m, w, k)))
def coloredJones(m, w, n):
    if n > 0: return coloredJonesPos(m, w, n - 1)
    if n < 0: return scal(-1, coloredJonesPos(m, w, -n - 1))
    return {}

# ---------------- KnotGroup.lean ----------------
def red(word):
    out = []
    for x in word:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]: out.pop()
        else: out.append(x)
    return tuple(out)
def inv(word): return tuple((g, -e) for g, e in reversed(word))
def artinGen(m, g, k):
    i, pos = g
    if i + 1 < m:
        if k == i: return (i + 1, ((k, 1),) if pos else ())
        if k == i + 1: return (i, () if pos else ((k, -1),))
    return (k, ())
def artinHom(m, g, word):
    out = ()
    for (k, e) in word:
        j, u = artinGen(m, g, k)
        img = red(u + ((j, 1),) + inv(u))
        out = red(out + (img if e == 1 else inv(img)))
    return out
def artinWord(m, w, k):
    if not w: return (k, ())
    g, rest = w[0], w[1:]
    j, u = artinWord(m, rest, k)
    jj, c = artinGen(m, g, j)
    return (jj, red(artinHom(m, g, u) + c))
def relators(m, w):
    rels = []
    for k in range(m):
        j, u = artinWord(m, w, k)
        rels.append(red(((k, -1),) + u + ((j, 1),) + inv(u)))
    return rels
def longitude_word(m, w):
    k, out = 0, ()
    for _ in range(m):
        j, u = artinWord(m, w, k)
        out = red(out + u)
        k = j
    wr = writhe(w)
    out = red(out + tuple([(0, -1 if wr > 0 else 1)] * abs(wr)))
    return out

def show(p):
    return " + ".join(f"{c}*T^{e}" for e, c in sorted(p.items())) or "0"
def showw(word):
    return " ".join(f"x{g}" + ("" if e == 1 else "^-1") for g, e in word) or "1"

if __name__ == "__main__":
    tre = [(0, True)] * 3
    print("unknot J(1..4):", [show(coloredJones(1, [], n)) for n in range(1, 5)])
    print("trefoil sigma0^3, writhe", writhe(tre))
    print("  bracket      :", show(bracket(2, tre)))
    j2 = coloredJones(2, tre, 2)
    print("  coloredJones 2:", show(j2))
    target = mul(add(lp(2), lp(-2)), add(add(lp(-4), lp(-12)), lp(-16, -1)))
    print("  equals (T^2+T^-2)(T^-4+T^-12-T^-16):", j2 == target)
    print("  relators :", [showw(r) for r in relators(2, tre)])
    print("  longitude:", showw(longitude_word(2, tre)))
