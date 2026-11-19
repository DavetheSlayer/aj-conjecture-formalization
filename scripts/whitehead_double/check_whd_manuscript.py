"""Is the formalized closed braid the knot the manuscript names?

Independent invariant checks on the braid words evaluated from the Lean library
(`pairWhiteheadWord r s`), and on the braid printed in the source manuscript (eq. (braid)).

 1. one component, writhe;
 2. Alexander polynomial (Burau / Fox) is trivial  -> the double is untwisted;
 3. the Lean-proved closed formula F_N of the coloured Jones function equals Zheng's printed
    formula (2.7), (2.9), (4.1) of math/0508138v4 for WD(T(p,q), 0), colours N <= NMAX;
    controls: Zheng's formula with r = +-1 twists, with the clasp alone mirrored, and with
    everything mirrored must NOT agree;
 4. colour 2 computed directly from the braid by the line-by-line transcription of the Lean
    definition equals [2] F_2 (ties the formula transcription to the braid itself).

Usage: python3 check_whd_manuscript.py WORDS.txt LEAN_DEFS_DIR [heavy]
"""
import ast
import re
import sys
from fractions import Fraction as Fr

WORDS, DEFS = sys.argv[1], sys.argv[2]
HEAVY = len(sys.argv) > 3
sys.path.insert(0, DEFS)
import lean_defs as LD  # noqa: E402

NMAX = 6
POINTS = [Fr(3, 2), Fr(5, 3), Fr(7, 4)]

# ---------------------------------------------------------------- words
def load_words(path):
    out = {}
    for line in open(path):
        m = re.match(r'"(PW|WT|TP) ([0-9 ]+) (\[.*\])"', line.strip())
        if not m:
            continue
        key = (m.group(1),) + tuple(int(x) for x in m.group(2).split())
        out[key] = ast.literal_eval(m.group(3).replace('true', 'True').replace('false', 'False'))
    return out

W = load_words(WORDS)
# the braid printed in the source manuscript, eq. (braid) / `whiteheadTrefoilWord`
BETA = [(1, True), (0, True), (1, False), (4, True), (3, True), (2, True), (1, True), (2, False),
        (3, False), (4, False), (5, False), (2, True), (1, True), (0, True), (1, False), (2, False),
        (3, True), (2, True), (3, False), (4, True), (5, False), (2, True), (1, True), (2, False)]

def strands(r, s):
    return 2 * (r - 1) * s + 1

def n_components(m, w):
    perm = list(range(m))
    for i, _ in w:
        perm[i], perm[i + 1] = perm[i + 1], perm[i]
    seen, c = set(), 0
    for a in range(m):
        if a not in seen:
            c += 1
            while a not in seen:
                seen.add(a)
                a = perm[a]
    return c

# ---------------------------------------------------------------- Alexander polynomial
def burau_minor(m, w, t):
    """det of (I - Burau(w)) with the last row and column removed, at the number t."""
    M = [[Fr(int(i == j)) for j in range(m)] for i in range(m)]
    for i, pos in w:
        # right multiplication by the elementary Burau matrix: only columns i, i+1 change
        a, b, c, d = ((1 - t, t, Fr(1), Fr(0)) if pos else (Fr(0), Fr(1), 1 / t, 1 - 1 / t))
        for row in M:
            x, y = row[i], row[i + 1]
            row[i], row[i + 1] = x * a + y * c, x * b + y * d
    n = m - 1
    A = [[Fr(int(i == j)) - M[i][j] for j in range(n)] for i in range(n)]
    det = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            det = -det
        det *= A[c][c]
        inv = 1 / A[c][c]
        for r in range(c + 1, n):
            if A[r][c] != 0:
                f = A[r][c] * inv
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return det

def alexander_is_trivial(m, w):
    """True iff the minor is +- t^k with one sign and one k at every test point."""
    pts = [Fr(p) for p in range(2, 22)] + [Fr(1, p) for p in range(2, 22)]
    sig = set()
    for t in pts:
        v = burau_minor(m, w, t)
        if v == 0:
            return False, None
        sgn = 1 if v > 0 else -1
        v = abs(v)
        k, x = 0, v
        # v must be an integer power of t
        tt = t if t > 1 else 1 / t
        y = x if x >= 1 else 1 / x
        e = 0
        while y > 1:
            y /= tt
            e += 1
        if y != 1:
            return False, None
        k = e if (x >= 1) == (t > 1) else -e
        sig.add((sgn, k))
    return len(sig) == 1, sig

def alexander_values(m, w, pts=(2, 3, 5)):
    return [burau_minor(m, w, Fr(p)) for p in pts]

# ---------------------------------------------------------------- Lean closed formula
def quantumInt(T, m):
    return (T ** (2 * m) - T ** (-2 * m)) / (T ** 2 - T ** (-2))

def qPoch(T, a, j):
    q = T ** 4
    r = 1
    for s in range(j):
        r = r * (1 - a * q ** s)
    return r

def pairQOddColor(T, r, s, n):
    q = T ** 4
    return q ** (-(r * s * n * (n + 1))) * sum(
        q ** (r * k * (s * k + 1)) * quantumInt(T, 2 * s * k + 1) for k in range(-n, n + 1))

def pairQCycloCoeff(T, u, j):
    q = T ** 4
    return q ** j * (1 - q) * qPoch(T, q, j) * sum(
        (-1) ** n * q ** (n * (n + 1) // 2) * u(n) / (qPoch(T, q, j - n) * qPoch(T, q, j + n + 1))
        for n in range(j + 1))

def cyclotomicKernel(T, j, N):
    q = T ** 4
    r = 1
    for s in range(1, j + 1):
        r = r * (1 - q ** (s + N)) * (1 - q ** (s - N))
    return r

def lean_F(T, r, s, N):
    u = lambda n: pairQOddColor(T, r, s, n)
    return sum(cyclotomicKernel(T, j, N) * pairQCycloCoeff(T, u, j) for j in range(N))

# ---------------------------------------------------------------- Zheng's printed formula
# x = t_Z^(1/2).  clasp_x, comp_x allow mirroring the clasp and the companion separately.
def zheng_xi(x, N, n):
    t = x * x
    tot = 0
    for i in range(N - n):
        term = t ** (-N * (i + n))
        for j in range(1, n + 1):
            term = term * (1 - t ** (N - i - j)) * (1 - t ** (i + j)) / (1 - t ** j)
        tot = tot + term
    return x ** ((N * N - 1) + N * (N - 1)) * tot

def zheng_torus(x, p, q, m):
    """(4.1) for odd m = 2n+1 (normalized, unknot = 1)."""
    t = x * x
    n = (m - 1) // 2
    return t ** (-p * q * n * (n + 1)) / (x ** m - x ** (-m)) * sum(
        t ** (p * k * (q * k + 1)) * (x ** (2 * q * k + 1) - x ** (-(2 * q * k + 1)))
        for k in range(-n, n + 1))

def zheng_WD(x, p, q, N, twist=0, clasp_x=None, comp_x=None, unknot=False):
    cx = x if clasp_x is None else clasp_x
    kx = x if comp_x is None else comp_x
    t = x * x
    tot = 0
    for n in range(N):
        JK = 1 if unknot else zheng_torus(kx, p, q, 2 * n + 1)
        tot = tot + ((x ** (2 * n + 1) - x ** (-(2 * n + 1))) / (x ** N - x ** (-N))
                     * t ** (twist * n * (n + 1)) * zheng_xi(cx, N, n) * JK)
    return tot

def ev(poly, T):
    return sum(c * T ** e for e, c in poly.items())

# ---------------------------------------------------------------- run
ok = True
def report(name, good, extra=''):
    global ok
    ok = ok and good
    print(('PASS  ' if good else 'FAIL  ') + name + (('   ' + extra) if extra else ''))

print('== 0. sanity of the tools')
t = Fr(5)
report('Burau minor of the trefoil = t^2 - t + 1 up to a unit',
       abs(burau_minor(2, [(0, True)] * 3, t)) in {(t * t - t + 1) * t ** k for k in range(-3, 4)})
report('Burau minor of the figure-eight = t^2 - 3t + 1 up to a unit',
       abs(burau_minor(3, [(0, True), (1, False)] * 2, t)) in
       {abs(t * t - 3 * t + 1) * t ** k for k in range(-4, 5)})
report("Zheng's formula gives 1 for the double of the unknot, N <= 6",
       all(zheng_WD(T * T, 1, 1, N, unknot=True) == 1 for N in range(1, 7) for T in POINTS))
T = POINTS[0]
report("Zheng's (4.1) at colour 3 is symmetric in (p, q)",
       zheng_torus(T * T, 3, 4, 3) == zheng_torus(T * T, 4, 3, 3))

print('== 1. components, writhe')
cases = [(k[1], k[2]) for k in W if k[0] == 'PW']
for (r, s) in cases:
    w, m = W[('PW', r, s)], strands(r, s)
    report(f'({r},{s}): {m} strands, {len(w)} crossings, one component, writhe 2(r-1)s-2',
           n_components(m, w) == 1 and LD.writhe(w) == 2 * (r - 1) * s - 2,
           f'writhe {LD.writhe(w)}')
report('source manuscript braid: 7 strands, 24 crossings, one component, writhe 4',
       n_components(7, BETA) == 1 and LD.writhe(BETA) == 4 and len(BETA) == 24)
report('Lean word (2,3) is NOT letter-for-letter the source manuscript braid (two presentations)',
       W[('PW', 2, 3)] != BETA)
report('family word k=1,2 equals pair word (2,3), (2,5)',
       W[('WT', 1)] == W[('PW', 2, 3)] and W[('WT', 2)] == W[('PW', 2, 5)])

print('== 2. Alexander polynomial trivial (untwisted double)')
for (r, s) in cases:
    good, sig = alexander_is_trivial(strands(r, s), W[('PW', r, s)])
    report(f'({r},{s}): minor = +-t^k at 40 rational points', good, f'(sign, k) = {sig}')
good, sig = alexander_is_trivial(7, BETA)
report('source manuscript braid: minor = +-t^k at 40 rational points', good, f'(sign, k) = {sig}')
for (r, s) in cases:
    tw = W.get(('TP', r, s))
    if tw:
        v = alexander_values(r, tw)
        report(f'control: companion braid T({r},{s}) has a NONtrivial Alexander polynomial',
               not alexander_is_trivial(r, tw)[0], f'values at 2,3,5: {[str(x) for x in v]}')

print("== 3. Lean closed formula F_N  vs  Zheng's printed formula, N = 1..%d, exact at %d points"
      % (NMAX, len(POINTS)))
for (r, s) in cases:
    res = {}
    for name, f in [
        ('Zheng r=0, t_Z = q', lambda T, N: zheng_WD(T * T, r, s, N)),
        ('everything mirrored (t_Z = 1/q)', lambda T, N: zheng_WD(1 / (T * T), r, s, N)),
        ('clasp alone mirrored', lambda T, N: zheng_WD(T * T, r, s, N, clasp_x=1 / (T * T))),
        ('companion alone mirrored', lambda T, N: zheng_WD(T * T, r, s, N, comp_x=1 / (T * T))),
        ('one twist, r=+1', lambda T, N: zheng_WD(T * T, r, s, N, twist=1)),
        ('one twist, r=-1', lambda T, N: zheng_WD(T * T, r, s, N, twist=-1)),
    ]:
        res[name] = all(f(T, N) == lean_F(T, r, s, N) for N in range(1, NMAX + 1) for T in POINTS)
        # agreement at N = 2 alone (N = 1 is trivially 1 for every variant)
        res[name + ' @N=2'] = all(f(T, 2) == lean_F(T, r, s, 2) for T in POINTS)
    report(f'({r},{s}): Lean F_N = Zheng WD(T({r},{s}), 0) with t_Zheng = q = T^4', res['Zheng r=0, t_Z = q'])
    for name in ['everything mirrored (t_Z = 1/q)', 'clasp alone mirrored', 'companion alone mirrored',
                 'one twist, r=+1', 'one twist, r=-1']:
        report(f'    control must differ already at N=2: {name}', not res[name + ' @N=2'])

print('== 4. colour 2 directly from the braid (transcribed Lean definition) vs [2] F_2 and Zheng')
todo = [('Lean word (2,3)', 7, W[('PW', 2, 3)], (2, 3)), ('source manuscript braid', 7, BETA, (2, 3))]
if HEAVY:
    todo.append(('Lean word (2,5)', 11, W[('PW', 2, 5)], (2, 5)))
polys = {}
for name, m, w, (r, s) in todo:
    P = LD.coloredJones(m, w, 2)
    polys[name] = P
    good = all(ev(P, T) == quantumInt(T, 2) * lean_F(T, r, s, 2) == quantumInt(T, 2) * zheng_WD(T * T, r, s, 2)
               for T in POINTS)
    report(f'{name}: coloredJones(2) = [2] F_2 = [2] Zheng_2', good)
    if (r, s) == (2, 3) and name.startswith('Lean'):
        print('      J(2) =', LD.show(P))
report('source manuscript braid and Lean word (2,3) have the same colour-2 polynomial',
       polys['Lean word (2,3)'] == polys['source manuscript braid'])
# the value F_2 printed in the source manuscript, in q = T^4
F2 = {8: 1, 4: -1, 0: 1, -4: -1, -8: 1, -12: -1, -16: 1, -28: 1, -32: -1, -36: 1, -40: -2, -44: 1}
report('F_2 printed in the source manuscript equals the Lean formula at N = 2',
       all(ev(F2, T) == lean_F(T, 2, 3, 2) for T in POINTS))

print('== 5. symbolic identity in Q(T) (needs sympy; skipped otherwise)')
try:
    import sympy as sp
except ImportError:
    sp = None
    print('SKIP  sympy not available')
if sp is not None:
    X = sp.Symbol('T')
    for (r, s, top) in [(2, 3, 4), (2, 5, 3), (3, 4, 3), (3, 5, 2)]:
        good = all(sp.cancel(sp.together(lean_F(X, r, s, N) - zheng_WD(X * X, r, s, N))) == 0
                   for N in range(1, top + 1))
        report(f'({r},{s}): F_N - Zheng_N cancels to 0 as a rational function, N = 1..{top}', good)
    d = sp.cancel(sp.together(lean_F(X, 2, 3, 2) - zheng_WD(X * X, 2, 3, 2, clasp_x=1 / (X * X))))
    report('control: with the clasp alone mirrored the difference is a nonzero rational function', d != 0)
    P = polys['Lean word (2,3)']
    lhs = sum(c * X ** e for e, c in P.items())
    report('colour 2 of the Lean braid (2,3), as a Laurent polynomial, equals [2] * Zheng_2 exactly',
           sp.cancel(sp.together(lhs - quantumInt(X, 2) * zheng_WD(X * X, 2, 3, 2))) == 0)

print()
print('ALL PASS' if ok else 'SOME CHECK FAILED')
sys.exit(0 if ok else 1)
