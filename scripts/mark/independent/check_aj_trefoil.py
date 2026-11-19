"""End-to-end positive control on the closure of [(0,True)]^3, in the Lean variables.
RecOp = Z[t][M][L];  (P f)(n) = sum_i P_i(t, t^{2n}) f(n+i);  specialize: t -> -1."""
import sys, pickle, time, functools
print = functools.partial(print, flush=True)
sys.path.insert(0, sys.argv[1])
from leandefs import *
import sympy as sp
NDEF = int(sys.argv[2])
t, M, L = sp.symbols("t M L")
tref = (2, [(0, True)] * 3)

_cache = {}
def le_trefoil_unsigned(n):
    if n in _cache: return _cache[n]
    tot = ZERO
    term = sum((T(-4 * j) for j in range(n)), ZERO)      # (1-t^{-4n})/(1-t^-4), the i=0 factor
    for k in range(n):
        if k >= 1: term = term * (ONE - T(4 * k - 4 * n))
        tot = tot + T(-4 * n * k) * term
    _cache[n] = T(2 - 2 * n) * tot
    return _cache[n]

# values from the Lean definitions
Jdef = {0: ZERO}
for n in range(1, NDEF + 1):
    t0 = time.time(); Jdef[n] = coloredJones(*tref, n); Jdef[-n] = -Jdef[n]
    print("n=%d from definitions: %d terms, degrees [%d,%d], equals closed formula: %s  [%.1fs]" %
          (n, len(Jdef[n].c), min(Jdef[n].c), max(Jdef[n].c), Jdef[n] == le_trefoil_unsigned(n), time.time() - t0), flush=True)
assert all(coloredJones(*tref, -n) == Jdef[-n] for n in range(1, 4)) and coloredJones(*tref, 0) == ZERO

# Le's P (p.2), cleared of negative powers of t by t^18
P_le = (t**4 * M**10 - M**6) * L**2 - (t**2 * M**10 + t**-18 - t**-10 * M**6 - t**-14 * M**4) * L + (t**-16 - t**-4 * M**4)
P = sp.expand(t**18 * P_le)
coeffs = sp.Poly(P, L).all_coeffs()[::-1]          # P_0, P_1, P_2 in Z[t][M]
print("alpha (Lean variables) =", sp.collect(P, L))

def evalAt(c, n):
    """c in Z[t,M] -> Laurent polynomial, t -> T^1, M -> T^(2n)"""
    r = ZERO
    for (i, j), v in sp.Poly(c, t, M).terms():
        r = r + int(v) * T(i + 2 * n * j)
    return r
def opApply(cs, f, n):
    r = ZERO
    for i, c in enumerate(cs): r = r + evalAt(c, n) * f(n + i)
    return r

rng_def = range(-NDEF, NDEF - 1)
print("alpha annihilates the Lean-defined J for n in [%d,%d] (all windows inside computed range):" % (rng_def[0], rng_def[-1]),
      all(opApply(coeffs, lambda k: Jdef[k], n).is_zero() for n in rng_def))
Jf = lambda k: le_trefoil_unsigned(k) if k > 0 else (-le_trefoil_unsigned(-k) if k < 0 else ZERO)
print("alpha annihilates the closed formula (odd extension) for n in [-30,30]:", all(opApply(coeffs, Jf, n).is_zero() for n in range(-30, 31)))
Jsigned = lambda k: ((-1) ** (abs(k) - 1)) * Jf(k) if k else ZERO
print("alpha annihilates Le's formula AS PRINTED (with (-1)^(n-1)) for n in [1,10]:", all(opApply(coeffs, Jsigned, n).is_zero() for n in range(1, 11)))
# mirror control: does alpha annihilate the mirror function?  and the mirrored operator?
Jmir = lambda k: Jf(k).sub_T(-1)
print("alpha annihilates the MIRROR function J(n)(t^-1), n in [1,10]:", all(opApply(coeffs, Jmir, n).is_zero() for n in range(1, 11)))

# primitivity in Z[t][M] and specialisation
g = sp.gcd_list([sp.expand(c) for c in coeffs])
print("gcd of the L-coefficients in Z[t,M]:", g)
eps = sp.factor(P.subs(t, -1))
print("specialize(alpha) = alpha|_{t=-1} =", eps)

# no first-order element of the localized annihilator with M-degree <= D (rank test at a rational t)
tv = sp.Rational(3, 2)
for D in (4, 8, 12):
    rows = []
    for n in range(1, 2 * (D + 1) + 6):
        f0 = sum(sp.Integer(v) * tv**e for e, v in Jf(n).c.items()); f1 = sum(sp.Integer(v) * tv**e for e, v in Jf(n + 1).c.items())
        m_ = tv ** (2 * n)
        rows.append([m_**j * f1 for j in range(D + 1)] + [m_**j * f0 for j in range(D + 1)])
    A = sp.Matrix(rows)
    print("order-1 operators a(M)L+b(M), deg_M <= %d: unknowns %d, rank at t=3/2: %d" % (D, 2 * (D + 1), A.rank()))

# mirror: operator for the left-handed function, obtained from the same computation
ltref = (2, [(0, False)] * 3)
P_m = sp.expand(sp.expand(P.subs(t, 1 / t).subs(M, 1 / M)) * t**22 * M**10)
cm = sp.Poly(P_m, L).all_coeffs()[::-1]
Jl = {0: ZERO}
for n in range(1, min(NDEF, 5) + 1): Jl[n] = coloredJones(*ltref, n); Jl[-n] = -Jl[n]
r = range(-min(NDEF, 5), min(NDEF, 5) - 1)
print("mirror operator alpha(t^-1,M^-1,L)*t^22*M^10 =", sp.collect(P_m, L))
print("  annihilates Lean-defined J of [(0,False)]^3 on", (r[0], r[-1]), ":", all(opApply(cm, lambda k: Jl[k], n).is_zero() for n in r))
print("  its t=-1 specialisation:", sp.factor(P_m.subs(t, -1)))
