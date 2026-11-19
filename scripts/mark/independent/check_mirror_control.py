"""What a mirrored side would look like: recurrence operator of the closure of [(0,False)]^3 (Lean J),
its t=-1 specialisation, versus the A-polynomial of the Lean group of [(0,True)]^3."""
import sys
sys.path.insert(0, sys.argv[1])
from leandefs import *
import sympy as sp
t, M, L = sp.symbols("t M L")
P = (M**10 * t**22 - M**6 * t**18) * L**2 + (-M**10 * t**20 + M**6 * t**8 + M**4 * t**4 - 1) * L - M**4 * t**14 + t**2
P_m = sp.expand(sp.expand(P.subs(t, 1 / t).subs(M, 1 / M)) * t**22 * M**10)
def evalAt(c, n):
    r = ZERO
    for (i, j), v in sp.Poly(c, t, M).terms(): r = r + int(v) * T(i + 2 * n * j)
    return r
def opApply(cs, f, n):
    r = ZERO
    for i, c in enumerate(cs): r = r + evalAt(c, n) * f(n + i)
    return r
for name, w, Q in [("[(0,False)]^3 with mirrored operator", [(0, False)] * 3, P_m), ("[(0,False)]^3 with alpha of the right-handed", [(0, False)] * 3, P),
                   ("[(0,True)]^3 with mirrored operator", [(0, True)] * 3, P_m)]:
    Jv = {0: ZERO}
    for n in range(1, 6): Jv[n] = coloredJones(2, w, n); Jv[-n] = -Jv[n]
    cs = sp.Poly(Q, L).all_coeffs()[::-1]
    print(name, ": annihilates Lean J on n in [-5,3]:", all(opApply(cs, lambda k: Jv[k], n).is_zero() for n in range(-5, 4)))
print("mirrored operator =", sp.collect(P_m, L))
print("gcd of its coefficients:", sp.gcd_list(sp.Poly(P_m, L).all_coeffs()))
print("its t=-1 specialisation:", sp.factor(P_m.subs(t, -1)))
print("alpha|_{t=-1}          :", sp.factor(P.subs(t, -1)))
