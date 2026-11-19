"""Peripheral data from the Lean definitions for 2-strand braids, symbolically (sympy)."""
import sys
sys.path.insert(0, sys.argv[1])
from leandefs import *
import sympy as sp
M, y, L = sp.symbols("M y L")

def show(wd): return " ".join(("x%d" % (abs(x) - 1)) + ("" if x > 0 else "^-1") for x in wd) or "1"
def expsum(wd): return sum(1 if x > 0 else -1 for x in wd)
def rho(wd, mats):
    R = sp.eye(2)
    for x in wd:
        A = mats[abs(x) - 1]
        R = R * (A if x > 0 else A.inv())
        R = R.applyfunc(sp.cancel)
    return R

X0 = sp.Matrix([[M, 1], [0, 1 / M]]); X1 = sp.Matrix([[M, 0], [y, 1 / M]])
for name, m, w in [("[(0,T)]^3", 2, [(0, True)] * 3), ("[(0,F)]^3", 2, [(0, False)] * 3),
                   ("[(0,T)]^5", 2, [(0, True)] * 5), ("[(0,F)]^5", 2, [(0, False)] * 5)]:
    rels = artinRels(m, w); lam = longitude(m, w)
    print("=====", name)
    for k in range(m): print("  artinWord k=%d -> (%d, %s)" % (k, artinWord(m, w, k)[0], show(artinWord(m, w, k)[1])))
    print("  relations:", [show(r) for r in rels])
    print("  longitude word:", show(lam), "| exponent sum:", expsum(lam))
    # Riley polynomial
    polys = []
    for r in rels:
        R = rho(r, [X0, X1]) - sp.eye(2)
        polys += [sp.numer(sp.together(e)) for e in R]
    g = 0
    for p_ in polys: g = sp.gcd(g, p_)
    g = sp.factor(g)
    print("  gcd of relation entries (Riley polynomial, up to units):", g)
    riley = [f for f, _ in sp.factor_list(g)[1] if f.has(y) and f != y]
    Lam = rho(lam, [X0, X1])
    for phi in riley:
        l10 = sp.rem(sp.numer(sp.together(Lam[1, 0])), phi, y)
        num, den = sp.fraction(sp.together(Lam[0, 0]))
        res = sp.factor(sp.resultant(sp.expand(L * den - num), phi, y))
        print("  factor", phi, ": rho(longitude)[1,0] mod phi =", sp.simplify(l10), "; (M,L) relation:", res)
        # commutation
        C = (rho(lam, [X0, X1]) * X0 - X0 * rho(lam, [X0, X1])).applyfunc(lambda e: sp.rem(sp.numer(sp.together(e)), phi, y))
        print("    [longitude, meridian] = 0 on this component:", C == sp.zeros(2, 2))
    # abelian representations: x0 = x1 = diag(M, 1/M)
    D = sp.Matrix([[M, 0], [0, 1 / M]])
    print("  abelian rep: rho(longitude) =", rho(lam, [D, D]).tolist())
    if len(w) == 3:
        h = fg_pow(fg_mul(fg_of(0), fg_of(1)), 3)
        for sgn, cand, nm in [(+1, fg_mul(h, fg_pow(fg_of(0), -6)), "(x0 x1)^3 x0^-6"), (-1, fg_mul(fg_inv(h), fg_pow(fg_of(0), 6)), "(x0 x1)^-3 x0^6")]:
            d = (rho(fg_mul(lam, fg_inv(cand)), [X0, X1]) - sp.eye(2)).applyfunc(lambda e: sp.rem(sp.numer(sp.together(e)), riley[0], y))
            print("  rho(longitude * (%s)^-1) == 1 on the irreducible component:" % nm, d == sp.zeros(2, 2))
