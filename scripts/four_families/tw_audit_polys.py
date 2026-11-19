"""Transliteration of the Lean definitions twistPoly, twistPolyNeg, twP, twBound, extraFactor,
extraFactorMirror, compared with the paper's (2), (B), (classicalcontainment)."""
from sympy import symbols, expand, cancel, together, fraction, factor, Poly, simplify, resultant, gcd
M, L, x, J = symbols('M L x J')
# ---- Lean side (x is the inner variable before the substitution x = M^2) ----
symbolZeta = x*J**2 - (x**2+1)*J + (x**2+x+1)
symbolZetaMoebius = (x**2+1)*L**2 - (x**4-2*x**3-2*x**2-2*x+1)*L + x**2*(x**2+1)
zetaMoebiusM = symbolZetaMoebius.subs(x, M**2)
def twistPoly(k):
    if k == 0: return 1
    if k == 1: return expand(zetaMoebiusM + M**2*(M**2*L+1)*(M**2+L) - (M**4+1)*(M**2+L)**2)
    return expand(zetaMoebiusM*twistPoly(k-1) - M**4*(M**2+L)**4*twistPoly(k-2))
def symbolTwistNeg(k):
    if k == 0: return 1
    if k == 1: return (x**2+1) - x*J
    return expand(symbolZeta*symbolTwistNeg(k-1) - x**2*symbolTwistNeg(k-2))
def moebiusSubst(d, p):
    P = Poly(p, J)
    return expand(sum(P.coeff_monomial(J**k)*(x*L+1)**k*(x+L)**(d-k) for k in range(d+1)))
def twistPolyNeg(b):
    return expand(moebiusSubst(2*b-1, symbolTwistNeg(b)).subs(x, M**2))
def twP(k): return twistPoly(k) if k >= 0 else twistPolyNeg(-k)
def twBound(k1, k2): return expand((L-1)*twP(k1)*twP(k2))
extraFactor = L**2 - (M**4-4*M**2+1)*L + M**4
extraFactorMirror = M**4*L**2 - (M**4-4*M**2+1)*L + 1
# ---- paper side ----
X = M**2
Jp = (X*L+1)/(L+X); K = X + 1/X; Z = 1 + K - K*Jp + Jp**2; e = 1 + Jp - K
Tm = {0: 1, 1: Z - 1 + e}
for k in range(1, 7): Tm[k+1] = Z*Tm[k] - Tm[k-1]
for k in range(0, -7, -1): Tm[k-1] = Z*Tm[k] - Tm[k+1]
def B(k): return cancel(X**k*(L+X)**(2*k)*Tm[k])
def Cc(k): return cancel(X**k*(L+X)**(2*k-1)*Tm[-k])
ok = True
for k in range(1, 7):
    a = expand(twistPoly(k) - B(k)) == 0; b = expand(twistPolyNeg(k) - Cc(k)) == 0
    ok &= a and b
    print(f"k={k}: Lean twistPoly k == paper B_k: {a};  Lean twistPolyNeg k == paper C_k: {b}")
print("twistPoly 0 =", twistPoly(0), "; twistPolyNeg 1 =", twistPolyNeg(1), "; twistPoly 1 =", factor(twistPoly(1)))
# E, E^vee: eq. (2)
E = lambda m, l: l**2 - (m**4-4*m**2+1)*l + m**4
print("extraFactor == E:", expand(extraFactor - E(M, L)) == 0,
      "; extraFactorMirror == M^4 E(1/M, L):", expand(extraFactorMirror - cancel(M**4*E(1/M, L))) == 0,
      "; == L^2 E(M, 1/L):", expand(extraFactorMirror - cancel(L**2*E(M, 1/L))) == 0)
# the reversed bound: Lean uses P.reverse (L -> 1/L); the paper transports by M -> 1/M. Same up to units +-M^i L^j ?
def reverseL(P_):
    p = Poly(P_, L); d = p.degree()
    return expand(L**d*P_.subs(L, 1/L))
def monomial_ratio(a, b):
    r = factor(cancel(a/b)); n, d = fraction(r)
    return r if (len(Poly(n, M, L).terms()) == 1 and len(Poly(d, M, L).terms()) == 1) else None
for (k1, k2) in [(1, 5), (-1, 6), (2, -3), (0, 6), (-2, -1), (3, 0)]:
    Pb = twBound(k1, k2)
    rev = reverseL(Pb); minv = cancel(Pb.subs(M, 1/M))
    print(f"twBound({k1},{k2}): reverse(L) / P(1/M, L) =", monomial_ratio(rev, minv),
          "; gcd(E^vee, reverse) =", gcd(extraFactorMirror, rev), "; gcd(E, bound) =", gcd(extraFactor, Pb))
print("ALL twist polynomials agree:", ok)
