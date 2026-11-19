"""Is the refutation robust under a chirality mix-up between the two sides?

E  = L^2 - (M^4 - 4M^2 + 1) L + M^4          (the extra factor, `extraFactor`)
E' = M^4 L^2 - (M^4 - 4M^2 + 1) L + 1        (= L^2 E(M, 1/L) = M^4 E(1/M, L))
B_m = famB m  (AJFamily/Classical/FamilyPolynomials.lean), bound (L - 1) B_m.

E and E' are irreducible quadratics in L over Q(M) (discriminant (M^4-6M^2+1)(M^2-1)^2 is not a
square), so each is coprime to (L-1) B_m in Q(M)[L, 1/L] iff B_m mod it is nonzero.
"""
import sys
from sympy import symbols, Poly, expand, rem, simplify, factor, gcd, ZZ

M, L = symbols("M L")
x = M**2
P = (x - 1) * (1 - L)
Q = x + L
k = x * Q**2
tau = x**2*P*Q + x*P**2 - 2*x*P*Q + 2*x*Q**2 + P*Q
A = x**2*P*Q - x**2*Q**2 + x*P**2 - 3*x*P*Q + 3*x*Q**2 + P*Q - Q**2

def homcheb(n):
    a, b = 0, 1          # S_0, S_1
    if n == 0:
        return a
    for _ in range(n - 1):
        a, b = b, expand(tau*b - k**2*a)
    return b

def famB(m):
    return expand(A*homcheb(m) - k**2*homcheb(m - 1 if m >= 1 else 0))

E  = L**2 - (M**4 - 4*M**2 + 1)*L + M**4
Ep = M**4*L**2 - (M**4 - 4*M**2 + 1)*L + 1
assert expand(L**2*E.subs(L, 1/L) - Ep) == 0
assert expand(M**4*E.subs(M, 1/M) - Ep) == 0

top = int(sys.argv[1]) if len(sys.argv) > 1 else 24
bad = []
for m in range(1, top + 1):
    B = famB(m)
    PB = Poly(B, L, domain=ZZ[M])
    r1 = Poly(rem(B, E, L), L)      # remainder as polynomial in L with coefficients rational in M
    r2 = Poly(rem(B, Ep, L), L)
    z1, z2 = r1.is_zero, r2.is_zero
    # gcd over Q[M, L] as a cross-check (degree in L must be 0)
    g1 = Poly(gcd(expand((L - 1)*B), E), L).degree()
    g2 = Poly(gcd(expand((L - 1)*B), Ep), L).degree()
    print(f"m={m:2d}  deg_L B_m={PB.degree():3d}  B_m mod E  zero? {z1}  B_m mod E' zero? {z2}   deg_L gcd: E {g1}, E' {g2}")
    if z1 or z2 or g1 or g2:
        bad.append(m)
print("NOT coprime for m in", bad if bad else "none")
