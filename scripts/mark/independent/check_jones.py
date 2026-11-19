"""Coloured Jones from the Lean definitions vs published formulas."""
import sys, time, pickle
sys.path.insert(0, sys.argv[1])
from leandefs import *
outdir = sys.argv[2]
NMAX_TREF = int(sys.argv[3]) if len(sys.argv) > 3 else 5

def qn(n):  # [n] = (t^{2n}-t^{-2n})/(t^2-t^-2)
    return sum((T(2 * (n - 1 - 2 * j)) for j in range(n)), ZERO)

def le_trefoil(n, signed=True):
    """Le, sec 0.1.3 (p.2): J_K(n) = (-1)^{n-1} t^{2-2n}/(1-t^-4) sum_{k=0}^{n-1} t^{-4nk} prod_{i=0}^{k} (1-t^{4i-4n})."""
    tot = ZERO
    for k in range(n):
        term = sum((T(-4 * j) for j in range(n)), ZERO)   # (1-t^{-4n})/(1-t^-4), the i=0 factor
        for i in range(1, k + 1): term = term * (ONE - T(4 * i - 4 * n))
        tot = tot + T(-4 * n * k) * term
    r = T(2 - 2 * n) * tot
    return ((-1) ** (n - 1)) * r if signed else r

def habiro_fig8(n):
    tot = ZERO
    for k in range(n):
        term = ONE
        for j in range(1, k + 1):
            term = term * (T(2 * (n + j)) - T(-2 * (n + j))) * (T(2 * (n - j)) - T(-2 * (n - j)))
        tot = tot + term
    return qn(n) * tot

def jonesV(coeffs):  # V(t_J) given as {power: coeff}; substitute t_J = T^-4
    return LP({-4 * e: v for e, v in coeffs.items()})
mirror = lambda p: p.sub_T(-1)

tref = (2, [(0, True)] * 3)
ltref = (2, [(0, False)] * 3)
fig8 = (3, [(0, True), (1, False), (0, True), (1, False)])
k52 = (3, [(0, True)] * 3 + [(1, True), (0, False), (1, True)])
t25 = (2, [(0, True)] * 5)

print("== unknot (1 strand, empty word): J(n) == [n] for n=1..5:", all(coloredJones(1, [], n) == qn(n) for n in range(1, 6)))
print("== unknot via stabilised braid [(0,True)] on 2 strands, n=1..4:", all(coloredJones(2, [(0, True)], n) == qn(n) for n in range(1, 5)),
      "; [(0,False)]:", all(coloredJones(2, [(0, False)], n) == qn(n) for n in range(1, 5)))

V_RH = {1: 1, 3: 1, 4: -1}          # Jones 1985: right-handed trefoil t + t^3 - t^4  (skein 1/t V+ - t V- = (sqrt t - 1/sqrt t) V0)
J2 = coloredJones(*tref, 2)
print("== trefoil [(0,T)]^3: J(2) =", J2)
print("   J(2) == [2]*V_RH(t_J=T^-4):", J2 == qn(2) * jonesV(V_RH), "; == [2]*V_RH(t_J=T^4) (mirror):", J2 == qn(2) * mirror(jonesV(V_RH)))
vals = {}
for n in range(1, NMAX_TREF + 1):
    t0 = time.time(); v = coloredJones(*tref, n); vals[n] = v
    a = le_trefoil(n, True); b = le_trefoil(n, False)
    print("   n=%d  ==Le formula as printed: %s ; ==Le formula without (-1)^(n-1): %s ; ==mirror(unsigned): %s ; value at T=1: %d  [%.1fs]"
          % (n, v == a, v == b, v == mirror(b), sum(v.c.values()), time.time() - t0))
pickle.dump({n: v.c for n, v in vals.items()}, open(outdir + "/trefoil_J.pkl", "wb"))
print("== left trefoil [(0,F)]^3: J(n) == mirror of right, n=1..4:", all(coloredJones(*ltref, n) == mirror(vals[n]) for n in range(1, 5)))
print("   negative n: J(-n) == -J(n), J(0)==0:", all(coloredJones(*tref, -n) == -vals[n] for n in range(1, 4)), coloredJones(*tref, 0) == ZERO)

print("== figure-eight braid", fig8[1])
for n in range(1, 5):
    t0 = time.time(); v = coloredJones(*fig8, n)
    print("   n=%d == [n]*Habiro: %s ; palindromic: %s [%.1fs]" % (n, v == habiro_fig8(n), v == mirror(v), time.time() - t0))

print("== 5_2 braid (KnotInfo 1,1,1,2,-1,2 with 1 -> (0,True))")
J2 = coloredJones(*k52, 2)
# V(5_2), Knot Atlas form: -q^-6 + q^-5 - q^-4 + 2q^-3 - q^-2 + q^-1  ; mirror has positive powers
V52_neg = {-6: -1, -5: 1, -4: -1, -3: 2, -2: -1, -1: 1}
V52_pos = {-e: v for e, v in V52_neg.items()}
print("   J(2) =", J2)
print("   J(2)==[2]*V(t_J=T^-4) with V = t - t^2 + 2t^3 - t^4 + t^5 - t^6 :", J2 == qn(2) * jonesV(V52_pos),
      "; with V = t^-1 - t^-2 + ... - t^-6:", J2 == qn(2) * jonesV(V52_neg))
print("== T(2,5) [(0,T)]^5")
J2 = coloredJones(*t25, 2)
V25_pos = {2: 1, 4: 1, 5: -1, 6: 1, 7: -1}   # positive T(2,5): t^2 + t^4 - t^5 + t^6 - t^7
print("   J(2)==[2]*V(t_J=T^-4), V = t^2+t^4-t^5+t^6-t^7:", J2 == qn(2) * jonesV(V25_pos))
