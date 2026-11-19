"""Positive control in Le's own conventions (math/0407521, sections 0.1.3 and 0.2).

Le states that for the right-handed trefoil the recurrence polynomial is
  P = (t^4 M^10 - M^6) L^2 - (t^2 M^10 + t^-18 - t^-10 M^6 - t^-14 M^4) L + (t^-16 - t^-4 M^4),
that P J_K = 0 with J_K(0) = 0, J_K(1) = 1 determines J_K, and that at t = -1
  eps(alpha_K) = (M^4 - 1)(L - 1)(L M^6 + 1).
Here J is computed from the Lean definitions for the closure of sigma_0^3 (letters `true`), and P
is applied with (M f)(n) = t^(2n) f(n), (L f)(n) = f(n+1), exactly as the Lean `opApply`.
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_defs import coloredJones, lp, add, mul, scal, show

top = int(sys.argv[1]) if len(sys.argv) > 1 else 5
tre = [(0, True)] * 3
t0 = time.time()
J = {0: {}}
for n in range(1, top + 1):
    J[n] = coloredJones(2, tre, n)
    J[-n] = scal(-1, J[n])
    print(f"J({n}) has {len(J[n])} terms, degrees {min(J[n])}..{max(J[n])}   [{time.time()-t0:.0f}s]", flush=True)

def P_apply(f, n, sign=1):
    """coefficients of Le's P at M = t^(2n); `sign` = -1 replaces t by 1/t (mirror image)."""
    e = lambda k: lp(sign * k)
    a2 = add(e(4 + 20*n), scal(-1, e(12*n)))
    a1 = scal(-1, add(add(e(2 + 20*n), e(-18)), add(scal(-1, e(-10 + 12*n)), scal(-1, e(-14 + 8*n)))))
    a0 = add(e(-16), scal(-1, e(-4 + 8*n)))
    return add(add(mul(a2, f[n + 2]), mul(a1, f[n + 1])), mul(a0, f[n]))

rng = range(-top, top - 1)
ok = all(P_apply(J, n) == {} for n in rng)
print(f"Le's P annihilates the Lean J of sigma_0^3 for n in [{rng[0]}, {rng[-1]}]:", ok)
Jm = {n: {(-e): c for e, c in p.items()} for n, p in J.items()}       # mirror: t -> 1/t
print("Le's P annihilates the mirror function J(1/t):", all(P_apply(Jm, n) == {} for n in rng))
print("mirror function is annihilated by P(1/t, 1/M, L) (the mirror recurrence):",
      all(P_apply(J, n, 1) == {} for n in rng))
# sign-twisted function (-1)^(n-1) J(n): would need L -> -L
Js = {n: scal((-1) ** (abs(n) - 1) if n else 0, p) for n, p in J.items()}
print("Le's P annihilates (-1)^(n-1) J(n):", all(P_apply(Js, n) == {} for n in rng))

# classical limit of P at t = -1, as a polynomial in M, L
from sympy import symbols, factor, expand
M, L = symbols("M L")
t = -1
P_eps = (t**4*M**10 - M**6)*L**2 - (t**2*M**10 + t**-18 - t**-10*M**6 - t**-14*M**4)*L + (t**-16 - t**-4*M**4)
print("eps(P) =", factor(P_eps))
