"""No order-1 element a(t,M) L + b(t,M) (deg_M <= D) kills the trefoil function for almost all n:
full column rank of the linear system modulo a prime at t = 3 (rank mod p <= generic rank)."""
import sys, pickle
p = (1 << 61) - 1; tv = 3
def J(n):  # closed formula (verified equal to the Lean definition for n<=6), evaluated mod p at t=tv
    inv = lambda x: pow(x, p - 2, p); tp = lambda e: pow(tv, e, p) if e >= 0 else inv(pow(tv, -e, p))
    term = sum(tp(-4 * j) for j in range(n)) % p; tot = 0
    for k in range(n):
        if k >= 1: term = term * (1 - tp(4 * k - 4 * n)) % p
        tot = (tot + tp(-4 * n * k) * term) % p
    return tp(2 - 2 * n) * tot % p
def rank(rows):
    rows = [r[:] for r in rows]; rk = 0; ncol = len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]; iv = pow(rows[rk][c], p - 2, p)
        rows[rk] = [x * iv % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]; rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk
for D in (4, 8, 16, 30):
    rows = []
    for n in range(40, 40 + 2 * (D + 1) + 8):      # large n: avoids any finite exceptional set of a multiplier c
        m_ = pow(tv, 2 * n, p); f0, f1 = J(n), J(n + 1)
        rows.append([pow(m_, j, p) * f1 % p for j in range(D + 1)] + [pow(m_, j, p) * f0 % p for j in range(D + 1)])
    print("deg_M <= %d: unknowns %d, rank mod p: %d" % (D, 2 * (D + 1), rank(rows)))
