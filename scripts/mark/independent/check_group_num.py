"""Numerical SL2(C) representations of the Lean KnotGroup for braid words on m strands.
rho(x0) = diag(M, 1/M) (so lower-left entry 0, top-left M); other generators trace M+1/M, det 1.
Gauge: b_1 = 1.  Gauss-Newton from random complex starts (seeded).  Returns (M, L) pairs,
L = rho(longitude)[0,0].  Then: nullspace fit of a polynomial in (M^2, L); asymptotic slopes."""
import sys, itertools
sys.path.insert(0, sys.argv[1])
from leandefs import *
import numpy as np

def mats_from(v, Mv, m):
    tau = Mv + 1 / Mv
    X = [np.array([[Mv, 0], [0, 1 / Mv]], dtype=complex)]
    a1 = v[0]; X.append(np.array([[a1, 1], [a1 * (tau - a1) - 1, tau - a1]], dtype=complex))
    for j in range(2, m):
        a, b, c = v[1 + 3 * (j - 2): 4 + 3 * (j - 2)]
        X.append(np.array([[a, b], [c, tau - a]], dtype=complex))
    return X
def ev(wd, X, Xi):
    R = np.eye(2, dtype=complex)
    for x in wd: R = R @ (X[x - 1] if x > 0 else Xi[-x - 1])
    return R
def residual(v, Mv, m, rels):
    X = mats_from(v, Mv, m); Xi = [np.linalg.inv(A) for A in X]
    out = []
    for j in range(2, m): out.append(np.linalg.det(X[j]) - 1)
    for r in rels: out += list((ev(r, X, Xi) - np.eye(2)).ravel())
    return np.array(out)
def solve(Mv, m, rels, rng, tries=200):
    nv = 1 + 3 * (m - 2); sols = []
    for _ in range(tries):
        v = rng.normal(size=nv) + 1j * rng.normal(size=nv)
        ok = False
        for it in range(80):
            F = residual(v, Mv, m, rels)
            if not np.all(np.isfinite(F)): break
            if np.linalg.norm(F) < 1e-12: ok = True; break
            J = np.zeros((len(F), nv), dtype=complex); h = 1e-7
            for k in range(nv):
                dv = np.zeros(nv, dtype=complex); dv[k] = h
                J[:, k] = (residual(v + dv, Mv, m, rels) - residual(v - dv, Mv, m, rels)) / (2 * h)
            try: step = np.linalg.lstsq(J, -F, rcond=None)[0]
            except Exception: break
            v = v + step
            if np.linalg.norm(v) > 1e6: break
        if ok and not any(np.linalg.norm(v - s) < 1e-6 for s in sols): sols.append(v)
    return sols

def analyse(name, m, w, maxMdeg, Ldeg, published=None, seed=0):
    print("=====", name, "word", [(i, "T" if b else "F") for i, b in w], "writhe", writhe(w))
    rels = artinRels(m, w); lam = longitude(m, w); rng = np.random.default_rng(seed)
    print("  longitude exponent sum:", sum(1 if x > 0 else -1 for x in lam), "; length", len(lam))
    pts = []; comm = 0; low = 0
    for t in range(40):
        Mv = np.exp(1j * rng.uniform(0.2, 2.9)) * rng.uniform(0.8, 1.25)
        sols = solve(Mv, m, rels, rng, tries=60)
        for v in sols:
            X = mats_from(v, Mv, m); Xi = [np.linalg.inv(A) for A in X]
            Lm = ev(lam, X, Xi)
            irreducible = abs(X[1][1, 0]) > 1e-7 or any(abs(A[1, 0]) > 1e-7 for A in X[2:])
            comm = max(comm, np.abs(Lm @ X[0] - X[0] @ Lm).max()); low = max(low, abs(Lm[1, 0]))
            if irreducible: pts.append((Mv, Lm[0, 0]))
        if t == 0: print("  first sample: M=%s, #solutions %d, L values %s" % (np.round(Mv, 4), len(sols), [np.round(ev(lam, mats_from(v, Mv, m), [np.linalg.inv(A) for A in mats_from(v, Mv, m)])[0, 0], 6) for v in sols]))
    print("  irreducible points collected: %d ; max |[lambda,mu]| = %.1e ; max |rho(lambda)[1,0]| = %.1e" % (len(pts), comm, low))
    # nullspace fit: monomials M^(2i) L^j
    for md in range(2, maxMdeg + 1, 2):
        mons = [(2 * i, j) for j in range(Ldeg + 1) for i in range(md // 2 + 1)]
        A = np.array([[Mv ** i * Lv ** j for (i, j) in mons] for Mv, Lv in pts])
        A = A / np.abs(A).max(axis=1, keepdims=True)
        U, S, Vh = np.linalg.svd(A)
        null = int((S < 1e-8 * S[0]).sum()) + max(0, len(mons) - len(S))
        if null >= 1:
            vec = Vh[-1].conj(); vec = vec / vec[np.argmax(np.abs(vec))]
            scale = min(abs(x) for x in vec if abs(x) > 1e-6); vec = vec / scale
            vec = vec / (vec[np.argmax(np.abs(vec))] / abs(vec[np.argmax(np.abs(vec))]))
            terms = {mons[k]: int(round(vec[k].real)) for k in range(len(mons)) if abs(vec[k]) > 1e-5}
            err = max(abs(vec[k] - round(vec[k].real)) for k in range(len(mons)))
            print("  minimal M-degree bound with nullspace: %d (dim %d, sing. values tail %s); rounding error %.1e" % (md, null, np.round(S[-2:] / S[0], 12), err))
            byL = {}
            for (i, j), c in sorted(terms.items(), key=lambda z: (z[0][1], z[0][0])): byL.setdefault(j, []).append("%+d*M^%d" % (c, i))
            for j in sorted(byL): print("     L^%d * (%s)" % (j, " ".join(byL[j])))
            newton = sorted(terms)
            print("     support (Mexp,Lexp):", newton)
            break
    else:
        print("  no polynomial found up to M-degree", maxMdeg)
    if published:
        for nm, f in published.items():
            print("  max |%s| over points: %.2e" % (nm, max(abs(f(Mv, Lv)) for Mv, Lv in pts)))
    # asymptotic slopes: |M| large
    for R in (4.0, 8.0):
        Mv = R * np.exp(0.7j); sols = solve(Mv, m, rels, rng, tries=80); sl = []
        for v in sols:
            X = mats_from(v, Mv, m); Xi = [np.linalg.inv(A) for A in X]
            if abs(X[1][1, 0]) > 1e-7 or any(abs(A[1, 0]) > 1e-7 for A in X[2:]):
                sl.append(round(float(np.log(abs(ev(lam, X, Xi)[0, 0])) / np.log(R)), 2))
        print("  |M|=%g: log|L|/log|M| for irreducible solutions: %s" % (R, sorted(sl)))

A52 = lambda M, L: 1 + L * (-1 + 2 * M**2 + 2 * M**4 - M**8 + M**10) + L**2 * (M**4 - M**6 + 2 * M**10 + 2 * M**12 - M**14) + L**3 * M**14
A41 = lambda M, L: -L + L * M**2 + M**4 + 2 * L * M**4 + L**2 * M**4 + L * M**6 - L * M**8
which = sys.argv[2:]
if "tref" in which:
    analyse("trefoil 2 strands", 2, [(0, True)] * 3, 8, 1, {"1+L M^6": lambda M, L: 1 + L * M**6, "L+M^6": lambda M, L: L + M**6})
if "fig8" in which:
    analyse("figure-eight", 3, [(0, True), (1, False), (0, True), (1, False)], 10, 2, {"CCGLS A(4_1)": A41})
if "52" in which:
    analyse("5_2 (1,1,1,2,-1,2)", 3, [(0, True)] * 3 + [(1, True), (0, False), (1, True)], 16, 3,
            {"recalled A(5_2)(M,L)": A52, "recalled A(5_2)(M,1/L)": lambda M, L: A52(M, 1 / L)})
if "52m" in which:
    analyse("mirror 5_2 (-1,-1,-1,-2,1,-2)", 3, [(0, False)] * 3 + [(1, False), (0, True), (1, False)], 16, 3,
            {"recalled A(5_2)(M,L)": A52, "recalled A(5_2)(M,1/L)": lambda M, L: A52(M, 1 / L)})
if "tref3" in which:   # trefoil as a 3-strand braid (stabilised): tests Markov stabilisation of the peripheral recipe
    analyse("trefoil stabilised +", 3, [(0, True)] * 3 + [(1, True)], 8, 1, {"1+L M^6": lambda M, L: 1 + L * M**6, "L+M^6": lambda M, L: L + M**6})
    analyse("trefoil stabilised -", 3, [(0, True)] * 3 + [(1, False)], 8, 1, {"1+L M^6": lambda M, L: 1 + L * M**6, "L+M^6": lambda M, L: L + M**6})
