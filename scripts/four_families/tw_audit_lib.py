"""Independent audit code (written from scratch for this audit).
- parse braid words dumped from Lean (#eval of twWhiteheadWord / invWord / torusPairWord)
- Kauffman bracket of a braid closure mod p at a numeric point t (tensor rep on weight spaces)
- Alexander polynomial via the unreduced Burau representation (exact, sympy)
- the paper's finite-sum formula (commoninput)+(claspfinite) evaluated mod p
"""
import itertools, json, random, sys
import numpy as np
from math import comb

P = 998244353

def load(path):
    W, I, T, Pw = {}, {}, {}, {}
    for line in open(path):
        f = line.split(' ')
        if f[0] in ('W', 'I'):
            r, s, l, sg, m = map(int, f[1:6]); w = json.loads(f[6])
            (W if f[0] == 'W' else I)[(r, s, l, bool(sg))] = (m, [(a, b) for a, b in w])
        elif f[0] in ('T', 'P'):
            r, s, m = map(int, f[1:4]); w = json.loads(f[4])
            (T if f[0] == 'T' else Pw)[(r, s)] = (m, [(a, b) for a, b in w])
    return W, I, T, Pw

def writhe(w): return sum(e for _, e in w)

def components(m, w):
    perm = list(range(m))
    for i, _ in w:
        perm[i], perm[i+1] = perm[i+1], perm[i]
    seen, c = set(), 0
    for x in range(m):
        if x not in seen:
            c += 1
            while x not in seen:
                seen.add(x); x = perm[x]
    return c

def inv_word(w): return [(i, -e) for i, e in reversed(w)]

def cable(c, w):
    out = []
    for i, e in w:
        if e > 0:
            for a in reversed(range(c)):
                for b in range(c): out.append((c*i + a + b, 1))
        else:
            for a in range(c):
                for b in reversed(range(c)): out.append((c*i + a + b, -1))
    return out

def weight_trace(m, w, k, t, p=P):
    """trace of prod (1 + lam*U_i) on the weight space with k ones (the scalar A^writhe is
    put back by the caller). U on (01,10) = [[a,1],[1,1/a]], a = -t^2."""
    states = [sum(1 << j for j in c) for c in itertools.combinations(range(m), k)]
    idx = {s: n for n, s in enumerate(states)}
    d = len(states)
    M = np.eye(d, dtype=np.int64)
    a = (-t*t) % p; ai = pow(a, p-2, p); ti = pow(t, p-2, p)
    pairs = {}
    for i in set(g for g, _ in w):
        i01 = [n for n, s in enumerate(states) if not (s >> i) & 1 and (s >> (i+1)) & 1]
        i10 = [idx[states[n] ^ (1 << i) ^ (1 << (i+1))] for n in i01]
        pairs[i] = (np.array(i01, dtype=np.int64), np.array(i10, dtype=np.int64))
    for i, e in w:
        lam = (ti*ti) % p if e > 0 else (t*t) % p   # sigma = t(1 + t^-2 U); sigma^-1 = t^-1(1 + t^2 U)
        c1 = (1 + lam*a) % p; c3 = (1 + lam*ai) % p
        i01, i10 = pairs[i]
        if len(i01) == 0: continue
        R0 = M[i01]; R1 = M[i10]
        M[i01] = (c1*R0 + lam*R1) % p
        M[i10] = (lam*R0 + c3*R1) % p
    return int(np.trace(M) % p)

def bracket_mod(m, w, t, p=P, check_sym=False):
    """Kauffman bracket <closure(w)> at t mod p, normalisation <unknot> = -t^2 - t^-2,
    positive letter = t*1 + t^-1*U (the convention of the Lean definition `bracket`)."""
    a = (-t*t) % p; ai = pow(a, p-2, p)
    tot = 0
    for k in range(0, m//2 + 1):
        tr = weight_trace(m, w, k, t, p)
        if check_sym:
            assert tr == weight_trace(m, w, m-k, t, p), "weight symmetry failed"
        if 2*k == m:
            tot += tr
        else:
            tot += tr * (pow(a, m-2*k, p) + pow(ai, m-2*k, p))
    wr = writhe(w)
    sc = pow(t, wr, p) if wr >= 0 else pow(pow(t, p-2, p), -wr, p)
    return tot * sc % p

def lean_colored_jones(m, w, n, t, p=P):
    """coloredJones K n of the Lean library for n = 1, 2, 3, evaluated at t mod p."""
    k = n - 1
    wr = writhe(w)
    ti = pow(t, p-2, p)
    def tp(e): return pow(t, e, p) if e >= 0 else pow(ti, -e, p)
    if k == 0: cheb = 1                      # bracket of 0 strands... k=0: (k-0)*m = 0 strands -> 1
    elif k == 1: cheb = bracket_mod(m, w, t, p)
    elif k == 2: cheb = (bracket_mod(2*m, cable(2, w), t, p) - 1) % p
    else: raise ValueError
    sign = (-1) ** (k * (1 + abs(wr)))
    return sign * tp(-wr * ((k+1)**2 - 1)) * cheb % p

# ---------- the paper's formula, mod p ----------
def inv(x, p=P): return pow(x % p, p-2, p)
def qpow(q, e, p=P): return pow(q, e, p) if e >= 0 else pow(inv(q, p), -e, p)
def qint_odd(q, j, p=P):
    """[j] for odd j (any sign) = sum_{i=-(j-1)/2}^{(j-1)/2} q^i ; [-j] = -[j]"""
    if j < 0: return (-qint_odd(q, -j, p)) % p
    h = (j-1)//2
    return sum(qpow(q, i, p) for i in range(-h, h+1)) % p
def poch(z, q, n, p=P):
    r = 1
    for i in range(n): r = r * (1 - z*qpow(q, i, p)) % p
    return r
def V(q, r, s, n, p=P):
    return sum(qpow(q, r*k*(s*k+1), p) * qint_odd(q, 2*s*k+1, p) for k in range(-n, n+1)) % p
def torus_odd(q, r, s, eta, n, p=P):
    """Phi_{T_eta}(2n+1) = q^{-eta m n(n+1)} V_n(q^eta)"""
    qq = q if eta > 0 else inv(q, p)
    return qpow(qq, -r*s*n*(n+1), p) * V(qq, r, s, n, p) % p
def F_neg(q, r, s, eta, ell, N, p=P, companion=None):
    """reduced F_N of W_{-,ell}(T_eta): sum_n beta_{N,n} q^{ell n(n+1)} Phi_T(2n+1)."""
    tot = 0
    for n in range(N):
        sm = 0
        for i in range(N-n):
            sm += qpow(q, -N*(i+n), p) * poch(qpow(q, i+1, p), q, n, p) * poch(qpow(q, N-i-n, p), q, n, p) * inv(poch(q, q, n, p), p)
        beta = qpow(q, N*N-1, p) * (1-q) * inv(1 - qpow(q, N, p), p) * sm % p
        phi = torus_odd(q, r, s, eta, n, p) if companion is None else companion(q, n)
        tot += beta * qpow(q, ell*n*(n+1), p) * phi
    return tot % p
def qint_t(t, N, p=P):
    ti = inv(t, p)
    return (pow(t, 2*N, p) - pow(ti, 2*N, p)) * inv(t*t - ti*ti, p) % p
def paper_Phi(t, r, s, negclasp, eta, ell, N, p=P):
    """Phi_S(N;t) of S = W_{eps,ell}(T_eta) by the paper: negative clasp by the finite sum,
    positive clasp by (mirror-marked): Phi_{W_{+,ell}(T_eta)}(N;t) = Phi_{W_{-,-ell}(T_{-eta})}(N;1/t)."""
    if negclasp:
        q = pow(t, 4, p)
        return qint_t(t, N, p) * F_neg(q, r, s, eta, ell, N, p) % p
    return paper_Phi(inv(t, p), r, s, True, -eta, -ell, N, p)
