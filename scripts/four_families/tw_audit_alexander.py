"""Alexander polynomial of the closures of twWhiteheadWord (dumped from Lean) by the unreduced
Burau representation, exact rational arithmetic at t0 in {3,5,7,11}; compared with
d t^2 + (1-2d) t + d up to a unit +-t^k (same k and sign at all t0)."""
import os, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from tw_audit_lib import load, components, writhe, inv_word

def burau(m, w, t):
    B = [[Fr(int(i == j)) for j in range(m)] for i in range(m)]
    for i, e in w:
        # B <- B * g_i (acts on columns i, i+1)
        for row in B:
            x, y = row[i], row[i+1]
            if e > 0:   # block [[1-t, t],[1, 0]]
                row[i], row[i+1] = x*(1-t) + y, x*t
            else:       # inverse block [[0,1],[1/t, 1-1/t]]
                row[i], row[i+1] = y/t, x + y*(1-1/t)
    return B
def det(A):
    A = [r[:] for r in A]; n = len(A); d = Fr(1)
    for c in range(n):
        pv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if pv is None: return Fr(0)
        if pv != c: A[c], A[pv] = A[pv], A[c]; d = -d
        d *= A[c][c]
        for r in range(c+1, n):
            f = A[r][c] / A[c][c]
            if f: A[r] = [a - f*b for a, b in zip(A[r], A[c])]
    return d
def alex_val(m, w, t):
    B = burau(m, w, t)
    Mx = [[Fr(int(i == j)) - B[i][j] for j in range(m-1)] for i in range(m-1)]
    return det(Mx)   # (m-1)-minor of the Fox matrix I - Burau: the Alexander polynomial up to a unit
_c = {}
def alex_cached(m, w, t):
    k = (m, tuple(w), t)
    if k not in _c: _c[k] = alex_val(m, w, t)
    return _c[k]
def unit_exp(ratio, t):
    """return (sign, k) with ratio = sign * t^k, else None"""
    sg = 1 if ratio > 0 else -1; x = abs(ratio); k = 0
    while x > 1 and k < 400: x /= t; k += 1
    while x < 1 and k > -400: x *= t; k -= 1
    return (sg, k) if x == 1 else None
def match_d(m, w, d):
    res = set()
    for t in (Fr(3), Fr(5), Fr(7), Fr(11)):
        v = alex_cached(m, w, t); pred = d*t*t + (1-2*d)*t + d
        if v == 0: return False
        res.add(unit_exp(v / pred, t))
    return len(res) == 1 and None not in res

W, I, T, Pw = load(os.path.join(HERE, 'lean_words.txt'))
# self-test on known knots: trefoil d=1, figure-eight d=-1, unknot (sigma_0 on 2 strands) d=0, 5_2 = closure of s0^3 s1 s0^-1 s1 (d=2)
assert [d for d in range(-5, 6) if match_d(2, [(0,1)]*3, d)] == [1]
assert [d for d in range(-5, 6) if match_d(3, [(0,1),(1,-1),(0,1),(1,-1)], d)] == [-1]
assert [d for d in range(-5, 6) if match_d(2, [(0,1)], d)] == [0]
assert [d for d in range(-5, 6) if match_d(3, [(0,1)]*3+[(1,1),(0,-1),(1,1)], d)] == [2]
# the closure of a torus braid T(2,5) must match no d (Alexander polynomial of degree 4)
assert [d for d in range(-5, 6) if match_d(2, [(0,1)]*5, d)] == []
print('self-tests passed')
bad = 0
for (r, s, l, sg), (m, w) in sorted(W.items()):
    ds = [d for d in range(-5, 6) if match_d(m, w, d)]
    exp = l if sg else -l
    wr_pred = 2*(r-1)*s - 2*l + (-2 if sg else 2)
    ok = ds == [exp] and components(m, w) == 1 and writhe(w) == wr_pred
    bad += not ok
    print(f"(r,s)=({r},{s}) l={l:+d} sigma={'true ' if sg else 'false'} strands={m} len={len(w)} comps={components(m,w)} "
          f"writhe={writhe(w)} (Lean lemma {wr_pred}) Alexander d in {ds} expected d={exp} {'OK' if ok else 'MISMATCH'}")
print("mismatches:", bad)
