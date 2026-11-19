"""Colour-2 coloured Jones function (Lean definition `coloredJones K 2`, re-implemented) of the
closed braids twFamilyKnot r s h sigma eta l, at t1 and 1/t1 mod p, against the paper's formula
(commoninput)+(claspfinite) at N = 2 and the mirror identity (mirror-marked)."""
import os, sys, random, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from tw_audit_lib import *
W, I, T, Pw = load(os.path.join(HERE, 'lean_words.txt'))
random.seed(77)
t1 = random.randrange(2, P-1); pts = [t1, inv(t1)]
print("p =", P, "points t1, 1/t1 =", pts, flush=True)
todo = [(2,3,l) for l in (0,-1,-2,1,-3,2)] + [(2,5,l) for l in (0,-1,-2)]
J = {}   # (r,s,l,sg) -> [J2(t1), J2(1/t1)] of W ; JI likewise of invWord W
JI = {}
for (r, s, l) in todo:
    for sg in (True, False):
        m, w = W[(r, s, l, sg)]
        t0 = time.time()
        J[(r,s,l,sg)] = [lean_colored_jones(m, w, 2, t) for t in pts]
        if m <= 11:
            mi, wi = I[(r, s, l, sg)]
            direct = [lean_colored_jones(mi, wi, 2, t) for t in pts]
            assert direct == J[(r,s,l,sg)][::-1], "bar identity J(inv w)(t)=J(w)(1/t) failed"
            how = "computed directly (and = bar of J(w))"
        else:
            how = "by the bar identity J(inv w)(t) = J(w)(1/t)"
        JI[(r,s,l,sg)] = J[(r,s,l,sg)][::-1]
        print(f"word W(r,s,l,sigma)=({r},{s},{l:+d},{sg}) strands {m} len {len(w)}: J2 done in {time.time()-t0:.1f}s; inverse word {how}", flush=True)
cands = [(nc, eta, ell) for nc in (True, False) for eta in (1, -1) for ell in range(-4, 5)]
bad = 0
for (r, s) in ((2,3), (2,5)):
    for sg in (True, False):          # sigma: True = negative clasp
        for eta in (True, False):
            for l in range(-3, 4):
                key = (r, s, l, sg) if eta else (r, s, -l, not sg)
                src = J if eta else JI
                if key not in src: continue
                val = src[key]
                match = [c for c in cands if all(paper_Phi(t, r, s, c[0], c[1], c[2], 2) == v for t, v in zip(pts, val))]
                exp = (sg, 1 if eta else -1, l)
                ok = match == [exp]
                bad += not ok
                print(f"twFamilyKnot {r} {s} sigma={sg} eta={eta} l={l:+d}: J_Lean(2) equals paper Phi(2) exactly for (negclasp,eta,l) in {match}; expected {exp}: {'OK' if ok else 'MISMATCH'}", flush=True)
print("mismatches:", bad)
