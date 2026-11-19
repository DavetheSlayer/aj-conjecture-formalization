import os, sys, random, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from tw_audit_lib import *
W, I, T, Pw = load(os.path.join(HERE, 'lean_words.txt'))
random.seed(20261119)
pts = [random.randrange(2, P-1) for _ in range(2)]
print("points", pts)
# 0. sanity of my bracket: weight symmetry, trefoil and figure-eight Jones polynomials
for t in pts:
    ti = inv(t)
    # closure of sigma_0^3: Lean-normalised J(2)/[2] expected t^-4+t^-12-t^-16 or its mirror
    for name, m, w in [("s0^3", 2, [(0,1)]*3), ("fig8", 3, [(0,1),(1,-1),(0,1),(1,-1)])]:
        b = bracket_mod(m, w, t, check_sym=True)
        j2 = lean_colored_jones(m, w, 2, t)
        red = j2 * inv(qint_t(t, 2)) % P
        q = pow(t, 4, P)
        cand = {"q+q^3-q^4": (q + q**3 - q**4) % P, "q^-1+q^-3-q^-4": (qpow(q,-1)+qpow(q,-3)-qpow(q,-4)) % P,
                "fig8 q^2-q+1-q^-1+q^-2": (q*q - q + 1 - qpow(q,-1) + qpow(q,-2)) % P}
        print(name, "J(2)/[2] matches:", [k for k, v in cand.items() if v == red])
# 1. calibration of the companion: Lean coloredJones(torusPairKnot r s) 3 against the paper's
#    Phi_{T_+}(3;t) = q^{-m*2} V_1(q), and against the mirror formula
for (r, s), (m, w) in sorted(T.items()):
    for t in pts:
        q = pow(t, 4, P)
        j3 = lean_colored_jones(m, w, 3, t)
        print("torus", r, s, "comp", components(m, w), "J_Lean(3)==Phi_{T+}(3):", j3 == torus_odd(q, r, s, +1, 1),
              " ==Phi_{T-}(3):", j3 == torus_odd(q, r, s, -1, 1))
# 2. twFamilyKnot words: P word = W(l=0, sigma=true); I = invWord(W)
for key, (m, w) in sorted(W.items()):
    assert I[key] == (m, inv_word(w)), key
    assert all(0 <= i and i + 1 < m for i, _ in w)
for (r, s), (m, w) in Pw.items():
    assert W[(r, s, 0, True)] == (m, w)
print("invWord dump == my inverse; pair word == tw word at l=0, sigma=true; all letters on strands")
