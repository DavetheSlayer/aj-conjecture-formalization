"""Knot Atlas page 3_1 (braid BR(2,{-1,-1,-1}), Jones -q^-4+q^-3+q^-1): coloured Jones J_2, J_3 (unknot = 1)."""
import sys
sys.path.insert(0, sys.argv[1])
from leandefs import *
qn = lambda n: sum((T(2 * (n - 1 - 2 * j)) for j in range(n)), ZERO)
KA = {2: {-1: 1, -3: 1, -4: -1},
      3: {-2: 1, -5: 1, -7: -1, -8: 1, -9: -1, -10: -1, -11: 1},
      4: {-3: 1, -7: 1, -10: -1, -11: 1, -13: -1, -14: -1, -15: 1, -17: -1, -19: 1, -20: 1, -21: -1}}
sub = lambda d, k: LP({k * e: v for e, v in d.items()})
for name, w in [("[(0,False)]^3", [(0, False)] * 3), ("[(0,True)]^3", [(0, True)] * 3)]:
    for n in (2, 3, 4):
        J = coloredJones(2, w, n)
        print(name, "n=%d: J == [n]*KA(q=T^-4): %s ; J == [n]*KA(q=T^4): %s" % (n, J == qn(n) * sub(KA[n], -4), J == qn(n) * sub(KA[n], 4)))
