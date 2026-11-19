import sys
sys.path.insert(0, sys.argv[1])
from leandefs import *
base = [coloredJones(2, [(0, True)] * 3, n) for n in range(1, 5)]
for w in ([(0, True)] * 3 + [(1, True)], [(0, True)] * 3 + [(1, False)], [(1, True)] * 3 + [(0, False)]):
    print(w, [coloredJones(3, w, n) == base[n - 1] for n in range(1, 5)])
f8 = [coloredJones(3, [(0, True), (1, False), (0, True), (1, False)], n) for n in range(1, 4)]
w = [(0, True), (1, False), (0, True), (1, False), (2, True)]
print("fig8 stabilised", [coloredJones(4, w, n) == f8[n - 1] for n in range(1, 4)])
