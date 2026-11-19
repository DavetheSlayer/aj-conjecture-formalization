"""1. bracket_literal == bracket_fast == independent Kauffman state sum (loop counting).
2. Algebraic check of the Jones skein relation satisfied by the Lean crossing matrices."""
import sys, time, itertools, random
sys.path.insert(0, sys.argv[1])
from leandefs import *

def state_sum(m, w):
    """Independent path: sum over smoothings, delta^(number of loops); <empty>=1.
    letter (i,True): coefficient T for the vertical (braid-like) smoothing, T^-1 for cup-cap."""
    n = len(w); delta = -T(2) - T(-2); tot = ZERO
    if n == 0:
        r = ONE
        for _ in range(m): r = r * delta
        return r
    for choice in itertools.product([0, 1], repeat=n):
        parent = list(range(n * m))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]; x = parent[x]
            return x
        def union(a, b):
            a, b = find(a), find(b)
            if a != b: parent[a] = b
        e = 0
        for l, ((i, b), ch) in enumerate(zip(w, choice)):
            top = lambda j: l * m + j
            bot = lambda j: ((l + 1) % n) * m + j
            for j in range(m):
                if ch == 1 and j in (i, i + 1): continue
                union(top(j), bot(j))
            if ch == 1:
                union(top(i), top(i + 1)); union(bot(i), bot(i + 1))
            # exponent: vertical smoothing gets T^(+1) for True, T^(-1) for False
            if ch == 0: e += 1 if b else -1
            else: e += -1 if b else 1
        loops = len({find(x) for x in range(n * m)})
        term = T(e)
        for _ in range(loops): term = term * delta
        tot = tot + term
    return tot

tests = [
    (1, []), (2, []), (2, [(0, True)]), (2, [(0, False)]), (2, [(0, True)] * 3), (2, [(0, False)] * 3),
    (3, [(0, True), (1, False), (0, True), (1, False)]),
    (3, [(0, True)] * 3 + [(1, True), (0, False), (1, True)]),
    (4, cable(2, [(0, True)] * 3)),
    (4, cable(2, [(0, False)] * 2)),
]
random.seed(1)
for _ in range(6):
    m = random.randint(2, 4)
    tests.append((m, [(random.randrange(m - 1), random.random() < .5) for _ in range(random.randint(1, 7))]))
ok = True
for m, w in tests:
    a = bracket_literal(m, w); b = bracket_fast(m, w); c = state_sum(m, w)
    good = (a == b == c); ok &= good
    print(m, len(w), "literal==fast==statesum:", good)
print("ALL AGREE:", ok)
print("kink values: <closure of [(0,True)] on 2 strands> =", bracket_literal(2, [(0, True)]), " ; delta =", bracket_literal(1, []))
print("             <closure of [(0,False)]> =", bracket_literal(2, [(0, False)]))
# skein relation of the crossing matrices:  T*X_true - T^-1*X_false = (T^2 - T^-2) * 1
for m in (2, 3):
    for i in range(m - 1):
        lhs = mat_add(mat_smul(T(1), crossingMatrix(m, (i, True))), mat_smul(-T(-1), crossingMatrix(m, (i, False))))
        rhs = mat_smul(T(2) - T(-2), mat_one(m))
        print("m=%d i=%d  T*X(true) - T^-1*X(false) == (T^2-T^-2)*1 :" % (m, i), lhs == rhs,
              "; X(true)*X(false)==1:", mat_mul(crossingMatrix(m, (i, True)), crossingMatrix(m, (i, False))) == mat_one(m))
