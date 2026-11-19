"""Validation of the whDouble design: orientation semantics, writhe, bracket, Jones.

Laurent polynomials in A are dicts {exponent: int}.  Conventions follow the library:
(cross True, i) = A*id + A^-1*e_i, (cross False, i) = A^-1*id + A*e_i, delta = -A^2 - A^-2,
Jones V = (-A^3)^(-writhe) <D>_long with t = A^-4.
"""
from collections import defaultdict
from math import gcd


def padd(p, q, c=1):
    r = defaultdict(int, p)
    for e, v in q.items():
        r[e] += c * v
    return {e: v for e, v in r.items() if v}


def pmul(p, q):
    r = defaultdict(int)
    for a, x in p.items():
        for b, y in q.items():
            r[a + b] += x * y
    return {e: v for e, v in r.items() if v}


def mono(e, c=1):
    return {e: c}


DELTA = {2: -1, -2: -1}

# ---------------------------------------------------------------- words
def cable2_gen(i, s):
    # library cableGen 2 (i, s)
    if s:
        return [(2 * i + a + b, True) for a in reversed(range(2)) for b in range(2)]
    return [(2 * i + a + b, False) for a in range(2) for b in reversed(range(2))]


def morse_of_braid(w):
    return [(('cross', s), i) for (i, s) in w]


def long_closure(m, w):
    return ([('cup', j + 1) for j in range(m - 1)] + morse_of_braid(w)
            + [('cap', j + 1) for j in reversed(range(m - 1))])


def morse_double_letter(l):
    k, i = l
    if k == 'cup':
        return [('cup', 2 * i), ('cup', 2 * i + 1)]
    if k == 'cap':
        return [('cap', 2 * i + 1), ('cap', 2 * i)]
    return morse_of_braid(cable2_gen(i, k[1]))


def morse_double(w):
    return [x for l in w for x in morse_double_letter(l)]


CLASP = [('cup', 2), (('cross', True), 1), (('cross', True), 1), ('cap', 0)]


def band_untwist(wr):
    if wr >= 0:
        return [(('cross', False), 0)] * (2 * wr)
    return [(('cross', True), 0)] * (2 * (-wr))


# ---------------------------------------------------------------- orientation semantics
def orient_sign(s, a, b):
    return (1 if s else -1) * (1 if a == b else -1)


def orient_letter(l, st):
    k, i = l
    a, x = st
    if k == 'cup':
        if i <= len(a):
            return [(a[:i] + (True, False) + a[i:], x), (a[:i] + (False, True) + a[i:], x)]
        return []
    if len(a) < i + 2:
        return []
    p, q = a[i], a[i + 1]
    if k == 'cap':
        return [(a[:i] + a[i + 2:], x)] if p != q else []
    return [(a[:i] + (q, p) + a[i + 2:], x + orient_sign(k[1], p, q))]


def orient_states(w, S):
    for l in w:
        S = [t for st in S for t in orient_letter(l, st)]
    return S


def orient_writhes(D):
    return [x for (a, x) in orient_states(D, [((True,), 0)]) if a == (True,)]


def morse_writhe(D):
    return sum(orient_writhes(D))


def wh_double(D):
    return [('cup', 1)] + morse_double(D) + band_untwist(morse_writhe(D)) + CLASP + [('cap', 1)]


# linking semantics: labels (dir, comp)
def lk_letter(l, st):
    k, i = l
    a, x = st
    if k == 'cup':
        if i > len(a):
            return []
        return [(a[:i] + ((d, c), (not d, c)) + a[i:], x)
                for d in (True, False) for c in (False, True)]
    if len(a) < i + 2:
        return []
    p, q = a[i], a[i + 1]
    if k == 'cap':
        return [(a[:i] + a[i + 2:], x)] if (p[0] != q[0] and p[1] == q[1]) else []
    wgt = orient_sign(k[1], p[0], q[0]) if p[1] != q[1] else 0
    return [(a[:i] + (q, p) + a[i + 2:], x + wgt)]


def lk_states(w, S):
    for l in w:
        S = [t for st in S for t in lk_letter(l, st)]
    return S


BAND_END = ((True, False), (True, True))


def band_linkings(T):
    return [x for (a, x) in lk_states(T, [(BAND_END, 0)]) if a == BAND_END]


# ---------------------------------------------------------------- bracket transfer matrix
def bracket_long(w):
    """Kauffman bracket of a 1 -> 1 Morse word (closed loops weighted by delta)."""
    # state: tuple conn, conn[p] = partner index or -1 (connected to the input end)
    states = {(-1,): {0: 1}}

    def ins_cup(conn, i):
        new = []
        for c in conn:
            new.append(c if c < i or c == -1 else c + 2)
        new = new[:i] + [i + 1, i] + new[i:]
        return tuple(new)

    def do_cap(conn, i):
        conn = list(conn)
        a, b = conn[i], conn[i + 1]
        if a == i + 1:  # closed loop
            loop = True
            rest = conn[:i] + conn[i + 2:]
        else:
            loop = False
            if a != -1:
                conn[a] = b
            if b != -1:
                conn[b] = a
            rest = conn[:i] + conn[i + 2:]
        rest = [c if c < i or c == -1 else c - 2 for c in rest]
        return tuple(rest), loop

    for (k, i) in w:
        new = defaultdict(dict)
        for conn, poly in states.items():
            outs = []
            if k == 'cup':
                outs.append((ins_cup(conn, i), poly))
            elif k == 'cap':
                c2, loop = do_cap(conn, i)
                outs.append((c2, pmul(poly, DELTA) if loop else poly))
            else:
                s = k[1]
                aid, ae = (1, -1) if s else (-1, 1)
                outs.append((conn, pmul(poly, mono(aid))))
                c2, loop = do_cap(conn, i)
                p2 = pmul(poly, mono(ae))
                if loop:
                    p2 = pmul(p2, DELTA)
                outs.append((ins_cup(c2, i), p2))
            for c, p in outs:
                new[c] = padd(new[c], p)
        states = {c: p for c, p in new.items() if p}
    assert set(states) <= {(-1,)}, states.keys()
    return states.get((-1,), {})


def jones_long(w, wr):
    f = pmul(mono(3 * -wr, (-1) ** (abs(wr) % 2)), bracket_long(w))
    return f  # polynomial in A; t = A^-4


def to_t(p):
    out = {}
    for e, v in p.items():
        assert e % 4 == 0, p
        out[-e // 4] = v
    return dict(sorted(out.items()))


# ---------------------------------------------------------------- tests
def torus_word(r, s):
    return [(i, True) for _ in range(s) for i in range(r - 1)]


def braid_writhe(w):
    return sum(1 if s else -1 for _, s in w)


def cable2(w):
    return [g for x in w for g in cable2_gen(*x)]


def J3(r, s):
    w = torus_word(r, s)
    cl = long_closure(2 * r, cable2(w))
    # bracket of the closed 2-cable: closing the long 2r-strand closure ... use long closure on 2r
    # strands: closed bracket = delta * long bracket
    bb = pmul(DELTA, bracket_long(cl))
    return pmul(mono(-8 * braid_writhe(w)), padd(bb, {0: -1}))


def predicted_jones_wh_minus(r, s):
    # V(Wh^-_0 K) = t^-2 + (t^-3/2 - t^-1/2) V(C_0),  V(C_0) = (J3 + 1)/delta, t^(1/2) = A^-2
    j = padd(J3(r, s), {0: 1})
    # divide by delta: (J3+1) / (-(A^2 + A^-2)); do polynomial division
    num = dict(j)
    q = {}
    while num:
        e = max(num)
        c = num[e]
        # leading of delta is -A^2
        q[e - 2] = -c
        num = padd(num, pmul({e - 2: -c}, DELTA), -1)
        if num and min(num) < min(j) - 10:
            raise ValueError("not divisible")
    vc0 = q
    return padd({8: 1}, pmul({6: 1, 2: -1}, vc0))


PAIR_LIB = None


if __name__ == '__main__':
    import json
    res = {}
    # sanity: right-handed trefoil
    tre = long_closure(2, torus_word(2, 3))
    print('trefoil writhes', orient_writhes(tre))
    print('trefoil V(t)', to_t(jones_long(tre, morse_writhe(tre))))
    # unknot tests of whDouble
    for D in ([], [('cup', 1), (('cross', True), 0), ('cap', 1)],
              [('cup', 1), (('cross', False), 0), ('cap', 1)]):
        W = wh_double(D)
        print('D =', D, 'wr', orient_writhes(D), 'whD writhes', orient_writhes(W),
              'V', to_t(jones_long(W, morse_writhe(W))), 'band lk', band_linkings(
                  morse_double(D) + band_untwist(morse_writhe(D))))
    for (r, s) in [(2, 3), (2, 5), (3, 4), (3, 5), (2, 7)]:
        L = long_closure(r, torus_word(r, s))
        W = wh_double(L)
        ws = orient_writhes(W)
        V = to_t(jones_long(W, ws[0]))
        P = to_t(predicted_jones_wh_minus(r, s))
        band = morse_double(L) + band_untwist(morse_writhe(L))
        clasp_check = orient_states(CLASP + [('cap', 1)], [((True, False, True), 0)])
        print((r, s), 'wr(L)', orient_writhes(L), 'writhes(whD)', ws,
              'band lk', band_linkings(band), 'clasp', clasp_check)
        print('   V(whD)      ', V)
        print('   skein/J3    ', P, 'MATCH' if V == P else 'MISMATCH')
        res[f'{r},{s}'] = {'writhe_L': orient_writhes(L), 'writhes_whD': ws,
                           'band_linkings': band_linkings(band), 'jones_whD': V,
                           'jones_skein_J3': P, 'match': V == P}
    json.dump(res, open(__file__.replace('whd_check.py', 'whd_check.json'), 'w'), indent=1,
              default=str)
