import sys
sys.path.insert(0, '.')
from whd_check import *

def band_word(i, j, b):
    return ([(j - 1 - t, True) for t in range(j - 1 - i)] + [(i, b)]
            + [(i + 1 + t, False) for t in range(j - 1 - i)])

def pair_blocks(r, s):
    c = (r - 1) * s; T = 2 * c - 1; E = (r - 2) * (s - 1) + 1; z = c - r - 1
    bl = [('band', i, T - 1 - i) for i in range(r - 2)]
    bl += [('band', r + E - 3 - j, r + E - 2 - j) for j in range(E)]
    bl += [('band', r - 2 + E + j, r - 1 + E + j) for j in range(z)]
    bl += [('band', r - 2 + E + z, T + 1 - r), ('band', T - r, T), ('neg', T)]
    bl += [('band', T - r - 1 - j, T - 1 - j) for j in range(s - 2)]
    bl += [('band', r - 2, T + 1 - s), ('band', T - s, T)]
    bl += [('band', r - 3 - j, T + 2 - s - r + j) for j in range(r - 2)]
    bl += [('neg', T)]
    return bl

def pair_word(r, s):
    out = []
    for b in pair_blocks(r, s):
        out += band_word(b[1], b[2], True) if b[0] == 'band' else [(b[1], False)]
    return out

for (r, s) in [(2, 3), (2, 5)]:
    m = 2 * (r - 1) * s + 1
    B = long_closure(m, pair_word(r, s))
    ws = orient_writhes(B)
    V = to_t(jones_long(B, ws[0]))
    L = long_closure(r, torus_word(r, s))
    W = wh_double(L)
    V2 = to_t(jones_long(W, orient_writhes(W)[0]))
    print((r, s), 'braid writhe', braid_writhe(pair_word(r, s)), 'orient', ws, 'match whD', V == V2)
