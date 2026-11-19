import sys
sys.path.insert(0, '.')
from whd_check import *
tests = {'fig8': (3, [(0, True), (1, False), (0, True), (1, False)]),
         'T23neg': (2, [(0, False)] * 3),
         'b4': (4, [(0, True), (1, False), (2, True), (1, True), (0, False), (2, True)])}
for name, (m, w) in tests.items():
    L = long_closure(m, w)
    print(name, 'orient writhes', orient_writhes(L), 'braid writhe', braid_writhe(w),
          'band lk', band_linkings(morse_double(L) + band_untwist(morse_writhe(L))),
          'whD writhes', orient_writhes(wh_double(L)))
