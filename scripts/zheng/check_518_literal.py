"""Zheng's (5.18) as printed: b = O(N^2) on 0 < n, i, n+i < alpha N.  Test i = 1, n = N/2."""
import numpy as np
pi = np.pi
def b_closed(N, n, i, corrected=True):
    j = np.arange(1, n + 1); m = i + j
    im = 0.5 * np.sum((N - 2 * m) / np.tan(pi * m / N) + j / np.tan(pi * j / N))
    re = (-N * i - n * N / 2 - n * (n + 1) / 4) if corrected else (-N * i - 3 * n * N / 2 + n * (n + 1) / 4)
    return re + 1j * (im if corrected else -im)
for N in [10**2, 10**3, 10**4, 10**5, 10**6]:
    n = N // 2
    bc, bp = b_closed(N, n, 1), b_closed(N, n, 1, False)
    print(N, "i=1,n=N/2: |b_corr|/N^2 =", round(abs(bc) / N**2, 3), " |b_printed|/N^2 =",
          round(abs(bp) / N**2, 3), " log(N)/(2pi) =", round(np.log(N) / (2 * pi), 3))
