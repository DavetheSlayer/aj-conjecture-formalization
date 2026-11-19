"""Numerical checks for the corrected (5.16), (5.18), (5.19) and the window-enlargement step.

b_{n,i} (corrected sign) = -N(i+n) + sum_{j=1}^n [ (N-i-j)/(1-q^{-N+i+j}) + (i+j)/(1-q^{-i-j}) - j/(1-q^{-j}) ],
q = e^{2 pi i/N};  H_n(s) = s^{-4an(n+1)} sum_{k=-n}^n s^{2ak(2k+1)} (s^{4k+1} - s^{-4k-1}),  s = e^{pi i/N};
D_n = (s/2) H_n'(s).
"""
import numpy as np, sys
pi = np.pi

def spow(m, N):
    return np.exp(1j * pi * np.mod(m, 2 * N) / N)

def H_D(a, n, N):
    k = np.arange(-n, n + 1)
    E = -4 * a * n * (n + 1) + 2 * a * k * (2 * k + 1)
    f = 4 * k + 1
    H = np.sum(spow(E + f, N) - spow(E - f, N))
    D = 0.5 * np.sum((E + f) * spow(E + f, N) - (E - f) * spow(E - f, N))
    return H, D

def b_direct(N, n, i):
    q = np.exp(2j * pi / N)
    j = np.arange(1, n + 1)
    t = (N - i - j) / (1 - q ** (-N + i + j)) + (i + j) / (1 - q ** (-(i + j))) - j / (1 - q ** (-j))
    return -N * (i + n) + np.sum(t)

def b_closed(N, n, i):
    j = np.arange(1, n + 1)
    m = i + j
    re = -N * i - n * N / 2 - n * (n + 1) / 4
    im = 0.5 * np.sum((N - 2 * m) / np.tan(pi * m / N) + j / np.tan(pi * j / N))
    return re + 1j * im

def b_all(N):
    """b[n,i] for all n+i<N via cumulative sums (corrected sign)."""
    q = lambda m: np.exp(2j * pi * m / N)
    m = np.arange(N)
    g = np.zeros(N, complex)
    g[1:] = (N - m[1:]) / (1 - q(m[1:])) + m[1:] / (1 - q(-m[1:]))
    G = np.concatenate([[0], np.cumsum(g[1:])])
    h = np.zeros(N, complex)
    h[1:] = m[1:] / (1 - q(-m[1:]))
    Hc = np.concatenate([[0], np.cumsum(h[1:])])
    return G, Hc

def main():
    rng = np.random.default_rng(1)
    # 1. closed form of b
    err = 0
    for _ in range(400):
        N = int(rng.integers(2, 400)); n = int(rng.integers(0, N)); i = int(rng.integers(0, N - n))
        bd, bc = b_direct(N, n, i), b_closed(N, n, i)
        err = max(err, abs(bd - bc) / max(1, abs(bd)))
    print("1. closed form of corrected b: max relative error", err)

    # 2./3. bounds
    for a in [1, 3, 5, 7, 11, 21]:
        worst_win_b = 0; worst516 = 0; worst_b3 = 0; worst_H = 0; worst_D = 0
        worst_win_bH = 0; worst_win_H = 0
        Ns = list(range(1, 120)) + [200, 301, 500, 801, 1000, 1500]
        for N in Ns:
            G, Hc = b_all(N)
            for n in range(N):
                H, D = H_D(a, n, N)
                worst_H = max(worst_H, abs(H) / N); worst_D = max(worst_D, abs(D) / (a * N ** 3))
                i = np.arange(0, N - n)
                b = -N * (i + n) + (G[i + n] - G[i]) - Hc[n]
                worst_b3 = max(worst_b3, np.max(np.abs(b)) / N ** 3)
                worst516 = max(worst516, np.max(np.abs(b * H + D)) / N ** 4)
                win = np.abs(n - N / 2) + np.abs(i - N / 4) < N / (8 * a)
                if win.any():
                    worst_win_b = max(worst_win_b, np.max(np.abs(b[win])) / N ** 2)
                    worst_win_bH = max(worst_win_bH, np.max(np.abs(b[win] * H)) / N ** 2)
                    worst_win_H = max(worst_win_H, abs(H))
        print(f"a={a}: (5.16) max|bH+D|/N^4={worst516:.3f} (claimed <= {7+24*a}); "
              f"max|b|/N^3={worst_b3:.3f} (<=7/4); max|H|/N={worst_H:.3f} (<=4); "
              f"max|D|/(aN^3)={worst_D:.3f} (<=24)")
        print(f"      window: max|b|/N^2={worst_win_b:.3f} (claimed <= 2); max|H|={worst_win_H:.3f}; "
              f"max|bH|/N^2={worst_win_bH:.3f}")

    # 4. one-step recursion H_{n+1} = s^{-8a(n+1)} H_n + E_n, |E_n| <= 4, and
    #    D_{n+1} = s^{-8a(n+1)} (D_n - 4a(n+1) H_n) + (s/2)E_n', |(s/2)E_n'| <= 40 a N^2
    worstE = 0; worstR = 0; worstEd = 0
    for a in [3, 5, 9]:
        for N in [17, 64, 101, 333]:
            for n in range(N - 1):
                H0, D0 = H_D(a, n, N); H1, D1 = H_D(a, n + 1, N)
                ph = spow(-8 * a * (n + 1), N)
                E = H1 - ph * H0
                worstE = max(worstE, abs(E))
                k = np.array([n + 1, -(n + 1)])
                Ek = -4 * a * (n + 1) * (n + 2) + 2 * a * k * (2 * k + 1)
                f = 4 * k + 1
                Edir = np.sum(spow(Ek + f, N) - spow(Ek - f, N))
                Ed = 0.5 * np.sum((Ek + f) * spow(Ek + f, N) - (Ek - f) * spow(Ek - f, N))
                worstR = max(worstR, abs(E - Edir), abs(D1 - ph * (D0 - 4 * a * (n + 1) * H0) - Ed))
                worstEd = max(worstEd, abs(Ed) / (a * N ** 2))
    print("4. one-step recursion: max|E_n| =", round(worstE, 4), "(<=4); identity residual",
          worstR, "; max|(s/2)E_n'|/(aN^2) =", round(worstEd, 3), "(<=40)")

    # 5. H_n on Zheng's colour window |2n+1-N| < N/(4a) versus our enlarged window
    for a in [3, 5, 7]:
        mz = 0; me = 0
        for N in range(8 * a, 1500, 7):
            for n in range(N):
                c = abs(2 * n + 1 - N)
                if c < N / (4 * a):
                    mz = max(mz, abs(H_D(a, n, N)[0]))
                elif c < N / (4 * a) + 1:
                    me = max(me, abs(H_D(a, n, N)[0]))
        print(f"5. a={a}: sup|H_n| on Zheng window {mz:.3f}; on the extra boundary layer {me:.3f}")

main()
