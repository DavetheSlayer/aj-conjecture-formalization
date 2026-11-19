"""min over N mod 8a of |A^+_{a,2}(N,1)| for odd a (Zheng Prop 4.1); A is 8a-periodic in N."""
import numpy as np
pi = np.pi
worst = (1e9, None)
rows = []
for a in range(3, 402, 2):
    j = np.arange(1, 2 * a, dtype=np.float64)
    w = j ** 2 * np.sin(j * pi / a) * np.sin(j * pi / 2)
    N = np.arange(0, 8 * a)[:, None]
    ph = np.exp(-1j * pi * np.mod(N * (j[None, :] ** 2), 8 * a) / (4 * a))
    A = ph @ w
    m = np.min(np.abs(A)); arg = int(np.argmin(np.abs(A)))
    rows.append((a, m, arg))
    if m < worst[0]:
        worst = (m, (a, arg))
print("odd a in [3,401]: global min |A| =", worst)
print("smallest ten:", sorted(rows, key=lambda r: r[1])[:10])
