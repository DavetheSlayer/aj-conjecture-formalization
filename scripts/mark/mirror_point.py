"""The witness point for the mirror factor E': M^2 = 6, L = 1/4.
E'(M, L) = M^4 L^2 - (M^4 - 4 M^2 + 1) L + 1 vanishes there, and B_m is negative for every m >= 1."""
from fractions import Fraction as F
x, L = F(6), F(1, 4)
P = (x - 1) * (1 - L); Q = x + L; k = x * Q**2
tau = x**2*P*Q + x*P**2 - 2*x*P*Q + 2*x*Q**2 + P*Q
A = x**2*P*Q - x**2*Q**2 + x*P**2 - 3*x*P*Q + 3*x*Q**2 + P*Q - Q**2
print("E' =", x**2*L**2 - (x**2 - 4*x + 1)*L + 1, " P,Q,k,tau,A =", P, Q, k, tau, A, " tau - 2k =", tau - 2*k)
s0, s1 = F(0), F(1)
ok = True
for m in range(1, 61):
    B = A*s1 - k**2*s0
    ok &= (B < 0) and (s1 > 0) and (s1 >= (tau/2)*s0)
    s0, s1 = s1, tau*s1 - k**2*s0
print("B_m < 0, S_m > 0 and S_m >= (tau/2) S_{m-1} for m = 1..60:", ok)
