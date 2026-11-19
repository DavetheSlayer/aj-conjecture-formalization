# Zheng's analytic estimates after the sign correction of $b_{n,i}$

Source: H. Zheng, *Proof of the volume conjecture for Whitehead doubles of a family of torus
knots*, arXiv math/0508138v4 (4 Mar 2006). Page numbers are those of the arXiv v4 PDF.
Throughout, $a=2k+1\ge 3$ is odd, $(p,q)=(a,2)$, $pq=2a$, the twist is $r=0$, and the colour of
the companion is $2n+1$.

## 0. Verdict

* **None of the six estimates is false, and no statement has to be changed.**
* Only (5.16) and (5.19) contain $b_{n,i}$, so only they are affected by the sign correction.
  Zheng's arguments for them bound every summand of $b_{n,i}$ *in absolute value*; the sign of
  the three summed terms therefore plays no role, and the arguments go through for the corrected
  $b$. Complete proofs with explicit constants are given below (Sections 4–8):
  * (5.16) for the corrected $b$: **proved**, elementary, $K=7+24a$.
  * (5.19) for the corrected $b$: **proved from** Zheng's Lemma 5.2 bound
    $\hat J_{T(a,2),2n+1}(e^{2\pi i/N})=O(1)$ ((5.12), p. 16), which does not involve $b$ and is
    cited verbatim. The new ingredient is the bound $|b_{n,i}|\le 2N^2$ on the window, proved here.
* Two small inaccuracies in Zheng's text were found; neither affects the estimates as used.
  1. (5.18) as printed ("$b_{n,i}=O(N^2)$ uniformly on $0<n,i,n+i<\alpha N$", p. 16) is false
     near $i=0$: for $i=1$, $n=N/2$ one has $|b_{n,i}|/N^2\approx(\log N)/(2\pi)$, for either
     sign (numbers in Section 9). It is true on the window
     $|n-\tfrac N2|+|i-\tfrac N4|<\tfrac N{8a}$, which is all that is used (Section 6).
  2. Lemma 5.2 is stated for colours $c$ with $|c-N|<N/(2pq)=N/(4a)$, but (5.19), (5.20) are
     asserted on $|n-\tfrac N2|+|i-\tfrac N4|<\tfrac N{8a}$, where the colour $c=2n+1$ only
     satisfies $|c-N|<N/(4a)+1$. The extra boundary layer is covered by an exact one-step
     recursion in $n$ (Lemma W, Section 7), so (5.19) and (5.20) hold on the stated window.

## 1. Notation

$N\ge 1$, $q=e^{2\pi i/N}$, $s=q^{1/2}=e^{\pi i/N}$. For $n+i<N$ the corrected logarithmic
derivative is
$$
b_{n,i}=-N(i+n)+\sum_{j=1}^{n}\Big(\frac{N-i-j}{1-q^{-N+i+j}}+\frac{i+j}{1-q^{-i-j}}
-\frac{j}{1-q^{-j}}\Big),
$$
(Zheng's printed (5.4), p. 14, has the opposite sign on the three summed terms). The companion
input and its $q$-derivative are, as Laurent polynomials in $z$ evaluated at $z=s$,
$$
\hat H_n(z)=z^{-4an(n+1)}\sum_{k=-n}^{n}z^{2ak(2k+1)}\big(z^{4k+1}-z^{-4k-1}\big)
=\sum_{k=-n}^{n}\big(z^{u_k^+}-z^{u_k^-}\big),\qquad
u_k^{\pm}=-4an(n+1)+2ak(2k+1)\pm(4k+1),
$$
$$
D_n:=q\partial_q\hat H_n\big|_{q=e^{2\pi i/N}}=\tfrac s2\,\hat H_n'(s)
=\tfrac12\sum_{k=-n}^{n}\big(u_k^+s^{u_k^+}-u_k^-s^{u_k^-}\big).
$$
$\hat H_n(s)=\hat J_{T(a,2),2n+1}(e^{2\pi i/N})$ in Zheng's notation ((4.1), (5.2)). The window is
$W_N=\{(n,i):n+i<N,\ |n-\tfrac N2|+|i-\tfrac N4|<\tfrac N{8a}\}$, and the leading term of (5.20) is
$M_n=C_{a,N}\,s^{-4an(n+1)}=C_{a,N}\,a_n^{-8a}$ with
$C_{a,N}=-2\,\frac{N^{5/2}}{(4a)^{3/2}}e^{-(\frac a2+\frac2a)\frac{\pi i}{2N}+\frac{\pi i}4}A^+_{a,2}(N,1)$.

## 2. Classification

| Estimate | Kind | Where in Zheng (v4) | Status |
|---|---|---|---|
| Lemma 3.2 (localization of $S_{n,i}$, all $\tfrac12<\delta<1$) | (a) verbatim | Lemma 3.2, (3.25), p. 9 (uses (3.21), p. 8) | external |
| Lemma 3.3, $\alpha=0$, $\beta\in\{-(8a+1),0\}$, $\tfrac12<\delta<\tfrac23$, constant (3.34) | (a) verbatim | Lemma 3.3, (3.29), p. 9; (3.34), p. 10 | external |
| (5.16) bracket $=O(N^4)$ on $0\le n,i,\ n+i<N$ | (b) involves $b$ | (5.16), p. 16 | **proved here** (Sec. 5) |
| (5.19) $b_{n,i}\hat H_n=O(N^2)$ on $W_N$ | (b) involves $b$ | (5.18)–(5.19), p. 16 | **proved here from (5.12)** (Sec. 6–8) |
| (5.20) $D_n=M_n+O(N^2)$ on $W_N$ | (a) verbatim ($b$-free) | (5.20), p. 16, from Lemma 5.2 (5.13), p. 16, and Lemma 5.1, p. 15 | external; window gap closed by Lemma W |
| Prop. 4.1, $A^+_{a,2}(N,1)\ne0$ for all $N\in\mathbb Z$ | (a) verbatim | Prop. 4.1, (4.6), p. 11; Lemmas 4.2–4.4, pp. 11–12; proof pp. 13–14 | external |

Kind (a) means: the statement is Zheng's, word for word in our specialization $(p,q)=(a,2)$,
$r=0$, $\alpha=0$, and his proof does not involve $b$. The O-constants are uniform in $N\ge1$
because only finitely many $N$ lie below any threshold and every quantity is finite.

## 3. Elementary facts

**(F1)** For $m\in\mathbb Z$, $|1-q^{m}|=2|\sin(\pi m/N)|$. If $1\le m\le N-1$, then
$2\sin(\pi m/N)\ge 4\min(m,N-m)/N\ge 4/N$ (Jordan: $\sin\pi x\ge 2x$ on $[0,\tfrac12]$, by
concavity, and $\sin(\pi m/N)=\sin(\pi(N-m)/N)$).

**(F2)** If $N\nmid m$, then
$\dfrac1{1-q^{m}}=\dfrac12+\dfrac i2\cot\dfrac{\pi m}N$ and
$\dfrac1{1-q^{-m}}=\dfrac12-\dfrac i2\cot\dfrac{\pi m}N$.
Indeed, with $\theta=2\pi m/N$, $1-e^{i\theta}=-2i\sin(\theta/2)\,e^{i\theta/2}$, so
$(1-e^{i\theta})^{-1}=\dfrac{i\,e^{-i\theta/2}}{2\sin(\theta/2)}=\dfrac12+\dfrac i2\cot\dfrac\theta2$;
the second formula is the first for $-m$.

**(F3)** Indices. If $n+i<N$ and $1\le j\le n$, then $1\le j\le N-1$ and
$1\le i+j\le i+n\le N-1$; moreover $q^{-N+i+j}=q^{i+j}$ since $q^N=1$. So no denominator of
$b_{n,i}$ vanishes.

## 4. Closed form of the corrected $b$

**Proposition B.** For $n+i<N$,
$$
b_{n,i}=-Ni-\frac{nN}2-\frac{n(n+1)}4
+\frac i2\sum_{j=1}^{n}\Big[(N-2(i+j))\cot\frac{\pi(i+j)}N+j\cot\frac{\pi j}N\Big].
$$

*Proof.* Put $m=i+j$. By (F2), (F3),
$\frac{N-m}{1-q^{m}}=\frac{N-m}2+\frac i2(N-m)\cot\frac{\pi m}N$,
$\frac{m}{1-q^{-m}}=\frac m2-\frac i2m\cot\frac{\pi m}N$,
$-\frac{j}{1-q^{-j}}=-\frac j2+\frac i2j\cot\frac{\pi j}N$.
The sum is $\frac{N-j}2+\frac i2\big[(N-2m)\cot\frac{\pi m}N+j\cot\frac{\pi j}N\big]$, and
$\sum_{j=1}^n\frac{N-j}2=\frac{nN}2-\frac{n(n+1)}4$. $\square$

With the printed sign one gets instead
$b^{\rm pr}_{n,i}=-Ni-\frac{3nN}2+\frac{n(n+1)}4-\frac i2\sum_j[\cdots]$: the imaginary parts are
negatives of each other and the real parts differ by $nN-\frac{n(n+1)}2$. On the window
$b\approx-\frac9{16}N^2+i\,\mathrm{Im}\,b$ while $b^{\rm pr}\approx-\frac{15}{16}N^2-i\,\mathrm{Im}\,b$; both are
of order $N^2$, which is why the order-of-magnitude statements survive while the exact value of
the diagonal changes.

## 5. (5.16) for the corrected $b$

**Proposition 5.16.** For all $a\ge1$, $N\ge1$ and $n,i\ge0$ with $n+i<N$:
$$
|b_{n,i}\hat H_n(s)+D_n|\le(7+24a)\,N^4 .
$$

*Proof.* (i) *$|b_{n,i}|\le\frac74N^3$.* With $m=i+j\in[1,N-1]$ and $j\in[1,N-1]$ (F3), (F1) gives
$$
\Big|\frac{N-m}{1-q^{m}}\Big|\le\frac{N}{4/N}=\frac{N^2}4,\qquad
\Big|\frac{m}{1-q^{-m}}\Big|\le\frac{N^2}4,\qquad
\Big|\frac{j}{1-q^{-j}}\Big|\le\frac{N^2}4 .
$$
Hence $|b_{n,i}|\le N(i+n)+n\cdot\frac34N^2\le N^2+\frac34N^3\le\frac74N^3$. Only absolute values of
the summands were used, so the same bound holds for the printed $b$.

(ii) *$|\hat H_n(s)|\le4N$.* $|s|=1$, so each of the $2(2n+1)$ monomials has modulus $1$, and
$2(2n+1)\le 4N-2$.

(iii) *$|D_n|\le24aN^3$.* For $|k|\le n\le N-1$,
$|u_k^\pm|\le4an(n+1)+2an(2n+1)+4n+1=a(8n^2+6n)+4n+1\le8aN^2+4N\le12aN^2$
(using $8n^2+6n\le8(N-1)^2+6(N-1)\le8N^2$ and $4n+1\le4N$). Hence
$|D_n|\le\frac12\cdot2(2n+1)\cdot12aN^2\le24aN^3$.

(iv) $|b\hat H_n+D_n|\le\frac74N^3\cdot4N+24aN^3\le(7+24a)N^4$. $\square$

This is exactly Zheng's argument "$O(N^3)O(N)+O(N^3)$" of (5.16), now with constants and for the
corrected $b$.

## 6. The bound $|b_{n,i}|\le 2N^2$ on the window (corrected (5.18))

**Proposition 5.18.** Let $a\ge1$, $N\ge1$, $(n,i)\in W_N$. Then $|b_{n,i}|<\frac{57}{32}N^2<2N^2$.
(For the printed $b$ the same argument gives $|b^{\rm pr}_{n,i}|<\frac94N^2$.)

*Proof.* Since $\frac N{8a}\le\frac N8$: $|n-\frac N2|<\frac N8$ and $|i-\frac N4|<\frac N8$, so
$n<\frac58N$, $\frac N8<i<\frac38N$, and $n+i<\frac34N+\frac N8=\frac78N$.

*Imaginary part.* For $1\le j\le n$ let $m=i+j$, so $\frac N8<m<\frac78N$. Then
$\theta=\pi m/N\in(\frac\pi8,\frac{7\pi}8)$, $\sin\theta>\sin\frac\pi8>\frac38$, so
$|\cot\theta|<\frac83$; also $|N-2m|<\frac34N$. Hence $|(N-2m)\cot\theta|<2N$.
Let $\varphi=\pi j/N\in(0,\frac{5\pi}8)$. If $\varphi\le\frac\pi2$:
$0\le j\cot\varphi=\frac N\pi\,\varphi\cot\varphi\le\frac N\pi$ (as $\tan\varphi\ge\varphi$).
If $\frac\pi2<\varphi<\frac{5\pi}8$: $|\cot\varphi|=\tan(\varphi-\frac\pi2)<\tan\frac\pi8<\frac12$ and
$j<\frac58N$, so $|j\cot\varphi|<N$. By Proposition B,
$|\mathrm{Im}\,b_{n,i}|\le\frac12\,n\,(2N+N)<\frac32\cdot\frac58N^2=\frac{30}{32}N^2$.

*Real part.* $|\mathrm{Re}\,b_{n,i}|=Ni+\frac{nN}2+\frac{n(n+1)}4<\frac38N^2+\frac5{16}N^2+\frac{\frac58N\cdot N}4
=\frac{27}{32}N^2$ (using $n+1\le N$).

So $|b_{n,i}|\le|\mathrm{Re}\,b|+|\mathrm{Im}\,b|<\frac{57}{32}N^2$. For the printed $b$ the imaginary part is
the same up to sign and $|\mathrm{Re}\,b^{\rm pr}|=Ni+\frac{3nN}2-\frac{n(n+1)}4<\frac38N^2+\frac{15}{16}N^2$,
which gives $|b^{\rm pr}|<\frac{72}{32}N^2=\frac94N^2$. $\square$

*Termwise variant (no closed form, constant 4).* With the same window facts, for $1\le j\le n$
the argument $m=i+j\in(\frac N8,\frac78N)$ has $\min(m,N-m)>\frac N8$, so by (F1)
$|1-q^{\pm m}|=2\sin(\pi m/N)\ge4\min(m,N-m)/N>\frac12$, whence
$|\frac{N-m}{1-q^{m}}|<2N$ and $|\frac{m}{1-q^{-m}}|<2N$. For the third summand: if
$j\le\frac N2$, then $|1-q^{-j}|\ge4j/N$ and $|\frac j{1-q^{-j}}|\le\frac N4$; if
$\frac N2<j<\frac58N$, then $N-j>\frac38N$, $|1-q^{-j}|>\frac32$ and
$|\frac j{1-q^{-j}}|<\frac23\cdot\frac58N<\frac N2$. Therefore
$|b_{n,i}|\le N(i+n)+n\,(2N+2N+\tfrac N2)<\tfrac78N^2+\tfrac58\cdot\tfrac92N^2=\tfrac{59}{16}N^2<4N^2$,
for either sign of the summed terms. (Any constant suffices for (5.19).)

(The hypothesis $i>\frac N8$ is essential: for $i=1$ the sum $\sum_j(N-2m)\cot(\pi m/N)$ behaves
like $\frac{N^2}\pi\log n$; this is why (5.18) as printed is too strong. The window keeps
$i+j$ away from $0$ and $N$.)

## 7. Window bookkeeping: Lemma W

Zheng's Lemma 5.2 ((5.12), (5.13), p. 16) for odd colour $c=2n+1$ reads, in our notation
(for odd $c$, $A^{(-1)^{c-1}}=A^+$ and $e^{-pq\frac{c^2-1}{2N}\pi i}=s^{-4an(n+1)}=a_n^{-8a}$):

> **(Z)** There are $K_0,N_0$ such that for all $N\ge N_0$ and all $0\le n\le N-1$ with
> $|2n+1-N|<\frac N{4a}$: $\ |\hat H_n(s)|\le K_0$ and $|D_n-M_n|\le K_0N^2$.

**Lemma W.** Assume (Z). Then there is $K_1$ such that for all $N\ge1$ and all
$0\le n\le N-1$ with $|n-\frac N2|<\frac N{8a}$ (in particular for all $(n,i)\in W_N$):
$|\hat H_n(s)|\le K_1$ and $|D_n-M_n|\le K_1N^2$.

*Proof.* **One-step identities.** Let $g_k(z)=z^{2ak(2k+1)}(z^{4k+1}-z^{-4k-1})$. Since
$-4a(n+1)(n+2)=-4an(n+1)-8a(n+1)$,
$$
\hat H_{n+1}(z)=z^{-8a(n+1)}\hat H_n(z)+E_n(z),\qquad
E_n(z)=z^{-4a(n+1)(n+2)}\big(g_{n+1}(z)+g_{-n-1}(z)\big). \tag{R1}
$$
Applying $\frac z2\frac d{dz}$ and evaluating at $z=s$:
$$
D_{n+1}=s^{-8a(n+1)}\big(D_n-4a(n+1)\hat H_n(s)\big)+F_n,\qquad F_n=\tfrac s2E_n'(s). \tag{R2}
$$
Also $M_{n+1}=s^{-8a(n+1)}M_n$. $E_n$ consists of four monomials $\pm z^{u}$ with
$|u|\le4a(n+1)(n+2)+2a(n+1)(2n+3)+4n+5$; for $n+1\le N-1$ this is $\le4aN^2+4aN^2+5N\le13aN^2$.
Hence, for $0\le n<n+1\le N-1$,
$$
|E_n(s)|\le4,\qquad |F_n|\le26aN^2,
$$
$$
\big||\hat H_{n+1}|-|\hat H_n|\big|\le4,\qquad
\big|(D_{n+1}-M_{n+1})-s^{-8a(n+1)}(D_n-M_n)\big|\le4aN|\hat H_n|+26aN^2 .
$$
**Large $N$.** Let $N\ge\max(N_0,8a)$ and $|n-\frac N2|<\frac N{8a}$, so
$|2n+1-N|<\frac N{4a}+1$. If $|2n+1-N|<\frac N{4a}$, (Z) applies. Otherwise
$|2n+1-N|\ge\frac N{4a}\ge2$; put $n'=n-1$ if $2n+1>N$ and $n'=n+1$ if $2n+1<N$. Then
$0\le n'\le N-1$ and $|2n'+1-N|=|2n+1-N|-2<\frac N{4a}$, so (Z) holds at $n'$, and one step of
the identities gives $|\hat H_n|\le K_0+4$ and
$|D_n-M_n|\le K_0N^2+4aN(K_0+4)+26aN^2\le(K_0+4a(K_0+4)+26a)N^2$.
**Small $N$.** For the finitely many $N<\max(N_0,8a)$ use $|\hat H_n|\le4N$,
$|D_n|\le24aN^3$ (Section 5) and $|M_n|=|C_{a,N}|<\infty$. $\square$

Lemma W shows that (5.20) on $W_N$ follows from Zheng's Lemma 5.2 exactly as he states it; it is
also the form of (5.12) used in Section 8.

## 8. (5.19) for the corrected $b$

**Proposition 5.19.** Assume Zheng's Lemma 5.2 in the form (Z). Then there is $K$ such that
for all $N\ge1$ and $(n,i)\in W_N$: $|b_{n,i}\hat H_n(s)|\le KN^2$.

*Proof.* By Proposition 5.18, $|b_{n,i}|\le2N^2$ on $W_N$; by Lemma W, $|\hat H_n(s)|\le K_1$
there. Take $K=2K_1$. $\square$

Zheng's own derivation is "(5.18) and (5.12)"; the two repairs are the window version of
(5.18) (Section 6) and the colour-window bookkeeping (Section 7). Nothing depends on the sign of
the summed terms of $b$. Lemma 5.2 itself, and the vanishing $A^\pm_{p,q}(N,0)\equiv0$ that it uses
((5.14)–(5.15)), do not involve $b$ and are cited unchanged.

## 9. Numerical evidence

Scripts (in `scripts/zheng/`): `check_corrected.py`, `check_518_literal.py`, `check_prop41.py`,
`zheng_phys_copy.py`; outputs `*.out` in the same directory.

* Proposition B agrees with the definition of $b$ (400 random $(N,n,i)$, $N<400$): max relative
  error $2\cdot10^{-13}$.
* Proposition 5.16, $a\in\{1,3,5,7,11,21\}$, $N\in[1,119]\cup\{200,301,500,801,1000,1500\}$, all
  $n+i<N$: $\max|b\hat H+D|/N^4\le1.45$ (bound $7+24a$); $\max|b|/N^3=0.25$ (bound $1.75$);
  $\max|\hat H|/N=1$ (bound 4); $\max|D|/(aN^3)\le1$ (bound 24).
* Proposition 5.18 on $W_N$, same range: $\max|b|/N^2=0.70$ ($a=1$), $0.60$–$0.62$ ($a\ge3$)
  (bound 2).
* Lemma W: identities (R1), (R2) hold to $3\cdot10^{-8}$; $\max|E_n|=3.94$ (bound 4);
  $\max|F_n|/(aN^2)=0.35$ (bound 26). $\sup|\hat H_n|$ on Zheng's colour window / on the extra
  boundary layer, $8a\le N<1500$: $0.71/0.85$ ($a=3$), $0.44/0.64$ ($a=5$), $0.31/0.41$ ($a=7$).
* (5.19) on $W_N$: $\max|b\hat H|/N^2=0.85$ over the whole range above (small $N$ dominate);
  $0.394, 0.397, 0.419$ at $N=201,401,801$ for $a=3$; $0.25$ for $a=5$; $0.18$ for $a=7$.
* (5.20) on $W_N$: $\max|D_n-M_n|/N^2=0.011,0.006,0.003$ at $N=201,401,801$ ($a=3,5,7$ alike).
* (5.18) as printed, $i=1$, $n=N/2$: $|b|/N^2=0.54,0.86,1.20,1.56,1.92$ for $N=10^2,\dots,10^6$
  (corrected sign; printed sign $0.82,\dots,2.02$), growing like $(\log N)/(2\pi)$.
* Prop. 4.1: for every odd $a\le401$, $\min_{N\bmod 8a}|A^+_{a,2}(N,1)|\ge6.2835$; the minimum
  tends to $2\pi$ and is attained at $N\equiv a$ or $7a\pmod{8a}$. ($A^+_{a,2}(\cdot,1)$ is
  $8a$-periodic, so this is a complete check for these $a$; it is not a proof for all $a$.)

## 10. Notes on the verbatim estimates

* **Lemma 3.2.** Zheng's proof combines (3.21) (error $O(\log N)$, uniform on $0\le n,i,n+i<N$)
  with a quadratic upper bound for $f$ away from its maximum; the $O(\log N)$ is absorbed by
  replacing $\epsilon$ with $\epsilon/2$, since $N^{2\delta-1}/\log N\to\infty$. The statement is
  unchanged.
* **Lemma 3.3.** The phase error $e^{\beta\pi i n/(2N)}=e^{\beta\pi i/4}(1+O(N^{\delta-1}))$ and the
  Riemann-sum error $O(N^{\delta-1})$ are dominated by $O(N^{3\delta-2})$ because $\delta>\frac12$.
  The previous audit (`audit2/zheng_l33.py`) found error$/N$ below $N^{3\delta-2}$ for
  $\beta\in\{0,-25\}$, $N\le1600$.
* **(5.20), Prop. 4.1.** These are $b$-free and are cited unchanged; the only addition is
  Lemma W for the window.

## Appendix: labels used in the formal library

| Label above | Named proposition |
|---|---|
| Lemma 3.2 | `ZhengLemma32` |
| Lemma 3.3 ($\beta=-(8a+1)$ and $0$) | `ZhengLemma33 (-(8a+1)) δ`, `ZhengLemma33 0 δ` |
| (5.16) | `ZhengEq516 a` |
| (5.19) | `ZhengEq519 a` |
| (5.20) | `ZhengEq520 a` |
| Prop. 4.1 | `ZhengProp41 a` |
