import numpy as np, sys
pi=np.pi
def spow(m,N): # s^m, s=e^{pi i/N}
    return np.exp(1j*pi*(np.mod(m,2*N))/N)
def A_plus(a,N,k=1):
    j=np.arange(1,2*a)
    return np.sum(np.exp(-N*j**2*pi*1j/(4*a))*j**(2*k)*np.sin(j*pi/a)*np.sin(j*pi/2))
def Cconst(a,N):
    return -2*(N**2.5/(4*a)**1.5)*np.exp(-(a/2+2/a)*pi*1j/(2*N)+pi*1j/4)*A_plus(a,N)
def Cbeta(beta):
    return np.exp(beta*pi*1j/4)/np.sqrt(1-1j*beta+0j)
def H_and_D(a,n,N):
    k=np.arange(-n,n+1)
    E=-4*a*n*(n+1)+2*a*k*(2*k+1); f=4*k+1
    H=np.sum(spow(E+f,N)-spow(E-f,N))
    D=0.5*np.sum((E+f)*spow(E+f,N)-(E-f)*spow(E-f,N))
    return H,D
def run(a,N,check=False):
    q=lambda m: np.exp(2j*pi*m/N)
    m=np.arange(0,N)
    g=np.zeros(N,complex)
    g[1:]=(N-m[1:])/(1-q(m[1:]))+m[1:]/(1-q(-m[1:]))
    G=np.concatenate([[0],np.cumsum(g[1:])])  # G[t]=sum_{m=1}^t g(m)
    hj=np.zeros(N,complex); hj[1:]=m[1:]/(1-q(-m[1:]))
    Hc=np.concatenate([[0],np.cumsum(hj[1:])])
    ls=np.zeros(N); ls[1:]=np.log(4*np.sin(m[1:]*pi/N)**2)
    Pl=np.concatenate([[0],np.cumsum(ls[1:])])
    l2=np.zeros(N); l2[1:]=np.log(2*np.sin(m[1:]*pi/N))
    Ql=np.concatenate([[0],np.cumsum(l2[1:])])
    n0,i0=N//2,N//4
    logS0=Pl[i0+n0]-Pl[i0]-Ql[n0]
    tot=0j; maxdev520=0; max519=0
    C=Cconst(a,N)
    for n in range(N):
        H,D=H_and_D(a,n,N)
        an_inv=np.exp(-1j*pi*n*(n+1-N)/(2*N))
        i=np.arange(0,N-n)
        b=-N*(i+n)+(G[i+n]-G[i])-Hc[n]
        S=np.exp(Pl[i+n]-Pl[i]-Ql[n]-logS0)
        tot+=an_inv*np.sum(S*(b*H+D))
        if check:
            win=np.abs(n-N/2)+np.abs(i-N/4)<N/(8*a)
            if win.any():
                ph=np.exp(1j*(-8*a)*pi*n*(n+1-N)/(2*N))
                maxdev520=max(maxdev520,abs(D-C*ph))
                max519=max(max519,np.max(np.abs(b[win]*H)))
    s=np.exp(1j*pi/N)
    diag_over_S0=tot/s/N
    beta=-(8*a+1)
    lead_over_S0=C*Cbeta(beta)*np.exp((8*a+1)*N*pi*1j/8)/s
    return diag_over_S0/lead_over_S0, abs(C)/N**2.5, maxdev520/N**2, max519/N**2
a=int(sys.argv[1])
for N in [int(x) for x in sys.argv[2:]]:
    r,c,d520,d519=run(a,N,check=True)
    print(a,N,"ratio",np.round(r,4),"|ratio|",round(abs(r),4),"|C|/N^2.5",round(c,4),"dev520/N^2",round(d520,3),"519/N^2",round(d519,3))
