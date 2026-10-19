# Independent check written from scratch. Usage: python independent_check.py [mmax] [N] [mc]
# (1) R_i valuations from ST's definitions,
# (2) congruences directly from the product generating function.
import sys
def nu(c):
    if c==0: return 10**9
    v=0
    while c%2==0: c//=2; v+=1
    return v
def numin(p): return min(nu(c) for c in p if c) 
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def pscale(a,s): return [s*c for c in a]
T=[[1],[0,1]]
def cheb(n):
    while len(T)<=n:
        a=T[-1];b=T[-2]; T.append(padd([0]+pscale(a,2),pscale(b,-1)))
    return T[n]
def S(p):
    r=[0]
    for j,c in enumerate(p):
        if c: r=padd(r,pscale(cheb(2*j),c))
    return r
def divx1(p):  # synthetic division by x-1, assert exact
    n=len(p)-1; q=[0]*n; acc=0
    for k in range(n,0,-1):
        acc=acc+p[k]; q[k-1]=acc
    assert acc+p[0]==0
    return q
def ev(p,x): return sum(c*x**k for k,c in enumerate(p))
def der1(p): return sum(k*c for k,c in enumerate(p))
fails=0
MMAX=int(sys.argv[1]) if len(sys.argv)>1 else 80
for m in range(2,MMAX+1,2):
    im=1 if m%4==0 else 2
    P={im-1: ([0]*(m//4)+[1]) if m%4==0 else cheb(m//2)}
    top=im+5
    for i in range(im,top+2): P[i]=S(P[i-1])
    R={i:divx1(padd(P[i],pscale(P[i-1],-1))) for i in range(im,top+2)}
    nm=nu(m)
    for i in range(im+1,top+1):
        v=numin(R[i]); pred=3*i-8 if nm==1 else 3*i+2*nm-9
        ok = v==pred and nu(der1(R[i]))==v and nu(ev(R[i],1))==v+1 and numin(R[i+1])==v+3
        if not ok: fails+=1; print("FAIL",m,i)
print("valuation check even m<=%d, i_m<i<=i_m+5: fails ="%MMAX,fails)
# (2) direct congruences
N=int(sys.argv[2]) if len(sys.argv)>2 else 2**8
MC=int(sys.argv[3]) if len(sys.argv)>3 else 24
A=[1]+[0]*N
for j in range(1,N+1,2):
    # multiply by (1+q^j)/(1-q^j) = 1 + 2 sum_{k>=1} q^{jk}
    B=A[:]
    for n in range(N+1):
        if A[n]:
            k=j
            while n+k<=N: B[n+k]+=2*A[n]; k+=j
    A=B
def mul(a,b):
    c=[0]*(N+1)
    for i,x in enumerate(a):
        if x:
            for j in range(N+1-i): c[i+j]+=x*b[j]
    return c
pw=[1]+[0]*N; f2=0
for m in range(1,MC+1):
    pw=mul(pw,A)
    if m%2: continue
    im=1 if m%4==0 else 2; nm=nu(m); cm=-4 if nm==1 else 2*nm-5
    for i in range(im+1,N.bit_length()):
        mod=3*i+cm; mins=[]
        for n in range(1,N//2**i+1):
            d=pw[2**i*n]-pw[2**(i-1)*n]; mins.append(nu(d))
        if not mins: continue
        if min(mins)<mod or mins[0]!=mod: f2+=1; print("CONG FAIL",m,i,min(mins),mod)
print("direct congruence check even m<=%d, 2^i n<=%d: fails ="%(MC,N),f2)

# (3) the q-series identities of Lemma 6.1 (truncated at q^N)
def phi(sign):  # phi(sign*q)
    c=[0]*(N+1)
    k=0
    while k*k<=N:
        c[k*k]+= (1 if k==0 else 2)*(sign**(k*k))
        k+=1
    return c
def mul(a,b):
    c=[0]*(N+1)
    for i,x in enumerate(a):
        if x:
            for j in range(N+1-i): c[i+j]+=x*b[j]
    return c
def sub2(a): # f(q) -> f(q^2)
    c=[0]*(N+1)
    for i,x in enumerate(a):
        if 2*i<=N: c[2*i]=x
    return c
p,m=phi(1),phi(-1)
print("phi(q)phi(-q)=phi(-q^2)^2:", mul(p,m)==mul(sub2(m),sub2(m)))
print("phi(q)^2+phi(-q)^2=2phi(q^2)^2:", [a+b for a,b in zip(mul(p,p),mul(m,m))]==[2*x for x in mul(sub2(p),sub2(p))])
# A from product; check A^2 phi(-q) = phi(q)
A=[1]+[0]*N
for j in range(1,N+1,2):
    B=A[:]
    for n in range(N+1):
        if A[n]:
            k=j
            while n+k<=N: B[n+k]+=2*A[n]; k+=j
    A=B
A2=mul(A,A)
print("A^2 phi(-q) = phi(q):", mul(A2,m)==p)
# U(A^{2k}) = T_k(xi), xi=A^4
xi=mul(A2,A2)
def U(a): return [a[2*n] for n in range(N//2+1)]
T=[[1],[0,1]]
for n in range(2,12): T.append([0]+[2*c for c in T[-1]]); T[-1]=[x-(T[-3][i] if i<len(T[-3]) else 0) for i,x in enumerate(T[-1])]
def evalpoly(P,f):
    res=[0]*(N+1); pw=[1]+[0]*N
    for c in P:
        res=[r+c*x for r,x in zip(res,pw)]; pw=mul(pw,f)
    return res
ok=True; pw=[1]+[0]*N
for k in range(1,11):
    pw=mul(pw,A2)
    lhs=U(pw); rhs=evalpoly(T[k],xi)[:N//2+1]
    ok&= lhs==rhs
print("U(A^{2k}) = T_k(xi), k<=10:", ok)
