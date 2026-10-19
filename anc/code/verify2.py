# Independent check #2 (Python, exact mod 2^K): Clenshaw + composition implementation of S
import sys
K = 160
MOD = 1 << K
def nu(c):
    c %= MOD
    if c == 0: return K
    return (c & -c).bit_length() - 1
def add(a,b):
    n=max(len(a),len(b)); return [((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%MOD for i in range(n)]
def sub(a,b):
    n=max(len(a),len(b)); return [((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%MOD for i in range(n)]
def mulx(a,c=1):  # c*x*a
    return [0]+[(c*v)%MOD for v in a]
def M1(P):  # sum p_j T_j(x) via Clenshaw
    d=len(P)-1
    b1=[0]; b2=[0]
    for j in range(d,0,-1):
        bj = sub(add([P[j]], mulx(b1,2)), b2)
        b2, b1 = b1, bj
    return sub(add([P[0]], mulx(b1,1)), b2)
def compose_2x2m1(Q):  # Q(2x^2-1) by Horner
    res=[0]
    for c in reversed(Q):
        # res = res*(2x^2-1) + c
        new=[0]*(len(res)+2)
        for i,v in enumerate(res):
            if v:
                new[i+2]=(new[i+2]+2*v)%MOD
                new[i]=(new[i]-v)%MOD
        new[0]=(new[0]+c)%MOD
        res=new
    while len(res)>1 and res[-1]==0: res.pop()
    return res
def S(P): return compose_2x2m1(M1(P))
def divxm1(P):  # exact division by (x-1), synthetic
    d=len(P)-1; q=[0]*d; carry=0
    for i in range(d,0,-1):
        carry=(carry+P[i])%MOD; q[i-1]=carry
    assert (carry+P[0])%MOD==0
    return q
def cheb(n):  # T_n coefficients via recurrence
    a=[1]; b=[0,1]
    if n==0: return a
    for _ in range(n-1):
        a,b=b,sub(mulx(b,2),a)
    return b
def run(m, imax):
    im = 1 if m%4==0 else 2
    Pprev = [0]*(m//4)+[1] if m%4==0 else cheb(m//2)
    out=[]
    for i in range(im, imax+1):
        P=S(Pprev); R=divxm1(sub(P,Pprev))
        v=min(nu(c) for c in R)
        r0=sum(R)%MOD; r1=sum(j*c for j,c in enumerate(R))%MOD
        out.append((i,v,nu(r1),nu(r0), ((r0>>(v+1)) + (r1>>v))%4 ))
        Pprev=P
    return out
bad=0; tot=0
for m in range(2, int(sys.argv[1])+1, 2):
    im = 1 if m%4==0 else 2
    imax = im + int(sys.argv[2])
    res=run(m, imax)
    for k,(i,v,n1,n0,ab) in enumerate(res):
        if i>im:
            tot+=1
            ok = (n1==v and n0==v+1 and ab==2 and v+4<K)
            if k+1<len(res): ok = ok and res[k+1][1]==v+3
            if not ok: bad+=1; print("FAIL",m,res[k], res[k+1] if k+1<len(res) else None)
    print(m, [r[1] for r in res], flush=True) if m<=16 or m%32==0 else None
print("total checked",tot,"failures",bad)
