default(parisize, 10^9);
T(n) = polchebyshev(n,1,'x);
S(P) = {my(d=poldegree(P), r=0); for(j=0,d, my(c=polcoef(P,j)); if(c, r += c*T(2*j))); r;}
vals(R,K) = {my(Q=subst(R,'x,1+'y)); vector(K+1,k, my(c=polcoef(Q,k-1,'y)); if(c,valuation(c,2),-1));}
{
for(j=1,8, my(m=8*j, n=m/4, P0='x^n, P1=S(P0), R1=(P1-P0)/('x-1), P2=S(P1), R2=(P2-P1)/('x-1));
  print("m=",m," nu(m)=",valuation(m,2));
  print("  R1 t-coef vals: ", vals(R1,12));
  print("  R2 t-coef vals: ", vals(R2,12));
  my(Q=subst(R2,'x,1+'y), v=valuation(content(R2),2), r0=polcoef(Q,0,'y), r1=polcoef(Q,1,'y));
  print("  v2=",v," a+b mod 4 = ", (r0/2^(v+1) + r1/2^v)%4);
);
}
