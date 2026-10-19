T(n) = polchebyshev(n,1,'x);
S(P) = {my(d=poldegree(P), r=0); for(j=0,d, my(c=polcoef(P,j)); if(c, r += c*T(2*j))); r;}
Th(R) = S(('x-1)*R)/('x-1);
nuP(P) = {my(v=oo); for(j=0,poldegree(P), my(c=polcoef(P,j)); if(c, v=min(v,valuation(c,2)))); v;}
{
my(bad=0);
forstep(m=8, 480, 8,
  my(n=m/4, P0='x^n, P1=S(P0), R1=(P1-P0)/('x-1), R2=Th(R1), Q=(T(2*n)-1)/('x-1), A=Th(Q), v=2*valuation(n,2)+1);
  if(R2 != A - Q, bad++; print("R2 != A-Q at m=",m));
  my(At=subst(A,'x,1+'t), Qt=subst(Q,'x,1+'t));
  if(nuP(Q)!=v || valuation(polcoef(Qt,1,'t),2)!=v || valuation(polcoef(Qt,0,'t),2)!=v+1, bad++; print("Q shape fail m=",m));
  if(nuP(A) < v+2 || valuation(polcoef(At,0,'t),2)!=v+4 || valuation(polcoef(At,1,'t),2)!=v+3, bad++; print("A fail m=",m," ",nuP(A)," ",valuation(polcoef(At,0,'t),2)," ",valuation(polcoef(At,1,'t),2)));
  my(aQ=polcoef(Qt,0,'t)/2^(v+1), bQ=polcoef(Qt,1,'t)/2^v);
  if(aQ%8!=1 || bQ%8!=5, bad++; print("aQ,bQ mod 8 fail m=",m," ",aQ%8," ",bQ%8));
);
print("base-case (8|m) component failures: ", bad);
}
