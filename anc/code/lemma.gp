\\ verify content(Theta(t^k)) = 2^(k+1) and low-order coefficients, k=0..80
T(n) = polchebyshev(n,1,'x);
S(P) = {my(d=poldegree(P), r=0); for(j=0,d, my(c=polcoef(P,j)); if(c, r += c*T(2*j))); r;}
Th(R) = S(('x-1)*R)/('x-1);
{
my(bad=0);
for(k=0,80,
  my(Q = subst(Th(('x-1)^k),'x,1+'t), c = content(Q), v = valuation(c,2));
  if(v != k+1, bad++; print("content mismatch k=",k," v=",v));
  if(k>=4 && (polcoef(Q,0,'t)!=0 || polcoef(Q,1,'t)!=0), bad++; print("low coeff nonzero k=",k));
  if(k<=3, print("k=",k,": ",Q));
);
print("lemma failures: ",bad);
}
