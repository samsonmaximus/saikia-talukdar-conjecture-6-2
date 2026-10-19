\\ Conjecture 6.2 of arXiv:2609.11806 (even m)
default(parisize, 2*10^9);
Tcache = Map();
T(n) = polchebyshev(n,1,'x);
\\ S: x^j -> T_{2j}(x)
S(P) = my(d=poldegree(P), r=0); for(j=0,d, my(c=polcoef(P,j)); if(c, r += c*T(2*j))); r;
nu2(P) = my(v=oo); for(j=0,poldegree(P), my(c=polcoef(P,j)); if(c, v=min(v,valuation(c,2)))); v;
check(m, imax) = {
  my(im = if(m%4==0,1,2), P0 = if(m%4==0, 'x^(m/4), T(m/2)), Pprev=P0, res=List());
  my(P);
  for(i=im, imax,
    P = S(Pprev);
    my(R = (P - Pprev)/('x-1));
    my(vi = nu2(R), a = valuation(subst(deriv(R),'x,1),2), b = valuation(subst(R,'x,1),2));
    listput(res, [i, vi, a, b]);
    Pprev = P;
  );
  res;
}
for(mm=1,20, my(m=2*mm); my(r=check(m, if(m<=16,8,7))); print("m=",m," [i,v_i,nu(R'(1)),nu(R(1))]: ", Vec(r)));
