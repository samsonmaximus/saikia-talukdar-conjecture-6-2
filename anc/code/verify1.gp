\\ Independent check #1 (PARI): definitions verbatim from arXiv:2609.11806 Sec. 6
default(parisize, 4*10^9);
T(n) = polchebyshev(n,1,'x);
S(P) = {my(d=poldegree(P), r=0); for(j=0,d, my(c=polcoef(P,j)); if(c, r += c*T(2*j))); r;}
nuP(P) = {my(v=oo); for(j=0,poldegree(P), my(c=polcoef(P,j)); if(c, v=min(v,valuation(c,2)))); v;}
\\ returns list of [i, v_i, nu(R'(1)), nu(R(1)), (a+b) mod 4]
run(m, imax) = {
  my(im = if(m%4==0,1,2), Pprev = if(m%4==0, 'x^(m/4), T(m/2)), out=List(), P, R, v, a1, a0, ab);
  for(i=im, imax,
    P = S(Pprev); R = (P - Pprev)/('x-1);
    v = nuP(R); a1 = subst(deriv(R),'x,1); a0 = subst(R,'x,1);
    ab = if(valuation(a1,2)==v && valuation(a0,2)==v+1, (a0/2^(v+1) + a1/2^v)%4, -1);
    listput(out, [i, v, valuation(a1,2), valuation(a0,2), ab]);
    Pprev = P);
  Vec(out);
}
{
my(bad=0, cnt=0);
forstep(m=2, 400, 2,
  my(im = if(m%4==0,1,2), res = run(m, im+2));
  for(k=1, #res, my(r=res[k], i=r[1]);
    if(i > im,
      cnt++;
      if(r[3]!=r[2] || r[4]!=r[2]+1 || r[5]!=2, bad++; print("FAIL m=",m," ",r));
      if(k<#res && res[k+1][2]!=r[2]+3, bad++; print("FAIL v step m=",m," ",r," -> ",res[k+1]));
    ));
  \\ base value check
  my(vb = res[2][2], pred = if(m%4==2, 1, if(m%8==4, 1, 2*valuation(m,2)-3)));
  if(vb != pred, bad++; print("base v mismatch m=",m," got ",vb," pred ",pred));
);
print("checked (m,i) pairs: ", cnt, "  failures: ", bad);
}
