\\ sanity check of the congruence implied (via the paper's Cor. 6.3) by Conjecture 6.2
N = 6000;
f(k) = eta('q^k + O('q^(N+1)), 0);  \\ (q^k;q^k)_inf
A = f(2)^3/(f(1)^2*f(4));
cm(m) = if(m%4==2, -4, 2*valuation(m,2)-5);
{
for(j=1,8, my(m=2*j, F=A^m, im=if(m%4==0,1,2), worst=oo, bad=0);
  for(i=im+1, 7,
    my(mod=3*i+cm(m), minv=oo);
    for(n=1, floor(N/2^i),
      my(d = polcoef(F,2^i*n,'q) - polcoef(F,2^(i-1)*n,'q));
      if(d!=0, minv=min(minv, valuation(d,2)));
    );
    print("m=",m," i=",i," modulus exponent 3i+c_m=",mod," min nu over n<=",floor(N/2^i),": ",minv, if(minv>=mod," OK"," FAIL"));
  );
);
}
