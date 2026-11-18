from sympy import symbols,expand,Rational
v,Q,V,z,E,W,a,b,g,H,p,f,F=symbols('v Q V z E W a b g H p f F')
assert expand(2*((2*V)**2+2*(2*V)+344)-4*2*(V**2+V+86))==0
assert expand((v*Q)*(v**2+(v*Q)*v+43*(v*Q)**3)-v**2*(v*Q*(1+Q+43*v*Q**3)))==0
c=(4801-Rational(1,343**3))/2
assert 4801*343**3-1==2*96868833603 and c.p%2 and c.q%2
assert expand(H*z**4*(a*(z*E)+b*(z*W)+g*z)**6-z**2*H*z**8*(a*E+b*W+g)**6)==0
assert expand(2*c+(Rational(1,343**3)-f**-3)+4801*(2*p+p**2)-(4801*(1+p)**2-f**-3))==0
assert all((u*u+u+86)%2==0 for u in (0,1)); print('unit, chart, and exponent identities OK')
