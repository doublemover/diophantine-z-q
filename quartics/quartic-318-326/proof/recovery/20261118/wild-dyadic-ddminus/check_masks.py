from sympy import symbols,expand
u,w,x,W,h,X,Y,e,E,V=symbols('u w x W h X Y e E V')
for d in (1,-1):
 L=(1+u)*w+(1+d)//2*u*u+u+172
 J=(1+x)*W+(1+d)//2+x+172*x*x
 assert expand((1+u+w)**2+d*u*u+343-(w*w+2*L))==0
 assert expand((1+x+W)**2+d+343*x*x-(W*W+2*J))==0
 assert (-d)**5==-d and 2400==75*2**5
assert expand((X+e)**2+(Y-X)*(X+e)-2401*X*Y-(e*(e+X+Y)-2400*X*Y))==0
assert expand(X**6*(X*V-X*E-X)**6-X**2*X**10*(V-E-1)**6)==0
assert 1-4*86==-343
print('chart identities, unramified discriminant, residual product, exponent verified')
