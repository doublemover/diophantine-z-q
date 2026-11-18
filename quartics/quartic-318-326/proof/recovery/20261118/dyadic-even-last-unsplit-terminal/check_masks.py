from sympy import symbols,expand
q,T,L,J,v,t,f,m,n,u,S,P,Z,B0,B1,W,V=symbols('q T L J v t f m n u S P Z B0 B1 W V')
def eq(x,y):assert expand(x-y)==0
eq(f*(v+t)**2+q*T*L*t*(v+t)+T*J*t**2,f*v**2+(q*T*L+2*f)*t*v+(f+q*T*L+T*J)*t**2)
a=f*v**2+q*m*t*v+(B0*t+q*q*B1)*t**2-u*q**10
b=f*V**2+q*m*S*V+q*B0*S**3+q*q*B1*S*S-u*q**8
eq(a.subs({v:q*V,t:q*S}),q*q*b)
c=f*Z**2+m*P*Z+B0*P**3+B1*P*P-u*q**4
eq(b.subs({S:q*P,V:q**2*Z}),q**4*c)
d=f*V**2+m*W*V+q*B0*W**3+B1*W**2-u*q*q
eq(c.subs({P:q*W,Z:q*V}),q*q*d)
eq(d.subs({W:q*S,V:q*Z}),q*q*(f*Z**2+m*S*Z+q*q*B0*S**3+B1*S*S-u))
print('exact cusp shift, four terminal scale divisions verified')
