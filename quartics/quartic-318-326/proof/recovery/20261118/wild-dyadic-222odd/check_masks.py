from sympy import symbols,expand
d,a,q,u,c,j,Y,z,R,f,P,m,w,s,E,V=symbols('d a q u c j Y z R f P m w s E V')
assert expand((u*q)*a*d*u**2+(u*q)**3*j-(u*q)**2*c*u*Y-u**2*(u*q*(a*d+j*q**2-c*q*Y)))==0
for d in (1,-1):
 c0=(4801-d)//2; m=c0%2
 f=171-w+d*w**4*s**2
 N=c0+4801*(w*m+f*m*m)
 assert expand(N-c0-4801*171*m-4801*m*d*w**4*s**2)==0
 assert (c0+4801*171*m)%2==0
 assert expand(c0+4801*(w*(m+z)+f*(m+z)**2)-(N+4801*(w+2*f*m)*z+4801*f*z*z))==0
 assert (d+171)%2==0
assert expand(w**3*(w*E+w*V+w)**5-w**2*w**6*(E+V+1)**5)==0
print('failed-derivative cancellation, split exponents, first quotient direction verified')
