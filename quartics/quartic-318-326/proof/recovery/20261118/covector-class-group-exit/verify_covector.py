"""Exact SymPy replay. No class number or Selmer dimension is assumed or computed."""
import sympy as s
x,X=s.symbols("x X")
f=x**3+2*x*x-3*x
fprime=s.diff(f,x)
psi3=3*x**4+8*x**3-18*x*x-9
psi4over2y=2*x**6+8*x**5-30*x**4-90*x*x-72*x+54
g=s.expand(16*f**2*psi4over2y-psi3**3)
assert s.degree(g,x)==12 and s.gcd(g,s.diff(g,x))==1
def red(a):return s.rem(a,g,x,domain=s.QQ)
inv=s.invert(f,g,x)
x2=red(fprime**2*inv/4-2-2*x)
R=red(-1+fprime*(x-x2)*inv/2)
# For h=zeta+1/zeta, h^2+h-1=0:
# U^2=(h^2-4)f(1+hR)^2=A+hB.  X is the variable for U^2/4.
A=red(f*(-3*(1+R**2)-(2*R-R**2)))
B=red(f*(-(1+R**2)-2*(2*R-R**2)))
raw=(4*X-A)**2+(4*X-A)*B-B**2
M=sum(X**i[0]*red(v) for i,v in s.Poly(raw,X).terms())
res=s.Poly(s.resultant(g,M,x),X).monic()
coef=[1,-700,-3842,16695000,-224138925,-439425000,1192371070500,-534340800000,
      -19638779315625,501591411562500,3056024037318750,19643523283125000,101989511552503125]
H=s.Poly.from_list(coef,gens=X,domain=s.QQ)
assert res==H**2 and s.gcd(H,H.diff()).degree()==0 and H.eval(0)!=0
def trace(q):return q-sum((y*y-i*(i-1)*(i+3))%q==0 for i in range(q) for y in range(q))
assert [trace(q) for q in (5,7,13)]==[-2,0,-2]
# class of Frobenius 13 in F25*/F5* order six, via X^2+2X+13
a,b=1,0
for i in range(1,7):
    a,b=(-13*b)%5,(a-2*b)%5
    assert (b==0)==(i==6)
assert (4-4*13)%5==2 and (-7)%5==3 and {pow(3,i,5) for i in range(4)}=={1,2,3,4}
print("degree",H.degree()*2,"distinct resolvent values; base traces at 5,7,13 = -2,0,-2")
print("H descending coefficients:",coef)
