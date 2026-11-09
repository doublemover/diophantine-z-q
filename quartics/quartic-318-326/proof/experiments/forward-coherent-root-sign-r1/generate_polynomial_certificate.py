from pathlib import Path
import sympy as s
x,y,a,b,D=s.symbols('x y a b D');q=x*x+D;r=a*a+D;L=-(b+y);d=a-x;X=L**2-(x+a)*d*d;Y=L*(x*d*d-X)-y*d**3
v=x**4-6*D*x*x+D*D;w=a**4-6*D*a*a+D*D
N=2*Y*d*(q*q*r*r+16*D*y*y*b*b)-(2*y*w*q-2*b*v*r)*(X*X+D*d**4)
cs=[y*y-x**3+D*x,b*b-a**3+D*a]
f=s.Poly(s.expand(N),y,b,x,a,D);q1,rem=s.div(f,s.Poly(cs[0],y,b,x,a,D));q2,rem=s.div(rem,s.Poly(cs[1],y,b,x,a,D));assert rem.is_zero

def lean(expr):return str(expr).replace('**','^')
def terms(expr):return '\n      + '.join('('+lean(t)+')' for t in s.Add.make_args(expr))
text='''module
public import Mathlib.Tactic
public section
namespace CoherentSecantPolynomial318
variable {F : Type*} [Field F]
set_option maxHeartbeats 2000000

@[expose] def rawX (x y a b : F) : F := (-b-y)^2-(x+a)*(a-x)^2
@[expose] def rawY (x y a b : F) : F :=
  (-b-y)*(x*(a-x)^2-rawX x y a b)-y*(a-x)^3

/-- A checked polynomial certificate for the historical coherent chart's
subtraction formula. Generated coefficients are checked by Lean's ring kernel
proofs; the external algebra program is not a trusted proof oracle. -/
theorem secant_identity (D x y a b : F)
    (hc : y^2=x^3-D*x) (hd : b^2=a^3-D*a) :
    2*rawY x y a b*(a-x)*((x^2+D)^2*(a^2+D)^2+16*D*y^2*b^2)=
      (2*y*(a^4-6*D*a^2+D^2)*(x^2+D)-
        2*b*(x^4-6*D*x^2+D^2)*(a^2+D))*
        ((rawX x y a b)^2+D*(a-x)^4) := by
  dsimp [rawY,rawX]
  linear_combination
    ('''+terms(q1.as_expr())+''')*hc +
    ('''+terms(q2.as_expr())+''')*hd

end CoherentSecantPolynomial318
'''
Path(__file__).with_name('CoherentSecantPolynomial318.lean').write_text(text)
print('Exact remainder zero; certificate terms:',len(q1.terms()),len(q2.terms()))
