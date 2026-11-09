from pathlib import Path
import sympy as s
D,u,v,a,b,c,e=s.symbols('D u v a b c e');vs=(v,b,e,u,a,c,D)
q=1+D*u*u*a*a;p=u*b+a*v;r=v*b*(1-D*u*u*a*a)-2*D*u*a*(u*u+a*a)
t=1+D*a*a*c*c;k=a*e+c*b;l=b*e*(1-D*a*a*c*c)-2*D*a*c*(a*a+c*c)
Lden=q*q+D*p*p*c*c;Rden=t*t+D*k*k*u*u;Lun=p*e*q+c*r;Run=u*l+k*v*t
Q,rem=s.reduced(s.expand(Lun*Rden-Run*Lden),[v*v-1+D*u**4,b*b-1+D*a**4,e*e-1+D*c**4],*vs);assert rem==0
lean=lambda z:str(z).replace('**','^')
pth=Path('quartics/quartic-318-326/proof/experiments/forward-real-oval-group-r1/RealQuarticAssociativityPolynomial318.lean')
pth.write_text('''module
public import Mathlib.Tactic
public section
namespace RealQuarticAssociativityPolynomial318
set_option maxHeartbeats 2000000
variable {F : Type*} [CommRing F]

/-- Cleared first-coordinate associativity of the reciprocal quartic law.
The coefficient certificate is checked by Lean, not trusted from its generator. -/
theorem cleared_u_associativity (D u v a b c e : F)
    (hv : v^2=1-D*u^4) (hb : b^2=1-D*a^4) (he : e^2=1-D*c^4) :
    ((u*b+a*v)*e*(1+D*u^2*a^2)+c*(v*b*(1-D*u^2*a^2)-2*D*u*a*(u^2+a^2))) *
      ((1+D*a^2*c^2)^2+D*(a*e+c*b)^2*u^2) =
    (u*(b*e*(1-D*a^2*c^2)-2*D*a*c*(a^2+c^2))+(a*e+c*b)*v*(1+D*a^2*c^2)) *
      ((1+D*u^2*a^2)^2+D*(u*b+a*v)^2*c^2) := by
  linear_combination
'''+ ' +\n'.join('    ('+lean(coeff)+')*'+hyp for coeff,hyp in zip(Q,['hv','hb','he']))+'\n\nend RealQuarticAssociativityPolynomial318\n')
print(pth, [len(s.Poly(x,*vs).terms()) for x in Q])
