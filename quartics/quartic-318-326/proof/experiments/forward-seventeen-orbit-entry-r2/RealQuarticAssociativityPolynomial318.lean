module
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
    (-D^2*a^5*c^4*e*v + 2*D^2*a^5*c^3*u - D^2*a^4*b*c^5*v - D^2*a^4*b*c^4*e*u - 2*D^2*a^3*b^2*c^5*u + 2*D^2*a^3*c^5*u - D*a^3*c^2*e*v - D*a^2*b*c^3*v - 3*D*a^2*b*c^2*e*u - 2*D*a*b^2*c^3*u)*hv +
    (2*D^3*a^3*c^5*u^5 - 2*D^2*a^3*c^5*u + D^2*a^3*c^4*e*u^2*v - D^2*a^3*c^2*e*u^4*v + 2*D^2*a^3*c*e^2*u^5 - D^2*a^2*b*c^5*u^2*v + D^2*a^2*b*c^4*e*u^3 - D^2*a^2*b*c^3*u^4*v + D^2*a^2*b*c^2*e*u^5 + 2*D^2*a*c^5*u^3 - 2*D*a*c^3*u + 2*D*a*c*e^2*u^3)*hb +
    (-2*D^3*a^7*c*u^5 - 4*D^2*a^5*c*u^3 + D^2*a^5*e*u^4*v + D^2*a^4*b*c*u^4*v + D^2*a^4*b*e*u^5 + D*a^3*e*u^2*v + 3*D*a^2*b*c*u^2*v + D*a^2*b*e*u^3 + 2*D*a*c*u^3)*he

end RealQuarticAssociativityPolynomial318
