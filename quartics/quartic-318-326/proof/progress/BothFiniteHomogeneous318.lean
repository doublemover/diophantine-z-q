module
public import BothFiniteTangent318
public section
namespace BothFiniteHomogeneous318
open InfinityVietaAlgebra318
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]
@[expose] def normalizedX (x t a b : R) := a^2-(x+t)*b^2
@[expose] def normalizedY (x y t a b : R) :=
  -a*(x*b^2-normalizedX x t a b)-y*b^3
@[expose] def numeratorX (x t D L : R) := L^2-(x+t)*D^2
@[expose] def numeratorY (x y t D L : R) :=
  L*(x*D^2-numeratorX x t D L)-y*D^3

lemma normalized_norm (A B x y t z a b : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (h1 : a*x+b*y=1) (h2 : a*t+b*z=1)
    (htan : a*(y+z)+b*(x^2+x*t+t^2+A)=0) :
    c A B a+y*z*normalizedY x y t a b=0 := by
  unfold c normalizedY normalizedX
  linear_combination -a^3*hF+
    (-A*a^2-a^2*t^2-a^2*t*x-a^2*x^2-a*b*t*z-a*b*x*z-b^2*y*z-b*z)*h1+
    (a^2*t*x+a^2*x^2-a*t-1)*h2+a^2*y*htan

lemma normalized_trace (A B x y t z a b : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (h1 : a*x+b*y=1) (h2 : a*t+b*z=1)
    (htan : a*(y+z)+b*(x^2+x*t+t^2+A)=0) :
    (x*z+t*y)*normalizedY x y t a b-d A B a b=
      b*normalizedX x t a b*y*z := by
  unfold d normalizedY normalizedX
  linear_combination 3*a^2*b*hG+
    (a^2*z-a*b*t^2-a*b*t*x-b^2*t*y+b^2*t*z-b*t)*h1+
    (a^2*t-2*a*b*z)*htan+(2*A*a*b-a^2*z+2*a*b*t^2+b*t)*h2

/-- No finite-output denominator is required: this normalized comparison also
covers outputs at infinity and retains nonreduced coefficient directions. -/
theorem normalized_coordinates (A B x y t z a b U V : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (h1 : a*x+b*y=1) (h2 : a*t+b*z=1)
    (htan : a*(y+z)+b*(x^2+x*t+t^2+A)=0)
    (hy : IsUnit y) (hz : IsUnit z)
    (hU : c A B a*y*z*U=(x*z+t*y)*c A B a+d A B a b*y*z)
    (hV : V=a*U-b) :
    U*normalizedY x y t a b=b*normalizedX x t a b ∧
      V*normalizedY x y t a b=b^3 := by
  have hn := normalized_norm A B x y t z a b hF hG h1 h2 htan
  have ht := normalized_trace A B x y t z a b hF hG h1 h2 htan
  have hu : U*normalizedY x y t a b=b*normalizedX x t a b := by
    apply ((hy.mul hz).pow 2).mul_left_cancel
    linear_combination -hU+(y*z*U-x*z-t*y)*hn+y*z*ht
  refine ⟨hu,?_⟩
  rw [hV,sub_mul,mul_assoc,hu]
  unfold normalizedY normalizedX
  linear_combination b^3*h1

/-- Equality in homogeneous coordinates on either ordinary-chord or tangent
charts. The theorem cancels neither the chord gap nor the output ordinate. -/
theorem coordinates (A B x y t z a b U V D L : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (h1 : a*x+b*y=1) (h2 : a*t+b*z=1)
    (htan : a*(y+z)+b*(x^2+x*t+t^2+A)=0)
    (hDL : a*D+b*L=0) (hy : IsUnit y) (hz : IsUnit z)
    (hU : c A B a*y*z*U=(x*z+t*y)*c A B a+d A B a b*y*z)
    (hV : V=a*U-b) :
    U*numeratorY x y t D L=numeratorX x t D L*D ∧
      V*numeratorY x y t D L=D^3 := by
  have hD : D=b*(D*y-L*x) := by linear_combination x*hDL-D*h1
  have hL : L= -a*(D*y-L*x) := by linear_combination y*hDL-L*h1
  obtain ⟨hu,hv⟩ := normalized_coordinates A B x y t z a b U V hF hG h1 h2 htan hy hz hU hV
  have hX : numeratorX x t D L=(D*y-L*x)^2*normalizedX x t a b := by
    calc
      _=numeratorX x t (b*(D*y-L*x)) (-a*(D*y-L*x)) :=
        congrArg₂ (numeratorX x t) hD hL
      _=_ := by unfold numeratorX normalizedX; ring
  have hY : numeratorY x y t D L=(D*y-L*x)^3*normalizedY x y t a b := by
    calc
      _=numeratorY x y t (b*(D*y-L*x)) (-a*(D*y-L*x)) :=
        congrArg₂ (numeratorY x y t) hD hL
      _=_ := by unfold numeratorY numeratorX normalizedY normalizedX; ring
  rw [hY,hX]
  constructor
  · calc
      _=(D*y-L*x)^3*(U*normalizedY x y t a b) := by ring
      _=(D*y-L*x)^3*(b*normalizedX x t a b) := by rw [hu]
      _=(D*y-L*x)^2*normalizedX x t a b*(b*(D*y-L*x)) := by ring
      _=_ := congrArg (fun q => (D*y-L*x)^2*normalizedX x t a b*q) hD.symm
  · calc
      _=(D*y-L*x)^3*(V*normalizedY x y t a b) := by ring
      _=(D*y-L*x)^3*b^3 := by rw [hv]
      _=(b*(D*y-L*x))^3 := by ring
      _=D^3 := congrArg (fun q => q^3) hD.symm

end BothFiniteHomogeneous318
