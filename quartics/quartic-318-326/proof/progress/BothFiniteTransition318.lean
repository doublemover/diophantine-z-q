module
public import BothFiniteHomogeneous318
public section
namespace BothFiniteTransition318
open InfinityVietaAlgebra318
set_option maxHeartbeats 600000
variable {R : Type*} [CommRing R]

lemma scaled_q (A B u v r w x y t z : R)
    (hu : u*y=x) (hv : v*y=1) (hr : r*z=t) (hw : w*z=1) :
    q A B r v w*y^2*z^2=BothFiniteTangent318.Q A B x y t z := by
  unfold q BothFiniteTangent318.Q
  linear_combination (-A*v*y^2*z-A*w*y^2*z)*hr+
    (-A*t*y*z-B*v*y*z^2-B*w*y*z^2-B*z^2)*hv+
    (-A*t*y^2-B*w*y^2*z-B*y^2-B*y*z)*hw

lemma scaled_s (A u v r w x y t z : R)
    (hu : u*y=x) (hv : v*y=1) (hr : r*z=t) (hw : w*z=1) :
    s A u r v*y^2*z^2=BothFiniteTangent318.S A x y t z := by
  unfold s BothFiniteTangent318.S
  linear_combination (r*y*z^2+u*y*z^2+x*z^2)*hu+
    (r*y^2*z+t*y^2+x*y*z)*hr+(A*v*y*z^2+A*z^2)*hv

/-- The original regular infinity divided difference implies the complementary
finite divided difference, after the literal chart transition. -/
theorem tangent_line (A B u v r w x y t z a b : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (hu : u*y=x) (hv : v*y=1) (hr : r*z=t) (hw : w*z=1)
    (hline : v=a*u+b) (hslope : a*q A B r v w=s A u r v)
    (hq : IsUnit (q A B r v w)) :
    a*(y+z)+b*(x^2+x*t+t^2+A)=0 := by
  have hy : IsUnit y := IsUnit.of_mul_eq_one_right v hv
  have hz : IsUnit z := IsUnit.of_mul_eq_one_right w hw
  have hQ := scaled_q A B u v r w x y t z hu hv hr hw
  have hS := scaled_s A u v r w x y t z hu hv hr hw
  have hq' : IsUnit (BothFiniteTangent318.Q A B x y t z) := by
    rw [←hQ]
    exact (hq.mul (hy.pow 2)).mul (hz.pow 2)
  apply BothFiniteTangent318.tangent_line A B x y t z a b hF hG ?_ ?_ hy hq'
  · linear_combination -y*hline-a*hu+hv
  · rw [←hQ,←hS]
    linear_combination y^2*z^2*hslope

/-- Exact chart-transition compatibility with homogeneous chord/tangent addition.
Every premise records an original equation or literal coordinate transition. -/
theorem coordinates (A B u v r w x y t z a b U V D L : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (hu : u*y=x) (hv : v*y=1) (hr : r*z=t) (hw : w*z=1)
    (hline : v=a*u+b) (hline' : w=a*r+b)
    (hslope : a*q A B r v w=s A u r v) (hq : IsUnit (q A B r v w))
    (hU : c A B a*(U-u-r)=d A B a b) (hV : V=a*U-b)
    (hDL : a*D+b*L=0) :
    U*BothFiniteHomogeneous318.numeratorY x y t D L=
      BothFiniteHomogeneous318.numeratorX x t D L*D ∧
    V*BothFiniteHomogeneous318.numeratorY x y t D L=D^3 := by
  apply BothFiniteHomogeneous318.coordinates A B x y t z a b U V D L hF hG ?_ ?_
    (tangent_line A B u v r w x y t z a b hF hG hu hv hr hw hline hslope hq)
    hDL (IsUnit.of_mul_eq_one_right v hv) (IsUnit.of_mul_eq_one_right w hw) ?_ hV
  · linear_combination -y*hline-a*hu+hv
  · linear_combination -z*hline'-a*hr+hw
  · linear_combination y*z*hU+c A B a*z*hu+c A B a*y*hr

end BothFiniteTransition318
