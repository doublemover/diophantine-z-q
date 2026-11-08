module
public import BothFiniteLine318
public section
namespace BothFiniteTangent318
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]

@[expose] def Q (A B x y t z : R) :=
  y^2*z^2-A*t*y*(z+y)-B*(z^2+y*z+y^2)
@[expose] def S (A x y t z : R) :=
  x^2*z^2+x*t*y*z+t^2*y^2+A*z^2
@[expose] def L (A x t : R) := x^2+x*t+t^2+A

/-- The infinity-chart divided difference determines the finite tangent line,
including the equal-input and nilpotent directions. -/
lemma tangent_certificate (A B x y t z : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0) :
    S A x y t z*((y+z)*y-x*L A x t)+L A x t*Q A B x y t z=0 := by
  unfold S L Q
  linear_combination
    (-A^2*t-A*B-A*t^3-A*t^2*x-A*t*x^2+2*A*z^2-B*t*x-B*x^2-
      t^4*x-t^3*x^2+t^2*y^2+t^2*y*z+t^2*z^2+t*x*y*z+2*t*x*z^2+2*x^2*z^2)*hF+
    (A^2*x+A*B+A*t*x^2+2*A*x^3+A*y*z+B*t*x+B*x^2+t*x^4+x^5+x^2*y*z)*hG

theorem tangent_line (A B x y t z a b : R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0)
    (hline : a*x+b*y=1) (hslope : a*Q A B x y t z=S A x y t z)
    (hy : IsUnit y) (hq : IsUnit (Q A B x y t z)) :
    a*(y+z)+b*L A x t=0 := by
  apply (hq.mul hy).mul_right_cancel
  have hp := tangent_certificate A B x y t z hF hG
  linear_combination hp+((y+z)*y-x*L A x t)*hslope+L A x t*Q A B x y t z*hline

end BothFiniteTangent318
