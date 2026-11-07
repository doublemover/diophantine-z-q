module
public import InfinityAdditionAlgebra318
public section
noncomputable section
namespace HomogeneousCross318
set_option maxHeartbeats 500000
variable {R:Type*} [CommRing R]

/-- Homogeneous cubic coordinates for two proportional slope pairs agree by polynomial identities;
no slope denominator is cancelled. -/
theorem cross_coordinates (x y z d e D E:R) (h:e*D-E*d=0) :
    let U:=e^2-(x+z)*d^2
    let V:=e*(x*d^2-U)-y*d^3
    let U':=E^2-(x+z)*D^2
    let V':=E*(x*D^2-U')-y*D^3
    U*d*V'=U'*D*V ∧ d^3*V'=D^3*V := by
  dsimp only
  constructor
  · linear_combination
      (2*D^2*d^2*x^2+3*D^2*d^2*x*z+D^2*d^2*z^2-D^2*d*e*y-D^2*e^2*x-
        D^2*e^2*z-D*E*d^2*y+D*E*d*e*x-E^2*d^2*x-E^2*d^2*z+E^2*e^2)*h
  · linear_combination (-2*D^2*d^2*x-D^2*d^2*z+D^2*e^2+D*E*d*e+E^2*d^2)*h

/-- Unit-denominator cancellation, valid over arbitrary commutative rings. -/
theorem inverse_cross (a b v w k l:R) (hv:v*k=1) (hw:w*l=1) (h:a*w=b*v) : a*k=b*l := by
  linear_combination (k*l)*h-(a*k)*hw+(b*l)*hv

/-- The actual two slope pairs satisfy the required projective proportionality. -/
theorem actual_cross (A B:R) :
    InfinityAdditionAlgebra318.slopeNumerator A B false*InfinityAdditionAlgebra318.denominator A B true-
      InfinityAdditionAlgebra318.slopeNumerator A B true*InfinityAdditionAlgebra318.denominator A B false=0 := by
  have h1:=InfinityAdditionAlgebra318.first_equation A B
  have h2:=InfinityAdditionAlgebra318.second_equation A B
  simp only [InfinityAdditionAlgebra318.slopeNumerator,InfinityAdditionAlgebra318.denominator,
    Bool.false_eq_true,ite_false,ite_true]
  linear_combination h2-h1

end HomogeneousCross318
