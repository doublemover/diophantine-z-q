module
public import InfinityInputPolynomial318
public section
noncomputable section
namespace InfinityInputChordIdentities318
open InfinityInputPolynomial318
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R]

/-- On the finite-coordinate overlap, invertibility of v and the actual output denominator
forces invertibility of the ordinary chord denominator. -/
theorem denominator_relation (A B u v x:R) (hv:v-u^3-A*u*v^2-B*v^3=0) :
    (x*v-u)*u^2= -v*denominator (1-A*u*v-B*v^2) u x := by
  unfold denominator
  linear_combination hv

/-- Literal denominator-cleared compatibility with the ordinary chord formula. -/
theorem x_identity (A B u v x y:R)
    (hf:y^2-x^3-A*x-B=0) (hg:v-u^3-A*u*v^2-B*v^3=0) :
    v*(x*v-u)^2*numeratorX A B (1-A*u*v-B*v^2) u x y=
      denominator (1-A*u*v-B*v^2) u x^2*
        (v*(y*v-1)^2-(u+x*v)*(x*v-u)^2) := by
  simp only [numeratorX,numeratorY,denominator]
  linear_combination (-A^2*u^2*v^5 - 2*A*B*u*v^6 - 2*A*u^3*v^4*x + 2*A*u*v^4 - B^2*v^7 - 2*B*u^2*v^5*x + 2*B*v^5 - u^4*v^3*x^2 + 2*u^2*v^3*x - v^3)*hf+(A^2*u*v^3*x + A*B*u*v^3 + A*B*v^4*x - 3*A*u^3*v*x + 6*A*u^2*v^2*x^2 - A*u*v^3*x^3 - 2*A*u*v^2*y + A*u*v - A*v^2*x + B^2*v^4 - 2*B*u^3*v + 2*B*u^2*v^2*x + 3*B*u*v^3*x^2 - B*v^4*x^3 - 2*B*v^3*y - u^4*x^2 + u^3*v*x^3 + u^2*v^2*x^4 + 2*u^2*x - 2*u*v^2*x^2*y - 3*u*v*x^2 + v^2*x^3 + 2*v*y - 1)*hg

/-- Literal denominator-cleared compatibility with the ordinary chord formula. -/
theorem y_identity (A B u v x y:R)
    (hf:y^2-x^3-A*x-B=0) (hg:v-u^3-A*u*v^2-B*v^3=0) :
    v*(x*v-u)*numeratorY A B (1-A*u*v-B*v^2) u x y=
      (y*v-1)*denominator (1-A*u*v-B*v^2) u x*
        (u*denominator (1-A*u*v-B*v^2) u x^2-v*numeratorX A B (1-A*u*v-B*v^2) u x y)-
      (x*v-u)*denominator (1-A*u*v-B*v^2) u x^3 := by
  simp only [numeratorX,numeratorY,denominator]
  linear_combination (-2*A^2*u^3*v^4 - 4*A*B*u^2*v^5 - 2*A*u^4*v^3*x + 4*A*u^2*v^3 - 2*B^2*u*v^6 - 2*B*u^3*v^4*x + 4*B*u*v^4 + 2*u^3*v^2*x - 2*u*v^2)*hf+(-2*A^2*u^3*v^2*y + A^2*u^2*v^3*x*y + 3*A^2*u^2*v^2*x - 3*A*B*u^2*v^3*y + 2*A*B*u^2*v^2 + 2*A*B*u*v^4*x*y + 3*A*B*u*v^3*x + A*u^4*v*x*y - 3*A*u^3*v^2*x^2*y - A*u^3*v*x^2 + 5*A*u^2*v^2*x^3 + 2*A*u^2*v*y - 3*A*u*v^2*x*y - 3*A*u*v*x - B^2*u*v^4*y + 2*B^2*u*v^3 + B^2*v^5*x*y + 3*B*u^4*v*y - B*u^3*v^2*x*y - 2*B*u^3*v*x - 3*B*u^2*v^3*x^2*y + 5*B*u*v^3*x^3 + B*u*v^2*y - 2*B*u*v - 3*B*v^3*x*y - u^4*v*x^3*y + u^3*v*x^4 + 3*u^2*v*x^2*y - 5*u*v*x^3 + 2*v*x*y)*hg

end InfinityInputChordIdentities318
