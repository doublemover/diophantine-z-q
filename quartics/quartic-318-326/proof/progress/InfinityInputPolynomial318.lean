module
public import HomogeneousAddition318
public section
noncomputable section
namespace InfinityInputPolynomial318
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R]

@[expose] def denominator (k u x:R) := k-x*u^2
@[expose] def numeratorX (A B k u x y:R) :=
  x*k^2-2*k*y*u+(x^2+A)*k*u^2+(A*x+2*B)*u^4
@[expose] def numeratorY (A B k u x y:R) :=
  y*k^2-(3*x^2+A)*k^2*u+3*x*y*k^2*u^2-(x^3+3*A*x+4*B)*k*u^3+
    2*A*y*k*u^4+y*(A*x+3*B)*u^6

/-- The infinity chart supplies the actual polynomial relation for its regular parameter. -/
theorem parameter_relation (A B u v:R) (hv:v-u^3-A*u*v^2-B*v^3=0) :
    let k:=1-A*u*v-B*v^2
    k^2*(1-k)-A*u^4*k-B*u^6=0 := by
  let k:=1-A*u*v-B*v^2
  have hk:k*v=u^3 := by dsimp [k]; linear_combination hv
  change k^2*(1-k)-A*u^4*k-B*u^6=0
  calc
    _=A*u*k*(k*v-u^3)+B*(k*v+u^3)*(k*v-u^3) := by dsimp [k]; ring
    _=0 := by rw [hk,sub_self]; ring

/-- A universal denominator-cleared addition identity, proved by the kernel from the two
actual curve relations. The generated coefficient certificate is checked by ring arithmetic. -/
theorem output_equation (A B k u x y:R)
    (hf:y^2-x^3-A*x-B=0) (hg:k^2*(1-k)-A*u^4*k-B*u^6=0) :
    numeratorY A B k u x y^2-numeratorX A B k u x y^3-
      A*numeratorX A B k u x y*denominator k u x^4-B*denominator k u x^6=0 := by
  unfold numeratorY numeratorX denominator
  linear_combination (4*A^2*k^2*u^8 + 4*A^2*k*u^10*x + A^2*u^12*x^2 + 12*A*B*k*u^10 + 6*A*B*u^12*x + 12*A*k^3*u^6*x - 8*A*k^3*u^4 + 6*A*k^2*u^8*x^2 - 10*A*k^2*u^6*x + 9*B^2*u^12 + 18*B*k^2*u^8*x - 18*B*k^2*u^6 + 9*k^4*u^4*x^2 - 6*k^4*u^2*x + k^4 - 12*k^3*u^4*x^2 + 8*k^3*u^3*y)*hf+(A^2*k^2*u^2 - A^2*k*u^4*x - A^2*u^6*x^2 + A*B*k*u^4 - 3*A*B*u^6*x + A*k^3*x - 2*A*k^2*u*y + A*k^2*x + A*k*u^4*x^3 + 2*A*k*u^3*x*y - 4*A*u^6*x^4 - B^2*u^6 + B*k^3 - 6*B*k^2*u^2*x + B*k^2 + 12*B*k*u^4*x^2 - 9*B*u^6*x^3 + k^3*x^3 + 3*k^2*u^2*x^4 - 6*k^2*u*x^2*y + k^2*x^3 - 6*k*u^4*x^5 + 6*k*u^3*x^3*y + u^6*x^6)*hg

/-- Exact values along the actual infinity section. -/
theorem at_infinity (A B x y:R) : denominator 1 0 x=1 ∧
    numeratorX A B 1 0 x y=x ∧ numeratorY A B 1 0 x y=y := by
  simp [denominator,numeratorX,numeratorY]

end InfinityInputPolynomial318
