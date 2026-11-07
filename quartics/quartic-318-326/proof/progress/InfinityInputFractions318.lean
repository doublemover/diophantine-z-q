module
public import InfinityInputChordIdentities318
public section
noncomputable section
namespace InfinityInputFractions318
set_option maxHeartbeats 500000
variable {R:Type*} [CommRing R]

/-- Unit-only conversion of the two literal polynomial identities to the ordinary chord
output. There is no field or reducedness assumption. -/
theorem chord_coordinates (u v x e d h nx ny vi hi l:R)
    (hv:v*vi=1) (hh:h*hi=1) (hd:IsUnit d) (hl:l*d=e)
    (hX:v*d^2*nx=h^2*(v*e^2-(u+x*v)*d^2))
    (hY:v*d*ny=e*h*(u*h^2-v*nx)-d*h^3) :
    nx*hi^2=l^2-u*vi-x ∧ ny*hi^3=l*(u*vi-nx*hi^2)-vi := by
  have vu:IsUnit v:=IsUnit.of_mul_eq_one _ hv
  have hu:IsUnit h:=IsUnit.of_mul_eq_one _ hh
  constructor
  · apply (vu.mul (hd.pow 2)).mul_right_cancel
    calc
      _=(v*d^2*nx)*hi^2 := by ring
      _=(v*e^2-(u+x*v)*d^2)*(h*hi)^2 := by rw [hX]; ring
      _=v*(l*d)^2-(u+x*v)*d^2 := by rw [hh,←hl]; ring
      _=(l^2-u*vi-x)*(v*d^2) := by linear_combination (u*d^2)*hv
  · apply ((vu.mul hd).mul (hu.pow 3)).mul_right_cancel
    calc
      _=(v*d*ny)*(h*hi)^3 := by ring
      _=e*h*(u*h^2-v*nx)-d*h^3 := by rw [hh]; simpa using hY
      _=(l*d)*(u*(v*vi)*h^3-v*nx*h*(h*hi)^2)-d*h^3*(v*vi) := by rw [hl,hv,hh]; ring
      _=(l*(u*vi-nx*hi^2)-vi)*(v*d*h^3) := by ring

/-- The infinity-to-finite input intersection lies in the ordinary chord open automatically. -/
theorem chord_denominator_unit (A B u v x:R) (hg:v-u^3-A*u*v^2-B*v^3=0)
    (hv:IsUnit v) (hh:IsUnit (InfinityInputPolynomial318.denominator (1-A*u*v-B*v^2) u x)) :
    IsUnit (x*v-u) := by
  have he:=InfinityInputChordIdentities318.denominator_relation A B u v x hg
  have hu : IsUnit ((x*v-u)*u^2) := by
    rw [he]
    simpa only [neg_mul] using (hv.mul hh).neg
  exact (IsUnit.mul_iff.mp hu).1

end InfinityInputFractions318
