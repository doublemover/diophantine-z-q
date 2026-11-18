module
public import Mathlib.Tactic
public section
namespace WildDyadicSignCluster318
variable {F : Type*} [Field F] [CharZero F]

/-- Direct coordinates for the Gaussian ramified sign pattern (−,−,−,+). -/
theorem finite_equations (u a b c : F) (ha : a^2=u^2+32)
    (hb : b^2=u^2+76832) (hc : c^2=343-u^2) :
    ((a-u)/2)^2 + u*((a-u)/2)=8 ∧
    ((b-u)/2)^2 + u*((b-u)/2)=19208 ∧
    (c-u-1)^2+2*((1+u)*(c-u-1)+u^2+u-171)=0 := by
  constructor
  · linear_combination (1/4:F)*ha
  constructor
  · linear_combination (1/4:F)*hb
  · linear_combination hc

theorem reciprocal_equation (x c : F) (hc : c^2 = -1+343*x^2) :
    (c-1-x)^2+2*((1+x)*(c-1-x)+1+x-171*x^2)=0 := by
  linear_combination hc

theorem split_product (d t : F) (hd : d^2+t*d-2400*(t-1)=0) :
    (d-2400)*(d-2400+t+4800) = -2400*2401 := by
  linear_combination hd

end WildDyadicSignCluster318
