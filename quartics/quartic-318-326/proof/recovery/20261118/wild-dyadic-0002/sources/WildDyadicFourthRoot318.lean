module
public import Mathlib.Tactic
public section
namespace WildDyadicFourthRoot318
variable {F : Type*} [Field F] [CharZero F]

theorem two_chart (Y V : F)
    (h : (2*Y)^2 = 2*((2*V)^2+2*(2*V)+344)) :
    Y^2 = 2*(V^2+V+86) := by
  linear_combination (1/4:F)*h

theorem other_chart (v Q : F) (hv : v*Q=2) :
    2*(v^2+2*v+344) = v^2*(v*Q*(1+Q+43*v*Q^3)) := by
  calc
    2*(v^2+2*v+344) = (v*Q)*(v^2+(v*Q)*v+43*(v*Q)^3) := by rw [hv]; ring
    _ = _ := by ring

theorem valuation_constant :
    (4801:ℤ)*343^3 - 1 = 2*96868833603 := by norm_num

theorem crossing_scale (H z E V a b g : F) :
    H*z^4*(a*(z*E)+b*(z*V)+g*z)^6 =
      z^2*(H*z^8*(a*E+b*V+g)^6) := by ring

end WildDyadicFourthRoot318
