module
public import Mathlib.Tactic
public section
namespace WildDyadicScaleBasepoint318
variable {F : Type*} [Field F] [CharZero F]

theorem true_u_chart (u Q a d j c Y : F) :
    (u*Q)*a*d*u^2+(u*Q)^3*j-(u*Q)^2*c*u*Y =
      u^2*(u*Q*(a*d+j*Q^2-c*Q*Y)) := by ring

theorem shifted_coefficient (c y f m z : F) :
    c+4801*(y*(m+z)+f*(m+z)^2) =
      (c+4801*(y*m+f*m^2))+4801*(y+2*f*m)*z+4801*f*z^2 := by ring

theorem exact_cancellation (c y d s : F) :
    c+4801*(y+(171-y+d*y^4*s^2)) =
       c+4801*171+4801*d*y^4*s^2 := by ring
end WildDyadicScaleBasepoint318
