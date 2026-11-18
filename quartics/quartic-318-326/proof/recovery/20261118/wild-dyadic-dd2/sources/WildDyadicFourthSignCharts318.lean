module
public import Mathlib.Tactic
public section
namespace WildDyadicFourthSignCharts318
variable {F : Type*} [Field F] [CharZero F]

theorem ordinary_direction (v Q m Z a d c : F) :
    (v*Q)*a*d*v^2+(v*Q)^2*a*d*v+(v*Q)^3*c-(v*Q)^2*m*v*Z =
      v^2*(v*Q*(a*d+a*d*Q+c*Q^2-m*Q*Z)) := by ring

theorem exceptional_parities :
    ((4801:ℤ)*343^3-1)%4=2 ∧ ((4801:ℤ)*343^3+1)%8=0 := by
  norm_num

end WildDyadicFourthSignCharts318
