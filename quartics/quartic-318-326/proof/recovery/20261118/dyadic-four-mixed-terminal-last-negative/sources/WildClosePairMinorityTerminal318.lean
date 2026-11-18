module
public import Mathlib.Tactic
public section
namespace WildClosePairMinorityTerminal318
variable {F : Type*} [Field F] [CharZero F]
theorem exact_inner_conic (R h : F) :
    -R^2-h^2*(1+2*R)=h^2*(h^2-1)-(R+h^2)^2 := by ring
theorem exact_final_shift (D s x K : F) :
    (D+s)^2+x*K*s*(D+s)+K*s^2 =
       D^2+(2+x*K)*s*D+(1+K+x*K)*s^2 := by ring
theorem contact_order : (49:ℤ)^2-1=75*2^5 := by norm_num
end WildClosePairMinorityTerminal318
