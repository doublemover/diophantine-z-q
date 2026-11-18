module
public import Mathlib.Tactic
public section
namespace WildDyadicMixedTwoTerminal318
variable {F : Type*} [Field F] [CharZero F]
theorem t_direction (t P W delta : F) :
   (t*W)^2+(t*P)*(1+t)*(t*W)+(t*P)*t^2+(t*P)^2*t+(t*P)^2*delta =
    t^2*(W^2+P*(1+t)*W+t*P+t*P^2+delta*P^2) := by ring
theorem constant_orders : ((32-76832)/16:ℚ) = -75*2^6 ∧
    ((0-32)/4:ℚ) = -2^3 := by norm_num
end WildDyadicMixedTwoTerminal318
