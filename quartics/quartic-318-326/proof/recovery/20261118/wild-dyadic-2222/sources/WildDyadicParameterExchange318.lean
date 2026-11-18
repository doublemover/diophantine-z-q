module
public import Mathlib.Tactic
public section
namespace WildDyadicParameterExchange318
variable {F : Type*} [Field F] [CharZero F]

theorem cleared_exchange (T b : F) :
    375*T*(343+b)-375*b*(T+343) = (375*343)*(T-b) := by ring

theorem corrected_split (j k g : F) :
    (j-k+1)*(j-k+1+(2*k-1)+g)+k*(k-1) =
       j^2+(1+g)*j-(k-1)*g := by ring

theorem contacts : (375:ℚ)*76832/(343+76832)=1120/3 ∧
    (1120/3:ℚ)/32=35/3 := by norm_num
end WildDyadicParameterExchange318
