module
public import Mathlib.Tactic
public section
namespace WildQuarterParameterCorner318
variable {F : Type*} [Field F]
theorem translated_product (u t p a b d : F) :
 (u-d*(a^2*t+2*a*b*p^2))*t=u*t-d*(a*t+b*p^2)^2+d*b^2*p^4 := by ring
end WildQuarterParameterCorner318
