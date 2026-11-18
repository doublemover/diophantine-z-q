module
public import Mathlib.Tactic
public section
namespace WildUnramifiedOpposingOdd318
variable {F : Type*} [Field F]
theorem shift_square (s v k : F) : (v+s+k)^2 = v^2+2*(s+k)*v+(s+k)^2 := by ring
end WildUnramifiedOpposingOdd318
