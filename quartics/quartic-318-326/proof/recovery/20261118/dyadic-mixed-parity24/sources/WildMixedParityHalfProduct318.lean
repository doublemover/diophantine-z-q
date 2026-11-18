module
public import Mathlib.Tactic
public section
namespace WildMixedParityHalfProduct318
variable {F : Type*} [Field F]
theorem product_expansion (u w b : F) :
   (2*b+u*w)^2=4*(b^2+u*w*b)+(u*w)^2 := by ring
end WildMixedParityHalfProduct318
