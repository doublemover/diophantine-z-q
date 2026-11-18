module
public import Mathlib.Tactic
public section
namespace WildMixedParityCloseNorm318
variable {F : Type*} [Field F]
theorem norm_completion (s K : F) :
 (s+2*K)^2-(s^2+4*K*(1+s))=4*K*(K-1) := by ring
end WildMixedParityCloseNorm318
