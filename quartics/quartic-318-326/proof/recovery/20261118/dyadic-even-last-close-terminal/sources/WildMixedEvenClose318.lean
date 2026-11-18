module
public import Mathlib.Tactic
public section
namespace WildMixedEvenClose318
variable {F : Type*} [Field F]
theorem contact_norm (R S A K : F) :
    R^2+(S+2*K*A)^2-4*K*(K-1)*A^2=R^2+S^2+4*K*(A^2+S*A) := by ring
theorem scale_contact (p k g : F) :
    (p^2*k)*(p^2*k+p^2*g)=p^4*(k*(k+g)) := by ring
end WildMixedEvenClose318
