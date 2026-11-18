module
public import Mathlib.Tactic
public section
namespace WildDyadicCoefficientShift318
variable {F : Type*} [Field F] [CharZero F]

theorem unit_shift (U V s A B l m : F) :
    (s*V+A*U+B)^2-(l*U^2+m) =
     s^2*V^2+2*s*(A*U+B)*V+(A^2-l)*U^2+2*A*B*U+(B^2-m) := by ring

theorem cyclotomic_uniformizer (P : F) :
    (1-P)^4+1=P^4-4*P^3+6*P^2-4*P+2 := by ring
end WildDyadicCoefficientShift318
