module
public import Mathlib.Tactic
public section
namespace DyadicMixedOriginFirstChart318
variable {F : Type*} [Field F] [CharZero F]

theorem uniformizer_shift (u tau d C : F) :
    tau^2-2*((tau+u)+C-u*tau-((1-d)/2)*u^2) =
      (tau+u)^2-2*(tau+u)-d*u^2-2*C := by ring

theorem product_ratio (v z a b : F) (hv : v^2=2*a) (hz : z^2=2*b) :
    (v*z/2)^2=a*b := by
  rw [div_pow,mul_pow,hv,hz]; ring
end DyadicMixedOriginFirstChart318
