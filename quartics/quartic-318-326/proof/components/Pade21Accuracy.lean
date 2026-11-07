module
public import Pade21Domains
public section
namespace Pade21Accuracy
open ConcreteG8Domain Pade21Domains
variable {F : Type*} [Field F] [CharZero F]

@[expose] def G3 (x : F) : F := 1-(2/5)*x-(2/15)*x^2-(14/195)*x^3
@[expose] def J3 (x : F) : F := 1-x/5+x^2/15-x^3/39

theorem G_error (x : F) : PG x-QG x*G3 x=(-98/2535)*x^4 := by
  unfold PG QG G3
  norm_num
  ring

theorem J_error (x : F) : PJ x-QJ x*J3 x=(5/507)*x^4 := by
  unfold PJ QJ J3
  norm_num
  ring

theorem actual_G_denominator (f : K) : QG (D*f^2) ≠ 0 := by
  have h : D*f^2=((3-i)*f)^2 := by unfold D; ring
  rw [h]
  exact QG_nonzero_on_square _

theorem actual_J_denominator (u v : K) (hc : v^2+D*u^4=1) :
    QJ (v-1) ≠ 0 := by
  apply QJ_nonzero_on_circle v ((3-i)*u^2)
  convert hc using 1 <;> unfold D <;> ring

theorem actual_J_log_zero_iff (u v : K) (hc : v^2+D*u^4=1) :
    -u*(PJ (v-1)/QJ (v-1))=0 ↔ u=0 := by
  have hn := div_ne_zero (PJ_nonzero (v-1)) (actual_J_denominator u v hc)
  simp only [mul_eq_zero,neg_eq_zero,hn,or_false]
end Pade21Accuracy
