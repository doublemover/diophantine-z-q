module
public import Pade21Accuracy
public import Mathlib.RingTheory.Valuation.Basic
public section
namespace Pade21LocalError
open Pade21Domains Pade21Accuracy
variable {K : Type*} [Field K] [CharZero K]

theorem G_error_valuation (v : AddValuation K (WithTop ℤ)) (x : K)
    (hQ : v (QG x)=0) (hC : v (-98/2535 : K)=0) :
    v (PG x/QG x-G3 x)=4 • v x := by
  have hq : QG x≠0 := (v.ne_top_iff).mp (by rw [hQ]; simp)
  have he : PG x/QG x-G3 x=((-98/2535)*x^4)/QG x := by
    apply (eq_div_iff hq).mpr
    calc
      (PG x/QG x-G3 x)*QG x=PG x-QG x*G3 x := by field_simp
      _=(-98/2535)*x^4 := G_error x
  rw [he,v.map_div,v.map_mul,v.map_pow,hC,hQ]
  simp

theorem J_error_valuation (v : AddValuation K (WithTop ℤ)) (x : K)
    (hQ : v (QJ x)=0) (hC : v (5/507 : K)=0) :
    v (PJ x/QJ x-J3 x)=4 • v x := by
  have hq : QJ x≠0 := (v.ne_top_iff).mp (by rw [hQ]; simp)
  have he : PJ x/QJ x-J3 x=((5/507)*x^4)/QJ x := by
    apply (eq_div_iff hq).mpr
    calc
      (PJ x/QJ x-J3 x)*QJ x=PJ x-QJ x*J3 x := by field_simp
      _=(5/507)*x^4 := J_error x
  rw [he,v.map_div,v.map_mul,v.map_pow,hC,hQ]
  simp
end Pade21LocalError
