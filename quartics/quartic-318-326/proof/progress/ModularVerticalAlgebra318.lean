module
public import Mathlib.Tactic
public section
namespace ModularVerticalAlgebra318
variable {K : Type*} [Field K] [CharZero K]

@[expose] def A (j : K) : K := -3*j/(j-1728)
@[expose] def B (j : K) : K := -2*j/(j-1728)

theorem discriminant_core (j : K) (hj : j≠1728) :
    4*(A j)^3+27*(B j)^2=-108*1728*j^2/(j-1728)^3 := by
  have hd : j-1728≠0 := sub_ne_zero.mpr hj
  unfold A B
  field_simp
  ring

theorem discriminant_core_ne_zero (j : K) (h0 : j≠0) (hj : j≠1728) :
    4*(A j)^3+27*(B j)^2≠0 := by
  rw [discriminant_core j hj]
  exact div_ne_zero (by simpa using h0) (pow_ne_zero 3 (sub_ne_zero.mpr hj))

theorem exact_j_invariant (j : K) (h0 : j≠0) (hj : j≠1728) :
    1728*(4*(A j)^3)/(4*(A j)^3+27*(B j)^2)=j := by
  rw [discriminant_core j hj]
  unfold A
  have hd : j-1728≠0 := sub_ne_zero.mpr hj
  field_simp
  ring

end ModularVerticalAlgebra318
#print axioms ModularVerticalAlgebra318.discriminant_core
#print axioms ModularVerticalAlgebra318.discriminant_core_ne_zero
#print axioms ModularVerticalAlgebra318.exact_j_invariant
