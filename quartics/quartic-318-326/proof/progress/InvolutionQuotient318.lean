module
public import ConjugateFormalQuotient318
public section
noncomputable section
namespace InvolutionQuotient318
set_option maxHeartbeats 0
open PowerSeries TameCoordinate318 TameLinearization318 ConjugateFormalQuotient318
variable {k:Type*} [Field k]

/-- A nonidentity actual formal involution has tangent minus one when two
is invertible; tangent faithfulness is proved by finite-order averaging. -/
theorem tangent_eq_neg_one (h2:(2:k)≠0) (F:k⟦X⟧)
    (hF:F.constantCoeff=0) (hperiod:F.subst F=X) (hne:F≠X) : coeff 1 F= -1 := by
  have hp:orbit F hF 2=X := by
    simpa only [show (2:ℕ)=0+1+1 from rfl,orbit_succ,orbit_zero,sigma_apply,
      subst_X (HasSubst.of_constantCoeff_zero' hF)] using hperiod
  have ht:coeff 1 F^2=1 := tangent_period F hF 2 hp
  have hm:(coeff 1 F-1)*(coeff 1 F+1)=0 := by linear_combination ht
  rcases mul_eq_zero.mp hm with h|h
  · exact (hne (finite_order_tangent_one F hF (sub_eq_zero.mp h) 2 h2 hp)).elim
  · exact eq_neg_of_add_eq_zero_left h

/-- A normalized parameter has exact order one. -/
theorem normalized_parameter_order (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (h1:coeff 1 H=1) : H.order=1 := by
  apply order_eq_nat.mpr
  refine ⟨by rw [h1];exact one_ne_zero,?_⟩
  intro i hi
  have hi0:i=0 := by omega
  subst i
  simpa only [coeff_zero_eq_constantCoeff] using hH

/-- The actual squared normalized parameter has ramification order two. -/
theorem squared_parameter_order (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (h1:coeff 1 H=1) : (H^2).order=2 := by
  rw [order_pow,normalized_parameter_order H hH h1]
  norm_num

/-- The derivative of the actual quotient parameter has order one, without
any separate different-exponent hypothesis. -/
theorem squared_parameter_derivative_order (h2:(2:k)≠0) (H:k⟦X⟧)
    (hH:H.constantCoeff=0) (h1:coeff 1 H=1) : (derivative (H^2)).order=1 := by
  have hd:(derivative H).order=0 := by
    apply order_eq_nat.mpr
    constructor
    · rw [coeff_zero_eq_constantCoeff,constant_derivative,h1];exact one_ne_zero
    · intro i hi;omega
  have hC:(C (2:k):k⟦X⟧).order=0 := by
    apply order_eq_nat.mpr
    constructor
    · simpa using h2
    · intro i hi;omega
  have he:derivative (H^2)=C (2:k)*H*derivative H := by
    rw [pow_two,Derivation.leibniz]
    simp only [map_ofNat]
    ring
  rw [he,order_mul,order_mul,hC,normalized_parameter_order H hH h1,hd]
  simp

/-- The invariant ring of an actual nontrivial formal involution is uniquely
k[[H²]], where H is constructed by finite-order averaging. The quotient
parameter and its derivative have their exact ramification orders. -/
theorem exists_normalized_quotient (h2:(2:k)≠0) (F:k⟦X⟧)
    (hF:F.constantCoeff=0) (hperiod:F.subst F=X) (hne:F≠X) :
    ∃H:k⟦X⟧,H.constantCoeff=0 ∧ coeff 1 H=1 ∧ H.subst F= -H ∧
      (H^2).order=2 ∧ (derivative (H^2)).order=1 ∧
      ∀f:k⟦X⟧,f.subst F=f ↔ ∃!g:k⟦X⟧,g.subst (H^2)=f := by
  have hp:orbit F hF 2=X := by
    simpa only [show (2:ℕ)=0+1+1 from rfl,orbit_succ,orbit_zero,sigma_apply,
      subst_X (HasSubst.of_constantCoeff_zero' hF)] using hperiod
  obtain ⟨H,hH,h1,he⟩:=exists_linearizing_parameter F hF 2 h2 hp
  have he':H.subst F= -H := by
    simpa only [tangent_eq_neg_one h2 F hF hperiod hne,neg_one_smul] using he
  refine ⟨H,hH,h1,he',squared_parameter_order H hH h1,
    squared_parameter_derivative_order h2 H hH h1,?_⟩
  intro f
  exact fixed_iff_unique_square_parameter h2 F H hF hH (by rw [h1];exact isUnit_one) he' f

end InvolutionQuotient318
