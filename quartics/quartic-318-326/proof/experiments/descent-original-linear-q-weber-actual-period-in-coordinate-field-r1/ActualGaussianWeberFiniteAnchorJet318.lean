module
public import ActualGaussianWeberMixedValuedData318
import all ActualGaussianWeberMixedPolynomial318
public section
noncomputable section

namespace ActualGaussianWeberFiniteAnchorJet318
open IsLocalRing ActualGaussianWeberMixedPolynomial318 ActualGaussianWeberMixedValuedData318

variable {F : Type*} [Field F] (V : ValuationSubring F)

/-- Scale the *finite ordinate* by the fixed actual parameter t.
When the old finite abscissa is 0 in the residue, the new coefficient
drops by one. No operation is carried out by dividing in the residue. -/
theorem ordinate_coefficient {t w A d : V}
    (K : IntegralData V t w A (t*d)) (ht : t∈maximalIdeal V) (hA : residue V A=0) :
    ∃ e : V, K.Y=t*e ∧ residue V e=residue V d-1 := by
  let B : V := t*d
  let C : V := 2*d+(3*A^2-1)-(A^3+A)*(t^2*K.u)
  let e : V := -d+(1+B*w)*K.u*K.beta^3*C
  have hC : H t w A B=t*C := by
    unfold H B C
    linear_combination -(A^3+A)*K.w_relation
  refine ⟨e,?_,?_⟩
  · rw [K.y_formula,hC]
    dsimp only [e,B]
    ring
  · have ht0 := (residue_eq_zero_iff t).mpr ht
    simp [e,B,C,hA,ht0,K.u_res,K.beta_res,map_ofNat] <;> ring

end ActualGaussianWeberFiniteAnchorJet318
