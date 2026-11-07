module
public import QuadraticFormalBasis318
public import InvolutionQuotient318
public section
noncomputable section
namespace NormalizedQuadraticModel318
set_option maxHeartbeats 0
open PowerSeries ConjugateFormalQuotient318 EvenOddSeries318
variable {k:Type*} [Field k]

/-- Actual algebra automorphism associated to an invertible formal parameter. -/
@[expose] def parameterEquiv (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) : k⟦X⟧≃ₐ[k]k⟦X⟧ :=
  AlgEquiv.ofBijective (substAlgHom (HasSubst.of_constantCoeff_zero' hH)) ⟨by
    simpa only [coe_substAlgHom] using parameter_subst_injective H hH hu,by
    intro f
    refine ⟨f.subst (H.substInvOfIsUnit hu),?_⟩
    simpa only [coe_substAlgHom] using inverse_parameter_cancel H hH hu f⟩

@[expose] def quadraticModel (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) : QuadraticAlgebra k⟦X⟧ X 0 ≃+* k⟦X⟧ :=
  quadraticEquiv.trans (parameterEquiv H hH hu).toRingEquiv

theorem model_apply (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) (z:QuadraticAlgebra k⟦X⟧ X 0) :
    quadraticModel H hH hu z=z.re.subst (H^2)+H*z.im.subst (H^2) := by
  change (substAlgHom (HasSubst.of_constantCoeff_zero' hH)) (expandTwo z.re+X*expandTwo z.im)=_
  rw [coe_substAlgHom]
  rw [subst_add (HasSubst.of_constantCoeff_zero' hH),subst_mul (HasSubst.of_constantCoeff_zero' hH),
    subst_X (HasSubst.of_constantCoeff_zero' hH)]
  rw [expandTwo,expand_subst_parameter H hH,expand_subst_parameter H hH]

/-- The concrete model sends the actual quadratic generator to H. -/
theorem model_generator (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) :
    quadraticModel H hH hu QuadraticAlgebra.omega=H := by
  rw [model_apply]
  have hs:HasSubst (H^2):=HasSubst.of_constantCoeff_zero' (by simp [hH])
  simp only [QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega,←coe_substAlgHom hs,map_zero,map_one,mul_one,zero_add]

/-- The actual invariant base ring is embedded by composition with H squared. -/
theorem model_base (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) (f:k⟦X⟧) :
    quadraticModel H hH hu (algebraMap k⟦X⟧ (QuadraticAlgebra k⟦X⟧ X 0) f)=f.subst (H^2) := by
  rw [model_apply]
  have hs:HasSubst (H^2):=HasSubst.of_constantCoeff_zero' (by simp [hH])
  simp only [←coe_substAlgHom hs]
  simp

end NormalizedQuadraticModel318
