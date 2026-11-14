module
public import PELOriginalCentralSignTransport318
public section
noncomputable section
namespace PELOriginalEvenTensorCocycle318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalFlatPeriodKernel318 PELOriginalUnitFlatTransport318
open PELOriginalFlatPeriodSquare318 PELOriginalKernelMonodromyCovariance318
open PELOriginalCentralSignTransport318
open scoped TensorProduct

lemma parameter_mul (u v : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : parameter u (parameter v τ)=parameter (u*v) τ :=
  QuaternionicPeriodAutomorphy318.unit_parameter_comp representation order u.val v.val
    u.property v.property τ hτ

lemma coefficient_cocycle (u v : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (z : ComplexVectors) :
    coefficientEquiv v τ hτ (coefficientEquiv u (parameter v τ)
      (parameter_positive v τ hτ) z)=coefficientEquiv (u*v) τ hτ z := by
  have hk := (kernel_transport u (parameter v τ) (parameter_positive v τ hτ)
    (kernelLift (parameter u (parameter v τ)) z)).mpr (kernelLift_period _ z)
  change (transport v.val (kernelLift (parameter v τ)
    (transport u.val (kernelLift (parameter u (parameter v τ)) z)).2)).2=
      (transport (u*v).val (kernelLift (parameter (u*v) τ) z)).2
  rw [kernel_recover _ _ hk,transport_mul,parameter_mul u v τ hτ]
  rfl
lemma coefficient_one (τ : ℂ) (hτ : 0<τ.im) (z : ComplexVectors) :
    coefficientEquiv 1 τ hτ z=z := by
  change (transport (1:orderˣ) (kernelLift (parameter 1 τ) z)).2=z
  rw [transport_one]
  rfl

/-- Full ordered cocycle on the entire tensor square, with the actual
changed base point in the first transition. -/
theorem tensor_cocycle (u v : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : ComplexVectors ⊗[ℂ] ComplexVectors) :
    tensorTransition v τ hτ (tensorTransition u (parameter v τ)
      (parameter_positive v τ hτ) x)=tensorTransition (u*v) τ hτ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
      change coefficientEquiv v τ hτ (coefficientEquiv u _ _ z) ⊗ₜ[ℂ]
        coefficientEquiv v τ hτ (coefficientEquiv u _ _ w)=
        coefficientEquiv (u*v) τ hτ z ⊗ₜ[ℂ] coefficientEquiv (u*v) τ hτ w
      rw [coefficient_cocycle,coefficient_cocycle]
  | add x y hx hy => simp only [map_add,hx,hy]
lemma tensor_one (τ : ℂ) (hτ : 0<τ.im) (x : ComplexVectors ⊗[ℂ] ComplexVectors) :
    tensorTransition 1 τ hτ x=x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
      change coefficientEquiv 1 τ hτ z ⊗ₜ[ℂ] coefficientEquiv 1 τ hτ w=z ⊗ₜ[ℂ] w
      rw [coefficient_one,coefficient_one]
  | add x y hx hy => simp only [map_add,hx,hy]
end PELOriginalEvenTensorCocycle318
