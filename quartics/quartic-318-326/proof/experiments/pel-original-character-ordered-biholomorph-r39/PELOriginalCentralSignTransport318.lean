module
public import PELOriginalKernelMonodromyCovariance318
public import PELEffectiveNormOneAction318
public import Mathlib.LinearAlgebra.TensorProduct.Map
public section
noncomputable section
namespace PELOriginalCentralSignTransport318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318 PELOriginalFlatPeriodKernel318
open PELOriginalComplexifiedOrder318 PELOriginalUnitFlatTransport318
open PELOriginalFlatPeriodSquare318 PELOriginalKernelMonodromyCovariance318
open QuaternionicUnitPeriodTransport318 QuaternionicMobiusPeriods318
open scoped TensorProduct

lemma unitMatrixC_neg (u : orderˣ) : unitMatrixC (-u)= -unitMatrixC u := by
  ext i j
  simp [unitMatrixC,unitMatrix]
lemma transport_neg (u : orderˣ) (p : Ambient) : transport (-u) p= -transport u p := by
  apply splitEquiv.injective
  change split (transport (-u) p)=split (-transport u p)
  rw [show split (-transport u p)= -split (transport u p) from splitEquiv.map_neg _,
    split_transport,split_transport,unitMatrixC_neg,Matrix.mul_neg]
lemma transport_one (p : Ambient) : transport (1:orderˣ) p=p := by
  apply splitEquiv.injective
  change split (transport 1 p)=split p
  rw [split_transport]
  simp [unitMatrixC,unitMatrix]
lemma transport_negative_one (p : Ambient) : transport (-1:orderˣ) p= -p := by
  rw [transport_neg,transport_one]

lemma parameter_neg (u : orderˣ) (τ : ℂ) :
    unitParameter representation order (-u) τ=unitParameter representation order u τ := by
  have hm : unitMatrix representation order (-u)= -unitMatrix representation order u := by
    simp [unitMatrix]
  simp only [unitParameter,mobius,denominator,hm,Matrix.neg_apply,Complex.ofReal_neg]
  rw [neg_mul,neg_mul,←neg_add,←neg_add,neg_div_neg_eq]

/-- The central sign does NOT act trivially on the rank-two kernel plane.
Thus it cannot silently be descended as an unchanged vector bundle over
the effective coarse base; the even tensor below is the genuine invariant. -/
lemma coefficient_neg (u v : PELJointNormOneAction318.normOneUnits)
    (hu : u.val= -v.val) (τ : ℂ) (hτ : 0<τ.im) (z : ComplexVectors) :
    coefficientEquiv u τ hτ z= -coefficientEquiv v τ hτ z := by
  change (transport u.val (kernelLift (parameter u τ) z)).2=
    -(transport v.val (kernelLift (parameter v τ) z)).2
  have hp : parameter u τ=parameter v τ := by
    change unitParameter representation order u.val τ=unitParameter representation order v.val τ
    rw [hu,parameter_neg]
  rw [hp,hu,transport_neg]
  rfl

@[expose] def tensorTransition (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    (ComplexVectors ⊗[ℂ] ComplexVectors) ≃ₗ[ℂ] (ComplexVectors ⊗[ℂ] ComplexVectors) :=
  TensorProduct.congr (coefficientEquiv u τ hτ) (coefficientEquiv u τ hτ)

/-- The actual WHOLE tensor-square transition is unchanged by the central
sign, not only its values on a basis or its determinant. -/
theorem tensorTransition_neg (u v : PELJointNormOneAction318.normOneUnits)
    (hu : u.val= -v.val) (τ : ℂ) (hτ : 0<τ.im) :
    tensorTransition u τ hτ=tensorTransition v τ hτ := by
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
      change coefficientEquiv u τ hτ z ⊗ₜ[ℂ] coefficientEquiv u τ hτ w=
        coefficientEquiv v τ hτ z ⊗ₜ[ℂ] coefficientEquiv v τ hτ w
      rw [coefficient_neg u v hu τ hτ z,coefficient_neg u v hu τ hτ w,
        TensorProduct.neg_tmul,TensorProduct.tmul_neg,neg_neg]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Equality of actual effective original base actions gives exactly the
same full tensor-square transition. This uses the produced ±1 kernel. -/
theorem tensorTransition_effective (u v : PELJointNormOneAction318.normOneUnits)
    (h : PELEffectiveNormOneAction318.effectiveMap u=PELEffectiveNormOneAction318.effectiveMap v)
    (τ : ℂ) (hτ : 0<τ.im) : tensorTransition u τ hτ=tensorTransition v τ hτ := by
  have hk : PELEffectiveNormOneAction318.effectiveMap (u*v⁻¹)=1 := by
    rw [map_mul,map_inv,h,mul_inv_cancel]
  rcases (PELEffectiveNormOneAction318.effectiveMap_eq_one_iff (u*v⁻¹)).mp hk with hp|hn
  · have huv : u.val=v.val := by
      have hv := congrArg (fun x : orderˣ => x*v.val) hp
      simpa [mul_assoc] using hv
    have he : u=v := Subtype.ext huv
    subst u
    rfl
  · have huv : u.val= -v.val := by
      have hv := congrArg (fun x : orderˣ => x*v.val) hn
      simpa [mul_assoc] using hv
    exact tensorTransition_neg u v huv τ hτ
end PELOriginalCentralSignTransport318
