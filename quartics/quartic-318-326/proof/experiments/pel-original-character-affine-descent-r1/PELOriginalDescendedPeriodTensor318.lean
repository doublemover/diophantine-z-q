module
public import PELOriginalEffectiveTensorDescent318
public section
noncomputable section
namespace PELOriginalDescendedPeriodTensor318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELOriginalSiegelNormalization318 PELOriginalPeriodKernelConnection318
open PELOriginalFlatPeriodSquare318 PELOriginalKernelMonodromyCovariance318
open PELOriginalCentralSignTransport318 PELOriginalEffectiveTensorDescent318
open scoped TensorProduct

/-- The genuine second-fundamental bilinear pairing, retaining all
original kernel/flat derivative/polarization data. -/
@[expose] def bilinear (τ : ℂ) (hτ : 0<τ.im) :
    ComplexVectors →ₗ[ℂ] ComplexVectors →ₗ[ℂ] ℂ where
  toFun v :=
    { toFun := secondPairing τ v
      map_add' := by
        intro w w'
        simp only [secondPairing_formula τ (parameter_ne τ hτ)]
        simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two]
        ring
      map_smul' := by
        intro a w
        simp only [secondPairing_formula τ (parameter_ne τ hτ)]
        simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two,smul_eq_mul]
        ring }
  map_add' := by
    intro v v'
    ext w
    simp only [LinearMap.add_apply,secondPairing_formula τ (parameter_ne τ hτ)]
    simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two]
    ring
  map_smul' := by
    intro a v
    ext w
    simp only [LinearMap.smul_apply,secondPairing_formula τ (parameter_ne τ hτ)]
    simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two,smul_eq_mul]
    ring

/-- Actual balanced functional on the WHOLE tensor square. -/
@[expose] def tensorForm (τ : ℂ) (hτ : 0<τ.im) :
    (ComplexVectors ⊗[ℂ] ComplexVectors) →ₗ[ℂ] ℂ := TensorProduct.lift (bilinear τ hτ)
lemma tensorForm_tmul (τ : ℂ) (hτ : 0<τ.im) (v w : ComplexVectors) :
    tensorForm τ hτ (v ⊗ₜ[ℂ] w)=secondPairing τ v w := by
  rw [tensorForm,TensorProduct.lift.tmul]
  rfl

/-- Whole balanced tensor covariance for actual norm-one monodromy. -/
theorem tensorForm_covariance (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : ComplexVectors ⊗[ℂ] ComplexVectors) :
    tensorForm τ hτ (tensorTransition u τ hτ x)=
      deriv (parameter u) τ*tensorForm (parameter u τ) (parameter_positive u τ hτ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
      change tensorForm τ hτ (coefficientEquiv u τ hτ v ⊗ₜ[ℂ] coefficientEquiv u τ hτ w)=_
      rw [tensorForm_tmul,tensorForm_tmul]
      exact secondPairing_covariance u τ hτ v w
  | add x y hx hy => simp only [map_add,hx,hy,mul_add]

/-- Actual effective-base descent of the entire connection tensor. Its
base map is the original effective action, and its transition is the
lift-independent even tensor transition with the proved cocycle. -/
theorem effective_covariance (g : PELEffectiveNormOneAction318.effectiveGroup)
    (τ : HalfPlane) (x : ComplexVectors ⊗[ℂ] ComplexVectors) :
    tensorForm τ τ.property (transition g τ x)=
      deriv (parameter (unitLift g)) τ*tensorForm (g • τ) (g • τ).property x := by
  have h := tensorForm_covariance (unitLift g) τ τ.property x
  simpa only [transition,actual_parameter g τ] using h
end PELOriginalDescendedPeriodTensor318
