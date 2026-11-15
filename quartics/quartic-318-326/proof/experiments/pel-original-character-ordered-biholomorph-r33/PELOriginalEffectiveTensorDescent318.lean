module
public import PELOriginalEvenTensorCocycle318
public section
noncomputable section
namespace PELOriginalEffectiveTensorDescent318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointNormOneAction318 PELEffectiveNormOneAction318
open PELOriginalFlatPeriodSquare318 PELOriginalCentralSignTransport318
open PELOriginalEvenTensorCocycle318
open scoped TensorProduct

@[expose] def unitLift (g : effectiveGroup) : normOneUnits :=
  Classical.choose (effectiveMap_surjective g)
lemma unitLift_spec (g : effectiveGroup) : effectiveMap (unitLift g)=g :=
  Classical.choose_spec (effectiveMap_surjective g)
lemma actual_parameter (g : effectiveGroup) (τ : HalfPlane) :
    parameter (unitLift g) (τ:ℂ)=((g • τ:HalfPlane):ℂ) := by
  exact congrArg (fun a : effectiveGroup => ((a • τ:HalfPlane):ℂ)) (unitLift_spec g)

/-- Genuine whole even-tensor transition over the SAME actual effective
original base action. Its independence of this auxiliary lift is proved below. -/
@[expose] def transition (g : effectiveGroup) (τ : HalfPlane) :
    (ComplexVectors ⊗[ℂ] ComplexVectors) ≃ₗ[ℂ] (ComplexVectors ⊗[ℂ] ComplexVectors) :=
  tensorTransition (unitLift g) τ τ.property
lemma transition_lift (g : effectiveGroup) (u : normOneUnits) (hu : effectiveMap u=g)
    (τ : HalfPlane) : transition g τ=tensorTransition u τ τ.property := by
  exact tensorTransition_effective (unitLift g) u ((unitLift_spec g).trans hu.symm) τ τ.property

/-- Actual identity and cocycle on ALL tensor elements, after removing
precisely the original central sign, not after silently discarding it on
the rank-two kernel itself. -/
theorem cocycle (g h : effectiveGroup) (τ : HalfPlane)
    (x : ComplexVectors ⊗[ℂ] ComplexVectors) :
    transition h τ (transition g (h • τ) x)=transition (g*h) τ x := by
  have hm : effectiveMap (unitLift g*unitLift h)=g*h := by
    rw [map_mul,unitLift_spec,unitLift_spec]
  rw [transition_lift g (unitLift g) (unitLift_spec g),
    transition_lift h (unitLift h) (unitLift_spec h),
    transition_lift (g*h) (unitLift g*unitLift h) hm]
  have hb := (actual_parameter h τ).symm
  simpa only [hb] using tensor_cocycle (unitLift g) (unitLift h) τ τ.property x
lemma identity (τ : HalfPlane) (x : ComplexVectors ⊗[ℂ] ComplexVectors) :
    transition 1 τ x=x := by
  rw [transition_lift 1 1 (map_one effectiveMap)]
  exact tensor_one τ τ.property x
end PELOriginalEffectiveTensorDescent318
