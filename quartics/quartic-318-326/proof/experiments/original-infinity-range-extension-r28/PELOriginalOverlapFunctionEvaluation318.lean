module
public import FaithfulLocalizedFunctionEvaluation318
public import PELOriginalCompletedChartEvaluation318
public import PELOriginalRegularEvaluationInjective318
public import FourRootCoordinateOverlap318
public section
noncomputable section
namespace PELOriginalOverlapFunctionEvaluation318
open PELOriginalRegularCoordinateAlgebra318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedChartEvaluation318

lemma root_zero_ne (x : OriginalRegular) : roots x.val 0 ≠ 0 := by
  intro h
  have he := roots_square x.val x.property 0
  rw [h,zero_pow (by decide : 2 ≠ 0)] at he
  have ht : base x.val = branches 0 := sub_eq_zero.mp he.symm
  apply denominator_ne x.val x.property
  simp [FourCharacterRootRecombination318.denominator,
    FourCharacterRootRecombination318.product,FourCharacterRootRecombination318.linear,ht]

@[expose] def overlapEvaluation : FourRootCoordinateOverlap318.AffineOverlap branches →ₐ[ℂ] Functions :=
  FaithfulLocalizedFunctionEvaluation318.evaluation evaluation
    (FourRootAffineCoordinateRing318.coordinate branches (some 0))
    (fun x => by simpa only [evaluation_root,originalRoot] using root_zero_ne x)

lemma overlapEvaluation_source (a : CoordinateRing) :
    overlapEvaluation (algebraMap CoordinateRing _ a) = evaluation a :=
  FaithfulLocalizedFunctionEvaluation318.evaluation_source ..

lemma overlapEvaluation_injective : Function.Injective overlapEvaluation :=
  FaithfulLocalizedFunctionEvaluation318.evaluation_injective _ _ _
    PELOriginalRegularEvaluationInjective318.evaluation_injective

lemma overlapEvaluation_inverse (x : OriginalRegular) :
    overlapEvaluation (FourRootCoordinateOverlap318.zi branches) x = (roots x.val 0)⁻¹ := by
  have h := congrArg (fun q => overlapEvaluation q x) (FourRootCoordinateOverlap318.z_zi branches)
  simp only [map_mul,map_one,Pi.mul_apply,Pi.one_apply] at h
  simp only [FourRootCoordinateOverlap318.z,overlapEvaluation_source] at h
  change evaluation (FourRootAffineCoordinateRing318.coordinate branches (some 0)) x * _ = 1 at h
  rw [evaluation_root] at h
  change roots x.val 0 * _ = 1 at h
  calc
    _ = (roots x.val 0)⁻¹ * (roots x.val 0 * overlapEvaluation (FourRootCoordinateOverlap318.zi branches) x) := by
      rw [←mul_assoc,inv_mul_cancel₀ (root_zero_ne x),one_mul]
    _ = (roots x.val 0)⁻¹ := by rw [h,mul_one]

/-- Exact old regular point in the normalized infinity chart, with no root choice. -/
def regularInfinity (x : OriginalRegular) : InfinitySource :=
  ⟨(x.val,(FourRootNormalizedPointCharts318.toInfinity branches
      ⟨(regularPoint x).val.2,root_zero_ne x⟩).val),
    (regularPoint x).property.trans
      (FourRootNormalizedPointCharts318.overlap_agreement branches _).symm⟩

/-- Full-ring equality, not just a comparison of complex Scheme points. -/
lemma infinity_regular_agreement (a : FourRootInfinityCoordinateRing318.Ring branches)
    (x : OriginalRegular) :
    infinityAt (regularInfinity x) a =
      overlapEvaluation (FourRootCoordinateOverlap318.toAffineBase branches a) x := by
  let ev : FourRootCoordinateOverlap318.AffineOverlap branches →ₐ[ℂ] ℂ :=
    { toFun := fun q => overlapEvaluation q x
      map_zero' := congrFun (map_zero overlapEvaluation) x
      map_one' := congrFun (map_one overlapEvaluation) x
      map_add' := fun q r => congrFun (map_add overlapEvaluation q r) x
      map_mul' := fun q r => congrFun (map_mul overlapEvaluation q r) x
      commutes' := fun c => congrFun (overlapEvaluation.commutes c) x }
  have he : infinityAt (regularInfinity x) = ev.comp (FourRootCoordinateOverlap318.toAffineBase branches) := by
    apply FourRootInfinityCoordinateRing318.hom_ext
    intro k
    cases k with
    | none =>
      simpa [infinityAt,regularInfinity,FourRootInfinityCoordinateRing318.pointEquiv,
        FourRootNormalizedPointCharts318.toInfinity,ev] using (overlapEvaluation_inverse x).symm
    | some k =>
      simp [infinityAt,regularInfinity,FourRootInfinityCoordinateRing318.pointEquiv,
        FourRootNormalizedPointCharts318.toInfinity,ev,
        FourRootCoordinateOverlap318.z,overlapEvaluation_source,evaluation_root,
        originalRoot,regularPoint,overlapEvaluation_inverse,div_eq_mul_inv]
  exact AlgHom.congr_fun he a
end PELOriginalOverlapFunctionEvaluation318
