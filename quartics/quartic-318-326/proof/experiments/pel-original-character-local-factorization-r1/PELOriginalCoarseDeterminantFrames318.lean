module
public import PELOriginalCoarseDeterminantBundle318
public section
noncomputable section
namespace PELOriginalCoarseDeterminantFrames318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318
open PELOriginalDeterminantCover318 PELOriginalContinuousDeterminantCocycle318
open PELOriginalCoarseDeterminantBundle318
open PELOriginalEffectiveTensorDescent318 PELOriginalDeterminantCoordinate318
open PELOriginalNormedKernelDeterminant318 PELOriginalDeterminantMetricTransition318
open PELOriginalFlatPeriodSquare318

/-- Actual local coordinate of the constructed bundle, with the chosen
fiber gauge transported to the specified genuine covering chart. -/
@[expose] def localCoordinate (a : HalfPlane) (q : UnlevelledBase) :
    PELOriginalCoarseDeterminantBundle318.Fiber q ≃ₗ[ℂ] ℂ :=
  LinearEquiv.smulOfUnit (Units.mk0 (transition (core.indexAt q) a q)
    (transition_ne _ _ _))
lemma localCoordinate_apply (a : HalfPlane) (q : UnlevelledBase)
    (x : PELOriginalCoarseDeterminantBundle318.Fiber q) :
    localCoordinate a q x=transition (core.indexAt q) a q*x := rfl
lemma genuine_localTriv (a : HalfPlane) (q : UnlevelledBase)
    (x : PELOriginalCoarseDeterminantBundle318.Fiber q) :
    (core.localTriv a ⟨q,x⟩).2=localCoordinate a q x := rfl
lemma localCoordinate_change (a b : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b)
    (x : PELOriginalCoarseDeterminantBundle318.Fiber q) :
    localCoordinate b q x=transition a b q*localCoordinate a q x := by
  simp only [localCoordinate_apply]
  rw [←mul_assoc,transition_comp _ a b q (core.mem_baseSet_at q) ha hb]

/-- Both-inverse comparison with the GENUINE whole exterior kernel fiber
at the actual covering lift, not just an isomorphism of rank-one carriers. -/
@[expose] def exteriorFrame (a : HalfPlane) (q : UnlevelledBase) :
    PELOriginalCoarseDeterminantBundle318.Fiber q ≃ₗ[ℂ]
      PELOriginalKernelDeterminantLine318.Fiber (chart a q:ℂ) :=
  (localCoordinate a q).trans (coordinate (chart a q:ℂ)).symm
lemma exteriorFrame_coordinate (a : HalfPlane) (q : UnlevelledBase)
    (x : PELOriginalCoarseDeterminantBundle318.Fiber q) :
    coordinate (chart a q:ℂ) (exteriorFrame a q x)=localCoordinate a q x :=
  (coordinate _).apply_symm_apply _
/-- Exact whole-vector square with the original integral exterior
monodromy. The source parameter is the literal Mobius transform, whose
equality to the second covering lift is produced by shift_spec. -/
lemma exteriorFrame_transport (a b : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b)
    (x : PELOriginalCoarseDeterminantBundle318.Fiber q) :
    PELOriginalKernelDeterminantLine318.transport (unitLift (shift a b q))
      (chart a q:ℂ) (chart a q).property
      ((coordinate (parameter (unitLift (shift a b q)) (chart a q:ℂ))).symm
        (localCoordinate b q x))=exteriorFrame a q x := by
  apply (coordinate (chart a q:ℂ)).injective
  rw [coordinate_transport,LinearEquiv.apply_symm_apply,exteriorFrame_coordinate,
    ←scalar_eq,localCoordinate_change a b q ha hb,transition]
  rw [←mul_assoc,mul_inv_cancel₀ (scalar_nonzero _ _),one_mul]

lemma local_norm_change (a b : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b)
    (x : PELOriginalCoarseDeterminantBundle318.Fiber q) :
    scale (chart b q:ℂ)*‖localCoordinate b q x‖=
      scale (chart a q:ℂ)*‖localCoordinate a q x‖ := by
  have hp : parameter (unitLift (shift a b q)) (chart a q:ℂ)=(chart b q:ℂ) := by
    rw [actual_parameter,shift_spec a b q ha hb]
  have hs := scale_transport (unitLift (shift a b q)) (chart a q:ℂ) (chart a q).property
  rw [hp,←scalar_eq] at hs
  rw [localCoordinate_change a b q ha hb,transition,norm_mul,norm_inv,hs]
  have hn : ‖scalar (shift a b q) (chart a q)‖≠0 := norm_ne_zero_iff.mpr (scalar_nonzero _ _)
  field_simp
end PELOriginalCoarseDeterminantFrames318
