module
public import PELOriginalDeterminantMetricTransition318
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public section
noncomputable section
namespace PELOriginalNormedKernelDeterminant318
open PELOriginalKernelDeterminantLine318 PELOriginalDeterminantCoordinate318
open PELOriginalDeterminantDescent318 PELOriginalDeterminantMetricTransition318
open PELOriginalFlatPeriodSquare318

/-- Canonical determinant coordinate of the ACTUAL full kernel exterior
fiber, produced by its genuine kernel frame and universal determinant. -/
@[expose] def coordinate (τ : ℂ) : Fiber τ ≃ₗ[ℂ] ℂ := (frame τ).symm.trans coordinateEquiv
@[expose] def metricFrame (τ : ℂ) (hτ : 0<τ.im) : Fiber τ ≃ₗ[ℂ] ℂ :=
  (coordinate τ).trans (LinearEquiv.smulOfUnit
    (Units.mk0 (scale τ:ℂ) (Complex.ofReal_ne_zero.mpr (scale_positive τ hτ).ne')))
@[expose] def normedGroup (τ : ℂ) (hτ : 0<τ.im) : NormedAddCommGroup (Fiber τ) :=
  NormedAddCommGroup.induced _ ℂ (metricFrame τ hτ).toAddMonoidHom (metricFrame τ hτ).injective
@[expose] def normedSpace (τ : ℂ) (hτ : 0<τ.im) :
    letI := normedGroup τ hτ
    NormedSpace ℂ (Fiber τ) := by
  letI := normedGroup τ hτ
  refine { norm_smul_le := ?_ }
  intro a x
  change ‖metricFrame τ hτ (a • x)‖≤‖a‖*‖metricFrame τ hτ x‖
  rw [map_smul,norm_smul]
@[expose] def normValue (τ : ℂ) (hτ : 0<τ.im) (x : Fiber τ) : ℝ := ‖metricFrame τ hτ x‖
lemma norm_formula (τ : ℂ) (hτ : 0<τ.im) (x : Fiber τ) :
    normValue τ hτ x=scale τ*‖coordinate τ x‖ := by
  change ‖(scale τ:ℂ)*coordinate τ x‖=_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (scale_positive τ hτ)]
lemma actual_norm (τ : ℂ) (hτ : 0<τ.im) (x : Fiber τ) :
    letI := normedGroup τ hτ
    ‖x‖=normValue τ hτ x := rfl

lemma coordinate_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : Fiber (parameter u τ)) :
    coordinate τ (PELOriginalKernelDeterminantLine318.transport u τ hτ x)=
      transitionScalar u τ hτ*coordinate (parameter u τ) x := by
  have h := congrArg (fun f => f ((frame (parameter u τ)).symm x)) (frame_transport u τ hτ)
  simp only [LinearMap.comp_apply,LinearEquiv.apply_symm_apply] at h
  have hf : (frame τ).symm (PELOriginalKernelDeterminantLine318.transport u τ hτ x)=
      unitTransition u τ hτ ((frame (parameter u τ)).symm x) := by
    apply (frame τ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact h
  change coefficient ((frame τ).symm (PELOriginalKernelDeterminantLine318.transport u τ hτ x))=_
  rw [hf,coefficient_transition]
  rfl

/-- Genuine entire-fiber isometry of the actual determinant line under
its original integral monodromy. No abstract normed-line identification
or unproved arithmetic Hodge comparison is inserted. -/
theorem norm_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : Fiber (parameter u τ)) :
    normValue τ hτ (PELOriginalKernelDeterminantLine318.transport u τ hτ x)=
      normValue (parameter u τ) (parameter_positive u τ hτ) x := by
  rw [norm_formula,norm_formula,coordinate_transport,norm_mul,scale_transport]
  ring
end PELOriginalNormedKernelDeterminant318
