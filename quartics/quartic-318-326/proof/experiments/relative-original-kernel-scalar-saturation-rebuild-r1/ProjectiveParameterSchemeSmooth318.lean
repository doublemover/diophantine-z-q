module
public import OriginalParameterSliceSmooth318
public import ProjectiveParameterSliceBase318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace ProjectiveParameterSchemeSmooth318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

instance chart_smooth (i : Fin F.size) :
    Smooth (ProjectiveParameterSliceSchemes318.projection R P i) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- Smoothness of the ACTUAL glued normalization parameter over its
original coefficient base. Every chart is the original coordinate-one
quotient, and the full existing gluing cover is used. -/
instance smooth : Smooth (ProjectiveParameterSliceBase318.projection R P) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Smooth)
    (ProjectiveParameterSliceGluing318.cover R P)
  intro i
  change Smooth (ProjectiveParameterSliceGluing318.into R P i ≫
    ProjectiveParameterSliceBase318.projection R P)
  rw [ProjectiveParameterSliceBase318.into_projection]
  infer_instance

theorem flat_lfp : Flat (ProjectiveParameterSliceBase318.projection R P) ∧
    LocallyOfFinitePresentation (ProjectiveParameterSliceBase318.projection R P) :=
  ⟨inferInstance,inferInstance⟩
end ProjectiveParameterSchemeSmooth318
