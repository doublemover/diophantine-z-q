module
public import ProjectiveParameterSliceSchemes318
public section
noncomputable section
namespace ProjectiveParameterSliceSelf318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
variable (i : Fin F.size)
lemma coordinate_one : ProjectiveParameterSliceLocalization318.coordinate R P i i=1 :=
  ProjectiveParameterSliceAlgebra318.coordinate_one R P i

@[expose] def ringIso : B i ≃ₐ[B i] O i i :=
  IsLocalization.atUnit (B i) (O i i) (ProjectiveParameterSliceLocalization318.coordinate R P i i)
    (by rw [coordinate_one]; exact isUnit_one)
lemma ringIso_map : (ringIso R P i).toRingHom=algebraMap (B i) (O i i) := by
  apply RingHom.ext
  intro a
  simpa only [Algebra.algebraMap_self_apply] using (ringIso R P i).commutes a

/-- A diagonal overlap is the whole original slice, by actual
localization at its coordinate-one relation. -/
@[expose] def schemeIso : ProjectiveParameterSliceSchemes318.overlap R P i i ≅
    ProjectiveParameterSliceSchemes318.chart R P i :=
  Scheme.Spec.mapIso (ringIso R P i).toRingEquiv.toCommRingCatIso.op
lemma schemeIso_hom : (schemeIso R P i).hom=ProjectiveParameterSliceSchemes318.inclusion R P i i := by
  change Spec.map (CommRingCat.ofHom (ringIso R P i).toRingHom)=_
  rw [ringIso_map]
  rfl
instance self_inclusion : IsIso (ProjectiveParameterSliceSchemes318.inclusion R P i i) := by
  rw [← schemeIso_hom]
  infer_instance

lemma unit_one : ProjectiveParameterSliceLocalization318.unit R P i i=1 := by
  apply Units.ext
  change algebraMap (B i) (O i i) (ProjectiveParameterSliceLocalization318.coordinate R P i i)=1
  rw [coordinate_one,map_one]
lemma transition_ring : ProjectiveParameterSliceLocalization318.transition R P i i=AlgHom.id R (O i i) := by
  apply ProjectiveParameterSliceLocalizationIso318.hom_ext R P i i
  intro a
  rw [ProjectiveParameterSliceLocalization318.transition_point,unit_one,inv_one]
  exact DFunLike.congr_fun
    (ProjectiveParameterUnitAction318.pointScale_one R P (O i i)
      (ProjectiveParameterSliceLocalization318.point R P i i)) a
lemma transition_self : (ProjectiveParameterSliceSchemes318.transitionIso R P i i).hom=𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceLocalization318.transition R P i i).toRingHom)=_
  rw [transition_ring]
  exact Spec.map_id _
end ProjectiveParameterSliceSelf318
