module
public import ProjectiveSwap318
import all JLineAtlas318
public section
noncomputable section
namespace ProjectiveSwapCharts318
open MvPolynomial Graded HomogeneousIdeal AlgebraicGeometry CategoryTheory HomogeneousLocalization
open ProjectiveSwap318 ProjectiveAffineCharts318
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R:Type*) [CommRing R]
@[expose] def awayMap:Away (grading R) (X (0:Fin 2))→+*Away (grading R) (X (1:Fin 2)):=
  awayMapAt R (gh R) (X 0) (X 1) (gh_X0 R)
lemma away_naturality:
    Proj.awayι (grading R) (X (1:Fin 2)) (isHomogeneous_X R 1) (by omega)≫ProjectiveSwap318.map R=
      Spec.map (CommRingCat.ofHom (awayMap R))≫
        Proj.awayι (grading R) (X (0:Fin 2)) (isHomogeneous_X R 0) (by omega):=
  awayMapAt_naturality R (gh R) (irrelevant_le R) (X 0) (X 1) (gh_X0 R)
    (by decide:0<1) (isHomogeneous_X R 0)
lemma away_C (r:R):awayMap R (algebraMap R (Away (grading R) (X (0:Fin 2))) r)=
    algebraMap R (Away (grading R) (X (1:Fin 2))) r:=by
  change awayMap R (Away.mk (grading R) (isHomogeneous_X R 0) 0 (C r) _)=
    Away.mk (grading R) (isHomogeneous_X R 1) 0 (C r) _
  rw [awayMap,awayMapAt_mk]
  simp only [gh_C]
lemma chart_mapped_X:
    JLineAtlas318.chartEquiv R 1 (awayMap R ((JLineAtlas318.chartEquiv R 0).symm Polynomial.X))=Polynomial.X:=by
  rw [JLineAtlas318.chartEquiv_symm_X]
  change JLineAtlas318.chartEquiv R 1 (awayMap R
    (Away.mk (grading R) (isHomogeneous_X R 0) 1 (X (1:Fin 2)) _))=_
  rw [awayMap,awayMapAt_mk]
  change (uniqueAlgEquiv R (Fin 1)) ((renameEquiv R (finSuccAboveEquiv (1:Fin 2)).symm)
    (ProjectiveChart318.fromChart R (Fin 2) 1 (Away.mk (grading R) (isHomogeneous_X R 1) 1
      (gh R (X 1)) _)))=_
  rw [ProjectiveChart318.fromChart_mk]
  change (uniqueAlgEquiv R (Fin 1)) ((renameEquiv R (finSuccAboveEquiv (1:Fin 2)).symm)
    (ProjectiveChart318.dehomogenize R (Fin 2) 1 (hom R (X 1))))=_
  rw [hom_X1]
  simp [ProjectiveChart318.dehomogenize,renameEquiv,uniqueAlgEquiv]
@[expose] def awayAlgHom:Away (grading R) (X (0:Fin 2))→ₐ[R]Away (grading R) (X (1:Fin 2)) where
  __:=awayMap R
  commutes':=away_C R
lemma awayAlgHom_apply (r):awayAlgHom R r=awayMap R r:=rfl
lemma chartHom_eq:
    (JLineAtlas318.chartEquiv R 1).toAlgHom.comp ((awayAlgHom R).comp
      (JLineAtlas318.chartEquiv R 0).symm.toAlgHom)=AlgHom.id R (Polynomial R):=by
  apply Polynomial.algHom_ext
  exact chart_mapped_X R
/-- Genuine coordinate inversion interchanges the actual two polynomial charts. -/
@[reassoc] theorem chart_one:JLineAtlas318.chart R 1≫ProjectiveSwap318.map R=JLineAtlas318.chart R 0:=by
  unfold JLineAtlas318.chart
  rw [Category.assoc,away_naturality,←Category.assoc,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change JLineAtlas318.chartEquiv R 1 (awayMap R p)=JLineAtlas318.chartEquiv R 0 p
  have h:=congrArg (fun f:Polynomial R→ₐ[R]Polynomial R=>f (JLineAtlas318.chartEquiv R 0 p)) (chartHom_eq R)
  simpa only [AlgHom.comp_apply,AlgEquiv.toAlgHom_eq_coe,AlgEquiv.coe_algHom,
    AlgEquiv.symm_apply_apply,AlgHom.id_apply,awayAlgHom_apply] using h
@[reassoc] theorem chart_zero:JLineAtlas318.chart R 0≫ProjectiveSwap318.map R=JLineAtlas318.chart R 1:=by
  rw [←chart_one R,Category.assoc,map_twice,Category.comp_id]
@[reassoc] theorem over_base:ProjectiveSwap318.map R≫ProjectiveJLine318.structureMap R=
    ProjectiveJLine318.structureMap R:=by
  apply (JLineAtlas318.cover R).hom_ext
  intro i
  change Fin 2 at i
  change JLineAtlas318.chart R i≫(ProjectiveSwap318.map R≫_)=JLineAtlas318.chart R i≫_
  fin_cases i
  · change JLineAtlas318.chart R 0≫(ProjectiveSwap318.map R≫ProjectiveJLine318.structureMap R)=JLineAtlas318.chart R 0≫ProjectiveJLine318.structureMap R
    rw [←Category.assoc,chart_zero,JLineAtlas318.chart_over_base,JLineAtlas318.chart_over_base]
  · change JLineAtlas318.chart R 1≫(ProjectiveSwap318.map R≫ProjectiveJLine318.structureMap R)=JLineAtlas318.chart R 1≫ProjectiveJLine318.structureMap R
    rw [←Category.assoc,chart_one,JLineAtlas318.chart_over_base,JLineAtlas318.chart_over_base]
end ProjectiveSwapCharts318
