module
public import PELOriginalWholeCharacterProper318
public import FourRootSchematicDensity318
public import WeierstrassXStructure318
public import ProjectiveAffineCharts318
public section
noncomputable section
namespace PELOriginalCharacterBaseProjection318
open AlgebraicGeometry CategoryTheory Polynomial
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev P1:=ProjectiveJLine318.scheme ℂ
@[expose] def slope (i:Fin 4):ℂˣ:=Units.mk0 (difference i)
  (sub_ne_zero.mpr (PELOriginalOrderedCharacterSchemeMaps318.first_difference i))
@[expose] def affinePolynomial (i:Fin 4):ℂ[X]:=C (difference i)*X+C (center i)
@[expose] def affineTransform (i:Fin 4):P1⟶P1:=ProjectiveAffineLine318.map ℂ (slope i) (center i)
lemma affineTransform_chart (i:Fin 4):JLineAtlas318.chart ℂ 1≫affineTransform i=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℂ) (affinePolynomial i)).toRingHom)≫
      JLineAtlas318.chart ℂ 1:=
  ProjectiveAffineCharts318.chart_naturality ℂ (slope i) (center i)
lemma affineTransform_over_complex (i:Fin 4):affineTransform i≫ProjectiveJLine318.structureMap ℂ=
    ProjectiveJLine318.structureMap ℂ:=
  ProjectiveAffineCharts318.map_over_base ℂ (slope i) (center i)

lemma source_adjusted_x (i:Fin 4):
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (difference i)*
      PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i (ShortAffineJacobian318.x (A i) (B i))+
      algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (center i)=
        FourRootAffineCoordinateRing318.coordinate branches none:=by
  rw [PELOriginalOrderedCharacterCoordinates318.finite_x,←mul_assoc,←map_mul,
    mul_inv_cancel₀ (sub_ne_zero.mpr (PELOriginalOrderedCharacterSchemeMaps318.first_difference i)),
    map_one,one_mul,sub_add_cancel]

/-- The target map restores the exact original t, including the original
root difference and centroid. It is defined on the whole proper target. -/
@[expose] def targetTMap (i:Fin 4):Curve i⟶P1:=
  WeierstrassXProjection318.xMap (A i) (B i)≫affineTransform i
lemma target_over_complex (i:Fin 4):targetTMap i≫ProjectiveJLine318.structureMap ℂ=
    WeierstrassGluing318.structureMap (A i) (B i):=by
  rw [targetTMap,Category.assoc,affineTransform_over_complex,WeierstrassXStructure318.xMap_over_base]

lemma finite_composite (i:Fin 4):FourRootGluedScheme318.finiteChart branches≫morphism i≫targetTMap i=
    FourRootGluedScheme318.finiteChart branches≫FourRootProjectiveProjection318.projection branches:=by
  rw [←Category.assoc,on_finite,finiteMap,targetTMap]
  simp only [Category.assoc]
  rw [←Category.assoc (WeierstrassGluing318.finiteChart (A i) (B i))
    (WeierstrassXProjection318.xMap (A i) (B i)) (affineTransform i),
    WeierstrassXProjection318.finiteChart_xMap]
  rw [WeierstrassXProjection318.finiteProjection,Category.assoc,affineTransform_chart,
    FourRootProjectiveProjection318.finite_projection]
  unfold PELOriginalOrderedCharacterSchemeMaps318.morphism
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,affinePolynomial,
      map_add,map_mul,Polynomial.aeval_C,AlgHom.commutes]
    exact source_adjusted_x i

/-- The global factorization is an equality of genuine scheme morphisms
over the ORIGINAL unshifted t-line, not only of function-field elements. -/
theorem full_composite (i:Fin 4):morphism i≫targetTMap i=
    FourRootProjectiveProjection318.projection branches:=by
  apply FourRootSchematicDensity318.ext branches branches_injective
    (ProjectiveJLine318.structureMap ℂ)
  · rw [Category.assoc,target_over_complex,over_complex,FourRootProjectiveProjection318.over_base]
  · exact finite_composite i
end PELOriginalCharacterBaseProjection318
