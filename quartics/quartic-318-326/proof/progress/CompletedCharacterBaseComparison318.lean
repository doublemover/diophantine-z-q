module
public import WeierstrassXStructure318
public import CompletedCharacterGlobal318
public import CubicInverseCoordinates318
public import SchematicEqualityExtension318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace CompletedCharacterBaseComparison318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev P1:=ProjectiveJLine318.scheme ℚ
@[expose] def slope (i:Fin 4):ℚˣ:=(CubicInverseCoordinates318.xScale i)⁻¹
@[expose] def affinePolynomial (i:Fin 4):ℚ[X]:=C (slope i:ℚ)*X+C (SourceTwistArithmetic318.centroid i)

lemma source_adjusted_x (i:Fin 4):
    algebraMap ℚ SourceCharacterAlgebra318.Source (slope i:ℚ)*
      SourceCharacterAlgebra318.publishedToSource i (ShortAffineJacobian318.x (publishedA i) (publishedB i))+
        algebraMap ℚ SourceCharacterAlgebra318.Source (SourceTwistArithmetic318.centroid i)=
      algebraMap ℚ[X] SourceCharacterAlgebra318.Source X:=by
  rw [CubicInverseCoordinates318.source_x,←mul_assoc,←map_mul]
  change algebraMap ℚ SourceCharacterAlgebra318.Source
      ((↑(CubicInverseCoordinates318.xScale i)⁻¹:ℚ)*(CubicInverseCoordinates318.xScale i:ℚ))*_+_=_
  rw [Units.inv_mul,map_one,one_mul,sub_add_cancel]

variable (i:Fin 4) (L:P1⟶P1)
  (hL:JLineAtlas318.chart ℚ 1≫L=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (affinePolynomial i)).toRingHom)≫JLineAtlas318.chart ℚ 1)
  (hQ:L≫ProjectiveJLine318.structureMap ℚ=ProjectiveJLine318.structureMap ℚ)

include hL in
lemma finite_composite:
    SourceGlobalAffine318.chartEmbedding units≫completedMap i≫
      WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L=
    SourceGlobalAffine318.chartEmbedding units≫ContactProjectiveModel318.modelMap units:=by
  rw [←Category.assoc,←Category.assoc,on_finite]
  rw [finiteChartMap]
  simp only [Category.assoc]
  rw [←Category.assoc (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
      (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)) L,
    WeierstrassXProjection318.finiteChart_xMap]
  rw [WeierstrassXProjection318.finiteProjection,Category.assoc,hL,
    ContactProjectiveModel318.modelMap]
  erw [SourceGlobalAffine318.chartEmbedding_over_contact_line]
  unfold SourceCharacterAffine318.publishedMap
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply ℚ ℚ[X] SourceCharacterAlgebra318.Source r).symm
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,affinePolynomial,
      map_add,map_mul,Polynomial.aeval_C,AlgHom.commutes]
    exact source_adjusted_x i

include hL hQ in
/-- The full actual source map respects the original t-line, once the stated
actual projective affine transformation has been supplied. -/
theorem full_composite:
    completedMap i≫WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L=
      ContactProjectiveModel318.modelMap units:=by
  letI:IsIntegral (ContactGlobalSmooth318.Model units):=
    (ContactGlobalProper318.proper_integral_extension units).2.1
  letI:IsDomain (ContactKummerOrder318.SourceOrder units):=ContactKummerOrder318.source_domain units
  let j:=SourceGlobalAffine318.chartEmbedding units
  letI:IsDominant j:=⟨IsOpenMap.denseRange_of_isPreirreducibleSpace j j.isOpenEmbedding.isOpenMap⟩
  letI:IsSchemeTheoreticallyDominant j:=IsSchemeTheoreticallyDominant.of_isDominant j
  have hb:(completedMap i≫WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)≫
      ProjectiveJLine318.structureMap ℚ=
      ContactProjectiveModel318.modelMap units≫ProjectiveJLine318.structureMap ℚ:=by
    rw [Category.assoc,Category.assoc,hQ,WeierstrassXStructure318.xMap_over_base]
    exact over_Q i
  exact SchematicEqualityExtension318.ext (ProjectiveJLine318.structureMap ℚ) hb j
    (finite_composite i L hL)

include hQ in
lemma target_composite_separated:
    IsSeparated (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L):=by
  haveI:IsSeparated ((WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)≫
      ProjectiveJLine318.structureMap ℚ):=by
    rw [Category.assoc,hQ,WeierstrassXStructure318.xMap_over_base]
    exact CubicClosedImmersion318.structure_separated _ _
  exact IsSeparated.of_comp _ (ProjectiveJLine318.structureMap ℚ)

include hL hQ in
/-- Finiteness of the actual completed character map follows from its exact
factorization of the original finite contact normalization over P1. -/
theorem finite_of_affine_transformation:IsFinite (completedMap i):=by
  letI:=target_composite_separated i L hQ
  haveI:IsFinite (completedMap i≫(WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)):=by
    rw [full_composite i L hL hQ]
    exact ContactGlobalProper318.normalization_finite units
  exact IsFinite.of_comp (completedMap i) (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)
end CompletedCharacterBaseComparison318
